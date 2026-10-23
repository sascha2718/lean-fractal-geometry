import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.BlockIndependence
import FractalGeometry.Probability.GridPercolation.Configuration
import FractalGeometry.Probability.GridPercolation.ExplorationParameters
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.LawInvariance
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.Processes
import FractalGeometry.Probability.GridPercolation.RootIndependence
import FractalGeometry.Probability.GridPercolation.TreeExploration
import FractalGeometry.Probability.GridPercolation.TreeExplorationProbability
import FractalGeometry.Probability.GridPercolation.WordSplitting

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory ProbabilityTheory Filter Topology

open scoped ENNReal

variable {A : GridLaw}

noncomputable def allowedDigits (A : GridLaw) : Finset (Fin A.M × Fin A.N) :=
  Finset.univ.filter fun a => 0 < A.p a.1 a.2

lemma m_le_card_allowedDigits (A : GridLaw) : A.m ≤ (allowedDigits A).card := by
  classical
  have h1 : A.m = ∑ a : Fin A.M × Fin A.N, A.p a.1 a.2 := by
    simp only [GridLaw.m, GridLaw.E, Fintype.sum_prod_type]
  rw [h1, allowedDigits, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  split_ifs with h
  · simpa using A.p_le_one a.1 a.2
  · simpa using not_lt.mp h

noncomputable def allowedWords (A : GridLaw) (ℓ : ℕ) : Finset (Word A) :=
  (Fintype.piFinset fun _ : Fin ℓ => allowedDigits A).image wordOfDigits

lemma card_allowedWords (A : GridLaw) (ℓ : ℕ) :
    (allowedWords A ℓ).card = (allowedDigits A).card ^ ℓ := by
  have hinj : Function.Injective (wordOfDigits (A := A) (L := ℓ)) :=
    fun u v h => List.ofFn_injective h
  rw [allowedWords, Finset.card_image_of_injective _ hinj, Fintype.card_piFinset]
  simp

noncomputable def fullBranchingCoords (A : GridLaw) (k₀ : ℕ) :
    Finset (Word A × (Fin A.M × Fin A.N)) :=
  ((Finset.range k₀).biUnion (allowedWords A)) ×ˢ allowedDigits A

lemma allowedWords_subset_retainedLevel {x : Configuration A} {k₀ : ℕ}
    (hx : ∀ q ∈ fullBranchingCoords A k₀, x q = true) :
    allowedWords A k₀ ⊆ retainedLevel x k₀ := by
  intro w hw
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
  rw [Fintype.mem_piFinset] at hu
  rw [mem_retainedLevel]
  refine ⟨length_wordOfDigits u, fun l => ?_⟩
  have hl : (l : ℕ) < k₀ := by
    have := l.isLt
    simpa using this
  apply hx
  simp only [fullBranchingCoords, Finset.mem_product, Finset.mem_biUnion, Finset.mem_range]
  refine ⟨⟨l, hl, ?_⟩, ?_⟩
  · rw [List.nil_append, allowedWords, Finset.mem_image]
    refine ⟨Fin.take l hl.le u, Fintype.mem_piFinset.mpr fun i => hu _, ?_⟩
    exact Fin.ofFn_take_eq_take_ofFn hl.le u
  · rw [List.get_eq_getElem]
    simp only [wordOfDigits, List.getElem_ofFn]
    exact hu _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

lemma measure_fullBranching_pos (hX : IsPercolation P X) (k₀ : ℕ) :
    0 < P {ω | ∀ q ∈ fullBranchingCoords A k₀, X q.1 q.2 ω = true} := by
  rw [measure_forall_retained_eq_prod hX, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro q hq
  have hpos : 0 < A.p q.2.1 q.2.2 := by
    simp only [fullBranchingCoords, Finset.mem_product, allowedDigits, Finset.mem_filter,
      Finset.mem_univ, true_and] at hq
    exact hq.2
  exact (ENNReal.ofReal_pos.mpr hpos).ne'

omit [MeasurableSpace Ω] in

lemma fullBranching_subset_exploreGood_zero {k₀ : ℕ} {c : ℕ → ℕ} {M : ℕ → ℝ}
    (hM0 : M 0 ≤ A.m ^ k₀) :
    {ω | ∀ q ∈ fullBranchingCoords A k₀, X q.1 q.2 ω = true} ⊆
      config X ⁻¹' exploreGood k₀ c M 0 := by
  intro ω hω j hj
  obtain rfl : j = 0 := Nat.le_zero.mp hj
  have hsub := allowedWords_subset_retainedLevel (x := config X ω) hω
  calc M 0 ≤ A.m ^ k₀ := hM0
    _ ≤ ((allowedDigits A).card : ℝ) ^ k₀ :=
        pow_le_pow_left₀ A.m_nonneg (m_le_card_allowedDigits A) k₀
    _ = ((allowedWords A k₀).card : ℝ) := by
        rw [card_allowedWords]
        push_cast
        rfl
    _ ≤ (exploreG (config X ω) k₀ c 0).card := by
        exact_mod_cast Finset.card_le_card hsub

theorem measure_exploreGood_ge (hX : IsPercolation P X) {k₀ : ℕ} {K : ℕ → ℝ}
    (hη : ∀ j, 0 ≤ explorationEta A j ∧ explorationEta A j ≤ 1)
    (hcM : ∀ j, (explorationSize A K k₀ j : ℝ) ≤ explorationThreshold A K k₀ j)
    (hS : ∀ J, ∑ j ∈ Finset.range J, explorationFailure A K k₀ j ≤ 1 / 2) (J : ℕ) :
    (P {ω | ∀ q ∈ fullBranchingCoords A k₀, X q.1 q.2 ω = true}).toReal *
        (1 - ∑ j ∈ Finset.range J, explorationFailure A K k₀ j) ≤
      (P (config X ⁻¹' exploreGood k₀ (explorationSize A K k₀)
        (explorationThreshold A K k₀) J)).toReal := by
  let := hX.toIsProbabilityMeasure
  induction J with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, sub_zero, mul_one]
      exact ENNReal.toReal_mono (measure_ne_top _ _)
        (measure_mono (fullBranching_subset_exploreGood_zero le_rfl))
  | succ J ih =>
      set θ := (P {ω | ∀ q ∈ fullBranchingCoords A k₀, X q.1 q.2 ω = true}).toReal with hθ
      set good := config X ⁻¹' exploreGood k₀ (explorationSize A K k₀)
        (explorationThreshold A K k₀) J with hgood
      set good' := config X ⁻¹' exploreGood k₀ (explorationSize A K k₀)
        (explorationThreshold A K k₀) (J + 1) with hgood'
      have hdiff := measure_exploreGood_diff_le hX (M := explorationThreshold A K k₀)
        (c := explorationSize A K k₀) (k₀ := k₀) (J := J) (hη J).1 (hη J).2 (hcM J) le_rfl
      have hsub : good' ⊆ good := Set.preimage_mono (exploreGood_anti (Nat.le_succ J))
      have hmeas' : MeasurableSet good' :=
        measurable_config hX (measurableSet_exploreGood _ _ _ _)
      have heq : (P good').toReal = (P good).toReal - (P (good \ good')).toReal := by
        rw [measure_sdiff hsub hmeas'.nullMeasurableSet (measure_ne_top _ _),
          ENNReal.toReal_sub_of_le (measure_mono hsub) (measure_ne_top _ _)]
        ring
      set e := explorationFailure A K k₀ J with he
      have he0 : 0 ≤ e := (Real.exp_pos _).le
      have he1 : e ≤ 1 := by
        rw [he, explorationFailure, Real.exp_le_one_iff, neg_nonpos]
        have hMc : 0 ≤ explorationThreshold A K k₀ J - explorationSize A K k₀ J := by
          linarith [hcM J]
        positivity
      have hd : (P (good \ good')).toReal ≤ e * (P good).toReal := by
        have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (measure_ne_top _ _)) hdiff
        rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at h
      have hS' : ∑ j ∈ Finset.range J, explorationFailure A K k₀ j ≤ 1 / 2 := hS J
      have hθ0 : 0 ≤ θ := ENNReal.toReal_nonneg
      have hgood_le : (P good).toReal ≤ 1 := by
        rw [← ENNReal.toReal_one]
        exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
      have hS0 : 0 ≤ ∑ j ∈ Finset.range J, explorationFailure A K k₀ j :=
        Finset.sum_nonneg fun j _ => (Real.exp_pos _).le
      rw [Finset.sum_range_succ, heq, ← he]
      have h1 : θ * (1 - ∑ j ∈ Finset.range J, explorationFailure A K k₀ j) * (1 - e) ≤
          (P good).toReal * (1 - e) := mul_le_mul_of_nonneg_right ih (by linarith)
      linarith [mul_nonneg (mul_nonneg hθ0 hS0) he0]

end FractalGeometry.Probability.GridPercolation
