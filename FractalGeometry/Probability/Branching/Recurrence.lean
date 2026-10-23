import Mathlib
import FractalGeometry.Probability.Branching.Configuration
import FractalGeometry.Probability.Branching.Descendants
import FractalGeometry.Probability.Branching.Exploration
import FractalGeometry.Probability.Branching.ExplorationParameters
import FractalGeometry.Probability.Branching.ExplorationProbability
import FractalGeometry.Probability.Branching.GenerationIndependence
import FractalGeometry.Probability.Branching.IdenticalLaws
import FractalGeometry.Probability.Branching.Law
import FractalGeometry.Probability.Branching.Process
import FractalGeometry.Probability.Branching.RetainedWords
import FractalGeometry.Probability.Branching.Words

namespace FractalGeometry.Probability.Branching

open MeasureTheory ProbabilityTheory Filter Topology

open scoped ENNReal

variable {A : Law}

noncomputable def allowedDigits (A : Law) : Finset (Fin A.arity) :=
  Finset.univ.filter fun a => 0 < A.p a

lemma m_le_card_allowedDigits (A : Law) : A.m ≤ (allowedDigits A).card := by
  classical
  have h1 : A.m = ∑ a : Fin A.arity, A.p a := by
    rfl
  rw [h1, allowedDigits, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  split_ifs with h
  · simpa using A.p_le_one a
  · simpa using not_lt.mp h

noncomputable def allowedWords (A : Law) (ℓ : ℕ) : Finset (Word A) :=
  (Fintype.piFinset fun _ : Fin ℓ => allowedDigits A).image wordOfDigits

lemma card_allowedWords (A : Law) (ℓ : ℕ) :
    (allowedWords A ℓ).card = (allowedDigits A).card ^ ℓ := by
  have hinj : Function.Injective (wordOfDigits (A := A) (L := ℓ)) :=
    fun u v h => List.ofFn_injective h
  rw [allowedWords, Finset.card_image_of_injective _ hinj, Fintype.card_piFinset]
  simp

noncomputable def fullBranchingCoords (A : Law) (k₀ : ℕ) :
    Finset (Word A × (Fin A.arity)) :=
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
  {X : Word A → (Fin A.arity) → Ω → Bool}

lemma measure_fullBranching_pos (hX : IsPercolation P X) (k₀ : ℕ) :
    0 < P {ω | ∀ q ∈ fullBranchingCoords A k₀, X q.1 q.2 ω = true} := by
  rw [measure_forall_retained_eq_prod hX, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro q hq
  have hpos : 0 < A.p q.2 := by
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

def treeHits (E : ℕ → Set (Configuration A)) : Set (Configuration A) :=
  {x | ∃ᶠ n in atTop, ∃ v : Word A, v.length = n ∧ retainedBelowConfig x [] v ∧
    rebase v x ∈ E n}

theorem exists_measure_treeHits_ge (hX : IsPercolation P X) (hm : 1 < A.m) :
    ∃ α : ℝ≥0∞, 0 < α ∧ ∀ E : ℕ → Set (Configuration A), (∀ n, MeasurableSet (E n)) →
      ∀ K : ℕ → ℝ, (∀ n, 0 ≤ K n) → Summable K → ∑' n, K n ≤ 1 / 4 →
        ¬ Summable (fun n => K n * (P (config X ⁻¹' E n)).toReal * A.m ^ n) →
          α ≤ P (config X ⁻¹' treeHits E) := by
  classical
  let := hX.toIsProbabilityMeasure
  obtain ⟨k₀, hk₀⟩ := exists_explorationStart A hm
  set Φ := {ω | ∀ q ∈ fullBranchingCoords A k₀, X q.1 q.2 ω = true} with hΦ
  have hΦpos : 0 < (P Φ).toReal := ENNReal.toReal_pos (measure_fullBranching_pos hX k₀).ne'
    (measure_ne_top _ _)
  refine ⟨ENNReal.ofReal ((P Φ).toReal / 2), ENNReal.ofReal_pos.mpr (by positivity),
    fun E hE K hK0 hKsum hK4 hdiv => ?_⟩
  obtain ⟨hη, hcM, hS⟩ := hk₀ K hK0 hKsum hK4
  set c := explorationSize A K k₀ with hc
  set M := explorationThreshold A K k₀ with hM
  set good : ℕ → Set Ω := fun J => config X ⁻¹' exploreGood k₀ c M J with hgood
  have hgood_meas : ∀ J, MeasurableSet (good J) := fun J =>
    measurable_config hX (measurableSet_exploreGood k₀ c M J)
  have hgood_ge : ∀ J, ENNReal.ofReal ((P Φ).toReal / 2) ≤ P (good J) := by
    intro J
    have h1 := measure_exploreGood_ge hX hη hcM hS J
    have h2 := hS J
    rw [← ENNReal.ofReal_toReal (measure_ne_top P (good J))]
    refine ENNReal.ofReal_le_ofReal (le_trans ?_ h1)
    nlinarith
  set goodInf := ⋂ J, good J with hgoodInf
  have hgoodInf_ge : ENNReal.ofReal ((P Φ).toReal / 2) ≤ P goodInf := by
    have htend := tendsto_measure_iInter_atTop (μ := P)
      (fun J => (hgood_meas J).nullMeasurableSet)
      (fun J J' hJJ' => Set.preimage_mono (exploreGood_anti hJJ')) ⟨0, measure_ne_top _ _⟩
    exact ge_of_tendsto' htend fun J => hgood_ge J

  set p : ℕ → ℝ := fun j => (P (config X ⁻¹' E (k₀ + j))).toReal with hp
  have hp01 : ∀ j, 0 ≤ p j ∧ p j ≤ 1 := fun j => ⟨ENNReal.toReal_nonneg, by
    rw [hp, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one⟩

  have hfactor : ∀ j, (1 - P (config X ⁻¹' E (k₀ + j))) ^ c j ≤
      ENNReal.ofReal (Real.exp (-(p j * c j))) := by
    intro j
    have h1 : 1 - P (config X ⁻¹' E (k₀ + j)) ≤ ENNReal.ofReal (Real.exp (-p j)) := by
      rw [ENNReal.le_ofReal_iff_toReal_le (ENNReal.sub_ne_top ENNReal.one_ne_top)
        (Real.exp_pos _).le, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
        ENNReal.toReal_one]
      exact Real.one_sub_le_exp_neg _
    calc (1 - P (config X ⁻¹' E (k₀ + j))) ^ c j
        ≤ ENNReal.ofReal (Real.exp (-p j)) ^ c j := pow_le_pow_left₀ zero_le h1 _
      _ = ENNReal.ofReal (Real.exp (-(p j * c j))) := by
          rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
          congr 2
          ring
  have hdiv' : ∀ j₁, Tendsto (fun J => ∑ j ∈ Finset.Ico j₁ J, p j * c j) atTop atTop := by
    intro j₁
    have hnonneg : ∀ n, 0 ≤ K n * (P (config X ⁻¹' E n)).toReal * A.m ^ n := fun n =>
      mul_nonneg (mul_nonneg (hK0 n) ENNReal.toReal_nonneg) (pow_nonneg A.m_nonneg n)
    have hshift : ¬ Summable (fun i => K (i + (k₀ + j₁)) *
        (P (config X ⁻¹' E (i + (k₀ + j₁)))).toReal * A.m ^ (i + (k₀ + j₁))) := by
      rw [summable_nat_add_iff (f := fun n => K n * (P (config X ⁻¹' E n)).toReal * A.m ^ n)]
      exact hdiv
    have htend := (not_summable_iff_tendsto_nat_atTop_of_nonneg fun i => hnonneg _).mp hshift
    refine tendsto_atTop_mono' atTop ?_ (htend.comp (tendsto_sub_atTop_nat j₁))
    filter_upwards [eventually_ge_atTop j₁] with J hJ
    simp only [Function.comp]
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_le_sum fun i _ => ?_
    have hceil : K (k₀ + (j₁ + i)) * A.m ^ (k₀ + (j₁ + i)) ≤ c (j₁ + i) := Nat.le_ceil _
    have hidx : i + (k₀ + j₁) = k₀ + (j₁ + i) := by ring
    rw [hidx]
    calc K (k₀ + (j₁ + i)) * (P (config X ⁻¹' E (k₀ + (j₁ + i)))).toReal * A.m ^ (k₀ + (j₁ + i))
        = p (j₁ + i) * (K (k₀ + (j₁ + i)) * A.m ^ (k₀ + (j₁ + i))) := by rw [hp]; ring
      _ ≤ p (j₁ + i) * c (j₁ + i) := mul_le_mul_of_nonneg_left hceil (hp01 _).1
  have hmiss : ∀ j₁, P (goodInf ∩ {ω | ∀ j, j₁ ≤ j → ∀ v ∈ exploreA (config X ω) k₀ c j,
      rebase v (config X ω) ∉ E (k₀ + j)}) = 0 := by
    intro j₁
    have hlim : Tendsto (fun J => ENNReal.ofReal (Real.exp (-∑ j ∈ Finset.Ico j₁ J, p j * c j)))
        atTop (𝓝 0) := by
      have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hdiv' j₁)
      simpa [Function.comp_def] using ENNReal.tendsto_ofReal h
    refine le_antisymm (ge_of_tendsto' hlim fun J => ?_) zero_le
    · calc P (goodInf ∩ {ω | ∀ j, j₁ ≤ j → ∀ v ∈ exploreA (config X ω) k₀ c j,
            rebase v (config X ω) ∉ E (k₀ + j)})
          ≤ P (good J ∩ {ω | ∀ j, j₁ ≤ j → j < J → ∀ v ∈ exploreA (config X ω) k₀ c j,
            rebase v (config X ω) ∉ E (k₀ + j)}) := by
            refine measure_mono fun ω hω => ⟨Set.mem_iInter.mp hω.1 J, fun j hj _ => hω.2 j hj⟩
        _ ≤ ∏ j ∈ Finset.Ico j₁ J, (1 - P (config X ⁻¹' E (k₀ + j))) ^ c j :=
            measure_exploreGood_inter_miss_le hX hcM E hE j₁ J
        _ ≤ ∏ j ∈ Finset.Ico j₁ J, ENNReal.ofReal (Real.exp (-(p j * c j))) :=
            Finset.prod_le_prod fun j _ => hfactor j
        _ = ENNReal.ofReal (Real.exp (-∑ j ∈ Finset.Ico j₁ J, p j * c j)) := by
            rw [← ENNReal.ofReal_prod_of_nonneg fun j _ => (Real.exp_pos _).le, ← Real.exp_sum,
              Finset.sum_neg_distrib]

  have hsub : goodInf \ config X ⁻¹' treeHits E ⊆
      ⋃ j₁, goodInf ∩ {ω | ∀ j, j₁ ≤ j → ∀ v ∈ exploreA (config X ω) k₀ c j,
        rebase v (config X ω) ∉ E (k₀ + j)} := by
    rintro ω ⟨hgω, hnot⟩
    simp only [Set.mem_preimage, treeHits, Set.mem_ofPred_eq, Filter.not_frequently] at hnot
    obtain ⟨N, hN⟩ := eventually_atTop.mp hnot
    refine Set.mem_iUnion.mpr ⟨N, hgω, fun j hj v hv hvE => hN (k₀ + j) (by omega) ⟨v, ?_, ?_, hvE⟩⟩
    · exact (mem_exploreG (exploreA_subset _ _ _ _ hv)).1
    · exact (mem_exploreG (exploreA_subset _ _ _ _ hv)).2
  have hnull : P (goodInf \ config X ⁻¹' treeHits E) = 0 :=
    measure_mono_null hsub (measure_iUnion_null hmiss)
  calc ENNReal.ofReal ((P Φ).toReal / 2) ≤ P goodInf := hgoodInf_ge
    _ ≤ P (goodInf ∩ config X ⁻¹' treeHits E) + P (goodInf \ config X ⁻¹' treeHits E) :=
        measure_le_inter_add_sdiff _ _ _
    _ = P (goodInf ∩ config X ⁻¹' treeHits E) := by rw [hnull, add_zero]
    _ ≤ P (config X ⁻¹' treeHits E) := measure_mono Set.inter_subset_right

end FractalGeometry.Probability.Branching
