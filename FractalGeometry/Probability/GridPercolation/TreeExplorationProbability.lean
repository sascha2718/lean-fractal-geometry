import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.BlockIndependence
import FractalGeometry.Probability.GridPercolation.ColumnOffspring
import FractalGeometry.Probability.GridPercolation.Configuration
import FractalGeometry.Probability.GridPercolation.GenerationConditioning
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.LawInvariance
import FractalGeometry.Probability.GridPercolation.OffspringHoeffding
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.RootIndependence
import FractalGeometry.Probability.GridPercolation.SecondMoments
import FractalGeometry.Probability.GridPercolation.ShallowEvents
import FractalGeometry.Probability.GridPercolation.TreeExploration

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal

variable {A : GridLaw}

lemma measurableSet_of_shallow_congr (ℓ : ℕ) {S : Set (Configuration A)}
    (hS : ∀ x y : Configuration A,
      (∀ q : Word A × (Fin A.M × Fin A.N), q.1.length < ℓ → x q = y q) → x ∈ S → y ∈ S) :
    MeasurableSet S := by
  classical
  have : Finite {u : Word A // u.length < ℓ} := (List.finite_length_lt _ ℓ).to_subtype
  have hset : S = (fun x : Configuration A => fun j : ShallowCoord A ℓ => x (j.1.1, j.2)) ⁻¹'
      (shallowExtend ℓ ⁻¹' S) := by
    ext x
    simp only [Set.mem_preimage]
    constructor
    · refine hS x _ fun q hq => ?_
      simp [shallowExtend, hq]
    · refine hS _ x fun q hq => ?_
      simp [shallowExtend, hq]
  rw [hset]
  exact (Measurable.of_eval fun j => measurable_pi_apply _) (Set.to_countable _).measurableSet

lemma length_lt_of_mem_exploreRegion {x : Configuration A} {k₀ : ℕ} {c : ℕ → ℕ} {J : ℕ}
    {q : Word A × (Fin A.M × Fin A.N)} (hq : q ∈ exploreRegion x k₀ c J) :
    q.1.length < k₀ + J := by
  simp only [exploreRegion, exploreRegionOf, Set.mem_ofPred_eq] at hq
  rcases hq with h | ⟨j, hj, hmem⟩
  · omega
  · have := (mem_exploreG (Finset.mem_sdiff.mp hmem).1).1
    omega

lemma exploreG_congr_shallow {x y : Configuration A} {k₀ : ℕ} {c : ℕ → ℕ} {J : ℕ}
    (hxy : ∀ q : Word A × (Fin A.M × Fin A.N), q.1.length < k₀ + J → x q = y q) :
    ∀ j ≤ J, exploreG y k₀ c j = exploreG x k₀ c j :=
  exploreG_congr fun q hq => (hxy q (length_lt_of_mem_exploreRegion hq)).symm

lemma offspringConfig_config {Ω : Type*}
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (ω : Ω) (w : Word A) :
    offspringConfig (config X ω) w = totalOffspring X w ω := by
  classical
  unfold offspringConfig totalOffspring
  rw [Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [columnOffspring_eq_sum]
  rfl

def exploreGood (k₀ : ℕ) (c : ℕ → ℕ) (M : ℕ → ℝ) (J : ℕ) : Set (Configuration A) :=
  {x | ∀ j ≤ J, M j ≤ (exploreG x k₀ c j).card}

lemma exploreGood_anti {k₀ : ℕ} {c : ℕ → ℕ} {M : ℕ → ℝ} {J J' : ℕ} (h : J ≤ J') :
    exploreGood (A := A) k₀ c M J' ⊆ exploreGood k₀ c M J :=
  fun _ hx j hj => hx j (hj.trans h)

lemma measurableSet_exploreGood (k₀ : ℕ) (c : ℕ → ℕ) (M : ℕ → ℝ) (J : ℕ) :
    MeasurableSet (exploreGood (A := A) k₀ c M J) :=
  measurableSet_of_shallow_congr (k₀ + J) fun x y hxy hx j hj => by
    rw [exploreG_congr_shallow hxy j hj]
    exact hx j hj

lemma measurableSet_exploreG_eq (k₀ : ℕ) (c : ℕ → ℕ) (J : ℕ) (s : Finset (Word A)) :
    MeasurableSet {x : Configuration A | exploreG x k₀ c J = s} :=
  measurableSet_of_shallow_congr (k₀ + J) fun x y hxy hx => by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [exploreG_congr_shallow hxy J le_rfl]
    exact hx

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

theorem measure_exploreGood_diff_le (hX : IsPercolation P X) {k₀ : ℕ} {c : ℕ → ℕ}
    {M : ℕ → ℝ} {J : ℕ} {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hcM : (c J : ℝ) ≤ M J)
    (hMsucc : M (J + 1) ≤ (1 - η) * A.m * (M J - c J)) :
    P (config X ⁻¹' exploreGood k₀ c M J \ config X ⁻¹' exploreGood k₀ c M (J + 1)) ≤
      ENNReal.ofReal (Real.exp (-(2 * η ^ 2 * A.m ^ 2 * (M J - c J) / ((A.M : ℝ) * A.N) ^ 2))) *
        P (config X ⁻¹' exploreGood k₀ c M J) := by
  classical
  let := hX.toIsProbabilityMeasure
  set e := ENNReal.ofReal (Real.exp (-(2 * η ^ 2 * A.m ^ 2 * (M J - c J) /
    ((A.M : ℝ) * A.N) ^ 2))) with he
  set good := config X ⁻¹' exploreGood k₀ c M J with hgood
  set bad := config X ⁻¹' exploreGood k₀ c M (J + 1) with hbad
  set slice : Finset (Word A) → Set Ω :=
    fun s => good ∩ config X ⁻¹' {x | exploreG x k₀ c J = s} with hslice
  have hslice_meas : ∀ s, MeasurableSet (slice s) := fun s =>
    (measurable_config hX (measurableSet_exploreGood k₀ c M J)).inter
      (measurable_config hX (measurableSet_exploreG_eq k₀ c J s))
  have hdisj : Pairwise (Function.onFun Disjoint slice) := by
    intro s t hst
    rw [Function.onFun, Set.disjoint_left]
    intro ω hs ht
    exact hst (hs.2.symm.trans ht.2)
  have hunion : ⋃ s, slice s = good := by
    ext ω
    simp only [hslice, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨_, h, rfl⟩⟩
  have hbound : ∀ s, P (slice s \ bad) ≤ e * P (slice s) := by
    intro s
    rcases (slice s \ bad).eq_empty_or_nonempty with hempty | ⟨ω₀, ⟨hω₀good, hω₀s⟩, -⟩
    · rw [hempty, measure_empty]
      exact zero_le
    have hs : exploreG (config X ω₀) k₀ c J = s := hω₀s
    have hs_len : ∀ w ∈ s, w.length = k₀ + J := fun w hw => by
      rw [← hs] at hw
      exact (mem_exploreG hw).1
    have hMs : M J ≤ s.card := by
      have := hω₀good J le_rfl
      rwa [hs] at this
    have hcs : c J ≤ s.card := by exact_mod_cast hcM.trans hMs
    set T := s \ chooseSubset s (c J) with hT
    have hTcard : (T.card : ℝ) = s.card - c J := by
      rw [hT, Finset.card_sdiff_of_subset (chooseSubset_subset s (c J)), chooseSubset_card hcs,
        Nat.cast_sub hcs]

    let f : ShallowCoord A (k₀ + J) → Word A × (Fin A.M × Fin A.N) := fun j => (j.1.1, j.2)
    let g : {w // w ∈ T} × (Fin A.M × Fin A.N) → Word A × (Fin A.M × Fin A.N) :=
      fun p => (p.1.1, p.2)
    have hf : Function.Injective f := by
      rintro ⟨⟨u, hu⟩, a⟩ ⟨⟨u', hu'⟩, a'⟩ h
      simp only [f, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    have hg : Function.Injective g := by
      rintro ⟨⟨w, hw⟩, a⟩ ⟨⟨w', hw'⟩, a'⟩ h
      simp only [g, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    have hfg : ∀ i j, f i ≠ g j := by
      rintro ⟨⟨u, hu⟩, a⟩ ⟨⟨w, hw⟩, b⟩ h
      simp only [f, g, Prod.mk.injEq] at h
      have hwlen := hs_len w (Finset.mem_sdiff.mp hw).1
      rw [← h.1] at hwlen
      omega
    have hind := iIndepFun.indepFun_coordinateBlocks (Z := fun q ω => X q.1 q.2 ω)
      (fun q => hX.measurable q.1 q.2) hX.indep f g hf hg hfg

    have : Finite {u : Word A // u.length < k₀ + J} :=
      (List.finite_length_lt _ (k₀ + J)).to_subtype
    set S₁ : Set (ShallowCoord A (k₀ + J) → Bool) :=
      {v | shallowExtend (k₀ + J) v ∈ exploreGood k₀ c M J ∧
        exploreG (shallowExtend (k₀ + J) v) k₀ c J = s} with hS₁
    have hslice_eq : slice s = (fun ω i => X (f i).1 (f i).2 ω) ⁻¹' S₁ := by
      ext ω
      have hagree : ∀ q : Word A × (Fin A.M × Fin A.N), q.1.length < k₀ + J →
          config X ω q = shallowExtend (k₀ + J) (fun i => X (f i).1 (f i).2 ω) q := by
        intro q hq
        simp [shallowExtend, hq, f, config]
      have hG := exploreG_congr_shallow (c := c) hagree
      simp only [hslice, hS₁, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, exploreGood]
      constructor
      · rintro ⟨hgoodω, hsω⟩
        exact ⟨fun j hj => by rw [hG j hj]; exact hgoodω j hj, by rw [hG J le_rfl]; exact hsω⟩
      · rintro ⟨hgoodω, hsω⟩
        exact ⟨fun j hj => by rw [← hG j hj]; exact hgoodω j hj, by rw [← hG J le_rfl]; exact hsω⟩

    set S₂ : Set ({w // w ∈ T} × (Fin A.M × Fin A.N) → Bool) :=
      {v | (∑ w : {w // w ∈ T},
        (((Finset.univ : Finset (Fin A.M × Fin A.N)).filter fun a => v (w, a) = true).card : ℝ))
          ≤ (1 - η) * A.m * T.card} with hS₂
    set hoeff := {ω | (∑ w ∈ T, (totalOffspring X w ω : ℝ)) ≤ (1 - η) * A.m * T.card}
      with hhoeff
    have hhoeff_eq : hoeff = (fun ω j => X (g j).1 (g j).2 ω) ⁻¹' S₂ := by
      ext ω
      simp only [hhoeff, hS₂, Set.mem_preimage, Set.mem_ofPred_eq, g]
      rw [← Finset.sum_coe_sort T]
      refine iff_of_eq (congrArg (· ≤ _) (Finset.sum_congr rfl fun w _ => ?_))
      rw [← offspringConfig_config X ω w]
      rfl

    have hsub : slice s \ bad ⊆ slice s ∩ hoeff := by
      rintro ω ⟨⟨hgoodω, hsω⟩, hbadω⟩
      refine ⟨⟨hgoodω, hsω⟩, ?_⟩
      have hsω' : exploreG (config X ω) k₀ c J = s := hsω
      have hfail : ¬ M (J + 1) ≤ (exploreG (config X ω) k₀ c (J + 1)).card := by
        intro hsucc
        refine hbadω fun j hj => ?_
        rcases Nat.lt_or_ge j (J + 1) with hlt | hge
        · exact hgoodω j (Nat.lt_succ_iff.mp hlt)
        · rw [show j = J + 1 by omega]
          exact hsucc
      have hchildren : (exploreG (config X ω) k₀ c (J + 1)).card =
          ∑ w ∈ T, totalOffspring X w ω := by
        rw [exploreG_succ, card_childrenConfig]
        simp only [exploreA, hsω', hT]
        exact Finset.sum_congr rfl fun w _ => offspringConfig_config X ω w
      rw [hchildren] at hfail
      push Not at hfail
      simp only [hhoeff, Set.mem_ofPred_eq]
      have hm0 : 0 ≤ (1 - η) * A.m := mul_nonneg (by linarith) A.m_nonneg
      calc (∑ w ∈ T, (totalOffspring X w ω : ℝ)) = ((∑ w ∈ T, totalOffspring X w ω : ℕ) : ℝ) := by
            push_cast; rfl
        _ ≤ M (J + 1) := hfail.le
        _ ≤ (1 - η) * A.m * (M J - c J) := hMsucc
        _ ≤ (1 - η) * A.m * T.card := by
            refine mul_le_mul_of_nonneg_left ?_ hm0
            rw [hTcard]
            linarith
    have hS₁meas : MeasurableSet S₁ := (Set.to_countable _).measurableSet
    have hS₂meas : MeasurableSet S₂ := (Set.to_countable _).measurableSet
    have hprod : P (slice s ∩ hoeff) = P (slice s) * P hoeff := by
      rw [hslice_eq, hhoeff_eq]
      exact hind.measure_inter_preimage_eq_mul _ _ hS₁meas hS₂meas
    have hhoeff_le : P hoeff ≤ e := by
      refine (measure_sum_totalOffspring_le hX T hη0).trans (ENNReal.ofReal_le_ofReal ?_)
      refine Real.exp_le_exp.mpr ?_
      have hMN : 0 < ((A.M : ℝ) * A.N) ^ 2 := by
        have : (0 : ℝ) < A.M := by exact_mod_cast A.hM_pos
        have : (0 : ℝ) < A.N := by exact_mod_cast A.hN_pos
        positivity
      rw [neg_le_neg_iff, div_le_div_iff_of_pos_right hMN]
      have hk : 0 ≤ 2 * η ^ 2 * A.m ^ 2 := by positivity
      refine mul_le_mul_of_nonneg_left ?_ hk
      rw [hTcard]
      linarith
    calc P (slice s \ bad) ≤ P (slice s ∩ hoeff) := measure_mono hsub
      _ = P (slice s) * P hoeff := hprod
      _ ≤ P (slice s) * e := by gcongr
      _ = e * P (slice s) := mul_comm _ _
  calc P (good \ bad) = P (⋃ s, (slice s \ bad)) := by
        rw [← Set.iUnion_sdiff, hunion]
    _ ≤ ∑' s, P (slice s \ bad) := measure_iUnion_le _
    _ ≤ ∑' s, e * P (slice s) := ENNReal.tsum_le_tsum hbound
    _ = e * ∑' s, P (slice s) := ENNReal.tsum_mul_left
    _ = e * P good := by rw [← measure_iUnion hdisj hslice_meas, hunion]

end FractalGeometry.Probability.GridPercolation
