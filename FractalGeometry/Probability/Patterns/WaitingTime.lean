import Mathlib
import FractalGeometry.Probability.Patterns.Defs
import FractalGeometry.Probability.Patterns.IndependentWords
import FractalGeometry.Probability.Patterns.Weights
import FractalGeometry.Probability.Patterns.WordProbability

namespace FractalGeometry.Probability.Patterns

open MeasureTheory ProbabilityTheory Finset

open scoped ENNReal

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace Ω]

def blockFrom (I : ℕ → Ω → ι) (s t : ℕ) (ω : Ω) : Word ι t := fun i => I (s + 1 + i) ω

theorem block_eq_blockFrom (I : ℕ → Ω → ι) (m k : ℕ) (ω : Ω) :
    block I m k ω = blockFrom I (k - m) m ω := rfl

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Ω] in

theorem blockFrom_eq_iff (I : ℕ → Ω → ι) (s t : ℕ) (w : Word ι t) (ω : Ω) :
    blockFrom I s t ω = w ↔ ∀ i : Fin t, I (s + 1 + i) ω = w i := by
  constructor
  · intro h i; rw [← h]; rfl
  · intro h; funext i; exact h i

def subword {t : ℕ} (W : Word ι t) (a m : ℕ) (h : a + m ≤ t) : Word ι m :=
  fun i => W ⟨a + i, by omega⟩

def WordNoOcc {t : ℕ} (W : Word ι t) (m : ℕ) (U : Finset (Word ι m)) : Prop :=
  ∀ k, m ≤ k → k ≤ t → ∀ h : k - m + m ≤ t, subword W (k - m) m h ∉ U

def NoOccIn (I : ℕ → Ω → ι) (m : ℕ) (U : Finset (Word ι m)) (k₀ L : ℕ) (ω : Ω) : Prop :=
  ∀ k, k₀ ≤ k → k ≤ L → block I m k ω ∉ U

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Ω] in

theorem noOccIn_iff_wordNoOcc (I : ℕ → Ω → ι) (m : ℕ) (U : Finset (Word ι m)) (s t : ℕ)
    (ω : Ω) : NoOccIn I m U (s + m) (s + t) ω ↔ WordNoOcc (blockFrom I s t ω) m U := by
  have key1 : ∀ k, m ≤ k → k ≤ t → ∀ h : k - m + m ≤ t,
      block I m (s + k) ω = subword (blockFrom I s t ω) (k - m) m h := by
    intro k hk1 hk2 h
    funext i
    simp only [block, subword, blockFrom]
    congr 1
    omega
  have key2 : ∀ k, s + m ≤ k → k ≤ s + t → ∀ h : k - s - m + m ≤ t,
      block I m k ω = subword (blockFrom I s t ω) (k - s - m) m h := by
    intro k hk1 hk2 h
    funext i
    simp only [block, subword, blockFrom]
    congr 1
    omega
  constructor
  · intro hno k hk1 hk2 h
    rw [← key1 k hk1 hk2 h]
    exact hno (s + k) (by omega) (by omega)
  · intro hW k hk1 hk2
    rw [key2 k hk1 hk2 (by omega)]
    exact hW (k - s) (by omega) (by omega) _

section Law

variable {p : Weights ι} {P : Measure Ω} {I : ℕ → Ω → ι} (hI : IsIIDProcess p P I)

include hI

omit [MeasurableSingletonClass ι] in

theorem IsIIDProcess.measurable_blockFrom (s t : ℕ) : Measurable (blockFrom I s t) :=
  measurable_pi_iff.mpr fun _ => hI.measurable _

omit hI [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in

theorem prod_Ico_wordAt [Nonempty ι] (f : ι → ℝ≥0∞) (s t : ℕ) (w : Word ι t) :
    ∏ j ∈ Ico (s + 1) (s + t + 1), f (wordAt (s + 1) w j) = ∏ i, f (w i) := by
  rw [prod_Ico_eq_prod_range, show s + t + 1 - (s + 1) = t by omega, ← Fin.prod_univ_eq_prod_range]
  exact prod_congr rfl fun i _ => by rw [wordAt_apply]

theorem IsIIDProcess.measure_blockFrom_eq [Nonempty ι] (s t : ℕ) (w : Word ι t) :
    P {ω | blockFrom I s t ω = w} = ENNReal.ofReal (p.wordProb w) := by
  have hset : {ω | blockFrom I s t ω = w}
      = {ω | ∀ j ∈ Ico (s + 1) (s + t + 1), I j ω = wordAt (s + 1) w j} := by
    ext ω
    simp only [Set.mem_setOf_eq, blockFrom_eq_iff, mem_Ico]
    constructor
    · rintro h j ⟨hj1, hj2⟩
      have hi : j - (s + 1) < t := by omega
      have := h ⟨j - (s + 1), hi⟩
      rw [show s + 1 + (j - (s + 1)) = j by omega] at this
      rw [this, ← wordAt_apply (s + 1) w ⟨j - (s + 1), hi⟩]
      congr 1
      simp only
      omega
    · intro h i
      rw [h (s + 1 + i) ⟨by omega, by omega⟩, wordAt_apply]
  rw [hset, hI.measure_cylinder, prod_Ico_wordAt (fun i => ENNReal.ofReal (p.p i)),
    Weights.wordProb, ENNReal.ofReal_prod_of_nonneg fun i _ => (p.pos _).le]

theorem IsIIDProcess.measure_blockFrom_and [Nonempty ι] {s₁ t₁ s₂ t₂ : ℕ} (h : s₁ + t₁ ≤ s₂)
    (w₁ : Word ι t₁) (w₂ : Word ι t₂) :
    P {ω | blockFrom I s₁ t₁ ω = w₁ ∧ blockFrom I s₂ t₂ ω = w₂}
      = ENNReal.ofReal (p.wordProb w₁) * ENNReal.ofReal (p.wordProb w₂) := by
  classical
  let a : ℕ → ι := fun j => if j ≤ s₁ + t₁ then wordAt (s₁ + 1) w₁ j else wordAt (s₂ + 1) w₂ j
  let S₁ := Ico (s₁ + 1) (s₁ + t₁ + 1)
  let S₂ := Ico (s₂ + 1) (s₂ + t₂ + 1)
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [S₁, S₂, mem_Ico] at hj1 hj2
    omega
  have hset : {ω | blockFrom I s₁ t₁ ω = w₁ ∧ blockFrom I s₂ t₂ ω = w₂}
      = {ω | ∀ j ∈ S₁ ∪ S₂, I j ω = a j} := by
    ext ω
    simp only [Set.mem_setOf_eq, blockFrom_eq_iff, mem_union, S₁, S₂, mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases hj with hj | hj
      · have hi : j - (s₁ + 1) < t₁ := by omega
        have := h1 ⟨j - (s₁ + 1), hi⟩
        rw [show s₁ + 1 + (j - (s₁ + 1)) = j by omega] at this
        simp only [a, if_pos (by omega : j ≤ s₁ + t₁)]
        rw [this, ← wordAt_apply (s₁ + 1) w₁ ⟨j - (s₁ + 1), hi⟩]
        congr 1
        simp only
        omega
      · have hi : j - (s₂ + 1) < t₂ := by omega
        have := h2 ⟨j - (s₂ + 1), hi⟩
        rw [show s₂ + 1 + (j - (s₂ + 1)) = j by omega] at this
        simp only [a, if_neg (by omega : ¬ j ≤ s₁ + t₁)]
        rw [this, ← wordAt_apply (s₂ + 1) w₂ ⟨j - (s₂ + 1), hi⟩]
        congr 1
        simp only
        omega
    · intro hall
      refine ⟨fun i => ?_, fun i => ?_⟩
      · rw [hall (s₁ + 1 + i) (Or.inl ⟨by omega, by omega⟩)]
        simp only [a, if_pos (by omega : s₁ + 1 + (i : ℕ) ≤ s₁ + t₁)]
        exact wordAt_apply _ _ _
      · rw [hall (s₂ + 1 + i) (Or.inr ⟨by omega, by omega⟩)]
        simp only [a, if_neg (by omega : ¬ s₂ + 1 + (i : ℕ) ≤ s₁ + t₁)]
        exact wordAt_apply _ _ _
  rw [hset, hI.measure_cylinder, prod_union hdisj]
  congr 1
  · rw [Weights.wordProb, ENNReal.ofReal_prod_of_nonneg fun i _ => (p.pos _).le,
      ← prod_Ico_wordAt (fun i => ENNReal.ofReal (p.p i)) s₁ t₁ w₁]
    refine prod_congr rfl fun j hj => ?_
    simp only [mem_Ico] at hj
    simp only [a, if_pos (by omega : j ≤ s₁ + t₁)]
  · rw [Weights.wordProb, ENNReal.ofReal_prod_of_nonneg fun i _ => (p.pos _).le,
      ← prod_Ico_wordAt (fun i => ENNReal.ofReal (p.p i)) s₂ t₂ w₂]
    refine prod_congr rfl fun j hj => ?_
    simp only [mem_Ico] at hj
    simp only [a, if_neg (by omega : ¬ j ≤ s₁ + t₁)]

theorem IsIIDProcess.measure_window [Nonempty ι] (s t : ℕ) (Q : Word ι t → Prop)
    [DecidablePred Q] :
    P {ω | Q (blockFrom I s t ω)} = ∑ w ∈ univ.filter Q, ENNReal.ofReal (p.wordProb w) := by
  classical
  have hset : {ω | Q (blockFrom I s t ω)} = ⋃ w ∈ univ.filter Q, {ω | blockFrom I s t ω = w} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, mem_filter, mem_univ, true_and, exists_prop]
    constructor
    · intro h; exact ⟨blockFrom I s t ω, h, rfl⟩
    · rintro ⟨w, hw, rfl⟩; exact hw
  rw [hset, measure_biUnion_finset]
  · exact sum_congr rfl fun w _ => hI.measure_blockFrom_eq s t w
  · intro w _ w' _ hww'
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    exact hww' (h1.symm.trans h2)
  · intro w _
    exact (hI.measurable_blockFrom s t) (measurableSet_singleton w)

theorem IsIIDProcess.measure_window_and [Nonempty ι] {s₁ t₁ s₂ t₂ : ℕ} (h : s₁ + t₁ ≤ s₂)
    (Q₁ : Word ι t₁ → Prop) [DecidablePred Q₁] (Q₂ : Word ι t₂ → Prop) [DecidablePred Q₂] :
    P {ω | Q₁ (blockFrom I s₁ t₁ ω) ∧ Q₂ (blockFrom I s₂ t₂ ω)}
      = P {ω | Q₁ (blockFrom I s₁ t₁ ω)} * P {ω | Q₂ (blockFrom I s₂ t₂ ω)} := by
  classical
  have hset : {ω | Q₁ (blockFrom I s₁ t₁ ω) ∧ Q₂ (blockFrom I s₂ t₂ ω)}
      = ⋃ q ∈ (univ.filter Q₁) ×ˢ (univ.filter Q₂),
          {ω | blockFrom I s₁ t₁ ω = q.1 ∧ blockFrom I s₂ t₂ ω = q.2} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, mem_product, mem_filter, mem_univ, true_and,
      exists_prop, Prod.exists]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨_, _, ⟨h1, h2⟩, rfl, rfl⟩
    · rintro ⟨w₁, w₂, ⟨h1, h2⟩, rfl, rfl⟩; exact ⟨h1, h2⟩
  rw [hset, measure_biUnion_finset, hI.measure_window, hI.measure_window, sum_mul_sum,
    sum_product]
  · exact sum_congr rfl fun w₁ _ => sum_congr rfl fun w₂ _ => hI.measure_blockFrom_and h w₁ w₂
  · intro q _ q' _ hqq'
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨h1, h2⟩ ⟨h1', h2'⟩
    exact hqq' (Prod.ext (h1.symm.trans h1') (h2.symm.trans h2'))
  · intro q _
    exact ((hI.measurable_blockFrom s₁ t₁) (measurableSet_singleton q.1)).inter
      ((hI.measurable_blockFrom s₂ t₂) (measurableSet_singleton q.2))

end Law

section Hitting

variable (p : Weights ι) (m : ℕ) (U : Finset (Word ι m))

noncomputable def Weights.avoidProb (t : ℕ) : ℝ := by
  classical exact ∑ W ∈ (univ : Finset (Word ι t)).filter (fun W => WordNoOcc W m U), p.wordProb W

variable {p m U}

variable {P : Measure Ω} {I : ℕ → Ω → ι} (hI : IsIIDProcess p P I)

include hI

theorem IsIIDProcess.measure_noOcc [Nonempty ι] (L : ℕ) :
    P {ω | NoOcc I m U L ω} = ENNReal.ofReal (p.avoidProb m U L) := by
  classical
  have : {ω | NoOcc I m U L ω} = {ω | WordNoOcc (blockFrom I 0 L ω) m U} := by
    ext ω
    change NoOcc I m U L ω ↔ WordNoOcc (blockFrom I 0 L ω) m U
    have h := noOccIn_iff_wordNoOcc I m U 0 L ω
    rw [zero_add, zero_add] at h
    exact h
  rw [this, hI.measure_window 0 L (fun W => WordNoOcc W m U), Weights.avoidProb,
    ENNReal.ofReal_sum_of_nonneg fun W _ => (p.wordProb_pos W).le]

theorem IsIIDProcess.measure_noOccIn [Nonempty ι] (s t : ℕ) :
    P {ω | NoOccIn I m U (s + m) (s + t) ω} = ENNReal.ofReal (p.avoidProb m U t) := by
  classical
  have : {ω | NoOccIn I m U (s + m) (s + t) ω} = {ω | WordNoOcc (blockFrom I s t ω) m U} := by
    ext ω
    exact noOccIn_iff_wordNoOcc I m U s t ω
  rw [this, hI.measure_window s t (fun W => WordNoOcc W m U), Weights.avoidProb,
    ENNReal.ofReal_sum_of_nonneg fun W _ => (p.wordProb_pos W).le]

theorem IsIIDProcess.measurableSet_noOccIn (k₀ L : ℕ) :
    MeasurableSet {ω | NoOccIn I m U k₀ L ω} := by
  have : {ω | NoOccIn I m U k₀ L ω} = ⋂ k ∈ Finset.Icc k₀ L, (block I m k) ⁻¹' (↑U)ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_Icc, Set.mem_preimage,
      Set.mem_compl_iff, Finset.mem_coe, NoOccIn]
    exact ⟨fun h k hk => h k hk.1 hk.2, fun h k hk1 hk2 => h k ⟨hk1, hk2⟩⟩
  rw [this]
  refine MeasurableSet.biInter (Finset.countable_toSet _) fun k _ => ?_
  exact (measurable_pi_iff.mpr fun i => hI.measurable _) (U.finite_toSet.measurableSet.compl)

omit hI [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Ω] in

theorem lt_hittingTime_iff (L : ℕ) (ω : Ω) :
    (L : ℕ∞) < hittingTime I m U ω ↔ NoOcc I m U L ω := by
  unfold hittingTime NoOcc
  rw [← ENat.add_one_le_iff (ENat.coe_ne_top L), le_iInf_iff]
  constructor
  · intro h k hk1 hk2 hmem
    have := h k
    rw [le_iInf_iff] at this
    have := this hk1
    rw [le_iInf_iff] at this
    have := this hmem
    have hlt : (L : ℕ∞) < k := by
      rw [← ENat.add_one_le_iff (ENat.coe_ne_top L)]
      exact this
    exact absurd (ENat.coe_lt_coe.mp hlt) (by omega)
  · intro h k
    rw [le_iInf_iff]
    intro hk1
    rw [le_iInf_iff]
    intro hmem
    by_contra hlt
    push Not at hlt
    have hkL : k ≤ L := by
      have h' : (k : ℕ∞) < ((L + 1 : ℕ) : ℕ∞) := by push_cast; exact hlt
      have := ENat.coe_lt_coe.mp h'
      omega
    exact h k hk1 hkL hmem

omit hI [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Ω] in

theorem hittingTime_ge (ω : Ω) : (m : ℕ∞) ≤ hittingTime I m U ω := by
  unfold hittingTime
  exact le_iInf fun k => le_iInf fun hk => le_iInf fun _ => by exact_mod_cast hk

omit hI in

theorem ENat.toENNReal_eq_tsum (x : ℕ∞) :
    (x : ℝ≥0∞) = ∑' t : ℕ, if (t : ℕ∞) < x then 1 else 0 := by
  induction x using ENat.recTopCoe with
  | top =>
    simp only [ENat.toENNReal_top, ENat.coe_lt_top, if_true]
    exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
  | coe n =>
    rw [ENat.toENNReal_coe, tsum_eq_sum (s := Finset.range n) (fun t ht => by
      rw [Finset.mem_range, not_lt] at ht
      simp [not_lt.mpr (ENat.coe_le_coe.mpr ht)])]
    rw [Finset.sum_ite_of_true (fun t ht => by
      rw [Finset.mem_range] at ht; exact ENat.coe_lt_coe.mpr ht)]
    simp

theorem IsIIDProcess.measurableSet_noOcc (t : ℕ) : MeasurableSet {ω | NoOcc I m U t ω} :=
  hI.measurableSet_noOccIn (m := m) (U := U) m t

theorem IsIIDProcess.expectedHitting_eq_tsum :
    expectedHitting P I m U = ∑' t : ℕ, P {ω | NoOcc I m U t ω} := by
  classical
  unfold expectedHitting
  have h : ∀ ω, (hittingTime I m U ω : ℝ≥0∞)
      = ∑' t : ℕ, {ω | NoOcc I m U t ω}.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω
    rw [ENat.toENNReal_eq_tsum]
    refine tsum_congr fun t => ?_
    by_cases hω : NoOcc I m U t ω
    · rw [if_pos ((lt_hittingTime_iff t ω).mpr hω), Set.indicator_of_mem hω]
    · rw [if_neg (fun h' => hω ((lt_hittingTime_iff t ω).mp h')), Set.indicator_of_notMem hω]
  simp_rw [h]
  rw [lintegral_tsum fun t => (measurable_const.indicator (hI.measurableSet_noOcc t)).aemeasurable]
  refine tsum_congr fun t => ?_
  exact lintegral_indicator_one (hI.measurableSet_noOcc t)

end Hitting

end FractalGeometry.Probability.Patterns
