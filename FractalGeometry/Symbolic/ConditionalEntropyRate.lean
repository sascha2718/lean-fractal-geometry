import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.SelfAffine.Filtration
import FractalGeometry.Symbolic.BlockEntropyBounds
import FractalGeometry.Symbolic.Conditional
import FractalGeometry.Symbolic.ConditionalMeasures
import FractalGeometry.Symbolic.ConditionalRefinement
import FractalGeometry.Symbolic.Conditioning
import FractalGeometry.Symbolic.Disintegration
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.Information
import FractalGeometry.Symbolic.Past
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal

universe u

section General

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

omit [Fintype α] in

theorem measurableSet_zeroCyl (a : α) : MeasurableSet {y : ℤ → α | y 0 = a} :=
  show MeasurableSet ((fun y : ℤ → α => y 0) ⁻¹' {a}) from
    measurable_pi_apply (0 : ℤ) (measurableSet_singleton a)

def refineZero (ξ : (ℤ → α) → Set (ℤ → α)) (x : ℤ → α) : Set (ℤ → α) :=
  ξ x ∩ {y | y 0 = x 0}

def pullShift (ξ : (ℤ → α) → Set (ℤ → α)) (x : ℤ → α) : Set (ℤ → α) :=
  shift 1 ⁻¹' ξ (shift 1 x)

theorem isMeasurablePartition_refineZero {ξ : (ℤ → α) → Set (ℤ → α)}
    (hξ : IsMeasurablePartition ξ) : IsMeasurablePartition (refineZero ξ) := by
  obtain ⟨f, hf, hfξ⟩ := hξ
  have he := MeasureTheory.measurableEmbedding_embeddingReal (ℝ × α)
  refine ⟨fun x => MeasureTheory.embeddingReal (ℝ × α) (f x, x 0),
    he.measurable.comp (hf.prodMk (measurable_pi_apply 0)), fun x y => ?_⟩
  simp only [refineZero, mem_inter_iff, mem_ofPred_eq, he.injective.eq_iff, Prod.mk.injEq, hfξ]

theorem exists_saturated_inter_zeroCyl {ξ : (ℤ → α) → Set (ℤ → α)} {f : (ℤ → α) → ℝ}
    (hf : Measurable f) (hfξ : ∀ x y, y ∈ ξ x ↔ f y = f x) {B : Set (ℤ → α)}
    (hB : MeasurableSet[saturated (refineZero ξ)] B) (a : α) :
    ∃ B', MeasurableSet[saturated ξ] B' ∧ B ∩ {y | y 0 = a} = B' ∩ {y | y 0 = a} := by
  have hG : Measurable fun x : ℤ → α => (f x, x 0) := hf.prodMk (measurable_pi_apply 0)
  have hGξ : ∀ x y, y ∈ refineZero ξ x ↔ (f y, y 0) = (f x, x 0) := fun x y => by
    simp only [refineZero, mem_inter_iff, mem_ofPred_eq, Prod.mk.injEq, hfξ]
  rw [saturated_eq_comap hG hGξ] at hB
  obtain ⟨U, hU, rfl⟩ := hB
  refine ⟨f ⁻¹' ((fun r => (r, a)) ⁻¹' U),
    ⟨hf (measurable_prodMk_right hU), fun x y hxy => ?_⟩, ?_⟩
  · simp only [mem_preimage, (hfξ x y).1 hxy]
  · ext x
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, rfl⟩
    · rintro ⟨h, rfl⟩
      exact ⟨h, rfl⟩

theorem condMeas_refineZero (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ]
    {ξ : (ℤ → α) → Set (ℤ → α)} (hξ : IsMeasurablePartition ξ) :
    ∀ᵐ x ∂μ, condMeas μ (refineZero ξ) x = (condMeas μ ξ x)[|{y | y 0 = x 0}] := by
  classical
  obtain ⟨f, hf, hfξ⟩ := hξ
  set C : α → Set (ℤ → α) := fun a => {y | y 0 = a} with hC
  have hCm : ∀ a, MeasurableSet (C a) := measurableSet_zeroCyl
  have hle : saturated ξ ≤ saturated (refineZero ξ) :=
    saturated_mono fun x => inter_subset_left
  have hCsat : ∀ a, MeasurableSet[saturated (refineZero ξ)] (C a) := fun a =>
    ⟨hCm a, fun x y hxy => by
      simp only [hC, mem_ofPred_eq, show y 0 = x 0 from hxy.2]⟩
  set F : Set (ℤ → α) → α → (ℤ → α) → ℝ≥0∞ := fun A a x =>
    (condMeas μ ξ x (C a))⁻¹ * condMeas μ ξ x (C a ∩ A) with hF
  have hFm : ∀ A, MeasurableSet A → ∀ a, Measurable[saturated ξ] (F A a) := fun A hA a =>
    (measurable_condMeas μ ξ (hCm a)).inv.mul (measurable_condMeas μ ξ ((hCm a).inter hA))
  have hKF : ∀ A x, (condMeas μ ξ x)[|C (x 0)] A = F A (x 0) x := fun A x => by
    rw [cond_apply (hCm _)]
  have hpt : ∀ p q : ℝ≥0∞, q ≤ p → p ≠ ∞ → p⁻¹ * q * p = q := by
    intro p q hqp hp
    rcases eq_or_ne p 0 with rfl | h0
    · simp [nonpos_iff_eq_zero.1 hqp]
    · rw [mul_comm p⁻¹ q, mul_assoc, ENNReal.inv_mul_cancel h0 hp, mul_one]
  have hdisj : ∀ B : Set (ℤ → α), Pairwise (Function.onFun Disjoint fun a => B ∩ C a) :=
    fun B a b hab => Set.disjoint_left.2 fun x hx hy => hab (hx.2.symm.trans hy.2)
  have hcover : ∀ B : Set (ℤ → α), B = ⋃ a, B ∩ C a := fun B => by
    ext x
    simp only [mem_iUnion, mem_inter_iff, hC, mem_ofPred_eq]
    exact ⟨fun h => ⟨x 0, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  refine (condMeas_unique μ (refineZero ξ) (fun x => (condMeas μ ξ x)[|C (x 0)]) ?_ ?_).mono
    fun x hx => hx.symm
  · intro A hA
    have e : (fun x => (condMeas μ ξ x)[|C (x 0)] A) =
        fun x => ∑ a, (C a).indicator (F A a) x := by
      funext x
      rw [hKF, Finset.sum_eq_single (x 0)]
      · rw [indicator_of_mem (show x ∈ C (x 0) from rfl)]
      · intro a _ ha
        exact indicator_of_notMem (show x ∉ C a from fun h => ha h.symm) _
      · simp
    rw [e]
    exact Finset.measurable_sum _ fun a _ => ((hFm A hA a).mono hle le_rfl).indicator (hCsat a)
  · intro A B hA hB
    have hBm : MeasurableSet B := hB.1
    have key : ∀ a, ∫⁻ x in B ∩ C a, (condMeas μ ξ x)[|C (x 0)] A ∂μ = μ (A ∩ (B ∩ C a)) := by
      intro a
      obtain ⟨B', hB', hBB'⟩ := exists_saturated_inter_zeroCyl hf hfξ hB a
      calc ∫⁻ x in B ∩ C a, (condMeas μ ξ x)[|C (x 0)] A ∂μ
          = ∫⁻ x in C a ∩ B', F A a x ∂μ := by
            rw [hBB', inter_comm]
            refine setLIntegral_congr_fun ((hCm a).inter hB'.1) fun x hx => ?_
            rw [hKF, show x 0 = a from hx.1]
        _ = ∫⁻ x in B', F A a x * condMeas μ ξ x (C a) ∂μ :=
            (setLIntegral_mul_condMeas μ ξ (hFm A hA a) (hCm a) hB').symm
        _ = ∫⁻ x in B', condMeas μ ξ x (C a ∩ A) ∂μ :=
            lintegral_congr fun x => hpt _ _ (measure_mono inter_subset_left) (measure_ne_top _ _)
        _ = μ ((C a ∩ A) ∩ B') := setLIntegral_condMeas μ ξ ((hCm a).inter hA) hB'
        _ = μ (A ∩ (B ∩ C a)) := by
            rw [hBB']
            congr 1
            ext x
            simp only [mem_inter_iff]
            tauto
    calc ∫⁻ x in B, (condMeas μ ξ x)[|C (x 0)] A ∂μ
        = ∑' a, ∫⁻ x in B ∩ C a, (condMeas μ ξ x)[|C (x 0)] A ∂μ := by
          conv_lhs => rw [hcover B]
          exact lintegral_iUnion (fun a => hBm.inter (hCm a)) (hdisj B) _
      _ = ∑ a, μ (A ∩ (B ∩ C a)) := by
          rw [tsum_fintype]
          exact Finset.sum_congr rfl fun a _ => key a
      _ = μ (A ∩ B) := by
          have e : A ∩ B = ⋃ a, A ∩ (B ∩ C a) := by
            conv_lhs => rw [hcover B]
            rw [inter_iUnion]
          rw [e, measure_iUnion (fun a b hab => (hdisj B hab).mono inter_subset_right
            inter_subset_right) (fun a => hA.inter (hBm.inter (hCm a))), tsum_fintype]

theorem condMeas_pullShift {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (ξ : (ℤ → α) → Set (ℤ → α)) :
    ∀ᵐ x ∂μ, condMeas μ (pullShift ξ) x = (condMeas μ ξ (shift 1 x)).map (shift (-1)) := by
  have hback : ∀ x : ℤ → α, shift (-1) (shift 1 x) = x := fun x => by
    rw [shift_shift]; simp
  have hfwd : ∀ x : ℤ → α, shift 1 (shift (-1) x) = x := fun x => by
    rw [shift_shift]; simp
  have hσ : @Measurable _ _ (saturated (pullShift ξ)) (saturated ξ) (shift 1) := by
    intro B hB
    exact ⟨measurable_shift 1 hB.1, fun x y hxy => hB.2 _ _ hxy⟩
  refine (condMeas_unique μ (pullShift ξ) _ ?_ ?_).mono fun x hx => hx.symm
  · intro A hA
    simp_rw [Measure.map_apply (measurable_shift (-1)) hA]
    exact (measurable_condMeas μ ξ (measurable_shift (-1) hA)).comp hσ
  · intro A B hA hB
    have hA' : MeasurableSet (shift (-1) ⁻¹' A) := measurable_shift (-1) hA
    have hB' : MeasurableSet[saturated ξ] (shift (-1) ⁻¹' B) := by
      refine ⟨measurable_shift (-1) hB.1, fun z w hzw => ?_⟩
      have h : shift (-1) w ∈ pullShift ξ (shift (-1) z) := by
        simp only [pullShift, mem_preimage, hfwd]
        exact hzw
      exact hB.2 _ _ h
    have hBB : shift 1 ⁻¹' (shift (-1) ⁻¹' B) = B := by
      ext x
      simp [hback]
    have hAA : shift 1 ⁻¹' (shift (-1) ⁻¹' A) = A := by
      ext x
      simp [hback]
    calc ∫⁻ x in B, (condMeas μ ξ (shift 1 x)).map (shift (-1)) A ∂μ
        = ∫⁻ x in shift 1 ⁻¹' (shift (-1) ⁻¹' B),
            condMeas μ ξ (shift 1 x) (shift (-1) ⁻¹' A) ∂μ := by
          rw [hBB]
          simp_rw [Measure.map_apply (measurable_shift (-1)) hA]
      _ = ∫⁻ z in shift (-1) ⁻¹' B, condMeas μ ξ z (shift (-1) ⁻¹' A) ∂μ :=
          hinv.setLIntegral_comp_preimage hB'.1
            ((measurable_condMeas μ ξ hA').mono (saturated_le ξ) le_rfl)
      _ = μ (shift (-1) ⁻¹' A ∩ shift (-1) ⁻¹' B) := setLIntegral_condMeas μ ξ hA' hB'
      _ = μ (shift 1 ⁻¹' (shift (-1) ⁻¹' A ∩ shift (-1) ⁻¹' B)) :=
          (hinv.measure_preimage (hA'.inter hB'.1).nullMeasurableSet).symm
      _ = μ (A ∩ B) := by rw [preimage_inter, hAA, hBB]

theorem condMeas_pullShift_ae_eq_refineZero (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ]
    {ξ : (ℤ → α) → Set (ℤ → α)} (hξ : IsMeasurablePartition ξ) {D : Set (ℤ → α)}
    (hD : MeasurableSet D) (hD0 : μ Dᶜ = 0) (hin : ∀ x ∈ D, pullShift ξ x = refineZero ξ x)
    (hsub : ∀ x ∈ D, ξ x ⊆ D) (hout : ∀ x ∉ D, pullShift ξ x ⊆ Dᶜ) :
    ∀ᵐ x ∂μ, condMeas μ (pullShift ξ) x = condMeas μ (refineZero ξ) x :=
  condMeas_ae_eq_of_cut μ (isMeasurablePartition_refineZero hξ) hD hD0
    (fun x hx => by
      rw [hin x hx]
      exact (inter_eq_left.2 (show refineZero ξ x ⊆ D from
        inter_subset_left.trans (hsub x hx))).symm) hout

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in

theorem cylinder_block_succ (n : ℕ) (x : ℤ → α) :
    cylinder (block (n + 1) x) =
      {y | y 0 = x 0} ∩ shift 1 ⁻¹' cylinder (block n (shift 1 x)) := by
  ext y
  simp only [mem_cylinder, block_apply, mem_inter_iff, mem_ofPred_eq, mem_preimage, shift_apply]
  constructor
  · intro h
    refine ⟨by simpa using h 0, fun k => ?_⟩
    have := h k.succ
    simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one] at this
    rwa [add_comm (1 : ℤ)]
  · rintro ⟨h0, h⟩ k
    refine Fin.cases ?_ (fun k => ?_) k
    · simpa using h0
    · have := h k
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
      rwa [add_comm (1 : ℤ)] at this

theorem condMeas_zeroCyl_pos (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (ξ : (ℤ → α) → Set (ℤ → α)) : ∀ᵐ x ∂μ, 0 < condMeas μ ξ x {y | y 0 = x 0} := by
  have h : ∀ᵐ x ∂μ, ∀ a : α, x ∈ {y : ℤ → α | y 0 = a} → 0 < condMeas μ ξ x {y | y 0 = a} :=
    ae_all_iff.2 fun a => condMeas_pos_of_mem μ ξ (measurableSet_zeroCyl a)
  filter_upwards [h] with x hx using hx (x 0) rfl

variable {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ] {ξ : (ℤ → α) → Set (ℤ → α)}
  {D : Set (ℤ → α)}

theorem condMeas_cylinder_succ (hinv : MeasurePreserving (shift 1) μ μ)
    (hξ : IsMeasurablePartition ξ) (hD : MeasurableSet D) (hD0 : μ Dᶜ = 0)
    (hin : ∀ x ∈ D, pullShift ξ x = refineZero ξ x) (hsub : ∀ x ∈ D, ξ x ⊆ D)
    (hout : ∀ x ∉ D, pullShift ξ x ⊆ Dᶜ) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, condMeas μ ξ x (cylinder (block (n + 1) x)) =
      condMeas μ ξ x {y | y 0 = x 0} *
        condMeas μ ξ (shift 1 x) (cylinder (block n (shift 1 x))) := by
  filter_upwards [condMeas_pullShift hinv ξ,
    condMeas_pullShift_ae_eq_refineZero μ hξ hD hD0 hin hsub hout, condMeas_refineZero μ hξ,
    condMeas_zeroCyl_pos μ ξ] with x hT hE hC hpos n
  have hfwd : ∀ z : ℤ → α, shift 1 (shift (-1) z) = z := fun z => by
    rw [shift_shift]; simp
  set Cn := cylinder (block n (shift 1 x)) with hCn
  have hmeas : MeasurableSet (shift 1 ⁻¹' Cn) := measurable_shift 1 (measurableSet_cylinder _)
  have hpre : shift (-1) ⁻¹' (shift 1 ⁻¹' Cn) = Cn := by
    ext z
    simp [hfwd]
  rw [cylinder_block_succ]
  calc condMeas μ ξ x ({y | y 0 = x 0} ∩ shift 1 ⁻¹' Cn)
      = condMeas μ ξ x {y | y 0 = x 0} *
          (condMeas μ ξ x)[|{y | y 0 = x 0}] (shift 1 ⁻¹' Cn) := by
        rw [cond_apply (measurableSet_zeroCyl _), ← mul_assoc,
          ENNReal.mul_inv_cancel hpos.ne' (measure_ne_top _ _), one_mul]
    _ = condMeas μ ξ x {y | y 0 = x 0} * condMeas μ (pullShift ξ) x (shift 1 ⁻¹' Cn) := by
        rw [← hC, ← hE]
    _ = condMeas μ ξ x {y | y 0 = x 0} * condMeas μ ξ (shift 1 x) Cn := by
        rw [hT, Measure.map_apply (measurable_shift (-1)) hmeas, hpre]

theorem condMeas_cylinder_eq_prod (hinv : MeasurePreserving (shift 1) μ μ)
    (hξ : IsMeasurablePartition ξ) (hD : MeasurableSet D) (hD0 : μ Dᶜ = 0)
    (hin : ∀ x ∈ D, pullShift ξ x = refineZero ξ x) (hsub : ∀ x ∈ D, ξ x ⊆ D)
    (hout : ∀ x ∉ D, pullShift ξ x ⊆ Dᶜ) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, condMeas μ ξ x (cylinder (block n x)) =
      ∏ k ∈ Finset.range n, condMeas μ ξ (shift k x) {y | y 0 = shift k x 0} := by
  have hstep := condMeas_cylinder_succ hinv hξ hD hD0 hin hsub hout
  have hall : ∀ᵐ x ∂μ, ∀ k : ℕ, ∀ n : ℕ,
      condMeas μ ξ (shift k x) (cylinder (block (n + 1) (shift k x))) =
        condMeas μ ξ (shift k x) {y | y 0 = shift k x 0} *
          condMeas μ ξ (shift 1 (shift k x)) (cylinder (block n (shift 1 (shift k x)))) :=
    ae_all_iff.2 fun k => (measurePreserving_shift_natCast hinv k).quasiMeasurePreserving.ae hstep
  have hsk : ∀ (k : ℕ) (z : ℤ → α), shift (k : ℤ) (shift 1 z) = shift ((k + 1 : ℕ) : ℤ) z :=
    fun k z => by
      rw [shift_shift]
      congr 1
      push_cast
      ring
  filter_upwards [hall] with x hx n
  induction n generalizing x with
  | zero =>
    have : cylinder (block 0 x) = univ := by
      ext y
      simp [mem_cylinder]
    simp [this]
  | succ n ih =>
    have h1 : ∀ k : ℕ, ∀ m : ℕ,
        condMeas μ ξ (shift k (shift 1 x)) (cylinder (block (m + 1) (shift k (shift 1 x)))) =
          condMeas μ ξ (shift k (shift 1 x)) {y | y 0 = shift k (shift 1 x) 0} *
            condMeas μ ξ (shift 1 (shift k (shift 1 x)))
              (cylinder (block m (shift 1 (shift k (shift 1 x))))) := fun k => by
      rw [hsk]
      exact hx (k + 1)
    have h0 := hx 0 n
    simp only [Nat.cast_zero, shift_zero] at h0
    rw [h0, ih (shift 1 x) h1, Finset.prod_range_succ', mul_comm]
    simp only [hsk, Nat.cast_zero, shift_zero]

theorem infoSum_of_pullShift (hinv : MeasurePreserving (shift 1) μ μ)
    (hξ : IsMeasurablePartition ξ) (hD : MeasurableSet D) (hD0 : μ Dᶜ = 0)
    (hin : ∀ x ∈ D, pullShift ξ x = refineZero ξ x) (hsub : ∀ x ∈ D, ξ x ⊆ D)
    (hout : ∀ x ∉ D, pullShift ξ x ⊆ Dᶜ) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, -Real.log ((condMeas μ ξ x).real (cylinder (block n x))) =
      ∑ k ∈ Finset.range n, condInfo μ ξ (shift k x) := by
  have hpos : ∀ᵐ x ∂μ, ∀ k : ℕ, 0 < condMeas μ ξ (shift k x) {y | y 0 = shift k x 0} :=
    ae_all_iff.2 fun k => (measurePreserving_shift_natCast hinv k).quasiMeasurePreserving.ae
      (condMeas_zeroCyl_pos μ ξ)
  filter_upwards [condMeas_cylinder_eq_prod hinv hξ hD hD0 hin hsub hout, hpos] with x hx hp n
  rw [measureReal_def, hx n, ENNReal.toReal_prod,
    Real.log_prod fun k _ => (ENNReal.toReal_pos (hp k).ne' (measure_ne_top _ _)).ne',
    ← Finset.sum_neg_distrib]
  rfl

end General

theorem samePast_shift_one_iff {β : Type*} {x y : ℤ → β} :
    SamePast (shift 1 y) (shift 1 x) ↔ SamePast y x ∧ y 0 = x 0 := by
  constructor
  · intro h
    refine ⟨fun n hn => ?_, ?_⟩
    · have := h (n - 1) (by omega)
      rwa [shift_apply, shift_apply, add_sub_cancel] at this
    · have := h (-1) (by norm_num)
      simpa using this
  · rintro ⟨h, h0⟩ n hn
    simp only [shift_apply]
    rcases lt_or_eq_of_le (show 1 + n ≤ 0 by omega) with h' | h'
    · exact h _ h'
    · rw [h']
      exact h0

end FractalGeometry
