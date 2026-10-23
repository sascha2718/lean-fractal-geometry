module

public import Mathlib
public import FractalGeometry.Symbolic.Conditional
public import FractalGeometry.Symbolic.Shift

@[expose] public section

namespace FractalGeometry


open MeasureTheory ProbabilityTheory Set

open scoped ENNReal

section Disintegration

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

theorem lintegral_mul_lintegral_condMeas (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Set Ω)
    {h g : Ω → ℝ≥0∞} (hh : Measurable[saturated ξ] h) (hg : Measurable g) :
    ∫⁻ x, h x * ∫⁻ y, g y ∂condMeas μ ξ x ∂μ = ∫⁻ x, h x * g x ∂μ := by
  have hm := saturated_le (Ω := Ω) ξ
  have hF : Measurable[(saturated ξ).prod mΩ] fun p : Ω × Ω => h p.1 * g p.2 :=
    (hh.comp measurable_fst).mul (hg.comp measurable_snd)
  have hd : @Measurable Ω (Ω × Ω) mΩ ((saturated ξ).prod mΩ) Function.diag :=
    (measurable_id'' hm).prodMk measurable_id
  have h1 := Measure.lintegral_compProd (μ := μ.trim hm) (κ := condExpKernel μ (saturated ξ)) hF
  rw [compProd_trim_condExpKernel hm,
    @lintegral_map Ω (Ω × Ω) mΩ ((saturated ξ).prod mΩ) μ _ _ hF hd] at h1
  simp only [Function.diag_apply] at h1
  rw [h1, lintegral_trim hm
    (hF.lintegral_kernel_prod_right' (κ := condExpKernel μ (saturated ξ)))]
  refine lintegral_congr fun x => ?_
  change h x * _ = ∫⁻ b, h x * g b ∂(condExpKernel μ (saturated ξ) x)
  rw [lintegral_const_mul _ hg]
  rfl

theorem setLIntegral_mul_condMeas (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Set Ω)
    {h : Ω → ℝ≥0∞} (hh : Measurable[saturated ξ] h) {A B : Set Ω} (hA : MeasurableSet A)
    (hB : MeasurableSet[saturated ξ] B) :
    ∫⁻ x in B, h x * condMeas μ ξ x A ∂μ = ∫⁻ x in A ∩ B, h x ∂μ := by
  have hm := saturated_le (Ω := Ω) ξ
  have h1 := lintegral_mul_lintegral_condMeas μ ξ (hh.indicator hB)
    ((measurable_one (α := ℝ≥0∞)).indicator hA)
  calc ∫⁻ x in B, h x * condMeas μ ξ x A ∂μ
      = ∫⁻ x, B.indicator h x * ∫⁻ y, A.indicator 1 y ∂condMeas μ ξ x ∂μ := by
        rw [← lintegral_indicator (hm _ hB)]
        refine lintegral_congr fun x => ?_
        rw [lintegral_indicator_one hA]
        by_cases hx : x ∈ B <;> simp [hx]
    _ = ∫⁻ x, B.indicator h x * A.indicator 1 x ∂μ := h1
    _ = ∫⁻ x in A ∩ B, h x ∂μ := by
        rw [← lintegral_indicator (hA.inter (hm _ hB))]
        refine lintegral_congr fun x => ?_
        by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> simp [hxA, hxB]

theorem setLIntegral_condMeas (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Set Ω) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet[saturated ξ] B) :
    ∫⁻ x in B, condMeas μ ξ x A ∂μ = μ (A ∩ B) := by
  have h1 := setLIntegral_mul_condMeas μ ξ
    (measurable_const : Measurable[saturated ξ] fun _ : Ω => (1 : ℝ≥0∞)) hA hB
  simpa using h1

end Disintegration

section Shift

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem localEntropy_ae_eq (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (ξ : (ℤ → α) → Set (ℤ → α)) :
    ∀ᵐ x ∂μ, localEntropy μ ξ x = condEntropy μ ξ := by
  have hmeas : Measurable[MeasurableSpace.invariants (shift 1 : (ℤ → α) → ℤ → α)]
      (localEntropy μ ξ) := stronglyMeasurable_condExp.measurable
  obtain ⟨c, hc⟩ := herg.toPreErgodic.ae_eq_const_of_ae_eq_comp
    (hmeas.mono (MeasurableSpace.invariants_le _) le_rfl)
    (MeasurableSpace.comp_eq_of_measurable_invariants hmeas)
  have hcval : c = condEntropy μ ξ := by
    rw [← integral_localEntropy, integral_congr_ae hc]
    simp
  filter_upwards [hc] with x hx
  rw [hx, Function.const_apply, hcval]

end Shift

end FractalGeometry
