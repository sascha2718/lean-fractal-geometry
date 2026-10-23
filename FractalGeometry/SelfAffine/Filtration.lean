import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Symbolic.Conditional
import FractalGeometry.Symbolic.ConditionalMeasures
import FractalGeometry.Symbolic.ConditionalRefinement
import FractalGeometry.Symbolic.Disintegration

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology Set Matrix

open scoped ENNReal

section Cut

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [StandardBorelSpace Ω] in

theorem measurableSet_saturated_inter_of_cut {ξ ξ' : Ω → Set Ω} {D : Set Ω}
    (hD : MeasurableSet D) (hin : ∀ x ∈ D, ξ' x = ξ x ∩ D) (hout : ∀ x ∉ D, ξ' x ⊆ Dᶜ)
    {B : Set Ω} (hB : MeasurableSet[saturated ξ] B) : MeasurableSet[saturated ξ'] (B ∩ D) := by
  refine ⟨hB.1.inter hD, fun x y hy => ?_⟩
  by_cases hx : x ∈ D
  · rw [hin x hx] at hy
    simp only [mem_inter_iff, hB.2 x y hy.1, hx, hy.2]
  · have hy' : y ∉ D := hout x hx hy
    simp [hx, hy']

theorem exists_measurableSet_saturated_ae_eq_of_cut (μ : Measure Ω) [IsFiniteMeasure μ]
    {ξ ξ' : Ω → Set Ω} (hξ : IsMeasurablePartition ξ) {D : Set Ω} (hD : MeasurableSet D)
    (hD0 : μ Dᶜ = 0) (hin : ∀ x ∈ D, ξ' x = ξ x ∩ D) {B : Set Ω}
    (hB : MeasurableSet[saturated ξ'] B) :
    ∃ B', MeasurableSet[saturated ξ] B' ∧ B =ᵐ[μ] B' := by
  have hDae : ∀ᵐ x ∂μ, x ∈ D := ae_iff.2 hD0
  have hDc : ∀ᵐ x ∂μ, condMeas μ ξ x Dᶜ = 0 := by
    have h := setLIntegral_condMeas μ ξ hD.compl (@MeasurableSet.univ _ (saturated ξ))
    rw [Measure.restrict_univ, inter_univ, hD0] at h
    exact (lintegral_eq_zero_iff ((measurable_condMeas μ ξ hD.compl).mono (saturated_le ξ)
      le_rfl)).1 h
  refine ⟨{x | condMeas μ ξ x B = 1},
    measurable_condMeas μ ξ hB.1 (measurableSet_singleton 1), ?_⟩
  filter_upwards [condMeas_atom μ hξ, hDc, hDae] with x h1 h2 h3
  have hfull : condMeas μ ξ x (ξ' x) = 1 := by
    rw [hin x h3]
    refine le_antisymm prob_le_one ?_
    calc (1 : ℝ≥0∞) = condMeas μ ξ x (ξ x) := h1.symm
      _ ≤ condMeas μ ξ x (ξ x ∩ D ∪ Dᶜ) := measure_mono fun y hy => by
          by_cases hyD : y ∈ D
          · exact Or.inl ⟨hy, hyD⟩
          · exact Or.inr hyD
      _ ≤ condMeas μ ξ x (ξ x ∩ D) + condMeas μ ξ x Dᶜ := measure_union_le _ _
      _ = condMeas μ ξ x (ξ x ∩ D) := by rw [h2, add_zero]
  change (x ∈ B) = (condMeas μ ξ x B = 1)
  rw [eq_iff_iff]
  constructor
  · intro hxB
    refine le_antisymm prob_le_one ?_
    rw [← hfull]
    exact measure_mono fun y hy => (hB.2 x y hy).1 hxB
  · intro hB1
    by_contra hxB
    have hc : condMeas μ ξ x Bᶜ = 1 := by
      refine le_antisymm prob_le_one ?_
      rw [← hfull]
      exact measure_mono fun y hy hyB => hxB ((hB.2 x y hy).2 hyB)
    rw [prob_compl_eq_one_iff₀ hB.1.nullMeasurableSet] at hc
    rw [hc] at hB1
    exact zero_ne_one hB1

theorem condMeas_ae_eq_of_cut (μ : Measure Ω) [IsFiniteMeasure μ] {ξ ξ' : Ω → Set Ω}
    (hξ : IsMeasurablePartition ξ) {D : Set Ω} (hD : MeasurableSet D) (hD0 : μ Dᶜ = 0)
    (hin : ∀ x ∈ D, ξ' x = ξ x ∩ D) (hout : ∀ x ∉ D, ξ' x ⊆ Dᶜ) :
    ∀ᵐ x ∂μ, condMeas μ ξ' x = condMeas μ ξ x := by
  classical
  have hDae : ∀ᵐ x ∂μ, x ∈ D := ae_iff.2 hD0
  have hDsat : MeasurableSet[saturated ξ'] D := by
    simpa using measurableSet_saturated_inter_of_cut hD hin hout
      (@MeasurableSet.univ _ (saturated ξ))
  let K : Ω → Measure Ω := fun x => if x ∈ D then condMeas μ ξ x else condMeas μ ξ' x
  have hK : ∀ A, MeasurableSet A → Measurable[saturated ξ'] fun x => K x A := by
    intro A hA
    have e : (fun x => K x A) =
        D.piecewise (fun x => condMeas μ ξ x A) (fun x => condMeas μ ξ' x A) := by
      funext x
      by_cases hx : x ∈ D <;> simp [K, hx]
    rw [e]
    intro U hU
    rw [piecewise_preimage, Set.ite]
    exact (measurableSet_saturated_inter_of_cut hD hin hout
      (measurable_condMeas μ ξ hA hU)).union ((measurable_condMeas μ ξ' hA hU).diff hDsat)
  have hint : ∀ A B, MeasurableSet A → MeasurableSet[saturated ξ'] B →
      ∫⁻ x in B, K x A ∂μ = μ (A ∩ B) := by
    intro A B hA hB
    obtain ⟨B', hB', hBB'⟩ :=
      exists_measurableSet_saturated_ae_eq_of_cut μ hξ hD hD0 hin hB
    calc ∫⁻ x in B, K x A ∂μ = ∫⁻ x in B, condMeas μ ξ x A ∂μ :=
          lintegral_congr_ae (ae_restrict_of_ae (hDae.mono fun x hx => by simp [K, hx]))
      _ = ∫⁻ x in B', condMeas μ ξ x A ∂μ := setLIntegral_congr hBB'
      _ = μ (A ∩ B') := setLIntegral_condMeas μ ξ hA hB'
      _ = μ (A ∩ B) :=
          measure_congr (EventuallyEqSet.inter (EventuallyEq.refl (ae μ) A) hBB'.symm)
  filter_upwards [condMeas_unique μ ξ' K hK hint, hDae] with x hx hxD
  rw [← hx]
  simp [K, hxD]

end Cut

end FractalGeometry
