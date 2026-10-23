module

public import Mathlib
public import FractalGeometry.Symbolic.Conditional
public import FractalGeometry.Symbolic.ConditionalMeasures

@[expose] public section

namespace FractalGeometry


open MeasureTheory Filter Topology Set

universe u

section StandardBorel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]

theorem condMeas_pos_of_mem (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Set Ω) {A : Set Ω}
    (hA : MeasurableSet A) : ∀ᵐ x ∂μ, x ∈ A → 0 < condMeas μ ξ x A := by
  have hB : MeasurableSet[saturated ξ] {x | condMeas μ ξ x A = 0} :=
    measurable_condMeas μ ξ hA (measurableSet_singleton 0)
  have h0 : μ (A ∩ {x | condMeas μ ξ x A = 0}) = 0 := by
    rw [← setLIntegral_condMeas μ ξ hA hB,
      setLIntegral_congr_fun (saturated_le ξ _ hB) (fun x hx => hx)]
    simp
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with x hx hxA
  exact pos_iff_ne_zero.2 fun h => hx ⟨hxA, h⟩

end StandardBorel

end FractalGeometry
