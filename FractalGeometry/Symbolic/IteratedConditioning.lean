import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Symbolic.Conditional

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal NNReal

universe u

section Saturated

variable {Ω : Type*} [MeasurableSpace Ω]

theorem eq_of_measurable_saturated {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {ξ : Ω → Set Ω} {f : Ω → Z} (hf : Measurable[saturated ξ] f) {x y : Ω} (hxy : y ∈ ξ x) :
    f x = f y := by
  have h := (hf (measurableSet_singleton (f x))).2 x y hxy
  simp only [mem_preimage, mem_singleton_iff, true_iff] at h
  exact h.symm

end Saturated

section Transport

variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y]
  [StandardBorelSpace Y]

theorem condMeas_eq_of_mem (μ : Measure X) [IsFiniteMeasure μ] {ξ : X → Set X} {x y : X}
    (hxy : y ∈ ξ x) : condMeas μ ξ x = condMeas μ ξ y :=
  Measure.ext fun _ hA => eq_of_measurable_saturated (measurable_condMeas μ ξ hA) hxy

end Transport

end FractalGeometry
