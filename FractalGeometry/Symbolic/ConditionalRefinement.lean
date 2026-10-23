import Mathlib
import FractalGeometry.Ergodic.Birkhoff

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory ProbabilityTheory Set

section Partition

variable {Ω : Type*}

def IsMeasurablePartition [MeasurableSpace Ω] (ξ : Ω → Set Ω) : Prop :=
  ∃ f : Ω → ℝ, Measurable f ∧ ∀ x y, y ∈ ξ x ↔ f y = f x

variable [MeasurableSpace Ω] [StandardBorelSpace Ω]

end Partition

end FractalGeometry
