import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open Filter Topology MeasureTheory

section Entropy

variable {α : Type*} [Fintype α] [MeasurableSpace α]

variable [MeasurableSingletonClass α]

theorem entropy_nonneg {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) : 0 ≤ entropy μ :=
  ge_of_tendsto' (tendsto_entropy hμ) fun n =>
    div_nonneg (blockEntropy_nonneg μ n) (Nat.cast_nonneg n)

end Entropy

end FractalGeometry
