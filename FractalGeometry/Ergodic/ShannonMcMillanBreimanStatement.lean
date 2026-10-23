module

public import Mathlib
public import FractalGeometry.Symbolic.Entropy
public import FractalGeometry.Symbolic.Shift

@[expose] public section

namespace FractalGeometry


open MeasureTheory Filter Topology

universe u

def ShannonMcMillanBreimanStatement : Prop :=
  ∀ (α : Type u) [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ], Ergodic (shift 1) μ →
      ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => -Real.log (μ.real (cylinder (block n x))) / n) atTop
        (𝓝 (entropy μ))

end FractalGeometry
