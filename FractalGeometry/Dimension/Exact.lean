import Mathlib
import FractalGeometry.Ergodic.Birkhoff

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology Metric

open scoped ENNReal

section Definitions

def HasLocalDim {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (x : X) (d : ℝ) : Prop :=
  Tendsto (fun r : ℝ => Real.log (μ.real (closedBall x r)) / Real.log r) (𝓝[>] 0) (𝓝 d)

def IsExactDim {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (d : ℝ) : Prop := ∀ᵐ x ∂μ, HasLocalDim μ x d

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  {μ ν' ν : Measure X} {x : X} {d d' d₁ d₂ : ℝ}

end Definitions

end FractalGeometry
