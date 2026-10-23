import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Dimension.Exact
import FractalGeometry.SelfAffine.Partitions
import FractalGeometry.SelfAffine.Planar
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory

universe u

def PlanarFengLedrappierYoung : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (P : AffineIFS ι) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ],
    MeasurePreserving (shift 1) μ μ → Ergodic (shift 1) μ → P.lyapunov₂ μ < P.lyapunov₁ μ →
    IsExactDim (μ.map P.proj)
      ((P.dimEntropy μ 1 - P.dimEntropy μ 0) / P.lyapunov₁ μ +
        (P.dimEntropy μ 2 - P.dimEntropy μ 1) / P.lyapunov₂ μ)

end FractalGeometry
