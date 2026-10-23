import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Oseledets
import FractalGeometry.SelfAffine.CylinderEntropy
import FractalGeometry.SelfAffine.Partitions
import FractalGeometry.SelfAffine.Planar
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology Set Matrix

open scoped Matrix.Norms.L2Operator

universe u

namespace AffineIFS

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (P : AffineIFS ι)

theorem measure_SigmaPrime_compl_of_ergodic (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    μ (P.SigmaPrime μ)ᶜ = 0 :=
  MatrixTuple.measure_regularSet_compl_of_ergodic P.det_ne_zero herg hlt

theorem tendsto_neg_log_cylinder_dimEntropyAt_of_ergodic (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (herg : Ergodic (shift 1) μ)
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => -Real.log (μ.real (cylinder (block n x))) / n) atTop
      (𝓝 (P.dimEntropyAt μ 0 x)) :=
  P.tendsto_neg_log_cylinder_dimEntropyAt μ herg.toMeasurePreserving hlt
    (P.measure_SigmaPrime_compl_of_ergodic μ herg hlt)

end AffineIFS

end FractalGeometry
