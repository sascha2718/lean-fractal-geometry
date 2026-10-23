import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.ShannonMcMillanBreiman
import FractalGeometry.LinearCocycles.EuclideanNorm
import FractalGeometry.SelfAffine.Partitions
import FractalGeometry.SelfAffine.Planar
import FractalGeometry.Symbolic.Conditional
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.Past
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology Set

universe u

namespace AffineIFS

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (P : AffineIFS ι)

omit [Fintype ι] [MeasurableSingletonClass ι] in

theorem xi_zero_eq (μ : Measure (ℤ → ι)) :
    P.xi μ 0 = atomsOn (P.SigmaPrime μ) fun x => {y | SamePast y x} := by
  unfold xi
  congr 1
  funext x
  ext y
  simp [oseledets, MatrixTuple.filtration]

theorem tendsto_neg_log_cylinder_dimEntropyAt (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    (hfull : μ (P.SigmaPrime μ)ᶜ = 0) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => -Real.log (μ.real (cylinder (block n x))) / n) atTop
      (𝓝 (P.dimEntropyAt μ 0 x)) := by
  rw [dimEntropyAt, xi_zero_eq]
  exact tendsto_neg_log_cylinder_localEntropy hinv (P.measurableSet_SigmaPrime μ hlt) hfull

end AffineIFS

end FractalGeometry
