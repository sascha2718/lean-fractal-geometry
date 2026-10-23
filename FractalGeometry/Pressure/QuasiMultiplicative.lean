import Mathlib
import FractalGeometry.LinearCocycles.Products
import FractalGeometry.Pressure.NormPotential
import FractalGeometry.Symbolic.Shift

namespace FractalGeometry

open MeasureTheory

open scoped Matrix.Norms.L2Operator

universe u

namespace MatrixTuple

variable {ι : Type*}

def NormQuasiMultiplicative (A : ι → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ m : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ u v : List ι, ∃ k : List ι, k.length ≤ m ∧
    c * (‖word A u‖ * ‖word A v‖) ≤ ‖word A (u ++ k ++ v)‖

end MatrixTuple

def NormGibbsExistenceStatement : Prop :=
  ∀ {ι : Type u} [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (A : ι → Matrix (Fin 2) (Fin 2) ℝ), (∀ i, (A i).det ≠ 0) →
    MatrixTuple.NormQuasiMultiplicative A → ∀ {q : ℝ}, 0 < q →
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ Ergodic (shift 1) μ ∧
      MatrixTuple.HasNormGibbs A q μ

end FractalGeometry
