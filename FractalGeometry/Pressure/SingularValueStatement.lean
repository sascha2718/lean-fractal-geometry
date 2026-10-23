import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.LinearCocycles.Pressure
import FractalGeometry.LinearCocycles.Products
import FractalGeometry.LinearCocycles.SingularValue
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.FutureWords

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter

open scoped Matrix.Norms.L2Operator

namespace MatrixTuple

variable {ι : Type*} (A : ι → Matrix (Fin 2) (Fin 2) ℝ)

variable [MeasurableSpace ι]

noncomputable def energyLim (s : ℝ) (μ : Measure (ℤ → ι)) : ℝ :=
  limUnder atTop fun n : ℕ => (∫ x, Real.log (svf s (word A (futureWord x n))) ∂μ) / n

def IsEquilibriumState [Fintype ι] (s : ℝ) (μ : Measure (ℤ → ι)) : Prop :=
  pressure A s = entropy μ + energyLim A s μ

def HasGibbsBounds [Fintype ι] (s : ℝ) (μ : Measure (ℤ → ι)) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ w : Fin n → ι,
    C⁻¹ * (Real.exp (-(n * pressure A s)) * svf s (word A (List.ofFn w))) ≤
        μ.real (cylinder w) ∧
      μ.real (cylinder w) ≤
        C * (Real.exp (-(n * pressure A s)) * svf s (word A (List.ofFn w)))

end MatrixTuple

end FractalGeometry
