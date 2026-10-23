import Mathlib
import GeometricMeasureTheory.Box.BoxDimension
import FractalGeometry.LinearCocycles.Products
import FractalGeometry.LinearCocycles.SingularValue


open GeometricMeasureTheory

namespace FractalGeometry

open MeasureTheory Filter

open scoped Matrix.Norms.L2Operator

namespace MatrixTuple

variable {ι : Type*} (A : ι → Matrix (Fin 2) (Fin 2) ℝ)

noncomputable def svfSum [Fintype ι] (s : ℝ) (n : ℕ) : ℝ :=
  ∑ w : Fin n → ι, svf s (word A (List.ofFn w))

noncomputable def pressure [Fintype ι] (s : ℝ) : ℝ :=
  sInf ((fun n : ℕ => Real.log (svfSum A s n) / n) '' Set.Ici 1)

variable [MeasurableSpace ι]

end MatrixTuple

end FractalGeometry
