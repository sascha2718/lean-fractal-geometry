import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.LinearCocycles.Products
import FractalGeometry.LinearCocycles.SingularValue
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.WordIntegrals

open FractalGeometry.Ergodic

namespace FractalGeometry

open Filter MeasureTheory Topology

open scoped ENNReal Matrix.Norms.L2Operator

namespace MatrixTuple

variable {ι : Type*} [Fintype ι] {A : ι → Matrix (Fin 2) (Fin 2) ℝ} {s : ℝ}

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

variable (A) in

noncomputable def blockEnergy (s : ℝ) (μ : Measure (ℤ → ι)) (n : ℕ) : ℝ :=
  ∑ w : Fin n → ι, μ.real (cylinder w) * Real.log (svf s (word A (List.ofFn w)))

theorem blockEnergy_eq_integral (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] (n : ℕ) :
    blockEnergy A s μ n = ∫ x, Real.log (svf s (word A (futureWord x n))) ∂μ :=
  (integral_comp_futureWord_eq_sum μ (fun w => Real.log (svf s (word A w))) n).symm

variable [Nonempty ι]

end MatrixTuple

end FractalGeometry
