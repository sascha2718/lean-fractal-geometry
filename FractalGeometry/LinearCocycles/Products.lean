module

public import Mathlib
public import FractalGeometry.Symbolic.FutureWords

@[expose] public section

namespace FractalGeometry


open MeasureTheory Filter

open scoped Matrix.Norms.L2Operator

namespace MatrixTuple

variable {ι : Type*} (A : ι → Matrix (Fin 2) (Fin 2) ℝ)

def word (w : List ι) : Matrix (Fin 2) (Fin 2) ℝ := (w.map A).prod

@[simp] theorem word_nil : word A [] = 1 := rfl

theorem word_append (w w' : List ι) : word A (w ++ w') = word A w * word A w' := by
  simp [word]

variable [MeasurableSpace ι]

noncomputable def lyapunov₁ (μ : Measure (ℤ → ι)) : ℝ :=
  limUnder atTop fun n : ℕ => (∫ x, Real.log ‖word A (futureWord x n)‖ ∂μ) / n

noncomputable def lyapunov₂ (μ : Measure (ℤ → ι)) : ℝ :=
  limUnder atTop fun n : ℕ =>
    (∫ x, Real.log (|(word A (futureWord x n)).det| / ‖word A (futureWord x n)‖) ∂μ) / n

end MatrixTuple

end FractalGeometry
