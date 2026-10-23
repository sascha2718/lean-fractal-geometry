import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.LinearCocycles.Monomial
import FractalGeometry.Pressure.Rectangular.Matrices
import FractalGeometry.SelfAffine.Rectangular.Defs

open FractalGeometry.Ergodic

namespace FractalGeometry

open Matrix

variable {ι : Type*}

namespace RectangularIFS

variable (S : RectangularIFS ι)

theorem det_mat_ne_zero (i : ι) : (S.mat i).det ≠ 0 := by
  rw [mat]
  rcases zmod_two_cases (S.o i) with h | h <;> rw [h]
  · rw [monomialMatrix_zero, Matrix.det_fin_two_of]
    simpa using ⟨S.a_ne_zero i, S.b_ne_zero i⟩
  · rw [monomialMatrix_one, Matrix.det_fin_two_of]
    simpa using ⟨S.a_ne_zero i, S.b_ne_zero i⟩

end RectangularIFS

end FractalGeometry
