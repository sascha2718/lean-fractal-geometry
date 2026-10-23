import Mathlib
import FractalGeometry.LinearCocycles.Monomial

namespace FractalGeometry

open Matrix

open scoped Matrix.Norms.L2Operator

theorem monomialMatrix_mulVec (c : ZMod 2) (a b : ℝ) (v : Fin 2 → ℝ) :
    monomialMatrix c a b *ᵥ v = if c = 0 then ![a * v 0, b * v 1] else ![a * v 1, b * v 0] := by
  rcases zmod_two_cases c with rfl | rfl <;>
    ext j <;> fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end FractalGeometry
