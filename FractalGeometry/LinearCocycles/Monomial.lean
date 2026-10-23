import Mathlib

namespace FractalGeometry

open Matrix

def monomialMatrix (c : ZMod 2) (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if c = 0 then !![a, 0; 0, b] else !![0, a; b, 0]

@[simp] theorem monomialMatrix_zero (a b : ℝ) : monomialMatrix 0 a b = !![a, 0; 0, b] := rfl

@[simp] theorem monomialMatrix_one (a b : ℝ) : monomialMatrix 1 a b = !![0, a; b, 0] := rfl

theorem zmod_two_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide

theorem monomialMatrix_mul (c c' : ZMod 2) (a b a' b' : ℝ) :
    monomialMatrix c a b * monomialMatrix c' a' b' =
      monomialMatrix (c + c') (a * if c = 0 then a' else b') (b * if c = 0 then b' else a') := by
  rcases zmod_two_cases c with rfl | rfl <;> rcases zmod_two_cases c' with rfl | rfl <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, show (1 : ZMod 2) + 1 = 0 from by decide]

end FractalGeometry
