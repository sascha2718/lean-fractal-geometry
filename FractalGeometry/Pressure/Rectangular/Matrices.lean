import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.LinearCocycles.Monomial
import FractalGeometry.SelfAffine.Rectangular.Defs

open FractalGeometry.Ergodic

namespace FractalGeometry

open Matrix

namespace RectangularIFS

variable {ι : Type*} (S : RectangularIFS ι)

def HasBothOrientations : Prop := (∃ i, S.o i = 0) ∧ ∃ i, S.o i = 1

def HasProximalDiagonal : Prop := ∃ i, S.o i = 0 ∧ |S.a i| ≠ |S.b i|

def mat (i : ι) : Matrix (Fin 2) (Fin 2) ℝ := monomialMatrix (S.o i) (S.a i) (S.b i)

def matWord (w : List ι) : Matrix (Fin 2) (Fin 2) ℝ := (w.map S.mat).prod

@[simp] theorem matWord_nil : S.matWord [] = 1 := rfl

@[simp] theorem matWord_cons (i : ι) (w : List ι) :
    S.matWord (i :: w) = S.mat i * S.matWord w := by
  simp [matWord]

theorem matWord_eq (w : List ι) :
    S.matWord w =
      monomialMatrix (S.oWord w) (S.gDeriv (S.codeWord 0 w)) (S.gDeriv (S.codeWord 1 w)) := by
  induction w with
  | nil =>
    ext i j; fin_cases i <;> fin_cases j <;> simp
  | cons i w ih =>
    rw [matWord_cons, ih, mat, monomialMatrix_mul]
    rcases zmod_two_cases (S.o i) with h | h <;>
      simp [h, show (1 : ZMod 2) + 1 = 0 from by decide]

end RectangularIFS

end FractalGeometry
