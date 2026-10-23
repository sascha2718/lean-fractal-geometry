import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.LinearCocycles.Monomial
import FractalGeometry.LinearCocycles.Proximal
import FractalGeometry.Pressure.Rectangular.Matrices
import FractalGeometry.SelfAffine.Rectangular.Defs

open FractalGeometry.Ergodic

namespace FractalGeometry

open Polynomial Matrix

namespace RectangularIFS

variable {ι : Type*}

def Proximal (S : RectangularIFS ι) : Prop :=
  ∃ w : List ι, w ≠ [] ∧ IsProximalMatrix (S.matWord w)

theorem HasProximalDiagonal.proximal {S : RectangularIFS ι} (h : S.HasProximalDiagonal) :
    S.Proximal := by
  obtain ⟨i, hi, hne⟩ := h
  refine ⟨[i], List.cons_ne_nil _ _, ?_⟩
  rw [matWord_cons, matWord_nil, mul_one, mat, hi]
  exact isProximalMatrix_monomialMatrix_zero.2 hne

end RectangularIFS

end FractalGeometry
