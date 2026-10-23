import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.SelfSimilar.Line.Defs

open FractalGeometry.Ergodic

namespace FractalGeometry

open Matrix

namespace LineIFS

variable {ι : Type*} (S : LineIFS ι)

def g (p : ι) (t : ℝ) : ℝ := S.ratio p * t + S.trans p

def gDeriv (u : List (ι)) : ℝ := (u.map S.ratio).prod

@[simp] theorem gDeriv_nil : S.gDeriv [] = 1 := rfl

@[simp] theorem gDeriv_cons (p : ι) (u : List (ι)) :
    S.gDeriv (p :: u) = S.ratio p * S.gDeriv u := by
  simp [gDeriv]

theorem gDeriv_ne_zero (u : List (ι)) : S.gDeriv u ≠ 0 := by
  induction u with
  | nil => simp
  | cons p u ih => simpa using ⟨S.ratio_ne_zero p, ih⟩

end LineIFS

end FractalGeometry
