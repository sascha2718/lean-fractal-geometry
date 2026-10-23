import Mathlib
import GeometricMeasureTheory.Box.ModifiedBox
import FractalGeometry.SelfAffine.Rectangular.Defs

open GeometricMeasureTheory

namespace FractalGeometry

open scoped ENNReal

namespace RectangularIFS

variable {ι : Type*} (S : RectangularIFS ι)

def gWord : List (ι × ZMod 2) → ℝ → ℝ
  | [] => id
  | p :: u => S.g p ∘ gWord u

@[simp] theorem gWord_nil : S.gWord [] = id := rfl

@[simp] theorem gWord_cons (p : ι × ZMod 2) (u : List (ι × ZMod 2)) :
    S.gWord (p :: u) = S.g p ∘ S.gWord u := rfl

theorem gWord_apply (u : List (ι × ZMod 2)) (t : ℝ) :
    S.gWord u t = S.gDeriv u * t + S.gWord u 0 := by
  induction u with
  | nil => simp
  | cons p u ih =>
    simp only [gWord_cons, Function.comp_apply, gDeriv_cons, g]
    rw [ih]; ring

theorem gWord_append (u u' : List (ι × ZMod 2)) :
    S.gWord (u ++ u') = S.gWord u ∘ S.gWord u' := by
  induction u with
  | nil => rfl
  | cons p u ih => simp [ih, Function.comp_assoc]

theorem gDeriv_append (u u' : List (ι × ZMod 2)) :
    S.gDeriv (u ++ u') = S.gDeriv u * S.gDeriv u' := by
  simp [gDeriv]

end RectangularIFS

end FractalGeometry
