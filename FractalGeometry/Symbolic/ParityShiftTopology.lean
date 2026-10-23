import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.SelfAffine.Rectangular.Orientation

open FractalGeometry.Ergodic

namespace FractalGeometry

open Finset

variable {ι : Type*}

variable (o : ι → ZMod 2) (x : ℤ → ι)

theorem eps_sub_one (m : ℤ) : eps o x (m - 1) = eps o x m + o (x (m - 1)) := by
  have h := eps_add_one o x (m - 1)
  rw [sub_add_cancel] at h
  rw [h, add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem eq_eps_of_succ {S : ℤ → ZMod 2} (h0 : S 0 = 0)
    (hS : ∀ m, S (m + 1) = S m + o (x m)) : S = eps o x := by
  funext n
  induction n using Int.induction_on with
  | zero => rw [h0, eps_zero]
  | succ n ih => rw [hS, eps_add_one, ih]
  | pred n ih =>
    have h := hS (-(n : ℤ) - 1)
    rw [sub_add_cancel] at h
    rw [eps_sub_one, ← ih, h, add_assoc, CharTwo.add_self_eq_zero, add_zero]

end FractalGeometry
