import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.SelfAffine.Rectangular.Orientation
import FractalGeometry.Symbolic.OrientationCoding
import FractalGeometry.Symbolic.PastWords

open FractalGeometry.Ergodic

namespace FractalGeometry

open Matrix

@[simp] theorem length_pastWord {α : Type*} (x : ℤ → α) (n : ℕ) :
    (pastWord x n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

namespace RectangularIFS

variable {ι : Type*} (S : RectangularIFS ι)

theorem codeWord_pastWord_tau (x : ℤ → ι) (n : ℕ) :
    S.codeWord (eps S.o x (-(n : ℤ))) (pastWord x n) = pastWord (tau S.o x) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := eps_add_one S.o x (-((n : ℤ) + 1))
    rw [show -((n : ℤ) + 1) + 1 = -(n : ℤ) by ring] at h
    rw [pastWord_succ, pastWord_succ, Nat.cast_succ, codeWord_cons, ← h, ih, tau_apply]

theorem codeWord_pastWord_omega (x : ℤ → ι) (n : ℕ) :
    S.codeWord (eps S.o x (-(n : ℤ)) + 1) (pastWord x n) = pastWord (omega S.o x) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := eps_add_one S.o x (-((n : ℤ) + 1))
    rw [show -((n : ℤ) + 1) + 1 = -(n : ℤ) by ring] at h
    rw [pastWord_succ, pastWord_succ, Nat.cast_succ, codeWord_cons, add_right_comm, ← h, ih,
      omega_apply]

end RectangularIFS

end FractalGeometry
