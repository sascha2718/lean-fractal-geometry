module

public import Mathlib
public import FractalGeometry.Symbolic.Shift
public import FractalGeometry.Symbolic.FutureWords
public import FractalGeometry.Symbolic.PastWords

@[expose] public section

namespace FractalGeometry


open MeasureTheory Filter Topology Set Matrix

def SamePast {α : Type*} (x y : ℤ → α) : Prop := ∀ n : ℤ, n < 0 → x n = y n

theorem SamePast.symm {α : Type*} {x y : ℤ → α} (h : SamePast x y) : SamePast y x :=
  fun n hn => (h n hn).symm

theorem pastWord_congr {α : Type*} {x y : ℤ → α} (h : SamePast x y) (n : ℕ) :
    pastWord x n = pastWord y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pastWord_succ, pastWord_succ, ih, h _ (by omega)]

theorem pastWord_eq_futureWord {α : Type*} (x : ℤ → α) (n : ℕ) :
    pastWord x n = futureWord (shift (-(n : ℤ)) x) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by push_cast; ring
    rw [pastWord_succ, futureWord_succ', ih, shift_shift, e]
    simp

end FractalGeometry
