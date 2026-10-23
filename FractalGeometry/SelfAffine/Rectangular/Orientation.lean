import Mathlib
import GeometricMeasureTheory.Box.ModifiedBox

open GeometricMeasureTheory

namespace FractalGeometry

open Finset

variable {ι : Type*}

def eps (o : ι → ZMod 2) (x : ℤ → ι) : ℤ → ZMod 2
  | Int.ofNat n => ∑ j ∈ range n, o (x j)
  | Int.negSucc n => ∑ j ∈ range (n + 1), o (x (-(j + 1 : ℤ)))

variable (o : ι → ZMod 2) (x : ℤ → ι)

theorem eps_natCast (n : ℕ) : eps o x n = ∑ j ∈ range n, o (x j) := rfl

theorem eps_negSucc (n : ℕ) :
    eps o x (Int.negSucc n) = ∑ j ∈ range (n + 1), o (x (-(j + 1 : ℤ))) := rfl

@[simp] theorem eps_zero : eps o x 0 = 0 := by
  simpa using eps_natCast o x 0

theorem eps_add_one (m : ℤ) : eps o x (m + 1) = eps o x m + o (x m) := by
  rcases m with n | n
  · change eps o x ((n + 1 : ℕ) : ℤ) = eps o x (n : ℤ) + o (x (n : ℤ))
    rw [eps_natCast, eps_natCast, sum_range_succ]
  · rcases n with _ | n
    · change eps o x 0 = eps o x (Int.negSucc 0) + o (x (Int.negSucc 0))
      rw [eps_zero, eps_negSucc]
      simp [Int.negSucc_eq, CharTwo.add_self_eq_zero]
    · have h : Int.negSucc (n + 1) + 1 = Int.negSucc n := by
        simp only [Int.negSucc_eq]; omega
      rw [h, eps_negSucc, eps_negSucc, sum_range_succ _ (n + 1), add_assoc]
      have hx : x (Int.negSucc (n + 1)) = x (-(((n + 1 : ℕ) : ℤ) + 1)) := by
        simp [Int.negSucc_eq]
      rw [hx, CharTwo.add_self_eq_zero, add_zero]

end FractalGeometry
