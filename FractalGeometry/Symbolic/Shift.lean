module

public import Mathlib

@[expose] public section

namespace FractalGeometry


open Finset

variable {ι : Type*}

def shift (n : ℤ) (x : ℤ → ι) : ℤ → ι := fun k => x (n + k)

@[simp] theorem shift_apply (n k : ℤ) (x : ℤ → ι) : shift n x k = x (n + k) := rfl

@[simp] theorem shift_zero (x : ℤ → ι) : shift 0 x = x := by
  funext k; simp

theorem shift_shift (m n : ℤ) (x : ℤ → ι) : shift m (shift n x) = shift (n + m) x := by
  funext k; simp [add_assoc]

end FractalGeometry
