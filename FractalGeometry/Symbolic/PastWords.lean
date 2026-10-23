module

public import Mathlib

@[expose] public section

namespace FractalGeometry


open Matrix

def pastWord {α : Type*} (x : ℤ → α) : ℕ → List α
  | 0 => []
  | n + 1 => x (-((n : ℤ) + 1)) :: pastWord x n

@[simp] theorem pastWord_zero {α : Type*} (x : ℤ → α) : pastWord x 0 = [] := rfl

@[simp] theorem pastWord_succ {α : Type*} (x : ℤ → α) (n : ℕ) :
    pastWord x (n + 1) = x (-((n : ℤ) + 1)) :: pastWord x n := rfl

end FractalGeometry
