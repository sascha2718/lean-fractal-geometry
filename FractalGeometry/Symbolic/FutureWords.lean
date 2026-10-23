module

public import Mathlib
public import FractalGeometry.Symbolic.Shift

@[expose] public section

namespace FractalGeometry


open Filter Topology Finset

def futureWord {α : Type*} (x : ℤ → α) (n : ℕ) : List α :=
  (List.range n).map fun k : ℕ => x (k : ℤ)

@[simp] theorem futureWord_zero {α : Type*} (x : ℤ → α) : futureWord x 0 = [] := rfl

section futureWord

variable {α : Type*} (x : ℤ → α)

@[simp] theorem length_futureWord (n : ℕ) : (futureWord x n).length = n := by
  simp [futureWord]

theorem futureWord_succ (n : ℕ) : futureWord x (n + 1) = futureWord x n ++ [x n] := by
  simp [futureWord, List.range_succ]

theorem futureWord_succ' (n : ℕ) :
    futureWord x (n + 1) = x 0 :: futureWord (shift 1 x) n := by
  simp only [futureWord, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.cast_zero]
  congr 1
  apply List.map_congr_left
  intro k _
  simp [add_comm]

theorem futureWord_congr {y : ℤ → α} (h : ∀ k : ℕ, x k = y k) (n : ℕ) :
    futureWord x n = futureWord y n := by
  simp [futureWord, h]

end futureWord

end FractalGeometry
