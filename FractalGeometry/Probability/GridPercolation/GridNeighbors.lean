import Mathlib

namespace FractalGeometry.Probability.GridPercolation

open Finset

lemma nat_mem_Icc_of_near {t : ℝ} {n : ℕ} (hlow : t - 2 < n) (hhigh : (n : ℝ) < t + 1) :
    n ∈ Finset.Icc (⌈t + 1⌉₊ - 3) (⌈t + 1⌉₊ - 1) := by
  have h1 : n < ⌈t + 1⌉₊ := Nat.lt_ceil.mpr hhigh
  have h2 : ⌈t + 1⌉₊ ≤ n + 3 := by
    apply Nat.ceil_le.mpr
    push_cast
    linarith
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

lemma card_Icc_sub_three_le (c : ℕ) : (Finset.Icc (c - 3) (c - 1)).card ≤ 3 := by
  rw [Nat.card_Icc]
  omega

end FractalGeometry.Probability.GridPercolation
