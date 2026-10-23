import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Symbolic.ParityShift

open FractalGeometry.Ergodic

namespace FractalGeometry

open Set

section Glue

variable {ι : Type*} {o : ι → ZMod 2}

open Classical in

noncomputable def glue (y y' : ℤ → ι × ZMod 2) (b : ℤ) (r : ι × ZMod 2) : ℤ → ι × ZMod 2 :=
  fun k => if k ≤ b - 2 then y k else if k = b - 1 then r else y' k

theorem glue_of_le {y y' : ℤ → ι × ZMod 2} {b k : ℤ} {r : ι × ZMod 2} (hk : k ≤ b - 2) :
    glue y y' b r k = y k := by
  simp [glue, hk]

theorem glue_of_ge {y y' : ℤ → ι × ZMod 2} {b k : ℤ} {r : ι × ZMod 2} (hk : b ≤ k) :
    glue y y' b r k = y' k := by
  have h1 : ¬ k ≤ b - 2 := by omega
  have h2 : k ≠ b - 1 := by omega
  simp [glue, h1, h2]

theorem glue_sub_one {y y' : ℤ → ι × ZMod 2} {b : ℤ} {r : ι × ZMod 2} :
    glue y y' b r (b - 1) = r := by
  have h1 : ¬ b - 1 ≤ b - 2 := by omega
  simp [glue, h1]

theorem glue_mem_subshift {y y' : ℤ → ι × ZMod 2} (hy : y ∈ subshift o) (hy' : y' ∈ subshift o)
    {b : ℤ} {r : ι × ZMod 2} (h1 : Trans o (y (b - 2)) r) (h2 : Trans o r (y' b)) :
    glue y y' b r ∈ subshift o := by
  intro k
  rcases lt_trichotomy k (b - 2) with hk | hk | hk
  · rw [glue_of_le hk.le, glue_of_le (by omega)]
    exact hy k
  · subst hk
    rw [glue_of_le le_rfl, show b - 2 + 1 = b - 1 by ring, glue_sub_one]
    exact h1
  · rcases eq_or_lt_of_le (show b - 1 ≤ k by omega) with hk' | hk'
    · subst hk'
      rw [glue_sub_one, show b - 1 + 1 = b by ring, glue_of_ge le_rfl]
      exact h2
    · rw [glue_of_ge (by omega), glue_of_ge (by omega)]
      exact hy' k

end Glue

end FractalGeometry
