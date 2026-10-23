module

public import Mathlib
public import FractalGeometry.Symbolic.Past

@[expose] public section

namespace FractalGeometry


open MeasureTheory Set

def past {α : Type*} (x : ℤ → α) : ℕ → α := fun n => x (Int.negSucc n)

theorem past_eq_iff {α : Type*} {x y : ℤ → α} : past y = past x ↔ SamePast y x := by
  constructor
  · intro h n hn
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = Int.negSucc k := by
      rcases n with n | n
      · exact absurd hn (by simp)
      · exact ⟨n, rfl⟩
    exact congrFun h k
  · intro h
    funext k
    exact h _ (Int.negSucc_lt_zero k)

theorem measurable_past {α : Type*} [MeasurableSpace α] :
    Measurable (past : (ℤ → α) → ℕ → α) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

end FractalGeometry
