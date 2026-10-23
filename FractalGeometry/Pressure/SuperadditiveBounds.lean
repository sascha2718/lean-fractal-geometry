import Mathlib

namespace FractalGeometry

open MeasureTheory Filter Topology Set

theorem le_mul_of_superadditive {a : ℕ → ℝ} {L : ℝ}
    (ha : ∀ m n : ℕ, 0 < m → 0 < n → a m + a n ≤ a (m + n))
    (hL : Tendsto (fun n : ℕ => a n / n) atTop (𝓝 L)) {n : ℕ} (hn : 0 < n) : a n ≤ n * L := by
  have hk : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) * a n ≤ a ((k + 1) * n) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := ha ((k + 1) * n) n (Nat.mul_pos (Nat.succ_pos k) hn) hn
      rw [show (k + 1 + 1) * n = (k + 1) * n + n by ring]
      push_cast at ih ⊢
      linarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmul : Tendsto (fun k : ℕ => (k + 1) * n) atTop atTop :=
    tendsto_atTop_mono (fun k => le_trans (Nat.le_succ k) (Nat.le_mul_of_pos_right _ hn))
      tendsto_id
  have ht := hL.comp hmul
  have hle : ∀ k : ℕ, a n / n ≤ (fun n : ℕ => a n / n) ((fun k : ℕ => (k + 1) * n) k) := by
    intro k
    have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    simp only
    rw [div_le_div_iff₀ hn' (by positivity)]
    have := mul_le_mul_of_nonneg_right (hk k) hn'.le
    push_cast at this ⊢
    nlinarith
  have := ge_of_tendsto' ht hle
  rwa [div_le_iff₀ hn', mul_comm] at this

end FractalGeometry
