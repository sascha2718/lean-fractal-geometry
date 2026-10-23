import Mathlib
import GeometricMeasureTheory.Box.BoxDimension


open GeometricMeasureTheory

namespace FractalGeometry

open Filter Topology

open scoped ENNReal NNReal

theorem exists_stop {F : ℕ → ℝ} {δ₀ ρ : ℝ} (hδ₀ : 0 ≤ δ₀) (hδ₀1 : δ₀ ≤ 1) (hρ : 0 ≤ ρ)
    (h0 : ρ ≤ F 0) (hδ : ∀ n, δ₀ * F n ≤ F (n + 1)) (hex : ∃ n, F n ≤ ρ) :
    ∃ n, δ₀ * ρ ≤ F n ∧ F n ≤ ρ := by
  classical
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  cases h : Nat.find hex with
  | zero => exact (mul_le_of_le_one_left hρ hδ₀1).trans h0
  | succ m =>
    have hm : ¬ F m ≤ ρ := Nat.find_min hex (by omega)
    exact (mul_le_mul_of_nonneg_left (not_le.1 hm).le hδ₀).trans (hδ m)

end FractalGeometry
