import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.Floor

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

lemma bfloor_cast_le {Γ : ℝ} (hΓ0 : 0 ≤ Γ) (a : ℕ) :
    (bfloor Γ a : ℝ) ≤ (a : ℝ) * Γ := by
  unfold bfloor
  exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) hΓ0)

lemma lt_bfloor_cast_add_one (Γ : ℝ) (a : ℕ) :
    (a : ℝ) * Γ < (bfloor Γ a : ℝ) + 1 := by
  unfold bfloor
  exact Nat.lt_floor_add_one _

end FractalGeometry.Probability.GridPercolation
