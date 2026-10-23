import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open Filter Topology Set

noncomputable def bfloor (Γ : ℝ) (a : ℕ) : ℕ := ⌊(a : ℝ) * Γ⌋₊

lemma bfloor_le_self {Γ : ℝ} (hΓ1 : Γ ≤ 1) (a : ℕ) :
    bfloor Γ a ≤ a := by
  unfold bfloor
  apply Nat.floor_le_of_le
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  nlinarith

end FractalGeometry.Probability.GridPercolation
