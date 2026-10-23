import Mathlib
import GeometricMeasureTheory.Box.ModifiedBox
import FractalGeometry.SelfAffine.Rectangular.Attractor
import FractalGeometry.SelfAffine.Rectangular.Coding
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.SelfAffine.Rectangular.ModifiedPressure
import FractalGeometry.SelfAffine.Rectangular.OpenSet
import FractalGeometry.SelfAffine.Rectangular.SingularValues
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.Shift

open GeometricMeasureTheory

namespace FractalGeometry

open Filter Topology

open scoped ENNReal NNReal

namespace RectangularIFS

variable {ι : Type*} (S : RectangularIFS ι)

variable {S} in

theorem Bounds.exists_proj_eq_phiWord {r M : ℝ} (hS : S.Bounds r M) (n : ℕ) (x : ℤ → ι) :
    ∃ y, S.proj x = S.phiWord (futureWord x n) (S.proj y) := by
  induction n generalizing x with
  | zero => exact ⟨x, rfl⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih (shift 1 x)
    refine ⟨y, ?_⟩
    rw [hS.proj_eq x, futureWord_succ', phiWord_cons, Function.comp_apply, hy]

theorem abs_coord_phiWord_sub_le {D : ℝ}
    (hdist : ∀ x ∈ S.attractor, ∀ x' ∈ S.attractor, dist x x' ≤ D) (c : ZMod 2) (w : List ι)
    {p q : ℝ × ℝ} (hp : p ∈ S.attractor) (hq : q ∈ S.attractor) :
    |coord c (S.phiWord w p) - coord c (S.phiWord w q)| ≤ S.side c w * D := by
  rw [coord_phiWord, coord_phiWord, S.gWord_apply (S.codeWord c w) (coord (c + S.oWord w) p),
    S.gWord_apply (S.codeWord c w) (coord (c + S.oWord w) q)]
  calc |S.gDeriv (S.codeWord c w) * coord (c + S.oWord w) p + S.gWord (S.codeWord c w) 0 -
        (S.gDeriv (S.codeWord c w) * coord (c + S.oWord w) q + S.gWord (S.codeWord c w) 0)|
      = S.side c w * |coord (c + S.oWord w) p - coord (c + S.oWord w) q| := by
        unfold side
        rw [← abs_mul]
        ring_nf
    _ ≤ S.side c w * D := mul_le_mul_of_nonneg_left
        ((abs_coord_sub_le _ p q).trans (hdist p hp q hq)) (S.side_pos c w).le

theorem alpha₁_nil : S.alpha₁ [] = 1 := by
  simp [alpha₁, wordBase, wordHeight]

theorem alpha₂_nil : S.alpha₂ [] = 1 := by
  simp [alpha₂, wordBase, wordHeight]

variable {S} {r M δ₀ : ℝ}

theorem Bounds.alpha₂_le (hS : S.Bounds r M) (w : List ι) : S.alpha₂ w ≤ r ^ w.length :=
  (S.alpha₂_le_alpha₁ w).trans (hS.alpha₁_le w)

theorem RatioLowerBound.side_append_ge (hδ₀ : S.RatioLowerBound δ₀) (c : ZMod 2) (w : List ι)
    (j : ι) : δ₀ * S.side c w ≤ S.side c (w ++ [j]) := by
  rw [side_append, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (S.side_pos c w).le
  simpa [side] using hδ₀.2 (j, c + S.oWord w)

theorem RatioLowerBound.alpha₂_append_ge (hδ₀ : S.RatioLowerBound δ₀) (w : List ι) (j : ι) :
    δ₀ * S.alpha₂ w ≤ S.alpha₂ (w ++ [j]) := by
  change δ₀ * min (S.side 0 w) (S.side 1 w) ≤ min (S.side 0 (w ++ [j])) (S.side 1 (w ++ [j]))
  rw [mul_min_of_nonneg _ _ hδ₀.1.le]
  exact min_le_min (hδ₀.side_append_ge 0 w j) (hδ₀.side_append_ge 1 w j)

variable (S)

end RectangularIFS

end FractalGeometry
