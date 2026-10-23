import Mathlib
import GeometricMeasureTheory.Box.ModifiedBox
import FractalGeometry.SelfAffine.Rectangular.Defs

open GeometricMeasureTheory

namespace FractalGeometry

open Filter Topology

namespace RectangularIFS

variable {ι : Type*} (S : RectangularIFS ι)

def RatioLowerBound (δ : ℝ) : Prop := 0 < δ ∧ ∀ p, δ ≤ |S.ratio p|

theorem exists_ratioLowerBound [Finite ι] [Nonempty ι] : ∃ δ, S.RatioLowerBound δ := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨p, -, hp⟩ := Finset.exists_min_image Finset.univ (fun p => |S.ratio p|)
    Finset.univ_nonempty
  exact ⟨|S.ratio p|, abs_pos.2 (S.ratio_ne_zero p), fun q => hp q (Finset.mem_univ _)⟩

variable {S} {δ : ℝ}

theorem RatioLowerBound.le_abs_gDeriv (hδ : S.RatioLowerBound δ) (u : List (ι × ZMod 2)) :
    δ ^ u.length ≤ |S.gDeriv u| := by
  induction u with
  | nil => simp
  | cons p u ih =>
    rw [gDeriv_cons, abs_mul, List.length_cons, pow_succ']
    exact mul_le_mul (hδ.2 p) ih (pow_nonneg hδ.1.le _) (abs_nonneg _)

variable (S) [Fintype ι]

variable {S}

variable (S)

variable {S}

end RectangularIFS

end FractalGeometry
