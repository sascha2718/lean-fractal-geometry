module

public import Mathlib

@[expose] public section

namespace FractalGeometry


open MeasureTheory Filter Topology Matrix

open scoped Matrix.Norms.L2Operator

theorem abs_apply_le_l2_opNorm (M : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) : |M i j| ≤ ‖M‖ := by
  have h := M.l2_opNorm_mulVec (EuclideanSpace.single j (1 : ℝ))
  rw [EuclideanSpace.single, PiLp.norm_single, norm_one, mul_one] at h
  refine le_trans (le_of_eq ?_) ((PiLp.norm_apply_le _ i).trans h)
  simp

theorem norm_mulVec_le (M : Matrix (Fin 2) (Fin 2) ℝ) (u : Fin 2 → ℝ) :
    ‖M *ᵥ u‖ ≤ 2 * ‖M‖ * ‖u‖ := by
  have hM : 0 ≤ ‖M‖ := norm_nonneg M
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have h0 : |u 0| ≤ ‖u‖ := norm_le_pi_norm u 0
  have h1 : |u 1| ≤ ‖u‖ := norm_le_pi_norm u 1
  have := abs_apply_le_l2_opNorm M i 0
  have := abs_apply_le_l2_opNorm M i 1
  nlinarith [abs_nonneg (M i 0), abs_nonneg (M i 1), abs_nonneg (u 0), abs_nonneg (u 1)]

end FractalGeometry
