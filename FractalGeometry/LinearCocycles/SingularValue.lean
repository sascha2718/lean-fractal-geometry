import Mathlib
import GeometricMeasureTheory.Box.BoxDimension


open GeometricMeasureTheory

namespace FractalGeometry

open Matrix

open scoped Matrix.Norms.L2Operator

noncomputable def svf (s : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  if s ≤ 1 then ‖A‖ ^ s
  else if s ≤ 2 then ‖A‖ ^ (2 - s) * |A.det| ^ (s - 1)
  else |A.det| ^ (s / 2)

theorem svf_nonneg (s : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ svf s A := by
  unfold svf
  split_ifs <;> positivity

theorem svf_mul_le {s : ℝ} (hs : 0 ≤ s) (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    svf s (A * B) ≤ svf s A * svf s B := by
  unfold svf
  split_ifs with h1 h2
  · rw [← Real.mul_rpow (norm_nonneg A) (norm_nonneg B)]
    exact Real.rpow_le_rpow (norm_nonneg _) (norm_mul_le A B) hs
  · have hn : ‖A * B‖ ^ (2 - s) ≤ ‖A‖ ^ (2 - s) * ‖B‖ ^ (2 - s) := by
      rw [← Real.mul_rpow (norm_nonneg A) (norm_nonneg B)]
      exact Real.rpow_le_rpow (norm_nonneg _) (norm_mul_le A B) (by linarith)
    rw [det_mul, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), mul_mul_mul_comm]
    exact mul_le_mul_of_nonneg_right hn (by positivity)
  · rw [det_mul, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]

end FractalGeometry
