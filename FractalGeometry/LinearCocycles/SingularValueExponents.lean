import Mathlib
import GeometricMeasureTheory.Box.BoxDimension


open GeometricMeasureTheory

namespace FractalGeometry

open Filter Topology

noncomputable def svfExp (s : ℝ) : ℝ := if s ≤ 1 then s else if s ≤ 2 then 1 else s / 2

theorem svfExp_le_svfExp_add (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) : svfExp s ≤ svfExp (s + δ) := by
  unfold svfExp
  split_ifs <;> linarith

theorem svfExp_add_le (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) : svfExp (s + δ) ≤ svfExp s + δ := by
  unfold svfExp
  split_ifs <;> linarith

theorem rpow_le_rpow_mul_rpow_sub {x y u : ℝ} (δ : ℝ) (hy : 0 < y) (hyx : y ≤ x)
    (hu : 0 ≤ u) : y ^ δ ≤ x ^ u * y ^ (δ - u) :=
  calc y ^ δ = y ^ u * y ^ (δ - u) := by rw [← Real.rpow_add hy]; congr 1; ring
    _ ≤ x ^ u * y ^ (δ - u) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hy.le hyx hu) (Real.rpow_nonneg hy.le _)

theorem rpow_mul_rpow_sub_le {x y u δ : ℝ} (hy : 0 < y) (hyx : y ≤ x) (huδ : u ≤ δ) :
    x ^ u * y ^ (δ - u) ≤ x ^ δ :=
  have hx : 0 < x := hy.trans_le hyx
  calc x ^ u * y ^ (δ - u) ≤ x ^ u * x ^ (δ - u) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy.le hyx (sub_nonneg.2 huδ))
        (Real.rpow_nonneg hx.le _)
    _ = x ^ δ := by rw [← Real.rpow_add hx]; congr 1; ring

end FractalGeometry
