import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.LinearCocycles.Monomial
import FractalGeometry.LinearCocycles.SingularValue

open FractalGeometry.Ergodic

namespace FractalGeometry

open Matrix

open scoped Matrix.Norms.L2Operator

theorem norm_vec2 (x y : ℝ) : ‖(![x, y] : Fin 2 → ℝ)‖ = max |x| |y| := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (abs_nonneg x))).2 fun i => ?_
    fin_cases i <;> simp
  · refine max_le ?_ ?_
    · simpa using norm_le_pi_norm (![x, y] : Fin 2 → ℝ) 0
    · simpa using norm_le_pi_norm (![x, y] : Fin 2 → ℝ) 1

theorem conjTranspose_mul_self_monomialMatrix (c : ZMod 2) (a b : ℝ) :
    (monomialMatrix c a b)ᴴ * monomialMatrix c a b =
      diagonal (if c = 0 then ![a * a, b * b] else ![b * b, a * a]) := by
  rcases zmod_two_cases c with rfl | rfl <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem norm_monomialMatrix (c : ZMod 2) (a b : ℝ) : ‖monomialMatrix c a b‖ = max |a| |b| := by
  have hmax : 0 ≤ max |a| |b| := le_max_of_le_left (abs_nonneg a)
  have hsq : max |a * a| |b * b| = max |a| |b| * max |a| |b| := by
    rw [abs_mul, abs_mul]
    rcases le_total |a| |b| with h | h
    · rw [max_eq_right h, max_eq_right (mul_self_le_mul_self (abs_nonneg _) h)]
    · rw [max_eq_left h, max_eq_left (mul_self_le_mul_self (abs_nonneg _) h)]
  have h : ‖monomialMatrix c a b‖ * ‖monomialMatrix c a b‖ = max |a| |b| * max |a| |b| := by
    rw [← l2_opNorm_conjTranspose_mul_self, conjTranspose_mul_self_monomialMatrix, l2_opNorm_diagonal]
    rcases zmod_two_cases c with rfl | rfl
    · simp only [ite_true]; rw [norm_vec2, hsq]
    · rw [ite_eq_right (by decide), norm_vec2, max_comm, hsq]
  rcases mul_self_eq_mul_self_iff.1 h with h | h
  · exact h
  · have := norm_nonneg (monomialMatrix c a b); linarith

theorem abs_det_monomialMatrix (c : ZMod 2) (a b : ℝ) : |(monomialMatrix c a b).det| = |a| * |b| := by
  rcases zmod_two_cases c with rfl | rfl
  · simp [det_fin_two, abs_mul]
  · simp [det_fin_two, abs_mul]

theorem abs_mul_abs_eq_max_mul_min (a b : ℝ) : |a| * |b| = max |a| |b| * min |a| |b| := by
  rcases le_total |a| |b| with h | h
  · rw [max_eq_right h, min_eq_left h, mul_comm]
  · rw [max_eq_left h, min_eq_right h]

theorem svf_monomialMatrix_of_le_one {s : ℝ} (hs : s ≤ 1) (c : ZMod 2) (a b : ℝ) :
    svf s (monomialMatrix c a b) = max |a| |b| ^ s := by
  rw [svf, ite_eq_left hs, norm_monomialMatrix]

theorem svf_monomialMatrix_of_le_two {s : ℝ} (hs1 : 1 < s) (hs2 : s ≤ 2) (c : ZMod 2) {a : ℝ} (b : ℝ)
    (ha : a ≠ 0) :
    svf s (monomialMatrix c a b) = max |a| |b| * min |a| |b| ^ (s - 1) := by
  have hmax : 0 < max |a| |b| := lt_max_of_lt_left (abs_pos.2 ha)
  have hmin : 0 ≤ min |a| |b| := le_min (abs_nonneg _) (abs_nonneg _)
  rw [svf, ite_eq_right (not_le.2 hs1), ite_eq_left hs2, norm_monomialMatrix, abs_det_monomialMatrix,
    abs_mul_abs_eq_max_mul_min, Real.mul_rpow hmax.le hmin, ← mul_assoc,
    ← Real.rpow_add hmax]
  norm_num

theorem svf_monomialMatrix_of_two_lt {s : ℝ} (hs : 2 < s) (c : ZMod 2) (a b : ℝ) :
    svf s (monomialMatrix c a b) = (max |a| |b| * min |a| |b|) ^ (s / 2) := by
  rw [svf, ite_eq_right (by linarith), ite_eq_right (not_le.2 hs), abs_det_monomialMatrix,
    abs_mul_abs_eq_max_mul_min]

end FractalGeometry
