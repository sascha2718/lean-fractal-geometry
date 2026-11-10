module

/-
The singular value function `φ^s` of `sec:Singular_value_function`.

The norm on `2 × 2` matrices is the `ℓ²` operator norm, so `‖A‖ = α_1(A)`, and
`|det A| = α_1(A) α_2(A)`.

* `svf`: the singular value function `φ^s`, defined on all real `2 × 2` matrices.
* `svf_mul_le`: sub-multiplicativity, `φ^s(AB) ≤ φ^s(A) φ^s(B)` for `s ≥ 0`.
* `norm_boxMat`, `abs_det_boxMat`: `α_1 = max{|a|, |b|}` and `α_1 α_2 = |a| |b|` for diagonal
  and anti-diagonal matrices.
* `svf_boxMat_of_le_one`, `svf_boxMat_of_le_two`, `svf_boxMat_of_two_lt`: the values
  `α_1^s`, `α_1 α_2^{s-1}` and `(α_1 α_2)^{s/2}` of `φ^s` on such matrices, with
  `α_2 = min{|a|, |b|}`.
-/
public import BoxLike.System
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

namespace BoxLike

open Matrix
open scoped Matrix.Norms.L2Operator

/-- The singular value function `φ^s(A)` of `sec:Singular_value_function`, with
`‖A‖ = α_1(A)` the `ℓ²` operator norm and `|det A| = α_1(A) α_2(A)`. -/
noncomputable def svf (s : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  if s ≤ 1 then ‖A‖ ^ s
  else if s ≤ 2 then ‖A‖ ^ (2 - s) * |A.det| ^ (s - 1)
  else |A.det| ^ (s / 2)

theorem svf_nonneg (s : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ svf s A := by
  unfold svf
  split_ifs <;> positivity

/-- `φ^s(AB) ≤ φ^s(A) φ^s(B)` for all `s ≥ 0`: the determinant is multiplicative and the
operator norm is sub-multiplicative. -/
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

/-- The supremum norm of a vector of `ℝ²`. -/
theorem norm_vec2 (x y : ℝ) : ‖(![x, y] : Fin 2 → ℝ)‖ = max |x| |y| := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (abs_nonneg x))).2 fun i => ?_
    fin_cases i <;> simp
  · refine max_le ?_ ?_
    · simpa using norm_le_pi_norm (![x, y] : Fin 2 → ℝ) 0
    · simpa using norm_le_pi_norm (![x, y] : Fin 2 → ℝ) 1

theorem conjTranspose_mul_self_boxMat (c : ZMod 2) (a b : ℝ) :
    (boxMat c a b)ᴴ * boxMat c a b =
      diagonal (if c = 0 then ![a * a, b * b] else ![b * b, a * a]) := by
  rcases zmod_two_cases c with rfl | rfl <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `α_1(A) = max{|a|, |b|}` for a diagonal or anti-diagonal matrix `A`. -/
theorem norm_boxMat (c : ZMod 2) (a b : ℝ) : ‖boxMat c a b‖ = max |a| |b| := by
  have hmax : 0 ≤ max |a| |b| := le_max_of_le_left (abs_nonneg a)
  have hsq : max |a * a| |b * b| = max |a| |b| * max |a| |b| := by
    rw [abs_mul, abs_mul]
    rcases le_total |a| |b| with h | h
    · rw [max_eq_right h, max_eq_right (mul_self_le_mul_self (abs_nonneg _) h)]
    · rw [max_eq_left h, max_eq_left (mul_self_le_mul_self (abs_nonneg _) h)]
  have h : ‖boxMat c a b‖ * ‖boxMat c a b‖ = max |a| |b| * max |a| |b| := by
    rw [← l2_opNorm_conjTranspose_mul_self, conjTranspose_mul_self_boxMat, l2_opNorm_diagonal]
    rcases zmod_two_cases c with rfl | rfl
    · simp only [ite_true]; rw [norm_vec2, hsq]
    · rw [ite_eq_right (by decide), norm_vec2, max_comm, hsq]
  rcases mul_self_eq_mul_self_iff.1 h with h | h
  · exact h
  · have := norm_nonneg (boxMat c a b); linarith

/-- `α_1(A) α_2(A) = |a| |b|` for a diagonal or anti-diagonal matrix `A`. -/
theorem abs_det_boxMat (c : ZMod 2) (a b : ℝ) : |(boxMat c a b).det| = |a| * |b| := by
  rcases zmod_two_cases c with rfl | rfl
  · simp [det_fin_two, abs_mul]
  · simp [det_fin_two, abs_mul]

/-- `|a| |b| = α_1 α_2` with `α_1 = max` and `α_2 = min`. -/
theorem abs_mul_abs_eq_max_mul_min (a b : ℝ) : |a| * |b| = max |a| |b| * min |a| |b| := by
  rcases le_total |a| |b| with h | h
  · rw [max_eq_right h, min_eq_left h, mul_comm]
  · rw [max_eq_left h, min_eq_right h]

/-- `φ^s(A) = α_1(A)^s` for `0 ≤ s ≤ 1`. -/
theorem svf_boxMat_of_le_one {s : ℝ} (hs : s ≤ 1) (c : ZMod 2) (a b : ℝ) :
    svf s (boxMat c a b) = max |a| |b| ^ s := by
  rw [svf, ite_eq_left hs, norm_boxMat]

/-- `φ^s(A) = α_1(A) α_2(A)^{s-1}` for `1 < s ≤ 2`, when `A ≠ 0`. -/
theorem svf_boxMat_of_le_two {s : ℝ} (hs1 : 1 < s) (hs2 : s ≤ 2) (c : ZMod 2) {a : ℝ} (b : ℝ)
    (ha : a ≠ 0) :
    svf s (boxMat c a b) = max |a| |b| * min |a| |b| ^ (s - 1) := by
  have hmax : 0 < max |a| |b| := lt_max_of_lt_left (abs_pos.2 ha)
  have hmin : 0 ≤ min |a| |b| := le_min (abs_nonneg _) (abs_nonneg _)
  rw [svf, ite_eq_right (not_le.2 hs1), ite_eq_left hs2, norm_boxMat, abs_det_boxMat,
    abs_mul_abs_eq_max_mul_min, Real.mul_rpow hmax.le hmin, ← mul_assoc,
    ← Real.rpow_add hmax]
  norm_num

/-- `φ^s(A) = (α_1(A) α_2(A))^{s/2}` for `s > 2`. -/
theorem svf_boxMat_of_two_lt {s : ℝ} (hs : 2 < s) (c : ZMod 2) (a b : ℝ) :
    svf s (boxMat c a b) = (max |a| |b| * min |a| |b|) ^ (s / 2) := by
  rw [svf, ite_eq_right (by linarith), ite_eq_right (not_le.2 hs), abs_det_boxMat,
    abs_mul_abs_eq_max_mul_min]

end BoxLike
