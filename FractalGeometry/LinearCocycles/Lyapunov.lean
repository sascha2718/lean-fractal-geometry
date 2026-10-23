module

public import Mathlib
public import FractalGeometry.Symbolic.WordAverages
public import FractalGeometry.LinearCocycles.Products
public import FractalGeometry.Symbolic.Shift
public import FractalGeometry.LinearCocycles.Regularity
public import FractalGeometry.LinearCocycles.Norms
public import FractalGeometry.Symbolic.FutureWords

@[expose] public section

namespace FractalGeometry


open MeasureTheory Filter Topology Matrix

open scoped Matrix.Norms.L2Operator

theorem abs_det_le_two_mul_sq_norm (M : Matrix (Fin 2) (Fin 2) ℝ) : |M.det| ≤ 2 * ‖M‖ ^ 2 := by
  rw [det_fin_two]
  have h00 := abs_apply_le_l2_opNorm M 0 0
  have h01 := abs_apply_le_l2_opNorm M 0 1
  have h10 := abs_apply_le_l2_opNorm M 1 0
  have h11 := abs_apply_le_l2_opNorm M 1 1
  calc |M 0 0 * M 1 1 - M 0 1 * M 1 0| ≤ |M 0 0| * |M 1 1| + |M 0 1| * |M 1 0| := by
        rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
    _ ≤ ‖M‖ * ‖M‖ + ‖M‖ * ‖M‖ := by gcongr
    _ = 2 * ‖M‖ ^ 2 := by ring

theorem norm_pos_of_det_ne_zero {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.det ≠ 0) : 0 < ‖M‖ := by
  refine norm_pos_iff.2 fun h => hM ?_
  rw [h, det_zero]

theorem norm_one_matrix : ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ = 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  simp

namespace MatrixTuple

variable {ι : Type*} {A : ι → Matrix (Fin 2) (Fin 2) ℝ}

theorem log_norm_word_append_le (hA : ∀ i, (A i).det ≠ 0) (w w' : List ι) :
    Real.log ‖word A (w ++ w')‖ ≤ Real.log ‖word A w‖ + Real.log ‖word A w'‖ := by
  rw [word_append, ← Real.log_mul (norm_pos_of_det_ne_zero (det_word_ne_zero hA w)).ne'
    (norm_pos_of_det_ne_zero (det_word_ne_zero hA w')).ne']
  exact Real.log_le_log (norm_pos_of_det_ne_zero (by
    rw [det_mul]; exact mul_ne_zero (det_word_ne_zero hA w) (det_word_ne_zero hA w')))
    (Matrix.l2_opNorm_mul _ _)

theorem log_abs_det_word (hA : ∀ i, (A i).det ≠ 0) (w : List ι) :
    Real.log |(word A w).det| = (w.map fun i => Real.log |(A i).det|).sum := by
  induction w with
  | nil => simp [word]
  | cons i w ih =>
    rw [show word A (i :: w) = A i * word A w by simp [word], det_mul, abs_mul,
      Real.log_mul (abs_ne_zero.2 (hA i)) (abs_ne_zero.2 (det_word_ne_zero hA w)), ih]
    simp

theorem exists_le_log_norm_word [Fintype ι] (hA : ∀ i, (A i).det ≠ 0) :
    ∃ c : ℝ, ∀ w : List ι, c * w.length ≤ Real.log ‖word A w‖ := by
  set m : ℝ := -∑ i, abs (Real.log |(A i).det|) with hm
  have hmi : ∀ i, m ≤ Real.log |(A i).det| := fun i => by
    have := Finset.single_le_sum (f := fun j => abs (Real.log |(A j).det|))
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have := neg_abs_le (Real.log |(A i).det|)
    linarith
  have hdet : ∀ w : List ι, m * w.length ≤ Real.log |(word A w).det| := by
    intro w
    rw [log_abs_det_word hA]
    induction w with
    | nil => simp
    | cons i w ih =>
      simp only [List.length_cons, Nat.cast_succ, List.map_cons, List.sum_cons]
      linarith [hmi i]
  refine ⟨(m - Real.log 2) / 2, fun w => ?_⟩
  by_cases hw : w = []
  · subst hw
    simp
  have hpos := norm_pos_of_det_ne_zero (det_word_ne_zero hA w)
  have hd := abs_det_le_two_mul_sq_norm (word A w)
  have hl : Real.log |(word A w).det| ≤ Real.log 2 + 2 * Real.log ‖word A w‖ := by
    rw [← Real.log_rpow hpos, Real.rpow_two, ← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (abs_pos.2 (det_word_ne_zero hA w)) hd
  have hlen : (1 : ℝ) ≤ w.length := by
    exact_mod_cast List.length_pos_iff.2 hw
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have := hdet w
  nlinarith

theorem le_log_abs_det_div_norm_word_append (hA : ∀ i, (A i).det ≠ 0) (w w' : List ι) :
    Real.log (|(word A w).det| / ‖word A w‖) + Real.log (|(word A w').det| / ‖word A w'‖) ≤
      Real.log (|(word A (w ++ w')).det| / ‖word A (w ++ w')‖) := by
  have hd : ∀ v : List ι, |(word A v).det| ≠ 0 := fun v => abs_ne_zero.2 (det_word_ne_zero hA v)
  have hn : ∀ v : List ι, ‖word A v‖ ≠ 0 := fun v =>
    (norm_pos_of_det_ne_zero (det_word_ne_zero hA v)).ne'
  rw [Real.log_div (hd w) (hn w), Real.log_div (hd w') (hn w'), Real.log_div (hd _) (hn _)]
  have h1 := log_norm_word_append_le hA w w'
  have h2 : Real.log |(word A (w ++ w')).det| = Real.log |(word A w).det| +
      Real.log |(word A w').det| := by
    rw [word_append, det_mul, abs_mul, Real.log_mul (hd w) (hd w')]
  linarith

theorem norm_word_le_pow {R : ℝ} (hR : 0 ≤ R) (hAR : ∀ i, ‖A i‖ ≤ R) (w : List ι) :
    ‖word A w‖ ≤ R ^ w.length := by
  induction w with
  | nil => simp only [word_nil, norm_one_matrix, List.length_nil, pow_zero, le_refl]
  | cons i w ih =>
    rw [show word A (i :: w) = A i * word A w by simp [word], List.length_cons, pow_succ']
    exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul (hAR i) ih (norm_nonneg _) hR)

theorem exists_log_abs_det_div_norm_word_le [Fintype ι] (hA : ∀ i, (A i).det ≠ 0) :
    ∃ c : ℝ, ∀ w : List ι, Real.log (|(word A w).det| / ‖word A w‖) ≤ c * w.length := by
  set R : ℝ := 1 + ∑ i, ‖A i‖ with hR
  have hR1 : 1 ≤ R := by
    have : 0 ≤ ∑ i, ‖A i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
    linarith
  have hAR : ∀ i, ‖A i‖ ≤ R := fun i => by
    have := Finset.single_le_sum (f := fun j => ‖A j‖) (fun j _ => norm_nonneg _)
      (Finset.mem_univ i)
    linarith
  refine ⟨Real.log 2 + Real.log R, fun w => ?_⟩
  by_cases hw : w = []
  · subst hw
    simp
  have hpos := norm_pos_of_det_ne_zero (det_word_ne_zero hA w)
  have hdpos : 0 < |(word A w).det| := abs_pos.2 (det_word_ne_zero hA w)
  have h1 : Real.log (|(word A w).det| / ‖word A w‖) ≤ Real.log (2 * ‖word A w‖) := by
    refine Real.log_le_log (div_pos hdpos hpos) ?_
    rw [div_le_iff₀ hpos]
    have := abs_det_le_two_mul_sq_norm (word A w)
    nlinarith
  have h2 : Real.log (2 * ‖word A w‖) ≤ Real.log 2 + w.length * Real.log R := by
    rw [Real.log_mul (by norm_num) hpos.ne', ← Real.log_pow]
    gcongr
    exact norm_word_le_pow (by linarith) hAR w
  have hlen : (1 : ℝ) ≤ w.length := by exact_mod_cast List.length_pos_iff.2 hw
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]

theorem tendsto_lyapunov₁_of_det_ne_zero (hA : ∀ i, (A i).det ≠ 0)
    (hμ : MeasurePreserving (shift 1) μ μ) :
    Tendsto (fun n : ℕ => (∫ x, Real.log ‖word A (futureWord x n)‖ ∂μ) / n) atTop
      (𝓝 (lyapunov₁ A μ)) := by
  obtain ⟨c, hc⟩ := exists_le_log_norm_word hA
  obtain ⟨L, hL⟩ := exists_tendsto_integral_futureWord_div hμ
    (G := fun w => Real.log ‖word A w‖) (log_norm_word_append_le hA) hc
  rw [lyapunov₁, hL.limUnder_eq]
  exact hL

theorem tendsto_lyapunov₂_of_det_ne_zero (hA : ∀ i, (A i).det ≠ 0)
    (hμ : MeasurePreserving (shift 1) μ μ) :
    Tendsto (fun n : ℕ =>
      (∫ x, Real.log (|(word A (futureWord x n)).det| / ‖word A (futureWord x n)‖) ∂μ) / n)
      atTop (𝓝 (lyapunov₂ A μ)) := by
  obtain ⟨c, hc⟩ := exists_log_abs_det_div_norm_word_le hA
  obtain ⟨L, hL⟩ := exists_tendsto_integral_futureWord_div_of_superadditive hμ
    (G := fun w => Real.log (|(word A w).det| / ‖word A w‖))
    (le_log_abs_det_div_norm_word_append hA) hc
  rw [lyapunov₂, hL.limUnder_eq]
  exact hL

end MatrixTuple

end FractalGeometry
