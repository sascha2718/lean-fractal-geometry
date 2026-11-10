module

/-
The Lyapunov exponents of `sec:lyapunov_exponents` for an arbitrary tuple of invertible planar
matrices and for a planar self-affine system (tex lines 1495 to 1505): the limits defining
`λ_1(𝖠, μ)` and `λ_2(𝖠, μ)` exist by Fekete's lemma, since `α_1` is sub-multiplicative, `α_2`
is super-multiplicative and `μ` is invariant, and `-∞ < λ_2(𝖠, μ) ≤ λ_1(𝖠, μ)`; for contracting
linear parts `λ_1(𝖠, μ) < 0`. The exponents in the hypotheses of `thm:feng_entropy_as_limit`,
`thm:feng_entropy_zero` and `thm:feng1` are therefore genuine limits. The existence statements
concern matrices only and assume invertibility, not contraction.

* `abs_det_le_two_mul_sq_norm`, `norm_pos_of_det_ne_zero`: `|det A| ≤ 2 ‖A‖²` and `‖A‖ > 0` for
  invertible `A`.
* `MatrixTuple.log_norm_word_append_le`, `MatrixTuple.exists_le_log_norm_word`: sub-additivity
  of `log α_1(A_𝐢)` and a linear lower bound.
* `MatrixTuple.le_log_abs_det_div_norm_word_append`,
  `MatrixTuple.exists_log_abs_det_div_norm_word_le`: super-additivity of `log α_2(A_𝐢)` and a
  linear upper bound.
* `MatrixTuple.tendsto_lyapunov₁_of_det_ne_zero`, `MatrixTuple.tendsto_lyapunov₂_of_det_ne_zero`:
  the limits exist.
* `MatrixTuple.lyapunov₂_le_lyapunov₁_of_det_ne_zero`: `λ_2(𝖠, μ) ≤ λ_1(𝖠, μ)`.
* `PlanarSystem.tendsto_lyapunov₁`, `PlanarSystem.tendsto_lyapunov₂`,
  `PlanarSystem.lyapunov₂_le_lyapunov₁`, `PlanarSystem.lyapunov₁_neg`: the same for a planar
  self-affine system, and `λ_1(𝖠, μ) < 0`.
-/
public import BoxLike.Planar.Partitions

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.L2Operator

/-- `|det A| ≤ 2 ‖A‖²` for the `ℓ²` operator norm, from the bound of the entries. -/
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

/-- An invertible matrix has positive operator norm. -/
theorem norm_pos_of_det_ne_zero {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.det ≠ 0) : 0 < ‖M‖ := by
  refine norm_pos_iff.2 fun h => hM ?_
  rw [h, det_zero]

/-- The identity matrix has operator norm one. -/
theorem norm_one_matrix : ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ = 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  simp

namespace MatrixTuple

variable {ι : Type*} {A : ι → Matrix (Fin 2) (Fin 2) ℝ}

/-- `log α_1(A_{𝐢𝐣}) ≤ log α_1(A_𝐢) + log α_1(A_𝐣)`. -/
theorem log_norm_word_append_le (hA : ∀ i, (A i).det ≠ 0) (w w' : List ι) :
    Real.log ‖word A (w ++ w')‖ ≤ Real.log ‖word A w‖ + Real.log ‖word A w'‖ := by
  rw [word_append, ← Real.log_mul (norm_pos_of_det_ne_zero (det_word_ne_zero hA w)).ne'
    (norm_pos_of_det_ne_zero (det_word_ne_zero hA w')).ne']
  exact Real.log_le_log (norm_pos_of_det_ne_zero (by
    rw [det_mul]; exact mul_ne_zero (det_word_ne_zero hA w) (det_word_ne_zero hA w')))
    (Matrix.l2_opNorm_mul _ _)

/-- `log |det A_𝐢| = ∑_k log |det A_{i_k}|`. -/
theorem log_abs_det_word (hA : ∀ i, (A i).det ≠ 0) (w : List ι) :
    Real.log |(word A w).det| = (w.map fun i => Real.log |(A i).det|).sum := by
  induction w with
  | nil => simp [word]
  | cons i w ih =>
    rw [show word A (i :: w) = A i * word A w by simp [word], det_mul, abs_mul,
      Real.log_mul (abs_ne_zero.2 (hA i)) (abs_ne_zero.2 (det_word_ne_zero hA w)), ih]
    simp

/-- A linear lower bound `c |𝐢| ≤ log α_1(A_𝐢)` for a finite invertible tuple. -/
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

/-- `log α_2(A_{𝐢𝐣}) ≥ log α_2(A_𝐢) + log α_2(A_𝐣)`, with `α_2(A) = |det A| / ‖A‖`. -/
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

/-- `‖A_𝐢‖ ≤ R^{|𝐢|}` when every `‖A_i‖ ≤ R`. -/
theorem norm_word_le_pow {R : ℝ} (hR : 0 ≤ R) (hAR : ∀ i, ‖A i‖ ≤ R) (w : List ι) :
    ‖word A w‖ ≤ R ^ w.length := by
  induction w with
  | nil => simp only [word_nil, norm_one_matrix, List.length_nil, pow_zero, le_refl]
  | cons i w ih =>
    rw [show word A (i :: w) = A i * word A w by simp [word], List.length_cons, pow_succ']
    exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul (hAR i) ih (norm_nonneg _) hR)

/-- A linear upper bound `log α_2(A_𝐢) ≤ c |𝐢|` for a finite invertible tuple. -/
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

/-- `sec:lyapunov_exponents`, tex lines 1502 to 1504: the limit defining `λ_1(𝖠, μ)` exists for
an invertible tuple and an invariant `μ`, by Fekete's lemma. -/
theorem tendsto_lyapunov₁_of_det_ne_zero (hA : ∀ i, (A i).det ≠ 0)
    (hμ : MeasurePreserving (shift 1) μ μ) :
    Tendsto (fun n : ℕ => (∫ x, Real.log ‖word A (futureWord x n)‖ ∂μ) / n) atTop
      (𝓝 (lyapunov₁ A μ)) := by
  obtain ⟨c, hc⟩ := exists_le_log_norm_word hA
  obtain ⟨L, hL⟩ := exists_tendsto_integral_futureWord_div hμ
    (G := fun w => Real.log ‖word A w‖) (log_norm_word_append_le hA) hc
  rw [lyapunov₁, hL.limUnder_eq]
  exact hL

/-- `sec:lyapunov_exponents`, tex lines 1502 to 1504: the limit defining `λ_2(𝖠, μ)` exists for
an invertible tuple and an invariant `μ`, by Fekete's lemma. -/
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

/-- `sec:lyapunov_exponents`, tex line 1504: `λ_2(𝖠, μ) ≤ λ_1(𝖠, μ)` for an invertible tuple and
an invariant `μ`. The bound `α_2(A) ≤ 2 α_1(A)` used here suffices, since the constant
disappears in the limit. -/
theorem lyapunov₂_le_lyapunov₁_of_det_ne_zero (hA : ∀ i, (A i).det ≠ 0)
    (hμ : MeasurePreserving (shift 1) μ μ) : lyapunov₂ A μ ≤ lyapunov₁ A μ := by
  have h1 := tendsto_lyapunov₁_of_det_ne_zero hA hμ
  have h0 : Tendsto (fun n : ℕ => Real.log 2 / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have h1' := h1.add h0
  rw [add_zero] at h1'
  refine le_of_tendsto_of_tendsto' (tendsto_lyapunov₂_of_det_ne_zero hA hμ) h1' fun n => ?_
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n)
  have hb : ∀ w : List ι, Real.log (|(word A w).det| / ‖word A w‖) ≤
      Real.log ‖word A w‖ + Real.log 2 := fun w => by
    have hpos := norm_pos_of_det_ne_zero (det_word_ne_zero hA w)
    rw [← Real.log_mul hpos.ne' (by norm_num)]
    refine Real.log_le_log (div_pos (abs_pos.2 (det_word_ne_zero hA w)) hpos) ?_
    rw [div_le_iff₀ hpos]
    have := abs_det_le_two_mul_sq_norm (word A w)
    nlinarith
  calc ∫ x, Real.log (|(word A (futureWord x n)).det| / ‖word A (futureWord x n)‖) ∂μ
      ≤ ∫ x, (Real.log ‖word A (futureWord x n)‖ + Real.log 2) ∂μ :=
        integral_futureWord_mono (G := fun w => Real.log (|(word A w).det| / ‖word A w‖))
          (H := fun w => Real.log ‖word A w‖ + Real.log 2) hb n
    _ = ∫ x, Real.log ‖word A (futureWord x n)‖ ∂μ + Real.log 2 := by
        rw [integral_add (integrable_comp_futureWord (fun w => Real.log ‖word A w‖) n)
          (integrable_const _)]
        simp

end MatrixTuple

namespace PlanarSystem

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (P : PlanarSystem ι) {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]

/-- The limit defining `λ_1(𝖠, μ)` exists for a planar self-affine system. -/
theorem tendsto_lyapunov₁ (hμ : MeasurePreserving (shift 1) μ μ) :
    Tendsto (fun n : ℕ => (∫ x, Real.log ‖MatrixTuple.word P.mat (futureWord x n)‖ ∂μ) / n)
      atTop (𝓝 (P.lyapunov₁ μ)) :=
  MatrixTuple.tendsto_lyapunov₁_of_det_ne_zero P.det_ne_zero hμ

/-- The limit defining `λ_2(𝖠, μ)` exists for a planar self-affine system. -/
theorem tendsto_lyapunov₂ (hμ : MeasurePreserving (shift 1) μ μ) :
    Tendsto (fun n : ℕ =>
      (∫ x, Real.log (|(MatrixTuple.word P.mat (futureWord x n)).det| /
        ‖MatrixTuple.word P.mat (futureWord x n)‖) ∂μ) / n) atTop (𝓝 (P.lyapunov₂ μ)) :=
  MatrixTuple.tendsto_lyapunov₂_of_det_ne_zero P.det_ne_zero hμ

/-- `λ_2(𝖠, μ) ≤ λ_1(𝖠, μ)` for a planar self-affine system. -/
theorem lyapunov₂_le_lyapunov₁ (hμ : MeasurePreserving (shift 1) μ μ) :
    P.lyapunov₂ μ ≤ P.lyapunov₁ μ :=
  MatrixTuple.lyapunov₂_le_lyapunov₁_of_det_ne_zero P.det_ne_zero hμ

/-- `λ_1(𝖠, μ) < 0` for a planar self-affine system (tex line 1505): every `‖A_i‖ < 1`. -/
theorem lyapunov₁_neg (hμ : MeasurePreserving (shift 1) μ μ) : P.lyapunov₁ μ < 0 := by
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
  obtain ⟨i₁, -, h₁⟩ := Finset.exists_max_image Finset.univ (fun i => ‖P.mat i‖)
    Finset.univ_nonempty
  set r := ‖P.mat i₁‖
  have hr : 0 < r := norm_pos_of_det_ne_zero (P.det_ne_zero i₁)
  have hr1 : r < 1 := P.norm_lt_one i₁
  have hbound : ∀ w : List ι, Real.log ‖MatrixTuple.word P.mat w‖ ≤ Real.log r * w.length := by
    intro w
    have hpos := norm_pos_of_det_ne_zero (MatrixTuple.det_word_ne_zero P.det_ne_zero w)
    calc Real.log ‖MatrixTuple.word P.mat w‖ ≤ Real.log (r ^ w.length) :=
          Real.log_le_log hpos (P.norm_word_le hr.le (fun i => h₁ i (Finset.mem_univ i)) w)
      _ = Real.log r * w.length := by rw [Real.log_pow, mul_comm]
  have hle : P.lyapunov₁ μ ≤ Real.log r :=
    le_of_tendsto (P.tendsto_lyapunov₁ hμ) ((eventually_gt_atTop 0).mono fun n hn =>
      integral_futureWord_div_le (G := fun w => Real.log ‖MatrixTuple.word P.mat w‖) hbound hn)
  exact hle.trans_lt (Real.log_neg hr hr1)

end PlanarSystem

end BoxLike
