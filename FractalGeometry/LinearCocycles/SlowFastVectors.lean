module

public import Mathlib
public import FractalGeometry.LinearCocycles.Invertibility
public import FractalGeometry.LinearCocycles.Filtration
public import FractalGeometry.LinearCocycles.Lyapunov
public import FractalGeometry.LinearCocycles.Regularity
public import FractalGeometry.LinearCocycles.PlaneNorm
public import FractalGeometry.LinearCocycles.Norms

@[expose] public section

namespace FractalGeometry


open MeasureTheory Filter Topology Set Matrix

open scoped Matrix.Norms.L2Operator

namespace MatrixTuple

def perp (v : Fin 2 → ℝ) : Fin 2 → ℝ := ![-v 1, v 0]

def dot (u v : Fin 2 → ℝ) : ℝ := u 0 * v 0 + u 1 * v 1

theorem cross_mulVec (M : Matrix (Fin 2) (Fin 2) ℝ) (u v : Fin 2 → ℝ) :
    cross (M *ᵥ u) (M *ᵥ v) = M.det * cross u v := by
  simp only [cross, mulVec, dotProduct, Fin.sum_univ_two, det_fin_two]
  ring

theorem abs_cross_le (u v : Fin 2 → ℝ) : |cross u v| ≤ 2 * ‖u‖ * ‖v‖ := by
  have hu0 : |u 0| ≤ ‖u‖ := norm_le_pi_norm u 0
  have hu1 : |u 1| ≤ ‖u‖ := norm_le_pi_norm u 1
  have hv0 : |v 0| ≤ ‖v‖ := norm_le_pi_norm v 0
  have hv1 : |v 1| ≤ ‖v‖ := norm_le_pi_norm v 1
  calc |cross u v| ≤ |u 0| * |v 1| + |u 1| * |v 0| := by
        rw [cross, ← abs_mul, ← abs_mul]
        exact abs_sub _ _
    _ ≤ ‖u‖ * ‖v‖ + ‖u‖ * ‖v‖ := by gcongr
    _ = 2 * ‖u‖ * ‖v‖ := by ring

theorem norm_perp (v : Fin 2 → ℝ) : ‖perp v‖ = ‖v‖ := by
  rw [norm_fin_two, norm_fin_two]
  simp [perp, max_comm]

theorem cross_perp (v : Fin 2 → ℝ) : cross v (perp v) = v 0 ^ 2 + v 1 ^ 2 := by
  simp only [cross, perp, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem perp_ne_zero {v : Fin 2 → ℝ} (hv : v ≠ 0) : perp v ≠ 0 := by
  intro h
  apply hv
  have h0 : -v 1 = 0 := congrFun h 0
  have h1 : v 0 = 0 := congrFun h 1
  ext j; fin_cases j
  · exact h1
  · simpa using h0

theorem norm_le_eucNorm (v : Fin 2 → ℝ) : ‖v‖ ≤ eucNorm v := by
  rw [norm_fin_two, eucNorm_eq]
  refine max_le ?_ ?_
  · rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (v 1)])
  · rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (v 0)])

theorem eucNorm_smul (c : ℝ) (v : Fin 2 → ℝ) : eucNorm (c • v) = |c| * eucNorm v := by
  rw [eucNorm, eucNorm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

theorem eucNorm_neg (v : Fin 2 → ℝ) : eucNorm (-v) = eucNorm v := by
  rw [show -v = (-1 : ℝ) • v by simp, eucNorm_smul]
  simp

theorem continuous_eucNorm : Continuous eucNorm :=
  continuous_norm.comp (PiLp.continuous_toLp 2 _)

theorem sq_add_le_of_abs_le {a b m : ℝ} (ha : |a| ≤ m) (hb : |b| ≤ m) (u v : ℝ) :
    (a * u + b * v) ^ 2 ≤ 2 * m ^ 2 * (u ^ 2 + v ^ 2) := by
  have ha2 : a ^ 2 ≤ m ^ 2 := by
    rw [← sq_abs a]
    exact pow_le_pow_left₀ (abs_nonneg a) ha 2
  have hb2 : b ^ 2 ≤ m ^ 2 := by
    rw [← sq_abs b]
    exact pow_le_pow_left₀ (abs_nonneg b) hb 2
  nlinarith [sq_nonneg (a * v - b * u), sq_nonneg u, sq_nonneg v]

theorem norm_le_two_mul_of_abs_le (M : Matrix (Fin 2) (Fin 2) ℝ) {m : ℝ}
    (hm : ∀ i j, |M i j| ≤ m) : ‖M‖ ≤ 2 * m := by
  have hm0 : 0 ≤ m := (abs_nonneg _).trans (hm 0 0)
  rw [← l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, Fin.sum_univ_two, ofLp_toEuclideanCLM]
  simp only [mulVec, dotProduct, Fin.sum_univ_two]
  have h0 := sq_add_le_of_abs_le (hm 0 0) (hm 0 1) (x.ofLp 0) (x.ofLp 1)
  have h1 := sq_add_le_of_abs_le (hm 1 0) (hm 1 1) (x.ofLp 0) (x.ofLp 1)
  nlinarith

theorem abs_det_mul_norm_le (M : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) :
    |M.det| * ‖v‖ ≤ 4 * ‖M‖ * ‖M *ᵥ v‖ := by
  have h1 : |M.det| * (v 0 ^ 2 + v 1 ^ 2) ≤ 2 * ‖M *ᵥ v‖ * ‖M *ᵥ perp v‖ := by
    have h := abs_cross_le (M *ᵥ v) (M *ᵥ perp v)
    rwa [cross_mulVec, cross_perp, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ v 0 ^ 2 + v 1 ^ 2)] at h
  have h2 : ‖M *ᵥ perp v‖ ≤ 2 * ‖M‖ * ‖v‖ := by
    have h := norm_mulVec_le M (perp v)
    rwa [norm_perp] at h
  have h3 : ‖v‖ ^ 2 ≤ v 0 ^ 2 + v 1 ^ 2 := by
    rw [norm_fin_two]
    rcases max_choice |v 0| |v 1| with h | h <;> rw [h, sq_abs] <;> nlinarith [sq_nonneg (v 0),
      sq_nonneg (v 1)]
  rcases eq_or_lt_of_le (norm_nonneg v) with h | h
  · rw [← h, mul_zero]
    positivity
  · refine le_of_mul_le_mul_right ?_ h
    have hd := abs_nonneg M.det
    have hMv := norm_nonneg (M *ᵥ v)
    calc |M.det| * ‖v‖ * ‖v‖ = |M.det| * ‖v‖ ^ 2 := by ring
      _ ≤ |M.det| * (v 0 ^ 2 + v 1 ^ 2) := by gcongr
      _ ≤ 2 * ‖M *ᵥ v‖ * ‖M *ᵥ perp v‖ := h1
      _ ≤ 2 * ‖M *ᵥ v‖ * (2 * ‖M‖ * ‖v‖) := by gcongr
      _ = 4 * ‖M‖ * ‖M *ᵥ v‖ * ‖v‖ := by ring

theorem exists_slow_vector (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det ≠ 0) :
    ∃ s : Fin 2 → ℝ, eucNorm s = 1 ∧ ‖M *ᵥ s‖ ≤ 2 * |M.det| / ‖M‖ := by
  set r0 := max |M 0 0| |M 0 1| with hr0
  set r1 := max |M 1 0| |M 1 1| with hr1
  obtain ⟨s₀, hs₀M, hs₀n⟩ : ∃ s₀ : Fin 2 → ℝ, ‖M *ᵥ s₀‖ = |M.det| ∧ ‖s₀‖ = max r0 r1 := by
    rcases le_total r1 r0 with h | h
    · refine ⟨![-M 0 1, M 0 0], ?_, ?_⟩
      · rw [norm_fin_two]
        simp only [mulVec, dotProduct, Fin.sum_univ_two, det_fin_two, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        rw [show M 0 0 * -M 0 1 + M 0 1 * M 0 0 = 0 by ring, abs_zero,
          max_eq_right (abs_nonneg _)]
        congr 1
        ring
      · rw [norm_fin_two, max_eq_left h, hr0]
        simp [max_comm]
    · refine ⟨![-M 1 1, M 1 0], ?_, ?_⟩
      · rw [norm_fin_two]
        simp only [mulVec, dotProduct, Fin.sum_univ_two, det_fin_two, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        rw [show M 1 0 * -M 1 1 + M 1 1 * M 1 0 = 0 by ring, abs_zero,
          max_eq_left (abs_nonneg _), show M 0 0 * -M 1 1 + M 0 1 * M 1 0 =
            -(M 0 0 * M 1 1 - M 0 1 * M 1 0) by ring, abs_neg]
      · rw [norm_fin_two, max_eq_right h, hr1]
        simp [max_comm]
  have hm : ∀ i j, |M i j| ≤ max r0 r1 := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  have hnorm := norm_le_two_mul_of_abs_le M hm
  have hMpos : 0 < ‖M‖ := norm_pos_of_det_ne_zero hM
  have he : ‖s₀‖ ≤ eucNorm s₀ := norm_le_eucNorm s₀
  have hepos : 0 < eucNorm s₀ := by linarith
  refine ⟨(eucNorm s₀)⁻¹ • s₀, ?_, ?_⟩
  · rw [eucNorm_smul, abs_inv, abs_of_pos hepos, inv_mul_cancel₀ hepos.ne']
  · rw [mulVec_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hepos, hs₀M,
      inv_mul_eq_div, div_le_div_iff₀ hepos hMpos]
    nlinarith [abs_nonneg M.det]

theorem abs_cross_le_of_slow {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.det ≠ 0) {s : Fin 2 → ℝ}
    {C : ℝ} (hs : ‖M *ᵥ s‖ ≤ C * |M.det| / ‖M‖) (x : Fin 2 → ℝ) :
    |cross s x| ≤ 2 * C * ‖M *ᵥ x‖ / ‖M‖ := by
  have h := abs_cross_le (M *ᵥ s) (M *ᵥ x)
  rw [cross_mulVec, abs_mul] at h
  have hd : 0 < |M.det| := abs_pos.2 hM
  have hMpos : 0 < ‖M‖ := norm_pos_of_det_ne_zero hM
  have hMx := norm_nonneg (M *ᵥ x)
  have h2 : |M.det| * |cross s x| * ‖M‖ ≤ |M.det| * (2 * C * ‖M *ᵥ x‖) := by
    have h3 : |M.det| * |cross s x| ≤ 2 * (C * |M.det| / ‖M‖) * ‖M *ᵥ x‖ :=
      h.trans (by gcongr)
    have h4 : 2 * (C * |M.det| / ‖M‖) * ‖M *ᵥ x‖ * ‖M‖ = |M.det| * (2 * C * ‖M *ᵥ x‖) := by
      field_simp
    calc |M.det| * |cross s x| * ‖M‖ ≤ 2 * (C * |M.det| / ‖M‖) * ‖M *ᵥ x‖ * ‖M‖ := by
          gcongr
      _ = _ := h4
  rw [le_div_iff₀ hMpos]
  rw [mul_assoc] at h2
  exact le_of_mul_le_mul_left h2 hd

noncomputable def alignSeq (s : ℕ → Fin 2 → ℝ) : ℕ → Fin 2 → ℝ
  | 0 => s 0
  | n + 1 => if 0 ≤ dot (alignSeq s n) (s (n + 1)) then s (n + 1) else -s (n + 1)

theorem alignSeq_eq_or (s : ℕ → Fin 2 → ℝ) : ∀ n, alignSeq s n = s n ∨ alignSeq s n = -s n
  | 0 => Or.inl rfl
  | n + 1 => by
    show (if 0 ≤ dot (alignSeq s n) (s (n + 1)) then s (n + 1) else -s (n + 1)) = s (n + 1) ∨
      (if 0 ≤ dot (alignSeq s n) (s (n + 1)) then s (n + 1) else -s (n + 1)) = -s (n + 1)
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem dot_alignSeq_nonneg (s : ℕ → Fin 2 → ℝ) (n : ℕ) :
    0 ≤ dot (alignSeq s n) (alignSeq s (n + 1)) := by
  show 0 ≤ dot (alignSeq s n)
    (if 0 ≤ dot (alignSeq s n) (s (n + 1)) then s (n + 1) else -s (n + 1))
  split_ifs with h
  · exact h
  · simp only [dot, Pi.neg_apply] at h ⊢
    linarith

theorem norm_sub_le_two_abs_cross {a b : Fin 2 → ℝ} (ha : eucNorm a = 1) (hb : eucNorm b = 1)
    (hab : 0 ≤ dot a b) : ‖a - b‖ ≤ 2 * |cross a b| := by
  have ha2 : a 0 ^ 2 + a 1 ^ 2 = 1 := by rw [← eucNorm_sq, ha, one_pow]
  have hb2 : b 0 ^ 2 + b 1 ^ 2 = 1 := by rw [← eucNorm_sq, hb, one_pow]
  have hlag : dot a b ^ 2 + cross a b ^ 2 = 1 := by
    have : dot a b ^ 2 + cross a b ^ 2 = (a 0 ^ 2 + a 1 ^ 2) * (b 0 ^ 2 + b 1 ^ 2) := by
      simp only [dot, cross]
      ring
    rw [this, ha2, hb2, one_mul]
  have hdot1 : dot a b ≤ 1 := by nlinarith [sq_nonneg (cross a b), sq_nonneg (dot a b - 1)]
  have hsum : (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 ≤ (2 * |cross a b|) ^ 2 := by
    have e : (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 = 2 - 2 * dot a b := by
      simp only [dot]
      nlinarith
    rw [e, mul_pow, sq_abs]
    nlinarith
  have hc := abs_nonneg (cross a b)
  rw [norm_fin_two]
  refine max_le ?_ ?_
  · refine (sq_le_sq₀ (abs_nonneg _) (by positivity)).1 ?_
    rw [sq_abs]
    simp only [Pi.sub_apply]
    nlinarith [sq_nonneg (a 1 - b 1)]
  · refine (sq_le_sq₀ (abs_nonneg _) (by positivity)).1 ?_
    rw [sq_abs]
    simp only [Pi.sub_apply]
    nlinarith [sq_nonneg (a 0 - b 0)]

theorem eventually_le_exp_of_tendsto {a : ℕ → ℝ} {l : ℝ} (ha : ∀ n, 0 < a n)
    (h : Tendsto (fun n : ℕ => Real.log (a n) / n) atTop (𝓝 l)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, a n ≤ Real.exp (n * (l + ε)) := by
  filter_upwards [h.eventually (gt_mem_nhds (by linarith : l < l + ε)),
    eventually_gt_atTop 0] with n hn hn0
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  rw [div_lt_iff₀ hn'] at hn
  rw [← Real.exp_log (ha n)]
  exact Real.exp_le_exp.2 (by linarith)

theorem eventually_exp_le_of_tendsto {a : ℕ → ℝ} {l : ℝ} (ha : ∀ n, 0 < a n)
    (h : Tendsto (fun n : ℕ => Real.log (a n) / n) atTop (𝓝 l)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.exp (n * (l - ε)) ≤ a n := by
  filter_upwards [h.eventually (lt_mem_nhds (by linarith : l - ε < l)),
    eventually_gt_atTop 0] with n hn hn0
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  rw [lt_div_iff₀ hn'] at hn
  rw [← Real.exp_log (ha n)]
  exact Real.exp_le_exp.2 (by linarith)

theorem tendsto_log_div_of_bounds {a : ℕ → ℝ} {l : ℝ} (ha : ∀ n, 0 < a n)
    (hup : ∀ ε > 0, ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, a n ≤ C * Real.exp (n * (l + ε)))
    (hlow : ∀ ε > 0, ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop, C * Real.exp (n * (l - ε)) ≤ a n) :
    Tendsto (fun n : ℕ => Real.log (a n) / n) atTop (𝓝 l) := by
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨C, hC, hev⟩ := hlow ((l - b) / 2) (by linarith)
    have h0 : Tendsto (fun n : ℕ => Real.log C / n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    filter_upwards [hev, h0.eventually (lt_mem_nhds (by linarith : -((l - b) / 2) < 0)),
      eventually_gt_atTop 0] with n hn hn2 hn0
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
    have hlog : Real.log C + n * (l - (l - b) / 2) ≤ Real.log (a n) := by
      have := Real.log_le_log (by positivity) hn
      rwa [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp] at this
    rw [lt_div_iff₀ hn']
    rw [lt_div_iff₀ hn'] at hn2
    nlinarith
  · obtain ⟨C, hev⟩ := hup ((b - l) / 2) (by linarith)
    have hC : ∀ᶠ n : ℕ in atTop, 0 < C := hev.mono fun n hn =>
      pos_of_mul_pos_left ((ha n).trans_le hn) (Real.exp_pos _).le
    obtain ⟨n₁, hn₁⟩ := hC.exists
    have hC' : 0 < C := hn₁
    have h0 : Tendsto (fun n : ℕ => Real.log C / n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    filter_upwards [hev, h0.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < (b - l) / 2)),
      eventually_gt_atTop 0] with n hn hn2 hn0
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
    have hlog : Real.log (a n) ≤ Real.log C + n * (l + (b - l) / 2) := by
      have := Real.log_le_log (ha n) hn
      rwa [Real.log_mul hC'.ne' (Real.exp_pos _).ne', Real.log_exp] at this
    rw [div_lt_iff₀ hn']
    rw [div_lt_iff₀ hn'] at hn2
    nlinarith

theorem abs_cross_slow_succ_le {M B : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.det ≠ 0)
    (hB : B.det ≠ 0) {K : ℝ} (hK : ‖B‖ ≤ K) (hK' : ‖B⁻¹‖ ≤ K) {s s' : Fin 2 → ℝ}
    (hs : ‖M *ᵥ s‖ ≤ 2 * |M.det| / ‖M‖)
    (hs' : ‖(B * M) *ᵥ s'‖ ≤ 2 * |(B * M).det| / ‖B * M‖) :
    |cross s s'| ≤ 32 * K ^ 4 * (|M.det| / ‖M‖ ^ 2) := by
  have hBM : (B * M).det ≠ 0 := by rw [det_mul]; exact mul_ne_zero hB hM
  have hMpos : 0 < ‖M‖ := norm_pos_of_det_ne_zero hM
  have hBMpos : 0 < ‖B * M‖ := norm_pos_of_det_ne_zero hBM
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hK
  have hd := abs_nonneg M.det
  have hinv : M = B⁻¹ * (B * M) := by
    rw [← Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hB), Matrix.one_mul]
  have h1 : ‖M *ᵥ s'‖ ≤ 2 * K * (2 * |(B * M).det| / ‖B * M‖) := by
    conv_lhs => rw [hinv, ← mulVec_mulVec]
    calc ‖B⁻¹ *ᵥ ((B * M) *ᵥ s')‖ ≤ 2 * ‖B⁻¹‖ * ‖(B * M) *ᵥ s'‖ := norm_mulVec_le _ _
      _ ≤ 2 * K * (2 * |(B * M).det| / ‖B * M‖) := by gcongr
  have h2 : |(B * M).det| ≤ 2 * K ^ 2 * |M.det| := by
    rw [det_mul, abs_mul]
    have := (abs_det_le_two_mul_sq_norm B).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg B) hK 2) (by norm_num))
    exact mul_le_mul_of_nonneg_right this hd
  have h3 : ‖M‖ ≤ K * ‖B * M‖ := by
    conv_lhs => rw [hinv]
    exact (l2_opNorm_mul _ _).trans (by gcongr)
  have h4 : ‖M *ᵥ s'‖ ≤ 8 * K ^ 4 * |M.det| / ‖M‖ := by
    refine h1.trans ?_
    rw [mul_div_assoc', div_le_div_iff₀ hBMpos hMpos]
    calc 2 * K * (2 * |(B * M).det|) * ‖M‖
        ≤ 2 * K * (2 * (2 * K ^ 2 * |M.det|)) * (K * ‖B * M‖) := by gcongr
      _ = 8 * K ^ 4 * |M.det| * ‖B * M‖ := by ring
  have h5 := abs_cross_le_of_slow hM (C := 2) (by simpa using hs) s'
  calc |cross s s'| ≤ 2 * 2 * ‖M *ᵥ s'‖ / ‖M‖ := h5
    _ ≤ 2 * 2 * (8 * K ^ 4 * |M.det| / ‖M‖) / ‖M‖ := by gcongr
    _ = 32 * K ^ 4 * (|M.det| / ‖M‖ ^ 2) := by field_simp; ring

theorem exists_slow_fast_of_tendsto {M B : ℕ → Matrix (Fin 2) (Fin 2) ℝ}
    (hMB : ∀ n, M (n + 1) = B n * M n) (hM : ∀ n, (M n).det ≠ 0) (hB : ∀ n, (B n).det ≠ 0)
    {K : ℝ} (hK : ∀ n, ‖B n‖ ≤ K) (hK' : ∀ n, ‖(B n)⁻¹‖ ≤ K) {l₁ l₂ : ℝ} (hlt : l₂ < l₁)
    (h₁ : Tendsto (fun n : ℕ => Real.log ‖M n‖ / n) atTop (𝓝 l₁))
    (h₂ : Tendsto (fun n : ℕ => Real.log (|(M n).det| / ‖M n‖) / n) atTop (𝓝 l₂)) :
    ∃ u w : Fin 2 → ℝ, u ≠ 0 ∧ w ≠ 0 ∧
      Tendsto (fun n : ℕ => Real.log ‖M n *ᵥ u‖ / n) atTop (𝓝 l₂) ∧
      Tendsto (fun n : ℕ => Real.log ‖M n *ᵥ w‖ / n) atTop (𝓝 l₁) := by
  have hMn : ∀ n, 0 < ‖M n‖ := fun n => norm_pos_of_det_ne_zero (hM n)
  have hdn : ∀ n, 0 < |(M n).det| := fun n => abs_pos.2 (hM n)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)

  choose s hs1 hs2 using fun n => exists_slow_vector (M n) (hM n)
  set e := alignSeq s with he_def
  have he1 : ∀ n, eucNorm (e n) = 1 := fun n => by
    rw [he_def]
    rcases alignSeq_eq_or s n with h | h <;> rw [h]
    · exact hs1 n
    · rw [eucNorm_neg]; exact hs1 n
  have he2 : ∀ n, ‖M n *ᵥ e n‖ ≤ 2 * |(M n).det| / ‖M n‖ := fun n => by
    rw [he_def]
    rcases alignSeq_eq_or s n with h | h <;> rw [h]
    · exact hs2 n
    · rw [mulVec_neg, norm_neg]; exact hs2 n

  set ρ : ℕ → ℝ := fun n => |(M n).det| / ‖M n‖ ^ 2 with hρ_def
  have hρpos : ∀ n, 0 < ρ n := fun n => div_pos (hdn n) (pow_pos (hMn n) 2)
  set C := 64 * K ^ 4 with hC_def
  have hC0 : 0 ≤ C := by positivity
  have hstep : ∀ n, dist (e n) (e (n + 1)) ≤ C * ρ n := by
    intro n
    have hc : |cross (e n) (e (n + 1))| ≤ 32 * K ^ 4 * ρ n := by
      have hcs := abs_cross_slow_succ_le (hM n) (hB n) (hK n) (hK' n) (he2 n)
        (s' := e (n + 1)) (by rw [← hMB]; exact he2 (n + 1))
      exact hcs
    rw [dist_eq_norm]
    calc ‖e n - e (n + 1)‖ ≤ 2 * |cross (e n) (e (n + 1))| :=
          norm_sub_le_two_abs_cross (he1 n) (he1 (n + 1)) (dot_alignSeq_nonneg s n)
      _ ≤ 2 * (32 * K ^ 4 * ρ n) := by gcongr
      _ = C * ρ n := by rw [hC_def]; ring
  have hρrate : Tendsto (fun n : ℕ => Real.log (ρ n) / n) atTop (𝓝 (l₂ - l₁)) := by
    refine (h₂.sub h₁).congr fun n => ?_
    rw [← sub_div]
    congr 1
    rw [hρ_def]
    dsimp only
    rw [show |(M n).det| / ‖M n‖ ^ 2 = |(M n).det| / ‖M n‖ / ‖M n‖ by ring,
      Real.log_div (div_pos (hdn n) (hMn n)).ne' (hMn n).ne']

  have hgeo : ∀ δ, 0 < δ → ∃ N, ∀ n ≥ N,
      dist (e n) (e (n + 1)) ≤ C * Real.exp (l₂ - l₁ + δ) ^ n := by
    intro δ hδ
    obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_le_exp_of_tendsto hρpos hρrate hδ)
    refine ⟨N, fun n hn => (hstep n).trans ?_⟩
    rw [← Real.exp_nat_mul]
    exact mul_le_mul_of_nonneg_left (hN n hn) hC0

  have hr : ∀ δ, δ < l₁ - l₂ → Real.exp (l₂ - l₁ + δ) < 1 := fun δ hδ =>
    Real.exp_lt_one_iff.2 (by linarith)
  have hrate : ∀ δ, 0 < δ → δ < l₁ - l₂ → ∀ u, Tendsto e atTop (𝓝 u) → ∃ N, ∀ n ≥ N,
      ‖e n - u‖ ≤ C / (1 - Real.exp (l₂ - l₁ + δ)) * Real.exp (l₂ - l₁ + δ) ^ n := by
    intro δ hδ hδ' u hu
    obtain ⟨N, hN⟩ := hgeo δ hδ
    set r := Real.exp (l₂ - l₁ + δ) with hr_def
    have hr1 : r < 1 := hr δ hδ'
    have hd := dist_le_of_le_geometric_of_tendsto r (C * r ^ N) hr1 (f := fun k => e (k + N))
      (fun k => by
        have := hN (k + N) (by omega)
        rw [pow_add, show k + N + 1 = k + 1 + N by omega] at this
        calc dist (e (k + N)) (e (k + 1 + N)) ≤ C * (r ^ k * r ^ N) := this
          _ = C * r ^ N * r ^ k := by ring)
      ((tendsto_add_atTop_iff_nat N).2 hu)
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + N := ⟨n - N, by omega⟩
    have h := hd k
    rw [dist_eq_norm] at h
    have hr1' : 0 < 1 - r := by linarith
    calc ‖e (k + N) - u‖ ≤ C * r ^ N * r ^ k / (1 - r) := h
      _ = C / (1 - r) * r ^ (k + N) := by rw [pow_add]; field_simp
  obtain ⟨N₀, hN₀⟩ := hgeo ((l₁ - l₂) / 2) (by linarith)
  have hcauchy : CauchySeq fun k => e (k + N₀) := by
    refine cauchySeq_of_le_geometric (Real.exp (l₂ - l₁ + (l₁ - l₂) / 2))
      (C * Real.exp (l₂ - l₁ + (l₁ - l₂) / 2) ^ N₀) (hr _ (by linarith)) fun k => ?_
    have := hN₀ (k + N₀) (by omega)
    rw [pow_add, show k + N₀ + 1 = k + 1 + N₀ by omega] at this
    calc dist (e (k + N₀)) (e (k + 1 + N₀)) ≤ _ := this
      _ = _ := by ring
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hcauchy
  have heu : Tendsto e atTop (𝓝 u) := (tendsto_add_atTop_iff_nat N₀).1 hu
  have hu1 : eucNorm u = 1 := by
    have h := (continuous_eucNorm.tendsto u).comp heu
    have hconst : (eucNorm ∘ e) = fun _ => (1 : ℝ) := funext fun n => he1 n
    rw [hconst] at h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp [eucNorm] at hu1
  have hunorm : 0 < ‖u‖ := norm_pos_iff.2 hu0
  set w := perp u with hw_def
  have hw0 : w ≠ 0 := perp_ne_zero hu0
  have hwnorm : ‖w‖ = ‖u‖ := norm_perp u
  refine ⟨u, w, hu0, hw0, ?_, ?_⟩
  ·
    refine tendsto_log_div_of_bounds (fun n => norm_pos_iff.2
      (mulVec_ne_zero_of_det_ne_zero (hM n) hu0)) (fun ε hε => ?_) (fun ε hε => ?_)
    · set δ := min (ε / 2) ((l₁ - l₂) / 2) with hδ_def
      have hδ : 0 < δ := lt_min (by linarith) (by linarith)
      have hδ1 : δ < l₁ - l₂ := (min_le_right _ _).trans_lt (by linarith)
      have hδ2 : δ ≤ ε / 2 := min_le_left _ _
      obtain ⟨N, hN⟩ := hrate δ hδ hδ1 u heu
      set r := Real.exp (l₂ - l₁ + δ) with hr_def
      have hr1 : r < 1 := hr δ hδ1
      set C' := C / (1 - r) with hC'_def
      have hC'0 : 0 ≤ C' := div_nonneg hC0 (by linarith)
      refine ⟨2 + 2 * C', ?_⟩
      filter_upwards [eventually_ge_atTop N, eventually_le_exp_of_tendsto hMn h₁ hδ,
        eventually_le_exp_of_tendsto (fun n => div_pos (hdn n) (hMn n)) h₂ hδ] with n hn ha hb
      have hsplit : M n *ᵥ u = M n *ᵥ e n + M n *ᵥ (u - e n) := by
        rw [← mulVec_add, add_sub_cancel]
      have hdiff : ‖u - e n‖ ≤ C' * r ^ n := by rw [norm_sub_rev]; exact hN n hn
      have hexp1 : Real.exp (n * (l₂ + δ)) ≤ Real.exp (n * (l₂ + ε)) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n))
      have hexp2 : Real.exp (n * (l₁ + δ)) * r ^ n ≤ Real.exp (n * (l₂ + ε)) := by
        rw [hr_def, ← Real.exp_nat_mul, ← Real.exp_add]
        exact Real.exp_le_exp.2 (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      have hrn : 0 ≤ r ^ n := pow_nonneg (Real.exp_pos _).le n
      calc ‖M n *ᵥ u‖ ≤ ‖M n *ᵥ e n‖ + ‖M n *ᵥ (u - e n)‖ := by
            rw [hsplit]; exact norm_add_le _ _
        _ ≤ 2 * (|(M n).det| / ‖M n‖) + 2 * ‖M n‖ * ‖u - e n‖ := by
            gcongr
            · exact (he2 n).trans_eq (mul_div_assoc _ _ _)
            · exact norm_mulVec_le _ _
        _ ≤ 2 * Real.exp (n * (l₂ + δ)) + 2 * Real.exp (n * (l₁ + δ)) * (C' * r ^ n) := by
            gcongr
        _ = 2 * Real.exp (n * (l₂ + δ)) + 2 * C' * (Real.exp (n * (l₁ + δ)) * r ^ n) := by
            ring
        _ ≤ 2 * Real.exp (n * (l₂ + ε)) + 2 * C' * Real.exp (n * (l₂ + ε)) := by gcongr
        _ = (2 + 2 * C') * Real.exp (n * (l₂ + ε)) := by ring
    · refine ⟨‖u‖ / 4, by positivity, ?_⟩
      filter_upwards [eventually_exp_le_of_tendsto (fun n => div_pos (hdn n) (hMn n)) h₂ hε]
        with n hn
      have h := abs_det_mul_norm_le (M n) u
      have hMn' := hMn n
      calc ‖u‖ / 4 * Real.exp (n * (l₂ - ε)) ≤ ‖u‖ / 4 * (|(M n).det| / ‖M n‖) := by gcongr
        _ = |(M n).det| * ‖u‖ / (4 * ‖M n‖) := by field_simp
        _ ≤ ‖M n *ᵥ u‖ := by
            rw [div_le_iff₀ (by positivity)]
            linarith
  ·
    refine tendsto_log_div_of_bounds (fun n => norm_pos_iff.2
      (mulVec_ne_zero_of_det_ne_zero (hM n) hw0)) (fun ε hε => ?_) (fun ε hε => ?_)
    · refine ⟨2 * ‖w‖, ?_⟩
      filter_upwards [eventually_le_exp_of_tendsto hMn h₁ hε] with n hn
      calc ‖M n *ᵥ w‖ ≤ 2 * ‖M n‖ * ‖w‖ := norm_mulVec_le _ _
        _ ≤ 2 * Real.exp (n * (l₁ + ε)) * ‖w‖ := by gcongr
        _ = 2 * ‖w‖ * Real.exp (n * (l₁ + ε)) := by ring
    · refine ⟨1 / 8, by norm_num, ?_⟩
      have hcross : Tendsto (fun n => cross (e n) w) atTop (𝓝 (cross u w)) := by
        have hc : Continuous fun v : Fin 2 → ℝ => cross v w := by
          unfold cross
          fun_prop
        exact (hc.tendsto u).comp heu
      have hcu : cross u w = 1 := by
        rw [hw_def, cross_perp, ← eucNorm_sq, hu1, one_pow]
      rw [hcu] at hcross
      filter_upwards [hcross.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1)),
        eventually_exp_le_of_tendsto hMn h₁ hε] with n hn hn'
      have h := abs_cross_le_of_slow (hM n) (C := 2) (by simpa [mul_div_assoc] using he2 n) w
      have hMn' := hMn n
      have habs : 1 / 2 ≤ |cross (e n) w| := hn.le.trans (le_abs_self _)
      have h2 : ‖M n‖ / 8 ≤ ‖M n *ᵥ w‖ := by
        have h3 : 1 / 2 ≤ 2 * 2 * ‖M n *ᵥ w‖ / ‖M n‖ := habs.trans h
        rw [le_div_iff₀ hMn'] at h3
        linarith
      calc 1 / 8 * Real.exp (n * (l₁ - ε)) ≤ 1 / 8 * ‖M n‖ := by gcongr
        _ = ‖M n‖ / 8 := by ring
        _ ≤ ‖M n *ᵥ w‖ := h2

end MatrixTuple

end FractalGeometry
