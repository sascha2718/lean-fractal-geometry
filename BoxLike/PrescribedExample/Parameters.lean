module

/-
The choice of the parameter `p` in `ex:projection_double_dimensional`, tex lines 2769 to 2784:
`H` decreases and `J` increases on `(1/2, 1)`, the ratio `(log 2 + H(p)) / (log 2 + J(p))`
decreases continuously from one to zero, and so a unique `p ∈ (1/2, 1)` has ratio `s_2/s_1`
for every `0 < s_2 < s_1`. The parameters `a = (p/2)^{1/s_1}` and `b = ((1-p)/2)^{1/s_1}`
satisfy `2 a^{s_1} + 2 b^{s_1} = 1`.

* `PrescribedExample.H_eq_binEntropy`, `PrescribedExample.H_add_J`: `H` is Mathlib's binary
  entropy, and `H(p) + J(p) = -log(p(1-p))`.
* `PrescribedExample.strictAntiOn_H`, `PrescribedExample.strictMonoOn_J`: `H` decreases on
  `[1/2, 1]` and `J` increases on `[1/2, 1)`.
* `PrescribedExample.continuousOn_ratio`, `PrescribedExample.strictAntiOn_ratio`: the ratio is
  continuous and strictly decreasing on `[1/2, 1)`.
* `PrescribedExample.ratio_half`, `PrescribedExample.tendsto_ratio_half`,
  `PrescribedExample.tendsto_ratio_one`: the ratio is one at `1/2` and tends to one at `1/2`
  and to zero at `1`.
* `PrescribedExample.existsUnique_ratio_eq`, `PrescribedExample.existsUnique_p`: the unique
  `p ∈ (1/2, 1)` with ratio `y ∈ (0, 1)`, in particular with ratio `s_2/s_1`.
* `PrescribedExample.aOf_rpow`, `PrescribedExample.bOf_rpow`,
  `PrescribedExample.two_mul_aOf_rpow_add`: `a^{s_1} = p/2`, `b^{s_1} = (1-p)/2` and
  `2 a^{s_1} + 2 b^{s_1} = 1`.
* `PrescribedExample.paramsOf_bounds`: `0 < b < a < 1/2`.
-/
public import BoxLike.PrescribedExample.Defs
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

namespace BoxLike

namespace PrescribedExample

open Real Filter Topology Set

/-- The function `H` of `ex:projection_double_dimensional` is Mathlib's binary entropy. -/
theorem H_eq_binEntropy (p : ℝ) : H p = binEntropy p := by
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog_def, H]
  ring

/-- `H(p) + J(p) = -log(p (1 - p))` for `0 < p < 1`, the identity behind the monotonicity of
`J` in `ex:projection_double_dimensional`. -/
theorem H_add_J {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) : H p + J p = -Real.log (p * (1 - p)) := by
  rw [Real.log_mul hp₀.ne' (by linarith)]
  simp only [H, J]
  ring

/-- `H(p) ≥ 0` for `0 ≤ p ≤ 1`, as in `ex:projection_double_dimensional`. -/
theorem H_nonneg {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : 0 ≤ H p := by
  rw [H_eq_binEntropy]
  exact binEntropy_nonneg hp₀ hp₁

/-- `H(p) ≤ log 2`, as in `ex:projection_double_dimensional`. -/
theorem H_le_log_two (p : ℝ) : H p ≤ Real.log 2 := by
  rw [H_eq_binEntropy]
  exact binEntropy_le_log_two

/-- `J(p) > 0` for `0 < p < 1`, as in `ex:projection_double_dimensional`. -/
theorem J_pos {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) : 0 < J p := by
  have h1 : Real.log (1 - p) < 0 := Real.log_neg (by linarith) (by linarith)
  have h2 : Real.log p < 0 := Real.log_neg hp₀ hp₁
  have h3 : 0 < -p * Real.log (1 - p) := by nlinarith
  have h4 : 0 ≤ -(1 - p) * Real.log p := by nlinarith
  simp only [J]
  linarith

/-- `H(1/2) = log 2` in `ex:projection_double_dimensional`. -/
theorem H_half : H (1 / 2) = Real.log 2 := by
  rw [H_eq_binEntropy, one_div, binEntropy_two_inv]

/-- `J(1/2) = log 2` in `ex:projection_double_dimensional`. -/
theorem J_half : J (1 / 2) = Real.log 2 := by
  rw [J, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, one_div, Real.log_inv]
  ring

/-- The ratio of `ex:projection_double_dimensional` is one at `p = 1/2`. -/
theorem ratio_half : ratio (1 / 2) = 1 := by
  have h : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [ratio, H_half, J_half, div_self (by linarith)]

/-- `H` decreases on `[1/2, 1]`, as stated in `ex:projection_double_dimensional`. -/
theorem strictAntiOn_H : StrictAntiOn H (Icc (1 / 2) 1) := by
  have h := binEntropy_strictAntiOn
  rw [← one_div] at h
  intro x hx y hy hxy
  rw [H_eq_binEntropy, H_eq_binEntropy]
  exact h hx hy hxy

/-- `J` increases on `[1/2, 1)`, as stated in `ex:projection_double_dimensional`: by
`H_add_J`, `J(p) = -log(p(1-p)) - H(p)`, the function `p(1-p)` decreases on `[1/2, 1]` and `H`
decreases there. -/
theorem strictMonoOn_J : StrictMonoOn J (Ico (1 / 2) 1) := by
  intro x hx y hy hxy
  have hx₀ : 0 < x := by linarith [hx.1]
  have hy₀ : 0 < y := by linarith [hy.1]
  have hH : H y < H x :=
    strictAntiOn_H ⟨hx.1, hx.2.le⟩ ⟨hy.1, hy.2.le⟩ hxy
  have hprod : y * (1 - y) < x * (1 - x) := by nlinarith [hx.1, hy.1]
  have hlog : Real.log (y * (1 - y)) < Real.log (x * (1 - x)) :=
    Real.log_lt_log (mul_pos hy₀ (by linarith [hy.2])) hprod
  have ex := H_add_J hx₀ hx.2
  have ey := H_add_J hy₀ hy.2
  linarith

/-- `J` is continuous on `(0, 1)`. -/
theorem continuousOn_J : ContinuousOn J (Ioo 0 1) := by
  intro x hx
  have h1 : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
  have h2 : x ≠ 0 := hx.1.ne'
  refine ContinuousAt.continuousWithinAt ?_
  unfold J
  fun_prop (disch := assumption)

/-- The numerator `log 2 + H(p)` of the ratio is positive on `[0, 1]`. -/
theorem num_pos {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : 0 < Real.log 2 + H p := by
  linarith [H_nonneg hp₀ hp₁, Real.log_pos one_lt_two]

/-- The denominator `log 2 + J(p)` of the ratio is positive on `(0, 1)`. -/
theorem den_pos {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) : 0 < Real.log 2 + J p := by
  linarith [J_pos hp₀ hp₁, Real.log_pos one_lt_two]

/-- The ratio `(log 2 + H(p)) / (log 2 + J(p))` of `ex:projection_double_dimensional` is
continuous on `[1/2, 1)`. -/
theorem continuousOn_ratio : ContinuousOn ratio (Ico (1 / 2) 1) := by
  have hsub : Ico (1 / 2 : ℝ) 1 ⊆ Ioo 0 1 := fun x hx => ⟨by linarith [hx.1], hx.2⟩
  refine ContinuousOn.div ?_ ?_ fun x hx => (den_pos (hsub hx).1 (hsub hx).2).ne'
  · refine continuousOn_const.add ?_
    have h : Continuous H := by
      rw [show H = binEntropy from funext H_eq_binEntropy]
      exact binEntropy_continuous
    exact h.continuousOn
  · exact continuousOn_const.add (continuousOn_J.mono hsub)

/-- The ratio of `ex:projection_double_dimensional` decreases strictly on `[1/2, 1)`: its
numerator is positive and decreasing, its denominator is positive and increasing. -/
theorem strictAntiOn_ratio : StrictAntiOn ratio (Ico (1 / 2) 1) := by
  intro x hx y hy hxy
  have hx₀ : 0 < x := by linarith [hx.1]
  have hy₀ : 0 < y := by linarith [hy.1]
  have hH : H y < H x := strictAntiOn_H ⟨hx.1, hx.2.le⟩ ⟨hy.1, hy.2.le⟩ hxy
  have hJ : J x < J y := strictMonoOn_J hx hy hxy
  have hnx := num_pos hx₀.le hx.2.le
  have hny := num_pos hy₀.le hy.2.le
  have hdx := den_pos hx₀ hx.2
  have hdy := den_pos hy₀ hy.2
  rw [ratio, ratio, div_lt_div_iff₀ hdy hdx]
  have h1 : (Real.log 2 + H y) * (Real.log 2 + J x) < (Real.log 2 + H x) * (Real.log 2 + J x) :=
    mul_lt_mul_of_pos_right (by linarith) hdx
  have h2 : (Real.log 2 + H x) * (Real.log 2 + J x) < (Real.log 2 + H x) * (Real.log 2 + J y) :=
    mul_lt_mul_of_pos_left (by linarith) hnx
  linarith

/-- The ratio of `ex:projection_double_dimensional` tends to one as `p` decreases to `1/2`. -/
theorem tendsto_ratio_half : Tendsto ratio (𝓝[>] (1 / 2)) (𝓝 1) := by
  have h := (continuousOn_ratio (1 / 2) ⟨le_rfl, by norm_num⟩).tendsto
  rw [ratio_half] at h
  exact h.mono_left (nhdsWithin_le_of_mem (Ico_mem_nhdsGT (by norm_num)))

/-- The denominator `log 2 + J(p)` tends to infinity as `p` increases to one: it is at least
`-(1/2) log(1 - p)` on `[1/2, 1)`. -/
theorem tendsto_den_one : Tendsto (fun p => Real.log 2 + J p) (𝓝[<] 1) atTop := by
  have hlog : Tendsto (fun p : ℝ => Real.log (1 - p)) (𝓝[<] 1) atBot := by
    refine Real.tendsto_log_nhdsGT_zero.comp ?_
    have hc : Continuous fun p : ℝ => 1 - p := continuous_sub_left 1
    have hm : MapsTo (fun p : ℝ => 1 - p) (Iio 1) (Ioi 0) := fun p hp => by
      simp only [mem_Iio, mem_Ioi, sub_pos] at hp ⊢
      exact hp
    have := hc.continuousWithinAt.tendsto_nhdsWithin hm (x := 1)
    rwa [sub_self] at this
  have hK : Tendsto (fun p : ℝ => -(1 / 2) * Real.log (1 - p)) (𝓝[<] 1) atTop :=
    (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
      (tendsto_neg_atTop_iff.mpr hlog)).congr fun p => by ring
  refine tendsto_atTop_mono' _ ?_ hK
  filter_upwards [Ico_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with p hp
  have hp₀ : 0 < p := by linarith [hp.1]
  have hl1 : Real.log (1 - p) < 0 := Real.log_neg (by linarith [hp.2]) (by linarith [hp.2])
  have hl2 : Real.log p < 0 := Real.log_neg hp₀ hp.2
  have h4 : 0 ≤ -(1 - p) * Real.log p := by nlinarith [hp.2]
  have h5 : -(1 / 2) * Real.log (1 - p) ≤ -p * Real.log (1 - p) := by nlinarith [hp.1]
  have h6 : 0 < Real.log 2 := Real.log_pos one_lt_two
  simp only [J]
  linarith

/-- The ratio of `ex:projection_double_dimensional` tends to zero as `p` increases to one: its
numerator lies in `(0, 2 log 2]` and its denominator tends to infinity. -/
theorem tendsto_ratio_one : Tendsto ratio (𝓝[<] 1) (𝓝 0) := by
  have hup : Tendsto (fun p => 2 * Real.log 2 * (Real.log 2 + J p)⁻¹) (𝓝[<] 1) (𝓝 0) := by
    simpa using tendsto_den_one.inv_tendsto_atTop.const_mul (2 * Real.log 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [Ico_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with p hp
    have hp₀ : 0 < p := by linarith [hp.1]
    exact (div_pos (num_pos hp₀.le hp.2.le) (den_pos hp₀ hp.2)).le
  · filter_upwards [Ico_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with p hp
    have hp₀ : 0 < p := by linarith [hp.1]
    rw [ratio, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (den_pos hp₀ hp.2).le)
    linarith [H_le_log_two p]

/-- For every `y ∈ (0, 1)` there is exactly one `p ∈ (1/2, 1)` with
`(log 2 + H(p)) / (log 2 + J(p)) = y`: the ratio decreases continuously from one to zero
(`ex:projection_double_dimensional`). -/
theorem existsUnique_ratio_eq {y : ℝ} (hy₀ : 0 < y) (hy₁ : y < 1) :
    ∃! p : ℝ, p ∈ Ioo (1 / 2) 1 ∧ ratio p = y := by
  obtain ⟨q, hq, hqy⟩ : ∃ q ∈ Ioo (1 / 2 : ℝ) 1, ratio q < y := by
    have h1 : ∀ᶠ p in 𝓝[<] (1 : ℝ), ratio p < y := tendsto_ratio_one (gt_mem_nhds hy₀)
    have h2 : ∀ᶠ p in 𝓝[<] (1 : ℝ), p ∈ Ioo (1 / 2 : ℝ) 1 :=
      Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)
    obtain ⟨q, hq1, hq2⟩ := (h1.and h2).exists
    exact ⟨q, hq2, hq1⟩
  have hsub : Icc (1 / 2) q ⊆ Ico (1 / 2 : ℝ) 1 := fun x hx => ⟨hx.1, hx.2.trans_lt hq.2⟩
  obtain ⟨p, hp, hpy⟩ := intermediate_value_Icc' hq.1.le (continuousOn_ratio.mono hsub)
    ⟨hqy.le, by rw [ratio_half]; exact hy₁.le⟩
  have hp' : p ∈ Ioo (1 / 2 : ℝ) 1 := by
    refine ⟨lt_of_le_of_ne hp.1 ?_, hp.2.trans_lt hq.2⟩
    rintro rfl
    rw [ratio_half] at hpy
    exact hy₁.ne' hpy
  refine ⟨p, ⟨hp', hpy⟩, fun r hr => ?_⟩
  exact strictAntiOn_ratio.injOn ⟨hr.1.1.le, hr.1.2⟩ ⟨hp'.1.le, hp'.2⟩ (hr.2.trans hpy.symm)

/-- The choice of `p` in `ex:projection_double_dimensional`: for `0 < s_2 < s_1` there is
exactly one `p ∈ (1/2, 1)` with `(log 2 + H(p)) / (log 2 + J(p)) = s_2/s_1`. -/
theorem existsUnique_p {s₁ s₂ : ℝ} (h₀ : 0 < s₂) (h₁₂ : s₂ < s₁) :
    ∃! p : ℝ, p ∈ Ioo (1 / 2) 1 ∧ ratio p = s₂ / s₁ :=
  existsUnique_ratio_eq (div_pos h₀ (h₀.trans h₁₂)) ((div_lt_one (h₀.trans h₁₂)).2 h₁₂)

/-- `a^{s_1} = p/2` for `a = (p/2)^{1/s_1}` (`ex:projection_double_dimensional`). -/
theorem aOf_rpow {s₁ p : ℝ} (hs : 0 < s₁) (hp : 0 ≤ p) : aOf s₁ p ^ s₁ = p / 2 := by
  rw [aOf, ← Real.rpow_mul (by linarith), one_div_mul_cancel hs.ne', Real.rpow_one]

/-- `b^{s_1} = (1-p)/2` for `b = ((1-p)/2)^{1/s_1}` (`ex:projection_double_dimensional`). -/
theorem bOf_rpow {s₁ p : ℝ} (hs : 0 < s₁) (hp : p ≤ 1) : bOf s₁ p ^ s₁ = (1 - p) / 2 := by
  rw [bOf, ← Real.rpow_mul (by linarith), one_div_mul_cancel hs.ne', Real.rpow_one]

/-- `2 a^{s_1} + 2 b^{s_1} = 1` (`ex:projection_double_dimensional`). -/
theorem two_mul_aOf_rpow_add {s₁ p : ℝ} (hs : 0 < s₁) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    2 * aOf s₁ p ^ s₁ + 2 * bOf s₁ p ^ s₁ = 1 := by
  rw [aOf_rpow hs hp₀, bOf_rpow hs hp₁]
  ring

/-- `0 < b < a < 1/2` for the parameters of `ex:projection_double_dimensional`. -/
theorem paramsOf_bounds {s₁ p : ℝ} (hs₀ : 0 < s₁) (hs₁ : s₁ ≤ 1) (hp₀ : 1 / 2 < p)
    (hp₁ : p < 1) : 0 < bOf s₁ p ∧ bOf s₁ p < aOf s₁ p ∧ aOf s₁ p < 1 / 2 :=
  ⟨(paramsOf s₁ p hs₀ hs₁ hp₀ hp₁).b_pos, (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁).b_lt_a,
    (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁).a_lt_half⟩

end PrescribedExample

end BoxLike
