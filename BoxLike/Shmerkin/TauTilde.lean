module

public import BoxLike.Shmerkin.Limit

@[expose] public section

/-!
# Shmerkin, Theorem 6.6: the exponent `τ̃(q)`

* `tauTildeFun`, `tauTildeFun_strictMono`, `exists_unique_tauTildeFun_eq_one`, `tauTilde`:
  `Φ_q(τ) = ∑_j p_j^q |r_j|^{-τ}` is continuous and strictly increasing, and `τ̃(q)` is the unique
  solution of `Φ_q(τ̃) = 1` (Theorem 6.6).
* `lt_tauTilde_iff`: `β < τ̃(q)` if and only if `Φ_q(β) < 1`, the reformulation used in
  `BoxLike.ShmerkinLqDimension`.
* `tendsto_tauTilde`: (6.6), `τ̃(q) = lim_m -log₂ ∑_{u ∈ Ω_m} p_u^q / m`.
-/

open MeasureTheory Filter Topology Set

namespace BoxLike
namespace Shmerkin

variable {κ : Type*} [Fintype κ] {r p : κ → ℝ}

/-- `Φ_q(τ) = ∑_j p_j^q |r_j|^{-τ}` (Shmerkin, Theorem 6.6). -/
noncomputable def tauTildeFun (r p : κ → ℝ) (q τ : ℝ) : ℝ := ∑ j, p j ^ q * |r j| ^ (-τ)

/-- `Φ_q` is continuous. -/
theorem continuous_tauTildeFun (hr : ∀ j, r j ≠ 0) (q : ℝ) :
    Continuous (tauTildeFun r p q) :=
  continuous_finsetSum _ fun j _ => continuous_const.mul
    (continuous_const.rpow continuous_neg fun _ => Or.inl (abs_pos.mpr (hr j)).ne')

/-- `Φ_q` is strictly increasing, since `|r_j| < 1`. -/
theorem tauTildeFun_strictMono [Nonempty κ] (hr : ∀ j, r j ≠ 0) (hr1 : ∀ j, |r j| < 1)
    (hp : ∀ j, 0 < p j) (q : ℝ) : StrictMono (tauTildeFun r p q) := by
  intro τ₁ τ₂ hτ
  refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun j _ =>
    mul_lt_mul_of_pos_left ?_ (Real.rpow_pos_of_pos (hp j) _)
  exact Real.rpow_lt_rpow_of_exponent_gt (abs_pos.mpr (hr j)) (hr1 j) (by linarith)

/-- `Φ_q(τ̃) = 1` has a unique solution, and it is `≥ 0` for `q ≥ 1`. -/
theorem exists_unique_tauTildeFun_eq_one [Nonempty κ] (hr : ∀ j, r j ≠ 0)
    (hr1 : ∀ j, |r j| < 1) (hp : ∀ j, 0 < p j) (hp1 : ∑ j, p j = 1) {q : ℝ} (hq : 1 ≤ q) :
    ∃! τ : ℝ, tauTildeFun r p q τ = 1 := by
  have hmono := tauTildeFun_strictMono hr hr1 hp q
  refine existsUnique_of_exists_of_unique ?_ fun a b ha hb => hmono.injective (ha.trans hb.symm)
  -- `Φ_q(0) ≤ 1`
  have h0 : tauTildeFun r p q 0 ≤ 1 := by
    unfold tauTildeFun
    simp only [neg_zero, Real.rpow_zero, mul_one]
    calc ∑ j, p j ^ q ≤ ∑ j, p j := Finset.sum_le_sum fun j _ => by
          have hp1' : p j ≤ 1 := by
            rw [← hp1]
            exact Finset.single_le_sum (fun i _ => (hp i).le) (Finset.mem_univ j)
          calc p j ^ q ≤ p j ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_ge (hp j) hp1' hq
            _ = p j := Real.rpow_one _
      _ = 1 := hp1
  -- `Φ_q(b) ≥ 1` for large `b`
  obtain ⟨j₀⟩ := (inferInstance : Nonempty κ)
  have hr0 : 0 < |r j₀| := abs_pos.mpr (hr j₀)
  have hlim : Tendsto (fun b : ℝ => p j₀ ^ q * |r j₀| ^ (-b)) atTop atTop := by
    refine Tendsto.const_mul_atTop (Real.rpow_pos_of_pos (hp j₀) _) ?_
    have : (fun b : ℝ => |r j₀| ^ (-b)) = fun b => (|r j₀|⁻¹) ^ b := by
      funext b; rw [Real.rpow_neg hr0.le, Real.inv_rpow hr0.le]
    rw [this]
    exact tendsto_rpow_atTop_of_base_gt_one _ (one_lt_inv₀ hr0 |>.mpr (hr1 j₀))
  obtain ⟨b, hb, hb0⟩ := ((hlim.eventually_ge_atTop 1).and (eventually_ge_atTop 0)).exists
  have hb1 : 1 ≤ tauTildeFun r p q b := hb.trans (Finset.single_le_sum (f := fun j =>
    p j ^ q * |r j| ^ (-b)) (fun j _ => mul_nonneg (Real.rpow_nonneg (hp j).le _)
      (Real.rpow_nonneg (abs_nonneg _) _)) (Finset.mem_univ j₀))
  obtain ⟨τ, -, hτ⟩ := intermediate_value_Icc hb0 (continuous_tauTildeFun hr q).continuousOn
    ⟨h0, hb1⟩
  exact ⟨τ, hτ⟩

/-- `τ̃(q)`, the unique solution of `∑_j p_j^q |r_j|^{-τ̃} = 1` (Shmerkin, Theorem 6.6); `0`
outside the range of the theorem. -/
noncomputable def tauTilde (r p : κ → ℝ) (q : ℝ) : ℝ :=
  open Classical in
  if h : ∃! τ : ℝ, tauTildeFun r p q τ = 1 then h.exists.choose else 0

/-- `Φ_q(τ̃(q)) = 1` (Theorem 6.6). -/
theorem tauTildeFun_tauTilde [Nonempty κ] (hr : ∀ j, r j ≠ 0) (hr1 : ∀ j, |r j| < 1)
    (hp : ∀ j, 0 < p j) (hp1 : ∑ j, p j = 1) {q : ℝ} (hq : 1 ≤ q) :
    tauTildeFun r p q (tauTilde r p q) = 1 := by
  have h := exists_unique_tauTildeFun_eq_one hr hr1 hp hp1 hq
  unfold tauTilde
  simp only [h, dite_true]
  exact h.exists.choose_spec

/-- `β < τ̃(q)` if and only if `∑_j p_j^q |r_j|^{-β} < 1`; the statement
`BoxLike.ShmerkinLqDimension` is phrased with the latter. -/
theorem lt_tauTilde_iff [Nonempty κ] (hr : ∀ j, r j ≠ 0) (hr1 : ∀ j, |r j| < 1)
    (hp : ∀ j, 0 < p j) (hp1 : ∑ j, p j = 1) {q : ℝ} (hq : 1 ≤ q) {β : ℝ} :
    β < tauTilde r p q ↔ tauTildeFun r p q β < 1 := by
  conv_rhs => rw [← tauTildeFun_tauTilde hr hr1 hp hp1 hq]
  exact (tauTildeFun_strictMono hr hr1 hp q).lt_iff_lt.symm

/-- `τ̃(q) ≥ 0` for `q ≥ 1`. -/
theorem tauTilde_nonneg [Nonempty κ] (hr : ∀ j, r j ≠ 0) (hr1 : ∀ j, |r j| < 1)
    (hp : ∀ j, 0 < p j) (hp1 : ∑ j, p j = 1) {q : ℝ} (hq : 1 ≤ q) : 0 ≤ tauTilde r p q := by
  by_contra hneg
  push Not at hneg
  have h := (lt_tauTilde_iff hr hr1 hp hp1 hq).not.mp (not_lt.mpr hneg.le)
  push Not at h
  -- `Φ_q(0) ≤ 1 = Φ_q(τ̃)` with `τ̃ < 0` contradicts strict monotonicity
  have h0 : tauTildeFun r p q 0 ≤ 1 := by
    unfold tauTildeFun
    simp only [neg_zero, Real.rpow_zero, mul_one]
    calc ∑ j, p j ^ q ≤ ∑ j, p j := Finset.sum_le_sum fun j _ => by
          have hp1' : p j ≤ 1 := by
            rw [← hp1]
            exact Finset.single_le_sum (fun i _ => (hp i).le) (Finset.mem_univ j)
          calc p j ^ q ≤ p j ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_ge (hp j) hp1' hq
            _ = p j := Real.rpow_one _
      _ = 1 := hp1
  have h1 := tauTildeFun_strictMono hr hr1 hp q hneg
  rw [tauTildeFun_tauTilde hr hr1 hp hp1 hq] at h1
  linarith

/-- Iterating the definition of `τ̃(q)` along `Ω_m`: `∑_{u ∈ Ω_m} p_u^q |λ_u|^{-τ̃(q)} = 1` for
`m ≥ 1` (Shmerkin, proof of Proposition 6.7). -/
theorem sum_omega_tauTilde_eq_one [Nonempty κ] (hr : ∀ j, r j ≠ 0) (hr1 : ∀ j, |r j| < 1)
    (hp : ∀ j, 0 < p j) (hp1 : ∑ j, p j = 1) {q : ℝ} (hq : 1 ≤ q) {m : ℕ} (hm : 1 ≤ m) :
    ∑ u ∈ omega r m, wordWeight p u ^ q * |wordRatio r u| ^ (-tauTilde r p q) = 1 := by
  set τ := tauTilde r p q
  have hΦ := tauTildeFun_tauTilde hr hr1 hp hp1 hq
  set F : List κ → ℝ := fun u => wordWeight p u ^ q * |wordRatio r u| ^ (-τ)
  have hF : ∀ v, F v = ∑ j, F (v ++ [j]) := by
    intro v
    simp only [F, wordWeight_append, wordRatio_append, abs_mul]
    have e : ∀ j, (wordWeight p v * wordWeight p [j]) ^ q *
        (|wordRatio r v| * |wordRatio r [j]|) ^ (-τ) =
        wordWeight p v ^ q * |wordRatio r v| ^ (-τ) * (p j ^ q * |r j| ^ (-τ)) := by
      intro j
      rw [Real.mul_rpow (wordWeight_pos hp v).le (wordWeight_pos hp [j]).le,
        Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
      simp only [wordWeight, wordRatio, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one]
      ring
    simp_rw [e]
    rw [← Finset.mul_sum]
    change _ = _ * tauTildeFun r p q τ
    rw [hΦ, mul_one]
  have h := sum_omega_eq hr1 F hF hm
  simpa [F] using h

/-- (6.6): `τ̃(q) = lim_m -log₂ ∑_{u ∈ Ω_m} p_u^q / m` (Shmerkin, proof of Proposition 6.7). -/
theorem tendsto_tauTilde [Nonempty κ] (hr : ∀ j, r j ≠ 0) (hr1 : ∀ j, |r j| < 1)
    (hp : ∀ j, 0 < p j) (hp1 : ∑ j, p j = 1) {q : ℝ} (hq : 1 ≤ q) :
    Tendsto (fun m : ℕ => -Real.logb 2 (∑ u ∈ omega r m, wordWeight p u ^ q) / m) atTop
      (𝓝 (tauTilde r p q)) := by
  set τ := tauTilde r p q
  have hτ0 : 0 ≤ τ := tauTilde_nonneg hr hr1 hp hp1 hq
  obtain ⟨ρ₀, hρ₀, hρ⟩ := exists_ratio_lower hr
  have hρ₀1 : ρ₀ ≤ 1 := by
    obtain ⟨j⟩ := (inferInstance : Nonempty κ)
    exact (hρ j).trans (hr1 j).le
  set Z : ℕ → ℝ := fun m => ∑ u ∈ omega r m, wordWeight p u ^ q
  have hupper : ∀ m : ℕ, 1 ≤ m → Z m ≤ (2 : ℝ) ^ (-(m * τ)) := fun m hm =>
    sum_omega_weight_rpow_le hr hr1 hp hτ0 (tauTildeFun_tauTilde hr hr1 hp hp1 hq).le hm
  have hlower : ∀ m : ℕ, 1 ≤ m → ρ₀ ^ τ * (2 : ℝ) ^ (-(m * τ)) ≤ Z m := by
    intro m hm
    have h1 := sum_omega_tauTilde_eq_one hr hr1 hp hp1 hq hm
    have h2 : ∀ u ∈ omega r m, |wordRatio r u| ^ (-τ) ≤ (ρ₀ * (2 : ℝ) ^ (-(m : ℝ))) ^ (-τ) :=
      fun u hu => Real.rpow_le_rpow_of_nonpos (by positivity)
        (lt_abs_wordRatio_of_stopping hρ₀ hρ ((mem_omega hr1).mp hu)).le (by linarith)
    have h3 : 1 ≤ Z m * (ρ₀ * (2 : ℝ) ^ (-(m : ℝ))) ^ (-τ) := by
      rw [← h1, Finset.sum_mul]
      exact Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left (h2 u hu)
        (Real.rpow_nonneg (wordWeight_pos hp u).le _)
    have e : (ρ₀ * (2 : ℝ) ^ (-(m : ℝ))) ^ (-τ) * (ρ₀ ^ τ * (2 : ℝ) ^ (-(m * τ))) = 1 := by
      rw [Real.mul_rpow hρ₀.le (by positivity), ← Real.rpow_mul (by norm_num),
        Real.rpow_neg hρ₀.le]
      rw [show (-(m : ℝ)) * -τ = -(-(m * τ)) by ring, Real.rpow_neg (by norm_num)]
      field_simp
    calc ρ₀ ^ τ * (2 : ℝ) ^ (-(m * τ))
        ≤ Z m * (ρ₀ * (2 : ℝ) ^ (-(m : ℝ))) ^ (-τ) * (ρ₀ ^ τ * (2 : ℝ) ^ (-(m * τ))) :=
          le_mul_of_one_le_left (by positivity) h3
      _ = Z m := by rw [mul_assoc, e, mul_one]
  -- squeeze
  have hlo : ∀ᶠ m : ℕ in atTop, τ ≤ -Real.logb 2 (Z m) / m := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hZ : 0 < Z m := lt_of_lt_of_le (by positivity) (hlower m hm)
    rw [le_div_iff₀ hm']
    have := (Real.logb_le_iff_le_rpow (by norm_num) hZ).mpr (hupper m hm)
    linarith
  have hhi : ∀ᶠ m : ℕ in atTop, -Real.logb 2 (Z m) / m ≤ τ + (-τ * Real.logb 2 ρ₀) / m := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hZ : 0 < Z m := lt_of_lt_of_le (by positivity) (hlower m hm)
    have h1 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) (hlower m hm)
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_rpow (by norm_num) (by norm_num),
      Real.logb_rpow_eq_mul_logb_of_pos hρ₀] at h1
    have e : (τ + (-τ * Real.logb 2 ρ₀) / m) * m = τ * m - τ * Real.logb 2 ρ₀ := by
      field_simp; ring
    rw [div_le_iff₀ hm', e]
    linarith
  have hlim : Tendsto (fun m : ℕ => τ + (-τ * Real.logb 2 ρ₀) / m) atTop (𝓝 τ) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (-τ * Real.logb 2 ρ₀))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim hlo hhi

end Shmerkin
end BoxLike
