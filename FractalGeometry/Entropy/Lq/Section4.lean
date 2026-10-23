import Mathlib
import FractalGeometry.Entropy.Lq.Basic

open MeasureTheory Filter Topology Set

namespace FractalGeometry

namespace Lq

theorem lqSum_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (m : ℕ) : lqSum ν 1 m = 1 := by
  unfold lqSum
  simp only [Real.rpow_one]
  rw [tsum_measureReal_dyadicIco]
  simp

theorem lqSpectrum_one (ν : Measure ℝ) [IsProbabilityMeasure ν] : lqSpectrum ν 1 = 0 := by
  unfold lqSpectrum
  simp only [lqSum_one, Real.logb_one, neg_zero, zero_div]
  exact liminf_const 0

theorem lqSum_convex (ν : Measure ℝ) [IsFiniteMeasure ν] {q₁ q₂ : ℝ} (hq₁ : 1 ≤ q₁)
    (hq₂ : 1 ≤ q₂) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (m : ℕ) :
    lqSum ν (a * q₁ + b * q₂) m ≤ lqSum ν q₁ m ^ a * lqSum ν q₂ m ^ b := by
  have hpq : (1 / a).HolderConjugate (1 / b) := by
    rw [Real.holderConjugate_iff]
    refine ⟨by rw [lt_div_iff₀ ha]; linarith, ?_⟩
    simp only [one_div, inv_inv]
    exact hab
  set x : ℤ → ℝ := fun k => ν.real (dyadicIco m k)
  have hx : ∀ k, 0 ≤ x k := fun k => measureReal_nonneg
  have e1 : ∀ k, x k ^ (a * q₁) * x k ^ (b * q₂) = x k ^ (a * q₁ + b * q₂) := fun k =>
    (Real.rpow_add' (hx k) (by nlinarith)).symm
  have e2 : ∀ k, (x k ^ (a * q₁)) ^ (1 / a) = x k ^ q₁ := fun k => by
    rw [← Real.rpow_mul (hx k)]; congr 1; field_simp
  have e3 : ∀ k, (x k ^ (b * q₂)) ^ (1 / b) = x k ^ q₂ := fun k => by
    rw [← Real.rpow_mul (hx k)]; congr 1; field_simp
  have h := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hpq (f := fun k => x k ^ (a * q₁))
    (g := fun k => x k ^ (b * q₂)) (fun k => Real.rpow_nonneg (hx k) _)
    (fun k => Real.rpow_nonneg (hx k) _) (by simp only [e2]; exact summable_lq ν hq₁ m)
    (by simp only [e3]; exact summable_lq ν hq₂ m)
  simp only [e1, e2, e3, one_div_one_div] at h
  exact h

theorem concaveOn_lqSpectrum {ν : Measure ℝ} [IsProbabilityMeasure ν] {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ν (Set.Icc (-L) L)ᶜ = 0) : ConcaveOn ℝ (Set.Ici 1) (lqSpectrum ν) := by
  refine ⟨convex_Ici 1, fun q₁ hq₁ q₂ hq₂ a b ha hb hab => ?_⟩
  simp only [Set.mem_Ici] at hq₁ hq₂
  simp only [smul_eq_mul]
  rcases ha.lt_or_eq with ha | rfl
  · rcases hb.lt_or_eq with hb | rfl
    · have hq : 1 ≤ a * q₁ + b * q₂ := by nlinarith
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have h1 := eventually_lt_of_lt_liminf (show lqSpectrum ν q₁ - ε < lqSpectrum ν q₁ by
        linarith) (isBoundedUnder_ge_lqExponent hq₁)
      have h2 := eventually_lt_of_lt_liminf (show lqSpectrum ν q₂ - ε < lqSpectrum ν q₂ by
        linarith) (isBoundedUnder_ge_lqExponent hq₂)
      have hle : a * lqSpectrum ν q₁ + b * lqSpectrum ν q₂ - ε ≤
          lqSpectrum ν (a * q₁ + b * q₂) := by
        refine le_liminf_of_le (isBoundedUnder_le_lqExponent hL0 hL hq).isCoboundedUnder_flip ?_
        filter_upwards [h1, h2, eventually_ge_atTop 1] with m hm1 hm2 hm
        have hm' : (0 : ℝ) < m := by exact_mod_cast hm
        show _ ≤ -Real.logb 2 (lqSum ν (a * q₁ + b * q₂) m) / m
        have hS1 := lqSum_pos hL0 hL hq₁ m
        have hS2 := lqSum_pos hL0 hL hq₂ m
        have hconv := lqSum_convex ν hq₁ hq₂ ha hb hab m
        have hlog : Real.logb 2 (lqSum ν (a * q₁ + b * q₂) m) ≤
            a * Real.logb 2 (lqSum ν q₁ m) + b * Real.logb 2 (lqSum ν q₂ m) := by
          calc Real.logb 2 (lqSum ν (a * q₁ + b * q₂) m)
              ≤ Real.logb 2 (lqSum ν q₁ m ^ a * lqSum ν q₂ m ^ b) :=
                Real.logb_le_logb_of_le (by norm_num) (lqSum_pos hL0 hL hq m) hconv
            _ = _ := by
                rw [Real.logb_mul (Real.rpow_pos_of_pos hS1 _).ne'
                  (Real.rpow_pos_of_pos hS2 _).ne', Real.logb_rpow_eq_mul_logb_of_pos hS1,
                  Real.logb_rpow_eq_mul_logb_of_pos hS2]
        rw [lt_div_iff₀ hm'] at hm1 hm2
        rw [le_div_iff₀ hm']
        have e : (a * lqSpectrum ν q₁ + b * lqSpectrum ν q₂ - ε) * m =
            a * ((lqSpectrum ν q₁ - ε) * m) + b * ((lqSpectrum ν q₂ - ε) * m) := by
          linear_combination (ε * m) * hab
        linarith [mul_lt_mul_of_pos_left hm1 ha, mul_lt_mul_of_pos_left hm2 hb]
      linarith
    · simp only [add_zero] at hab
      subst hab
      simp
  · simp only [zero_add] at hab
    subst hab
    simp

noncomputable def legendre (ν : Measure ℝ) (q : ℝ) : ℝ :=
  q * deriv (lqSpectrum ν) q - lqSpectrum ν q

theorem logb_add_le_of_mul_rpow_le {N a b : ℝ} (hN : 0 < N)
    (h : N * (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b) : Real.logb 2 N + a ≤ b := by
  have e : N * (2 : ℝ) ^ a = (2 : ℝ) ^ (Real.logb 2 N + a) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hN]
  rw [e] at h
  exact (Real.rpow_le_rpow_left_iff (by norm_num)).mp h

theorem le_logb_add_of_rpow_le_mul {N a b : ℝ} (hN : 0 < N)
    (h : (2 : ℝ) ^ b ≤ N * (2 : ℝ) ^ a) : b ≤ Real.logb 2 N + a := by
  have e : N * (2 : ℝ) ^ a = (2 : ℝ) ^ (Real.logb 2 N + a) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hN]
  rw [e] at h
  exact (Real.rpow_le_rpow_left_iff (by norm_num)).mp h

theorem le_rpow_of_logb_le {N b : ℝ} (hN : 0 < N) (h : Real.logb 2 N ≤ b) :
    N ≤ (2 : ℝ) ^ b :=
  (Real.logb_le_iff_le_rpow (by norm_num) hN).mp h

theorem exists_sub_le_of_hasDerivAt {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) {η : ℝ}
    (hη : 0 < η) : ∃ c > 0, ∀ h, 0 < h → h < c → f x - f (x - h) ≤ h * (f' + η) := by
  have hlim := hf.tendsto_slope_zero_left
  have hev : ∀ᶠ t in 𝓝[<] (0 : ℝ), t⁻¹ • (f (x + t) - f x) < f' + η :=
    hlim.eventually (gt_mem_nhds (by linarith))
  obtain ⟨l, hl, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).mp hev
  have hl' : l < 0 := hl
  refine ⟨-l, by linarith, fun h h0 hc => ?_⟩
  have ht : (-h)⁻¹ • (f (x + -h) - f x) < f' + η :=
    hsub (show -h ∈ Set.Ioo l 0 from ⟨by linarith, by linarith⟩)
  rw [smul_eq_mul, show x + -h = x - h by ring, inv_neg, neg_mul, ← mul_neg, neg_sub] at ht
  rw [← div_eq_inv_mul, div_lt_iff₀ h0] at ht
  linarith [mul_comm (f' + η) h]

theorem exists_le_sub_of_hasDerivAt {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) {η : ℝ}
    (hη : 0 < η) : ∃ c > 0, ∀ h, 0 < h → h < c → h * (f' - η) ≤ f (x + h) - f x := by
  have hlim := hf.tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), f' - η < t⁻¹ • (f (x + t) - f x) :=
    hlim.eventually (lt_mem_nhds (by linarith))
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hev
  refine ⟨u, hu, fun h h0 hc => ?_⟩
  have ht : f' - η < h⁻¹ • (f (x + h) - f x) := hsub (show h ∈ Set.Ioo 0 u from ⟨h0, hc⟩)
  rw [smul_eq_mul, ← div_eq_inv_mul, lt_div_iff₀ h0] at ht
  linarith [mul_comm (f' - η) h]

section Lemmas

variable {ν : Measure ℝ} [IsProbabilityMeasure ν] {L : ℝ} (hL0 : 0 ≤ L)
  (hL : ν (Set.Icc (-L) L)ᶜ = 0)

include hL0 hL

theorem lemma_4_9 {q : ℝ} (hq : 1 < q) (hd : DifferentiableAt ℝ (lqSpectrum ν) q)
    (hτ : lqSpectrum ν q < q - 1) :
    legendre ν q ≤ deriv (lqSpectrum ν) q ∧ deriv (lqSpectrum ν) q < 1 := by
  have hslope := (concaveOn_lqSpectrum hL0 hL).deriv_le_slope (Set.mem_Ici.mpr le_rfl)
    (Set.mem_Ici.mpr hq.le) hq hd
  rw [slope_def_field, lqSpectrum_one] at hslope
  have hq1 : 0 < q - 1 := by linarith
  rw [le_div_iff₀ hq1] at hslope
  constructor
  · unfold legendre; nlinarith
  · by_contra h
    push Not at h
    nlinarith

omit [IsProbabilityMeasure ν] hL0 hL in

theorem card_mul_le_sum_rpow (D' : Finset ℤ) {x q : ℝ} (hx : 0 ≤ x) (hq : 0 ≤ q) (m : ℕ)
    (h : ∀ k ∈ D', x ≤ ν.real (dyadicIco m k)) :
    (D'.card : ℝ) * x ^ q ≤ ∑ k ∈ D', ν.real (dyadicIco m k) ^ q := by
  rw [← nsmul_eq_mul]
  exact Finset.card_nsmul_le_sum _ _ _ fun k hk => Real.rpow_le_rpow hx (h k hk) hq

omit [IsProbabilityMeasure ν] hL0 hL in

theorem sum_rpow_le_card_mul (D' : Finset ℤ) {x q : ℝ} (hq : 0 ≤ q) (m : ℕ)
    (h : ∀ k ∈ D', ν.real (dyadicIco m k) ≤ x) :
    ∑ k ∈ D', ν.real (dyadicIco m k) ^ q ≤ (D'.card : ℝ) * x ^ q := by
  rw [← nsmul_eq_mul]
  exact Finset.sum_le_card_nsmul _ _ _ fun k hk =>
    Real.rpow_le_rpow measureReal_nonneg (h k hk) hq

theorem lemma_4_10 {q₀ : ℝ} (hq₀ : 1 < q₀) (hd : DifferentiableAt ℝ (lqSpectrum ν) q₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ᶠ m : ℕ in atTop, ∀ (D' : Finset ℤ) (α : ℝ), 0 ≤ α →
      (∀ k ∈ D', (2 : ℝ) ^ (-(α * m)) ≤ ν.real (dyadicIco m k) ∧
        ν.real (dyadicIco m k) ≤ 2 * (2 : ℝ) ^ (-(α * m))) →
      (2 : ℝ) ^ (-((lqSpectrum ν q₀ + δ) * m)) ≤ ∑ k ∈ D', ν.real (dyadicIco m k) ^ q₀ →
      (D'.card : ℝ) ≤ (2 : ℝ) ^ (m * (legendre ν q₀ + ε)) := by
  set τ := lqSpectrum ν
  set α₀ := deriv τ q₀
  set η := ε / (3 * q₀) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨c, hc, hsl⟩ := exists_sub_le_of_hasDerivAt hd.hasDerivAt hη0
  refine ⟨min (η ^ 2 / 9) (min ((c / 2) ^ 2) (((q₀ - 1) / 2) ^ 2)), by positivity,
    fun δ hδ hδ₀ => ?_⟩
  set h := Real.sqrt δ with hh
  have hh0 : 0 < h := Real.sqrt_pos.mpr hδ
  have hδh : δ = h ^ 2 := (Real.sq_sqrt hδ.le).symm
  have hhη : h ≤ η / 3 := by
    rw [hh, Real.sqrt_le_left (by positivity)]
    calc δ ≤ η ^ 2 / 9 := hδ₀.trans (min_le_left _ _)
      _ = (η / 3) ^ 2 := by ring
  have hhc : h < c := by
    have : h ≤ c / 2 := by
      rw [hh, Real.sqrt_le_left (by positivity)]
      exact hδ₀.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hhq : h ≤ (q₀ - 1) / 2 := by
    rw [hh, Real.sqrt_le_left (by linarith)]
    exact hδ₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  set q₁ := q₀ - h
  have hq₁ : 1 < q₁ := by linarith
  have h44 : τ q₀ - τ q₁ ≤ h * (α₀ + η) := hsl h hh0 hhc
  filter_upwards [eventually_lqSum_le hL0 hL hq₁.le (show τ q₁ - δ < τ q₁ by linarith),
    eventually_lqSum_le hL0 hL hq₀.le (show τ q₀ - ε / 3 < τ q₀ by linarith),
    eventually_ge_atTop ⌈q₀ / δ⌉₊, eventually_ge_atTop 1] with m hm₁ hm₀ hmδ hm1 D' α hα h1 h2
  rcases D'.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  have hN : (0 : ℝ) < D'.card := by exact_mod_cast hne.card_pos
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hqδ : q₀ ≤ δ * m := by
    have := (Nat.ceil_le.mp hmδ)
    rw [div_le_iff₀ hδ] at this
    linarith

  have hi : (D'.card : ℝ) * (2 : ℝ) ^ (-(α * m) * q₁) ≤ (2 : ℝ) ^ (-((τ q₁ - δ) * m)) := by
    calc (D'.card : ℝ) * (2 : ℝ) ^ (-(α * m) * q₁)
        = (D'.card : ℝ) * ((2 : ℝ) ^ (-(α * m))) ^ q₁ := by rw [Real.rpow_mul (by norm_num)]
      _ ≤ ∑ k ∈ D', ν.real (dyadicIco m k) ^ q₁ :=
          card_mul_le_sum_rpow D' (by positivity) (by linarith) m fun k hk => (h1 k hk).1
      _ ≤ lqSum ν q₁ m := sum_le_lqSum ν hq₁.le m D'
      _ ≤ _ := hm₁

  have hii : (2 : ℝ) ^ (-((τ q₀ + δ) * m)) ≤ (D'.card : ℝ) * (2 : ℝ) ^ (q₀ - α * m * q₀) := by
    calc (2 : ℝ) ^ (-((τ q₀ + δ) * m)) ≤ ∑ k ∈ D', ν.real (dyadicIco m k) ^ q₀ := h2
      _ ≤ (D'.card : ℝ) * (2 * (2 : ℝ) ^ (-(α * m))) ^ q₀ :=
          sum_rpow_le_card_mul D' (by linarith) m fun k hk => (h1 k hk).2
      _ = (D'.card : ℝ) * (2 : ℝ) ^ (q₀ - α * m * q₀) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by norm_num),
            ← Real.rpow_add (by norm_num)]
          ring_nf

  have hiii : (D'.card : ℝ) * (2 : ℝ) ^ (-(α * m) * q₀) ≤
      (2 : ℝ) ^ (-((τ q₀ - ε / 3) * m)) := by
    calc (D'.card : ℝ) * (2 : ℝ) ^ (-(α * m) * q₀)
        = (D'.card : ℝ) * ((2 : ℝ) ^ (-(α * m))) ^ q₀ := by rw [Real.rpow_mul (by norm_num)]
      _ ≤ ∑ k ∈ D', ν.real (dyadicIco m k) ^ q₀ :=
          card_mul_le_sum_rpow D' (by positivity) (by linarith) m fun k hk => (h1 k hk).1
      _ ≤ lqSum ν q₀ m := sum_le_lqSum ν hq₀.le m D'
      _ ≤ _ := hm₀
  have li := logb_add_le_of_mul_rpow_le hN hi
  have lii := le_logb_add_of_rpow_le_mul hN hii
  have liii := logb_add_le_of_mul_rpow_le hN hiii

  have hm0 : (0 : ℝ) < m := by linarith
  have e1 : -(α * m) * q₁ = -(α * m * q₀) + α * m * h := by simp only [q₁]; ring
  rw [e1] at li
  have s1 : α * m * h ≤ (τ q₀ - τ q₁) * m + 2 * δ * m + q₀ := by linarith
  have s2 : (τ q₀ - τ q₁) * m ≤ h * (α₀ + η) * m := mul_le_mul_of_nonneg_right h44 hm0.le
  have s3 : α * (m * h) ≤ (α₀ + η + 3 * h) * (m * h) := by
    have : q₀ ≤ h ^ 2 * m := by rw [← hδh]; exact hqδ
    have e2 : δ * m = h ^ 2 * m := by rw [hδh]
    nlinarith
  have hα₀ : α ≤ α₀ + 2 * η := by
    have := le_of_mul_le_mul_right s3 (by positivity)
    linarith
  refine le_rpow_of_logb_le hN ?_
  unfold legendre
  have s4 : α * m * q₀ ≤ (α₀ + 2 * η) * m * q₀ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hα₀ hm0.le) (by linarith)
  have hηq : 2 * η * q₀ = 2 * ε / 3 := by rw [hη]; field_simp
  have e3 : (α₀ + 2 * η) * m * q₀ = q₀ * α₀ * m + (2 * η * q₀) * m := by ring
  rw [hηq] at e3
  have e4 : -(α * m) * q₀ = -(α * m * q₀) := by ring
  rw [e4] at liii
  nlinarith

theorem lemma_4_11 {q₀ : ℝ} (hq₀ : 1 < q₀) (hd : DifferentiableAt ℝ (lqSpectrum ν) q₀)
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ ε > 0, ∀ᶠ m : ℕ in atTop, ∀ D' : Finset ℤ,
      (∀ k ∈ D', (2 : ℝ) ^ (-(m * (deriv (lqSpectrum ν) q₀ - σ))) ≤ ν.real (dyadicIco m k)) →
      ∑ k ∈ D', ν.real (dyadicIco m k) ^ q₀ ≤
        (2 : ℝ) ^ (-(m * (lqSpectrum ν q₀ + ε))) := by
  set τ := lqSpectrum ν
  set α₀ := deriv τ q₀
  obtain ⟨c, hc, hsl⟩ := exists_le_sub_of_hasDerivAt hd.hasDerivAt (show 0 < σ / 4 by positivity)
  set η := c / 2
  have hη : 0 < η := by positivity
  have h46 : η * (α₀ - σ / 4) ≤ τ (q₀ + η) - τ q₀ := hsl η hη (by simp only [η]; linarith)
  refine ⟨η * σ / 2, by positivity, ?_⟩
  have hq : 1 ≤ q₀ + η := by linarith
  filter_upwards [eventually_lqSum_le hL0 hL hq
    (show τ (q₀ + η) - η * σ / 4 < τ (q₀ + η) by nlinarith)] with m hm D' hD'
  set x := (2 : ℝ) ^ (-(m * (α₀ - σ)))
  have hx : 0 < x := by positivity
  have hterm : ∀ k ∈ D', ν.real (dyadicIco m k) ^ q₀ ≤
      (2 : ℝ) ^ (m * η * (α₀ - σ)) * ν.real (dyadicIco m k) ^ (q₀ + η) := by
    intro k hk
    have hk0 : 0 < ν.real (dyadicIco m k) := lt_of_lt_of_le hx (hD' k hk)
    rw [Real.rpow_add hk0]
    have h1 : 1 ≤ (2 : ℝ) ^ (m * η * (α₀ - σ)) * ν.real (dyadicIco m k) ^ η := by
      calc (1 : ℝ) = (2 : ℝ) ^ (m * η * (α₀ - σ)) * x ^ η := by
            rw [← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
            ring_nf; simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.le (hD' k hk) hη.le)
            (by positivity)
    calc ν.real (dyadicIco m k) ^ q₀ = 1 * ν.real (dyadicIco m k) ^ q₀ := (one_mul _).symm
      _ ≤ (2 : ℝ) ^ (m * η * (α₀ - σ)) * ν.real (dyadicIco m k) ^ η *
            ν.real (dyadicIco m k) ^ q₀ :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hk0.le _)
      _ = _ := by ring
  calc ∑ k ∈ D', ν.real (dyadicIco m k) ^ q₀
      ≤ ∑ k ∈ D', (2 : ℝ) ^ (m * η * (α₀ - σ)) * ν.real (dyadicIco m k) ^ (q₀ + η) :=
        Finset.sum_le_sum hterm
    _ = (2 : ℝ) ^ (m * η * (α₀ - σ)) * ∑ k ∈ D', ν.real (dyadicIco m k) ^ (q₀ + η) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (2 : ℝ) ^ (m * η * (α₀ - σ)) * lqSum ν (q₀ + η) m :=
        mul_le_mul_of_nonneg_left (sum_le_lqSum ν hq m D') (by positivity)
    _ ≤ (2 : ℝ) ^ (m * η * (α₀ - σ)) * (2 : ℝ) ^ (-((τ (q₀ + η) - η * σ / 4) * m)) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
    _ = (2 : ℝ) ^ (m * η * (α₀ - σ) - (τ (q₀ + η) - η * σ / 4) * m) := by
        rw [← Real.rpow_add (by norm_num)]; ring_nf
    _ ≤ (2 : ℝ) ^ (-(m * (τ q₀ + η * σ / 2))) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have := mul_le_mul_of_nonneg_left h46 hm0
        nlinarith

theorem lemma_4_12 {q₀ : ℝ} (hq₀ : 1 < q₀) (hd : DifferentiableAt ℝ (lqSpectrum ν) q₀)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ ε > 0, ∀ᶠ m : ℕ in atTop, ∀ D' : Finset ℤ,
      (D'.card : ℝ) ≤ (2 : ℝ) ^ ((legendre ν q₀ - κ) * m) →
      ∑ k ∈ D', ν.real (dyadicIco m k) ^ q₀ ≤ (2 : ℝ) ^ (-((lqSpectrum ν q₀ + ε) * m)) := by
  set τ := lqSpectrum ν
  set α₀ := deriv τ q₀
  set σ := κ / (2 * q₀) with hσ
  have hσ0 : 0 < σ := by positivity
  obtain ⟨ε₁, hε₁, h411⟩ := lemma_4_11 hL0 hL hq₀ hd hσ0
  set ε₂ := min ε₁ (κ / 2)
  have hε₂ : 0 < ε₂ := lt_min hε₁ (by positivity)
  refine ⟨ε₂ / 2, by positivity, ?_⟩
  filter_upwards [h411, eventually_ge_atTop ⌈2 / ε₂⌉₊] with m hm hm2 D' hcard
  classical
  set x := (2 : ℝ) ^ (-(m * (α₀ - σ)))
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [← Finset.sum_filter_add_sum_filter_not D' (fun k => x ≤ ν.real (dyadicIco m k))]
  have hbig := hm (D'.filter fun k => x ≤ ν.real (dyadicIco m k))
    (fun k hk => (Finset.mem_filter.mp hk).2)
  have hsmall : ∑ k ∈ D'.filter (fun k => ¬ x ≤ ν.real (dyadicIco m k)),
      ν.real (dyadicIco m k) ^ q₀ ≤ (2 : ℝ) ^ (-((τ q₀ + κ / 2) * m)) := by
    calc ∑ k ∈ D'.filter (fun k => ¬ x ≤ ν.real (dyadicIco m k)), ν.real (dyadicIco m k) ^ q₀
        ≤ ((D'.filter (fun k => ¬ x ≤ ν.real (dyadicIco m k))).card : ℝ) * x ^ q₀ :=
          sum_rpow_le_card_mul _ (by linarith) m fun k hk =>
            (not_le.mp (Finset.mem_filter.mp hk).2).le
      _ ≤ (D'.card : ℝ) * x ^ q₀ :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le _ _)
            (by positivity)
      _ ≤ (2 : ℝ) ^ ((legendre ν q₀ - κ) * m) * x ^ q₀ :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (2 : ℝ) ^ ((legendre ν q₀ - κ) * m - m * (α₀ - σ) * q₀) := by
          rw [← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]; ring_nf
      _ = (2 : ℝ) ^ (-((τ q₀ + κ / 2) * m)) := by
          congr 1
          unfold legendre
          have : σ * q₀ = κ / 2 := by rw [hσ]; field_simp
          linear_combination (m : ℝ) * this
  have hm2' : 2 / ε₂ ≤ m := Nat.ceil_le.mp hm2
  have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (ε₂ / 2 * m) := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
          rw [div_le_iff₀ hε₂] at hm2'
          nlinarith)
  calc ∑ k ∈ D'.filter (fun k => x ≤ ν.real (dyadicIco m k)), ν.real (dyadicIco m k) ^ q₀ +
        ∑ k ∈ D'.filter (fun k => ¬ x ≤ ν.real (dyadicIco m k)), ν.real (dyadicIco m k) ^ q₀
      ≤ (2 : ℝ) ^ (-(m * (τ q₀ + ε₁))) + (2 : ℝ) ^ (-((τ q₀ + κ / 2) * m)) :=
        add_le_add hbig hsmall
    _ ≤ (2 : ℝ) ^ (-((τ q₀ + ε₂) * m)) + (2 : ℝ) ^ (-((τ q₀ + ε₂) * m)) := by
        refine add_le_add (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
        · have := mul_le_mul_of_nonneg_right (min_le_left ε₁ (κ / 2)) hm0
          nlinarith
        · have := mul_le_mul_of_nonneg_right (min_le_right ε₁ (κ / 2)) hm0
          nlinarith
    _ = 2 * (2 : ℝ) ^ (-((τ q₀ + ε₂) * m)) := by ring
    _ ≤ (2 : ℝ) ^ (ε₂ / 2 * m) * (2 : ℝ) ^ (-((τ q₀ + ε₂) * m)) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = (2 : ℝ) ^ (-((τ q₀ + ε₂ / 2) * m)) := by
        rw [← Real.rpow_add (by norm_num)]; ring_nf

end Lemmas

theorem lemma_4_1 {ι ι' : Type*} [DecidableEq ι'] (μ : Measure ℝ) [IsFiniteMeasure μ]
    (P : Finset ι)
    (Q : Finset ι') (S : ι → Set ℝ) (T : ι' → Set ℝ) (M : ℕ) {q : ℝ} (hq : 1 ≤ q)
    (c : ι → Finset ι') (hcQ : ∀ i ∈ P, c i ⊆ Q) (hcov : ∀ i ∈ P, S i ⊆ ⋃ j ∈ c i, T j)
    (hcard : ∀ i ∈ P, (c i).card ≤ M)
    (hmeet : ∀ j ∈ Q, (P.filter fun i => j ∈ c i).card ≤ M) :
    ∑ i ∈ P, μ.real (S i) ^ q ≤ (M : ℝ) ^ q * ∑ j ∈ Q, μ.real (T j) ^ q := by
  classical
  have h1 : ∀ i ∈ P, μ.real (S i) ^ q ≤ (M : ℝ) ^ (q - 1) * ∑ j ∈ c i, μ.real (T j) ^ q := by
    intro i hi
    have hS : μ.real (S i) ≤ ∑ j ∈ c i, μ.real (T j) :=
      (measureReal_mono (hcov i hi) (measure_ne_top _ _)).trans
        (measureReal_biUnion_finset_le _ _)
    have h2 := Real.rpow_sum_le_const_mul_sum_rpow (c i) (fun j => μ.real (T j)) hq
    simp only [abs_of_nonneg measureReal_nonneg] at h2
    calc μ.real (S i) ^ q ≤ (∑ j ∈ c i, μ.real (T j)) ^ q :=
          Real.rpow_le_rpow measureReal_nonneg hS (by linarith)
      _ ≤ ((c i).card : ℝ) ^ (q - 1) * ∑ j ∈ c i, μ.real (T j) ^ q := h2
      _ ≤ (M : ℝ) ^ (q - 1) * ∑ j ∈ c i, μ.real (T j) ^ q :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _)
            (by exact_mod_cast hcard i hi) (by linarith))
            (Finset.sum_nonneg fun j _ => Real.rpow_nonneg measureReal_nonneg _)
  have hswap : ∑ i ∈ P, ∑ j ∈ c i, μ.real (T j) ^ q =
      ∑ j ∈ Q, ∑ i ∈ P.filter (fun i => j ∈ c i), μ.real (T j) ^ q := by
    refine Finset.sum_comm' fun i j => ?_
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi, hj⟩; exact ⟨⟨hi, hj⟩, hcQ i hi hj⟩
    · rintro ⟨⟨hi, hj⟩, -⟩; exact ⟨hi, hj⟩
  calc ∑ i ∈ P, μ.real (S i) ^ q
      ≤ ∑ i ∈ P, (M : ℝ) ^ (q - 1) * ∑ j ∈ c i, μ.real (T j) ^ q := Finset.sum_le_sum h1
    _ = (M : ℝ) ^ (q - 1) * ∑ j ∈ Q, ((P.filter fun i => j ∈ c i).card : ℝ) *
          μ.real (T j) ^ q := by
        rw [← Finset.mul_sum, hswap]
        simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (M : ℝ) ^ (q - 1) * ∑ j ∈ Q, (M : ℝ) * μ.real (T j) ^ q := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) (by positivity)
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmeet j hj)
          (Real.rpow_nonneg measureReal_nonneg _)
    _ = (M : ℝ) ^ q * ∑ j ∈ Q, μ.real (T j) ^ q := by
        rw [← Finset.mul_sum, ← mul_assoc]
        congr 1
        rcases (Nat.cast_nonneg M : (0 : ℝ) ≤ M).lt_or_eq with hM | hM
        · rw [← Real.rpow_add_one hM.ne']; ring_nf
        · rw [← hM]
          rcases (show (1 : ℝ) ≤ q from hq).lt_or_eq with hq' | hq'
          · rw [Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]; ring
          · subst hq'; simp

theorem sum_rpow_le_of_separated {ι : Type*} (μ : Measure ℝ) [IsFiniteMeasure μ] (P : Finset ι)
    (S : ι → Set ℝ) (y : ι → ℝ) {ℓ : ℝ} {m : ℕ} {q : ℝ} (hq : 1 ≤ q) (hℓ : 1 / 2 ^ m ≤ ℓ)
    (hS : ∀ i ∈ P, S i ⊆ Set.Icc (y i) (y i + ℓ))
    (hsep : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → ℓ ≤ |y i - y j|) :
    ∃ Q : Finset ℤ, (Q.card : ℝ) ≤ (ℓ * 2 ^ m + 2) * P.card ∧
      ∑ i ∈ P, μ.real (S i) ^ q ≤ (ℓ * 2 ^ m + 2) ^ q * ∑ k ∈ Q, μ.real (dyadicIco m k) ^ q := by
  classical
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le (by positivity) hℓ
  have hℓm : 1 ≤ ℓ * 2 ^ m := by rwa [div_le_iff₀ h2m] at hℓ
  set c : ι → Finset ℤ := fun i => Finset.Icc ⌊y i * 2 ^ m⌋ ⌊(y i + ℓ) * 2 ^ m⌋
  set M : ℕ := ⌊ℓ * 2 ^ m⌋₊ + 2
  have hMℓ : (M : ℝ) ≤ ℓ * 2 ^ m + 2 := by
    simp only [M]; push_cast; linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ ℓ * 2 ^ m)]
  have hcard : ∀ i, (c i).card ≤ M := by
    intro i
    simp only [c, Int.card_Icc]
    have h1 : ⌊(y i + ℓ) * 2 ^ m⌋ ≤ ⌊y i * 2 ^ m⌋ + ⌊ℓ * 2 ^ m⌋ + 1 := by
      rw [add_mul]
      have := Int.floor_le (y i * 2 ^ m)
      have := Int.floor_le (ℓ * 2 ^ m)
      have := Int.lt_floor_add_one (y i * 2 ^ m)
      have := Int.lt_floor_add_one (ℓ * 2 ^ m)
      have h3 := Int.floor_le (y i * 2 ^ m + ℓ * 2 ^ m)
      have h4 : (⌊y i * 2 ^ m + ℓ * 2 ^ m⌋ : ℝ) < ⌊y i * 2 ^ m⌋ + ⌊ℓ * 2 ^ m⌋ + 2 := by linarith
      have h5 : ⌊y i * 2 ^ m + ℓ * 2 ^ m⌋ < ⌊y i * 2 ^ m⌋ + ⌊ℓ * 2 ^ m⌋ + 2 := by exact_mod_cast h4
      omega
    have h6 : (⌊ℓ * 2 ^ m⌋ : ℤ) = (⌊ℓ * 2 ^ m⌋₊ : ℤ) :=
      (Int.natCast_floor_eq_floor (by linarith)).symm
    simp only [M]
    omega
  have hmeet : ∀ k, (P.filter fun i => k ∈ c i).card ≤ 2 := by
    intro k
    set a := (k : ℝ) / 2 ^ m - ℓ
    have hmaps : Set.MapsTo (fun i => ⌊(y i - a) / ℓ⌋) ↑(P.filter fun i => k ∈ c i)
        ↑(Finset.Ico (0 : ℤ) 2) := by
      intro i hi
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, c, Finset.mem_Icc] at hi
      obtain ⟨-, h1, h2⟩ := hi
      have h2' := Int.floor_le ((y i + ℓ) * 2 ^ m)
      have h2'' : (k : ℝ) ≤ ⌊(y i + ℓ) * 2 ^ m⌋ := by exact_mod_cast h2
      have hlo : a ≤ y i := by
        simp only [a]
        rw [sub_le_iff_le_add, div_le_iff₀ h2m]
        linarith
      have hhi : y i < a + 2 * ℓ := by
        have : y i * 2 ^ m < k + 1 := by
          have h1'' : (⌊y i * 2 ^ m⌋ : ℝ) ≤ k := by exact_mod_cast h1
          have := Int.lt_floor_add_one (y i * 2 ^ m); linarith
        have hk : y i < (k + 1) / 2 ^ m := by rw [lt_div_iff₀ h2m]; exact this
        have : (k + 1) / 2 ^ m = (k : ℝ) / 2 ^ m + 1 / 2 ^ m := by ring
        simp only [a]; linarith
      simp only [Finset.coe_Ico, Set.mem_Ico]
      constructor
      · exact Int.floor_nonneg.mpr (div_nonneg (by linarith) hℓ0.le)
      · rw [Int.floor_lt]
        push_cast
        rw [div_lt_iff₀ hℓ0]; linarith
    have hinj : Set.InjOn (fun i => ⌊(y i - a) / ℓ⌋) ↑(P.filter fun i => k ∈ c i) := by
      intro i hi j hj hij
      by_contra hne
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hi hj
      have h := Int.abs_sub_lt_one_of_floor_eq_floor hij
      rw [← sub_div, show y i - a - (y j - a) = y i - y j by ring, abs_div, abs_of_pos hℓ0,
        div_lt_one hℓ0] at h
      exact absurd (hsep i hi.1 j hj.1 hne) (not_le.mpr h)
    have := Finset.card_le_card_of_injOn _ hmaps hinj
    simpa using this
  set Q := P.biUnion c
  refine ⟨Q, ?_, ?_⟩
  · calc (Q.card : ℝ) ≤ ∑ i ∈ P, ((c i).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ P, (ℓ * 2 ^ m + 2) := Finset.sum_le_sum fun i _ =>
          (Nat.cast_le.mpr (hcard i)).trans hMℓ
      _ = (ℓ * 2 ^ m + 2) * P.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  · have h := lemma_4_1 μ P Q S (dyadicIco m) M hq c
      (fun i hi => Finset.subset_biUnion_of_mem c hi)
      (fun i hi x hx => by
        have hx' := hS i hi hx
        simp only [Set.mem_iUnion]
        refine ⟨⌊x * 2 ^ m⌋, ?_, mem_dyadicIco_iff.mpr rfl⟩
        simp only [c, Finset.mem_Icc]
        exact ⟨Int.floor_le_floor (mul_le_mul_of_nonneg_right hx'.1 h2m.le),
          Int.floor_le_floor (mul_le_mul_of_nonneg_right hx'.2 h2m.le)⟩)
      (fun i _ => hcard i) (fun k _ => (hmeet k).trans (by simp [M]))
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun k _ =>
      Real.rpow_nonneg measureReal_nonneg _))
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hMℓ (by linarith)

theorem sum_rpow_le_of_separated' {ι : Type*} (μ : Measure ℝ) [IsFiniteMeasure μ]
    (P : Finset ι) (S : ι → Set ℝ) (y : ι → ℝ) {ℓ : ℝ} {m : ℕ} {q : ℝ} (hq : 1 ≤ q)
    (hℓ0 : 0 < ℓ) (hS : ∀ i ∈ P, S i ⊆ Set.Icc (y i) (y i + ℓ))
    (hsep : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → ℓ ≤ |y i - y j|) :
    ∃ Q : Finset ℤ, (Q.card : ℝ) ≤ (ℓ * 2 ^ m + (ℓ * 2 ^ m)⁻¹ + 2) * P.card ∧
      ∑ i ∈ P, μ.real (S i) ^ q ≤
        (ℓ * 2 ^ m + (ℓ * 2 ^ m)⁻¹ + 2) ^ q * ∑ k ∈ Q, μ.real (dyadicIco m k) ^ q := by
  classical
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hℓm : 0 < ℓ * 2 ^ m := by positivity
  set c : ι → Finset ℤ := fun i => Finset.Icc ⌊y i * 2 ^ m⌋ ⌊(y i + ℓ) * 2 ^ m⌋
  set M : ℕ := max (⌊ℓ * 2 ^ m⌋₊ + 2) (⌊(ℓ * 2 ^ m)⁻¹⌋₊ + 2)
  have hMℓ : (M : ℝ) ≤ ℓ * 2 ^ m + (ℓ * 2 ^ m)⁻¹ + 2 := by
    simp only [M]
    push_cast
    have h1 := Nat.floor_le hℓm.le
    have h2 := Nat.floor_le (inv_pos.mpr hℓm).le
    refine max_le ?_ ?_
    · linarith [inv_pos.mpr hℓm]
    · linarith
  have hcard : ∀ i, (c i).card ≤ M := by
    intro i
    simp only [c, Int.card_Icc]
    have h1 : ⌊(y i + ℓ) * 2 ^ m⌋ ≤ ⌊y i * 2 ^ m⌋ + ⌊ℓ * 2 ^ m⌋ + 1 := by
      rw [add_mul]
      have := Int.floor_le (y i * 2 ^ m)
      have := Int.floor_le (ℓ * 2 ^ m)
      have := Int.lt_floor_add_one (y i * 2 ^ m)
      have := Int.lt_floor_add_one (ℓ * 2 ^ m)
      have h3 := Int.floor_le (y i * 2 ^ m + ℓ * 2 ^ m)
      have h4 : (⌊y i * 2 ^ m + ℓ * 2 ^ m⌋ : ℝ) < ⌊y i * 2 ^ m⌋ + ⌊ℓ * 2 ^ m⌋ + 2 := by linarith
      have h5 : ⌊y i * 2 ^ m + ℓ * 2 ^ m⌋ < ⌊y i * 2 ^ m⌋ + ⌊ℓ * 2 ^ m⌋ + 2 := by exact_mod_cast h4
      omega
    have h6 : (⌊ℓ * 2 ^ m⌋ : ℤ) = (⌊ℓ * 2 ^ m⌋₊ : ℤ) :=
      (Int.natCast_floor_eq_floor hℓm.le).symm
    simp only [M]
    omega
  have hmeet : ∀ k, (P.filter fun i => k ∈ c i).card ≤ M := by
    intro k
    set a := (k : ℝ) / 2 ^ m - ℓ
    set B : ℕ := ⌊(ℓ * 2 ^ m)⁻¹⌋₊ + 2
    have hmaps : Set.MapsTo (fun i => ⌊(y i - a) / ℓ⌋) ↑(P.filter fun i => k ∈ c i)
        ↑(Finset.Ico (0 : ℤ) B) := by
      intro i hi
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, c, Finset.mem_Icc] at hi
      obtain ⟨-, h1, h2⟩ := hi
      have h2' := Int.floor_le ((y i + ℓ) * 2 ^ m)
      have h2'' : (k : ℝ) ≤ ⌊(y i + ℓ) * 2 ^ m⌋ := by exact_mod_cast h2
      have hlo : a ≤ y i := by
        simp only [a]
        rw [sub_le_iff_le_add, div_le_iff₀ h2m]
        linarith
      have hhi : y i < a + ℓ + 1 / 2 ^ m := by
        have : y i * 2 ^ m < k + 1 := by
          have h1'' : (⌊y i * 2 ^ m⌋ : ℝ) ≤ k := by exact_mod_cast h1
          have := Int.lt_floor_add_one (y i * 2 ^ m); linarith
        have hk : y i < (k + 1) / 2 ^ m := by rw [lt_div_iff₀ h2m]; exact this
        have : (k + 1) / 2 ^ m = (k : ℝ) / 2 ^ m + 1 / 2 ^ m := by ring
        simp only [a]; linarith
      simp only [Finset.coe_Ico, Set.mem_Ico]
      constructor
      · exact Int.floor_nonneg.mpr (div_nonneg (by linarith) hℓ0.le)
      · rw [Int.floor_lt]
        simp only [B]
        push_cast
        have hfl := Nat.lt_floor_add_one (ℓ * 2 ^ m)⁻¹
        have e : (1 / 2 ^ m) / ℓ = (ℓ * 2 ^ m)⁻¹ := by field_simp
        rw [div_lt_iff₀ hℓ0]
        have h3 : y i - a < ℓ * (1 + (ℓ * 2 ^ m)⁻¹) := by
          have : ℓ * (ℓ * 2 ^ m)⁻¹ = 1 / 2 ^ m := by field_simp
          nlinarith
        nlinarith
    have hinj : Set.InjOn (fun i => ⌊(y i - a) / ℓ⌋) ↑(P.filter fun i => k ∈ c i) := by
      intro i hi j hj hij
      by_contra hne
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hi hj
      have h := Int.abs_sub_lt_one_of_floor_eq_floor hij
      rw [← sub_div, show y i - a - (y j - a) = y i - y j by ring, abs_div, abs_of_pos hℓ0,
        div_lt_one hℓ0] at h
      exact absurd (hsep i hi.1 j hj.1 hne) (not_le.mpr h)
    have := Finset.card_le_card_of_injOn _ hmaps hinj
    simp only [Int.card_Ico, sub_zero, Int.toNat_natCast] at this
    exact this.trans (le_max_right _ _)
  set Q := P.biUnion c
  refine ⟨Q, ?_, ?_⟩
  · calc (Q.card : ℝ) ≤ ∑ i ∈ P, ((c i).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ P, (ℓ * 2 ^ m + (ℓ * 2 ^ m)⁻¹ + 2) := Finset.sum_le_sum fun i _ =>
          (Nat.cast_le.mpr (hcard i)).trans hMℓ
      _ = (ℓ * 2 ^ m + (ℓ * 2 ^ m)⁻¹ + 2) * P.card := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  · have h := lemma_4_1 μ P Q S (dyadicIco m) M hq c
      (fun i hi => Finset.subset_biUnion_of_mem c hi)
      (fun i hi x hx => by
        have hx' := hS i hi hx
        simp only [Set.mem_iUnion]
        refine ⟨⌊x * 2 ^ m⌋, ?_, mem_dyadicIco_iff.mpr rfl⟩
        simp only [c, Finset.mem_Icc]
        exact ⟨Int.floor_le_floor (mul_le_mul_of_nonneg_right hx'.1 h2m.le),
          Int.floor_le_floor (mul_le_mul_of_nonneg_right hx'.2 h2m.le)⟩)
      (fun i _ => hcard i) (fun k _ => hmeet k)
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun k _ =>
      Real.rpow_nonneg measureReal_nonneg _))
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hMℓ (by linarith)

end Lq

end FractalGeometry
