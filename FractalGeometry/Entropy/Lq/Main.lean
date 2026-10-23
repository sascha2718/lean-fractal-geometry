import Mathlib
import FractalGeometry.Entropy.Lq.Basic
import FractalGeometry.Entropy.Lq.Prop68
import FractalGeometry.Entropy.Lq.Statement
import FractalGeometry.Pressure.Rectangular.LyapunovStatement
import FractalGeometry.SelfSimilar.SimilarityWords

open MeasureTheory Filter Topology Set

namespace FractalGeometry

namespace Lq

universe u

variable {κ : Type*}

theorem exists_differentiableAt_lqSpectrum {ν : Measure ℝ} [IsProbabilityMeasure ν] {L : ℝ}
    (hL0 : 0 ≤ L) (hL : ν (Set.Icc (-L) L)ᶜ = 0) {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) :
    ∃ q ∈ Set.Ioo a b, DifferentiableAt ℝ (lqSpectrum ν) q := by
  set g : ℝ → ℝ := fun q => lqSpectrum ν (max q 1)
  have hg : Monotone g := fun x y hxy =>
    lqSpectrum_mono hL0 hL (le_max_right x 1) (max_le_max hxy le_rfl)
  have hae := hg.ae_differentiableAt
  have hne : (ae (volume.restrict (Set.Ioo a b))).NeBot := by
    rw [ae_restrict_neBot, Real.volume_Ioo]
    simpa using hab
  have h1 : ∀ᵐ x ∂(volume.restrict (Set.Ioo a b)), x ∈ Set.Ioo a b ∧ DifferentiableAt ℝ g x :=
    (ae_restrict_mem measurableSet_Ioo).and (ae_restrict_of_ae hae)
  obtain ⟨q, hq, hdiff⟩ := @Filter.Eventually.exists _ _ _ hne h1
  refine ⟨q, hq, hdiff.congr_of_eventuallyEq ?_⟩
  filter_upwards [Ioi_mem_nhds (lt_of_le_of_lt ha hq.1)] with y hy
  simp only [g, max_eq_left (le_of_lt (Set.mem_Ioi.mp hy))]

variable [Fintype κ]

theorem le_lqSpectrum_of_proposition68 {r t p : κ → ℝ} {μ : Measure ℝ}
    (h : IsSelfSimilar r t p μ) (hsep : ShmerkinExpSeparation r t)
    (h68 : Proposition68 r t p μ) {q : ℝ} (hq : 1 < q)
    (hd : DifferentiableAt ℝ (lqSpectrum μ) q) (hτ : lqSpectrum μ q < q - 1) {β : ℝ}
    (hβ : 0 ≤ β) (hsum : ∑ j, p j ^ q * |r j| ^ (-β) ≤ 1) : β ≤ lqSpectrum μ q := by
  obtain ⟨R, hR, hfreq⟩ := hsep
  set N := ⌈R⌉₊ with hN
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hR).ne'
  by_contra hlt
  push Not at hlt
  set τ := lqSpectrum μ q
  set σ := (β - τ) / 2 with hσ
  have hσ0 : 0 < σ := by rw [hσ]; linarith
  have hlim := h68 q hq hd hτ N hN1
  have hev : ∀ᶠ m : ℕ in atTop,
      -τ - σ < Real.logb 2 (lqSum (stoppedMeasure r t p m) q (N * m)) / m :=
    hlim.eventually (lt_mem_nhds (by linarith))
  obtain ⟨A, hA⟩ := card_ratioSet_le (h.abs_ratio_lt_one)
  set e := (Fintype.card κ : ℝ) * (q - 1)
  have hpoly := eventually_rpow_lt_two_rpow (B := 2 * A + 1) (e := e) (by
    have : (0 : ℝ) ≤ A := Nat.cast_nonneg A
    linarith) hσ0
  obtain ⟨m, hm, hm1, hmlog, hmpoly⟩ :=
    (hfreq.and_eventually ((eventually_ge_atTop 1).and (hev.and hpoly))).exists
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  set S := lqSum (stoppedMeasure r t p m) q (N * m)
  have hS0 : 0 < S := lqSum_stoppedMeasure_pos h.abs_ratio_lt_one h.weight_pos h.weight_sum
    hm1 (by linarith) _

  have h67 := lqSum_stoppedMeasure_le h.abs_ratio_lt_one h.weight_pos (t := t) (n := N * m)
    (R := R) hm (by
      push_cast
      exact mul_le_mul_of_nonneg_right (Nat.le_ceil R) (Nat.cast_nonneg m)) hq.le

  have h66 := sum_omega_weight_rpow_le h.ratio_ne_zero h.abs_ratio_lt_one h.weight_pos hβ
    hsum hm1

  have h63 : ((ratioSet r m).card : ℝ) ^ (q - 1) ≤ ((2 * A + 1) * m) ^ e := by
    have h1 : ((ratioSet r m).card : ℝ) ≤ ((A * (m + 1) + 1 : ℕ) : ℝ) ^ Fintype.card κ := by
      exact_mod_cast hA m
    have h2 : ((A * (m + 1) + 1 : ℕ) : ℝ) ≤ (2 * A + 1) * m := by
      push_cast
      have : (0 : ℝ) ≤ A := Nat.cast_nonneg A
      nlinarith
    calc ((ratioSet r m).card : ℝ) ^ (q - 1)
        ≤ (((A * (m + 1) + 1 : ℕ) : ℝ) ^ Fintype.card κ) ^ (q - 1) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) h1 (by linarith)
      _ ≤ (((2 * A + 1) * m) ^ Fintype.card κ) ^ (q - 1) :=
          Real.rpow_le_rpow (by positivity) (pow_le_pow_left₀ (Nat.cast_nonneg _) h2 _)
            (by linarith)
      _ = ((2 * A + 1) * m) ^ e := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]

  have hS1 : S ≤ ((2 * A + 1) * m) ^ e * (2 : ℝ) ^ (-(m * β)) :=
    h67.trans (mul_le_mul h63 h66 (Finset.sum_nonneg fun u _ =>
      Real.rpow_nonneg (wordWeight_pos h.weight_pos u).le _) (by positivity))
  have hS2 : (2 : ℝ) ^ ((-τ - σ) * m) < S := by
    rw [lt_div_iff₀ (by linarith)] at hmlog
    exact (Real.lt_logb_iff_rpow_lt (by norm_num) hS0).mp hmlog
  have hkey : (2 : ℝ) ^ (σ * m) < ((2 * A + 1) * m) ^ e := by
    have h3 : (2 : ℝ) ^ ((-τ - σ) * m) < ((2 * A + 1) * m) ^ e * (2 : ℝ) ^ (-(m * β)) :=
      hS2.trans_le hS1
    have h4 : (2 : ℝ) ^ ((-τ - σ) * m) = (2 : ℝ) ^ (σ * m) * (2 : ℝ) ^ (-(m * β)) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      rw [hσ]
      ring
    rw [h4] at h3
    exact lt_of_mul_lt_mul_right h3 (by positivity)
  exact absurd hmpoly (not_lt.mpr hkey.le)

theorem lt_lqSpectrum_of_proposition68 {r t p : κ → ℝ} {μ : Measure ℝ}
    (h : IsSelfSimilar r t p μ) (hsep : ShmerkinExpSeparation r t)
    (h68 : Proposition68 r t p μ) {q₀ : ℝ} {β : ℝ} (hβ : 0 < β)
    (hβq : β < q₀ - 1) (hsum : ∑ j, p j ^ q₀ * |r j| ^ (-β) < 1) : β < lqSpectrum μ q₀ := by
  obtain ⟨L, hL0, hL⟩ := h.exists_support
  have := h.isProbabilityMeasure
  have hrpos : ∀ j, 0 < |r j| := fun j => abs_pos.mpr (h.ratio_ne_zero j)

  have hcont1 : Continuous fun b : ℝ => ∑ j, p j ^ q₀ * |r j| ^ (-b) :=
    continuous_finsetSum _ fun j _ => continuous_const.mul
      (continuous_const.rpow continuous_neg fun _ => Or.inl (hrpos j).ne')
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    ((hcont1.tendsto β).eventually (gt_mem_nhds hsum))
  set β' := β + min ε (q₀ - 1 - β) / 2 with hβ'
  have hmin : 0 < min ε (q₀ - 1 - β) := lt_min hε (by linarith)
  have hββ' : β < β' := by rw [hβ']; linarith
  have hβ'q : β' < q₀ - 1 := by
    rw [hβ']; linarith [min_le_right ε (q₀ - 1 - β)]
  have hsum' : ∑ j, p j ^ q₀ * |r j| ^ (-β') < 1 := hball (by
    rw [Real.dist_eq, hβ', add_sub_cancel_left, abs_of_pos (by linarith)]
    linarith [min_le_left ε (q₀ - 1 - β)])

  have hcont2 : Continuous fun q : ℝ => ∑ j, p j ^ q * |r j| ^ (-β') :=
    continuous_finsetSum _ fun j _ =>
      (continuous_const.rpow continuous_id fun _ => Or.inl (h.weight_pos j).ne').mul
        continuous_const
  obtain ⟨η, hη, hball2⟩ := Metric.eventually_nhds_iff.mp
    ((hcont2.tendsto q₀).eventually (gt_mem_nhds hsum'))
  set a := max (q₀ - η) (β' + 1) with ha
  have ha1 : 1 ≤ a := le_max_of_le_right (by linarith)
  have haq : a < q₀ := max_lt (by linarith) (by linarith)
  obtain ⟨q, ⟨hqa, hqq₀⟩, hd⟩ := exists_differentiableAt_lqSpectrum hL0 hL ha1 haq
  have hq1 : 1 < q := lt_of_le_of_lt ha1 hqa
  have hβ'q' : β' < q - 1 := by linarith [le_max_right (q₀ - η) (β' + 1)]
  have hsumq : ∑ j, p j ^ q * |r j| ^ (-β') ≤ 1 := (hball2 (by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [le_max_left (q₀ - η) (β' + 1)])).le
  have hτq : β' ≤ lqSpectrum μ q := by
    by_cases hτ : lqSpectrum μ q < q - 1
    · exact le_lqSpectrum_of_proposition68 h hsep h68 hq1 hd hτ (by linarith) hsumq
    · push Not at hτ
      linarith
  calc β < β' := hββ'
    _ ≤ lqSpectrum μ q := hτq
    _ ≤ lqSpectrum μ q₀ := lqSpectrum_mono hL0 hL hq1.le hqq₀.le

end Lq

open Lq in

theorem shmerkinLqDimension_of_proposition68
    (h68 : ∀ {κ : Type u} [Fintype κ] (r t p : κ → ℝ) (μ : Measure ℝ),
      IsSelfSimilar r t p μ → Proposition68 r t p μ) :
    ShmerkinLqDimension.{u} := by
  intro κ _ r t p hr hr1 hp hp1 hsep μ _ hμ q hq α hα hsum
  have h : IsSelfSimilar r t p μ := ⟨hr, hr1, hp, hp1, inferInstance, hμ⟩
  obtain ⟨L, hL0, hL⟩ := h.exists_support
  by_cases hβ : (q - 1) * α ≤ 0
  · refine Eventually.of_forall fun M s => ?_
    calc ∑ k ∈ s, μ.real (Set.Ico ((k : ℝ) / 2 ^ M) ((k + 1) / 2 ^ M)) ^ q
        ≤ lqSum μ q M := sum_le_lqSum μ hq.le M s
      _ ≤ 1 := lqSum_le_one μ hq.le M
      _ ≤ (2 : ℝ) ^ (-((M : ℝ) * ((q - 1) * α))) :=
          Real.one_le_rpow (by norm_num) (by nlinarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)])
  · push Not at hβ
    have hβq : (q - 1) * α < q - 1 := by nlinarith
    have hτ := lt_lqSpectrum_of_proposition68 h hsep (h68 r t p μ h) hβ hβq hsum
    filter_upwards [eventually_lqSum_le hL0 hL hq.le hτ] with M hM s
    calc ∑ k ∈ s, μ.real (Set.Ico ((k : ℝ) / 2 ^ M) ((k + 1) / 2 ^ M)) ^ q
        ≤ lqSum μ q M := sum_le_lqSum μ hq.le M s
      _ ≤ (2 : ℝ) ^ (-((M : ℝ) * ((q - 1) * α))) := by rw [mul_comm (M : ℝ)]; exact hM

end FractalGeometry
