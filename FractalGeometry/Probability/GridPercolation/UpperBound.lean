import FractalGeometry.Probability.GridPercolation.UpperCovering

/-! The first-moment and Borel–Cantelli upper bound for box dimension. -/

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory ProbabilityTheory Filter Topology
open FractalGeometry.Dimension.PhiAssouad
open scoped ENNReal

variable {A : GridLaw} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

lemma GridLaw.lam_le_mean (A : GridLaw) : A.lam ≤ A.m := by
  obtain ⟨β, hβ, hval, hmin⟩ := A.lam_isMinOn
  rw [← A.colSum_one, ← hval]
  exact hmin 1 (by simp)

lemma GridLaw.sbox_nonneg (A : GridLaw) (hm : 1 < A.m) : 0 ≤ A.sbox := by
  unfold GridLaw.sbox GridLaw.sproj
  exact add_nonneg (div_nonneg (Real.log_nonneg hm.le) A.log_N_pos.le)
    (mul_nonneg (sub_nonneg.mpr A.Gamma_lt_one.le)
      (div_nonneg (Real.log_nonneg (A.one_le_lam hm)) A.log_M_pos.le))

lemma squareCount_mean_bound (hX : IsPercolation P X) (hm : 1 < A.m) (a : ℕ) :
    ∫ ω, (squareCount X (bfloor A.Gamma a) (a - bfloor A.Gamma a) ω : ℝ) ∂P ≤
      Real.exp (a * (A.sbox * Real.log A.M)) := by
  refine (integral_squareCount_le hX _ _).trans ?_
  have hm0 := zero_lt_one.trans hm
  have hl0 := A.lam_pos hm
  have hlm : Real.log A.lam ≤ Real.log A.m := Real.log_le_log hl0 A.lam_le_mean
  have hb := bfloor_cast_le A.Gamma_pos.le a
  have hba := A.bfloor_le a
  calc
    A.m ^ bfloor A.Gamma a * A.lam ^ (a - bfloor A.Gamma a) =
        Real.exp ((bfloor A.Gamma a : ℝ) * Real.log A.m +
          (a - bfloor A.Gamma a : ℕ) * Real.log A.lam) := by
      rw [Real.exp_add, ← Real.log_pow, ← Real.log_pow,
        Real.exp_log (pow_pos hm0 _), Real.exp_log (pow_pos hl0 _)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [sbox_log_M_eq_gamma_log_m_add, Nat.cast_sub hba]
      nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hlm)]

theorem ae_eventually_squareCount_lt_exp (hX : IsPercolation P X) (hm : 1 < A.m)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ᶠ a : ℕ in atTop,
      (squareCount X (bfloor A.Gamma a) (a - bfloor A.Gamma a) ω : ℝ) <
        Real.exp (a * (A.sbox * Real.log A.M + ε)) := by
  let := hX.toIsProbabilityMeasure
  let bad : ℕ → Set Ω := fun a => {ω |
    Real.exp (a * (A.sbox * Real.log A.M + ε)) ≤
      (squareCount X (bfloor A.Gamma a) (a - bfloor A.Gamma a) ω : ℝ)}
  have hbad (a : ℕ) : P (bad a) ≤ ENNReal.ofReal (Real.exp (-ε) ^ a) := by
    rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)]
    have hmark := mul_meas_ge_le_integral_of_nonneg
      (μ := P) (f := fun ω =>
        (squareCount X (bfloor A.Gamma a) (a - bfloor A.Gamma a) ω : ℝ))
      (Eventually.of_forall fun _ => Nat.cast_nonneg _)
      (integrable_squareCount hX _ _)
      (Real.exp (a * (A.sbox * Real.log A.M + ε)))
    change Real.exp (a * (A.sbox * Real.log A.M + ε)) * (P (bad a)).toReal ≤ _ at hmark
    rw [mul_comm] at hmark
    have hmark := (le_div_iff₀ (Real.exp_pos (a * (A.sbox * Real.log A.M + ε)))).mpr hmark
    have hquot : Real.exp (a * (A.sbox * Real.log A.M)) /
        Real.exp (a * (A.sbox * Real.log A.M + ε)) = Real.exp (-ε) ^ a := by
      rw [← Real.exp_sub, ← Real.exp_nat_mul]
      congr 1
      ring
    rw [← hquot]
    exact hmark.trans (div_le_div_of_nonneg_right (squareCount_mean_bound hX hm a)
      (Real.exp_pos _).le)
  have hs : Summable fun a : ℕ => Real.exp (-ε) ^ a :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (by rw [Real.exp_lt_one_iff]; linarith)
  have hsum : (∑' a, P (bad a)) ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' a : ℕ, Real.exp (-ε) ^ a)) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun a => by positivity) hs]
    exact ENNReal.tsum_le_tsum hbad
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  exact hω.mono fun a ha => lt_of_not_ge ha

theorem ae_eventually_approximateSquareRate_le (hX : IsPercolation P X) (hm : 1 < A.m)
    {η : ℝ} (hη : 0 < η) :
    ∀ᵐ ω ∂P, ∀ᶠ a : ℕ in atTop, approximateSquareRate X ω a ≤ A.sbox + η := by
  have hlogM := A.log_M_pos
  have hev : ∀ᶠ a : ℕ in atTop,
      Real.log (25 * (A.N : ℝ)) / (a * Real.log A.M) ≤ η / 2 :=
    (tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_mul_const hlogM)).eventually_le_const (by linarith)
  filter_upwards [ae_eventually_squareCount_lt_exp hX hm
    (show 0 < η / 2 * Real.log A.M by positivity)] with ω hω
  filter_upwards [hω, hev, eventually_ge_atTop 1] with a ha he ha1
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
  have hden : 0 < (a : ℝ) * Real.log A.M := mul_pos ha0 hlogM
  have hN : (0 : ℝ) < A.N := by exact_mod_cast A.hN_pos
  have hC : 0 < 25 * (A.N : ℝ) := by positivity
  have hcard : ((limitMeetingCodes X ω a).card : ℝ) ≤
      25 * A.N * Real.exp (a * (A.sbox * Real.log A.M + η / 2 * Real.log A.M)) := by
    have h := card_limitMeetingCodes_le_squareCount (X := X) ω a
    exact (by exact_mod_cast h : ((limitMeetingCodes X ω a).card : ℝ) ≤
      25 * A.N * (squareCount X (bfloor A.Gamma a) (a - bfloor A.Gamma a) ω : ℝ)).trans
        (mul_le_mul_of_nonneg_left ha.le hC.le)
  rcases Nat.eq_zero_or_pos (limitMeetingCodes X ω a).card with hzero | hpos
  · simp only [approximateSquareRate, hzero, Nat.cast_zero, Real.log_zero, zero_div]
    exact add_nonneg (A.sbox_nonneg hm) hη.le
  · have hlog := Real.log_le_log (by exact_mod_cast hpos) hcard
    rw [Real.log_mul hC.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
    unfold approximateSquareRate
    apply (div_le_iff₀ hden).mpr
    have he' := (div_le_iff₀ hden).mp he
    nlinarith

theorem ae_limsup_approximateSquareRate_le (hX : IsPercolation P X) (hm : 1 < A.m) :
    ∀ᵐ ω ∂P, limsup (approximateSquareRate X ω) atTop ≤ A.sbox := by
  have hall : ∀ᵐ ω ∂P, ∀ j : ℕ, ∀ᶠ a : ℕ in atTop,
      approximateSquareRate X ω a ≤ A.sbox + 1 / ((j : ℝ) + 1) :=
    ae_all_iff.mpr fun j => ae_eventually_approximateSquareRate_le hX hm (by positivity)
  filter_upwards [hall] with ω hω
  have hcob : IsCoboundedUnder (· ≤ ·) atTop (approximateSquareRate X ω) :=
    isCoboundedUnder_le_of_eventually_le atTop (Eventually.of_forall fun a =>
      div_nonneg (Real.log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) A.log_M_pos.le))
  have hj (j : ℕ) : limsup (approximateSquareRate X ω) atTop ≤ A.sbox + 1 / ((j : ℝ) + 1) :=
    limsup_le_of_le hcob (hω j)
  by_contra h
  obtain ⟨j, hj'⟩ := exists_nat_one_div_lt (sub_pos.mpr (not_le.mp h))
  linarith [hj j]

end FractalGeometry.Probability.GridPercolation
