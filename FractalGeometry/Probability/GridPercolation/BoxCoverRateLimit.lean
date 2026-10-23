import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Dimension.PhiAssouad.BoxRate
import FractalGeometry.Probability.GridPercolation.ApproxSquareBoxDimensions
import FractalGeometry.Probability.GridPercolation.ApproxSquareCount
import FractalGeometry.Probability.GridPercolation.ApproxSquares
import FractalGeometry.Probability.GridPercolation.Floor
import FractalGeometry.Probability.GridPercolation.GridCoveringReduction
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Process

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open Filter Topology

variable {A : GridLaw} {Ω : Type*} {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

lemma eventually_boxCoverRate_nonneg (Y : Set (ℝ × ℝ)) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 ≤ boxCoverRate Y r := by
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr
  exact div_nonneg (Real.log_natCast_nonneg _)
    (Real.log_pos (one_lt_one_div hr.1 hr.2)).le

lemma coverNum_gridScale_limitSet_toNat_le (ω : Ω) (a : ℕ) :
    (coverNum (gridScale A.M a) (limitSet X ω)).toNat ≤ (A.M * A.N) ^ (a + 1) := by
  have hcard : (limitMeetingCodes X ω a).card ≤ Fintype.card (SquareCode A a) :=
    Finset.card_le_univ _
  have hcover : coverNum (gridScale A.M a) (limitSet X ω) ≤
      ((A.N * Fintype.card (SquareCode A a) : ℕ) : ℕ∞) := by
    calc
      coverNum (gridScale A.M a) (limitSet X ω) ≤
          (A.N : ℕ∞) * (limitMeetingCodes X ω a).card :=
        coverNum_le_mul_card_limitMeetingCodes ω a
      _ ≤ (A.N : ℕ∞) * Fintype.card (SquareCode A a) := by
        gcongr
      _ = ((A.N * Fintype.card (SquareCode A a) : ℕ) : ℕ∞) := by norm_cast
  have hnat := ENat.toNat_le_of_le_natCast hcover
  rw [card_squareCode] at hnat
  refine hnat.trans ?_
  have hb : A.N ^ (bfloor A.Gamma a) ≤ A.N ^ a :=
    pow_le_pow_right₀ (le_trans (by norm_num) (le_trans A.hM A.hMN.le)) (A.bfloor_le a)
  have hN : A.N ≤ A.M * A.N := by nlinarith [A.hM_pos, A.hN_pos]
  calc
    A.N * (A.M ^ a * A.N ^ (bfloor A.Gamma a)) ≤
        A.N * (A.M ^ a * A.N ^ a) := by gcongr
    _ = A.N * (A.M * A.N) ^ a := by rw [mul_pow]
    _ ≤ (A.M * A.N) * (A.M * A.N) ^ a := by gcongr
    _ = (A.M * A.N) ^ (a + 1) := by rw [pow_succ]; ring

lemma eventually_boxCoverRate_limitSet_le (ω : Ω) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      boxCoverRate (limitSet X ω) r ≤ 3 * Real.log (A.M * A.N) / Real.log A.M := by
  have hM0 : (0 : ℝ) < A.M := by exact_mod_cast A.hM_pos
  have hlogM : 0 < Real.log A.M := A.log_M_pos
  have hMN : (1 : ℝ) ≤ A.M * A.N :=
    one_le_mul_of_one_le_of_one_le A.one_le_M_real A.one_lt_N_real.le
  have hlogMN : 0 ≤ Real.log (A.M * A.N) := Real.log_nonneg hMN
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / A.M by positivity)] with r hr
  obtain ⟨hr0, hrM⟩ := hr
  set L : ℝ := Real.log (1 / r) with hL
  have hMr : (A.M : ℝ) ≤ 1 / r := by
    rw [le_one_div hM0 hr0]
    exact hrM.le
  have hLM : Real.log A.M ≤ L := Real.log_le_log hM0 hMr
  have hLpos : 0 < L := hlogM.trans_le hLM
  set q : ℝ := L / Real.log A.M with hq
  have hq1 : 1 ≤ q := by
    rw [hq, le_div_iff₀ hlogM, one_mul]
    exact hLM
  set a : ℕ := ⌈q⌉₊ with ha
  have hqa : q ≤ a := Nat.le_ceil q
  have haq : (a : ℝ) < q + 1 := Nat.ceil_lt_add_one (by linarith)
  have hLa : L ≤ a * Real.log A.M := by
    have := mul_le_mul_of_nonneg_right hqa hlogM.le
    rwa [hq, div_mul_cancel₀ _ hlogM.ne'] at this
  have hscale : gridScale A.M a ≤ r := by
    rw [gridScale_eq_inv_pow]
    have hpow : 1 / r ≤ (A.M : ℝ) ^ a := by
      calc
        1 / r = Real.exp L := by rw [hL, Real.exp_log (by positivity)]
        _ ≤ Real.exp (a * Real.log A.M) := Real.exp_le_exp.mpr hLa
        _ = (A.M : ℝ) ^ a := by
          rw [← Real.log_pow, Real.exp_log (by positivity)]
    rw [one_div] at hpow
    exact inv_le_of_inv_le₀ hr0 hpow
  have hcount : (coverNum r (limitSet X ω)).toNat ≤ (A.M * A.N) ^ (a + 1) := by
    refine le_trans ?_ (coverNum_gridScale_limitSet_toNat_le (X := X) ω a)
    exact ENat.toNat_le_toNat (coverNum_anti hscale)
      (ne_top_of_le_ne_top (ENat.natCast_ne_top _)
        (coverNum_le_mul_card_limitMeetingCodes (X := X) ω a))
  have hlog : Real.log (coverNum r (limitSet X ω)).toNat ≤
      ((a : ℝ) + 1) * Real.log (A.M * A.N) := by
    rcases Nat.eq_zero_or_pos (coverNum r (limitSet X ω)).toNat with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      positivity
    · calc
        Real.log (coverNum r (limitSet X ω)).toNat ≤
            Real.log (((A.M * A.N) ^ (a + 1) : ℕ) : ℝ) :=
          Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcount)
        _ = ((a : ℝ) + 1) * Real.log (A.M * A.N) := by
          rw [Nat.cast_pow, Nat.cast_mul, Real.log_pow]
          push_cast
          rfl
  have ha1 : (a : ℝ) + 1 ≤ 3 * q := by linarith
  unfold boxCoverRate
  rw [← hL, div_le_iff₀ hLpos]
  calc
    Real.log (coverNum r (limitSet X ω)).toNat ≤ ((a : ℝ) + 1) * Real.log (A.M * A.N) := hlog
    _ ≤ 3 * q * Real.log (A.M * A.N) := mul_le_mul_of_nonneg_right ha1 hlogMN
    _ = 3 * Real.log (A.M * A.N) / Real.log A.M * L := by
      rw [hq]
      field_simp

theorem tendsto_boxCoverRate_of_le_liminf_of_limsup_le {ω : Ω}
    (hF : (limitSet X ω).Nonempty) {s : ℝ}
    (hup : limsup (approximateSquareRate X ω) atTop ≤ s)
    (hlow : s ≤ liminf (approximateSquareRate X ω) atTop) :
    Tendsto (boxCoverRate (limitSet X ω)) (𝓝[>] (0 : ℝ)) (𝓝 s) := by
  have hsup : limsup (boxCoverRate (limitSet X ω)) (𝓝[>] (0 : ℝ)) ≤ s := by
    have h := upperBoxDim_eq_limsup_approximateSquareRate (X := X) hF
    rw [upperBoxDim] at h
    rw [h]
    exact hup
  have hinf : s ≤ liminf (boxCoverRate (limitSet X ω)) (𝓝[>] (0 : ℝ)) := by
    have h := lowerBoxDim_eq_liminf_approximateSquareRate (X := X) hF
    rw [lowerBoxDim] at h
    rw [h]
    exact hlow
  exact tendsto_of_le_liminf_of_limsup_le hinf hsup
    (isBoundedUnder_of_eventually_le (eventually_boxCoverRate_limitSet_le (X := X) ω))
    (isBoundedUnder_of_eventually_ge (eventually_boxCoverRate_nonneg _))

end FractalGeometry.Probability.GridPercolation
