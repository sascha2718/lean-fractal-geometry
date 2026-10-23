import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Measure Filter Topology Metric Set Module Function

open scoped ENNReal

section Pointwise

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {μ : Measure X} {x : X}
  {r s t c : ℝ}

theorem eventually_log_div_log_le (hc : 0 < c)
    (h : ∀ᶠ r : ℝ in 𝓝[>] 0, c * r ^ s ≤ μ.real (closedBall x r)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, Real.log (μ.real (closedBall x r)) / Real.log r ≤ s + ε := by
  have hL : Tendsto (fun r : ℝ => Real.log c / Real.log r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.div_atBot Real.tendsto_log_nhdsGT_zero
  have h1 : ∀ᶠ r : ℝ in 𝓝[>] 0, Real.log c / Real.log r < ε := hL.eventually_lt_const hε
  have h2 : ∀ᶠ r : ℝ in 𝓝[>] 0, Real.log r < 0 :=
    Real.tendsto_log_nhdsGT_zero.eventually_lt_atBot 0
  filter_upwards [h, h1, h2, self_mem_nhdsWithin] with r hr hr1 hr2 hr0
  have hr0 : 0 < r := hr0
  have hpos : 0 < c * r ^ s := mul_pos hc (Real.rpow_pos_of_pos hr0 s)
  have hlog : Real.log c + s * Real.log r ≤ Real.log (μ.real (closedBall x r)) := by
    rw [← Real.log_rpow hr0, ← Real.log_mul hc.ne' (Real.rpow_pos_of_pos hr0 s).ne']
    exact Real.log_le_log hpos hr
  calc Real.log (μ.real (closedBall x r)) / Real.log r
      ≤ (Real.log c + s * Real.log r) / Real.log r := div_le_div_of_nonpos_of_le hr2.le hlog
    _ = s + Real.log c / Real.log r := by
      rw [add_div, mul_div_assoc, div_self hr2.ne, mul_one, add_comm]
    _ ≤ s + ε := by linarith

end Pointwise

section UpperBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ ν₁ ν₂ : Measure E} {d d₁ d₂ : ℝ}

theorem ae_exists_mul_pow_le_measure_closedBall [IsLocallyFiniteMeasure μ] :
    ∀ᵐ x ∂μ, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
      c * ENNReal.ofReal (r ^ finrank ℝ E) ≤ μ (closedBall x r) := by
  let vol : Measure E := addHaar
  have hv0 : vol (ball (0 : E) 1) ≠ 0 := (measure_ball_pos vol 0 one_pos).ne'
  have hvtop : vol (ball (0 : E) 1) ≠ ∞ := measure_ball_lt_top.ne
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv vol μ, rnDeriv_lt_top vol μ] with x hx hlt
  have hC0 : vol.rnDeriv μ x + 1 ≠ 0 := by simp
  have hCtop : vol.rnDeriv μ x + 1 ≠ ∞ := by simp [hlt.ne]
  refine ⟨vol (ball (0 : E) 1) / (vol.rnDeriv μ x + 1), ENNReal.div_ne_zero.2 ⟨hv0, hCtop⟩,
    ENNReal.div_ne_top hvtop hC0, ?_⟩
  have hev := hx.eventually_lt_const (ENNReal.lt_add_right hlt.ne one_ne_zero)
  filter_upwards [hev, self_mem_nhdsWithin] with r hr hr0
  have hr0 : 0 < r := hr0
  have h1 : vol (closedBall x r) ≤ (vol.rnDeriv μ x + 1) * μ (closedBall x r) :=
    (ENNReal.div_le_iff_le_mul (Or.inr hCtop) (Or.inr hC0)).1 hr.le
  rw [addHaar_closedBall vol x hr0.le] at h1
  calc vol (ball (0 : E) 1) / (vol.rnDeriv μ x + 1) * ENNReal.ofReal (r ^ finrank ℝ E)
      = ENNReal.ofReal (r ^ finrank ℝ E) * vol (ball (0 : E) 1) / (vol.rnDeriv μ x + 1) := by
        rw [mul_comm, mul_div_assoc]
    _ ≤ μ (closedBall x r) := ENNReal.div_le_of_le_mul' h1

theorem ae_exists_mul_pow_le_measureReal_closedBall [IsFiniteMeasure μ] :
    ∀ᵐ x ∂μ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
      c * r ^ (finrank ℝ E : ℝ) ≤ μ.real (closedBall x r) := by
  filter_upwards [ae_exists_mul_pow_le_measure_closedBall (μ := μ)] with x ⟨c, hc0, hctop, hc⟩
  refine ⟨c.toReal, ENNReal.toReal_pos hc0 hctop, ?_⟩
  filter_upwards [hc, self_mem_nhdsWithin] with r hr hr0
  have hr0 : 0 < r := hr0
  have h := ENNReal.toReal_mono (measure_ne_top μ _) hr
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr0.le _), ← Real.rpow_natCast]
    at h

end UpperBound

end FractalGeometry
