import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.Dimension.Exact

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology Metric

open scoped ENNReal

section Definitions

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  {μ ν' ν : Measure X} {x : X} {d d' d₁ d₂ : ℝ}

theorem tendsto_log_div_log_sub {c : ℝ≥0∞} (hc : 0 < c) (hc' : c ≠ ∞)
    (h : Tendsto (fun r : ℝ => ν' (closedBall x r) / ν (closedBall x r)) (𝓝[>] 0) (𝓝 c)) :
    Tendsto (fun r : ℝ => Real.log (ν'.real (closedBall x r)) / Real.log r
      - Real.log (ν.real (closedBall x r)) / Real.log r) (𝓝[>] 0) (𝓝 0) := by
  have hc0 : 0 < c.toReal := ENNReal.toReal_pos hc.ne' hc'
  have hq : Tendsto (fun r : ℝ => ν'.real (closedBall x r) / ν.real (closedBall x r))
      (𝓝[>] 0) (𝓝 c.toReal) := by
    simpa only [Function.comp_def, ENNReal.toReal_div, Measure.real_def] using
      (ENNReal.tendsto_toReal hc').comp h
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < ν'.real (closedBall x r) / ν.real (closedBall x r) :=
    hq.eventually_const_lt hc0
  have hlog : Tendsto (fun r : ℝ => Real.log (ν'.real (closedBall x r))
      - Real.log (ν.real (closedBall x r))) (𝓝[>] 0) (𝓝 (Real.log c.toReal)) := by
    refine (hq.log hc0.ne').congr' ?_
    filter_upwards [hpos] with r hr
    have h' : ν'.real (closedBall x r) ≠ 0 := fun h0 => by simp [h0] at hr
    have h'' : ν.real (closedBall x r) ≠ 0 := fun h0 => by simp [h0] at hr
    exact Real.log_div h' h''
  have hdiv := hlog.div_atBot Real.tendsto_log_nhdsGT_zero
  simpa only [sub_div] using hdiv

end Definitions

end FractalGeometry
