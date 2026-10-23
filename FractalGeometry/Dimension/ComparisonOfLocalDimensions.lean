import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.Dimension.LogMassRatios

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology Metric

open scoped ENNReal

section Besicovitch

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [HasBesicovitchCovering X]
  {ν' ν ν₁ ν₂ : Measure X} {d₁ d₂ : ℝ}

theorem ae_tendsto_log_div_log_sub_of_le [IsFiniteMeasure ν] (h : ν' ≤ ν) :
    ∀ᵐ x ∂ν', Tendsto (fun r : ℝ => Real.log (ν'.real (closedBall x r)) / Real.log r
      - Real.log (ν.real (closedBall x r)) / Real.log r) (𝓝[>] 0) (𝓝 0) := by
  have : IsFiniteMeasure ν' := isFiniteMeasure_of_le ν h
  have hac : ν' ≪ ν := Measure.absolutelyContinuous_of_le h
  filter_upwards [hac.ae_le (Besicovitch.ae_tendsto_rnDeriv ν' ν), Measure.rnDeriv_pos hac,
    hac.ae_le (Measure.rnDeriv_ne_top ν' ν)] with x hx hpos htop
  exact tendsto_log_div_log_sub hpos htop hx

end Besicovitch

end FractalGeometry
