import Mathlib
import FractalGeometry.Ergodic.Birkhoff

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Measure Filter Topology Metric Set Module Function

open scoped ENNReal

section Pointwise

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {μ : Measure X} {x : X}
  {r s t c : ℝ}

theorem ae_forall_measure_closedBall_pos [SecondCountableTopology X] (μ : Measure X) :
    ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < μ (closedBall x r) := by
  rw [ae_iff]
  refine measure_null_of_locally_null _ fun x hx => ?_
  simp only [mem_ofPred_eq, not_forall, not_lt, nonpos_iff_eq_zero] at hx
  obtain ⟨r, hr, h0⟩ := hx
  exact ⟨closedBall x r, mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x hr), h0⟩

end Pointwise

end FractalGeometry
