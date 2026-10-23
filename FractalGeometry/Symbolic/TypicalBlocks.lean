import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.Ergodic.ShannonMcMillanBreiman
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.Shift
import FractalGeometry.Symbolic.TypicalWords

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Measure Filter Topology Metric Set

open scoped ENNReal NNReal Matrix.Norms.L2Operator

section Typical

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]

theorem ae_eventually_block_mem_typicalWords (herg : Ergodic (shift 1) μ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᵐ x ∂μ, ∀ᶠ n : ℕ in atTop, block n x ∈ typicalWords μ (entropy μ) ε n := by
  filter_upwards [tendsto_neg_log_cylinder_entropy herg, ae_measureReal_cylinder_pos (μ := μ)]
    with x hx hpos
  filter_upwards [hx.eventually_lt_const (lt_add_of_pos_right _ hε),
    hx.eventually_const_lt (sub_lt_self _ hε), eventually_gt_atTop 0] with n h1 h2 hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hlog := Real.exp_log (hpos n)
  rw [div_lt_iff₀ hn'] at h1
  rw [lt_div_iff₀ hn'] at h2
  rw [mem_typicalWords]
  constructor
  · rw [← hlog, Real.exp_le_exp]
    nlinarith
  · rw [← hlog, Real.exp_le_exp]
    nlinarith

end Typical

end FractalGeometry
