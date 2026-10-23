import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open Set

open scoped ENNReal

theorem coverNum_inter_eball_le_of_scale_bracket
    {E : Type*} [PseudoEMetricSpace E]
    {X : Set E} {x : E} {R Rg r rg : ℝ}
    (houter : R ≤ Rg) (hinner : rg ≤ r) :
    coverNum r (X ∩ Metric.eball x (ENNReal.ofReal R)) ≤
      coverNum rg (X ∩ Metric.eball x (ENNReal.ofReal Rg)) := by
  calc
    coverNum r (X ∩ Metric.eball x (ENNReal.ofReal R)) ≤
        coverNum r (X ∩ Metric.eball x (ENNReal.ofReal Rg)) := by
      apply coverNum_mono
      apply Set.inter_subset_inter_right
      exact Metric.eball_subset_eball (ENNReal.ofReal_le_ofReal houter)
    _ ≤ coverNum rg (X ∩ Metric.eball x (ENNReal.ofReal Rg)) :=
      coverNum_anti hinner

end FractalGeometry.Probability.GridPercolation
