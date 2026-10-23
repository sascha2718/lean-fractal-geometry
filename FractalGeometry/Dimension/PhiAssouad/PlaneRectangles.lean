import Mathlib

namespace FractalGeometry.Dimension.PhiAssouad

open Finset Set

open scoped ENNReal

variable {Ω : Type*}

lemma ediam_prod_Icc_le {x1 x2 y1 y2 r : ℝ} (h1 : x2 - x1 ≤ r) (h2 : y2 - y1 ≤ r) :
    Metric.ediam (Set.Icc x1 x2 ×ˢ Set.Icc y1 y2) ≤ ENNReal.ofReal r := by
  show Metric.ediam _ ≤ _
  refine Metric.ediam_le fun p hp q hq => ?_
  rw [Prod.edist_eq]
  refine max_le ?_ ?_
  · calc edist p.1 q.1 ≤ Metric.ediam (Set.Icc x1 x2) :=
        Metric.edist_le_ediam_of_mem hp.1 hq.1
      _ = ENNReal.ofReal (x2 - x1) := Real.ediam_Icc x1 x2
      _ ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal h1
  · calc edist p.2 q.2 ≤ Metric.ediam (Set.Icc y1 y2) :=
        Metric.edist_le_ediam_of_mem hp.2 hq.2
      _ = ENNReal.ofReal (y2 - y1) := Real.ediam_Icc y1 y2
      _ ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal h2

end FractalGeometry.Dimension.PhiAssouad
