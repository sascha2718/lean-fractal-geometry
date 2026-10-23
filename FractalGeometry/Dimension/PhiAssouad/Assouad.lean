import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Dimension.PhiAssouad

open Set EMetric

open scoped ENNReal

noncomputable def dimA {E : Type*} [PseudoEMetricSpace E] (X : Set E) : ℝ :=
  sInf {s | 0 ≤ s ∧ ∃ C : ℝ, 0 < C ∧ ∀ R r : ℝ, 0 < r → r ≤ R → R < 1 → ∀ x ∈ X,
    (coverNum r (X ∩ Metric.eball x (ENNReal.ofReal R)) : ℝ≥0∞)
      ≤ ENNReal.ofReal (C * (R / r) ^ s)}

section

variable {E : Type*} [PseudoEMetricSpace E]

lemma bddBelow_assouadExponents (X : Set E) : BddBelow (AssouadExponents X) :=
  ⟨0, fun _ hs => hs.1⟩

end

end FractalGeometry.Dimension.PhiAssouad
