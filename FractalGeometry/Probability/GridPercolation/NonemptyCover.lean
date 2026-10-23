import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open Filter Set Topology

open scoped ENNReal

lemma one_le_coverNum_of_nonempty {E : Type*} [PseudoEMetricSpace E]
    {r : ℝ} {Y : Set E} (hY : Y.Nonempty) : (1 : ℕ∞) ≤ coverNum r Y := by
  rw [coverNum]
  refine le_iInf fun C => le_iInf fun hcov => le_iInf fun _ => ?_
  rw [Set.one_le_encard_iff_nonempty]
  obtain ⟨y, hy⟩ := hY
  obtain ⟨S, hSC, -⟩ := hcov hy
  exact ⟨S, hSC⟩

end FractalGeometry.Probability.GridPercolation
