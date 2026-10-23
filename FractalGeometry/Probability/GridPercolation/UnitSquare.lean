import Mathlib
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Process

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open Filter Topology MeasureTheory

open scoped ENNReal

variable {Ω ι : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in

lemma limitSet_subset_unitSquare {A : GridLaw}
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (ω : Ω) :
    limitSet X ω ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
  intro z hz
  have h0 : z ∈ levelSet X ω 0 := Set.iInter_subset _ 0 hz
  simp only [levelSet, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at h0
  obtain ⟨w, ⟨hw, -⟩, hzw⟩ := h0
  have hw' : w = [] := List.length_eq_zero_iff.mp hw
  rw [hw'] at hzw
  exact hzw

end FractalGeometry.Probability.GridPercolation
