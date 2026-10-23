import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Symbolic.Conditional
import FractalGeometry.Symbolic.ConditionalRefinement

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Set

theorem isMeasurablePartition_atomsOn {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [StandardBorelSpace X] {D : Set Ω} (hD : MeasurableSet D) {G : Ω → X} (hG : Measurable G)
    {ξ : Ω → Set Ω} (hξ : ∀ x ∈ D, ∀ y ∈ D, y ∈ ξ x ↔ G y = G x) :
    IsMeasurablePartition (atomsOn D ξ) := by
  classical
  have he := measurableEmbedding_embeddingReal X
  refine ⟨fun x => if x ∈ D then Real.exp (embeddingReal X (G x)) else 0, ?_, fun x y => ?_⟩
  · exact Measurable.ite hD (Real.measurable_exp.comp (he.measurable.comp hG)) measurable_const
  · by_cases hx : x ∈ D
    · rw [atomsOn_of_mem hx]
      by_cases hy : y ∈ D
      · simp only [mem_inter_iff, hy, and_true, ite_eq_left hx, ite_true, Real.exp_eq_exp,
          he.injective.eq_iff]
        exact hξ x hx y hy
      · simp [hx, hy, (Real.exp_pos _).ne]
    · rw [atomsOn_of_notMem hx]
      by_cases hy : y ∈ D
      · simp [hx, hy, (Real.exp_pos _).ne']
      · simp [hx, hy]

end FractalGeometry
