module

/-
Invariant measures of the iterated function system `Φ`, used in the case `s ≥ 2` of
`thm:main_extended` in `sec:dimension_result_proof`.

* `System.IsInvariantMeasure`: the measure `ν` on the plane satisfies
  `ν = ∑_i p_i (φ_i)_*ν` for the weights `p`.
-/
public import BoxLike.System
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Map

@[expose] public section

namespace BoxLike

open MeasureTheory
open scoped ENNReal

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι)

/-- The measure `ν` on the plane is invariant under `Φ` with the weights `p`:
`ν = ∑_i p_i (φ_i)_*ν`. -/
def IsInvariantMeasure (p : ι → ℝ≥0∞) (ν : Measure (ℝ × ℝ)) : Prop :=
  ν = ∑ i, p i • ν.map (S.phi i)

end System

end BoxLike
