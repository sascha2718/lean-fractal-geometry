/-
# Section 2.2: Basic properties of Hausdorff dimension

Every result of this subsection is in Mathlib; the examples below state them in the form of the
notes.

| Notes | Lean declaration | Location |
|---|---|---|
| Proposition 2.15: monotonicity | `dimH_mono` | `Mathlib/Topology/MetricSpace/HausdorffDimension.lean` |
| Proposition 2.15: countable stability | `dimH_iUnion` | `Mathlib/Topology/MetricSpace/HausdorffDimension.lean` |
| Proposition 2.15: countable sets | `Set.Countable.dimH_zero` (alias of `dimH_countable`) | `Mathlib/Topology/MetricSpace/HausdorffDimension.lean` |
| Proposition 2.15: subsets of `ℝ^d` | `Real.dimH_univ_eq_finrank`, `dimH_mono` | `Mathlib/Topology/MetricSpace/HausdorffDimension.lean` |
| `ℚ ∩ [0, 1]` and `{0} ∪ {1/n}` have dimension zero | `Set.Countable.dimH_zero`, `Set.countable_range` | `Mathlib/Topology/MetricSpace/HausdorffDimension.lean` |
-/
import GeometricMeasureTheory.Hausdorff.Basic

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

variable {X : Type*} [EMetricSpace X]

/-! ## Proposition 2.15 (`thm:hausdorff-dimension-properties`) -/

example {E F : Set X} (h : E ⊆ F) : dimH E ≤ dimH F :=
  dimH_mono h

example (E : ℕ → Set X) : dimH (⋃ j, E j) = ⨆ j, dimH (E j) :=
  dimH_iUnion E

example {E : Set X} (hE : E.Countable) : dimH E = 0 :=
  hE.dimH_zero

example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (E : Set F) :
    dimH E ≤ Module.finrank ℝ F :=
  (dimH_mono (subset_univ E)).trans_eq (Real.dimH_univ_eq_finrank F)

/-! The examples after Proposition 2.15. -/

example : dimH ((Set.range ((↑) : ℚ → ℝ)) ∩ Icc 0 1) = 0 :=
  ((countable_range _).mono inter_subset_left).dimH_zero

example : dimH (insert (0 : ℝ) (Set.range fun n : ℕ => ((n : ℝ) + 1)⁻¹)) = 0 :=
  ((countable_range _).insert 0).dimH_zero

end GeometricMeasureTheory
