/-
# Section 5.6: Comparison of dimensions

The inequalities between the dimensions of Block I on a bounded set, and the examples showing that
the lower box and packing dimensions are not comparable.

| Notes | Lean declaration | Location |
|---|---|---|
| The comparison chain | `dimension_comparison` | here |
| No ordering between lower box and packing dimension | `exists_lowerBoxDim_lt_packingDim`, `exists_packingDim_lt_lowerBoxDim` | here |
| The reciprocal sequence is compact | `isCompact_reciprocal_sequence` | here |
| The reciprocal sequence is countable | `countable_reciprocal_sequence` | here |
| Properties in the table of Section 5.6 | `upperBoxDim_mono`, `upperBoxDim_union`, `assouadDim_union`, `upperBoxDim_closure`, `assouadDim_closure`, `packingDim_iUnion`, `lipschitz_assouad_increase` | `Box.BoxDimension`, `Assouad.Basic`, `Box.PackingMeasure`, `Assouad.WeakTangents` |
-/
import GeometricMeasureTheory.Assouad.MeasureDimensions
import GeometricMeasureTheory.Box.ScaleExamples

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

variable {X : Type*} [MetricSpace X]

/-- The comparison of dimensions of Section 5.6: on a bounded set,
`dim_H ≤ lower box ≤ upper box ≤ Assouad` and `dim_H ≤ packing ≤ upper box`. -/
theorem dimension_comparison {E : Set X} (hb : Bornology.IsBounded E) (hne : E.Nonempty) :
    dimH E ≤ lowerBoxDim E ∧ lowerBoxDim E ≤ upperBoxDim E ∧ upperBoxDim E ≤ assouadDim E ∧
      dimH E ≤ packingDim E ∧ packingDim E ≤ upperBoxDim E :=
  ⟨hausdorff_lower_box E, lowerBoxDim_le_upperBoxDim E, upperBoxDim_le_assouadDim hb hne,
    dimH_le_packingDim E, packingDim_le_upperBoxDim⟩

/-- A compact set whose lower box dimension is smaller than its packing dimension. -/
theorem exists_lowerBoxDim_lt_packingDim :
    ∃ E : Set ℝ, IsCompact E ∧ lowerBoxDim E < packingDim E := by
  obtain ⟨E, hE, hlower, -, hpacking⟩ := exists_lowerBoxDim_zero_upperBoxDim_one
  refine ⟨E, hE, ?_⟩
  rw [hlower, hpacking]
  exact zero_lt_one

/-- The reciprocal sequence `{0} ∪ {1/(n+1)}` of Example 4.7 is compact. -/
theorem isCompact_reciprocal_sequence :
    IsCompact (insert (0 : ℝ) (Set.range fun n : ℕ => ((n : ℝ) + 1)⁻¹)) :=
  Filter.Tendsto.isCompact_insert_range <| by
    simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The reciprocal sequence `{0} ∪ {1/(n+1)}` of Example 4.7 is countable. -/
theorem countable_reciprocal_sequence :
    (insert (0 : ℝ) (Set.range fun n : ℕ => ((n : ℝ) + 1)⁻¹)).Countable :=
  (Set.countable_range _).insert _

/-- A compact set whose packing dimension is smaller than its lower box dimension. -/
theorem exists_packingDim_lt_lowerBoxDim :
    ∃ E : Set ℝ, IsCompact E ∧ packingDim E < lowerBoxDim E := by
  refine ⟨insert (0 : ℝ) (Set.range fun n : ℕ => ((n : ℝ) + 1)⁻¹),
    isCompact_reciprocal_sequence, ?_⟩
  rw [packingDim_countable countable_reciprocal_sequence, box_reciprocal_sequence.1]
  exact ENNReal.ofReal_pos.mpr (by norm_num)

end GeometricMeasureTheory
