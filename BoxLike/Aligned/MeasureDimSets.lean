module

/-
The set-based argument of `sec:ledrappier_young_formula` for the dimensions of a sum of measures
(tex lines 2674 to 2685), and the characterisation of the measures whose pointwise dimension
takes two values almost everywhere by `\overline{dim}_p` and `\underline{dim}_H` (tex lines 2686
to 2688).

The article derives `eq:haus_dim_sum` from `eq:dimension_measure_def`. Since `μ ≪ μ + ν`, every
Borel set of full `(μ + ν)`-measure has full `μ`-measure and every Borel set of positive
`μ`-measure has positive `(μ + ν)`-measure, so `\overline{dim}_p(μ + ν) ≥ \overline{dim}_p(μ)`
and `\underline{dim}_H(μ + ν) ≤ \underline{dim}_H(μ)`. For the reverse inequalities, Borel sets
`A`, `B` of full `μ`- and `ν`-measure with packing dimensions close to `\overline{dim}_p(μ)` and
`\overline{dim}_p(ν)` give the Borel set `A ∪ B` of full `(μ + ν)`-measure with
`dim_P(A ∪ B) = max {dim_P A, dim_P B}`, and a Borel set `C` of positive `(μ + ν)`-measure with
Hausdorff dimension close to `\underline{dim}_H(μ + ν)` has positive `μ`- or `ν`-measure.
Both lines of `eq:dimension_measure_def` are theorems of `PackingDimMeasure` and
`LocalDimBounds`.

* `packingDim_union_le`, `packingDim_union`: the packing dimension is finitely stable.
* `lowerHausdorffDim_le_of_absolutelyContinuous`: `μ ≪ ν` and `μ ≠ 0` give
  `\underline{dim}_H(ν) ≤ \underline{dim}_H(μ)`, from the second line of
  `eq:dimension_measure_def`.
* `le_upperPackingDim_add_left`, `le_upperPackingDim_add_right`,
  `lowerHausdorffDim_add_le_left`, `lowerHausdorffDim_add_le_right`: the four monotonicity
  inequalities of tex lines 2550 to 2553.
* `upperPackingDim_add_eq_max`, `lowerHausdorffDim_add_eq_min`: `eq:haus_dim_sum` by the
  set-based argument.
* `hasLocalDimPair_iff_upperPackingDim_lowerHausdorffDim`: the pointwise dimension of a nonzero
  measure exists almost everywhere with two values if and only if it exists almost everywhere
  with the values `\overline{dim}_p(μ)` and `\underline{dim}_H(μ)` only.
-/
public import BoxLike.PackingDimMeasure

@[expose] public section

namespace BoxLike

open MeasureTheory Measure Filter Topology Metric Set
open scoped ENNReal NNReal

/-! ### Finite stability of the packing dimension -/

section Packing

variable {X : Type*} [PseudoMetricSpace X]

/-- `dim_P(E ∪ F) ≤ max {dim_P E, dim_P F}`: interleaving two countable bounded covers of `E`
and `F` gives one of `E ∪ F` (tex lines 2553 to 2555, the countable stability of the packing
dimension). -/
theorem packingDim_union_le (E F : Set X) :
    packingDim (E ∪ F) ≤ max (packingDim E) (packingDim F) := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  obtain ⟨A, hA, hAb, hAc⟩ : ∃ A : ℕ → Set X, E ⊆ ⋃ i, A i ∧
      (∀ i, Bornology.IsBounded (A i)) ∧ ⨆ i, upperBoxDim (A i) < c := by
    simpa only [packingDim, iInf_lt_iff, exists_prop] using (le_max_left _ _).trans_lt hc
  obtain ⟨B, hB, hBb, hBc⟩ : ∃ B : ℕ → Set X, F ⊆ ⋃ i, B i ∧
      (∀ i, Bornology.IsBounded (B i)) ∧ ⨆ i, upperBoxDim (B i) < c := by
    simpa only [packingDim, iInf_lt_iff, exists_prop] using (le_max_right _ _).trans_lt hc
  -- The interleaved cover `C (2i) = A i`, `C (2i + 1) = B i`.
  set e := Equiv.natSumNatEquivNat
  set C : ℕ → Set X := fun n => Sum.elim A B (e.symm n)
  have hCA : ∀ i, C (e (Sum.inl i)) = A i := fun i => by simp [C]
  have hCB : ∀ i, C (e (Sum.inr i)) = B i := fun i => by simp [C]
  refine packingDim_le_of_cover C ?_ (fun n => ?_) (iSup_le fun n => ?_)
  · rintro x (hx | hx)
    · obtain ⟨i, hi⟩ := mem_iUnion.1 (hA hx)
      exact mem_iUnion.2 ⟨e (Sum.inl i), (hCA i).symm ▸ hi⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.1 (hB hx)
      exact mem_iUnion.2 ⟨e (Sum.inr i), (hCB i).symm ▸ hi⟩
  · rcases h : e.symm n with i | i <;> simp only [C, h, Sum.elim_inl, Sum.elim_inr]
    exacts [hAb i, hBb i]
  · rcases h : e.symm n with i | i <;> simp only [C, h, Sum.elim_inl, Sum.elim_inr]
    exacts [(le_iSup (fun i => upperBoxDim (A i)) i).trans hAc.le,
      (le_iSup (fun i => upperBoxDim (B i)) i).trans hBc.le]

/-- `dim_P(E ∪ F) = max {dim_P E, dim_P F}`. -/
theorem packingDim_union (E F : Set X) :
    packingDim (E ∪ F) = max (packingDim E) (packingDim F) :=
  le_antisymm (packingDim_union_le E F)
    (max_le (packingDim_mono subset_union_left) (packingDim_mono subset_union_right))

end Packing

/-! ### `eq:haus_dim_sum` from `eq:dimension_measure_def` -/

section Sum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ ν : Measure E}

/-- If `μ ≪ ν` for finite Borel measures on a finite-dimensional real normed space and `μ ≠ 0`,
then `\underline{dim}_H(ν) ≤ \underline{dim}_H(μ)`: every Borel set of positive `μ`-measure has
positive `ν`-measure, so the infimum in the second line of `eq:dimension_measure_def` for `ν` is
taken over more sets. This is the argument of tex lines 2550 to 2553 for
`\underline{dim}_H(μ + ν) ≤ \underline{dim}_H(μ)`.
Depends on: `ofReal_lowerHausdorffDim_eq_iInf_dimH_of_finiteDimensional`. -/
theorem lowerHausdorffDim_le_of_absolutelyContinuous [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ ≪ ν) (hne : μ ≠ 0) : lowerHausdorffDim ν ≤ lowerHausdorffDim μ := by
  have hνne : ν ≠ 0 := fun h0 => hne (Measure.absolutelyContinuous_zero_iff.1 (h0 ▸ h))
  have hle : ENNReal.ofReal (lowerHausdorffDim ν) ≤ ENNReal.ofReal (lowerHausdorffDim μ) := by
    rw [ofReal_lowerHausdorffDim_eq_iInf_dimH_of_finiteDimensional hne,
      ofReal_lowerHausdorffDim_eq_iInf_dimH_of_finiteDimensional hνne]
    exact le_iInf fun A => le_iInf fun hA => le_iInf fun hpos =>
      iInf_le_of_le A (iInf_le_of_le hA (iInf_le _ (pos_iff_ne_zero.2 fun h0 =>
        hpos.ne' (h h0))))
  exact (ENNReal.ofReal_le_ofReal_iff lowerHausdorffDim_nonneg).1 hle

/-- Tex lines 2674 to 2677: `\overline{dim}_p(μ + ν) ≥ \overline{dim}_p(μ)`, since
`μ ≪ μ + ν`. -/
theorem le_upperPackingDim_add_left [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    upperPackingDim μ ≤ upperPackingDim (μ + ν) :=
  upperPackingDim_le_of_absolutelyContinuous (AbsolutelyContinuous.rfl.add_right ν)

/-- `\overline{dim}_p(μ + ν) ≥ \overline{dim}_p(ν)`, since `ν ≪ μ + ν`. -/
theorem le_upperPackingDim_add_right [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    upperPackingDim ν ≤ upperPackingDim (μ + ν) := by
  rw [add_comm]
  exact le_upperPackingDim_add_left

/-- Tex lines 2674 to 2677: `\underline{dim}_H(μ + ν) ≤ \underline{dim}_H(μ)` for `μ ≠ 0`,
since `μ ≪ μ + ν`. -/
theorem lowerHausdorffDim_add_le_left [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hne : μ ≠ 0) :
    lowerHausdorffDim (μ + ν) ≤ lowerHausdorffDim μ :=
  lowerHausdorffDim_le_of_absolutelyContinuous (AbsolutelyContinuous.rfl.add_right ν) hne

/-- `\underline{dim}_H(μ + ν) ≤ \underline{dim}_H(ν)` for `ν ≠ 0`, since `ν ≪ μ + ν`. -/
theorem lowerHausdorffDim_add_le_right [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hne : ν ≠ 0) :
    lowerHausdorffDim (μ + ν) ≤ lowerHausdorffDim ν := by
  rw [add_comm]
  exact lowerHausdorffDim_add_le_left hne

/-- First line of `eq:haus_dim_sum` by the argument of the article:
`\overline{dim}_p(μ + ν) = max {\overline{dim}_p(μ), \overline{dim}_p(ν)}` for finite Borel
measures on a finite-dimensional real normed space. The inequality `≥` is
`le_upperPackingDim_add_left` and `le_upperPackingDim_add_right`. For `≤`, Borel sets `A`, `B`
of full `μ`- and `ν`-measure with `dim_P A ≤ \overline{dim}_p(μ) + ε` and
`dim_P B ≤ \overline{dim}_p(ν) + ε` give the set `A ∪ B` of full `(μ + ν)`-measure, and the first
line of `eq:dimension_measure_def` gives
`\overline{dim}_p(μ + ν) ≤ dim_P(A ∪ B) = max {dim_P A, dim_P B}`. The measures may be zero.
Depends on: `exists_packingDim_le`, `ofReal_upperPackingDim_le_packingDim`,
`packingDim_union`. -/
theorem upperPackingDim_add_eq_max [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    upperPackingDim (μ + ν) = max (upperPackingDim μ) (upperPackingDim ν) := by
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_)
    (max_le le_upperPackingDim_add_left le_upperPackingDim_add_right)
  obtain ⟨A, -, hA, hAdim⟩ := exists_packingDim_le (μ := μ) hε
  obtain ⟨B, -, hB, hBdim⟩ := exists_packingDim_le (μ := ν) hε
  have hAB : (μ + ν) (A ∪ B)ᶜ = 0 := by
    rw [Measure.add_apply, compl_union, measure_mono_null inter_subset_left hA,
      measure_mono_null inter_subset_right hB, add_zero]
  have h := (ofReal_upperPackingDim_le_packingDim hAB).trans_eq (packingDim_union A B)
  have hA' : upperPackingDim μ + ε ≤ max (upperPackingDim μ) (upperPackingDim ν) + ε :=
    add_le_add_left (le_max_left _ _) ε
  have hB' : upperPackingDim ν + ε ≤ max (upperPackingDim μ) (upperPackingDim ν) + ε :=
    add_le_add_left (le_max_right _ _) ε
  have hmax : max (packingDim A) (packingDim B) ≤
      ENNReal.ofReal (max (upperPackingDim μ) (upperPackingDim ν) + ε) :=
    max_le (hAdim.trans (ENNReal.ofReal_le_ofReal hA'))
      (hBdim.trans (ENNReal.ofReal_le_ofReal hB'))
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (le_max_of_le_left upperPackingDim_nonneg)
    hε.le)).1 (h.trans hmax)

/-- Second line of `eq:haus_dim_sum` by the argument of the article:
`\underline{dim}_H(μ + ν) = min {\underline{dim}_H(μ), \underline{dim}_H(ν)}` for nonzero finite
Borel measures on a finite-dimensional real normed space. The inequality `≤` is
`lowerHausdorffDim_add_le_left` and `lowerHausdorffDim_add_le_right`. For `≥`, a Borel set `C`
with `(μ + ν)(C) > 0` and `dim_H C ≤ \underline{dim}_H(μ + ν) + ε` has `μ(C) > 0` or
`ν(C) > 0`, so the second line of `eq:dimension_measure_def` gives
`min {\underline{dim}_H(μ), \underline{dim}_H(ν)} ≤ dim_H C`.
Depends on: `exists_measurableSet_dimH_le`, `ofReal_lowerHausdorffDim_le_dimH`. -/
theorem lowerHausdorffDim_add_eq_min [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : μ ≠ 0)
    (hν : ν ≠ 0) :
    lowerHausdorffDim (μ + ν) = min (lowerHausdorffDim μ) (lowerHausdorffDim ν) := by
  refine le_antisymm (le_min (lowerHausdorffDim_add_le_left hμ)
    (lowerHausdorffDim_add_le_right hν)) (le_of_forall_pos_le_add fun ε hε => ?_)
  have hne : μ + ν ≠ 0 := by
    intro h
    apply hμ
    rw [← Measure.measure_univ_eq_zero]
    have h' := congrArg (fun m : Measure E => m univ) h
    simp only [Measure.add_apply, Measure.coe_zero, Pi.zero_apply, add_eq_zero] at h'
    exact h'.1
  obtain ⟨C, -, hCpos, hCdim⟩ := exists_measurableSet_dimH_le hne
    ae_isBoundedUnder_le_log_div_log (lt_add_of_pos_right (lowerHausdorffDim (μ + ν)) hε)
  have hmin : ENNReal.ofReal (min (lowerHausdorffDim μ) (lowerHausdorffDim ν)) ≤ dimH C := by
    rw [Measure.add_apply, pos_iff_ne_zero, ne_eq, add_eq_zero, not_and_or] at hCpos
    rcases hCpos with h | h
    · exact (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans
        (ofReal_lowerHausdorffDim_le_dimH (pos_iff_ne_zero.2 h))
    · exact (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans
        (ofReal_lowerHausdorffDim_le_dimH (pos_iff_ne_zero.2 h))
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith [lowerHausdorffDim_nonneg (μ := μ + ν)])).1
    (hmin.trans hCdim)

end Sum

/-! ### Double-dimensional measures -/

section DoubleDim

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {μ : Measure X}

/-- Tex lines 2686 to 2688: the pointwise dimension of a nonzero measure exists almost
everywhere with two values if and only if it exists almost everywhere and `\overline{dim}_p(μ)`
and `\underline{dim}_H(μ)` are its only possible values. If both values `d₂ ≤ d₁` occur on sets
of positive measure, they are `\underline{dim}_H(μ)` and `\overline{dim}_p(μ)`; if one of them
occurs only on a null set, the measure is exact-dimensional with the other value, which is then
both dimensions. The double-dimensional measures of the article are characterised in
`isDoubleDim_iff_upperPackingDim_lowerHausdorffDim`.
Depends on: `HasLocalDimPair.upperPackingDim_eq`, `HasLocalDimPair.lowerHausdorffDim_eq`,
`IsExactDim.upperPackingDim_eq`, `IsExactDim.lowerHausdorffDim_eq`. -/
theorem hasLocalDimPair_iff_upperPackingDim_lowerHausdorffDim (hne : μ ≠ 0) :
    (∃ d₁ d₂, HasLocalDimPair μ d₁ d₂) ↔
      HasLocalDimPair μ (upperPackingDim μ) (lowerHausdorffDim μ) := by
  refine ⟨fun ⟨d₁, d₂, h⟩ => ?_, fun h => ⟨_, _, h⟩⟩
  -- A value occurring only on a null set can be discarded.
  have hex : ∀ {a b : ℝ}, HasLocalDimPair μ a b → μ {x | HasLocalDim μ x b} = 0 →
      IsExactDim μ a := fun {a b} hab h0 => by
    have h0' : ∀ᵐ x ∂μ, ¬HasLocalDim μ x b := by
      rw [ae_iff]
      simpa using h0
    filter_upwards [hab, h0'] with x hx hx'
    exact hx.resolve_right hx'
  have hexact : ∀ {a : ℝ}, IsExactDim μ a →
      HasLocalDimPair μ (upperPackingDim μ) (lowerHausdorffDim μ) := fun {a} ha => by
    rw [ha.upperPackingDim_eq hne, ha.lowerHausdorffDim_eq hne]
    exact ha.hasLocalDimPair
  wlog hle : d₂ ≤ d₁ generalizing d₁ d₂
  · exact this d₂ d₁ h.symm (le_of_not_ge hle)
  rcases eq_or_ne (μ {x | HasLocalDim μ x d₂}) 0 with h2 | h2
  · exact hexact (hex h h2)
  rcases eq_or_ne (μ {x | HasLocalDim μ x d₁}) 0 with h1 | h1
  · exact hexact (hex h.symm h1)
  rw [h.upperPackingDim_eq hle (pos_iff_ne_zero.2 h1),
    h.lowerHausdorffDim_eq hle (pos_iff_ne_zero.2 h2)]
  exact h

end DoubleDim

end BoxLike
