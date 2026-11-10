module

/-
Double-dimensional measures, `sec:ledrappier_young_formula`: the characterisation of
`IsDoubleDim` by the upper packing and the lower Hausdorff dimension (tex lines 2556 to 2560), and
the parts of `thm:exact-dimensional-mixture` that conclude `IsDoubleDim` or `IsExactDim` for the
sum of two exact-dimensional measures.

* `IsExactDim.eq_of_measure_hasLocalDim_pos`: a value of the pointwise dimension that occurs on
  a set of positive measure is the dimension of an exact-dimensional measure.
* `IsDoubleDim.not_isExactDim`, `IsDoubleDim.ne_zero`: a double-dimensional measure is nonzero
  and not exact-dimensional.
* `IsDoubleDim.exists_lt`: the two values of a double-dimensional measure, in increasing order.
* `HasLocalDimPair.isDoubleDim`: two distinct values, each on a set of positive measure.
* `HasLocalDimPair.measure_hasLocalDim_pos_of_lt`, `HasLocalDimPair.isDoubleDim_of_lt`: if the
  pointwise dimension takes the values `d₂ < d₁` almost everywhere with
  `\overline{dim}_p(μ) = d₁` and `\underline{dim}_H(μ) = d₂`, then both values occur on sets of
  positive measure and `μ` is double-dimensional.
* `IsDoubleDim.hasLocalDimPair_upperPackingDim_lowerHausdorffDim`,
  `isDoubleDim_iff_upperPackingDim_lowerHausdorffDim`: a nonzero measure is double-dimensional if
  and only if its pointwise dimension exists almost everywhere, takes only the values
  `\overline{dim}_p(μ)` and `\underline{dim}_H(μ)`, and
  `\underline{dim}_H(μ) < \overline{dim}_p(μ)`.
* `IsExactDim.isDoubleDim_add`, `IsExactDim.isExactDim_add`, `isDoubleDim_add_iff`,
  `IsExactDim.mixture`: `thm:exact-dimensional-mixture`, the sum of two nonzero exact-dimensional
  measures is double-dimensional if their dimensions differ and exact-dimensional otherwise.
-/
public import BoxLike.MeasureDimBounds

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Metric

section General

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {μ : Measure X} {d d' d₁ d₂ : ℝ}

/-- If `μ` is exact-dimensional with `dim μ = d` and the pointwise dimension takes the value
`d'` on a set of positive measure, then `d' = d`. -/
theorem IsExactDim.eq_of_measure_hasLocalDim_pos (h : IsExactDim μ d)
    (hpos : 0 < μ {x | HasLocalDim μ x d'}) : d' = d := by
  obtain ⟨x, hx, hx'⟩ := ((frequently_ae_iff.2 hpos.ne').and_eventually h).exists
  exact hx.unique hx'

/-- A double-dimensional measure (`sec:ledrappier_young_formula`) is not exact-dimensional:
both of its values would equal the dimension. -/
theorem IsDoubleDim.not_isExactDim (h : IsDoubleDim μ) : ¬ ∃ d, IsExactDim μ d := by
  rintro ⟨d, hd⟩
  obtain ⟨d₁, d₂, hne, -, h₁, h₂⟩ := h
  exact hne ((hd.eq_of_measure_hasLocalDim_pos h₁).trans
    (hd.eq_of_measure_hasLocalDim_pos h₂).symm)

/-- A double-dimensional measure is nonzero. -/
theorem IsDoubleDim.ne_zero (h : IsDoubleDim μ) : μ ≠ 0 := by
  rintro rfl
  obtain ⟨_, _, -, -, h₁, -⟩ := h
  simp at h₁

/-- The two values of a double-dimensional measure, listed in increasing order. -/
theorem IsDoubleDim.exists_lt (h : IsDoubleDim μ) :
    ∃ d₁ d₂ : ℝ, d₂ < d₁ ∧ HasLocalDimPair μ d₁ d₂ ∧
      0 < μ {x | HasLocalDim μ x d₁} ∧ 0 < μ {x | HasLocalDim μ x d₂} := by
  obtain ⟨d₁, d₂, hne, hp, h₁, h₂⟩ := h
  rcases hne.lt_or_gt with hlt | hlt
  · exact ⟨d₂, d₁, hlt, HasLocalDimPair.symm hp, h₂, h₁⟩
  · exact ⟨d₁, d₂, hlt, hp, h₁, h₂⟩

/-- The definition of a double-dimensional measure (`sec:ledrappier_young_formula`): the
pointwise dimension takes the values `d₁ ≠ d₂` almost everywhere, each on a set of positive
measure. -/
theorem HasLocalDimPair.isDoubleDim (h : HasLocalDimPair μ d₁ d₂) (hne : d₁ ≠ d₂)
    (h₁ : 0 < μ {x | HasLocalDim μ x d₁}) (h₂ : 0 < μ {x | HasLocalDim μ x d₂}) :
    IsDoubleDim μ :=
  ⟨d₁, d₂, hne, h, h₁, h₂⟩

/-- If the pointwise dimension of a nonzero measure takes the values `d₂ < d₁` almost everywhere,
with `\overline{dim}_p(μ) = d₁` and `\underline{dim}_H(μ) = d₂`, then each value occurs on a set
of positive measure: if one of the sets were null, the measure would be exact-dimensional with
the other value, and both dimensions would equal it (tex lines 2556 to 2560). -/
theorem HasLocalDimPair.measure_hasLocalDim_pos_of_lt (hne : μ ≠ 0) (h : HasLocalDimPair μ d₁ d₂)
    (hlt : d₂ < d₁) (hup : upperPackingDim μ = d₁) (hlow : lowerHausdorffDim μ = d₂) :
    0 < μ {x | HasLocalDim μ x d₁} ∧ 0 < μ {x | HasLocalDim μ x d₂} := by
  constructor
  · refine pos_iff_ne_zero.2 fun h0 => ?_
    have hae := measure_eq_zero_iff_ae_notMem.1 h0
    have hex : IsExactDim μ d₂ := (h.and hae).mono fun x hx => hx.1.resolve_left hx.2
    have := hex.upperPackingDim_eq hne
    linarith
  · refine pos_iff_ne_zero.2 fun h0 => ?_
    have hae := measure_eq_zero_iff_ae_notMem.1 h0
    have hex : IsExactDim μ d₁ := (h.and hae).mono fun x hx => hx.1.resolve_right hx.2
    have := hex.lowerHausdorffDim_eq hne
    linarith

/-- A nonzero measure whose pointwise dimension takes the values `d₂ < d₁` almost everywhere,
with `\overline{dim}_p(μ) = d₁` and `\underline{dim}_H(μ) = d₂`, is double-dimensional. -/
theorem HasLocalDimPair.isDoubleDim_of_lt (hne : μ ≠ 0) (h : HasLocalDimPair μ d₁ d₂)
    (hlt : d₂ < d₁) (hup : upperPackingDim μ = d₁) (hlow : lowerHausdorffDim μ = d₂) :
    IsDoubleDim μ :=
  let hpos := h.measure_hasLocalDim_pos_of_lt hne hlt hup hlow
  h.isDoubleDim hlt.ne' hpos.1 hpos.2

/-- The pointwise dimension of a double-dimensional measure exists almost everywhere and takes
only the values `\overline{dim}_p(μ)` and `\underline{dim}_H(μ)`, which satisfy
`\underline{dim}_H(μ) < \overline{dim}_p(μ)` (tex lines 2556 to 2560). -/
theorem IsDoubleDim.hasLocalDimPair_upperPackingDim_lowerHausdorffDim (h : IsDoubleDim μ) :
    HasLocalDimPair μ (upperPackingDim μ) (lowerHausdorffDim μ) ∧
      lowerHausdorffDim μ < upperPackingDim μ := by
  obtain ⟨d₁, d₂, hlt, hp, h₁, h₂⟩ := h.exists_lt
  rw [hp.upperPackingDim_eq hlt.le h₁, hp.lowerHausdorffDim_eq hlt.le h₂]
  exact ⟨hp, hlt⟩

/-- Tex lines 2556 to 2560: a nonzero measure is double-dimensional if and only if its pointwise
dimension exists almost everywhere, takes only the values `\overline{dim}_p(μ)` and
`\underline{dim}_H(μ)`, and `\underline{dim}_H(μ) < \overline{dim}_p(μ)`. -/
theorem isDoubleDim_iff_upperPackingDim_lowerHausdorffDim (hne : μ ≠ 0) :
    IsDoubleDim μ ↔
      HasLocalDimPair μ (upperPackingDim μ) (lowerHausdorffDim μ) ∧
        lowerHausdorffDim μ < upperPackingDim μ :=
  ⟨IsDoubleDim.hasLocalDimPair_upperPackingDim_lowerHausdorffDim,
    fun ⟨hp, hlt⟩ => hp.isDoubleDim_of_lt hne hlt rfl rfl⟩

end General

section Besicovitch

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [HasBesicovitchCovering X] {ν₁ ν₂ : Measure X} {d d₁ d₂ : ℝ}

/-- `thm:exact-dimensional-mixture`: the sum of two nonzero exact-dimensional measures of
different dimensions is double-dimensional. -/
theorem IsExactDim.isDoubleDim_add [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h₁ : IsExactDim ν₁ d₁) (h₂ : IsExactDim ν₂ d₂) (hne₁ : ν₁ ≠ 0) (hne₂ : ν₂ ≠ 0)
    (hd : d₁ ≠ d₂) : IsDoubleDim (ν₁ + ν₂) :=
  (h₁.hasLocalDimPair_add h₂).isDoubleDim hd (h₁.measure_hasLocalDim_add_left_pos hne₁)
    (h₂.measure_hasLocalDim_add_right_pos hne₂)

/-- `thm:exact-dimensional-mixture`: the sum of two exact-dimensional measures of the same
dimension `d` is exact-dimensional with `dim(ν₁ + ν₂) = d`. -/
theorem IsExactDim.isExactDim_add [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h₁ : IsExactDim ν₁ d) (h₂ : IsExactDim ν₂ d) : IsExactDim (ν₁ + ν₂) d :=
  hasLocalDimPair_self_iff.1 (h₁.hasLocalDimPair_add h₂)

/-- `thm:exact-dimensional-mixture`: the sum of two nonzero exact-dimensional measures is
double-dimensional if and only if `dim ν₁ ≠ dim ν₂`. -/
theorem isDoubleDim_add_iff [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h₁ : IsExactDim ν₁ d₁) (h₂ : IsExactDim ν₂ d₂) (hne₁ : ν₁ ≠ 0) (hne₂ : ν₂ ≠ 0) :
    IsDoubleDim (ν₁ + ν₂) ↔ d₁ ≠ d₂ :=
  ⟨fun h hd => h.not_isExactDim ((isExactDim_add_iff h₁ h₂ hne₁ hne₂).2 hd),
    fun hd => h₁.isDoubleDim_add h₂ hne₁ hne₂ hd⟩

/-- `thm:exact-dimensional-mixture` in full. Let `ν₁`, `ν₂` be nonzero finite exact-dimensional
measures and `ν = ν₁ + ν₂`. Then `dimloc(ν, x) = dim ν_k` for `ν_k`-almost every `x`, each value
`dim ν_k` occurs on a set of positive `ν`-measure, and `ν` is double-dimensional if
`dim ν₁ ≠ dim ν₂` and exact-dimensional otherwise. -/
theorem IsExactDim.mixture [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h₁ : IsExactDim ν₁ d₁) (h₂ : IsExactDim ν₂ d₂) (hne₁ : ν₁ ≠ 0) (hne₂ : ν₂ ≠ 0) :
    (∀ᵐ x ∂ν₁, HasLocalDim (ν₁ + ν₂) x d₁) ∧ (∀ᵐ x ∂ν₂, HasLocalDim (ν₁ + ν₂) x d₂) ∧
      0 < (ν₁ + ν₂) {x | HasLocalDim (ν₁ + ν₂) x d₁} ∧
      0 < (ν₁ + ν₂) {x | HasLocalDim (ν₁ + ν₂) x d₂} ∧
      (d₁ ≠ d₂ → IsDoubleDim (ν₁ + ν₂)) ∧ (d₁ = d₂ → IsExactDim (ν₁ + ν₂) d₁) :=
  ⟨h₁.ae_hasLocalDim_add_left, h₂.ae_hasLocalDim_add_right,
    h₁.measure_hasLocalDim_add_left_pos hne₁, h₂.measure_hasLocalDim_add_right_pos hne₂,
    h₁.isDoubleDim_add h₂ hne₁ hne₂, fun hd => h₁.isExactDim_add (hd ▸ h₂)⟩

end Besicovitch

section Examples

/-- Every theorem of this file holds on the real line. -/
example {ν₁ ν₂ : Measure ℝ} [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] {d₁ d₂ : ℝ}
    (h₁ : IsExactDim ν₁ d₁) (h₂ : IsExactDim ν₂ d₂) (hne₁ : ν₁ ≠ 0) (hne₂ : ν₂ ≠ 0)
    (hd : d₁ ≠ d₂) :
    IsDoubleDim (ν₁ + ν₂) ∧ (¬ ∃ d, IsExactDim (ν₁ + ν₂) d) ∧
      HasLocalDimPair (ν₁ + ν₂) (upperPackingDim (ν₁ + ν₂)) (lowerHausdorffDim (ν₁ + ν₂)) ∧
      lowerHausdorffDim (ν₁ + ν₂) < upperPackingDim (ν₁ + ν₂) :=
  let h := h₁.isDoubleDim_add h₂ hne₁ hne₂ hd
  ⟨h, h.not_isExactDim, h.hasLocalDimPair_upperPackingDim_lowerHausdorffDim.1,
    h.hasLocalDimPair_upperPackingDim_lowerHausdorffDim.2⟩

end Examples

end BoxLike
