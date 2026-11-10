module

/-
The pointwise dimension of a measure, exact-dimensional and double-dimensional measures, and
`thm:exact-dimensional-mixture` of `sec:ledrappier_young_formula`.

* `HasLocalDim`, `IsExactDim`, `HasLocalDimPair`, `IsDoubleDim`: `dimloc(μ, x) = d`,
  exact-dimensional measures with `dim μ = d`, measures whose pointwise dimension is `d₁` or
  `d₂` almost everywhere, and double-dimensional measures: two distinct values, each on a set
  of positive measure.
* `HasLocalDim.unique`, `IsExactDim.unique`: the pointwise dimension at a point and the
  dimension of a nonzero exact-dimensional measure are unique.
* `tendsto_log_div_log_sub`: if `ν'(B(x,r)) / ν(B(x,r))` has a limit in `(0, ∞)`, then
  `log ν'(B(x,r)) / log r - log ν(B(x,r)) / log r → 0`.
* `ae_hasLocalDim_iff_of_le`: if `ν' ≤ ν`, then `dimloc(ν', x) = dimloc(ν, x)` for `ν'`-almost
  every `x`, by the Besicovitch differentiation theorem.
* `IsExactDim.of_le`: the step `eq:restricted-projection-dimensions` of
  `sec:dimension_of_projections`.
* `IsExactDim.ae_hasLocalDim_add_left`, `IsExactDim.ae_hasLocalDim_add_right`,
  `IsExactDim.hasLocalDimPair_add`, `IsExactDim.measure_hasLocalDim_add_left_pos`,
  `IsExactDim.measure_hasLocalDim_add_right_pos`, `isExactDim_add_iff`:
  `thm:exact-dimensional-mixture`.
-/
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Metric
open scoped ENNReal

section Definitions

/-- The pointwise dimension of `μ` at `x` exists and equals `d`, that is `dimloc(μ, x) = d`:
the quotient `log μ(B(x, r)) / log r` tends to `d` as `r ↓ 0`. The balls are closed. At a point
`x` with `μ(B(x, r)) = 0` for small `r`, the convention `Real.log 0 = 0` gives
`dimloc(μ, x) = 0`; such points lie outside the support of `μ`. -/
def HasLocalDim {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (x : X) (d : ℝ) : Prop :=
  Tendsto (fun r : ℝ => Real.log (μ.real (closedBall x r)) / Real.log r) (𝓝[>] 0) (𝓝 d)

/-- The measure `μ` is exact-dimensional with `dim μ = d`: `dimloc(μ, x) = d` for `μ`-almost
every `x`. -/
def IsExactDim {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (d : ℝ) : Prop := ∀ᵐ x ∂μ, HasLocalDim μ x d

/-- For `μ`-almost every `x` the pointwise dimension `dimloc(μ, x)` exists and equals `d₁` or
`d₂`. The article has no name for this; its double-dimensional measures are those for which,
in addition, the two values differ and each occurs on a set of positive measure
(`IsDoubleDim`). -/
def HasLocalDimPair {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (d₁ d₂ : ℝ) : Prop := ∀ᵐ x ∂μ, HasLocalDim μ x d₁ ∨ HasLocalDim μ x d₂

/-- The measure `μ` is double-dimensional (`sec:ledrappier_young_formula`): its pointwise
dimension exists at `μ`-almost every point and takes exactly two values, each on a set of
positive `μ`-measure. -/
def IsDoubleDim {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] (μ : Measure X) : Prop :=
  ∃ d₁ d₂ : ℝ, d₁ ≠ d₂ ∧ (∀ᵐ x ∂μ, HasLocalDim μ x d₁ ∨ HasLocalDim μ x d₂) ∧
    0 < μ {x | HasLocalDim μ x d₁} ∧ 0 < μ {x | HasLocalDim μ x d₂}

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  {μ ν' ν : Measure X} {x : X} {d d' d₁ d₂ : ℝ}

/-- The pointwise dimension of a measure at a point is unique. -/
theorem HasLocalDim.unique (h : HasLocalDim μ x d) (h' : HasLocalDim μ x d') : d = d' :=
  tendsto_nhds_unique h h'

/-- The dimension of a nonzero exact-dimensional measure is unique. -/
theorem IsExactDim.unique (hne : μ ≠ 0) (h : IsExactDim μ d) (h' : IsExactDim μ d') :
    d = d' := by
  have : (ae μ).NeBot := ae_neBot.2 hne
  obtain ⟨x, hx, hx'⟩ := (h.and h').exists
  exact hx.unique hx'

/-- The pointwise dimension of an exact-dimensional measure is `dim μ` or `dim μ` almost
everywhere. -/
theorem IsExactDim.hasLocalDimPair (h : IsExactDim μ d) : HasLocalDimPair μ d d :=
  h.mono fun _ hx => Or.inl hx

/-- The pointwise dimension is `d` or `d` almost everywhere exactly when the measure is
exact-dimensional with `dim μ = d`. -/
theorem hasLocalDimPair_self_iff : HasLocalDimPair μ d d ↔ IsExactDim μ d := by
  simp only [HasLocalDimPair, IsExactDim, or_self]

/-- The two values of the pointwise dimension may be listed in either order. -/
theorem HasLocalDimPair.symm (h : HasLocalDimPair μ d₁ d₂) : HasLocalDimPair μ d₂ d₁ :=
  h.mono fun _ hx => hx.symm

/-- If the quotient `ν'(B(x, r)) / ν(B(x, r))` tends to a limit `c ∈ (0, ∞)` as `r ↓ 0`, then
`log ν'(B(x, r)) / log r - log ν(B(x, r)) / log r` tends to `0`. This is the last step in the
proof of `thm:exact-dimensional-mixture`. -/
theorem tendsto_log_div_log_sub {c : ℝ≥0∞} (hc : 0 < c) (hc' : c ≠ ∞)
    (h : Tendsto (fun r : ℝ => ν' (closedBall x r) / ν (closedBall x r)) (𝓝[>] 0) (𝓝 c)) :
    Tendsto (fun r : ℝ => Real.log (ν'.real (closedBall x r)) / Real.log r
      - Real.log (ν.real (closedBall x r)) / Real.log r) (𝓝[>] 0) (𝓝 0) := by
  have hc0 : 0 < c.toReal := ENNReal.toReal_pos hc.ne' hc'
  have hq : Tendsto (fun r : ℝ => ν'.real (closedBall x r) / ν.real (closedBall x r))
      (𝓝[>] 0) (𝓝 c.toReal) := by
    simpa only [Function.comp_def, ENNReal.toReal_div, Measure.real_def] using
      (ENNReal.tendsto_toReal hc').comp h
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < ν'.real (closedBall x r) / ν.real (closedBall x r) :=
    hq.eventually_const_lt hc0
  have hlog : Tendsto (fun r : ℝ => Real.log (ν'.real (closedBall x r))
      - Real.log (ν.real (closedBall x r))) (𝓝[>] 0) (𝓝 (Real.log c.toReal)) := by
    refine (hq.log hc0.ne').congr' ?_
    filter_upwards [hpos] with r hr
    have h' : ν'.real (closedBall x r) ≠ 0 := fun h0 => by simp [h0] at hr
    have h'' : ν.real (closedBall x r) ≠ 0 := fun h0 => by simp [h0] at hr
    exact Real.log_div h' h''
  have hdiv := hlog.div_atBot Real.tendsto_log_nhdsGT_zero
  simpa only [sub_div] using hdiv

end Definitions

section Besicovitch

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [HasBesicovitchCovering X]
  {ν' ν ν₁ ν₂ : Measure X} {d d₁ d₂ : ℝ}

/-- If `ν' ≤ ν`, then for `ν'`-almost every `x` the pointwise dimensions of `ν'` and `ν` at
`x` agree: one exists if and only if the other does, with the same value. The Besicovitch
differentiation theorem gives `ν'(B(x, r)) / ν(B(x, r)) → dν'/dν(x)` for `ν'`-almost every
`x`, and the Radon-Nikodym derivative is positive and finite `ν'`-almost everywhere. This is
the proof of `thm:exact-dimensional-mixture`. -/
theorem ae_hasLocalDim_iff_of_le [IsFiniteMeasure ν] (h : ν' ≤ ν) :
    ∀ᵐ x ∂ν', ∀ d : ℝ, HasLocalDim ν' x d ↔ HasLocalDim ν x d := by
  have : IsFiniteMeasure ν' := isFiniteMeasure_of_le ν h
  have hac : ν' ≪ ν := Measure.absolutelyContinuous_of_le h
  filter_upwards [hac.ae_le (Besicovitch.ae_tendsto_rnDeriv ν' ν), Measure.rnDeriv_pos hac,
    hac.ae_le (Measure.rnDeriv_ne_top ν' ν)] with x hx hpos htop d
  have h0 := tendsto_log_div_log_sub hpos htop hx
  unfold HasLocalDim
  constructor
  · intro hd
    simpa using hd.sub h0
  · intro hd
    simpa using hd.add h0

/-- If `ν' ≤ ν` and `ν` is exact-dimensional, then `ν'` is exact-dimensional with
`dim ν' = dim ν`. This is the step `eq:restricted-projection-dimensions`. -/
theorem IsExactDim.of_le [IsFiniteMeasure ν] (h : ν' ≤ ν) (hν : IsExactDim ν d) :
    IsExactDim ν' d := by
  filter_upwards [ae_hasLocalDim_iff_of_le h, ae_mono h hν] with x hx hd
  exact (hx d).2 hd

/-- First part of `thm:exact-dimensional-mixture`: if `ν₁` is exact-dimensional, then
`dimloc(ν₁ + ν₂, x) = dim ν₁` for `ν₁`-almost every `x`. -/
theorem IsExactDim.ae_hasLocalDim_add_left [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h₁ : IsExactDim ν₁ d₁) : ∀ᵐ x ∂ν₁, HasLocalDim (ν₁ + ν₂) x d₁ := by
  filter_upwards [ae_hasLocalDim_iff_of_le (Measure.le_add_right le_rfl : ν₁ ≤ ν₁ + ν₂), h₁]
    with x hx hd
  exact (hx d₁).1 hd

/-- First part of `thm:exact-dimensional-mixture`: if `ν₂` is exact-dimensional, then
`dimloc(ν₁ + ν₂, x) = dim ν₂` for `ν₂`-almost every `x`. -/
theorem IsExactDim.ae_hasLocalDim_add_right [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h₂ : IsExactDim ν₂ d₂) : ∀ᵐ x ∂ν₂, HasLocalDim (ν₁ + ν₂) x d₂ := by
  filter_upwards [ae_hasLocalDim_iff_of_le (Measure.le_add_left le_rfl : ν₂ ≤ ν₁ + ν₂), h₂]
    with x hx hd
  exact (hx d₂).1 hd

/-- Second part of `thm:exact-dimensional-mixture`: the pointwise dimension of the sum of two
exact-dimensional measures is `dim ν₁` or `dim ν₂` almost everywhere. The sum is
double-dimensional when the dimensions differ (`IsExactDim.isDoubleDim_add`). -/
theorem IsExactDim.hasLocalDimPair_add [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h₁ : IsExactDim ν₁ d₁) (h₂ : IsExactDim ν₂ d₂) : HasLocalDimPair (ν₁ + ν₂) d₁ d₂ :=
  ae_add_measure_iff.2 ⟨h₁.ae_hasLocalDim_add_left.mono fun _ hx => Or.inl hx,
    h₂.ae_hasLocalDim_add_right.mono fun _ hx => Or.inr hx⟩

/-- Third part of `thm:exact-dimensional-mixture`: if `ν₁` is nonzero and exact-dimensional,
then the value `dim ν₁` of the pointwise dimension of `ν₁ + ν₂` occurs on a set of positive
`ν₁ + ν₂`-measure. -/
theorem IsExactDim.measure_hasLocalDim_add_left_pos [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h₁ : IsExactDim ν₁ d₁) (hne : ν₁ ≠ 0) :
    0 < (ν₁ + ν₂) {x | HasLocalDim (ν₁ + ν₂) x d₁} := by
  have hpos : 0 < ν₁ {x | HasLocalDim (ν₁ + ν₂) x d₁} := by
    rw [pos_iff_ne_zero]
    intro h0
    have : (ae ν₁).NeBot := ae_neBot.2 hne
    obtain ⟨x, hx, hx'⟩ :=
      ((measure_eq_zero_iff_ae_notMem.1 h0).and (h₁.ae_hasLocalDim_add_left (ν₂ := ν₂))).exists
    exact hx hx'
  exact hpos.trans_le (Measure.le_add_right le_rfl _)

/-- Third part of `thm:exact-dimensional-mixture`: if `ν₂` is nonzero and exact-dimensional,
then the value `dim ν₂` of the pointwise dimension of `ν₁ + ν₂` occurs on a set of positive
`ν₁ + ν₂`-measure. -/
theorem IsExactDim.measure_hasLocalDim_add_right_pos [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h₂ : IsExactDim ν₂ d₂) (hne : ν₂ ≠ 0) :
    0 < (ν₁ + ν₂) {x | HasLocalDim (ν₁ + ν₂) x d₂} := by
  have hpos : 0 < ν₂ {x | HasLocalDim (ν₁ + ν₂) x d₂} := by
    rw [pos_iff_ne_zero]
    intro h0
    have : (ae ν₂).NeBot := ae_neBot.2 hne
    obtain ⟨x, hx, hx'⟩ :=
      ((measure_eq_zero_iff_ae_notMem.1 h0).and (h₂.ae_hasLocalDim_add_right (ν₁ := ν₁))).exists
    exact hx hx'
  exact hpos.trans_le (Measure.le_add_left le_rfl _)

/-- Last part of `thm:exact-dimensional-mixture`: the sum of two nonzero exact-dimensional
measures is exact-dimensional if and only if `dim ν₁ = dim ν₂`. -/
theorem isExactDim_add_iff [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h₁ : IsExactDim ν₁ d₁) (h₂ : IsExactDim ν₂ d₂) (hne₁ : ν₁ ≠ 0) (hne₂ : ν₂ ≠ 0) :
    (∃ d, IsExactDim (ν₁ + ν₂) d) ↔ d₁ = d₂ := by
  constructor
  · rintro ⟨d, hd⟩
    have hd' := ae_add_measure_iff.1 hd
    have : (ae ν₁).NeBot := ae_neBot.2 hne₁
    have : (ae ν₂).NeBot := ae_neBot.2 hne₂
    obtain ⟨x, hx, hx'⟩ := (hd'.1.and (h₁.ae_hasLocalDim_add_left (ν₂ := ν₂))).exists
    obtain ⟨y, hy, hy'⟩ := (hd'.2.and (h₂.ae_hasLocalDim_add_right (ν₁ := ν₁))).exists
    rw [← hx.unique hx', ← hy.unique hy']
  · rintro rfl
    exact ⟨d₁, hasLocalDimPair_self_iff.1 (h₁.hasLocalDimPair_add h₂)⟩

end Besicovitch

section Examples

/-- Every theorem of this file holds on a finite-dimensional real normed space with its Borel
σ-algebra, in particular on the plane. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν' ν ν₁ ν₂ : Measure E} [IsFiniteMeasure ν]
    [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] {d d₁ d₂ : ℝ} (h : ν' ≤ ν) (hν : IsExactDim ν d)
    (h₁ : IsExactDim ν₁ d₁) (h₂ : IsExactDim ν₂ d₂) (hne₁ : ν₁ ≠ 0) (hne₂ : ν₂ ≠ 0) :
    (∀ᵐ x ∂ν', ∀ d : ℝ, HasLocalDim ν' x d ↔ HasLocalDim ν x d) ∧ IsExactDim ν' d ∧
      (∀ᵐ x ∂ν₁, HasLocalDim (ν₁ + ν₂) x d₁) ∧ (∀ᵐ x ∂ν₂, HasLocalDim (ν₁ + ν₂) x d₂) ∧
      HasLocalDimPair (ν₁ + ν₂) d₁ d₂ ∧ 0 < (ν₁ + ν₂) {x | HasLocalDim (ν₁ + ν₂) x d₁} ∧
      0 < (ν₁ + ν₂) {x | HasLocalDim (ν₁ + ν₂) x d₂} ∧
      ((∃ d, IsExactDim (ν₁ + ν₂) d) ↔ d₁ = d₂) :=
  ⟨ae_hasLocalDim_iff_of_le h, hν.of_le h, h₁.ae_hasLocalDim_add_left,
    h₂.ae_hasLocalDim_add_right, h₁.hasLocalDimPair_add h₂,
    h₁.measure_hasLocalDim_add_left_pos hne₁, h₂.measure_hasLocalDim_add_right_pos hne₂,
    isExactDim_add_iff h₁ h₂ hne₁ hne₂⟩

/-- Every theorem of this file holds on the real line. -/
example {ν' ν ν₁ ν₂ : Measure ℝ} [IsFiniteMeasure ν] [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    {d d₁ d₂ : ℝ} (h : ν' ≤ ν) (hν : IsExactDim ν d) (h₁ : IsExactDim ν₁ d₁)
    (h₂ : IsExactDim ν₂ d₂) (hne₁ : ν₁ ≠ 0) (hne₂ : ν₂ ≠ 0) :
    (∀ᵐ x ∂ν', ∀ d : ℝ, HasLocalDim ν' x d ↔ HasLocalDim ν x d) ∧ IsExactDim ν' d ∧
      (∀ᵐ x ∂ν₁, HasLocalDim (ν₁ + ν₂) x d₁) ∧ (∀ᵐ x ∂ν₂, HasLocalDim (ν₁ + ν₂) x d₂) ∧
      HasLocalDimPair (ν₁ + ν₂) d₁ d₂ ∧ 0 < (ν₁ + ν₂) {x | HasLocalDim (ν₁ + ν₂) x d₁} ∧
      0 < (ν₁ + ν₂) {x | HasLocalDim (ν₁ + ν₂) x d₂} ∧
      ((∃ d, IsExactDim (ν₁ + ν₂) d) ↔ d₁ = d₂) :=
  ⟨ae_hasLocalDim_iff_of_le h, hν.of_le h, h₁.ae_hasLocalDim_add_left,
    h₂.ae_hasLocalDim_add_right, h₁.hasLocalDimPair_add h₂,
    h₁.measure_hasLocalDim_add_left_pos hne₁, h₂.measure_hasLocalDim_add_right_pos hne₂,
    isExactDim_add_iff h₁ h₂ hne₁ hne₂⟩

end Examples

end BoxLike
