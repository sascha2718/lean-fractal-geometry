module

/-
Bounds for the pointwise dimensions of a finite Borel measure on `ℝ^d` and the Hausdorff half of
`eq:dimension_measure_def`, from `sec:ledrappier_young_formula`.

* `log_div_log_nonneg`, `isBoundedUnder_ge_log_div_log`, `ae_zero_le_lowerLocalDim`: the lower
  bound `0` for the pointwise dimensions of a finite measure.
* `ae_forall_measure_closedBall_pos`: almost every point lies in the support of the measure.
* `ae_exists_mul_pow_le_measure_closedBall`, `ae_exists_mul_pow_le_measureReal_closedBall`: for
  a Borel measure `μ` on a finite-dimensional real normed space `E` and `μ`-almost every `x`
  there is `c > 0` with `μ(B(x, r)) ≥ c r^d` for all small `r`, where `d = dim E`. This is the
  differentiation of a Haar measure with respect to `μ`.
* `ae_isBoundedUnder_le_log_div_log`, `ae_upperLocalDim_le`, `ae_lowerLocalDim_le`,
  `ae_upperLocalDim_le_one`, `ae_upperLocalDim_le_two`: the pointwise dimensions are at most `d`
  almost everywhere, with `d = 1` on `ℝ` and `d = 2` on `ℝ × ℝ`.
* `upperPackingDim_le`, `lowerHausdorffDim_le`, `upperPackingDim_add_of_finiteDimensional`: the
  dimensions of `μ` are at most `d`, and the first line of `eq:haus_dim_sum` holds for all finite
  Borel measures on `E`.
* `mem_Icc_of_measure_hasLocalDim_pos`, `IsExactDim.dim_mem_Icc`, `HasLocalDimPair.dim_mem_Icc`,
  `IsExactDim.dim_mem_Icc_one`, `IsExactDim.dim_mem_Icc_two`: the dimension of a nonzero
  exact-dimensional measure lies in `[0, d]`.
* `isExactDim_iff_upperPackingDim_eq_lowerHausdorffDim`: `μ` is exact-dimensional if and only if
  `\overline{dim}_p(μ) = \underline{dim}_H(μ) = dim μ`.
* `le_dimH_of_ae_le_lowerLocalDim`, `ofReal_lowerHausdorffDim_le_dimH`: the mass distribution
  principle, `\underline{dim}_H(μ) ≤ dim_H A` for every set `A` with `μ(A) > 0`.
* `heavyBallSet`, `measurableSet_heavyBallSet`, `hausdorffMeasure_heavyBallSet_le`,
  `dimH_heavyBallSet_le`, `mem_heavyBallSet_of_lowerLocalDim_lt`: the `G_δ` set of the points
  where `μ(U(x, r)) > r^t` for arbitrarily small `r` has Hausdorff dimension at most `t`, by the
  Vitali covering lemma.
* `exists_measurableSet_dimH_le`, `ofReal_lowerHausdorffDim_eq_iInf_dimH`,
  `ofReal_lowerHausdorffDim_eq_iInf_dimH_of_pos`,
  `ofReal_lowerHausdorffDim_eq_iInf_dimH_of_finiteDimensional`,
  `lowerHausdorffDim_eq_toReal_iInf_dimH`: the second line of `eq:dimension_measure_def`.
-/
public import BoxLike.MeasureDimBounds
public import BoxLike.MassDistribution
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

namespace BoxLike

open MeasureTheory Measure Filter Topology Metric Set Module Function
open scoped ENNReal

section Pointwise

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {μ : Measure X} {x : X}
  {r s t c : ℝ}

/-- At a radius `r ∈ (0, 1)` with `μ(B(x, r)) ≤ 1` the quotient `log μ(B(x, r)) / log r` of
`sec:ledrappier_young_formula` is non-negative. The case `μ(B(x, r)) = 0` is included, where
`Real.log 0 = 0` makes the quotient `0`. -/
theorem log_div_log_nonneg (hr : 0 < r) (hr1 : r < 1) (h : μ.real (closedBall x r) ≤ 1) :
    0 ≤ Real.log (μ.real (closedBall x r)) / Real.log r :=
  div_nonneg_of_nonpos (Real.log_nonpos measureReal_nonneg h) (Real.log_neg hr hr1).le

/-- For a finite measure the quotient `log μ(B(x, r)) / log r` is bounded below as `r ↓ 0`, at
every point `x`. The `liminf` that defines `lowerLocalDim` is therefore a supremum over a
non-empty set. -/
theorem isBoundedUnder_ge_log_div_log [IsFiniteMeasure μ] (x : X) :
    (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≥ ·)
      fun r : ℝ => Real.log (μ.real (closedBall x r)) / Real.log r :=
  isBoundedUnder_of_eventually_ge (eventually_neg_le_log_div_log x one_pos)

/-- The lower pointwise dimension of a finite measure is non-negative almost everywhere; see
lines 2649 to 2655 of the article. The bound holds at every point, by `lowerLocalDim_nonneg`. -/
theorem ae_zero_le_lowerLocalDim [IsFiniteMeasure μ] : ∀ᵐ x ∂μ, 0 ≤ lowerLocalDim μ x :=
  Eventually.of_forall lowerLocalDim_nonneg

/-- If `μ(B(x, r)) ≥ c r^s` for all small `r`, with `c > 0`, then for every `ε > 0` the quotient
`log μ(B(x, r)) / log r` is at most `s + ε` for all small `r`. -/
theorem eventually_log_div_log_le (hc : 0 < c)
    (h : ∀ᶠ r : ℝ in 𝓝[>] 0, c * r ^ s ≤ μ.real (closedBall x r)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, Real.log (μ.real (closedBall x r)) / Real.log r ≤ s + ε := by
  have hL : Tendsto (fun r : ℝ => Real.log c / Real.log r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.div_atBot Real.tendsto_log_nhdsGT_zero
  have h1 : ∀ᶠ r : ℝ in 𝓝[>] 0, Real.log c / Real.log r < ε := hL.eventually_lt_const hε
  have h2 : ∀ᶠ r : ℝ in 𝓝[>] 0, Real.log r < 0 :=
    Real.tendsto_log_nhdsGT_zero.eventually_lt_atBot 0
  filter_upwards [h, h1, h2, self_mem_nhdsWithin] with r hr hr1 hr2 hr0
  have hr0 : 0 < r := hr0
  have hpos : 0 < c * r ^ s := mul_pos hc (Real.rpow_pos_of_pos hr0 s)
  have hlog : Real.log c + s * Real.log r ≤ Real.log (μ.real (closedBall x r)) := by
    rw [← Real.log_rpow hr0, ← Real.log_mul hc.ne' (Real.rpow_pos_of_pos hr0 s).ne']
    exact Real.log_le_log hpos hr
  calc Real.log (μ.real (closedBall x r)) / Real.log r
      ≤ (Real.log c + s * Real.log r) / Real.log r := div_le_div_of_nonpos_of_le hr2.le hlog
    _ = s + Real.log c / Real.log r := by
      rw [add_div, mul_div_assoc, div_self hr2.ne, mul_one, add_comm]
    _ ≤ s + ε := by linarith

/-- If `t` is smaller than the lower pointwise dimension of a finite measure `μ` at `x`, then
`μ(B(x, r)) ≤ r^t` for all small `r > 0`. -/
theorem eventually_measure_closedBall_le_of_lt_lowerLocalDim [IsFiniteMeasure μ]
    (ht : t < lowerLocalDim μ x) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, μ (closedBall x r) ≤ ENNReal.ofReal (r ^ t) := by
  have hlt : ∀ᶠ r : ℝ in 𝓝[>] 0, t < Real.log (μ.real (closedBall x r)) / Real.log r :=
    eventually_lt_of_lt_liminf ht (isBoundedUnder_ge_log_div_log x)
  have hone : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 := nhdsWithin_le_nhds (eventually_lt_nhds one_pos)
  filter_upwards [hlt, hone, self_mem_nhdsWithin] with r hr hr1 hr0
  have hr0 : 0 < r := hr0
  rw [lt_div_iff_of_neg (Real.log_neg hr0 hr1)] at hr
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases (measureReal_nonneg (μ := μ) (s := closedBall x r)).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact Real.rpow_nonneg hr0.le t
  · rw [← Real.log_le_log_iff hpos (Real.rpow_pos_of_pos hr0 t), Real.log_rpow hr0]
    exact hr.le

/-- In a second-countable space, almost every point `x` of a measure `μ` has `μ(B(x, r)) > 0`
for every `r > 0`: the complement of the support of `μ` is a null set. At the other points the
convention `Real.log 0 = 0` gives the pointwise dimension `0`, where the article has `∞`. -/
theorem ae_forall_measure_closedBall_pos [SecondCountableTopology X] (μ : Measure X) :
    ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < μ (closedBall x r) := by
  rw [ae_iff]
  refine measure_null_of_locally_null _ fun x hx => ?_
  simp only [mem_ofPred_eq, not_forall, not_lt, nonpos_iff_eq_zero] at hx
  obtain ⟨r, hr, h0⟩ := hx
  exact ⟨closedBall x r, mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x hr), h0⟩

end Pointwise

section UpperBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ ν₁ ν₂ : Measure E} {d d₁ d₂ : ℝ}

/-- For a locally finite Borel measure `μ` on a finite-dimensional real normed space `E` of
dimension `d` and `μ`-almost every `x`, there is a constant `c ∈ (0, ∞)` with
`μ(B(x, r)) ≥ c r^d` for all small `r`. The Besicovitch differentiation theorem, applied to a
Haar measure `vol` and `μ`, gives `vol(B(x, r)) / μ(B(x, r)) → d vol / dμ (x)` for `μ`-almost
every `x`, the limit is finite `μ`-almost everywhere, and `vol(B(x, r))` is a multiple of
`r^d`. -/
theorem ae_exists_mul_pow_le_measure_closedBall [IsLocallyFiniteMeasure μ] :
    ∀ᵐ x ∂μ, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
      c * ENNReal.ofReal (r ^ finrank ℝ E) ≤ μ (closedBall x r) := by
  let vol : Measure E := addHaar
  have hv0 : vol (ball (0 : E) 1) ≠ 0 := (measure_ball_pos vol 0 one_pos).ne'
  have hvtop : vol (ball (0 : E) 1) ≠ ∞ := measure_ball_lt_top.ne
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv vol μ, rnDeriv_lt_top vol μ] with x hx hlt
  have hC0 : vol.rnDeriv μ x + 1 ≠ 0 := by simp
  have hCtop : vol.rnDeriv μ x + 1 ≠ ∞ := by simp [hlt.ne]
  refine ⟨vol (ball (0 : E) 1) / (vol.rnDeriv μ x + 1), ENNReal.div_ne_zero.2 ⟨hv0, hCtop⟩,
    ENNReal.div_ne_top hvtop hC0, ?_⟩
  have hev := hx.eventually_lt_const (ENNReal.lt_add_right hlt.ne one_ne_zero)
  filter_upwards [hev, self_mem_nhdsWithin] with r hr hr0
  have hr0 : 0 < r := hr0
  have h1 : vol (closedBall x r) ≤ (vol.rnDeriv μ x + 1) * μ (closedBall x r) :=
    (ENNReal.div_le_iff_le_mul (Or.inr hCtop) (Or.inr hC0)).1 hr.le
  rw [addHaar_closedBall vol x hr0.le] at h1
  calc vol (ball (0 : E) 1) / (vol.rnDeriv μ x + 1) * ENNReal.ofReal (r ^ finrank ℝ E)
      = ENNReal.ofReal (r ^ finrank ℝ E) * vol (ball (0 : E) 1) / (vol.rnDeriv μ x + 1) := by
        rw [mul_comm, mul_div_assoc]
    _ ≤ μ (closedBall x r) := ENNReal.div_le_of_le_mul' h1

/-- For a finite Borel measure `μ` on a finite-dimensional real normed space `E` of dimension
`d` and `μ`-almost every `x`, there is `c > 0` with `μ(B(x, r)) ≥ c r^d` for all small `r`. In
particular `μ(B(x, r)) > 0` for all small `r`, so the convention `Real.log 0 = 0` plays no role
at such a point. -/
theorem ae_exists_mul_pow_le_measureReal_closedBall [IsFiniteMeasure μ] :
    ∀ᵐ x ∂μ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
      c * r ^ (finrank ℝ E : ℝ) ≤ μ.real (closedBall x r) := by
  filter_upwards [ae_exists_mul_pow_le_measure_closedBall (μ := μ)] with x ⟨c, hc0, hctop, hc⟩
  refine ⟨c.toReal, ENNReal.toReal_pos hc0 hctop, ?_⟩
  filter_upwards [hc, self_mem_nhdsWithin] with r hr hr0
  have hr0 : 0 < r := hr0
  have h := ENNReal.toReal_mono (measure_ne_top μ _) hr
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr0.le _), ← Real.rpow_natCast]
    at h

/-- For a finite Borel measure on a finite-dimensional real normed space and almost every `x`,
the quotient `log μ(B(x, r)) / log r` is bounded above as `r ↓ 0`. The `limsup` that defines
`upperLocalDim` is therefore an infimum over a non-empty set, and with
`isBoundedUnder_ge_log_div_log` both pointwise dimensions carry their usual meaning. -/
theorem ae_isBoundedUnder_le_log_div_log [IsFiniteMeasure μ] :
    ∀ᵐ x ∂μ, (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≤ ·)
      fun r : ℝ => Real.log (μ.real (closedBall x r)) / Real.log r := by
  filter_upwards [ae_exists_mul_pow_le_measureReal_closedBall (μ := μ)] with x ⟨c, hc, h⟩
  exact isBoundedUnder_of_eventually_le (eventually_log_div_log_le hc h one_pos)

/-- The upper pointwise dimension of a finite Borel measure on a finite-dimensional real normed
space `E` is at most `dim E` almost everywhere; see lines 2649 to 2655 of the article. -/
theorem ae_upperLocalDim_le [IsFiniteMeasure μ] :
    ∀ᵐ x ∂μ, upperLocalDim μ x ≤ finrank ℝ E := by
  filter_upwards [ae_exists_mul_pow_le_measureReal_closedBall (μ := μ)] with x ⟨c, hc, h⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  exact limsup_le_of_le (isBoundedUnder_ge_log_div_log x).isCoboundedUnder_le
    (eventually_log_div_log_le hc h hε)

/-- The lower pointwise dimension of a finite Borel measure on a finite-dimensional real normed
space is at most the upper pointwise dimension almost everywhere. -/
theorem ae_lowerLocalDim_le_upperLocalDim [IsFiniteMeasure μ] :
    ∀ᵐ x ∂μ, lowerLocalDim μ x ≤ upperLocalDim μ x := by
  filter_upwards [ae_isBoundedUnder_le_log_div_log (μ := μ)] with x hx
  exact liminf_le_limsup hx (isBoundedUnder_ge_log_div_log x)

/-- The lower pointwise dimension of a finite Borel measure on a finite-dimensional real normed
space `E` is at most `dim E` almost everywhere. -/
theorem ae_lowerLocalDim_le [IsFiniteMeasure μ] :
    ∀ᵐ x ∂μ, lowerLocalDim μ x ≤ finrank ℝ E := by
  filter_upwards [ae_lowerLocalDim_le_upperLocalDim (μ := μ), ae_upperLocalDim_le (μ := μ)]
    with x h₁ h₂ using h₁.trans h₂

/-- The upper pointwise dimension of a finite Borel measure on a finite-dimensional real normed
space is essentially bounded above. This is the hypothesis of `upperPackingDim_add`. -/
theorem isBoundedUnder_upperLocalDim [IsFiniteMeasure μ] :
    (ae μ).IsBoundedUnder (· ≤ ·) (upperLocalDim μ) :=
  isBoundedUnder_of_eventually_le ae_upperLocalDim_le

/-- The upper packing dimension of a finite Borel measure on a finite-dimensional real normed
space `E` is at most `dim E`. -/
theorem upperPackingDim_le [IsFiniteMeasure μ] : upperPackingDim μ ≤ finrank ℝ E := by
  rcases eq_or_ne μ 0 with rfl | hne
  · rw [upperPackingDim_zero]
    exact Nat.cast_nonneg _
  · have : (ae μ).NeBot := ae_neBot.2 hne
    exact limsup_le_of_le (isBoundedUnder_of_eventually_ge
      (Eventually.of_forall upperLocalDim_nonneg)).isCoboundedUnder_le ae_upperLocalDim_le

/-- The lower Hausdorff dimension of a nonzero finite Borel measure on a finite-dimensional real
normed space `E` is at most `dim E`. -/
theorem lowerHausdorffDim_le [IsFiniteMeasure μ] (hne : μ ≠ 0) :
    lowerHausdorffDim μ ≤ finrank ℝ E := by
  have : (ae μ).NeBot := ae_neBot.2 hne
  exact liminf_le_of_frequently_le ae_lowerLocalDim_le.frequently
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall lowerLocalDim_nonneg))

/-- The first line of `eq:haus_dim_sum` for all finite Borel measures on a finite-dimensional
real normed space: `\overline{dim}_p(ν₁ + ν₂) = max {\overline{dim}_p(ν₁), \overline{dim}_p(ν₂)}`.
The boundedness hypotheses of `upperPackingDim_add` hold by `ae_upperLocalDim_le`. -/
theorem upperPackingDim_add_of_finiteDimensional [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] :
    upperPackingDim (ν₁ + ν₂) = max (upperPackingDim ν₁) (upperPackingDim ν₂) :=
  upperPackingDim_add isBoundedUnder_upperLocalDim isBoundedUnder_upperLocalDim

/-- If the pointwise dimension of a finite Borel measure on a finite-dimensional real normed
space `E` equals `d` on a set of positive measure, then `0 ≤ d ≤ dim E`. -/
theorem mem_Icc_of_measure_hasLocalDim_pos [IsFiniteMeasure μ]
    (h : 0 < μ {x | HasLocalDim μ x d}) : d ∈ Icc (0 : ℝ) (finrank ℝ E) := by
  obtain ⟨x, hx, hx'⟩ :=
    ((frequently_ae_mem_iff.2 h.ne').and_eventually (ae_upperLocalDim_le (μ := μ))).exists
  have hx : HasLocalDim μ x d := hx
  rw [hx.upperLocalDim_eq] at hx'
  exact ⟨hx.upperLocalDim_eq ▸ upperLocalDim_nonneg x, hx'⟩

/-- The dimension of a nonzero finite exact-dimensional Borel measure on a finite-dimensional
real normed space `E` lies in `[0, dim E]`. -/
theorem IsExactDim.dim_mem_Icc [IsFiniteMeasure μ] (h : IsExactDim μ d) (hne : μ ≠ 0) :
    d ∈ Icc (0 : ℝ) (finrank ℝ E) :=
  mem_Icc_of_measure_hasLocalDim_pos (h.measure_hasLocalDim_pos hne)

/-- If the pointwise dimension of a nonzero finite Borel measure on a finite-dimensional real
normed space `E` is `d₁` or `d₂` almost everywhere, then one of the two values lies in
`[0, dim E]`. A value that occurs on a set of positive measure lies in `[0, dim E]` by
`mem_Icc_of_measure_hasLocalDim_pos`; a value that occurs on a null set is not constrained by
the definition. -/
theorem HasLocalDimPair.dim_mem_Icc [IsFiniteMeasure μ] (h : HasLocalDimPair μ d₁ d₂)
    (hne : μ ≠ 0) :
    d₁ ∈ Icc (0 : ℝ) (finrank ℝ E) ∨ d₂ ∈ Icc (0 : ℝ) (finrank ℝ E) := by
  have : (ae μ).NeBot := ae_neBot.2 hne
  obtain ⟨x, hx, hx'⟩ := (h.and (ae_upperLocalDim_le (μ := μ))).exists
  rcases hx with hx | hx
  · exact Or.inl ⟨hx.upperLocalDim_eq ▸ upperLocalDim_nonneg x, hx.upperLocalDim_eq ▸ hx'⟩
  · exact Or.inr ⟨hx.upperLocalDim_eq ▸ upperLocalDim_nonneg x, hx.upperLocalDim_eq ▸ hx'⟩

/-- A nonzero finite Borel measure `μ` on a finite-dimensional real normed space is
exact-dimensional with `dim μ = d` if and only if
`\overline{dim}_p(μ) = \underline{dim}_H(μ) = d`; see lines 2686 to 2687 of the article. -/
theorem isExactDim_iff_upperPackingDim_eq_lowerHausdorffDim [IsFiniteMeasure μ] (hne : μ ≠ 0) :
    IsExactDim μ d ↔ upperPackingDim μ = d ∧ lowerHausdorffDim μ = d := by
  refine ⟨fun h => ⟨h.upperPackingDim_eq hne, h.lowerHausdorffDim_eq hne⟩, fun ⟨hp, hh⟩ => ?_⟩
  have h₁ : ∀ᵐ x ∂μ, upperLocalDim μ x ≤ d := hp ▸ ae_le_essSup isBoundedUnder_upperLocalDim
  have h₂ : ∀ᵐ x ∂μ, d ≤ lowerLocalDim μ x := hh ▸ ae_essInf_le
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall lowerLocalDim_nonneg))
  filter_upwards [h₁, h₂, ae_isBoundedUnder_le_log_div_log (μ := μ)] with x hx₁ hx₂ hb
  exact tendsto_of_le_liminf_of_limsup_le hx₂ hx₁ hb (isBoundedUnder_ge_log_div_log x)

end UpperBound

section MassDistribution

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
  {x : X} {t : ℝ}

/-- The mass distribution principle for the lower pointwise dimension: if `μ` is a finite measure,
`μ(A) > 0` and `\underline{dim}_loc(μ, x) ≥ t` for `μ`-almost every `x ∈ A`, then
`dim_H A ≥ t`. The set `A` is arbitrary and `μ(A)` is its outer measure. The proof is that of
`IsExactDim.le_dimH`. -/
theorem le_dimH_of_ae_le_lowerLocalDim [IsFiniteMeasure μ] {A : Set X} (hA : 0 < μ A)
    (h : ∀ᵐ x ∂μ, x ∈ A → t ≤ lowerLocalDim μ x) : ENNReal.ofReal t ≤ dimH A := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
  have hctop : c ≠ ∞ := ne_top_of_lt hc
  have ht : c.toReal < t := (ENNReal.lt_ofReal_iff_toReal_lt hctop).1 hc
  have ht0 : 0 ≤ c.toReal := ENNReal.toReal_nonneg
  let G : ℕ → Set X := fun n => {x | ∀ r : ℝ, 0 < r → r < 1 / ((n : ℝ) + 1) →
    μ (closedBall x r) ≤ ENNReal.ofReal (r ^ c.toReal)}
  have hsub : A ∩ {x | x ∈ A → t ≤ lowerLocalDim μ x} ⊆ ⋃ n, A ∩ G n := by
    rintro x ⟨hxA, hx⟩
    obtain ⟨u, hu, hIoo⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
      (eventually_measure_closedBall_le_of_lt_lowerLocalDim (ht.trans_le (hx hxA)))
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < u from hu)
    exact mem_iUnion.2 ⟨n, hxA, fun r hr0 hr => hIoo ⟨hr0, hr.trans hn⟩⟩
  have hpos : 0 < μ (⋃ n, A ∩ G n) := by
    have hfull : μ (A ∩ {x | x ∈ A → t ≤ lowerLocalDim μ x}) = μ A :=
      measure_inter_conull (ae_iff.1 h)
    exact (hfull ▸ hA).trans_le (measure_mono hsub)
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hpos.ne'
  have hH : μH[c.toReal] (A ∩ G n) ≠ 0 :=
    (hn.trans_le (measure_le_hausdorffMeasure_of_closedBall_le ht0 Nat.one_div_pos_of_nat
      fun x hx => hx.2)).ne'
  calc c = ((c.toReal.toNNReal : NNReal) : ℝ≥0∞) := (ENNReal.ofReal_toReal hctop).symm
    _ ≤ dimH (A ∩ G n) :=
      le_dimH_of_hausdorffMeasure_ne_zero (by rwa [Real.coe_toNNReal _ ht0])
    _ ≤ dimH A := dimH_mono inter_subset_left

/-- The inequality `≤` in the second line of `eq:dimension_measure_def`: if `μ` is a finite
measure and `μ(A) > 0`, then `\underline{dim}_H(μ) ≤ dim_H A`. The set `A` is arbitrary and
`μ(A)` is its outer measure. -/
theorem ofReal_lowerHausdorffDim_le_dimH [IsFiniteMeasure μ] {A : Set X} (hA : 0 < μ A) :
    ENNReal.ofReal (lowerHausdorffDim μ) ≤ dimH A := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
  have hctop : c ≠ ∞ := ne_top_of_lt hc
  have ht : c.toReal < lowerHausdorffDim μ := (ENNReal.lt_ofReal_iff_toReal_lt hctop).1 hc
  have hae : ∀ᵐ x ∂μ, c.toReal < lowerLocalDim μ x :=
    eventually_lt_of_lt_liminf ht
      (isBoundedUnder_of_eventually_ge (Eventually.of_forall lowerLocalDim_nonneg))
  calc c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hctop).symm
    _ ≤ dimH A := le_dimH_of_ae_le_lowerLocalDim hA (hae.mono fun x hx _ => hx.le)

end MassDistribution

section Covering

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
  {x : X} {t : ℝ}

/-- The set of the points `x` such that `μ(U(x, r)) > r^t` for arbitrarily small radii `r`,
where `U(x, r)` is the open ball. It is a `G_δ` set, it has Hausdorff dimension at most `t`, and
it contains the points of the support of `μ` at which the lower pointwise dimension is smaller
than `t`. It provides the Borel sets of small dimension in the second line of
`eq:dimension_measure_def`. -/
def heavyBallSet (μ : Measure X) (t : ℝ) : Set X :=
  ⋂ n : ℕ, ⋃ r ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)), {x | ENNReal.ofReal (r ^ t) < μ (ball x r)}

omit [BorelSpace X] in
/-- The function `x ↦ μ(U(x, r))` is lower semicontinuous, for the open ball `U(x, r)`: its
strict superlevel sets are open. -/
theorem isOpen_setOf_lt_measure_ball (μ : Measure X) (c : ℝ≥0∞) (r : ℝ) :
    IsOpen {x | c < μ (ball x r)} := by
  refine Metric.isOpen_iff.2 fun x hx => ?_
  have hmono : Monotone fun n : ℕ => ball x (r - 1 / ((n : ℝ) + 1)) := by
    intro m n hmn
    refine ball_subset_ball ?_
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmn
    have := one_div_le_one_div_of_le (by positivity) hmn'
    linarith
  have hU : ball x r = ⋃ n : ℕ, ball x (r - 1 / ((n : ℝ) + 1)) := by
    refine Subset.antisymm (fun y hy => ?_) (iUnion_subset fun n => ball_subset_ball ?_)
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (mem_ball.1 hy))
      exact mem_iUnion.2 ⟨n, mem_ball.2 (by linarith)⟩
    · have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
      linarith
  have hx' : c < μ (ball x r) := hx
  rw [hU, hmono.measure_iUnion, lt_iSup_iff] at hx'
  obtain ⟨n, hn⟩ := hx'
  refine ⟨1 / ((n : ℝ) + 1), Nat.one_div_pos_of_nat, fun y hy => ?_⟩
  have hy' : dist y x < 1 / ((n : ℝ) + 1) := mem_ball.1 hy
  refine hn.trans_le (measure_mono (ball_subset_ball' ?_))
  rw [dist_comm]
  linarith

/-- The set `heavyBallSet μ t` is a Borel set: it is a countable intersection of open sets. -/
theorem measurableSet_heavyBallSet (μ : Measure X) (t : ℝ) : MeasurableSet (heavyBallSet μ t) :=
  MeasurableSet.iInter fun _ =>
    (isOpen_biUnion fun r _ => isOpen_setOf_lt_measure_ball μ _ r).measurableSet

/-- The covering step for `heavyBallSet μ t`. For every `δ > 0` the Vitali covering lemma gives
a countable family of pairs `(y, ρ)` with `0 < ρ < δ` such that the closed balls `B(y, ρ)` are
disjoint with `μ(B(y, ρ)) > ρ^t`, and the balls `B(y, 4ρ)` cover the set. The family is countable
since `μ` is finite, and `∑ ρ^t ≤ μ(X)`. -/
theorem exists_countable_cover_heavyBallSet [IsFiniteMeasure μ] (t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : Set (X × ℝ), u.Countable ∧ (∀ p ∈ u, 0 < p.2 ∧ p.2 < δ) ∧
      heavyBallSet μ t ⊆ ⋃ p ∈ u, closedBall p.1 (4 * p.2) ∧
      ∑' p : u, ENNReal.ofReal ((p : X × ℝ).2 ^ t) ≤ μ univ := by
  let T : Set (X × ℝ) :=
    {p | 0 < p.2 ∧ p.2 < δ ∧ ENNReal.ofReal (p.2 ^ t) < μ (ball p.1 p.2)}
  obtain ⟨u, huT, hdisj, hcov⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall T Prod.fst Prod.snd δ
      (fun p hp => hp.2.1.le) 4 (by norm_num)
  have hmeas : ∀ p : u, MeasurableSet (closedBall (p : X × ℝ).1 (p : X × ℝ).2) :=
    fun p => measurableSet_closedBall
  have hpair : Pairwise (Disjoint on fun p : u => closedBall (p : X × ℝ).1 (p : X × ℝ).2) :=
    fun p q hpq => hdisj p.2 q.2 fun h => hpq (Subtype.ext h)
  have hlt : ∀ p : u, ENNReal.ofReal ((p : X × ℝ).2 ^ t)
      < μ (closedBall (p : X × ℝ).1 (p : X × ℝ).2) :=
    fun p => (huT p.2).2.2.trans_le (measure_mono ball_subset_closedBall)
  have hcount : Countable u := by
    have h := Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ) hmeas hpair
    rw [show {p : u | 0 < μ (closedBall (p : X × ℝ).1 (p : X × ℝ).2)} = univ from
      eq_univ_of_forall fun p => pos_of_gt (hlt p)] at h
    exact countable_univ_iff.1 h
  refine ⟨u, countable_coe_iff.1 hcount, fun p hp => ⟨(huT hp).1, (huT hp).2.1⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.1 (mem_iInter.1 hx n)
    obtain ⟨b, hb, hsub⟩ := hcov (x, r) ⟨hr.1, hr.2.trans hn, hxr⟩
    exact mem_iUnion₂.2 ⟨b, hb, hsub (mem_closedBall_self hr.1.le)⟩
  · calc ∑' p : u, ENNReal.ofReal ((p : X × ℝ).2 ^ t)
        ≤ ∑' p : u, μ (closedBall (p : X × ℝ).1 (p : X × ℝ).2) :=
          ENNReal.tsum_le_tsum fun p => (hlt p).le
      _ = μ (⋃ p : u, closedBall (p : X × ℝ).1 (p : X × ℝ).2) :=
          (measure_iUnion hpair hmeas).symm
      _ ≤ μ univ := measure_mono (subset_univ _)

/-- The `t`-dimensional Hausdorff measure of `heavyBallSet μ t` is at most `8^t μ(X)`, for a
finite measure `μ` and `t ≥ 0`. -/
theorem hausdorffMeasure_heavyBallSet_le [IsFiniteMeasure μ] (ht : 0 ≤ t) :
    μH[t] (heavyBallSet μ t) ≤ ENNReal.ofReal (8 ^ t) * μ univ := by
  choose u hu_count hu_rad hu_cov hu_sum using fun n : ℕ =>
    exists_countable_cover_heavyBallSet (μ := μ) t
      (Nat.one_div_pos_of_nat (n := n) : (0 : ℝ) < 1 / ((n : ℝ) + 1))
  have : ∀ n, Countable (u n) := fun n => (hu_count n).to_subtype
  have hr : Tendsto (fun n : ℕ => ENNReal.ofReal (8 * (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (8 : ℝ)
    rw [mul_zero] at h
    simpa using ENNReal.tendsto_ofReal h
  have hdiam : ∀ n (p : u n), ediam (closedBall (p : X × ℝ).1 (4 * (p : X × ℝ).2))
      ≤ ENNReal.ofReal (8 * (p : X × ℝ).2) := by
    intro n p
    refine ediam_le_of_forall_dist_le fun a ha b hb => ?_
    have h := dist_triangle_right a b (p : X × ℝ).1
    have ha := mem_closedBall.1 ha
    have hb := mem_closedBall.1 hb
    linarith
  refine (hausdorffMeasure_le_liminf_tsum t _ _ hr
    (fun n (p : u n) => closedBall (p : X × ℝ).1 (4 * (p : X × ℝ).2))
    (Eventually.of_forall fun n p => ?_) (Eventually.of_forall fun n => ?_)).trans ?_
  · refine (hdiam n p).trans (ENNReal.ofReal_le_ofReal ?_)
    have := (hu_rad n p p.2).2
    linarith
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 (hu_cov n hx)
    exact mem_iUnion.2 ⟨⟨p, hp⟩, hxp⟩
  · refine (liminf_le_liminf (Eventually.of_forall fun n => ?_)).trans (liminf_const _).le
    calc ∑' p : u n, ediam (closedBall (p : X × ℝ).1 (4 * (p : X × ℝ).2)) ^ t
        ≤ ∑' p : u n, ENNReal.ofReal (8 ^ t) * ENNReal.ofReal ((p : X × ℝ).2 ^ t) := by
          refine ENNReal.tsum_le_tsum fun p => ?_
          have hp0 : 0 ≤ (p : X × ℝ).2 := (hu_rad n p p.2).1.le
          calc ediam (closedBall (p : X × ℝ).1 (4 * (p : X × ℝ).2)) ^ t
              ≤ ENNReal.ofReal (8 * (p : X × ℝ).2) ^ t := ENNReal.rpow_le_rpow (hdiam n p) ht
            _ = ENNReal.ofReal (8 ^ t) * ENNReal.ofReal ((p : X × ℝ).2 ^ t) := by
              rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) ht,
                Real.mul_rpow (by norm_num) hp0, ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (8 ^ t) * ∑' p : u n, ENNReal.ofReal ((p : X × ℝ).2 ^ t) :=
          ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (8 ^ t) * μ univ := by
          gcongr
          exact hu_sum n

/-- The Hausdorff dimension of `heavyBallSet μ t` is at most `t`, for a finite measure `μ` and
`t ≥ 0`. -/
theorem dimH_heavyBallSet_le [IsFiniteMeasure μ] (ht : 0 ≤ t) :
    dimH (heavyBallSet μ t) ≤ ENNReal.ofReal t := by
  have h : μH[(t.toNNReal : ℝ)] (heavyBallSet μ t) ≠ ∞ := by
    rw [Real.coe_toNNReal t ht]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _))
      (hausdorffMeasure_heavyBallSet_le ht)
  exact dimH_le_of_hausdorffMeasure_ne_top h

omit [BorelSpace X] in
/-- If `μ(B(x, r)) > 0` for all small `r` and `log μ(B(x, r)) / log r < t` for arbitrarily small
`r`, then `x ∈ heavyBallSet μ t`. At such a radius `μ(B(x, r)) > r^t`, and a slightly larger open
ball has the same property. -/
theorem mem_heavyBallSet [IsFiniteMeasure μ]
    (hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < μ.real (closedBall x r))
    (h : ∃ᶠ r : ℝ in 𝓝[>] 0, Real.log (μ.real (closedBall x r)) / Real.log r < t) :
    x ∈ heavyBallSet μ t := by
  refine mem_iInter.2 fun n => ?_
  have hn : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 / ((n : ℝ) + 1) :=
    nhdsWithin_le_nhds (eventually_lt_nhds Nat.one_div_pos_of_nat)
  have h1 : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 := nhdsWithin_le_nhds (eventually_lt_nhds one_pos)
  obtain ⟨r, hr, hrpos, hrn, hr1, hr0⟩ :=
    (h.and_eventually (hpos.and (hn.and (h1.and self_mem_nhdsWithin)))).exists
  have hr0 : 0 < r := hr0
  rw [div_lt_iff_of_neg (Real.log_neg hr0 hr1)] at hr
  have hlt : r ^ t < μ.real (closedBall x r) := by
    rw [← Real.log_lt_log_iff (Real.rpow_pos_of_pos hr0 t) hrpos, Real.log_rpow hr0]
    exact hr
  have hcont : ContinuousAt (fun ρ : ℝ => ρ ^ t) r :=
    Real.continuousAt_rpow_const r t (Or.inl hr0.ne')
  have hev : ∀ᶠ ρ : ℝ in 𝓝[>] r, (ρ ^ t < μ.real (closedBall x r) ∧ ρ < 1 / ((n : ℝ) + 1))
      ∧ r < ρ :=
    (((hcont.eventually (gt_mem_nhds hlt)).and (eventually_lt_nhds hrn)).filter_mono
      nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨ρ, ⟨hρ1, hρ2⟩, hρ3⟩ := hev.exists
  refine mem_iUnion₂.2 ⟨ρ, ⟨hr0.trans hρ3, hρ2⟩, ?_⟩
  calc ENNReal.ofReal (ρ ^ t) < ENNReal.ofReal (μ.real (closedBall x r)) :=
        (ENNReal.ofReal_lt_ofReal_iff hrpos).2 hρ1
    _ = μ (closedBall x r) := ofReal_measureReal
    _ ≤ μ (ball x ρ) := measure_mono (closedBall_subset_ball hρ3)

omit [BorelSpace X] in
/-- A point `x` of the support of a finite measure `μ` with `\underline{dim}_loc(μ, x) < t`, at
which the quotient `log μ(B(x, r)) / log r` is bounded above, lies in `heavyBallSet μ t`. The
two side conditions exclude the points where the real-valued `liminf` of the library does not
carry its usual meaning. -/
theorem mem_heavyBallSet_of_lowerLocalDim_lt [IsFiniteMeasure μ]
    (hpos : ∀ r : ℝ, 0 < r → 0 < μ (closedBall x r))
    (hb : (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≤ ·)
      fun r : ℝ => Real.log (μ.real (closedBall x r)) / Real.log r)
    (h : lowerLocalDim μ x < t) : x ∈ heavyBallSet μ t := by
  refine mem_heavyBallSet ?_ (frequently_lt_of_liminf_lt hb.isCoboundedUnder_ge h)
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact ENNReal.toReal_pos (hpos r hr).ne' (measure_ne_top μ _)

/-- The inequality `≥` in the second line of `eq:dimension_measure_def`: for every
`t > \underline{dim}_H(μ)` there is a Borel set `A` with `μ(A) > 0` and `dim_H A ≤ t`. The
measure `μ` is nonzero and finite on a second-countable metric space, and the quotients
`log μ(B(x, r)) / log r` are bounded above as `r ↓ 0` for almost every `x`, which holds on
`ℝ^d` by `ae_isBoundedUnder_le_log_div_log`. -/
theorem exists_measurableSet_dimH_le [SecondCountableTopology X] [IsFiniteMeasure μ]
    (hne : μ ≠ 0)
    (hb : ∀ᵐ x ∂μ, (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≤ ·)
      fun r : ℝ => Real.log (μ.real (closedBall x r)) / Real.log r)
    (ht : lowerHausdorffDim μ < t) :
    ∃ A : Set X, MeasurableSet A ∧ 0 < μ A ∧ dimH A ≤ ENNReal.ofReal t := by
  have ht0 : 0 ≤ t := lowerHausdorffDim_nonneg.trans ht.le
  refine ⟨heavyBallSet μ t, measurableSet_heavyBallSet μ t, ?_, dimH_heavyBallSet_le ht0⟩
  obtain ⟨a, ha⟩ := exists_frequently_ae_le hne (lowerLocalDim μ)
  have hfreq : ∃ᵐ x ∂μ, lowerLocalDim μ x < t :=
    frequently_lt_of_liminf_lt (IsCoboundedUnder.of_frequently_le ha) ht
  refine pos_iff_ne_zero.2 (frequently_ae_mem_iff.1 ?_)
  refine (hfreq.and_eventually (hb.and (ae_forall_measure_closedBall_pos μ))).mono ?_
  rintro x ⟨hx, hbx, hpos⟩
  exact mem_heavyBallSet_of_lowerLocalDim_lt hpos hbx hx

/-- The second line of `eq:dimension_measure_def`:
`\underline{dim}_H(μ) = inf {dim_H A : A is a Borel set such that μ(A) > 0}`, for a nonzero
finite measure `μ` on a second-countable metric space such that the quotients
`log μ(B(x, r)) / log r` are bounded above as `r ↓ 0` for almost every `x`. The infimum is taken
in `[0, ∞]`. -/
theorem ofReal_lowerHausdorffDim_eq_iInf_dimH [SecondCountableTopology X] [IsFiniteMeasure μ]
    (hne : μ ≠ 0)
    (hb : ∀ᵐ x ∂μ, (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≤ ·)
      fun r : ℝ => Real.log (μ.real (closedBall x r)) / Real.log r) :
    ENNReal.ofReal (lowerHausdorffDim μ)
      = ⨅ (A : Set X) (_ : MeasurableSet A) (_ : 0 < μ A), dimH A := by
  refine le_antisymm (le_iInf fun A => le_iInf fun _ => le_iInf fun hA =>
    ofReal_lowerHausdorffDim_le_dimH hA) ?_
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  rcases eq_or_ne c ∞ with rfl | hctop
  · exact le_top
  have ht : lowerHausdorffDim μ < c.toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal lowerHausdorffDim_nonneg hctop).1 hc
  obtain ⟨A, hAm, hApos, hAdim⟩ := exists_measurableSet_dimH_le hne hb ht
  calc (⨅ (A : Set X) (_ : MeasurableSet A) (_ : 0 < μ A), dimH A) ≤ dimH A :=
        iInf_le_of_le A (iInf_le_of_le hAm (iInf_le _ hApos))
    _ ≤ ENNReal.ofReal c.toReal := hAdim
    _ = c := ENNReal.ofReal_toReal hctop

/-- The second line of `eq:dimension_measure_def` with the infimum over all sets of positive
outer measure: the restriction to Borel sets does not change the infimum. -/
theorem ofReal_lowerHausdorffDim_eq_iInf_dimH_of_pos [SecondCountableTopology X]
    [IsFiniteMeasure μ] (hne : μ ≠ 0)
    (hb : ∀ᵐ x ∂μ, (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≤ ·)
      fun r : ℝ => Real.log (μ.real (closedBall x r)) / Real.log r) :
    ENNReal.ofReal (lowerHausdorffDim μ) = ⨅ (A : Set X) (_ : 0 < μ A), dimH A := by
  refine le_antisymm (le_iInf fun A => le_iInf fun hA => ofReal_lowerHausdorffDim_le_dimH hA) ?_
  rw [ofReal_lowerHausdorffDim_eq_iInf_dimH hne hb]
  exact le_iInf fun A => le_iInf fun _ => le_iInf fun hA => iInf_le_of_le A (iInf_le _ hA)

end Covering

section DimensionMeasureDef

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- The second line of `eq:dimension_measure_def` for a nonzero finite Borel measure `μ` on a
finite-dimensional real normed space:
`\underline{dim}_H(μ) = inf {dim_H A : A is a Borel set such that μ(A) > 0}`. The infimum is
taken in `[0, ∞]`. -/
theorem ofReal_lowerHausdorffDim_eq_iInf_dimH_of_finiteDimensional [IsFiniteMeasure μ]
    (hne : μ ≠ 0) :
    ENNReal.ofReal (lowerHausdorffDim μ)
      = ⨅ (A : Set E) (_ : MeasurableSet A) (_ : 0 < μ A), dimH A :=
  ofReal_lowerHausdorffDim_eq_iInf_dimH hne ae_isBoundedUnder_le_log_div_log

/-- The second line of `eq:dimension_measure_def` with real values, for a nonzero finite Borel
measure on a finite-dimensional real normed space. -/
theorem lowerHausdorffDim_eq_toReal_iInf_dimH [IsFiniteMeasure μ] (hne : μ ≠ 0) :
    lowerHausdorffDim μ
      = (⨅ (A : Set E) (_ : MeasurableSet A) (_ : 0 < μ A), dimH A).toReal := by
  rw [← ofReal_lowerHausdorffDim_eq_iInf_dimH_of_finiteDimensional hne,
    ENNReal.toReal_ofReal lowerHausdorffDim_nonneg]

end DimensionMeasureDef

section LineAndPlane

/-- The upper pointwise dimension of a finite Borel measure on `ℝ` is at most `1` almost
everywhere. -/
theorem ae_upperLocalDim_le_one {μ : Measure ℝ} [IsFiniteMeasure μ] :
    ∀ᵐ x ∂μ, upperLocalDim μ x ≤ 1 := by
  simpa using ae_upperLocalDim_le (μ := μ)

/-- The upper pointwise dimension of a finite Borel measure on the plane `ℝ × ℝ` with the
supremum metric is at most `2` almost everywhere. -/
theorem ae_upperLocalDim_le_two {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ] :
    ∀ᵐ x ∂μ, upperLocalDim μ x ≤ 2 := by
  simpa using ae_upperLocalDim_le (μ := μ)

/-- The dimension of a nonzero finite exact-dimensional Borel measure on `ℝ` lies in
`[0, 1]`. -/
theorem IsExactDim.dim_mem_Icc_one {μ : Measure ℝ} [IsFiniteMeasure μ] {d : ℝ}
    (h : IsExactDim μ d) (hne : μ ≠ 0) : d ∈ Icc (0 : ℝ) 1 := by
  simpa using h.dim_mem_Icc hne

/-- The dimension of a nonzero finite exact-dimensional Borel measure on the plane `ℝ × ℝ` lies
in `[0, 2]`. -/
theorem IsExactDim.dim_mem_Icc_two {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ] {d : ℝ}
    (h : IsExactDim μ d) (hne : μ ≠ 0) : d ∈ Icc (0 : ℝ) 2 := by
  simpa using h.dim_mem_Icc hne

/-- The second line of `eq:dimension_measure_def` holds on the real line. -/
example {μ : Measure ℝ} [IsFiniteMeasure μ] (hne : μ ≠ 0) :
    ENNReal.ofReal (lowerHausdorffDim μ)
      = ⨅ (A : Set ℝ) (_ : MeasurableSet A) (_ : 0 < μ A), dimH A :=
  ofReal_lowerHausdorffDim_eq_iInf_dimH_of_finiteDimensional hne

/-- The second line of `eq:dimension_measure_def` holds on the plane `ℝ × ℝ` with the supremum
metric. -/
example {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ] (hne : μ ≠ 0) :
    ENNReal.ofReal (lowerHausdorffDim μ)
      = ⨅ (A : Set (ℝ × ℝ)) (_ : MeasurableSet A) (_ : 0 < μ A), dimH A :=
  ofReal_lowerHausdorffDim_eq_iInf_dimH_of_finiteDimensional hne

end LineAndPlane

end BoxLike
