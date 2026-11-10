module

/-
The upper and lower pointwise dimensions, the upper packing dimension and the lower Hausdorff
dimension of a measure, and `eq:haus_dim_sum`, from `sec:ledrappier_young_formula`.

* `upperLocalDim`, `lowerLocalDim`: the upper and lower pointwise dimensions of `μ` at `x`.
* `upperPackingDim`, `lowerHausdorffDim`: `\overline{dim}_p(μ)` and `\underline{dim}_H(μ)` as
  the essential supremum and the essential infimum of the pointwise dimensions.
* `HasLocalDim.upperLocalDim_eq`, `HasLocalDim.lowerLocalDim_eq`: where `dimloc(μ, x)` exists,
  both pointwise dimensions equal it.
* `HasLocalDimPair.upperPackingDim_eq`, `HasLocalDimPair.lowerHausdorffDim_eq`: for a
  measure whose pointwise dimension is `d₁` or `d₂` almost everywhere, `\overline{dim}_p(μ)` is
  the larger value and `\underline{dim}_H(μ)` is the smaller value, when that value occurs on a
  set of positive measure.
* `IsExactDim.upperPackingDim_eq`, `IsExactDim.lowerHausdorffDim_eq`: for a nonzero
  exact-dimensional measure, `\overline{dim}_p(μ) = \underline{dim}_H(μ) = dim μ`.
* `upperLocalDim_nonneg`, `lowerLocalDim_nonneg`, `upperPackingDim_nonneg`,
  `lowerHausdorffDim_nonneg`: all four dimensions of a finite measure are non-negative.
* `ae_upperLocalDim_eq_of_le`, `ae_lowerLocalDim_eq_of_le`: if `ν' ≤ ν`, then the upper and
  lower pointwise dimensions of `ν'` and `ν` agree `ν'`-almost everywhere.
* `upperPackingDim_add`, `lowerHausdorffDim_add`: `eq:haus_dim_sum`.
* `IsExactDim.upperPackingDim_add`, `IsExactDim.lowerHausdorffDim_add`: `eq:haus_dim_sum` for
  two nonzero exact-dimensional measures, as used in the proof of `thm:eq_state_proj_dim`.
-/
public import BoxLike.MeasureDim
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.Topology.Order.LiminfLimsup

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Metric
open scoped ENNReal

section Real

variable {α : Type*} {f : Filter α} {u v : α → ℝ}

/-- If `S + ε ⊆ T` and `T + ε ⊆ S` for every `ε > 0`, then `sInf S ≤ sInf T`. The statement
includes the cases where `S` and `T` are empty or unbounded below, in which both infima are
`0`. -/
theorem sInf_le_sInf_of_add_mem {S T : Set ℝ} (hST : ∀ a ∈ S, ∀ ε > 0, a + ε ∈ T)
    (hTS : ∀ a ∈ T, ∀ ε > 0, a + ε ∈ S) : sInf S ≤ sInf T := by
  rcases T.eq_empty_or_nonempty with rfl | hT
  · have hS : S = ∅ := Set.eq_empty_of_forall_notMem fun a ha => hST a ha 1 one_pos
    rw [hS]
  · by_cases hb : BddBelow S
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      rw [← sub_le_iff_le_add]
      refine le_csInf hT fun a ha => ?_
      have := csInf_le hb (hTS a ha ε hε)
      linarith
    · have hb' : ¬BddBelow T := fun ⟨b, hb'⟩ =>
        hb ⟨b - 1, fun a ha => by have := hb' (hST a ha 1 one_pos); linarith⟩
      rw [Real.sInf_of_not_bddBelow hb, Real.sInf_of_not_bddBelow hb']

/-- Two real functions whose difference tends to `0` along a filter have the same `limsup`
along it. No boundedness is assumed. -/
theorem limsup_eq_of_tendsto_sub (h : Tendsto (fun a => u a - v a) f (𝓝 0)) :
    limsup u f = limsup v f := by
  have key : ∀ {u v : α → ℝ}, Tendsto (fun a => u a - v a) f (𝓝 0) →
      ∀ a ∈ {a | ∀ᶠ n in f, u n ≤ a}, ∀ ε > 0, a + ε ∈ {a | ∀ᶠ n in f, v n ≤ a} := by
    intro u v h a ha ε hε
    have h1 : ∀ᶠ n in f, -ε < u n - v n := h.eventually_const_lt (by linarith)
    filter_upwards [ha, h1] with n hn hn'
    linarith
  have h' : Tendsto (fun a => v a - u a) f (𝓝 0) := by simpa using h.neg
  rw [limsup_eq, limsup_eq]
  exact le_antisymm (sInf_le_sInf_of_add_mem (key h) (key h'))
    (sInf_le_sInf_of_add_mem (key h') (key h))

/-- In `ℝ` the identity `liminf u = -limsup (-u)` holds along every filter. No boundedness is
assumed. -/
theorem liminf_eq_neg_limsup_neg (f : Filter α) (u : α → ℝ) :
    liminf u f = -limsup (fun a => -u a) f := by
  rw [liminf_eq, limsup_eq, ← Real.sSup_neg]
  congr 1
  ext a
  simp only [Set.mem_neg, Set.mem_ofPred_eq, neg_le_neg_iff]

/-- Two real functions whose difference tends to `0` along a filter have the same `liminf`
along it. No boundedness is assumed. -/
theorem liminf_eq_of_tendsto_sub (h : Tendsto (fun a => u a - v a) f (𝓝 0)) :
    liminf u f = liminf v f := by
  rw [liminf_eq_neg_limsup_neg, liminf_eq_neg_limsup_neg]
  congr 1
  refine limsup_eq_of_tendsto_sub ?_
  have h' := h.neg
  rw [neg_zero] at h'
  exact h'.congr fun a => by ring

/-- If a real function is eventually at least `-ε` for every `ε > 0`, then its `limsup` is
non-negative. -/
theorem limsup_nonneg_of_eventually (h : ∀ ε > 0, ∀ᶠ a in f, -ε ≤ u a) : 0 ≤ limsup u f := by
  rw [limsup_eq]
  rcases f.eq_or_neBot with rfl | hf
  · simp
  · refine Real.sInf_nonneg fun a ha => le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨n, hn, hn'⟩ := ((h ε hε).and ha).exists
    linarith

/-- If a real function is eventually at least `-ε` for every `ε > 0`, then its `liminf` is
non-negative. -/
theorem liminf_nonneg_of_eventually (h : ∀ ε > 0, ∀ᶠ a in f, -ε ≤ u a) : 0 ≤ liminf u f := by
  rw [liminf_eq]
  by_cases hb : BddAbove {a | ∀ᶠ n in f, a ≤ u n}
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have := le_csSup hb (h ε hε)
    linarith
  · rw [Real.sSup_of_not_bddAbove hb]

/-- The `limsup` along a supremum of two filters is the maximum of the two `limsup`s, when the
function is bounded and cobounded above along both. -/
theorem limsup_sup_filter_of_isBoundedUnder {β : Type*} [ConditionallyCompleteLinearOrder β]
    [DenselyOrdered β] {F G : Filter α} {g : α → β}
    (hF : F.IsBoundedUnder (· ≤ ·) g) (hG : G.IsBoundedUnder (· ≤ ·) g)
    (hF' : F.IsCoboundedUnder (· ≤ ·) g) (hG' : G.IsCoboundedUnder (· ≤ ·) g) :
    limsup g (F ⊔ G) = max (limsup g F) (limsup g G) := by
  have hFG : (F ⊔ G).IsBoundedUnder (· ≤ ·) g := by
    unfold IsBoundedUnder
    rw [map_sup]
    exact isBounded_sup hF hG
  refine le_antisymm ?_ (max_le ?_ ?_)
  · refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    have h1 := eventually_lt_of_limsup_lt ((le_max_left _ _).trans_lt hc) hF
    have h2 := eventually_lt_of_limsup_lt ((le_max_right _ _).trans_lt hc) hG
    exact limsup_le_of_le (IsCobounded.mono (map_mono le_sup_left) hF')
      (eventually_sup.2 ⟨h1.mono fun _ h => h.le, h2.mono fun _ h => h.le⟩)
  · exact limsup_le_limsup_of_le le_sup_left hF' hFG
  · exact limsup_le_limsup_of_le le_sup_right hG' hFG

/-- The `liminf` along a supremum of two filters is the minimum of the two `liminf`s, when the
function is bounded and cobounded below along both. -/
theorem liminf_sup_filter_of_isBoundedUnder {β : Type*} [ConditionallyCompleteLinearOrder β]
    [DenselyOrdered β] {F G : Filter α} {g : α → β}
    (hF : F.IsBoundedUnder (· ≥ ·) g) (hG : G.IsBoundedUnder (· ≥ ·) g)
    (hF' : F.IsCoboundedUnder (· ≥ ·) g) (hG' : G.IsCoboundedUnder (· ≥ ·) g) :
    liminf g (F ⊔ G) = min (liminf g F) (liminf g G) :=
  limsup_sup_filter_of_isBoundedUnder (β := βᵒᵈ) hF hG hF' hG'

end Real

section AlmostEverywhere

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A real function is not almost everywhere larger than every constant, when the measure is
nonzero. -/
theorem exists_frequently_ae_le (hne : μ ≠ 0) (g : X → ℝ) : ∃ a, ∃ᵐ x ∂μ, g x ≤ a := by
  have : (ae μ).NeBot := ae_neBot.2 hne
  by_contra h
  have h' : ∀ n : ℕ, ∀ᵐ x ∂μ, ¬g x ≤ n := fun n =>
    not_frequently.1 fun hn => h ⟨n, hn⟩
  obtain ⟨x, hx⟩ := (ae_all_iff.2 h').exists
  obtain ⟨n, hn⟩ := exists_nat_ge (g x)
  exact hx n hn

/-- A real function is not almost everywhere smaller than every constant, when the measure is
nonzero. -/
theorem exists_frequently_ae_ge (hne : μ ≠ 0) (g : X → ℝ) : ∃ a, ∃ᵐ x ∂μ, a ≤ g x := by
  obtain ⟨a, ha⟩ := exists_frequently_ae_le hne fun x => -g x
  exact ⟨-a, ha.mono fun x hx => by linarith⟩

/-- The almost everywhere filter of the sum of two measures is the supremum of the two almost
everywhere filters. -/
theorem ae_add_eq_sup (ν₁ ν₂ : Measure X) : ae (ν₁ + ν₂) = ae ν₁ ⊔ ae ν₂ := by
  ext s
  rw [mem_sup, mem_ae_iff, mem_ae_iff, mem_ae_iff, Measure.add_apply, add_eq_zero]

end AlmostEverywhere

section Definitions

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  {μ ν₁ ν₂ : Measure X} {x : X} {d d₁ d₂ : ℝ}

/-- The upper pointwise dimension `\overline{dim}_loc(μ, x)`: the `limsup` of
`log μ(B(x, r)) / log r` as `r ↓ 0`, with closed balls. The value is real. For a finite Borel
measure on `ℝ^d` the upper pointwise dimension lies in `[0, d]` almost everywhere, so the
real-valued `limsup` carries its usual meaning. -/
noncomputable def upperLocalDim (μ : Measure X) (x : X) : ℝ :=
  limsup (fun r : ℝ => Real.log (μ.real (closedBall x r)) / Real.log r) (𝓝[>] 0)

/-- The lower pointwise dimension `\underline{dim}_loc(μ, x)`: the `liminf` of
`log μ(B(x, r)) / log r` as `r ↓ 0`, with closed balls. The value is real. For a finite Borel
measure on `ℝ^d` the lower pointwise dimension lies in `[0, d]` almost everywhere, so the
real-valued `liminf` carries its usual meaning. -/
noncomputable def lowerLocalDim (μ : Measure X) (x : X) : ℝ :=
  liminf (fun r : ℝ => Real.log (μ.real (closedBall x r)) / Real.log r) (𝓝[>] 0)

/-- If `dimloc(μ, x) = d`, then the upper pointwise dimension of `μ` at `x` equals `d`. -/
theorem HasLocalDim.upperLocalDim_eq (h : HasLocalDim μ x d) : upperLocalDim μ x = d :=
  Tendsto.limsup_eq h

/-- If `dimloc(μ, x) = d`, then the lower pointwise dimension of `μ` at `x` equals `d`. -/
theorem HasLocalDim.lowerLocalDim_eq (h : HasLocalDim μ x d) : lowerLocalDim μ x = d :=
  Tendsto.liminf_eq h

/-- The upper packing dimension `\overline{dim}_p(μ)`: the essential supremum of the upper
pointwise dimension with respect to `μ`. The value is real. For a finite Borel measure on
`ℝ^d` the pointwise dimensions lie in `[0, d]` almost everywhere, so the real-valued `essSup`
carries its usual meaning. -/
noncomputable def upperPackingDim (μ : Measure X) : ℝ := essSup (upperLocalDim μ) μ

/-- The lower Hausdorff dimension `\underline{dim}_H(μ)`: the essential infimum of the lower
pointwise dimension with respect to `μ`. The value is real. For a finite Borel measure on
`ℝ^d` the pointwise dimensions lie in `[0, d]` almost everywhere, so the real-valued `essInf`
carries its usual meaning. -/
noncomputable def lowerHausdorffDim (μ : Measure X) : ℝ := essInf (lowerLocalDim μ) μ

/-- If the pointwise dimension of `μ` is `d₁` or `d₂` almost everywhere, with `d₂ ≤ d₁` and `d₁`
occurring on a set of positive measure, then `\overline{dim}_p(μ) = d₁`. This is the first half
of the characterisation of double-dimensional measures in `sec:ledrappier_young_formula`. -/
theorem HasLocalDimPair.upperPackingDim_eq (h : HasLocalDimPair μ d₁ d₂) (hle : d₂ ≤ d₁)
    (hpos : 0 < μ {x | HasLocalDim μ x d₁}) : upperPackingDim μ = d₁ := by
  have hub : ∀ᵐ x ∂μ, upperLocalDim μ x ≤ d₁ := by
    filter_upwards [h] with x hx
    rcases hx with hx | hx
    · exact hx.upperLocalDim_eq.le
    · exact hx.upperLocalDim_eq.le.trans hle
  have hfreq : ∃ᵐ x ∂μ, d₁ ≤ upperLocalDim μ x :=
    (frequently_ae_iff.2 hpos.ne').mono fun x hx => hx.upperLocalDim_eq.ge
  exact le_antisymm (limsup_le_of_le (IsCoboundedUnder.of_frequently_ge hfreq) hub)
    (le_limsup_of_frequently_le hfreq (isBoundedUnder_of_eventually_le hub))

/-- If the pointwise dimension of `μ` is `d₁` or `d₂` almost everywhere, with `d₂ ≤ d₁` and `d₂`
occurring on a set of positive measure, then `\underline{dim}_H(μ) = d₂`. This is the second
half of the characterisation of double-dimensional measures in
`sec:ledrappier_young_formula`. -/
theorem HasLocalDimPair.lowerHausdorffDim_eq (h : HasLocalDimPair μ d₁ d₂) (hle : d₂ ≤ d₁)
    (hpos : 0 < μ {x | HasLocalDim μ x d₂}) : lowerHausdorffDim μ = d₂ := by
  have hlb : ∀ᵐ x ∂μ, d₂ ≤ lowerLocalDim μ x := by
    filter_upwards [h] with x hx
    rcases hx with hx | hx
    · exact hle.trans hx.lowerLocalDim_eq.ge
    · exact hx.lowerLocalDim_eq.ge
  have hfreq : ∃ᵐ x ∂μ, lowerLocalDim μ x ≤ d₂ :=
    (frequently_ae_iff.2 hpos.ne').mono fun x hx => hx.lowerLocalDim_eq.le
  exact le_antisymm (liminf_le_of_frequently_le hfreq (isBoundedUnder_of_eventually_ge hlb))
    (le_liminf_of_le (IsCoboundedUnder.of_frequently_le hfreq) hlb)

/-- For a nonzero exact-dimensional measure, the set of points where the pointwise dimension
equals `dim μ` has positive outer measure. -/
theorem IsExactDim.measure_hasLocalDim_pos (h : IsExactDim μ d) (hne : μ ≠ 0) :
    0 < μ {x | HasLocalDim μ x d} := by
  have : (ae μ).NeBot := ae_neBot.2 hne
  exact pos_iff_ne_zero.2 (frequently_ae_iff.1 h.frequently)

/-- For a nonzero exact-dimensional measure, `\overline{dim}_p(μ) = dim μ`. -/
theorem IsExactDim.upperPackingDim_eq (h : IsExactDim μ d) (hne : μ ≠ 0) :
    upperPackingDim μ = d :=
  h.hasLocalDimPair.upperPackingDim_eq le_rfl (h.measure_hasLocalDim_pos hne)

/-- For a nonzero exact-dimensional measure, `\underline{dim}_H(μ) = dim μ`. -/
theorem IsExactDim.lowerHausdorffDim_eq (h : IsExactDim μ d) (hne : μ ≠ 0) :
    lowerHausdorffDim μ = d :=
  h.hasLocalDimPair.lowerHausdorffDim_eq le_rfl (h.measure_hasLocalDim_pos hne)

/-- For a finite measure and every `ε > 0`, the quotient `log μ(B(x, r)) / log r` is at least
`-ε` for all small `r`. -/
theorem eventually_neg_le_log_div_log [IsFiniteMeasure μ] (x : X) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, -ε ≤ Real.log (μ.real (closedBall x r)) / Real.log r := by
  have hL : Tendsto (fun r : ℝ => max (Real.log (μ.real Set.univ)) 0 / Real.log r)
      (𝓝[>] 0) (𝓝 0) := tendsto_const_nhds.div_atBot Real.tendsto_log_nhdsGT_zero
  have h1 : ∀ᶠ r : ℝ in 𝓝[>] 0, -ε < max (Real.log (μ.real Set.univ)) 0 / Real.log r :=
    hL.eventually_const_lt (by linarith)
  have h2 : ∀ᶠ r : ℝ in 𝓝[>] 0, Real.log r < 0 :=
    Real.tendsto_log_nhdsGT_zero.eventually_lt_atBot 0
  filter_upwards [h1, h2] with r hr hr'
  refine hr.le.trans (div_le_div_of_nonpos_of_le hr'.le ?_)
  rcases eq_or_lt_of_le (measureReal_nonneg : 0 ≤ μ.real (closedBall x r)) with h0 | h0
  · rw [← h0, Real.log_zero]
    exact le_max_right _ _
  · exact (Real.log_le_log h0 (measureReal_mono (Set.subset_univ _))).trans (le_max_left _ _)

/-- The upper pointwise dimension of a finite measure is non-negative. -/
theorem upperLocalDim_nonneg [IsFiniteMeasure μ] (x : X) : 0 ≤ upperLocalDim μ x :=
  limsup_nonneg_of_eventually fun _ hε => eventually_neg_le_log_div_log x hε

/-- The lower pointwise dimension of a finite measure is non-negative. -/
theorem lowerLocalDim_nonneg [IsFiniteMeasure μ] (x : X) : 0 ≤ lowerLocalDim μ x :=
  liminf_nonneg_of_eventually fun _ hε => eventually_neg_le_log_div_log x hε

/-- The upper packing dimension of a finite measure is non-negative. -/
theorem upperPackingDim_nonneg [IsFiniteMeasure μ] : 0 ≤ upperPackingDim μ :=
  limsup_nonneg_of_eventually fun _ hε =>
    Eventually.of_forall fun x => (neg_nonpos.2 hε.le).trans (upperLocalDim_nonneg x)

/-- The lower Hausdorff dimension of a finite measure is non-negative. -/
theorem lowerHausdorffDim_nonneg [IsFiniteMeasure μ] : 0 ≤ lowerHausdorffDim μ :=
  liminf_nonneg_of_eventually fun _ hε =>
    Eventually.of_forall fun x => (neg_nonpos.2 hε.le).trans (lowerLocalDim_nonneg x)

/-- The real-valued upper packing dimension of the zero measure is `0`. -/
theorem upperPackingDim_zero : upperPackingDim (0 : Measure X) = 0 := by
  simp [upperPackingDim, essSup, limsup_eq]

end Definitions

section Besicovitch

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [HasBesicovitchCovering X]
  {ν' ν ν₁ ν₂ : Measure X} {d₁ d₂ : ℝ}

/-- If `ν' ≤ ν`, then for `ν'`-almost every `x` the difference
`log ν'(B(x, r)) / log r - log ν(B(x, r)) / log r` tends to `0` as `r ↓ 0`. This is the proof
of `thm:exact-dimensional-mixture`, without any assumption on the pointwise dimensions. -/
theorem ae_tendsto_log_div_log_sub_of_le [IsFiniteMeasure ν] (h : ν' ≤ ν) :
    ∀ᵐ x ∂ν', Tendsto (fun r : ℝ => Real.log (ν'.real (closedBall x r)) / Real.log r
      - Real.log (ν.real (closedBall x r)) / Real.log r) (𝓝[>] 0) (𝓝 0) := by
  have : IsFiniteMeasure ν' := isFiniteMeasure_of_le ν h
  have hac : ν' ≪ ν := Measure.absolutelyContinuous_of_le h
  filter_upwards [hac.ae_le (Besicovitch.ae_tendsto_rnDeriv ν' ν), Measure.rnDeriv_pos hac,
    hac.ae_le (Measure.rnDeriv_ne_top ν' ν)] with x hx hpos htop
  exact tendsto_log_div_log_sub hpos htop hx

/-- If `ν' ≤ ν`, then the upper pointwise dimensions of `ν'` and `ν` agree `ν'`-almost
everywhere. -/
theorem ae_upperLocalDim_eq_of_le [IsFiniteMeasure ν] (h : ν' ≤ ν) :
    ∀ᵐ x ∂ν', upperLocalDim ν' x = upperLocalDim ν x :=
  (ae_tendsto_log_div_log_sub_of_le h).mono fun _ hx => limsup_eq_of_tendsto_sub hx

/-- If `ν' ≤ ν`, then the lower pointwise dimensions of `ν'` and `ν` agree `ν'`-almost
everywhere. -/
theorem ae_lowerLocalDim_eq_of_le [IsFiniteMeasure ν] (h : ν' ≤ ν) :
    ∀ᵐ x ∂ν', lowerLocalDim ν' x = lowerLocalDim ν x :=
  (ae_tendsto_log_div_log_sub_of_le h).mono fun _ hx => liminf_eq_of_tendsto_sub hx

/-- First line of `eq:haus_dim_sum`: `\overline{dim}_p(ν₁ + ν₂)` is the maximum of
`\overline{dim}_p(ν₁)` and `\overline{dim}_p(ν₂)`, for finite measures whose upper pointwise
dimensions are essentially bounded above. On `ℝ^d` the bound `d` serves for every finite
Borel measure. -/
theorem upperPackingDim_add [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (hb₁ : (ae ν₁).IsBoundedUnder (· ≤ ·) (upperLocalDim ν₁))
    (hb₂ : (ae ν₂).IsBoundedUnder (· ≤ ·) (upperLocalDim ν₂)) :
    upperPackingDim (ν₁ + ν₂) = max (upperPackingDim ν₁) (upperPackingDim ν₂) := by
  rcases eq_or_ne ν₁ 0 with rfl | hne₁
  · rw [zero_add, upperPackingDim_zero, max_eq_right upperPackingDim_nonneg]
  rcases eq_or_ne ν₂ 0 with rfl | hne₂
  · rw [add_zero, upperPackingDim_zero, max_eq_left upperPackingDim_nonneg]
  have e₁ : upperLocalDim (ν₁ + ν₂) =ᵐ[ν₁] upperLocalDim ν₁ :=
    (ae_upperLocalDim_eq_of_le (Measure.le_add_right le_rfl)).mono fun _ hx => hx.symm
  have e₂ : upperLocalDim (ν₁ + ν₂) =ᵐ[ν₂] upperLocalDim ν₂ :=
    (ae_upperLocalDim_eq_of_le (Measure.le_add_left le_rfl)).mono fun _ hx => hx.symm
  obtain ⟨a₁, ha₁⟩ := exists_frequently_ae_ge hne₁ (upperLocalDim (ν₁ + ν₂))
  obtain ⟨a₂, ha₂⟩ := exists_frequently_ae_ge hne₂ (upperLocalDim (ν₁ + ν₂))
  unfold upperPackingDim essSup
  rw [ae_add_eq_sup, limsup_sup_filter_of_isBoundedUnder (hb₁.mono_le e₁.le)
    (hb₂.mono_le e₂.le) (IsCoboundedUnder.of_frequently_ge ha₁)
    (IsCoboundedUnder.of_frequently_ge ha₂), limsup_congr e₁, limsup_congr e₂]

/-- Second line of `eq:haus_dim_sum`: `\underline{dim}_H(ν₁ + ν₂)` is the minimum of
`\underline{dim}_H(ν₁)` and `\underline{dim}_H(ν₂)`, for nonzero finite measures. -/
theorem lowerHausdorffDim_add [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] (hne₁ : ν₁ ≠ 0)
    (hne₂ : ν₂ ≠ 0) :
    lowerHausdorffDim (ν₁ + ν₂) = min (lowerHausdorffDim ν₁) (lowerHausdorffDim ν₂) := by
  have e₁ : lowerLocalDim (ν₁ + ν₂) =ᵐ[ν₁] lowerLocalDim ν₁ :=
    (ae_lowerLocalDim_eq_of_le (Measure.le_add_right le_rfl)).mono fun _ hx => hx.symm
  have e₂ : lowerLocalDim (ν₁ + ν₂) =ᵐ[ν₂] lowerLocalDim ν₂ :=
    (ae_lowerLocalDim_eq_of_le (Measure.le_add_left le_rfl)).mono fun _ hx => hx.symm
  obtain ⟨a₁, ha₁⟩ := exists_frequently_ae_le hne₁ (lowerLocalDim (ν₁ + ν₂))
  obtain ⟨a₂, ha₂⟩ := exists_frequently_ae_le hne₂ (lowerLocalDim (ν₁ + ν₂))
  have hb : ∀ ν : Measure X, (ae ν).IsBoundedUnder (· ≥ ·) (lowerLocalDim (ν₁ + ν₂)) :=
    fun ν => isBoundedUnder_of_eventually_ge (Eventually.of_forall lowerLocalDim_nonneg)
  unfold lowerHausdorffDim essInf
  rw [ae_add_eq_sup, liminf_sup_filter_of_isBoundedUnder (hb ν₁) (hb ν₂)
    (IsCoboundedUnder.of_frequently_le ha₁) (IsCoboundedUnder.of_frequently_le ha₂),
    liminf_congr e₁, liminf_congr e₂]

/-- First line of `eq:haus_dim_sum` for two nonzero exact-dimensional measures:
`\overline{dim}_p(ν₁ + ν₂) = max {dim ν₁, dim ν₂}`. This is the last step in the proof of
`thm:eq_state_proj_dim`. -/
theorem IsExactDim.upperPackingDim_add [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h₁ : IsExactDim ν₁ d₁) (h₂ : IsExactDim ν₂ d₂) (hne₁ : ν₁ ≠ 0) (hne₂ : ν₂ ≠ 0) :
    upperPackingDim (ν₁ + ν₂) = max d₁ d₂ := by
  rcases le_total d₂ d₁ with hle | hle
  · rw [max_eq_left hle]
    exact (h₁.hasLocalDimPair_add h₂).upperPackingDim_eq hle
      (h₁.measure_hasLocalDim_add_left_pos hne₁)
  · rw [max_eq_right hle]
    exact (h₁.hasLocalDimPair_add h₂).symm.upperPackingDim_eq hle
      (h₂.measure_hasLocalDim_add_right_pos hne₂)

/-- Second line of `eq:haus_dim_sum` for two nonzero exact-dimensional measures:
`\underline{dim}_H(ν₁ + ν₂) = min {dim ν₁, dim ν₂}`. This is the last step in the proof of
`thm:eq_state_proj_dim`. -/
theorem IsExactDim.lowerHausdorffDim_add [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h₁ : IsExactDim ν₁ d₁) (h₂ : IsExactDim ν₂ d₂) (hne₁ : ν₁ ≠ 0) (hne₂ : ν₂ ≠ 0) :
    lowerHausdorffDim (ν₁ + ν₂) = min d₁ d₂ := by
  rcases le_total d₂ d₁ with hle | hle
  · rw [min_eq_right hle]
    exact (h₁.hasLocalDimPair_add h₂).lowerHausdorffDim_eq hle
      (h₂.measure_hasLocalDim_add_right_pos hne₂)
  · rw [min_eq_left hle]
    exact (h₁.hasLocalDimPair_add h₂).symm.lowerHausdorffDim_eq hle
      (h₁.measure_hasLocalDim_add_left_pos hne₁)

end Besicovitch

end BoxLike
