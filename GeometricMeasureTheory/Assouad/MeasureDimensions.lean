/-
# Section 5.5: Local dimensions and uniform scaling of measures

The local dimensions of a measure at a point, the dimension bounds they give for sets, and the
upper regularity dimension, which is the two-scale analogue of Assouad dimension for measures.

| Notes | Lean declaration | Location |
|---|---|---|
| Definition 5.13 (local dimensions) | `lowerLocalDim`, `upperLocalDim` | here |
| Proposition 5.14 (local dimensions bound Hausdorff dimension) | `local_dimension_bounds` | here |
| Definition 5.15 (upper regularity dimension, doubling measure) | `UpperRegularityDimLE`, `upperRegularityDim`, `IsDoublingMeasure` | here |
| Proposition 5.16 (doubling measures) | `doubling_measure_dimension`, `assouadDim_support_le_upperRegularityDim`, `upperRegularityDim_of_isAhlforsRegular` | here |
| Example 5.17 (a measure scaling faster than its support) | `measure_dimension_exceeds_ambient` | here |
| Ball masses at a support point are positive | `measure_ball_pos_of_mem_support` | here |
| The ball bounds behind the lower local dimension | `eventually_measure_ball_le_rpow`, `frequently_rpow_le_measure_ball` | here |
| Two-sided ball bounds give the local dimension | `localDim_eq_of_measure_ball_bounds` | here |
-/
import GeometricMeasureTheory.Assouad.AhlforsDimensions

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-! ## Definition 5.13 (`def:local-measure-dimensions`) -/

/-- Definition 5.13 (`def:local-measure-dimensions`): the lower local dimension
`liminf_{r → 0} log μ(B(x, r)) / log r`. -/
def lowerLocalDim (μ : Measure X) (x : X) : ℝ≥0∞ :=
  liminf (fun r : ℝ => ENNReal.ofReal (Real.log (μ (ball x r)).toReal / Real.log r)) (𝓝[>] 0)

/-- Definition 5.13 (`def:local-measure-dimensions`): the upper local dimension
`limsup_{r → 0} log μ(B(x, r)) / log r`. -/
def upperLocalDim (μ : Measure X) (x : X) : ℝ≥0∞ :=
  limsup (fun r : ℝ => ENNReal.ofReal (Real.log (μ (ball x r)).toReal / Real.log r)) (𝓝[>] 0)

/-! ### Auxiliary facts -/

omit [BorelSpace X] in
/-- Every ball centred at a point of the support has positive mass. -/
theorem measure_ball_pos_of_mem_support {μ : Measure X} {x : X} (hx : x ∈ μ.support) {r : ℝ}
    (hr : 0 < r) : 0 < μ (ball x r) :=
  (Measure.mem_support_iff_forall x).1 hx _ (ball_mem_nhds x hr)

/-- A number below every `ENNReal.ofReal t` with `0 < t < s` is below `ENNReal.ofReal s`. -/
private theorem ofReal_le_of_forall_lt {d : ℝ≥0∞} {s : ℝ}
    (h : ∀ t : ℝ, 0 < t → t < s → ENNReal.ofReal t ≤ d) : ENNReal.ofReal s ≤ d := by
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (s - 1 / ((n : ℝ) + 1))) atTop
      (𝓝 (ENNReal.ofReal s)) := by
    refine ENNReal.tendsto_ofReal ?_
    have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using tendsto_const_nhds.sub h0
  refine le_of_tendsto' hlim fun n => ?_
  rcases le_or_gt (s - 1 / ((n : ℝ) + 1)) 0 with hle | hpos
  · rw [ENNReal.ofReal_eq_zero.2 hle]
    exact bot_le
  · refine h _ hpos ?_
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- A number below every `ENNReal.ofReal u` with `s < u` is below `ENNReal.ofReal s`. -/
private theorem le_ofReal_of_forall_gt {d : ℝ≥0∞} {s : ℝ}
    (h : ∀ u : ℝ, s < u → d ≤ ENNReal.ofReal u) : d ≤ ENNReal.ofReal s := by
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (s + 1 / ((n : ℝ) + 1))) atTop
      (𝓝 (ENNReal.ofReal s)) := by
    refine ENNReal.tendsto_ofReal ?_
    have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using tendsto_const_nhds.add h0
  refine ge_of_tendsto' hlim fun n => h _ ?_
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

/-- Below the crossover exponent, `c r^u ≤ r^t` for all small `r`. -/
private theorem eventually_const_mul_rpow_le_rpow {t u : ℝ} (htu : t < u) (c : ℝ) :
    ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), c * r ^ u ≤ r ^ t := by
  have h1 : Tendsto (fun r : ℝ => r ^ (t - u)) (𝓝[>] (0 : ℝ)) atTop := by
    refine ((tendsto_rpow_atTop (show (0 : ℝ) < u - t by linarith)).comp
      tendsto_inv_nhdsGT_zero).congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with r hr
    have hr0 : (0 : ℝ) < r := hr
    simp only [Function.comp_apply]
    rw [Real.inv_rpow hr0.le, ← Real.rpow_neg hr0.le, neg_sub]
  filter_upwards [h1.eventually_ge_atTop c, eventually_mem_nhdsWithin] with r hr hr0
  have hr0' : (0 : ℝ) < r := hr0
  calc c * r ^ u ≤ r ^ (t - u) * r ^ u :=
        mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg hr0'.le u)
    _ = r ^ t := by rw [← Real.rpow_add hr0']; ring_nf

/-- A real power and a natural power of a non-negative base commute. -/
private theorem rpow_natCast_comm {x : ℝ} (hx : 0 ≤ x) (t : ℝ) (n : ℕ) :
    (x ^ t) ^ n = (x ^ n) ^ t := by
  rw [← Real.rpow_natCast (x ^ t) n, ← Real.rpow_natCast x n, ← Real.rpow_mul hx,
    ← Real.rpow_mul hx, mul_comm]

omit [BorelSpace X] in
/-- Two-sided power bounds for the ball masses at `x` make both local dimensions equal to the
exponent: the logarithms of the two bounds differ from `p log r` by a constant. -/
theorem localDim_eq_of_measure_ball_bounds {μ : Measure X} [IsFiniteMeasure μ] {x : X}
    {p c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (h : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), ENNReal.ofReal (c₀ * r ^ p) ≤ μ (ball x r) ∧
      μ (ball x r) ≤ ENNReal.ofReal (c₁ * r ^ p)) :
    lowerLocalDim μ x = ENNReal.ofReal p ∧ upperLocalDim μ x = ENNReal.ofReal p := by
  have hsq : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      p + Real.log c₁ / Real.log r ≤ Real.log (μ (ball x r)).toReal / Real.log r ∧
        Real.log (μ (ball x r)).toReal / Real.log r ≤ p + Real.log c₀ / Real.log r := by
    filter_upwards [h, eventually_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_lt_nhds (zero_lt_one' ℝ))] with r hr hr0 hr1
    have hr0' : (0 : ℝ) < r := hr0
    have hlogr : Real.log r < 0 := Real.log_neg hr0' hr1
    have hfin : μ (ball x r) ≠ ⊤ := measure_ne_top _ _
    have hrp : (0 : ℝ) < r ^ p := Real.rpow_pos_of_pos hr0' p
    have hlow : c₀ * r ^ p ≤ (μ (ball x r)).toReal := by
      have h1 := ENNReal.toReal_mono hfin hr.1
      rwa [ENNReal.toReal_ofReal (by positivity)] at h1
    have hup : (μ (ball x r)).toReal ≤ c₁ * r ^ p := by
      have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hr.2
      rwa [ENNReal.toReal_ofReal (by positivity)] at h2
    have hm : 0 < (μ (ball x r)).toReal := lt_of_lt_of_le (by positivity) hlow
    have hlog1 : Real.log c₀ + p * Real.log r ≤ Real.log (μ (ball x r)).toReal := by
      have := Real.log_le_log (by positivity) hlow
      rwa [Real.log_mul hc₀.ne' hrp.ne', Real.log_rpow hr0'] at this
    have hlog2 : Real.log (μ (ball x r)).toReal ≤ Real.log c₁ + p * Real.log r := by
      have := Real.log_le_log hm hup
      rwa [Real.log_mul hc₁.ne' hrp.ne', Real.log_rpow hr0'] at this
    have hlogr0 : Real.log r ≠ 0 := hlogr.ne
    constructor
    · rw [le_div_iff_of_neg hlogr,
        show (p + Real.log c₁ / Real.log r) * Real.log r = p * Real.log r + Real.log c₁ by
          rw [add_mul, div_mul_cancel₀ _ hlogr0]]
      linarith
    · rw [div_le_iff_of_neg hlogr,
        show (p + Real.log c₀ / Real.log r) * Real.log r = p * Real.log r + Real.log c₀ by
          rw [add_mul, div_mul_cancel₀ _ hlogr0]]
      linarith
  have hlim : ∀ c : ℝ, Tendsto (fun r : ℝ => p + Real.log c / Real.log r) (𝓝[>] (0 : ℝ)) (𝓝 p) := by
    intro c
    have := (tendsto_const_nhds (x := Real.log c) (f := 𝓝[>] (0 : ℝ))).div_atBot
      Real.tendsto_log_nhdsGT_zero
    simpa using tendsto_const_nhds.add this
  have key : Tendsto (fun r : ℝ => Real.log (μ (ball x r)).toReal / Real.log r) (𝓝[>] (0 : ℝ))
      (𝓝 p) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim c₁) (hlim c₀) (hsq.mono fun _ hr => hr.1)
      (hsq.mono fun _ hr => hr.2)
  exact ⟨(ENNReal.tendsto_ofReal key).liminf_eq, (ENNReal.tendsto_ofReal key).limsup_eq⟩

omit [BorelSpace X] in
/-- If the lower local dimension at `x` is above `t`, then `μ(B(x, r)) ≤ r^t` for all small `r`. -/
theorem eventually_measure_ball_le_rpow {μ : Measure X} [IsFiniteMeasure μ] {x : X} {t : ℝ}
    (h : ENNReal.ofReal t < lowerLocalDim μ x) :
    ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), μ (ball x r) ≤ ENNReal.ofReal (r ^ t) := by
  filter_upwards [eventually_lt_of_lt_liminf h, eventually_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_lt_nhds (zero_lt_one' ℝ))] with r hr hr0 hr1
  have hr0' : (0 : ℝ) < r := hr0
  rcases eq_or_ne (μ (ball x r)) 0 with h0 | h0
  · simp [h0]
  have hfin : μ (ball x r) ≠ ⊤ := measure_ne_top _ _
  have hm : 0 < (μ (ball x r)).toReal := ENNReal.toReal_pos h0 hfin
  have hlogr : Real.log r < 0 := Real.log_neg hr0' hr1
  have h1 : Real.log (μ (ball x r)).toReal < t * Real.log r := by
    rw [← lt_div_iff_of_neg hlogr]
    by_contra hcon
    exact absurd (ENNReal.ofReal_le_ofReal (not_lt.1 hcon)) (not_le.2 hr)
  have h2 : (μ (ball x r)).toReal < r ^ t := by
    have := Real.exp_lt_exp.2 h1
    rwa [Real.exp_log hm, ← Real.log_rpow hr0', Real.exp_log (Real.rpow_pos_of_pos hr0' t)] at this
  calc μ (ball x r) = ENNReal.ofReal (μ (ball x r)).toReal := (ENNReal.ofReal_toReal hfin).symm
    _ ≤ ENNReal.ofReal (r ^ t) := ENNReal.ofReal_le_ofReal h2.le

omit [BorelSpace X] in
/-- If the lower local dimension at a support point `x` is below `t`, then `r^t ≤ μ(B(x, r))` for
arbitrarily small `r`. -/
theorem frequently_rpow_le_measure_ball {μ : Measure X} [IsFiniteMeasure μ] {x : X}
    (hx : x ∈ μ.support) {t : ℝ} (h : lowerLocalDim μ x < ENNReal.ofReal t) :
    ∃ᶠ r : ℝ in 𝓝[>] (0 : ℝ), ENNReal.ofReal (r ^ t) ≤ μ (ball x r) := by
  refine ((frequently_lt_of_liminf_lt (h := h)).and_eventually (eventually_mem_nhdsWithin.and
    (nhdsWithin_le_nhds (eventually_lt_nhds (zero_lt_one' ℝ))))).mono ?_
  rintro r ⟨hr, hr0, hr1⟩
  have hr0' : (0 : ℝ) < r := hr0
  have hfin : μ (ball x r) ≠ ⊤ := measure_ne_top _ _
  have hm : 0 < (μ (ball x r)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos_of_mem_support hx hr0').ne' hfin
  have hlogr : Real.log r < 0 := Real.log_neg hr0' hr1
  have h1 : t * Real.log r < Real.log (μ (ball x r)).toReal := by
    rw [← div_lt_iff_of_neg hlogr]
    by_contra hcon
    exact absurd (ENNReal.ofReal_le_ofReal (not_lt.1 hcon)) (not_le.2 hr)
  have h2 : r ^ t < (μ (ball x r)).toReal := by
    have := Real.exp_lt_exp.2 h1
    rwa [Real.exp_log hm, ← Real.log_rpow hr0', Real.exp_log (Real.rpow_pos_of_pos hr0' t)] at this
  calc ENNReal.ofReal (r ^ t) ≤ ENNReal.ofReal (μ (ball x r)).toReal :=
        ENNReal.ofReal_le_ofReal h2.le
    _ = μ (ball x r) := ENNReal.ofReal_toReal hfin

/-! ## Proposition 5.14 (`thm:local-dimension-bounds`) -/

/-- Proposition 5.14 (`thm:local-dimension-bounds`): a lower bound on the lower local dimension on
a set of positive mass bounds its Hausdorff dimension from below, and an upper bound on the lower
local dimension bounds it from above. -/
theorem local_dimension_bounds (μ : Measure X) [IsFiniteMeasure μ] {s : ℝ} (hs : 0 ≤ s)
    {A : Set X} (hAsupp : A ⊆ μ.support) :
    (0 < μ A → (∀ x ∈ A, ENNReal.ofReal s ≤ lowerLocalDim μ x) → ENNReal.ofReal s ≤ dimH A) ∧
      ((∀ x ∈ A, lowerLocalDim μ x ≤ ENNReal.ofReal s) → dimH A ≤ ENNReal.ofReal s) := by
  constructor
  · -- The lower bound, from the mass distribution principle.
    intro hμA hlow
    refine ofReal_le_of_forall_lt fun t ht0 hts => ?_
    set F : ℕ → Set X := fun n => {x | x ∈ A ∧ ∀ r : ℝ, 0 < r → r < 1 / ((n : ℝ) + 1) →
      μ (ball x r) ≤ ENNReal.ofReal (r ^ t)} with hFdef
    have hAF : A ⊆ ⋃ n, F n := by
      intro x hx
      have hlt : ENNReal.ofReal t < lowerLocalDim μ x :=
        ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht0.le).2 hts).trans_le (hlow x hx)
      obtain ⟨u, hu, hsub⟩ :=
        mem_nhdsGT_iff_exists_Ioo_subset.1 (eventually_measure_ball_le_rpow hlt)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < u from hu)
      exact mem_iUnion.2 ⟨n, hx, fun r hr hrn => hsub ⟨hr, hrn.trans hn⟩⟩
    obtain ⟨n, hn⟩ : ∃ n, 0 < μ (F n) := by
      by_contra hcon
      have h0 : ∀ n, μ (F n) = 0 := fun n =>
        le_antisymm (not_lt.1 (not_exists.1 hcon n)) bot_le
      exact hμA.ne' (le_antisymm (((measure_mono hAF).trans (measure_iUnion_le F)).trans
        (by simp [h0])) bot_le)
    -- A uniform ball bound on `F n`, with a large constant covering the radii above `1/(n+1)`.
    set δ : ℝ := 1 / ((n : ℝ) + 1) with hδdef
    have hδ : 0 < δ := by positivity
    set Y : ℝ≥0∞ := ENNReal.ofReal (δ ^ t) with hYdef
    have hY0 : Y ≠ 0 := by
      simp only [hYdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact Real.rpow_pos_of_pos hδ t
    have hYtop : Y ≠ ⊤ := ENNReal.ofReal_ne_top
    set K : ℝ≥0∞ := μ univ / Y with hKdef
    have hK : K ≠ ⊤ := by
      simp only [hKdef]
      exact (ENNReal.div_lt_top (measure_ne_top μ univ) hY0).ne
    set C : ℝ≥0 := max 1 K.toNNReal with hCdef
    have hC1 : (1 : ℝ≥0) ≤ C := le_max_left _ _
    have hCK : K ≤ (C : ℝ≥0∞) := by
      rw [← ENNReal.coe_toNNReal hK]
      exact_mod_cast le_max_right _ _
    have hball : ∀ x ∈ F n, ∀ r : ℝ, 0 < r → μ (ball x r) ≤ C * ENNReal.ofReal r ^ t := by
      intro x hx r hr
      rcases lt_or_ge r δ with hlt | hge
      · calc μ (ball x r) ≤ ENNReal.ofReal (r ^ t) := hx.2 r hr hlt
          _ = ENNReal.ofReal r ^ t := (ENNReal.ofReal_rpow_of_pos hr).symm
          _ ≤ C * ENNReal.ofReal r ^ t := le_mul_of_one_le_left' (by exact_mod_cast hC1)
      · calc μ (ball x r) ≤ μ univ := measure_mono (subset_univ _)
          _ = K * Y := (ENNReal.div_mul_cancel hY0 hYtop).symm
          _ ≤ C * ENNReal.ofReal r ^ t := by
              refine mul_le_mul' hCK ?_
              rw [hYdef, ENNReal.ofReal_rpow_of_pos hr]
              exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hδ.le hge ht0.le)
    exact ((mass_distribution μ ht0 (ne_of_gt (lt_of_lt_of_le zero_lt_one hC1)) hball).2 hn).trans
      (dimH_mono fun y hy => hy.1)
  · -- The upper bound, from the density comparison.
    intro hup
    refine le_ofReal_of_forall_gt fun u hu => ?_
    have hu0 : 0 < u := hs.trans_lt hu
    set t : ℝ := (s + u) / 2 with htdef
    have hst : s < t := by simp only [htdef]; linarith
    have htu : t < u := by simp only [htdef]; linarith
    have ht0 : 0 < t := hs.trans_lt hst
    have hdens : ∀ c : ℝ≥0, ∀ x ∈ A, (c : ℝ≥0∞) ≤
        limsup (fun r : ℝ => μ (ball x r) / ENNReal.ofReal r ^ u) (𝓝[>] 0) := by
      intro c x hx
      have hfr := frequently_rpow_le_measure_ball (hAsupp hx)
        ((hup x hx).trans_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs).2 hst))
      refine le_limsup_of_frequently_le ((hfr.and_eventually
        (eventually_mem_nhdsWithin.and (eventually_const_mul_rpow_le_rpow htu c))).mono ?_)
      rintro r ⟨h1, h2, h3⟩
      have hr0 : (0 : ℝ) < r := h2
      rw [ENNReal.le_div_iff_mul_le
        (Or.inl (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hr0) ENNReal.ofReal_ne_top).ne')
        (Or.inl (ENNReal.rpow_ne_top_of_nonneg hu0.le ENNReal.ofReal_ne_top))]
      calc (c : ℝ≥0∞) * ENNReal.ofReal r ^ u = ENNReal.ofReal ((c : ℝ) * r ^ u) := by
            rw [ENNReal.ofReal_rpow_of_pos hr0, ← ENNReal.ofReal_coe_nnreal,
              ← ENNReal.ofReal_mul c.coe_nonneg]
        _ ≤ ENNReal.ofReal (r ^ t) := ENNReal.ofReal_le_ofReal h3
        _ ≤ μ (ball x r) := h1
    have hH : μH[u] A = 0 := by
      have htop : (2 : ℝ≥0∞) ^ u * μ univ ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hu0.le ENNReal.ofNat_ne_top)
          (measure_ne_top μ univ)
      have hbound : ∀ᶠ n : ℕ in atTop, μH[u] A ≤ 2 ^ u * μ univ / (n : ℝ≥0∞) := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        have := (density_comparison μ hu0 A (c := (n : ℝ≥0))
          (by exact_mod_cast Nat.one_le_iff_ne_zero.1 hn)).2 (hdens _)
        simpa using this
      have hlim : Tendsto (fun n : ℕ => 2 ^ u * μ univ / (n : ℝ≥0∞)) atTop (𝓝 0) := by
        simp only [div_eq_mul_inv]
        simpa using ENNReal.Tendsto.const_mul (a := 2 ^ u * μ univ)
          ENNReal.tendsto_inv_nat_nhds_zero (Or.inr htop)
      exact le_antisymm (ge_of_tendsto hlim hbound) bot_le
    exact dimH_le_of_hausdorffMeasure_ne_top (d := u.toNNReal) (s := A)
      (by rw [Real.coe_toNNReal u hu0.le, hH]; exact ENNReal.zero_ne_top)

/-! ## Definition 5.15 (`def:upper-regularity-dimension`) -/

/-- The two-scale mass bound `μ(B(x, R)) ≤ C (R/r)^t μ(B(x, r))` of Definition 5.15. -/
def UpperRegularityDimLE (μ : Measure X) (t : ℝ) : Prop :=
  ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ x ∈ μ.support, ∀ r R : ℝ, 0 < r → r < R →
    μ (ball x R) ≤ C * ENNReal.ofReal ((R / r) ^ t) * μ (ball x r)

/-- Definition 5.15 (`def:upper-regularity-dimension`): the upper regularity dimension, also called
the Assouad dimension of a measure. -/
def upperRegularityDim (μ : Measure X) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : UpperRegularityDimLE μ (t : ℝ)), (t : ℝ≥0∞)

/-- Definition 5.15 (`def:upper-regularity-dimension`): a doubling measure. -/
def IsDoublingMeasure (μ : Measure X) : Prop :=
  ∃ D : ℝ≥0, 1 ≤ D ∧ ∀ x ∈ μ.support, ∀ r : ℝ, 0 < r → μ (ball x (2 * r)) ≤ D * μ (ball x r)

/-! ## Proposition 5.16 (`thm:doubling-measure-dimension`) -/

omit [BorelSpace X] in
/-- Proposition 5.16 (`thm:doubling-measure-dimension`): a finite Borel measure is doubling if and
only if its upper regularity dimension is finite. The zero measure has empty support, so both sides
hold trivially. -/
theorem doubling_measure_dimension (μ : Measure X) [IsFiniteMeasure μ] :
    IsDoublingMeasure μ ↔ upperRegularityDim μ ≠ ⊤ := by
  classical
  constructor
  · -- Iterating the doubling inequality `n` times, with `2^{n-1} < R/r ≤ 2^n`.
    rintro ⟨D, hD1, hD⟩
    have hD1' : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
    have hD0 : (0 : ℝ) < D := zero_lt_one.trans_le hD1'
    have hl2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    set t : ℝ := Real.log D / Real.log 2 with htdef
    have ht0 : 0 ≤ t := div_nonneg (Real.log_nonneg hD1') (Real.log_pos one_lt_two).le
    have h2t : (2 : ℝ) ^ t = D := by
      rw [Real.rpow_def_of_pos two_pos,
        show Real.log 2 * t = Real.log D by rw [htdef]; field_simp, Real.exp_log hD0]
    have hiter : ∀ x ∈ μ.support, ∀ (n : ℕ) (r : ℝ), 0 < r →
        μ (ball x (2 ^ n * r)) ≤ (D : ℝ≥0∞) ^ n * μ (ball x r) := by
      intro x hx n
      induction n with
      | zero => intro r _; simp
      | succ n ih =>
        intro r hr
        have hrn : (0 : ℝ) < 2 ^ n * r := by positivity
        rw [show (2 : ℝ) ^ (n + 1) * r = 2 * (2 ^ n * r) by ring]
        calc μ (ball x (2 * (2 ^ n * r))) ≤ D * μ (ball x (2 ^ n * r)) := hD x hx _ hrn
          _ ≤ (D : ℝ≥0∞) * ((D : ℝ≥0∞) ^ n * μ (ball x r)) := by gcongr; exact ih r hr
          _ = (D : ℝ≥0∞) ^ (n + 1) * μ (ball x r) := by ring
    have hURD : UpperRegularityDimLE μ t := by
      refine ⟨D, hD1, fun x hx r R hr hrR => ?_⟩
      have hRr : (1 : ℝ) < R / r := (one_lt_div hr).2 hrR
      have hex : ∃ n : ℕ, R / r ≤ 2 ^ n := by
        obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (R / r) (by norm_num : (1 : ℝ) < 2)
        exact ⟨n, hn.le⟩
      have hk' : R / r ≤ 2 ^ Nat.find hex := Nat.find_spec hex
      have hk0' : Nat.find hex ≠ 0 := by
        intro h0
        rw [h0, pow_zero] at hk'
        linarith
      obtain ⟨k, hk, hk0, hprev⟩ :
          ∃ k : ℕ, R / r ≤ 2 ^ k ∧ k ≠ 0 ∧ (2 : ℝ) ^ (k - 1) < R / r :=
        ⟨Nat.find hex, hk', hk0', not_le.1 (Nat.find_min hex (by omega))⟩
      have h2k : (2 : ℝ) ^ k < 2 * (R / r) := by
        have hsucc : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [hsucc]
        linarith
      have hDk : (D : ℝ≥0∞) ^ k ≤ D * ENNReal.ofReal ((R / r) ^ t) := by
        have hreal : (D : ℝ) ^ k ≤ (D : ℝ) * (R / r) ^ t :=
          calc (D : ℝ) ^ k = ((2 : ℝ) ^ k) ^ t := by
                rw [← h2t, rpow_natCast_comm (by norm_num : (0 : ℝ) ≤ 2)]
            _ ≤ (2 * (R / r)) ^ t := Real.rpow_le_rpow (by positivity) h2k.le ht0
            _ = (D : ℝ) * (R / r) ^ t := by
                rw [Real.mul_rpow (by norm_num) (by positivity), h2t]
        calc (D : ℝ≥0∞) ^ k = ENNReal.ofReal ((D : ℝ) ^ k) := by
              rw [← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_pow]
          _ ≤ ENNReal.ofReal ((D : ℝ) * (R / r) ^ t) := ENNReal.ofReal_le_ofReal hreal
          _ = D * ENNReal.ofReal ((R / r) ^ t) := by
              rw [ENNReal.ofReal_mul D.coe_nonneg, ENNReal.ofReal_coe_nnreal]
      calc μ (ball x R) ≤ μ (ball x (2 ^ k * r)) :=
            measure_mono (ball_subset_ball ((div_le_iff₀ hr).1 hk))
        _ ≤ (D : ℝ≥0∞) ^ k * μ (ball x r) := hiter x hx k r hr
        _ ≤ D * ENNReal.ofReal ((R / r) ^ t) * μ (ball x r) := by gcongr
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top
      (iInf_le_of_le t.toNNReal (iInf_le_of_le (by rwa [Real.coe_toNNReal t ht0]) le_rfl))
  · -- An admissible exponent with `R = 2r` gives doubling.
    intro h
    have hex : ∃ t : ℝ≥0, UpperRegularityDimLE μ (t : ℝ) := by
      by_contra hcon
      exact h (iInf_eq_top.2 fun t =>
        iInf_eq_top.2 fun ht => absurd ht (not_exists.1 hcon t))
    obtain ⟨t, C, hC1, hC⟩ := hex
    refine ⟨C * (2 : ℝ≥0) ^ (t : ℝ),
      one_le_mul_of_one_le_of_one_le hC1 (NNReal.one_le_rpow one_le_two t.coe_nonneg),
      fun x hx r hr => ?_⟩
    have hcoe : ((C * (2 : ℝ≥0) ^ (t : ℝ) : ℝ≥0) : ℝ≥0∞)
        = C * ENNReal.ofReal ((2 : ℝ) ^ (t : ℝ)) := by
      rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ t.coe_nonneg,
        ← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hcoe]
    have h2 : 2 * r / r = 2 := by field_simp
    have := hC x hx r (2 * r) hr (by linarith)
    rwa [h2] at this

omit [MetricSpace X] [BorelSpace X] in
/-- Counting by mass: if the sets `B y` for `y ∈ S` are pairwise disjoint measurable subsets of a
set `A` of finite measure, each of mass at least `m / K`, then `S` has at most `K μ(A) / m`
elements. -/
private theorem encard_mul_le_measure_of_disjoint {μ : Measure X} {S A : Set X} {B : X → Set X}
    {m K : ℝ≥0∞} (hm : m ≠ 0) (hK : K ≠ ⊤) (hA : μ A ≠ ⊤)
    (hmeas : ∀ y ∈ S, MeasurableSet (B y)) (hdisj : S.PairwiseDisjoint B)
    (hsub : ∀ y ∈ S, B y ⊆ A) (hle : ∀ y ∈ S, m ≤ K * μ (B y)) :
    (S.encard : ℝ≥0∞) * m ≤ K * μ A := by
  have hKA : K * μ A ≠ ⊤ := ENNReal.mul_ne_top hK hA
  have key : ∀ T : Finset X, ↑T ⊆ S → (T.card : ℝ≥0∞) * m ≤ K * μ A := by
    intro T hT
    calc (T.card : ℝ≥0∞) * m
        = ∑ _y ∈ T, m := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ y ∈ T, K * μ (B y) := Finset.sum_le_sum fun y hy => hle y (hT hy)
      _ = K * μ (⋃ y ∈ T, B y) := by
          rw [measure_biUnion_finset (hdisj.subset hT) fun y hy => hmeas y (hT hy), Finset.mul_sum]
      _ ≤ K * μ A := by gcongr; exact iUnion₂_subset fun y hy => hsub y (hT hy)
  rcases S.finite_or_infinite with hfin | hinf
  · rw [hfin.encard_eq_coe_toFinset_card, ENat.toENNReal_coe]
    exact key hfin.toFinset (by simp)
  · obtain ⟨n, hn⟩ :=
      ENNReal.exists_nat_gt (r := K * μ A / m) (by simp [ENNReal.div_eq_top, hm, hKA])
    obtain ⟨T, hTS, hTcard⟩ := hinf.exists_subset_card_eq n
    have h1 := key T hTS
    rw [hTcard] at h1
    exact absurd h1 (not_le.2 ((ENNReal.div_lt_iff (Or.inl hm) (Or.inr hKA)).1 hn))

/-- Proposition 5.16 (`thm:doubling-measure-dimension`): the Assouad dimension of the support is at
most the upper regularity dimension. -/
theorem assouadDim_support_le_upperRegularityDim (μ : Measure X) [IsFiniteMeasure μ] :
    assouadDim μ.support ≤ upperRegularityDim μ := by
  refine le_iInf₂ fun t ht => ?_
  obtain ⟨C, hC1, hC⟩ := ht
  have hCtop : (C : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.coe_nonneg
  set C' : ℝ≥0 := max 1 (C * C * ((8 : ℝ) ^ (t : ℝ)).toNNReal) with hC'def
  have hC'ge : (C : ℝ≥0∞) * C * ENNReal.ofReal ((8 : ℝ) ^ (t : ℝ)) ≤ (C' : ℝ≥0∞) := by
    have hcoe : ((C * C * ((8 : ℝ) ^ (t : ℝ)).toNNReal : ℝ≥0) : ℝ≥0∞)
        = (C : ℝ≥0∞) * C * ENNReal.ofReal ((8 : ℝ) ^ (t : ℝ)) := by
      rw [ENNReal.coe_mul, ENNReal.coe_mul]
      rfl
    rw [← hcoe, ENNReal.coe_le_coe, hC'def]
    exact le_max_right _ _
  have hAss : AssouadDimLE μ.support (t : ℝ) := by
    refine ⟨C', le_max_left _ _, fun x hx r R hr hrR => ?_⟩
    have hR : 0 < R := hr.trans hrR
    have hr2 : 0 < r / 2 := by linarith
    have hm0 : μ (ball x R) ≠ 0 := (measure_ball_pos_of_mem_support hx hR).ne'
    have hmtop : μ (ball x R) ≠ ⊤ := measure_ne_top _ _
    set K : ℝ≥0∞ := (C : ℝ≥0∞) * ENNReal.ofReal ((2 * R / (r / 2)) ^ (t : ℝ)) with hKdef
    have hKtop : K ≠ ⊤ := ENNReal.mul_ne_top hCtop ENNReal.ofReal_ne_top
    set NN : ℝ≥0∞ := (C' : ℝ≥0∞) * ENNReal.ofReal ((R / r) ^ (t : ℝ)) with hNNdef
    have hNNtop : NN ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
    -- The product of the two ratio bounds, at the centre `x` and at a separated point.
    have hNeq : K * ((C : ℝ≥0∞) * ENNReal.ofReal ((2 * R / R) ^ (t : ℝ)))
        = (C : ℝ≥0∞) * C * ENNReal.ofReal ((8 : ℝ) ^ (t : ℝ))
          * ENNReal.ofReal ((R / r) ^ (t : ℝ)) := by
      have h4 : 2 * R / (r / 2) = 4 * (R / r) := by field_simp; ring
      have h2 : 2 * R / R = 2 := by field_simp
      rw [hKdef, h4, h2, Real.mul_rpow (by norm_num) (by positivity),
        ENNReal.ofReal_mul (by positivity), show (8 : ℝ) = 4 * 2 by norm_num,
        Real.mul_rpow (by norm_num) (by norm_num), ENNReal.ofReal_mul (by positivity)]
      ring
    -- Every `r`-separated family in `F ∩ B(x, R)` is small.
    have hSN : ∀ S ⊆ μ.support ∩ ball x R, Metric.IsSeparated ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S →
        (S.encard : ℝ≥0∞) ≤ NN := by
      intro S hS hsepS
      refine (ENNReal.mul_le_mul_iff_left hm0 hmtop).1 ?_
      calc (S.encard : ℝ≥0∞) * μ (ball x R) ≤ K * μ (ball x (2 * R)) := by
            refine encard_mul_le_measure_of_disjoint (B := fun y => ball y (r / 2)) hm0 hKtop
              (measure_ne_top _ _) (fun _ _ => measurableSet_ball) ?_ ?_ ?_
            · intro y hy z hz hyz
              have h := hsepS hy hz hyz
              rw [show ((r.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal r from rfl, edist_dist,
                ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr.le] at h
              exact Metric.ball_disjoint_ball (by linarith)
            · intro y hy z hz
              have h1 : dist y x < R := mem_ball.1 (hS hy).2
              have h2 : dist z y < r / 2 := mem_ball.1 hz
              have h3 : dist z x ≤ dist z y + dist y x := dist_triangle z y x
              exact mem_ball.2 (by linarith)
            · intro y hy
              have hsubball : ball x R ⊆ ball y (2 * R) := by
                intro z hz
                have h1 : dist y x < R := mem_ball.1 (hS hy).2
                have h2 : dist z x < R := mem_ball.1 hz
                have h3 : dist z y ≤ dist z x + dist x y := dist_triangle z x y
                rw [dist_comm x y] at h3
                exact mem_ball.2 (by linarith)
              exact (measure_mono hsubball).trans
                (hC y (hS hy).1 (r / 2) (2 * R) hr2 (by linarith))
        _ ≤ K * ((C : ℝ≥0∞) * ENNReal.ofReal ((2 * R / R) ^ (t : ℝ)) * μ (ball x R)) := by
            gcongr
            exact hC x hx R (2 * R) hR (by linarith)
        _ = K * ((C : ℝ≥0∞) * ENNReal.ofReal ((2 * R / R) ^ (t : ℝ))) * μ (ball x R) := by ring
        _ = (C : ℝ≥0∞) * C * ENNReal.ofReal ((8 : ℝ) ^ (t : ℝ))
              * ENNReal.ofReal ((R / r) ^ (t : ℝ)) * μ (ball x R) := by rw [hNeq]
        _ ≤ NN * μ (ball x R) := by rw [hNNdef]; gcongr
    -- Pass from separated families to the covering number.
    set n : ℕ := ⌊NN.toReal⌋₊ with hndef
    have hnNN : (n : ℝ≥0∞) ≤ NN := by
      rw [← ENNReal.ofReal_toReal hNNtop, ← ENNReal.ofReal_natCast n]
      exact ENNReal.ofReal_le_ofReal (Nat.floor_le ENNReal.toReal_nonneg)
    have hpack : Metric.packingNumber r.toNNReal (μ.support ∩ ball x R) ≤ (n : ℕ∞) := by
      simp only [Metric.packingNumber]
      refine iSup₂_le fun S hS => iSup_le fun hsepS => ?_
      have h := hSN S hS hsepS
      rcases S.finite_or_infinite with hfin | hinf
      · rw [hfin.encard_eq_coe_toFinset_card] at h ⊢
        rw [Nat.cast_le, hndef]
        refine Nat.le_floor ?_
        have h2 := ENNReal.toReal_mono hNNtop h
        rwa [ENat.toENNReal_coe, ENNReal.toReal_natCast] at h2
      · rw [hinf.encard_eq, ENat.toENNReal_top] at h
        exact absurd (top_le_iff.1 h) hNNtop
    calc ((Metric.externalCoveringNumber r.toNNReal (μ.support ∩ ball x R) : ℕ∞) : ℝ≥0∞)
        ≤ ((Metric.packingNumber r.toNNReal (μ.support ∩ ball x R) : ℕ∞) : ℝ≥0∞) :=
          ENat.toENNReal_mono
            ((Metric.externalCoveringNumber_le_coveringNumber _ _).trans
              (Metric.coveringNumber_le_packingNumber _ _))
      _ ≤ ((n : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_mono hpack
      _ ≤ NN := by rwa [ENat.toENNReal_coe]
  exact iInf₂_le t hAss

/-- Proposition 5.16 (`thm:doubling-measure-dimension`): a compactly supported Ahlfors `s`-regular
measure has upper regularity dimension `s`, and all its local dimensions equal `s`. -/
theorem upperRegularityDim_of_isAhlforsRegular {μ : Measure X} [IsFiniteMeasure μ] {s : ℝ}
    {E : Set X} {C : ℝ≥0} (hμ : IsAhlforsRegular μ s E C) (hE : IsCompact E) :
    upperRegularityDim μ = ENNReal.ofReal s ∧
      ∀ x ∈ E, lowerLocalDim μ x = ENNReal.ofReal s ∧ upperLocalDim μ x = ENNReal.ofReal s := by
  have hs : 0 < s := hμ.pos
  have hCpos : (0 : ℝ) < C := by exact_mod_cast zero_lt_one.trans_le hμ.one_le
  have hpow_pos : ∀ a : ℝ, 0 < a → ENNReal.ofReal a ^ s ≠ 0 := fun a ha =>
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 ha) ENNReal.ofReal_ne_top).ne'
  have hpow_top : ∀ a : ℝ, ENNReal.ofReal a ^ s ≠ ∞ := fun _ =>
    (ENNReal.rpow_lt_top_of_nonneg hs.le ENNReal.ofReal_ne_top).ne
  have hEb : Bornology.IsBounded E := hE.isBounded
  set d : ℝ := Metric.diam E with hddef
  have hd0 : 0 < d := Metric.diam_pos hμ.nontrivial hEb
  have hediam : ediam E = ENNReal.ofReal d := (ENNReal.ofReal_toReal hEb.ediam_ne_top).symm
  have hμE : μ E ≠ ∞ := (hμ.measure_lt_top_of_isCompact hE).ne
  have hμle : ∀ A : Set X, μ A ≤ μ E := fun A =>
    (measure_mono (subset_univ _)).trans_eq (by rw [← hμ.measure_inter univ, univ_inter])
  -- An upper mass bound at every radius, with the total mass taking over above the diameter.
  set C₁ : ℝ≥0∞ := max C (μ E / ENNReal.ofReal d ^ s) with hC₁def
  have hC₁top : C₁ ≠ ∞ :=
    (max_lt ENNReal.coe_lt_top (ENNReal.div_lt_top hμE (hpow_pos d hd0))).ne
  have hupper : ∀ y ∈ E, ∀ ρ : ℝ, 0 < ρ → μ (ball y ρ) ≤ C₁ * ENNReal.ofReal ρ ^ s := by
    intro y hy ρ hρ
    rcases le_or_gt ρ d with hρd | hρd
    · refine (hμ.measure_ball_le y hy ρ hρ
        (by rw [hediam]; exact ENNReal.ofReal_le_ofReal hρd)).trans ?_
      gcongr
      exact le_max_left _ _
    · calc μ (ball y ρ) ≤ μ E := hμle _
        _ = μ E / ENNReal.ofReal d ^ s * ENNReal.ofReal d ^ s :=
            (ENNReal.div_mul_cancel (hpow_pos d hd0) (hpow_top d)).symm
        _ ≤ C₁ * ENNReal.ofReal ρ ^ s :=
            mul_le_mul' (le_max_right _ _)
              (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hρd.le) hs.le)
  set C' : ℝ≥0 := max 1 (C₁ * C).toNNReal with hC'def
  have hC'ge : C₁ * C ≤ (C' : ℝ≥0∞) := by
    calc C₁ * C = ((C₁ * C).toNNReal : ℝ≥0∞) :=
          (ENNReal.coe_toNNReal (ENNReal.mul_ne_top hC₁top ENNReal.coe_ne_top)).symm
      _ ≤ (C' : ℝ≥0∞) := by rw [hC'def]; exact_mod_cast le_max_right _ _
  have hURD : UpperRegularityDimLE μ s := by
    refine ⟨C', le_max_left _ _, fun x hx r R hr hrR => ?_⟩
    rw [hμ.support_eq] at hx
    have hR : 0 < R := hr.trans hrR
    have hX1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((R / r) ^ s) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow ((one_le_div hr).2 hrR.le) hs.le)
    rcases le_or_gt r d with hrd | hrd
    · -- Below the diameter the two Ahlfors bounds give the ratio bound.
      have h1 : ENNReal.ofReal r ^ s ≤ C * μ (ball x r) :=
        hμ.le_measure_ball x hx r hr (by rw [hediam]; exact ENNReal.ofReal_le_ofReal hrd)
      have h3 : ENNReal.ofReal ((R / r) ^ s) * ENNReal.ofReal r ^ s = ENNReal.ofReal R ^ s := by
        rw [ENNReal.ofReal_rpow_of_pos hr, ENNReal.ofReal_rpow_of_pos hR,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) s),
          ← Real.mul_rpow (by positivity) hr.le, div_mul_cancel₀ _ hr.ne']
      calc μ (ball x R) ≤ C₁ * ENNReal.ofReal R ^ s := hupper x hx R hR
        _ = C₁ * ENNReal.ofReal ((R / r) ^ s) * ENNReal.ofReal r ^ s := by rw [← h3]; ring
        _ ≤ C₁ * ENNReal.ofReal ((R / r) ^ s) * (C * μ (ball x r)) := by gcongr
        _ = C₁ * C * ENNReal.ofReal ((R / r) ^ s) * μ (ball x r) := by ring
        _ ≤ C' * ENNReal.ofReal ((R / r) ^ s) * μ (ball x r) := by gcongr
    · -- Above the diameter the ball already carries the whole mass.
      have hEsub : E ⊆ ball x r := fun y hy =>
        mem_ball.2 ((Metric.dist_le_diam_of_mem hEb hy hx).trans_lt hrd)
      calc μ (ball x R) ≤ μ E := hμle _
        _ ≤ μ (ball x r) := measure_mono hEsub
        _ ≤ C' * ENNReal.ofReal ((R / r) ^ s) * μ (ball x r) := by
            refine le_mul_of_one_le_left' ?_
            calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
              _ ≤ (C' : ℝ≥0∞) * ENNReal.ofReal ((R / r) ^ s) := by
                  gcongr
                  exact_mod_cast le_max_left 1 (C₁ * C).toNNReal
  -- The support inequality and Theorem 5.12 give the matching lower bound.
  have hlow : ENNReal.ofReal s ≤ upperRegularityDim μ := by
    have h1 := assouadDim_support_le_upperRegularityDim μ
    rw [hμ.support_eq, (ahlfors_dimensions hμ hE).2.2.2.2] at h1
    exact h1
  refine ⟨le_antisymm (iInf₂_le s.toNNReal (by rwa [Real.coe_toNNReal s hs.le])) hlow,
    fun x hx => ?_⟩
  -- Taking logarithms of the two ball bounds gives the local dimensions.
  refine localDim_eq_of_measure_ball_bounds (c₀ := (C : ℝ)⁻¹) (c₁ := (C : ℝ))
    (inv_pos.2 hCpos) hCpos ?_
  filter_upwards [eventually_pos_ofReal_le_ediam hμ.nontrivial] with r hr
  obtain ⟨hr0, hrE⟩ := hr
  constructor
  · have h1 := hμ.le_measure_ball x hx r hr0 hrE
    rw [ENNReal.ofReal_rpow_of_pos hr0] at h1
    calc ENNReal.ofReal ((C : ℝ)⁻¹ * r ^ s) = ENNReal.ofReal (r ^ s) / C := by
          rw [show (C : ℝ)⁻¹ * r ^ s = r ^ s / (C : ℝ) by ring,
            ENNReal.ofReal_div_of_pos hCpos, ENNReal.ofReal_coe_nnreal]
      _ ≤ μ (ball x r) := ENNReal.div_le_of_le_mul (by rwa [mul_comm] at h1)
  · calc μ (ball x r) ≤ C * ENNReal.ofReal r ^ s := hμ.measure_ball_le x hx r hr0 hrE
      _ = ENNReal.ofReal ((C : ℝ) * r ^ s) := by
          rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal,
            ENNReal.ofReal_rpow_of_pos hr0]

/-! ## Example 5.17 (`ex:measure-dimension-exceeds-ambient`) -/

/-- Example 5.17 (`ex:measure-dimension-exceeds-ambient`): on `[0, 1]` the measure with density
`(a+1)x^a` has local dimension `a + 1` at the origin and `1` elsewhere, and its upper regularity
dimension is at least `a + 1`, although its support has Assouad dimension one. -/
theorem measure_dimension_exceeds_ambient {a : ℝ} (ha : 0 < a) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ μ.support = Icc 0 1 ∧
      lowerLocalDim μ 0 = ENNReal.ofReal (a + 1) ∧ upperLocalDim μ 0 = ENNReal.ofReal (a + 1) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, lowerLocalDim μ x = 1 ∧ upperLocalDim μ x = 1) ∧
      ENNReal.ofReal (a + 1) ≤ upperRegularityDim μ ∧ assouadDim (Icc (0 : ℝ) 1) = 1 := by
  have ha1 : (0 : ℝ) < a + 1 := by linarith
  set f : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal ((a + 1) * y ^ a) with hfdef
  have hfmeas : Measurable f :=
    ENNReal.continuous_ofReal.measurable.comp
      (measurable_const.mul (Real.continuous_rpow_const ha.le).measurable)
  set μ : Measure ℝ := (volume.withDensity f).restrict (Icc 0 1) with hμdef
  have hμapply : ∀ A : Set ℝ, MeasurableSet A → μ A = ∫⁻ y in A ∩ Icc 0 1, f y := by
    intro A hA
    rw [hμdef, Measure.restrict_apply hA, withDensity_apply _ (hA.inter measurableSet_Icc)]
  have hupperInt : ∀ (A : Set ℝ) (c : ℝ), MeasurableSet A → (∀ y ∈ A, (a + 1) * y ^ a ≤ c) →
      ∫⁻ y in A, f y ≤ ENNReal.ofReal c * volume A := fun A c hA hc =>
    (setLIntegral_mono' hA fun y hy => ENNReal.ofReal_le_ofReal (hc y hy)).trans
      (setLIntegral_const A (ENNReal.ofReal c)).le
  have hlowerInt : ∀ (A : Set ℝ) (c : ℝ), MeasurableSet A → (∀ y ∈ A, c ≤ (a + 1) * y ^ a) →
      ENNReal.ofReal c * volume A ≤ ∫⁻ y in A, f y := fun A c hA hc =>
    (setLIntegral_const A (ENNReal.ofReal c)).ge.trans
      (setLIntegral_mono' hA fun y hy => ENNReal.ofReal_le_ofReal (hc y hy))
  -- The measure is finite: the density is at most `a + 1` on `[0, 1]`.
  have hfin : μ univ ≠ ⊤ := by
    rw [hμapply univ MeasurableSet.univ, univ_inter]
    refine ne_top_of_le_ne_top ?_ (hupperInt (Icc 0 1) (a + 1) measurableSet_Icc fun y hy => ?_)
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    · have h1 : y ^ a ≤ 1 := Real.rpow_le_one hy.1 hy.2 ha.le
      nlinarith
  haveI hμfin : IsFiniteMeasure μ := ⟨hfin.lt_top⟩
  -- The support is the whole interval.
  have hsupp : μ.support = Icc 0 1 := by
    refine Subset.antisymm ?_ ?_
    · refine Measure.support_restrict_subset.trans ?_
      rw [closure_Icc]
      exact inter_subset_left
    · intro x hx
      rw [Measure.mem_support_iff_forall]
      intro U hU
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
      refine lt_of_lt_of_le ?_ (measure_mono hball)
      have hcd : max 0 (x - ε) < min 1 (x + ε) :=
        max_lt (lt_min one_pos (by linarith [hx.1])) (lt_min (by linarith [hx.2]) (by linarith))
      set c : ℝ := max 0 (x - ε) with hcdef
      set d : ℝ := min 1 (x + ε) with hddef
      have hc0 : 0 ≤ c := le_max_left _ _
      have hcm : c < (c + d) / 2 := by linarith
      have hmd : (c + d) / 2 < d := by linarith
      have hm0 : 0 < (c + d) / 2 := lt_of_le_of_lt hc0 hcm
      have hsub : Ico ((c + d) / 2) d ⊆ ball x ε ∩ Icc 0 1 := by
        rintro y ⟨hy1, hy2⟩
        have hcx : x - ε ≤ c := le_max_right _ _
        have hd1 : d ≤ 1 := min_le_left _ _
        have hdx : d ≤ x + ε := min_le_right _ _
        refine ⟨?_, ⟨by linarith, by linarith⟩⟩
        rw [Real.ball_eq_Ioo]
        exact ⟨by linarith, by linarith⟩
      have hvol : 0 < volume (Ico ((c + d) / 2) d) := by
        rw [Real.volume_Ico]
        exact ENNReal.ofReal_pos.2 (by linarith)
      have hmass : 0 < μ (Ico ((c + d) / 2) d) := by
        rw [hμapply _ measurableSet_Ico,
          inter_eq_self_of_subset_left (hsub.trans inter_subset_right)]
        refine lt_of_lt_of_le ?_ (hlowerInt _ ((a + 1) * ((c + d) / 2) ^ a) measurableSet_Ico
          fun y hy => ?_)
        · exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (by positivity)).ne' hvol.ne'
        · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hm0.le hy.1 ha.le) ha1.le
      exact hmass.trans_le (measure_mono (hsub.trans inter_subset_left))
  -- The ball masses at the origin.
  have hball0 : ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ENNReal.ofReal ((a + 1) * (1 / 2 : ℝ) ^ (a + 1) * ρ ^ (a + 1)) ≤ μ (ball 0 ρ) ∧
        μ (ball 0 ρ) ≤ ENNReal.ofReal ((a + 1) * ρ ^ (a + 1)) := by
    intro ρ hρ hρ1
    constructor
    · have hsub : Ico (ρ / 2) ρ ⊆ ball (0 : ℝ) ρ ∩ Icc 0 1 := by
        rintro y ⟨hy1, hy2⟩
        refine ⟨?_, ⟨by linarith, by linarith⟩⟩
        rw [Real.ball_eq_Ioo]
        exact ⟨by linarith, by linarith⟩
      have hkey : (a + 1) * (ρ / 2) ^ a * (ρ / 2)
          = (a + 1) * (1 / 2 : ℝ) ^ (a + 1) * ρ ^ (a + 1) := by
        rw [mul_assoc, ← Real.rpow_add_one (by positivity) a,
          show ρ / 2 = ρ * (1 / 2 : ℝ) by ring, Real.mul_rpow hρ.le (by norm_num)]
        ring
      calc ENNReal.ofReal ((a + 1) * (1 / 2 : ℝ) ^ (a + 1) * ρ ^ (a + 1))
          = ENNReal.ofReal ((a + 1) * (ρ / 2) ^ a) * volume (Ico (ρ / 2) ρ) := by
            rw [Real.volume_Ico, ← ENNReal.ofReal_mul (by positivity), ← hkey]
            congr 1
            ring
        _ ≤ ∫⁻ y in Ico (ρ / 2) ρ, f y :=
            hlowerInt _ _ measurableSet_Ico fun y hy =>
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hy.1 ha.le) ha1.le
        _ = μ (Ico (ρ / 2) ρ) := by
            rw [hμapply _ measurableSet_Ico,
              inter_eq_self_of_subset_left (hsub.trans inter_subset_right)]
        _ ≤ μ (ball 0 ρ) := measure_mono (hsub.trans inter_subset_left)
    · have hsub2 : ball (0 : ℝ) ρ ∩ Icc 0 1 ⊆ Ico 0 ρ := by
        rintro y ⟨hy1, hy2⟩
        rw [Real.ball_eq_Ioo] at hy1
        exact ⟨hy2.1, by linarith [hy1.2]⟩
      calc μ (ball 0 ρ) = ∫⁻ y in ball (0 : ℝ) ρ ∩ Icc 0 1, f y := hμapply _ measurableSet_ball
        _ ≤ ∫⁻ y in Ico 0 ρ, f y := lintegral_mono_set hsub2
        _ ≤ ENNReal.ofReal ((a + 1) * ρ ^ a) * volume (Ico 0 ρ) :=
            hupperInt _ _ measurableSet_Ico fun y hy =>
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy.1 hy.2.le ha.le) ha1.le
        _ = ENNReal.ofReal ((a + 1) * ρ ^ (a + 1)) := by
            rw [Real.volume_Ico, sub_zero, ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [mul_assoc, ← Real.rpow_add_one hρ.ne' a]
  -- The local dimension at the origin.
  have hlocal0 : lowerLocalDim μ 0 = ENNReal.ofReal (a + 1) ∧
      upperLocalDim μ 0 = ENNReal.ofReal (a + 1) := by
    refine localDim_eq_of_measure_ball_bounds (c₀ := (a + 1) * (1 / 2 : ℝ) ^ (a + 1))
      (c₁ := a + 1) (mul_pos ha1 (Real.rpow_pos_of_pos (by norm_num) _)) ha1 ?_
    filter_upwards [eventually_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_lt_nhds (zero_lt_one' ℝ))] with ρ hρ0 hρ1
    exact hball0 ρ hρ0 hρ1
  -- The local dimensions in the interior.
  have hlocalx : ∀ x ∈ Ioo (0 : ℝ) 1, lowerLocalDim μ x = 1 ∧ upperLocalDim μ x = 1 := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have h := localDim_eq_of_measure_ball_bounds (μ := μ) (x := x) (p := 1)
      (c₀ := 2 * (a + 1) * (x / 2) ^ a) (c₁ := 2 * (a + 1))
      (by positivity) (by linarith) ?_
    · simpa using h
    · filter_upwards [eventually_mem_nhdsWithin,
        nhdsWithin_le_nhds (eventually_lt_nhds (lt_min (by linarith : (0:ℝ) < x / 2)
          (by linarith : (0:ℝ) < 1 - x)))] with ρ hρ0 hρlt
      have hρ : (0 : ℝ) < ρ := hρ0
      have hρx : ρ < x / 2 := hρlt.trans_le (min_le_left _ _)
      have hρ1 : ρ < 1 - x := hρlt.trans_le (min_le_right _ _)
      have hsub : ball x ρ ⊆ Icc (0 : ℝ) 1 := by
        rw [Real.ball_eq_Ioo]
        rintro y ⟨hy1, hy2⟩
        exact ⟨by linarith, by linarith⟩
      have hμball : μ (ball x ρ) = ∫⁻ y in ball x ρ, f y := by
        rw [hμapply _ measurableSet_ball, inter_eq_self_of_subset_left hsub]
      have hvol : volume (ball x ρ) = ENNReal.ofReal (2 * ρ) := by
        rw [Real.ball_eq_Ioo, Real.volume_Ioo]
        congr 1
        ring
      have hmem : ∀ y ∈ ball x ρ, x / 2 ≤ y ∧ y ≤ 1 := by
        intro y hy
        rw [Real.ball_eq_Ioo] at hy
        exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
      rw [hμball]
      constructor
      · calc ENNReal.ofReal (2 * (a + 1) * (x / 2) ^ a * ρ ^ (1 : ℝ))
            = ENNReal.ofReal ((a + 1) * (x / 2) ^ a) * volume (ball x ρ) := by
              rw [hvol, ← ENNReal.ofReal_mul (by positivity)]
              congr 1
              rw [Real.rpow_one]
              ring
          _ ≤ ∫⁻ y in ball x ρ, f y :=
              hlowerInt _ _ measurableSet_ball fun y hy =>
                mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow (by positivity) (hmem y hy).1 ha.le) ha1.le
      · calc ∫⁻ y in ball x ρ, f y ≤ ENNReal.ofReal (a + 1) * volume (ball x ρ) :=
              hupperInt _ _ measurableSet_ball fun y hy => by
                have h1 : y ^ a ≤ 1 :=
                  Real.rpow_le_one (by linarith [(hmem y hy).1]) (hmem y hy).2 ha.le
                nlinarith
          _ = ENNReal.ofReal (2 * (a + 1) * ρ ^ (1 : ℝ)) := by
              rw [hvol, ← ENNReal.ofReal_mul ha1.le]
              congr 1
              rw [Real.rpow_one]
              ring
  -- The upper regularity dimension is at least `a + 1`.
  have hURD : ENNReal.ofReal (a + 1) ≤ upperRegularityDim μ := by
    refine le_iInf₂ fun t ht => ?_
    obtain ⟨C, hC1, hC⟩ := ht
    have h0supp : (0 : ℝ) ∈ μ.support := by rw [hsupp]; exact ⟨le_refl 0, zero_le_one⟩
    have hball1 : 0 < μ (ball (0 : ℝ) 1) := measure_ball_pos_of_mem_support h0supp one_pos
    have hta : a + 1 ≤ (t : ℝ) := by
      by_contra hcon
      have he : (0 : ℝ) < a + 1 - (t : ℝ) := by linarith [not_le.1 hcon]
      have hlimK : Tendsto
          (fun ρ : ℝ => ENNReal.ofReal ((C : ℝ) * (a + 1) * ρ ^ (a + 1 - (t : ℝ))))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have h1 : Tendsto (fun ρ : ℝ => ρ ^ (a + 1 - (t : ℝ))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have h2 := (Real.continuousAt_rpow_const (0 : ℝ) (a + 1 - (t : ℝ))
            (Or.inr he.le)).tendsto
          rw [Real.zero_rpow he.ne'] at h2
          exact h2.mono_left nhdsWithin_le_nhds
        have h3 : Tendsto (fun ρ : ℝ => (C : ℝ) * (a + 1) * ρ ^ (a + 1 - (t : ℝ)))
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa using tendsto_const_nhds.mul h1
        simpa using ENNReal.tendsto_ofReal h3
      have hev : ∀ᶠ ρ : ℝ in 𝓝[>] (0 : ℝ),
          μ (ball (0 : ℝ) 1) ≤ ENNReal.ofReal ((C : ℝ) * (a + 1) * ρ ^ (a + 1 - (t : ℝ))) := by
        filter_upwards [eventually_mem_nhdsWithin,
          nhdsWithin_le_nhds (eventually_lt_nhds (zero_lt_one' ℝ))] with ρ hρ0 hρ1
        have hρ : (0 : ℝ) < ρ := hρ0
        have hpow : (1 / ρ) ^ (t : ℝ) * ρ ^ (a + 1) = ρ ^ (a + 1 - (t : ℝ)) := by
          rw [one_div, Real.inv_rpow hρ.le, ← Real.rpow_neg hρ.le, ← Real.rpow_add hρ]
          congr 1
          ring
        calc μ (ball (0 : ℝ) 1)
            ≤ C * ENNReal.ofReal ((1 / ρ) ^ (t : ℝ)) * μ (ball 0 ρ) := hC 0 h0supp ρ 1 hρ hρ1
          _ ≤ C * ENNReal.ofReal ((1 / ρ) ^ (t : ℝ))
                * ENNReal.ofReal ((a + 1) * ρ ^ (a + 1)) := by
              gcongr
              exact (hball0 ρ hρ hρ1).2
          _ = ENNReal.ofReal ((C : ℝ) * (a + 1) * ρ ^ (a + 1 - (t : ℝ))) := by
              rw [show (C : ℝ≥0∞) = ENNReal.ofReal (C : ℝ) from ENNReal.ofReal_coe_nnreal.symm,
                ← ENNReal.ofReal_mul C.coe_nonneg, ← ENNReal.ofReal_mul (by positivity), ← hpow]
              congr 1
              ring
      exact absurd (ge_of_tendsto hlimK hev) (not_le.2 hball1)
    calc ENNReal.ofReal (a + 1) ≤ ENNReal.ofReal (t : ℝ) := ENNReal.ofReal_le_ofReal hta
      _ = (t : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
  -- The support has Assouad dimension one.
  have hassouad : assouadDim (Icc (0 : ℝ) 1) = 1 := by
    refine le_antisymm ?_ ?_
    · simpa using assouadDim_le_finrank (Icc (0 : ℝ) 1)
    · have h1 := upperBoxDim_le_assouadDim (E := Icc (0 : ℝ) 1) isCompact_Icc.isBounded
        (nonempty_Icc.2 zero_le_one)
      rwa [(box_interval (show (0 : ℝ) < 1 by norm_num)).2] at h1
  exact ⟨μ, hμfin, hsupp, hlocal0.1, hlocal0.2, hlocalx, hURD, hassouad⟩

end GeometricMeasureTheory
