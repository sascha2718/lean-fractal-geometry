/-
# Section 3.4: Densities and s-sets

Upper and lower densities of a set with respect to `𝓗^s`, `s`-sets, regular and irregular points,
and the density bounds for an `s`-set. Densities are normalised by `(2r)^s`, the `s`-th power of the
diameter of a Euclidean ball. Everything holds in an arbitrary metric space.

| Notes | Lean declaration | Location |
|---|---|---|
| Theorem 3.11 (Lebesgue density theorem) | `ae_tendsto_measure_inter_ball_div` | here |
| Theorem 3.11, closed balls | `Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet` | `Mathlib/MeasureTheory/Covering/Besicovitch.lean` |
| Definition 3.12 (upper and lower densities) | `upperDensity`, `lowerDensity` | here |
| Definition 3.13 (`s`-set) | `IsSSet` | here |
| Every `s`-set has dimension `s` | `dimH_of_hausdorffMeasure_ne_zero_ne_top` | `Mathlib/Topology/MetricSpace/HausdorffDimension.lean` |
| Exercise 3.14 | `ahlfors_hausdorff` | `GeometricMeasureTheory.Covering.AhlforsRegular` |
| Definition 3.15 (regular and irregular points and sets) | `IsRegularPoint`, `IsRegularSSet`, `IsIrregularSSet` | here |
| Proposition 3.17 (density bounds) | `density_bounds` | here |
| Theorem 3.19 (Marstrand) for `0 < s < 1` | `noninteger_density_of_lt_one` | `GeometricMeasureTheory.Covering.NonintegerDensity` |
-/
import GeometricMeasureTheory.Covering.DensityComparison

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

/-! ## Theorem 3.11 (`thm:lebesgue-density`)

Mathlib proves this as `Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet`, with closed
balls, for every locally finite measure on a finite-dimensional real normed space. For an additive
Haar measure open and closed balls have the same measure, since spheres are null. -/

section Lebesgue

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  [FiniteDimensional ℝ F]

/-- For an additive Haar measure, `E ∩ B(x, r)` and `E ∩ B̄(x, r)` have the same measure when
`r ≠ 0`, since spheres are null. -/
theorem measure_inter_ball_eq_inter_closedBall (μ : Measure F) [μ.IsAddHaarMeasure] (E : Set F)
    (x : F) {r : ℝ} (hr : r ≠ 0) : μ (E ∩ ball x r) = μ (E ∩ closedBall x r) := by
  refine le_antisymm (measure_mono (inter_subset_inter_right _ ball_subset_closedBall)) ?_
  calc μ (E ∩ closedBall x r) ≤ μ (E ∩ ball x r ∪ sphere x r) := by
        refine measure_mono ?_
        rw [← ball_union_sphere, inter_union_distrib_left]
        exact union_subset_union_right _ inter_subset_right
    _ ≤ μ (E ∩ ball x r) + μ (sphere x r) := measure_union_le _ _
    _ = μ (E ∩ ball x r) := by rw [Measure.addHaar_sphere_of_ne_zero μ x hr, add_zero]

/-- Theorem 3.11 (`thm:lebesgue-density`) for a measurable set and an additive Haar measure, with
open balls. -/
theorem ae_tendsto_measure_inter_ball_div (μ : Measure F) [μ.IsAddHaarMeasure] {E : Set F}
    (hE : MeasurableSet E) :
    ∀ᵐ x ∂μ, Tendsto (fun r : ℝ => μ (E ∩ ball x r) / μ (ball x r)) (𝓝[>] 0)
      (𝓝 (E.indicator 1 x)) := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet μ hE] with x hx
  refine hx.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [measure_inter_ball_eq_inter_closedBall μ E x hr.ne', ← univ_inter (ball x r),
    measure_inter_ball_eq_inter_closedBall μ univ x hr.ne', univ_inter]

end Lebesgue

example (d : ℕ) {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      Tendsto (fun r : ℝ => volume (E ∩ ball x r) / volume (ball x r)) (𝓝[>] 0)
        (𝓝 (E.indicator 1 x)) :=
  ae_tendsto_measure_inter_ball_div _ hE

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-! ## Definitions 3.12, 3.13 and 3.15 -/

/-- Definition 3.12 (`def:densities`): the upper density
`limsup_{r → 0} 𝓗^s(E ∩ B(x, r)) / (2r)^s`. -/
def upperDensity (s : ℝ) (E : Set X) (x : X) : ℝ≥0∞ :=
  limsup (fun r : ℝ => μH[s] (E ∩ ball x r) / ENNReal.ofReal (2 * r) ^ s) (𝓝[>] 0)

/-- Definition 3.12 (`def:densities`): the lower density
`liminf_{r → 0} 𝓗^s(E ∩ B(x, r)) / (2r)^s`. -/
def lowerDensity (s : ℝ) (E : Set X) (x : X) : ℝ≥0∞ :=
  liminf (fun r : ℝ => μH[s] (E ∩ ball x r) / ENNReal.ofReal (2 * r) ^ s) (𝓝[>] 0)

/-- Definition 3.13 (`def:s-set`): a Borel set of positive finite `𝓗^s` measure. -/
def IsSSet (s : ℝ) (E : Set X) : Prop :=
  MeasurableSet E ∧ 0 < μH[s] E ∧ μH[s] E < ∞

/-- Definition 3.15 (`def:density-regularity`): `x` is a regular point of `E` if the density of `E`
at `x` exists and equals one. -/
def IsRegularPoint (s : ℝ) (E : Set X) (x : X) : Prop :=
  lowerDensity s E x = 1 ∧ upperDensity s E x = 1

/-- Definition 3.15 (`def:density-regularity`): an `s`-set is regular if `𝓗^s`-almost every point
of it is regular. -/
def IsRegularSSet (s : ℝ) (E : Set X) : Prop :=
  IsSSet s E ∧ ∀ᵐ x ∂μH[s], x ∈ E → IsRegularPoint s E x

/-- Definition 3.15 (`def:density-regularity`): an `s`-set is irregular if `𝓗^s`-almost every
point of it is irregular. -/
def IsIrregularSSet (s : ℝ) (E : Set X) : Prop :=
  IsSSet s E ∧ ∀ᵐ x ∂μH[s], x ∈ E → ¬IsRegularPoint s E x

/-! ## Basic properties of the densities -/

/-- The lower density is at most the upper density. -/
theorem lowerDensity_le_upperDensity (s : ℝ) (E : Set X) (x : X) :
    lowerDensity s E x ≤ upperDensity s E x :=
  liminf_le_limsup

/-- The upper density is monotone in the set. -/
theorem upperDensity_mono (s : ℝ) {E F : Set X} (h : E ⊆ F) (x : X) :
    upperDensity s E x ≤ upperDensity s F x :=
  limsup_le_limsup (Eventually.of_forall fun _ =>
    ENNReal.div_le_div_right (measure_mono (inter_subset_inter_left _ h)) _)

/-- The lower density is monotone in the set. -/
theorem lowerDensity_mono (s : ℝ) {E F : Set X} (h : E ⊆ F) (x : X) :
    lowerDensity s E x ≤ lowerDensity s F x :=
  liminf_le_liminf (Eventually.of_forall fun _ =>
    ENNReal.div_le_div_right (measure_mono (inter_subset_inter_left _ h)) _)

/-- `𝓗^s(E ∩ B(x, r))` is the mass of `B(x, r)` for the restriction of `𝓗^s` to `E`. -/
theorem hausdorffMeasure_inter_ball_eq_restrict (s : ℝ) (E : Set X) (x : X) (r : ℝ) :
    μH[s] (E ∩ ball x r) = μH[s].restrict E (ball x r) := by
  rw [Measure.restrict_apply measurableSet_ball, inter_comm]

/-- The ball ratio `m / r^s` of `density_comparison` is `2^s` times the density ratio
`m / (2r)^s`. -/
theorem div_ofReal_rpow_eq_two_rpow_mul (m : ℝ≥0∞) (s r : ℝ) :
    m / ENNReal.ofReal r ^ s = 2 ^ s * (m / ENNReal.ofReal (2 * r) ^ s) := by
  have h0 : (2 : ℝ≥0∞) ^ s ≠ 0 := by simp [ENNReal.rpow_eq_zero_iff]
  have ht : (2 : ℝ≥0∞) ^ s ≠ ∞ := by simp [ENNReal.rpow_eq_top_iff]
  rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
    ENNReal.mul_rpow_of_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top,
    ← ENNReal.mul_div_mul_left m (ENNReal.ofReal r ^ s) h0 ht, mul_div_assoc]

/-- If a measure `ν` gives small balls about `x` the same mass as `𝓗^s` restricted to `E`, then
the upper ball ratio of `ν` at `x` used in `density_comparison` is `2^s` times the upper density
of `E` at `x`. -/
theorem limsup_measure_ball_div_eq_two_rpow_mul_upperDensity {s : ℝ} {E : Set X} {x : X}
    {ν : Measure X} (hν : ∀ᶠ r in 𝓝[>] (0 : ℝ), ν (ball x r) = μH[s] (E ∩ ball x r)) :
    limsup (fun r : ℝ => ν (ball x r) / ENNReal.ofReal r ^ s) (𝓝[>] 0) =
      2 ^ s * upperDensity s E x := by
  rw [upperDensity, ← ENNReal.limsup_const_mul_of_ne_top (by simp [ENNReal.rpow_eq_top_iff])]
  refine limsup_congr ?_
  filter_upwards [hν] with r hr
  rw [hr, div_ofReal_rpow_eq_two_rpow_mul]

/-- The upper ball ratio of `𝓗^s` restricted to `E` used in `density_comparison` is `2^s` times
the upper density of `E`. -/
theorem limsup_restrict_ball_div_eq_two_rpow_mul_upperDensity (s : ℝ) (E : Set X) (x : X) :
    limsup (fun r : ℝ => μH[s].restrict E (ball x r) / ENNReal.ofReal r ^ s) (𝓝[>] 0) =
      2 ^ s * upperDensity s E x :=
  limsup_measure_ball_div_eq_two_rpow_mul_upperDensity (Eventually.of_forall fun r =>
    (hausdorffMeasure_inter_ball_eq_restrict s E x r).symm)

omit [MeasurableSpace X] [BorelSpace X] in
/-- If `U` is a neighbourhood of `x`, then `B(x, r) ⊆ U` for all sufficiently small `r > 0`. -/
theorem eventually_ball_subset_of_mem_nhds {x : X} {U : Set X} (hU : U ∈ 𝓝 x) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ball x r ⊆ U := by
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hε)] with r (hr : r < ε)
  exact (ball_subset_ball hr.le).trans hεU

/-! ## Proposition 3.17 (`thm:density-bounds`) -/

/-- Countable reduction for upper bounds: if the sets `{P ∧ t < f}` are null for all `t > b`, then
`f ≤ b` almost everywhere on `P`. -/
private theorem ae_le_of_forall_lt_null {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {P : α → Prop} {f : α → ℝ≥0∞} {b : ℝ≥0∞}
    (h : ∀ t : ℝ≥0, b < t → μ {x | P x ∧ (t : ℝ≥0∞) < f x} = 0) :
    ∀ᵐ x ∂μ, P x → f x ≤ b := by
  have hq : ∀ q : ℚ, ∀ᵐ x ∂μ, P x → b < Real.toNNReal q → f x ≤ Real.toNNReal q := by
    intro q
    by_cases hbq : b < Real.toNNReal q
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (h _ hbq)] with x hx hP _
      exact not_lt.1 fun hlt => hx ⟨hP, hlt⟩
    · exact Eventually.of_forall fun x _ hb => absurd hb hbq
  filter_upwards [ae_all_iff.2 hq] with x hx hP
  by_contra! hlt
  obtain ⟨q, -, hbq, hqf⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
  exact (hx q hP hbq).not_gt hqf

/-- Countable reduction for lower bounds: if the sets `{P ∧ f ≤ a}` are null for all `0 < a < b`,
then `b ≤ f` almost everywhere on `P`. -/
private theorem ae_ge_of_forall_gt_null {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {P : α → Prop} {f : α → ℝ≥0∞} {b : ℝ≥0∞}
    (h : ∀ a : ℝ≥0, 0 < a → (a : ℝ≥0∞) < b → μ {x | P x ∧ f x ≤ a} = 0) :
    ∀ᵐ x ∂μ, P x → b ≤ f x := by
  have hq : ∀ q : ℚ,
      ∀ᵐ x ∂μ, P x → f x < Real.toNNReal q → (Real.toNNReal q : ℝ≥0∞) < b → False := by
    intro q
    by_cases hqb : 0 < Real.toNNReal q ∧ (Real.toNNReal q : ℝ≥0∞) < b
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (h _ hqb.1 hqb.2)] with x hx hP hfq _
      exact hx ⟨hP, hfq.le⟩
    · refine Eventually.of_forall fun x _ hfq hqb' => hqb ⟨?_, hqb'⟩
      exact ENNReal.coe_pos.1 (pos_of_gt hfq)
  filter_upwards [ae_all_iff.2 hq] with x hx hP
  by_contra! hlt
  obtain ⟨q, -, hfq, hqb⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
  exact hx q hP hfq hqb

/-- If `m ≤ m * c` with `m` finite and `c < 1`, then `m = 0`. -/
private theorem eq_zero_of_le_mul_of_lt_one {m c : ℝ≥0∞} (hm : m ≠ ∞) (hc : c < 1)
    (h : m ≤ m * c) : m = 0 := by
  by_contra h0
  exact (ENNReal.mul_lt_mul_right h0 hm hc).trans_eq (mul_one m) |>.not_ge h

/-- Proposition 3.17 (`thm:density-bounds`): for a Borel set `E` of finite `𝓗^s` measure,
(1) both densities vanish at `𝓗^s`-almost every point outside `E`, and (2)
`2^{-s} ≤ D̄^s(E, x) ≤ 1` at `𝓗^s`-almost every point of `E`. -/
theorem density_bounds {s : ℝ} (hs : 0 < s) {E : Set X} (hE : MeasurableSet E)
    (hfin : μH[s] E ≠ ∞) :
    (∀ᵐ x ∂μH[s], x ∉ E → lowerDensity s E x = 0 ∧ upperDensity s E x = 0) ∧
      ∀ᵐ x ∂μH[s], x ∈ E → (2 : ℝ≥0∞)⁻¹ ^ s ≤ upperDensity s E x ∧ upperDensity s E x ≤ 1 := by
  set μ := μH[s].restrict E with hμ
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 hfin
  have h2 : (2 : ℝ≥0∞) ^ s ≠ 0 := by simp [ENNReal.rpow_eq_zero_iff]
  have h2' : (2 : ℝ≥0∞) ^ s ≠ ∞ := by simp [ENNReal.rpow_eq_top_iff]
  have hc : ∀ t : ℝ≥0, (((2 : ℝ≥0) ^ s * t : ℝ≥0) : ℝ≥0∞) = 2 ^ s * t := fun t => by
    rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero two_ne_zero, ENNReal.coe_ofNat]
  have hc0 : ∀ t : ℝ≥0, t ≠ 0 → (2 : ℝ≥0) ^ s * t ≠ 0 := fun t ht =>
    mul_ne_zero (NNReal.rpow_pos two_pos).ne' ht
  have hμA : ∀ A ⊆ E, μ A = μH[s] A := fun A hA => by
    rw [hμ, Measure.restrict_apply' hE, inter_eq_left.2 hA]
  refine ⟨?_, ?_⟩
  · -- Part (1): approximate `E` from inside by closed sets `K`, which small balls about `x ∉ E`
    -- avoid, and apply the second density comparison to `𝓗^s` restricted to `E \ K`.
    have key : ∀ t : ℝ≥0, 0 < t →
        μH[s] {x | x ∉ E ∧ (t : ℝ≥0∞) < upperDensity s E x} = 0 := by
      intro t ht
      set A := {x | x ∉ E ∧ (t : ℝ≥0∞) < upperDensity s E x}
      refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
      rw [zero_add]
      have hεt : (ε : ℝ≥0∞) * t ≠ 0 := by positivity
      obtain ⟨K, hKE, hK, hKε⟩ :=
        hE.exists_isClosed_sdiff_lt (μ := μ) (by rwa [hμA E subset_rfl]) hεt
      rw [hμA _ sdiff_subset] at hKε
      have hA := (density_comparison (μH[s].restrict (E \ K)) hs A (hc0 t ht.ne')).2
        fun x hx => by
          rw [limsup_measure_ball_div_eq_two_rpow_mul_upperDensity, hc]
          · exact mul_le_mul_right hx.2.le _
          · have hxK : Kᶜ ∈ 𝓝 x := hK.isOpen_compl.mem_nhds fun hxK => hx.1 (hKE hxK)
            filter_upwards [eventually_ball_subset_of_mem_nhds hxK] with r hr
            rw [Measure.restrict_apply measurableSet_ball]
            congr 1
            ext y
            exact ⟨fun ⟨hy, hyE, _⟩ => ⟨hyE, hy⟩, fun ⟨hyE, hy⟩ => ⟨hy, hyE, hr hy⟩⟩
      rw [Measure.restrict_apply_univ, hc, ENNReal.mul_div_mul_left _ _ h2 h2'] at hA
      exact hA.trans (ENNReal.div_le_of_le_mul hKε.le)
    filter_upwards [ae_le_of_forall_lt_null (P := fun x => x ∉ E) (b := 0)
      fun t ht => key t (ENNReal.coe_pos.1 ht)] with x hx hxE
    have hup : upperDensity s E x = 0 := nonpos_iff_eq_zero.1 (hx hxE)
    exact ⟨nonpos_iff_eq_zero.1 (hup ▸ lowerDensity_le_upperDensity s E x), hup⟩
  · -- Lower bound in part (2): the first density comparison, with `2^s a < 1`.
    have hlow : ∀ a : ℝ≥0, 0 < a → (a : ℝ≥0∞) < 2⁻¹ ^ s →
        μH[s] {x | x ∈ E ∧ upperDensity s E x ≤ a} = 0 := by
      intro a ha haS
      set A := {x | x ∈ E ∧ upperDensity s E x ≤ a}
      have hA := (density_comparison μ hs A (hc0 a ha.ne')).1 fun x hx => by
        rw [limsup_restrict_ball_div_eq_two_rpow_mul_upperDensity, hc]
        exact mul_le_mul_right hx.2 _
      rw [hμA A fun x hx => hx.1, hc] at hA
      refine eq_zero_of_le_mul_of_lt_one (measure_ne_top_of_subset ?_ hfin) ?_ <|
        (ENNReal.div_le_iff_le_mul (Or.inl ?_) (Or.inl ?_)).1 hA
      · exact fun x hx => hx.1
      · calc (2 : ℝ≥0∞) ^ s * a < 2 ^ s * 2⁻¹ ^ s := ENNReal.mul_lt_mul_right h2 h2' haS
          _ = 1 := by
            rw [← ENNReal.mul_rpow_of_ne_top ENNReal.ofNat_ne_top
                (ENNReal.inv_ne_top.2 two_ne_zero),
              ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, ENNReal.one_rpow]
      · exact mul_ne_zero h2 (ENNReal.coe_ne_zero.2 ha.ne')
      · exact ENNReal.mul_ne_top h2' ENNReal.coe_ne_top
    -- Upper bound in part (2): outer regularity and the second density comparison.
    have hup : ∀ t : ℝ≥0, 1 < t →
        μH[s] {x | x ∈ E ∧ (t : ℝ≥0∞) < upperDensity s E x} = 0 := by
      intro t ht
      set A := {x | x ∈ E ∧ (t : ℝ≥0∞) < upperDensity s E x}
      have hAE : A ⊆ E := fun x hx => hx.1
      have ht0 : t ≠ 0 := (zero_lt_one.trans ht).ne'
      have hle : μH[s] A ≤ μH[s] A / t := by
        refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
        have hεt : (ε : ℝ≥0∞) * t ≠ 0 := by positivity
        obtain ⟨U, hAU, hU, hUA⟩ := Set.exists_isOpen_le_add A μ hεt
        have hA := (density_comparison (μ.restrict U) hs A (hc0 t ht0)).2 fun x hx => by
          rw [limsup_measure_ball_div_eq_two_rpow_mul_upperDensity, hc]
          · exact mul_le_mul_right hx.2.le _
          · filter_upwards [eventually_ball_subset_of_mem_nhds (hU.mem_nhds (hAU hx))]
              with r hr
            rw [Measure.restrict_apply measurableSet_ball, inter_eq_left.2 hr]
            exact (hausdorffMeasure_inter_ball_eq_restrict s E x r).symm
        rw [Measure.restrict_apply_univ, hc, ENNReal.mul_div_mul_left _ _ h2 h2'] at hA
        rw [hμA A hAE] at hUA
        calc μH[s] A ≤ μ U / t := hA
          _ ≤ (μH[s] A + ε * t) / t := ENNReal.div_le_div_right hUA _
          _ = μH[s] A / t + ε := by
            rw [ENNReal.add_div, ENNReal.mul_div_cancel_right (by simpa using ht0)
              ENNReal.coe_ne_top]
      refine eq_zero_of_le_mul_of_lt_one (measure_ne_top_of_subset hAE hfin) ?_
        (by rwa [← div_eq_mul_inv])
      exact ENNReal.inv_lt_one.2 (by exact_mod_cast ht)
    filter_upwards [ae_ge_of_forall_gt_null hlow,
      ae_le_of_forall_lt_null (b := 1) fun t ht => hup t (by exact_mod_cast ht)]
      with x hx₁ hx₂ hxE
    exact ⟨hx₁ hxE, hx₂ hxE⟩

end GeometricMeasureTheory
