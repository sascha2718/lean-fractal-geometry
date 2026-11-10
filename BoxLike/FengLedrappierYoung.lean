module

/-
`PlanarFengLedrappierYoung`, Feng's Theorems 1.2 (ii) and 1.3 (Duke Math. J. 172 (2023),
arXiv:1901.01691v2) in the plane, along his Sections 4 to 6 with `d = 2`, `s = 2`,
`k_1 = k_2 = 1`. With `ν^i_𝐢 = π_* μ_𝐢^{ξ_i}`, `δ_i` its pointwise dimension at `π(𝐢)`,
`c_1 = (h_1 - h_0)/λ_1` and `c_2 = (h_2 - h_1)/λ_2`, the claims are (C1) `δ_2 = 0`, (C2)
`\overline{δ}_i ≤ c_{i+1} + \overline{δ}_{i+1}`, (C3) `\underline{δ}_i ≥ \underline{δ}_{i+1} + ϑ_i`
and Proposition 5.1, `ϑ_0 ≥ c_1`, `ϑ_1 ≥ c_2`; combined downwards they give `δ_{-1} = c_1 + c_2`.
(C1) to (C3) are theorems about nested measurable partitions; Proposition 5.1 comes from the planar
form of Lemma 5.4 (with `ℓ = 1`, no induced map) and Proposition 5.5, Besicovitch differentiation
on the atoms with the weak maximal inequality.

* `LowerLocalDimGe`, `UpperLocalDimLe`, `isExactDim_map_of_ae_hasLocalDim`: pointwise bounds.
* `ae_condMeas_density`: Feng, Lemmas 2.5 (1) and 2.2.
* `ae_lowerLocalDimGe_map_of_condMeas`, `ae_lowerLocalDimGe_condMeas_of_tube`: (C3).
* `ae_upperLocalDimLe_condMeas_of_counting`: (C2).
* `maker_triangular_ergodic`: Maker's theorem in triangular form, Feng, Lemma 2.3.
* `ae_transverseDimGe_of_step`: Feng's (5.6) with `ℓ = 1`.
* `coordTube`, `IsFibreCoordinate`, `ae_tendsto_ratio_coordTube`, `exists_envelope_coordTube`,
  `exists_ballRatio_maximal_constant_of_besicovitch`, `ae_ae_rnDeriv_eq_condMeas`:
  Proposition 5.5 for a coordinate on the atoms.
* `PlanarSystem.slowScale`, `PlanarSystem.transScale`, `PlanarSystem.condMeas_eucTube_step`,
  `PlanarSystem.condMeas_transTube_step`: the planar scalings, Lemmas 5.4 and 4.5 (3).
* `PlanarSystem.tendsto_condMeas_eucTube_ratio`, `PlanarSystem.exists_envelope_eucTube`,
  `PlanarSystem.tendsto_condMeas_transTube_ratio`, `PlanarSystem.exists_envelope_transTube`:
  Proposition 5.5 in the plane.
* `PlanarSystem.FengSteps`, `PlanarSystem.isExactDim_of_fengSteps`, `PlanarSystem.fengSteps`:
  the steps and their combination.
* `planarFengLedrappierYoung_holds`, `fengLedrappierYoung_holds`, `fengLedrappierYoungBar_holds`.
-/
public import BoxLike.LiteraturePlanarFeng
public import BoxLike.Planar.OseledetsTheorem
public import BoxLike.LocalDimBounds
public import BoxLike.FengEntropy
public import BoxLike.Planar.Specialisation
public import BoxLike.Planar.OseledetsTheoremDirection
public import BoxLike.Planar.FengIdentity
public import BoxLike.FurstenbergKesten
public import BoxLike.Planar.OseledetsChoice
public import BoxLike.Planar.FalconerBound
public import ExactOverlaps.SelfSimilar.RadiusInterpolation
public import BoxLike.ConditionalTwoWays
public import BoxLike.ProjectiveLineSystem
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import BoxLike.SMB.Maker
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import ExactOverlaps.SelfSimilar.MeasurableEnvelope

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Metric Set ProbabilityTheory
open scoped ENNReal

universe u

/-! ### Bounds for the pointwise dimensions -/

section LocalDimBounds

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

/-- The lower pointwise dimension of `ν` at `z` is at least `a`:
`liminf_{r ↓ 0} log ν(B(z, r)) / log r ≥ a`, stated without the limit inferior, with closed
balls as in `HasLocalDim`. -/
def LowerLocalDimGe (ν : Measure X) (z : X) (a : ℝ) : Prop :=
  ∀ a' < a, ∀ᶠ r in 𝓝[>] (0 : ℝ), a' ≤ Real.log (ν.real (closedBall z r)) / Real.log r

/-- The upper pointwise dimension of `ν` at `z` is at most `b`:
`limsup_{r ↓ 0} log ν(B(z, r)) / log r ≤ b`, stated without the limit superior. -/
def UpperLocalDimLe (ν : Measure X) (z : X) (b : ℝ) : Prop :=
  ∀ b' > b, ∀ᶠ r in 𝓝[>] (0 : ℝ), Real.log (ν.real (closedBall z r)) / Real.log r ≤ b'

/-- The pointwise dimension exists and equals `d` exactly when the lower pointwise dimension is
at least `d` and the upper one at most `d`. -/
theorem hasLocalDim_iff_lowerLocalDimGe_and_upperLocalDimLe {ν : Measure X} {z : X} {d : ℝ} :
    HasLocalDim ν z d ↔ LowerLocalDimGe ν z d ∧ UpperLocalDimLe ν z d := by
  rw [HasLocalDim, tendsto_order]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun a ha => (h1 a ha).mono fun r hr => hr.le,
      fun b hb => (h2 b hb).mono fun r hr => hr.le⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · obtain ⟨a', haa', ha'd⟩ := exists_between ha
      exact (h1 a' ha'd).mono fun r hr => haa'.trans_le hr
    · obtain ⟨b', hdb', hb'b⟩ := exists_between hb
      exact (h2 b' hdb').mono fun r hr => hr.trans_lt hb'b

/-- An existing pointwise dimension `d` bounds the lower pointwise dimension from below. -/
theorem HasLocalDim.lowerLocalDimGe {ν : Measure X} {z : X} {d : ℝ} (h : HasLocalDim ν z d) :
    LowerLocalDimGe ν z d :=
  (hasLocalDim_iff_lowerLocalDimGe_and_upperLocalDimLe.1 h).1

/-- An existing pointwise dimension `d` bounds the upper pointwise dimension from above. -/
theorem HasLocalDim.upperLocalDimLe {ν : Measure X} {z : X} {d : ℝ} (h : HasLocalDim ν z d) :
    UpperLocalDimLe ν z d :=
  (hasLocalDim_iff_lowerLocalDimGe_and_upperLocalDimLe.1 h).2

end LocalDimBounds

/-! ### Exact dimension of an image measure -/

section Transfer

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

section Measurability

variable [OpensMeasurableSpace X] [SecondCountableTopology X]

/-- The mass `ν(B(z, r))` of a closed ball of fixed radius is a Borel function of the centre. -/
theorem measurable_measure_closedBall_left (ν : Measure X) [SFinite ν] (r : ℝ) :
    Measurable fun z : X => ν (closedBall z r) := by
  have hs : MeasurableSet {p : X × X | dist p.2 p.1 ≤ r} :=
    measurableSet_le (measurable_snd.dist measurable_fst) measurable_const
  have h := measurable_measure_prodMk_left (ν := ν) hs
  convert h using 2 with z
  congr 1

/-- The dyadic information rate `-log ν(B(z, 2^{-n})) / n` of the proof of
`isExactDim_map_of_ae_hasLocalDim`. -/
noncomputable def dyadicRate (ν : Measure X) (z : X) (n : ℕ) : ℝ :=
  -Real.log (ν.real (closedBall z ((1 / 2 : ℝ) ^ n))) / n

/-- The dyadic information rate is a Borel function of the centre. -/
theorem measurable_dyadicRate (ν : Measure X) [IsFiniteMeasure ν] (n : ℕ) :
    Measurable fun z => dyadicRate ν z n := by
  unfold dyadicRate
  simp only [measureReal_def]
  exact ((measurable_measure_closedBall_left ν _).ennreal_toReal.log.neg).div_const _

end Measurability

/-- The dyadic radii tend to `0` from the right. -/
theorem tendsto_half_pow_nhdsGT : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num),
    Eventually.of_forall fun n => pow_pos (by norm_num) n⟩

/-- `-log 2^{-n} / n → log 2`. -/
theorem tendsto_neg_log_half_pow_div :
    Tendsto (fun n : ℕ => -Real.log ((1 / 2 : ℝ) ^ n) / n) atTop (𝓝 (Real.log 2)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [one_div, Real.log_pow, Real.log_inv]
  field_simp

/-- A pointwise dimension `d` gives the dyadic information rate `d log 2`. -/
theorem HasLocalDim.tendsto_dyadicRate {ν : Measure X} {z : X} {d : ℝ}
    (h : HasLocalDim ν z d) :
    Tendsto (fun n => dyadicRate ν z n) atTop (𝓝 (d * Real.log 2)) := by
  have h2 := (h.comp tendsto_half_pow_nhdsGT).mul tendsto_neg_log_half_pow_div
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hl : Real.log ((1 / 2 : ℝ) ^ n) ≠ 0 := by
    simp only [one_div, Real.log_pow, Real.log_inv]
    exact mul_ne_zero hn0 (neg_ne_zero.2 (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne')
  simp only [Function.comp_def, dyadicRate]
  field_simp

/-- Conversely, at a point of the support of a probability measure the dyadic information rate
`d log 2` gives the pointwise dimension `d`, by the interpolation of
`ExactOverlaps.information_radius_limit_of_sampled_rates`. -/
theorem hasLocalDim_of_tendsto_dyadicRate {ν : Measure X} [IsProbabilityMeasure ν] {z : X}
    {d : ℝ} (hpos : ∀ r : ℝ, 0 < r → 0 < ν (closedBall z r))
    (h : Tendsto (fun n => dyadicRate ν z n) atTop (𝓝 (d * Real.log 2))) :
    HasLocalDim ν z d := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hI0 : ∀ t : ℝ, 0 < t → 0 ≤ -Real.log (ν.real (closedBall z t)) := fun t _ =>
    neg_nonneg.2 (Real.log_nonpos measureReal_nonneg measureReal_le_one)
  have hI : AntitoneOn (fun t => -Real.log (ν.real (closedBall z t))) (Ioi 0) := by
    intro s hs t _ hst
    refine neg_le_neg (Real.log_le_log ?_ ?_)
    · exact ENNReal.toReal_pos (hpos s hs).ne' (measure_ne_top _ _)
    · exact measureReal_mono (closedBall_subset_closedBall hst)
  have hh := ExactOverlaps.information_radius_limit_of_sampled_rates
    (r := fun n : ℕ => (1 / 2 : ℝ) ^ n) (fun n => pow_pos (by norm_num) n)
    (pow_right_anti₀ (by norm_num) (by norm_num))
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)) hI0 hI hL h
    tendsto_neg_log_half_pow_div
  rw [mul_div_cancel_right₀ d hL.ne'] at hh
  unfold HasLocalDim
  refine hh.congr' (Eventually.of_forall fun t => ?_)
  simp only [neg_div_neg_eq]

/-- If the pointwise dimension of the image measure `f_* μ` at `f(x)` is `d` for `μ`-almost every
`x`, then `f_* μ` is exact-dimensional with `dim f_* μ = d`. The event is transferred through the
measurable dyadic characterisation, so no measurability of the limit over all radii is used. -/
theorem isExactDim_map_of_ae_hasLocalDim [OpensMeasurableSpace X] [SecondCountableTopology X]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : Ω → X} (hf : Measurable f) {d : ℝ}
    (h : ∀ᵐ x ∂μ, HasLocalDim (μ.map f) (f x) d) : IsExactDim (μ.map f) d := by
  have hS : MeasurableSet {z | Tendsto (fun n => dyadicRate (μ.map f) z n) atTop
      (𝓝 (d * Real.log 2))} :=
    measurableSet_tendsto _ fun n => measurable_dyadicRate (μ.map f) n
  have hrate : ∀ᵐ z ∂(μ.map f),
      Tendsto (fun n => dyadicRate (μ.map f) z n) atTop (𝓝 (d * Real.log 2)) :=
    (ae_map_iff hf.aemeasurable hS).2 (h.mono fun x hx => hx.tendsto_dyadicRate)
  filter_upwards [hrate, ae_forall_measure_closedBall_pos (μ.map f)] with z hz hpos
  exact hasLocalDim_of_tendsto_dyadicRate hpos hz

end Transfer

/-! ### Feng, Lemmas 2.5 (1) and 2.2: density of conditional measures -/

section Fibre

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [HasBesicovitchCovering X]

/-- For finite measures `ν' ≤ ν` with the Besicovitch covering property and radii `r_n → 0⁺`,
`ν'`-almost every `z` has `ν'(B(z, r_n)) ≥ c ν(B(z, r_n))` for all large `n`, with some `c > 0`:
the ratio tends to the Radon–Nikodym derivative `dν'/dν(z)`, which is positive `ν'`-almost
everywhere. -/
theorem ae_exists_mul_le_of_le {ν ν' : Measure X} [IsFiniteMeasure ν] (h : ν' ≤ ν)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝[>] 0)) :
    ∀ᵐ z ∂ν', ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
      ∀ᶠ n in atTop, c * ν (closedBall z (r n)) ≤ ν' (closedBall z (r n)) := by
  have : IsFiniteMeasure ν' := isFiniteMeasure_of_le ν h
  have hac : ν' ≪ ν := Measure.absolutelyContinuous_of_le h
  filter_upwards [hac.ae_le (Besicovitch.ae_tendsto_rnDeriv ν' ν), Measure.rnDeriv_pos hac]
    with z hz hpos
  obtain ⟨c, hc0, hcL⟩ := exists_between hpos
  refine ⟨c, hc0, ne_top_of_lt hcL, ?_⟩
  filter_upwards [(hz.comp hr).eventually (lt_mem_nhds hcL)] with n hn
  by_cases h0 : ν (closedBall z (r n)) = 0
  · rw [h0, mul_zero]
    exact bot_le
  · exact (ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl (measure_ne_top _ _))).1 hn.le

end Fibre

section Kernel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The conditional measures `x ↦ μ_x^ξ` as a Markov kernel on `Ω` with its Borel `σ`-algebra
(they are measurable for the smaller `σ`-algebra `\widehat{ξ}`). -/
noncomputable def condMeasKernel (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Set Ω) :
    Kernel Ω Ω where
  toFun := condMeas μ ξ
  measurable' := Measure.measurable_of_measurable_coe _ fun _ hA =>
    (measurable_condMeas μ ξ hA).mono (saturated_le ξ) le_rfl

/-- The kernel of conditional measures evaluates to the conditional measures. -/
theorem condMeasKernel_apply (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Set Ω) (x : Ω) :
    condMeasKernel μ ξ x = condMeas μ ξ x := rfl

/-- The kernel of conditional measures is a Markov kernel. -/
instance (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Set Ω) :
    IsMarkovKernel (condMeasKernel μ ξ) :=
  ⟨fun x => by rw [condMeasKernel_apply]; infer_instance⟩

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology X]

/-- The mass `μ_y^ξ(A ∩ φ⁻¹B(φy, s))` is a Borel function of `y`. -/
theorem measurable_condMeas_inter_preimage_closedBall (μ : Measure Ω) [IsFiniteMeasure μ]
    (ξ : Ω → Set Ω) {φ : Ω → X} (hφ : Measurable φ) {A : Set Ω} (hA : MeasurableSet A)
    (s : ℝ) : Measurable fun y => condMeas μ ξ y (A ∩ φ ⁻¹' closedBall (φ y) s) := by
  have ht : MeasurableSet {p : Ω × Ω | p.2 ∈ A ∧ dist (φ p.2) (φ p.1) ≤ s} :=
    (measurable_snd hA).inter (measurableSet_le
      ((hφ.comp measurable_snd).dist (hφ.comp measurable_fst)) measurable_const)
  have h := Kernel.measurable_kernel_prodMk_left (κ := condMeasKernel μ ξ) ht
  convert h using 2 with y
  rfl

/-- The set of the points `y` at which `μ_y^ξ(A ∩ φ⁻¹B(φy, r_n)) ≥ μ_y^ξ(φ⁻¹B(φy, r_n)) / (m+1)`
for all large `n`, for some `m`. -/
def densityGood (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Set Ω) (φ : Ω → X) (A : Set Ω)
    (r : ℕ → ℝ) : Set Ω :=
  {y | ∃ m : ℕ, ∀ᶠ n in atTop, ((m : ℝ≥0∞) + 1)⁻¹ *
    condMeas μ ξ y (φ ⁻¹' closedBall (φ y) (r n)) ≤
      condMeas μ ξ y (A ∩ φ ⁻¹' closedBall (φ y) (r n))}

/-- The set `densityGood` is Borel. -/
theorem measurableSet_densityGood (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Set Ω)
    {φ : Ω → X} (hφ : Measurable φ) {A : Set Ω} (hA : MeasurableSet A) (r : ℕ → ℝ) :
    MeasurableSet (densityGood μ ξ φ A r) := by
  have h : densityGood μ ξ φ A r = ⋃ m : ℕ, ⋃ N : ℕ, ⋂ n : ℕ, ⋂ (_ : N ≤ n),
      {y | ((m : ℝ≥0∞) + 1)⁻¹ * condMeas μ ξ y (φ ⁻¹' closedBall (φ y) (r n)) ≤
        condMeas μ ξ y (A ∩ φ ⁻¹' closedBall (φ y) (r n))} := by
    ext y
    simp only [densityGood, eventually_atTop, mem_iUnion, mem_iInter, mem_ofPred_eq]
  rw [h]
  refine MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun N =>
    MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ => ?_
  have h1 := measurable_condMeas_inter_preimage_closedBall μ ξ hφ MeasurableSet.univ (r n)
  simp only [univ_inter] at h1
  exact measurableSet_le (h1.const_mul _)
    (measurable_condMeas_inter_preimage_closedBall μ ξ hφ hA (r n))

end Kernel

section Density

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [HasBesicovitchCovering X]

/-- Feng, Lemma 2.5 (1) with Lemma 2.2, along a sequence of radii: for a measurable partition
`ξ`, a Borel map `φ` into a Besicovitch space, a Borel set `A` and radii `r_n → 0⁺`, for
`μ`-almost every `x ∈ A` there is `c > 0` with
`c μ_x^ξ(φ⁻¹B(φx, r_n)) ≤ μ_x^ξ(A ∩ φ⁻¹B(φx, r_n))` for all large `n`. -/
theorem ae_condMeas_density (μ : Measure Ω) [IsFiniteMeasure μ] {ξ : Ω → Set Ω}
    (hξ : IsMeasurablePartition ξ) {φ : Ω → X} (hφ : Measurable φ) {A : Set Ω}
    (hA : MeasurableSet A) {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝[>] 0)) :
    ∀ᵐ x ∂μ, x ∈ A → ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧ ∀ᶠ n in atTop,
      c * condMeas μ ξ x (φ ⁻¹' closedBall (φ x) (r n)) ≤
        condMeas μ ξ x (A ∩ φ ⁻¹' closedBall (φ x) (r n)) := by
  set G := densityGood μ ξ φ A r
  have hG : MeasurableSet G := measurableSet_densityGood μ ξ hφ hA r
  -- the fibrewise statement
  have hfibre : ∀ x, ∀ᵐ y ∂(condMeas μ ξ x).restrict A, ∃ c : ℝ≥0∞, 0 < c ∧
      ∀ᶠ n in atTop, c * condMeas μ ξ x (φ ⁻¹' closedBall (φ y) (r n)) ≤
        condMeas μ ξ x (A ∩ φ ⁻¹' closedBall (φ y) (r n)) := by
    intro x
    have hle : ((condMeas μ ξ x).restrict A).map φ ≤ (condMeas μ ξ x).map φ :=
      Measure.map_mono Measure.restrict_le_self hφ
    have h := ae_of_ae_map hφ.aemeasurable (ae_exists_mul_le_of_le hle hr)
    filter_upwards [h] with y hy
    obtain ⟨c, hc, -, hev⟩ := hy
    refine ⟨c, hc, hev.mono fun n hn => ?_⟩
    rwa [Measure.map_apply hφ measurableSet_closedBall, Measure.map_apply hφ
      measurableSet_closedBall, Measure.restrict_apply (hφ measurableSet_closedBall),
      inter_comm] at hn
  -- the exceptional set is null for every conditional measure
  have hnull : ∀ᵐ x ∂μ, condMeas μ ξ x (A \ G) = 0 := by
    obtain ⟨f, hf, hfξ⟩ := hξ
    filter_upwards [condMeas_atom μ ⟨f, hf, hfξ⟩] with x hx
    have hmeas : MeasurableSet (ξ x) := by
      have : ξ x = f ⁻¹' {f x} := by
        ext y
        exact hfξ x y
      rw [this]
      exact hf (measurableSet_singleton _)
    have hcompl : condMeas μ ξ x (ξ x)ᶜ = 0 := (prob_compl_eq_zero_iff hmeas).2 hx
    set B := {y | ¬ ∃ c : ℝ≥0∞, 0 < c ∧
        ∀ᶠ n in atTop, c * condMeas μ ξ x (φ ⁻¹' closedBall (φ y) (r n)) ≤
          condMeas μ ξ x (A ∩ φ ⁻¹' closedBall (φ y) (r n))} with hB
    have hbad : condMeas μ ξ x (B ∩ A) = 0 := by
      rw [← Measure.restrict_apply' hA]
      exact ae_iff.1 (hfibre x)
    have hsub : A \ G ⊆ (ξ x)ᶜ ∪ (B ∩ A) := by
      intro y ⟨hyA, hyG⟩
      by_cases hyx : y ∈ ξ x
      · refine Or.inr ⟨fun hP => hyG ?_, hyA⟩
        obtain ⟨c, hc, hev⟩ := hP
        obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt hc.ne'
        refine ⟨m, hev.mono fun n hn => ?_⟩
        rw [← condMeas_eq_of_mem μ hyx]
        refine le_trans ?_ hn
        gcongr
        exact (ENNReal.inv_le_inv.2 le_self_add).trans hm.le
      · exact Or.inl hyx
    refine le_antisymm ((measure_mono hsub).trans ((measure_union_le _ _).trans ?_)) bot_le
    rw [hcompl, hbad, add_zero]
  -- the disintegration
  have hzero : μ (A \ G) = 0 := by
    have h := setLIntegral_condMeas μ ξ (hA.diff hG)
      (MeasurableSet.univ : MeasurableSet[saturated ξ] univ)
    rw [Measure.restrict_univ, inter_univ] at h
    rw [← h, lintegral_congr_ae hnull, lintegral_zero]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hzero] with x hx hxA
  have hxG : x ∈ G := by
    by_contra h
    exact hx ⟨hxA, h⟩
  obtain ⟨m, hm⟩ := hxG
  exact ⟨((m : ℝ≥0∞) + 1)⁻¹, ENNReal.inv_pos.2 (by simp), ENNReal.inv_ne_top.2 (by simp), hm⟩

end Density

/-! ### The lower pointwise dimension of an image measure and of its conditional measures -/

section LowerDim

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [HasBesicovitchCovering X]

omit [BorelSpace X] [SecondCountableTopology X] [HasBesicovitchCovering X] in
/-- Bounds `ν(B(z, e^{-n})) ≤ C e^{-n d}` for every `d < D` give `\underline{dim}_loc(ν, z) ≥ D` at
a point of the support of a probability measure: a radius `r` lies between `e^{-n-1}` and
`e^{-n}` for `n = ⌊-log r⌋`. -/
theorem lowerLocalDimGe_of_exp_bounds {ν : Measure X} [IsProbabilityMeasure ν] {z : X} {D : ℝ}
    (hpos : ∀ r : ℝ, 0 < r → 0 < ν (closedBall z r))
    (h : ∀ d < D, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ν.real (closedBall z (Real.exp (-n))) ≤ C * Real.exp (-(n * d))) :
    LowerLocalDimGe ν z D := by
  intro a ha
  obtain ⟨d, had, hdD⟩ := exists_between ha
  rcases le_or_gt d 0 with hd0 | hd0
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with r ⟨hr0, hr1⟩
    have h1 : Real.log (ν.real (closedBall z r)) ≤ 0 :=
      Real.log_nonpos measureReal_nonneg measureReal_le_one
    have h2 : Real.log r < 0 := Real.log_neg hr0 hr1
    have : 0 ≤ Real.log (ν.real (closedBall z r)) / Real.log r := div_nonneg_of_nonpos h1 h2.le
    linarith
  · obtain ⟨C, hC, hev⟩ := h d hdD
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    set K : ℝ := max (N : ℝ) (|Real.log C + d| / (d - a)) + 1 with hK
    have hK1 : (N : ℝ) + 1 ≤ K := by
      rw [hK]; linarith [le_max_left (N : ℝ) (|Real.log C + d| / (d - a))]
    have hK2 : |Real.log C + d| / (d - a) + 1 ≤ K := by
      rw [hK]; linarith [le_max_right (N : ℝ) (|Real.log C + d| / (d - a))]
    filter_upwards [Ioo_mem_nhdsGT (Real.exp_pos (-K))] with r ⟨hr0, hrK⟩
    set t := -Real.log r with ht_def
    have ht : K < t := by
      have := Real.log_lt_log hr0 hrK
      rw [Real.log_exp] at this
      linarith
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have ht0 : 0 < t := by linarith
    have hn1 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0.le
    have hn2 : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
    have hnN : N ≤ ⌊t⌋₊ := Nat.le_floor (by linarith)
    have hrn : r ≤ Real.exp (-(⌊t⌋₊ : ℝ)) := by
      rw [← Real.exp_log hr0]
      exact Real.exp_le_exp.2 (by linarith)
    have hpos' : 0 < ν.real (closedBall z r) :=
      ENNReal.toReal_pos (hpos r hr0).ne' (measure_ne_top _ _)
    have hle : ν.real (closedBall z r) ≤ C * Real.exp (-((⌊t⌋₊ : ℝ) * d)) :=
      (measureReal_mono (closedBall_subset_closedBall hrn)).trans (hN _ hnN)
    have hlog : Real.log (ν.real (closedBall z r)) ≤ Real.log C - (⌊t⌋₊ : ℝ) * d := by
      have := Real.log_le_log hpos' hle
      rwa [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp, ← sub_eq_add_neg] at this
    have hfac : |Real.log C + d| ≤ t * (d - a) :=
      (div_le_iff₀ (sub_pos.2 had)).1 (by linarith)
    have hlogr : Real.log r = -t := by rw [ht_def, neg_neg]
    rw [hlogr, le_div_iff_of_neg (by linarith)]
    have hmul : d * (t - 1) ≤ d * (⌊t⌋₊ : ℝ) := mul_le_mul_of_nonneg_left (by linarith) hd0.le
    nlinarith [le_abs_self (Real.log C + d)]

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The lower bound `\underline{dim}_loc(π_*μ, πx) ≥ D` from the bound
`\underline{dim}_loc(π_*μ_x^η, πx) ≥ D` for the conditional measures of any measurable partition
`η`. This is Feng's (C3) for `i = -1` (pp. 42 to 43, after Ledrappier–Young, Lemma 11.3.1), with
the partition `ξ_{-1}` trivial and `ϑ_{-1} = 0`, at the generality of an arbitrary measurable
partition. For `n ≥ N` and `x ∈ A_N`, the set of the points `y` with
`μ_y^η(B^π(y, 2e^{-n})) ≤ (2e^{-n})^d` for all `n ≥ N`, every atom of `η` meeting
`A_N ∩ B^π(x, e^{-n})` at a point `w` lies in `B^π(w, 2 e^{-n})`, so
`μ(A_N ∩ B^π(x, e^{-n})) ≤ (2e^{-n})^d`; the density of `A_N` (Lemma 2.5 (1), Lemma 2.2)
bounds `μ(B^π(x, e^{-n}))` by a multiple of this. -/
theorem ae_lowerLocalDimGe_map_of_condMeas (μ : Measure Ω) [IsProbabilityMeasure μ]
    {η : Ω → Set Ω} (hη : IsMeasurablePartition η) {π : Ω → X} (hπ : Measurable π) {D : ℝ}
    (h : ∀ᵐ x ∂μ, LowerLocalDimGe ((condMeas μ η x).map π) (π x) D) :
    ∀ᵐ x ∂μ, LowerLocalDimGe (μ.map π) (π x) D := by
  -- the radii and the bounds
  have hexp : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => Real.exp_pos _⟩
    exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have hη_meas : ∀ y, MeasurableSet (η y) := by
    obtain ⟨f, hf, hfη⟩ := hη
    intro y
    have : η y = f ⁻¹' {f y} := by
      ext w
      exact hfη y w
    rw [this]
    exact hf (measurableSet_singleton _)
  have hmass : ∀ (s : ℝ), Measurable fun y => condMeas μ η y (π ⁻¹' closedBall (π y) s) := by
    intro s
    have h1 := measurable_condMeas_inter_preimage_closedBall μ η hπ MeasurableSet.univ s
    simpa only [univ_inter] using h1
  have step : ∀ d < D, ∀ᵐ x ∂μ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (μ.map π).real (closedBall (π x) (Real.exp (-n))) ≤ C * Real.exp (-(n * d)) := by
    intro d hd
    set ρ : ℕ → ℝ := fun n => 2 * Real.exp (-(n : ℝ)) with hρ
    set b : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (Real.exp (d * Real.log (ρ n))) with hb
    set A : ℕ → Set Ω := fun N => {y | ∀ n, N ≤ n →
      condMeas μ η y (π ⁻¹' closedBall (π y) (ρ n)) ≤ b n} with hA
    have hAm : ∀ N, MeasurableSet (A N) := by
      intro N
      have : A N = ⋂ n, ⋂ (_ : N ≤ n),
          {y | condMeas μ η y (π ⁻¹' closedBall (π y) (ρ n)) ≤ b n} := by
        ext y
        simp only [hA, mem_iInter, mem_ofPred_eq]
      rw [this]
      exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
        measurableSet_le (hmass _) measurable_const
    -- almost every point lies in some `A N`
    have hρ0 : Tendsto ρ atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
        mem_Ioi.2 (mul_pos two_pos (Real.exp_pos _))⟩
      simpa using (tendsto_nhdsWithin_iff.1 hexp).1.const_mul 2
    have hcover : ∀ᵐ y ∂μ, ∃ N, y ∈ A N := by
      filter_upwards [h] with y hy
      have h1 := (hy d hd).filter_mono (le_refl _)
      have h2 : ∀ᶠ n in atTop, d ≤ Real.log (((condMeas μ η y).map π).real
          (closedBall (π y) (ρ n))) / Real.log (ρ n) := hρ0.eventually h1
      have h3 : ∀ᶠ n in atTop, ρ n < 1 :=
        (tendsto_nhdsWithin_iff.1 hρ0).1.eventually (gt_mem_nhds zero_lt_one)
      obtain ⟨N, hN⟩ := eventually_atTop.1 (h2.and h3)
      refine ⟨N, fun n hn => ?_⟩
      obtain ⟨hd', hρ1⟩ := hN n hn
      have hρpos : 0 < ρ n := by positivity
      have hlogρ : Real.log (ρ n) < 0 := Real.log_neg hρpos hρ1
      rw [measureReal_def, Measure.map_apply hπ measurableSet_closedBall] at hd'
      set m := condMeas μ η y (π ⁻¹' closedBall (π y) (ρ n))
      have hm : m ≠ ∞ := measure_ne_top _ _
      rcases eq_or_lt_of_le (ENNReal.toReal_nonneg (a := m)) with hm0 | hm0
      · rw [eq_comm, ENNReal.toReal_eq_zero_iff] at hm0
        rcases hm0 with hm0 | hm0
        · rw [hm0]
          exact bot_le
        · exact absurd hm0 hm
      · rw [ENNReal.le_ofReal_iff_toReal_le hm (Real.exp_pos _).le, ← Real.log_le_iff_le_exp hm0]
        rw [le_div_iff_of_neg hlogρ] at hd'
        linarith
    -- the mass of `A N` near `x`
    have hS : ∀ N n, N ≤ n → ∀ x, μ (A N ∩ π ⁻¹' closedBall (π x) (Real.exp (-n))) ≤ b n := by
      intro N n hn x
      set S := A N ∩ π ⁻¹' closedBall (π x) (Real.exp (-n))
      have hSm : MeasurableSet S := (hAm N).inter (hπ measurableSet_closedBall)
      have hint := setLIntegral_condMeas μ η hSm
        (MeasurableSet.univ : MeasurableSet[saturated η] univ)
      rw [Measure.restrict_univ, inter_univ] at hint
      rw [← hint]
      calc ∫⁻ y, condMeas μ η y S ∂μ ≤ ∫⁻ _y, b n ∂μ := by
            refine lintegral_mono_ae ?_
            filter_upwards [condMeas_atom μ hη] with y hy
            by_cases hne : (S ∩ η y).Nonempty
            · obtain ⟨w, ⟨hwA, hwB⟩, hwy⟩ := hne
              rw [condMeas_eq_of_mem μ hwy]
              have hsub : S ⊆ π ⁻¹' closedBall (π w) (ρ n) := by
                intro v ⟨_, hv⟩
                simp only [mem_preimage, mem_closedBall] at hv hwB ⊢
                calc dist (π v) (π w) ≤ dist (π v) (π x) + dist (π w) (π x) :=
                      dist_triangle_right _ _ _
                  _ ≤ ρ n := by rw [hρ]; linarith
              exact (measure_mono hsub).trans (hwA n hn)
            · have hcompl : condMeas μ η y (η y)ᶜ = 0 := (prob_compl_eq_zero_iff (hη_meas y)).2 hy
              refine le_trans (measure_mono_null ?_ hcompl).le bot_le
              intro v hv hvy
              exact hne ⟨v, hv, hvy⟩
        _ = b n := by rw [lintegral_const, measure_univ, mul_one]
    -- the density of `A N`
    have hdens : ∀ N, ∀ᵐ x ∂μ, x ∈ A N → ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧ ∀ᶠ n : ℕ in atTop,
        c * μ (π ⁻¹' closedBall (π x) (Real.exp (-n))) ≤
          μ (A N ∩ π ⁻¹' closedBall (π x) (Real.exp (-n))) := by
      intro N
      have hle : (μ.restrict (A N)).map π ≤ μ.map π := Measure.map_mono Measure.restrict_le_self hπ
      have h1 := ae_of_ae_map hπ.aemeasurable (ae_exists_mul_le_of_le hle hexp)
      refine (ae_restrict_iff' (hAm N)).1 (h1.mono fun x hx => ?_)
      obtain ⟨c, hc, hctop, hev⟩ := hx
      refine ⟨c, hc, hctop, hev.mono fun n hn => ?_⟩
      rwa [Measure.map_apply hπ measurableSet_closedBall, Measure.map_apply hπ
        measurableSet_closedBall, Measure.restrict_apply (hπ measurableSet_closedBall),
        inter_comm] at hn
    filter_upwards [hcover, ae_all_iff.2 hdens] with x ⟨N, hxN⟩ hx
    obtain ⟨c, hc0, hctop, hev⟩ := hx N hxN
    have hcinv : 0 < c⁻¹.toReal :=
      ENNReal.toReal_pos (ENNReal.inv_ne_zero.2 hctop) (ENNReal.inv_ne_top.2 hc0.ne')
    refine ⟨c⁻¹.toReal * Real.exp (d * Real.log 2), by positivity, ?_⟩
    filter_upwards [hev, eventually_ge_atTop N] with n hn hnN
    have h1 : μ (π ⁻¹' closedBall (π x) (Real.exp (-n))) ≤ c⁻¹ * b n :=
      (ENNReal.mul_le_iff_le_inv hc0.ne' hctop).1 (hn.trans (hS N n hnN x))
    rw [measureReal_def, Measure.map_apply hπ measurableSet_closedBall]
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0.ne')
      ENNReal.ofReal_ne_top) h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at h2
    refine h2.trans (le_of_eq ?_)
    rw [hρ, Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_exp, mul_assoc,
      ← Real.exp_add]
    ring_nf
  -- all `d < D` at once
  have hall : ∀ᵐ x ∂μ, ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (μ.map π).real (closedBall (π x) (Real.exp (-n))) ≤
        C * Real.exp (-(n * (D - 1 / ((k : ℝ) + 1)))) :=
    ae_all_iff.2 fun k => step _ (by have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
                                     linarith)
  filter_upwards [hall, ae_of_ae_map hπ.aemeasurable (ae_forall_measure_closedBall_pos (μ.map π))]
    with x hx hpos
  refine lowerLocalDimGe_of_exp_bounds hpos fun d hd => ?_
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hd)
  obtain ⟨C, hC, hev⟩ := hx k
  refine ⟨C, hC, hev.mono fun n hn => hn.trans ?_⟩
  gcongr
  linarith


/-- An almost sure property holds almost surely for almost every conditional measure:
if `p` holds `μ`-almost everywhere, then for `μ`-almost every `x` it holds `μ_x^ξ`-almost
everywhere, by `μ(N) = ∫ μ_x^ξ(N) dμ(x)` for a Borel null set `N` containing the exceptions. -/
theorem ae_ae_condMeas_of_ae {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Set Ω) {p : Ω → Prop}
    (h : ∀ᵐ y ∂μ, p y) : ∀ᵐ x ∂μ, ∀ᵐ y ∂condMeas μ ξ x, p y := by
  obtain ⟨N, hpN, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
  have hint := setLIntegral_condMeas μ ξ hNm (MeasurableSet.univ : MeasurableSet[saturated ξ] univ)
  rw [Measure.restrict_univ, inter_univ, hN0] at hint
  have hmeas : Measurable fun x => condMeas μ ξ x N :=
    (measurable_condMeas μ ξ hNm).mono (saturated_le ξ) le_rfl
  filter_upwards [(lintegral_eq_zero_iff hmeas).1 hint] with x hx
  exact ae_iff.2 (measure_mono_null hpN hx)

/-- The atoms of a measurable partition are Borel. -/
theorem IsMeasurablePartition.measurableSet_atom {Ω : Type*} [MeasurableSpace Ω]
    {ξ : Ω → Set Ω} (hξ : IsMeasurablePartition ξ) (x : Ω) : MeasurableSet (ξ x) := by
  obtain ⟨f, hf, hfξ⟩ := hξ
  have : ξ x = f ⁻¹' {f x} := by
    ext y
    exact hfξ x y
  rw [this]
  exact hf (measurableSet_singleton _)

/-- For `μ`-almost every `x`, the point `φ(x)` lies in the support of `φ_* μ_x^ξ`: every ball
about `φ(x)` has positive `φ_* μ_x^ξ`-measure. The set of such points is Borel (radii `1/(q+1)`
suffice), every `μ_x^ξ` is carried by `ξ(x)`, on which the conditional measures equal `μ_x^ξ`,
and `φ_* μ_x^ξ`-almost every point lies in its support. -/
theorem ae_condMeas_preimage_closedBall_pos {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopology X]
    (μ : Measure Ω) [IsFiniteMeasure μ] {ξ : Ω → Set Ω} (hξ : IsMeasurablePartition ξ)
    {φ : Ω → X} (hφ : Measurable φ) :
    ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < condMeas μ ξ x (φ ⁻¹' closedBall (φ x) r) := by
  have hmass : ∀ s : ℝ, Measurable fun y => condMeas μ ξ y (φ ⁻¹' closedBall (φ y) s) := by
    intro s
    have h1 := measurable_condMeas_inter_preimage_closedBall μ ξ hφ MeasurableSet.univ s
    simpa only [univ_inter] using h1
  set G := ⋂ q : ℕ, {y | 0 < condMeas μ ξ y (φ ⁻¹' closedBall (φ y) (1 / ((q : ℝ) + 1)))}
  have hG : MeasurableSet G := MeasurableSet.iInter fun q =>
    measurableSet_lt measurable_const (hmass _)
  have hnull : ∀ᵐ x ∂μ, condMeas μ ξ x Gᶜ = 0 := by
    filter_upwards [condMeas_atom μ hξ] with x hx
    have hcompl : condMeas μ ξ x (ξ x)ᶜ = 0 :=
      (prob_compl_eq_zero_iff (hξ.measurableSet_atom x)).2 hx
    have hsupp : ∀ᵐ y ∂condMeas μ ξ x, ∀ r : ℝ, 0 < r →
        0 < condMeas μ ξ x (φ ⁻¹' closedBall (φ y) r) := by
      have h1 := ae_of_ae_map hφ.aemeasurable
        (ae_forall_measure_closedBall_pos ((condMeas μ ξ x).map φ))
      filter_upwards [h1] with y hy r hr
      have := hy r hr
      rwa [Measure.map_apply hφ measurableSet_closedBall] at this
    have hsub : Gᶜ ⊆ (ξ x)ᶜ ∪ {y | ¬ ∀ r : ℝ, 0 < r →
        0 < condMeas μ ξ x (φ ⁻¹' closedBall (φ y) r)} := by
      intro y hy
      by_cases hyx : y ∈ ξ x
      · refine Or.inr fun hall => hy ?_
        simp only [G, mem_iInter, mem_ofPred_eq]
        intro q
        rw [← condMeas_eq_of_mem μ hyx]
        exact hall _ (by positivity)
      · exact Or.inl hyx
    refine le_antisymm ((measure_mono hsub).trans ((measure_union_le _ _).trans ?_)) bot_le
    rw [hcompl, ae_iff.1 hsupp, add_zero]
  have hzero : μ Gᶜ = 0 := by
    have h := setLIntegral_condMeas μ ξ hG.compl
      (MeasurableSet.univ : MeasurableSet[saturated ξ] univ)
    rw [Measure.restrict_univ, inter_univ] at h
    rw [← h, lintegral_congr_ae hnull, lintegral_zero]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hzero] with x hx r hr
  have hxG : x ∈ G := not_not.1 hx
  obtain ⟨q, hq⟩ := exists_nat_one_div_lt hr
  simp only [G, mem_iInter, mem_ofPred_eq] at hxG
  exact (hxG q).trans_le (measure_mono (preimage_mono (closedBall_subset_closedBall hq.le)))

/-- A lower bound `d` for `log f(r) / log r` near `0⁺`, for masses `f(r) ≤ 1`, gives
`f(ρ_n) ≤ ρ_n^d = e^{d log ρ_n}` along every sequence `ρ_n → 0⁺`. -/
theorem eventually_le_ofReal_exp_of_le_log_div {f : ℝ → ℝ≥0∞} (hf : ∀ r, f r ≠ ∞) {d : ℝ}
    (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), d ≤ Real.log (f r).toReal / Real.log r) {ρ : ℕ → ℝ}
    (hρ : Tendsto ρ atTop (𝓝[>] 0)) :
    ∀ᶠ n in atTop, f (ρ n) ≤ ENNReal.ofReal (Real.exp (d * Real.log (ρ n))) := by
  have h3 : ∀ᶠ n in atTop, ρ n < 1 :=
    (tendsto_nhdsWithin_iff.1 hρ).1.eventually (gt_mem_nhds zero_lt_one)
  have h4 : ∀ᶠ n in atTop, 0 < ρ n := (tendsto_nhdsWithin_iff.1 hρ).2
  filter_upwards [hρ.eventually h, h3, h4] with n hd' hρ1 hρpos
  have hlogρ : Real.log (ρ n) < 0 := Real.log_neg hρpos hρ1
  rcases eq_or_lt_of_le (ENNReal.toReal_nonneg (a := f (ρ n))) with hm0 | hm0
  · rw [eq_comm, ENNReal.toReal_eq_zero_iff] at hm0
    rcases hm0 with hm0 | hm0
    · rw [hm0]
      exact bot_le
    · exact absurd hm0 (hf _)
  · rw [ENNReal.le_ofReal_iff_toReal_le (hf _) (Real.exp_pos _).le, ← Real.log_le_iff_le_exp hm0]
    rw [le_div_iff_of_neg hlogρ] at hd'
    linarith

/-- Feng's (C3) (pp. 42 to 43, after Ledrappier–Young, Lemma 11.3.1 and Feng–Hu, Theorem 2.11),
at the generality of two nested measurable partitions `η ⊆ ξ` and a family of Borel tubes
`Γ(x, r)` such that an atom `η(y)`, `y ∈ ξ(x)`, meeting `φ⁻¹B(φx, r)` has `y ∈ Γ(x, κ r)`: if
`\underline{dim}_loc(φ_* μ_x^η, φx) ≥ D` and the transverse dimension
`liminf_{r → 0} log μ_x^ξ(Γ(x, r)) / log r ≥ c` almost everywhere, then
`\underline{dim}_loc(φ_* μ_x^ξ, φx) ≥ D + c` almost everywhere. The proof is Feng's (6.15):
`μ_x^ξ = ∫ μ_y^η dμ_x^ξ(y)` (`double_conditional`), every atom of `η` meeting
`A_N ∩ φ⁻¹B(φx, e^{-n})` at `w` has mass at most `(2 e^{-n})^d` there and lies over
`Γ(x, κ e^{-n})`, and the density of `A_N` for `μ_x^ξ` (Lemma 2.5 (1), Lemma 2.2). -/
theorem ae_lowerLocalDimGe_condMeas_of_tube {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [HasBesicovitchCovering X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {ξ η : Ω → Set Ω} (hξ : IsMeasurablePartition ξ)
    (hη : IsMeasurablePartition η) (hfine : ∀ x, η x ⊆ ξ x) {φ : Ω → X} (hφ : Measurable φ)
    {Γ : Ω → ℝ → Set Ω} (hΓm : ∀ x r, MeasurableSet (Γ x r)) {κ : ℝ} (hκ : 0 < κ)
    (htube : ∀ᵐ x ∂μ, ∀ y ∈ ξ x, ∀ r : ℝ,
      (η y ∩ φ ⁻¹' closedBall (φ x) r).Nonempty → y ∈ Γ x (κ * r))
    {D c : ℝ} (hD : ∀ᵐ x ∂μ, LowerLocalDimGe ((condMeas μ η x).map φ) (φ x) D)
    (hc : ∀ᵐ x ∂μ, ∀ c' < c, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      c' ≤ Real.log ((condMeas μ ξ x).real (Γ x r)) / Real.log r) :
    ∀ᵐ x ∂μ, LowerLocalDimGe ((condMeas μ ξ x).map φ) (φ x) (D + c) := by
  have hexp : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => Real.exp_pos _⟩
    exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have hmass : ∀ (s : ℝ), Measurable fun y => condMeas μ η y (φ ⁻¹' closedBall (φ y) s) := by
    intro s
    have h1 := measurable_condMeas_inter_preimage_closedBall μ η hφ MeasurableSet.univ s
    simpa only [univ_inter] using h1
  -- the disintegration of `μ_x^ξ` along `η`
  have hdis : ∀ᵐ x ∂μ, ∀ S, MeasurableSet S →
      condMeas μ ξ x S = ∫⁻ y, condMeas μ η y S ∂condMeas μ ξ x := by
    filter_upwards [(double_conditional μ hξ hη hfine).1] with x hx S hS
    have h := setLIntegral_condMeas (condMeas μ ξ x) η hS
      (MeasurableSet.univ : MeasurableSet[saturated η] univ)
    rw [Measure.restrict_univ, inter_univ] at h
    rw [← h]
    exact lintegral_congr_ae (hx.mono fun y hy => by
      change condMeas (condMeas μ ξ x) η y S = condMeas μ η y S
      rw [hy])
  have hatomη : ∀ᵐ x ∂μ, ∀ᵐ y ∂condMeas μ ξ x, condMeas μ η y (η y) = 1 :=
    ae_ae_condMeas_of_ae μ ξ (condMeas_atom μ hη)
  have hatomξ : ∀ᵐ x ∂μ, ∀ᵐ y ∂condMeas μ ξ x, y ∈ ξ x := by
    filter_upwards [condMeas_atom μ hξ] with x hx
    rw [ae_iff]
    have := (prob_compl_eq_zero_iff (hξ.measurableSet_atom x)).2 hx
    simpa only [compl_def, mem_ofPred_eq] using this
  have step : ∀ d < D, ∀ c' < c, ∀ᵐ x ∂μ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ((condMeas μ ξ x).map φ).real (closedBall (φ x) (Real.exp (-n))) ≤
        C * Real.exp (-(n * (d + c'))) := by
    intro d hd c' hc'
    set ρ : ℕ → ℝ := fun n => 2 * Real.exp (-(n : ℝ)) with hρ
    set b : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (Real.exp (d * Real.log (ρ n))) with hb
    set A : ℕ → Set Ω := fun N => {y | ∀ n, N ≤ n →
      condMeas μ η y (φ ⁻¹' closedBall (φ y) (ρ n)) ≤ b n} with hA
    have hAm : ∀ N, MeasurableSet (A N) := by
      intro N
      have : A N = ⋂ n, ⋂ (_ : N ≤ n),
          {y | condMeas μ η y (φ ⁻¹' closedBall (φ y) (ρ n)) ≤ b n} := by
        ext y
        simp only [hA, mem_iInter, mem_ofPred_eq]
      rw [this]
      exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
        measurableSet_le (hmass _) measurable_const
    have hρ0 : Tendsto ρ atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
        mem_Ioi.2 (mul_pos two_pos (Real.exp_pos _))⟩
      simpa using (tendsto_nhdsWithin_iff.1 hexp).1.const_mul 2
    have hκρ : Tendsto (fun n : ℕ => κ * Real.exp (-(n : ℝ))) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
        mem_Ioi.2 (mul_pos hκ (Real.exp_pos _))⟩
      simpa using (tendsto_nhdsWithin_iff.1 hexp).1.const_mul κ
    have hcover : ∀ᵐ y ∂μ, ∃ N, y ∈ A N := by
      filter_upwards [hD] with y hy
      have h1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), d ≤ Real.log
          (condMeas μ η y (φ ⁻¹' closedBall (φ y) r)).toReal / Real.log r := by
        filter_upwards [hy d hd] with r hr
        rwa [measureReal_def, Measure.map_apply hφ measurableSet_closedBall] at hr
      obtain ⟨N, hN⟩ := eventually_atTop.1
        (eventually_le_ofReal_exp_of_le_log_div (fun _ => measure_ne_top _ _) h1 hρ0)
      exact ⟨N, hN⟩
    -- the mass of `A N` near `x`, through the atoms of `η`
    have hS : ∀ᵐ x ∂μ, ∀ N n, N ≤ n →
        condMeas μ ξ x (A N ∩ φ ⁻¹' closedBall (φ x) (Real.exp (-n))) ≤
          b n * condMeas μ ξ x (Γ x (κ * Real.exp (-n))) := by
      filter_upwards [hdis, hatomη, hatomξ, htube] with x hxdis hxη hxξ hxtube N n hn
      set S := A N ∩ φ ⁻¹' closedBall (φ x) (Real.exp (-n))
      have hSm : MeasurableSet S := (hAm N).inter (hφ measurableSet_closedBall)
      rw [hxdis S hSm, ← lintegral_indicator_const (hΓm x _)]
      refine lintegral_mono_ae ?_
      filter_upwards [hxη, hxξ] with y hy hyξ
      by_cases hne : (S ∩ η y).Nonempty
      · obtain ⟨w, ⟨hwA, hwB⟩, hwy⟩ := hne
        have hyΓ : y ∈ Γ x (κ * Real.exp (-n)) := hxtube y hyξ _ ⟨w, hwy, hwB⟩
        rw [indicator_of_mem hyΓ, condMeas_eq_of_mem μ hwy]
        have hsub : S ⊆ φ ⁻¹' closedBall (φ w) (ρ n) := by
          intro v ⟨_, hv⟩
          simp only [mem_preimage, mem_closedBall] at hv hwB ⊢
          calc dist (φ v) (φ w) ≤ dist (φ v) (φ x) + dist (φ w) (φ x) :=
                dist_triangle_right _ _ _
            _ ≤ ρ n := by rw [hρ]; linarith
        exact (measure_mono hsub).trans (hwA n hn)
      · have hcompl : condMeas μ η y (η y)ᶜ = 0 :=
          (prob_compl_eq_zero_iff (hη.measurableSet_atom y)).2 hy
        refine le_trans (measure_mono_null ?_ hcompl).le bot_le
        intro v hv hvy
        exact hne ⟨v, hv, hvy⟩
    -- the density of `A N` for `μ_x^ξ`
    have hdens : ∀ N, ∀ᵐ x ∂μ, x ∈ A N → ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ c₀ ≠ ∞ ∧
        ∀ᶠ n : ℕ in atTop, c₀ * condMeas μ ξ x (φ ⁻¹' closedBall (φ x) (Real.exp (-n))) ≤
          condMeas μ ξ x (A N ∩ φ ⁻¹' closedBall (φ x) (Real.exp (-n))) :=
      fun N => ae_condMeas_density μ hξ hφ (hAm N) hexp
    -- the transverse bound
    have htrans : ∀ᵐ x ∂μ, ∀ᶠ n : ℕ in atTop, condMeas μ ξ x (Γ x (κ * Real.exp (-n))) ≤
        ENNReal.ofReal (Real.exp (c' * Real.log (κ * Real.exp (-n)))) := by
      filter_upwards [hc] with x hx
      exact eventually_le_ofReal_exp_of_le_log_div (fun _ => measure_ne_top _ _)
        (hx c' hc') hκρ
    filter_upwards [hcover, ae_all_iff.2 hdens, hS, htrans] with x ⟨N, hxN⟩ hx hxS hxt
    obtain ⟨c₀, hc0, hctop, hev⟩ := hx N hxN
    have hcinv : 0 < c₀⁻¹.toReal :=
      ENNReal.toReal_pos (ENNReal.inv_ne_zero.2 hctop) (ENNReal.inv_ne_top.2 hc0.ne')
    refine ⟨c₀⁻¹.toReal * Real.exp (d * Real.log 2) * Real.exp (c' * Real.log κ),
      by positivity, ?_⟩
    filter_upwards [hev, eventually_ge_atTop N, hxt] with n hn hnN hnt
    have h1 : condMeas μ ξ x (φ ⁻¹' closedBall (φ x) (Real.exp (-n))) ≤
        c₀⁻¹ * (b n * ENNReal.ofReal (Real.exp (c' * Real.log (κ * Real.exp (-n))))) :=
      (ENNReal.mul_le_iff_le_inv hc0.ne' hctop).1
        (hn.trans ((hxS N n hnN).trans (mul_le_mul_of_nonneg_left hnt bot_le)))
    rw [measureReal_def, Measure.map_apply hφ measurableSet_closedBall]
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0.ne')
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)) h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      ENNReal.toReal_ofReal (Real.exp_pos _).le] at h2
    refine h2.trans (le_of_eq ?_)
    rw [hρ, Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_mul hκ.ne'
      (Real.exp_pos _).ne', Real.log_exp]
    rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    ring_nf
  -- all `d < D`, `c' < c` at once
  have hall : ∀ᵐ x ∂μ, ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ((condMeas μ ξ x).map φ).real (closedBall (φ x) (Real.exp (-n))) ≤
        C * Real.exp (-(n * ((D - 1 / ((k : ℝ) + 1)) + (c - 1 / ((k : ℝ) + 1))))) := by
    refine ae_all_iff.2 fun k => ?_
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    exact step _ (by linarith) _ (by linarith)
  filter_upwards [hall, ae_condMeas_preimage_closedBall_pos μ hξ hφ] with x hx hpos
  refine lowerLocalDimGe_of_exp_bounds (fun r hr => ?_) fun d hd => ?_
  · rw [Measure.map_apply hφ measurableSet_closedBall]
    exact hpos r hr
  · obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < (D + c - d) / 2 by linarith)
    obtain ⟨C, hC, hev⟩ := hx k
    refine ⟨C, hC, hev.mono fun n hn => hn.trans ?_⟩
    gcongr
    have : 1 / ((k : ℝ) + 1) < (D + c - d) / 2 := hk
    linarith

end LowerDim


/-! ### The upper pointwise dimension: Feng's counting argument (C2) -/

section UpperDim

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [HasBesicovitchCovering X]

omit [BorelSpace X] [SecondCountableTopology X] [HasBesicovitchCovering X] in
/-- Lower bounds `ν(B(z, K e^{ns})) ≥ C e^{nsb}` along a geometric sequence of radii, `s < 0`,
for every `b > B` give `\overline{dim}_loc(ν, z) ≤ B` for a probability measure. -/
theorem upperLocalDimLe_of_exp_bounds {ν : Measure X} [IsProbabilityMeasure ν] {z : X} {B : ℝ}
    (h : ∀ b > B, ∃ C K s : ℝ, 0 < C ∧ 0 < K ∧ s < 0 ∧ ∀ᶠ n : ℕ in atTop,
      C * Real.exp (n * s * b) ≤ ν.real (closedBall z (K * Real.exp (n * s)))) :
    UpperLocalDimLe ν z B := by
  intro b' hb'
  obtain ⟨b, hBb, hbb'⟩ := exists_between hb'
  obtain ⟨C, K, s, hC, hK, hs, hev⟩ := h b hBb
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  rcases lt_or_ge b 0 with hb0 | hb0
  · -- the bounds are impossible for `b < 0`
    exfalso
    have ht : Tendsto (fun n : ℕ => C * Real.exp (n * s * b)) atTop atTop := by
      refine Tendsto.const_mul_atTop hC (Real.tendsto_exp_atTop.comp ?_)
      have hsb : 0 < s * b := mul_pos_of_neg_of_neg hs hb0
      simpa [mul_assoc] using tendsto_natCast_atTop_atTop.atTop_mul_const hsb
    obtain ⟨n, hn1, hn2⟩ := ((ht.eventually_gt_atTop 1).and (eventually_ge_atTop N)).exists
    exact absurd ((hN n hn2).trans measureReal_le_one) (not_le.2 hn1)
  · set E := |Real.log C - b * Real.log K + b * s|
    set T : ℝ := max (|Real.log K| - s * N) (E / (b' - b)) + 1 with hT
    have hsN : 0 ≤ -s * N := mul_nonneg (by linarith) (Nat.cast_nonneg N)
    have hT1 : |Real.log K| - s * N + 1 ≤ T := by
      rw [hT]; linarith [le_max_left (|Real.log K| - s * N) (E / (b' - b))]
    have hT2 : E / (b' - b) + 1 ≤ T := by
      rw [hT]; linarith [le_max_right (|Real.log K| - s * N) (E / (b' - b))]
    filter_upwards [Ioo_mem_nhdsGT (Real.exp_pos (-T))] with r ⟨hr0, hrT⟩
    have hlogr : Real.log r < -T := by
      have := Real.log_lt_log hr0 hrT
      rwa [Real.log_exp] at this
    have hK1 := neg_abs_le (Real.log K)
    -- the index `n` with `K e^{(n+1)s} < r ≤ K e^{ns}`
    set t := (Real.log r - Real.log K) / s with ht_def
    have ht0 : 0 ≤ t := div_nonneg_of_nonpos (by linarith) hs.le
    have hn1 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
    have hts : t * s = Real.log r - Real.log K := by rw [ht_def, div_mul_cancel₀ _ hs.ne]
    have hnN : N ≤ ⌊t⌋₊ + 1 := by
      have : (N : ℝ) ≤ t := by
        rw [ht_def, le_div_iff_of_neg hs]
        linarith
      exact (Nat.le_floor this).trans (Nat.le_succ _)
    have hrad : K * Real.exp (((⌊t⌋₊ + 1 : ℕ) : ℝ) * s) ≤ r := by
      rw [← Real.exp_log hK, ← Real.exp_add, ← Real.exp_log hr0]
      refine Real.exp_le_exp.2 ?_
      have hn2 : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
      push_cast
      nlinarith
    have hmass := (hN _ hnN).trans (measureReal_mono (closedBall_subset_closedBall hrad))
    have hlog : Real.log C + ((⌊t⌋₊ + 1 : ℕ) : ℝ) * s * b ≤
        Real.log (ν.real (closedBall z r)) := by
      have := Real.log_le_log (mul_pos hC (Real.exp_pos _)) hmass
      rwa [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp] at this
    have hstep : (Real.log r - Real.log K + s) * b ≤ ((⌊t⌋₊ + 1 : ℕ) : ℝ) * s * b := by
      push_cast
      have h1 : (t + 1) * s ≤ ((⌊t⌋₊ : ℝ) + 1) * s :=
        mul_le_mul_of_nonpos_right (by linarith) hs.le
      have h2 : Real.log r - Real.log K + s = (t + 1) * s := by rw [add_mul, hts, one_mul]
      rw [h2]
      exact mul_le_mul_of_nonneg_right h1 hb0
    have hE : |Real.log C - b * Real.log K + b * s| ≤ (b' - b) * (-Real.log r) := by
      have h2 : E / (b' - b) ≤ -Real.log r := by linarith
      rw [div_le_iff₀ (by linarith)] at h2
      linarith
    have hT0 : 1 ≤ T := by linarith [abs_nonneg (Real.log K)]
    rw [div_le_iff_of_neg (by linarith)]
    nlinarith [neg_abs_le (Real.log C - b * Real.log K + b * s)]

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- In a measurable partition, the atom of a point of an atom is that atom. -/
theorem IsMeasurablePartition.eq_of_mem {Ω : Type*} [MeasurableSpace Ω] {ξ : Ω → Set Ω}
    (hξ : IsMeasurablePartition ξ) {x z : Ω} (hz : z ∈ ξ x) : ξ z = ξ x := by
  obtain ⟨f, -, hfξ⟩ := hξ
  have hfz : f z = f x := (hfξ x z).1 hz
  ext v
  rw [hfξ z v, hfξ x v, hfz]

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- A point of the cylinder `[w]` has the block `w`. -/
theorem block_eq_of_mem_cylinder {n : ℕ} {w : Fin n → α} {z : ℤ → α} (hz : z ∈ cylinder w) :
    block n z = w :=
  funext fun k => hz k

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Every point lies in the cylinder of its block. -/
theorem mem_cylinder_block (n : ℕ) (z : ℤ → α) : z ∈ cylinder (block n z) := fun _ => rfl

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Cylinders of distinct words of the same length are disjoint. -/
theorem pairwiseDisjoint_cylinder (n : ℕ) (W : Set (Fin n → α)) :
    W.PairwiseDisjoint (cylinder : (Fin n → α) → Set (ℤ → α)) := by
  intro w _ w' _ hww'
  refine Set.disjoint_left.2 fun z hz hz' => hww' ?_
  rw [← block_eq_of_mem_cylinder hz, ← block_eq_of_mem_cylinder hz']

/-- `y ↦ μ_y^ξ([y_0 ⋯ y_{n-1}])` is Borel. -/
theorem measurable_condMeas_cylinder_block (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (ξ : (ℤ → α) → Set (ℤ → α)) (n : ℕ) :
    Measurable fun y => condMeas μ ξ y (cylinder (block n y)) := by
  have ht : MeasurableSet {p : (ℤ → α) × (ℤ → α) | block n p.2 = block n p.1} :=
    measurableSet_eq_fun ((measurable_block n).comp measurable_snd)
      ((measurable_block n).comp measurable_fst)
  have h := Kernel.measurable_kernel_prodMk_left (κ := condMeasKernel μ ξ) ht
  convert h using 2 with y
  rw [cylinder_eq_preimage]
  rfl

/-- The conditional measures of the trivial partition are `μ`. -/
theorem condMeas_univ_ae_eq (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ] :
    ∀ᵐ x ∂μ, condMeas μ (fun _ => univ) x = μ := by
  have h := condMeas_unique μ (fun _ => univ) (fun _ => μ) (fun A _ => measurable_const)
    fun A B hA hB => by
      rcases eq_empty_or_nonempty B with rfl | ⟨b, hb⟩
      · simp
      · have hBu : B = univ := eq_univ_of_forall fun y => (hB.2 b y (mem_univ y)).1 hb
        subst hBu
        simp
  filter_upwards [h] with x hx using hx.symm

/-- The trivial partition is measurable. -/
theorem isMeasurablePartition_univ {Ω : Type*} [MeasurableSpace Ω] :
    IsMeasurablePartition (fun _ : Ω => (univ : Set Ω)) :=
  ⟨fun _ => 0, measurable_const, fun _ _ => by simp⟩

/-- Feng's (C2) (pp. 40 to 42, after Ledrappier–Young, Section 10.2, and Feng–Hu,
Theorem 2.11), at the generality of two nested measurable partitions `η ⊆ ξ` of the shift
space: if `-n⁻¹ log μ_x^ξ([x|_n]) → h` and `-n⁻¹ log μ_x^η([x|_n]) → h'` almost everywhere, the
sets `ξ(z) ∩ [z|_n]` lie in balls `φ⁻¹B(φz, ρ_n(z))` with Borel radii,
`ρ_n ≤ e^{n(λ + ε)}` eventually for every `ε > 0`, `λ < 0`, and
`\overline{dim}_loc(φ_* μ_x^η, φx) ≤ D` almost everywhere, then
`\overline{dim}_loc(φ_* μ_x^ξ, φx) ≤ (h' - h)/λ + D` almost everywhere.

The proof counts cylinders, as Feng does, but directly rather than by contradiction: with
`R_n = e^{n(λ+ε)}` and `L = φ⁻¹B(φx, R_n)`, the cylinders `[w]` of length `n` meeting
`η(x) ∩ L ∩ Δ` for a good set `Δ` carry `μ_x^η(L ∩ Δ)` with mass at most `e^{-n(h'-ε)}` each, and
each of them meets `ξ(x)` inside `φ⁻¹B(φx, 2R_n)` with `μ_x^ξ`-mass at least `e^{-n(h+ε)}`. -/
theorem ae_upperLocalDimLe_condMeas_of_counting (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ]
    {ξ η : (ℤ → α) → Set (ℤ → α)} (hξ : IsMeasurablePartition ξ)
    (hη : IsMeasurablePartition η) (hfine : ∀ x, η x ⊆ ξ x)
    {φ : (ℤ → α) → X} (hφ : Measurable φ) {E : Set (ℤ → α)} (hE : MeasurableSet E)
    (hEfull : μ Eᶜ = 0) {ρ : ℕ → (ℤ → α) → ℝ} (hρm : ∀ n, Measurable (ρ n))
    (hcont : ∀ z ∈ E, ∀ n : ℕ, ξ z ∩ cylinder (block n z) ⊆ φ ⁻¹' closedBall (φ z) (ρ n z))
    {lam h h' D : ℝ} (hlam : lam < 0)
    (hρ : ∀ ε > 0, ∀ᵐ x ∂μ, ∀ᶠ n : ℕ in atTop, ρ n x ≤ Real.exp (n * (lam + ε)))
    (hentξ : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ =>
      -Real.log ((condMeas μ ξ x).real (cylinder (block n x))) / n) atTop (𝓝 h))
    (hentη : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ =>
      -Real.log ((condMeas μ η x).real (cylinder (block n x))) / n) atTop (𝓝 h'))
    (hD : ∀ᵐ x ∂μ, UpperLocalDimLe ((condMeas μ η x).map φ) (φ x) D) :
    ∀ᵐ x ∂μ, UpperLocalDimLe ((condMeas μ ξ x).map φ) (φ x) ((h' - h) / lam + D) := by
  classical
  set g : ℝ → ℝ := fun ε => (D + ε) + (h' - h - 2 * ε) / (lam + ε) with hg
  have hmassη : ∀ s : ℝ, Measurable fun y => condMeas μ η y (φ ⁻¹' closedBall (φ y) s) := by
    intro s
    have h1 := measurable_condMeas_inter_preimage_closedBall μ η hφ MeasurableSet.univ s
    simpa only [univ_inter] using h1
  have step : ∀ ε : ℝ, 0 < ε → lam + ε < 0 → ∀ᵐ x ∂μ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C * Real.exp (n * (lam + ε) * g ε) ≤
        ((condMeas μ ξ x).map φ).real (closedBall (φ x) (2 * Real.exp (n * (lam + ε)))) := by
    intro ε hε hs
    set sε := lam + ε with hsε
    set R : ℕ → ℝ := fun n => Real.exp (n * sε) with hR
    have hRlim : Tendsto R atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => mem_Ioi.2 (Real.exp_pos _)⟩
      refine Real.tendsto_exp_atBot.comp ?_
      exact tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg hs
    -- the good sets
    set Δ : ℕ → Set (ℤ → α) := fun N => E ∩ {y | ∀ n, N ≤ n →
        Real.exp (n * sε * (D + ε)) ≤ (condMeas μ η y).real (φ ⁻¹' closedBall (φ y) (R n)) ∧
        (condMeas μ η y).real (cylinder (block n y)) ≤ Real.exp (-(n * (h' - ε))) ∧
        ρ n y ≤ R n ∧
        Real.exp (-(n * (h + ε))) ≤ (condMeas μ ξ y).real (cylinder (block n y))} with hΔ
    have hΔm : ∀ N, MeasurableSet (Δ N) := by
      intro N
      have : Δ N = E ∩ ⋂ n, ⋂ (_ : N ≤ n),
          ({y | Real.exp (n * sε * (D + ε)) ≤
              (condMeas μ η y).real (φ ⁻¹' closedBall (φ y) (R n))} ∩
            {y | (condMeas μ η y).real (cylinder (block n y)) ≤ Real.exp (-(n * (h' - ε)))} ∩
            {y | ρ n y ≤ R n} ∩
            {y | Real.exp (-(n * (h + ε))) ≤ (condMeas μ ξ y).real (cylinder (block n y))}) := by
        ext y
        simp only [hΔ, mem_inter_iff, mem_iInter, mem_ofPred_eq, and_assoc]
      rw [this]
      refine hE.inter (MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ => ?_)
      simp only [measureReal_def]
      exact (((measurableSet_le measurable_const (hmassη _).ennreal_toReal).inter
        (measurableSet_le (measurable_condMeas_cylinder_block μ η n).ennreal_toReal
          measurable_const)).inter (measurableSet_le (hρm n) measurable_const)).inter
        (measurableSet_le measurable_const
          (measurable_condMeas_cylinder_block μ ξ n).ennreal_toReal)
    -- almost every point is good from some `N` on
    have hcover : ∀ᵐ y ∂μ, ∃ N, y ∈ Δ N := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hEfull, hD, hentξ, hentη, hρ ε hε,
        ae_condMeas_preimage_closedBall_pos μ hη hφ, condMeas_cylinder_pos μ ξ]
        with y hyE hyD hyξ hyη hyρ hypos hycyl
      have ha : ∀ᶠ n : ℕ in atTop, Real.exp (n * sε * (D + ε)) ≤
          (condMeas μ η y).real (φ ⁻¹' closedBall (φ y) (R n)) := by
        filter_upwards [hRlim.eventually (hyD (D + ε) (by linarith)), eventually_gt_atTop 0]
          with n hn hn0
        rw [measureReal_def, Measure.map_apply hφ measurableSet_closedBall] at hn
        have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
        have hlogR : Real.log (R n) = n * sε := by rw [hR, Real.log_exp]
        rw [hlogR, div_le_iff_of_neg (by nlinarith)] at hn
        have hpos' : 0 < (condMeas μ η y (φ ⁻¹' closedBall (φ y) (R n))).toReal :=
          ENNReal.toReal_pos (hypos _ (Real.exp_pos _)).ne' (measure_ne_top _ _)
        rw [measureReal_def, ← Real.exp_log hpos']
        exact Real.exp_le_exp.2 (by linarith)
      have hb : ∀ᶠ n : ℕ in atTop,
          (condMeas μ η y).real (cylinder (block n y)) ≤ Real.exp (-(n * (h' - ε))) := by
        filter_upwards [hyη.eventually (lt_mem_nhds (show h' - ε < h' by linarith)),
          eventually_gt_atTop 0] with n hn hn0
        have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
        rw [lt_div_iff₀ hn0'] at hn
        rcases eq_or_lt_of_le (measureReal_nonneg (μ := condMeas μ η y)
          (s := cylinder (block n y))) with h0 | h0
        · rw [← h0]
          exact (Real.exp_pos _).le
        · rw [← Real.exp_log h0]
          exact Real.exp_le_exp.2 (by linarith)
      have hd : ∀ᶠ n : ℕ in atTop,
          Real.exp (-(n * (h + ε))) ≤ (condMeas μ ξ y).real (cylinder (block n y)) := by
        filter_upwards [hyξ.eventually (gt_mem_nhds (show h < h + ε by linarith)),
          eventually_gt_atTop 0] with n hn hn0
        have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
        rw [div_lt_iff₀ hn0'] at hn
        have hpos' : 0 < (condMeas μ ξ y).real (cylinder (block n y)) :=
          ENNReal.toReal_pos (hycyl n).ne' (measure_ne_top _ _)
        rw [← Real.exp_log hpos']
        exact Real.exp_le_exp.2 (by linarith)
      obtain ⟨N, hN⟩ := eventually_atTop.1 (ha.and (hb.and (hyρ.and hd)))
      exact ⟨N, not_not.1 hyE, fun n hn => hN n hn⟩
    -- the density of `Δ N` for `μ_x^η`
    have hdens : ∀ N, ∀ᵐ x ∂μ, x ∈ Δ N → ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ c₀ ≠ ∞ ∧
        ∀ᶠ n : ℕ in atTop, c₀ * condMeas μ η x (φ ⁻¹' closedBall (φ x) (R n)) ≤
          condMeas μ η x (Δ N ∩ φ ⁻¹' closedBall (φ x) (R n)) :=
      fun N => ae_condMeas_density μ hη hφ (hΔm N) hRlim
    filter_upwards [hcover, ae_all_iff.2 hdens, condMeas_atom μ hη, condMeas_atom μ hξ]
      with x ⟨N, hxN⟩ hx hxη hxξ
    obtain ⟨c₀, hc0, hctop, hev⟩ := hx N hxN
    have hc0' : 0 < c₀.toReal := ENNReal.toReal_pos hc0.ne' hctop
    refine ⟨c₀.toReal, hc0', ?_⟩
    filter_upwards [hev, eventually_ge_atTop N] with n hn hnN
    have hxηc : (condMeas μ η x).real (η x)ᶜ = 0 := by
      rw [measureReal_def, (prob_compl_eq_zero_iff (hη.measurableSet_atom x)).2 hxη,
        ENNReal.toReal_zero]
    have hxξc : (condMeas μ ξ x).real (ξ x)ᶜ = 0 := by
      rw [measureReal_def, (prob_compl_eq_zero_iff (hξ.measurableSet_atom x)).2 hxξ,
        ENNReal.toReal_zero]
    set L := φ ⁻¹' closedBall (φ x) (R n) with hL
    set S := Δ N ∩ L ∩ η x with hS
    set W : Finset (Fin n → α) := Finset.univ.filter fun w => (cylinder w ∩ S).Nonempty with hW
    have hwit : ∀ w ∈ W, ∃ z ∈ S, block n z = w := by
      intro w hw
      obtain ⟨z, hzw, hzS⟩ := (Finset.mem_filter.1 hw).2
      exact ⟨z, hzS, block_eq_of_mem_cylinder hzw⟩
    -- (A): the fine conditional measure
    have hA : c₀.toReal * (condMeas μ η x).real L ≤ W.card * Real.exp (-(n * (h' - ε))) := by
      have h1 : c₀.toReal * (condMeas μ η x).real L ≤ (condMeas μ η x).real (Δ N ∩ L) := by
        have := ENNReal.toReal_mono (measure_ne_top _ _) hn
        rwa [ENNReal.toReal_mul] at this
      have h2 : (condMeas μ η x).real (Δ N ∩ L) ≤ (condMeas μ η x).real S := by
        have hsub : Δ N ∩ L ⊆ S ∪ (η x)ᶜ := by
          intro v hv
          by_cases hvx : v ∈ η x
          · exact Or.inl ⟨hv, hvx⟩
          · exact Or.inr hvx
        calc (condMeas μ η x).real (Δ N ∩ L) ≤ (condMeas μ η x).real (S ∪ (η x)ᶜ) :=
              measureReal_mono hsub
          _ ≤ (condMeas μ η x).real S + (condMeas μ η x).real (η x)ᶜ := measureReal_union_le _ _
          _ = (condMeas μ η x).real S := by rw [hxηc, add_zero]
      have h3 : (condMeas μ η x).real S ≤ ∑ w ∈ W, (condMeas μ η x).real (cylinder w) := by
        have hsub : S ⊆ ⋃ w ∈ W, cylinder w := by
          intro z hz
          refine mem_biUnion (x := block n z) ?_ (mem_cylinder_block n z)
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, z, mem_cylinder_block n z, hz⟩
        exact (measureReal_mono hsub (measure_ne_top _ _)).trans
          (measureReal_biUnion_finset_le W cylinder)
      have h4 : ∀ w ∈ W, (condMeas μ η x).real (cylinder w) ≤ Real.exp (-(n * (h' - ε))) := by
        intro w hw
        obtain ⟨z, ⟨⟨hzΔ, -⟩, hzη⟩, rfl⟩ := hwit w hw
        rw [condMeas_eq_of_mem μ hzη]
        exact (hzΔ.2 n hnN).2.1
      calc c₀.toReal * (condMeas μ η x).real L ≤ ∑ w ∈ W, (condMeas μ η x).real (cylinder w) :=
            h1.trans (h2.trans h3)
        _ ≤ ∑ _w ∈ W, Real.exp (-(n * (h' - ε))) := Finset.sum_le_sum h4
        _ = W.card * Real.exp (-(n * (h' - ε))) := by rw [Finset.sum_const, nsmul_eq_mul]
    -- (B): the coarse conditional measure
    have hB : W.card * Real.exp (-(n * (h + ε))) ≤
        (condMeas μ ξ x).real (φ ⁻¹' closedBall (φ x) (2 * R n)) := by
      have h1 : ∀ w ∈ W, Real.exp (-(n * (h + ε))) ≤ (condMeas μ ξ x).real (cylinder w) := by
        intro w hw
        obtain ⟨z, ⟨⟨hzΔ, -⟩, hzη⟩, rfl⟩ := hwit w hw
        rw [condMeas_eq_of_mem μ (hfine x hzη)]
        exact (hzΔ.2 n hnN).2.2.2
      have h2 : ∑ w ∈ W, (condMeas μ ξ x).real (cylinder w) =
          (condMeas μ ξ x).real (⋃ w ∈ W, cylinder w) :=
        (measureReal_biUnion_finset (pairwiseDisjoint_cylinder n _)
          (fun w _ => measurableSet_cylinder w)).symm
      have h3 : (⋃ w ∈ W, cylinder w) ⊆ φ ⁻¹' closedBall (φ x) (2 * R n) ∪ (ξ x)ᶜ := by
        intro v hv
        obtain ⟨w, hw, hvw⟩ := mem_iUnion₂.1 hv
        obtain ⟨z, ⟨⟨hzΔ, hzL⟩, hzη⟩, hzw⟩ := hwit w hw
        by_cases hvx : v ∈ ξ x
        · refine Or.inl ?_
          have hzξ : z ∈ ξ x := hfine x hzη
          have hvz : v ∈ ξ z ∩ cylinder (block n z) := by
            rw [hξ.eq_of_mem hzξ, hzw]
            exact ⟨hvx, hvw⟩
          have hb1 := hcont z hzΔ.1 n hvz
          have hb2 := (hzΔ.2 n hnN).2.2.1
          simp only [mem_preimage, mem_closedBall] at hb1 hzL ⊢
          calc dist (φ v) (φ x) ≤ dist (φ v) (φ z) + dist (φ z) (φ x) := dist_triangle _ _ _
            _ ≤ R n + R n := add_le_add (hb1.trans hb2) hzL
            _ = 2 * R n := by ring
        · exact Or.inr hvx
      calc (W.card : ℝ) * Real.exp (-(n * (h + ε))) = ∑ _w ∈ W, Real.exp (-(n * (h + ε))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ w ∈ W, (condMeas μ ξ x).real (cylinder w) := Finset.sum_le_sum h1
        _ = (condMeas μ ξ x).real (⋃ w ∈ W, cylinder w) := h2
        _ ≤ (condMeas μ ξ x).real (φ ⁻¹' closedBall (φ x) (2 * R n) ∪ (ξ x)ᶜ) :=
            measureReal_mono h3
        _ ≤ (condMeas μ ξ x).real (φ ⁻¹' closedBall (φ x) (2 * R n)) +
              (condMeas μ ξ x).real (ξ x)ᶜ := measureReal_union_le _ _
        _ = (condMeas μ ξ x).real (φ ⁻¹' closedBall (φ x) (2 * R n)) := by rw [hxξc, add_zero]
    -- the good point `x` itself
    have hxL : Real.exp (n * sε * (D + ε)) ≤ (condMeas μ η x).real L := (hxN.2 n hnN).1
    rw [measureReal_def, Measure.map_apply hφ measurableSet_closedBall, ← measureReal_def]
    have hg' : (n : ℝ) * sε * g ε = n * sε * (D + ε) + n * (h' - ε) - n * (h + ε) := by
      have hne : sε ≠ 0 := hs.ne
      have hgε : g ε = D + ε + (h' - h - 2 * ε) / sε := by rw [hg, hsε]
      rw [hgε]
      field_simp
      ring
    rw [hg', Real.exp_sub, Real.exp_add]
    have hW : c₀.toReal * Real.exp (n * sε * (D + ε)) * Real.exp (n * (h' - ε)) ≤ W.card := by
      have := (mul_le_mul_of_nonneg_left hxL hc0'.le).trans hA
      rw [Real.exp_neg] at this
      have hexp := Real.exp_pos (n * (h' - ε))
      calc c₀.toReal * Real.exp (n * sε * (D + ε)) * Real.exp (n * (h' - ε))
          ≤ W.card * (Real.exp (n * (h' - ε)))⁻¹ * Real.exp (n * (h' - ε)) :=
            mul_le_mul_of_nonneg_right this hexp.le
        _ = W.card := by field_simp
    calc c₀.toReal * (Real.exp (n * sε * (D + ε)) * Real.exp (n * (h' - ε)) /
          Real.exp (n * (h + ε)))
        = c₀.toReal * Real.exp (n * sε * (D + ε)) * Real.exp (n * (h' - ε)) *
            Real.exp (-(n * (h + ε))) := by rw [Real.exp_neg]; ring
      _ ≤ W.card * Real.exp (-(n * (h + ε))) :=
          mul_le_mul_of_nonneg_right hW (Real.exp_pos _).le
      _ ≤ _ := hB
  -- the exponents `g(ε_k)` tend to the claimed bound
  set ε : ℕ → ℝ := fun k => (-lam / 2) / ((k : ℝ) + 1) with hε
  have hεpos : ∀ k, 0 < ε k := fun k => div_pos (by linarith) (by positivity)
  have hεs : ∀ k, lam + ε k < 0 := by
    intro k
    have : ε k ≤ -lam / 2 := div_le_self (by linarith) (by
      have := Nat.cast_nonneg (α := ℝ) k
      linarith)
    linarith
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h0 := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (-lam / 2)
    rw [mul_zero] at h0
    refine h0.congr fun k => ?_
    show -lam / 2 * (1 / ((k : ℝ) + 1)) = (-lam / 2) / ((k : ℝ) + 1)
    ring
  have hglim : Tendsto (fun k => g (ε k)) atTop (𝓝 ((h' - h) / lam + D)) := by
    have h1 : Tendsto (fun k => (D + ε k) + (h' - h - 2 * ε k) / (lam + ε k)) atTop
        (𝓝 ((D + 0) + (h' - h - 2 * 0) / (lam + 0))) :=
      (tendsto_const_nhds.add hεlim).add ((tendsto_const_nhds.sub (hεlim.const_mul 2)).div
        (tendsto_const_nhds.add hεlim) (by simpa using hlam.ne))
    simpa [hg, add_comm] using h1
  have hall : ∀ᵐ x ∂μ, ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C * Real.exp (n * (lam + ε k) * g (ε k)) ≤
        ((condMeas μ ξ x).map φ).real (closedBall (φ x) (2 * Real.exp (n * (lam + ε k)))) :=
    ae_all_iff.2 fun k => step (ε k) (hεpos k) (hεs k)
  filter_upwards [hall] with x hx
  refine upperLocalDimLe_of_exp_bounds fun b hb => ?_
  obtain ⟨k, hk⟩ := (hglim.eventually (gt_mem_nhds hb)).exists
  obtain ⟨C, hC, hev⟩ := hx k
  refine ⟨C, 2, lam + ε k, hC, two_pos, hεs k, hev.mono fun n hn => le_trans ?_ hn⟩
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC.le
  have hns : (n : ℝ) * (lam + ε k) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (hεs k).le
  exact mul_le_mul_of_nonpos_left hk.le hns

/-- Feng, Lemma 4.5 (3), for every Borel set and `n = 1`:
`μ_x^ξ([x_0] ∩ σ⁻¹A) = μ_x^ξ([x_0]) μ_{σx}^ξ(A)` for almost every `x`, under the invariance property
`σ^{-1}(ξ(σx)) = ξ(x) ∩ [x_0]` of `BoxLike/FengIdentity.lean`. -/
theorem condMeas_zeroCyl_inter_preimage_shift {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) {ξ : (ℤ → α) → Set (ℤ → α)}
    (hξ : IsMeasurablePartition ξ) {D : Set (ℤ → α)} (hD : MeasurableSet D) (hD0 : μ Dᶜ = 0)
    (hin : ∀ x ∈ D, pullShift ξ x = refineZero ξ x) (hsub : ∀ x ∈ D, ξ x ⊆ D)
    (hout : ∀ x ∉ D, pullShift ξ x ⊆ Dᶜ) :
    ∀ᵐ x ∂μ, ∀ A : Set (ℤ → α), MeasurableSet A →
      condMeas μ ξ x ({y | y 0 = x 0} ∩ shift 1 ⁻¹' A) =
        condMeas μ ξ x {y | y 0 = x 0} * condMeas μ ξ (shift 1 x) A := by
  filter_upwards [condMeas_pullShift hinv ξ,
    condMeas_pullShift_ae_eq_refineZero μ hξ hD hD0 hin hsub hout, condMeas_refineZero μ hξ,
    condMeas_zeroCyl_pos μ ξ] with x hT hE hC hpos A hA
  have h1 : condMeas μ (refineZero ξ) x (shift 1 ⁻¹' A) = condMeas μ ξ (shift 1 x) A := by
    rw [← hE, hT, Measure.map_apply (measurable_shift (-1)) (measurable_shift 1 hA)]
    congr 1
    ext z
    simp only [mem_preimage, shift_shift]
    simp
  rw [hC, ProbabilityTheory.cond_apply (measurableSet_zeroCyl _)] at h1
  rw [← h1, ← mul_assoc, ENNReal.mul_inv_cancel hpos.ne' (measure_ne_top _ _), one_mul]

end UpperDim


/-! ### Feng's proof of (5.6) with `ℓ = 1`: the transverse dimension -/

section Transverse

/-- Maker's theorem in the triangular form of Feng, Lemma 2.3 (after Maker, Duke Math. J. 6
(1940)), for an ergodic map: if `f_k → g` almost everywhere with `|f_k| ≤ F ∈ L¹`, then
`n⁻¹ ∑_{j<n} f_{n-j}(T^j x) → ∫ g dμ` almost everywhere. The library proves the form
`n⁻¹ ∑_{k<n} f_k(T^k x)` (`maker_ergodic`); the triangular form differs by a terminal block of
`N` terms, each at most `2 F(T^j x)` with `j > n - N`, and `F(T^n x)/n → 0` by Birkhoff's
theorem. -/
theorem maker_triangular_ergodic {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {T : X → X} (hT : Ergodic T μ) {f : ℕ → X → ℝ} {g F : X → ℝ}
    (hf : ∀ k, Measurable (f k)) (hg : Measurable g) (hF : Integrable F μ)
    (hbound : ∀ᵐ x ∂μ, ∀ k, |f k x| ≤ F x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => f k x) atTop (𝓝 (g x))) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f (n - j) (T^[j] x))
      atTop (𝓝 (∫ x, g x ∂μ)) := by
  have hT' := hT.toMeasurePreserving
  have hgF : ∀ᵐ x ∂μ, |g x| ≤ F x := by
    filter_upwards [hbound, hlim] with x hb hl
    exact le_of_tendsto ((continuous_abs.tendsto _).comp hl) (Eventually.of_forall hb)
  have hgi : Integrable g μ :=
    hF.mono' hg.aestronglyMeasurable (by simpa [Real.norm_eq_abs] using hgF)
  have hgood : ∀ᵐ x ∂μ, (∀ k, |f k x| ≤ F x) ∧ |g x| ≤ F x ∧
      Tendsto (fun k => f k x) atTop (𝓝 (g x)) := by
    filter_upwards [hbound, hgF, hlim] with x h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have horbit : ∀ᵐ x ∂μ, ∀ j, (∀ k, |f k (T^[j] x)| ≤ F (T^[j] x)) ∧
      |g (T^[j] x)| ≤ F (T^[j] x) :=
    ae_all_iff.2 fun j => (hT'.iterate j).quasiMeasurePreserving.ae
      (p := fun y => (∀ k, |f k y| ≤ F y) ∧ |g y| ≤ F y) (hgood.mono fun _ hx => ⟨hx.1, hx.2.1⟩)
  set H : ℕ → X → ℝ := tailSup f g with hH
  have hHm : ∀ N, Measurable (H N) := measurable_tailSup hf hg
  have hHbd : ∀ N, ∀ᵐ x ∂μ, ‖H N x‖ ≤ 2 * F x := fun N => by
    filter_upwards [hgood] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (tailSup_nonneg f g N x)]
    exact tailSup_le hx.1 hx.2.1 N
  have hHi : ∀ N, Integrable (H N) μ := fun N =>
    (hF.const_mul 2).mono' (hHm N).aestronglyMeasurable (hHbd N)
  have hHint : Tendsto (fun N => ∫ x, H N x ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun x => 2 * F x)
      (fun N => (hHm N).aestronglyMeasurable) (hF.const_mul 2) hHbd
      (hgood.mono fun x hx => tendsto_tailSup hx.2.2)
    simpa using h
  have hBH : ∀ᵐ x ∂μ, ∀ N, Tendsto (fun n => birkhoffAverage ℝ T (H N) n x) atTop
      (𝓝 (∫ x, H N x ∂μ)) := ae_all_iff.2 fun N => birkhoff_ergodic hT (hHi N)
  have hBF := birkhoff_ergodic hT hF
  -- the triangular error
  set e : ℕ → X → ℝ := fun n x =>
    (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, |f (n - j) (T^[j] x) - g (T^[j] x)| with he
  have he0 : ∀ n x, 0 ≤ e n x := fun n x =>
    mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg n)) (Finset.sum_nonneg fun j _ => abs_nonneg _)
  have hsmall : ∀ k : ℕ, ∀ᵐ x ∂μ, ∀ᶠ n in atTop, e n x ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hHint.eventually (gt_mem_nhds (half_pos hk)))
    have hIN := hN N le_rfl
    filter_upwards [horbit, hBH, hBF] with x hx hBHx hBFx
    -- the terminal block of `N` terms is negligible
    set S : ℕ → ℝ := fun m => ∑ j ∈ Finset.range m, F (T^[j] x) with hS
    have hSlim : Tendsto (fun m : ℕ => S m / m) atTop (𝓝 (∫ x, F x ∂μ)) :=
      hBFx.congr fun m => by
        simp only [birkhoffAverage, birkhoffSum, smul_eq_mul, hS, inv_mul_eq_div]
    have hSlim' : Tendsto (fun n : ℕ => S (n - N) / n) atTop (𝓝 (∫ x, F x ∂μ)) := by
      have h1 := hSlim.comp (tendsto_sub_atTop_nat N)
      have h2 : Tendsto (fun n : ℕ => ((n - N : ℕ) : ℝ) / n) atTop (𝓝 1) := by
        have h3 : Tendsto (fun n : ℕ => 1 - (N : ℝ) / n) atTop (𝓝 1) := by
          simpa using (tendsto_const_div_atTop_nhds_zero_nat (N : ℝ)).const_sub 1
        refine h3.congr' ?_
        filter_upwards [eventually_ge_atTop N, eventually_gt_atTop 0] with n hn hn0
        have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
        rw [Nat.cast_sub hn]
        field_simp
      have h4 := h1.mul h2
      rw [mul_one] at h4
      refine h4.congr' ?_
      filter_upwards [eventually_gt_atTop N] with n hn
      have hnN : ((n - N : ℕ) : ℝ) ≠ 0 := by
        have : 0 < n - N := Nat.sub_pos_of_lt hn
        exact_mod_cast this.ne'
      simp only [Function.comp_apply]
      field_simp
    have hterm : Tendsto (fun n : ℕ => (S n - S (n - N)) / n) atTop (𝓝 0) := by
      have := hSlim.sub hSlim'
      rw [sub_self] at this
      exact this.congr fun n => by rw [sub_div]
    filter_upwards [(hBHx N).eventually (gt_mem_nhds (show ∫ x, H N x ∂μ <
        ∫ x, H N x ∂μ + 1 / ((k : ℝ) + 1) / 4 by linarith)),
      hterm.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / ((k : ℝ) + 1) / 8 by positivity)),
      eventually_ge_atTop N] with n h1 h2 hn
    have hnn : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg n)
    -- the termwise bound
    have hterm' : ∀ j ∈ Finset.range n, |f (n - j) (T^[j] x) - g (T^[j] x)| ≤
        H N (T^[j] x) + (if j ∈ Finset.Ico (n - N) n then 2 * F (T^[j] x) else 0) := by
      intro j hj
      rw [Finset.mem_range] at hj
      by_cases hjN : j < n - N
      · have hidx : n - j = N + (n - j - N) := by omega
        have := abs_sub_le_tailSup (hx j).1 (hx j).2 N (n - j - N)
        rw [← hidx] at this
        have hmem : j ∉ Finset.Ico (n - N) n := by
          rw [Finset.mem_Ico]
          omega
        simp only [hmem, ↓reduceIte, add_zero]
        exact this
      · have hmem : j ∈ Finset.Ico (n - N) n := by
          rw [Finset.mem_Ico]
          omega
        simp only [hmem, ↓reduceIte]
        have h0 := tailSup_nonneg f g N (T^[j] x)
        have hf' := (hx j).1 (n - j)
        have hg' := (hx j).2
        calc |f (n - j) (T^[j] x) - g (T^[j] x)|
            ≤ |f (n - j) (T^[j] x)| + |g (T^[j] x)| := abs_sub _ _
          _ ≤ H N (T^[j] x) + 2 * F (T^[j] x) := by linarith
    have hsum : ∑ j ∈ Finset.range n, |f (n - j) (T^[j] x) - g (T^[j] x)| ≤
        ∑ j ∈ Finset.range n, H N (T^[j] x) + 2 * (S n - S (n - N)) := by
      refine (Finset.sum_le_sum hterm').trans (le_of_eq ?_)
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, hS]
      congr 1
      have hfilt : (Finset.range n).filter (fun j => j ∈ Finset.Ico (n - N) n) =
          Finset.Ico (n - N) n := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      rw [hfilt, ← Finset.mul_sum, Finset.sum_Ico_eq_sub _ (Nat.sub_le n N)]
    have hbirk : (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, H N (T^[j] x) =
        birkhoffAverage ℝ T (H N) n x := by
      simp only [birkhoffAverage, birkhoffSum, smul_eq_mul]
    calc e n x ≤ (n : ℝ)⁻¹ * (∑ j ∈ Finset.range n, H N (T^[j] x) +
          2 * (S n - S (n - N))) := mul_le_mul_of_nonneg_left hsum hnn
      _ = birkhoffAverage ℝ T (H N) n x + 2 * ((S n - S (n - N)) / n) := by
          rw [mul_add, hbirk, div_eq_inv_mul]
          ring
      _ ≤ 1 / ((k : ℝ) + 1) := by linarith
  have hE : ∀ᵐ x ∂μ, Tendsto (fun n => e n x) atTop (𝓝 0) := by
    filter_upwards [ae_all_iff.2 hsmall] with x hx
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨M, hM⟩ := eventually_atTop.1 (hx k)
    refine ⟨M, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (he0 n x)]
    exact (hM n hn).trans_lt hk
  filter_upwards [hE, birkhoff_ergodic hT hgi] with x hEx hgx
  have hdiff : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f (n - j) (T^[j] x) -
      birkhoffAverage ℝ T g n x) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hEx
    rw [birkhoffAverage, birkhoffSum, smul_eq_mul, ← mul_sub, ← Finset.sum_sub_distrib,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg n))]
    exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
      (inv_nonneg.2 (Nat.cast_nonneg n))
  have h := hdiff.add hgx
  simp only [sub_add_cancel, zero_add] at h
  exact h

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `σ^j(σ 𝐢) = σ^{j+1} 𝐢`. -/
theorem shift_natCast_shift_one (x : ℤ → α) (j : ℕ) :
    shift (j : ℤ) (shift 1 x) = shift ((j + 1 : ℕ) : ℤ) x := by
  rw [shift_shift]
  push_cast
  ring_nf

/-- Feng's proof of (5.6) (pp. 36 to 38) with `ℓ = 1` and exact scaling, at the generality of a
partition `ζ` of the shift space, a monotone family of Borel tubes `T(x, r)` and a scaling factor
`κ` with `κ_0 ≤ κ ≤ 1` and `∫ log κ dμ = L < 0`, such that
`μ_x^ζ([x_0] ∩ T(x, κ(x) r)) = μ_x^ζ([x_0]) μ_{σx}^ζ(T(σx, r))` (Lemma 5.4 with Lemma 4.5 (3)).
Given the density limit `μ_x^ζ([x_0] ∩ T(x, r)) / μ_x^ζ(T(x, r)) → μ_x^{ζ'}([x_0])` of
Proposition 5.5 and an integrable envelope of the logarithms of these ratios (Lemma 2.5 (2)),
`liminf_{r → 0} log μ_x^ζ(T(x, r)) / log r ≥ (H(ζ') - H(ζ)) / L` almost everywhere, where
`H(ζ) = H_μ(𝒫 | \widehat{ζ})`.

With `ρ_n(x) = ∏_{k<n} κ(σ^k x)` and `G_k(x) = log` of the ratio at radius `ρ_k(x)`, the one-step
identity gives `log μ_x^ζ(T(x, ρ_n(x))) = ∑_{j<n} (log μ_{σ^j x}^ζ([x_j]) - G_{n-j}(σ^j x)) +
log μ_{σ^n x}^ζ(T(σ^n x, 1))`; Maker's theorem, Birkhoff's theorem and the interpolation between
the radii `ρ_n(x)` conclude. -/
theorem ae_transverseDimGe_of_step (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (ζ ζ' : (ℤ → α) → Set (ℤ → α))
    (T : (ℤ → α) → ℝ → Set (ℤ → α)) (hTmono : ∀ x, Monotone (T x))
    (κ : (ℤ → α) → ℝ) (hκm : Measurable κ) {κ0 : ℝ} (hκ0 : 0 < κ0)
    (hκ : ∀ x, κ0 ≤ κ x ∧ κ x ≤ 1) {L : ℝ} (hL : L < 0)
    (hκint : ∫ x, Real.log (κ x) ∂μ = L)
    (hstep : ∀ᵐ x ∂μ, ∀ r : ℝ, condMeas μ ζ x ({y | y 0 = x 0} ∩ T x (κ x * r)) =
      condMeas μ ζ x {y | y 0 = x 0} * condMeas μ ζ (shift 1 x) (T (shift 1 x) r))
    (hpos : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < condMeas μ ζ x (T x r))
    (hmeas : ∀ R : (ℤ → α) → ℝ, Measurable R →
      Measurable (fun x => condMeas μ ζ x (T x (R x))) ∧
        Measurable (fun x => condMeas μ ζ x ({y | y 0 = x 0} ∩ T x (R x))))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun r => (condMeas μ ζ x).real ({y | y 0 = x 0} ∩ T x r) /
      (condMeas μ ζ x).real (T x r)) (𝓝[>] 0) (𝓝 ((condMeas μ ζ' x).real {y | y 0 = x 0})))
    (henv : ∃ F : (ℤ → α) → ℝ, Integrable F μ ∧ ∀ᵐ x ∂μ, ∀ r ∈ Ioc (0 : ℝ) 1,
      -Real.log ((condMeas μ ζ x).real ({y | y 0 = x 0} ∩ T x r) /
        (condMeas μ ζ x).real (T x r)) ≤ F x) :
    ∀ᵐ x ∂μ, ∀ c' < (condEntropy μ ζ' - condEntropy μ ζ) / L, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      c' ≤ Real.log ((condMeas μ ζ x).real (T x r)) / Real.log r := by
  classical
  have hinv := herg.toMeasurePreserving
  obtain ⟨F, hFi, hF⟩ := henv
  set C : (ℤ → α) → Set (ℤ → α) := fun x => {y | y 0 = x 0} with hC
  -- the radii `ρ_n(x) = ∏_{k<n} κ(σ^k x)`
  set ρ : ℕ → (ℤ → α) → ℝ := fun n x => ∏ k ∈ Finset.range n, κ (shift (k : ℤ) x) with hρ
  have hκpos : ∀ x, 0 < κ x := fun x => hκ0.trans_le (hκ x).1
  have hρpos : ∀ n x, 0 < ρ n x := fun n x => Finset.prod_pos fun k _ => hκpos _
  have hρle : ∀ n x, ρ n x ≤ 1 := fun n x =>
    Finset.prod_le_one₀ (fun k _ => (hκpos _).le) (fun k _ => (hκ _).2)
  have hρsucc : ∀ n x, ρ (n + 1) x = κ x * ρ n (shift 1 x) := by
    intro n x
    simp only [hρ]
    rw [Finset.prod_range_succ', mul_comm]
    simp only [Nat.cast_zero, shift_zero, shift_natCast_shift_one]
  have hρsucc' : ∀ n x, ρ (n + 1) x = ρ n x * κ (shift (n : ℤ) x) := fun n x =>
    Finset.prod_range_succ _ _
  have hρanti : ∀ x, Antitone fun n => ρ n x := fun x => antitone_nat_of_succ_le fun n => by
    rw [hρsucc']
    exact mul_le_of_le_one_right (hρpos n x).le (hκ _).2
  have hρm : ∀ n, Measurable (ρ n) := fun n =>
    Finset.measurable_prod _ fun k _ => hκm.comp (measurable_shift _)
  have hlogκ : Integrable (fun x => Real.log (κ x)) μ := by
    refine Integrable.of_bound (hκm.log.aestronglyMeasurable) (-Real.log κ0)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_le]
    have h1 := Real.log_le_log hκ0 (hκ x).1
    have h2 := Real.log_nonpos (hκpos x).le (hκ x).2
    constructor <;> linarith
  have hρlim : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => Real.log (ρ n x) / n) atTop (𝓝 L) := by
    have h := birkhoff_ergodic herg hlogκ
    rw [hκint] at h
    filter_upwards [h] with x hx
    refine hx.congr fun n => ?_
    simp only [birkhoffAverage, birkhoffSum, iterate_shift_one, smul_eq_mul, inv_mul_eq_div, hρ]
    rw [Real.log_prod fun k _ => (hκpos _).ne']
  have hρ0 : ∀ᵐ x ∂μ, Tendsto (fun n => ρ n x) atTop (𝓝[>] 0) := by
    filter_upwards [hρlim] with x hx
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => hρpos n x⟩
    have hbot : Tendsto (fun n : ℕ => Real.log (ρ n x)) atTop atBot := by
      refine (hx.neg_mul_atTop hL tendsto_natCast_atTop_atTop).congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    exact (Real.tendsto_exp_atBot.comp hbot).congr fun n => Real.exp_log (hρpos n x)
  -- the information functions
  set Q : (ℤ → α) → ℝ := fun x => -condInfo μ ζ x with hQ
  have hQi : Integrable Q μ := (integrable_condInfo μ ζ).neg
  have hQeq : ∀ x, Q x = Real.log ((condMeas μ ζ x).real (C x)) := fun x => by
    simp [hQ, condInfo, hC]
  set Ginf : (ℤ → α) → ℝ := fun x => -condInfo μ ζ' x with hGinf
  -- the logarithmic ratios and masses at the radii `ρ_n`
  set G : ℕ → (ℤ → α) → ℝ := fun k x => Real.log ((condMeas μ ζ x).real (C x ∩ T x (ρ k x)) /
    (condMeas μ ζ x).real (T x (ρ k x))) with hG
  set Φ : ℕ → (ℤ → α) → ℝ := fun n x => Real.log ((condMeas μ ζ x).real (T x (ρ n x)))
    with hΦ
  -- good points and their orbits
  have hgood : ∀ᵐ x ∂μ, (∀ r : ℝ, condMeas μ ζ x (C x ∩ T x (κ x * r)) =
      condMeas μ ζ x (C x) * condMeas μ ζ (shift 1 x) (T (shift 1 x) r)) ∧
      (∀ r : ℝ, 0 < r → 0 < condMeas μ ζ x (T x r)) ∧ 0 < condMeas μ ζ x (C x) := by
    filter_upwards [hstep, hpos, condMeas_zeroCyl_pos μ ζ] with x h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have horbit : ∀ᵐ x ∂μ, ∀ j : ℕ, (∀ r : ℝ, condMeas μ ζ (shift (j : ℤ) x)
      (C (shift (j : ℤ) x) ∩ T (shift (j : ℤ) x) (κ (shift (j : ℤ) x) * r)) =
      condMeas μ ζ (shift (j : ℤ) x) (C (shift (j : ℤ) x)) *
        condMeas μ ζ (shift 1 (shift (j : ℤ) x)) (T (shift 1 (shift (j : ℤ) x)) r)) ∧
      (∀ r : ℝ, 0 < r → 0 < condMeas μ ζ (shift (j : ℤ) x) (T (shift (j : ℤ) x) r)) ∧
      0 < condMeas μ ζ (shift (j : ℤ) x) (C (shift (j : ℤ) x)) :=
    ae_all_iff.2 fun j => (measurePreserving_shift_natCast hinv j).quasiMeasurePreserving.ae hgood
  -- the one-step recurrence
  have hrec : ∀ x, (∀ r : ℝ, condMeas μ ζ x (C x ∩ T x (κ x * r)) =
      condMeas μ ζ x (C x) * condMeas μ ζ (shift 1 x) (T (shift 1 x) r)) →
      (∀ r : ℝ, 0 < r → 0 < condMeas μ ζ x (T x r)) → 0 < condMeas μ ζ x (C x) →
      (∀ r : ℝ, 0 < r → 0 < condMeas μ ζ (shift 1 x) (T (shift 1 x) r)) →
      ∀ n, Φ (n + 1) x = Q x + Φ n (shift 1 x) - G (n + 1) x := by
    intro x hs hp hc hp1 n
    have hr := hρpos n (shift 1 x)
    have hA := hs (ρ n (shift 1 x))
    have ha : 0 < (condMeas μ ζ x).real (C x) := ENNReal.toReal_pos hc.ne' (measure_ne_top _ _)
    have hb : 0 < (condMeas μ ζ (shift 1 x)).real (T (shift 1 x) (ρ n (shift 1 x))) :=
      ENNReal.toReal_pos (hp1 _ hr).ne' (measure_ne_top _ _)
    have hB : 0 < (condMeas μ ζ x).real (T x (ρ (n + 1) x)) :=
      ENNReal.toReal_pos (hp _ (hρpos _ _)).ne' (measure_ne_top _ _)
    have hAr : (condMeas μ ζ x).real (C x ∩ T x (ρ (n + 1) x)) = (condMeas μ ζ x).real (C x) *
        (condMeas μ ζ (shift 1 x)).real (T (shift 1 x) (ρ n (shift 1 x))) := by
      rw [hρsucc, measureReal_def, hA, ENNReal.toReal_mul]
      rfl
    simp only [hΦ, hG, hQeq]
    rw [hAr, Real.log_div (mul_pos ha hb).ne' hB.ne', Real.log_mul ha.ne' hb.ne']
    ring
  -- the telescoping identity along the orbit
  have htel : ∀ᵐ x ∂μ, ∀ n, Φ n x = ∑ j ∈ Finset.range n,
      (Q (shift (j : ℤ) x) - G (n - j) (shift (j : ℤ) x)) + Φ 0 (shift (n : ℤ) x) := by
    filter_upwards [horbit] with x hx
    intro n
    induction n generalizing x with
    | zero => simp
    | succ n ih =>
      have h0 := hx 0
      have h1 := hx 1
      simp only [Nat.cast_zero, shift_zero, Nat.cast_one] at h0 h1
      have hx' : ∀ j : ℕ, _ := fun j => by
        have := hx (j + 1)
        rw [← shift_natCast_shift_one] at this
        exact this
      rw [hrec x h0.1 h0.2.1 h0.2.2 h1.2.1 n, ih (shift 1 x) hx', Finset.sum_range_succ']
      simp only [Nat.cast_zero, shift_zero, shift_natCast_shift_one, Nat.sub_zero,
        Nat.add_sub_add_right]
      ring
  -- Maker's theorem for `G_k` and Birkhoff's theorem for `Q`
  have hGm : ∀ k, Measurable (G k) := fun k => by
    obtain ⟨h1, h2⟩ := hmeas (ρ k) (hρm k)
    simp only [hG, measureReal_def]
    exact (h2.ennreal_toReal.div h1.ennreal_toReal).log
  have hGinfm : Measurable Ginf := (measurable_condInfo μ ζ').neg
  have hGle : ∀ᵐ x ∂μ, ∀ k, |G k x| ≤ F x := by
    filter_upwards [hF, hpos] with x hx hp k
    have hT : 0 < (condMeas μ ζ x).real (T x (ρ k x)) :=
      ENNReal.toReal_pos (hp _ (hρpos k x)).ne' (measure_ne_top _ _)
    have hratio : (condMeas μ ζ x).real (C x ∩ T x (ρ k x)) /
        (condMeas μ ζ x).real (T x (ρ k x)) ≤ 1 :=
      div_le_one_of_le₀ (measureReal_mono inter_subset_right) hT.le
    have hG0 : G k x ≤ 0 := Real.log_nonpos (div_nonneg measureReal_nonneg hT.le) hratio
    rw [abs_of_nonpos hG0]
    exact hx (ρ k x) ⟨hρpos k x, hρle k x⟩
  have hGlim : ∀ᵐ x ∂μ, Tendsto (fun k => G k x) atTop (𝓝 (Ginf x)) := by
    filter_upwards [hlim, hρ0, condMeas_zeroCyl_pos μ ζ'] with x hx hρx hpos'
    have hp : 0 < (condMeas μ ζ' x).real {y | y 0 = x 0} :=
      ENNReal.toReal_pos hpos'.ne' (measure_ne_top _ _)
    have h1 := ((Real.continuousAt_log hp.ne').tendsto).comp (hx.comp hρx)
    have hGinfx : Ginf x = Real.log ((condMeas μ ζ' x).real {y | y 0 = x 0}) := by
      simp [hGinf, condInfo]
    rw [hGinfx]
    exact h1
  have hmaker := maker_triangular_ergodic herg hGm hGinfm hFi hGle hGlim
  have hbirk := birkhoff_ergodic herg hQi
  have hint_Ginf : ∫ x, Ginf x ∂μ = -condEntropy μ ζ' := by
    simp only [hGinf, integral_neg, condEntropy]
  have hint_Q : ∫ x, Q x ∂μ = -condEntropy μ ζ := by
    simp only [hQ, integral_neg, condEntropy]
  rw [hint_Ginf] at hmaker
  rw [hint_Q] at hbirk
  simp only [iterate_shift_one] at hmaker
  simp only [birkhoffAverage, birkhoffSum, iterate_shift_one, smul_eq_mul] at hbirk
  -- the final combination
  filter_upwards [htel, hmaker, hbirk, hρlim, hρ0, hpos] with x htx hmx hbx hlx hρx hpx
  intro c' hc'
  set D0 := condEntropy μ ζ - condEntropy μ ζ' with hD0
  have hv := hmx.sub hbx
  have hvlim : -condEntropy μ ζ' - -condEntropy μ ζ = D0 := by rw [hD0]; ring
  rw [hvlim] at hv
  have hΦle : ∀ n : ℕ, 0 < n → (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, G (n - j) (shift (j : ℤ) x) -
      (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, Q (shift (j : ℤ) x) ≤ -Φ n x / n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hΦ0 : Φ 0 (shift (n : ℤ) x) ≤ 0 :=
      Real.log_nonpos measureReal_nonneg measureReal_le_one
    rw [htx n, Finset.sum_sub_distrib, ← mul_sub, inv_mul_eq_div]
    gcongr
    linarith
  rcases lt_or_ge c' 0 with hc'0 | hc'0
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with r ⟨hr0, hr1⟩
    have h1 : Real.log ((condMeas μ ζ x).real (T x r)) ≤ 0 :=
      Real.log_nonpos measureReal_nonneg measureReal_le_one
    have h2 : Real.log r < 0 := Real.log_neg hr0 hr1
    have := div_nonneg_of_nonpos h1 h2.le
    linarith
  · obtain ⟨c'', hc'c'', hc''c⟩ := exists_between hc'
    have hc''pos : 0 < c'' := hc'0.trans_lt hc'c''
    have hkey : c'' * (-L) < D0 := by
      have hc_eq : (condEntropy μ ζ' - condEntropy μ ζ) / L = D0 / (-L) := by
        rw [hD0, div_neg, ← neg_div]
        ring_nf
      rw [hc_eq, lt_div_iff₀ (by linarith)] at hc''c
      linarith
    set gap := D0 - c'' * (-L) with hgap
    have hgap0 : 0 < gap := by linarith
    set δ := gap / (2 * (c'' + 1)) with hδ
    have hδ0 : 0 < δ := div_pos hgap0 (by linarith)
    have hδgap : δ * (c'' + 1) < gap := by
      rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    have hev : ∀ᶠ n : ℕ in atTop, Φ n x ≤ c'' * Real.log (ρ n x) := by
      filter_upwards [hv.eventually (lt_mem_nhds (show D0 - δ < D0 by linarith)),
        hlx.eventually (lt_mem_nhds (show L - δ < L by linarith)), eventually_gt_atTop 0]
        with n hn1 hn2 hn0
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
      have h1 := hn1.trans_le (hΦle n hn0)
      rw [lt_div_iff₀ hn'] at h1 hn2
      nlinarith
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    set K := c'' * (-Real.log κ0) / (c'' - c') with hK
    have hmin : 0 < min (min (ρ N x) 1) (Real.exp (-K)) :=
      lt_min (lt_min (hρpos N x) one_pos) (Real.exp_pos _)
    filter_upwards [Ioo_mem_nhdsGT hmin] with r ⟨hr0, hrlt⟩
    have hrN : r < ρ N x := hrlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hr1 : r < 1 := hrlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hrK : r < Real.exp (-K) := hrlt.trans_le (min_le_right _ _)
    have hex : ∃ n, ρ (n + 1) x < r := by
      obtain ⟨M, hM⟩ := eventually_atTop.1
        ((tendsto_nhdsWithin_iff.1 hρx).1.eventually (gt_mem_nhds hr0))
      exact ⟨M, hM (M + 1) (Nat.le_succ M)⟩
    set n := Nat.find hex with hn
    have hn1 : ρ (n + 1) x < r := Nat.find_spec hex
    have hn2 : r ≤ ρ n x := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos'
      · rw [h0]
        simp only [hρ, Finset.range_zero, Finset.prod_empty]
        exact hr1.le
      · obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        have := Nat.find_min hex (show k < n by omega)
        rw [hk]
        exact not_lt.1 this
    have hnN : N ≤ n := by
      by_contra hlt
      rw [not_le] at hlt
      have : ρ N x ≤ ρ (n + 1) x := hρanti x (by omega)
      linarith
    have hmT : 0 < (condMeas μ ζ x).real (T x r) :=
      ENNReal.toReal_pos (hpx r hr0).ne' (measure_ne_top _ _)
    have hlog1 : Real.log ((condMeas μ ζ x).real (T x r)) ≤ Φ n x :=
      Real.log_le_log hmT (measureReal_mono (hTmono x hn2))
    have hlog2 : Φ n x ≤ c'' * Real.log (ρ n x) := hN n hnN
    have hlog3 : Real.log (ρ n x) + Real.log κ0 < Real.log r := by
      have hle : ρ n x * κ0 ≤ ρ (n + 1) x := by
        rw [hρsucc']
        exact mul_le_mul_of_nonneg_left (hκ _).1 (hρpos n x).le
      rw [← Real.log_mul (hρpos n x).ne' hκ0.ne']
      exact Real.log_lt_log (mul_pos (hρpos n x) hκ0) (hle.trans_lt hn1)
    have hlogr : Real.log r < -K := by
      have := Real.log_lt_log hr0 hrK
      rwa [Real.log_exp] at this
    have hlogκ0 : Real.log κ0 ≤ 0 := Real.log_nonpos hκ0.le ((hκ x).1.trans (hκ x).2)
    have hKeq : K * (c'' - c') = c'' * (-Real.log κ0) := by
      rw [hK]
      field_simp [show c'' - c' ≠ 0 by linarith]
    rw [le_div_iff_of_neg (Real.log_neg hr0 hr1)]
    nlinarith

end Transverse

/-! ### Feng, Proposition 5.5 for a coordinate on the atoms -/

open scoped NNReal

section Maximal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology X] [HasBesicovitchCovering X]

/-- The weak maximal inequality for ratios of balls (Feng, (5.18), after Feng–Hu, Lemma 3.3),
from the Besicovitch covering theorem: there is `N` such that for all measures `κ`, `ν` on a
Besicovitch space, all `R` and `t`, the `κ`-mass of the points `z` with
`κ(B(z, r)) ≤ t ν(B(z, r))` for some `r ∈ (0, R]` is at most `N t ν(X)`. This is
`ExactOverlaps.exists_ballRatio_maximal_constant`, there stated on `ℝ`, with the same proof. -/
theorem exists_ballRatio_maximal_constant_of_besicovitch :
    ∃ N : ℕ, ∀ (κ ν : Measure X) (R : ℝ) (t : ℝ≥0∞),
    κ {x | ∃ r, 0 < r ∧ r ≤ R ∧ κ (closedBall x r) ≤ t * ν (closedBall x r)} ≤
      (N : ℝ≥0∞) * (t * ν univ) := by
  classical
  obtain ⟨N, τ, hτ, hN⟩ := HasBesicovitchCovering.no_satelliteConfig (α := X)
  refine ⟨N, fun κ ν R t => ?_⟩
  let E := {x : X | ∃ r, 0 < r ∧ r ≤ R ∧ κ (closedBall x r) ≤ t * ν (closedBall x r)}
  choose r hr using fun x : E ↦ x.property
  let q : Besicovitch.BallPackage E X :=
    { c := fun x ↦ x
      r := r
      rpos := fun x ↦ (hr x).1
      r_bound := R
      r_le := fun x ↦ (hr x).2.1 }
  obtain ⟨A, hdisj, hcover⟩ := Besicovitch.exist_disjoint_covering_families hτ hN q
  have hcount : ∀ i, (A i).Countable := by
    intro i
    apply (hdisj i).countable_of_nonempty_interior
    intro j _
    exact (nonempty_ball.mpr (q.rpos j)).mono ball_subset_interior_closedBall
  have hone : ∀ i, κ (⋃ j ∈ A i, closedBall (q.c j) (q.r j)) ≤ t * ν univ := by
    intro i
    calc
      κ (⋃ j ∈ A i, closedBall (q.c j) (q.r j)) ≤
          ∑' j : A i, κ (closedBall (q.c j) (q.r j)) :=
        measure_biUnion_le κ (hcount i) _
      _ ≤ ∑' j : A i, t * ν (closedBall (q.c j) (q.r j)) := by
        exact ENNReal.tsum_le_tsum (fun j ↦ (hr j.1).2.2)
      _ = t * ∑' j : A i, ν (closedBall (q.c j) (q.r j)) := ENNReal.tsum_mul_left
      _ ≤ t * ν univ := by
        apply mul_le_mul le_rfl _ bot_le bot_le
        apply tsum_measure_le_measure_univ (fun _ ↦ measurableSet_closedBall.nullMeasurableSet)
        exact ((pairwise_subtype_iff_pairwise_set _ _).2 (hdisj i)).aedisjoint
  have hE : E ⊆ ⋃ i : Fin N, ⋃ j ∈ A i, closedBall (q.c j) (q.r j) := by
    intro x hx
    have hh := hcover (show x ∈ range q.c from ⟨⟨x, hx⟩, rfl⟩)
    simp only [mem_iUnion] at hh ⊢
    obtain ⟨i, j, hj, h⟩ := hh
    exact ⟨i, j, hj, ball_subset_closedBall h⟩
  calc
    κ E ≤ κ (⋃ i : Fin N, ⋃ j ∈ A i, closedBall (q.c j) (q.r j)) := measure_mono hE
    _ ≤ ∑' i : Fin N, κ (⋃ j ∈ A i, closedBall (q.c j) (q.r j)) := measure_iUnion_le _
    _ ≤ ∑' _i : Fin N, t * ν univ := ENNReal.tsum_le_tsum hone
    _ = (N : ℝ≥0∞) * (t * ν univ) := by simp

end Maximal

section RightContinuity

/-- The mass of the sublevel sets `A ∩ {g ≤ s}` of a Borel function is right-continuous in `s`:
the closed tubes of Feng, Proposition 5.5, decrease to the closed tube as the radius decreases. -/
theorem tendsto_measure_inter_sublevel {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsFiniteMeasure ν] {g : Ω → ℝ} (hg : Measurable g) {A : Set Ω} (hA : MeasurableSet A)
    (r : ℝ) : Tendsto (fun s => ν (A ∩ {y | g y ≤ s})) (𝓝[>] r)
      (𝓝 (ν (A ∩ {y | g y ≤ r}))) := by
  have h := tendsto_measure_biInter_gt (μ := ν) (s := fun s => A ∩ {y | g y ≤ s}) (a := r)
    (fun s _ => (hA.inter (measurableSet_le hg measurable_const)).nullMeasurableSet)
    (fun i j _ hij y hy => ⟨hy.1, le_trans hy.2 hij⟩) ⟨r + 1, by linarith, measure_ne_top _ _⟩
  have heq : (⋂ s > r, A ∩ {y | g y ≤ s}) = A ∩ {y | g y ≤ r} := by
    ext y
    simp only [mem_iInter, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hy
      exact ⟨(hy (r + 1) (by linarith)).1,
        le_of_forall_gt_imp_ge_of_dense fun s hs => (hy s hs).2⟩
    · rintro ⟨hyA, hy⟩ s hs
      exact ⟨hyA, hy.trans hs.le⟩
  rw [heq] at h
  exact h

/-- For the density limit of Feng, Proposition 5.5: a function on `(0, ∞)` that is
right-continuous and converges to `L` along the rationals converges to `L` at `0⁺`. -/
theorem tendsto_nhdsGT_zero_of_rat {f : ℝ → ℝ} {L : ℝ}
    (hf : ∀ r : ℝ, 0 < r → Tendsto f (𝓝[>] r) (𝓝 (f r)))
    (h : ∀ k : ℕ, ∃ m : ℕ, ∀ q : ℚ, 0 < q → (q : ℝ) < 1 / ((m : ℝ) + 1) →
      |f q - L| ≤ 1 / ((k : ℝ) + 1)) :
    Tendsto f (𝓝[>] 0) (𝓝 L) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨m, hm⟩ := h k
  refine ⟨1 / ((m : ℝ) + 1), by positivity, fun r hr hdist => ?_⟩
  have hr0 : 0 < r := hr
  rw [Real.dist_eq, sub_zero, abs_of_pos hr0] at hdist
  rw [Real.dist_eq]
  refine lt_of_le_of_lt ?_ hk
  by_contra hcon
  rw [not_le] at hcon
  set η := |f r - L| - 1 / ((k : ℝ) + 1) with hη
  have hη0 : 0 < η := by linarith
  have hev := (hf r hr0).eventually (Metric.ball_mem_nhds (f r) hη0)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min hu hdist)
  have hqu : (q : ℝ) ∈ Ioo r u := ⟨hq1, hq2.trans_le (min_le_left _ _)⟩
  have h1 : dist (f q) (f r) < η := hsub hqu
  rw [Real.dist_eq] at h1
  have h2 := hm q (by exact_mod_cast hr0.trans hq1) (hq2.trans_le (min_le_right _ _))
  have h3 : |f r - L| ≤ |f q - f r| + |f q - L| := by
    calc |f r - L| = |(f q - L) - (f q - f r)| := by ring_nf
      _ ≤ |f q - L| + |f q - f r| := abs_sub _ _
      _ = |f q - f r| + |f q - L| := add_comm _ _
  linarith

/-- For the envelope of Feng, Proposition 5.5: a right-continuous function below `t` at `r` is
below `t` at a rational point of `(r, R)`. -/
theorem exists_rat_lt_of_tendsto_nhdsGT {f : ℝ → ℝ} {r R t : ℝ}
    (hf : Tendsto f (𝓝[>] r) (𝓝 (f r))) (hrR : r < R) (ht : f r < t) :
    ∃ q : ℚ, r < q ∧ (q : ℝ) < R ∧ f q < t := by
  have hev := hf.eventually (gt_mem_nhds ht)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min hu hrR)
  exact ⟨q, hq1, hq2.trans_le (min_le_right _ _),
    hsub ⟨hq1, hq2.trans_le (min_le_left _ _)⟩⟩

end RightContinuity

section RatioContinuity

/-- The density ratio `ν(A ∩ {g ≤ s}) / ν({g ≤ s})` of Feng, Proposition 5.5, is right-continuous
in the radius `s` where `ν({g ≤ s}) ≠ 0`. -/
theorem tendsto_ratio_sublevel_nhdsGT {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsFiniteMeasure ν] {g : Ω → ℝ} (hg : Measurable g) {A : Set Ω} (hA : MeasurableSet A)
    {r : ℝ} (hr : ν {y | g y ≤ r} ≠ 0) :
    Tendsto (fun s => ν.real (A ∩ {y | g y ≤ s}) / ν.real {y | g y ≤ s}) (𝓝[>] r)
      (𝓝 (ν.real (A ∩ {y | g y ≤ r}) / ν.real {y | g y ≤ r})) := by
  have h1 := tendsto_measure_inter_sublevel ν hg hA r
  have h2 := tendsto_measure_inter_sublevel ν hg MeasurableSet.univ r
  simp only [univ_inter] at h2
  simp only [measureReal_def]
  exact ((ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h1).div
    ((ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h2)
    (ENNReal.toReal_pos hr (measure_ne_top _ _)).ne'

/-- `a.toReal / b.toReal < c` with `a ≤ b < ∞` gives `a ≤ c b`: the passage from the real density
ratios of Feng, Proposition 5.5, to the masses of the maximal inequality (5.18). -/
theorem le_ofReal_mul_of_toReal_div_lt {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) (hab : a ≤ b)
    {c : ℝ} (h : a.toReal / b.toReal < c) : a ≤ ENNReal.ofReal c * b := by
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [le_bot_iff.1 hab]
    exact bot_le
  · have hbpos : 0 < b.toReal := ENNReal.toReal_pos hb0 hb
    rw [div_lt_iff₀ hbpos] at h
    have hc : 0 ≤ c := by
      by_contra hc
      rw [not_le] at hc
      have := mul_neg_of_neg_of_pos hc hbpos
      linarith [ENNReal.toReal_nonneg (a := a)]
    calc a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal ha).symm
      _ ≤ ENNReal.ofReal (c * b.toReal) := ENNReal.ofReal_le_ofReal h.le
      _ = ENNReal.ofReal c * b := by rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_toReal hb]

end RatioContinuity

section Coordinate

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [CompleteSpace X] [HasBesicovitchCovering X]

/-- The tube `{𝐣 : d(Φ_𝐢(𝐣), Φ_𝐢(𝐢)) ≤ r}` of a coordinate `Φ_𝐢` attached to the point `𝐢`, the
form of the tubes of Feng, Proposition 5.5, for `ℓ = 1`. -/
def coordTube (Φ : (ℤ → α) → (ℤ → α) → X) (x : ℤ → α) (r : ℝ) : Set (ℤ → α) :=
  {y | dist (Φ x y) (Φ x x) ≤ r}

/-- A coordinate `Φ_𝐢` on the atoms of `ζ`, constant along each atom, whose fibres in the atom
`ζ(𝐢)` are the atoms of `ζ'`: the setting of Feng, Proposition 5.5, for `ℓ = 1`. -/
structure IsFibreCoordinate (ζ ζ' : (ℤ → α) → Set (ℤ → α)) (Φ : (ℤ → α) → (ℤ → α) → X) :
    Prop where
  /-- `(𝐢, 𝐣) ↦ Φ_𝐢(𝐣)` is Borel. -/
  measurable : Measurable (Function.uncurry Φ)
  /-- The coordinate depends only on the atom of `ζ`. -/
  const : ∀ x y, y ∈ ζ x → Φ y = Φ x
  /-- Within `ζ(𝐢)`, the atom `ζ'(𝐢)` is the fibre of `Φ_𝐢` through `𝐢`. -/
  fibre : ∀ x y, y ∈ ζ x → (y ∈ ζ' x ↔ Φ x y = Φ x x)

omit [CompleteSpace X] [HasBesicovitchCovering X] in
/-- The masses `μ_𝐢^ζ(T(𝐢, r))` and `μ_𝐢^ζ([i_0] ∩ T(𝐢, r))` of the coordinate tubes are Borel
functions of `𝐢`, Feng, Proposition 5.5. -/
theorem measurable_condMeas_coordTube (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (ζ : (ℤ → α) → Set (ℤ → α)) {Φ : (ℤ → α) → (ℤ → α) → X}
    (hΦ : Measurable (Function.uncurry Φ)) (r : ℝ) :
    Measurable (fun x => condMeas μ ζ x (coordTube Φ x r)) ∧
      Measurable (fun x => condMeas μ ζ x ({y | y 0 = x 0} ∩ coordTube Φ x r)) := by
  have hd : Measurable fun p : (ℤ → α) × (ℤ → α) => dist (Φ p.1 p.2) (Φ p.1 p.1) :=
    hΦ.dist (hΦ.comp (measurable_fst.prodMk measurable_fst))
  have ht : MeasurableSet {p : (ℤ → α) × (ℤ → α) | dist (Φ p.1 p.2) (Φ p.1 p.1) ≤ r} :=
    measurableSet_le hd measurable_const
  have hc : MeasurableSet {p : (ℤ → α) × (ℤ → α) | p.2 0 = p.1 0} :=
    measurableSet_eq_fun ((measurable_pi_apply 0).comp measurable_snd)
      ((measurable_pi_apply 0).comp measurable_fst)
  refine ⟨?_, ?_⟩
  · have h := Kernel.measurable_kernel_prodMk_left (κ := condMeasKernel μ ζ) ht
    convert h using 2 with x
    rfl
  · have h := Kernel.measurable_kernel_prodMk_left (κ := condMeasKernel μ ζ) (hc.inter ht)
    convert h using 2 with x
    rfl

/-- The mass `μ_𝐢^ζ([i_0])`, the limit in Feng, Proposition 5.5, is a Borel function of `𝐢`. -/
theorem measurable_condMeas_zeroCyl (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (ζ : (ℤ → α) → Set (ℤ → α)) : Measurable fun x => condMeas μ ζ x {y | y 0 = x 0} := by
  have hc : MeasurableSet {p : (ℤ → α) × (ℤ → α) | p.2 0 = p.1 0} :=
    measurableSet_eq_fun ((measurable_pi_apply 0).comp measurable_snd)
      ((measurable_pi_apply 0).comp measurable_fst)
  have h := Kernel.measurable_kernel_prodMk_left (κ := condMeasKernel μ ζ) hc
  convert h using 2 with x
  rfl

omit [HasBesicovitchCovering X] in
/-- The identification of the density in Feng, Proposition 5.5 (through his Lemma 2.5 and
`double_conditional`): for `μ`-almost every `𝐣` and `μ_𝐣^ζ`-almost every `𝐲`, the
Radon–Nikodym derivative of `Φ_𝐣 * (μ_𝐣^ζ|_A)` with respect to `Φ_𝐣 * μ_𝐣^ζ` at `Φ_𝐣(𝐲)` is
`μ_𝐲^{ζ'}(A)`. The atoms of `ζ'` are the fibres of `𝐲 ↦ (f(𝐲), Φ_𝐲(𝐲))`, `f` inducing `ζ`, so
`\widehat{ζ'}` is the pull-back of the Borel sets under this map (Blackwell) and `𝐲 ↦ μ_𝐲^{ζ'}(A)`
factors through it (Doob–Dynkin). -/
theorem ae_ae_rnDeriv_eq_condMeas (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ]
    {ζ ζ' : (ℤ → α) → Set (ℤ → α)} (hζ : IsMeasurablePartition ζ)
    (hζ' : IsMeasurablePartition ζ') (hfine : ∀ x, ζ' x ⊆ ζ x)
    {Φ : (ℤ → α) → (ℤ → α) → X} (hΦ : IsFibreCoordinate ζ ζ' Φ) {A : Set (ℤ → α)}
    (hA : MeasurableSet A) :
    ∀ᵐ j ∂μ, ∀ᵐ y ∂condMeas μ ζ j,
      (((condMeas μ ζ j).restrict A).map (Φ j)).rnDeriv ((condMeas μ ζ j).map (Φ j)) (Φ j y) =
        condMeas μ ζ' y A := by
  obtain ⟨f, hf, hfζ⟩ := hζ
  set F : (ℤ → α) → ℝ × X := fun y => (f y, Φ y y) with hF
  have hFm : Measurable F :=
    hf.prodMk (hΦ.measurable.comp (measurable_id.prodMk measurable_id))
  have hFζ' : ∀ x y, y ∈ ζ' x ↔ F y = F x := by
    intro x y
    constructor
    · intro hy
      have hyx : y ∈ ζ x := hfine x hy
      have h1 := hΦ.const x y hyx
      have h2 := (hΦ.fibre x y hyx).1 hy
      simp only [hF, Prod.mk.injEq]
      exact ⟨(hfζ x y).1 hyx, by rw [h1, h2]⟩
    · intro h
      simp only [hF, Prod.mk.injEq] at h
      have hyx : y ∈ ζ x := (hfζ x y).2 h.1
      have h1 := hΦ.const x y hyx
      refine (hΦ.fibre x y hyx).2 ?_
      rw [← h.2, h1]
  have hsat : saturated ζ' = MeasurableSpace.comap F inferInstance :=
    saturated_eq_comap hFm hFζ'
  filter_upwards [condMeas_atom μ ⟨f, hf, hfζ⟩,
    (double_conditional μ ⟨f, hf, hfζ⟩ hζ' hfine).1] with j hj hdc
  set ν := condMeas μ ζ j with hν
  have hφ : Measurable (Φ j) := hΦ.measurable.comp measurable_prodMk_left
  have hatom : MeasurableSet (ζ j) := IsMeasurablePartition.measurableSet_atom ⟨f, hf, hfζ⟩ j
  have hcompl : ν (ζ j)ᶜ = 0 := (prob_compl_eq_zero_iff hatom).2 hj
  have hνζ : ∀ᵐ y ∂ν, y ∈ ζ j := by
    rw [ae_iff]
    exact hcompl
  -- Doob–Dynkin
  have hg : Measurable[MeasurableSpace.comap F inferInstance] fun y => condMeas ν ζ' y A := by
    rw [← hsat]
    exact measurable_condMeas ν ζ' hA
  obtain ⟨G, hGm, hGeq⟩ := hg.exists_eq_measurable_comp
  set Gj : X → ℝ≥0∞ := fun z => G (f j, z) with hGj
  have hGjm : Measurable Gj := hGm.comp measurable_prodMk_left
  have hGjeq : ∀ y ∈ ζ j, Gj (Φ j y) = condMeas ν ζ' y A := by
    intro y hy
    rw [show condMeas ν ζ' y A = G (F y) from congrFun hGeq y]
    simp only [hGj, hF, (hfζ j y).1 hy, hΦ.const j y hy]
  have hκ : (ν.restrict A).map (Φ j) = (ν.map (Φ j)).withDensity Gj := by
    ext B hB
    rw [Measure.map_apply hφ hB, Measure.restrict_apply (hφ hB), withDensity_apply _ hB,
      setLIntegral_map hB hGjm hφ]
    have hS : MeasurableSet[saturated ζ'] (F ⁻¹' ({f j} ×ˢ B)) := by
      rw [hsat]
      exact ⟨_, (measurableSet_singleton _).prod hB, rfl⟩
    have hSeq : F ⁻¹' ({f j} ×ˢ B) = Φ j ⁻¹' B ∩ ζ j := by
      ext y
      simp only [mem_preimage, mem_prod, mem_singleton_iff, mem_inter_iff, hF]
      constructor
      · rintro ⟨h1, h2⟩
        have hy : y ∈ ζ j := (hfζ j y).2 h1
        exact ⟨by rwa [hΦ.const j y hy] at h2, hy⟩
      · rintro ⟨h2, hy⟩
        exact ⟨(hfζ j y).1 hy, by rwa [hΦ.const j y hy]⟩
    have hae : Φ j ⁻¹' B ∩ ζ j =ᵐ[ν] Φ j ⁻¹' B := by
      have : ζ j =ᵐ[ν] (univ : Set (ℤ → α)) := ae_eq_univ.2 hcompl
      have h2 : (Φ j ⁻¹' B ∩ ζ j : Set (ℤ → α)) =ᵐ[ν] (Φ j ⁻¹' B ∩ univ : Set (ℤ → α)) :=
        ae_eq_set_inter (ae_eq_refl _) this
      rwa [inter_univ] at h2
    calc ν (Φ j ⁻¹' B ∩ A) = ν (A ∩ (Φ j ⁻¹' B ∩ ζ j)) := by
          rw [inter_comm]
          have h2 : (A ∩ Φ j ⁻¹' B : Set (ℤ → α)) =ᵐ[ν] (A ∩ (Φ j ⁻¹' B ∩ ζ j) : Set (ℤ → α)) :=
            ae_eq_set_inter (ae_eq_refl _) hae.symm
          exact measure_congr h2
      _ = ∫⁻ y in Φ j ⁻¹' B ∩ ζ j, condMeas ν ζ' y A ∂ν := by
          rw [← hSeq, setLIntegral_condMeas ν ζ' hA hS]
      _ = ∫⁻ y in Φ j ⁻¹' B ∩ ζ j, Gj (Φ j y) ∂ν :=
          setLIntegral_congr_fun ((hφ hB).inter hatom) fun y hy => (hGjeq y hy.2).symm
      _ = ∫⁻ y in Φ j ⁻¹' B, Gj (Φ j y) ∂ν := by rw [Measure.restrict_congr_set hae]
  have hrn := Measure.rnDeriv_withDensity (ν.map (Φ j)) hGjm
  rw [← hκ] at hrn
  filter_upwards [ae_of_ae_map hφ.aemeasurable hrn, hνζ, hdc] with y hy1 hy2 hy3
  rw [hy1, hGjeq y hy2, hy3]

/-- Feng, Proposition 5.5, the density limit, on the atoms: for `μ`-almost every `𝐣` and
`μ_𝐣^ζ`-almost every `𝐲`, `μ_𝐲^ζ([y_0] ∩ T(𝐲, r)) / μ_𝐲^ζ(T(𝐲, r)) → μ_𝐲^{ζ'}([y_0])` as
`r → 0⁺`. On the atom `ζ(𝐣)` the ratio is that of `Φ_𝐣 * (μ_𝐣^ζ|_{[a]})` and `Φ_𝐣 * μ_𝐣^ζ` on
the ball `B(Φ_𝐣(𝐲), r)`, which tends to the Radon–Nikodym derivative by Besicovitch's
differentiation theorem; `ae_ae_rnDeriv_eq_condMeas` identifies it. -/
theorem ae_ae_tendsto_ratio_coordTube (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ]
    {ζ ζ' : (ℤ → α) → Set (ℤ → α)} (hζ : IsMeasurablePartition ζ)
    (hζ' : IsMeasurablePartition ζ') (hfine : ∀ x, ζ' x ⊆ ζ x)
    {Φ : (ℤ → α) → (ℤ → α) → X} (hΦ : IsFibreCoordinate ζ ζ' Φ) :
    ∀ᵐ j ∂μ, ∀ᵐ y ∂condMeas μ ζ j, Tendsto (fun r =>
      (condMeas μ ζ y).real ({z | z 0 = y 0} ∩ coordTube Φ y r) /
        (condMeas μ ζ y).real (coordTube Φ y r)) (𝓝[>] 0)
      (𝓝 ((condMeas μ ζ' y).real {z | z 0 = y 0})) := by
  have hcyl : ∀ a : α, MeasurableSet {z : ℤ → α | z 0 = a} := fun a =>
    show MeasurableSet ((fun y : ℤ → α => y 0) ⁻¹' {a}) from
      measurable_pi_apply (0 : ℤ) (measurableSet_singleton a)
  filter_upwards [condMeas_atom μ hζ, ae_all_iff.2 fun a =>
    ae_ae_rnDeriv_eq_condMeas μ hζ hζ' hfine hΦ (hcyl a)] with j hj hid
  set ν := condMeas μ ζ j with hν
  have hφ : Measurable (Φ j) := hΦ.measurable.comp measurable_prodMk_left
  have hνζ : ∀ᵐ y ∂ν, y ∈ ζ j := by
    rw [ae_iff]
    exact (prob_compl_eq_zero_iff (hζ.measurableSet_atom j)).2 hj
  have hbes : ∀ a : α, ∀ᵐ y ∂ν, Tendsto (fun r =>
      ((ν.restrict {z | z 0 = a}).map (Φ j)) (closedBall (Φ j y) r) /
        (ν.map (Φ j)) (closedBall (Φ j y) r)) (𝓝[>] 0)
      (𝓝 (((ν.restrict {z | z 0 = a}).map (Φ j)).rnDeriv (ν.map (Φ j)) (Φ j y))) := fun a =>
    ae_of_ae_map hφ.aemeasurable (Besicovitch.ae_tendsto_rnDeriv _ _)
  filter_upwards [ae_all_iff.2 hbes, ae_all_iff.2 hid, hνζ] with y hb hi hy
  have hcm : condMeas μ ζ y = ν := (condMeas_eq_of_mem μ hy).symm
  have hT : ∀ r, coordTube Φ y r = Φ j ⁻¹' closedBall (Φ j y) r := by
    intro r
    ext z
    simp only [coordTube, mem_ofPred_eq, mem_preimage, mem_closedBall, hΦ.const j y hy]
  have hlim := hb (y 0)
  rw [hi (y 0)] at hlim
  refine ((ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hlim).congr fun r => ?_
  simp only [Function.comp_apply, measureReal_def, hcm, hT, ENNReal.toReal_div]
  rw [Measure.map_apply hφ measurableSet_closedBall, Measure.map_apply hφ measurableSet_closedBall,
    Measure.restrict_apply (hφ measurableSet_closedBall), inter_comm]

/-- Feng, Proposition 5.5, the density limit (p. 34, through his Lemma 2.5 (1) and Feng–Hu,
Proposition 3.5), for a coordinate on the atoms: if the coordinate tubes have positive mass,
then `μ_𝐱^ζ([x_0] ∩ T(𝐱, r)) / μ_𝐱^ζ(T(𝐱, r)) → μ_𝐱^{ζ'}([x_0])` as `r → 0⁺` for `μ`-almost
every `𝐱`. The convergence along the rationals defines a Borel set, which has full
`μ_𝐣^ζ`-measure for almost every `𝐣` (`ae_ae_tendsto_ratio_coordTube`), hence full
`μ`-measure; the ratios are right-continuous in `r`. -/
theorem ae_tendsto_ratio_coordTube (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ]
    {ζ ζ' : (ℤ → α) → Set (ℤ → α)} (hζ : IsMeasurablePartition ζ)
    (hζ' : IsMeasurablePartition ζ') (hfine : ∀ x, ζ' x ⊆ ζ x)
    {Φ : (ℤ → α) → (ℤ → α) → X} (hΦ : IsFibreCoordinate ζ ζ' Φ)
    (hpos : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < condMeas μ ζ x (coordTube Φ x r)) :
    ∀ᵐ x ∂μ, Tendsto (fun r => (condMeas μ ζ x).real ({y | y 0 = x 0} ∩ coordTube Φ x r) /
        (condMeas μ ζ x).real (coordTube Φ x r)) (𝓝[>] 0)
      (𝓝 ((condMeas μ ζ' x).real {y | y 0 = x 0})) := by
  set ρ : (ℤ → α) → ℝ → ℝ := fun x r =>
    (condMeas μ ζ x).real ({y | y 0 = x 0} ∩ coordTube Φ x r) /
      (condMeas μ ζ x).real (coordTube Φ x r) with hρ
  set L : (ℤ → α) → ℝ := fun x => (condMeas μ ζ' x).real {y | y 0 = x 0} with hL
  have hρm : ∀ r, Measurable fun x => ρ x r := fun r => by
    obtain ⟨h1, h2⟩ := measurable_condMeas_coordTube μ ζ hΦ.measurable r
    simp only [hρ, measureReal_def]
    exact h2.ennreal_toReal.div h1.ennreal_toReal
  have hLm : Measurable L := (measurable_condMeas_zeroCyl μ ζ').ennreal_toReal
  set G1 : Set (ℤ → α) := {x | ∀ k : ℕ, ∃ m : ℕ, ∀ q : ℚ, 0 < q →
    (q : ℝ) < 1 / ((m : ℝ) + 1) → |ρ x q - L x| ≤ 1 / ((k : ℝ) + 1)} with hG1
  have hG1m : MeasurableSet G1 := by
    have : G1 = ⋂ k : ℕ, ⋃ m : ℕ, ⋂ q : ℚ, ⋂ (_ : 0 < q ∧ (q : ℝ) < 1 / ((m : ℝ) + 1)),
        {x | |ρ x q - L x| ≤ 1 / ((k : ℝ) + 1)} := by
      ext x
      simp only [hG1, mem_ofPred_eq, mem_iInter, mem_iUnion, and_imp]
    rw [this]
    exact MeasurableSet.iInter fun k => MeasurableSet.iUnion fun m =>
      MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ =>
        measurableSet_le (continuous_abs.measurable.comp ((hρm q).sub hLm)) measurable_const
  have hmemG : ∀ x, Tendsto (fun r => ρ x r) (𝓝[>] 0) (𝓝 (L x)) → x ∈ G1 := by
    intro x hx k
    rw [Metric.tendsto_nhdsWithin_nhds] at hx
    obtain ⟨δ, hδ, hδ'⟩ := hx (1 / ((k : ℝ) + 1)) (by positivity)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    refine ⟨m, fun q hq hqm => ?_⟩
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have h := hδ' (show (q : ℝ) ∈ Ioi 0 from hq')
      (by rw [Real.dist_eq, sub_zero, abs_of_pos hq']; linarith)
    rw [Real.dist_eq] at h
    exact h.le
  have hnull : μ G1ᶜ = 0 := by
    have h := setLIntegral_condMeas μ ζ hG1m.compl
      (MeasurableSet.univ : MeasurableSet[saturated ζ] univ)
    rw [Measure.restrict_univ, inter_univ] at h
    have hae : ∀ᵐ j ∂μ, condMeas μ ζ j G1ᶜ = 0 := by
      filter_upwards [ae_ae_tendsto_ratio_coordTube μ hζ hζ' hfine hΦ] with j hj
      exact measure_eq_zero_iff_ae_notMem.2 (hj.mono fun y hy hc => hc (hmemG y hy))
    rw [← h, lintegral_congr_ae hae, lintegral_zero]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull, hpos] with x hx hp
  have hxG : x ∈ G1 := not_not.1 hx
  have hg : Measurable fun y => dist (Φ x y) (Φ x x) :=
    (hΦ.measurable.comp measurable_prodMk_left).dist measurable_const
  have hcx : MeasurableSet {y : ℤ → α | y 0 = x 0} :=
    show MeasurableSet ((fun y : ℤ → α => y 0) ⁻¹' {x 0}) from
      measurable_pi_apply (0 : ℤ) (measurableSet_singleton _)
  exact tendsto_nhdsGT_zero_of_rat (f := fun r => ρ x r)
    (fun r hr => tendsto_ratio_sublevel_nhdsGT (condMeas μ ζ x) hg hcx (hp r hr).ne') hxG

omit [CompleteSpace X] in
/-- Feng, Proposition 5.5, integrability of `g` (5.14) (pp. 35 to 36, after Feng–Hu, Lemma 3.3
and Proposition 3.5), for a coordinate on the atoms: if the coordinate tubes have positive mass,
the logarithmic densities `-log(μ_𝐱^ζ([x_0] ∩ T(𝐱, r)) / μ_𝐱^ζ(T(𝐱, r)))`, `r ∈ (0, 1]`, have
an integrable envelope. On each atom, the weak maximal inequality
`exists_ballRatio_maximal_constant_of_besicovitch` for `Φ_𝐣 * (μ_𝐣^ζ|_{[a]})` and
`Φ_𝐣 * μ_𝐣^ζ` bounds by `N e^{-n}` the mass of the set `E_n` of the points with a ratio below
`e^{-n}` at some rational radius in `(0, 2)`, Feng's (5.18); integrated over the atoms and
summed over the finitely many letters `a`, it gives `μ(E_n) ≤ |α| N e^{-n}`, so
`∑ (n + 1) μ(E_n) < ∞`. The ratios are right-continuous in `r`, so the rational radii control
every radius. -/
theorem exists_envelope_coordTube (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ]
    {ζ : (ℤ → α) → Set (ℤ → α)} (hζ : IsMeasurablePartition ζ)
    {Φ : (ℤ → α) → (ℤ → α) → X} (hΦm : Measurable (Function.uncurry Φ))
    (hΦc : ∀ x y, y ∈ ζ x → Φ y = Φ x)
    (hpos : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < condMeas μ ζ x (coordTube Φ x r)) :
    ∃ F : (ℤ → α) → ℝ, Integrable F μ ∧ ∀ᵐ x ∂μ, ∀ r ∈ Ioc (0 : ℝ) 1,
      -Real.log ((condMeas μ ζ x).real ({y | y 0 = x 0} ∩ coordTube Φ x r) /
        (condMeas μ ζ x).real (coordTube Φ x r)) ≤ F x := by
  classical
  obtain ⟨N, hN⟩ := exists_ballRatio_maximal_constant_of_besicovitch (X := X)
  have hcyl : ∀ a : α, MeasurableSet {z : ℤ → α | z 0 = a} := fun a =>
    show MeasurableSet ((fun y : ℤ → α => y 0) ⁻¹' {a}) from
      measurable_pi_apply (0 : ℤ) (measurableSet_singleton a)
  set ρ : (ℤ → α) → ℝ → ℝ := fun x r =>
    (condMeas μ ζ x).real ({y | y 0 = x 0} ∩ coordTube Φ x r) /
      (condMeas μ ζ x).real (coordTube Φ x r) with hρ
  have hρm : ∀ r, Measurable fun x => ρ x r := fun r => by
    obtain ⟨h1, h2⟩ := measurable_condMeas_coordTube μ ζ hΦm r
    simp only [hρ, measureReal_def]
    exact h2.ennreal_toReal.div h1.ennreal_toReal
  -- the exceptional sets
  set E : ℕ → Set (ℤ → α) := fun n =>
    {x | ∃ q : ℚ, 0 < q ∧ (q : ℝ) < 2 ∧ ρ x q < Real.exp (-(n : ℝ))} with hE
  have hEm : ∀ n, MeasurableSet (E n) := fun n => by
    have : E n = ⋃ q : ℚ, ⋃ (_ : 0 < q ∧ (q : ℝ) < 2), {x | ρ x q < Real.exp (-(n : ℝ))} := by
      ext x
      simp only [hE, mem_ofPred_eq, mem_iUnion, exists_prop, and_assoc]
    rw [this]
    exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
      measurableSet_lt (hρm q) measurable_const
  -- Feng's (5.18) on each atom
  have hatomE : ∀ n : ℕ, ∀ a : α, ∀ᵐ j ∂μ, condMeas μ ζ j (E n ∩ {z | z 0 = a}) ≤
      (N : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(n : ℝ))) := by
    intro n a
    filter_upwards [condMeas_atom μ hζ] with j hj
    set ν := condMeas μ ζ j with hν
    have hφ : Measurable (Φ j) := hΦm.comp measurable_prodMk_left
    set t := ENNReal.ofReal (Real.exp (-(n : ℝ))) with ht
    set Z : Set X := {z | ∃ r, 0 < r ∧ r ≤ 2 ∧ ((ν.restrict {z | z 0 = a}).map (Φ j))
      (closedBall z r) ≤ t * (ν.map (Φ j)) (closedBall z r)} with hZ
    have hsub : E n ∩ {z | z 0 = a} ⊆ (ζ j)ᶜ ∪ (Φ j ⁻¹' Z ∩ {z | z 0 = a}) := by
      rintro y ⟨⟨q, hq0, hq2, hqρ⟩, hya⟩
      by_cases hy : y ∈ ζ j
      · right
        refine ⟨⟨q, by exact_mod_cast hq0, hq2.le, ?_⟩, hya⟩
        have hcm : condMeas μ ζ y = ν := (condMeas_eq_of_mem μ hy).symm
        have hT : coordTube Φ y q = Φ j ⁻¹' closedBall (Φ j y) q := by
          ext z
          simp only [coordTube, mem_ofPred_eq, mem_preimage, mem_closedBall, hΦc j y hy]
        have hya' : y 0 = a := hya
        simp only [hρ, hcm, hT, hya', measureReal_def] at hqρ
        rw [Measure.map_apply hφ measurableSet_closedBall,
          Measure.map_apply hφ measurableSet_closedBall,
          Measure.restrict_apply (hφ measurableSet_closedBall), inter_comm]
        exact le_ofReal_mul_of_toReal_div_lt (measure_ne_top _ _) (measure_ne_top _ _)
          (measure_mono inter_subset_right) hqρ
      · exact Or.inl hy
    calc condMeas μ ζ j (E n ∩ {z | z 0 = a})
        ≤ ν (ζ j)ᶜ + ν (Φ j ⁻¹' Z ∩ {z | z 0 = a}) :=
          (measure_mono hsub).trans (measure_union_le _ _)
      _ = (ν.restrict {z | z 0 = a}) (Φ j ⁻¹' Z) := by
          rw [(prob_compl_eq_zero_iff (hζ.measurableSet_atom j)).2 hj, zero_add,
            Measure.restrict_apply' (hcyl a)]
      _ ≤ ((ν.restrict {z | z 0 = a}).map (Φ j)) Z := Measure.le_map_apply hφ.aemeasurable _
      _ ≤ (N : ℝ≥0∞) * (t * (ν.map (Φ j)) univ) := hN _ _ 2 t
      _ = (N : ℝ≥0∞) * t := by
          rw [Measure.map_apply hφ MeasurableSet.univ, preimage_univ, measure_univ, mul_one]
  -- integration over the atoms
  have hEn : ∀ n : ℕ, μ (E n) ≤
      (Fintype.card α : ℝ≥0∞) * ((N : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(n : ℝ)))) := by
    intro n
    have hcover : E n ⊆ ⋃ a : α, E n ∩ {z | z 0 = a} := fun y hy =>
      mem_iUnion.2 ⟨y 0, hy, rfl⟩
    calc μ (E n) ≤ ∑ a : α, μ (E n ∩ {z | z 0 = a}) :=
          (measure_mono hcover).trans (measure_iUnion_fintype_le _ _)
      _ ≤ ∑ _a : α, (N : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(n : ℝ))) := by
          refine Finset.sum_le_sum fun a _ => ?_
          have h := setLIntegral_condMeas μ ζ ((hEm n).inter (hcyl a))
            (MeasurableSet.univ : MeasurableSet[saturated ζ] univ)
          rw [Measure.restrict_univ, inter_univ] at h
          rw [← h]
          calc ∫⁻ j, condMeas μ ζ j (E n ∩ {z | z 0 = a}) ∂μ
              ≤ ∫⁻ _j, (N : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(n : ℝ))) ∂μ :=
                lintegral_mono_ae (hatomE n a)
            _ = (N : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(n : ℝ))) := by
                rw [lintegral_const, measure_univ, mul_one]
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- the weighted sum of the masses is finite
  set q : ℝ≥0 := ⟨Real.exp (-1), (Real.exp_pos _).le⟩ with hq
  have hq1 : q < 1 := by
    change Real.exp (-1) < 1
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  have hqn : ∀ n : ℕ, ENNReal.ofReal (Real.exp (-(n : ℝ))) = (q : ℝ≥0∞) ^ n := by
    intro n
    have h1 : Real.exp (-(n : ℝ)) = Real.exp (-1) ^ n := by
      rw [← Real.exp_nat_mul]
      ring_nf
    rw [h1, ENNReal.ofReal_pow (Real.exp_pos _).le,
      ENNReal.ofReal_eq_coe_nnreal (Real.exp_pos _).le]
    rfl
  have hsum : (∑' n : ℕ, (n + 1 : ℝ≥0∞) * μ (E n)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := (Fintype.card α : ℝ≥0∞) * (N : ℝ≥0∞) *
      ∑' n : ℕ, (n + 1 : ℝ≥0∞) * (q : ℝ≥0∞) ^ n) ?_ ?_
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp))
        (ExactOverlaps.weighted_geometric_tsum_ne_top hq1)
    · rw [← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun n => ?_
      calc (n + 1 : ℝ≥0∞) * μ (E n)
          ≤ (n + 1 : ℝ≥0∞) * ((Fintype.card α : ℝ≥0∞) *
            ((N : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(n : ℝ))))) := by gcongr; exact hEn n
        _ = (Fintype.card α : ℝ≥0∞) * (N : ℝ≥0∞) * ((n + 1 : ℝ≥0∞) * (q : ℝ≥0∞) ^ n) := by
          rw [hqn n]
          ring
  obtain ⟨G, -, hGi, hG0, hG⟩ :=
    ExactOverlaps.exists_integrable_envelope_of_weighted_measure_tsum μ E hsum
  refine ⟨fun x => G x + 1, hGi.add (integrable_const 1), ?_⟩
  filter_upwards [hG, hpos] with x hx hp r ⟨hr0, hr1⟩
  change -Real.log (ρ x r) ≤ G x + 1
  have hρ0 : 0 ≤ ρ x r := div_nonneg measureReal_nonneg measureReal_nonneg
  have hρ1 : ρ x r ≤ 1 := div_le_one_of_le₀ (measureReal_mono inter_subset_right)
    measureReal_nonneg
  rcases hρ0.eq_or_lt with h0 | hρpos
  · rw [← h0, Real.log_zero, neg_zero]
    linarith [hG0 x]
  set s := -Real.log (ρ x r) with hs
  have hs0 : 0 ≤ s := neg_nonneg.2 (Real.log_nonpos hρ0 hρ1)
  have hm1 : s < (⌊s⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one s
  rcases Nat.eq_zero_or_pos ⌊s⌋₊ with hm0 | hmpos
  · rw [hm0, Nat.cast_zero, zero_add] at hm1
    linarith [hG0 x]
  obtain ⟨k, hk⟩ : ∃ k, ⌊s⌋₊ = k + 1 := ⟨⌊s⌋₊ - 1, by omega⟩
  have hmle : ((⌊s⌋₊ : ℕ) : ℝ) ≤ s := Nat.floor_le hs0
  rw [hk] at hm1 hmle
  push_cast at hm1 hmle
  have hlt : ρ x r < Real.exp (-(k : ℝ)) := by
    calc ρ x r = Real.exp (-s) := by rw [hs, neg_neg, Real.exp_log hρpos]
      _ ≤ Real.exp (-((k : ℝ) + 1)) := Real.exp_le_exp.2 (by linarith)
      _ < Real.exp (-(k : ℝ)) := Real.exp_lt_exp.2 (by linarith)
  have hg : Measurable fun y => dist (Φ x y) (Φ x x) :=
    (hΦm.comp measurable_prodMk_left).dist measurable_const
  have hrc := tendsto_ratio_sublevel_nhdsGT (condMeas μ ζ x) hg
    (show MeasurableSet ((fun y : ℤ → α => y 0) ⁻¹' {x 0}) from
      measurable_pi_apply (0 : ℤ) (measurableSet_singleton _)) (hp r hr0).ne'
  obtain ⟨q', hq'1, hq'2, hq'3⟩ := exists_rat_lt_of_tendsto_nhdsGT (f := fun r => ρ x r) hrc
    (show r < 2 by linarith) hlt
  have hxE : x ∈ E k := ⟨q', by exact_mod_cast hr0.trans hq'1, hq'2, hq'3⟩
  have := hx k hxE
  linarith

end Coordinate

section Components

/-! ### The planar scalings

In the plane both Oseledets steps are one-dimensional. Let `u_𝐢 = (cos θ, sin θ)` be the unit
vector of the slow line `V_𝐢^1`. For `𝐢 ∈ Σ'` the matrix `A_{i_0}` maps `V_{σ𝐢}^1` onto `V_𝐢^1`,
so `A_{i_0} u_{σ𝐢} = c u_𝐢` with `|c| = κ_2(𝐢)`, and `u_𝐢 ∧ A_{i_0} w = (det A_{i_0} / c)
(u_{σ𝐢} ∧ w)`: `A_{i_0}` multiplies distances to the slow line by `κ_1(𝐢) = |det A_{i_0}| /
κ_2(𝐢)`. Hence Feng's Lemma 5.4 holds with `ℓ(𝐢) = 1`, with equality, with the exact factors
`κ_1`, `κ_2` instead of `e^{ℓ(λ_i - ε)}`, and with no angle between Oseledets subspaces. -/

open Matrix
open scoped Matrix.Norms.L2Operator

/-! ### Euclidean geometry of the plane -/

namespace MatrixTuple

/-- Lagrange's identity in the plane: `(u ∧ v)² + (u · v)² = |u|² |v|²`. -/
theorem cross_sq_add_dot_sq (u v : Fin 2 → ℝ) :
    cross u v ^ 2 + dot u v ^ 2 = (u 0 ^ 2 + u 1 ^ 2) * (v 0 ^ 2 + v 1 ^ 2) := by
  simp only [cross, dot]
  ring

/-- `|u ∧ v| ≤ |u| |v|` for the Euclidean norm. -/
theorem abs_cross_le_eucNorm_mul (u v : Fin 2 → ℝ) : |cross u v| ≤ eucNorm u * eucNorm v := by
  rw [eucNorm_eq, eucNorm_eq, ← Real.sqrt_mul (by positivity)]
  refine Real.abs_le_sqrt ?_
  nlinarith [cross_sq_add_dot_sq u v, sq_nonneg (dot u v)]

/-- The vector `(cos θ, sin θ)` is a Euclidean unit vector. -/
theorem eucNorm_dirVec (θ : ℝ) : eucNorm (dirVec θ) = 1 := by
  rw [eucNorm_eq]
  simp [dirVec, Real.cos_sq_add_sin_sq]

/-- `|M v| ≤ ‖M‖ |v|` for the Euclidean norm and the `ℓ²` operator norm `‖M‖ = α_1(M)`. -/
theorem eucNorm_mulVec_le (M : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) :
    eucNorm (M *ᵥ v) ≤ ‖M‖ * eucNorm v := by
  have := Matrix.l2_opNorm_mulVec M (WithLp.toLp 2 v)
  simpa [eucNorm] using this

/-- `|det M| ≤ |M u| ‖M‖` for a Euclidean unit vector `u`: with `J u` the rotation of `u` by a
right angle, `|det M| = |M u ∧ M J u| ≤ |M u| |M J u|`. -/
theorem abs_det_le_eucNorm_mulVec_mul (M : Matrix (Fin 2) (Fin 2) ℝ) {u : Fin 2 → ℝ}
    (hu : eucNorm u = 1) : |M.det| ≤ eucNorm (M *ᵥ u) * ‖M‖ := by
  have hsq : u 0 ^ 2 + u 1 ^ 2 = 1 := by rw [← eucNorm_sq, hu, one_pow]
  have hcross : cross u (perp u) = 1 := by rw [cross_perp, hsq]
  have hperp : eucNorm (perp u) = 1 := by
    rw [eucNorm_eq]
    simp only [perp, Matrix.cons_val_zero, Matrix.cons_val_one, neg_sq]
    rw [add_comm, hsq, Real.sqrt_one]
  calc |M.det| = |cross (M *ᵥ u) (M *ᵥ perp u)| := by rw [cross_mulVec, hcross, mul_one]
    _ ≤ eucNorm (M *ᵥ u) * eucNorm (M *ᵥ perp u) := abs_cross_le_eucNorm_mul _ _
    _ ≤ eucNorm (M *ᵥ u) * (‖M‖ * eucNorm (perp u)) :=
        mul_le_mul_of_nonneg_left (eucNorm_mulVec_le M _) (eucNorm_nonneg _)
    _ = eucNorm (M *ᵥ u) * ‖M‖ := by rw [hperp, mul_one]

end MatrixTuple

namespace PlanarSystem

variable {ι : Type u} [MeasurableSpace ι] (P : PlanarSystem ι)

/-! ### The slow direction and the two scaling factors -/

/-- The unit vector `u_𝐢 = (cos θ, sin θ)` of the slow line `V_𝐢^1`, `θ` the slow angle. -/
noncomputable def slowDir (μ : Measure (ℤ → ι)) (x : ℤ → ι) : Fin 2 → ℝ :=
  MatrixTuple.dirVec (P.slowAngle μ x)

/-- The factor `κ_2(𝐢) = |A_{i_0} u_{σ𝐢}|` by which `A_{i_0}` maps `V_{σ𝐢}^1` onto `V_𝐢^1`. -/
noncomputable def slowScale (μ : Measure (ℤ → ι)) (x : ℤ → ι) : ℝ :=
  eucNorm (P.mat (x 0) *ᵥ P.slowDir μ (shift 1 x))

/-- The factor `κ_1(𝐢) = |det A_{i_0}| / κ_2(𝐢)` by which `A_{i_0}` multiplies distances to the
slow line. -/
noncomputable def transScale (μ : Measure (ℤ → ι)) (x : ℤ → ι) : ℝ :=
  |(P.mat (x 0)).det| / P.slowScale μ x

/-- The slow direction is a Euclidean unit vector. -/
theorem eucNorm_slowDir (μ : Measure (ℤ → ι)) (x : ℤ → ι) : eucNorm (P.slowDir μ x) = 1 :=
  MatrixTuple.eucNorm_dirVec _

/-- The slow direction is non-zero. -/
theorem slowDir_ne_zero (μ : Measure (ℤ → ι)) (x : ℤ → ι) : P.slowDir μ x ≠ 0 :=
  MatrixTuple.dirVec_ne_zero _

/-- On `Σ'`, a vector lies on the slow line exactly when its determinant with `u_𝐢` vanishes. -/
theorem mem_oseledets_one_iff (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    {x : ℤ → ι} (hx : x ∈ P.SigmaPrime μ) (v : Fin 2 → ℝ) :
    v ∈ P.oseledets μ x 1 ↔ MatrixTuple.cross (P.slowDir μ x) v = 0 := by
  rw [P.oseledets_one_eq μ hlt hx]
  rfl

/-- `κ_2(𝐢) > 0`. -/
theorem slowScale_pos (μ : Measure (ℤ → ι)) (x : ℤ → ι) : 0 < P.slowScale μ x := by
  have h : P.mat (x 0) *ᵥ P.slowDir μ (shift 1 x) ≠ 0 :=
    mulVec_ne_zero_of_det_ne_zero (P.det_ne_zero _) (P.slowDir_ne_zero μ _)
  rw [slowScale, eucNorm]
  exact norm_pos_iff.2 fun h' => h (by simpa using congrArg WithLp.ofLp h')

/-- `κ_1(𝐢) > 0`. -/
theorem transScale_pos (μ : Measure (ℤ → ι)) (x : ℤ → ι) : 0 < P.transScale μ x :=
  div_pos (abs_pos.2 (P.det_ne_zero _)) (P.slowScale_pos μ x)

/-- For `𝐢 ∈ Σ'`, `A_{i_0} u_{σ𝐢} = c u_𝐢` with `|c| = κ_2(𝐢)`: the slow line is invariant, (V1). -/
theorem exists_mulVec_slowDir_eq (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    {x : ℤ → ι} (hx : x ∈ P.SigmaPrime μ) :
    ∃ c : ℝ, P.mat (x 0) *ᵥ P.slowDir μ (shift 1 x) = c • P.slowDir μ x ∧
      |c| = P.slowScale μ x := by
  have hx1 : shift 1 x ∈ P.SigmaPrime μ := (P.shift_mem_SigmaPrime_iff μ x).2 hx
  have hmem : P.slowDir μ (shift 1 x) ∈ P.oseledets μ (shift 1 x) 1 := by
    rw [P.mem_oseledets_one_iff μ hlt hx1]
    simp [MatrixTuple.cross, mul_comm]
  have hA := (P.mulVec_mem_oseledets_iff μ x 1 _).1 hmem
  rw [P.mem_oseledets_one_iff μ hlt hx, ← MatrixTuple.mem_span_iff_cross
    (P.slowDir_ne_zero μ x)] at hA
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hA
  refine ⟨c, hc.symm, ?_⟩
  rw [slowScale, ← hc, MatrixTuple.eucNorm_smul, P.eucNorm_slowDir, mul_one]

/-- The transverse scaling: for `𝐢 ∈ Σ'` and every `w`,
`|u_𝐢 ∧ A_{i_0} w| = κ_1(𝐢) |u_{σ𝐢} ∧ w|`. -/
theorem abs_cross_slowDir_mulVec (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    {x : ℤ → ι} (hx : x ∈ P.SigmaPrime μ) (w : Fin 2 → ℝ) :
    |MatrixTuple.cross (P.slowDir μ x) (P.mat (x 0) *ᵥ w)| =
      P.transScale μ x * |MatrixTuple.cross (P.slowDir μ (shift 1 x)) w| := by
  obtain ⟨c, hc, habs⟩ := P.exists_mulVec_slowDir_eq μ hlt hx
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at habs
    exact (P.slowScale_pos μ x).ne' habs.symm
  have key : c * MatrixTuple.cross (P.slowDir μ x) (P.mat (x 0) *ᵥ w) =
      (P.mat (x 0)).det * MatrixTuple.cross (P.slowDir μ (shift 1 x)) w := by
    rw [← MatrixTuple.cross_mulVec, hc]
    simp only [MatrixTuple.cross, Pi.smul_apply, smul_eq_mul]
    ring
  have key' : MatrixTuple.cross (P.slowDir μ x) (P.mat (x 0) *ᵥ w) =
      (P.mat (x 0)).det / c * MatrixTuple.cross (P.slowDir μ (shift 1 x)) w := by
    field_simp
    linarith [key]
  rw [key', abs_mul, abs_div, habs, transScale]

/-- The scaling along the slow line: for `𝐢 ∈ Σ'` and `w ∈ V_{σ𝐢}^1`, `|A_{i_0} w| = κ_2(𝐢) |w|`. -/
theorem eucNorm_mulVec_of_mem_oseledets (μ : Measure (ℤ → ι))
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) {x : ℤ → ι} (hx : x ∈ P.SigmaPrime μ)
    {w : Fin 2 → ℝ} (hw : w ∈ P.oseledets μ (shift 1 x) 1) :
    eucNorm (P.mat (x 0) *ᵥ w) = P.slowScale μ x * eucNorm w := by
  have hx1 : shift 1 x ∈ P.SigmaPrime μ := (P.shift_mem_SigmaPrime_iff μ x).2 hx
  rw [P.mem_oseledets_one_iff μ hlt hx1, ← MatrixTuple.mem_span_iff_cross
    (P.slowDir_ne_zero μ _)] at hw
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hw
  rw [mulVec_smul, MatrixTuple.eucNorm_smul, MatrixTuple.eucNorm_smul, P.eucNorm_slowDir,
    slowScale]
  ring

/-! ### Differences of projections -/

variable [Finite ι]

omit [Finite ι] in
/-- The Euclidean distance `dist(π𝐣 + V_𝐢^1, π𝐢 + V_𝐢^1)` between the two parallel lines in the
direction of the slow line `V_𝐢^1`, which is `|u_𝐢 ∧ (π𝐣 - π𝐢)|`. -/
noncomputable def transDist (μ : Measure (ℤ → ι)) (x y : ℤ → ι) : ℝ :=
  |MatrixTuple.cross (P.slowDir μ x) (toVec (P.proj y - P.proj x))|

/-- Feng (4.11) in the transverse direction: for `𝐢 ∈ Σ'` and `j_0 = i_0`, the distance of `π𝐣`
to the line `π𝐢 + V_𝐢^1` is `κ_1(𝐢)` times the distance of `π(σ𝐣)` to `π(σ𝐢) + V_{σ𝐢}^1`. -/
theorem transDist_eq_of_head (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    {x y : ℤ → ι} (hx : x ∈ P.SigmaPrime μ) (hy : y 0 = x 0) :
    P.transDist μ x y = P.transScale μ x * P.transDist μ (shift 1 x) (shift 1 y) := by
  rw [transDist, transDist, P.proj_sub_proj hy, P.abs_cross_slowDir_mulVec μ hlt hx]

/-- Feng (4.11) along the slow line: for `𝐢 ∈ Σ'`, `j_0 = i_0` and `π(σ𝐣) - π(σ𝐢) ∈ V_{σ𝐢}^1`,
`|π𝐣 - π𝐢| = κ_2(𝐢) |π(σ𝐣) - π(σ𝐢)|`. -/
theorem eucDist_eq_of_head (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    {x y : ℤ → ι} (hx : x ∈ P.SigmaPrime μ) (hy : y 0 = x 0)
    (hmem : toVec (P.proj (shift 1 y) - P.proj (shift 1 x)) ∈ P.oseledets μ (shift 1 x) 1) :
    eucNorm (toVec (P.proj y - P.proj x)) =
      P.slowScale μ x * eucNorm (toVec (P.proj (shift 1 y) - P.proj (shift 1 x))) := by
  rw [P.proj_sub_proj hy, P.eucNorm_mulVec_of_mem_oseledets μ hlt hx hmem]

/-! ### Feng's Lemma 5.4 in the plane -/

omit [Finite ι] in
/-- Feng's set `Γ_1(𝐢, r) = {𝐣 : dist(π𝐣 + V_𝐢^1, π𝐢 + V_𝐢^1) ≤ r}` of (5.1), without the
intersection with `Σ'`, which the conditional measures do not see. -/
def transTube (μ : Measure (ℤ → ι)) (x : ℤ → ι) (r : ℝ) : Set (ℤ → ι) :=
  {y | P.transDist μ x y ≤ r}

/-- The Euclidean tube `B^π(𝐢, r) = {𝐣 : |π𝐣 - π𝐢| ≤ r}` of Feng (2.3). -/
def eucTube (x : ℤ → ι) (r : ℝ) : Set (ℤ → ι) :=
  {y | eucNorm (toVec (P.proj y - P.proj x)) ≤ r}

/-- Feng, Lemma 5.4 for `i = 1` in the plane, with `ℓ = 1` and equality: for `𝐢 ∈ Σ'`,
`ξ_0(𝐢) ∩ [i_0] ∩ Γ_1(𝐢, κ_1(𝐢) r) = σ⁻¹(ξ_0(σ𝐢) ∩ Γ_1(σ𝐢, r))`. -/
theorem refineZero_xi_zero_inter_transTube (μ : Measure (ℤ → ι))
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) {x : ℤ → ι} (hx : x ∈ P.SigmaPrime μ) (r : ℝ) :
    refineZero (P.xi μ 0) x ∩ P.transTube μ x (P.transScale μ x * r) =
      shift 1 ⁻¹' (P.xi μ 0 (shift 1 x) ∩ P.transTube μ (shift 1 x) r) := by
  have hpull := P.pullShift_xi μ 0 hx
  rw [pullShift] at hpull
  ext y
  simp only [mem_inter_iff, mem_preimage, transTube, mem_ofPred_eq]
  constructor
  · rintro ⟨hy, hd⟩
    have hy' : y ∈ shift 1 ⁻¹' P.xi μ 0 (shift 1 x) := by rw [hpull]; exact hy
    refine ⟨hy', ?_⟩
    rw [P.transDist_eq_of_head μ hlt hx hy.2] at hd
    exact le_of_mul_le_mul_left hd (P.transScale_pos μ x)
  · rintro ⟨hy, hd⟩
    have hy' : y ∈ refineZero (P.xi μ 0) x := by rw [← hpull]; exact hy
    refine ⟨hy', ?_⟩
    rw [P.transDist_eq_of_head μ hlt hx hy'.2]
    exact mul_le_mul_of_nonneg_left hd (P.transScale_pos μ x).le

/-- Feng, Lemma 5.4 for `i = 2` in the plane, with `ℓ = 1` and equality: for `𝐢 ∈ Σ'`,
`ξ_1(𝐢) ∩ [i_0] ∩ B^π(𝐢, κ_2(𝐢) r) = σ⁻¹(ξ_1(σ𝐢) ∩ B^π(σ𝐢, r))`, Euclidean tubes. -/
theorem refineZero_xi_one_inter_eucTube (μ : Measure (ℤ → ι))
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) {x : ℤ → ι} (hx : x ∈ P.SigmaPrime μ) (r : ℝ) :
    refineZero (P.xi μ 1) x ∩ P.eucTube x (P.slowScale μ x * r) =
      shift 1 ⁻¹' (P.xi μ 1 (shift 1 x) ∩ P.eucTube (shift 1 x) r) := by
  have hpull := P.pullShift_xi μ 1 hx
  rw [pullShift] at hpull
  have hx1 : shift 1 x ∈ P.SigmaPrime μ := (P.shift_mem_SigmaPrime_iff μ x).2 hx
  have hmem : ∀ y, y ∈ shift 1 ⁻¹' P.xi μ 1 (shift 1 x) →
      toVec (P.proj (shift 1 y) - P.proj (shift 1 x)) ∈ P.oseledets μ (shift 1 x) 1 := by
    intro y hy
    rw [mem_preimage, xi, atomsOn_of_mem hx1] at hy
    exact hy.1.2
  ext y
  simp only [mem_inter_iff, mem_preimage, eucTube, mem_ofPred_eq]
  constructor
  · rintro ⟨hy, hd⟩
    have hy' : y ∈ shift 1 ⁻¹' P.xi μ 1 (shift 1 x) := by rw [hpull]; exact hy
    refine ⟨hy', ?_⟩
    rw [P.eucDist_eq_of_head μ hlt hx hy.2 (hmem y hy')] at hd
    exact le_of_mul_le_mul_left hd (P.slowScale_pos μ x)
  · rintro ⟨hy, hd⟩
    have hy' : y ∈ refineZero (P.xi μ 1) x := by rw [← hpull]; exact hy
    refine ⟨hy', ?_⟩
    rw [P.eucDist_eq_of_head μ hlt hx hy'.2 (hmem y hy)]
    exact mul_le_mul_of_nonneg_left hd (P.slowScale_pos μ x).le

/-! ### Products along the orbit -/

omit [Finite ι] in
/-- `σ^n 𝐢 ∈ Σ'` exactly when `𝐢 ∈ Σ'`. -/
theorem shift_natCast_mem_SigmaPrime_iff (μ : Measure (ℤ → ι)) (x : ℤ → ι) (n : ℕ) :
    shift (n : ℤ) x ∈ P.SigmaPrime μ ↔ x ∈ P.SigmaPrime μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← ih, ← P.shift_mem_SigmaPrime_iff μ (shift (n : ℤ) x), shift_shift]
    push_cast
    rfl

/-- `(σ^n 𝐢)_0 = i_n`. -/
theorem shift_natCast_apply_zero {α : Type*} (x : ℤ → α) (n : ℕ) : shift (n : ℤ) x 0 = x n := by
  simp [shift_apply]

/-- `σ(σ^n 𝐢) = σ^{n+1} 𝐢`. -/
theorem shift_one_shift_natCast {α : Type*} (x : ℤ → α) (n : ℕ) :
    shift 1 (shift (n : ℤ) x) = shift ((n + 1 : ℕ) : ℤ) x := by
  rw [shift_shift]
  push_cast
  rfl

omit [MeasurableSpace ι] [Finite ι] in
/-- `A_{𝐢|_{n+1}} = A_{𝐢|_n} A_{i_n}`. -/
theorem word_futureWord_succ (x : ℤ → ι) (n : ℕ) :
    MatrixTuple.word P.mat (futureWord x (n + 1)) =
      MatrixTuple.word P.mat (futureWord x n) * P.mat (x n) := by
  rw [futureWord_succ, MatrixTuple.word_append]
  simp [MatrixTuple.word]

omit [Finite ι] in
/-- The multiplicative cocycle along the slow line: for `𝐢 ∈ Σ'`,
`|A_{𝐢|_n} u_{σ^n 𝐢}| = ∏_{k<n} κ_2(σ^k 𝐢)`. -/
theorem eucNorm_word_mulVec_slowDir (μ : Measure (ℤ → ι))
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) {x : ℤ → ι} (hx : x ∈ P.SigmaPrime μ) (n : ℕ) :
    eucNorm (MatrixTuple.word P.mat (futureWord x n) *ᵥ P.slowDir μ (shift (n : ℤ) x)) =
      ∏ k ∈ Finset.range n, P.slowScale μ (shift (k : ℤ) x) := by
  induction n with
  | zero => simp [P.eucNorm_slowDir]
  | succ n ih =>
    obtain ⟨c, hc, habs⟩ := P.exists_mulVec_slowDir_eq μ hlt
      ((P.shift_natCast_mem_SigmaPrime_iff μ x n).2 hx)
    rw [shift_natCast_apply_zero, shift_one_shift_natCast] at hc
    rw [P.word_futureWord_succ, ← mulVec_mulVec, hc, mulVec_smul, MatrixTuple.eucNorm_smul, ih,
      habs, Finset.prod_range_succ, mul_comm]

omit [Finite ι] in
/-- The multiplicative cocycle transverse to the slow line: for `𝐢 ∈ Σ'` and every `w`,
`|u_𝐢 ∧ A_{𝐢|_n} w| = ∏_{k<n} κ_1(σ^k 𝐢) |u_{σ^n 𝐢} ∧ w|`. -/
theorem abs_cross_slowDir_word (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    {x : ℤ → ι} (hx : x ∈ P.SigmaPrime μ) (n : ℕ) (w : Fin 2 → ℝ) :
    |MatrixTuple.cross (P.slowDir μ x) (MatrixTuple.word P.mat (futureWord x n) *ᵥ w)| =
      (∏ k ∈ Finset.range n, P.transScale μ (shift (k : ℤ) x)) *
        |MatrixTuple.cross (P.slowDir μ (shift (n : ℤ) x)) w| := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    have h := P.abs_cross_slowDir_mulVec μ hlt ((P.shift_natCast_mem_SigmaPrime_iff μ x n).2 hx) w
    rw [shift_natCast_apply_zero, shift_one_shift_natCast] at h
    rw [P.word_futureWord_succ, ← mulVec_mulVec, ih, h, Finset.prod_range_succ]
    ring

/-! ### Bounds -/

omit [Finite ι] in
/-- `κ_2(𝐢) ≤ ‖A_{i_0}‖`. -/
theorem slowScale_le_norm (μ : Measure (ℤ → ι)) (x : ℤ → ι) :
    P.slowScale μ x ≤ ‖P.mat (x 0)‖ := by
  have h := MatrixTuple.eucNorm_mulVec_le (P.mat (x 0)) (P.slowDir μ (shift 1 x))
  rwa [P.eucNorm_slowDir, mul_one] at h

omit [Finite ι] in
/-- `κ_2(𝐢) ≥ α_2(A_{i_0}) = |det A_{i_0}| / ‖A_{i_0}‖`. -/
theorem abs_det_div_norm_le_slowScale (μ : Measure (ℤ → ι)) (x : ℤ → ι) :
    |(P.mat (x 0)).det| / ‖P.mat (x 0)‖ ≤ P.slowScale μ x := by
  rw [div_le_iff₀ (norm_pos_of_det_ne_zero (P.det_ne_zero _))]
  exact MatrixTuple.abs_det_le_eucNorm_mulVec_mul _ (P.eucNorm_slowDir μ _)

/-- The bound `|log ‖A_i‖| + |log α_2(A_i)|` for `|log κ_2|` on the cylinder `[i]`. -/
noncomputable def logBound (i : ι) : ℝ :=
  |Real.log ‖P.mat i‖| + |Real.log (|(P.mat i).det| / ‖P.mat i‖)|

omit [Finite ι] in
/-- `|log κ_2(𝐢)| ≤ |log ‖A_{i_0}‖| + |log α_2(A_{i_0})|`. -/
theorem abs_log_slowScale_le (μ : Measure (ℤ → ι)) (x : ℤ → ι) :
    |Real.log (P.slowScale μ x)| ≤ P.logBound (x 0) := by
  have hpos : 0 < |(P.mat (x 0)).det| / ‖P.mat (x 0)‖ :=
    div_pos (abs_pos.2 (P.det_ne_zero _)) (norm_pos_of_det_ne_zero (P.det_ne_zero _))
  have h1 := Real.log_le_log hpos (P.abs_det_div_norm_le_slowScale μ x)
  have h2 := Real.log_le_log (P.slowScale_pos μ x) (P.slowScale_le_norm μ x)
  rw [logBound, abs_le]
  constructor <;> linarith [neg_abs_le (Real.log (|(P.mat (x 0)).det| / ‖P.mat (x 0)‖)),
    le_abs_self (Real.log ‖P.mat (x 0)‖), abs_nonneg (Real.log ‖P.mat (x 0)‖),
    abs_nonneg (Real.log (|(P.mat (x 0)).det| / ‖P.mat (x 0)‖))]

omit [Finite ι] in
/-- `log κ_1(𝐢) = log |det A_{i_0}| - log κ_2(𝐢)`. -/
theorem log_transScale (μ : Measure (ℤ → ι)) (x : ℤ → ι) :
    Real.log (P.transScale μ x) =
      Real.log |(P.mat (x 0)).det| - Real.log (P.slowScale μ x) :=
  Real.log_div (abs_ne_zero.2 (P.det_ne_zero _)) (P.slowScale_pos μ x).ne'

/-! ### Differences of projections along cylinders -/

omit [MeasurableSpace ι] in
/-- Feng (4.11): if `𝐣` and `𝐢` agree on `0, …, n-1`, then
`π𝐣 - π𝐢 = A_{𝐢|_n}(π(σ^n 𝐣) - π(σ^n 𝐢))`. -/
theorem toVec_proj_sub_proj_of_agree {x y : ℤ → ι} (n : ℕ) (h : ∀ k < n, y k = x k) :
    toVec (P.proj y - P.proj x) = MatrixTuple.word P.mat (futureWord x n) *ᵥ
      toVec (P.proj (shift (n : ℤ) y) - P.proj (shift (n : ℤ) x)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih fun k hk => h k (Nat.lt_succ_of_lt hk)]
    have h0 : shift (n : ℤ) y 0 = shift (n : ℤ) x 0 := by
      rw [shift_natCast_apply_zero, shift_natCast_apply_zero]
      exact h n (Nat.lt_succ_self n)
    rw [P.proj_sub_proj h0, shift_natCast_apply_zero, shift_one_shift_natCast,
      shift_one_shift_natCast, mulVec_mulVec, ← P.word_futureWord_succ]

omit [Finite ι] in
/-- The filtration is invariant along the orbit: `v ∈ V_{σ^n 𝐢}^i` exactly when
`A_{𝐢|_n} v ∈ V_𝐢^i`. -/
theorem mem_oseledets_shift_natCast_iff (μ : Measure (ℤ → ι)) (x : ℤ → ι) (n i : ℕ)
    (v : Fin 2 → ℝ) :
    v ∈ P.oseledets μ (shift (n : ℤ) x) i ↔
      MatrixTuple.word P.mat (futureWord x n) *ᵥ v ∈ P.oseledets μ x i := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    have h := P.mulVec_mem_oseledets_iff μ (shift (n : ℤ) x) i v
    rw [shift_natCast_apply_zero, shift_one_shift_natCast] at h
    rw [h, ih, P.word_futureWord_succ, mulVec_mulVec]

/-- Feng (4.11) and (4.12) for `i = 1` in the plane, with equality: if `𝐢 ∈ Σ'`,
`π𝐣 - π𝐢 ∈ V_𝐢^1` and `𝐣` agrees with `𝐢` on `0, …, n-1`, then
`|π𝐣 - π𝐢| = ∏_{k<n} κ_2(σ^k 𝐢) |π(σ^n 𝐣) - π(σ^n 𝐢)|`. -/
theorem eucNorm_proj_sub_of_agree (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    {x y : ℤ → ι} (hx : x ∈ P.SigmaPrime μ) (n : ℕ) (h : ∀ k < n, y k = x k)
    (hmem : toVec (P.proj y - P.proj x) ∈ P.oseledets μ x 1) :
    eucNorm (toVec (P.proj y - P.proj x)) =
      (∏ k ∈ Finset.range n, P.slowScale μ (shift (k : ℤ) x)) *
      eucNorm (toVec (P.proj (shift (n : ℤ) y) - P.proj (shift (n : ℤ) x))) := by
  have hxn := (P.shift_natCast_mem_SigmaPrime_iff μ x n).2 hx
  have he := P.toVec_proj_sub_proj_of_agree n h
  rw [he] at hmem ⊢
  have hv := (P.mem_oseledets_shift_natCast_iff μ x n 1 _).2 hmem
  rw [P.mem_oseledets_one_iff μ hlt hxn, ← MatrixTuple.mem_span_iff_cross
    (P.slowDir_ne_zero μ _)] at hv
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hv
  rw [← ht, mulVec_smul, MatrixTuple.eucNorm_smul, MatrixTuple.eucNorm_smul,
    P.eucNorm_word_mulVec_slowDir μ hlt hx n, P.eucNorm_slowDir]
  ring

/-- The Euclidean norm is at most twice the supremum norm. -/
theorem eucNorm_le_two_mul_norm (v : Fin 2 → ℝ) : eucNorm v ≤ 2 * ‖v‖ := by
  rw [eucNorm_eq]
  have h0 : |v 0| ≤ ‖v‖ := norm_le_pi_norm v 0
  have h1 : |v 1| ≤ ‖v‖ := norm_le_pi_norm v 1
  have hn : 0 ≤ ‖v‖ := norm_nonneg v
  rw [show 2 * ‖v‖ = √((2 * ‖v‖) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
  refine Real.sqrt_le_sqrt ?_
  nlinarith [sq_abs (v 0), sq_abs (v 1), abs_nonneg (v 0), abs_nonneg (v 1)]

omit [MeasurableSpace ι] in
/-- The differences of projections are bounded: `|π𝐣 - π𝐢| ≤ R` for a constant `R`. -/
theorem exists_eucNorm_proj_sub_le : ∃ R : ℝ, 0 ≤ R ∧
    ∀ x y : ℤ → ι, eucNorm (toVec (P.proj y - P.proj x)) ≤ R := by
  obtain ⟨C, hC⟩ := P.isCompact_attractor.isBounded.exists_norm_le
  have hC0 : ∀ x : ℤ → ι, ‖P.proj x‖ ≤ C := fun x => hC _ ⟨x, rfl⟩
  have hnorm : ∀ z : ℝ × ℝ, ‖toVec z‖ = ‖z‖ := fun z => by
    rw [norm_fin_two, Prod.norm_def]
    simp [Real.norm_eq_abs]
  refine ⟨2 * (|C| + |C|), by positivity, fun x y => ?_⟩
  refine (eucNorm_le_two_mul_norm _).trans ?_
  rw [hnorm]
  gcongr
  exact (norm_sub_le _ _).trans (add_le_add ((hC0 y).trans (le_abs_self C))
    ((hC0 x).trans (le_abs_self C)))

end PlanarSystem

/-! ### Ergodic averages of the scaling factors -/

namespace PlanarSystem

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (P : PlanarSystem ι)

/-- `κ_2` is a Borel function. -/
theorem measurable_slowScale (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    Measurable (P.slowScale μ) := by
  have hθ : Measurable fun x : ℤ → ι => P.slowAngle μ (shift 1 x) :=
    (P.measurable_slowAngle μ hlt).comp (measurable_shift 1)
  have hM : ∀ j k : Fin 2, Measurable fun x : ℤ → ι => P.mat (x 0) j k := fun j k =>
    (Measurable.of_discrete (f := fun i : ι => P.mat i j k)).comp (measurable_pi_apply 0)
  have hc := Real.measurable_cos.comp hθ
  have hs := Real.measurable_sin.comp hθ
  have h0 := ((hM 0 0).mul hc).add ((hM 0 1).mul hs)
  have h1 := ((hM 1 0).mul hc).add ((hM 1 1).mul hs)
  have h := ((h0.pow_const 2).add (h1.pow_const 2)).sqrt
  convert h using 1
  funext x
  simp only [slowScale, slowDir, eucNorm_eq, mulVec, dotProduct, Fin.sum_univ_two,
    MatrixTuple.dirVec, Matrix.cons_val_zero, Matrix.cons_val_one, Function.comp_apply,
    Pi.add_apply, Pi.mul_apply]

/-- `log κ_2` is a Borel function. -/
theorem measurable_log_slowScale (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    Measurable fun x => Real.log (P.slowScale μ x) :=
  (P.measurable_slowScale μ hlt).log

/-- The uniform bound `∑_i (|log ‖A_i‖| + |log α_2(A_i)|)` for `|log κ_2|`. -/
noncomputable def logBoundSum : ℝ := ∑ i, P.logBound i

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The bound of `|log κ_2|` on a cylinder is non-negative. -/
theorem logBound_nonneg (i : ι) : 0 ≤ P.logBound i := by
  unfold logBound; positivity

omit [MeasurableSingletonClass ι] in
/-- `|log κ_2| ≤ ∑_i (|log ‖A_i‖| + |log α_2(A_i)|)` everywhere. -/
theorem abs_log_slowScale_le_logBoundSum (μ : Measure (ℤ → ι)) (x : ℤ → ι) :
    |Real.log (P.slowScale μ x)| ≤ P.logBoundSum :=
  (P.abs_log_slowScale_le μ x).trans
    (Finset.single_le_sum (fun i _ => P.logBound_nonneg i) (Finset.mem_univ _))

/-- `log κ_2` is integrable. -/
theorem integrable_log_slowScale (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ]
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    Integrable (fun x => Real.log (P.slowScale μ x)) μ :=
  Integrable.of_bound (P.measurable_log_slowScale μ hlt).aestronglyMeasurable P.logBoundSum
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      exact P.abs_log_slowScale_le_logBoundSum μ x)

/-- `log |det A_{i_0}|` is integrable. -/
theorem integrable_log_abs_det (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] (k : ℤ) :
    Integrable (fun x : ℤ → ι => Real.log |(P.mat (x k)).det|) μ :=
  (Integrable.of_finite (f := fun i : ι => Real.log |(P.mat i).det|)).comp_measurable
    (measurable_pi_apply k)

/-- `log κ_1` is integrable. -/
theorem integrable_log_transScale (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ]
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    Integrable (fun x => Real.log (P.transScale μ x)) μ := by
  simp only [P.log_transScale]
  exact (P.integrable_log_abs_det μ 0).sub (P.integrable_log_slowScale μ hlt)

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- `∑_{k<n} log κ_2(σ^k 𝐢) = log |A_{𝐢|_n} u_{σ^n 𝐢}|` for `𝐢 ∈ Σ'`. -/
theorem sum_log_slowScale (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    {x : ℤ → ι} (hx : x ∈ P.SigmaPrime μ) (n : ℕ) :
    ∑ k ∈ Finset.range n, Real.log (P.slowScale μ (shift (k : ℤ) x)) =
      Real.log (eucNorm (MatrixTuple.word P.mat (futureWord x n) *ᵥ
        P.slowDir μ (shift (n : ℤ) x))) := by
  rw [P.eucNorm_word_mulVec_slowDir μ hlt hx n,
    Real.log_prod fun k _ => (P.slowScale_pos μ _).ne']

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- At a point of `Σ'` the slow direction grows backwards at the rate `λ_2` in the Euclidean
norm: `n⁻¹ log |A_{i_{-n}} ⋯ A_{i_{-1}} u_𝐢| → λ_2`. -/
theorem hasEucPastRate_slowDir (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    {y : ℤ → ι} (hy : y ∈ P.SigmaPrime μ) :
    MatrixTuple.HasEucPastRate P.mat y (P.slowDir μ y) (P.lyapunov₂ μ) := by
  have hreg := MatrixTuple.isRegularWith_slowAngle (A := P.mat) hlt hy
  have hrate := (hreg.2 (P.slowDir μ y)).1 (Submodule.mem_span_singleton_self _)
    (P.slowDir_ne_zero μ y)
  exact (MatrixTuple.hasPastRate_iff_hasEucPastRate _ _ _).1 hrate

/-- Feng's Birkhoff step for the slow line: `∫ log κ_2 dμ = λ_2` for an ergodic `μ` with
`λ_2 < λ_1`. The Birkhoff sums of `log κ_2` along the orbit of `σ^{-n} 𝐲` are
`log |A_{y_{-n}} ⋯ A_{y_{-1}} u_𝐲|`, whose `n`-th part tends to `λ_2` at every point of `Σ'`;
their integrals are `n ∫ log κ_2 dμ` by invariance, and dominated convergence concludes. -/
theorem integral_log_slowScale (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    ∫ x, Real.log (P.slowScale μ x) ∂μ = P.lyapunov₂ μ := by
  have hinv := herg.toMeasurePreserving
  set f : (ℤ → ι) → ℝ := fun x => Real.log (P.slowScale μ x) with hf
  have hfm : Measurable f := P.measurable_log_slowScale μ hlt
  have hfi : Integrable f μ := P.integrable_log_slowScale μ hlt
  set C := P.logBoundSum
  have hC : ∀ x, |f x| ≤ C := P.abs_log_slowScale_le_logBoundSum μ
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => P.logBound_nonneg i
  set S : ℕ → (ℤ → ι) → ℝ := fun n x => ∑ k ∈ Finset.range n, f (shift (k : ℤ) x)
  have hSm : ∀ n, Measurable (S n) := fun n =>
    Finset.measurable_sum _ fun k _ => hfm.comp (measurable_shift _)
  set F : ℕ → (ℤ → ι) → ℝ := fun n y => S n (shift (-(n : ℤ)) y) / n
  -- the integrals
  have hFint : ∀ n : ℕ, 1 ≤ n → ∫ y, F n y ∂μ = ∫ x, f x ∂μ := by
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
    simp only [F]
    rw [integral_div, integral_comp_shift_neg hinv n (hSm n)]
    simp only [S]
    have hint : ∀ k : ℕ, Integrable (fun x => f (shift (k : ℤ) x)) μ := fun k =>
      (measurePreserving_shift_natCast hinv k).integrable_comp_of_integrable hfi
    rw [integral_finsetSum _ fun k _ => hint k]
    simp only [fun k => integral_comp_shift hinv k hfm, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    field_simp
  -- the pointwise limit
  have hFlim : ∀ᵐ y ∂μ, Tendsto (fun n => F n y) atTop (𝓝 (P.lyapunov₂ μ)) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (P.measure_SigmaPrime_compl_of_ergodic μ herg hlt)] with y hy
    have hy' : y ∈ P.SigmaPrime μ := not_not.1 hy
    refine (P.hasEucPastRate_slowDir μ hlt hy').congr fun n => ?_
    have hx : shift (-(n : ℤ)) y ∈ P.SigmaPrime μ := by
      rw [← P.shift_natCast_mem_SigmaPrime_iff μ _ n, shift_shift]
      simpa using hy'
    simp only [F, S]
    rw [P.sum_log_slowScale μ hlt hx n, shift_shift, ← pastWord_eq_futureWord]
    simp
  -- dominated convergence
  have hbound : ∀ n, ∀ᵐ y ∂μ, ‖F n y‖ ≤ C := fun n => ae_of_all _ fun y => by
    simp only [F, S, Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using hC0
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [abs_div, Nat.abs_cast, div_le_iff₀ hn']
      calc |∑ k ∈ Finset.range n, f (shift (k : ℤ) (shift (-(n : ℤ)) y))|
          ≤ ∑ k ∈ Finset.range n, |f (shift (k : ℤ) (shift (-(n : ℤ)) y))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k ∈ Finset.range n, C := Finset.sum_le_sum fun k _ => hC _
        _ = C * n := by simp [mul_comm]
  have hFm : ∀ n, AEStronglyMeasurable (F n) μ := fun n =>
    (((hSm n).comp (measurable_shift _)).div_const _).aestronglyMeasurable
  have hlim := tendsto_integral_of_dominated_convergence (fun _ => C) hFm
    (integrable_const C) hbound hFlim
  rw [integral_const, probReal_univ, one_smul] at hlim
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (hFint n hn).symm

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- `log |det A_{𝐢|_n}| = ∑_{k<n} log |det A_{i_k}|`. -/
theorem log_abs_det_word_futureWord (x : ℤ → ι) (n : ℕ) :
    Real.log |(MatrixTuple.word P.mat (futureWord x n)).det| =
      ∑ k ∈ Finset.range n, Real.log |(P.mat (x k)).det| := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [P.word_futureWord_succ, det_mul, abs_mul, Real.log_mul
      (abs_ne_zero.2 (MatrixTuple.det_word_ne_zero P.det_ne_zero _))
      (abs_ne_zero.2 (P.det_ne_zero _)), Finset.sum_range_succ, ih]

/-- `∫ log |det A_{i_0}| dμ = λ_1 + λ_2` for an invariant `μ`: `α_1 α_2 = |det|` and the
determinant is multiplicative. -/
theorem integral_log_abs_det (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) :
    ∫ x, Real.log |(P.mat (x 0)).det| ∂μ = P.lyapunov₁ μ + P.lyapunov₂ μ := by
  refine tendsto_nhds_unique ?_ ((P.tendsto_lyapunov₁ hinv).add (P.tendsto_lyapunov₂ hinv))
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hpos : ∀ x : ℤ → ι, 0 < ‖MatrixTuple.word P.mat (futureWord x n)‖ := fun x =>
    norm_pos_of_det_ne_zero (MatrixTuple.det_word_ne_zero P.det_ne_zero _)
  have hdet : ∀ x : ℤ → ι, |(MatrixTuple.word P.mat (futureWord x n)).det| ≠ 0 := fun x =>
    abs_ne_zero.2 (MatrixTuple.det_word_ne_zero P.det_ne_zero _)
  have h₁ : Integrable (fun x => Real.log ‖MatrixTuple.word P.mat (futureWord x n)‖) μ :=
    integrable_comp_futureWord (fun w => Real.log ‖MatrixTuple.word P.mat w‖) n
  have h₂ : Integrable (fun x => Real.log (|(MatrixTuple.word P.mat (futureWord x n)).det| /
      ‖MatrixTuple.word P.mat (futureWord x n)‖)) μ :=
    integrable_comp_futureWord
      (fun w => Real.log (|(MatrixTuple.word P.mat w).det| / ‖MatrixTuple.word P.mat w‖)) n
  have hF : Measurable fun x : ℤ → ι => Real.log |(P.mat (x 0)).det| :=
    (Measurable.of_discrete (f := fun i : ι => Real.log |(P.mat i).det|)).comp
      (measurable_pi_apply 0)
  have hk : ∀ k : ℕ, ∫ x, Real.log |(P.mat (x k)).det| ∂μ =
      ∫ x, Real.log |(P.mat (x 0)).det| ∂μ := fun k => by
    rw [← integral_comp_shift hinv k hF]
    simp [shift_apply]
  rw [← add_div, ← integral_add h₁ h₂]
  simp only [fun x => Real.log_div (hdet x) (hpos x).ne', add_sub_cancel,
    P.log_abs_det_word_futureWord]
  rw [integral_finsetSum _ fun (k : ℕ) _ => P.integrable_log_abs_det μ (k : ℤ)]
  simp only [hk, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-- Feng's Birkhoff step for the transverse direction: `∫ log κ_1 dμ = λ_1` for an ergodic `μ`
with `λ_2 < λ_1`, since `log κ_1 = log |det A_{i_0}| - log κ_2`. -/
theorem integral_log_transScale (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    ∫ x, Real.log (P.transScale μ x) ∂μ = P.lyapunov₁ μ := by
  simp only [P.log_transScale]
  rw [integral_sub (P.integrable_log_abs_det μ 0) (P.integrable_log_slowScale μ hlt),
    P.integral_log_abs_det μ herg.toMeasurePreserving, P.integral_log_slowScale μ herg hlt]
  ring

/-- Birkhoff's theorem for `log κ_2`: `n⁻¹ ∑_{k<n} log κ_2(σ^k 𝐢) → λ_2` almost everywhere, so the
radii `ρ_n(𝐢) = ∏_{k<n} κ_2(σ^k 𝐢)` of Feng's proof of (5.6) have `n⁻¹ log ρ_n → λ_2`. -/
theorem tendsto_sum_log_slowScale (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n,
      Real.log (P.slowScale μ (shift (k : ℤ) x))) / n) atTop (𝓝 (P.lyapunov₂ μ)) := by
  have h := birkhoff_ergodic herg (P.integrable_log_slowScale μ hlt)
  rw [P.integral_log_slowScale μ herg hlt] at h
  filter_upwards [h] with x hx
  refine hx.congr fun n => ?_
  simp only [birkhoffAverage, birkhoffSum, iterate_shift_one, smul_eq_mul, inv_mul_eq_div]

/-- Birkhoff's theorem for `log κ_1`: `n⁻¹ ∑_{k<n} log κ_1(σ^k 𝐢) → λ_1` almost everywhere. -/
theorem tendsto_sum_log_transScale (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n,
      Real.log (P.transScale μ (shift (k : ℤ) x))) / n) atTop (𝓝 (P.lyapunov₁ μ)) := by
  have h := birkhoff_ergodic herg (P.integrable_log_transScale μ hlt)
  rw [P.integral_log_transScale μ herg hlt] at h
  filter_upwards [h] with x hx
  refine hx.congr fun n => ?_
  simp only [birkhoffAverage, birkhoffSum, iterate_shift_one, smul_eq_mul, inv_mul_eq_div]

/-- The forward theorem of Furstenberg and Kesten: `n⁻¹ log ‖A_{i_0} ⋯ A_{i_{n-1}}‖ → λ_1`
almost everywhere, by Kingman's theorem over `σ`. It gives Feng's (4.10), the inclusion
`𝒫_0^{n-1}(𝐢) ⊆ B^π(𝐢, e^{n(λ_1 + ε)})` for large `n`. -/
theorem tendsto_log_norm_word_futureWord (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => Real.log ‖MatrixTuple.word P.mat (futureWord x n)‖ / n)
      atTop (𝓝 (P.lyapunov₁ μ)) := by
  have hcoc : IsSubadditiveCocycle (shift 1)
      fun n x => Real.log ‖MatrixTuple.word P.mat (futureWord x n)‖ := by
    intro m n x
    dsimp only
    rw [iterate_shift_one, futureWord_add]
    exact MatrixTuple.log_norm_word_append_le P.det_ne_zero _ _
  exact kingman_ergodic_of_tendsto herg hcoc
    (fun n => measurable_comp_futureWord (fun w => Real.log ‖MatrixTuple.word P.mat w‖) n)
    (fun n => integrable_comp_futureWord (fun w => Real.log ‖MatrixTuple.word P.mat w‖) n)
    (P.tendsto_lyapunov₁ herg.toMeasurePreserving)

end PlanarSystem

end Components

/-! ### The objects of Feng's Section 6 in the plane -/

namespace PlanarSystem

open Matrix
open scoped Matrix.Norms.L2Operator

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (P : PlanarSystem ι)

/-- The projected conditional measure `ν^i_𝐢 = π_* μ_𝐢^{ξ_i}` (Feng, Section 6, the measures of
`δ_i`): `ν^i_𝐢(B(π𝐢, r)) = μ_𝐢^{ξ_i}(B^π(𝐢, r))` with Feng's `B^π(𝐢, r) = π⁻¹ B(π𝐢, r)` of
(2.3). The balls are those of the supremum norm. -/
noncomputable def condProj (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] (i : ℕ) (x : ℤ → ι) :
    Measure (ℝ × ℝ) :=
  (condMeas μ (P.xi μ i) x).map P.proj

/-- The projected conditional measures are probability measures. -/
instance (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] (i : ℕ) (x : ℤ → ι) :
    IsProbabilityMeasure (P.condProj μ i x) := by
  unfold condProj
  infer_instance

/-- The transverse dimension `ϑ_0(𝐢) = liminf_{r → 0} log μ_𝐢^{ξ_0}(Γ_1(𝐢, r)) / log r` of
Feng (5.1) is at least `c`, stated without the limit inferior. -/
def TransverseDimGe (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] (x : ℤ → ι) (c : ℝ) : Prop :=
  ∀ c' < c, ∀ᶠ r in 𝓝[>] (0 : ℝ),
    c' ≤ Real.log ((condMeas μ (P.xi μ 0) x).real (P.transTube μ x r)) / Real.log r

/-- The steps of Feng's proof of Theorems 1.2 (ii) and 1.3 (Section 6, pp. 38 to 44) for a
planar system with `s = 2`, `k_1 = k_2 = 1`, with the pointwise dimensions `δ_i` of
`ν^i_𝐢 = π_* μ_𝐢^{ξ_i}` at `π𝐢`, `ν^{-1} = π_* μ`, `c_1 = (h_1 - h_0)/λ_1` and
`c_2 = (h_2 - h_1)/λ_2`. Each implication is the instance of Feng's claim used in the descent
(6.7) to (6.9), with the value of `δ_{i+1}` already known. -/
structure FengSteps (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] : Prop where
  /-- (C1): `δ_2 = 0`. -/
  c1 : ∀ᵐ x ∂μ, HasLocalDim (P.condProj μ 2 x) (P.proj x) 0
  /-- Proposition 5.1 for `i = 2`: `ϑ_1 = \underline{δ}_1 ≥ (h_2 - h_1)/λ_2`. -/
  transverse_two : ∀ᵐ x ∂μ, LowerLocalDimGe (P.condProj μ 1 x) (P.proj x)
    ((P.dimEntropy μ 2 - P.dimEntropy μ 1) / P.lyapunov₂ μ)
  /-- (C2) for `i = 1`: `\overline{δ}_1 ≤ (h_2 - h_1)/λ_2 + \overline{δ}_2`. -/
  c2_one : ∀ D : ℝ, (∀ᵐ x ∂μ, UpperLocalDimLe (P.condProj μ 2 x) (P.proj x) D) →
    ∀ᵐ x ∂μ, UpperLocalDimLe (P.condProj μ 1 x) (P.proj x)
      ((P.dimEntropy μ 2 - P.dimEntropy μ 1) / P.lyapunov₂ μ + D)
  /-- Proposition 5.1 for `i = 1`: `ϑ_0 ≥ (h_1 - h_0)/λ_1`. -/
  transverse_one : ∀ᵐ x ∂μ,
    P.TransverseDimGe μ x ((P.dimEntropy μ 1 - P.dimEntropy μ 0) / P.lyapunov₁ μ)
  /-- (C3) for `i = 0`: `\underline{δ}_0 ≥ \underline{δ}_1 + ϑ_0`. -/
  c3_zero : ∀ D c : ℝ, (∀ᵐ x ∂μ, LowerLocalDimGe (P.condProj μ 1 x) (P.proj x) D) →
    (∀ᵐ x ∂μ, P.TransverseDimGe μ x c) →
    ∀ᵐ x ∂μ, LowerLocalDimGe (P.condProj μ 0 x) (P.proj x) (D + c)
  /-- (C2) for `i = 0`: `\overline{δ}_0 ≤ (h_1 - h_0)/λ_1 + \overline{δ}_1`. -/
  c2_zero : ∀ D : ℝ, (∀ᵐ x ∂μ, UpperLocalDimLe (P.condProj μ 1 x) (P.proj x) D) →
    ∀ᵐ x ∂μ, UpperLocalDimLe (P.condProj μ 0 x) (P.proj x)
      ((P.dimEntropy μ 1 - P.dimEntropy μ 0) / P.lyapunov₁ μ + D)
  /-- (C3) for `i = -1`: `\underline{δ}_{-1} ≥ \underline{δ}_0`, since `ϑ_{-1} = 0`. -/
  c3_neg : ∀ D : ℝ, (∀ᵐ x ∂μ, LowerLocalDimGe (P.condProj μ 0 x) (P.proj x) D) →
    ∀ᵐ x ∂μ, LowerLocalDimGe (μ.map P.proj) (P.proj x) D
  /-- (C2) for `i = -1`: `\overline{δ}_{-1} ≤ \overline{δ}_0`, since `h_{-1} = h_0` by (4.17). -/
  c2_neg : ∀ D : ℝ, (∀ᵐ x ∂μ, UpperLocalDimLe (P.condProj μ 0 x) (P.proj x) D) →
    ∀ᵐ x ∂μ, UpperLocalDimLe (μ.map P.proj) (P.proj x) D

/-- The descent (6.7) to (6.9) of Feng, Section 6: the steps give
`dim π_* μ = (h_1 - h_0)/λ_1 + (h_2 - h_1)/λ_2`, with exact-dimensionality. -/
theorem isExactDim_of_fengSteps (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (h : P.FengSteps μ) :
    IsExactDim (μ.map P.proj)
      ((P.dimEntropy μ 1 - P.dimEntropy μ 0) / P.lyapunov₁ μ +
        (P.dimEntropy μ 2 - P.dimEntropy μ 1) / P.lyapunov₂ μ) := by
  set c₁ := (P.dimEntropy μ 1 - P.dimEntropy μ 0) / P.lyapunov₁ μ
  set c₂ := (P.dimEntropy μ 2 - P.dimEntropy μ 1) / P.lyapunov₂ μ
  -- `δ_1 = c_2`
  have hU1 := h.c2_one 0 (h.c1.mono fun x hx => hx.upperLocalDimLe)
  rw [add_zero] at hU1
  -- `δ_0 = c_1 + c_2`
  have hU0 := h.c2_zero c₂ hU1
  have hL0 := h.c3_zero c₂ c₁ h.transverse_two h.transverse_one
  -- `δ_{-1} = c_1 + c_2`
  have hU := h.c2_neg (c₁ + c₂) hU0
  have hL := h.c3_neg (c₁ + c₂) (by simpa only [add_comm] using hL0)
  refine isExactDim_map_of_ae_hasLocalDim μ P.measurable_proj ?_
  filter_upwards [hU, hL] with x hxU hxL
  exact hasLocalDim_iff_lowerLocalDimGe_and_upperLocalDimLe.2 ⟨hxL, hxU⟩

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- The atom `ξ_2(𝐢)` of a point of `Σ'` lies in the fibre `π⁻¹{π𝐢}`. -/
theorem xi_two_subset_fibre (μ : Measure (ℤ → ι)) {x : ℤ → ι} (hx : x ∈ P.SigmaPrime μ) :
    P.xi μ 2 x ⊆ P.proj ⁻¹' {P.proj x} := by
  intro y hy
  rw [xi, atomsOn_of_mem hx] at hy
  obtain ⟨⟨-, hv⟩, -⟩ := hy
  have h0 : toVec (P.proj y - P.proj x) = 0 := hv
  rw [← toVec_zero] at h0
  exact sub_eq_zero.1 (toVec_injective h0)

/-- (C1) of Feng, Section 6 (p. 40): for an ergodic `μ` with `λ_2 < λ_1`, `δ_2 = 0`, that is
`ν^2_𝐢 = π_* μ_𝐢^{ξ_2}` has pointwise dimension `0` at `π𝐢` for `μ`-almost every `𝐢`: the
conditional measure is carried by `ξ_2(𝐢) ⊆ π⁻¹{π𝐢}`, so every ball about `π𝐢` has mass one. -/
theorem hasLocalDim_condProj_two (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    ∀ᵐ x ∂μ, HasLocalDim (P.condProj μ 2 x) (P.proj x) 0 := by
  have hsub : ∀ᵐ x ∂μ, P.xi μ 2 x ⊆ P.proj ⁻¹' {P.proj x} := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (P.measure_SigmaPrime_compl_of_ergodic μ herg hlt)] with x hx
    exact P.xi_two_subset_fibre μ (not_not.1 hx)
  filter_upwards [condMeas_eq_one_of_atom_subset μ (P.isMeasurablePartition_xi μ hlt 2) hsub]
    with x hx
  have hone : ∀ r : ℝ, 0 < r → (P.condProj μ 2 x).real (closedBall (P.proj x) r) = 1 := by
    intro r hr
    rw [condProj, measureReal_def, Measure.map_apply P.measurable_proj measurableSet_closedBall]
    have hle : condMeas μ (P.xi μ 2) x (P.proj ⁻¹' {P.proj x}) ≤
        condMeas μ (P.xi μ 2) x (P.proj ⁻¹' closedBall (P.proj x) r) :=
      measure_mono (preimage_mono (singleton_subset_iff.2 (mem_closedBall_self hr.le)))
    rw [hx] at hle
    rw [le_antisymm prob_le_one hle, ENNReal.toReal_one]
  unfold HasLocalDim
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [hone r hr, Real.log_one, zero_div]

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The supremum norm of the coordinate vector of a point is its norm. -/
theorem norm_toVec (z : ℝ × ℝ) : ‖toVec z‖ = ‖z‖ := by
  rw [norm_fin_two, Prod.norm_def]
  simp [Real.norm_eq_abs]

/-- `-n⁻¹ log μ_𝐢^{ξ_i}([𝐢|_n]) → h_i(μ)` almost everywhere for an ergodic `μ` with `λ_2 < λ_1`:
Feng, (4.16) (`feng_entropy_as_limit_of_full`) and `eq:ergodic_entropy_constant`. -/
theorem tendsto_neg_log_condMeas_xi (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) (i : ℕ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ =>
      -Real.log ((condMeas μ (P.xi μ i) x).real (cylinder (block n x))) / n) atTop
      (𝓝 (P.dimEntropy μ i)) := by
  filter_upwards [P.feng_entropy_as_limit_of_full μ herg.toMeasurePreserving hlt
    (P.measure_SigmaPrime_compl_of_ergodic μ herg hlt) i, localEntropy_ae_eq μ herg (P.xi μ i)]
    with x hx hloc
  rwa [dimEntropyAt, hloc] at hx

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- If `a_n / n → λ`, then `R e^{a_n} ≤ e^{n(λ + ε)}` for all large `n`, for every `R ≥ 0` and
`ε > 0`. -/
theorem eventually_mul_exp_le {a : ℕ → ℝ} {lam R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (ha : Tendsto (fun n : ℕ => a n / n) atTop (𝓝 lam)) :
    ∀ᶠ n : ℕ in atTop, R * Real.exp (a n) ≤ Real.exp (n * (lam + ε)) := by
  have h1 : ∀ᶠ n : ℕ in atTop, Real.log (R + 1) ≤ n * (ε / 2) :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const (by linarith : (0 : ℝ) < ε / 2)).eventually
      (eventually_ge_atTop _)
  filter_upwards [ha.eventually (gt_mem_nhds (show lam < lam + ε / 2 by linarith)),
    eventually_gt_atTop 0, h1] with n hn hn0 hR1
  have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [div_lt_iff₀ hn0'] at hn
  have hR2 : R ≤ Real.exp (n * (ε / 2)) := by
    calc R ≤ R + 1 := by linarith
      _ = Real.exp (Real.log (R + 1)) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (n * (ε / 2)) := Real.exp_le_exp.2 hR1
  calc R * Real.exp (a n) ≤ Real.exp (n * (ε / 2)) * Real.exp (n * (lam + ε / 2)) :=
        mul_le_mul hR2 (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (n * (lam + ε)) := by rw [← Real.exp_add]; ring_nf

/-- Feng, (C2) for `i = 1` (pp. 40 to 42, after Ledrappier–Young, Section 10.2, and Feng–Hu,
Theorem 2.11): `\overline{δ}_1 ≤ (h_2 - h_1)/λ_2 + \overline{δ}_2`. This is
`ae_upperLocalDimLe_condMeas_of_counting` for `ξ_2 ⊆ ξ_1`, with Feng's inclusion (6.2) in the
exact form `ξ_1(𝐢) ∩ [𝐢|_n] ⊆ B^π(𝐢, ∏_{k<n} κ_2(σ^k 𝐢) R)` (`eucNorm_proj_sub_of_agree`) and
Birkhoff's theorem for `log κ_2`, of mean `λ_2` (`tendsto_sum_log_slowScale`). -/
theorem upperLocalDimLe_condProj_one (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) (D : ℝ)
    (hD : ∀ᵐ x ∂μ, UpperLocalDimLe (P.condProj μ 2 x) (P.proj x) D) :
    ∀ᵐ x ∂μ, UpperLocalDimLe (P.condProj μ 1 x) (P.proj x)
      ((P.dimEntropy μ 2 - P.dimEntropy μ 1) / P.lyapunov₂ μ + D) := by
  obtain ⟨R, hR, hRb⟩ := P.exists_eucNorm_proj_sub_le
  have hlam : P.lyapunov₂ μ < 0 := hlt.trans (P.lyapunov₁_neg herg.toMeasurePreserving)
  set ρ : ℕ → (ℤ → ι) → ℝ := fun n y =>
    R * Real.exp (∑ k ∈ Finset.range n, Real.log (P.slowScale μ (shift (k : ℤ) y))) with hρ
  have hρm : ∀ n, Measurable (ρ n) := fun n =>
    measurable_const.mul (Finset.measurable_sum _ fun k _ =>
      (P.measurable_log_slowScale μ hlt).comp (measurable_shift _)).exp
  have hcont : ∀ z ∈ P.SigmaPrime μ, ∀ n : ℕ, P.xi μ 1 z ∩ cylinder (block n z) ⊆
      P.proj ⁻¹' closedBall (P.proj z) (ρ n z) := by
    intro z hz n v ⟨hv1, hvc⟩
    rw [xi, atomsOn_of_mem hz] at hv1
    have hagree : ∀ k < n, v k = z k := fun k hk => hvc ⟨k, hk⟩
    have he := P.eucNorm_proj_sub_of_agree μ hlt hz n hagree hv1.1.2
    simp only [mem_preimage, mem_closedBall, dist_eq_norm]
    rw [← norm_toVec]
    refine (MatrixTuple.norm_le_eucNorm _).trans ?_
    rw [he, hρ]
    dsimp only
    rw [Real.exp_sum, mul_comm R]
    refine mul_le_mul (le_of_eq (Finset.prod_congr rfl fun k _ =>
      (Real.exp_log (P.slowScale_pos μ _)).symm)) (hRb _ _) (eucNorm_nonneg _) ?_
    exact Finset.prod_nonneg fun k _ => (Real.exp_pos _).le
  refine ae_upperLocalDimLe_condMeas_of_counting μ (P.isMeasurablePartition_xi μ hlt 1)
    (P.isMeasurablePartition_xi μ hlt 2) (fun x => P.xi_succ_subset μ 1 x) P.measurable_proj
    (P.measurableSet_SigmaPrime μ hlt) (P.measure_SigmaPrime_compl_of_ergodic μ herg hlt) hρm
    hcont hlam (fun ε hε => ?_) (P.tendsto_neg_log_condMeas_xi μ herg hlt 1)
    (P.tendsto_neg_log_condMeas_xi μ herg hlt 2) hD
  filter_upwards [P.tendsto_sum_log_slowScale μ herg hlt] with x hx
  exact eventually_mul_exp_le hR hε hx

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The inclusion `[𝐢|_n] ⊆ B^π(𝐢, 2 ‖A_{𝐢|_n}‖ R)` behind Feng's (4.10). -/
theorem proj_mem_closedBall_of_mem_cylinder {R : ℝ}
    (hRb : ∀ x y : ℤ → ι, eucNorm (toVec (P.proj y - P.proj x)) ≤ R) (z : ℤ → ι) (n : ℕ)
    {v : ℤ → ι} (hv : v ∈ cylinder (block n z)) :
    P.proj v ∈ closedBall (P.proj z)
      (2 * ‖MatrixTuple.word P.mat (futureWord z n)‖ * R) := by
  have hagree : ∀ k < n, v k = z k := fun k hk => hv ⟨k, hk⟩
  rw [mem_closedBall, dist_eq_norm, ← norm_toVec, P.toVec_proj_sub_proj_of_agree n hagree]
  refine (norm_mulVec_le _ _).trans ?_
  gcongr
  exact (MatrixTuple.norm_le_eucNorm _).trans (hRb _ _)

/-- Feng, (C2) for `i = 0` (pp. 40 to 42): `\overline{δ}_0 ≤ (h_1 - h_0)/λ_1 + \overline{δ}_1`.
This is `ae_upperLocalDimLe_condMeas_of_counting` for `ξ_1 ⊆ ξ_0`, with the inclusion
`[𝐢|_n] ⊆ B^π(𝐢, 2 ‖A_{𝐢|_n}‖ R)` and the forward theorem of Furstenberg and Kesten
(`tendsto_log_norm_word_futureWord`). -/
theorem upperLocalDimLe_condProj_zero (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) (D : ℝ)
    (hD : ∀ᵐ x ∂μ, UpperLocalDimLe (P.condProj μ 1 x) (P.proj x) D) :
    ∀ᵐ x ∂μ, UpperLocalDimLe (P.condProj μ 0 x) (P.proj x)
      ((P.dimEntropy μ 1 - P.dimEntropy μ 0) / P.lyapunov₁ μ + D) := by
  obtain ⟨R, hR, hRb⟩ := P.exists_eucNorm_proj_sub_le
  have hlam : P.lyapunov₁ μ < 0 := P.lyapunov₁_neg herg.toMeasurePreserving
  set ρ : ℕ → (ℤ → ι) → ℝ := fun n y =>
    2 * ‖MatrixTuple.word P.mat (futureWord y n)‖ * R with hρ
  have hρm : ∀ n, Measurable (ρ n) := fun n =>
    (measurable_const.mul (measurable_comp_futureWord
      (fun w => ‖MatrixTuple.word P.mat w‖) n)).mul measurable_const
  refine ae_upperLocalDimLe_condMeas_of_counting μ (P.isMeasurablePartition_xi μ hlt 0)
    (P.isMeasurablePartition_xi μ hlt 1) (fun x => P.xi_succ_subset μ 0 x) P.measurable_proj
    MeasurableSet.univ (by simp) hρm
    (fun z _ n v hv => P.proj_mem_closedBall_of_mem_cylinder hRb z n hv.2) hlam
    (fun ε hε => ?_) (P.tendsto_neg_log_condMeas_xi μ herg hlt 0)
    (P.tendsto_neg_log_condMeas_xi μ herg hlt 1) hD
  filter_upwards [P.tendsto_log_norm_word_futureWord μ herg] with x hx
  filter_upwards [eventually_mul_exp_le (by positivity : (0 : ℝ) ≤ 2 * R) hε hx] with n hn
  refine le_of_eq_of_le ?_ hn
  rw [hρ]
  dsimp only
  rw [Real.exp_log (norm_pos_of_det_ne_zero (MatrixTuple.det_word_ne_zero P.det_ne_zero _))]
  ring

/-- Feng, (C2) for `i = -1` (pp. 40 to 42): `\overline{δ}_{-1} ≤ \overline{δ}_0`. This is
`ae_upperLocalDimLe_condMeas_of_counting` for `ξ_0` inside the trivial partition, whose
conditional measures are `μ` (`condMeas_univ_ae_eq`), with `h_{-1} = h_0` by (4.17)
(`tendsto_neg_log_cylinder_dimEntropyAt_of_ergodic`) and `λ_0 = λ_1`. -/
theorem upperLocalDimLe_map_proj (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) (D : ℝ)
    (hD : ∀ᵐ x ∂μ, UpperLocalDimLe (P.condProj μ 0 x) (P.proj x) D) :
    ∀ᵐ x ∂μ, UpperLocalDimLe (μ.map P.proj) (P.proj x) D := by
  obtain ⟨R, hR, hRb⟩ := P.exists_eucNorm_proj_sub_le
  have hlam : P.lyapunov₁ μ < 0 := P.lyapunov₁_neg herg.toMeasurePreserving
  set ρ : ℕ → (ℤ → ι) → ℝ := fun n y =>
    2 * ‖MatrixTuple.word P.mat (futureWord y n)‖ * R with hρ
  have hρm : ∀ n, Measurable (ρ n) := fun n =>
    (measurable_const.mul (measurable_comp_futureWord
      (fun w => ‖MatrixTuple.word P.mat w‖) n)).mul measurable_const
  have hentξ : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ =>
      -Real.log ((condMeas μ (fun _ => univ) x).real (cylinder (block n x))) / n) atTop
      (𝓝 (P.dimEntropy μ 0)) := by
    filter_upwards [condMeas_univ_ae_eq μ, P.tendsto_neg_log_cylinder_dimEntropyAt_of_ergodic μ
      herg hlt, localEntropy_ae_eq μ herg (P.xi μ 0)] with x hx hlim hloc
    rw [hx]
    rwa [dimEntropyAt, hloc] at hlim
  have h := ae_upperLocalDimLe_condMeas_of_counting μ isMeasurablePartition_univ
    (P.isMeasurablePartition_xi μ hlt 0) (fun x => subset_univ _) P.measurable_proj
    MeasurableSet.univ (by simp) hρm
    (fun z _ n v hv => P.proj_mem_closedBall_of_mem_cylinder hRb z n hv.2) hlam
    (fun ε hε => ?_) hentξ (P.tendsto_neg_log_condMeas_xi μ herg hlt 0) hD
  · filter_upwards [h, condMeas_univ_ae_eq μ] with x hx hx'
    rwa [hx', sub_self, zero_div, zero_add] at hx
  · filter_upwards [P.tendsto_log_norm_word_futureWord μ herg] with x hx
    filter_upwards [eventually_mul_exp_le (by positivity : (0 : ℝ) ≤ 2 * R) hε hx] with n hn
    refine le_of_eq_of_le ?_ hn
    rw [hρ]
    dsimp only
    rw [Real.exp_log (norm_pos_of_det_ne_zero (MatrixTuple.det_word_ne_zero P.det_ne_zero _))]
    ring

/-- `Γ_1(𝐢, r)` is Borel. -/
theorem measurableSet_transTube (μ : Measure (ℤ → ι)) (x : ℤ → ι) (r : ℝ) :
    MeasurableSet (P.transTube μ x r) := by
  have hcont : Continuous fun z : ℝ × ℝ =>
      |MatrixTuple.cross (P.slowDir μ x) (toVec (z - P.proj x))| := by
    simp only [MatrixTuple.cross, toVec, Matrix.cons_val_zero, Matrix.cons_val_one]
    fun_prop
  exact measurableSet_le (hcont.measurable.comp P.measurable_proj) measurable_const

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- The geometric fact behind Feng's (6.15) in the plane: for `𝐢 ∈ Σ'`, `𝐣 ∈ ξ_0(𝐢)` and
`𝐰 ∈ ξ_1(𝐣)` with `|π𝐰 - π𝐢| ≤ r` (supremum norm), `𝐣 ∈ Γ_1(𝐢, 2r)`: the line `π𝐣 + V_𝐣^1` is
`π𝐰 + V_𝐢^1`, since `𝐣` and `𝐢` have the same past. -/
theorem mem_transTube_of_mem_xi (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    {x y w : ℤ → ι} (hx : x ∈ P.SigmaPrime μ) (hy : y ∈ P.xi μ 0 x) (hw : w ∈ P.xi μ 1 y)
    {r : ℝ} (hr : P.proj w ∈ closedBall (P.proj x) r) : y ∈ P.transTube μ x (2 * r) := by
  rw [xi, atomsOn_of_mem hx] at hy
  obtain ⟨⟨hyx, -⟩, hyS⟩ := hy
  rw [xi, atomsOn_of_mem hyS] at hw
  obtain ⟨⟨-, hwv⟩, -⟩ := hw
  rw [P.oseledets_congr μ hyx, P.mem_oseledets_one_iff μ hlt hx] at hwv
  set u := P.slowDir μ x
  have heq : MatrixTuple.cross u (toVec (P.proj y - P.proj x)) =
      MatrixTuple.cross u (toVec (P.proj w - P.proj x)) := by
    have : toVec (P.proj y - P.proj x) =
        toVec (P.proj w - P.proj x) - toVec (P.proj w - P.proj y) := by
      rw [← toVec_sub]
      congr 1
      abel
    rw [this]
    simp only [MatrixTuple.cross, Pi.sub_apply] at hwv ⊢
    linarith
  have hu : ‖u‖ ≤ 1 := by
    rw [norm_fin_two]
    simp only [u, slowDir, MatrixTuple.dirVec, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact max_le (Real.abs_cos_le_one _) (Real.abs_sin_le_one _)
  have hd : ‖toVec (P.proj w - P.proj x)‖ ≤ r := by
    rw [norm_toVec, ← dist_eq_norm]
    exact mem_closedBall.1 hr
  change |MatrixTuple.cross u (toVec (P.proj y - P.proj x))| ≤ 2 * r
  rw [heq]
  calc |MatrixTuple.cross u (toVec (P.proj w - P.proj x))|
      ≤ 2 * ‖u‖ * ‖toVec (P.proj w - P.proj x)‖ := MatrixTuple.abs_cross_le _ _
    _ ≤ 2 * 1 * r := by gcongr
    _ = 2 * r := by ring

/-- Feng, (C3) for `i = 0` (pp. 42 to 43, after Ledrappier–Young, Lemma 11.3.1, and Feng–Hu,
Theorem 2.11): `\underline{δ}_0 ≥ \underline{δ}_1 + ϑ_0`. This is
`ae_lowerLocalDimGe_condMeas_of_tube` for `ξ_1 ⊆ ξ_0`, the tubes `Γ_1(𝐢, r)` and `κ = 2`, by
`mem_transTube_of_mem_xi`. -/
theorem lowerLocalDimGe_condProj_zero (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) (D c : ℝ)
    (hD : ∀ᵐ x ∂μ, LowerLocalDimGe (P.condProj μ 1 x) (P.proj x) D)
    (hc : ∀ᵐ x ∂μ, P.TransverseDimGe μ x c) :
    ∀ᵐ x ∂μ, LowerLocalDimGe (P.condProj μ 0 x) (P.proj x) (D + c) := by
  have htube : ∀ᵐ x ∂μ, ∀ y ∈ P.xi μ 0 x, ∀ r : ℝ,
      (P.xi μ 1 y ∩ P.proj ⁻¹' closedBall (P.proj x) r).Nonempty →
        y ∈ P.transTube μ x (2 * r) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (P.measure_SigmaPrime_compl_of_ergodic μ herg hlt)] with x hx y hy r ⟨w, hw, hwr⟩
    exact P.mem_transTube_of_mem_xi μ hlt (not_not.1 hx) hy hw hwr
  exact ae_lowerLocalDimGe_condMeas_of_tube μ (P.isMeasurablePartition_xi μ hlt 0)
    (P.isMeasurablePartition_xi μ hlt 1) (fun x => P.xi_succ_subset μ 0 x) P.measurable_proj
    (P.measurableSet_transTube μ) two_pos htube hD hc

/-- Feng, (C3) for `i = -1` (pp. 42 to 43): `\underline{δ}_{-1} ≥ \underline{δ}_0`, the argument
of `lowerLocalDimGe_condProj_zero` with `ξ_{-1}` trivial and `Γ_0(𝐢, r) = Σ'`, so that `ϑ_{-1} = 0`.
-/
theorem lowerLocalDimGe_map_proj (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) (D : ℝ)
    (hD : ∀ᵐ x ∂μ, LowerLocalDimGe (P.condProj μ 0 x) (P.proj x) D) :
    ∀ᵐ x ∂μ, LowerLocalDimGe (μ.map P.proj) (P.proj x) D :=
  ae_lowerLocalDimGe_map_of_condMeas μ (P.isMeasurablePartition_xi μ hlt 0) P.measurable_proj hD

/-- The Euclidean tube `B^π(𝐢, r)` is Borel. -/
theorem measurableSet_eucTube (x : ℤ → ι) (r : ℝ) : MeasurableSet (P.eucTube x r) := by
  have hcont : Continuous fun z : ℝ × ℝ => eucNorm (toVec (z - P.proj x)) :=
    MatrixTuple.continuous_eucNorm.comp (continuous_toVec.comp (continuous_id.sub continuous_const))
  exact measurableSet_le (hcont.measurable.comp P.measurable_proj) measurable_const

/-- Feng's one-step identity of the proof of (5.6) for `i = 2` in the plane, with `ℓ = 1`:
`μ_𝐢^{ξ_1}([i_0] ∩ B^π(𝐢, κ_2(𝐢) r)) = μ_𝐢^{ξ_1}([i_0]) μ_{σ𝐢}^{ξ_1}(B^π(σ𝐢, r))` for every `r`,
`μ`-almost everywhere, with Euclidean tubes. Taking logarithms,
`H_n + G_n = -I_μ(𝒫 | \widehat{ξ}_1)` with equality (Feng, p. 37), by Lemma 5.4
(`refineZero_xi_one_inter_eucTube`) and Lemma 4.5 (3) (`condMeas_zeroCyl_inter_preimage_shift`). -/
theorem condMeas_eucTube_step (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    ∀ᵐ x ∂μ, ∀ r : ℝ, condMeas μ (P.xi μ 1) x
        ({y | y 0 = x 0} ∩ P.eucTube x (P.slowScale μ x * r)) =
      condMeas μ (P.xi μ 1) x {y | y 0 = x 0} *
        condMeas μ (P.xi μ 1) (shift 1 x) (P.eucTube (shift 1 x) r) := by
  have hinv := herg.toMeasurePreserving
  have hfull := P.measure_SigmaPrime_compl_of_ergodic μ herg hlt
  have hξ := P.isMeasurablePartition_xi μ hlt 1
  have hatom := condMeas_atom μ hξ
  filter_upwards [condMeas_zeroCyl_inter_preimage_shift hinv hξ (P.measurableSet_SigmaPrime μ hlt)
      hfull (fun _ hx => P.pullShift_xi μ 1 hx) (fun _ hx => P.xi_subset_SigmaPrime μ 1 hx)
      (fun _ hx => P.pullShift_xi_subset_of_notMem μ 1 hx), hatom,
    hinv.quasiMeasurePreserving.ae hatom, measure_eq_zero_iff_ae_notMem.1 hfull]
    with x hstep hx hσx hxS r
  have hxS' : x ∈ P.SigmaPrime μ := not_not.1 hxS
  have hset := P.refineZero_xi_one_inter_eucTube μ hlt hxS' r
  set S' := P.xi μ 1 (shift 1 x) ∩ P.eucTube (shift 1 x) r
  have hS'm : MeasurableSet S' := (hξ.measurableSet_atom _).inter (P.measurableSet_eucTube _ _)
  have hcompl : condMeas μ (P.xi μ 1) x (P.xi μ 1 x)ᶜ = 0 :=
    (prob_compl_eq_zero_iff (hξ.measurableSet_atom x)).2 hx
  have hcomplσ : condMeas μ (P.xi μ 1) (shift 1 x) (P.xi μ 1 (shift 1 x))ᶜ = 0 :=
    (prob_compl_eq_zero_iff (hξ.measurableSet_atom _)).2 hσx
  have hsubC : shift 1 ⁻¹' S' ⊆ {y | y 0 = x 0} := by
    rw [← hset]
    exact fun y hy => hy.1.2
  rw [← measure_inter_conull hcompl]
  have heq : {y | y 0 = x 0} ∩ P.eucTube x (P.slowScale μ x * r) ∩ P.xi μ 1 x =
      {y | y 0 = x 0} ∩ shift 1 ⁻¹' S' := by
    rw [← hset, refineZero]
    ext y
    simp only [mem_inter_iff]
    tauto
  rw [heq, hstep S' hS'm]
  congr 1
  show condMeas μ (P.xi μ 1) (shift 1 x) (P.xi μ 1 (shift 1 x) ∩ P.eucTube (shift 1 x) r) = _
  rw [inter_comm, measure_inter_conull hcomplσ]

/-- Feng's one-step identity of the proof of (5.6) for `i = 1` in the plane, with `ℓ = 1`:
`μ_𝐢^{ξ_0}([i_0] ∩ Γ_1(𝐢, κ_1(𝐢) r)) = μ_𝐢^{ξ_0}([i_0]) μ_{σ𝐢}^{ξ_0}(Γ_1(σ𝐢, r))` for every `r`,
`μ`-almost everywhere, by Lemma 5.4 (`refineZero_xi_zero_inter_transTube`) and Lemma 4.5 (3). -/
theorem condMeas_transTube_step (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    ∀ᵐ x ∂μ, ∀ r : ℝ, condMeas μ (P.xi μ 0) x
        ({y | y 0 = x 0} ∩ P.transTube μ x (P.transScale μ x * r)) =
      condMeas μ (P.xi μ 0) x {y | y 0 = x 0} *
        condMeas μ (P.xi μ 0) (shift 1 x) (P.transTube μ (shift 1 x) r) := by
  have hinv := herg.toMeasurePreserving
  have hfull := P.measure_SigmaPrime_compl_of_ergodic μ herg hlt
  have hξ := P.isMeasurablePartition_xi μ hlt 0
  have hatom := condMeas_atom μ hξ
  filter_upwards [condMeas_zeroCyl_inter_preimage_shift hinv hξ (P.measurableSet_SigmaPrime μ hlt)
      hfull (fun _ hx => P.pullShift_xi μ 0 hx) (fun _ hx => P.xi_subset_SigmaPrime μ 0 hx)
      (fun _ hx => P.pullShift_xi_subset_of_notMem μ 0 hx), hatom,
    hinv.quasiMeasurePreserving.ae hatom, measure_eq_zero_iff_ae_notMem.1 hfull]
    with x hstep hx hσx hxS r
  have hxS' : x ∈ P.SigmaPrime μ := not_not.1 hxS
  have hset := P.refineZero_xi_zero_inter_transTube μ hlt hxS' r
  set S' := P.xi μ 0 (shift 1 x) ∩ P.transTube μ (shift 1 x) r
  have hS'm : MeasurableSet S' :=
    (hξ.measurableSet_atom _).inter (P.measurableSet_transTube μ _ _)
  have hcompl : condMeas μ (P.xi μ 0) x (P.xi μ 0 x)ᶜ = 0 :=
    (prob_compl_eq_zero_iff (hξ.measurableSet_atom x)).2 hx
  have hcomplσ : condMeas μ (P.xi μ 0) (shift 1 x) (P.xi μ 0 (shift 1 x))ᶜ = 0 :=
    (prob_compl_eq_zero_iff (hξ.measurableSet_atom _)).2 hσx
  rw [← measure_inter_conull hcompl]
  have heq : {y | y 0 = x 0} ∩ P.transTube μ x (P.transScale μ x * r) ∩ P.xi μ 0 x =
      {y | y 0 = x 0} ∩ shift 1 ⁻¹' S' := by
    rw [← hset, refineZero]
    ext y
    simp only [mem_inter_iff]
    tauto
  rw [heq, hstep S' hS'm]
  congr 1
  show condMeas μ (P.xi μ 0) (shift 1 x)
    (P.xi μ 0 (shift 1 x) ∩ P.transTube μ (shift 1 x) r) = _
  rw [inter_comm, measure_inter_conull hcomplσ]


/-! ### Proposition 5.1 in the plane -/

omit [MeasurableSingletonClass ι] in
/-- A uniform lower bound `κ_0 = min_i α_2(A_i) > 0` for the scaling factors. -/
theorem exists_scale_bounds [Nonempty ι] : ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ μ : Measure (ℤ → ι), ∀ x,
    (κ0 ≤ P.slowScale μ x ∧ P.slowScale μ x ≤ 1) ∧
      (κ0 ≤ P.transScale μ x ∧ P.transScale μ x ≤ 1) := by
  classical
  set f : ι → ℝ := fun i => |(P.mat i).det| / ‖P.mat i‖
  have hf : ∀ i, 0 < f i := fun i =>
    div_pos (abs_pos.2 (P.det_ne_zero i)) (norm_pos_of_det_ne_zero (P.det_ne_zero i))
  refine ⟨Finset.univ.inf' Finset.univ_nonempty f,
    (Finset.lt_inf'_iff _).2 fun i _ => hf i, fun μ x => ?_⟩
  have hmin : Finset.univ.inf' Finset.univ_nonempty f ≤ f (x 0) :=
    Finset.inf'_le _ (Finset.mem_univ _)
  have h1 := P.abs_det_div_norm_le_slowScale μ x
  have h2 := P.slowScale_le_norm μ x
  have h3 : ‖P.mat (x 0)‖ ≤ 1 := (P.norm_lt_one _).le
  have hpos := P.slowScale_pos μ x
  have hn := norm_pos_of_det_ne_zero (P.det_ne_zero (x 0))
  have hd := abs_pos.2 (P.det_ne_zero (x 0))
  refine ⟨⟨hmin.trans h1, h2.trans h3⟩, ⟨?_, ?_⟩⟩
  · refine hmin.trans ?_
    exact div_le_div_of_nonneg_left hd.le hpos h2
  · refine le_trans ?_ h3
    rw [transScale, div_le_iff₀ hpos]
    rw [div_le_iff₀ hn] at h1
    linarith [mul_comm (P.slowScale μ x) ‖P.mat (x 0)‖]

/-- `κ_1` is a Borel function. -/
theorem measurable_transScale (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    Measurable (P.transScale μ) :=
  ((Measurable.of_discrete (f := fun i : ι => |(P.mat i).det|)).comp
    (measurable_pi_apply 0)).div (P.measurable_slowScale μ hlt)

/-- The masses of the tubes `B^π(x, R(x))` and `[x_0] ∩ B^π(x, R(x))` with Borel radii are Borel
functions of `x`. -/
theorem measurable_condMeas_eucTube (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ]
    (ξ : (ℤ → ι) → Set (ℤ → ι)) {R : (ℤ → ι) → ℝ} (hR : Measurable R) :
    Measurable (fun x => condMeas μ ξ x (P.eucTube x (R x))) ∧
      Measurable (fun x => condMeas μ ξ x ({y | y 0 = x 0} ∩ P.eucTube x (R x))) := by
  have hd : Measurable fun p : (ℤ → ι) × (ℤ → ι) =>
      eucNorm (toVec (P.proj p.2 - P.proj p.1)) :=
    (MatrixTuple.continuous_eucNorm.comp continuous_toVec).measurable.comp
      ((P.measurable_proj.comp measurable_snd).sub (P.measurable_proj.comp measurable_fst))
  have ht : MeasurableSet {p : (ℤ → ι) × (ℤ → ι) |
      eucNorm (toVec (P.proj p.2 - P.proj p.1)) ≤ R p.1} :=
    measurableSet_le hd (hR.comp measurable_fst)
  have hc : MeasurableSet {p : (ℤ → ι) × (ℤ → ι) | p.2 0 = p.1 0} :=
    measurableSet_eq_fun ((measurable_pi_apply 0).comp measurable_snd)
      ((measurable_pi_apply 0).comp measurable_fst)
  refine ⟨?_, ?_⟩
  · have h := Kernel.measurable_kernel_prodMk_left (κ := condMeasKernel μ ξ) ht
    convert h using 2 with x
    rfl
  · have h := Kernel.measurable_kernel_prodMk_left (κ := condMeasKernel μ ξ) (hc.inter ht)
    convert h using 2 with x
    rfl

/-- The masses of the tubes `Γ_1(x, R(x))` and `[x_0] ∩ Γ_1(x, R(x))` with Borel radii are
Borel functions of `x`. -/
theorem measurable_condMeas_transTube (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ]
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) (ξ : (ℤ → ι) → Set (ℤ → ι)) {R : (ℤ → ι) → ℝ}
    (hR : Measurable R) :
    Measurable (fun x => condMeas μ ξ x (P.transTube μ x (R x))) ∧
      Measurable (fun x => condMeas μ ξ x ({y | y 0 = x 0} ∩ P.transTube μ x (R x))) := by
  have hθ : Measurable fun p : (ℤ → ι) × (ℤ → ι) => P.slowAngle μ p.1 :=
    (P.measurable_slowAngle μ hlt).comp measurable_fst
  have hp2 : Measurable fun p : (ℤ → ι) × (ℤ → ι) => P.proj p.2 :=
    P.measurable_proj.comp measurable_snd
  have hp1 : Measurable fun p : (ℤ → ι) × (ℤ → ι) => P.proj p.1 :=
    P.measurable_proj.comp measurable_fst
  have hd : Measurable fun p : (ℤ → ι) × (ℤ → ι) => P.transDist μ p.1 p.2 := by
    simp only [transDist, slowDir, MatrixTuple.cross, MatrixTuple.dirVec, toVec,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    exact continuous_abs.measurable.comp (((Real.measurable_cos.comp hθ).mul
      ((measurable_snd.comp hp2).sub (measurable_snd.comp hp1))).sub
      ((Real.measurable_sin.comp hθ).mul ((measurable_fst.comp hp2).sub
        (measurable_fst.comp hp1))))
  have ht : MeasurableSet {p : (ℤ → ι) × (ℤ → ι) | P.transDist μ p.1 p.2 ≤ R p.1} :=
    measurableSet_le hd (hR.comp measurable_fst)
  have hc : MeasurableSet {p : (ℤ → ι) × (ℤ → ι) | p.2 0 = p.1 0} :=
    measurableSet_eq_fun ((measurable_pi_apply 0).comp measurable_snd)
      ((measurable_pi_apply 0).comp measurable_fst)
  refine ⟨?_, ?_⟩
  · have h := Kernel.measurable_kernel_prodMk_left (κ := condMeasKernel μ ξ) ht
    convert h using 2 with x
    rfl
  · have h := Kernel.measurable_kernel_prodMk_left (κ := condMeasKernel μ ξ) (hc.inter ht)
    convert h using 2 with x
    rfl

/-- Every Euclidean tube about `𝐢` contains a supremum-norm ball about `π𝐢` of half the radius, so
it has positive `μ_𝐢^ξ`-mass for `μ`-almost every `𝐢`. -/
theorem ae_condMeas_eucTube_pos (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    {ξ : (ℤ → ι) → Set (ℤ → ι)} (hξ : IsMeasurablePartition ξ) :
    ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < condMeas μ ξ x (P.eucTube x r) := by
  filter_upwards [ae_condMeas_preimage_closedBall_pos μ hξ P.measurable_proj] with x hx r hr
  refine (hx (r / 2) (by positivity)).trans_le (measure_mono fun y hy => ?_)
  simp only [mem_preimage, mem_closedBall, dist_eq_norm] at hy
  change eucNorm (toVec (P.proj y - P.proj x)) ≤ r
  refine (eucNorm_le_two_mul_norm _).trans ?_
  rw [norm_toVec]
  linarith

/-- Every tube `Γ_1(𝐢, r)` contains a supremum-norm ball about `π𝐢` of half the radius, so it has
positive `μ_𝐢^ξ`-mass for `μ`-almost every `𝐢`. -/
theorem ae_condMeas_transTube_pos (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    {ξ : (ℤ → ι) → Set (ℤ → ι)} (hξ : IsMeasurablePartition ξ) :
    ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < condMeas μ ξ x (P.transTube μ x r) := by
  filter_upwards [ae_condMeas_preimage_closedBall_pos μ hξ P.measurable_proj] with x hx r hr
  refine (hx (r / 2) (by positivity)).trans_le (measure_mono fun y hy => ?_)
  simp only [mem_preimage, mem_closedBall, dist_eq_norm] at hy
  change |MatrixTuple.cross (P.slowDir μ x) (toVec (P.proj y - P.proj x))| ≤ r
  have hu : ‖P.slowDir μ x‖ ≤ 1 := by
    rw [norm_fin_two]
    simp only [slowDir, MatrixTuple.dirVec, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact max_le (Real.abs_cos_le_one _) (Real.abs_sin_le_one _)
  calc |MatrixTuple.cross (P.slowDir μ x) (toVec (P.proj y - P.proj x))|
      ≤ 2 * ‖P.slowDir μ x‖ * ‖toVec (P.proj y - P.proj x)‖ := MatrixTuple.abs_cross_le _ _
    _ ≤ 2 * 1 * (r / 2) := by rw [norm_toVec]; gcongr
    _ = r := by ring

/-! ### Proposition 5.5 in the plane -/

open Classical in
/-- The coordinate `𝐣 ↦ π𝐣 ∈ ℝ²`, with the Euclidean norm, on the atoms of `ξ_1` (Feng,
Proposition 5.5 for `i = 2`); it is `0` on the extra atom `Σ ∖ Σ'`. -/
noncomputable def eucCoord (μ : Measure (ℤ → ι)) (x y : ℤ → ι) : EuclideanSpace ℝ (Fin 2) :=
  if x ∈ P.SigmaPrime μ then WithLp.toLp 2 (toVec (P.proj y)) else 0

open Classical in
/-- The transverse coordinate `𝐣 ↦ u_𝐢 ∧ π𝐣 ∈ ℝ` on the atoms of `ξ_0` (Feng, Proposition 5.5
for `i = 1`); it is `0` on the extra atom `Σ ∖ Σ'`. -/
noncomputable def transCoord (μ : Measure (ℤ → ι)) (x y : ℤ → ι) : ℝ :=
  if x ∈ P.SigmaPrime μ then MatrixTuple.cross (P.slowDir μ x) (toVec (P.proj y)) else 0

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- For `𝐢 ∈ Σ'`, the tubes of the coordinate `eucCoord` are the Euclidean tubes `B^π(𝐢, r)` of
Feng, Proposition 5.5 for `i = 2`. -/
theorem coordTube_eucCoord (μ : Measure (ℤ → ι)) {x : ℤ → ι} (hx : x ∈ P.SigmaPrime μ)
    (r : ℝ) : coordTube (P.eucCoord μ) x r = P.eucTube x r := by
  ext y
  simp only [coordTube, eucCoord, hx, ↓reduceIte, eucTube, mem_ofPred_eq, dist_eq_norm,
    ← WithLp.toLp_sub, ← toVec_sub]
  rfl

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- For `𝐢 ∈ Σ'`, the tubes of the coordinate `transCoord` are the tubes `Γ_1(𝐢, r)` of Feng,
Proposition 5.5 for `i = 1`. -/
theorem coordTube_transCoord (μ : Measure (ℤ → ι)) {x : ℤ → ι} (hx : x ∈ P.SigmaPrime μ)
    (r : ℝ) : coordTube (P.transCoord μ) x r = P.transTube μ x r := by
  ext y
  simp only [coordTube, transCoord, hx, ↓reduceIte, transTube, transDist, mem_ofPred_eq,
    Real.dist_eq]
  have h : MatrixTuple.cross (P.slowDir μ x) (toVec (P.proj y)) -
      MatrixTuple.cross (P.slowDir μ x) (toVec (P.proj x)) =
      MatrixTuple.cross (P.slowDir μ x) (toVec (P.proj y - P.proj x)) := by
    simp only [MatrixTuple.cross, toVec_sub, Pi.sub_apply]
    ring
  rw [h]

/-- The Euclidean coordinate is a coordinate on the atoms of `ξ_1` whose fibres are the atoms
of `ξ_2`, the setting of Feng, Proposition 5.5 for `i = 2`: `ξ_2(𝐢) = ξ_1(𝐢) ∩ π⁻¹{π𝐢}`. -/
theorem isFibreCoordinate_eucCoord (μ : Measure (ℤ → ι))
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    IsFibreCoordinate (P.xi μ 1) (P.xi μ 2) (P.eucCoord μ) := by
  classical
  refine ⟨?_, fun x y hy => ?_, fun x y hy => ?_⟩
  · change Measurable fun p : (ℤ → ι) × (ℤ → ι) => P.eucCoord μ p.1 p.2
    simp only [eucCoord]
    exact Measurable.ite (measurable_fst (P.measurableSet_SigmaPrime μ hlt))
      ((WithLp.measurable_toLp 2 _).comp
        (continuous_toVec.measurable.comp (P.measurable_proj.comp measurable_snd)))
      measurable_const
  · by_cases hx : x ∈ P.SigmaPrime μ
    · rw [xi, atomsOn_of_mem hx] at hy
      funext z
      simp only [eucCoord, hx, hy.2, ↓reduceIte]
    · rw [xi, atomsOn_of_notMem hx] at hy
      funext z
      simp only [eucCoord, hx, (show y ∉ P.SigmaPrime μ from hy), ↓reduceIte]
  · by_cases hx : x ∈ P.SigmaPrime μ
    · rw [xi, atomsOn_of_mem hx] at hy
      obtain ⟨⟨hyp, -⟩, hyS⟩ := hy
      rw [xi, atomsOn_of_mem hx]
      simp only [eucCoord, hx, ↓reduceIte, mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨⟨-, hv⟩, -⟩
        have h0 : toVec (P.proj y - P.proj x) = 0 := hv
        rw [toVec_sub, sub_eq_zero] at h0
        rw [h0]
      · intro h
        refine ⟨⟨hyp, ?_⟩, hyS⟩
        change toVec (P.proj y - P.proj x) = 0
        rw [toVec_sub, WithLp.toLp_injective 2 h, sub_self]
    · rw [xi, atomsOn_of_notMem hx] at hy ⊢
      exact ⟨fun _ => by simp [eucCoord, hx], fun _ => hy⟩

/-- The transverse coordinate is a coordinate on the atoms of `ξ_0` whose fibres are the atoms
of `ξ_1`, the setting of Feng, Proposition 5.5 for `i = 1`: on `ξ_0(𝐢)` the slow direction is
`u_𝐢`, and `ξ_1(𝐢) = ξ_0(𝐢) ∩ {𝐣 : u_𝐢 ∧ (π𝐣 - π𝐢) = 0}`. -/
theorem isFibreCoordinate_transCoord (μ : Measure (ℤ → ι))
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    IsFibreCoordinate (P.xi μ 0) (P.xi μ 1) (P.transCoord μ) := by
  classical
  refine ⟨?_, fun x y hy => ?_, fun x y hy => ?_⟩
  · change Measurable fun p : (ℤ → ι) × (ℤ → ι) => P.transCoord μ p.1 p.2
    have hθ : Measurable fun p : (ℤ → ι) × (ℤ → ι) => P.slowAngle μ p.1 :=
      (P.measurable_slowAngle μ hlt).comp measurable_fst
    have hp2 : Measurable fun p : (ℤ → ι) × (ℤ → ι) => P.proj p.2 :=
      P.measurable_proj.comp measurable_snd
    simp only [transCoord]
    refine Measurable.ite (measurable_fst (P.measurableSet_SigmaPrime μ hlt)) ?_
      measurable_const
    simp only [slowDir, MatrixTuple.cross, MatrixTuple.dirVec, toVec, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    exact ((Real.measurable_cos.comp hθ).mul (measurable_snd.comp hp2)).sub
      ((Real.measurable_sin.comp hθ).mul (measurable_fst.comp hp2))
  · by_cases hx : x ∈ P.SigmaPrime μ
    · rw [xi, atomsOn_of_mem hx] at hy
      obtain ⟨⟨hyp, -⟩, hyS⟩ := hy
      have hθ : P.slowAngle μ y = P.slowAngle μ x := P.slowAngle_congr μ hlt hyp
      funext z
      simp only [transCoord, hx, hyS, ↓reduceIte, slowDir, hθ]
    · rw [xi, atomsOn_of_notMem hx] at hy
      funext z
      simp only [transCoord, hx, (show y ∉ P.SigmaPrime μ from hy), ↓reduceIte]
  · by_cases hx : x ∈ P.SigmaPrime μ
    · rw [xi, atomsOn_of_mem hx] at hy
      obtain ⟨⟨hyp, -⟩, hyS⟩ := hy
      rw [xi, atomsOn_of_mem hx]
      simp only [transCoord, hx, ↓reduceIte, mem_inter_iff, mem_ofPred_eq]
      rw [P.mem_oseledets_one_iff μ hlt hx]
      have h : MatrixTuple.cross (P.slowDir μ x) (toVec (P.proj y - P.proj x)) =
          MatrixTuple.cross (P.slowDir μ x) (toVec (P.proj y)) -
            MatrixTuple.cross (P.slowDir μ x) (toVec (P.proj x)) := by
        simp only [MatrixTuple.cross, toVec_sub, Pi.sub_apply]
        ring
      rw [h, sub_eq_zero]
      exact ⟨fun h' => h'.1.2, fun h' => ⟨⟨hyp, h'⟩, hyS⟩⟩
    · rw [xi, atomsOn_of_notMem hx] at hy ⊢
      exact ⟨fun _ => by simp [transCoord, hx], fun _ => hy⟩

/-- Feng, Proposition 5.5 for `i = 2` and `ℓ = 1` (p. 34, through his Lemma 2.5 (1) and Feng–Hu,
Proposition 3.5), in the plane: the density of `[x_0]` for `μ_𝐢^{ξ_1}` along the Euclidean tubes
about `𝐢` tends to `μ_𝐢^{ξ_2}([x_0])`. On `Σ'` the Euclidean tubes are the tubes of the
coordinate `eucCoord`, `𝐣 ↦ π𝐣` with the Euclidean norm (`coordTube_eucCoord`), whose fibres in
the atoms of `ξ_1` are the atoms of `ξ_2` (`isFibreCoordinate_eucCoord`); the statement is
`ae_tendsto_ratio_coordTube`, Besicovitch's differentiation theorem for
`π_*(μ_𝐢^{ξ_1}|_{[a]}) ≤ π_* μ_𝐢^{ξ_1}`, whose density at `π𝐣` is `μ_𝐣^{ξ_2}([a])`
(`double_conditional`). -/
theorem tendsto_condMeas_eucTube_ratio (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    ∀ᵐ x ∂μ, Tendsto (fun r => (condMeas μ (P.xi μ 1) x).real ({y | y 0 = x 0} ∩ P.eucTube x r) /
      (condMeas μ (P.xi μ 1) x).real (P.eucTube x r)) (𝓝[>] 0)
      (𝓝 ((condMeas μ (P.xi μ 2) x).real {y | y 0 = x 0})) := by
  have hS : ∀ᵐ x ∂μ, x ∈ P.SigmaPrime μ := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (P.measure_SigmaPrime_compl_of_ergodic μ herg hlt)] with x hx using not_not.1 hx
  have hpos : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r →
      0 < condMeas μ (P.xi μ 1) x (coordTube (P.eucCoord μ) x r) := by
    filter_upwards [P.ae_condMeas_eucTube_pos μ (P.isMeasurablePartition_xi μ hlt 1), hS]
      with x hx hxS r hr
    rw [P.coordTube_eucCoord μ hxS]
    exact hx r hr
  filter_upwards [ae_tendsto_ratio_coordTube μ (P.isMeasurablePartition_xi μ hlt 1)
    (P.isMeasurablePartition_xi μ hlt 2) (fun x => P.xi_succ_subset μ 1 x)
    (P.isFibreCoordinate_eucCoord μ hlt) hpos, hS] with x hx hxS
  simpa only [P.coordTube_eucCoord μ hxS] using hx

/-- Feng, Proposition 5.5, integrability of `g` (5.14), for `i = 2` and `ℓ = 1` (pp. 35 to 36,
after Feng–Hu, Lemma 3.3 and Proposition 3.5), in the plane: the logarithmic densities of `[x_0]`
along the Euclidean tubes have an integrable envelope. This is `exists_envelope_coordTube` for
the coordinate `eucCoord`: the weak maximal inequality (5.18) of the Besicovitch covering theorem
in the plane, integrated over the atoms of `ξ_1`, and the finite entropy of `𝒫`. -/
theorem exists_envelope_eucTube (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    ∃ F : (ℤ → ι) → ℝ, Integrable F μ ∧ ∀ᵐ x ∂μ, ∀ r ∈ Ioc (0 : ℝ) 1,
      -Real.log ((condMeas μ (P.xi μ 1) x).real ({y | y 0 = x 0} ∩ P.eucTube x r) /
        (condMeas μ (P.xi μ 1) x).real (P.eucTube x r)) ≤ F x := by
  have hS : ∀ᵐ x ∂μ, x ∈ P.SigmaPrime μ := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (P.measure_SigmaPrime_compl_of_ergodic μ herg hlt)] with x hx using not_not.1 hx
  have hpos : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r →
      0 < condMeas μ (P.xi μ 1) x (coordTube (P.eucCoord μ) x r) := by
    filter_upwards [P.ae_condMeas_eucTube_pos μ (P.isMeasurablePartition_xi μ hlt 1), hS]
      with x hx hxS r hr
    rw [P.coordTube_eucCoord μ hxS]
    exact hx r hr
  have hΦ := P.isFibreCoordinate_eucCoord μ hlt
  obtain ⟨F, hF, hFb⟩ := exists_envelope_coordTube μ (P.isMeasurablePartition_xi μ hlt 1)
    hΦ.measurable hΦ.const hpos
  refine ⟨F, hF, ?_⟩
  filter_upwards [hFb, hS] with x hx hxS
  simpa only [P.coordTube_eucCoord μ hxS] using hx

/-- Feng, Proposition 5.5 for `i = 1` and `ℓ = 1` (p. 34), in the plane: the density of `[x_0]`
for `μ_𝐢^{ξ_0}` along the tubes `Γ_1(𝐢, r)` tends to `μ_𝐢^{ξ_1}([x_0])`. Within the atom `ξ_0(𝐢)`
the slow direction is constant, the tubes are the preimages of intervals under the transverse
coordinate `transCoord`, `𝐣 ↦ u_𝐢 ∧ π𝐣 ∈ ℝ` (`coordTube_transCoord`), and the atoms of `ξ_1` are
its fibres (`isFibreCoordinate_transCoord`); the statement is `ae_tendsto_ratio_coordTube`,
Besicovitch's differentiation theorem on the line for the images of `μ_𝐢^{ξ_0}|_{[a]}` and
`μ_𝐢^{ξ_0}`. -/
theorem tendsto_condMeas_transTube_ratio (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    ∀ᵐ x ∂μ, Tendsto (fun r => (condMeas μ (P.xi μ 0) x).real
      ({y | y 0 = x 0} ∩ P.transTube μ x r) / (condMeas μ (P.xi μ 0) x).real (P.transTube μ x r))
      (𝓝[>] 0) (𝓝 ((condMeas μ (P.xi μ 1) x).real {y | y 0 = x 0})) := by
  have hS : ∀ᵐ x ∂μ, x ∈ P.SigmaPrime μ := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (P.measure_SigmaPrime_compl_of_ergodic μ herg hlt)] with x hx using not_not.1 hx
  have hpos : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r →
      0 < condMeas μ (P.xi μ 0) x (coordTube (P.transCoord μ) x r) := by
    filter_upwards [P.ae_condMeas_transTube_pos μ (P.isMeasurablePartition_xi μ hlt 0), hS]
      with x hx hxS r hr
    rw [P.coordTube_transCoord μ hxS]
    exact hx r hr
  filter_upwards [ae_tendsto_ratio_coordTube μ (P.isMeasurablePartition_xi μ hlt 0)
    (P.isMeasurablePartition_xi μ hlt 1) (fun x => P.xi_succ_subset μ 0 x)
    (P.isFibreCoordinate_transCoord μ hlt) hpos, hS] with x hx hxS
  simpa only [P.coordTube_transCoord μ hxS] using hx

/-- Feng, Proposition 5.5, integrability of `g` (5.14), for `i = 1` and `ℓ = 1` (pp. 35 to 36),
in the plane: the logarithmic densities of `[x_0]` along the tubes `Γ_1(𝐢, r)` have an integrable
envelope: `exists_envelope_coordTube` for the coordinate `transCoord`, the weak maximal
inequality on the line (`exists_ballRatio_maximal_constant_of_besicovitch`, after
`ExactOverlaps.exists_ballRatio_maximal_constant`, applied to the images under the transverse
coordinate) integrated over the atoms of `ξ_0`. -/
theorem exists_envelope_transTube (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    ∃ F : (ℤ → ι) → ℝ, Integrable F μ ∧ ∀ᵐ x ∂μ, ∀ r ∈ Ioc (0 : ℝ) 1,
      -Real.log ((condMeas μ (P.xi μ 0) x).real ({y | y 0 = x 0} ∩ P.transTube μ x r) /
        (condMeas μ (P.xi μ 0) x).real (P.transTube μ x r)) ≤ F x := by
  have hS : ∀ᵐ x ∂μ, x ∈ P.SigmaPrime μ := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (P.measure_SigmaPrime_compl_of_ergodic μ herg hlt)] with x hx using not_not.1 hx
  have hpos : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r →
      0 < condMeas μ (P.xi μ 0) x (coordTube (P.transCoord μ) x r) := by
    filter_upwards [P.ae_condMeas_transTube_pos μ (P.isMeasurablePartition_xi μ hlt 0), hS]
      with x hx hxS r hr
    rw [P.coordTube_transCoord μ hxS]
    exact hx r hr
  have hΦ := P.isFibreCoordinate_transCoord μ hlt
  obtain ⟨F, hF, hFb⟩ := exists_envelope_coordTube μ (P.isMeasurablePartition_xi μ hlt 0)
    hΦ.measurable hΦ.const hpos
  refine ⟨F, hF, ?_⟩
  filter_upwards [hFb, hS] with x hx hxS
  simpa only [P.coordTube_transCoord μ hxS] using hx

/-- Feng, Proposition 5.1 for `i = 1` (pp. 30 to 38) in the plane: `ϑ_0 ≥ (h_1 - h_0)/λ_1`. This is
`ae_transverseDimGe_of_step` for `ζ = ξ_0`, `ζ' = ξ_1`, the tubes `Γ_1(𝐢, r)` and the factor
`κ_1`, with `∫ log κ_1 dμ = λ_1` (`integral_log_transScale`) and the one-step identity
`condMeas_transTube_step`: in the plane Lemma 5.4 holds with `ℓ = 1`, equality and no angle
between Oseledets subspaces. -/
theorem transverseDimGe_one (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    ∀ᵐ x ∂μ, P.TransverseDimGe μ x ((P.dimEntropy μ 1 - P.dimEntropy μ 0) / P.lyapunov₁ μ) := by
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
  obtain ⟨κ0, hκ0, hκ⟩ := P.exists_scale_bounds
  exact ae_transverseDimGe_of_step μ herg (P.xi μ 0) (P.xi μ 1) (P.transTube μ)
    (fun x r r' hrr' y hy => le_trans hy hrr') (P.transScale μ) (P.measurable_transScale μ hlt)
    hκ0 (fun x => (hκ μ x).2) (P.lyapunov₁_neg herg.toMeasurePreserving)
    (P.integral_log_transScale μ herg hlt) (P.condMeas_transTube_step μ herg hlt)
    (P.ae_condMeas_transTube_pos μ (P.isMeasurablePartition_xi μ hlt 0))
    (fun R hR => P.measurable_condMeas_transTube μ hlt _ hR)
    (P.tendsto_condMeas_transTube_ratio μ herg hlt) (P.exists_envelope_transTube μ herg hlt)

/-- Feng, Proposition 5.1 for `i = s = 2` (pp. 30 to 38) in the plane:
`ϑ_1 = \underline{δ}_1 ≥ (h_2 - h_1)/λ_2`. This is `ae_transverseDimGe_of_step` for `ζ = ξ_1`,
`ζ' = ξ_2`, the Euclidean tubes and the factor `κ_2`, with `∫ log κ_2 dμ = λ_2`
(`integral_log_slowScale`) and the one-step identity `condMeas_eucTube_step`, followed by the
comparison of the supremum-norm balls of `ν^1_𝐢` with the Euclidean tubes of twice the radius. -/
theorem lowerLocalDimGe_condProj_one (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    ∀ᵐ x ∂μ, LowerLocalDimGe (P.condProj μ 1 x) (P.proj x)
      ((P.dimEntropy μ 2 - P.dimEntropy μ 1) / P.lyapunov₂ μ) := by
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
  obtain ⟨κ0, hκ0, hκ⟩ := P.exists_scale_bounds
  have hlam : P.lyapunov₂ μ < 0 := hlt.trans (P.lyapunov₁_neg herg.toMeasurePreserving)
  have htube := ae_transverseDimGe_of_step μ herg (P.xi μ 1) (P.xi μ 2) P.eucTube
    (fun x r r' hrr' y hy => le_trans hy hrr') (P.slowScale μ) (P.measurable_slowScale μ hlt)
    hκ0 (fun x => (hκ μ x).1) hlam (P.integral_log_slowScale μ herg hlt)
    (P.condMeas_eucTube_step μ herg hlt)
    (P.ae_condMeas_eucTube_pos μ (P.isMeasurablePartition_xi μ hlt 1))
    (fun R hR => P.measurable_condMeas_eucTube μ _ hR)
    (P.tendsto_condMeas_eucTube_ratio μ herg hlt) (P.exists_envelope_eucTube μ herg hlt)
  filter_upwards [htube, ae_condMeas_preimage_closedBall_pos μ (P.isMeasurablePartition_xi μ hlt 1)
    P.measurable_proj] with x hx hpos
  intro a ha
  rcases lt_or_ge a 0 with ha0 | ha0
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with r ⟨hr0, hr1⟩
    have h1 : Real.log ((P.condProj μ 1 x).real (closedBall (P.proj x) r)) ≤ 0 :=
      Real.log_nonpos measureReal_nonneg measureReal_le_one
    have h2 : Real.log r < 0 := Real.log_neg hr0 hr1
    have := div_nonneg_of_nonpos h1 h2.le
    linarith
  · obtain ⟨c, hac, hc⟩ := exists_between ha
    have hc0 : 0 < c := ha0.trans_lt hac
    have h2r : Tendsto (fun r : ℝ => 2 * r) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · simpa using (tendsto_nhdsWithin_iff.1 (tendsto_id (x := 𝓝[>] (0 : ℝ)))).1.const_mul 2
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact mem_Ioi.2 (by have : (0 : ℝ) < r := hr; positivity)
    set K := c * Real.log 2 / (c - a) with hK
    filter_upwards [h2r.eventually (hx c hc), Ioo_mem_nhdsGT (lt_min (by norm_num : (0 : ℝ) < 1 / 2)
      (Real.exp_pos (-K)))] with r hr ⟨hr0, hrlt⟩
    have hr12 : r < 1 / 2 := hrlt.trans_le (min_le_left _ _)
    have hrK : r < Real.exp (-K) := hrlt.trans_le (min_le_right _ _)
    have hlog2r : Real.log (2 * r) < 0 := Real.log_neg (by positivity) (by linarith)
    have hlogr : Real.log r < 0 := Real.log_neg hr0 (by linarith)
    have hlogrK : Real.log r < -K := by
      have := Real.log_lt_log hr0 hrK
      rwa [Real.log_exp] at this
    -- the ball lies in the Euclidean tube of twice the radius
    have hsub : P.proj ⁻¹' closedBall (P.proj x) r ⊆ P.eucTube x (2 * r) := by
      intro y hy
      simp only [mem_preimage, mem_closedBall, dist_eq_norm] at hy
      change eucNorm (toVec (P.proj y - P.proj x)) ≤ 2 * r
      refine (eucNorm_le_two_mul_norm _).trans ?_
      rw [norm_toVec]
      linarith
    have hB : 0 < (P.condProj μ 1 x).real (closedBall (P.proj x) r) := by
      rw [condProj, measureReal_def, Measure.map_apply P.measurable_proj measurableSet_closedBall]
      exact ENNReal.toReal_pos (hpos r hr0).ne' (measure_ne_top _ _)
    have hle : (P.condProj μ 1 x).real (closedBall (P.proj x) r) ≤
        (condMeas μ (P.xi μ 1) x).real (P.eucTube x (2 * r)) := by
      rw [condProj, measureReal_def, Measure.map_apply P.measurable_proj measurableSet_closedBall]
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
    have h1 := Real.log_le_log hB hle
    rw [le_div_iff_of_neg hlog2r] at hr
    rw [Real.log_mul two_ne_zero hr0.ne'] at hr
    have hKeq : K * (c - a) = c * Real.log 2 := by
      rw [hK]
      field_simp [show c - a ≠ 0 by linarith]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [le_div_iff_of_neg hlogr]
    nlinarith

/-- The steps of Feng's Section 6 hold in the plane, for every ergodic `μ` with `λ_2 < λ_1`. -/
theorem fengSteps (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (_hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) : P.FengSteps μ where
  c1 := P.hasLocalDim_condProj_two μ herg hlt
  transverse_two := P.lowerLocalDimGe_condProj_one μ herg hlt
  c2_one := P.upperLocalDimLe_condProj_one μ herg hlt
  transverse_one := P.transverseDimGe_one μ herg hlt
  c3_zero := P.lowerLocalDimGe_condProj_zero μ herg hlt
  c2_zero := P.upperLocalDimLe_condProj_zero μ herg hlt
  c3_neg := P.lowerLocalDimGe_map_proj μ hlt
  c2_neg := P.upperLocalDimLe_map_proj μ herg hlt

end PlanarSystem

/-- The steps of Feng's Section 6 for every planar system and every ergodic measure with
`λ_2 < λ_1` imply `PlanarFengLedrappierYoung`. -/
theorem planarFengLedrappierYoung_of_fengSteps
    (h : ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (P : PlanarSystem ι) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ],
      MeasurePreserving (shift 1) μ μ → Ergodic (shift 1) μ → P.lyapunov₂ μ < P.lyapunov₁ μ →
      P.FengSteps μ) :
    PlanarFengLedrappierYoung.{u} := by
  intro ι _ _ _ P μ _ hinv herg hlt
  exact P.isExactDim_of_fengSteps μ (h P μ hinv herg hlt)

/-- `PlanarFengLedrappierYoung`, Feng, Theorems 1.2 (ii) and 1.3, for planar systems with
`λ_2 < λ_1`. -/
theorem planarFengLedrappierYoung_holds : PlanarFengLedrappierYoung.{u} :=
  planarFengLedrappierYoung_of_fengSteps fun P μ _ hinv herg hlt =>
    P.fengSteps μ hinv herg hlt

/-- `FengLedrappierYoung`, the first part of `thm:feng1` for box-like systems, from the planar
statement (`PlanarFengLedrappierYoung.fengLedrappierYoung`). -/
theorem fengLedrappierYoung_holds : FengLedrappierYoung.{u} :=
  planarFengLedrappierYoung_holds.fengLedrappierYoung

/-- `FengLedrappierYoungBar`, the second part of `thm:feng1`, from the first
(`fengLedrappierYoungBar_of_fengLedrappierYoung`). -/
theorem fengLedrappierYoungBar_holds : FengLedrappierYoungBar.{u} :=
  fengLedrappierYoungBar_of_fengLedrappierYoung fengLedrappierYoung_holds

end BoxLike
