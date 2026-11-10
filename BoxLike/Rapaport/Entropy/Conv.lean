module

/-
Convolution of planar measures for the proof of Rapaport's theorem (arXiv:2309.03985): the
iterated convolutions `convk`, their marginals and coordinate variances (used in Lemma 3.2,
lines 867 to 1017, and Proposition 1.7, lines 1075 to 1188), the decomposition of `θ^{∗k}` over
tuples of components (proof of Proposition 1.7), lower bounds for the entropy of `σ ∗ τ` through
the concavity of entropy under mixtures of translates (`Rapaport/Entropy/ConvBind.lean`), and the
two-sided bound for a small `τ` through the product space and the perturbation count (2.7).

* `convk`: `convk_zero`, `convk_succ`, `convk_cons`, `convk_congr`, `convk_one`,
  `isProbabilityMeasure_convk`, `convPow_zero`, `convPow_succ`, `convPow_one`,
  `isProbabilityMeasure_convPow`.
* Linear images and translates: `map_fst_conv`, `map_snd_conv`, `map_diagMap_conv`,
  `map_add_const_conv`, `conv_map_add_const`.
* Marginals of `convk`: `charFun_map_fst_convk`, `charFun_map_snd_convk`, `map_fst_convk`,
  `map_snd_convk`, `map_fst_convk_eq_continuousSumLaw`, `map_snd_convk_eq_continuousSumLaw`.
* Variances: `var₁_nonneg`, `var₂_nonneg`, `var₁_eq_variance_map`, `var₂_eq_variance_map`,
  `var₁_map_add_const`, `var₂_map_add_const`, `var₁_map_diagMap`, `var₂_map_diagMap`,
  `var₁_le_of_inBall`, `var₂_le_of_inBall`, `BddSupp.memLp_fst`, `BddSupp.memLp_snd`,
  `var₁_conv_of_memLp`, `var₂_conv_of_memLp`, `var₁_conv`, `var₂_conv`, `var₁_convk`,
  `var₂_convk`, `var₁_convPow`, `var₂_convPow`.
* Finite families (reordering and splitting the factors): `convFam`,
  `isProbabilityMeasure_convFam`, `convFam_comp_equiv`, `convFam_split`, `convk_eq_convFam`,
  `convFam_eq_convk`, `convk_comp_equiv`, `convk_split`, `BddSupp.convFam`, `var₁_convFam`,
  `var₂_convFam`, `map_diagMap_convk`, `map_diagMap_convFam`.
* Mixtures: `sFinite_finset_sum`, `finset_sum_conv`, `conv_finset_sum`, `convk_sum`,
  `convk_sum_ofReal`, `isFiniteMeasure_comp`, `convPow_eq_sum_comp`,
  `sum_prod_measureReal_fiber`.
* Lower bounds for `σ ∗ τ` (mixtures of translates): `ent_conv_ge_of_fiberBound`,
  `cent_conv_ge_of_fiberBound`, `ent_conv_ge_sub_log_four`, `ent_conv_ge_sub_log_four'`,
  `ent_conv_ge_hLabel`, `ent_conv_ge_vLabel`, `Exps.cent_conv_E_ge`, `Exps.cent_conv_E_E₂_ge`,
  `Exps.cent_conv_E_E₁_ge`, `Exps.cent_conv_E₁_ge`.
* Small `τ` (product space, no mixture): `shiftIn`, `measurable_shiftIn`, `conv_eq_map_shiftIn`,
  `abs_cent_sub_cent_le_of_fiberBound`, `ent_conv_le_ent_add_log_of_fiberBound`,
  `ent_le_ent_conv_add_log_of_fiberBound`, `abs_ent_conv_sub_ent_le_rect`,
  `abs_cent_conv_sub_cent_le_rect`, `Exps.abs_cent_conv_E_sub_le`.
-/
public import BoxLike.Rapaport.Entropy.ConvBind
public import ExactOverlaps.Entropy.ContinuousProductLaw
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

namespace BoxLike.Rapaport

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ### Iterated convolutions -/

section Convk

variable {k : ℕ}

/-- The empty convolution is `δ_0`. -/
theorem convk_zero (θ : Fin 0 → Measure (ℝ × ℝ)) : convk 0 θ = Measure.dirac 0 := rfl

/-- The recursion `θ_0 ∗ θ_1 ∗ ⋯ ∗ θ_k = θ_0 ∗ (θ_1 ∗ ⋯ ∗ θ_k)` (the convolutions of Rapaport,
lines 631 to 636 and 1161 to 1162 of the source). -/
theorem convk_succ (θ : Fin (k + 1) → Measure (ℝ × ℝ)) :
    convk (k + 1) θ = θ 0 ∗ convk k (Fin.tail θ) := rfl

/-- Convolution of a tuple with a new first entry. -/
theorem convk_cons (μ : Measure (ℝ × ℝ)) (θ : Fin k → Measure (ℝ × ℝ)) :
    convk (k + 1) (Fin.cons μ θ) = μ ∗ convk k θ := by
  rw [convk_succ, Fin.cons_zero, Fin.tail_cons]

/-- `convk` depends only on the entries of the tuple. -/
theorem convk_congr {θ θ' : Fin k → Measure (ℝ × ℝ)} (h : ∀ i, θ i = θ' i) :
    convk k θ = convk k θ' := by
  rw [funext h]

/-- The convolution of one measure is that measure. -/
theorem convk_one (θ : Fin 1 → Measure (ℝ × ℝ)) [SFinite (θ 0)] : convk 1 θ = θ 0 := by
  rw [convk_succ, convk_zero, Measure.conv_dirac_zero]

/-- The convolution of `k` probability measures is a probability measure. -/
instance isProbabilityMeasure_convk : ∀ (k : ℕ) (θ : Fin k → Measure (ℝ × ℝ))
    [∀ i, IsProbabilityMeasure (θ i)], IsProbabilityMeasure (convk k θ)
  | 0, _, _ => by
    show IsProbabilityMeasure (Measure.dirac 0)
    infer_instance
  | k + 1, θ, _ => by
    have : ∀ i, IsProbabilityMeasure (Fin.tail θ i) := fun i =>
      inferInstanceAs (IsProbabilityMeasure (θ i.succ))
    have := isProbabilityMeasure_convk k (Fin.tail θ)
    show IsProbabilityMeasure (θ 0 ∗ convk k (Fin.tail θ))
    infer_instance

/-- `θ^{∗0} = δ_0`. -/
theorem convPow_zero (θ : Measure (ℝ × ℝ)) : convPow θ 0 = Measure.dirac 0 := rfl

/-- `θ^{∗(k+1)} = θ ∗ θ^{∗k}`, Rapaport's `k`-fold self-convolution (lines 631 to 636). -/
theorem convPow_succ (θ : Measure (ℝ × ℝ)) (k : ℕ) : convPow θ (k + 1) = θ ∗ convPow θ k := rfl

/-- `θ^{∗1} = θ`. -/
theorem convPow_one (θ : Measure (ℝ × ℝ)) [SFinite θ] : convPow θ 1 = θ := by
  rw [convPow_succ, convPow_zero, Measure.conv_dirac_zero]

/-- A self-convolution of a probability measure is a probability measure. -/
instance isProbabilityMeasure_convPow (θ : Measure (ℝ × ℝ)) [IsProbabilityMeasure θ] (k : ℕ) :
    IsProbabilityMeasure (convPow θ k) :=
  isProbabilityMeasure_convk k _

end Convk

/-! ### Linear images, translates and marginals -/

section Marginals

variable {σ τ : Measure (ℝ × ℝ)} [SFinite σ] [SFinite τ]

/-- The first marginal of a convolution is the convolution of the first marginals:
`π₁(σ ∗ τ) = π₁σ ∗ π₁τ` (behind `Var(π_j σ) = ∑ Var(π_j θ_i)`, lines 1139 to 1145). -/
theorem map_fst_conv : (σ ∗ τ).map Prod.fst = σ.map Prod.fst ∗ τ.map Prod.fst := by
  simpa using Measure.map_conv_addMonoidHom (μ := σ) (ν := τ) (AddMonoidHom.fst ℝ ℝ)
    measurable_fst

/-- The second marginal of a convolution is the convolution of the second marginals:
`π₂(σ ∗ τ) = π₂σ ∗ π₂τ`. -/
theorem map_snd_conv : (σ ∗ τ).map Prod.snd = σ.map Prod.snd ∗ τ.map Prod.snd := by
  simpa using Measure.map_conv_addMonoidHom (μ := σ) (ν := τ) (AddMonoidHom.snd ℝ ℝ)
    measurable_snd

/-- The diagonal map `diag(s, t)` as an additive homomorphism. -/
private def diagMapHom (s t : ℝ) : ℝ × ℝ →+ ℝ × ℝ where
  toFun := diagMap s t
  map_zero' := by simp [diagMap]
  map_add' := diagMap_add s t

/-- A diagonal map commutes with convolution (Rapaport's rescalings `A_χ^i` are diagonal). -/
theorem map_diagMap_conv (s t : ℝ) :
    (σ ∗ τ).map (diagMap s t) = σ.map (diagMap s t) ∗ τ.map (diagMap s t) :=
  Measure.map_conv_addMonoidHom (diagMapHom s t) (measurable_diagMap s t)

/-- Translating a convolution translates its first factor. -/
theorem map_add_const_conv (v : ℝ × ℝ) : (σ ∗ τ).map (· + v) = σ.map (· + v) ∗ τ := by
  rw [← Measure.conv_dirac (σ ∗ τ) v, Measure.conv_assoc, Measure.conv_comm τ,
    ← Measure.conv_assoc, Measure.conv_dirac]

/-- Translating the second factor of a convolution translates the convolution. -/
theorem conv_map_add_const (v : ℝ × ℝ) : σ ∗ τ.map (· + v) = (σ ∗ τ).map (· + v) := by
  rw [← Measure.conv_dirac (σ ∗ τ) v, Measure.conv_assoc, Measure.conv_dirac]

end Marginals

section MarginalsConvk

/-- The characteristic function of the first marginal of `θ_0 ∗ ⋯ ∗ θ_{k-1}` is the product of
those of the first marginals. -/
theorem charFun_map_fst_convk : ∀ (k : ℕ) (θ : Fin k → Measure (ℝ × ℝ))
    [∀ i, IsProbabilityMeasure (θ i)] (t : ℝ),
    charFun ((convk k θ).map Prod.fst) t = ∏ i, charFun ((θ i).map Prod.fst) t
  | 0, θ, _, t => by
    rw [convk_zero, Measure.map_dirac' measurable_fst, charFun_dirac, Finset.univ_eq_empty,
      Finset.prod_empty]
    simp
  | k + 1, θ, _, t => by
    have : ∀ i, IsProbabilityMeasure (Fin.tail θ i) := fun i =>
      inferInstanceAs (IsProbabilityMeasure (θ i.succ))
    rw [convk_succ, map_fst_conv, charFun_conv, Fin.prod_univ_succ,
      charFun_map_fst_convk k (Fin.tail θ) t]
    rfl

/-- The characteristic function of the second marginal of `θ_0 ∗ ⋯ ∗ θ_{k-1}` is the product of
those of the second marginals. -/
theorem charFun_map_snd_convk : ∀ (k : ℕ) (θ : Fin k → Measure (ℝ × ℝ))
    [∀ i, IsProbabilityMeasure (θ i)] (t : ℝ),
    charFun ((convk k θ).map Prod.snd) t = ∏ i, charFun ((θ i).map Prod.snd) t
  | 0, θ, _, t => by
    rw [convk_zero, Measure.map_dirac' measurable_snd, charFun_dirac, Finset.univ_eq_empty,
      Finset.prod_empty]
    simp
  | k + 1, θ, _, t => by
    have : ∀ i, IsProbabilityMeasure (Fin.tail θ i) := fun i =>
      inferInstanceAs (IsProbabilityMeasure (θ i.succ))
    rw [convk_succ, map_snd_conv, charFun_conv, Fin.prod_univ_succ,
      charFun_map_snd_convk k (Fin.tail θ) t]
    rfl

variable {k : ℕ} (θ : Fin k → Measure (ℝ × ℝ)) [∀ i, IsProbabilityMeasure (θ i)]

/-- The first marginal of `θ_0 ∗ ⋯ ∗ θ_{k-1}` is the law of the sum of independent variables with
the first marginals of the `θ_i` as laws (the iterated real convolution of the marginals). -/
theorem map_fst_convk :
    (convk k θ).map Prod.fst =
      (Measure.pi fun i => (θ i).map Prod.fst).map fun w => ∑ i, w i := by
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_map_fst_convk, charFun_map_sum_pi_eq_prod, Finset.prod_apply]

/-- The second marginal of `θ_0 ∗ ⋯ ∗ θ_{k-1}` is the law of the sum of independent variables
with the second marginals of the `θ_i` as laws. -/
theorem map_snd_convk :
    (convk k θ).map Prod.snd =
      (Measure.pi fun i => (θ i).map Prod.snd).map fun w => ∑ i, w i := by
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_map_snd_convk, charFun_map_sum_pi_eq_prod, Finset.prod_apply]

/-- The first marginal of `θ_0 ∗ ⋯ ∗ θ_{k-1}` is the vendored `continuousSumLaw` of the first
marginals, the input of the quantitative central limit theorem behind Lemma 3.2. -/
theorem map_fst_convk_eq_continuousSumLaw :
    (convk k θ).map Prod.fst = (ExactOverlaps.Entropy.continuousSumLaw
      (fun i => (⟨(θ i).map Prod.fst, inferInstance⟩ : ProbabilityMeasure ℝ)) : Measure ℝ) := by
  rw [map_fst_convk]
  rfl

/-- The second marginal of `θ_0 ∗ ⋯ ∗ θ_{k-1}` is the vendored `continuousSumLaw` of the second
marginals. -/
theorem map_snd_convk_eq_continuousSumLaw :
    (convk k θ).map Prod.snd = (ExactOverlaps.Entropy.continuousSumLaw
      (fun i => (⟨(θ i).map Prod.snd, inferInstance⟩ : ProbabilityMeasure ℝ)) : Measure ℝ) := by
  rw [map_snd_convk]
  rfl

end MarginalsConvk

/-! ### Coordinate variances -/

section Variance

variable {θ σ τ : Measure (ℝ × ℝ)}

/-- The variance of the first coordinate is nonnegative. -/
theorem var₁_nonneg (θ : Measure (ℝ × ℝ)) : 0 ≤ var₁ θ := variance_nonneg _ _

/-- The variance of the second coordinate is nonnegative. -/
theorem var₂_nonneg (θ : Measure (ℝ × ℝ)) : 0 ≤ var₂ θ := variance_nonneg _ _

/-- `var₁ θ` is the variance of the first marginal. -/
theorem var₁_eq_variance_map (θ : Measure (ℝ × ℝ)) : var₁ θ = variance id (θ.map Prod.fst) := by
  rw [var₁, variance_map measurable_id.aemeasurable measurable_fst.aemeasurable]
  rfl

/-- `var₂ θ` is the variance of the second marginal. -/
theorem var₂_eq_variance_map (θ : Measure (ℝ × ℝ)) : var₂ θ = variance id (θ.map Prod.snd) := by
  rw [var₂, variance_map measurable_id.aemeasurable measurable_snd.aemeasurable]
  rfl

/-- Translation does not change the variance of the first coordinate. -/
theorem var₁_map_add_const [IsProbabilityMeasure θ] (v : ℝ × ℝ) :
    var₁ (θ.map (· + v)) = var₁ θ := by
  rw [var₁, variance_map (by fun_prop) (measurable_add_const v).aemeasurable]
  exact variance_add_const (X := fun z : ℝ × ℝ => z.1) measurable_fst.aestronglyMeasurable v.1

/-- Translation does not change the variance of the second coordinate. -/
theorem var₂_map_add_const [IsProbabilityMeasure θ] (v : ℝ × ℝ) :
    var₂ (θ.map (· + v)) = var₂ θ := by
  rw [var₂, variance_map (by fun_prop) (measurable_add_const v).aemeasurable]
  exact variance_add_const (X := fun z : ℝ × ℝ => z.2) measurable_snd.aestronglyMeasurable v.2

/-- The diagonal map `diag(s, t)` multiplies the variance of the first coordinate by `s²`. -/
theorem var₁_map_diagMap (s t : ℝ) : var₁ (θ.map (diagMap s t)) = s ^ 2 * var₁ θ := by
  rw [var₁, variance_map (by fun_prop) (measurable_diagMap s t).aemeasurable]
  exact variance_const_mul s (fun z : ℝ × ℝ => z.1) θ

/-- The diagonal map `diag(s, t)` multiplies the variance of the second coordinate by `t²`. -/
theorem var₂_map_diagMap (s t : ℝ) : var₂ (θ.map (diagMap s t)) = t ^ 2 * var₂ θ := by
  rw [var₂, variance_map (by fun_prop) (measurable_diagMap s t).aemeasurable]
  exact variance_const_mul t (fun z : ℝ × ℝ => z.2) θ

/-- A probability measure carried by a ball of radius `R` has `var₁ θ ≤ R²` (Popoviciu). -/
theorem var₁_le_of_inBall [IsProbabilityMeasure θ] {c : ℝ × ℝ} {R : ℝ} (h : InBall θ c R) :
    var₁ θ ≤ R ^ 2 := by
  have hb : ∀ᵐ z ∂θ, z.1 ∈ Set.Icc (c.1 - R) (c.1 + R) := by
    filter_upwards [h] with z hz
    have h1 := ((norm_le_iff_abs_le _ _).1 hz).1
    rw [Prod.fst_sub, abs_le] at h1
    exact ⟨by linarith, by linarith⟩
  have := variance_le_sq_of_bounded hb measurable_fst.aemeasurable
  rw [var₁]
  convert this using 2
  ring

/-- A probability measure carried by a ball of radius `R` has `var₂ θ ≤ R²` (Popoviciu). -/
theorem var₂_le_of_inBall [IsProbabilityMeasure θ] {c : ℝ × ℝ} {R : ℝ} (h : InBall θ c R) :
    var₂ θ ≤ R ^ 2 := by
  have hb : ∀ᵐ z ∂θ, z.2 ∈ Set.Icc (c.2 - R) (c.2 + R) := by
    filter_upwards [h] with z hz
    have h1 := ((norm_le_iff_abs_le _ _).1 hz).2
    rw [Prod.snd_sub, abs_le] at h1
    exact ⟨by linarith, by linarith⟩
  have := variance_le_sq_of_bounded hb measurable_snd.aemeasurable
  rw [var₂]
  convert this using 2
  ring

/-- The first coordinate of a finite measure of bounded support has all moments. -/
theorem BddSupp.memLp_fst [IsFiniteMeasure θ] (h : BddSupp θ) (p : ℝ≥0∞) :
    MemLp (fun z : ℝ × ℝ => z.1) p θ := by
  obtain ⟨c, R, hR⟩ := h
  refine memLp_of_bounded (a := c.1 - R) (b := c.1 + R) ?_
    measurable_fst.aestronglyMeasurable p
  filter_upwards [hR] with z hz
  have h1 := ((norm_le_iff_abs_le _ _).1 hz).1
  rw [Prod.fst_sub, abs_le] at h1
  exact ⟨by linarith, by linarith⟩

/-- The second coordinate of a finite measure of bounded support has all moments. -/
theorem BddSupp.memLp_snd [IsFiniteMeasure θ] (h : BddSupp θ) (p : ℝ≥0∞) :
    MemLp (fun z : ℝ × ℝ => z.2) p θ := by
  obtain ⟨c, R, hR⟩ := h
  refine memLp_of_bounded (a := c.2 - R) (b := c.2 + R) ?_
    measurable_snd.aestronglyMeasurable p
  filter_upwards [hR] with z hz
  have h1 := ((norm_le_iff_abs_le _ _).1 hz).2
  rw [Prod.snd_sub, abs_le] at h1
  exact ⟨by linarith, by linarith⟩

variable [IsProbabilityMeasure σ] [IsProbabilityMeasure τ]

/-- Variances of the first coordinate add under convolution, for square-integrable coordinates
(independence of the two factors under `σ ⊗ τ`). -/
theorem var₁_conv_of_memLp (hσ : MemLp (fun z : ℝ × ℝ => z.1) 2 σ)
    (hτ : MemLp (fun z : ℝ × ℝ => z.1) 2 τ) : var₁ (σ ∗ τ) = var₁ σ + var₁ τ := by
  rw [var₁, Measure.conv, variance_map (by fun_prop) measurable_add.aemeasurable]
  exact variance_add_prod hσ hτ

/-- Variances of the second coordinate add under convolution, for square-integrable
coordinates. -/
theorem var₂_conv_of_memLp (hσ : MemLp (fun z : ℝ × ℝ => z.2) 2 σ)
    (hτ : MemLp (fun z : ℝ × ℝ => z.2) 2 τ) : var₂ (σ ∗ τ) = var₂ σ + var₂ τ := by
  rw [var₂, Measure.conv, variance_map (by fun_prop) measurable_add.aemeasurable]
  exact variance_add_prod hσ hτ

/-- Variances of the first coordinate add under convolution of bounded probability measures. -/
theorem var₁_conv (hσ : BddSupp σ) (hτ : BddSupp τ) : var₁ (σ ∗ τ) = var₁ σ + var₁ τ :=
  var₁_conv_of_memLp (hσ.memLp_fst 2) (hτ.memLp_fst 2)

/-- Variances of the second coordinate add under convolution of bounded probability measures. -/
theorem var₂_conv (hσ : BddSupp σ) (hτ : BddSupp τ) : var₂ (σ ∗ τ) = var₂ σ + var₂ τ :=
  var₂_conv_of_memLp (hσ.memLp_snd 2) (hτ.memLp_snd 2)

/-- `Var(π₁ (θ_0 ∗ ⋯ ∗ θ_{k-1})) = ∑ Var(π₁ θ_i)` for bounded probability measures (Lemma 3.2,
lines 867 to 1017, and Proposition 1.7 of the source). -/
theorem var₁_convk : ∀ {k : ℕ} {θ : Fin k → Measure (ℝ × ℝ)} [∀ i, IsProbabilityMeasure (θ i)],
    (∀ i, BddSupp (θ i)) → var₁ (convk k θ) = ∑ i, var₁ (θ i)
  | 0, θ, _, _ => by
    rw [convk_zero, var₁, variance_dirac, Finset.univ_eq_empty, Finset.sum_empty]
  | k + 1, θ, _, h => by
    have : ∀ i, IsProbabilityMeasure (Fin.tail θ i) := fun i =>
      inferInstanceAs (IsProbabilityMeasure (θ i.succ))
    have ht : ∀ i, BddSupp (Fin.tail θ i) := fun i => h i.succ
    rw [convk_succ, var₁_conv (h 0) (BddSupp.convk ht), var₁_convk ht, Fin.sum_univ_succ]
    rfl

/-- `Var(π₂ (θ_0 ∗ ⋯ ∗ θ_{k-1})) = ∑ Var(π₂ θ_i)` for bounded probability measures. -/
theorem var₂_convk : ∀ {k : ℕ} {θ : Fin k → Measure (ℝ × ℝ)} [∀ i, IsProbabilityMeasure (θ i)],
    (∀ i, BddSupp (θ i)) → var₂ (convk k θ) = ∑ i, var₂ (θ i)
  | 0, θ, _, _ => by
    rw [convk_zero, var₂, variance_dirac, Finset.univ_eq_empty, Finset.sum_empty]
  | k + 1, θ, _, h => by
    have : ∀ i, IsProbabilityMeasure (Fin.tail θ i) := fun i =>
      inferInstanceAs (IsProbabilityMeasure (θ i.succ))
    have ht : ∀ i, BddSupp (Fin.tail θ i) := fun i => h i.succ
    rw [convk_succ, var₂_conv (h 0) (BddSupp.convk ht), var₂_convk ht, Fin.sum_univ_succ]
    rfl

omit [IsProbabilityMeasure σ] [IsProbabilityMeasure τ] in
/-- `Var(π₁ θ^{∗k}) = k Var(π₁ θ)` for a bounded probability measure. -/
theorem var₁_convPow [IsProbabilityMeasure θ] (h : BddSupp θ) (k : ℕ) :
    var₁ (convPow θ k) = k * var₁ θ := by
  rw [convPow, var₁_convk fun _ => h, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

omit [IsProbabilityMeasure σ] [IsProbabilityMeasure τ] in
/-- `Var(π₂ θ^{∗k}) = k Var(π₂ θ)` for a bounded probability measure. -/
theorem var₂_convPow [IsProbabilityMeasure θ] (h : BddSupp θ) (k : ℕ) :
    var₂ (convPow θ k) = k * var₂ θ := by
  rw [convPow, var₂_convk fun _ => h, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

end Variance

/-! ### Convolutions of finite families: reordering and splitting -/

section ConvFam

/-- The convolution `∗_{i ∈ ι} θ_i` of a finite family of planar measures: the law of the sum of
independent variables with the laws `θ_i`. For `ι = Fin k` and probability measures it is
`convk k θ` (`convk_eq_convFam`); it serves to reorder and split the factors, as in the proof of
Proposition 1.7 (lines 1075 to 1188 of the source), where the components of large variance are
convolved first and the remaining ones enter by convolution. -/
noncomputable def convFam {ι : Type*} [Fintype ι] (θ : ι → Measure (ℝ × ℝ)) : Measure (ℝ × ℝ) :=
  (Measure.pi θ).map fun x => ∑ i, x i

variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- The sum of the coordinates is measurable. -/
private theorem measurable_sum_pi : Measurable fun x : ι → ℝ × ℝ => ∑ i, x i :=
  Finset.measurable_sum _ fun i _ => measurable_pi_apply i

/-- The convolution of a finite family of probability measures is a probability measure. -/
instance isProbabilityMeasure_convFam (θ : ι → Measure (ℝ × ℝ))
    [∀ i, IsProbabilityMeasure (θ i)] : IsProbabilityMeasure (convFam θ) := by
  unfold convFam
  infer_instance

/-- The convolution of a finite family does not depend on the order of the factors. -/
theorem convFam_comp_equiv (θ : ι → Measure (ℝ × ℝ)) [∀ i, SigmaFinite (θ i)] (e : ι' ≃ ι) :
    convFam (fun i' => θ (e i')) = convFam θ := by
  unfold convFam
  rw [← (measurePreserving_piCongrLeft θ e).map_eq,
    Measure.map_map measurable_sum_pi (MeasurableEquiv.measurable _)]
  congr 1
  funext y
  rw [Function.comp_apply, ← e.sum_comp]
  exact Finset.sum_congr rfl fun i' _ =>
    (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ × ℝ) e y i').symm

/-- Splitting a finite family along a predicate: `∗_i θ_i = (∗_{p i} θ_i) ∗ (∗_{¬ p i} θ_i)`. -/
theorem convFam_split (θ : ι → Measure (ℝ × ℝ)) [∀ i, IsProbabilityMeasure (θ i)]
    (p : ι → Prop) [DecidablePred p] :
    convFam θ = convFam (fun i : {i // p i} => θ i) ∗ convFam (fun i : {i // ¬ p i} => θ i) := by
  unfold convFam
  rw [Measure.conv, Measure.map_prod_map _ _ measurable_sum_pi measurable_sum_pi,
    ← (measurePreserving_piEquivPiSubtypeProd θ p).map_eq,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _)]
  congr 1
  funext x
  simp [Fintype.sum_subtype_add_sum_subtype]

/-- `θ_0 ∗ ⋯ ∗ θ_{k-1}` is the convolution of the family `θ` (probability measures). -/
theorem convk_eq_convFam : ∀ (k : ℕ) (θ : Fin k → Measure (ℝ × ℝ))
    [∀ i, IsProbabilityMeasure (θ i)], convk k θ = convFam θ
  | 0, θ, _ => by
    rw [convk_zero, convFam, Measure.pi_of_empty, Measure.map_dirac' measurable_sum_pi]
    simp
  | k + 1, θ, _ => by
    have : ∀ i, IsProbabilityMeasure (Fin.tail θ i) := fun i =>
      inferInstanceAs (IsProbabilityMeasure (θ i.succ))
    rw [convk_succ, convk_eq_convFam k (Fin.tail θ)]
    unfold convFam
    have hS : (fun x : Fin (k + 1) → ℝ × ℝ => ∑ i, x i) =
        (fun q : (ℝ × ℝ) × (Fin k → ℝ × ℝ) => q.1 + ∑ j, q.2 j) ∘
          MeasurableEquiv.piFinSuccAbove (fun _ => ℝ × ℝ) 0 := by
      funext x
      simp [Fin.sum_univ_succ, Fin.tail]
    rw [hS, ← Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _),
      (measurePreserving_piFinSuccAbove θ 0).map_eq, Measure.conv,
      ← Measure.map_id (μ := θ 0), Measure.map_prod_map _ _ measurable_id measurable_sum_pi,
      Measure.map_map (by fun_prop) (by fun_prop), Measure.map_id]
    congr 1

/-- The convolution of a finite family indexed by `ι` is `convk` of the family enumerated by
`Fintype.equivFin ι`. -/
theorem convFam_eq_convk (θ : ι → Measure (ℝ × ℝ)) [∀ i, IsProbabilityMeasure (θ i)] :
    convFam θ = convk (Fintype.card ι) (fun i => θ ((Fintype.equivFin ι).symm i)) := by
  rw [convk_eq_convFam, convFam_comp_equiv]

/-- `convk` does not depend on the order of the factors. -/
theorem convk_comp_equiv {k : ℕ} (θ : Fin k → Measure (ℝ × ℝ)) [∀ i, IsProbabilityMeasure (θ i)]
    (e : Fin k ≃ Fin k) : convk k (fun i => θ (e i)) = convk k θ := by
  rw [convk_eq_convFam, convk_eq_convFam, convFam_comp_equiv]

/-- Splitting `θ_0 ∗ ⋯ ∗ θ_{k-1}` along a predicate on the indices. -/
theorem convk_split {k : ℕ} (θ : Fin k → Measure (ℝ × ℝ)) [∀ i, IsProbabilityMeasure (θ i)]
    (p : Fin k → Prop) [DecidablePred p] :
    convk k θ = convFam (fun i : {i // p i} => θ i) ∗ convFam (fun i : {i // ¬ p i} => θ i) := by
  rw [convk_eq_convFam, convFam_split θ p]

/-- The convolution of a finite family of bounded probability measures has bounded support. -/
theorem BddSupp.convFam {θ : ι → Measure (ℝ × ℝ)} [∀ i, IsProbabilityMeasure (θ i)]
    (h : ∀ i, BddSupp (θ i)) : BddSupp (convFam θ) := by
  rw [convFam_eq_convk]
  exact BddSupp.convk fun i => h _

/-- Variances of the first coordinate add over a finite family of bounded probability
measures. -/
theorem var₁_convFam {θ : ι → Measure (ℝ × ℝ)} [∀ i, IsProbabilityMeasure (θ i)]
    (h : ∀ i, BddSupp (θ i)) : var₁ (convFam θ) = ∑ i, var₁ (θ i) := by
  rw [convFam_eq_convk, var₁_convk fun i => h _]
  exact (Fintype.equivFin ι).symm.sum_comp fun i => var₁ (θ i)

/-- Variances of the second coordinate add over a finite family of bounded probability
measures. -/
theorem var₂_convFam {θ : ι → Measure (ℝ × ℝ)} [∀ i, IsProbabilityMeasure (θ i)]
    (h : ∀ i, BddSupp (θ i)) : var₂ (convFam θ) = ∑ i, var₂ (θ i) := by
  rw [convFam_eq_convk, var₂_convk fun i => h _]
  exact (Fintype.equivFin ι).symm.sum_comp fun i => var₂ (θ i)

/-- A diagonal map commutes with iterated convolution: `A (θ_0 ∗ ⋯ ∗ θ_{k-1}) =
A θ_0 ∗ ⋯ ∗ A θ_{k-1}` for `A = diag(s, t)` (Rapaport's rescalings `A_χ^i`). -/
theorem map_diagMap_convk (s t : ℝ) : ∀ (k : ℕ) (θ : Fin k → Measure (ℝ × ℝ))
    [∀ i, SFinite (θ i)],
    (convk k θ).map (diagMap s t) = convk k (fun i => (θ i).map (diagMap s t))
  | 0, θ, _ => by
    rw [convk_zero, convk_zero, Measure.map_dirac' (measurable_diagMap s t)]
    congr 1
    ext <;> simp
  | k + 1, θ, _ => by
    have : ∀ i, SFinite (Fin.tail θ i) := fun i => inferInstanceAs (SFinite (θ i.succ))
    rw [convk_succ, convk_succ, map_diagMap_conv, map_diagMap_convk s t k (Fin.tail θ)]
    rfl

/-- A diagonal map commutes with the convolution of a finite family of probability measures. -/
theorem map_diagMap_convFam (s t : ℝ) (θ : ι → Measure (ℝ × ℝ))
    [∀ i, IsProbabilityMeasure (θ i)] :
    (convFam θ).map (diagMap s t) = convFam (fun i => (θ i).map (diagMap s t)) := by
  rw [convFam_eq_convk, map_diagMap_convk, convFam_eq_convk]

end ConvFam

/-! ### Mixtures: the decomposition over tuples of components -/

section Mixture

/-- A finite sum of s-finite measures is s-finite. -/
theorem sFinite_finset_sum {ι : Type*} (s : Finset ι) (μ : ι → Measure (ℝ × ℝ))
    [∀ i, SFinite (μ i)] : SFinite (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    infer_instance
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    infer_instance

/-- Convolution distributes over finite sums in the first factor. -/
theorem finset_sum_conv {ι : Type*} (s : Finset ι) (μ : ι → Measure (ℝ × ℝ))
    [∀ i, SFinite (μ i)] (ν : Measure (ℝ × ℝ)) [SFinite ν] :
    (∑ i ∈ s, μ i) ∗ ν = ∑ i ∈ s, μ i ∗ ν := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have := sFinite_finset_sum s μ
    rw [Finset.sum_insert ha, Measure.add_conv, ih, Finset.sum_insert ha]

/-- Convolution distributes over finite sums in the second factor. -/
theorem conv_finset_sum {ι : Type*} (s : Finset ι) (μ : Measure (ℝ × ℝ)) [SFinite μ]
    (ν : ι → Measure (ℝ × ℝ)) [∀ i, SFinite (ν i)] :
    μ ∗ (∑ i ∈ s, ν i) = ∑ i ∈ s, μ ∗ ν i := by
  have := sFinite_finset_sum s ν
  rw [Measure.conv_comm, finset_sum_conv]
  exact Finset.sum_congr rfl fun i _ => Measure.conv_comm _ _

/-- The convolution of `k` finite mixtures `θ_i = ∑_b a_{i,b} ρ_{i,b}` is the mixture over tuples
`t` of the convolutions `ρ_{0,t_0} ∗ ⋯ ∗ ρ_{k-1,t_{k-1}}` with the product weights (proof of
Proposition 1.7, lines 1075 to 1188 of the source). -/
theorem convk_sum {β : Type*} [Fintype β] : ∀ (k : ℕ) (a : Fin k → β → ℝ≥0∞)
    (ρ : Fin k → β → Measure (ℝ × ℝ)) [∀ i b, SFinite (ρ i b)],
    convk k (fun i => ∑ b, a i b • ρ i b) =
      ∑ t : Fin k → β, (∏ i, a i (t i)) • convk k (fun i => ρ i (t i))
  | 0, a, ρ, _ => by
    simp [convk_zero]
  | k + 1, a, ρ, _ => by
    have hs : ∀ (k : ℕ) (θ : Fin k → Measure (ℝ × ℝ)) [∀ i, SFinite (θ i)],
        SFinite (convk k θ) := fun k θ _ => sFinite_convk k θ
    have ih := convk_sum k (fun i => a i.succ) (fun i => ρ i.succ)
    have e : ∀ (b : β) (t : Fin k → β), (∏ i, a i ((Fin.cons b t : Fin (k + 1) → β) i)) •
        convk (k + 1) (fun i => ρ i ((Fin.cons b t : Fin (k + 1) → β) i)) =
        (a 0 b * ∏ i, a i.succ (t i)) • (ρ 0 b ∗ convk k (fun i => ρ i.succ (t i))) := by
      intro b t
      rw [Fin.prod_univ_succ, convk_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rfl
    rw [← (Fin.consEquiv fun _ => β).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply]
    simp_rw [e]
    rw [convk_succ]
    change (∑ b, a 0 b • ρ 0 b) ∗ convk k (fun i : Fin k => ∑ b, a i.succ b • ρ i.succ b) = _
    have : ∀ t : Fin k → β, SFinite (convk k fun i => ρ i.succ (t i)) := fun t => hs _ _
    have : ∀ b, SFinite (a 0 b • ρ 0 b) := fun b => inferInstance
    have : ∀ t : Fin k → β, SFinite ((∏ i, a i.succ (t i)) • convk k fun i => ρ i.succ (t i)) :=
      fun t => inferInstance
    have := sFinite_finset_sum Finset.univ fun t : Fin k → β =>
      (∏ i, a i.succ (t i)) • convk k fun i => ρ i.succ (t i)
    rw [ih, finset_sum_conv]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Measure.conv_smul_left, conv_finset_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Measure.conv_smul_right, smul_smul]

/-- `convk_sum` with real weights `w_{i,b} ≥ 0`, the form of the mixtures of Rapaport (2.4) in
`Rapaport/Entropy/Basic.lean`. -/
theorem convk_sum_ofReal {β : Type*} [Fintype β] {k : ℕ} (w : Fin k → β → ℝ)
    (hw : ∀ i b, 0 ≤ w i b) (ρ : Fin k → β → Measure (ℝ × ℝ)) [∀ i b, SFinite (ρ i b)] :
    convk k (fun i => ∑ b, ENNReal.ofReal (w i b) • ρ i b) =
      ∑ t : Fin k → β, ENNReal.ofReal (∏ i, w i (t i)) • convk k (fun i => ρ i (t i)) := by
  rw [convk_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [ENNReal.ofReal_prod_of_nonneg fun i _ => hw i (t i)]

/-- A component of a finite measure is a finite measure. -/
instance isFiniteMeasure_comp {X L : Type*} [MeasurableSpace X] (θ : Measure X) [IsFiniteMeasure θ]
    (f : X → L) (b : L) : IsFiniteMeasure (comp θ f b) := by
  unfold comp
  infer_instance

variable {L : Type*} [MeasurableSpace L] [MeasurableSingletonClass L] [Countable L]

/-- The decomposition of `θ^{∗k}` over the tuples of components of `θ` for a labelling `f` with
finitely many labels: `θ^{∗k} = ∑_t (∏_i θ(f = t_i)) θ_{f = t_0} ∗ ⋯ ∗ θ_{f = t_{k-1}}` (proof
of Proposition 1.7, lines 1075 to 1188 of the source, where `f` is `ℰ_b`). -/
theorem convPow_eq_sum_comp {θ : Measure (ℝ × ℝ)} [IsFiniteMeasure θ] {f : ℝ × ℝ → L}
    (hf : Measurable f) (hfin : FiniteLabels θ f) (k : ℕ) :
    convPow θ k = ∑ t : Fin k → hfin.toFinset,
      ENNReal.ofReal (∏ i, θ.real (f ⁻¹' {(t i : L)})) •
        convk k (fun i => comp θ f (t i : L)) := by
  have hθ : θ = ∑ b : hfin.toFinset, ENNReal.ofReal (θ.real (f ⁻¹' {(b : L)})) •
      comp θ f (b : L) := by
    conv_lhs => rw [eq_sum_comp hf hfin]
    rw [← Finset.sum_coe_sort hfin.toFinset]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [ofReal_measureReal]
  rw [convPow, convk_congr (θ' := fun _ => ∑ b : hfin.toFinset,
      ENNReal.ofReal (θ.real (f ⁻¹' {(b : L)})) • comp θ f (b : L)) fun _ => hθ]
  have hc : ∀ (_ : Fin k) (b : hfin.toFinset), SFinite (comp θ f (b : L)) := fun _ _ =>
    inferInstance
  exact @convk_sum_ofReal hfin.toFinset _ k (fun _ b => θ.real (f ⁻¹' {(b : L)}))
    (fun _ _ => measureReal_nonneg) (fun _ b => comp θ f (b : L)) hc

/-- The weights of the decomposition `convPow_eq_sum_comp` form a probability vector. -/
theorem sum_prod_measureReal_fiber {θ : Measure (ℝ × ℝ)} [IsProbabilityMeasure θ]
    {f : ℝ × ℝ → L} (hf : Measurable f) (hfin : FiniteLabels θ f) (k : ℕ) :
    ∑ t : Fin k → hfin.toFinset, ∏ i, θ.real (f ⁻¹' {(t i : L)}) = 1 := by
  rw [← Fintype.sum_pow (fun b : hfin.toFinset => θ.real (f ⁻¹' {(b : L)})),
    Finset.sum_coe_sort hfin.toFinset (fun b => θ.real (f ⁻¹' {b})),
    sum_measureReal_fiber hf _ fun _ hb => hfin.mem_toFinset.2 hb, one_pow]

end Mixture

/-! ### Lower bounds for `σ ∗ τ` through mixtures of translates -/

section LowerBound

variable {σ τ : Measure (ℝ × ℝ)} [IsProbabilityMeasure σ] [IsProbabilityMeasure τ]
variable {L L' : Type*} [MeasurableSpace L] [MeasurableSingletonClass L] [Countable L]
variable [MeasurableSpace L'] [MeasurableSingletonClass L'] [Countable L']

omit [IsProbabilityMeasure σ] [IsProbabilityMeasure τ] in
/-- The translates `σ.map (· + y)` for `y` in a ball carrying `τ` lie in a common ball. -/
private theorem ae_inBall_map_add_const {c c' : ℝ × ℝ} {R R' : ℝ} (hσ : InBall σ c R)
    (hτ : InBall τ c' R') : ∀ᵐ y ∂τ, InBall (σ.map (· + y)) (c + c') (R + R') := by
  filter_upwards [hτ] with y hy
  refine ((hσ.map_add_const y).recentre (c + c')).mono ?_
  rw [add_sub_add_left_eq_sub]
  linarith

/-- If every translate `f ∘ (· + y)` meets at most `N` labels of `f` per fibre, then
`H(σ ∗ τ, f) ≥ H(σ, f) - log N` for bounded probability measures (Rapaport (2.4) for the mixture
`σ ∗ τ = ∫ σ.map (· + y) dτ(y)` with the translation count (2.5)). -/
theorem ent_conv_ge_of_fiberBound (hσ : BddSupp σ) (hτ : BddSupp τ) {f : ℝ × ℝ → L}
    (hf : Measurable f) (hfb : BallFinite f) {N : ℕ}
    (hN : ∀ y, FiberBound (f ∘ (· + y)) f N) : ent σ f - Real.log N ≤ ent (σ ∗ τ) f := by
  obtain ⟨c, R, hσc⟩ := hσ
  obtain ⟨c', R', hτc⟩ := hτ
  rw [conv_eq_bind_map_add_const]
  refine le_ent_bind_of_ae_le_of_inBall (measurable_map_add_const σ) (fun _ => inferInstance)
    (ae_inBall_map_add_const hσc hτc) hf hfb (ae_of_all _ fun y => ?_)
  have hy := measurable_add_const y
  rw [ent_map hy hf]
  have := ent_le_ent_add_log_of_fiber_card hf (hf.comp hy) (hfb.finiteLabels ⟨c, R, hσc⟩)
    ((hfb.comp_add_const y).finiteLabels ⟨c, R, hσc⟩) (hN y)
  linarith

/-- If the translates of `f` meet at most `N` labels of `f` per fibre and those of `g` are
`N'`-commensurable with `g`, then `H(σ ∗ τ, f ∣ g) ≥ H(σ, f ∣ g) - log N - 2 log N'` for bounded
probability measures (Rapaport (2.4) for `H(·, 𝒟 ∣ ℰ)` with (2.5); the step "the remaining
components enter by convolution" of the proof of Proposition 1.7). -/
theorem cent_conv_ge_of_fiberBound (hσ : BddSupp σ) (hτ : BddSupp τ) {f : ℝ × ℝ → L}
    {g : ℝ × ℝ → L'} (hf : Measurable f) (hg : Measurable g) (hfb : BallFinite f)
    (hgb : BallFinite g) {N N' : ℕ} (hN : ∀ y, FiberBound (f ∘ (· + y)) f N)
    (hN₁ : ∀ y, FiberBound (g ∘ (· + y)) g N') (hN₂ : ∀ y, FiberBound g (g ∘ (· + y)) N') :
    cent σ f g - (Real.log N + 2 * Real.log N') ≤ cent (σ ∗ τ) f g := by
  obtain ⟨c, R, hσc⟩ := hσ
  obtain ⟨c', R', hτc⟩ := hτ
  rw [conv_eq_bind_map_add_const]
  refine le_cent_bind_of_ae_le_of_inBall (measurable_map_add_const σ) (fun _ => inferInstance)
    (ae_inBall_map_add_const hσc hτc) hf hg hfb hgb (ae_of_all _ fun y => ?_)
  have hy := measurable_add_const y
  have hσ' : BddSupp σ := ⟨c, R, hσc⟩
  rw [cent_map hy hf hg]
  have h1 := cent_le_cent_add_two_log_of_commensurable_cond hf hg (hg.comp hy)
    (hfb.finiteLabels hσ') (hgb.finiteLabels hσ') ((hgb.comp_add_const y).finiteLabels hσ')
    (hN₁ y) (hN₂ y)
  have h2 := cent_le_cent_add_log_of_fiber_card hf (hf.comp hy) (hg.comp hy)
    (hfb.finiteLabels hσ') ((hfb.comp_add_const y).finiteLabels hσ')
    ((hgb.comp_add_const y).finiteLabels hσ')
    ((hN y).of_refine_left (φ := Prod.fst) (f := fun x => ((f ∘ (· + y)) x, (g ∘ (· + y)) x))
      rfl)
  linarith

/-- `H(σ ∗ τ, 𝒟_{i,j}) ≥ H(σ, 𝒟_{i,j}) - log 4` for bounded probability measures (Rapaport (2.4)
and (2.5), proof of Proposition 1.7). -/
theorem ent_conv_ge_sub_log_four (hσ : BddSupp σ) (hτ : BddSupp τ) (i j : ℤ) :
    ent σ (rect i j) - Real.log 4 ≤ ent (σ ∗ τ) (rect i j) := by
  have h := ent_conv_ge_of_fiberBound hσ hτ (measurable_rect i j) (ballFinite_rect i j)
    (N := 4) fun y => fiberBound_rect_translate i j y
  exact_mod_cast h

/-- `H(σ ∗ τ, 𝒟_{i,j}) ≥ H(τ, 𝒟_{i,j}) - log 4` for bounded probability measures. -/
theorem ent_conv_ge_sub_log_four' (hσ : BddSupp σ) (hτ : BddSupp τ) (i j : ℤ) :
    ent τ (rect i j) - Real.log 4 ≤ ent (σ ∗ τ) (rect i j) := by
  rw [Measure.conv_comm]
  exact ent_conv_ge_sub_log_four hτ hσ i j

/-- `H(σ ∗ τ, π₁⁻¹ 𝒟_i) ≥ H(σ, π₁⁻¹ 𝒟_i) - log 2` for bounded probability measures. -/
theorem ent_conv_ge_hLabel (hσ : BddSupp σ) (hτ : BddSupp τ) (i : ℤ) :
    ent σ (hLabel i) - Real.log 2 ≤ ent (σ ∗ τ) (hLabel i) := by
  have h := ent_conv_ge_of_fiberBound hσ hτ (measurable_hLabel i) (ballFinite_hLabel i)
    (N := 2) fun y => fiberBound_hLabel_translate i y
  exact_mod_cast h

/-- `H(σ ∗ τ, π₂⁻¹ 𝒟_j) ≥ H(σ, π₂⁻¹ 𝒟_j) - log 2` for bounded probability measures. -/
theorem ent_conv_ge_vLabel (hσ : BddSupp σ) (hτ : BddSupp τ) (j : ℤ) :
    ent σ (vLabel j) - Real.log 2 ≤ ent (σ ∗ τ) (vLabel j) := by
  have h := ent_conv_ge_of_fiberBound hσ hτ (measurable_vLabel j) (ballFinite_vLabel j)
    (N := 2) fun y => fiberBound_vLabel_translate j y
  exact_mod_cast h

/-- `H(σ ∗ τ, ℰ_{n+m} ∣ ℰ_n) ≥ H(σ, ℰ_{n+m} ∣ ℰ_n) - 3 log 4` for bounded probability measures
(proof of Proposition 1.7). -/
theorem Exps.cent_conv_E_ge (χ : Exps) (hσ : BddSupp σ) (hτ : BddSupp τ) (n m : ℤ) :
    cent σ (χ.E (n + m)) (χ.E n) - 3 * Real.log 4 ≤ cent (σ ∗ τ) (χ.E (n + m)) (χ.E n) := by
  have h := cent_conv_ge_of_fiberBound hσ hτ (f := χ.E (n + m)) (g := χ.E n)
    (χ.measurable_E _) (χ.measurable_E _) (χ.ballFinite_E _) (χ.ballFinite_E _) (N := 4) (N' := 4)
    (fun y => fiberBound_rect_translate _ _ y) (fun y => fiberBound_rect_translate _ _ y)
    (fun y => fiberBound_rect_translate_symm _ _ y)
  norm_num at h
  linarith

/-- `H(σ ∗ τ, ℰ_{n+m} ∣ ℰ_n ∨ π₂⁻¹ ℰ_{n+m}) ≥ H(σ, ℰ_{n+m} ∣ ℰ_n ∨ π₂⁻¹ ℰ_{n+m}) - log 4 -
2 log 8` for bounded probability measures (the sets `Q_1` of Proposition 1.7). -/
theorem Exps.cent_conv_E_E₂_ge (χ : Exps) (hσ : BddSupp σ) (hτ : BddSupp τ) (n m : ℤ) :
    cent σ (χ.E (n + m)) (fun z => (χ.E n z, χ.E₂ (n + m) z)) -
        (Real.log 4 + 2 * Real.log 8) ≤
      cent (σ ∗ τ) (χ.E (n + m)) (fun z => (χ.E n z, χ.E₂ (n + m) z)) := by
  have h := cent_conv_ge_of_fiberBound hσ hτ (f := χ.E (n + m))
    (g := fun z => (χ.E n z, χ.E₂ (n + m) z)) (χ.measurable_E _)
    ((χ.measurable_E _).prodMk (χ.measurable_E₂ _)) (χ.ballFinite_E _)
    ((χ.ballFinite_E _).pair (χ.ballFinite_E₂ _)) (N := 4) (N' := 4 * 2)
    (fun y => fiberBound_rect_translate _ _ y)
    (fun y => (fiberBound_rect_translate _ _ y).prod (fiberBound_vLabel_translate _ y))
    (fun y => (fiberBound_rect_translate_symm _ _ y).prod (fiberBound_vLabel_translate_symm _ y))
  norm_num at h
  linarith

/-- `H(σ ∗ τ, ℰ_{n+m} ∣ ℰ_n ∨ π₁⁻¹ ℰ_{n+m}) ≥ H(σ, ℰ_{n+m} ∣ ℰ_n ∨ π₁⁻¹ ℰ_{n+m}) - log 4 -
2 log 8` for bounded probability measures (the sets `Q_2` of Proposition 1.7). -/
theorem Exps.cent_conv_E_E₁_ge (χ : Exps) (hσ : BddSupp σ) (hτ : BddSupp τ) (n m : ℤ) :
    cent σ (χ.E (n + m)) (fun z => (χ.E n z, χ.E₁ (n + m) z)) -
        (Real.log 4 + 2 * Real.log 8) ≤
      cent (σ ∗ τ) (χ.E (n + m)) (fun z => (χ.E n z, χ.E₁ (n + m) z)) := by
  have h := cent_conv_ge_of_fiberBound hσ hτ (f := χ.E (n + m))
    (g := fun z => (χ.E n z, χ.E₁ (n + m) z)) (χ.measurable_E _)
    ((χ.measurable_E _).prodMk (χ.measurable_E₁ _)) (χ.ballFinite_E _)
    ((χ.ballFinite_E _).pair (χ.ballFinite_E₁ _)) (N := 4) (N' := 4 * 2)
    (fun y => fiberBound_rect_translate _ _ y)
    (fun y => (fiberBound_rect_translate _ _ y).prod (fiberBound_hLabel_translate _ y))
    (fun y => (fiberBound_rect_translate_symm _ _ y).prod (fiberBound_hLabel_translate_symm _ y))
  norm_num at h
  linarith

/-- `H(σ ∗ τ, π₁⁻¹ ℰ_{n+m} ∣ ℰ_n) ≥ H(σ, π₁⁻¹ ℰ_{n+m} ∣ ℰ_n) - log 2 - 2 log 4` for bounded
probability measures. -/
theorem Exps.cent_conv_E₁_ge (χ : Exps) (hσ : BddSupp σ) (hτ : BddSupp τ) (n m : ℤ) :
    cent σ (χ.E₁ (n + m)) (χ.E n) - (Real.log 2 + 2 * Real.log 4) ≤
      cent (σ ∗ τ) (χ.E₁ (n + m)) (χ.E n) := by
  have h := cent_conv_ge_of_fiberBound hσ hτ (f := χ.E₁ (n + m)) (g := χ.E n)
    (χ.measurable_E₁ _) (χ.measurable_E _)
    (χ.ballFinite_E₁ _) (χ.ballFinite_E _) (N := 2) (N' := 4)
    (fun y => fiberBound_hLabel_translate _ y) (fun y => fiberBound_rect_translate _ _ y)
    (fun y => fiberBound_rect_translate_symm _ _ y)
  exact_mod_cast h

end LowerBound

/-! ### Convolution with a small measure: the product space -/

section Small

/-- The sum `x + w` where `w` lies in `K`, and `x` otherwise: a version of the addition map of
`σ ⊗ τ` that agrees with it almost everywhere when `τ` is carried by `K`, and moves no point by a
vector outside `K ∪ {0}` (the perturbation count (2.7) needs a pointwise bound). -/
noncomputable def shiftIn (K : Set (ℝ × ℝ)) (p : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ × ℝ :=
  p.1 + K.indicator id p.2

/-- `shiftIn K` is measurable for a measurable set `K`. -/
theorem measurable_shiftIn {K : Set (ℝ × ℝ)} (hK : MeasurableSet K) : Measurable (shiftIn K) :=
  measurable_fst.add ((measurable_id.indicator hK).comp measurable_snd)

/-- If `τ` is carried by `K`, then `σ ∗ τ` is the image of `σ ⊗ τ` under `shiftIn K`. -/
theorem conv_eq_map_shiftIn {σ τ : Measure (ℝ × ℝ)} [SFinite σ] [SFinite τ] {K : Set (ℝ × ℝ)}
    (hτK : ∀ᵐ w ∂τ, w ∈ K) : σ ∗ τ = (σ.prod τ).map (shiftIn K) := by
  rw [Measure.conv]
  refine Measure.map_congr ?_
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hτK] with p hp
  rw [shiftIn, Set.indicator_of_mem hp, id]

/-- The coordinate displacement of `shiftIn K` is bounded by any bound valid on `K`. -/
private theorem abs_shiftIn_fst_sub_le {K : Set (ℝ × ℝ)} {a : ℝ} (ha : 0 ≤ a)
    (hK : ∀ w ∈ K, |w.1| ≤ a) (p : (ℝ × ℝ) × (ℝ × ℝ)) : |(shiftIn K p).1 - p.1.1| ≤ a := by
  rw [shiftIn, Prod.fst_add, add_sub_cancel_left]
  by_cases hw : p.2 ∈ K
  · rw [Set.indicator_of_mem hw]
    exact hK _ hw
  · rw [Set.indicator_of_notMem hw]
    simpa using ha

/-- The vertical displacement of `shiftIn K` is bounded by any bound valid on `K`. -/
private theorem abs_shiftIn_snd_sub_le {K : Set (ℝ × ℝ)} {b : ℝ} (hb : 0 ≤ b)
    (hK : ∀ w ∈ K, |w.2| ≤ b) (p : (ℝ × ℝ) × (ℝ × ℝ)) : |(shiftIn K p).2 - p.1.2| ≤ b := by
  rw [shiftIn, Prod.snd_add, add_sub_cancel_left]
  by_cases hw : p.2 ∈ K
  · rw [Set.indicator_of_mem hw]
    exact hK _ hw
  · rw [Set.indicator_of_notMem hw]
    simpa using hb

/-- The half-sides of a rectangle carrying a nonzero measure are nonnegative. -/
private theorem InRect.nonneg {θ : Measure (ℝ × ℝ)} [IsProbabilityMeasure θ] {c : ℝ × ℝ}
    {R₁ R₂ : ℝ} (h : InRect θ c R₁ R₂) : 0 ≤ R₁ ∧ 0 ≤ R₂ := by
  obtain ⟨z, hz⟩ := h.exists
  exact ⟨(abs_nonneg _).trans hz.1, (abs_nonneg _).trans hz.2⟩

/-- The rectangle `[-a, a] × [-b, b]`. -/
private theorem measurableSet_rectSet (a b : ℝ) :
    MeasurableSet {w : ℝ × ℝ | |w.1| ≤ a ∧ |w.2| ≤ b} := by
  rw [Set.ofPred_and]
  exact (measurableSet_le (f := fun w : ℝ × ℝ => |w.1|) (by fun_prop) measurable_const).inter
    (measurableSet_le (f := fun w : ℝ × ℝ => |w.2|) (by fun_prop) measurable_const)

variable {X : Type*} [MeasurableSpace X]
variable {L L' : Type*} [MeasurableSpace L] [MeasurableSingletonClass L] [Countable L]
variable [MeasurableSpace L'] [MeasurableSingletonClass L'] [Countable L']

/-- Two pairs of mutually commensurable labellings have conditional entropies within
`log N + 2 log N'` (Rapaport, lines 724 to 735, with (2.3)). -/
theorem abs_cent_sub_cent_le_of_fiberBound {θ : Measure X} [IsProbabilityMeasure θ]
    {f₁ f₂ : X → L} {g₁ g₂ : X → L'} (hf₁ : Measurable f₁) (hf₂ : Measurable f₂)
    (hg₁ : Measurable g₁) (hg₂ : Measurable g₂) (hfin₁ : FiniteLabels θ f₁)
    (hfin₂ : FiniteLabels θ f₂) (hgin₁ : FiniteLabels θ g₁) (hgin₂ : FiniteLabels θ g₂)
    {N N' : ℕ} (hf : FiberBound f₁ f₂ N) (hf' : FiberBound f₂ f₁ N) (hg : FiberBound g₁ g₂ N')
    (hg' : FiberBound g₂ g₁ N') :
    |cent θ f₁ g₁ - cent θ f₂ g₂| ≤ Real.log N + 2 * Real.log N' := by
  have a1 := cent_le_cent_add_two_log_of_commensurable_cond hf₁ hg₁ hg₂ hfin₁ hgin₁ hgin₂ hg' hg
  have a2 := cent_le_cent_add_log_of_fiber_card hf₁ hf₂ hg₂ hfin₁ hfin₂ hgin₂
    (hf'.of_refine_left (φ := Prod.fst) (f := fun x => (f₂ x, g₂ x)) rfl)
  have b1 := cent_le_cent_add_two_log_of_commensurable_cond hf₂ hg₂ hg₁ hfin₂ hgin₂ hgin₁ hg hg'
  have b2 := cent_le_cent_add_log_of_fiber_card hf₂ hf₁ hg₁ hfin₂ hfin₁ hgin₁
    (hf.of_refine_left (φ := Prod.fst) (f := fun x => (f₁ x, g₁ x)) rfl)
  rw [abs_sub_le_iff]
  constructor <;> linarith

variable {σ τ : Measure (ℝ × ℝ)} [IsProbabilityMeasure σ] [IsProbabilityMeasure τ]

omit [MeasurableSpace L'] [MeasurableSingletonClass L'] [Countable L'] in
omit [Countable L] in
/-- Entropy of `σ ∗ τ` on the product space, when `τ` is carried by `K`. -/
private theorem ent_conv_eq_prod {K : Set (ℝ × ℝ)} (hK : MeasurableSet K) (hτK : ∀ᵐ w ∂τ, w ∈ K)
    {f : ℝ × ℝ → L} (hf : Measurable f) :
    ent (σ ∗ τ) f = ent (σ.prod τ) (f ∘ shiftIn K) := by
  rw [conv_eq_map_shiftIn hτK, ent_map (measurable_shiftIn hK) hf]

omit [MeasurableSpace L'] [MeasurableSingletonClass L'] [Countable L'] in
omit [Countable L] [IsProbabilityMeasure σ] in
/-- Entropy of `σ` on the product space. -/
private theorem ent_eq_prod {f : ℝ × ℝ → L} (hf : Measurable f) :
    ent σ f = ent (σ.prod τ) (f ∘ Prod.fst) := by
  have h : (σ.prod τ).map Prod.fst = σ := by rw [Measure.map_fst_prod, measure_univ, one_smul]
  rw [← ent_map measurable_fst hf, h]

omit [Countable L] [Countable L'] in
/-- Conditional entropy of `σ ∗ τ` on the product space, when `τ` is carried by `K`. -/
private theorem cent_conv_eq_prod {K : Set (ℝ × ℝ)} (hK : MeasurableSet K)
    (hτK : ∀ᵐ w ∂τ, w ∈ K) {f : ℝ × ℝ → L} {g : ℝ × ℝ → L'} (hf : Measurable f)
    (hg : Measurable g) : cent (σ ∗ τ) f g = cent (σ.prod τ) (f ∘ shiftIn K) (g ∘ shiftIn K) := by
  rw [conv_eq_map_shiftIn hτK, cent_map (measurable_shiftIn hK) hf hg]

omit [Countable L] [Countable L'] [IsProbabilityMeasure σ] in
/-- Conditional entropy of `σ` on the product space. -/
private theorem cent_eq_prod {f : ℝ × ℝ → L} {g : ℝ × ℝ → L'} (hf : Measurable f)
    (hg : Measurable g) : cent σ f g = cent (σ.prod τ) (f ∘ Prod.fst) (g ∘ Prod.fst) := by
  have h : (σ.prod τ).map Prod.fst = σ := by rw [Measure.map_fst_prod, measure_univ, one_smul]
  rw [← cent_map measurable_fst hf hg, h]

omit [Countable L] [IsProbabilityMeasure σ] [IsProbabilityMeasure τ] in
/-- Labels finite on balls have finite labels on the product space through `shiftIn K`. -/
private theorem finiteLabels_prod_shiftIn [SFinite σ] [SFinite τ] (hσ : BddSupp σ)
    (hτ : BddSupp τ) {K : Set (ℝ × ℝ)} (hK : MeasurableSet K) (hτK : ∀ᵐ w ∂τ, w ∈ K)
    {f : ℝ × ℝ → L} (hf : Measurable f) (hfb : BallFinite f) :
    FiniteLabels (σ.prod τ) (f ∘ shiftIn K) := by
  refine (finiteLabels_map_iff (measurable_shiftIn hK) hf).1 ?_
  rw [← conv_eq_map_shiftIn hτK]
  exact hfb.finiteLabels (hσ.conv hτ)

omit [Countable L] [IsProbabilityMeasure σ] in
/-- Labels finite on balls have finite labels on the product space through `Prod.fst`. -/
private theorem finiteLabels_prod_fst (hσ : BddSupp σ) {f : ℝ × ℝ → L} (hf : Measurable f)
    (hfb : BallFinite f) : FiniteLabels (σ.prod τ) (f ∘ Prod.fst) := by
  refine (finiteLabels_map_iff measurable_fst hf).1 ?_
  rw [Measure.map_fst_prod, measure_univ, one_smul]
  exact hfb.finiteLabels hσ

/-- The upper half of the two-sided bound for a small `τ`, in general form: if `τ` is carried by
a measurable set `K` and every fibre of `f ∘ Prod.fst` meets at most `N` labels of
`f ∘ shiftIn K` (no point `x` is moved by a vector of `K` across more than `N` labels), then
`H(σ ∗ τ, f) ≤ H(σ, f) + log N` (Rapaport (2.7), lines 737 to 775). -/
theorem ent_conv_le_ent_add_log_of_fiberBound (hσ : BddSupp σ) (hτ : BddSupp τ)
    {K : Set (ℝ × ℝ)} (hK : MeasurableSet K) (hτK : ∀ᵐ w ∂τ, w ∈ K) {f : ℝ × ℝ → L}
    (hf : Measurable f) (hfb : BallFinite f) {N : ℕ}
    (hN : FiberBound (f ∘ Prod.fst) (f ∘ shiftIn K) N) :
    ent (σ ∗ τ) f ≤ ent σ f + Real.log N := by
  rw [ent_conv_eq_prod hK hτK hf, ent_eq_prod (τ := τ) hf]
  exact ent_le_ent_add_log_of_fiber_card (hf.comp (measurable_shiftIn hK))
    (hf.comp measurable_fst) (finiteLabels_prod_shiftIn hσ hτ hK hτK hf hfb)
    (finiteLabels_prod_fst hσ hf hfb) hN

/-- The lower half of the two-sided bound for a small `τ`, in general form:
`H(σ, f) ≤ H(σ ∗ τ, f) + log N` when every fibre of `f ∘ shiftIn K` meets at most `N` labels of
`f ∘ Prod.fst` (Rapaport (2.7), lines 737 to 775). -/
theorem ent_le_ent_conv_add_log_of_fiberBound (hσ : BddSupp σ) (hτ : BddSupp τ)
    {K : Set (ℝ × ℝ)} (hK : MeasurableSet K) (hτK : ∀ᵐ w ∂τ, w ∈ K) {f : ℝ × ℝ → L}
    (hf : Measurable f) (hfb : BallFinite f) {N : ℕ}
    (hN : FiberBound (f ∘ shiftIn K) (f ∘ Prod.fst) N) :
    ent σ f ≤ ent (σ ∗ τ) f + Real.log N := by
  rw [ent_conv_eq_prod hK hτK hf, ent_eq_prod (τ := τ) hf]
  exact ent_le_ent_add_log_of_fiber_card (hf.comp measurable_fst)
    (hf.comp (measurable_shiftIn hK)) (finiteLabels_prod_fst hσ hf hfb)
    (finiteLabels_prod_shiftIn hσ hτ hK hτK hf hfb) hN

/-- The two-sided bound for a small `τ`: if `τ` is carried by the rectangle
`[-C₁ 2^{-i}, C₁ 2^{-i}] × [-C₂ 2^{-j}, C₂ 2^{-j}]`, then
`|H(σ ∗ τ, 𝒟_{i,j}) - H(σ, 𝒟_{i,j})| ≤ log ((2 ⌈C₁⌉ + 3)(2 ⌈C₂⌉ + 3))`: the product space
`σ ⊗ τ` with the labellings `rect ∘ (+)` and `rect ∘ Prod.fst` and the perturbation count (2.7)
(lines 737 to 775), with no mixture. -/
theorem abs_ent_conv_sub_ent_le_rect (hσ : BddSupp σ) {i j : ℤ} {C₁ C₂ : ℝ}
    (hτ : InRect τ 0 (C₁ * 2 ^ (-i)) (C₂ * 2 ^ (-j))) :
    |ent (σ ∗ τ) (rect i j) - ent σ (rect i j)| ≤
      Real.log ((2 * ⌈C₁⌉₊ + 3) * (2 * ⌈C₂⌉₊ + 3) : ℕ) := by
  obtain ⟨ha, hb⟩ := InRect.nonneg hτ
  set K := {w : ℝ × ℝ | |w.1| ≤ C₁ * 2 ^ (-i) ∧ |w.2| ≤ C₂ * 2 ^ (-j)} with hKdef
  have hK : MeasurableSet K := measurableSet_rectSet _ _
  have hτK : ∀ᵐ w ∂τ, w ∈ K := by
    filter_upwards [hτ] with w hw
    simpa [hKdef] using hw
  have hτb : BddSupp τ := ⟨0, _, hτ.inBall⟩
  have h₁ := abs_shiftIn_fst_sub_le (K := K) ha fun w hw => hw.1
  have h₂ := abs_shiftIn_snd_sub_le (K := K) hb fun w hw => hw.2
  have hr := measurable_rect i j
  rw [ent_conv_eq_prod hK hτK hr, ent_eq_prod (τ := τ) hr]
  exact abs_ent_sub_ent_le_log_of_commensurable (hr.comp (measurable_shiftIn hK))
    (hr.comp measurable_fst) (finiteLabels_prod_shiftIn hσ hτb hK hτK hr (ballFinite_rect i j))
    (finiteLabels_prod_fst hσ hr (ballFinite_rect i j)) (fiberBound_rect_perturb_symm h₁ h₂)
    (fiberBound_rect_perturb h₁ h₂)

/-- The conditional two-sided bound for a small `τ`: if `τ` is carried by the rectangles of
half-sides `(C₁ 2^{-i}, C₂ 2^{-j})` and `(C₁' 2^{-i'}, C₂' 2^{-j'})`, then
`|H(σ ∗ τ, 𝒟_{i,j} ∣ 𝒟_{i',j'}) - H(σ, 𝒟_{i,j} ∣ 𝒟_{i',j'})| ≤ log N + 2 log N'` with the
perturbation counts `N`, `N'` of (2.7) at the two levels. -/
theorem abs_cent_conv_sub_cent_le_rect (hσ : BddSupp σ) {i j i' j' : ℤ} {C₁ C₂ C₁' C₂' : ℝ}
    (hτ : InRect τ 0 (C₁ * 2 ^ (-i)) (C₂ * 2 ^ (-j)))
    (hτ' : InRect τ 0 (C₁' * 2 ^ (-i')) (C₂' * 2 ^ (-j'))) :
    |cent (σ ∗ τ) (rect i j) (rect i' j') - cent σ (rect i j) (rect i' j')| ≤
      Real.log ((2 * ⌈C₁⌉₊ + 3) * (2 * ⌈C₂⌉₊ + 3) : ℕ) +
        2 * Real.log ((2 * ⌈C₁'⌉₊ + 3) * (2 * ⌈C₂'⌉₊ + 3) : ℕ) := by
  obtain ⟨ha, hb⟩ := InRect.nonneg hτ
  obtain ⟨ha', hb'⟩ := InRect.nonneg hτ'
  set K := {w : ℝ × ℝ | |w.1| ≤ C₁ * 2 ^ (-i) ∧ |w.2| ≤ C₂ * 2 ^ (-j)} ∩
    {w : ℝ × ℝ | |w.1| ≤ C₁' * 2 ^ (-i') ∧ |w.2| ≤ C₂' * 2 ^ (-j')} with hKdef
  have hK : MeasurableSet K := (measurableSet_rectSet _ _).inter (measurableSet_rectSet _ _)
  have hτK : ∀ᵐ w ∂τ, w ∈ K := by
    filter_upwards [hτ, hτ'] with w hw hw'
    simp only [Prod.fst_zero, Prod.snd_zero, sub_zero] at hw hw'
    exact ⟨hw, hw'⟩
  have hτb : BddSupp τ := ⟨0, _, hτ.inBall⟩
  have h₁ := abs_shiftIn_fst_sub_le (K := K) ha fun w hw => hw.1.1
  have h₂ := abs_shiftIn_snd_sub_le (K := K) hb fun w hw => hw.1.2
  have h₁' := abs_shiftIn_fst_sub_le (K := K) ha' fun w hw => hw.2.1
  have h₂' := abs_shiftIn_snd_sub_le (K := K) hb' fun w hw => hw.2.2
  have hr := measurable_rect i j
  have hr' := measurable_rect i' j'
  rw [cent_conv_eq_prod hK hτK hr hr', cent_eq_prod (τ := τ) hr hr']
  exact abs_cent_sub_cent_le_of_fiberBound (hr.comp (measurable_shiftIn hK))
    (hr.comp measurable_fst) (hr'.comp (measurable_shiftIn hK)) (hr'.comp measurable_fst)
    (finiteLabels_prod_shiftIn hσ hτb hK hτK hr (ballFinite_rect i j))
    (finiteLabels_prod_fst hσ hr (ballFinite_rect i j))
    (finiteLabels_prod_shiftIn hσ hτb hK hτK hr' (ballFinite_rect i' j'))
    (finiteLabels_prod_fst hσ hr' (ballFinite_rect i' j')) (fiberBound_rect_perturb h₁ h₂)
    (fiberBound_rect_perturb_symm h₁ h₂) (fiberBound_rect_perturb h₁' h₂')
    (fiberBound_rect_perturb_symm h₁' h₂')

/-- The conditional two-sided bound for a small `τ` at the levels of `ℰ_{n+m}` given `ℰ_n`: if
`τ` is carried by the rectangle of half-sides `(C₁ 2^{-lvl χ₁ (n+m)}, C₂ 2^{-lvl χ₂ (n+m)})`
and `m ≥ 0`, then `|H(σ ∗ τ, ℰ_{n+m} ∣ ℰ_n) - H(σ, ℰ_{n+m} ∣ ℰ_n)| ≤ 3 log N` with
`N = (2 ⌈C₁⌉ + 3)(2 ⌈C₂⌉ + 3)`. -/
theorem Exps.abs_cent_conv_E_sub_le (χ : Exps) (hσ : BddSupp σ) {n m : ℤ} (hm : 0 ≤ m)
    {C₁ C₂ : ℝ} (hτ : InRect τ 0 (C₁ * 2 ^ (-lvl χ.χ₁ (n + m))) (C₂ * 2 ^ (-lvl χ.χ₂ (n + m)))) :
    |cent (σ ∗ τ) (χ.E (n + m)) (χ.E n) - cent σ (χ.E (n + m)) (χ.E n)| ≤
      3 * Real.log ((2 * ⌈C₁⌉₊ + 3) * (2 * ⌈C₂⌉₊ + 3) : ℕ) := by
  obtain ⟨ha, hb⟩ := InRect.nonneg hτ
  have hC₁ : 0 ≤ C₁ := (mul_nonneg_iff_of_pos_right (zpow_pos two_pos _)).1 ha
  have hC₂ : 0 ≤ C₂ := (mul_nonneg_iff_of_pos_right (zpow_pos two_pos _)).1 hb
  have hτ' : InRect τ 0 (C₁ * 2 ^ (-lvl χ.χ₁ n)) (C₂ * 2 ^ (-lvl χ.χ₂ n)) :=
    hτ.mono (mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ one_le_two
        (neg_le_neg (lvl_mono χ.pos (by linarith)))) hC₁)
      (mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ one_le_two
        (neg_le_neg (lvl_mono χ.pos₂ (by linarith)))) hC₂)
  have h := abs_cent_conv_sub_cent_le_rect hσ hτ hτ'
  rw [χ.E_eq_rect, χ.E_eq_rect]
  linarith

end Small

end BoxLike.Rapaport
