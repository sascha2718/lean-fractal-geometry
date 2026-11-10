module

/-
The mass distribution principle for exact-dimensional measures. It gives the inequality
`dim μ ≤ dim_H A` for every set `A` of positive `μ`-measure, which is the half of
`\underline{dim}_H(μ) = inf {dim_H A : μ(A) > 0}` in `eq:dimension_measure_def` of
`sec:ledrappier_young_formula` used in the last step of the proof of `thm:main2`, where it
reads `dim(π_* μ) ≤ dim_H X`.

* `HasLocalDim.eventually_measure_closedBall_le`: if `dimloc(μ, x) = d` and `t < d`, then
  `μ(B(x, r)) ≤ r^t` for all small `r > 0`.
* `measure_le_hausdorffMeasure_of_closedBall_le`: the mass distribution principle. If
  `μ(B(x, r)) ≤ r^t` for every `x ∈ E` and every `r ∈ (0, δ)`, then `μ(E) ≤ 𝓗^t(E)`. The set
  `E` is arbitrary and `μ(E)` is its outer measure.
* `IsExactDim.le_dimH`: if `μ` is a finite exact-dimensional measure and `μ(A) > 0`, then
  `dim μ ≤ dim_H A`.
* `IsExactDim.le_dimH_of_map`: if the push-forward `f_* ν` of a probability measure is
  exact-dimensional, then `dim(f_* ν) ≤ dim_H f(Y)`. This is the form used for the attractor
  `X = π(Σ)`.
-/
public import BoxLike.MeasureDim
public import Mathlib.Topology.MetricSpace.HausdorffDimension

@[expose] public section

namespace BoxLike

open MeasureTheory Measure Filter Topology Metric Set
open scoped ENNReal

section LocalDim

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {μ : Measure X} {x : X}
  {d t : ℝ}

/-- If `dimloc(μ, x) = d` and `t < d`, then `μ(B(x, r)) ≤ r^t` for all small `r > 0`. For
`r < 1` the inequality `t < log μ(B(x, r)) / log r` gives `log μ(B(x, r)) < t log r`, since
`log r < 0`. -/
theorem HasLocalDim.eventually_measure_closedBall_le [IsFiniteMeasure μ]
    (h : HasLocalDim μ x d) (ht : t < d) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, μ (closedBall x r) ≤ ENNReal.ofReal (r ^ t) := by
  have hlt : ∀ᶠ r : ℝ in 𝓝[>] 0, t < Real.log (μ.real (closedBall x r)) / Real.log r :=
    h.eventually_const_lt ht
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

end LocalDim

section MassDistribution

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
  {d t δ : ℝ}

/-- The mass distribution principle: if `t ≥ 0` and `μ(B(x, r)) ≤ r^t` for every `x ∈ E` and
every `r ∈ (0, δ)`, then `μ(E) ≤ 𝓗^t(E)`. The set `E` is arbitrary and `μ(E)` is its outer
measure. A set `U` of diameter less than `δ` that meets `E` at `x` lies in `B(x, ρ)` for every
`ρ > |U|`, so `μ(U) ≤ ρ^t`, and `ρ ↓ |U|` gives `μ(U) ≤ |U|^t`. Summing over a countable cover
of `E` by such sets gives the claim. -/
theorem measure_le_hausdorffMeasure_of_closedBall_le (ht : 0 ≤ t) (hδ : 0 < δ) {E : Set X}
    (hE : ∀ x ∈ E, ∀ r : ℝ, 0 < r → r < δ → μ (closedBall x r) ≤ ENNReal.ofReal (r ^ t)) :
    μ E ≤ μH[t] E := by
  rw [hausdorffMeasure_apply]
  refine le_iSup₂_of_le (ENNReal.ofReal (δ / 2)) (ENNReal.ofReal_pos.2 (half_pos hδ)) ?_
  refine le_iInf fun U => le_iInf fun hEU => le_iInf fun hU => ?_
  have hcov : E ⊆ ⋃ n, U n ∩ E := by
    rw [← iUnion_inter]
    exact subset_inter hEU subset_rfl
  refine (measure_mono hcov).trans
    ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun n => ?_))
  rcases (U n ∩ E).eq_empty_or_nonempty with h | ⟨x, hxU, hxE⟩
  · simp [h]
  have htop : ediam (U n) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hU n)
  have hdiam : diam (U n) ≤ δ / 2 := ENNReal.toReal_le_of_le_ofReal (half_pos hδ).le (hU n)
  have hpow : ediam (U n) ^ t = ENNReal.ofReal (diam (U n) ^ t) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg diam_nonneg ht, diam, ENNReal.ofReal_toReal htop]
  have hlim : Tendsto (fun ρ : ℝ => ENNReal.ofReal (ρ ^ t)) (𝓝[>] diam (U n))
      (𝓝 (ediam (U n) ^ t)) := by
    rw [hpow]
    exact ((ENNReal.continuous_ofReal.continuousAt.comp
      (Real.continuousAt_rpow_const _ _ (Or.inr ht))).tendsto).mono_left nhdsWithin_le_nhds
  rw [iSup_pos ⟨x, hxU⟩]
  refine ge_of_tendsto hlim ?_
  have hlt : diam (U n) < δ := by linarith
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds hlt)] with ρ hρ hρδ
  have hρ : diam (U n) < ρ := hρ
  have hsub : U n ∩ E ⊆ closedBall x ρ := fun y hy =>
    mem_closedBall.2 ((dist_le_diam_of_mem' htop hy.1 hxU).trans hρ.le)
  exact (measure_mono hsub).trans (hE x hxE ρ (diam_nonneg.trans_lt hρ) hρδ)

/-- The half of `\underline{dim}_H(μ) = inf {dim_H A : μ(A) > 0}` used in the proof of
`thm:main2`: if `μ` is a finite exact-dimensional measure and `μ(A) > 0`, then
`dim μ ≤ dim_H A`. The set `A` is arbitrary. For `0 ≤ t < dim μ` the sets
`E_n = {x ∈ A : μ(B(x, r)) ≤ r^t for all r ∈ (0, 1 / (n + 1))}` cover `A` up to a `μ`-null
set, so `μ(E_n) > 0` for some `n`, and the mass distribution principle gives
`𝓗^t(E_n) ≥ μ(E_n) > 0`, hence `dim_H A ≥ dim_H E_n ≥ t`. -/
theorem IsExactDim.le_dimH [IsFiniteMeasure μ] (h : IsExactDim μ d) {A : Set X}
    (hA : 0 < μ A) : ENNReal.ofReal d ≤ dimH A := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
  have hctop : c ≠ ∞ := ne_top_of_lt hc
  have ht : c.toReal < d := (ENNReal.lt_ofReal_iff_toReal_lt hctop).1 hc
  have ht0 : 0 ≤ c.toReal := ENNReal.toReal_nonneg
  let G : ℕ → Set X := fun n => {x | ∀ r : ℝ, 0 < r → r < 1 / ((n : ℝ) + 1) →
    μ (closedBall x r) ≤ ENNReal.ofReal (r ^ c.toReal)}
  have hsub : A ∩ {x | HasLocalDim μ x d} ⊆ ⋃ n, A ∩ G n := by
    rintro x ⟨hxA, hx⟩
    obtain ⟨u, hu, hIoo⟩ :=
      mem_nhdsGT_iff_exists_Ioo_subset.1 (hx.eventually_measure_closedBall_le ht)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < u from hu)
    exact mem_iUnion.2 ⟨n, hxA, fun r hr0 hr => hIoo ⟨hr0, hr.trans hn⟩⟩
  have hpos : 0 < μ (⋃ n, A ∩ G n) := by
    have hfull : μ (A ∩ {x | HasLocalDim μ x d}) = μ A := measure_inter_conull (ae_iff.1 h)
    exact (hfull ▸ hA).trans_le (measure_mono hsub)
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hpos.ne'
  have hH : μH[c.toReal] (A ∩ G n) ≠ 0 :=
    (hn.trans_le (measure_le_hausdorffMeasure_of_closedBall_le ht0 Nat.one_div_pos_of_nat
      fun x hx => hx.2)).ne'
  calc c = ((c.toReal.toNNReal : NNReal) : ℝ≥0∞) := (ENNReal.ofReal_toReal hctop).symm
    _ ≤ dimH (A ∩ G n) :=
      le_dimH_of_hausdorffMeasure_ne_zero (by rwa [Real.coe_toNNReal _ ht0])
    _ ≤ dimH A := dimH_mono inter_subset_left

end MassDistribution

/-- The last step of the proof of `thm:main2`, `dim(π_* μ) ≤ dim_H X` for `X = π(Σ)`: if the
push-forward `f_* ν` of a probability measure `ν` under a measurable map `f` is
exact-dimensional, then `dim(f_* ν) ≤ dim_H f(Y)`. The range `f(Y)` has full outer
`f_* ν`-measure and no measurability of the range is needed. -/
theorem IsExactDim.le_dimH_of_map {Y X : Type*} [MeasurableSpace Y] [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {ν : Measure Y} [IsProbabilityMeasure ν] {f : Y → X}
    (hf : Measurable f) {d : ℝ} (h : IsExactDim (ν.map f) d) :
    ENNReal.ofReal d ≤ dimH (Set.range f) := by
  refine h.le_dimH (zero_lt_one.trans_le ?_)
  calc (1 : ℝ≥0∞) = ν (f ⁻¹' Set.range f) := by rw [preimage_range, measure_univ]
    _ ≤ ν.map f (Set.range f) := le_map_apply hf.aemeasurable _

/-- The assumptions of `IsExactDim.le_dimH` hold on the plane `ℝ × ℝ`. -/
example {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ] {d : ℝ} (h : IsExactDim μ d)
    {A : Set (ℝ × ℝ)} (hA : 0 < μ A) : ENNReal.ofReal d ≤ dimH A :=
  h.le_dimH hA

/-- The assumptions of `IsExactDim.le_dimH` hold on the real line. -/
example {μ : Measure ℝ} [IsFiniteMeasure μ] {d : ℝ} (h : IsExactDim μ d) {A : Set ℝ}
    (hA : 0 < μ A) : ENNReal.ofReal d ≤ dimH A :=
  h.le_dimH hA

end BoxLike
