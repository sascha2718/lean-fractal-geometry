module

/-
The packing half of `eq:dimension_measure_def`, from `sec:ledrappier_young_formula`: for a finite
Borel measure `μ` on `ℝ^d`,
`\overline{dim}_p(μ) = inf {dim_P A : A is a Borel set such that μ(ℝ^d \ A) = 0}`.
The packing dimension is `packingDim` of `SetDimensions`, the modified upper Minkowski
dimension, and the proofs use no packing measures.

* `measure_eq_zero_of_upperBoxDim_lt`, `le_upperBoxDim_of_measure_pos`,
  `le_packingDim_of_measure_pos`: if every point `x` of a set `F` has `μ(B(x, r)) ≤ r^s` for
  arbitrarily small `r` and `μ(F) > 0`, then `\overline{dim}_M F ≥ s` and `dim_P F ≥ s`. The
  measure is arbitrary and `μ(F)` is the outer measure.
* `frequently_measure_closedBall_le_of_lt_upperLocalDim`,
  `le_packingDim_of_ae_le_upperLocalDim`, `le_upperBoxDim_of_ae_le_upperLocalDim`: the same
  bounds under `\overline{dim}_loc(μ, x) ≥ t`, for a finite measure.
* `ofReal_upperPackingDim_le_packingDim`: `\overline{dim}_p(μ) ≤ dim_P A` for every set `A` of
  full measure.
* `uniformlyHeavySet`, `upperBoxDim_uniformlyHeavySet_le`, `isBounded_uniformlyHeavySet`,
  `exists_mem_uniformlyHeavySet`: the points at which every ball of radius `r < δ` has measure
  at least `r^t` form a bounded set of upper Minkowski dimension at most `t`, and for
  `t > \overline{dim}_loc(μ, x)` the point `x` lies in such a set.
* `exists_measurableSet_packingDim_le`, `ofReal_upperPackingDim_eq_iInf_packingDim`,
  `ofReal_upperPackingDim_eq_iInf_packingDim_of_compl`: the first line of
  `eq:dimension_measure_def` on a second-countable pseudo-metric space, under the boundedness
  hypotheses that hold on `ℝ^d`, over Borel sets and over all sets of full measure.
* `ofReal_upperPackingDim_eq_iInf_packingDim_of_finiteDimensional`,
  `upperPackingDim_eq_toReal_iInf_packingDim`, `exists_packingDim_le`: the first line of
  `eq:dimension_measure_def` for every finite Borel measure on a finite-dimensional real
  normed space.
* `upperPackingDim_le_of_absolutelyContinuous`: `μ ≪ ν` gives
  `\overline{dim}_p(μ) ≤ \overline{dim}_p(ν)`, the argument of tex lines 2550 to 2553.
-/
public import BoxLike.LocalDimBounds
public import BoxLike.SetDimensions
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

@[expose] public section

namespace BoxLike

open MeasureTheory Measure Filter Topology Metric Set
open scoped ENNReal NNReal

section LowerBound

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {μ : Measure X} {F : Set X}
  {s t : ℝ}

/-- A set `F` all of whose points `x` have `μ(B(x, r)) ≤ r^s` for arbitrarily small `r` is
`μ`-null when `\overline{dim}_M F < s`. Let `a = 1/2`. With `N_ρ(F) ≤ ρ^{-s₀}` for small `ρ` and
`s₀ < s`, the points of `F` with such a radius in `(a^{k+1}, a^k]` are covered by `N_ρ(F)` balls
of radius `ρ = a^{k+2}`, each inside a ball `B(x, r)` with `μ(B(x, r)) ≤ a^{ks}`; these bounds
are summable in `k`, and the first Borel–Cantelli lemma applies. The measure is arbitrary and
`μ(F)` is the outer measure. -/
theorem measure_eq_zero_of_upperBoxDim_lt (hF : upperBoxDim F < ENNReal.ofReal s)
    (h : ∀ x ∈ F, ∃ᶠ r : ℝ in 𝓝[>] 0, μ (closedBall x r) ≤ ENNReal.ofReal (r ^ s)) :
    μ F = 0 := by
  obtain ⟨s₀, hs₀, hs₀s⟩ :
      ∃ s₀ : ℝ≥0, UpperBoxDimLE F (s₀ : ℝ) ∧ (s₀ : ℝ≥0∞) < ENNReal.ofReal s := by
    simpa only [upperBoxDim, iInf_lt_iff, exists_prop] using hF
  have hlt : (s₀ : ℝ) < s := by
    simpa using (ENNReal.lt_ofReal_iff_toReal_lt ENNReal.coe_ne_top).1 hs₀s
  have hs : 0 < s := lt_of_le_of_lt s₀.coe_nonneg hlt
  obtain ⟨ρ₀, hρ₀, hN⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hs₀
  have hρ₀ : (0 : ℝ) < ρ₀ := hρ₀
  obtain ⟨a, ha0, ha2⟩ : ∃ a : ℝ, 0 < a ∧ 2 * a ≤ 1 := ⟨1 / 2, by norm_num, by norm_num⟩
  have ha1 : a < 1 := by linarith
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hρ₀ ha1
  let G : ℕ → Set X := fun k => {x | x ∈ F ∧ ∃ r : ℝ, a ^ (k + 1) < r ∧ r ≤ a ^ k ∧
    μ (closedBall x r) ≤ ENNReal.ofReal (r ^ s)}
  have hq0 : 0 ≤ a ^ (s - s₀) := Real.rpow_nonneg ha0.le _
  have hq1 : a ^ (s - s₀) < 1 := Real.rpow_lt_one ha0.le ha1 (by linarith)
  have hc0 : 0 ≤ (a ^ (-(s₀ : ℝ))) ^ 2 := by positivity
  -- the bound for one scale
  have hG : ∀ k, K ≤ k →
      μ (G k) ≤ ENNReal.ofReal ((a ^ (-(s₀ : ℝ))) ^ 2 * (a ^ (s - s₀)) ^ k) := by
    intro k hk
    have hρ0 : 0 < a ^ (k + 2) := pow_pos ha0 _
    have hρK : a ^ (k + 2) < ρ₀ :=
      (pow_le_pow_of_le_one ha0.le ha1.le (by omega : K ≤ k + 2)).trans_lt hK
    have hNρ : (Metric.externalCoveringNumber (a ^ (k + 2)).toNNReal F : ℝ≥0∞)
        ≤ ENNReal.ofReal ((a ^ (k + 2)) ^ (-(s₀ : ℝ))) := hN ⟨hρ0, hρK⟩
    have htop : Metric.externalCoveringNumber (a ^ (k + 2)).toNNReal F ≠ ⊤ := by
      intro h'
      rw [h', ENat.toENNReal_top, top_le_iff] at hNρ
      exact ENNReal.ofReal_ne_top hNρ
    obtain ⟨D, hDfin, hDcov, hDcard⟩ := exists_isCover_encard_eq htop
    have h2ρ : 2 * a ^ (k + 2) ≤ a ^ (k + 1) := by
      have := pow_pos ha0 (k + 1)
      rw [pow_succ a (k + 1)]
      nlinarith
    have hsub : G k ⊆ ⋃ c ∈ D, closedBall c (a ^ (k + 2)) ∩ G k := by
      intro x hx
      obtain ⟨c, hc, hxc⟩ := hDcov hx.1
      replace hxc : edist x c ≤ ENNReal.ofReal (a ^ (k + 2)) := hxc
      exact mem_iUnion₂.2 ⟨c, hc, mem_closedBall'.2 (by
        rw [dist_comm]; exact (edist_le_ofReal hρ0.le).1 hxc), hx⟩
    have hterm : ∀ c, μ (closedBall c (a ^ (k + 2)) ∩ G k) ≤ ENNReal.ofReal ((a ^ k) ^ s) := by
      intro c
      rcases (closedBall c (a ^ (k + 2)) ∩ G k).eq_empty_or_nonempty with he | ⟨x, hxc, hxG⟩
      · rw [he, measure_empty]
        exact zero_le
      obtain ⟨r, hr1, hr2, hr⟩ := hxG.2
      have hr0 : 0 < r := (pow_pos ha0 _).trans hr1
      calc μ (closedBall c (a ^ (k + 2)) ∩ G k) ≤ μ (closedBall x r) := by
            refine measure_mono fun y hy => mem_closedBall.2 ?_
            have h1 := mem_closedBall.1 hy.1
            have h2 := mem_closedBall.1 hxc
            have h3 := dist_triangle_right y x c
            linarith
        _ ≤ ENNReal.ofReal (r ^ s) := hr
        _ ≤ ENNReal.ofReal ((a ^ k) ^ s) :=
            ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hr0.le hr2 hs.le)
    calc μ (G k) ≤ μ (⋃ c ∈ D, closedBall c (a ^ (k + 2)) ∩ G k) := measure_mono hsub
      _ ≤ ∑' c : D, μ (closedBall c (a ^ (k + 2)) ∩ G k) :=
          measure_biUnion_le μ hDfin.countable _
      _ ≤ ∑' _ : D, ENNReal.ofReal ((a ^ k) ^ s) := ENNReal.tsum_le_tsum fun c => hterm c
      _ = (D.encard : ℝ≥0∞) * ENNReal.ofReal ((a ^ k) ^ s) := ENNReal.tsum_set_const D _
      _ ≤ ENNReal.ofReal ((a ^ (k + 2)) ^ (-(s₀ : ℝ))) * ENNReal.ofReal ((a ^ k) ^ s) := by
          gcongr
          rw [hDcard]
          exact hNρ
      _ = ENNReal.ofReal ((a ^ (k + 2)) ^ (-(s₀ : ℝ)) * (a ^ k) ^ s) :=
          (ENNReal.ofReal_mul (Real.rpow_nonneg hρ0.le _)).symm
      _ = ENNReal.ofReal ((a ^ (-(s₀ : ℝ))) ^ 2 * (a ^ (s - s₀)) ^ k) := by
          rw [← Real.rpow_pow_comm ha0.le, ← Real.rpow_pow_comm ha0.le, sub_eq_add_neg,
            Real.rpow_add ha0]
          ring_nf
  -- the first Borel–Cantelli lemma along the scales `k ≥ K`
  have hsum : ∑' k, μ (G (k + K)) ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∑' k, ENNReal.ofReal ((a ^ (-(s₀ : ℝ))) ^ 2)
      * ENNReal.ofReal (a ^ (s - s₀)) ^ k) ?_ (ENNReal.tsum_le_tsum fun k => ?_)
    · rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2
        (tsub_pos_iff_lt.2 (ENNReal.ofReal_lt_one.2 hq1)).ne')
    · refine (hG (k + K) (by omega)).trans ?_
      rw [← ENNReal.ofReal_pow hq0, ← ENNReal.ofReal_mul hc0]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hq0 hq1.le (by omega)) hc0)
  have hFsub : F ⊆ limsup (fun k => G (k + K)) atTop := by
    intro x hx
    refine mem_limsup_iff_frequently_mem.2 (frequently_atTop.2 fun N => ?_)
    have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r < a ^ (N + K) :=
      nhdsWithin_le_nhds (eventually_lt_nhds (pow_pos ha0 _))
    obtain ⟨r, hr, hrN, hr0⟩ := ((h x hx).and_eventually (hsmall.and self_mem_nhdsWithin)).exists
    have hr0 : 0 < r := hr0
    have hr1 : r ≤ 1 := hrN.le.trans (pow_le_one₀ ha0.le ha1.le)
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near_of_lt_one hr0 hr1 ha0 ha1
    have hnK : N + K ≤ n := by
      by_contra hcon
      have := pow_le_pow_of_le_one ha0.le ha1.le (by omega : n + 1 ≤ N + K)
      linarith
    obtain ⟨k, rfl⟩ : ∃ k, n = k + K := ⟨n - K, by omega⟩
    exact ⟨k, by omega, hx, r, hn1, hn2, hr⟩
  exact le_antisymm ((measure_mono hFsub).trans (measure_limsup_atTop_eq_zero hsum).le)
    zero_le

/-- A set `F` of positive outer measure all of whose points `x` have `μ(B(x, r)) ≤ r^s` for
arbitrarily small `r` has upper Minkowski dimension at least `s`. The measure is arbitrary. -/
theorem le_upperBoxDim_of_measure_pos (hF : 0 < μ F)
    (h : ∀ x ∈ F, ∃ᶠ r : ℝ in 𝓝[>] 0, μ (closedBall x r) ≤ ENNReal.ofReal (r ^ s)) :
    ENNReal.ofReal s ≤ upperBoxDim F :=
  not_lt.1 fun hlt => hF.ne' (measure_eq_zero_of_upperBoxDim_lt hlt h)

/-- A set `F` of positive outer measure all of whose points `x` have `μ(B(x, r)) ≤ r^s` for
arbitrarily small `r` has packing dimension at least `s`: for a countable cover of `F` some
piece meets `F` in a set of positive outer measure, to which `le_upperBoxDim_of_measure_pos`
applies. The boundedness of the pieces is not used. -/
theorem le_packingDim_of_measure_pos (hF : 0 < μ F)
    (h : ∀ x ∈ F, ∃ᶠ r : ℝ in 𝓝[>] 0, μ (closedBall x r) ≤ ENNReal.ofReal (r ^ s)) :
    ENNReal.ofReal s ≤ packingDim F := by
  refine le_packingDim fun A hcov _ => ?_
  have hpos : 0 < μ (⋃ i, F ∩ A i) := by
    rwa [← inter_iUnion, inter_eq_left.2 hcov]
  obtain ⟨i, hi⟩ := exists_measure_pos_of_not_measure_iUnion_null hpos.ne'
  exact (le_upperBoxDim_of_measure_pos hi fun x hx => h x hx.1).trans
    ((upperBoxDim_mono inter_subset_right).trans (le_iSup (fun i => upperBoxDim (A i)) i))

/-- If `s` is smaller than the upper pointwise dimension of a finite measure `μ` at `x`, then
`μ(B(x, r)) ≤ r^s` for arbitrarily small `r > 0`. This holds at every point `x`. Where the
convention `Real.log 0 = 0` or an unbounded quotient gives `upperLocalDim μ x = 0` in place of
the article's `∞`, the hypothesis admits only `s < 0`. -/
theorem frequently_measure_closedBall_le_of_lt_upperLocalDim [IsFiniteMeasure μ] {x : X}
    (hs : s < upperLocalDim μ x) :
    ∃ᶠ r : ℝ in 𝓝[>] 0, μ (closedBall x r) ≤ ENNReal.ofReal (r ^ s) := by
  have hlt : ∃ᶠ r : ℝ in 𝓝[>] 0, s < Real.log (μ.real (closedBall x r)) / Real.log r :=
    frequently_lt_of_lt_limsup (isBoundedUnder_ge_log_div_log x).isCoboundedUnder_le hs
  have hone : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 := nhdsWithin_le_nhds (eventually_lt_nhds one_pos)
  refine (hlt.and_eventually (hone.and self_mem_nhdsWithin)).mono fun r ⟨hr, hr1, hr0⟩ => ?_
  have hr0 : 0 < r := hr0
  rw [lt_div_iff_of_neg (Real.log_neg hr0 hr1)] at hr
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases (measureReal_nonneg (μ := μ) (s := closedBall x r)).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact Real.rpow_nonneg hr0.le s
  · rw [← Real.log_le_log_iff hpos (Real.rpow_pos_of_pos hr0 s), Real.log_rpow hr0]
    exact hr.le

/-- The packing analogue of the mass distribution principle: if `μ` is a finite measure,
`μ(A) > 0` and `\overline{dim}_loc(μ, x) ≥ t` for `μ`-almost every `x ∈ A`, then
`dim_P A ≥ t`. The set `A` is arbitrary and `μ(A)` is its outer measure. -/
theorem le_packingDim_of_ae_le_upperLocalDim [IsFiniteMeasure μ] {A : Set X} (hA : 0 < μ A)
    (h : ∀ᵐ x ∂μ, x ∈ A → t ≤ upperLocalDim μ x) : ENNReal.ofReal t ≤ packingDim A := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
  have hctop : c ≠ ∞ := ne_top_of_lt hc
  have ht : c.toReal < t := (ENNReal.lt_ofReal_iff_toReal_lt hctop).1 hc
  have hpos : 0 < μ (A ∩ {x | x ∈ A → t ≤ upperLocalDim μ x}) := by
    have hfull : μ (A ∩ {x | x ∈ A → t ≤ upperLocalDim μ x}) = μ A :=
      measure_inter_conull (ae_iff.1 h)
    rwa [hfull]
  calc c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hctop).symm
    _ ≤ packingDim (A ∩ {x | x ∈ A → t ≤ upperLocalDim μ x}) :=
        le_packingDim_of_measure_pos hpos fun x hx =>
          frequently_measure_closedBall_le_of_lt_upperLocalDim (ht.trans_le (hx.2 hx.1))
    _ ≤ packingDim A := packingDim_mono inter_subset_left

/-- If `μ` is a finite measure, `μ(A) > 0` and `\overline{dim}_loc(μ, x) ≥ t` for `μ`-almost
every `x ∈ A`, then `\overline{dim}_M A ≥ t`. -/
theorem le_upperBoxDim_of_ae_le_upperLocalDim [IsFiniteMeasure μ] {A : Set X} (hA : 0 < μ A)
    (h : ∀ᵐ x ∂μ, x ∈ A → t ≤ upperLocalDim μ x) : ENNReal.ofReal t ≤ upperBoxDim A :=
  (le_packingDim_of_ae_le_upperLocalDim hA h).trans (packingDim_le_upperBoxDim A)

/-- The inequality `≤` in the first line of `eq:dimension_measure_def`: if `μ` is a finite
measure and `μ(Aᶜ) = 0`, then `\overline{dim}_p(μ) ≤ dim_P A`. The set `A` is arbitrary. -/
theorem ofReal_upperPackingDim_le_packingDim [IsFiniteMeasure μ] {A : Set X} (hA : μ Aᶜ = 0) :
    ENNReal.ofReal (upperPackingDim μ) ≤ packingDim A := by
  rcases eq_or_ne μ 0 with rfl | hne
  · rw [upperPackingDim_zero, ENNReal.ofReal_zero]
    exact zero_le
  have : (ae μ).NeBot := ae_neBot.2 hne
  refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
  have hctop : c ≠ ∞ := ne_top_of_lt hc
  have ht : c.toReal < upperPackingDim μ := (ENNReal.lt_ofReal_iff_toReal_lt hctop).1 hc
  have hfreq : ∃ᵐ x ∂μ, c.toReal < upperLocalDim μ x :=
    frequently_lt_of_lt_limsup (f := ae μ) (u := upperLocalDim μ)
      (isBoundedUnder_of_eventually_ge
        (Eventually.of_forall upperLocalDim_nonneg)).isCoboundedUnder_le ht
  have hpos : 0 < μ ({x | c.toReal < upperLocalDim μ x} ∩ A) := by
    rw [measure_inter_conull hA]
    exact pos_iff_ne_zero.2 (frequently_ae_mem_iff.1 hfreq)
  calc c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hctop).symm
    _ ≤ packingDim ({x | c.toReal < upperLocalDim μ x} ∩ A) :=
        le_packingDim_of_measure_pos hpos fun x hx =>
          frequently_measure_closedBall_le_of_lt_upperLocalDim hx.1
    _ ≤ packingDim A := packingDim_mono inter_subset_right

end LowerBound

section UpperBound

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {μ : Measure X} {t δ : ℝ}

/-- The set of the points `x` such that `μ(B(x, r)) ≥ r^t` for every radius `r ∈ (0, δ)`. For a
finite measure it is bounded and has upper Minkowski dimension at most `t`. For
`t > \overline{dim}_p(μ)`, under the hypotheses of `exists_measurableSet_packingDim_le`, the sets
with `δ = 1 / (n + 1)` cover almost every point, and their union contains the Borel set of full
measure and small packing dimension in the first line of `eq:dimension_measure_def`. -/
def uniformlyHeavySet (μ : Measure X) (t δ : ℝ) : Set X :=
  {x | ∀ r : ℝ, 0 < r → r < δ → ENNReal.ofReal (r ^ t) ≤ μ (closedBall x r)}

/-- A `2ρ`-separated set `C` of points of `uniformlyHeavySet μ t δ`, with `0 < ρ < δ`, has at
most `μ(X) ρ^{-t}` elements: the closed balls of radius `ρ` about its points are disjoint and
each has measure at least `ρ^t`. -/
theorem encard_mul_le_of_subset_uniformlyHeavySet [OpensMeasurableSpace X] {C : Set X} {ρ : ℝ}
    (hρ : 0 < ρ) (hρδ : ρ < δ) (hC : C ⊆ uniformlyHeavySet μ t δ)
    (hsep : Metric.IsSeparated (ENNReal.ofReal (2 * ρ)) C) :
    (C.encard : ℝ≥0∞) * ENNReal.ofReal (ρ ^ t) ≤ μ univ := by
  rw [← ENNReal.tsum_set_const]
  refine (ENNReal.tsum_le_tsum fun x : C => hC x.2 ρ hρ hρδ).trans
    (tsum_measure_le_measure_univ (fun _ => measurableSet_closedBall.nullMeasurableSet)
      fun x y hxy => Disjoint.aedisjoint (Set.disjoint_left.2 fun z hzx hzy => ?_))
  have hne : (x : X) ≠ y := fun h => hxy (Subtype.ext h)
  have h1 : ENNReal.ofReal (2 * ρ) < edist (x : X) y := hsep x.2 y.2 hne
  rw [edist_dist] at h1
  have h2 := ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)).1 h1)
  have h3 := dist_triangle_left (x : X) y z
  rw [mem_closedBall] at hzx hzy
  linarith

/-- The set `uniformlyHeavySet μ t δ` has upper Minkowski dimension at most `t`, for a finite
measure, `t ≥ 0` and `δ > 0`. At a scale `r < 2δ` the covering number is at most the packing
number, which `encard_mul_le_of_subset_uniformlyHeavySet` bounds by `μ(X) (r/2)^{-t}`. -/
theorem upperBoxDim_uniformlyHeavySet_le [OpensMeasurableSpace X] [IsFiniteMeasure μ]
    (ht : 0 ≤ t) (hδ : 0 < δ) : upperBoxDim (uniformlyHeavySet μ t δ) ≤ ENNReal.ofReal t := by
  have hK : 0 < (μ.real univ + 1) * 2 ^ t := by positivity
  refine upperBoxDim_le_of_forall (s := t.toNNReal) (C := ((μ.real univ + 1) * 2 ^ t).toNNReal)
    (Real.toNNReal_pos.2 hK) ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_lt_nhds (by positivity : (0 : ℝ) < 2 * δ))] with r hr0 hrδ
  have hr0 : 0 < r := hr0
  rw [Real.coe_toNNReal t ht]
  refine (ENat.toENNReal_le.2 ((Metric.externalCoveringNumber_le_coveringNumber _ _).trans
    (Metric.coveringNumber_le_packingNumber _ _))).trans ?_
  rw [Metric.packingNumber]
  simp only [ENat.toENNReal_iSup, iSup_le_iff]
  intro C hCsub hCsep
  have key := encard_mul_le_of_subset_uniformlyHeavySet (ρ := r / 2) (by positivity)
    (by linarith) hCsub (by rwa [show 2 * (r / 2) = r by ring])
  have hprod : ENNReal.ofReal ((r / 2) ^ t) * ENNReal.ofReal ((r / 2) ^ (-t)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
      ← Real.rpow_add (by positivity), add_neg_cancel, Real.rpow_zero, ENNReal.ofReal_one]
  have hdiv : (r / 2) ^ (-t) = 2 ^ t * r ^ (-t) := by
    rw [Real.div_rpow hr0.le zero_le_two, Real.rpow_neg zero_le_two, div_inv_eq_mul, mul_comm]
  have huniv : μ univ ≤ ENNReal.ofReal (μ.real univ + 1) := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc (C.encard : ℝ≥0∞)
      = (C.encard : ℝ≥0∞) * ENNReal.ofReal ((r / 2) ^ t) * ENNReal.ofReal ((r / 2) ^ (-t)) := by
        rw [mul_assoc, hprod, mul_one]
    _ ≤ μ univ * ENNReal.ofReal ((r / 2) ^ (-t)) := by gcongr
    _ ≤ ENNReal.ofReal (μ.real univ + 1) * ENNReal.ofReal ((r / 2) ^ (-t)) := by gcongr
    _ = ENNReal.ofReal ((μ.real univ + 1) * 2 ^ t * r ^ (-t)) := by
        rw [← ENNReal.ofReal_mul (by positivity), hdiv, mul_assoc]
    _ = (((μ.real univ + 1) * 2 ^ t).toNNReal : ℝ≥0∞) * ENNReal.ofReal (r ^ (-t)) :=
        ENNReal.ofReal_mul hK.le

/-- The set `uniformlyHeavySet μ t δ` is bounded, for a finite measure, `t ≥ 0` and `δ > 0`. -/
theorem isBounded_uniformlyHeavySet [OpensMeasurableSpace X] [IsFiniteMeasure μ] (ht : 0 ≤ t)
    (hδ : 0 < δ) : Bornology.IsBounded (uniformlyHeavySet μ t δ) :=
  isBounded_of_upperBoxDim_ne_top
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (upperBoxDim_uniformlyHeavySet_le ht hδ))

/-- A point `x` of the support of a finite measure `μ` with `\overline{dim}_loc(μ, x) < t`, at
which the quotient `log μ(B(x, r)) / log r` is bounded above, lies in
`uniformlyHeavySet μ t (1 / (n + 1))` for some `n`. The two side conditions exclude the points
where the real-valued `limsup` of the library does not carry its usual meaning. -/
theorem exists_mem_uniformlyHeavySet [IsFiniteMeasure μ] {x : X}
    (hpos : ∀ r : ℝ, 0 < r → 0 < μ (closedBall x r))
    (hb : (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≤ ·)
      fun r : ℝ => Real.log (μ.real (closedBall x r)) / Real.log r)
    (h : upperLocalDim μ x < t) : ∃ n : ℕ, x ∈ uniformlyHeavySet μ t (1 / ((n : ℝ) + 1)) := by
  have hlt : ∀ᶠ r : ℝ in 𝓝[>] 0, Real.log (μ.real (closedBall x r)) / Real.log r < t :=
    eventually_lt_of_limsup_lt h hb
  have hone : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 := nhdsWithin_le_nhds (eventually_lt_nhds one_pos)
  obtain ⟨ρ, hρ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hlt.and hone)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < ρ from hρ)
  refine ⟨n, fun r hr0 hrn => ?_⟩
  obtain ⟨hr, hr1⟩ := hsub ⟨hr0, hrn.trans hn⟩
  have hm : 0 < μ.real (closedBall x r) :=
    ENNReal.toReal_pos (hpos r hr0).ne' (measure_ne_top μ _)
  rw [div_lt_iff_of_neg (Real.log_neg hr0 hr1)] at hr
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hr0 t) hm, Real.log_rpow hr0]
  exact hr.le

/-- The inequality `≥` in the first line of `eq:dimension_measure_def`: for every
`t > \overline{dim}_p(μ)` there is a Borel set `A` with `μ(Aᶜ) = 0` and `dim_P A ≤ t`. The
measure `μ` is finite on a second-countable pseudo-metric space, the quotients
`log μ(B(x, r)) / log r` are bounded above as `r ↓ 0` for almost every `x`, and the upper
pointwise dimension is essentially bounded above; on `ℝ^d` both hold by
`ae_isBoundedUnder_le_log_div_log` and `isBoundedUnder_upperLocalDim`. The union of the sets
`uniformlyHeavySet μ t (1 / (n + 1))` has full measure, and the complement of a measurable null
set containing its complement is the Borel set. -/
theorem exists_measurableSet_packingDim_le [SecondCountableTopology X] [OpensMeasurableSpace X]
    [IsFiniteMeasure μ]
    (hb : ∀ᵐ x ∂μ, (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≤ ·)
      fun r : ℝ => Real.log (μ.real (closedBall x r)) / Real.log r)
    (hbd : (ae μ).IsBoundedUnder (· ≤ ·) (upperLocalDim μ)) (ht : upperPackingDim μ < t) :
    ∃ A : Set X, MeasurableSet A ∧ μ Aᶜ = 0 ∧ packingDim A ≤ ENNReal.ofReal t := by
  have ht0 : 0 ≤ t := upperPackingDim_nonneg.trans ht.le
  have hS : μ (⋃ n : ℕ, uniformlyHeavySet μ t (1 / ((n : ℝ) + 1)))ᶜ = 0 := by
    have hae : ∀ᵐ x ∂μ, x ∈ ⋃ n : ℕ, uniformlyHeavySet μ t (1 / ((n : ℝ) + 1)) := by
      filter_upwards [hb, ae_le_essSup hbd, ae_forall_measure_closedBall_pos μ]
        with x hbx hle hpos
      exact mem_iUnion.2 (exists_mem_uniformlyHeavySet hpos hbx (hle.trans_lt ht))
    exact ae_iff.1 hae
  refine ⟨(toMeasurable μ (⋃ n : ℕ, uniformlyHeavySet μ t (1 / ((n : ℝ) + 1)))ᶜ)ᶜ,
    (measurableSet_toMeasurable μ _).compl, by rw [compl_compl, measure_toMeasurable, hS], ?_⟩
  have hsub : (toMeasurable μ (⋃ n : ℕ, uniformlyHeavySet μ t (1 / ((n : ℝ) + 1)))ᶜ)ᶜ
      ⊆ ⋃ n : ℕ, uniformlyHeavySet μ t (1 / ((n : ℝ) + 1)) :=
    compl_subset_comm.1 (subset_toMeasurable μ _)
  exact (packingDim_mono hsub).trans (packingDim_le_of_cover _ subset_rfl
    (fun _ => isBounded_uniformlyHeavySet ht0 Nat.one_div_pos_of_nat)
    (iSup_le fun _ => upperBoxDim_uniformlyHeavySet_le ht0 Nat.one_div_pos_of_nat))

/-- The first line of `eq:dimension_measure_def`:
`\overline{dim}_p(μ) = inf {dim_P A : A is a Borel set such that μ(Aᶜ) = 0}`, for a finite
measure `μ` on a second-countable pseudo-metric space such that the quotients
`log μ(B(x, r)) / log r` are bounded above as `r ↓ 0` for almost every `x` and the upper
pointwise dimension is essentially bounded above. The infimum is taken in `[0, ∞]`. The zero
measure is included: the empty set is a Borel set of full measure. -/
theorem ofReal_upperPackingDim_eq_iInf_packingDim [SecondCountableTopology X]
    [OpensMeasurableSpace X] [IsFiniteMeasure μ]
    (hb : ∀ᵐ x ∂μ, (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≤ ·)
      fun r : ℝ => Real.log (μ.real (closedBall x r)) / Real.log r)
    (hbd : (ae μ).IsBoundedUnder (· ≤ ·) (upperLocalDim μ)) :
    ENNReal.ofReal (upperPackingDim μ)
      = ⨅ (A : Set X) (_ : MeasurableSet A) (_ : μ Aᶜ = 0), packingDim A := by
  refine le_antisymm (le_iInf fun A => le_iInf fun _ => le_iInf fun hA =>
    ofReal_upperPackingDim_le_packingDim hA) ?_
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  rcases eq_or_ne c ∞ with rfl | hctop
  · exact le_top
  have ht : upperPackingDim μ < c.toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal upperPackingDim_nonneg hctop).1 hc
  obtain ⟨A, hAm, hA, hAdim⟩ := exists_measurableSet_packingDim_le hb hbd ht
  calc (⨅ (A : Set X) (_ : MeasurableSet A) (_ : μ Aᶜ = 0), packingDim A) ≤ packingDim A :=
        iInf_le_of_le A (iInf_le_of_le hAm (iInf_le _ hA))
    _ ≤ ENNReal.ofReal c.toReal := hAdim
    _ = c := ENNReal.ofReal_toReal hctop

/-- The first line of `eq:dimension_measure_def` with the infimum over all sets of full
measure: the restriction to Borel sets does not change the infimum. -/
theorem ofReal_upperPackingDim_eq_iInf_packingDim_of_compl [SecondCountableTopology X]
    [OpensMeasurableSpace X] [IsFiniteMeasure μ]
    (hb : ∀ᵐ x ∂μ, (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≤ ·)
      fun r : ℝ => Real.log (μ.real (closedBall x r)) / Real.log r)
    (hbd : (ae μ).IsBoundedUnder (· ≤ ·) (upperLocalDim μ)) :
    ENNReal.ofReal (upperPackingDim μ) = ⨅ (A : Set X) (_ : μ Aᶜ = 0), packingDim A := by
  refine le_antisymm (le_iInf fun A => le_iInf fun hA =>
    ofReal_upperPackingDim_le_packingDim hA) ?_
  rw [ofReal_upperPackingDim_eq_iInf_packingDim hb hbd]
  exact le_iInf fun A => le_iInf fun _ => le_iInf fun hA => iInf_le_of_le A (iInf_le _ hA)

end UpperBound

section DimensionMeasureDef

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ ν : Measure E}

/-- The first line of `eq:dimension_measure_def` for a finite Borel measure `μ` on a
finite-dimensional real normed space:
`\overline{dim}_p(μ) = inf {dim_P A : A is a Borel set such that μ(Aᶜ) = 0}`. The infimum is
taken in `[0, ∞]`. The measure may be zero, in contrast to the second line. -/
theorem ofReal_upperPackingDim_eq_iInf_packingDim_of_finiteDimensional [IsFiniteMeasure μ] :
    ENNReal.ofReal (upperPackingDim μ)
      = ⨅ (A : Set E) (_ : MeasurableSet A) (_ : μ Aᶜ = 0), packingDim A :=
  ofReal_upperPackingDim_eq_iInf_packingDim ae_isBoundedUnder_le_log_div_log
    isBoundedUnder_upperLocalDim

/-- The first line of `eq:dimension_measure_def` with real values, for a finite Borel measure
on a finite-dimensional real normed space. -/
theorem upperPackingDim_eq_toReal_iInf_packingDim [IsFiniteMeasure μ] :
    upperPackingDim μ
      = (⨅ (A : Set E) (_ : MeasurableSet A) (_ : μ Aᶜ = 0), packingDim A).toReal := by
  rw [← ofReal_upperPackingDim_eq_iInf_packingDim_of_finiteDimensional,
    ENNReal.toReal_ofReal upperPackingDim_nonneg]

/-- For a finite Borel measure on a finite-dimensional real normed space and every `ε > 0`
there is a Borel set of full measure with packing dimension at most
`\overline{dim}_p(μ) + ε`; this is the choice of sets in tex lines 2553 to 2555. -/
theorem exists_packingDim_le [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Set E, MeasurableSet A ∧ μ Aᶜ = 0 ∧
      packingDim A ≤ ENNReal.ofReal (upperPackingDim μ + ε) :=
  exists_measurableSet_packingDim_le ae_isBoundedUnder_le_log_div_log
    isBoundedUnder_upperLocalDim (lt_add_of_pos_right _ hε)

/-- If `μ ≪ ν` for finite Borel measures on a finite-dimensional real normed space, then
`\overline{dim}_p(μ) ≤ \overline{dim}_p(ν)`: every set of full `ν`-measure has full
`μ`-measure. This is the argument of tex lines 2550 to 2553 for
`\overline{dim}_p(μ + ν) ≥ \overline{dim}_p(μ)`. -/
theorem upperPackingDim_le_of_absolutelyContinuous [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ ≪ ν) : upperPackingDim μ ≤ upperPackingDim ν := by
  have hle : ENNReal.ofReal (upperPackingDim μ) ≤ ENNReal.ofReal (upperPackingDim ν) := by
    rw [ofReal_upperPackingDim_eq_iInf_packingDim_of_finiteDimensional (μ := ν)]
    exact le_iInf fun A => le_iInf fun _ => le_iInf fun hA =>
      ofReal_upperPackingDim_le_packingDim (h hA)
  exact (ENNReal.ofReal_le_ofReal_iff upperPackingDim_nonneg).1 hle

/-- Tex lines 2674 to 2677: `\overline{dim}_p(μ + ν) ≥ \overline{dim}_p(μ)`, since
`μ ≪ μ + ν`. -/
example [IsFiniteMeasure μ] [IsFiniteMeasure ν] : upperPackingDim μ ≤ upperPackingDim (μ + ν) :=
  upperPackingDim_le_of_absolutelyContinuous (AbsolutelyContinuous.rfl.add_right ν)

end DimensionMeasureDef

section LineAndPlane

/-- The first line of `eq:dimension_measure_def` holds on the real line. -/
example {μ : Measure ℝ} [IsFiniteMeasure μ] :
    ENNReal.ofReal (upperPackingDim μ)
      = ⨅ (A : Set ℝ) (_ : MeasurableSet A) (_ : μ Aᶜ = 0), packingDim A :=
  ofReal_upperPackingDim_eq_iInf_packingDim_of_finiteDimensional

/-- The first line of `eq:dimension_measure_def` holds on the plane `ℝ × ℝ` with the supremum
metric. -/
example {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ] :
    ENNReal.ofReal (upperPackingDim μ)
      = ⨅ (A : Set (ℝ × ℝ)) (_ : MeasurableSet A) (_ : μ Aᶜ = 0), packingDim A :=
  ofReal_upperPackingDim_eq_iInf_packingDim_of_finiteDimensional

end LineAndPlane

end BoxLike
