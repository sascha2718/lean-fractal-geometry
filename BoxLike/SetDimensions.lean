module

/-
The Minkowski (box-counting) and packing dimensions of subsets of a metric space, to which
`sec:affinity_dim` (tex lines 2077 to 2077) refers through Falconer, Techniques in Fractal
Geometry, §2. The values lie in `ℝ≥0∞`, as for Mathlib's `dimH`.

The definitions and most lemmas are taken from the library `GeometricMeasureTheory`
(`Box/CoveringNumbers.lean`, `Box/BoxDimension.lean`, `Box/ModifiedBox.lean`), with the
namespace changed to `BoxLike`; the counting lemmas for separated pieces and
`upperBoxDim_le_lowerBoxDim_of_superMul` are new. The covering count is Mathlib's
`Metric.externalCoveringNumber r E`, the least number of closed balls of radius `r` with ambient
centres that cover `E`. The packing dimension is defined as the modified upper box dimension
`inf {sup_i \overline{\dim}_M E_i : E ⊆ ⋃_i E_i}` over countable covers by bounded sets;
`packing_modified_box` of `GeometricMeasureTheory` identifies it with the packing dimension
defined through packing measures on a metric space.

* `upperBoxDim`, `lowerBoxDim`: the upper and lower Minkowski dimensions, as critical exponents
  of the covering count.
* `upperBoxDim_le_of_forall`: a bound `N_r(E) ≤ C r^{-s}` at all small scales gives
  `\overline{\dim}_M E ≤ s`.
* `le_lowerBoxDim_of_forall`, `le_lowerBoxDim_of_geometric`: a bound `N_r(E) ≥ C r^{-s}` at all
  small scales, or along a geometric sequence of scales, gives `s ≤ \underline{\dim}_M E`.
* `lowerBoxDim_le_upperBoxDim`, `upperBoxDim_mono`, `lowerBoxDim_mono`, `upperBoxDim_empty`,
  `lowerBoxDim_empty`, `upperBoxDim_subsingleton`.
* `upperBoxDim_image_le`, `lowerBoxDim_image_le`, `upperBoxDim_image_eq`,
  `lowerBoxDim_image_eq`: Lipschitz images and bi-Lipschitz invariance.
* `upperBoxDim_closure`: the upper Minkowski dimension of the closure.
* `isBounded_of_upperBoxDim_ne_top`: a set of finite upper Minkowski dimension is bounded.
* `upperBoxDim_le_lowerBoxDim_of_superMul`: a super-multiplicative covering count,
  `N_τ(E) N_σ(E) ≤ N_{βτσ}(E)`, forces `\underline{\dim}_M E = \overline{\dim}_M E`.
* `exists_separated_finset`, `sum_externalCoveringNumber_le`,
  `externalCoveringNumber_image_le_of_lipschitzWith`: a separated set with `N_ε(E)` points,
  the count of pieces in disjoint balls, and the count of a Lipschitz image.
* `upperBoxDim_le_one`, `upperBoxDim_le_two`: a bounded set of real numbers has upper Minkowski
  dimension at most `1`, and a bounded set of the plane at most `2`.
* `dimH_le_lowerBoxDim`: `\dim_H E ≤ \underline{\dim}_M E`.
* `packingDim`, `packingDim_mono`, `packingDim_image_le`, `packingDim_image_eq`: the packing
  dimension, its monotonicity and its bi-Lipschitz invariance.
* `dimH_le_packingDim`, `packingDim_le_upperBoxDim`: `\dim_H E ≤ \dim_P E ≤ \overline{\dim}_M E`.
* `packingDim_eq_upperBoxDim`: a compact set whose relatively open pieces have full upper
  Minkowski dimension satisfies `\dim_P E = \overline{\dim}_M E`.
-/
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import Mathlib.Topology.MetricSpace.HausdorffDimension

@[expose] public section

open Filter Topology Set Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace BoxLike

variable {X : Type*} [PseudoMetricSpace X]

/-! ### The Minkowski dimensions -/

/-- `N_r(E) ≤ r^{-s}` for all sufficiently small `r`. -/
def UpperBoxDimLE (E : Set X) (s : ℝ) : Prop :=
  ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
    (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞) ≤ ENNReal.ofReal (r ^ (-s))

/-- `N_r(E) ≤ r^{-s}` for arbitrarily small `r`. -/
def LowerBoxDimLE (E : Set X) (s : ℝ) : Prop :=
  ∃ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
    (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞) ≤ ENNReal.ofReal (r ^ (-s))

/-- The upper Minkowski (box-counting) dimension `\overline{\dim}_M E` of tex lines 2077 to
2175: the least `s` with `N_r(E) ≤ r^{-s}` for all small `r`. -/
def upperBoxDim (E : Set X) : ℝ≥0∞ :=
  ⨅ (s : ℝ≥0) (_ : UpperBoxDimLE E (s : ℝ)), (s : ℝ≥0∞)

/-- The lower Minkowski (box-counting) dimension `\underline{\dim}_M E` of tex lines 2077 to
2175: the least `s` with `N_r(E) ≤ r^{-s}` for arbitrarily small `r`. The Minkowski dimension
`\dim_M E` exists when `lowerBoxDim E = upperBoxDim E`. -/
def lowerBoxDim (E : Set X) : ℝ≥0∞ :=
  ⨅ (s : ℝ≥0) (_ : LowerBoxDimLE E (s : ℝ)), (s : ℝ≥0∞)

/-! ### Small scales -/

/-- A fixed positive power of `r` is eventually below any positive constant as `r ↓ 0`. -/
private lemma eventually_rpow_lt {C : ℝ} (hC : 0 < C) {p : ℝ} (hp : 0 < p) :
    ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r ^ p < C := by
  have hδ : (0 : ℝ) < C ^ p⁻¹ := Real.rpow_pos_of_pos hC _
  filter_upwards [eventually_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with r hr0 hrδ
  have hr : (0 : ℝ) < r := hr0
  calc r ^ p < (C ^ p⁻¹) ^ p := Real.rpow_lt_rpow hr.le hrδ hp
    _ = C := by rw [← Real.rpow_mul hC.le, inv_mul_cancel₀ hp.ne', Real.rpow_one]

/-- Scaling the radius by a positive constant preserves the filter of small scales. -/
theorem tendsto_const_mul_nhdsGT_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun r : ℝ => c * r) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun r : ℝ => c * r) (𝓝 (0 : ℝ)) (𝓝 (c * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [eventually_mem_nhdsWithin] with r hr
    exact mul_pos hc hr

/-- Frequent occurrence at small scales is unchanged by scaling the radius. -/
theorem frequently_nhdsGT_zero_const_mul {c : ℝ} (hc : 0 < c) {P : ℝ → Prop}
    (h : ∃ᶠ r : ℝ in 𝓝[>] (0 : ℝ), P r) : ∃ᶠ r : ℝ in 𝓝[>] (0 : ℝ), P (c * r) := by
  refine (tendsto_const_mul_nhdsGT_zero (c := c⁻¹) (by positivity)).frequently
    (h.mono fun r hr => ?_)
  rwa [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

/-! ### The critical exponent -/

section Scales

variable {G : ℝ → ℝ≥0∞}

/-- A constant is absorbed by an arbitrarily small increase of the exponent. -/
private lemma eventually_imp_of_pos {s C ε : ℝ≥0} (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), ∀ x : ℝ≥0∞, x ≤ C * ENNReal.ofReal (r ^ (-(s : ℝ))) →
      x ≤ ENNReal.ofReal (r ^ (-((s + ε : ℝ≥0) : ℝ))) := by
  have hCpos : (0 : ℝ) < (C : ℝ) := hC
  filter_upwards [eventually_mem_nhdsWithin,
    eventually_rpow_lt (C := (C : ℝ)⁻¹) (by positivity) (show (0 : ℝ) < (ε : ℝ) from hε)]
    with r hr0 hr1 x hx
  have hp : (0 : ℝ) < r := hr0
  have hCle : (C : ℝ) * r ^ (ε : ℝ) ≤ 1 := by
    have h2 := mul_lt_mul_of_pos_left hr1 hCpos
    rw [mul_inv_cancel₀ hCpos.ne'] at h2
    exact h2.le
  have hadd : r ^ (-(s : ℝ)) = r ^ (-((s : ℝ) + (ε : ℝ))) * r ^ (ε : ℝ) := by
    rw [← Real.rpow_add hp]; congr 1; ring
  have hreal : (C : ℝ) * r ^ (-(s : ℝ)) ≤ r ^ (-((s : ℝ) + (ε : ℝ))) := by
    calc (C : ℝ) * r ^ (-(s : ℝ))
        = r ^ (-((s : ℝ) + (ε : ℝ))) * ((C : ℝ) * r ^ (ε : ℝ)) := by rw [hadd]; ring
      _ ≤ r ^ (-((s : ℝ) + (ε : ℝ))) * 1 :=
          mul_le_mul_of_nonneg_left hCle (Real.rpow_nonneg hp.le _)
      _ = r ^ (-((s : ℝ) + (ε : ℝ))) := mul_one _
  calc x ≤ (C : ℝ≥0∞) * ENNReal.ofReal (r ^ (-(s : ℝ))) := hx
    _ = ENNReal.ofReal ((C : ℝ) * r ^ (-(s : ℝ))) := by
        rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal]
    _ ≤ ENNReal.ofReal (r ^ (-((s : ℝ) + (ε : ℝ)))) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (r ^ (-((s + ε : ℝ≥0) : ℝ))) := by norm_cast

/-- A bound `G r ≤ C r^{-s}` at all small scales bounds the upper critical exponent by `s`. -/
private lemma iInf_le_of_eventually {s C : ℝ≥0} (hC : 0 < C)
    (h : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), G r ≤ C * ENNReal.ofReal (r ^ (-(s : ℝ)))) :
    ⨅ (t : ℝ≥0) (_ : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), G r ≤ ENNReal.ofReal (r ^ (-(t : ℝ)))),
      (t : ℝ≥0∞) ≤ s := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have key : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), G r ≤ ENNReal.ofReal (r ^ (-((s + ε : ℝ≥0) : ℝ))) := by
    filter_upwards [h, eventually_imp_of_pos hC hε] with r hr himp using himp _ hr
  exact (iInf₂_le (s + ε) key).trans_eq (by push_cast; ring)

/-- A bound `G r ≤ C r^{-s}` at arbitrarily small scales bounds the lower critical exponent by
`s`. -/
private lemma iInf_le_of_frequently {s C : ℝ≥0} (hC : 0 < C)
    (h : ∃ᶠ r : ℝ in 𝓝[>] (0 : ℝ), G r ≤ C * ENNReal.ofReal (r ^ (-(s : ℝ)))) :
    ⨅ (t : ℝ≥0) (_ : ∃ᶠ r : ℝ in 𝓝[>] (0 : ℝ), G r ≤ ENNReal.ofReal (r ^ (-(t : ℝ)))),
      (t : ℝ≥0∞) ≤ s := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have key : ∃ᶠ r : ℝ in 𝓝[>] (0 : ℝ), G r ≤ ENNReal.ofReal (r ^ (-((s + ε : ℝ≥0) : ℝ))) :=
    (h.and_eventually (eventually_imp_of_pos hC hε)).mono fun r hr => hr.2 _ hr.1
  exact (iInf₂_le (s + ε) key).trans_eq (by push_cast; ring)

/-- The constant `c^{-s}` that a change of radius by the factor `c` costs. -/
private lemma ofReal_const_mul_rpow {c r : ℝ} (hc : 0 < c) (hr : 0 < r) (s : ℝ) :
    ENNReal.ofReal ((c * r) ^ (-s)) =
      (((c ^ (-s)).toNNReal : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (r ^ (-s)) := by
  rw [show (((c ^ (-s)).toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (c ^ (-s)) from rfl,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _), ← Real.mul_rpow hc.le hr.le]

/-- Comparing two counting functions at radii differing by a fixed factor compares their upper
critical exponents. -/
private lemma iInf_le_iInf_of_le_scale {F H : ℝ → ℝ≥0∞} {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), F r ≤ H (c * r)) :
    (⨅ (t : ℝ≥0) (_ : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), F r ≤ ENNReal.ofReal (r ^ (-(t : ℝ)))),
        (t : ℝ≥0∞)) ≤
      ⨅ (t : ℝ≥0) (_ : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), H r ≤ ENNReal.ofReal (r ^ (-(t : ℝ)))),
        (t : ℝ≥0∞) := by
  refine le_iInf₂ fun s hs => ?_
  refine iInf_le_of_eventually (G := F)
    (C := (c ^ (-(s : ℝ))).toNNReal) (Real.toNNReal_pos.2 (Real.rpow_pos_of_pos hc _)) ?_
  filter_upwards [h, (tendsto_const_mul_nhdsGT_zero hc).eventually hs, eventually_mem_nhdsWithin]
    with r hr hs' hr0
  exact hr.trans (hs'.trans (ofReal_const_mul_rpow hc hr0 _).le)

/-- The version of `iInf_le_iInf_of_le_scale` for the lower critical exponent. -/
private lemma iInf_le_iInf_of_le_scale' {F H : ℝ → ℝ≥0∞} {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), F r ≤ H (c * r)) :
    (⨅ (t : ℝ≥0) (_ : ∃ᶠ r : ℝ in 𝓝[>] (0 : ℝ), F r ≤ ENNReal.ofReal (r ^ (-(t : ℝ)))),
        (t : ℝ≥0∞)) ≤
      ⨅ (t : ℝ≥0) (_ : ∃ᶠ r : ℝ in 𝓝[>] (0 : ℝ), H r ≤ ENNReal.ofReal (r ^ (-(t : ℝ)))),
        (t : ℝ≥0∞) := by
  refine le_iInf₂ fun s hs => ?_
  refine iInf_le_of_frequently (G := F)
    (C := (c ^ (-(s : ℝ))).toNNReal) (Real.toNNReal_pos.2 (Real.rpow_pos_of_pos hc _)) ?_
  refine ((frequently_nhdsGT_zero_const_mul hc hs).and_eventually
    (h.and eventually_mem_nhdsWithin)).mono fun r hr => ?_
  obtain ⟨h1, h2, hr0⟩ := hr
  exact h2.trans (h1.trans (ofReal_const_mul_rpow hc hr0 _).le)

end Scales

/-! ### First properties -/

/-- The counting bound bounds the upper Minkowski dimension. -/
theorem upperBoxDim_le_of_upperBoxDimLE {E : Set X} {s : ℝ≥0} (h : UpperBoxDimLE E (s : ℝ)) :
    upperBoxDim E ≤ s := iInf₂_le s h

/-- The counting bound bounds the lower Minkowski dimension. -/
theorem lowerBoxDim_le_of_lowerBoxDimLE {E : Set X} {s : ℝ≥0} (h : LowerBoxDimLE E (s : ℝ)) :
    lowerBoxDim E ≤ s := iInf₂_le s h

/-- `\underline{\dim}_M E ≤ \overline{\dim}_M E`. -/
theorem lowerBoxDim_le_upperBoxDim (E : Set X) : lowerBoxDim E ≤ upperBoxDim E :=
  le_iInf₂ fun _ hs => lowerBoxDim_le_of_lowerBoxDimLE hs.frequently

/-- The upper Minkowski dimension is at most `s` when `N_r(E) ≤ C r^{-s}` at every sufficiently
small scale. -/
theorem upperBoxDim_le_of_forall {E : Set X} {s : ℝ≥0} {C : ℝ≥0} (hC : 0 < C)
    (h : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞) ≤ C * ENNReal.ofReal (r ^ (-(s : ℝ)))) :
    upperBoxDim E ≤ s :=
  iInf_le_of_eventually (G := fun r : ℝ => (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞))
    hC h

/-- If the count of `F` at radius `r` is dominated by the count of `E` at radius `c r` for all
small `r`, then the upper Minkowski dimension of `F` is at most that of `E`. -/
theorem upperBoxDim_le_of_le_scale {Y : Type*} [PseudoMetricSpace Y] {F : Set Y} {E : Set X}
    {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), (Metric.externalCoveringNumber r.toNNReal F : ℝ≥0∞) ≤
      (Metric.externalCoveringNumber (c * r).toNNReal E : ℝ≥0∞)) :
    upperBoxDim F ≤ upperBoxDim E :=
  iInf_le_iInf_of_le_scale hc h

/-- If the count of `F` at radius `r` is dominated by the count of `E` at radius `c r` for all
small `r`, then the lower Minkowski dimension of `F` is at most that of `E`. -/
theorem lowerBoxDim_le_of_le_scale {Y : Type*} [PseudoMetricSpace Y] {F : Set Y} {E : Set X}
    {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), (Metric.externalCoveringNumber r.toNNReal F : ℝ≥0∞) ≤
      (Metric.externalCoveringNumber (c * r).toNNReal E : ℝ≥0∞)) :
    lowerBoxDim F ≤ lowerBoxDim E :=
  iInf_le_iInf_of_le_scale' hc h

/-- The upper Minkowski dimension is monotone. -/
theorem upperBoxDim_mono {E F : Set X} (h : E ⊆ F) : upperBoxDim E ≤ upperBoxDim F := by
  refine upperBoxDim_le_of_le_scale (c := 1) one_pos ?_
  filter_upwards with r
  rw [one_mul]
  exact ENat.toENNReal_le.2 (Metric.externalCoveringNumber_mono_set h)

/-- The lower Minkowski dimension is monotone. -/
theorem lowerBoxDim_mono {E F : Set X} (h : E ⊆ F) : lowerBoxDim E ≤ lowerBoxDim F := by
  refine lowerBoxDim_le_of_le_scale (c := 1) one_pos ?_
  filter_upwards with r
  rw [one_mul]
  exact ENat.toENNReal_le.2 (Metric.externalCoveringNumber_mono_set h)

/-- The empty set has upper Minkowski dimension zero. -/
@[simp]
theorem upperBoxDim_empty : upperBoxDim (∅ : Set X) = 0 := by
  refine le_antisymm ?_ (by simp)
  refine (upperBoxDim_le_of_upperBoxDimLE (s := 0) ?_).trans_eq (by simp)
  filter_upwards with r
  simp

/-- The empty set has lower Minkowski dimension zero. -/
@[simp]
theorem lowerBoxDim_empty : lowerBoxDim (∅ : Set X) = 0 :=
  le_antisymm ((lowerBoxDim_le_upperBoxDim _).trans_eq upperBoxDim_empty) bot_le

/-- A set with at most one point has upper Minkowski dimension zero. -/
theorem upperBoxDim_subsingleton {E : Set X} (hE : E.Subsingleton) : upperBoxDim E = 0 := by
  refine le_antisymm ?_ bot_le
  refine (upperBoxDim_le_of_upperBoxDimLE (s := 0) ?_).trans_eq (by simp)
  filter_upwards with r
  have h1 : Metric.externalCoveringNumber r.toNNReal E ≤ 1 := by
    rcases hE.eq_empty_or_singleton with rfl | ⟨x, rfl⟩
    · simp
    · simp
  calc (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞) ≤ ((1 : ℕ∞) : ℝ≥0∞) :=
        ENat.toENNReal_le.2 h1
    _ = ENNReal.ofReal (r ^ (-((0 : ℝ≥0) : ℝ))) := by simp

/-! ### Minimising covers, closures and Lipschitz images -/

/-- A finite `r`-cover of `E` whose cardinality is the covering number, when the latter is
finite. -/
theorem exists_isCover_encard_eq {r : ℝ≥0} {E : Set X}
    (h : Metric.externalCoveringNumber r E ≠ ⊤) :
    ∃ C : Set X, C.Finite ∧ Metric.IsCover r E C ∧
      C.encard = Metric.externalCoveringNumber r E := by
  simp only [Metric.externalCoveringNumber, ne_eq, iInf_eq_top, Set.encard_eq_top_iff, not_forall,
    Set.not_infinite] at h
  obtain ⟨C', hC'_cover, hC'_fin⟩ := h
  have : Nonempty { s : Set X // Metric.IsCover r E s } := ⟨C', hC'_cover⟩
  obtain ⟨C, hC⟩ :=
    ENat.exists_eq_iInf fun C : { s : Set X // Metric.IsCover r E s } => (C : Set X).encard
  refine ⟨C, ?_, C.2, ?_⟩
  · refine Set.encard_lt_top_iff.mp ?_
    simp only [hC, iInf_lt_top, Set.encard_lt_top_iff, Subtype.exists, exists_prop]
    exact ⟨C', hC'_cover, hC'_fin⟩
  · rw [hC, Metric.externalCoveringNumber]
    simp_rw [iInf_subtype]

/-- An `r`-cover of `E` is an `s`-cover of the closure of `E` for every `s > r`. -/
theorem isCover_closure_of_lt {r s : ℝ≥0} {E C : Set X} (hC : Metric.IsCover r E C) (hrs : r < s) :
    Metric.IsCover s (closure E) C := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ :=
    EMetric.mem_closure_iff.1 hx ((s - r : ℝ≥0) : ℝ≥0∞) (by
      simpa using tsub_pos_of_lt hrs)
  obtain ⟨c, hcC, hyc⟩ := hC hy
  replace hyc : edist y c ≤ (r : ℝ≥0∞) := hyc
  refine ⟨c, hcC, show edist x c ≤ (s : ℝ≥0∞) from ?_⟩
  calc edist x c ≤ edist x y + edist y c := edist_triangle _ _ _
    _ ≤ ((s - r : ℝ≥0) : ℝ≥0∞) + (r : ℝ≥0∞) := add_le_add hxy.le hyc
    _ = (s : ℝ≥0∞) := by
        rw [← ENNReal.coe_add, tsub_add_cancel_of_le hrs.le]

/-- Taking the closure costs only an arbitrarily small enlargement of the radius. -/
theorem externalCoveringNumber_closure_le {r s : ℝ≥0} (hrs : r < s) (E : Set X) :
    Metric.externalCoveringNumber s (closure E) ≤ Metric.externalCoveringNumber r E :=
  le_iInf₂ fun _ hC => (isCover_closure_of_lt hC hrs).externalCoveringNumber_le_encard

/-- The upper Minkowski dimension of the closure of a set is that of the set. -/
theorem upperBoxDim_closure (E : Set X) : upperBoxDim (closure E) = upperBoxDim E := by
  refine le_antisymm (upperBoxDim_le_of_le_scale (c := 1 / 2) (by norm_num) ?_)
    (upperBoxDim_mono subset_closure)
  filter_upwards [eventually_mem_nhdsWithin] with r hr0
  have hp : (0 : ℝ) < r := hr0
  refine ENat.toENNReal_le.2 (externalCoveringNumber_closure_le ?_ E)
  rw [Real.toNNReal_lt_toNNReal_iff hp]
  linarith

/-- An `L`-Lipschitz image needs at most `N_r(E)` balls of radius `2Lr`: the factor of two
moves the centres of a minimising cover into `E`, where the Lipschitz bound applies. -/
theorem externalCoveringNumber_image_le {Y : Type*} [PseudoMetricSpace Y] {f : X → Y} {L : ℝ≥0}
    {E : Set X} (hf : LipschitzOnWith L f E) (r : ℝ≥0) :
    Metric.externalCoveringNumber (2 * L * r) (f '' E) ≤ Metric.externalCoveringNumber r E := by
  refine le_trans ?_ (Metric.coveringNumber_two_mul_le_externalCoveringNumber r E)
  simp only [Metric.coveringNumber, le_iInf_iff]
  intro C hCE hC
  refine le_trans (Metric.IsCover.externalCoveringNumber_le_encard ?_) (Set.encard_image_le f C)
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨c, hcC, hxc⟩ := hC hx
  replace hxc : edist x c ≤ ((2 * r : ℝ≥0) : ℝ≥0∞) := hxc
  refine ⟨f c, ⟨c, hcC, rfl⟩,
    show edist (f x) (f c) ≤ ((2 * L * r : ℝ≥0) : ℝ≥0∞) from ?_⟩
  calc edist (f x) (f c) ≤ (L : ℝ≥0∞) * edist x c := hf hx (hCE hcC)
    _ ≤ (L : ℝ≥0∞) * ((2 * r : ℝ≥0) : ℝ≥0∞) := by gcongr
    _ = ((2 * L * r : ℝ≥0) : ℝ≥0∞) := by push_cast; ring

/-- A Lipschitz image needs no more balls at radius `r` than the set does at radius
`r / (2(L + 1))`. -/
private lemma externalCoveringNumber_image_scale {Y : Type*} [PseudoMetricSpace Y] {f : X → Y}
    {L : ℝ≥0} {E : Set X} (hf : LipschitzOnWith L f E) :
    ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      (Metric.externalCoveringNumber r.toNNReal (f '' E) : ℝ≥0∞) ≤
        (Metric.externalCoveringNumber ((((2 * (L + 1))⁻¹ : ℝ≥0) : ℝ) * r).toNNReal E : ℝ≥0∞) := by
  have hK : (0 : ℝ≥0) < 2 * (L + 1) := by positivity
  have hf' : LipschitzOnWith (L + 1) f E := hf.weaken (by simp)
  filter_upwards with r
  refine ENat.toENNReal_le.2 ?_
  have hmul : 2 * (L + 1) * (((((2 * (L + 1))⁻¹ : ℝ≥0) : ℝ)) * r).toNNReal = r.toNNReal := by
    rw [Real.toNNReal_mul (NNReal.coe_nonneg _), Real.toNNReal_coe, ← mul_assoc,
      mul_inv_cancel₀ hK.ne', one_mul]
  calc Metric.externalCoveringNumber r.toNNReal (f '' E)
      = Metric.externalCoveringNumber
          (2 * (L + 1) * (((((2 * (L + 1))⁻¹ : ℝ≥0) : ℝ)) * r).toNNReal) (f '' E) := by rw [hmul]
    _ ≤ Metric.externalCoveringNumber ((((2 * (L + 1))⁻¹ : ℝ≥0) : ℝ) * r).toNNReal E :=
        externalCoveringNumber_image_le hf' _

/-- The upper Minkowski dimension does not increase under a Lipschitz map. -/
theorem upperBoxDim_image_le {Y : Type*} [PseudoMetricSpace Y] {f : X → Y} {L : ℝ≥0} {E : Set X}
    (hf : LipschitzOnWith L f E) : upperBoxDim (f '' E) ≤ upperBoxDim E := by
  refine upperBoxDim_le_of_le_scale (c := (((2 * (L + 1))⁻¹ : ℝ≥0) : ℝ)) ?_
    (externalCoveringNumber_image_scale hf)
  rw [NNReal.coe_pos]
  exact inv_pos.2 (by positivity)

/-- The lower Minkowski dimension does not increase under a Lipschitz map. -/
theorem lowerBoxDim_image_le {Y : Type*} [PseudoMetricSpace Y] {f : X → Y} {L : ℝ≥0} {E : Set X}
    (hf : LipschitzOnWith L f E) : lowerBoxDim (f '' E) ≤ lowerBoxDim E := by
  refine lowerBoxDim_le_of_le_scale (c := (((2 * (L + 1))⁻¹ : ℝ≥0) : ℝ)) ?_
    (externalCoveringNumber_image_scale hf)
  rw [NNReal.coe_pos]
  exact inv_pos.2 (by positivity)

/-- Bi-Lipschitz invariance of the upper Minkowski dimension: `f` is Lipschitz on `E` and has a
left inverse `g` that is Lipschitz on `f(E)`. -/
theorem upperBoxDim_image_eq {Y : Type*} [PseudoMetricSpace Y] {f : X → Y} {g : Y → X}
    {K L : ℝ≥0} {E : Set X} (hf : LipschitzOnWith L f E) (hg : LipschitzOnWith K g (f '' E))
    (hgf : ∀ x ∈ E, g (f x) = x) : upperBoxDim (f '' E) = upperBoxDim E := by
  refine le_antisymm (upperBoxDim_image_le hf) ?_
  have hE : g '' (f '' E) = E := by
    rw [Set.image_image]
    exact (Set.image_congr hgf).trans (Set.image_id E)
  calc upperBoxDim E = upperBoxDim (g '' (f '' E)) := by rw [hE]
    _ ≤ upperBoxDim (f '' E) := upperBoxDim_image_le hg

/-- Bi-Lipschitz invariance of the lower Minkowski dimension. -/
theorem lowerBoxDim_image_eq {Y : Type*} [PseudoMetricSpace Y] {f : X → Y} {g : Y → X}
    {K L : ℝ≥0} {E : Set X} (hf : LipschitzOnWith L f E) (hg : LipschitzOnWith K g (f '' E))
    (hgf : ∀ x ∈ E, g (f x) = x) : lowerBoxDim (f '' E) = lowerBoxDim E := by
  refine le_antisymm (lowerBoxDim_image_le hf) ?_
  have hE : g '' (f '' E) = E := by
    rw [Set.image_image]
    exact (Set.image_congr hgf).trans (Set.image_id E)
  calc lowerBoxDim E = lowerBoxDim (g '' (f '' E)) := by rw [hE]
    _ ≤ lowerBoxDim (f '' E) := lowerBoxDim_image_le hg

/-- A set of finite upper Minkowski dimension is bounded: it has a finite cover by closed balls
of one radius. -/
theorem isBounded_of_upperBoxDim_ne_top {E : Set X} (h : upperBoxDim E ≠ ⊤) :
    Bornology.IsBounded E := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, UpperBoxDimLE E (t : ℝ) := by
    by_contra hcon
    rw [not_exists] at hcon
    exact h (eq_top_iff.2 (le_iInf₂ fun s hs => absurd hs (hcon s)))
  obtain ⟨r, hr, hr0⟩ := (ht.and eventually_mem_nhdsWithin).exists
  have hr0' : (0 : ℝ) < r := hr0
  have htop : Metric.externalCoveringNumber r.toNNReal E ≠ ⊤ := by
    intro h'
    rw [h', ENat.toENNReal_top, top_le_iff] at hr
    exact ENNReal.ofReal_ne_top hr
  obtain ⟨C, hCfin, hC, -⟩ := exists_isCover_encard_eq htop
  have hsub := hC.subset_iUnion_closedBall
  rw [Real.coe_toNNReal r hr0'.le] at hsub
  exact ((Bornology.isBounded_biUnion hCfin).2 fun c _ => Metric.isBounded_closedBall).subset hsub

/-! ### Lower bounds for the lower Minkowski dimension -/

/-- A lower bound `C r^{-s} ≤ G r` and an upper bound `G r ≤ r^{-t}` at arbitrarily small
common scales force `s ≤ t`. -/
private lemma le_of_frequently_le {G : ℝ → ℝ≥0∞} {s t C : ℝ≥0} (hC : 0 < C)
    (h : ∃ᶠ r : ℝ in 𝓝[>] (0 : ℝ), (C : ℝ≥0∞) * ENNReal.ofReal (r ^ (-(s : ℝ))) ≤ G r ∧
      G r ≤ ENNReal.ofReal (r ^ (-(t : ℝ)))) : s ≤ t := by
  by_contra hts
  rw [not_le] at hts
  have hst : (0 : ℝ) < (s : ℝ) - (t : ℝ) := by
    have h' : (t : ℝ) < (s : ℝ) := hts
    linarith
  obtain ⟨r, ⟨h1, h2⟩, hr0, hr1⟩ :=
    (h.and_eventually (eventually_mem_nhdsWithin.and
      (eventually_rpow_lt (C := (C : ℝ)) hC hst))).exists
  have hp : (0 : ℝ) < r := hr0
  have hreal : (C : ℝ) * r ^ (-(s : ℝ)) ≤ r ^ (-(t : ℝ)) := by
    have h3 := h1.trans h2
    rwa [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg,
      ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hp.le _)] at h3
  have hadd : r ^ (-(t : ℝ)) = r ^ ((s : ℝ) - (t : ℝ)) * r ^ (-(s : ℝ)) := by
    rw [← Real.rpow_add hp]; congr 1; ring
  rw [hadd] at hreal
  have hle := le_of_mul_le_mul_right hreal (Real.rpow_pos_of_pos hp (-(s : ℝ)))
  linarith

/-- A bound `C r^{-s} ≤ G r` at all small scales bounds the lower critical exponent from
below. -/
private lemma le_iInf_of_eventually {G : ℝ → ℝ≥0∞} {s C : ℝ≥0} (hC : 0 < C)
    (h : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), (C : ℝ≥0∞) * ENNReal.ofReal (r ^ (-(s : ℝ))) ≤ G r) :
    (s : ℝ≥0∞) ≤
      ⨅ (t : ℝ≥0) (_ : ∃ᶠ r : ℝ in 𝓝[>] (0 : ℝ), G r ≤ ENNReal.ofReal (r ^ (-(t : ℝ)))),
        (t : ℝ≥0∞) := by
  refine le_iInf₂ fun t ht => ?_
  exact_mod_cast le_of_frequently_le hC ((ht.and_eventually h).mono fun r hr => ⟨hr.2, hr.1⟩)

/-- A lower bound `N_r(E) ≥ C r^{-s}` at all small scales gives `s ≤ \underline{\dim}_M E`. -/
theorem le_lowerBoxDim_of_forall {E : Set X} {s : ℝ≥0} {C : ℝ≥0} (hC : 0 < C)
    (h : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      C * ENNReal.ofReal (r ^ (-(s : ℝ))) ≤ (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞)) :
    (s : ℝ≥0∞) ≤ lowerBoxDim E :=
  le_iInf_of_eventually (G := fun r : ℝ => (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞))
    hC h

/-- For `0 < c < 1`, every `r < c^k` lies between two consecutive powers of `c` with exponent at
least `k`. -/
private lemma exists_pow_le_le_pow {c : ℝ} (hc₀ : 0 < c) (hc : c < 1) {r : ℝ} (hr : 0 < r)
    {k : ℕ} (hrk : r < c ^ k) : ∃ n : ℕ, k ≤ n ∧ c ^ (n + 1) ≤ r ∧ r ≤ c ^ n := by
  classical
  have hex : ∃ m : ℕ, c ^ (m + 1) ≤ r := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hr hc
    exact ⟨m, (pow_le_pow_of_le_one hc₀.le hc.le (Nat.le_succ m)).trans hm.le⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, ?_⟩
  · refine le_of_not_gt fun hlt => ?_
    exact absurd ((pow_le_pow_of_le_one hc₀.le hc.le hlt).trans (Nat.find_spec hex))
      (not_le.2 hrk)
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
    · rw [h0, pow_zero]
      exact (hrk.trans_le (pow_le_one₀ hc₀.le hc.le)).le
    · have hmin := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
      rw [not_le, show Nat.find hex - 1 + 1 = Nat.find hex by omega] at hmin
      exact hmin.le

/-- A lower bound for the covering count along a geometric sequence of scales bounds the lower
Minkowski dimension from below; monotonicity of the count in the radius controls the
intermediate scales. -/
theorem le_lowerBoxDim_of_geometric {E : Set X} {c : ℝ} (hc₀ : 0 < c) (hc : c < 1) {s C : ℝ≥0}
    (hC : 0 < C)
    (h : ∀ᶠ n : ℕ in atTop, C * ENNReal.ofReal ((c ^ n) ^ (-(s : ℝ))) ≤
      (Metric.externalCoveringNumber (c ^ n).toNNReal E : ℝ≥0∞)) :
    (s : ℝ≥0∞) ≤ lowerBoxDim E := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 h
  have hconst : ((C * (c ^ (s : ℝ)).toNNReal : ℝ≥0) : ℝ≥0∞)
      = (C : ℝ≥0∞) * ENNReal.ofReal (c ^ (s : ℝ)) := by rw [ENNReal.coe_mul]; rfl
  have hcc : c ^ (s : ℝ) * c ^ (-(s : ℝ)) = 1 := by rw [← Real.rpow_add hc₀]; simp
  refine le_lowerBoxDim_of_forall (C := C * (c ^ (s : ℝ)).toNNReal)
    (mul_pos hC (Real.toNNReal_pos.2 (Real.rpow_pos_of_pos hc₀ _))) ?_
  filter_upwards [eventually_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (pow_pos hc₀ n₀))] with r hr0 hrlt
  have hr : (0 : ℝ) < r := hr0
  obtain ⟨n, hkn, h1, h2⟩ := exists_pow_le_le_pow hc₀ hc hr (show r < c ^ n₀ from hrlt)
  have hsplit : (c ^ (n + 1)) ^ (-(s : ℝ)) = (c ^ n) ^ (-(s : ℝ)) * c ^ (-(s : ℝ)) := by
    rw [pow_succ, Real.mul_rpow (pow_pos hc₀ n).le hc₀.le]
  have hstep : c ^ (s : ℝ) * r ^ (-(s : ℝ)) ≤ (c ^ n) ^ (-(s : ℝ)) := by
    have hle : r ^ (-(s : ℝ)) ≤ (c ^ (n + 1)) ^ (-(s : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (pow_pos hc₀ (n + 1)) h1 (neg_nonpos.2 s.coe_nonneg)
    calc c ^ (s : ℝ) * r ^ (-(s : ℝ))
        ≤ c ^ (s : ℝ) * ((c ^ n) ^ (-(s : ℝ)) * c ^ (-(s : ℝ))) := by
          rw [← hsplit]
          exact mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hc₀.le _)
      _ = (c ^ n) ^ (-(s : ℝ)) * (c ^ (s : ℝ) * c ^ (-(s : ℝ))) := by ring
      _ = (c ^ n) ^ (-(s : ℝ)) := by rw [hcc, mul_one]
  calc ((C * (c ^ (s : ℝ)).toNNReal : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (r ^ (-(s : ℝ)))
      = (C : ℝ≥0∞) * ENNReal.ofReal (c ^ (s : ℝ) * r ^ (-(s : ℝ))) := by
        rw [hconst, ENNReal.ofReal_mul (Real.rpow_nonneg hc₀.le _), mul_assoc]
    _ ≤ (C : ℝ≥0∞) * ENNReal.ofReal ((c ^ n) ^ (-(s : ℝ))) :=
        mul_le_mul_right (ENNReal.ofReal_le_ofReal hstep) _
    _ ≤ (Metric.externalCoveringNumber (c ^ n).toNNReal E : ℝ≥0∞) := hn₀ n hkn
    _ ≤ (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞) :=
        ENat.toENNReal_le.2 (Metric.externalCoveringNumber_anti (Real.toNNReal_mono h2))

/-- A super-multiplicative covering count has a Minkowski dimension: if
`N_τ(E) N_σ(E) ≤ N_{βτσ}(E)` for all `τ, σ ∈ (0, 1)`, then
`\overline{\dim}_M E ≤ \underline{\dim}_M E`. Given `t'' < t < \overline{\dim}_M E`, a scale
`τ` with `N_τ(E) > τ^{-t}` gives `N_{(βτ)^k}(E) ≥ N_τ(E)^k ≥ (βτ)^{-k t''}` once `τ` is small. -/
theorem upperBoxDim_le_lowerBoxDim_of_superMul {E : Set X} (hne : E.Nonempty) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (h : ∀ τ σ : ℝ, 0 < τ → τ < 1 → 0 < σ → σ ≤ 1 →
      (Metric.externalCoveringNumber τ.toNNReal E : ℝ≥0∞) *
          Metric.externalCoveringNumber σ.toNNReal E ≤
        Metric.externalCoveringNumber (β * τ * σ).toNNReal E) :
    upperBoxDim E ≤ lowerBoxDim E := by
  set F : ℝ → ℝ≥0∞ := fun r => (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞) with hF
  refine ENNReal.le_of_forall_nnreal_lt fun t'' ht'' => ?_
  obtain ⟨t, ht''t, htU⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht''
  have hnot : ¬ UpperBoxDimLE E (t : ℝ) := fun hle =>
    (not_le.2 htU) (upperBoxDim_le_of_upperBoxDimLE hle)
  have hfreq : ∃ᶠ r : ℝ in 𝓝[>] (0 : ℝ), ENNReal.ofReal (r ^ (-(t : ℝ))) < F r := by
    simpa [UpperBoxDimLE, Filter.not_eventually, not_le] using hnot
  have htt : (0 : ℝ) < (t : ℝ) - (t'' : ℝ) :=
    sub_pos.2 (by exact_mod_cast (ENNReal.coe_lt_coe.1 ht''t))
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  obtain ⟨τ, hτF, hτ0, hτ1, hτβ⟩ := (hfreq.and_eventually (eventually_mem_nhdsWithin.and
      (hsmall.and
        (eventually_rpow_lt (C := β ^ (t'' : ℝ)) (Real.rpow_pos_of_pos hβ0 _) htt)))).exists
  have hτ : (0 : ℝ) < τ := hτ0
  have hτ1' : τ < 1 := hτ1
  set c := β * τ with hc
  have hc0 : 0 < c := mul_pos hβ0 hτ
  have hc1 : c < 1 := by nlinarith
  -- `N_τ(E)^k ≤ N_{c^k}(E)`
  have hpow : ∀ k : ℕ, F τ ^ k ≤ F (c ^ k) := by
    intro k
    induction k with
    | zero =>
      have h1 : 1 ≤ Metric.externalCoveringNumber (1 : ℝ).toNNReal E :=
        Order.one_le_iff_pos.2 (Metric.externalCoveringNumber_pos_iff.2 hne)
      simpa [F] using ENat.toENNReal_le.2 h1
    | succ k ih =>
      calc F τ ^ (k + 1) = F τ * F τ ^ k := pow_succ' _ _
        _ ≤ F τ * F (c ^ k) := by gcongr
        _ ≤ F (β * τ * c ^ k) := h τ (c ^ k) hτ hτ1' (pow_pos hc0 k) (pow_le_one₀ hc0.le hc1.le)
        _ = F (c ^ (k + 1)) := by rw [pow_succ', hc]
  -- `(βτ)^{-t''} ≤ τ^{-t}`
  have hbase : c ^ (-(t'' : ℝ)) ≤ τ ^ (-(t : ℝ)) := by
    have hτt : τ ^ (-(t : ℝ)) = (τ ^ ((t : ℝ) - (t'' : ℝ)))⁻¹ * τ ^ (-(t'' : ℝ)) := by
      rw [← Real.rpow_neg hτ.le, ← Real.rpow_add hτ]; congr 1; ring
    have hβt : β ^ (-(t'' : ℝ)) ≤ (τ ^ ((t : ℝ) - (t'' : ℝ)))⁻¹ := by
      rw [Real.rpow_neg hβ0.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hτ _) hτβ.le
    rw [hc, Real.mul_rpow hβ0.le hτ.le, hτt]
    exact mul_le_mul_of_nonneg_right hβt (Real.rpow_nonneg hτ.le _)
  refine le_lowerBoxDim_of_geometric hc0 hc1 one_pos (Eventually.of_forall fun n => ?_)
  calc ((1 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal ((c ^ n) ^ (-(t'' : ℝ)))
      = ENNReal.ofReal (c ^ (-(t'' : ℝ))) ^ n := by
        rw [ENNReal.coe_one, one_mul, ← ENNReal.ofReal_pow (Real.rpow_nonneg hc0.le _),
          ← Real.rpow_natCast, ← Real.rpow_mul hc0.le, ← Real.rpow_natCast,
          ← Real.rpow_mul hc0.le, mul_comm]
    _ ≤ ENNReal.ofReal (τ ^ (-(t : ℝ))) ^ n := by gcongr
    _ ≤ F τ ^ n := by gcongr
    _ ≤ F (c ^ n) := hpow n

/-! ### Covering counts of separated pieces and of Lipschitz images -/

/-- A totally bounded set has finite covering numbers at every positive radius. -/
theorem externalCoveringNumber_ne_top {E : Set X} (hE : TotallyBounded E) {r : ℝ≥0}
    (hr : 0 < r) : Metric.externalCoveringNumber r E ≠ ⊤ := by
  obtain ⟨N, -, hN, hcov⟩ := Metric.exists_finite_isCover_of_totallyBounded hr.ne' hE
  exact (hcov.externalCoveringNumber_le_encard.trans_lt hN.encard_lt_top).ne

/-- A totally bounded set has finite packing numbers at every positive radius. -/
theorem packingNumber_ne_top {E : Set X} (hE : TotallyBounded E) {r : ℝ≥0} (hr : 0 < r) :
    Metric.packingNumber r E ≠ ⊤ := by
  have h := Metric.packingNumber_two_mul_le_externalCoveringNumber (r / 2) E
  rw [mul_div_cancel₀ _ two_ne_zero] at h
  exact (h.trans_lt (lt_top_iff_ne_top.2 (externalCoveringNumber_ne_top hE (by positivity)))).ne

/-- A totally bounded set contains a finite `ε`-separated set with at least `N_ε(E)` points: a
maximal separated set is a cover. -/
theorem exists_separated_finset {E : Set X} (hE : TotallyBounded E) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ C : Finset X, (C : Set X) ⊆ E ∧
      (∀ y ∈ C, ∀ y' ∈ C, y ≠ y' → (ε : ℝ≥0∞) < edist y y') ∧
      Metric.externalCoveringNumber ε E ≤ C.card := by
  have htop := packingNumber_ne_top hE hε
  have hfin : (Metric.maximalSeparatedSet ε E).Finite := by
    rw [← Set.encard_ne_top_iff, Metric.encard_maximalSeparatedSet htop]
    exact htop
  refine ⟨hfin.toFinset, by simpa using Metric.maximalSeparatedSet_subset, fun y hy y' hy' hne =>
    Metric.isSeparated_maximalSeparatedSet (by simpa using hy) (by simpa using hy') hne, ?_⟩
  refine (Metric.isCover_maximalSeparatedSet htop).externalCoveringNumber_le_encard.trans_eq ?_
  rw [hfin.encard_eq_coe_toFinset_card]

/-- Pieces `P_y ⊆ E` inside the balls of radius `ρ` about the points of a `4ρ`-separated set
need, in total, at most `N_ε(E)` balls of radius `ε ≤ ρ`: a ball of radius `ε` meets at most
one piece. -/
theorem sum_externalCoveringNumber_le {E : Set X} {ρ ε : ℝ≥0} (hερ : ε ≤ ρ) (C : Finset X)
    (hC : ∀ y ∈ C, ∀ y' ∈ C, y ≠ y' → 4 * (ρ : ℝ≥0∞) < edist y y') (P : X → Set X)
    (hP : ∀ y ∈ C, ∀ x ∈ P y, x ∈ E ∧ edist x y ≤ ρ) :
    ∑ y ∈ C, Metric.externalCoveringNumber ε (P y) ≤ Metric.externalCoveringNumber ε E := by
  classical
  rcases eq_or_ne (Metric.externalCoveringNumber ε E) ⊤ with htop | htop
  · rw [htop]; exact le_top
  obtain ⟨D, hDfin, hDcov, hDcard⟩ := exists_isCover_encard_eq htop
  set T : X → Finset X := fun y => hDfin.toFinset.filter fun d => ∃ x ∈ P y, edist x d ≤ ε
    with hT
  have hcov : ∀ y ∈ C, Metric.externalCoveringNumber ε (P y) ≤ (T y).card := by
    intro y hy
    have hc : Metric.IsCover ε (P y) (T y : Set X) := by
      intro x hx
      obtain ⟨d, hd, hxd⟩ := hDcov (hP y hy x hx).1
      replace hxd : edist x d ≤ (ε : ℝ≥0∞) := hxd
      exact ⟨d, Finset.mem_filter.2 ⟨hDfin.mem_toFinset.2 hd, x, hx, hxd⟩, hxd⟩
    exact hc.externalCoveringNumber_le_encard.trans_eq (Set.encard_coe_eq_coe_finsetCard _)
  have hdisj : (C : Set X).PairwiseDisjoint T := by
    intro y hy y' hy' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro d hd hd'
    obtain ⟨x, hx, hxd⟩ := (Finset.mem_filter.1 hd).2
    obtain ⟨x', hx', hxd'⟩ := (Finset.mem_filter.1 hd').2
    have h1 := (hP y hy x hx).2
    have h2 := (hP y' hy' x' hx').2
    have hle : edist y y' ≤ 4 * (ρ : ℝ≥0∞) :=
      calc edist y y' ≤ edist y x + edist x d + edist d x' + edist x' y' := by
            refine (edist_triangle y x' y').trans ?_
            gcongr
            exact edist_triangle4 y x d x'
        _ ≤ ρ + ρ + ρ + ρ := by
            have e1 : edist y x ≤ ρ := by rw [edist_comm]; exact h1
            have e2 : edist x d ≤ ρ := hxd.trans (by exact_mod_cast hερ)
            have e3 : edist d x' ≤ ρ := by
              rw [edist_comm]; exact hxd'.trans (by exact_mod_cast hερ)
            exact add_le_add (add_le_add (add_le_add e1 e2) e3) h2
        _ = 4 * (ρ : ℝ≥0∞) := by ring
    exact (not_lt.2 hle) (hC y hy y' hy' hne)
  calc ∑ y ∈ C, Metric.externalCoveringNumber ε (P y)
      ≤ ∑ y ∈ C, ((T y).card : ℕ∞) := Finset.sum_le_sum hcov
    _ = ((C.biUnion T).card : ℕ∞) := by rw [Finset.card_biUnion hdisj]; push_cast; rfl
    _ ≤ (hDfin.toFinset.card : ℕ∞) := by
        gcongr
        exact Finset.biUnion_subset.2 fun y _ => Finset.filter_subset _ _
    _ = Metric.externalCoveringNumber ε E := by
        rw [← hDcard, hDfin.encard_eq_coe_toFinset_card]

/-- A `K`-Lipschitz image needs at most `N_ε(A)` balls of radius `Kε`. -/
theorem externalCoveringNumber_image_le_of_lipschitzWith {Y : Type*} [PseudoMetricSpace Y]
    {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) (ε : ℝ≥0) (A : Set X) :
    Metric.externalCoveringNumber (K * ε) (f '' A) ≤ Metric.externalCoveringNumber ε A := by
  refine le_iInf₂ fun C hC => ?_
  refine le_trans (Metric.IsCover.externalCoveringNumber_le_encard ?_) (Set.encard_image_le f C)
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨c, hcC, hxc⟩ := hC hx
  replace hxc : edist x c ≤ (ε : ℝ≥0∞) := hxc
  refine ⟨f c, ⟨c, hcC, rfl⟩, show edist (f x) (f c) ≤ ((K * ε : ℝ≥0) : ℝ≥0∞) from ?_⟩
  calc edist (f x) (f c) ≤ K * edist x c := hf x c
    _ ≤ K * ε := by gcongr
    _ = ((K * ε : ℝ≥0) : ℝ≥0∞) := by push_cast; rfl

/-! ### Sets of real numbers and planar sets -/

/-- The centres `a + (2k + 1) r`, `0 ≤ k ≤ ⌊(b - a) / (2r)⌋`, of a subdivision of `[a, b]` into
intervals of length `2r`. -/
def gridCentres (a b r : ℝ) : Set ℝ :=
  (fun k : ℕ => a + (2 * (k : ℝ) + 1) * r) '' ↑(Finset.range (⌊(b - a) / (2 * r)⌋₊ + 1))

/-- The closed balls of radius `r` about the centres of the subdivision cover `[a, b]`. -/
theorem isCover_gridCentres {a b r : ℝ} (hr : 0 < r) :
    Metric.IsCover r.toNNReal (Icc a b) (gridCentres a b r) := by
  have h2r : (0 : ℝ) < 2 * r := by linarith
  refine Metric.IsCover.of_subset_iUnion_closedBall ?_
  rintro x ⟨hxa, hxb⟩
  have hx0 : (0 : ℝ) ≤ (x - a) / (2 * r) := div_nonneg (by linarith) h2r.le
  have hk1 : ((⌊(x - a) / (2 * r)⌋₊ : ℕ) : ℝ) * (2 * r) ≤ x - a :=
    (le_div_iff₀ h2r).1 (Nat.floor_le hx0)
  have hk2 : x - a < (((⌊(x - a) / (2 * r)⌋₊ : ℕ) : ℝ) + 1) * (2 * r) :=
    (div_lt_iff₀ h2r).1 (Nat.lt_floor_add_one _)
  refine Set.mem_biUnion (Set.mem_image_of_mem _ (?_ : (⌊(x - a) / (2 * r)⌋₊ : ℕ) ∈
    (↑(Finset.range (⌊(b - a) / (2 * r)⌋₊ + 1)) : Set ℕ))) ?_
  · simp only [Finset.coe_range, Set.mem_Iio, Nat.lt_succ_iff]
    exact Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) h2r.le)
  · rw [Metric.mem_closedBall, Real.dist_eq, Real.coe_toNNReal r hr.le, abs_le]
    constructor <;> nlinarith

/-- The subdivision has at most `⌊(b - a) / (2r)⌋ + 1` centres. -/
theorem encard_gridCentres_le (a b r : ℝ) :
    (gridCentres a b r).encard ≤ ((⌊(b - a) / (2 * r)⌋₊ + 1 : ℕ) : ℕ∞) := by
  refine (Set.encard_image_le _ _).trans ?_
  rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_range]

/-- `⌊(b - a) / (2r)⌋ + 1 ≤ ((b - a)/2 + 1) r⁻¹` for `0 < r < 1` and `a ≤ b`. -/
theorem natFloor_add_one_le {a b r : ℝ} (hab : a ≤ b) (hr : 0 < r) (hr1 : r < 1) :
    ((⌊(b - a) / (2 * r)⌋₊ : ℕ) : ℝ) + 1 ≤ ((b - a) / 2 + 1) * r⁻¹ := by
  have hba : (0 : ℝ) ≤ b - a := by linarith
  have h2r : (0 : ℝ) < 2 * r := by linarith
  have h1 : ((⌊(b - a) / (2 * r)⌋₊ : ℕ) : ℝ) ≤ (b - a) / 2 * r⁻¹ := by
    refine (Nat.floor_le (div_nonneg hba h2r.le)).trans (le_of_eq ?_)
    field_simp
  have hinv : (0 : ℝ) < r⁻¹ := inv_pos.2 hr
  have h2 : (1 : ℝ) ≤ r⁻¹ := by nlinarith [mul_inv_cancel₀ hr.ne']
  nlinarith [h1, h2]

/-- A compact interval has upper Minkowski dimension at most `1`. -/
theorem upperBoxDim_Icc_le (a b : ℝ) : upperBoxDim (Icc a b) ≤ 1 := by
  rcases lt_or_ge b a with hba' | hab
  · rw [Icc_eq_empty (not_le.2 hba'), upperBoxDim_empty]
    exact zero_le_one
  have h1 : ((1 : ℝ≥0) : ℝ≥0∞) = 1 := by norm_num
  rw [← h1]
  refine upperBoxDim_le_of_forall (s := 1) (C := ((b - a) / 2 + 1).toNNReal)
    (Real.toNNReal_pos.2 (by linarith)) ?_
  filter_upwards [eventually_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one' ℝ))] with r hr0 hr1
  have hr : (0 : ℝ) < r := hr0
  have hN := (isCover_gridCentres (a := a) (b := b) hr).externalCoveringNumber_le_encard.trans
    (encard_gridCentres_le a b r)
  calc (Metric.externalCoveringNumber r.toNNReal (Icc a b) : ℝ≥0∞)
      ≤ ((⌊(b - a) / (2 * r)⌋₊ + 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast ENat.toENNReal_le.2 hN
    _ = ENNReal.ofReal (((⌊(b - a) / (2 * r)⌋₊ : ℕ) : ℝ) + 1) := by
        rw [show (((⌊(b - a) / (2 * r)⌋₊ : ℕ) : ℝ) + 1)
          = ((⌊(b - a) / (2 * r)⌋₊ + 1 : ℕ) : ℝ) by push_cast; ring]
        exact (ENNReal.ofReal_natCast _).symm
    _ ≤ ENNReal.ofReal (((b - a) / 2 + 1) * r⁻¹) :=
        ENNReal.ofReal_le_ofReal (natFloor_add_one_le hab hr hr1)
    _ = (((b - a) / 2 + 1).toNNReal : ℝ≥0∞) * ENNReal.ofReal (r ^ (-((1 : ℝ≥0) : ℝ))) := by
        rw [NNReal.coe_one, Real.rpow_neg_one, show ((((b - a) / 2 + 1).toNNReal : ℝ≥0) : ℝ≥0∞)
            = ENNReal.ofReal ((b - a) / 2 + 1) from rfl,
          ← ENNReal.ofReal_mul (by linarith)]

/-- A bounded set of real numbers has upper Minkowski dimension at most `1`. -/
theorem upperBoxDim_le_one {E : Set ℝ} (hE : Bornology.IsBounded E) : upperBoxDim E ≤ 1 := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hE
  rw [Real.closedBall_eq_Icc] at hR
  exact (upperBoxDim_mono hR).trans (upperBoxDim_Icc_le _ _)

/-- A closed rectangle of the plane with the sup metric has upper Minkowski dimension at most
`2`: the products of the centres of two subdivisions form a cover. -/
theorem upperBoxDim_Icc_prod_le (a b c d : ℝ) : upperBoxDim (Icc a b ×ˢ Icc c d) ≤ 2 := by
  rcases lt_or_ge b a with hba' | hab
  · rw [Icc_eq_empty (not_le.2 hba'), Set.empty_prod, upperBoxDim_empty]
    exact zero_le_two
  rcases lt_or_ge d c with hdc' | hcd
  · rw [Icc_eq_empty (not_le.2 hdc'), Set.prod_empty, upperBoxDim_empty]
    exact zero_le_two
  have h2 : ((2 : ℝ≥0) : ℝ≥0∞) = 2 := by norm_num
  rw [← h2]
  have hK₁ : (0 : ℝ) < (b - a) / 2 + 1 := by linarith
  have hK₂ : (0 : ℝ) < (d - c) / 2 + 1 := by linarith
  refine upperBoxDim_le_of_forall (s := 2)
    (C := (((b - a) / 2 + 1) * ((d - c) / 2 + 1)).toNNReal)
    (Real.toNNReal_pos.2 (mul_pos hK₁ hK₂)) ?_
  filter_upwards [eventually_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one' ℝ))] with r hr0 hr1
  have hr : (0 : ℝ) < r := hr0
  have hcov : Metric.IsCover r.toNNReal (Icc a b ×ˢ Icc c d)
      (gridCentres a b r ×ˢ gridCentres c d r) := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    obtain ⟨u, hu, hxu⟩ := isCover_gridCentres (a := a) (b := b) hr hx
    obtain ⟨v, hv, hyv⟩ := isCover_gridCentres (a := c) (b := d) hr hy
    replace hxu : edist x u ≤ (r.toNNReal : ℝ≥0∞) := hxu
    replace hyv : edist y v ≤ (r.toNNReal : ℝ≥0∞) := hyv
    exact ⟨(u, v), ⟨hu, hv⟩, show edist (x, y) (u, v) ≤ (r.toNNReal : ℝ≥0∞) from
      (Prod.edist_eq _ _).trans_le (max_le hxu hyv)⟩
  have hN : Metric.externalCoveringNumber r.toNNReal (Icc a b ×ˢ Icc c d) ≤
      (((⌊(b - a) / (2 * r)⌋₊ + 1) * (⌊(d - c) / (2 * r)⌋₊ + 1) : ℕ) : ℕ∞) := by
    refine hcov.externalCoveringNumber_le_encard.trans ?_
    rw [Set.encard_prod, Nat.cast_mul]
    exact mul_le_mul' (encard_gridCentres_le a b r) (encard_gridCentres_le c d r)
  have h₁ := natFloor_add_one_le hab hr hr1
  have h₂ := natFloor_add_one_le hcd hr hr1
  have hreal : (((⌊(b - a) / (2 * r)⌋₊ + 1) * (⌊(d - c) / (2 * r)⌋₊ + 1) : ℕ) : ℝ) ≤
      ((b - a) / 2 + 1) * ((d - c) / 2 + 1) * r ^ (-((2 : ℝ≥0) : ℝ)) := by
    have hpow : r ^ (-((2 : ℝ≥0) : ℝ)) = r⁻¹ * r⁻¹ := by
      rw [NNReal.coe_ofNat, Real.rpow_neg hr.le, Real.rpow_two, sq, mul_inv]
    rw [hpow]
    push_cast
    calc (((⌊(b - a) / (2 * r)⌋₊ : ℕ) : ℝ) + 1) * (((⌊(d - c) / (2 * r)⌋₊ : ℕ) : ℝ) + 1)
        ≤ (((b - a) / 2 + 1) * r⁻¹) * (((d - c) / 2 + 1) * r⁻¹) :=
          mul_le_mul h₁ h₂ (by positivity) (by positivity)
      _ = ((b - a) / 2 + 1) * ((d - c) / 2 + 1) * (r⁻¹ * r⁻¹) := by ring
  calc (Metric.externalCoveringNumber r.toNNReal (Icc a b ×ˢ Icc c d) : ℝ≥0∞)
      ≤ (((⌊(b - a) / (2 * r)⌋₊ + 1) * (⌊(d - c) / (2 * r)⌋₊ + 1) : ℕ) : ℝ≥0∞) := by
        exact_mod_cast ENat.toENNReal_le.2 hN
    _ = ENNReal.ofReal
        (((⌊(b - a) / (2 * r)⌋₊ + 1) * (⌊(d - c) / (2 * r)⌋₊ + 1) : ℕ) : ℝ) :=
        (ENNReal.ofReal_natCast _).symm
    _ ≤ ENNReal.ofReal
        (((b - a) / 2 + 1) * ((d - c) / 2 + 1) * r ^ (-((2 : ℝ≥0) : ℝ))) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ((((b - a) / 2 + 1) * ((d - c) / 2 + 1)).toNNReal : ℝ≥0∞) *
        ENNReal.ofReal (r ^ (-((2 : ℝ≥0) : ℝ))) := by
        rw [show (((((b - a) / 2 + 1) * ((d - c) / 2 + 1)).toNNReal : ℝ≥0) : ℝ≥0∞)
            = ENNReal.ofReal (((b - a) / 2 + 1) * ((d - c) / 2 + 1)) from rfl,
          ← ENNReal.ofReal_mul (mul_pos hK₁ hK₂).le]

/-- A bounded subset of the plane with the sup metric has upper Minkowski dimension at most
`2`. -/
theorem upperBoxDim_le_two {E : Set (ℝ × ℝ)} (hE : Bornology.IsBounded E) :
    upperBoxDim E ≤ 2 := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall ((0 : ℝ), (0 : ℝ))).1 hE
  rw [← closedBall_prod_same, Real.closedBall_eq_Icc] at hR
  exact (upperBoxDim_mono hR).trans (upperBoxDim_Icc_prod_le _ _ _ _)

/-! ### Hausdorff dimension against the lower Minkowski dimension -/

/-- `\dim_H E ≤ \underline{\dim}_M E`: a cover by `N_r(E) ≤ r^{-t}` balls of radius `r` has
`t`-dimensional cost at most `2^t`, so the `t`-dimensional Hausdorff measure of `E` is finite. -/
theorem dimH_le_lowerBoxDim {Y : Type*} [MetricSpace Y] (E : Set Y) :
    dimH E ≤ lowerBoxDim E := by
  borelize Y
  refine le_iInf₂ fun t ht => ?_
  refine dimH_le_of_hausdorffMeasure_ne_top (d := t) (ne_top_of_le_ne_top
    (ENNReal.ofReal_ne_top (r := 2 ^ (t : ℝ))) ?_)
  obtain ⟨ρ, hρtend, hρ⟩ := Filter.exists_seq_forall_of_frequently ht
  have hρpos : ∀ᶠ j in atTop, 0 < ρ j := hρtend.eventually eventually_mem_nhdsWithin
  -- a minimising cover at each positive scale
  have hC : ∀ j, ∃ C : Finset Y, (0 < ρ j → E ⊆ ⋃ c ∈ C, closedBall c (ρ j)) ∧
      (C.card : ℝ≥0∞) ≤ ENNReal.ofReal (ρ j ^ (-(t : ℝ))) := by
    intro j
    rcases le_or_gt (ρ j) 0 with hj | hj
    · exact ⟨∅, fun h => absurd h (not_lt.2 hj), by simp⟩
    have htop : Metric.externalCoveringNumber (ρ j).toNNReal E ≠ ⊤ := by
      intro h
      have := hρ j
      rw [h, ENat.toENNReal_top, top_le_iff] at this
      exact ENNReal.ofReal_ne_top this
    obtain ⟨C, hCfin, hCcov, hCcard⟩ := exists_isCover_encard_eq htop
    refine ⟨hCfin.toFinset, fun _ => ?_, ?_⟩
    · have h := hCcov.subset_iUnion_closedBall
      rw [Real.coe_toNNReal _ hj.le] at h
      exact h.trans (Set.iUnion₂_subset fun c hc =>
        Set.subset_biUnion_of_mem (u := fun c => closedBall c (ρ j)) (by simpa using hc))
    · refine le_of_eq_of_le ?_ (hρ j)
      rw [← hCcard, hCfin.encard_eq_coe_toFinset_card]
      simp
  choose C hCcov hCcard using hC
  have hr : Tendsto (fun j => ENNReal.ofReal (2 * ρ j)) atTop (𝓝 0) := by
    have h0 : Tendsto ρ atTop (𝓝 0) := hρtend.mono_right nhdsWithin_le_nhds
    have h := (ENNReal.continuous_ofReal.tendsto _).comp (h0.const_mul 2)
    rw [mul_zero, ENNReal.ofReal_zero] at h
    exact h
  have hdiam : ∀ j (c : Y), ediam (closedBall c (ρ j)) ≤ ENNReal.ofReal (2 * ρ j) := by
    intro j c
    refine Metric.ediam_le fun y hy z hz => ?_
    rw [edist_dist]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mem_closedBall] at hy hz
    have h1 := dist_triangle y c z
    rw [dist_comm c z] at h1
    linarith
  refine (Measure.hausdorffMeasure_le_liminf_sum (t : ℝ) E (fun j => ENNReal.ofReal (2 * ρ j)) hr
    (fun j (c : C j) => closedBall (c : Y) (ρ j)) (Eventually.of_forall fun j c => hdiam j c)
    (hρpos.mono fun j hj => (hCcov j hj).trans (by
      intro z hz
      obtain ⟨c, hc, hzc⟩ := Set.mem_iUnion₂.1 hz
      exact Set.mem_iUnion.2 ⟨⟨c, hc⟩, hzc⟩))).trans ?_
  refine liminf_le_of_frequently_le' (hρpos.frequently.mono fun j hj => ?_)
  calc ∑ c : C j, ediam (closedBall (c : Y) (ρ j)) ^ (t : ℝ)
      ≤ ∑ _c : C j, ENNReal.ofReal (2 * ρ j) ^ (t : ℝ) :=
        Finset.sum_le_sum fun c _ => ENNReal.rpow_le_rpow (hdiam j c) t.coe_nonneg
    _ = ((C j).card : ℝ≥0∞) * ENNReal.ofReal (2 * ρ j) ^ (t : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe]
    _ ≤ ENNReal.ofReal (ρ j ^ (-(t : ℝ))) * ENNReal.ofReal ((2 * ρ j) ^ (t : ℝ)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) t.coe_nonneg]
        exact mul_le_mul_left (hCcard j) _
    _ = ENNReal.ofReal (2 ^ (t : ℝ)) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hj.le _),
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hj.le, mul_left_comm,
          ← Real.rpow_add hj, neg_add_cancel, Real.rpow_zero, mul_one]

/-! ### The packing dimension -/

/-- The packing dimension `\dim_P E` of tex lines 2077 to 2077, defined as the modified upper
box dimension: the infimum over countable covers of `E` by bounded sets of the supremum of the
upper Minkowski dimensions of the pieces. On a metric space this equals the packing dimension
defined through packing measures, by `packing_modified_box` of the library
`GeometricMeasureTheory`. -/
def packingDim (E : Set X) : ℝ≥0∞ :=
  ⨅ (A : ℕ → Set X) (_ : E ⊆ ⋃ i, A i) (_ : ∀ i, Bornology.IsBounded (A i)),
    ⨆ i, upperBoxDim (A i)

/-- A countable bounded cover bounds the packing dimension from above. -/
theorem packingDim_le_of_cover {E : Set X} {x : ℝ≥0∞} (A : ℕ → Set X)
    (hcov : E ⊆ ⋃ i, A i) (hb : ∀ i, Bornology.IsBounded (A i))
    (h : ⨆ i, upperBoxDim (A i) ≤ x) : packingDim E ≤ x :=
  le_trans (iInf_le_of_le A (iInf_le_of_le hcov (iInf_le_of_le hb le_rfl))) h

/-- A bound valid for every countable bounded cover bounds the packing dimension from below. -/
theorem le_packingDim {E : Set X} {x : ℝ≥0∞}
    (h : ∀ A : ℕ → Set X, E ⊆ ⋃ i, A i → (∀ i, Bornology.IsBounded (A i)) →
      x ≤ ⨆ i, upperBoxDim (A i)) : x ≤ packingDim E :=
  le_iInf fun A => le_iInf fun hcov => le_iInf fun hb => h A hcov hb

/-- The packing dimension is monotone. -/
theorem packingDim_mono {E F : Set X} (h : E ⊆ F) : packingDim E ≤ packingDim F :=
  le_packingDim fun A hcov hb => packingDim_le_of_cover A (h.trans hcov) hb le_rfl

/-- `\dim_P E ≤ \overline{\dim}_M E`. A set of finite upper Minkowski dimension is bounded and
covers itself. -/
theorem packingDim_le_upperBoxDim (E : Set X) : packingDim E ≤ upperBoxDim E := by
  rcases eq_or_ne (upperBoxDim E) ⊤ with h | h
  · rw [h]
    exact le_top
  · exact packingDim_le_of_cover (fun _ => E) (fun z hz => Set.mem_iUnion.2 ⟨0, hz⟩)
      (fun _ => isBounded_of_upperBoxDim_ne_top h) (iSup_le fun _ => le_rfl)

/-- `\dim_H E ≤ \dim_P E`, by the countable stability of the Hausdorff dimension. -/
theorem dimH_le_packingDim {Y : Type*} [MetricSpace Y] (E : Set Y) : dimH E ≤ packingDim E := by
  refine le_packingDim fun A hcov _ => ?_
  calc dimH E ≤ dimH (⋃ i, A i) := dimH_mono hcov
    _ = ⨆ i, dimH (A i) := dimH_iUnion A
    _ ≤ ⨆ i, upperBoxDim (A i) :=
        iSup_mono fun i => (dimH_le_lowerBoxDim (A i)).trans (lowerBoxDim_le_upperBoxDim (A i))

/-- `\dim_H E ≤ \overline{\dim}_M E`. -/
theorem dimH_le_upperBoxDim {Y : Type*} [MetricSpace Y] (E : Set Y) : dimH E ≤ upperBoxDim E :=
  (dimH_le_lowerBoxDim E).trans (lowerBoxDim_le_upperBoxDim E)

/-- The packing dimension does not increase under a Lipschitz map. -/
theorem packingDim_image_le {Y : Type*} [PseudoMetricSpace Y] {f : X → Y} {L : ℝ≥0} {E : Set X}
    (hf : LipschitzOnWith L f E) : packingDim (f '' E) ≤ packingDim E := by
  refine le_packingDim fun A hcov hb => ?_
  refine packingDim_le_of_cover (fun i => f '' (A i ∩ E)) ?_ ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov hz)
    exact Set.mem_iUnion.2 ⟨i, ⟨z, ⟨hi, hz⟩, rfl⟩⟩
  · intro i
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 (hb i)
    refine Metric.isBounded_iff.2 ⟨L * C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    calc dist (f z) (f w) ≤ L * dist z w := hf.dist_le_mul z hz.2 w hw.2
      _ ≤ L * C := by
          have hzw : dist z w ≤ C := hC hz.1 hw.1
          gcongr
  · exact iSup_mono fun i => (upperBoxDim_image_le (hf.mono Set.inter_subset_right)).trans
      (upperBoxDim_mono Set.inter_subset_left)

/-- Bi-Lipschitz invariance of the packing dimension. -/
theorem packingDim_image_eq {Y : Type*} [PseudoMetricSpace Y] {f : X → Y} {g : Y → X}
    {K L : ℝ≥0} {E : Set X} (hf : LipschitzOnWith L f E) (hg : LipschitzOnWith K g (f '' E))
    (hgf : ∀ x ∈ E, g (f x) = x) : packingDim (f '' E) = packingDim E := by
  refine le_antisymm (packingDim_image_le hf) ?_
  have hE : g '' (f '' E) = E := by
    rw [Set.image_image]
    exact (Set.image_congr hgf).trans (Set.image_id E)
  calc packingDim E = packingDim (g '' (f '' E)) := by rw [hE]
    _ ≤ packingDim (f '' E) := packingDim_image_le hg

/-- If every relatively open piece of a compact set `E` has the full upper Minkowski dimension,
then `\dim_P E = \overline{\dim}_M E`, by Baire's category theorem. This is the fact behind
"`\dim_P F = \overline{\dim}_B F`, since every open ball centred in `F` contains a bi-Lipschitz
image of `F`" in the proof of Fraser's theorem, `thm:fraser`. -/
theorem packingDim_eq_upperBoxDim {Y : Type*} [MetricSpace Y] {E : Set Y} (hE : IsCompact E)
    (hne : E.Nonempty)
    (h : ∀ U : Set Y, IsOpen U → (E ∩ U).Nonempty → upperBoxDim (E ∩ U) = upperBoxDim E) :
    packingDim E = upperBoxDim E := by
  refine le_antisymm (packingDim_le_upperBoxDim E) ?_
  refine le_packingDim fun A hcov _ => ?_
  have : Nonempty ↥E := hne.to_subtype
  have : CompleteSpace ↥E := hE.isComplete.completeSpace_coe
  have hclosed : ∀ i, IsClosed ((Subtype.val : ↥E → Y) ⁻¹' closure (A i)) :=
    fun i => isClosed_closure.preimage continuous_subtype_val
  have hunion : (⋃ i, (Subtype.val : ↥E → Y) ⁻¹' closure (A i)) = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov z.2)
    exact Set.mem_iUnion.2 ⟨i, subset_closure hi⟩
  obtain ⟨i, p, hp⟩ := nonempty_interior_of_iUnion_of_closed hclosed hunion
  obtain ⟨U, hUopen, hUeq⟩ := isOpen_induced_iff.1
    (isOpen_interior (s := (Subtype.val : ↥E → Y) ⁻¹' closure (A i)))
  have hpU : (p : Y) ∈ U := by
    have : p ∈ (Subtype.val : ↥E → Y) ⁻¹' U := by rw [hUeq]; exact hp
    exact this
  have hUne : (E ∩ U).Nonempty := ⟨(p : Y), p.2, hpU⟩
  have hsub : E ∩ U ⊆ closure (A i) := by
    rintro z ⟨hzE, hzU⟩
    have hz : (⟨z, hzE⟩ : ↥E) ∈ (Subtype.val : ↥E → Y) ⁻¹' U := hzU
    rw [hUeq] at hz
    have hz2 : (⟨z, hzE⟩ : ↥E) ∈ (Subtype.val : ↥E → Y) ⁻¹' closure (A i) := interior_subset hz
    exact hz2
  calc upperBoxDim E = upperBoxDim (E ∩ U) := (h U hUopen hUne).symm
    _ ≤ upperBoxDim (closure (A i)) := upperBoxDim_mono hsub
    _ = upperBoxDim (A i) := upperBoxDim_closure (A i)
    _ ≤ ⨆ j, upperBoxDim (A j) := le_iSup (fun j => upperBoxDim (A j)) i

end BoxLike
