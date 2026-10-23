/-
# Section 4.2: Lower and upper box dimensions

The box-counting dimensions of Definition 4.3. They are defined here by the critical exponent of
the covering count: the upper box dimension is the least `s` with `N_r(E) ≤ r^{-s}` for all small
`r`, and the lower box dimension is the least `s` with that bound for arbitrarily small `r`. The
formulas of the notes, `limsup log N_r(E) / (-log r)` and the corresponding `liminf`, are proved in
`upperBoxDim_eq_limsup` and `lowerBoxDim_eq_liminf`.

| Notes | Lean declaration | Location |
|---|---|---|
| Definition 4.3 (box dimensions) | `UpperBoxDimLE`, `LowerBoxDimLE`, `upperBoxDim`, `lowerBoxDim` | here |
| The formulas of Definition 4.3 | `upperBoxDim_eq_limsup`, `lowerBoxDim_eq_liminf` | here |
| Proposition 4.4 (conventions) | `box_counting_conventions_packing`, `box_counting_conventions_scales` | here |
| Proposition 4.5 (properties) | `upperBoxDim_mono`, `lowerBoxDim_mono`, `upperBoxDim_closure`, `lowerBoxDim_closure`, `upperBoxDim_image_le`, `lowerBoxDim_image_le`, `upperBoxDim_union`, `upperBoxDim_le_finrank` | here |
| Example 4.6 (interval and Cantor set) | `box_interval`, `box_cantor` | here |
| Example 4.7 (reciprocal sequence) | `box_reciprocal_sequence` | here |
| Proposition 4.8 (Hausdorff against lower box) | `hausdorff_lower_box` | here |
| Rescaling the radius | `tendsto_const_mul_nhdsGT_zero`, `upperBoxDim_le_of_le_scale`, `lowerBoxDim_le_of_le_scale` | here |
| Counting along a geometric sequence of scales | `upperBoxDim_le_of_geometric`, `le_lowerBoxDim_of_geometric` | here |
| Bounds with a constant | `upperBoxDim_le_of_forall`, `lowerBoxDim_le_of_frequently`, `le_lowerBoxDim_of_forall`, `le_upperBoxDim_of_frequently` | here |
| Covering an interval | `externalCoveringNumber_Icc_le` | here |
-/
import GeometricMeasureTheory.Box.CoveringNumbers
import GeometricMeasureTheory.Hausdorff.CantorSets

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

variable {X : Type*} [PseudoMetricSpace X]

/-! ## Definition 4.3 (`def:box-dimensions`) -/

/-- `N_r(E) ≤ r^{-s}` for all sufficiently small `r`. -/
def UpperBoxDimLE (E : Set X) (s : ℝ) : Prop :=
  ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
    (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞) ≤ ENNReal.ofReal (r ^ (-s))

/-- `N_r(E) ≤ r^{-s}` for arbitrarily small `r`. -/
def LowerBoxDimLE (E : Set X) (s : ℝ) : Prop :=
  ∃ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
    (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞) ≤ ENNReal.ofReal (r ^ (-s))

/-- Definition 4.3 (`def:box-dimensions`): the upper box-counting dimension. -/
def upperBoxDim (E : Set X) : ℝ≥0∞ :=
  ⨅ (s : ℝ≥0) (_ : UpperBoxDimLE E (s : ℝ)), (s : ℝ≥0∞)

/-- Definition 4.3 (`def:box-dimensions`): the lower box-counting dimension. -/
def lowerBoxDim (E : Set X) : ℝ≥0∞ :=
  ⨅ (s : ℝ≥0) (_ : LowerBoxDimLE E (s : ℝ)), (s : ℝ≥0∞)

/-! ## Small scales

Two elementary facts about the filter `𝓝[>] 0` of small scales: a fixed positive power of `r` is
eventually below any positive constant, and scaling the radius by a positive constant is a
self-map of the filter. -/

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

/-! ## The critical exponent

The four workhorse lemmas are proved once for a general counting function `G` measured along a
general family of scales `ρ`, so that they apply verbatim to the covering numbers, to the packing
numbers, and to a geometric sequence of scales. -/

section Scales

variable {ι : Type*} {l : Filter ι} {G : ι → ℝ≥0∞} {ρ : ι → ℝ}

/-- A constant is absorbed by an arbitrarily small increase of the exponent. -/
private lemma eventually_imp_of_pos (hρ : Tendsto ρ l (𝓝[>] (0 : ℝ))) {s C ε : ℝ≥0} (hC : 0 < C)
    (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ x : ℝ≥0∞, x ≤ C * ENNReal.ofReal (ρ i ^ (-(s : ℝ))) →
      x ≤ ENNReal.ofReal (ρ i ^ (-((s + ε : ℝ≥0) : ℝ))) := by
  have hCpos : (0 : ℝ) < (C : ℝ) := hC
  filter_upwards [hρ.eventually eventually_mem_nhdsWithin,
    hρ.eventually (eventually_rpow_lt (C := (C : ℝ)⁻¹) (by positivity)
      (show (0 : ℝ) < (ε : ℝ) from hε))] with i hi0 hi1 x hx
  have hp : (0 : ℝ) < ρ i := hi0
  have hCle : (C : ℝ) * ρ i ^ (ε : ℝ) ≤ 1 := by
    have h2 := mul_lt_mul_of_pos_left hi1 hCpos
    rw [mul_inv_cancel₀ hCpos.ne'] at h2
    exact h2.le
  have hadd : ρ i ^ (-(s : ℝ)) = ρ i ^ (-((s : ℝ) + (ε : ℝ))) * ρ i ^ (ε : ℝ) := by
    rw [← Real.rpow_add hp]; congr 1; ring
  have hreal : (C : ℝ) * ρ i ^ (-(s : ℝ)) ≤ ρ i ^ (-((s : ℝ) + (ε : ℝ))) := by
    calc (C : ℝ) * ρ i ^ (-(s : ℝ))
        = ρ i ^ (-((s : ℝ) + (ε : ℝ))) * ((C : ℝ) * ρ i ^ (ε : ℝ)) := by rw [hadd]; ring
      _ ≤ ρ i ^ (-((s : ℝ) + (ε : ℝ))) * 1 :=
          mul_le_mul_of_nonneg_left hCle (Real.rpow_nonneg hp.le _)
      _ = ρ i ^ (-((s : ℝ) + (ε : ℝ))) := mul_one _
  calc x ≤ (C : ℝ≥0∞) * ENNReal.ofReal (ρ i ^ (-(s : ℝ))) := hx
    _ = ENNReal.ofReal ((C : ℝ) * ρ i ^ (-(s : ℝ))) := by
        rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal]
    _ ≤ ENNReal.ofReal (ρ i ^ (-((s : ℝ) + (ε : ℝ)))) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (ρ i ^ (-((s + ε : ℝ≥0) : ℝ))) := by norm_cast

private lemma iInf_le_of_eventually (hρ : Tendsto ρ l (𝓝[>] (0 : ℝ))) {s C : ℝ≥0} (hC : 0 < C)
    (h : ∀ᶠ i in l, G i ≤ C * ENNReal.ofReal (ρ i ^ (-(s : ℝ)))) :
    ⨅ (t : ℝ≥0) (_ : ∀ᶠ i in l, G i ≤ ENNReal.ofReal (ρ i ^ (-(t : ℝ)))), (t : ℝ≥0∞) ≤ s := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have key : ∀ᶠ i in l, G i ≤ ENNReal.ofReal (ρ i ^ (-((s + ε : ℝ≥0) : ℝ))) := by
    filter_upwards [h, eventually_imp_of_pos hρ hC hε] with i hi himp using himp _ hi
  exact (iInf₂_le (s + ε) key).trans_eq (by push_cast; ring)

private lemma iInf_le_of_frequently (hρ : Tendsto ρ l (𝓝[>] (0 : ℝ))) {s C : ℝ≥0} (hC : 0 < C)
    (h : ∃ᶠ i in l, G i ≤ C * ENNReal.ofReal (ρ i ^ (-(s : ℝ)))) :
    ⨅ (t : ℝ≥0) (_ : ∃ᶠ i in l, G i ≤ ENNReal.ofReal (ρ i ^ (-(t : ℝ)))), (t : ℝ≥0∞) ≤ s := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have key : ∃ᶠ i in l, G i ≤ ENNReal.ofReal (ρ i ^ (-((s + ε : ℝ≥0) : ℝ))) :=
    (h.and_eventually (eventually_imp_of_pos hρ hC hε)).mono fun i hi => hi.2 _ hi.1
  exact (iInf₂_le (s + ε) key).trans_eq (by push_cast; ring)

private lemma le_of_frequently_le (hρ : Tendsto ρ l (𝓝[>] (0 : ℝ))) {s t C : ℝ≥0} (hC : 0 < C)
    (h : ∃ᶠ i in l, (C : ℝ≥0∞) * ENNReal.ofReal (ρ i ^ (-(s : ℝ))) ≤ G i ∧
      G i ≤ ENNReal.ofReal (ρ i ^ (-(t : ℝ)))) : s ≤ t := by
  by_contra hts
  rw [not_le] at hts
  have hst : (0 : ℝ) < (s : ℝ) - (t : ℝ) := by
    have h' : (t : ℝ) < (s : ℝ) := hts
    linarith
  obtain ⟨i, ⟨h1, h2⟩, hi0, hi1⟩ :=
    (h.and_eventually ((hρ.eventually eventually_mem_nhdsWithin).and
      (hρ.eventually (eventually_rpow_lt (C := (C : ℝ)) hC hst)))).exists
  have hp : (0 : ℝ) < ρ i := hi0
  have hreal : (C : ℝ) * ρ i ^ (-(s : ℝ)) ≤ ρ i ^ (-(t : ℝ)) := by
    have h3 := h1.trans h2
    rwa [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg,
      ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hp.le _)] at h3
  have hadd : ρ i ^ (-(t : ℝ)) = ρ i ^ ((s : ℝ) - (t : ℝ)) * ρ i ^ (-(s : ℝ)) := by
    rw [← Real.rpow_add hp]; congr 1; ring
  rw [hadd] at hreal
  have hle := le_of_mul_le_mul_right hreal (Real.rpow_pos_of_pos hp (-(s : ℝ)))
  linarith

private lemma le_iInf_of_eventually (hρ : Tendsto ρ l (𝓝[>] (0 : ℝ))) {s C : ℝ≥0} (hC : 0 < C)
    (h : ∀ᶠ i in l, (C : ℝ≥0∞) * ENNReal.ofReal (ρ i ^ (-(s : ℝ))) ≤ G i) :
    (s : ℝ≥0∞) ≤
      ⨅ (t : ℝ≥0) (_ : ∃ᶠ i in l, G i ≤ ENNReal.ofReal (ρ i ^ (-(t : ℝ)))), (t : ℝ≥0∞) := by
  refine le_iInf₂ fun t ht => ?_
  exact_mod_cast le_of_frequently_le hρ hC ((ht.and_eventually h).mono fun i hi => ⟨hi.2, hi.1⟩)

private lemma le_iInf_of_frequently (hρ : Tendsto ρ l (𝓝[>] (0 : ℝ))) {s C : ℝ≥0} (hC : 0 < C)
    (h : ∃ᶠ i in l, (C : ℝ≥0∞) * ENNReal.ofReal (ρ i ^ (-(s : ℝ))) ≤ G i) :
    (s : ℝ≥0∞) ≤
      ⨅ (t : ℝ≥0) (_ : ∀ᶠ i in l, G i ≤ ENNReal.ofReal (ρ i ^ (-(t : ℝ)))), (t : ℝ≥0∞) := by
  refine le_iInf₂ fun t ht => ?_
  exact_mod_cast le_of_frequently_le hρ hC (h.and_eventually ht)

/-- Comparing two counting functions at radii differing by a fixed factor compares their critical
exponents. -/
private lemma iInf_le_iInf_of_le_scale {F H : ℝ → ℝ≥0∞} {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), F r ≤ H (c * r)) :
    (⨅ (t : ℝ≥0) (_ : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), F r ≤ ENNReal.ofReal (r ^ (-(t : ℝ)))),
        (t : ℝ≥0∞)) ≤
      ⨅ (t : ℝ≥0) (_ : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), H r ≤ ENNReal.ofReal (r ^ (-(t : ℝ)))),
        (t : ℝ≥0∞) := by
  refine le_iInf₂ fun s hs => ?_
  refine iInf_le_of_eventually (ρ := fun r : ℝ => r) (G := F) tendsto_id
    (C := (c ^ (-(s : ℝ))).toNNReal) (Real.toNNReal_pos.2 (Real.rpow_pos_of_pos hc _)) ?_
  filter_upwards [h, (tendsto_const_mul_nhdsGT_zero hc).eventually hs, eventually_mem_nhdsWithin]
    with r hr hs' hr0
  have hp : (0 : ℝ) < r := hr0
  refine hr.trans (hs'.trans (le_of_eq ?_))
  rw [show (((c ^ (-(s : ℝ))).toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (c ^ (-(s : ℝ))) from rfl,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _), ← Real.mul_rpow hc.le hp.le]

/-- The version of `iInf_le_iInf_of_le_scale` for the lower critical exponent. -/
private lemma iInf_le_iInf_of_le_scale' {F H : ℝ → ℝ≥0∞} {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), F r ≤ H (c * r)) :
    (⨅ (t : ℝ≥0) (_ : ∃ᶠ r : ℝ in 𝓝[>] (0 : ℝ), F r ≤ ENNReal.ofReal (r ^ (-(t : ℝ)))),
        (t : ℝ≥0∞)) ≤
      ⨅ (t : ℝ≥0) (_ : ∃ᶠ r : ℝ in 𝓝[>] (0 : ℝ), H r ≤ ENNReal.ofReal (r ^ (-(t : ℝ)))),
        (t : ℝ≥0∞) := by
  refine le_iInf₂ fun s hs => ?_
  refine iInf_le_of_frequently (ρ := fun r : ℝ => r) (G := F) tendsto_id
    (C := (c ^ (-(s : ℝ))).toNNReal) (Real.toNNReal_pos.2 (Real.rpow_pos_of_pos hc _)) ?_
  refine ((frequently_nhdsGT_zero_const_mul hc hs).and_eventually
    (h.and eventually_mem_nhdsWithin)).mono fun r hr => ?_
  obtain ⟨h1, h2, hr0⟩ := hr
  have hp : (0 : ℝ) < r := hr0
  refine h2.trans (h1.trans (le_of_eq ?_))
  rw [show (((c ^ (-(s : ℝ))).toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (c ^ (-(s : ℝ))) from rfl,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _), ← Real.mul_rpow hc.le hp.le]

end Scales

/-! ## First properties of the box dimensions -/

/-- The counting bound at one exponent implies it at every larger exponent. -/
theorem UpperBoxDimLE.mono_exponent {E : Set X} {s t : ℝ} (h : UpperBoxDimLE E s) (hst : s ≤ t) :
    UpperBoxDimLE E t := by
  filter_upwards [h, eventually_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one' ℝ))] with r hr hr0 hr1
  have hp : (0 : ℝ) < r := hr0
  refine hr.trans (ENNReal.ofReal_le_ofReal ?_)
  exact Real.rpow_le_rpow_of_exponent_ge hp (le_of_lt hr1) (by linarith)

/-- The counting bound at one exponent implies it at every larger exponent. -/
theorem LowerBoxDimLE.mono_exponent {E : Set X} {s t : ℝ} (h : LowerBoxDimLE E s) (hst : s ≤ t) :
    LowerBoxDimLE E t := by
  refine (h.and_eventually (?_ : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
    ENNReal.ofReal (r ^ (-s)) ≤ ENNReal.ofReal (r ^ (-t)))).mono fun r hr => hr.1.trans hr.2
  filter_upwards [eventually_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one' ℝ))] with r hr0 hr1
  have hp : (0 : ℝ) < r := hr0
  exact ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_ge hp (le_of_lt hr1) (by linarith))

/-- The counting bound bounds the upper box dimension. -/
theorem upperBoxDim_le_of_upperBoxDimLE {E : Set X} {s : ℝ≥0} (h : UpperBoxDimLE E (s : ℝ)) :
    upperBoxDim E ≤ s := iInf₂_le s h

/-- The counting bound bounds the lower box dimension. -/
theorem lowerBoxDim_le_of_lowerBoxDimLE {E : Set X} {s : ℝ≥0} (h : LowerBoxDimLE E (s : ℝ)) :
    lowerBoxDim E ≤ s := iInf₂_le s h

theorem lowerBoxDim_le_upperBoxDim (E : Set X) : lowerBoxDim E ≤ upperBoxDim E :=
  le_iInf₂ fun _ hs => lowerBoxDim_le_of_lowerBoxDimLE hs.frequently

@[simp]
theorem upperBoxDim_empty : upperBoxDim (∅ : Set X) = 0 := by
  refine le_antisymm ?_ (by simp)
  refine (upperBoxDim_le_of_upperBoxDimLE (s := 0) ?_).trans_eq (by simp)
  filter_upwards with r
  simp

@[simp]
theorem lowerBoxDim_empty : lowerBoxDim (∅ : Set X) = 0 :=
  le_antisymm ((lowerBoxDim_le_upperBoxDim _).trans_eq upperBoxDim_empty) (by simp)

/-- The upper box dimension is at most `s` exactly when the counting bound holds at every
sufficiently small scale, up to a constant. -/
theorem upperBoxDim_le_of_forall {E : Set X} {s : ℝ≥0} {C : ℝ≥0} (hC : 0 < C)
    (h : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞) ≤ C * ENNReal.ofReal (r ^ (-(s : ℝ)))) :
    upperBoxDim E ≤ s :=
  iInf_le_of_eventually (ρ := fun r : ℝ => r)
    (G := fun r : ℝ => (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞)) tendsto_id hC h

/-- The lower box dimension is at most `s` exactly when the counting bound holds at arbitrarily
small scales, up to a constant. -/
theorem lowerBoxDim_le_of_frequently {E : Set X} {s : ℝ≥0} {C : ℝ≥0} (hC : 0 < C)
    (h : ∃ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞) ≤ C * ENNReal.ofReal (r ^ (-(s : ℝ)))) :
    lowerBoxDim E ≤ s :=
  iInf_le_of_frequently (ρ := fun r : ℝ => r)
    (G := fun r : ℝ => (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞)) tendsto_id hC h

/-- A lower bound on the covering count at all small scales bounds the lower box dimension from
below. -/
theorem le_lowerBoxDim_of_forall {E : Set X} {s : ℝ≥0} {C : ℝ≥0} (hC : 0 < C)
    (h : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      C * ENNReal.ofReal (r ^ (-(s : ℝ))) ≤ (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞)) :
    (s : ℝ≥0∞) ≤ lowerBoxDim E :=
  le_iInf_of_eventually (ρ := fun r : ℝ => r)
    (G := fun r : ℝ => (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞)) tendsto_id hC h

/-- A lower bound on the covering count at arbitrarily small scales bounds the upper box dimension
from below. -/
theorem le_upperBoxDim_of_frequently {E : Set X} {s : ℝ≥0} {C : ℝ≥0} (hC : 0 < C)
    (h : ∃ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      C * ENNReal.ofReal (r ^ (-(s : ℝ))) ≤ (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞)) :
    (s : ℝ≥0∞) ≤ upperBoxDim E :=
  le_iInf_of_frequently (ρ := fun r : ℝ => r)
    (G := fun r : ℝ => (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞)) tendsto_id hC h

/-- A non-empty totally bounded set needs at least one ball at every positive radius. -/
private lemma one_le_toNat_externalCoveringNumber {E : Set X} (hE : E.Nonempty)
    (hTB : TotallyBounded E) {r : ℝ} (hr0 : 0 < r) :
    1 ≤ (Metric.externalCoveringNumber r.toNNReal E).toNat := by
  have h := ENat.toNat_le_toNat (one_le_externalCoveringNumber hE r.toNNReal)
    (externalCoveringNumber_ne_top hTB (Real.toNNReal_pos.2 hr0))
  simpa using h

/-- The counting quotient of Definition 4.3 is at most `c` exactly when `N_r(E) ≤ r ^ (-c)`. -/
private lemma log_count_div_le_iff {E : Set X} (hE : E.Nonempty) (hTB : TotallyBounded E)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (c : ℝ) :
    Real.log ((Metric.externalCoveringNumber r.toNNReal E).toNat : ℝ) / (-Real.log r) ≤ c ↔
      (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞) ≤ ENNReal.ofReal (r ^ (-c)) := by
  have hNtop : Metric.externalCoveringNumber r.toNNReal E ≠ ⊤ :=
    externalCoveringNumber_ne_top hTB (Real.toNNReal_pos.2 hr0)
  have hn1 : 1 ≤ (Metric.externalCoveringNumber r.toNNReal E).toNat :=
    one_le_toNat_externalCoveringNumber hE hTB hr0
  have hncast : (((Metric.externalCoveringNumber r.toNNReal E).toNat : ℕ) : ℕ∞)
      = Metric.externalCoveringNumber r.toNNReal E := ENat.coe_toNat hNtop
  have hlogr : 0 < -Real.log r := by
    have h := Real.log_neg hr0 hr1
    linarith
  have hnpos : (0 : ℝ) < ((Metric.externalCoveringNumber r.toNNReal E).toNat : ℝ) := by
    exact_mod_cast hn1
  have hrpow : (0 : ℝ) < r ^ (-c) := Real.rpow_pos_of_pos hr0 _
  have hcast2 : (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞)
      = ENNReal.ofReal (((Metric.externalCoveringNumber r.toNNReal E).toNat : ℕ) : ℝ) := by
    conv_lhs => rw [← hncast]
    rw [ENat.toENNReal_coe, ENNReal.ofReal_natCast]
  rw [div_le_iff₀ hlogr, show c * (-Real.log r) = Real.log (r ^ (-c)) by
      rw [Real.log_rpow hr0]; ring, Real.log_le_log_iff hnpos hrpow, hcast2,
    ENNReal.ofReal_le_ofReal_iff hrpow.le]

/-- The formula of Definition 4.3 for the upper box dimension. -/
theorem upperBoxDim_eq_limsup {E : Set X} (hE : E.Nonempty) (hTB : TotallyBounded E)
    (hfin : upperBoxDim E ≠ ⊤) :
    (upperBoxDim E).toReal =
      limsup (fun r : ℝ =>
        Real.log ((Metric.externalCoveringNumber r.toNNReal E).toNat : ℝ) / (-Real.log r))
        (𝓝[>] 0) := by
  set f : ℝ → ℝ := fun r : ℝ =>
    Real.log ((Metric.externalCoveringNumber r.toNNReal E).toNat : ℝ) / (-Real.log r) with hfdef
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r ∧ r < 1 := by
    filter_upwards [eventually_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one' ℝ))] with r h1 h2 using ⟨h1, h2⟩
  have hf0 : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 ≤ f r := by
    filter_upwards [hsmall] with r hr
    have hlogr : 0 < -Real.log r := by
      have h := Real.log_neg hr.1 hr.2
      linarith
    have hn1 : (1 : ℝ) ≤ ((Metric.externalCoveringNumber r.toNNReal E).toNat : ℝ) := by
      exact_mod_cast one_le_toNat_externalCoveringNumber hE hTB hr.1
    exact div_nonneg (Real.log_nonneg hn1) hlogr.le
  have key : ∀ t : ℝ≥0, UpperBoxDimLE E (t : ℝ) → ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), f r ≤ (t : ℝ) := by
    intro t ht
    filter_upwards [ht, hsmall] with r hr hr'
    exact (log_count_div_le_iff hE hTB hr'.1 hr'.2 _).2 hr
  obtain ⟨t₀, ht₀⟩ : ∃ t : ℝ≥0, UpperBoxDimLE E (t : ℝ) := by
    by_contra hcon
    rw [not_exists] at hcon
    exact hfin (eq_top_iff.2 (le_iInf₂ fun s hs => absurd hs (hcon s)))
  have hbddu : (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≤ ·) f :=
    isBoundedUnder_of_eventually_le (key t₀ ht₀)
  have hcobdd : (𝓝[>] (0 : ℝ)).IsCoboundedUnder (· ≤ ·) f := by
    refine ⟨0, fun a ha => ?_⟩
    rw [Filter.eventually_map] at ha
    obtain ⟨r, hr1, hr2⟩ := (ha.and hf0).exists
    exact hr2.trans hr1
  refine le_antisymm ?_ ?_
  · by_contra hcon
    rw [not_le] at hcon
    obtain ⟨c, hc1, hc2⟩ := exists_between hcon
    have hc0 : 0 ≤ c := le_trans (le_limsup_of_frequently_le hf0.frequently hbddu) hc1.le
    have hev : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), f r ≤ c :=
      (Filter.eventually_lt_of_limsup_lt hc1 hbddu).mono fun r hr => hr.le
    have hUB : upperBoxDim E ≤ ((c.toNNReal : ℝ≥0) : ℝ≥0∞) := by
      refine upperBoxDim_le_of_upperBoxDimLE ?_
      rw [Real.coe_toNNReal c hc0]
      filter_upwards [hev, hsmall] with r hr hr'
      exact (log_count_div_le_iff hE hTB hr'.1 hr'.2 c).1 hr
    have hle : (upperBoxDim E).toReal ≤ c := by
      have h := (ENNReal.toReal_le_toReal hfin (by simp)).2 hUB
      rwa [ENNReal.coe_toReal, Real.coe_toNNReal c hc0] at h
    linarith
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hlt : upperBoxDim E < ENNReal.ofReal ((upperBoxDim E).toReal + ε) := by
      have h : ENNReal.ofReal ((upperBoxDim E).toReal)
          < ENNReal.ofReal ((upperBoxDim E).toReal + ε) :=
        (ENNReal.ofReal_lt_ofReal_iff
          (add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hε)).2 (by linarith)
      rwa [ENNReal.ofReal_toReal hfin] at h
    rw [upperBoxDim, iInf_lt_iff] at hlt
    obtain ⟨t, hlt⟩ := hlt
    rw [iInf_lt_iff] at hlt
    obtain ⟨ht, hlt⟩ := hlt
    have htD : (t : ℝ) ≤ (upperBoxDim E).toReal + ε := by
      rw [← ENNReal.ofReal_coe_nnreal] at hlt
      exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff
        (add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hε)).1 hlt)
    exact Filter.limsup_le_of_le hcobdd ((key t ht).mono fun r hr => hr.trans htD)

/-- The formula of Definition 4.3 for the lower box dimension. -/
theorem lowerBoxDim_eq_liminf {E : Set X} (hE : E.Nonempty) (hTB : TotallyBounded E)
    (hfin : upperBoxDim E ≠ ⊤) :
    (lowerBoxDim E).toReal =
      liminf (fun r : ℝ =>
        Real.log ((Metric.externalCoveringNumber r.toNNReal E).toNat : ℝ) / (-Real.log r))
        (𝓝[>] 0) := by
  have hfin' : lowerBoxDim E ≠ ⊤ :=
    ((lowerBoxDim_le_upperBoxDim E).trans_lt (lt_top_iff_ne_top.2 hfin)).ne
  set f : ℝ → ℝ := fun r : ℝ =>
    Real.log ((Metric.externalCoveringNumber r.toNNReal E).toNat : ℝ) / (-Real.log r) with hfdef
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r ∧ r < 1 := by
    filter_upwards [eventually_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one' ℝ))] with r h1 h2 using ⟨h1, h2⟩
  have hf0 : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 ≤ f r := by
    filter_upwards [hsmall] with r hr
    have hlogr : 0 < -Real.log r := by
      have h := Real.log_neg hr.1 hr.2
      linarith
    have hn1 : (1 : ℝ) ≤ ((Metric.externalCoveringNumber r.toNNReal E).toNat : ℝ) := by
      exact_mod_cast one_le_toNat_externalCoveringNumber hE hTB hr.1
    exact div_nonneg (Real.log_nonneg hn1) hlogr.le
  have key : ∀ t : ℝ≥0, UpperBoxDimLE E (t : ℝ) → ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), f r ≤ (t : ℝ) := by
    intro t ht
    filter_upwards [ht, hsmall] with r hr hr'
    exact (log_count_div_le_iff hE hTB hr'.1 hr'.2 _).2 hr
  obtain ⟨t₀, ht₀⟩ : ∃ t : ℝ≥0, UpperBoxDimLE E (t : ℝ) := by
    by_contra hcon
    rw [not_exists] at hcon
    exact hfin (eq_top_iff.2 (le_iInf₂ fun s hs => absurd hs (hcon s)))
  have hbddl : (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≥ ·) f := ⟨0, hf0⟩
  have hcobdd : (𝓝[>] (0 : ℝ)).IsCoboundedUnder (· ≥ ·) f := by
    refine ⟨(t₀ : ℝ), fun a ha => ?_⟩
    rw [Filter.eventually_map] at ha
    obtain ⟨r, hr1, hr2⟩ := (ha.and (key t₀ ht₀)).exists
    exact hr1.trans hr2
  refine le_antisymm ?_ ?_
  · by_contra hcon
    rw [not_le] at hcon
    obtain ⟨c, hc1, hc2⟩ := exists_between hcon
    have hc0 : 0 ≤ c := le_trans (Filter.le_liminf_of_le hcobdd hf0) hc1.le
    have hev : ∃ᶠ r : ℝ in 𝓝[>] (0 : ℝ), f r ≤ c :=
      (Filter.frequently_lt_of_liminf_lt hcobdd hc1).mono fun r hr => hr.le
    have hLB : lowerBoxDim E ≤ ((c.toNNReal : ℝ≥0) : ℝ≥0∞) := by
      refine lowerBoxDim_le_of_lowerBoxDimLE ?_
      rw [Real.coe_toNNReal c hc0]
      refine (hev.and_eventually hsmall).mono fun r hr => ?_
      exact (log_count_div_le_iff hE hTB hr.2.1 hr.2.2 c).1 hr.1
    have hle : (lowerBoxDim E).toReal ≤ c := by
      have h := (ENNReal.toReal_le_toReal hfin' (by simp)).2 hLB
      rwa [ENNReal.coe_toReal, Real.coe_toNNReal c hc0] at h
    linarith
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hlt : lowerBoxDim E < ENNReal.ofReal ((lowerBoxDim E).toReal + ε) := by
      have h : ENNReal.ofReal ((lowerBoxDim E).toReal)
          < ENNReal.ofReal ((lowerBoxDim E).toReal + ε) :=
        (ENNReal.ofReal_lt_ofReal_iff
          (add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hε)).2 (by linarith)
      rwa [ENNReal.ofReal_toReal hfin'] at h
    rw [lowerBoxDim, iInf_lt_iff] at hlt
    obtain ⟨t, hlt⟩ := hlt
    rw [iInf_lt_iff] at hlt
    obtain ⟨ht, hlt⟩ := hlt
    have htD : (t : ℝ) ≤ (lowerBoxDim E).toReal + ε := by
      rw [← ENNReal.ofReal_coe_nnreal] at hlt
      exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff
        (add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hε)).1 hlt)
    have hfreq : ∃ᶠ r : ℝ in 𝓝[>] (0 : ℝ), f r ≤ (lowerBoxDim E).toReal + ε := by
      refine (ht.and_eventually hsmall).mono fun r hr => ?_
      exact ((log_count_div_le_iff hE hTB hr.2.1 hr.2.2 _).2 hr.1).trans htD
    exact Filter.liminf_le_of_frequently_le hfreq hbddl

/-! ## Comparison of counting functions at rescaled radii -/

/-- If the count of `F` at radius `r` is dominated by the count of `E` at radius `c r` for all
small `r`, then the upper box dimension of `F` is at most that of `E`. -/
theorem upperBoxDim_le_of_le_scale {Y : Type*} [PseudoMetricSpace Y] {F : Set Y} {E : Set X}
    {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), (Metric.externalCoveringNumber r.toNNReal F : ℝ≥0∞) ≤
      (Metric.externalCoveringNumber (c * r).toNNReal E : ℝ≥0∞)) :
    upperBoxDim F ≤ upperBoxDim E :=
  iInf_le_iInf_of_le_scale hc h

/-- If the count of `F` at radius `r` is dominated by the count of `E` at radius `c r` for all
small `r`, then the lower box dimension of `F` is at most that of `E`. -/
theorem lowerBoxDim_le_of_le_scale {Y : Type*} [PseudoMetricSpace Y] {F : Set Y} {E : Set X}
    {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), (Metric.externalCoveringNumber r.toNNReal F : ℝ≥0∞) ≤
      (Metric.externalCoveringNumber (c * r).toNNReal E : ℝ≥0∞)) :
    lowerBoxDim F ≤ lowerBoxDim E :=
  iInf_le_iInf_of_le_scale' hc h

/-! ## Proposition 4.4 (`thm:box-counting-conventions`) -/

/-- For `0 < c < 1`, every `r` below `c ^ k` lies between two consecutive powers of `c`, with
exponent at least `k`. -/
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

/-- A geometric sequence of scales tends to zero from above. -/
theorem tendsto_pow_atTop_nhdsGT_zero {c : ℝ} (hc₀ : 0 < c) (hc : c < 1) :
    Tendsto (fun n : ℕ => c ^ n) atTop (𝓝[>] (0 : ℝ)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc₀.le hc)
    (Eventually.of_forall fun n => pow_pos hc₀ n)

/-- Counting along a geometric sequence of scales bounds the upper box dimension: monotonicity of
the count in the radius controls the intermediate scales. -/
theorem upperBoxDim_le_of_geometric {E : Set X} {c : ℝ} (hc₀ : 0 < c) (hc : c < 1) {s C : ℝ≥0}
    (hC : 0 < C)
    (h : ∀ᶠ n : ℕ in atTop, (Metric.externalCoveringNumber (c ^ n).toNNReal E : ℝ≥0∞) ≤
      C * ENNReal.ofReal ((c ^ n) ^ (-(s : ℝ)))) :
    upperBoxDim E ≤ s := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 h
  have hconst : ((C * (c ^ (-(s : ℝ))).toNNReal : ℝ≥0) : ℝ≥0∞)
      = (C : ℝ≥0∞) * ENNReal.ofReal (c ^ (-(s : ℝ))) := by rw [ENNReal.coe_mul]; rfl
  refine upperBoxDim_le_of_forall (C := C * (c ^ (-(s : ℝ))).toNNReal)
    (mul_pos hC (Real.toNNReal_pos.2 (Real.rpow_pos_of_pos hc₀ _))) ?_
  filter_upwards [eventually_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (pow_pos hc₀ n₀))] with r hr0 hrlt
  have hr : (0 : ℝ) < r := hr0
  obtain ⟨n, hkn, h1, h2⟩ := exists_pow_le_le_pow hc₀ hc hr (show r < c ^ n₀ from hrlt)
  have hsplit : (c ^ (n + 1)) ^ (-(s : ℝ)) = c ^ (-(s : ℝ)) * (c ^ n) ^ (-(s : ℝ)) := by
    rw [pow_succ, Real.mul_rpow (pow_pos hc₀ n).le hc₀.le]; ring
  have hstep : (c ^ (n + 1)) ^ (-(s : ℝ)) ≤ c ^ (-(s : ℝ)) * r ^ (-(s : ℝ)) := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hr h2 (neg_nonpos.2 s.coe_nonneg))
      (Real.rpow_nonneg hc₀.le _)
  calc (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞)
      ≤ (Metric.externalCoveringNumber (c ^ (n + 1)).toNNReal E : ℝ≥0∞) :=
        ENat.toENNReal_le.2 (Metric.externalCoveringNumber_anti (Real.toNNReal_mono h1))
    _ ≤ C * ENNReal.ofReal ((c ^ (n + 1)) ^ (-(s : ℝ))) := hn₀ (n + 1) (by omega)
    _ ≤ (C : ℝ≥0∞) * ENNReal.ofReal (c ^ (-(s : ℝ)) * r ^ (-(s : ℝ))) :=
        mul_le_mul_right (ENNReal.ofReal_le_ofReal hstep) _
    _ = ((C * (c ^ (-(s : ℝ))).toNNReal : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (r ^ (-(s : ℝ))) := by
        rw [hconst, ENNReal.ofReal_mul (Real.rpow_nonneg hc₀.le _), mul_assoc]

/-- Counting along a geometric sequence of scales bounds the lower box dimension from below. -/
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

/-- Proposition 4.4 (`thm:box-counting-conventions`): the box dimensions are unchanged if the
covering numbers are replaced by the packing numbers. -/
theorem box_counting_conventions_packing (E : Set X) :
    upperBoxDim E = ⨅ (s : ℝ≥0) (_ : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
        (Metric.packingNumber r.toNNReal E : ℝ≥0∞) ≤ ENNReal.ofReal (r ^ (-(s : ℝ)))),
        (s : ℝ≥0∞) ∧
      lowerBoxDim E = ⨅ (s : ℝ≥0) (_ : ∃ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
        (Metric.packingNumber r.toNNReal E : ℝ≥0∞) ≤ ENNReal.ofReal (r ^ (-(s : ℝ)))),
        (s : ℝ≥0∞) := by
  have hc : (0 : ℝ) < ((2⁻¹ : ℝ≥0) : ℝ) := by rw [NNReal.coe_pos]; norm_num
  have h1 : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞) ≤
        (Metric.packingNumber (((2⁻¹ : ℝ≥0) : ℝ) * r).toNNReal E : ℝ≥0∞) := by
    filter_upwards with r
    refine ENat.toENNReal_le.2 ?_
    have hhalf : 2 * ((((2⁻¹ : ℝ≥0) : ℝ)) * r).toNNReal = r.toNNReal := by
      rw [Real.toNNReal_mul (NNReal.coe_nonneg _), Real.toNNReal_coe, ← mul_assoc,
        mul_inv_cancel₀ (two_ne_zero), one_mul]
    rw [← hhalf]
    exact (covering_packing_numbers _ E).1
  have h2 : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      (Metric.packingNumber r.toNNReal E : ℝ≥0∞) ≤
        (Metric.externalCoveringNumber (((2⁻¹ : ℝ≥0) : ℝ) * r).toNNReal E : ℝ≥0∞) := by
    filter_upwards with r
    refine ENat.toENNReal_le.2 ?_
    have hdiv : ((((2⁻¹ : ℝ≥0) : ℝ)) * r).toNNReal = r.toNNReal / 2 := by
      rw [Real.toNNReal_mul (NNReal.coe_nonneg _), Real.toNNReal_coe, div_eq_mul_inv, mul_comm]
    rw [hdiv]
    exact (covering_packing_numbers _ E).2
  exact ⟨le_antisymm (iInf_le_iInf_of_le_scale hc h1) (iInf_le_iInf_of_le_scale hc h2),
    le_antisymm (iInf_le_iInf_of_le_scale' hc h1) (iInf_le_iInf_of_le_scale' hc h2)⟩

/-- Proposition 4.4 (`thm:box-counting-conventions`): the box dimensions may be computed along a
geometric sequence of scales. -/
theorem box_counting_conventions_scales (E : Set X) {c : ℝ} (hc₀ : 0 < c) (hc : c < 1) :
    upperBoxDim E = ⨅ (s : ℝ≥0) (_ : ∀ᶠ n : ℕ in atTop,
        (Metric.externalCoveringNumber (c ^ n).toNNReal E : ℝ≥0∞) ≤
          ENNReal.ofReal ((c ^ n) ^ (-(s : ℝ)))), (s : ℝ≥0∞) ∧
      lowerBoxDim E = ⨅ (s : ℝ≥0) (_ : ∃ᶠ n : ℕ in atTop,
        (Metric.externalCoveringNumber (c ^ n).toNNReal E : ℝ≥0∞) ≤
          ENNReal.ofReal ((c ^ n) ^ (-(s : ℝ)))), (s : ℝ≥0∞) := by
  have htend := tendsto_pow_atTop_nhdsGT_zero hc₀ hc
  constructor
  · refine le_antisymm (le_iInf₂ fun s hs => ?_) (le_iInf₂ fun s hs => ?_)
    · exact upperBoxDim_le_of_geometric hc₀ hc one_pos (by simpa using hs)
    · exact iInf₂_le s (htend.eventually hs)
  · refine le_antisymm (le_iInf₂ fun s hs => ?_) (le_iInf₂ fun s hs => ?_)
    · refine lowerBoxDim_le_of_frequently one_pos ?_
      have hfreq := htend.frequently (p := fun r : ℝ =>
        (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞) ≤
          ENNReal.ofReal (r ^ (-(s : ℝ)))) hs
      simpa using hfreq
    · refine iInf_le_of_frequently (ρ := fun n : ℕ => c ^ n)
        (G := fun n : ℕ => (Metric.externalCoveringNumber (c ^ n).toNNReal E : ℝ≥0∞)) htend
        (C := (c ^ (-(s : ℝ))).toNNReal)
        (Real.toNNReal_pos.2 (Real.rpow_pos_of_pos hc₀ _)) ?_
      refine frequently_atTop.2 fun N => ?_
      obtain ⟨r, hPr, hr0, hrN⟩ := (hs.and_eventually (eventually_mem_nhdsWithin.and
        (nhdsWithin_le_nhds (Iio_mem_nhds (pow_pos hc₀ N))))).exists
      have hr : (0 : ℝ) < r := hr0
      obtain ⟨n, hNn, h1, h2⟩ := exists_pow_le_le_pow hc₀ hc hr (show r < c ^ N from hrN)
      refine ⟨n, hNn, ?_⟩
      have hsplit : (c ^ (n + 1)) ^ (-(s : ℝ)) = c ^ (-(s : ℝ)) * (c ^ n) ^ (-(s : ℝ)) := by
        rw [pow_succ, Real.mul_rpow (pow_pos hc₀ n).le hc₀.le]; ring
      calc (Metric.externalCoveringNumber (c ^ n).toNNReal E : ℝ≥0∞)
          ≤ (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞) :=
            ENat.toENNReal_le.2 (Metric.externalCoveringNumber_anti (Real.toNNReal_mono h2))
        _ ≤ ENNReal.ofReal (r ^ (-(s : ℝ))) := hPr
        _ ≤ ENNReal.ofReal ((c ^ (n + 1)) ^ (-(s : ℝ))) :=
            ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (pow_pos hc₀ (n + 1)) h1
              (neg_nonpos.2 s.coe_nonneg))
        _ = ((c ^ (-(s : ℝ))).toNNReal : ℝ≥0∞) * ENNReal.ofReal ((c ^ n) ^ (-(s : ℝ))) := by
            rw [hsplit, ENNReal.ofReal_mul (Real.rpow_nonneg hc₀.le _)]
            rfl

/-! ## Proposition 4.5 (`thm:box-properties`) -/

theorem upperBoxDim_mono {E F : Set X} (h : E ⊆ F) : upperBoxDim E ≤ upperBoxDim F := by
  refine upperBoxDim_le_of_le_scale (c := 1) one_pos ?_
  filter_upwards with r
  rw [one_mul]
  exact ENat.toENNReal_le.2 (Metric.externalCoveringNumber_mono_set h)

theorem lowerBoxDim_mono {E F : Set X} (h : E ⊆ F) : lowerBoxDim E ≤ lowerBoxDim F := by
  refine lowerBoxDim_le_of_le_scale (c := 1) one_pos ?_
  filter_upwards with r
  rw [one_mul]
  exact ENat.toENNReal_le.2 (Metric.externalCoveringNumber_mono_set h)

/-- Halving the radius of a cover of `E` produces a cover of its closure. -/
private lemma externalCoveringNumber_closure_half {E : Set X} :
    ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      (Metric.externalCoveringNumber r.toNNReal (closure E) : ℝ≥0∞) ≤
        (Metric.externalCoveringNumber (1 / 2 * r).toNNReal E : ℝ≥0∞) := by
  filter_upwards [eventually_mem_nhdsWithin] with r hr0
  have hp : (0 : ℝ) < r := hr0
  refine ENat.toENNReal_le.2 (externalCoveringNumber_closure_le ?_ E)
  rw [Real.toNNReal_lt_toNNReal_iff hp]
  linarith

theorem upperBoxDim_closure (E : Set X) : upperBoxDim (closure E) = upperBoxDim E :=
  le_antisymm
    (upperBoxDim_le_of_le_scale (c := 1 / 2) (by norm_num) externalCoveringNumber_closure_half)
    (upperBoxDim_mono subset_closure)

theorem lowerBoxDim_closure (E : Set X) : lowerBoxDim (closure E) = lowerBoxDim E :=
  le_antisymm
    (lowerBoxDim_le_of_le_scale (c := 1 / 2) (by norm_num) externalCoveringNumber_closure_half)
    (lowerBoxDim_mono subset_closure)

/-- A Lipschitz image needs no more balls at radius `r` than the set does at radius `r / (2L)`. -/
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

/-- Proposition 4.5 (`thm:box-properties`): box dimension does not increase under a Lipschitz
map. -/
theorem upperBoxDim_image_le {Y : Type*} [PseudoMetricSpace Y] {f : X → Y} {L : ℝ≥0} {E : Set X}
    (hf : LipschitzOnWith L f E) : upperBoxDim (f '' E) ≤ upperBoxDim E := by
  refine upperBoxDim_le_of_le_scale (c := (((2 * (L + 1))⁻¹ : ℝ≥0) : ℝ)) ?_
    (externalCoveringNumber_image_scale hf)
  rw [NNReal.coe_pos]
  exact inv_pos.2 (by positivity)

theorem lowerBoxDim_image_le {Y : Type*} [PseudoMetricSpace Y] {f : X → Y} {L : ℝ≥0} {E : Set X}
    (hf : LipschitzOnWith L f E) : lowerBoxDim (f '' E) ≤ lowerBoxDim E := by
  refine lowerBoxDim_le_of_le_scale (c := (((2 * (L + 1))⁻¹ : ℝ≥0) : ℝ)) ?_
    (externalCoveringNumber_image_scale hf)
  rw [NNReal.coe_pos]
  exact inv_pos.2 (by positivity)

/-- Proposition 4.5 (`thm:box-properties`): the upper box dimension is finitely stable. -/
theorem upperBoxDim_union (E F : Set X) :
    upperBoxDim (E ∪ F) = max (upperBoxDim E) (upperBoxDim F) := by
  refine le_antisymm ?_
    (max_le (upperBoxDim_mono subset_union_left) (upperBoxDim_mono subset_union_right))
  rcases eq_or_ne (max (upperBoxDim E) (upperBoxDim F)) ⊤ with hmax | hmax
  · rw [hmax]; exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hMε : max (upperBoxDim E) (upperBoxDim F) <
      max (upperBoxDim E) (upperBoxDim F) + (ε : ℝ≥0∞) :=
    ENNReal.lt_add_right hmax (by exact_mod_cast hε.ne')
  have hE : upperBoxDim E < max (upperBoxDim E) (upperBoxDim F) + (ε : ℝ≥0∞) :=
    lt_of_le_of_lt (le_max_left _ _) hMε
  have hF : upperBoxDim F < max (upperBoxDim E) (upperBoxDim F) + (ε : ℝ≥0∞) :=
    lt_of_le_of_lt (le_max_right _ _) hMε
  simp only [upperBoxDim, iInf_lt_iff] at hE hF
  obtain ⟨t₁, ht₁, ht₁'⟩ := hE
  obtain ⟨t₂, ht₂, ht₂'⟩ := hF
  have hEt : UpperBoxDimLE E ((max t₁ t₂ : ℝ≥0) : ℝ) :=
    ht₁.mono_exponent (by exact_mod_cast le_max_left t₁ t₂)
  have hFt : UpperBoxDimLE F ((max t₁ t₂ : ℝ≥0) : ℝ) :=
    ht₂.mono_exponent (by exact_mod_cast le_max_right t₁ t₂)
  have hunion : upperBoxDim (E ∪ F) ≤ ((max t₁ t₂ : ℝ≥0) : ℝ≥0∞) := by
    refine upperBoxDim_le_of_forall (C := 2) two_pos ?_
    filter_upwards [hEt, hFt] with r h1 h2
    calc (Metric.externalCoveringNumber r.toNNReal (E ∪ F) : ℝ≥0∞)
        ≤ ((Metric.externalCoveringNumber r.toNNReal E
            + Metric.externalCoveringNumber r.toNNReal F : ℕ∞) : ℝ≥0∞) :=
          ENat.toENNReal_le.2 (externalCoveringNumber_union_le _ _ _)
      _ = (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞)
            + (Metric.externalCoveringNumber r.toNNReal F : ℝ≥0∞) := ENat.toENNReal_add _ _
      _ ≤ ENNReal.ofReal (r ^ (-((max t₁ t₂ : ℝ≥0) : ℝ)))
            + ENNReal.ofReal (r ^ (-((max t₁ t₂ : ℝ≥0) : ℝ))) := add_le_add h1 h2
      _ = ((2 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (r ^ (-((max t₁ t₂ : ℝ≥0) : ℝ))) := by
          rw [ENNReal.coe_ofNat, two_mul]
  refine hunion.trans ?_
  rw [ENNReal.coe_max]
  exact max_le ht₁'.le ht₂'.le

/-- Proposition 4.5 (`thm:box-properties`): a subset of a finite-dimensional real normed space has
upper box dimension at most the dimension of the space. -/
theorem upperBoxDim_le_finrank {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {E : Set V} (hE : Bornology.IsBounded E) :
    upperBoxDim E ≤ Module.finrank ℝ V := by
  classical
  borelize V
  set μ : MeasureTheory.Measure V := (Module.finBasis ℝ V).addHaar with hμ
  obtain ⟨R₀, hER₀⟩ := hE.subset_closedBall (0 : V)
  have hR : (0 : ℝ) < |R₀| + 1 := by positivity
  have hER : E ⊆ ball (0 : V) (|R₀| + 1) :=
    hER₀.trans (closedBall_subset_ball (by linarith [le_abs_self R₀]))
  have hAtb : TotallyBounded E :=
    TotallyBounded.subset subset_closure hE.isCompact_closure.totallyBounded
  -- a maximal `r`-separated subset of `E` has at most `(4 R / r) ^ d` points
  have key : ∀ r : ℝ, 0 < r → r < |R₀| + 1 →
      (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞) ≤
        ENNReal.ofReal ((4 * ((|R₀| + 1) / r)) ^ Module.finrank ℝ V) := by
    intro r hr hrR
    have hrnn : 0 < r.toNNReal := Real.toNNReal_pos.2 hr
    obtain ⟨S, hSA, hSfin, hSsep, hScard⟩ :=
      Metric.exists_set_encard_eq_packingNumber (packingNumber_ne_top hAtb hrnn)
    have hNS : Metric.externalCoveringNumber r.toNNReal E ≤ S.encard := by
      rw [hScard]
      exact (Metric.externalCoveringNumber_le_coveringNumber _ _).trans
        (Metric.coveringNumber_le_packingNumber _ _)
    have hsep : ∀ c ∈ S, ∀ c' ∈ S, c ≠ c' → r < dist c c' := by
      intro c hc c' hc' hne
      have hlt : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < edist c c' := hSsep hc hc' hne
      rw [edist_dist] at hlt
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr.le).1 hlt
    have hdisj : (hSfin.toFinset : Set V).PairwiseDisjoint fun c => ball c (r / 2) := by
      rw [hSfin.coe_toFinset]
      intro c hc c' hc' hne
      refine Metric.ball_disjoint_ball ?_
      have := hsep c hc c' hc' hne
      linarith
    have hballsub : ∀ c ∈ S, ball c (r / 2) ⊆ ball (0 : V) (2 * (|R₀| + 1)) := by
      intro c hc
      refine Metric.ball_subset_ball' ?_
      have hcb : dist c 0 < |R₀| + 1 := mem_ball.1 (hER (hSA hc))
      linarith
    have hμpos : μ (ball (0 : V) 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
    have hμtop : μ (ball (0 : V) 1) ≠ ⊤ := measure_ball_lt_top.ne
    have hsum : ∑ c ∈ hSfin.toFinset, μ (ball c (r / 2))
        = (hSfin.toFinset.card : ℝ≥0∞) *
          (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ V) * μ (ball (0 : V) 1)) := by
      rw [Finset.sum_congr rfl fun c _ =>
        MeasureTheory.Measure.addHaar_ball_of_pos μ c (by positivity : (0 : ℝ) < r / 2),
        Finset.sum_const, nsmul_eq_mul]
    have hunion : μ (⋃ c ∈ hSfin.toFinset, ball c (r / 2)) ≤ μ (ball (0 : V) (2 * (|R₀| + 1))) :=
      measure_mono (Set.iUnion₂_subset fun c hc => hballsub c (by simpa using hc))
    rw [MeasureTheory.measure_biUnion_finset hdisj fun c _ => measurableSet_ball, hsum,
      MeasureTheory.Measure.addHaar_ball_of_pos μ (0 : V)
        (by linarith : (0 : ℝ) < 2 * (|R₀| + 1)), ← mul_assoc] at hunion
    have hcancel : (hSfin.toFinset.card : ℝ≥0∞) * ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ V)
        ≤ ENNReal.ofReal ((2 * (|R₀| + 1)) ^ Module.finrank ℝ V) :=
      (ENNReal.mul_le_mul_iff_left hμpos hμtop).1 hunion
    have hprod : ENNReal.ofReal ((4 * ((|R₀| + 1) / r)) ^ Module.finrank ℝ V) *
        ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ V)
        = ENNReal.ofReal ((2 * (|R₀| + 1)) ^ Module.finrank ℝ V) := by
      rw [← ENNReal.ofReal_mul (pow_nonneg (by positivity) _), ← mul_pow]
      congr 2
      field_simp
      ring
    have hcard : (hSfin.toFinset.card : ℝ≥0∞)
        ≤ ENNReal.ofReal ((4 * ((|R₀| + 1) / r)) ^ Module.finrank ℝ V) := by
      rw [← hprod] at hcancel
      refine (ENNReal.mul_le_mul_iff_left ?_ (by simp)).1 hcancel
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    calc (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞)
        ≤ (S.encard : ℝ≥0∞) := by exact_mod_cast hNS
      _ = (hSfin.toFinset.card : ℝ≥0∞) := by
          rw [hSfin.encard_eq_coe_toFinset_card]; simp
      _ ≤ _ := hcard
  -- the counting bound is the required power bound
  have hmain : upperBoxDim E ≤ ((Module.finrank ℝ V : ℝ≥0) : ℝ≥0∞) := by
    refine upperBoxDim_le_of_forall
      (C := ((4 * (|R₀| + 1)) ^ Module.finrank ℝ V).toNNReal)
      (Real.toNNReal_pos.2 (pow_pos (by linarith) _)) ?_
    filter_upwards [eventually_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hR)]
      with r hr0 hrR
    have hr : (0 : ℝ) < r := hr0
    refine (key r hr hrR).trans (le_of_eq ?_)
    have hexp : (4 * ((|R₀| + 1) / r)) ^ Module.finrank ℝ V
        = (4 * (|R₀| + 1)) ^ Module.finrank ℝ V * (r ^ Module.finrank ℝ V)⁻¹ := by
      field_simp
      rw [← mul_pow, div_mul_cancel₀ _ hr.ne']
    have hrpow : r ^ (-((Module.finrank ℝ V : ℝ≥0) : ℝ)) = (r ^ Module.finrank ℝ V)⁻¹ := by
      rw [NNReal.coe_natCast, Real.rpow_neg hr.le, Real.rpow_natCast]
    rw [hexp, hrpow, show ((((4 * (|R₀| + 1)) ^ Module.finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞)
        = ENNReal.ofReal ((4 * (|R₀| + 1)) ^ Module.finrank ℝ V) from rfl,
      ← ENNReal.ofReal_mul (pow_nonneg (by linarith) _)]
  exact hmain.trans_eq (by norm_cast)

/-! ## Examples 4.6 and 4.7 -/

/-- A subdivision covers an interval by `⌊(b - a) / (2r)⌋ + 1` closed balls of radius `r`. -/
theorem externalCoveringNumber_Icc_le {a b r : ℝ} (hr : 0 < r) :
    Metric.externalCoveringNumber r.toNNReal (Icc a b) ≤
      ((⌊(b - a) / (2 * r)⌋₊ + 1 : ℕ) : ℕ∞) := by
  have h2r : (0 : ℝ) < 2 * r := by linarith
  have hcov : Metric.IsCover r.toNNReal (Icc a b)
      ((fun k : ℕ => a + (2 * (k : ℝ) + 1) * r) ''
        ↑(Finset.range (⌊(b - a) / (2 * r)⌋₊ + 1))) := by
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
  refine hcov.externalCoveringNumber_le_encard.trans ?_
  refine (Set.encard_image_le _ _).trans ?_
  rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_range]

/-- Example 4.6 (`ex:box-interval-cantor`): a non-degenerate interval has box dimension one. -/
theorem box_interval {a b : ℝ} (hab : a < b) :
    lowerBoxDim (Icc a b) = 1 ∧ upperBoxDim (Icc a b) = 1 := by
  have hba : (0 : ℝ) < b - a := by linarith
  -- a subdivision into `(b - a) / (2r) + 1` intervals of length `2r` covers `[a, b]`
  have hupper : upperBoxDim (Icc a b) ≤ 1 := by
    refine upperBoxDim_le_of_forall (s := 1) (C := ((b - a) / 2 + 1).toNNReal)
      (Real.toNNReal_pos.2 (by linarith)) ?_
    filter_upwards [eventually_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one' ℝ))] with r hr0 hr1
    have hr : (0 : ℝ) < r := hr0
    have hr1' : r < 1 := hr1
    have h2r : (0 : ℝ) < 2 * r := by linarith
    have hN := externalCoveringNumber_Icc_le (a := a) (b := b) hr
    have hreal : ((⌊(b - a) / (2 * r)⌋₊ : ℕ) : ℝ) + 1 ≤ ((b - a) / 2 + 1) * r⁻¹ := by
      have h1 : ((⌊(b - a) / (2 * r)⌋₊ : ℕ) : ℝ) ≤ (b - a) / 2 * r⁻¹ := by
        refine (Nat.floor_le (div_nonneg hba.le h2r.le)).trans (le_of_eq ?_)
        field_simp
      have hinv : (0 : ℝ) < r⁻¹ := inv_pos.2 hr
      have h2 : (1 : ℝ) ≤ r⁻¹ := by nlinarith [mul_inv_cancel₀ hr.ne']
      nlinarith [h1, h2]
    calc (Metric.externalCoveringNumber r.toNNReal (Icc a b) : ℝ≥0∞)
        ≤ ((⌊(b - a) / (2 * r)⌋₊ + 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast ENat.toENNReal_le.2 hN
      _ = ENNReal.ofReal (((⌊(b - a) / (2 * r)⌋₊ : ℕ) : ℝ) + 1) := by
          rw [show (((⌊(b - a) / (2 * r)⌋₊ : ℕ) : ℝ) + 1)
            = ((⌊(b - a) / (2 * r)⌋₊ + 1 : ℕ) : ℝ) by push_cast; ring]
          exact (ENNReal.ofReal_natCast _).symm
      _ ≤ ENNReal.ofReal (((b - a) / 2 + 1) * r⁻¹) := ENNReal.ofReal_le_ofReal hreal
      _ = (((b - a) / 2 + 1).toNNReal : ℝ≥0∞) * ENNReal.ofReal (r ^ (-(1 : ℝ))) := by
          rw [Real.rpow_neg_one, show ((((b - a) / 2 + 1).toNNReal : ℝ≥0) : ℝ≥0∞)
              = ENNReal.ofReal ((b - a) / 2 + 1) from rfl,
            ← ENNReal.ofReal_mul (by linarith)]
  -- a cover by `N` balls of radius `r` has total length at least `b - a`
  have hlower : (1 : ℝ≥0∞) ≤ lowerBoxDim (Icc a b) := by
    have h1 : ((1 : ℝ≥0) : ℝ≥0∞) = 1 := by norm_num
    rw [← h1]
    refine le_lowerBoxDim_of_forall (s := 1) (C := ((b - a) / 2).toNNReal)
      (Real.toNNReal_pos.2 (by linarith)) ?_
    filter_upwards [eventually_mem_nhdsWithin] with r hr0
    have hr : (0 : ℝ) < r := hr0
    rcases eq_or_ne (Metric.externalCoveringNumber r.toNNReal (Icc a b)) ⊤ with htop | htop
    · rw [htop]
      simp
    obtain ⟨C, hCfin, hC, hCcard⟩ := exists_isCover_encard_eq htop
    have hsub : Icc a b ⊆ ⋃ c ∈ hCfin.toFinset, closedBall c r := by
      have h := hC.subset_iUnion_closedBall
      rw [Real.coe_toNNReal r hr.le] at h
      refine h.trans (Set.iUnion₂_subset fun c hc => ?_)
      exact Set.subset_biUnion_of_mem (u := fun c => closedBall c r) (by simpa using hc)
    have hvol : ENNReal.ofReal (b - a)
        ≤ ((hCfin.toFinset.card : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 * r) := by
      calc ENNReal.ofReal (b - a) = MeasureTheory.volume (Icc a b) := Real.volume_Icc.symm
        _ ≤ MeasureTheory.volume (⋃ c ∈ hCfin.toFinset, closedBall c r) := measure_mono hsub
        _ ≤ ∑ c ∈ hCfin.toFinset, MeasureTheory.volume (closedBall c r) :=
            measure_biUnion_finset_le _ _
        _ = ((hCfin.toFinset.card : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 * r) := by
            simp [Real.volume_closedBall, Finset.sum_const, nsmul_eq_mul]
    have hvol' : b - a ≤ ((hCfin.toFinset.card : ℕ) : ℝ) * (2 * r) := by
      rw [show ((hCfin.toFinset.card : ℕ) : ℝ≥0∞)
          = ENNReal.ofReal ((hCfin.toFinset.card : ℕ) : ℝ) from (ENNReal.ofReal_natCast _).symm,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hvol
      exact (ENNReal.ofReal_le_ofReal_iff
        (mul_nonneg (Nat.cast_nonneg _) (by linarith))).1 hvol
    have hcard : ((hCfin.toFinset.card : ℕ) : ℝ≥0∞)
        = (Metric.externalCoveringNumber r.toNNReal (Icc a b) : ℝ≥0∞) := by
      rw [← hCcard, hCfin.encard_eq_coe_toFinset_card]
      simp
    rw [← hcard]
    have hreal : ((b - a) / 2) * r⁻¹ ≤ ((hCfin.toFinset.card : ℕ) : ℝ) := by
      have hinv : (0 : ℝ) < r⁻¹ := inv_pos.2 hr
      nlinarith [mul_inv_cancel₀ hr.ne', hvol']
    calc (((b - a) / 2).toNNReal : ℝ≥0∞) * ENNReal.ofReal (r ^ (-(1 : ℝ)))
        = ENNReal.ofReal ((b - a) / 2 * r⁻¹) := by
          rw [Real.rpow_neg_one, show ((((b - a) / 2).toNNReal : ℝ≥0) : ℝ≥0∞)
              = ENNReal.ofReal ((b - a) / 2) from rfl,
            ← ENNReal.ofReal_mul (by linarith)]
      _ ≤ ENNReal.ofReal ((hCfin.toFinset.card : ℕ) : ℝ) := ENNReal.ofReal_le_ofReal hreal
      _ = ((hCfin.toFinset.card : ℕ) : ℝ≥0∞) := ENNReal.ofReal_natCast _
  exact ⟨le_antisymm ((lowerBoxDim_le_upperBoxDim _).trans hupper) hlower,
    le_antisymm hupper (hlower.trans (lowerBoxDim_le_upperBoxDim _))⟩

/-- Example 4.6 (`ex:box-interval-cantor`): the middle-third Cantor set has box dimension
`log 2 / log 3`. -/
theorem box_cantor :
    lowerBoxDim cantorSet = ENNReal.ofReal (Real.log 2 / Real.log 3) ∧
      upperBoxDim cantorSet = ENNReal.ofReal (Real.log 2 / Real.log 3) := by
  have ha₀ : (0 : ℝ) < 1 / 3 := by norm_num
  have ha1 : (1 : ℝ) / 3 < 1 := by norm_num
  have hlog : Real.log ((1 : ℝ) / 3)⁻¹ = Real.log 3 := by norm_num
  set s : ℝ := Real.log 2 / Real.log 3 with hs
  have hs0 : 0 < s := by
    have h := log_two_div_log_inv_pos ha₀ ha1
    rwa [hlog] at h
  set σ : ℝ≥0 := s.toNNReal with hσ
  have hσs : (σ : ℝ) = s := Real.coe_toNNReal s hs0.le
  have hpow : ∀ n : ℕ, ((1 / 3 : ℝ) ^ n) ^ (-s) = 2 ^ n := by
    intro n
    have h := pow_rpow_log_two_div_log_inv ha₀ ha1 n
    rw [hlog, ← hs] at h
    rw [Real.rpow_neg (pow_nonneg ha₀.le n), h, inv_pow, inv_inv]
  -- the `2 ^ n` construction intervals of level `n` cover the Cantor set
  have hup : upperBoxDim cantorSet ≤ (σ : ℝ≥0∞) := by
    refine upperBoxDim_le_of_geometric (c := 1 / 3) ha₀ ha1 (C := 1) one_pos ?_
    refine Eventually.of_forall fun n => ?_
    rw [ENNReal.coe_one, one_mul, hσs, hpow n]
    have hcov : Metric.IsCover ((1 / 3 : ℝ) ^ n).toNNReal cantorSet
        ((fun f : Fin n → Bool => cantorLeft (1 / 3) (List.ofFn f)) ''
          ↑(Finset.univ : Finset (Fin n → Bool))) := by
      refine Metric.IsCover.of_subset_iUnion_closedBall ?_
      intro x hx
      rw [← symmetricCantorSet_one_third] at hx
      obtain ⟨w, hw, hxw⟩ := mem_cantorLevel.1 (symmetricCantorSet_subset_cantorLevel n hx)
      subst hw
      refine Set.mem_biUnion
        (Set.mem_image_of_mem _ (Finset.mem_coe.2 (Finset.mem_univ w.get))) ?_
      rw [List.ofFn_get, Real.coe_toNNReal _ (pow_nonneg ha₀.le _)]
      exact cantorInterval_subset_closedBall ha₀.le
        (cantorLeft_mem_cantorInterval ha₀.le w) hxw
    have hN : Metric.externalCoveringNumber ((1 / 3 : ℝ) ^ n).toNNReal cantorSet
        ≤ ((2 ^ n : ℕ) : ℕ∞) := by
      refine hcov.externalCoveringNumber_le_encard.trans ?_
      refine (Set.encard_image_le _ _).trans ?_
      rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_univ, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin]
    calc (Metric.externalCoveringNumber ((1 / 3 : ℝ) ^ n).toNNReal cantorSet : ℝ≥0∞)
        ≤ ((2 ^ n : ℕ) : ℝ≥0∞) := by exact_mod_cast ENat.toENNReal_le.2 hN
      _ = ENNReal.ofReal ((2 : ℝ) ^ n) := by
          rw [← ENNReal.ofReal_natCast]
          norm_num
  -- the `2 ^ (n-1)` construction intervals of level `n - 1` are `3 ^ (1-n)`-separated
  have hlow : (σ : ℝ≥0∞) ≤ lowerBoxDim cantorSet := by
    refine le_lowerBoxDim_of_geometric (c := 1 / 3) ha₀ ha1 (C := 1 / 2) (by norm_num) ?_
    rw [eventually_atTop]
    refine ⟨2, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    set ω : (Fin (k + 1) → Bool) → ℕ → Bool :=
      fun f j => if h : j < k + 1 then f ⟨j, h⟩ else false with hω
    set p : (Fin (k + 1) → Bool) → ℝ := fun f => cantorCode (1 / 3) (ω f) with hp
    have hpmem : ∀ f, p f ∈ cantorInterval (1 / 3) (List.ofFn f) := by
      intro f
      have h := cantorCode_mem_cantorInterval ha₀.le ha1 (k + 1) (ω f)
      have hfun : (fun i : Fin (k + 1) => ω f (i : ℕ)) = f := by
        funext i
        simp only [hω, dif_pos i.isLt]
      rwa [hfun] at h
    have hpcantor : ∀ f, p f ∈ cantorSet := by
      intro f
      rw [← symmetricCantorSet_one_third]
      exact cantorCode_mem_symmetricCantorSet ha₀.le ha1 (ω f)
    have hsep : ∀ f g : Fin (k + 1) → Bool, f ≠ g → (1 / 3 : ℝ) ^ (k + 1) ≤ |p f - p g| := by
      intro f g hfg
      have hne : List.ofFn f ≠ List.ofFn g := fun h => hfg (List.ofFn_injective h)
      have h := le_abs_sub_of_mem_cantorInterval ha₀.le (by norm_num)
        List.length_ofFn List.length_ofFn hne (hpmem f) (hpmem g)
      calc (1 / 3 : ℝ) ^ (k + 1) = (1 - 2 * (1 / 3)) * (1 / 3) ^ k := by ring
        _ ≤ |p f - p g| := h
    have hSsep : Metric.IsSeparated ((2 * ((1 / 3 : ℝ) ^ (k + 2)).toNNReal : ℝ≥0))
        ((fun f : Fin (k + 1) → Bool => p f) ''
          ↑(Finset.univ : Finset (Fin (k + 1) → Bool))) := by
      rintro x ⟨f, -, rfl⟩ y ⟨g, -, rfl⟩ hxy
      have hfg : f ≠ g := fun h => hxy (by rw [h])
      have h1 : (2 : ℝ≥0) * ((1 / 3 : ℝ) ^ (k + 2)).toNNReal
          = ((2 * (1 / 3 : ℝ) ^ (k + 2) : ℝ)).toNNReal := by
        rw [Real.toNNReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      rw [edist_dist, Real.dist_eq, h1,
        show ((((2 * (1 / 3 : ℝ) ^ (k + 2) : ℝ)).toNNReal : ℝ≥0) : ℝ≥0∞)
          = ENNReal.ofReal (2 * (1 / 3 : ℝ) ^ (k + 2)) from rfl,
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)]
      have hp1 : (0 : ℝ) < (1 / 3 : ℝ) ^ (k + 1) := pow_pos ha₀ _
      have heq : (1 / 3 : ℝ) ^ (k + 2) = (1 / 3) * (1 / 3 : ℝ) ^ (k + 1) := by ring
      linarith [hsep f g hfg]
    have hinj : Set.InjOn (fun f : Fin (k + 1) → Bool => p f)
        ↑(Finset.univ : Finset (Fin (k + 1) → Bool)) := by
      intro f _ g _ hfg
      by_contra hne
      have h := hsep f g hne
      rw [show p f = p g from hfg, sub_self, abs_zero] at h
      exact absurd h (not_le.2 (pow_pos ha₀ _))
    have hScard : ((fun f : Fin (k + 1) → Bool => p f) ''
        ↑(Finset.univ : Finset (Fin (k + 1) → Bool))).encard = ((2 ^ (k + 1) : ℕ) : ℕ∞) := by
      rw [hinj.encard_image, Set.encard_coe_eq_coe_finsetCard, Finset.card_univ,
        Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    have hbound : ((2 ^ (k + 1) : ℕ) : ℕ∞)
        ≤ Metric.externalCoveringNumber ((1 / 3 : ℝ) ^ (k + 2)).toNNReal cantorSet := by
      rw [← hScard]
      refine encard_le_externalCoveringNumber ?_ hSsep
      rintro x ⟨f, -, rfl⟩
      exact hpcantor f
    rw [hσs, hpow (k + 2)]
    calc ((1 / 2 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (k + 2))
        = ((2 ^ (k + 1) : ℕ) : ℝ≥0∞) := by
          rw [show ((1 / 2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (1 / 2) by
              rw [← ENNReal.ofReal_coe_nnreal]; norm_num,
            ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_natCast]
          congr 1
          push_cast
          ring
      _ ≤ _ := by exact_mod_cast ENat.toENNReal_le.2 hbound
  exact ⟨le_antisymm ((lowerBoxDim_le_upperBoxDim _).trans hup) hlow,
    le_antisymm hup (hlow.trans (lowerBoxDim_le_upperBoxDim _))⟩

/-- Example 4.7 (`ex:reciprocal-sequence`): the compact countable set `{0} ∪ {1/n}` has box
dimension `1/2`. -/
theorem box_reciprocal_sequence :
    lowerBoxDim (insert (0 : ℝ) (Set.range fun n : ℕ => ((n : ℝ) + 1)⁻¹)) =
        ENNReal.ofReal (1 / 2) ∧
      upperBoxDim (insert (0 : ℝ) (Set.range fun n : ℕ => ((n : ℝ) + 1)⁻¹)) =
        ENNReal.ofReal (1 / 2) := by
  set E : Set ℝ := insert (0 : ℝ) (Set.range fun n : ℕ => ((n : ℝ) + 1)⁻¹) with hE
  set σ : ℝ≥0 := (1 / 2 : ℝ).toNNReal with hσ
  have hσs : (σ : ℝ) = 1 / 2 := Real.coe_toNNReal _ (by norm_num)
  have hrpow : ∀ r : ℝ, 0 < r → r ^ (-(σ : ℝ)) = (Real.sqrt r)⁻¹ := by
    intro r hr
    rw [hσs, Real.rpow_neg hr.le, ← Real.sqrt_eq_rpow]
  -- the first `⌈r^{-1/2}⌉` points separately, the rest in a short interval
  have hup : upperBoxDim E ≤ (σ : ℝ≥0∞) := by
    refine upperBoxDim_le_of_forall (C := (7 / 2 : ℝ≥0)) (by norm_num) ?_
    filter_upwards [eventually_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one' ℝ))] with r hr0 hr1
    have hr : (0 : ℝ) < r := hr0
    have hr1' : r < 1 := hr1
    have ht : (0 : ℝ) < Real.sqrt r := Real.sqrt_pos.2 hr
    have ht2 : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
    have ht1 : Real.sqrt r < 1 := by nlinarith
    have hinv1 : (1 : ℝ) ≤ (Real.sqrt r)⁻¹ := by
      have h := mul_le_mul_of_nonneg_left ht1.le (le_of_lt (inv_pos.2 ht))
      rwa [mul_one, inv_mul_cancel₀ ht.ne'] at h
    set m : ℕ := ⌈(Real.sqrt r)⁻¹⌉₊ with hm
    have hm1 : (Real.sqrt r)⁻¹ ≤ (m : ℝ) := Nat.le_ceil _
    have hm2 : (m : ℝ) < (Real.sqrt r)⁻¹ + 1 := Nat.ceil_lt_add_one (by positivity)
    have hmpos : 0 < m := by
      rw [hm]
      exact Nat.ceil_pos.2 (by linarith)
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
    have hsub : E ⊆ ((fun n : ℕ => ((n : ℝ) + 1)⁻¹) '' ↑(Finset.range m)) ∪
        Icc 0 (((m : ℝ) + 1)⁻¹) := by
      rw [hE]
      rintro x (rfl | ⟨n, rfl⟩)
      · exact Or.inr ⟨le_rfl, by positivity⟩
      · by_cases hn : n < m
        · exact Or.inl ⟨n, by simpa using hn, rfl⟩
        · rw [not_lt] at hn
          have hmn : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
            have h : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
            linarith
          exact Or.inr ⟨by positivity,
            show ((n : ℝ) + 1)⁻¹ ≤ ((m : ℝ) + 1)⁻¹ by gcongr⟩
    have hNA : Metric.externalCoveringNumber r.toNNReal
        ((fun n : ℕ => ((n : ℝ) + 1)⁻¹) '' ↑(Finset.range m)) ≤ ((m : ℕ) : ℕ∞) := by
      refine (Metric.externalCoveringNumber_le_encard_self _).trans ?_
      refine (Set.encard_image_le _ _).trans ?_
      rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_range]
    have hNE : Metric.externalCoveringNumber r.toNNReal E ≤
        ((m : ℕ) : ℕ∞) + ((⌊(((m : ℝ) + 1)⁻¹ - 0) / (2 * r)⌋₊ + 1 : ℕ) : ℕ∞) :=
      (Metric.externalCoveringNumber_mono_set hsub).trans
        ((externalCoveringNumber_union_le _ _ _).trans
          (add_le_add hNA (externalCoveringNumber_Icc_le hr)))
    have hinvm : ((m : ℝ))⁻¹ ≤ Real.sqrt r := by
      have h1 : (1 : ℝ) ≤ (m : ℝ) * Real.sqrt r := by
        have h := mul_le_mul_of_nonneg_right hm1 ht.le
        rwa [inv_mul_cancel₀ ht.ne'] at h
      have h3 := mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.2 hm0))
      rwa [mul_one, ← mul_assoc, inv_mul_cancel₀ hm0.ne', one_mul] at h3
    have hmulinv : (Real.sqrt r)⁻¹ * Real.sqrt r = 1 := inv_mul_cancel₀ ht.ne'
    have hfloor : (⌊(((m : ℝ) + 1)⁻¹ - 0) / (2 * r)⌋₊ : ℝ) ≤ (Real.sqrt r)⁻¹ / 2 := by
      rw [sub_zero]
      refine (Nat.floor_le (by positivity)).trans ?_
      have hmm : (((m : ℝ) + 1))⁻¹ ≤ ((m : ℝ))⁻¹ := by
        gcongr
        linarith
      have hrhs : (Real.sqrt r)⁻¹ * (2 * r) = 2 * Real.sqrt r := by
        calc (Real.sqrt r)⁻¹ * (2 * r)
            = (Real.sqrt r)⁻¹ * (2 * (Real.sqrt r * Real.sqrt r)) := by rw [ht2]
          _ = 2 * ((Real.sqrt r)⁻¹ * Real.sqrt r) * Real.sqrt r := by ring
          _ = 2 * Real.sqrt r := by rw [hmulinv]; ring
      calc (((m : ℝ) + 1))⁻¹ / (2 * r) ≤ ((m : ℝ))⁻¹ / (2 * r) := by gcongr
        _ ≤ Real.sqrt r / (2 * r) := by gcongr
        _ ≤ (Real.sqrt r)⁻¹ / 2 := by
            rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 2 * r) (by norm_num : (0 : ℝ) < 2),
              hrhs]
            exact le_of_eq (by ring)
    have htotal : ((m : ℝ) + ((⌊(((m : ℝ) + 1)⁻¹ - 0) / (2 * r)⌋₊ : ℝ) + 1))
        ≤ 7 / 2 * (Real.sqrt r)⁻¹ := by linarith
    calc (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞)
        ≤ ((m : ℕ) : ℝ≥0∞) + ((⌊(((m : ℝ) + 1)⁻¹ - 0) / (2 * r)⌋₊ + 1 : ℕ) : ℝ≥0∞) := by
          have h := ENat.toENNReal_le.2 hNE
          rwa [ENat.toENNReal_add] at h
      _ = ENNReal.ofReal ((m : ℝ) + ((⌊(((m : ℝ) + 1)⁻¹ - 0) / (2 * r)⌋₊ : ℝ) + 1)) := by
          rw [← ENNReal.ofReal_natCast m,
            ← ENNReal.ofReal_natCast (⌊(((m : ℝ) + 1)⁻¹ - 0) / (2 * r)⌋₊ + 1),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          push_cast
          ring
      _ ≤ ENNReal.ofReal (7 / 2 * (Real.sqrt r)⁻¹) := ENNReal.ofReal_le_ofReal htotal
      _ = ((7 / 2 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (r ^ (-(σ : ℝ))) := by
          rw [hrpow r hr, show ((7 / 2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (7 / 2) by
              rw [← ENNReal.ofReal_coe_nnreal]; norm_num,
            ← ENNReal.ofReal_mul (by norm_num)]
  -- the first `⌊r^{-1/2}/4⌋` reciprocals are `2r`-separated
  have hlow : (σ : ℝ≥0∞) ≤ lowerBoxDim E := by
    refine le_lowerBoxDim_of_forall (C := (1 / 8 : ℝ≥0)) (by norm_num) ?_
    filter_upwards [eventually_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 / 64 by norm_num))] with r hr0 hr1
    have hr : (0 : ℝ) < r := hr0
    have hr1' : r < 1 / 64 := hr1
    have ht : (0 : ℝ) < Real.sqrt r := Real.sqrt_pos.2 hr
    have ht2 : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
    have ht8 : Real.sqrt r < 1 / 8 := by nlinarith
    have hinvpos : (0 : ℝ) < (Real.sqrt r)⁻¹ := inv_pos.2 ht
    have hmul : (Real.sqrt r)⁻¹ * Real.sqrt r = 1 := inv_mul_cancel₀ ht.ne'
    have hinv8 : (8 : ℝ) < (Real.sqrt r)⁻¹ := by nlinarith
    set k : ℕ := ⌊(Real.sqrt r)⁻¹ / 4⌋₊ with hk
    have hk1 : (k : ℝ) ≤ (Real.sqrt r)⁻¹ / 4 := Nat.floor_le (by positivity)
    have hk2 : (Real.sqrt r)⁻¹ / 4 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hkpos : 0 < k := by
      rw [hk]
      exact Nat.floor_pos.2 (by linarith)
    have hsq : ((Real.sqrt r)⁻¹ / 4) * ((Real.sqrt r)⁻¹ / 4) * (16 * r) = 1 := by
      have h4 : (Real.sqrt r)⁻¹ * (Real.sqrt r)⁻¹ * (Real.sqrt r * Real.sqrt r) = 1 := by
        field_simp
      calc ((Real.sqrt r)⁻¹ / 4) * ((Real.sqrt r)⁻¹ / 4) * (16 * r)
          = (Real.sqrt r)⁻¹ * (Real.sqrt r)⁻¹ * (Real.sqrt r * Real.sqrt r) := by
            rw [ht2]; ring
        _ = 1 := h4
    have hk16 : (k : ℝ) * (k : ℝ) * (16 * r) ≤ 1 := by
      calc (k : ℝ) * (k : ℝ) * (16 * r)
          ≤ ((Real.sqrt r)⁻¹ / 4) * ((Real.sqrt r)⁻¹ / 4) * (16 * r) := by
            have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
            gcongr
        _ = 1 := hsq
    have hkey : ∀ i j : ℕ, i < k → j < k → i < j →
        2 * r < ((i : ℝ) + 1)⁻¹ - ((j : ℝ) + 1)⁻¹ := by
      intro i j hi hj hij
      have hi1 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have hik : ((i : ℝ) + 1) ≤ (k : ℝ) := by exact_mod_cast hi
      have hjk : ((j : ℝ) + 1) ≤ (k : ℝ) := by exact_mod_cast hj
      have hji : (1 : ℝ) ≤ (j : ℝ) - (i : ℝ) := by
        have h : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
        linarith
      have hdiff : ((i : ℝ) + 1)⁻¹ - ((j : ℝ) + 1)⁻¹
          = ((j : ℝ) - (i : ℝ)) / (((i : ℝ) + 1) * ((j : ℝ) + 1)) := by
        field_simp
        ring
      rw [hdiff, lt_div_iff₀ (by positivity)]
      have hprod : ((i : ℝ) + 1) * ((j : ℝ) + 1) ≤ (k : ℝ) * (k : ℝ) :=
        mul_le_mul hik hjk (by positivity) (by positivity)
      have hmain := mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ 2 * r)
      nlinarith
    have hSsub : ((fun n : ℕ => ((n : ℝ) + 1)⁻¹) '' ↑(Finset.range k)) ⊆ E := by
      rw [hE]
      rintro x ⟨n, -, rfl⟩
      exact Or.inr ⟨n, rfl⟩
    have hSsep : Metric.IsSeparated ((2 * r.toNNReal : ℝ≥0))
        ((fun n : ℕ => ((n : ℝ) + 1)⁻¹) '' ↑(Finset.range k)) := by
      rintro x ⟨i, hi, rfl⟩ y ⟨j, hj, rfl⟩ hxy
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      have h1 : (2 * r.toNNReal : ℝ≥0) = ((2 * r : ℝ)).toNNReal := by
        rw [Real.toNNReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      rw [edist_dist, Real.dist_eq, h1,
        show ((((2 * r : ℝ)).toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (2 * r) from rfl,
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)]
      rcases lt_trichotomy i j with h | h | h
      · have hpos := hkey i j hi hj h
        rw [abs_of_pos (by linarith)]
        exact hpos
      · exact absurd (by rw [h]) hxy
      · have hpos := hkey j i hj hi h
        rw [abs_sub_comm, abs_of_pos (by linarith)]
        exact hpos
    have hinj : Set.InjOn (fun n : ℕ => ((n : ℝ) + 1)⁻¹) ↑(Finset.range k) := by
      intro i _ j _ hij
      have h := inv_injective hij
      have h' : (i : ℝ) = (j : ℝ) := by linarith
      exact_mod_cast h'
    have hScard : ((fun n : ℕ => ((n : ℝ) + 1)⁻¹) '' ↑(Finset.range k)).encard
        = ((k : ℕ) : ℕ∞) := by
      rw [hinj.encard_image, Set.encard_coe_eq_coe_finsetCard, Finset.card_range]
    have hbound : ((k : ℕ) : ℕ∞) ≤ Metric.externalCoveringNumber r.toNNReal E := by
      rw [← hScard]
      exact encard_le_externalCoveringNumber hSsub hSsep
    rw [hrpow r hr]
    have hfinal : (1 / 8 : ℝ) * (Real.sqrt r)⁻¹ ≤ (k : ℝ) := by linarith
    calc ((1 / 8 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal ((Real.sqrt r)⁻¹)
        = ENNReal.ofReal ((1 / 8 : ℝ) * (Real.sqrt r)⁻¹) := by
          rw [show ((1 / 8 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (1 / 8) by
              rw [← ENNReal.ofReal_coe_nnreal]; norm_num,
            ← ENNReal.ofReal_mul (by norm_num)]
      _ ≤ ENNReal.ofReal ((k : ℝ)) := ENNReal.ofReal_le_ofReal hfinal
      _ = ((k : ℕ) : ℝ≥0∞) := ENNReal.ofReal_natCast _
      _ ≤ _ := by exact_mod_cast ENat.toENNReal_le.2 hbound
  exact ⟨le_antisymm ((lowerBoxDim_le_upperBoxDim _).trans hup) hlow,
    le_antisymm hup (hlow.trans (lowerBoxDim_le_upperBoxDim _))⟩

/-! ## Proposition 4.8 (`thm:hausdorff-lower-box`) -/

/-- Proposition 4.8 (`thm:hausdorff-lower-box`): the Hausdorff dimension is at most the lower box
dimension. -/
theorem hausdorff_lower_box {Y : Type*} [MetricSpace Y] (E : Set Y) :
    dimH E ≤ lowerBoxDim E := by
  rw [dimH_eq_iInf_hausdorffContent]
  refine le_iInf₂ fun t ht => ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεpos : (0 : ℝ) < (ε : ℝ) := hε
  set u : ℝ := ((t + ε : ℝ≥0) : ℝ) with hu
  have hu0 : (0 : ℝ) ≤ u := (t + ε).coe_nonneg
  -- a cover by `N_r(E)` balls of radius `r` bounds the content at exponent `u`
  have main : ∀ r : ℝ, 0 < r →
      (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞) ≤ ENNReal.ofReal (r ^ (-(t : ℝ))) →
      hausdorffContent u E ≤ ENNReal.ofReal (2 ^ u * r ^ (ε : ℝ)) := by
    intro r hr hNr
    have htop : Metric.externalCoveringNumber r.toNNReal E ≠ ⊤ := by
      intro h
      rw [h, ENat.toENNReal_top, top_le_iff] at hNr
      exact ENNReal.ofReal_ne_top hNr
    obtain ⟨C, hCfin, hC, hCcard⟩ := exists_isCover_encard_eq htop
    have hsub : E ⊆ ⋃ c ∈ hCfin.toFinset, closedBall c r := by
      have h := hC.subset_iUnion_closedBall
      rw [Real.coe_toNNReal r hr.le] at h
      exact h.trans (Set.iUnion₂_subset fun c hc =>
        Set.subset_biUnion_of_mem (u := fun c => closedBall c r) (by simpa using hc))
    have hOM := (hausdorff_outer_measures (X := Y) (fun s : ℝ≥0∞ => s ^ u) zero_lt_one).2.1
    have hediam : ∀ c : Y, ediam (closedBall c r) ≤ ENNReal.ofReal (2 * r) := by
      intro c
      refine Metric.ediam_le fun y hy z hz => ?_
      rw [edist_dist]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [mem_closedBall] at hy hz
      have h1 := dist_triangle y c z
      rw [dist_comm c z] at h1
      linarith
    have hcard : ((hCfin.toFinset.card : ℕ) : ℝ≥0∞)
        = (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞) := by
      rw [← hCcard, hCfin.encard_eq_coe_toFinset_card]
      simp
    have hue : -(t : ℝ) + u = (ε : ℝ) := by rw [hu]; push_cast; ring
    have hcalc : r ^ (-(t : ℝ)) * (2 * r) ^ u = 2 ^ u * r ^ (ε : ℝ) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le, ← mul_assoc,
        mul_comm (r ^ (-(t : ℝ))), mul_assoc, ← Real.rpow_add hr, hue]
    calc hausdorffContent u E
        ≤ hausdorffContent u (⋃ c ∈ hCfin.toFinset, closedBall c r) := hOM.mono hsub
      _ ≤ ∑ c ∈ hCfin.toFinset, hausdorffContent u (closedBall c r) := by
          have h := measure_biUnion_finset_le (μ := hOM.toOuterMeasure) hCfin.toFinset
            (fun c => closedBall c r)
          simpa only [hOM.coe_toOuterMeasure] using h
      _ ≤ ∑ _c ∈ hCfin.toFinset, ENNReal.ofReal (2 * r) ^ u :=
          Finset.sum_le_sum fun c _ => (hausdorffContent_le_ediam_rpow hu0 _).trans
            (ENNReal.rpow_le_rpow (hediam c) hu0)
      _ = ((hCfin.toFinset.card : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 * r) ^ u := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞) * ENNReal.ofReal ((2 * r) ^ u) := by
          rw [hcard, ENNReal.ofReal_rpow_of_pos (by linarith)]
      _ ≤ ENNReal.ofReal (r ^ (-(t : ℝ))) * ENNReal.ofReal ((2 * r) ^ u) :=
          mul_le_mul_left hNr _
      _ = ENNReal.ofReal (2 ^ u * r ^ (ε : ℝ)) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _), hcalc]
  -- the bound tends to zero along a sequence of good scales
  obtain ⟨ρ, hρtend, hρ⟩ := Filter.exists_seq_forall_of_frequently ht
  have hcontent : hausdorffContent u E = 0 := by
    refine le_antisymm ?_ (by simp)
    refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
    rw [zero_add]
    have h2u : (0 : ℝ) < 2 ^ u := Real.rpow_pos_of_pos (by norm_num) u
    obtain ⟨j, hj0, hjδ⟩ := ((hρtend.eventually eventually_mem_nhdsWithin).and
      (hρtend.eventually (eventually_rpow_lt (C := (δ : ℝ) / 2 ^ u)
        (div_pos (by exact_mod_cast hδ) h2u) hεpos))).exists
    have hj : (0 : ℝ) < ρ j := hj0
    refine (main (ρ j) hj (hρ j)).trans ?_
    rw [show ((δ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (δ : ℝ) from (ENNReal.ofReal_coe_nnreal).symm]
    refine ENNReal.ofReal_le_ofReal (le_of_lt ?_)
    calc 2 ^ u * ρ j ^ (ε : ℝ) < 2 ^ u * ((δ : ℝ) / 2 ^ u) := mul_lt_mul_of_pos_left hjδ h2u
      _ = (δ : ℝ) := by rw [mul_comm, div_mul_cancel₀ _ h2u.ne']
  exact (iInf₂_le (t + ε) hcontent).trans_eq (by push_cast; ring)

end GeometricMeasureTheory
