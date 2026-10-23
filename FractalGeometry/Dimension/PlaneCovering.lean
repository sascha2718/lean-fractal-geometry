import Mathlib
import GeometricMeasureTheory.Box.BoxDimension
import GeometricMeasureTheory


open GeometricMeasureTheory

open Filter Topology Set Metric MeasureTheory

open scoped ENNReal NNReal

namespace FractalGeometry

variable {X : Type*} [PseudoMetricSpace X]

def gridCentres (a b r : ℝ) : Set ℝ :=
  (fun k : ℕ => a + (2 * (k : ℝ) + 1) * r) '' ↑(Finset.range (⌊(b - a) / (2 * r)⌋₊ + 1))

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

theorem encard_gridCentres_le (a b r : ℝ) :
    (gridCentres a b r).encard ≤ ((⌊(b - a) / (2 * r)⌋₊ + 1 : ℕ) : ℕ∞) := by
  refine (Set.encard_image_le _ _).trans ?_
  rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_range]

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

theorem upperBoxDim_le_two {E : Set (ℝ × ℝ)} (hE : Bornology.IsBounded E) :
    upperBoxDim E ≤ 2 := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall ((0 : ℝ), (0 : ℝ))).1 hE
  rw [← closedBall_prod_same, Real.closedBall_eq_Icc] at hR
  exact (upperBoxDim_mono hR).trans (upperBoxDim_Icc_prod_le _ _ _ _)

theorem dimH_le_lowerBoxDim {Y : Type*} [MetricSpace Y] (E : Set Y) :
    dimH E ≤ lowerBoxDim E := by
  borelize Y
  refine le_iInf₂ fun t ht => ?_
  refine dimH_le_of_hausdorffMeasure_ne_top (d := t) (ne_top_of_le_ne_top
    (ENNReal.ofReal_ne_top (r := 2 ^ (t : ℝ))) ?_)
  obtain ⟨ρ, hρtend, hρ⟩ := Filter.exists_seq_forall_of_frequently ht
  have hρpos : ∀ᶠ j in atTop, 0 < ρ j := hρtend.eventually eventually_mem_nhdsWithin

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

theorem dimH_le_upperBoxDim {Y : Type*} [MetricSpace Y] (E : Set Y) : dimH E ≤ upperBoxDim E :=
  (dimH_le_lowerBoxDim E).trans (lowerBoxDim_le_upperBoxDim E)

end FractalGeometry
