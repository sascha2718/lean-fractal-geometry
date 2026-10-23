import Mathlib
import GeometricMeasureTheory.Box.ModifiedBox
import FractalGeometry.Dimension.PlaneCovering
import GeometricMeasureTheory.Box.BoxDimension
import GeometricMeasureTheory.Box.CoveringNumbers

open GeometricMeasureTheory

open Filter Topology Set Metric MeasureTheory

open scoped ENNReal NNReal

namespace FractalGeometry

variable {X : Type*} [PseudoMetricSpace X]

private lemma eventually_rpow_lt {C : ℝ} (hC : 0 < C) {p : ℝ} (hp : 0 < p) :
    ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r ^ p < C := by
  have hδ : (0 : ℝ) < C ^ p⁻¹ := Real.rpow_pos_of_pos hC _
  filter_upwards [eventually_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with r hr0 hrδ
  have hr : (0 : ℝ) < r := hr0
  calc r ^ p < (C ^ p⁻¹) ^ p := Real.rpow_lt_rpow hr.le hrδ hp
    _ = C := by rw [← Real.rpow_mul hC.le, inv_mul_cancel₀ hp.ne', Real.rpow_one]

theorem upperBoxDim_image_eq {Y : Type*} [PseudoMetricSpace Y] {f : X → Y} {g : Y → X}
    {K L : ℝ≥0} {E : Set X} (hf : LipschitzOnWith L f E) (hg : LipschitzOnWith K g (f '' E))
    (hgf : ∀ x ∈ E, g (f x) = x) : upperBoxDim (f '' E) = upperBoxDim E := by
  refine le_antisymm (upperBoxDim_image_le hf) ?_
  have hE : g '' (f '' E) = E := by
    rw [Set.image_image]
    exact (Set.image_congr hgf).trans (Set.image_id E)
  calc upperBoxDim E = upperBoxDim (g '' (f '' E)) := by rw [hE]
    _ ≤ upperBoxDim (f '' E) := upperBoxDim_image_le hg

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

theorem upperBoxDim_le_one {E : Set ℝ} (hE : Bornology.IsBounded E) : upperBoxDim E ≤ 1 := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hE
  rw [Real.closedBall_eq_Icc] at hR
  exact (upperBoxDim_mono hR).trans (upperBoxDim_Icc_le _ _)

end FractalGeometry
