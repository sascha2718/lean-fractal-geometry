/-
# Section 2.1: Covering conventions and maps

Arbitrary covers in place of open covers, Borel regularity, and the behaviour of Hausdorff measure
and dimension under Lipschitz and Hölder maps.

| Notes | Lean declaration | Location |
|---|---|---|
| Lemma 2.11 (arbitrary covers) | `arbitrary_covers` | here |
| Hausdorff measure of a subset in its induced metric | `Isometry.hausdorffMeasure_image`, `isometry_subtype_coe` | `Mathlib/MeasureTheory/Measure/Hausdorff.lean`, `Mathlib/Topology/MetricSpace/Isometry.lean` |
| Proposition 2.12 (Borel regularity) | `MeasureTheory.measurableSet_toMeasurable`, `MeasureTheory.subset_toMeasurable`, `MeasureTheory.measure_toMeasurable` | `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean` |
| Proposition 2.12 (finite Radon restriction) | `MeasureTheory.isFiniteMeasure_restrict`, `MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure` | `Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`, `Mathlib/MeasureTheory/Measure/Regular.lean` |
| Proposition 2.13 (Lipschitz images) | `LipschitzOnWith.hausdorffMeasure_image_le`, `LipschitzOnWith.dimH_image_le`, `LipschitzWith.dimH_image_le`, `AntilipschitzWith.le_dimH_image` | `Mathlib/MeasureTheory/Measure/Hausdorff.lean`, `Mathlib/Topology/MetricSpace/HausdorffDimension.lean` |
| Exercise 2.14 (Hölder images) | `HolderOnWith.dimH_image_le` | `Mathlib/Topology/MetricSpace/HausdorffDimension.lean` |
-/
import GeometricMeasureTheory.Hausdorff.Basic

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

variable {X : Type*} [EMetricSpace X]

/-! ## Lemma 2.11 (`thm:arbitrary-covers`) -/

/-- For `s ≥ 0`, a diameter `a` can be enlarged by `2η` with `η > 0` so that a strict cutoff
`a < δ` is kept and `a ^ s` grows by at most `ε`. -/
private lemma exists_pos_add_rpow_le (s : ℝ) (a δ : ℝ≥0∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ η : ℝ≥0, 0 < η ∧ (a < δ → a + 2 * η < δ) ∧ (a + 2 * η) ^ s ≤ a ^ s + ε := by
  have hlim : Tendsto (fun η : ℝ≥0 => a + 2 * (η : ℝ≥0∞)) (𝓝[>] 0) (𝓝 a) := by
    have hc : Continuous fun η : ℝ≥0 => a + 2 * (η : ℝ≥0∞) :=
      continuous_const.add ((ENNReal.continuous_const_mul (by simp)).comp ENNReal.continuous_coe)
    simpa only [ENNReal.coe_zero, mul_zero, add_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have h₁ : ∀ᶠ η in 𝓝[>] (0 : ℝ≥0), 0 < η := self_mem_nhdsWithin
  have h₂ : ∀ᶠ η : ℝ≥0 in 𝓝[>] 0, a < δ → a + 2 * η < δ := by
    by_cases ha : a < δ
    · exact (hlim.eventually (gt_mem_nhds ha)).mono fun _ h _ => h
    · exact Eventually.of_forall fun _ h => absurd h ha
  have h₃ : ∀ᶠ η : ℝ≥0 in 𝓝[>] 0, (a + 2 * η) ^ s ≤ a ^ s + ε := by
    by_cases ha : a ^ s = ∞
    · exact Eventually.of_forall fun _ => by simp [ha]
    · exact (((ENNReal.continuous_rpow_const.tendsto a).comp hlim).eventually
        (gt_mem_nhds (ENNReal.lt_add_right ha hε))).mono fun _ h => h.le
  exact (h₁.and (h₂.and h₃)).exists

/-- Every countable family `U` is contained in an open family `V` that keeps each strict diameter
cutoff `ediam (U i) < δ` and satisfies `∑ |V i|^s ≤ ∑ |U i|^s + ε`, for `s ≥ 0` and `ε ≠ 0`. -/
private lemma exists_isOpen_tsum_gaugeWeight_le {s : ℝ} (hs : 0 ≤ s) (δ : ℝ≥0∞)
    (U : ℕ → Set X) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ V : ℕ → Set X, (∀ i, IsOpen (V i)) ∧ (∀ i, U i ⊆ V i) ∧
      (∀ i, ediam (U i) < δ → ediam (V i) < δ) ∧
      ∑' i, gaugeWeight (fun t => t ^ s) (V i) ≤
        ∑' i, gaugeWeight (fun t => t ^ s) (U i) + ε := by
  obtain ⟨ε', hε'0, hε'⟩ := ENNReal.exists_pos_sum_of_countable' hε ℕ
  choose η hη0 hηδ hηs using fun i => exists_pos_add_rpow_le s (ediam (U i)) δ (hε'0 i).ne'
  have hsub : ∀ i, U i ⊆ thickening (η i) (U i) := fun i =>
    self_subset_thickening (NNReal.coe_pos.2 (hη0 i)) _
  refine ⟨fun i => thickening (η i) (U i), fun i => isOpen_thickening, hsub,
    fun i hi => (ediam_thickening_le _).trans_lt (hηδ i hi), ?_⟩
  calc
    ∑' i, gaugeWeight (fun t => t ^ s) (thickening (η i) (U i))
        ≤ ∑' i, (gaugeWeight (fun t => t ^ s) (U i) + ε' i) := by
      refine ENNReal.tsum_le_tsum fun i => ?_
      rcases (U i).eq_empty_or_nonempty with h | h
      · rw [h, thickening_empty]
        exact le_self_add
      · rw [gaugeWeight, gaugeWeight, iSup_pos h, iSup_pos (h.mono (hsub i))]
        exact (ENNReal.rpow_le_rpow (ediam_thickening_le _) hs).trans (hηs i)
    _ = ∑' i, gaugeWeight (fun t => t ^ s) (U i) + ∑' i, ε' i := ENNReal.tsum_add
    _ ≤ ∑' i, gaugeWeight (fun t => t ^ s) (U i) + ε := by gcongr

/-- Lemma 2.11 (`thm:arbitrary-covers`): the infima defining `𝓗^s_δ` and `𝓗^s_∞` are unchanged
when arbitrary covering sets are allowed in place of open ones. -/
theorem arbitrary_covers {s : ℝ} (hs : 0 ≤ s) (δ : ℝ≥0∞) (E : Set X) :
    hausdorffDelta s δ E =
        ⨅ (U : ℕ → Set X) (_ : ∀ i, ediam (U i) < δ) (_ : E ⊆ ⋃ i, U i),
          ∑' i, gaugeWeight (fun t => t ^ s) (U i) ∧
      hausdorffContent s E =
        ⨅ (U : ℕ → Set X) (_ : E ⊆ ⋃ i, U i), ∑' i, gaugeWeight (fun t => t ^ s) (U i) := by
  simp only [hausdorffDelta, hausdorffDeltaGauge, hausdorffContent, hausdorffContentGauge]
  constructor
  · refine le_antisymm (le_iInf fun U => le_iInf fun hδ => le_iInf fun hE => ?_)
      (le_iInf fun U => le_iInf fun _ => le_iInf fun hδ => le_iInf fun hE =>
        iInf_le_of_le U <| iInf_le_of_le hδ <| iInf_le_of_le hE le_rfl)
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨V, hVo, hUV, hVδ, hV⟩ :=
      exists_isOpen_tsum_gaugeWeight_le hs δ U (ENNReal.coe_ne_zero.2 hε.ne')
    refine le_trans ?_ hV
    exact iInf_le_of_le V <| iInf_le_of_le hVo <| iInf_le_of_le (fun i => hVδ i (hδ i)) <|
      iInf_le_of_le (hE.trans (iUnion_mono hUV)) le_rfl
  · refine le_antisymm (le_iInf fun U => le_iInf fun hE => ?_)
      (le_iInf fun U => le_iInf fun _ => le_iInf fun hE =>
        iInf_le_of_le U <| iInf_le_of_le hE le_rfl)
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨V, hVo, hUV, -, hV⟩ :=
      exists_isOpen_tsum_gaugeWeight_le hs ⊤ U (ENNReal.coe_ne_zero.2 hε.ne')
    refine le_trans ?_ hV
    exact iInf_le_of_le V <| iInf_le_of_le hVo <|
      iInf_le_of_le (hE.trans (iUnion_mono hUV)) le_rfl

/-! The Hausdorff measure of a subset agrees with the one computed in its induced metric, by
`Isometry.hausdorffMeasure_image` for the inclusion. -/

example [MeasurableSpace X] [BorelSpace X] (S : Set X) {s : ℝ} (hs : 0 ≤ s) (E : Set S) :
    μH[s] ((↑) '' E : Set X) = μH[s] E :=
  isometry_subtype_coe.hausdorffMeasure_image (Or.inl hs) E

/-! ## Proposition 2.12 (`thm:hausdorff-borel-regular`)

Every set has a Borel hull of the same Hausdorff measure. -/

example [MeasurableSpace X] [BorelSpace X] (s : ℝ) (A : Set X) :
    ∃ B, MeasurableSet B ∧ A ⊆ B ∧ μH[s] B = μH[s] A :=
  ⟨toMeasurable μH[s] A, measurableSet_toMeasurable _ _, subset_toMeasurable _ _,
    measure_toMeasurable _⟩

/-! The restriction of `𝓗^s` to a set of finite measure is a finite Radon measure: a finite Borel
measure on a finite-dimensional real normed space is `MeasureTheory.Measure.Regular`. -/

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (s : ℝ) {A : Set E} (hA : μH[s] A ≠ ∞) :
    IsFiniteMeasure (μH[s].restrict A) ∧ (μH[s].restrict A).Regular := by
  have : IsFiniteMeasure (μH[s].restrict A) := isFiniteMeasure_restrict.2 hA
  exact ⟨this, inferInstance⟩

/-! ## Proposition 2.13 (`thm:hausdorff-lipschitz`) -/

example {Y : Type*} [EMetricSpace Y] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]
    [BorelSpace Y] {f : X → Y} {L : ℝ≥0} {E : Set X} (hf : LipschitzOnWith L f E) {s : ℝ}
    (hs : 0 < s) : μH[s] (f '' E) ≤ (L : ℝ≥0∞) ^ s * μH[s] E :=
  hf.hausdorffMeasure_image_le hs.le

example {Y : Type*} [EMetricSpace Y] {f : X → Y} {L : ℝ≥0} {E : Set X}
    (hf : LipschitzOnWith L f E) : dimH (f '' E) ≤ dimH E :=
  hf.dimH_image_le

example {Y : Type*} [EMetricSpace Y] {f : X → Y} {K L : ℝ≥0} (hf : LipschitzWith L f)
    (hf' : AntilipschitzWith K f) (E : Set X) : dimH (f '' E) = dimH E :=
  le_antisymm (hf.dimH_image_le E) (hf'.le_dimH_image E)

/-! ## Exercise 2.14 (`ex:holder-maps`) -/

example {Y : Type*} [EMetricSpace Y] {f : X → Y} {C r : ℝ≥0} {E : Set X}
    (hf : HolderOnWith C r f E) (hr : 0 < r) : dimH (f '' E) ≤ dimH E / r :=
  hf.dimH_image_le hr

end GeometricMeasureTheory
