/-
# Section 2: Hausdorff content need not be additive

The paragraph *Hausdorff content need not be additive* of Section 2 (`rem:nonadditive-content`),
together with the content of an interval, which the paragraph *The interval* of Section 2.3 reads
off from the same projection argument.

| Notes | Lean declaration | Location |
|---|---|---|
| `𝓗^1_∞([a, b]) = b - a` (paragraph *The interval*) | `hausdorffContent_Icc` | here |
| `𝓗^1([a, b]) = b - a` | `MeasureTheory.hausdorffMeasure_real`, `Real.volume_Icc` | `Mathlib/MeasureTheory/Measure/Hausdorff.lean`, `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean` |
| Two unit segments at distance one: content is not additive | `nonadditive_content` | here |
-/
import GeometricMeasureTheory.Hausdorff.Basic

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

/-- For the gauge `t ↦ t ^ 1` the weight of a set is its diameter. -/
private theorem gaugeWeight_rpow_one_eq_ediam {X : Type*} [EMetricSpace X] (U : Set X) :
    gaugeWeight (fun t => t ^ (1 : ℝ)) U = ediam U := by
  rcases U.eq_empty_or_nonempty with rfl | hU
  · simp [gaugeWeight]
  · simp [gaugeWeight, hU]

/-- The projection argument: the image of `E` under a `1`-Lipschitz map to the real line has
Lebesgue measure at most `𝓗^1_∞(E)`. -/
theorem volume_image_le_hausdorffContent_one {X : Type*} [EMetricSpace X] {f : X → ℝ}
    (hf : LipschitzWith 1 f) (E : Set X) : volume (f '' E) ≤ hausdorffContent 1 E := by
  refine le_iInf fun U => le_iInf fun _ => le_iInf fun hEU => ?_
  calc volume (f '' E) ≤ volume (⋃ i, f '' U i) := by
        rw [← image_iUnion]
        exact measure_mono (image_mono hEU)
    _ ≤ ∑' i, volume (f '' U i) := measure_iUnion_le _
    _ ≤ ∑' i, gaugeWeight (fun t => t ^ (1 : ℝ)) (U i) := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        rw [gaugeWeight_rpow_one_eq_ediam]
        exact (Real.volume_le_diam _).trans (by simpa using hf.ediam_image_le (U i))

/-- The content of a compact interval: `𝓗^1_∞([a, b]) = b - a`. -/
theorem hausdorffContent_Icc {a b : ℝ} (hab : a ≤ b) :
    hausdorffContent 1 (Icc a b) = ENNReal.ofReal (b - a) := by
  refine le_antisymm ?_ ?_
  · calc hausdorffContent 1 (Icc a b) ≤ ediam (Icc a b) ^ (1 : ℝ) :=
          hausdorffContent_le_ediam_rpow zero_le_one _
      _ = ENNReal.ofReal (diam (Icc a b)) := by
          rw [ENNReal.rpow_one, diam, ENNReal.ofReal_toReal (isBounded_Icc a b).ediam_ne_top]
      _ = ENNReal.ofReal (b - a) := by rw [Real.diam_Icc hab]
  · simpa [Real.volume_Icc] using volume_image_le_hausdorffContent_one LipschitzWith.id (Icc a b)

/-- The measure of a compact interval, `𝓗^1([a, b]) = b - a`, is Mathlib's
`MeasureTheory.hausdorffMeasure_real` together with `Real.volume_Icc`. -/
example {a b : ℝ} : μH[1] (Icc a b) = ENNReal.ofReal (b - a) := by
  rw [hausdorffMeasure_real, Real.volume_Icc]

/-- The segment `L₀ = [0, 1] × {0}` in the Euclidean plane. -/
def lowerSegment : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 = 0}

/-- The segment `L₁ = [0, 1] × {1}` in the Euclidean plane. -/
def upperSegment : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 = 1}

/-- A set in the plane whose coordinates vary by at most `a` and `b` has diameter at most
`√(a ^ 2 + b ^ 2)`. -/
private theorem ediam_le_of_abs_sub_coord_le {S : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ}
    (h : ∀ p ∈ S, ∀ q ∈ S, |p 0 - q 0| ≤ a ∧ |p 1 - q 1| ≤ b) :
    ediam S ≤ ENNReal.ofReal √(a ^ 2 + b ^ 2) := by
  refine ediam_le fun p hp q hq => ?_
  obtain ⟨ha, hb⟩ := h p hp q hq
  rw [edist_dist, EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (add_le_add
    (pow_le_pow_left₀ (abs_nonneg _) ha 2) (pow_le_pow_left₀ (abs_nonneg _) hb 2)))

/-- A horizontal unit segment `[0, 1] × {y}` has `1`-dimensional content one. -/
private theorem hausdorffContent_horizontalSegment (y : ℝ) :
    hausdorffContent 1 {p : EuclideanSpace ℝ (Fin 2) | p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 = y} = 1 := by
  set S := {p : EuclideanSpace ℝ (Fin 2) | p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 = y}
  refine le_antisymm ?_ ?_
  · refine (hausdorffContent_le_ediam_rpow zero_le_one S).trans ?_
    rw [ENNReal.rpow_one]
    refine (ediam_le_of_abs_sub_coord_le (a := 1) (b := 0) fun p hp q hq => ⟨?_, ?_⟩).trans
      (by simp)
    · obtain ⟨⟨hp0, hp1⟩, -⟩ := hp
      obtain ⟨⟨hq0, hq1⟩, -⟩ := hq
      exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
    · rw [hp.2, hq.2]
      simp
  · have hproj : LipschitzWith 1 fun p : EuclideanSpace ℝ (Fin 2) => p 0 :=
      LipschitzWith.of_dist_le_mul fun p q => by simpa using PiLp.dist_apply_le p q 0
    have himage : Icc (0 : ℝ) 1 ⊆ (fun p : EuclideanSpace ℝ (Fin 2) => p 0) '' S :=
      fun t ht => ⟨WithLp.toLp 2 ![t, y], ⟨by simpa using ht, by simp⟩, by simp⟩
    calc (1 : ℝ≥0∞) = volume (Icc (0 : ℝ) 1) := by simp [Real.volume_Icc]
      _ ≤ volume ((fun p : EuclideanSpace ℝ (Fin 2) => p 0) '' S) := measure_mono himage
      _ ≤ hausdorffContent 1 S := volume_image_le_hausdorffContent_one hproj S

/-- The paragraph *Hausdorff content need not be additive* (`rem:nonadditive-content`): both unit
segments have content one, their union has content at most `√2`, and `L₀` fails the
Carathéodory test for `𝓗^1_∞`. -/
theorem nonadditive_content :
    hausdorffContent 1 lowerSegment = 1 ∧ hausdorffContent 1 upperSegment = 1 ∧
      hausdorffContent 1 (lowerSegment ∪ upperSegment) ≤ ENNReal.ofReal (Real.sqrt 2) ∧
      ¬(hausdorffContentOuter (X := EuclideanSpace ℝ (Fin 2)) 1).IsCaratheodory lowerSegment := by
  have h₀ : hausdorffContent 1 lowerSegment = 1 := hausdorffContent_horizontalSegment 0
  have h₁ : hausdorffContent 1 upperSegment = 1 := hausdorffContent_horizontalSegment 1
  have hunion : hausdorffContent 1 (lowerSegment ∪ upperSegment) ≤ ENNReal.ofReal √2 := by
    refine (hausdorffContent_le_ediam_rpow zero_le_one _).trans ?_
    rw [ENNReal.rpow_one]
    have key : ∀ p ∈ lowerSegment ∪ upperSegment,
        p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 ∈ Icc (0 : ℝ) 1 := by
      rintro p (⟨h0, h1⟩ | ⟨h0, h1⟩) <;> simp [h0, h1]
    refine (ediam_le_of_abs_sub_coord_le (a := 1) (b := 1) fun p hp q hq => ?_).trans
      (by norm_num)
    obtain ⟨⟨a0, a1⟩, b0, b1⟩ := key p hp
    obtain ⟨⟨c0, c1⟩, d0, d1⟩ := key q hq
    exact ⟨abs_sub_le_iff.2 ⟨by linarith, by linarith⟩, abs_sub_le_iff.2 ⟨by linarith, by linarith⟩⟩
  refine ⟨h₀, h₁, hunion, fun h => ?_⟩
  have hdisj : Disjoint lowerSegment upperSegment :=
    disjoint_left.2 fun p hp hq => by
      have : (0 : ℝ) = 1 := hp.2.symm.trans hq.2
      norm_num at this
  have hcar := h (lowerSegment ∪ upperSegment)
  rw [union_inter_cancel_left, union_sdiff_left, hdisj.symm.sdiff_eq_left] at hcar
  simp only [coe_hausdorffContentOuter, h₀, h₁] at hcar
  have hlt : ENNReal.ofReal √2 < 2 := by
    rw [← ENNReal.ofReal_ofNat, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hcontra := hunion.trans_lt hlt
  rw [hcar, one_add_one_eq_two] at hcontra
  exact lt_irrefl _ hcontra

end GeometricMeasureTheory
