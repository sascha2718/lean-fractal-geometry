/-
# Section 3.3: Examples of Ahlfors regular sets

The examples after Proposition 3.10: intervals with length measure and symmetric Cantor sets with
their equal-weight measures are Ahlfors regular.

| Notes | Lean declaration | Location |
|---|---|---|
| Intervals are Ahlfors `1`-regular | `isAhlforsRegularSet_Icc` | here |
| Symmetric Cantor sets are Ahlfors regular | `isAhlforsRegularSet_symmetricCantorSet` | here |
-/
import GeometricMeasureTheory.Covering.AhlforsRegular
import GeometricMeasureTheory.Hausdorff.CantorSets

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

section Constructor

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- A regular measure concentrated on a closed non-trivial set `E` with the two ball bounds is
Ahlfors regular: the lower ball bound makes every ball about a point of `E` have positive mass, so
the support is `E`. -/
theorem IsAhlforsRegular.of_measure_compl {μ : Measure X} {s : ℝ} {E : Set X} {C : ℝ≥0}
    (hE : IsClosed E) (hEn : E.Nontrivial) (hs : 0 < s) (hμ : μ.Regular) (hμE : μ Eᶜ = 0)
    (hC : 1 ≤ C)
    (hlow : ∀ x ∈ E, ∀ r : ℝ, 0 < r → ENNReal.ofReal r ≤ ediam E →
      ENNReal.ofReal r ^ s ≤ C * μ (ball x r))
    (hup : ∀ x ∈ E, ∀ r : ℝ, 0 < r → ENNReal.ofReal r ≤ ediam E →
      μ (ball x r) ≤ C * ENNReal.ofReal r ^ s) :
    IsAhlforsRegular μ s E C := by
  refine ⟨hE, hEn, hs, hμ, ?_, hC, hlow, hup⟩
  refine subset_antisymm (Measure.support_subset_of_isClosed hE (mem_ae_iff.2 hμE))
    fun x hx => ?_
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨r, hr, hrδ⟩ := ((eventually_pos_ofReal_le_ediam hEn).and
    (nhdsWithin_le_nhds (eventually_lt_nhds hδ))).exists
  refine (pos_iff_ne_zero.2 fun h0 => ?_).trans_le
    (measure_mono ((ball_subset_ball hrδ.le).trans hδU))
  have h := hlow x hx r hr.1 hr.2
  rw [h0, mul_zero] at h
  exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hr.1) ENNReal.ofReal_ne_top).not_ge h

end Constructor

/-- A compact interval with length measure is Ahlfors `1`-regular. -/
theorem isAhlforsRegularSet_Icc {a b : ℝ} (hab : a < b) : IsAhlforsRegularSet 1 (Icc a b) := by
  have hmeas : MeasurableSet (Icc a b) := measurableSet_Icc
  have hdiam : ∀ r : ℝ, ENNReal.ofReal r ≤ ediam (Icc a b) → r ≤ b - a := fun r hr =>
    (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.2 hab.le)).1 (by rwa [Real.ediam_Icc] at hr)
  refine ⟨volume.restrict (Icc a b), 2, IsAhlforsRegular.of_measure_compl isClosed_Icc
    ⟨a, left_mem_Icc.2 hab.le, b, right_mem_Icc.2 hab.le, hab.ne⟩ one_pos
    (regular_restrict_of_isCompact isCompact_Icc (by simp))
    (by rw [Measure.restrict_apply' hmeas, compl_inter_self, measure_empty]) one_le_two ?_ ?_⟩
  · intro x hx r hr hrE
    have hrab := hdiam r hrE
    rw [ENNReal.rpow_one, Measure.restrict_apply measurableSet_ball]
    have hsub : Ioo (max (x - r) a) (min (x + r) b) ⊆ ball x r ∩ Icc a b := by
      intro y hy
      rw [mem_Ioo, max_lt_iff, lt_min_iff] at hy
      refine ⟨?_, hy.1.2.le, hy.2.2.le⟩
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hy.1.1, hy.2.1]
    have hlen : r ≤ min (x + r) b - max (x - r) a := by
      rw [le_sub_iff_add_le]
      refine le_min ?_ ?_ <;> rcases max_cases (x - r) a with h | h <;> linarith [hx.1, hx.2]
    calc ENNReal.ofReal r ≤ volume (Ioo (max (x - r) a) (min (x + r) b)) := by
          rw [Real.volume_Ioo]; exact ENNReal.ofReal_le_ofReal hlen
      _ ≤ volume (ball x r ∩ Icc a b) := measure_mono hsub
      _ = 1 * volume (ball x r ∩ Icc a b) := (one_mul _).symm
      _ ≤ ((2 : ℝ≥0) : ℝ≥0∞) * volume (ball x r ∩ Icc a b) := by gcongr; norm_num
  · intro x hx r hr hrE
    rw [ENNReal.rpow_one]
    calc volume.restrict (Icc a b) (ball x r) ≤ volume (ball x r) :=
          Measure.restrict_le_self _
      _ = ((2 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal r := by
          rw [Real.volume_ball, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]; rfl

/-- The symmetric Cantor set with ratio `0 < a < 1/2` and its equal-weight measure is Ahlfors
`s`-regular for `s = log 2 / log (1/a)`. -/
theorem isAhlforsRegularSet_symmetricCantorSet {a : ℝ} (ha₀ : 0 < a) (ha : a < 1 / 2) :
    IsAhlforsRegularSet (Real.log 2 / Real.log a⁻¹) (symmetricCantorSet a) := by
  have ha1 : a < 1 := by linarith
  set s := Real.log 2 / Real.log a⁻¹ with hs_def
  haveI := isProbabilityMeasure_cantorMeasure ha₀.le ha1
  set C : ℝ≥0 := max 2 ((2 / (1 - 2 * a)) ^ s).toNNReal
  have h2C : ((2 : ℝ≥0) : ℝ≥0∞) ≤ C := ENNReal.coe_le_coe.2 (le_max_left _ _)
  refine ⟨cantorMeasure a, C, IsAhlforsRegular.of_measure_compl
    (isClosed_symmetricCantorSet ha₀.le) (symmetricCantorSet_nontrivial a)
    (log_two_div_log_inv_pos ha₀ ha1) inferInstance
    (cantorMeasure_compl_symmetricCantorSet ha₀.le ha1)
    (one_le_two.trans (le_max_left _ _)) ?_ ?_⟩
  · intro x hx r hr hrE
    rw [ediam_symmetricCantorSet, ENNReal.ofReal_le_one] at hrE
    calc ENNReal.ofReal r ^ s ≤ 2 * cantorMeasure a (ball x r) :=
          rpow_le_two_mul_cantorMeasure_ball ha₀ ha hx hr hrE
      _ ≤ C * cantorMeasure a (ball x r) := by gcongr; exact_mod_cast h2C
  · intro x _ r hr _
    calc cantorMeasure a (ball x r) ≤
          ENNReal.ofReal ((2 / (1 - 2 * a)) ^ s) * ENNReal.ofReal r ^ s :=
          cantorMeasure_ball_le ha₀ ha x hr
      _ ≤ C * ENNReal.ofReal r ^ s := by
          gcongr; exact ENNReal.coe_le_coe.2 (le_max_right _ _)

end GeometricMeasureTheory
