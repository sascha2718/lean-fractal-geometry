/-
# Section 3.5: The four-corner Cantor dust

The four-corner Cantor dust `F = K × K`, where `K` is the middle-half Cantor set, is Ahlfors
`1`-regular and has positive finite length. Its pure `1`-unrectifiability is used in the notes as a
background result (Mattila, *Rectifiability: a survey*, Example 4.6); it is not in Mathlib, Palomar
or TauCeti, and is not formalised here.

| Notes | Lean declaration | Location |
|---|---|---|
| The four-corner Cantor dust | `fourCornerDust` | here |
| `F` is Ahlfors `1`-regular | `fourCornerDust_isAhlforsRegularSet` | here |
| `0 < 𝓗^1(F) < ∞` | `fourCornerDust_hausdorffMeasure` | here |
| `F` is purely `1`-unrectifiable | not formalised | |

The measure on `F` is the product of two copies of the middle-half Cantor measure. The Cantor ball
bounds with exponent `1/2` in each coordinate give the ball bounds with exponent `1` in the plane,
since a ball of radius `r` lies in the rectangle of coordinate balls of radius `r` and contains the
rectangle of coordinate balls of radius `r/2`.
-/
import GeometricMeasureTheory.Covering.AhlforsRegularExamples

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

/-- The four-corner Cantor dust: the product of the middle-half Cantor set with itself, in the
Euclidean plane. -/
def fourCornerDust : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | p 0 ∈ symmetricCantorSet (1 / 4) ∧ p 1 ∈ symmetricCantorSet (1 / 4)}

/-! ### The measure on the dust -/

/-- The middle-half Cantor set has exponent `log 2 / log 4 = 1/2`. -/
theorem log_two_div_log_inv_one_fourth : Real.log 2 / Real.log (1 / 4 : ℝ)⁻¹ = 1 / 2 := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [show (1 / 4 : ℝ)⁻¹ = 2 ^ 2 by norm_num, Real.log_pow]
  field_simp
  norm_num

/-- The middle-half Cantor measure is a probability measure. -/
instance isProbabilityMeasure_cantorMeasure_one_fourth :
    IsProbabilityMeasure (cantorMeasure (1 / 4)) :=
  isProbabilityMeasure_cantorMeasure (by norm_num) (by norm_num)

/-- The natural measure on the four-corner Cantor dust: the product of two copies of the
middle-half Cantor measure, transported to the Euclidean plane. -/
def fourCornerDustMeasure : Measure (EuclideanSpace ℝ (Fin 2)) :=
  (Measure.pi fun _ : Fin 2 => cantorMeasure (1 / 4)).map (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

/-- The measure on the four-corner Cantor dust is a probability measure. -/
instance isProbabilityMeasure_fourCornerDustMeasure :
    IsProbabilityMeasure fourCornerDustMeasure := by
  unfold fourCornerDustMeasure
  infer_instance

/-- A coordinate rectangle has the product of the Cantor measures of its sides as mass. -/
theorem fourCornerDustMeasure_rectangle (A B : Set ℝ) :
    fourCornerDustMeasure {q | q 0 ∈ A ∧ q 1 ∈ B} =
      cantorMeasure (1 / 4) A * cantorMeasure (1 / 4) B := by
  have h : MeasurableEquiv.toLp 2 (Fin 2 → ℝ) ⁻¹' {q | q 0 ∈ A ∧ q 1 ∈ B} =
      univ.pi ![A, B] := by
    ext x
    simp [Fin.forall_fin_two, MeasurableEquiv.coe_toLp]
  rw [fourCornerDustMeasure, MeasurableEquiv.map_apply, h, Measure.pi_pi, Fin.prod_univ_two]
  simp

/-- A ball in the plane lies in the rectangle of the coordinate balls with the same radius. -/
theorem ball_subset_rectangle (p : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    ball p r ⊆ {q | q 0 ∈ ball (p 0) r ∧ q 1 ∈ ball (p 1) r} := fun q hq =>
  ⟨(PiLp.dist_apply_le q p 0).trans_lt hq, (PiLp.dist_apply_le q p 1).trans_lt hq⟩

/-- The rectangle of the coordinate balls of radius `t` lies in the ball of radius `2t`. -/
theorem rectangle_subset_ball (p : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    {q | q 0 ∈ ball (p 0) t ∧ q 1 ∈ ball (p 1) t} ⊆ ball p (2 * t) := by
  rintro q ⟨h0, h1⟩
  rw [mem_ball] at h0 h1 ⊢
  have ht : 0 < t := dist_nonneg.trans_lt h0
  rw [PiLp.dist_eq_of_L2, Fin.sum_univ_two, Real.sqrt_lt' (by positivity)]
  nlinarith [dist_nonneg (x := q 0) (y := p 0), dist_nonneg (x := q 1) (y := p 1)]

/-- The four-corner Cantor dust is closed. -/
theorem isClosed_fourCornerDust : IsClosed fourCornerDust := by
  have hK := isClosed_symmetricCantorSet (a := 1 / 4) (by norm_num)
  exact (hK.preimage (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0)).inter
    (hK.preimage (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1))

/-- The four-corner Cantor dust contains the points `(0, 0)` and `(1, 1)`. -/
theorem fourCornerDust_nontrivial : fourCornerDust.Nontrivial := by
  refine ⟨0, ?_, WithLp.toLp 2 fun _ => 1, ?_, fun h => ?_⟩
  · simp [fourCornerDust, zero_mem_symmetricCantorSet]
  · simp [fourCornerDust, one_mem_symmetricCantorSet]
  · simpa using congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 0) h

/-- The four-corner Cantor dust has diameter at most `4`. -/
theorem ediam_fourCornerDust_le : ediam fourCornerDust ≤ ENNReal.ofReal 4 := by
  refine ediam_le fun p hp q hq => ?_
  have hK : ∀ x ∈ symmetricCantorSet (1 / 4 : ℝ), ∀ y ∈ symmetricCantorSet (1 / 4 : ℝ),
      dist x y < 2 := by
    intro x hx y hy
    have hx' := symmetricCantorSet_subset_Icc _ hx
    have hy' := symmetricCantorSet_subset_Icc _ hy
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hx'.1, hx'.2, hy'.1, hy'.2]
  have h := rectangle_subset_ball q 2 ⟨hK _ hp.1 _ hq.1, hK _ hp.2 _ hq.2⟩
  rw [mem_ball] at h
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- The four-corner Cantor dust is compact. -/
theorem isCompact_fourCornerDust : IsCompact fourCornerDust :=
  isCompact_of_isClosed_isBounded isClosed_fourCornerDust
    (isBounded_iff_ediam_ne_top.2 (ediam_fourCornerDust_le.trans_lt ENNReal.ofReal_lt_top).ne)

/-- The measure on the four-corner Cantor dust is concentrated on the dust. -/
theorem fourCornerDustMeasure_compl : fourCornerDustMeasure fourCornerDustᶜ = 0 := by
  rw [prob_compl_eq_zero_iff isClosed_fourCornerDust.measurableSet, fourCornerDust,
    fourCornerDustMeasure_rectangle,
    cantorMeasure_symmetricCantorSet (by norm_num) (by norm_num), one_mul]

/-- The upper ball bound on the four-corner Cantor dust: `μ(B(p, r)) ≤ 4r`. -/
theorem fourCornerDustMeasure_ball_le (p : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) :
    fourCornerDustMeasure (ball p r) ≤ 4 * ENNReal.ofReal r := by
  have hc : ENNReal.ofReal ((2 / (1 - 2 * (1 / 4 : ℝ))) ^ (1 / 2 : ℝ)) = 2 := by
    rw [show 2 / (1 - 2 * (1 / 4 : ℝ)) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hK : ∀ x, cantorMeasure (1 / 4) (ball x r) ≤ 2 * ENNReal.ofReal r ^ (1 / 2 : ℝ) := by
    intro x
    have h := cantorMeasure_ball_le (a := 1 / 4) (by norm_num) (by norm_num) x hr
    rwa [log_two_div_log_inv_one_fourth, hc] at h
  have hhalf : ENNReal.ofReal r ^ (1 / 2 : ℝ) * ENNReal.ofReal r ^ (1 / 2 : ℝ) =
      ENNReal.ofReal r := by
    rw [← ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.2 hr).ne' ENNReal.ofReal_ne_top]
    norm_num
  calc fourCornerDustMeasure (ball p r)
      ≤ fourCornerDustMeasure {q | q 0 ∈ ball (p 0) r ∧ q 1 ∈ ball (p 1) r} :=
        measure_mono (ball_subset_rectangle p r)
    _ = cantorMeasure (1 / 4) (ball (p 0) r) * cantorMeasure (1 / 4) (ball (p 1) r) :=
        fourCornerDustMeasure_rectangle _ _
    _ ≤ (2 * ENNReal.ofReal r ^ (1 / 2 : ℝ)) * (2 * ENNReal.ofReal r ^ (1 / 2 : ℝ)) := by
        gcongr <;> exact hK _
    _ = 4 * (ENNReal.ofReal r ^ (1 / 2 : ℝ) * ENNReal.ofReal r ^ (1 / 2 : ℝ)) := by ring
    _ = 4 * ENNReal.ofReal r := by rw [hhalf]

/-- The lower ball bound on the four-corner Cantor dust: `r ≤ 16 μ(B(p, r))` for `p` in the dust
and `0 < r ≤ 4`. -/
theorem ofReal_le_fourCornerDustMeasure_ball {p : EuclideanSpace ℝ (Fin 2)}
    (hp : p ∈ fourCornerDust) {r : ℝ} (hr : 0 < r) (hr4 : r ≤ 4) :
    ENNReal.ofReal r ≤ 16 * fourCornerDustMeasure (ball p r) := by
  have ht : 0 < r / 4 := by positivity
  have ht1 : r / 4 ≤ 1 := by linarith
  have h0 := rpow_le_two_mul_cantorMeasure_ball (a := 1 / 4) (by norm_num) (by norm_num) hp.1 ht ht1
  have h1 := rpow_le_two_mul_cantorMeasure_ball (a := 1 / 4) (by norm_num) (by norm_num) hp.2 ht ht1
  rw [log_two_div_log_inv_one_fourth] at h0 h1
  have hhalf : ENNReal.ofReal (r / 4) ^ (1 / 2 : ℝ) * ENNReal.ofReal (r / 4) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (r / 4) := by
    rw [← ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.2 ht).ne' ENNReal.ofReal_ne_top]
    norm_num
  have hsub : {q | q 0 ∈ ball (p 0) (r / 4) ∧ q 1 ∈ ball (p 1) (r / 4)} ⊆ ball p r :=
    (rectangle_subset_ball p (r / 4)).trans (ball_subset_ball (by linarith))
  calc ENNReal.ofReal r = ENNReal.ofReal (4 * (r / 4)) := by congr 1; ring
    _ = 4 * (ENNReal.ofReal (r / 4) ^ (1 / 2 : ℝ) * ENNReal.ofReal (r / 4) ^ (1 / 2 : ℝ)) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, hhalf]
    _ ≤ 4 * ((2 * cantorMeasure (1 / 4) (ball (p 0) (r / 4))) *
          (2 * cantorMeasure (1 / 4) (ball (p 1) (r / 4)))) := by
        gcongr
    _ = 16 * (cantorMeasure (1 / 4) (ball (p 0) (r / 4)) *
          cantorMeasure (1 / 4) (ball (p 1) (r / 4))) := by ring
    _ = 16 * fourCornerDustMeasure {q | q 0 ∈ ball (p 0) (r / 4) ∧ q 1 ∈ ball (p 1) (r / 4)} := by
        rw [fourCornerDustMeasure_rectangle]
    _ ≤ 16 * fourCornerDustMeasure (ball p r) := by
        gcongr

/-! ### Ahlfors regularity and length -/

/-- The four-corner Cantor dust is Ahlfors `1`-regular. -/
theorem fourCornerDust_isAhlforsRegularSet : IsAhlforsRegularSet 1 fourCornerDust := by
  refine ⟨fourCornerDustMeasure, 16, IsAhlforsRegular.of_measure_compl isClosed_fourCornerDust
    fourCornerDust_nontrivial one_pos inferInstance fourCornerDustMeasure_compl (by norm_num)
    ?_ ?_⟩
  · intro p hp r hr hrE
    have hr4 : r ≤ 4 :=
      (ENNReal.ofReal_le_ofReal_iff (by norm_num)).1 (hrE.trans ediam_fourCornerDust_le)
    rw [ENNReal.rpow_one]
    exact_mod_cast ofReal_le_fourCornerDustMeasure_ball hp hr hr4
  · intro p _ r hr _
    rw [ENNReal.rpow_one]
    calc fourCornerDustMeasure (ball p r) ≤ 4 * ENNReal.ofReal r :=
          fourCornerDustMeasure_ball_le p hr
      _ ≤ ((16 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal r := by
          gcongr
          norm_num

/-- The four-corner Cantor dust has positive finite `𝓗^1` measure. -/
theorem fourCornerDust_hausdorffMeasure :
    0 < μH[1] fourCornerDust ∧ μH[1] fourCornerDust < ∞ := by
  obtain ⟨μ, C, hμ⟩ := fourCornerDust_isAhlforsRegularSet
  obtain ⟨-, hpos, htop, -⟩ := ahlfors_hausdorff hμ isCompact_fourCornerDust
  exact ⟨hpos, htop⟩

end GeometricMeasureTheory
