/-
# Section 3.4: Non-integer exponents

Marstrand's theorem that an `s`-set with `s` not an integer is irregular, in the case `0 < s < 1`
proved in the notes by the annulus argument. The general case (Mattila, Theorem 14.10) is used in
the notes as a background result; it is not in Mathlib, Palomar or TauCeti, and is not formalised
here.

| Notes | Lean declaration | Location |
|---|---|---|
| Theorem 3.19 (Marstrand) for `0 < s < 1` | `noninteger_density_of_lt_one` | here |
| Theorem 3.19 for general non-integer `s` | not formalised | |

The proof avoids Egorov's theorem and measurability of the set of regular points. The regular
points are split into the countably many sets `P N` on which the lower bound
`(2r)^s / 2 ≤ 𝓗^s(E ∩ B(x, r))` holds for all `0 < r < 1 / (N + 1)`. Points of `P N` that are
isolated in `P N` form countably many separated sets, which are `𝓗^s`-null. A non-isolated point
of `P N` contradicts the annulus estimate.
-/
import GeometricMeasureTheory.Covering.Densities

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A set whose distinct points are at distance at least `ε > 0` from each other and which has
finite `d`-dimensional Hausdorff measure is countable. -/
theorem countable_of_separated_of_hausdorffMeasure_ne_top {d ε : ℝ} (hε : 0 < ε) {S : Set X}
    (hS : ∀ x ∈ S, ∀ y ∈ S, dist x y < ε → x = y) (hfin : μH[d] S ≠ ∞) : S.Countable := by
  by_contra hS'
  apply hfin
  rw [Measure.hausdorffMeasure_apply]
  refine top_unique (le_iSup₂_of_le (ENNReal.ofReal (ε / 2)) (by simpa using half_pos hε) ?_)
  refine le_iInf fun t => le_iInf fun hcov => le_iInf fun hdiam => absurd ?_ hS'
  refine (countable_iUnion fun n => (?_ : (S ∩ t n).Subsingleton).countable).mono ?_
  · intro a ha b hb
    refine hS a ha.1 b hb.1 ?_
    have h := (edist_le_ediam_of_mem ha.2 hb.2).trans (hdiam n)
    rw [edist_dist, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
    linarith
  · intro a ha
    obtain ⟨n, hn⟩ := mem_iUnion.1 (hcov ha)
    exact mem_iUnion.2 ⟨n, ha, hn⟩

/-- At a regular point `x` of `E`, the mass `𝓗^s(E ∩ B(x, r))` lies between `(1 - θ)(2r)^s` and
`(1 + θ)(2r)^s` for all sufficiently small `r > 0`. -/
theorem IsRegularPoint.eventually_measure_ball_bounds {s : ℝ} {E : Set X} {x : X}
    (hx : IsRegularPoint s E x) {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), (1 - θ) * (2 * r) ^ s ≤ (μH[s] (E ∩ ball x r)).toReal ∧
      (μH[s] (E ∩ ball x r)).toReal ≤ (1 + θ) * (2 * r) ^ s := by
  have ht : Tendsto (fun r : ℝ => μH[s] (E ∩ ball x r) / ENNReal.ofReal (2 * r) ^ s) (𝓝[>] 0)
      (𝓝 1) := tendsto_of_liminf_eq_limsup hx.1 hx.2
  have ht' := ((ENNReal.tendsto_toReal ENNReal.one_ne_top).comp ht).eventually
    (Ioo_mem_nhds (show (1 - θ) < (1 : ℝ≥0∞).toReal by simpa using hθ)
      (show (1 : ℝ≥0∞).toReal < 1 + θ by simpa using hθ))
  filter_upwards [ht', self_mem_nhdsWithin] with r hr (hr0 : 0 < r)
  simp only [Function.comp_apply, ENNReal.toReal_div, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * r)] at hr
  have hpos : 0 < (2 * r) ^ s := by positivity
  exact ⟨(le_div_iff₀ hpos).1 hr.1.le, (div_le_iff₀ hpos).1 hr.2.le⟩

/-- For `s < 1` there is `0 < δ < 1` with `16 δ ≤ δ^s`. -/
private lemma exists_mul_le_rpow {s : ℝ} (hs₁ : s < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ 16 * δ ≤ δ ^ s := by
  have h1s : 0 < 1 - s := sub_pos.2 hs₁
  refine ⟨(1 / 16 : ℝ) ^ (1 / (1 - s)), by positivity,
    Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity), ?_⟩
  set δ := (1 / 16 : ℝ) ^ (1 / (1 - s)) with hδ
  have hδ0 : 0 < δ := by positivity
  have h1 : δ ^ (1 - s) = 1 / 16 := by
    rw [hδ, ← Real.rpow_mul (by norm_num), one_div_mul_cancel h1s.ne', Real.rpow_one]
  have h2 : δ = δ ^ s * δ ^ (1 - s) := by
    rw [← Real.rpow_add hδ0, add_sub_cancel, Real.rpow_one]
  rw [h1] at h2
  linarith

/-- The annulus argument: a regular point `y` of an `s`-set with `0 < s < 1` cannot be approached by
points `x ≠ y` at which `(2r)^s / 2 ≤ 𝓗^s(E ∩ B(x, r))` holds uniformly for `0 < r < ε`. -/
private lemma false_of_regular_of_accumulation {s : ℝ} (hs₁ : s < 1) {E : Set X}
    (hE : MeasurableSet E) (hfin : μH[s] E ≠ ∞) {y : X} (hy : IsRegularPoint s E y) {ε : ℝ}
    (hε : 0 < ε)
    (hacc : ∀ η > 0, ∃ x, x ≠ y ∧ dist x y < η ∧
      ∀ r ∈ Ioo 0 ε, (2 * r) ^ s / 2 ≤ (μH[s] (E ∩ ball x r)).toReal) : False := by
  obtain ⟨δ, hδ0, hδ1, hδs⟩ := exists_mul_le_rpow hs₁
  obtain ⟨ρ, hρ, hρbd⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1
    (hy.eventually_measure_ball_bounds (half_pos hδ0))
  obtain ⟨x, hxy, hdist, hx⟩ := hacc (min (ρ / 2) ε) (lt_min (half_pos hρ) hε)
  set r := dist x y with hr_def
  have hr0 : 0 < r := dist_pos.2 hxy
  have hrρ : r < ρ / 2 := hdist.trans_le (min_le_left _ _)
  have hrε : r < ε := hdist.trans_le (min_le_right _ _)
  have hfin' : ∀ z t, μH[s] (E ∩ ball z t) ≠ ∞ := fun z t =>
    ne_top_of_le_ne_top hfin (measure_mono inter_subset_left)
  have hdisj : Disjoint (E ∩ ball x (δ * r / 2)) (E ∩ ball y ((1 - δ) * r)) := by
    refine Set.disjoint_left.2 fun z hz1 hz2 => ?_
    have h1 := mem_ball.1 hz1.2
    have h2 := mem_ball.1 hz2.2
    have h3 := dist_triangle x z y
    rw [dist_comm x z] at h3
    nlinarith
  have hsub : E ∩ ball x (δ * r / 2) ∪ E ∩ ball y ((1 - δ) * r) ⊆ E ∩ ball y ((1 + δ) * r) := by
    rintro z (hz | hz)
    · refine ⟨hz.1, mem_ball.2 ?_⟩
      have h1 := mem_ball.1 hz.2
      have h3 := dist_triangle z x y
      nlinarith
    · exact ⟨hz.1, ball_subset_ball (by nlinarith) hz.2⟩
  have hsum : (μH[s] (E ∩ ball x (δ * r / 2))).toReal + (μH[s] (E ∩ ball y ((1 - δ) * r))).toReal
      ≤ (μH[s] (E ∩ ball y ((1 + δ) * r))).toReal := by
    rw [← ENNReal.toReal_add (hfin' _ _) (hfin' _ _),
      ← measure_union hdisj (hE.inter measurableSet_ball)]
    exact ENNReal.toReal_mono (hfin' _ _) (measure_mono hsub)
  have h1 := hx (δ * r / 2) ⟨by positivity, by nlinarith⟩
  have h2 := (hρbd (show (1 + δ) * r ∈ Ioo 0 ρ from ⟨by positivity, by nlinarith⟩)).2
  have h3 := (hρbd (show (1 - δ) * r ∈ Ioo 0 ρ from ⟨by nlinarith, by nlinarith⟩)).1
  have e1 : (2 * (δ * r / 2)) ^ s = (δ / 2) ^ s * (2 * r) ^ s := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]; congr 1; ring
  have e2 : (2 * ((1 + δ) * r)) ^ s = (1 + δ) ^ s * (2 * r) ^ s := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]; congr 1; ring
  have e3 : (2 * ((1 - δ) * r)) ^ s = (1 - δ) ^ s * (2 * r) ^ s := by
    rw [← Real.mul_rpow (by linarith) (by positivity)]; congr 1; ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  have hu : 0 < (2 * r) ^ s := by positivity
  have key : (δ / 2) ^ s / 2 ≤ (1 + δ / 2) * (1 + δ) ^ s - (1 - δ / 2) * (1 - δ) ^ s := by
    refine le_of_mul_le_mul_right ?_ hu
    nlinarith
  have hp : (2 : ℝ) ^ s ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs₁.le
  have hp0 : 0 < (2 : ℝ) ^ s := by positivity
  have hδ2 : δ ^ s / 2 ≤ (δ / 2) ^ s := by
    rw [Real.div_rpow hδ0.le (by norm_num)]
    exact div_le_div_of_nonneg_left (by positivity) hp0 hp
  have ha : (1 + δ) ^ s ≤ 1 + δ := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ 1 + δ) hs₁.le
  have hb : 1 - δ ≤ (1 - δ) ^ s := by
    simpa using Real.rpow_le_rpow_of_exponent_ge (by linarith : (0 : ℝ) < 1 - δ) (by linarith)
      hs₁.le
  have ha' := mul_le_mul_of_nonneg_left ha (by linarith : (0 : ℝ) ≤ 1 + δ / 2)
  have hb' := mul_le_mul_of_nonneg_left hb (by linarith : (0 : ℝ) ≤ 1 - δ / 2)
  nlinarith

/-- Theorem 3.19 (Marstrand, `thm:noninteger-density`) for `0 < s < 1`: every `s`-set is
irregular. -/
theorem noninteger_density_of_lt_one {s : ℝ} (hs₀ : 0 < s) (hs₁ : s < 1) {E : Set X}
    (hE : IsSSet s E) : IsIrregularSSet s E := by
  refine ⟨hE, ?_⟩
  obtain ⟨hEm, -, hEfin⟩ := hE
  haveI := Measure.nullSingletonClass_hausdorff X hs₀
  -- `P N`: regular points with the lower mass bound at all radii below `1 / (N + 1)`.
  set P : ℕ → Set X := fun N => {x | x ∈ E ∧ IsRegularPoint s E x ∧
    ∀ r ∈ Ioo 0 (1 / (N + 1 : ℝ)), (2 * r) ^ s / 2 ≤ (μH[s] (E ∩ ball x r)).toReal}
  -- `I N k`: points of `P N` with no other point of `P N` within distance `1 / (k + 1)`.
  set I : ℕ → ℕ → Set X := fun N k =>
    {x | x ∈ P N ∧ ∀ z ∈ P N, dist z x < 1 / (k + 1 : ℝ) → z = x}
  have hI : ∀ N k, μH[s] (I N k) = 0 := by
    intro N k
    refine Set.Countable.measure_zero ?_ _
    refine countable_of_separated_of_hausdorffMeasure_ne_top (d := s) (Nat.one_div_pos_of_nat)
      (fun a ha b hb hab => hb.2 a ha.1 hab) ?_
    exact ne_top_of_le_ne_top hEfin.ne (measure_mono fun z hz => hz.1.1)
  have hP : ∀ N, P N ⊆ ⋃ k, I N k := by
    intro N x hx
    by_contra h
    simp only [mem_iUnion, not_exists] at h
    refine false_of_regular_of_accumulation hs₁ hEm hEfin.ne hx.2.1
      (Nat.one_div_pos_of_nat (n := N)) fun η hη => ?_
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hη
    have hk' : ¬∀ z ∈ P N, dist z x < 1 / (k + 1 : ℝ) → z = x := fun h' => h k ⟨hx, h'⟩
    push Not at hk'
    obtain ⟨z, hz, hzx, hne⟩ := hk'
    exact ⟨z, hne, hzx.trans hk, hz.2.2⟩
  have hR : {x | ¬(x ∈ E → ¬IsRegularPoint s E x)} ⊆ ⋃ N, P N := by
    intro x hx
    simp only [mem_setOf_eq, Classical.not_imp, not_not] at hx
    obtain ⟨ε, hε, hεbd⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1
      (hx.2.eventually_measure_ball_bounds (by norm_num : (0 : ℝ) < 1 / 2))
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine mem_iUnion.2 ⟨N, hx.1, hx.2, fun r hr => ?_⟩
    have := (hεbd ⟨hr.1, hr.2.trans hN⟩).1
    linarith
  rw [ae_iff]
  exact measure_mono_null hR
    (measure_iUnion_null fun N => measure_mono_null (hP N) (measure_iUnion_null (hI N)))

end GeometricMeasureTheory
