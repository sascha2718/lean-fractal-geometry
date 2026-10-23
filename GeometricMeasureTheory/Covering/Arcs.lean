/-
# Section 3.5: Rectifiable arcs

Jordan arcs, their length, and their density. The length of an arc is the total variation
`eVariationOn γ (Icc 0 1)` of a parametrisation; Lemma 3.22 shows that it equals `𝓗^1` of the image,
so it depends only on the arc. Everything holds in an arbitrary metric space.

| Notes | Lean declaration | Location |
|---|---|---|
| Definition 3.21 (Jordan arc, length, rectifiable arc) | `IsJordanArc`, `IsRectifiableArc`, `eVariationOn` | here; `Mathlib/Topology/EMetricSpace/BoundedVariation.lean` |
| Lemma 3.22 (`𝓗^1(Γ) = L(Γ)`) | `arc_length`; chord bound `edist_le_hausdorffMeasure_image_Icc` | here |
| Arc-length parametrisation | `arc_length_parametrisation`, `exists_lipschitzOnWith_one_image_eq`; the unit-speed reparametrisation is `naturalParameterization` | here; `Mathlib/Analysis/ConstantSpeed.lean` |
| Proposition 3.23 (rectifiable arcs are regular) | `arc_density`; lower density bound `one_le_lowerDensity_image_Icc` | here |
-/
import GeometricMeasureTheory.Covering.Densities

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

variable {X : Type*} [MetricSpace X]

/-- Definition 3.21 (`def:rectifiable-arc`): a Jordan arc is the image of `[0, 1]` under a
continuous injection. -/
def IsJordanArc (Γ : Set X) : Prop :=
  ∃ γ : ℝ → X, ContinuousOn γ (Icc 0 1) ∧ InjOn γ (Icc 0 1) ∧ γ '' Icc 0 1 = Γ

/-- Definition 3.21 (`def:rectifiable-arc`): a rectifiable arc is a Jordan arc with a
parametrisation of finite length, the length being the supremum of chord sums. -/
def IsRectifiableArc (Γ : Set X) : Prop :=
  ∃ γ : ℝ → X, ContinuousOn γ (Icc 0 1) ∧ InjOn γ (Icc 0 1) ∧ γ '' Icc 0 1 = Γ ∧
    eVariationOn γ (Icc 0 1) ≠ ∞

/-! ## Auxiliary results on curves -/

/-- The signed variation `t ↦ variationOnFromTo γ (Icc a b) c t` of a continuous curve of finite
length is continuous on `[a, b]`. -/
theorem continuousOn_variationOnFromTo {γ : ℝ → X} {a b c : ℝ} (hc : ContinuousOn γ (Icc a b))
    (hfin : eVariationOn γ (Icc a b) ≠ ∞) (hcm : c ∈ Icc a b) :
    ContinuousOn (variationOnFromTo γ (Icc a b) c) (Icc a b) := by
  intro x hx
  have hbv : LocallyBoundedVariationOn γ (Icc a b) :=
    BoundedVariationOn.locallyBoundedVariationOn hfin
  have hl := variationOnFromTo.tendsto_left hcm hx hbv ((hc x hx).mono inter_subset_left).tendsto
  have hr := variationOnFromTo.tendsto_right hcm hx hbv ((hc x hx).mono inter_subset_left).tendsto
  rw [dist_self, sub_zero] at hl
  rw [dist_self, add_zero] at hr
  have hsub : Icc a b ⊆ (Icc a b ∩ Iio x ∪ Icc a b ∩ Ioi x) ∪ {x} := by
    intro y hy
    rcases lt_trichotomy y x with h | rfl | h
    · exact Or.inl (Or.inl ⟨hy, h⟩)
    · exact Or.inr rfl
    · exact Or.inl (Or.inr ⟨hy, h⟩)
  exact ((ContinuousWithinAt.union hl hr).union continuousWithinAt_singleton).mono hsub

/-- The signed variation of a continuous curve of finite length `L` on `[a, b]` maps `[a, b]` onto
`[0, L]`. -/
theorem image_variationOnFromTo_Icc {γ : ℝ → X} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn γ (Icc a b)) (hfin : eVariationOn γ (Icc a b) ≠ ∞) :
    variationOnFromTo γ (Icc a b) a '' Icc a b = Icc 0 (eVariationOn γ (Icc a b)).toReal := by
  have ha : a ∈ Icc a b := left_mem_Icc.2 hab
  have hb : b ∈ Icc a b := right_mem_Icc.2 hab
  have hva : variationOnFromTo γ (Icc a b) a a = 0 := variationOnFromTo.self _ _ _
  have hvb : variationOnFromTo γ (Icc a b) a b = (eVariationOn γ (Icc a b)).toReal := by
    rw [variationOnFromTo.eq_of_le _ _ hab, inter_self]
  have hmono := variationOnFromTo.monotoneOn
    (BoundedVariationOn.locallyBoundedVariationOn (f := γ) (s := Icc a b) hfin) ha
  rw [← hva, ← hvb]
  refine Subset.antisymm ?_ (intermediate_value_Icc hab (continuousOn_variationOnFromTo hc hfin ha))
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨hmono ha ht ht.1, hmono ht hb ht.2⟩

/-- A curve of unit speed on a set is `1`-Lipschitz there. -/
theorem lipschitzOnWith_one_of_hasUnitSpeedOn {g : ℝ → X} {s : Set ℝ} (h : HasUnitSpeedOn g s) :
    LipschitzOnWith 1 g s := by
  intro x hx y hy
  rw [ENNReal.coe_one, one_mul]
  wlog hxy : x ≤ y generalizing x y
  · rw [edist_comm, edist_comm x]
    exact this hy hx (le_of_not_ge hxy)
  calc edist (g x) (g y) ≤ eVariationOn g (s ∩ Icc x y) :=
        eVariationOn.edist_le g ⟨hx, le_rfl, hxy⟩ ⟨hy, hxy, le_rfl⟩
    _ = ENNReal.ofReal ((1 : ℝ≥0) * (y - x)) := h hx hy
    _ = edist x y := by
        rw [NNReal.coe_one, one_mul, edist_dist, Real.dist_eq, abs_sub_comm,
          abs_of_nonneg (sub_nonneg.2 hxy)]

/-- A continuous curve of finite length `L` on `[a, b]` has the same image as a `1`-Lipschitz map
on `[0, L]`, namely its natural parametrisation. -/
theorem exists_lipschitzOnWith_one_image_eq {γ : ℝ → X} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn γ (Icc a b)) (hfin : eVariationOn γ (Icc a b) ≠ ∞) :
    ∃ g : ℝ → X, LipschitzOnWith 1 g (Icc 0 (eVariationOn γ (Icc a b)).toReal) ∧
      g '' Icc 0 (eVariationOn γ (Icc a b)).toReal = γ '' Icc a b := by
  have ha : a ∈ Icc a b := left_mem_Icc.2 hab
  have hbv : LocallyBoundedVariationOn γ (Icc a b) :=
    BoundedVariationOn.locallyBoundedVariationOn hfin
  have himg := image_variationOnFromTo_Icc hab hc hfin
  refine ⟨naturalParameterization γ (Icc a b) a, ?_, ?_⟩
  · rw [← himg]
    exact lipschitzOnWith_one_of_hasUnitSpeedOn (has_unit_speed_naturalParameterization γ hbv ha)
  · rw [← himg, image_image]
    exact image_congr fun t ht =>
      edist_eq_zero.1 (edist_naturalParameterization_eq_zero hbv ha ht)

/-- The last time in `[a, t]` at which a continuous function `h` with `h t ≤ ρ ≤ h a` takes the
value `ρ`: after this time `h` stays at most `ρ`. -/
theorem exists_last_hitting_time {h : ℝ → ℝ} {a t ρ : ℝ} (hat : a ≤ t)
    (hc : ContinuousOn h (Icc a t)) (ht : h t ≤ ρ) (ha : ρ ≤ h a) :
    ∃ t₁ ∈ Icc a t, h t₁ = ρ ∧ ∀ s ∈ Icc t₁ t, h s ≤ ρ := by
  have hKc : IsClosed (Icc a t ∩ h ⁻¹' {ρ}) :=
    hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hKne : (Icc a t ∩ h ⁻¹' {ρ}).Nonempty := by
    obtain ⟨s, hs, hsρ⟩ := intermediate_value_Icc' hat hc ⟨ht, ha⟩
    exact ⟨s, hs, hsρ⟩
  have hKbdd : BddAbove (Icc a t ∩ h ⁻¹' {ρ}) := ⟨t, fun s hs => hs.1.2⟩
  obtain ⟨hmem, hρ⟩ := hKc.csSup_mem hKne hKbdd
  refine ⟨_, hmem, hρ, fun s hs => ?_⟩
  by_contra! hlt
  obtain ⟨s', hs', hs'ρ⟩ := intermediate_value_Icc' hs.2
    (hc.mono (Icc_subset_Icc_left (hmem.1.trans hs.1))) ⟨ht, hlt.le⟩
  have hs'K : s' ≤ sSup (Icc a t ∩ h ⁻¹' {ρ}) :=
    le_csSup hKbdd ⟨⟨hmem.1.trans (hs.1.trans hs'.1), hs'.2⟩, hs'ρ⟩
  rw [le_antisymm hs'.1 (hs'K.trans hs.1), hs'ρ] at hlt
  exact lt_irrefl _ hlt

/-- The first time in `[t, b]` at which a continuous function `h` with `h t ≤ ρ ≤ h b` takes the
value `ρ`: before this time `h` stays at most `ρ`. -/
theorem exists_first_hitting_time {h : ℝ → ℝ} {t b ρ : ℝ} (htb : t ≤ b)
    (hc : ContinuousOn h (Icc t b)) (ht : h t ≤ ρ) (hb : ρ ≤ h b) :
    ∃ t₂ ∈ Icc t b, h t₂ = ρ ∧ ∀ s ∈ Icc t t₂, h s ≤ ρ := by
  have hc' : ContinuousOn (fun s => h (-s)) (Icc (-b) (-t)) :=
    hc.comp continuous_neg.continuousOn fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  obtain ⟨t₁, ht₁, hρ, hle⟩ :=
    exists_last_hitting_time (neg_le_neg htb) hc' (by simpa using ht) (by simpa using hb)
  refine ⟨-t₁, ⟨by linarith [ht₁.2], by linarith [ht₁.1]⟩, hρ, fun s hs => ?_⟩
  simpa using hle (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩

variable [MeasurableSpace X] [BorelSpace X]

/-! ## The chord bound and Lemma 3.22 -/

/-- A preconnected set containing `x` and `y` has `𝓗^1` measure at least `edist x y`. -/
theorem edist_le_hausdorffMeasure_of_isPreconnected {S : Set X} (hS : IsPreconnected S)
    {x y : X} (hx : x ∈ S) (hy : y ∈ S) : edist x y ≤ μH[1] S := by
  have hsub : Icc 0 (dist y x) ⊆ (dist · x) '' S :=
    (hS.image _ (LipschitzWith.dist_left x).continuous.continuousOn).Icc_subset
      ⟨x, hx, dist_self x⟩ ⟨y, hy, rfl⟩
  calc edist x y = volume (Icc 0 (dist y x)) := by
        rw [Real.volume_Icc, sub_zero, edist_dist, dist_comm]
    _ = μH[1] (Icc 0 (dist y x)) := by rw [hausdorffMeasure_real]
    _ ≤ μH[1] ((dist · x) '' S) := measure_mono hsub
    _ ≤ ((1 : ℝ≥0) : ℝ≥0∞) ^ (1 : ℝ) * μH[1] S :=
        (LipschitzWith.dist_left x).hausdorffMeasure_image_le zero_le_one S
    _ = μH[1] S := by simp

/-- The chord bound: the image of `[u, v]` under a continuous curve has `𝓗^1` measure at least the
distance between the endpoints. -/
theorem edist_le_hausdorffMeasure_image_Icc {γ : ℝ → X} {u v : ℝ} (huv : u ≤ v)
    (hc : ContinuousOn γ (Icc u v)) : edist (γ u) (γ v) ≤ μH[1] (γ '' Icc u v) :=
  edist_le_hausdorffMeasure_of_isPreconnected (isPreconnected_Icc.image γ hc)
    (mem_image_of_mem γ ⟨le_rfl, huv⟩) (mem_image_of_mem γ ⟨huv, le_rfl⟩)

/-- Superadditivity of `𝓗^1` along an injective continuous curve: subarcs over adjacent parameter
intervals meet in a single point. -/
theorem hausdorffMeasure_image_Icc_add_le {γ : ℝ → X} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hc : ContinuousOn γ (Icc a c)) (hi : InjOn γ (Icc a c)) :
    μH[1] (γ '' Icc a b) + μH[1] (γ '' Icc b c) ≤ μH[1] (γ '' Icc a c) := by
  haveI := Measure.nullSingletonClass_hausdorff X one_pos
  have hmeas : NullMeasurableSet (γ '' Icc b c) μH[1] :=
    ((isCompact_Icc.image_of_continuousOn (hc.mono (Icc_subset_Icc_left hab))).measurableSet
      ).nullMeasurableSet
  have hinter : γ '' Icc a b ∩ γ '' Icc b c ⊆ {γ b} := by
    rintro _ ⟨⟨s, hs, rfl⟩, ⟨s', hs', hss'⟩⟩
    have := hi ⟨hs'.1.trans' hab, hs'.2⟩ ⟨hs.1, hs.2.trans hbc⟩ hss'
    subst this
    rw [mem_singleton_iff, le_antisymm hs.2 hs'.1]
  rw [← measure_union_add_inter₀ _ hmeas, measure_mono_null hinter (measure_singleton _), add_zero,
    ← image_union, Icc_union_Icc_eq_Icc hab hbc]

/-- Chord sums of an injective continuous curve along a monotone sequence are bounded by the
`𝓗^1` measure of the image. -/
theorem sum_edist_le_hausdorffMeasure_image_Icc {γ : ℝ → X} {u : ℕ → ℝ} (hu : Monotone u) (n : ℕ)
    (hc : ContinuousOn γ (Icc (u 0) (u n))) (hi : InjOn γ (Icc (u 0) (u n))) :
    ∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i)) ≤ μH[1] (γ '' Icc (u 0) (u n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h0n : u 0 ≤ u n := hu (Nat.zero_le n)
    have hn : u n ≤ u (n + 1) := hu (Nat.le_succ n)
    have hsub : Icc (u 0) (u n) ⊆ Icc (u 0) (u (n + 1)) := Icc_subset_Icc_right hn
    rw [Finset.sum_range_succ]
    calc _ ≤ μH[1] (γ '' Icc (u 0) (u n)) + μH[1] (γ '' Icc (u n) (u (n + 1))) := by
          gcongr
          · exact ih (hc.mono hsub) (hi.mono hsub)
          · rw [edist_comm]
            exact edist_le_hausdorffMeasure_image_Icc hn (hc.mono (Icc_subset_Icc_left h0n))
      _ ≤ _ := hausdorffMeasure_image_Icc_add_le h0n hn hc hi

/-- The length of an injective continuous curve is at most the `𝓗^1` measure of its image. -/
theorem eVariationOn_le_hausdorffMeasure_image {γ : ℝ → X} {a b : ℝ}
    (hc : ContinuousOn γ (Icc a b)) (hi : InjOn γ (Icc a b)) :
    eVariationOn γ (Icc a b) ≤ μH[1] (γ '' Icc a b) := by
  refine iSup_le fun ⟨n, u, hu, hus⟩ => ?_
  have hsub : Icc (u 0) (u n) ⊆ Icc a b := Icc_subset_Icc (hus 0).1 (hus n).2
  exact (sum_edist_le_hausdorffMeasure_image_Icc hu n (hc.mono hsub) (hi.mono hsub)).trans
    (measure_mono (image_mono hsub))

/-- The `𝓗^1` measure of the image of a continuous curve is at most its length. -/
theorem hausdorffMeasure_image_le_eVariationOn {γ : ℝ → X} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn γ (Icc a b)) : μH[1] (γ '' Icc a b) ≤ eVariationOn γ (Icc a b) := by
  by_cases hfin : eVariationOn γ (Icc a b) = ∞
  · simp [hfin]
  obtain ⟨g, hg, himg⟩ := exists_lipschitzOnWith_one_image_eq hab hc hfin
  calc μH[1] (γ '' Icc a b) = μH[1] (g '' Icc 0 (eVariationOn γ (Icc a b)).toReal) := by
        rw [himg]
    _ ≤ ((1 : ℝ≥0) : ℝ≥0∞) ^ (1 : ℝ) * μH[1] (Icc 0 (eVariationOn γ (Icc a b)).toReal) :=
        hg.hausdorffMeasure_image_le zero_le_one
    _ = eVariationOn γ (Icc a b) := by
        rw [hausdorffMeasure_real, Real.volume_Icc, sub_zero, ENNReal.ofReal_toReal hfin]
        simp

/-- Lemma 3.22 (`thm:arc-length`): the `𝓗^1` measure of a Jordan arc equals its length. -/
theorem arc_length {γ : ℝ → X} {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn γ (Icc a b))
    (hi : InjOn γ (Icc a b)) : μH[1] (γ '' Icc a b) = eVariationOn γ (Icc a b) :=
  le_antisymm (hausdorffMeasure_image_le_eVariationOn hab hc)
    (eVariationOn_le_hausdorffMeasure_image hc hi)

omit [MeasurableSpace X] [BorelSpace X] in
/-- The paragraph *Arc-length parametrisation*: a continuous curve of finite length `L` has a
Lipschitz parametrisation on `[0, 1]` with constant `L` and the same image. -/
theorem arc_length_parametrisation {γ : ℝ → X} (hc : ContinuousOn γ (Icc 0 1))
    (hfin : eVariationOn γ (Icc 0 1) ≠ ∞) :
    ∃ f : ℝ → X, LipschitzOnWith (eVariationOn γ (Icc 0 1)).toNNReal f (Icc 0 1) ∧
      f '' Icc 0 1 = γ '' Icc 0 1 := by
  obtain ⟨g, hg, himg⟩ := exists_lipschitzOnWith_one_image_eq zero_le_one hc hfin
  set L := (eVariationOn γ (Icc 0 1)).toReal with hL
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  have hmaps : ∀ t ∈ Icc (0 : ℝ) 1, L * t ∈ Icc 0 L := fun t ht =>
    ⟨mul_nonneg hL0 ht.1, mul_le_of_le_one_right hL0 ht.2⟩
  refine ⟨fun t => g (L * t), LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_, ?_⟩
  · calc dist (g (L * x)) (g (L * y)) ≤ (1 : ℝ≥0) * dist (L * x) (L * y) :=
          hg.dist_le_mul _ (hmaps x hx) _ (hmaps y hy)
      _ = (eVariationOn γ (Icc 0 1)).toNNReal * dist x y := by
          rw [NNReal.coe_one, one_mul, ENNReal.coe_toNNReal_eq_toReal, Real.dist_eq, Real.dist_eq,
            ← mul_sub, abs_mul, abs_of_nonneg hL0]
  · rw [← image_image g (L * ·), image_mul_left_Icc hL0 zero_le_one, mul_zero, mul_one, himg]

/-! ## Proposition 3.23 -/

/-- At a point of a Jordan arc other than its endpoints, the lower `1`-density is at least `1`. -/
theorem one_le_lowerDensity_image_Icc {γ : ℝ → X} (hc : ContinuousOn γ (Icc 0 1))
    (hi : InjOn γ (Icc 0 1)) {x : X} (hx : x ∈ γ '' Icc 0 1) (hx0 : x ≠ γ 0) (hx1 : x ≠ γ 1) :
    1 ≤ lowerDensity 1 (γ '' Icc 0 1) x := by
  obtain ⟨t, ht, rfl⟩ := hx
  have hr₀ : 0 < min (dist (γ 0) (γ t)) (dist (γ 1) (γ t)) :=
    lt_min (dist_pos.2 hx0.symm) (dist_pos.2 hx1.symm)
  have hcd : ContinuousOn (fun s => dist (γ s) (γ t)) (Icc 0 1) :=
    (LipschitzWith.dist_left (γ t)).continuous.comp_continuousOn hc
  have key : ∀ ρ, 0 < ρ → ρ < min (dist (γ 0) (γ t)) (dist (γ 1) (γ t)) → ∀ r, ρ < r →
      ENNReal.ofReal (2 * ρ) ≤ μH[1] (γ '' Icc 0 1 ∩ ball (γ t) r) := by
    intro ρ hρ hρr r hr
    obtain ⟨t₁, ht₁, hρ₁, hle₁⟩ := exists_last_hitting_time ht.1
      (hcd.mono (Icc_subset_Icc_right ht.2)) (by simp [hρ.le]) (hρr.trans_le (min_le_left _ _)).le
    obtain ⟨t₂, ht₂, hρ₂, hle₂⟩ := exists_first_hitting_time ht.2
      (hcd.mono (Icc_subset_Icc_left ht.1)) (by simp [hρ.le]) (hρr.trans_le (min_le_right _ _)).le
    have hρ₁' : dist (γ t₁) (γ t) = ρ := hρ₁
    have hρ₂' : dist (γ t₂) (γ t) = ρ := hρ₂
    have hsub : Icc t₁ t₂ ⊆ Icc 0 1 := Icc_subset_Icc ht₁.1 ht₂.2
    calc ENNReal.ofReal (2 * ρ) = edist (γ t₁) (γ t) + edist (γ t) (γ t₂) := by
          rw [edist_dist, edist_dist, hρ₁', dist_comm (γ t), hρ₂', two_mul,
            ENNReal.ofReal_add hρ.le hρ.le]
      _ ≤ μH[1] (γ '' Icc t₁ t) + μH[1] (γ '' Icc t t₂) := by
          gcongr
          · exact edist_le_hausdorffMeasure_image_Icc ht₁.2 (hc.mono (Icc_subset_Icc ht₁.1 ht.2))
          · exact edist_le_hausdorffMeasure_image_Icc ht₂.1 (hc.mono (Icc_subset_Icc ht.1 ht₂.2))
      _ ≤ μH[1] (γ '' Icc t₁ t₂) :=
          hausdorffMeasure_image_Icc_add_le ht₁.2 ht₂.1 (hc.mono hsub) (hi.mono hsub)
      _ ≤ _ := by
          refine measure_mono (subset_inter (image_mono hsub) ?_)
          rintro _ ⟨s, hs, rfl⟩
          rw [mem_ball]
          refine lt_of_le_of_lt ?_ hr
          rcases le_total s t with hst | hst
          · exact hle₁ s ⟨hs.1, hst⟩
          · exact hle₂ s ⟨hst, hs.2⟩
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [Ioo_mem_nhdsGT hr₀] with r hr
  have h2r : ENNReal.ofReal (2 * r) ≠ 0 := by simp [hr.1]
  rw [ENNReal.rpow_one, ENNReal.le_div_iff_mul_le (Or.inl h2r) (Or.inl ENNReal.ofReal_ne_top),
    one_mul]
  have htend : Tendsto (fun ρ : ℝ => ENNReal.ofReal (2 * ρ)) (𝓝[<] r)
      (𝓝 (ENNReal.ofReal (2 * r))) :=
    ((ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)).tendsto r).mono_left
      nhdsWithin_le_nhds
  refine le_of_tendsto htend ?_
  filter_upwards [Ioo_mem_nhdsLT hr.1] with ρ hρ
  exact key ρ hρ.1 (hρ.2.trans hr.2) r hρ.2

/-- Proposition 3.23 (`thm:arc-density`): a rectifiable Jordan arc is a regular `1`-set. -/
theorem arc_density {Γ : Set X} (hΓ : IsRectifiableArc Γ) : IsRegularSSet 1 Γ := by
  obtain ⟨γ, hc, hi, rfl, hfin⟩ := hΓ
  haveI := Measure.nullSingletonClass_hausdorff X one_pos
  have hmeas : MeasurableSet (γ '' Icc 0 1) :=
    (isCompact_Icc.image_of_continuousOn hc).measurableSet
  have hne : γ 0 ≠ γ 1 := fun h =>
    zero_ne_one (hi (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) h)
  have hpos : 0 < μH[1] (γ '' Icc 0 1) :=
    (edist_pos.2 hne).trans_le (edist_le_hausdorffMeasure_image_Icc zero_le_one hc)
  have hfin' : μH[1] (γ '' Icc 0 1) ≠ ∞ := by rwa [arc_length zero_le_one hc hi]
  refine ⟨⟨hmeas, hpos, hfin'.lt_top⟩, ?_⟩
  have hnull : μH[1] ({γ 0, γ 1} : Set X) = 0 := (toFinite _).countable.measure_zero _
  filter_upwards [(density_bounds one_pos hmeas hfin').2, measure_eq_zero_iff_ae_notMem.1 hnull]
    with x hx hxe hxΓ
  have hup := (hx hxΓ).2
  have hlow : 1 ≤ lowerDensity 1 (γ '' Icc 0 1) x :=
    one_le_lowerDensity_image_Icc hc hi hxΓ (fun h => hxe (Or.inl h)) (fun h => hxe (Or.inr h))
  have hle : lowerDensity 1 (γ '' Icc 0 1) x ≤ upperDensity 1 (γ '' Icc 0 1) x :=
    liminf_le_limsup
  exact ⟨le_antisymm (hle.trans hup) hlow, le_antisymm hup (hlow.trans hle)⟩

end GeometricMeasureTheory
