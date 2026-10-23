/-
# Section 3.5: Rectifiability of sets of finite length

Countably `1`-rectifiable and purely `1`-unrectifiable sets, the decomposition of a set of finite
length into the two, and their relation to density regularity.

The covering family in `IsCountablyRectifiable` is a countable set of Lipschitz maps, possibly
empty, so the decomposition holds in every metric space. Propositions 3.26 and 3.27 are proved in
finite-dimensional real normed spaces: the notes cover a Lipschitz curve by rectifiable arcs, a
background result from curve theory, whereas the proof here shows directly, through Rademacher's
theorem, that the image of a Lipschitz curve has lower density at least one at almost every point
(`lipschitz_curve_density`).

Theorem 3.28 uses as background the bound `D̲^1(P, x) ≤ 3/4` at almost every point of a purely
`1`-unrectifiable planar set `P` of finite length. It enters as the hypothesis
`BesicovitchLowerDensityBound`. The Palomar entry *A machine-checked bound of 0.6934 for
Besicovitch's 1/2-problem* (PALOMAR-2026-09-02-000011, repository `CoolRmal/Besicovitchs-1-2`)
proves `Besicovitch.forcesOneRectifiability_plane_of_gt`, which gives this bound in the plane
through `besicovitchLowerDensityBound_of_forcesOneRectifiability`. That repository is built on
Lean `v4.32.0` and cannot be imported alongside this library.

| Notes | Lean declaration | Location |
|---|---|---|
| Definition 3.24 (countably rectifiable, purely unrectifiable) | `IsCountablyRectifiable`, `IsPurelyUnrectifiable` | here |
| Theorem 3.25 (rectifiable decomposition) | `rectifiable_decomposition` | here |
| Lower density of Lipschitz curves | `lipschitz_curve_density` | here |
| Proposition 3.26 (curve-like sets are regular) | `curve_like` | here |
| Proposition 3.27 (irregular sets are curve-free) | `curve_free` | here |
| Lower density bound for purely unrectifiable sets (background) | `BesicovitchLowerDensityBound`; `Besicovitch.forcesOneRectifiability_plane_of_gt` | here; Palomar, `CoolRmal/Besicovitchs-1-2`, `Solution.lean` |
| Theorem 3.28 (density and rectifiability) | `density_rectifiability` | here |
-/
import GeometricMeasureTheory.Covering.DensityDecomposition

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-! ## Definition 3.24 (`def:countable-rectifiability`) -/

/-- Definition 3.24 (`def:countable-rectifiability`): `E` is countably `1`-rectifiable if countably
many Lipschitz images of `[0, 1]` cover it up to an `𝓗^1`-null set. -/
def IsCountablyRectifiable (E : Set X) : Prop :=
  ∃ S : Set (ℝ → X), S.Countable ∧ (∀ f ∈ S, ∃ K : ℝ≥0, LipschitzOnWith K f (Icc 0 1)) ∧
    μH[1] (E \ ⋃ f ∈ S, f '' Icc 0 1) = 0

/-- Definition 3.24 (`def:countable-rectifiability`): `E` is purely `1`-unrectifiable if it meets
every Lipschitz image of `[0, 1]` in an `𝓗^1`-null set. -/
def IsPurelyUnrectifiable (E : Set X) : Prop :=
  ∀ f : ℝ → X, (∃ K : ℝ≥0, LipschitzOnWith K f (Icc 0 1)) → μH[1] (E ∩ f '' Icc 0 1) = 0

/-- A disjoint Borel decomposition `E = R ∪ P` into a countably `1`-rectifiable part `R` and a
purely `1`-unrectifiable part `P`. -/
def IsRectifiableDecomposition (E R P : Set X) : Prop :=
  MeasurableSet R ∧ MeasurableSet P ∧ Disjoint R P ∧ R ∪ P = E ∧ IsCountablyRectifiable R ∧
    IsPurelyUnrectifiable P

/-! ## Lipschitz images of `[0, 1]` -/

omit [MeasurableSpace X] [BorelSpace X] in
/-- The image of `[0, 1]` under a map Lipschitz on `[0, 1]` is compact. -/
theorem isCompact_image_Icc_of_lipschitzOnWith {f : ℝ → X} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (Icc 0 1)) : IsCompact (f '' Icc 0 1) :=
  isCompact_Icc.image_of_continuousOn hf.continuousOn

/-- The image of `[0, 1]` under a map `K`-Lipschitz on `[0, 1]` has length at most `K`. -/
theorem hausdorffMeasure_image_Icc_le {f : ℝ → X} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (Icc 0 1)) : μH[1] (f '' Icc 0 1) ≤ K := by
  simpa [hausdorffMeasure_real] using hf.hausdorffMeasure_image_le zero_le_one

/-- A countable union of Lipschitz images of `[0, 1]` is Borel. -/
theorem measurableSet_biUnion_image_Icc {S : Set (ℝ → X)} (hSc : S.Countable)
    (hS : ∀ f ∈ S, ∃ K : ℝ≥0, LipschitzOnWith K f (Icc 0 1)) :
    MeasurableSet (⋃ f ∈ S, f '' Icc 0 1) :=
  MeasurableSet.biUnion hSc fun f hf =>
    (isCompact_image_Icc_of_lipschitzOnWith (hS f hf).choose_spec).measurableSet

/-- A purely `1`-unrectifiable set meets a countably `1`-rectifiable set in an `𝓗^1`-null set. -/
theorem IsPurelyUnrectifiable.hausdorffMeasure_inter_eq_zero {P R : Set X}
    (hP : IsPurelyUnrectifiable P) (hR : IsCountablyRectifiable R) : μH[1] (P ∩ R) = 0 := by
  obtain ⟨S, hSc, hS, hnull⟩ := hR
  refine measure_mono_null (t := (R \ ⋃ f ∈ S, f '' Icc 0 1) ∪ ⋃ f ∈ S, P ∩ f '' Icc 0 1) ?_
    (measure_union_null hnull ((measure_biUnion_null_iff hSc).2 fun f hf => hP f (hS f hf)))
  rintro x ⟨hxP, hxR⟩
  by_cases hx : x ∈ ⋃ f ∈ S, f '' Icc 0 1
  · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.1 hx
    exact Or.inr (mem_iUnion₂.2 ⟨f, hf, hxP, hxf⟩)
  · exact Or.inl ⟨hxR, hx⟩

/-! ## Theorem 3.25 (`thm:rectifiable-decomposition`) -/

/-- Existence in Theorem 3.25: `R = E ∩ G` and `P = E \ G`, where `G` is a countable union of
Lipschitz images of `[0, 1]` maximising `𝓗^1(E ∩ G)`. -/
theorem exists_isRectifiableDecomposition {E : Set X} (hE : MeasurableSet E)
    (hfin : μH[1] E ≠ ∞) : ∃ R P, IsRectifiableDecomposition E R P := by
  set Adm : Set (ℝ → X) → Prop := fun T =>
    T.Countable ∧ ∀ f ∈ T, ∃ K : ℝ≥0, LipschitzOnWith K f (Icc 0 1)
  set val : Set (ℝ → X) → ℝ≥0∞ := fun T => μH[1] (E ∩ ⋃ f ∈ T, f '' Icc 0 1)
  set V : Set ℝ≥0∞ := {v | ∃ T, Adm T ∧ val T = v}
  have hV : V.Nonempty := ⟨_, ∅, ⟨countable_empty, fun _ h => h.elim⟩, rfl⟩
  obtain ⟨u, -, hu, huV⟩ := exists_seq_tendsto_sSup hV (OrderTop.bddAbove V)
  choose T hT hTu using huV
  set S := ⋃ n, T n
  have hS : Adm S := ⟨countable_iUnion fun n => (hT n).1, fun f hf => by
    obtain ⟨n, hn⟩ := mem_iUnion.1 hf
    exact (hT n).2 f hn⟩
  set G := ⋃ f ∈ S, f '' Icc 0 1
  have hGm : MeasurableSet G := measurableSet_biUnion_image_Icc hS.1 hS.2
  have hvalS : val S = sSup V := by
    refine le_antisymm (le_sSup ⟨S, hS, rfl⟩) (le_of_tendsto' hu fun n => ?_)
    rw [← hTu n]
    exact measure_mono (inter_subset_inter_right _
      (biUnion_subset_biUnion_left (subset_iUnion T n)))
  have hafin : sSup V ≠ ∞ := hvalS ▸ ne_top_of_le_ne_top hfin (measure_mono inter_subset_left)
  refine ⟨E ∩ G, E \ G, hE.inter hGm, hE.diff hGm,
    disjoint_left.2 fun x hx hx' => hx'.2 hx.2, inter_union_sdiff E G,
    ⟨S, hS.1, hS.2, measure_mono_null (fun x hx => (hx.2 hx.1.2).elim) measure_empty⟩, ?_⟩
  rintro f ⟨K, hf⟩
  have hS' : Adm (insert f S) := ⟨hS.1.insert f, fun g hg => by
    rcases hg with rfl | hg
    · exact ⟨K, hf⟩
    · exact hS.2 g hg⟩
  have hsplit : E ∩ (f '' Icc 0 1 ∪ G) = (E ∩ G) ∪ ((E \ G) ∩ f '' Icc 0 1) := by
    ext x
    by_cases hx : x ∈ G <;> simp [hx]
  have hle : val (insert f S) ≤ sSup V := le_sSup ⟨_, hS', rfl⟩
  have hval' : val (insert f S) = sSup V + μH[1] ((E \ G) ∩ f '' Icc 0 1) := by
    change μH[1] (E ∩ ⋃ g ∈ insert f S, g '' Icc 0 1) = _
    rw [biUnion_insert, hsplit, measure_union (disjoint_left.2 fun x hx hx' => hx'.1.2 hx.2)
      ((hE.diff hGm).inter (isCompact_image_Icc_of_lipschitzOnWith hf).measurableSet)]
    exact congrArg (· + _) hvalS
  rw [hval'] at hle
  exact nonpos_iff_eq_zero.1 (ENNReal.le_of_add_le_add_left hafin (by simpa using hle))

/-- Uniqueness in Theorem 3.25: two rectifiable decompositions of the same set differ by null
sets. -/
theorem IsRectifiableDecomposition.hausdorffMeasure_symmDiff_eq_zero {E R P R' P' : Set X}
    (h : IsRectifiableDecomposition E R P) (h' : IsRectifiableDecomposition E R' P') :
    μH[1] (symmDiff R R') = 0 ∧ μH[1] (symmDiff P P') = 0 := by
  obtain ⟨-, -, hRP, hE, hR, hP⟩ := h
  obtain ⟨-, -, hRP', hE', hR', hP'⟩ := h'
  have h1 : μH[1] (P' ∩ R) = 0 := hP'.hausdorffMeasure_inter_eq_zero hR
  have h2 : μH[1] (P ∩ R') = 0 := hP.hausdorffMeasure_inter_eq_zero hR'
  have hmem : ∀ x, x ∈ R ∨ x ∈ P ↔ x ∈ R' ∨ x ∈ P' := fun x => by
    rw [← mem_union, ← mem_union, hE, hE']
  constructor
  · refine measure_mono_null ?_ (measure_union_null h1 h2)
    rintro x (⟨hx, hx'⟩ | ⟨hx', hx⟩)
    · exact Or.inl ⟨((hmem x).1 (Or.inl hx)).resolve_left hx', hx⟩
    · exact Or.inr ⟨((hmem x).2 (Or.inl hx')).resolve_left hx, hx'⟩
  · refine measure_mono_null ?_ (measure_union_null h2 h1)
    rintro x (⟨hx, hx'⟩ | ⟨hx', hx⟩)
    · exact Or.inl ⟨hx, ((hmem x).1 (Or.inr hx)).resolve_right hx'⟩
    · exact Or.inr ⟨hx', ((hmem x).2 (Or.inr hx')).resolve_right hx⟩

/-- Theorem 3.25 (`thm:rectifiable-decomposition`): a Borel set of finite `𝓗^1` measure has a
disjoint Borel decomposition into a countably `1`-rectifiable and a purely `1`-unrectifiable part,
unique up to `𝓗^1`-null sets. -/
theorem rectifiable_decomposition {E : Set X} (hE : MeasurableSet E) (hfin : μH[1] E ≠ ∞) :
    (∃ R P, IsRectifiableDecomposition E R P) ∧
      ∀ R P R' P', IsRectifiableDecomposition E R P → IsRectifiableDecomposition E R' P' →
        μH[1] (symmDiff R R') = 0 ∧ μH[1] (symmDiff P P') = 0 :=
  ⟨exists_isRectifiableDecomposition hE hfin,
    fun _ _ _ _ h h' => h.hausdorffMeasure_symmDiff_eq_zero h'⟩

/-! ## Lower density of Lipschitz curves -/

/-- If `S ⊆ [0, 1]` and `d(g s, g t) ≤ ε |s - t|` whenever `s, t ∈ S` and `|s - t| ≤ 1 / n`, then
`𝓗^1(g(S)) ≤ 2ε`: cover `[0, 1]` by `n + 1` intervals of length `1 / n`, on each of which `g` is
`ε`-Lipschitz on `S`. -/
theorem hausdorffMeasure_image_le_two_mul {g : ℝ → X} {S : Set ℝ} (hS : S ⊆ Icc 0 1)
    {ε : ℝ≥0} {n : ℕ} (hn : 0 < n)
    (hg : ∀ t ∈ S, ∀ s ∈ S, dist s t ≤ 1 / n → dist (g s) (g t) ≤ ε * dist s t) :
    μH[1] (g '' S) ≤ 2 * ε := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set J : ℕ → Set ℝ := fun k => Icc (k / n) ((k + 1) / n)
  have hcover : g '' S ⊆ ⋃ k ∈ Finset.range (n + 1), g '' (S ∩ J k) := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨ht0, ht1⟩ := hS ht
    refine mem_biUnion (x := ⌊t * n⌋₊) (Finset.mem_range.2 (Nat.lt_succ_of_le ?_))
      ⟨t, ⟨ht, ?_, ?_⟩, rfl⟩
    · exact Nat.floor_le_of_le (by nlinarith)
    · rw [div_le_iff₀ hn']
      exact Nat.floor_le (by positivity)
    · rw [le_div_iff₀ hn']
      exact (Nat.lt_floor_add_one _).le
  have hpiece : ∀ k, μH[1] (g '' (S ∩ J k)) ≤ ε * ENNReal.ofReal (1 / n) := by
    intro k
    have hL : LipschitzOnWith ε g (S ∩ J k) := by
      refine LipschitzOnWith.of_dist_le_mul fun s hs t ht => hg t ht.1 s hs.1 ?_
      rw [Real.dist_eq]
      have h1 := hs.2
      have h2 := ht.2
      simp only [J, mem_Icc] at h1 h2
      rw [abs_le]
      constructor <;> [skip; skip] <;>
      · have : (k + 1 : ℝ) / n - k / n = 1 / n := by field_simp; ring
        linarith [h1.1, h1.2, h2.1, h2.2]
    calc μH[1] (g '' (S ∩ J k)) ≤ (ε : ℝ≥0∞) ^ (1 : ℝ) * μH[1] (S ∩ J k) :=
          hL.hausdorffMeasure_image_le zero_le_one
      _ ≤ ε * μH[1] (J k) := by
          rw [ENNReal.rpow_one]
          gcongr
          exact inter_subset_right
      _ = ε * ENNReal.ofReal (1 / n) := by
          rw [hausdorffMeasure_real, Real.volume_Icc]
          congr 2
          field_simp
          ring
  calc μH[1] (g '' S) ≤ ∑ k ∈ Finset.range (n + 1), μH[1] (g '' (S ∩ J k)) :=
        (measure_mono hcover).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _k ∈ Finset.range (n + 1), (ε : ℝ≥0∞) * ENNReal.ofReal (1 / n) :=
        Finset.sum_le_sum fun k _ => hpiece k
    _ = ε * ((n + 1 : ℕ) * ENNReal.ofReal (1 / n)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ ε * 2 := by
        gcongr
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_ofNat 2]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_one_div, div_le_iff₀ hn']
        push_cast
        have : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn
        linarith
    _ = 2 * ε := mul_comm _ _

/-- A lower bound for the length of an arm of a curve inside a ball: if the distance from `y`
along `g` on `[a, b]` takes every value in `[0, r)`, then `g([a, b]) ∩ B(y, r)` has length at
least `r`. -/
theorem ofReal_le_hausdorffMeasure_image_Icc_inter_ball {g : ℝ → X} {a b r : ℝ} {y : X}
    (h : Ico 0 r ⊆ (fun s => dist (g s) y) '' Icc a b) :
    ENNReal.ofReal r ≤ μH[1] (g '' Icc a b ∩ ball y r) := by
  calc ENNReal.ofReal r = μH[1] (Ico 0 r) := by
        rw [hausdorffMeasure_real, Real.volume_Ico, sub_zero]
    _ ≤ μH[1] ((dist · y) '' (g '' Icc a b ∩ ball y r)) := by
        refine measure_mono fun ρ hρ => ?_
        obtain ⟨s, hs, hsρ⟩ := h hρ
        have hsρ' : dist (g s) y = ρ := hsρ
        exact ⟨g s, ⟨mem_image_of_mem g hs, by rw [mem_ball, hsρ']; exact hρ.2⟩, hsρ'⟩
    _ ≤ ((1 : ℝ≥0) : ℝ≥0∞) ^ (1 : ℝ) * μH[1] (g '' Icc a b ∩ ball y r) :=
        (LipschitzWith.dist_left y).hausdorffMeasure_image_le zero_le_one _
    _ = μH[1] (g '' Icc a b ∩ ball y r) := by simp

section CurveDensity

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- The image of the set of points of `[0, 1]` where `g` has derivative `0` is `𝓗^1`-null. -/
theorem hausdorffMeasure_image_hasDerivAt_zero (g : ℝ → F) :
    μH[1] (g '' {t ∈ Icc (0 : ℝ) 1 | HasDerivAt g 0 t}) = 0 := by
  set Z := {t ∈ Icc (0 : ℝ) 1 | HasDerivAt g 0 t}
  have key : ∀ ε : ℝ≥0, 0 < ε → μH[1] (g '' Z) ≤ 2 * ε := by
    intro ε hε
    set Zm : ℕ → Set ℝ := fun m =>
      {t ∈ Z | ∀ s, dist s t ≤ 1 / (m + 1 : ℕ) → dist (g s) (g t) ≤ ε * dist s t}
    have hmono : Monotone Zm := by
      intro m m' hmm' t ⟨htZ, ht⟩
      refine ⟨htZ, fun s hs => ht s (hs.trans ?_)⟩
      gcongr
    have hunion : Z = ⋃ m, Zm m := by
      refine subset_antisymm (fun t ht => ?_) (iUnion_subset fun m => fun t ht => ht.1)
      have h := ht.2
      rw [hasDerivAt_iff_isLittleO] at h
      obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 (h.def (show (0 : ℝ) < ε from hε))
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
      refine mem_iUnion.2 ⟨m, ht, fun s hs => ?_⟩
      have := hδ' (hs.trans_lt (by simpa using hm))
      simpa [Real.dist_eq, dist_eq_norm] using this
    have hle : ∀ m, μH[1] (g '' Zm m) ≤ 2 * ε := fun m =>
      hausdorffMeasure_image_le_two_mul (fun t ht => ht.1.1) (Nat.succ_pos m)
        fun t ht s _ hs => ht.2 s hs
    rw [hunion, image_iUnion, Monotone.measure_iUnion
      (show Monotone fun m => g '' Zm m from fun m m' h => image_mono (hmono h))]
    exact iSup_le hle
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  have h2 : (2 : ℝ≥0∞) * ((ε / 2 : ℝ≥0) : ℝ≥0∞) = ε := by
    rw [← ENNReal.coe_two, ← ENNReal.coe_mul, mul_div_cancel₀ _ two_ne_zero]
  rw [zero_add, ← h2]
  exact key _ (half_pos hε)

/-- At a parameter `t ∈ (0, 1)` where the continuous curve `g` has a non-zero derivative, the
image `g([0, 1])` has lower density at least one at `g t`. -/
theorem one_le_lowerDensity_image_of_hasDerivAt {g : ℝ → F} (hg : Continuous g) {t : ℝ}
    (ht : t ∈ Ioo 0 1) {v : F} (hv : v ≠ 0) (hgt : HasDerivAt g v t) :
    1 ≤ lowerDensity 1 (g '' Icc 0 1) (g t) := by
  set y := g t
  set c := ‖v‖
  have hc : 0 < c := norm_pos_iff.2 hv
  rw [hasDerivAt_iff_isLittleO] at hgt
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 (hgt.def (half_pos hc))
  set h₀ := min (δ / 2) (min t (1 - t))
  have hh₀ : 0 < h₀ := lt_min (half_pos hδ) (lt_min ht.1 (sub_pos.2 ht.2))
  have hh₀δ : h₀ ≤ δ / 2 := min_le_left _ _
  have hh₀t : h₀ ≤ t := (min_le_right _ _).trans (min_le_left _ _)
  have hh₀t' : h₀ ≤ 1 - t := (min_le_right _ _).trans (min_le_right _ _)
  have hest : ∀ s ∈ Icc (t - h₀) (t + h₀), ‖g s - y - (s - t) • v‖ ≤ c / 2 * |s - t| := by
    intro s hs
    have : dist s t < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hs.1, hs.2]
    simpa [Real.norm_eq_abs] using hδ' this
  have hfar : ∀ s ∈ Icc (t - h₀) (t + h₀), c / 2 * |s - t| ≤ dist (g s) y := by
    intro s hs
    have h1 := hest s hs
    have h2 : ‖(s - t) • v‖ = |s - t| * c := by rw [norm_smul, Real.norm_eq_abs]
    have h3 : ‖(s - t) • v‖ ≤ ‖g s - y‖ + ‖g s - y - (s - t) • v‖ := by
      calc ‖(s - t) • v‖ = ‖(g s - y) - (g s - y - (s - t) • v)‖ := by rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    rw [dist_eq_norm]
    nlinarith
  have hcross : ∀ s₁ ∈ Icc (t - h₀) t, ∀ s₂ ∈ Icc t (t + h₀), g s₁ = g s₂ → s₁ = t := by
    intro s₁ hs₁ s₂ hs₂ heq
    have e1 := hest s₁ ⟨hs₁.1, by linarith [hs₁.2]⟩
    have e2 := hest s₂ ⟨by linarith [hs₂.1], hs₂.2⟩
    have key : (s₂ - s₁) • v = (g s₁ - y - (s₁ - t) • v) - (g s₂ - y - (s₂ - t) • v) := by
      rw [heq]
      simp only [sub_smul]
      abel
    have hn : ‖(s₂ - s₁) • v‖ = (s₂ - s₁) * c := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs₁.2, hs₂.1])]
    have hle : ‖(s₂ - s₁) • v‖ ≤ c / 2 * |s₁ - t| + c / 2 * |s₂ - t| := by
      rw [key]
      exact (norm_sub_le _ _).trans (add_le_add e1 e2)
    rw [hn, abs_of_nonpos (by linarith [hs₁.2]), abs_of_nonneg (by linarith [hs₂.1])] at hle
    nlinarith [hs₁.2, hs₂.1]
  have hdcont : Continuous fun s => dist (g s) y := hg.dist continuous_const
  have hball : ∀ r, 0 < r → r ≤ c / 2 * h₀ →
      ENNReal.ofReal (2 * r) ≤ μH[1] (g '' Icc 0 1 ∩ ball y r) := by
    intro r hr hrc
    have hfar₁ : r ≤ dist (g (t - h₀)) y := by
      have := hfar (t - h₀) ⟨le_rfl, by linarith⟩
      rw [show t - h₀ - t = -h₀ by ring, abs_neg, abs_of_pos hh₀] at this
      exact hrc.trans this
    have hfar₂ : r ≤ dist (g (t + h₀)) y := by
      have := hfar (t + h₀) ⟨by linarith, le_rfl⟩
      rw [show t + h₀ - t = h₀ by ring, abs_of_pos hh₀] at this
      exact hrc.trans this
    have hy0 : dist (g t) y = 0 := dist_self _
    have harm₁ : ENNReal.ofReal r ≤ μH[1] (g '' Icc (t - h₀) t ∩ ball y r) :=
      ofReal_le_hausdorffMeasure_image_Icc_inter_ball ((Ico_subset_Icc_self.trans
        (Icc_subset_Icc hy0.le hfar₁)).trans
        (intermediate_value_Icc' (by linarith) hdcont.continuousOn))
    have harm₂ : ENNReal.ofReal r ≤ μH[1] (g '' Icc t (t + h₀) ∩ ball y r) :=
      ofReal_le_hausdorffMeasure_image_Icc_inter_ball ((Ico_subset_Icc_self.trans
        (Icc_subset_Icc hy0.le hfar₂)).trans
        (intermediate_value_Icc (by linarith) hdcont.continuousOn))
    have hmeas₂ : MeasurableSet (g '' Icc t (t + h₀) ∩ ball y r) :=
      ((isCompact_Icc.image hg).measurableSet).inter measurableSet_ball
    have hinter : μH[1] ((g '' Icc (t - h₀) t ∩ ball y r) ∩
        (g '' Icc t (t + h₀) ∩ ball y r)) = 0 := by
      haveI := Measure.nullSingletonClass_hausdorff F (d := 1) one_pos
      refine measure_mono_null ?_ (measure_singleton y)
      rintro _ ⟨⟨⟨s₁, hs₁, rfl⟩, -⟩, ⟨⟨s₂, hs₂, heq⟩, -⟩⟩
      rw [mem_singleton_iff, hcross s₁ hs₁ s₂ hs₂ heq.symm]
    have hunion : (g '' Icc (t - h₀) t ∩ ball y r) ∪ (g '' Icc t (t + h₀) ∩ ball y r) ⊆
        g '' Icc 0 1 ∩ ball y r := by
      rintro _ (⟨⟨s, hs, rfl⟩, hb⟩ | ⟨⟨s, hs, rfl⟩, hb⟩)
      · exact ⟨mem_image_of_mem g ⟨by linarith [hs.1], by linarith [hs.2, ht.2]⟩, hb⟩
      · exact ⟨mem_image_of_mem g ⟨by linarith [hs.1, ht.1], by linarith [hs.2]⟩, hb⟩
    calc ENNReal.ofReal (2 * r) = ENNReal.ofReal r + ENNReal.ofReal r := by
          rw [two_mul, ENNReal.ofReal_add hr.le hr.le]
      _ ≤ μH[1] (g '' Icc (t - h₀) t ∩ ball y r) + μH[1] (g '' Icc t (t + h₀) ∩ ball y r) :=
          add_le_add harm₁ harm₂
      _ = μH[1] ((g '' Icc (t - h₀) t ∩ ball y r) ∪ (g '' Icc t (t + h₀) ∩ ball y r)) := by
          rw [← measure_union_add_inter _ hmeas₂, hinter, add_zero]
      _ ≤ _ := measure_mono hunion
  unfold lowerDensity
  refine le_liminf_of_le (h := ?_)
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < c / 2 * h₀ by positivity)] with r hr
  rw [ENNReal.rpow_one, ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_pos.2 (by linarith [hr.1])).ne') (Or.inl ENNReal.ofReal_ne_top),
    one_mul]
  exact hball r hr.1 hr.2.le

end CurveDensity

/-! ## Propositions 3.26 and 3.27 -/

section Normed

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- The image of a Lipschitz curve has lower density at least one at `𝓗^1`-almost every point of
the image. -/
theorem lipschitz_curve_density {f : ℝ → F} {K : ℝ≥0} (hf : LipschitzOnWith K f (Icc 0 1)) :
    ∀ᵐ x ∂μH[1], x ∈ f '' Icc 0 1 → 1 ≤ lowerDensity 1 (f '' Icc 0 1) x := by
  set g : ℝ → F := IccExtend (zero_le_one' ℝ) ((Icc 0 1).restrict f)
  have hgL : LipschitzWith (K * 1) g := hf.to_restrict.comp (LipschitzWith.projIcc _)
  have hgf : EqOn g f (Icc 0 1) := fun t ht => IccExtend_of_mem _ _ ht
  rw [← hgf.image_eq, ae_iff]
  set N : Set ℝ := {0, 1} ∪ {t | ¬DifferentiableAt ℝ g t}
  have hN : volume N = 0 :=
    measure_union_null ((toFinite _).measure_zero _) (ae_iff.1 hgL.ae_differentiableAt_real)
  refine measure_mono_null (t := g '' N ∪ g '' {t ∈ Icc (0 : ℝ) 1 | HasDerivAt g 0 t}) ?_
    (measure_union_null ?_ (hausdorffMeasure_image_hasDerivAt_zero g))
  · intro x hx
    simp only [Classical.not_imp, not_le, mem_setOf_eq] at hx
    obtain ⟨⟨t, ht, rfl⟩, hlt⟩ := hx
    by_cases htN : t ∈ N
    · exact Or.inl (mem_image_of_mem g htN)
    · simp only [N, mem_union, mem_insert_iff, mem_singleton_iff, mem_setOf_eq, not_or,
        not_not] at htN
      obtain ⟨⟨ht0, ht1⟩, hdiff⟩ := htN
      by_cases hd : deriv g t = 0
      · exact Or.inr ⟨t, ⟨ht, hd ▸ hdiff.hasDerivAt⟩, rfl⟩
      · exact absurd (one_le_lowerDensity_image_of_hasDerivAt hgL.continuous
          ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩ hd hdiff.hasDerivAt)
          (not_le.2 hlt)
  · refine nonpos_iff_eq_zero.1 ((hgL.hausdorffMeasure_image_le zero_le_one N).trans ?_)
    simp [hausdorffMeasure_real, hN]

/-- Proposition 3.26 (`thm:curve-like`): every countably `1`-rectifiable `1`-set is regular. -/
theorem curve_like {E : Set F} (hE : IsSSet 1 E) (hrect : IsCountablyRectifiable E) :
    IsRegularSSet 1 E := by
  obtain ⟨S, hSc, hS, hnull⟩ := hrect
  refine ⟨hE, ?_⟩
  have hΓm : ∀ f ∈ S, MeasurableSet (f '' Icc 0 1) := fun f hf =>
    (isCompact_image_Icc_of_lipschitzOnWith (hS f hf).choose_spec).measurableSet
  have hΓfin : ∀ f ∈ S, μH[1] (f '' Icc 0 1) ≠ ∞ := fun f hf =>
    ne_top_of_le_ne_top ENNReal.coe_ne_top (hausdorffMeasure_image_Icc_le (hS f hf).choose_spec)
  have hlow : ∀ f ∈ S, ∀ᵐ x ∂μH[1], x ∈ E ∩ f '' Icc 0 1 → 1 ≤ lowerDensity 1 E x := by
    intro f hf
    filter_upwards [density_inheritance one_pos hE.1 hE.2.2.ne (hE.1.inter (hΓm f hf))
        inter_subset_left,
      density_inheritance one_pos (hΓm f hf) (hΓfin f hf) (hE.1.inter (hΓm f hf))
        inter_subset_right,
      lipschitz_curve_density (hS f hf).choose_spec] with x h1 h2 h3 hx
    rw [← (h1 hx).1, (h2 hx).1]
    exact h3 hx.2
  filter_upwards [(ae_ball_iff hSc).2 hlow, measure_eq_zero_iff_ae_notMem.1 hnull,
    (density_bounds one_pos hE.1 hE.2.2.ne).2] with x hlow hx hup hxE
  obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.1 (Classical.not_not.1 fun h => hx ⟨hxE, h⟩)
  have h1 := hlow f hf ⟨hxE, hxf⟩
  have h2 := (hup hxE).2
  have h3 : lowerDensity 1 E x ≤ upperDensity 1 E x := by
    unfold lowerDensity upperDensity
    exact liminf_le_limsup
  exact ⟨le_antisymm (h3.trans h2) h1, le_antisymm h2 (h1.trans h3)⟩

/-- Proposition 3.27 (`thm:curve-free`): every irregular `1`-set is purely `1`-unrectifiable. -/
theorem curve_free {E : Set F} (hE : IsIrregularSSet 1 E) : IsPurelyUnrectifiable E := by
  rintro f ⟨K, hf⟩
  obtain ⟨hES, hirr⟩ := hE
  have hSm : MeasurableSet (E ∩ f '' Icc 0 1) :=
    hES.1.inter (isCompact_image_Icc_of_lipschitzOnWith hf).measurableSet
  by_contra hpos
  have hS : IsSSet 1 (E ∩ f '' Icc 0 1) :=
    ⟨hSm, pos_iff_ne_zero.2 hpos, (measure_mono inter_subset_left).trans_lt hES.2.2⟩
  have hreg := (curve_like hS ⟨{f}, countable_singleton f,
    fun g hg => (mem_singleton_iff.1 hg) ▸ ⟨K, hf⟩,
    measure_mono_null (fun x hx => (hx.2 (by simpa using hx.1.2)).elim) measure_empty⟩).2
  refine hpos (measure_eq_zero_iff_ae_notMem.2 ?_)
  filter_upwards [hreg, hirr, density_inheritance one_pos hES.1 hES.2.2.ne hSm inter_subset_left]
    with x h1 h2 h3 hx
  exact h2 hx.1 ⟨(h3 hx).1.symm.trans (h1 hx).1, (h3 hx).2.symm.trans (h1 hx).2⟩

end Normed

/-! ## Theorem 3.28 (`thm:density-rectifiability`) -/

/-- The background result of Theorem 3.28: a purely `1`-unrectifiable Borel set of finite length
has lower density at most `3/4` at `𝓗^1`-almost every point. -/
def BesicovitchLowerDensityBound (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] :
    Prop :=
  ∀ P : Set X, MeasurableSet P → μH[1] P ≠ ∞ → IsPurelyUnrectifiable P →
    ∀ᵐ x ∂μH[1], x ∈ P → lowerDensity 1 P x ≤ 3 / 4

/-- Theorem 3.28 (`thm:density-rectifiability`): under the lower density bound, a `1`-set is regular
if and only if it is countably `1`-rectifiable, and irregular if and only if it is purely
`1`-unrectifiable. The notes state this in `ℝ²`, where the bound holds. -/
theorem density_rectifiability {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (hB : BesicovitchLowerDensityBound F)
    {E : Set F} (hE : IsSSet 1 E) :
    (IsRegularSSet 1 E ↔ IsCountablyRectifiable E) ∧
      (IsIrregularSSet 1 E ↔ IsPurelyUnrectifiable E) := by
  have hlt : ¬(1 : ℝ≥0∞) ≤ 3 / 4 := by
    rw [not_le, ENNReal.div_lt_iff (by norm_num) (by norm_num)]
    norm_num
  refine ⟨⟨fun hreg => ?_, curve_like hE⟩, ⟨curve_free, fun hpu => ⟨hE, ?_⟩⟩⟩
  · obtain ⟨R, P, -, hPm, -, hRP, ⟨S, hSc, hS, hnull⟩, hP⟩ :=
      exists_isRectifiableDecomposition hE.1 hE.2.2.ne
    have hPE : P ⊆ E := hRP ▸ subset_union_right
    have hPnull : μH[1] P = 0 := by
      refine measure_eq_zero_iff_ae_notMem.2 ?_
      filter_upwards [hreg.2, hB P hPm (ne_top_of_le_ne_top hE.2.2.ne (measure_mono hPE)) hP,
        density_inheritance one_pos hE.1 hE.2.2.ne hPm hPE] with x h1 h2 h3 hx
      have h4 := h2 hx
      rw [(h3 hx).1, (h1 (hPE hx)).1] at h4
      exact hlt h4
    refine ⟨S, hSc, hS, measure_mono_null ?_ (measure_union_null hnull hPnull)⟩
    rintro x ⟨hxE, hx⟩
    rw [← hRP] at hxE
    rcases hxE with hxR | hxP
    · exact Or.inl ⟨hxR, hx⟩
    · exact Or.inr hxP
  · filter_upwards [hB E hE.1 hE.2.2.ne hpu] with x hx hxE hreg
    have h4 := hx hxE
    rw [hreg.1] at h4
    exact hlt h4

/-- The conclusion of `Besicovitch.forcesOneRectifiability_plane_of_gt` in the Palomar entry
`CoolRmal/Besicovitchs-1-2`, with its definitions unfolded: every Borel set of finite length whose
lower density is at least `β` almost everywhere is covered, up to a null set, by countably many
Lipschitz curves. -/
def ForcesOneRectifiability (X : Type*) [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (β : ℝ≥0∞) : Prop :=
  ∀ s : Set X, MeasurableSet s → μH[1] s < ∞ →
    (∀ᵐ x ∂μH[1].restrict s, β ≤ lowerDensity 1 s x) →
      ∃ f : ℕ → ℝ → X, (∀ i, ∃ K : ℝ≥0, LipschitzWith K (f i)) ∧
        μH[1] (s \ ⋃ i, range (f i)) = 0

/-- The threshold `3/4` forcing rectifiability, which the Palomar entry proves in the plane, gives
the background bound of Theorem 3.28. -/
theorem besicovitchLowerDensityBound_of_forcesOneRectifiability
    (h : ForcesOneRectifiability X (3 / 4)) : BesicovitchLowerDensityBound X := by
  intro P hPm hPfin hP
  set A := {x ∈ P | 3 / 4 < lowerDensity 1 P x}
  have hAm : MeasurableSet A :=
    hPm.inter (measurableSet_lt measurable_const (measurable_lowerDensity 1 P))
  have hAP : A ⊆ P := sep_subset _ _
  suffices hA : μH[1] A = 0 by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hA] with x hx hxP
    exact not_lt.1 fun hlt => hx ⟨hxP, hlt⟩
  have hdens : ∀ᵐ x ∂μH[1].restrict A, 3 / 4 ≤ lowerDensity 1 A x := by
    rw [ae_restrict_iff' hAm]
    filter_upwards [density_inheritance one_pos hPm hPfin hAm hAP] with x h1 hx
    rw [(h1 hx).1]
    exact hx.2.le
  obtain ⟨f, hf, hnull⟩ := h A hAm ((measure_mono hAP).trans_lt hPfin.lt_top) hdens
  have hlip : ∀ n : ℕ, LipschitzWith (2 * ((n : ℝ≥0) + 1))
      fun u : ℝ => 2 * ((n : ℝ) + 1) * u - (n + 1) := fun n => by
    refine LipschitzWith.of_dist_le_mul fun u w => ?_
    rw [Real.dist_eq, Real.dist_eq, show 2 * ((n : ℝ) + 1) * u - (n + 1) -
      (2 * ((n : ℝ) + 1) * w - (n + 1)) = (2 * ((n : ℝ) + 1)) * (u - w) by ring, abs_mul,
      abs_of_nonneg (by positivity)]
    push_cast
    rfl
  refine measure_mono_null (t := (A \ ⋃ i, range (f i)) ∪
      ⋃ i, ⋃ n : ℕ, P ∩ (fun u : ℝ => f i (2 * ((n : ℝ) + 1) * u - (n + 1))) '' Icc 0 1) ?_
    (measure_union_null hnull (measure_iUnion_null fun i => measure_iUnion_null fun n =>
      hP _ ?_))
  · intro x hxA
    by_cases hx : x ∈ ⋃ i, range (f i)
    · obtain ⟨i, s, rfl⟩ := mem_iUnion.1 hx
      set m : ℝ := (⌈|s|⌉₊ : ℝ) + 1 with hm
      have hm0 : 0 < m := by positivity
      have hsm : |s| ≤ m := by linarith [Nat.le_ceil |s|]
      refine Or.inr (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨⌈|s|⌉₊, hAP hxA, (s + m) / (2 * m),
        ⟨div_nonneg (by linarith [neg_abs_le s]) (by positivity), ?_⟩, ?_⟩⟩)
      · rw [div_le_one (by positivity)]
        linarith [le_abs_self s]
      · change f i (2 * m * ((s + m) / (2 * m)) - m) = f i s
        congr 1
        field_simp
        ring
    · exact Or.inl ⟨hxA, hx⟩
  · obtain ⟨K, hK⟩ := hf i
    exact ⟨K * (2 * ((n : ℝ≥0) + 1)), (hK.comp (hlip n)).lipschitzOnWith⟩

end GeometricMeasureTheory
