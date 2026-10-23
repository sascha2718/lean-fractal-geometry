/-
# Section 8.2.2: Geometrical homogeneity of quasi-self-similar sets

For a quasi-self-similar set the Hausdorff measure and the Hausdorff content need not agree: the
upper half-circle has content `2` and measure `π`. They are, however, comparable, and the ball
masses obey a power bound. The consequence is a clean criterion: a quasi-self-similar set of
dimension `s` is Ahlfors `s`-regular exactly when its `s`-dimensional Hausdorff measure is
positive.

| Notes | Lean declaration | Location |
|---|---|---|
| Lemma 8.5 (`thm:qss-packing-bounds`) | `qss_packing_bounds` | here |
| Theorem 8.7 (`thm:qss-measure-content`) | `qss_measure_content` | here |
| Corollary 8.9 (Ahlfors regularity) | `qss_isAhlforsRegularSet_iff` | here |
| Exercise 8.10 (Ahlfors regular sets have dimension `s`) | `ahlfors_hausdorff` | `GeometricMeasureTheory.Covering.AhlforsRegular` |
| Exercise 8.11 (`𝓗^s|_E` is a finite Radon measure) | `hausdorffMeasure_restrict_isFiniteMeasure_regular` | here |
-/
import GeometricMeasureTheory.QuasiSelfSimilar.Basic

open MeasureTheory Filter Topology Set Metric

open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-! ### Auxiliary estimates -/

omit [MeasurableSpace X] [BorelSpace X] in
/-- A set whose Hausdorff dimension is a positive real number has at least two points: a
subsingleton has dimension zero. -/
private lemma nontrivial_of_dimH_eq {s : ℝ} (hs : 0 < s) {E : Set X}
    (hdim : dimH E = ENNReal.ofReal s) : E.Nontrivial := by
  rw [← Set.not_subsingleton_iff]
  intro h
  rw [dimH_subsingleton h, eq_comm, ENNReal.ofReal_eq_zero] at hdim
  exact absurd hdim hs.not_ge

omit [MeasurableSpace X] [BorelSpace X] in
/-- A closed ball of radius `ρ` has diameter at most `2ρ`. -/
private lemma ediam_closedBall_le' (y : X) (ρ : ℝ) :
    ediam (closedBall y ρ) ≤ ENNReal.ofReal (2 * ρ) := by
  refine ediam_le_of_forall_dist_le fun u hu v hv => ?_
  rw [mem_closedBall] at hu hv
  calc dist u v ≤ dist u y + dist y v := dist_triangle _ _ _
    _ ≤ ρ + ρ := add_le_add hu (by rwa [dist_comm])
    _ = 2 * ρ := by ring

omit [MeasurableSpace X] [BorelSpace X] in
/-- A set of diameter less than `δ` is an admissible `δ`-cover of itself. -/
private lemma hausdorffDelta_le_ediam_rpow {s : ℝ} (hs : 0 ≤ s) {δ : ℝ≥0∞} {U : Set X}
    (hU : ediam U < δ) : hausdorffDelta s δ U ≤ ediam U ^ s := by
  classical
  rw [(arbitrary_covers hs δ U).1]
  refine iInf_le_of_le (fun i => if i = 0 then U else ∅) (iInf_le_of_le ?_ (iInf_le_of_le ?_ ?_))
  · intro i
    dsimp only
    split_ifs with h
    · exact hU
    · exact (ediam_empty (X := X)).trans_lt (lt_of_le_of_lt zero_le hU)
  · exact subset_iUnion_of_subset 0 (by simp)
  · rw [tsum_eq_single 0 fun i hi => by simp [hi]]
    simp only [gaugeWeight]
    exact iSup_le fun _ => le_rfl

/-- The Hausdorff `δ`-content `𝓗^s_δ` bundled as an outer measure. -/
private def hausdorffDeltaOuter (s : ℝ) {δ : ℝ≥0∞} (hδ : 0 < δ) : OuterMeasure X :=
  (hausdorff_outer_measures (X := X) (fun t => t ^ s) hδ).1.toOuterMeasure

omit [MeasurableSpace X] [BorelSpace X] in
/-- The bundled `δ`-content evaluates as `𝓗^s_δ`. -/
@[simp]
private lemma coe_hausdorffDeltaOuter (s : ℝ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ⇑(hausdorffDeltaOuter (X := X) s hδ) = hausdorffDelta s δ := rfl

/-- The `δ`-content is at most the Hausdorff measure. -/
private lemma hausdorffDelta_le_hausdorffMeasure {s : ℝ} (hs : 0 ≤ s) {δ : ℝ≥0∞} (hδ : 0 < δ)
    (A : Set X) : hausdorffDelta s δ A ≤ μH[s] A := by
  rw [← hausdorffMeasureGauge_rpow hs]
  exact hausdorffDeltaGauge_le_hausdorffMeasureGauge _ hδ A

/-- The Hausdorff content is at most the Hausdorff measure. -/
private lemma hausdorffContent_le_hausdorffMeasure {s : ℝ} (hs : 0 ≤ s) (A : Set X) :
    hausdorffContent s A ≤ μH[s] A :=
  (hausdorffContentGauge_le_hausdorffDeltaGauge _ 1 A).trans
    (hausdorffDelta_le_hausdorffMeasure hs one_pos A)

/-- The Hausdorff measure is the supremum of the `δ`-contents, so a bound on every `δ`-content
shifted by a constant passes to the measure. -/
private lemma hausdorffMeasure_add_le_of_forall {s : ℝ} (hs : 0 ≤ s) {E : Set X} {c b : ℝ≥0∞}
    (h : ∀ δ : ℝ≥0∞, 0 < δ → hausdorffDelta s δ E + c ≤ b) : μH[s] E + c ≤ b := by
  haveI : Nonempty {δ : ℝ≥0∞ // 0 < δ} := ⟨⟨1, one_pos⟩⟩
  rw [← hausdorffMeasureGauge_rpow hs, hausdorffMeasureGauge, iSup_subtype', ENNReal.iSup_add]
  exact iSup_le fun δ => h δ.1 δ.2

/-- A map that expands distances on `S` by at least the factor `k > 0` multiplies the Hausdorff
measure of `S` by at least `k ^ s`: its inverse is `k⁻¹`-Lipschitz on the image. -/
private lemma le_hausdorffMeasure_image_of_dist_le {s : ℝ} (hs : 0 ≤ s) {k : ℝ} (hk : 0 < k)
    {g : X → X} {S : Set X} (h : ∀ u ∈ S, ∀ v ∈ S, k * dist u v ≤ dist (g u) (g v)) :
    ENNReal.ofReal (k ^ s) * μH[s] S ≤ μH[s] (g '' S) := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  haveI : Nonempty X := ⟨x₀⟩
  set f := Function.invFunOn g S with hfdef
  have hfS : ∀ p ∈ g '' S, f p ∈ S ∧ g (f p) = p := by
    rintro p ⟨u, hu, rfl⟩
    exact ⟨Function.invFunOn_mem ⟨u, hu, rfl⟩, Function.invFunOn_eq ⟨u, hu, rfl⟩⟩
  have hinj : Set.InjOn g S := by
    intro u hu v hv huv
    have hd := h u hu v hv
    rw [huv, dist_self] at hd
    refine dist_le_zero.1 (le_of_mul_le_mul_left ?_ hk)
    simpa using hd
  have hSsub : S ⊆ f '' (g '' S) := by
    intro u hu
    obtain ⟨hmem, heq⟩ := hfS (g u) ⟨u, hu, rfl⟩
    exact ⟨g u, ⟨u, hu, rfl⟩, hinj hmem hu heq⟩
  have hlip : LipschitzOnWith (k⁻¹).toNNReal f (g '' S) := by
    refine LipschitzOnWith.of_dist_le' fun p hp q hq => ?_
    obtain ⟨hpS, hpg⟩ := hfS p hp
    obtain ⟨hqS, hqg⟩ := hfS q hq
    have hd := h _ hpS _ hqS
    rw [hpg, hqg] at hd
    rw [inv_mul_eq_div, le_div_iff₀ hk, mul_comm]
    exact hd
  have hkpos : (0 : ℝ) < k ^ s := Real.rpow_pos_of_pos hk s
  have hmeas : μH[s] S ≤ ENNReal.ofReal ((k ^ s)⁻¹) * μH[s] (g '' S) := by
    refine (measure_mono hSsub).trans ?_
    refine (hlip.hausdorffMeasure_image_le hs).trans_eq ?_
    congr 1
    rw [show ((k⁻¹).toNNReal : ℝ≥0∞) = ENNReal.ofReal k⁻¹ from rfl,
      ENNReal.ofReal_rpow_of_pos (by positivity), Real.inv_rpow hk.le]
  calc ENNReal.ofReal (k ^ s) * μH[s] S
      ≤ ENNReal.ofReal (k ^ s) * (ENNReal.ofReal ((k ^ s)⁻¹) * μH[s] (g '' S)) := by gcongr
    _ = ENNReal.ofReal (k ^ s * (k ^ s)⁻¹) * μH[s] (g '' S) := by
        rw [← mul_assoc, ENNReal.ofReal_mul hkpos.le]
    _ = μH[s] (g '' S) := by rw [mul_inv_cancel₀ hkpos.ne', ENNReal.ofReal_one, one_mul]

/-! ## Lemma 8.5 -/

/-- Lemma 8.5 (`thm:qss-packing-bounds`): the maximal packings of a quasi-self-similar set at scale
`r` are bounded above and below by fixed multiples of `r^{-s}`. -/
theorem qss_packing_bounds {D : ℝ} (hD : 0 < D) {E : Set X} (hE : IsCompact E)
    (hQ : IsQuasiSelfSimilar D E) {s : ℝ} (hs : 0 < s) (hdim : dimH E = ENNReal.ofReal s)
    {r : ℝ} (hr : 0 < r) (hrE : r < diam E) (hrD : r < D) :
    ENNReal.ofReal (4 ^ (-s) * r ^ (-s)) * hausdorffContent s E ≤
        (Metric.packingNumber (2 * r).toNNReal E : ℝ≥0∞) ∧
      (Metric.packingNumber (2 * r).toNNReal E : ℝ≥0∞) ≤ ENNReal.ofReal (D ^ s * r ^ (-s)) := by
  have hne : E.Nonempty := (nontrivial_of_dimH_eq hs hdim).nonempty
  have hub := (qss_packing_finite hD hE hne hQ.lower hs hdim.le).1 r hr hrE hrD
  refine ⟨?_, hub⟩
  have hMtop : Metric.packingNumber (2 * r).toNNReal E ≠ ⊤ := fun h => by
    rw [h] at hub; simp at hub
  set P := Metric.maximalSeparatedSet (2 * r).toNNReal E with hPdef
  have hPfin : P.Finite :=
    Set.encard_ne_top_iff.1 (by rw [hPdef, Metric.encard_maximalSeparatedSet hMtop]; exact hMtop)
  have hcard : ((hPfin.toFinset.card : ℕ) : ℝ≥0∞)
      = (Metric.packingNumber (2 * r).toNNReal E : ℝ≥0∞) := by
    rw [← ENat.toENNReal_coe, ← hPfin.encard_eq_coe_toFinset_card, hPdef,
      Metric.encard_maximalSeparatedSet hMtop]
  -- A maximal `2r`-separated set doubles to a cover by balls of radius `2r`.
  have hcov : E ⊆ ⋃ y ∈ hPfin.toFinset, closedBall y (2 * r) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Metric.isCover_maximalSeparatedSet hMtop hx
    refine mem_biUnion (hPfin.mem_toFinset.2 hy) ?_
    rw [mem_closedBall, ← ENNReal.ofReal_le_ofReal_iff (by positivity), ← edist_dist]
    exact hxy
  have hball : ∀ y : X, hausdorffContent s (closedBall y (2 * r)) ≤ ENNReal.ofReal ((4 * r) ^ s) :=
    fun y => (hausdorffContent_le_ediam_rpow hs.le _).trans <| by
      calc ediam (closedBall y (2 * r)) ^ s ≤ ENNReal.ofReal (4 * r) ^ s := by
            refine ENNReal.rpow_le_rpow ?_ hs.le
            have h := ediam_closedBall_le' y (2 * r)
            rwa [show (2 : ℝ) * (2 * r) = 4 * r by ring] at h
        _ = ENNReal.ofReal ((4 * r) ^ s) := ENNReal.ofReal_rpow_of_pos (by positivity)
  have hcontent : hausdorffContent s E
      ≤ ((hPfin.toFinset.card : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((4 * r) ^ s) := by
    calc hausdorffContent s E
        ≤ hausdorffContentOuter s (⋃ y ∈ hPfin.toFinset, closedBall y (2 * r)) :=
          measure_mono (μ := hausdorffContentOuter s) hcov
      _ ≤ ∑ y ∈ hPfin.toFinset, hausdorffContentOuter s (closedBall y (2 * r)) :=
          measure_biUnion_finset_le _ _
      _ ≤ hPfin.toFinset.card • ENNReal.ofReal ((4 * r) ^ s) :=
          Finset.sum_le_card_nsmul _ _ _ fun y _ => hball y
      _ = _ := by rw [nsmul_eq_mul]
  have h4 : (4 : ℝ) ^ s ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) s).ne'
  have hrs : r ^ s ≠ 0 := (Real.rpow_pos_of_pos hr s).ne'
  have hconst : ENNReal.ofReal (4 ^ (-s) * r ^ (-s)) * ENNReal.ofReal ((4 * r) ^ s) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    have hid : (4 : ℝ) ^ (-s) * r ^ (-s) * ((4 : ℝ) * r) ^ s = 1 := by
      rw [Real.mul_rpow (by norm_num) hr.le, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4),
        Real.rpow_neg hr.le]
      field_simp
    rw [hid, ENNReal.ofReal_one]
  calc ENNReal.ofReal (4 ^ (-s) * r ^ (-s)) * hausdorffContent s E
      ≤ ENNReal.ofReal (4 ^ (-s) * r ^ (-s)) *
          (((hPfin.toFinset.card : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((4 * r) ^ s)) := by gcongr
    _ = ((hPfin.toFinset.card : ℕ) : ℝ≥0∞) *
          (ENNReal.ofReal (4 ^ (-s) * r ^ (-s)) * ENNReal.ofReal ((4 * r) ^ s)) := by ring
    _ = ((hPfin.toFinset.card : ℕ) : ℝ≥0∞) := by rw [hconst, mul_one]
    _ = _ := hcard

/-! ## Theorem 8.7 -/

/-- The scale estimate behind Theorem 8.7: pushing `E ∩ B(x₀, r₀)` into the balls of a maximal
`ρ`-packing of `E` produces disjoint pieces whose measures are large while their `δ`-contents at
the scale of their diameters stay small. -/
private lemma qss_scale_estimate {D : ℝ} (hD : 0 < D) {E : Set X} (hE : IsCompact E)
    (hQ : IsQuasiSelfSimilar D E) {s : ℝ} (hs : 0 < s)
    (hdim : dimH E = ENNReal.ofReal s) (x₀ : X) {r₀ : ℝ} (hr₀ : 0 < r₀)
    {ρ : ℝ} (hρ : 0 < ρ) (hρE : ρ < diam E) (hρD : ρ < D) :
    hausdorffDelta s (ENNReal.ofReal (2 * (2 * D * ρ * r₀))) E
        + ENNReal.ofReal (4 ^ (-s) * D ^ (-s)) * hausdorffContent s E *
            μH[s] (E ∩ closedBall x₀ r₀)
      ≤ μH[s] E + ENNReal.ofReal (2 ^ s * D ^ (2 * s) * r₀ ^ s) := by
  classical
  obtain ⟨hlow, hup⟩ := qss_packing_bounds hD hE hQ hs hdim hρ hρE hρD
  have hρs : (0 : ℝ) < ρ ^ s := Real.rpow_pos_of_pos hρ s
  have hDs : (0 : ℝ) < D ^ s := Real.rpow_pos_of_pos hD s
  set δ : ℝ≥0∞ := ENNReal.ofReal (2 * (2 * D * ρ * r₀)) with hδdef
  have hδpos : 0 < δ := ENNReal.ofReal_pos.2 (by positivity)
  set ε : ℝ≥0 := (2 * ρ).toNNReal with hεdef
  have hMtop : Metric.packingNumber ε E ≠ ⊤ := fun h => by rw [h] at hup; simp at hup
  set P := Metric.maximalSeparatedSet ε E with hPdef
  have hPE : P ⊆ E := Metric.maximalSeparatedSet_subset
  have hPfin : P.Finite :=
    Set.encard_ne_top_iff.1 (by rw [hPdef, Metric.encard_maximalSeparatedSet hMtop]; exact hMtop)
  set T := hPfin.toFinset with hTdef
  have hmemT : ∀ y, y ∈ T ↔ y ∈ P := fun y => hPfin.mem_toFinset
  have hcardT : ((T.card : ℕ) : ℝ≥0∞) = (Metric.packingNumber ε E : ℝ≥0∞) := by
    rw [hTdef, ← ENat.toENNReal_coe, ← hPfin.encard_eq_coe_toFinset_card, hPdef,
      Metric.encard_maximalSeparatedSet hMtop]
  have hgex : ∀ y ∈ P, ∃ g : X → X, MapsTo g E (E ∩ closedBall y ρ) ∧
      ∀ u ∈ E, ∀ v ∈ E, D⁻¹ * ρ * dist u v ≤ dist (g u) (g v) ∧
        dist (g u) (g v) ≤ D * ρ * dist u v := fun y hy => hQ y (hPE hy) ρ hρ hρE
  choose! G hGmaps hGdist using hgex
  set S : Set X := E ∩ closedBall x₀ r₀ with hSdef
  have hSE : S ⊆ E := inter_subset_left
  have hScomp : IsCompact S := hE.inter_right isClosed_closedBall
  have hSdist : ∀ u ∈ S, ∀ v ∈ S, dist u v ≤ 2 * r₀ := by
    intro u hu v hv
    calc dist u v ≤ dist u x₀ + dist x₀ v := dist_triangle _ _ _
      _ ≤ r₀ + r₀ :=
          add_le_add (mem_closedBall.1 hu.2) (by rw [dist_comm]; exact mem_closedBall.1 hv.2)
      _ = 2 * r₀ := by ring
  set F : X → Set X := fun y => G y '' S with hFdef
  have hFsub : ∀ y ∈ P, F y ⊆ E ∩ closedBall y ρ := fun y hy =>
    (Set.image_mono hSE).trans (hGmaps y hy).image_subset
  have hFcomp : ∀ y ∈ P, IsCompact (F y) := fun y hy =>
    hScomp.image_of_continuousOn <| (LipschitzOnWith.of_dist_le' (K := D * ρ)
      fun u hu v hv => (hGdist y hy u hu v hv).2).mono hSE |>.continuousOn
  have hFediam : ∀ y ∈ P, ediam (F y) ≤ ENNReal.ofReal (D * ρ * (2 * r₀)) := by
    intro y hy
    refine ediam_le_of_forall_dist_le ?_
    rintro p ⟨u, hu, rfl⟩ q ⟨v, hv, rfl⟩
    exact ((hGdist y hy u (hSE hu) v (hSE hv)).2).trans
      (mul_le_mul_of_nonneg_left (hSdist u hu v hv) (by positivity))
  -- The images sit in the disjoint balls of the packing.
  have hdisj : (T : Set X).PairwiseDisjoint F := by
    rw [hTdef, hPfin.coe_toFinset]
    intro y hy z hz hyz
    refine Set.disjoint_left.2 fun w hw hw' => ?_
    have hsep : (ε : ℝ≥0∞) < edist y z :=
      Metric.isSeparated_maximalSeparatedSet (ε := ε) (A := E) hy hz hyz
    have hd : dist y z ≤ 2 * ρ := by
      calc dist y z ≤ dist y w + dist w z := dist_triangle _ _ _
        _ ≤ ρ + ρ := add_le_add (by rw [dist_comm]; exact mem_closedBall.1 (hFsub y hy hw).2)
              (mem_closedBall.1 (hFsub z hz hw').2)
        _ = 2 * ρ := by ring
    rw [edist_dist] at hsep
    exact absurd (ENNReal.ofReal_le_ofReal hd) (not_le.2 hsep)
  have hFmeas : ∀ y ∈ T, MeasurableSet (F y) := fun y hy =>
    (hFcomp y ((hmemT y).1 hy)).isClosed.measurableSet
  set U : Set X := ⋃ y ∈ T, F y with hUdef
  have hUE : U ⊆ E := iUnion₂_subset fun y hy =>
    (hFsub y ((hmemT y).1 hy)).trans inter_subset_left
  have hUmeas : MeasurableSet U := Finset.measurableSet_biUnion _ hFmeas
  have hid1 : ENNReal.ofReal (4 ^ (-s) * ρ ^ (-s)) * ENNReal.ofReal ((D⁻¹ * ρ) ^ s)
      = ENNReal.ofReal (4 ^ (-s) * D ^ (-s)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.mul_rpow (by positivity) hρ.le, Real.inv_rpow hD.le, Real.rpow_neg hρ.le,
      Real.rpow_neg hD.le]
    field_simp
  -- The images carry a definite share of the measure.
  have hLow : ENNReal.ofReal (4 ^ (-s) * D ^ (-s)) * hausdorffContent s E * μH[s] S
      ≤ μH[s] U := by
    rw [hUdef, measure_biUnion_finset hdisj hFmeas]
    calc ENNReal.ofReal (4 ^ (-s) * D ^ (-s)) * hausdorffContent s E * μH[s] S
        = ENNReal.ofReal (4 ^ (-s) * ρ ^ (-s)) * hausdorffContent s E *
            (ENNReal.ofReal ((D⁻¹ * ρ) ^ s) * μH[s] S) := by rw [← hid1]; ring
      _ ≤ (Metric.packingNumber ε E : ℝ≥0∞) *
            (ENNReal.ofReal ((D⁻¹ * ρ) ^ s) * μH[s] S) := by gcongr
      _ = T.card • (ENNReal.ofReal ((D⁻¹ * ρ) ^ s) * μH[s] S) := by rw [nsmul_eq_mul, hcardT]
      _ ≤ ∑ y ∈ T, μH[s] (F y) :=
          Finset.card_nsmul_le_sum _ _ _ fun y hy =>
            le_hausdorffMeasure_image_of_dist_le hs.le (by positivity)
              fun u hu v hv => (hGdist y ((hmemT y).1 hy) u (hSE hu) v (hSE hv)).1
  have hid2 : ENNReal.ofReal (D ^ s * ρ ^ (-s)) * ENNReal.ofReal ((D * ρ * (2 * r₀)) ^ s)
      = ENNReal.ofReal (2 ^ s * D ^ (2 * s) * r₀ ^ s) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hD.le hρ.le,
      Real.mul_rpow (by norm_num) hr₀.le, Real.rpow_neg hρ.le, two_mul, Real.rpow_add hD]
    field_simp
  -- Their `δ`-contents at the scale of their diameters stay small.
  have hUp : hausdorffDelta s δ U ≤ ENNReal.ofReal (2 ^ s * D ^ (2 * s) * r₀ ^ s) := by
    have hterm : ∀ y ∈ T, hausdorffDelta s δ (F y) ≤ ENNReal.ofReal ((D * ρ * (2 * r₀)) ^ s) := by
      intro y hy
      have hy' := (hmemT y).1 hy
      have hlt : ediam (F y) < δ := by
        refine (hFediam y hy').trans_lt ?_
        rw [hδdef]
        exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.2
          (by nlinarith [mul_pos (mul_pos hD hρ) hr₀])
      refine (hausdorffDelta_le_ediam_rpow hs.le hlt).trans ?_
      calc ediam (F y) ^ s ≤ ENNReal.ofReal (D * ρ * (2 * r₀)) ^ s :=
            ENNReal.rpow_le_rpow (hFediam y hy') hs.le
        _ = ENNReal.ofReal ((D * ρ * (2 * r₀)) ^ s) := ENNReal.ofReal_rpow_of_pos (by positivity)
    calc hausdorffDelta s δ U
        ≤ ∑ y ∈ T, hausdorffDelta s δ (F y) := by
          simpa [hUdef] using
            measure_biUnion_finset_le (μ := hausdorffDeltaOuter (X := X) s hδpos) T F
      _ ≤ T.card • ENNReal.ofReal ((D * ρ * (2 * r₀)) ^ s) :=
          Finset.sum_le_card_nsmul _ _ _ hterm
      _ = ((T.card : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((D * ρ * (2 * r₀)) ^ s) := by rw [nsmul_eq_mul]
      _ ≤ ENNReal.ofReal (D ^ s * ρ ^ (-s)) * ENNReal.ofReal ((D * ρ * (2 * r₀)) ^ s) := by
          rw [hcardT]; gcongr
      _ = _ := hid2
  have hEsplit : μH[s] U + μH[s] (E \ U) = μH[s] E := by
    have h := measure_inter_add_sdiff (μ := μH[s]) E hUmeas
    rwa [inter_eq_right.2 hUE] at h
  have hdeltaE : hausdorffDelta s δ E
      ≤ μH[s] (E \ U) + ENNReal.ofReal (2 ^ s * D ^ (2 * s) * r₀ ^ s) := by
    have hcover : E ⊆ (E \ U) ∪ U := fun x hx => by
      by_cases h : x ∈ U
      exacts [Or.inr h, Or.inl ⟨hx, h⟩]
    calc hausdorffDelta s δ E ≤ hausdorffDelta s δ ((E \ U) ∪ U) := by
          simpa using measure_mono (μ := hausdorffDeltaOuter (X := X) s hδpos) hcover
      _ ≤ hausdorffDelta s δ (E \ U) + hausdorffDelta s δ U := by
          simpa using measure_union_le (μ := hausdorffDeltaOuter (X := X) s hδpos) (E \ U) U
      _ ≤ μH[s] (E \ U) + ENNReal.ofReal (2 ^ s * D ^ (2 * s) * r₀ ^ s) :=
          add_le_add (hausdorffDelta_le_hausdorffMeasure hs.le hδpos _) hUp
  calc hausdorffDelta s δ E +
        ENNReal.ofReal (4 ^ (-s) * D ^ (-s)) * hausdorffContent s E * μH[s] S
      ≤ (μH[s] (E \ U) + ENNReal.ofReal (2 ^ s * D ^ (2 * s) * r₀ ^ s)) + μH[s] U :=
        add_le_add hdeltaE hLow
    _ = (μH[s] U + μH[s] (E \ U)) + ENNReal.ofReal (2 ^ s * D ^ (2 * s) * r₀ ^ s) := by ring
    _ = μH[s] E + ENNReal.ofReal (2 ^ s * D ^ (2 * s) * r₀ ^ s) := by rw [hEsplit]

/-- The ball bound of Theorem 8.7, in the form produced by the scale estimate: the scales cancel
as the approximation parameter tends to zero. -/
private lemma qss_ball_bound {D : ℝ} (hD : 0 < D) {E : Set X} (hE : IsCompact E)
    (hQ : IsQuasiSelfSimilar D E) {s : ℝ} (hs : 0 < s)
    (hdim : dimH E = ENNReal.ofReal s) (hdiam : 0 < diam E) (hfin : μH[s] E ≠ ⊤)
    (x₀ : X) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ENNReal.ofReal (4 ^ (-s) * D ^ (-s)) * hausdorffContent s E *
        μH[s] (E ∩ closedBall x₀ r₀)
      ≤ ENNReal.ofReal (2 ^ s * D ^ (2 * s) * r₀ ^ s) := by
  refine (ENNReal.add_le_add_iff_left hfin).1 ?_
  refine hausdorffMeasure_add_le_of_forall hs.le fun δ hδ => ?_
  obtain ⟨t, ht0, htδ⟩ : ∃ t : ℝ, 0 < t ∧ ENNReal.ofReal t ≤ δ := by
    rcases eq_or_ne δ ⊤ with rfl | h
    · exact ⟨1, one_pos, le_top⟩
    · exact ⟨δ.toReal, ENNReal.toReal_pos hδ.ne' h, (ENNReal.ofReal_toReal h).le⟩
  set ρ : ℝ := min (min (diam E / 2) (D / 2)) (t / (4 * D * r₀)) with hρdef
  have hρ0 : 0 < ρ := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have hρE : ρ < diam E := ((min_le_left _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hρD : ρ < D := ((min_le_left _ _).trans (min_le_right _ _)).trans_lt (by linarith)
  have hρt : 2 * (2 * D * ρ * r₀) ≤ t := by
    have h1 : ρ ≤ t / (4 * D * r₀) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    calc 2 * (2 * D * ρ * r₀) = ρ * (4 * D * r₀) := by ring
      _ ≤ t := h1
  have hanti : hausdorffDelta s δ E
      ≤ hausdorffDelta s (ENNReal.ofReal (2 * (2 * D * ρ * r₀))) E :=
    hausdorffDeltaGauge_anti _ E ((ENNReal.ofReal_le_ofReal hρt).trans htδ)
  exact (add_le_add hanti le_rfl).trans
    (qss_scale_estimate hD hE hQ hs hdim x₀ hr₀ hρ0 hρE hρD)

/-- From the ball bound the measure of a piece of `E` is controlled by the gauge weight of any set
containing it. -/
private lemma measure_inter_le_gaugeWeight {s : ℝ} (hs : 0 < s) {E : Set X} {c : ℝ≥0} (hc : c ≠ 0)
    (hball : ∀ x ∈ E, ∀ r : ℝ, 0 < r → μH[s] (E ∩ closedBall x r) ≤ c * ENNReal.ofReal (r ^ s))
    (A U : Set X) : μH[s] (E ∩ A ∩ U) ≤ c * gaugeWeight (fun t => t ^ s) U := by
  rcases (E ∩ A ∩ U).eq_empty_or_nonempty with h | ⟨x, hx⟩
  · simp [h]
  have hxE : x ∈ E := hx.1.1
  have hxU : x ∈ U := hx.2
  rw [gaugeWeight_of_nonempty _ ⟨x, hxU⟩]
  rcases eq_or_ne (ediam U) ⊤ with htop | htop
  · rw [htop, ENNReal.top_rpow_of_pos hs, ENNReal.mul_top (by exact_mod_cast hc)]
    exact le_top
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0∞) ≤ ediam U) with hzero | hpos
  · haveI := Measure.nullSingletonClass_hausdorff X hs
    have hsub : E ∩ A ∩ U ⊆ {x} := by
      intro u hu
      have hdu : edist u x ≤ ediam U := edist_le_ediam_of_mem hu.2 hxU
      rw [← hzero, nonpos_iff_eq_zero, edist_eq_zero] at hdu
      simp [hdu]
    calc μH[s] (E ∩ A ∩ U) ≤ μH[s] ({x} : Set X) := measure_mono hsub
      _ = 0 := measure_singleton x
      _ ≤ _ := zero_le
  · have hρ : 0 < (ediam U).toReal := ENNReal.toReal_pos hpos.ne' htop
    have hsub : E ∩ A ∩ U ⊆ E ∩ closedBall x (ediam U).toReal := by
      intro u hu
      refine ⟨hu.1.1, ?_⟩
      rw [mem_closedBall, ← ENNReal.ofReal_le_ofReal_iff hρ.le, ← edist_dist,
        ENNReal.ofReal_toReal htop]
      exact edist_le_ediam_of_mem hu.2 hxU
    calc μH[s] (E ∩ A ∩ U) ≤ μH[s] (E ∩ closedBall x (ediam U).toReal) := measure_mono hsub
      _ ≤ c * ENNReal.ofReal ((ediam U).toReal ^ s) := hball x hxE _ hρ
      _ = c * ediam U ^ s := by rw [← ENNReal.ofReal_rpow_of_pos hρ, ENNReal.ofReal_toReal htop]

/-- Exercise 8.8: the ball bound makes the Hausdorff measure of a piece of `E` at most a fixed
multiple of its Hausdorff content. -/
private lemma measure_le_content_of_ball_bound {s : ℝ} (hs : 0 < s) {E : Set X} {c : ℝ≥0}
    (hc : c ≠ 0)
    (hball : ∀ x ∈ E, ∀ r : ℝ, 0 < r → μH[s] (E ∩ closedBall x r) ≤ c * ENNReal.ofReal (r ^ s))
    (A : Set X) : μH[s] (E ∩ A) ≤ c * hausdorffContent s (E ∩ A) := by
  have hc' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc
  rw [(arbitrary_covers hs.le 1 (E ∩ A)).2, ENNReal.mul_iInf_of_ne hc' ENNReal.coe_ne_top]
  refine le_iInf fun U => ?_
  rw [ENNReal.mul_iInf_of_ne hc' ENNReal.coe_ne_top]
  refine le_iInf fun hU => ?_
  calc μH[s] (E ∩ A) ≤ ∑' i, μH[s] (E ∩ A ∩ U i) := by
        refine (measure_mono ?_).trans (measure_iUnion_le _)
        rw [← inter_iUnion]
        exact subset_inter Subset.rfl hU
    _ ≤ ∑' i, (c : ℝ≥0∞) * gaugeWeight (fun t => t ^ s) (U i) :=
        ENNReal.tsum_le_tsum fun i => measure_inter_le_gaugeWeight hs hc hball A (U i)
    _ = _ := ENNReal.tsum_mul_left

/-- Theorem 8.7 (`thm:qss-measure-content`): on a quasi-self-similar set the Hausdorff measure of a
ball obeys a power bound, and the Hausdorff measure and content of every subset are comparable. -/
theorem qss_measure_content {D : ℝ} (hD : 0 < D) {E : Set X} (hE : IsCompact E)
    (hQ : IsQuasiSelfSimilar D E) {s : ℝ} (hs : 0 < s) (hdim : dimH E = ENNReal.ofReal s) :
    ∃ c : ℝ≥0, 0 < c ∧
      (∀ x ∈ E, ∀ r : ℝ, 0 < r → μH[s] (E ∩ closedBall x r) ≤ c * ENNReal.ofReal (r ^ s)) ∧
        ∀ A : Set X, hausdorffContent s (E ∩ A) ≤ μH[s] (E ∩ A) ∧
          μH[s] (E ∩ A) ≤ c * hausdorffContent s (E ∩ A) := by
  have hcontent_le : ∀ A : Set X, hausdorffContent s (E ∩ A) ≤ μH[s] (E ∩ A) := fun A =>
    hausdorffContent_le_hausdorffMeasure hs.le _
  by_cases hzero : μH[s] E = 0
  · have hnull : ∀ A : Set X, μH[s] (E ∩ A) = 0 := fun A =>
      le_antisymm ((measure_mono inter_subset_left).trans hzero.le) zero_le
    exact ⟨1, one_pos, fun x _ r _ => by rw [hnull]; exact zero_le,
      fun A => ⟨hcontent_le A, by rw [hnull]; exact zero_le⟩⟩
  -- A set of positive dimension has at least two points, hence positive diameter.
  have hntriv : E.Nontrivial := nontrivial_of_dimH_eq hs hdim
  have hdiam : 0 < diam E := Metric.diam_pos hntriv hE.isBounded
  have hfin : μH[s] E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (qss_packing_finite hD hE hntriv.nonempty hQ.lower hs hdim.le).2
  have hcont_ne : hausdorffContent s E ≠ 0 := fun h => hzero ((same_null_sets hs.le E).2 h)
  have hcont_top : hausdorffContent s E ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (hausdorffContent_le_hausdorffMeasure hs.le E)
  have hL0 : ENNReal.ofReal (4 ^ (-s) * D ^ (-s)) * hausdorffContent s E ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.2 (by positivity)).ne' hcont_ne
  have hLtop : ENNReal.ofReal (4 ^ (-s) * D ^ (-s)) * hausdorffContent s E ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcont_top
  obtain ⟨c, hcval⟩ : ∃ c : ℝ≥0, (c : ℝ≥0∞) = ENNReal.ofReal (2 ^ s * D ^ (2 * s)) /
      (ENNReal.ofReal (4 ^ (-s) * D ^ (-s)) * hausdorffContent s E) :=
    ⟨_, ENNReal.coe_toNNReal (ENNReal.div_ne_top ENNReal.ofReal_ne_top hL0)⟩
  have hc0 : 0 < c := by
    rw [← ENNReal.coe_pos, hcval]
    exact ENNReal.div_pos (ENNReal.ofReal_pos.2 (by positivity)).ne' hLtop
  have hball : ∀ x ∈ E, ∀ r : ℝ, 0 < r →
      μH[s] (E ∩ closedBall x r) ≤ c * ENNReal.ofReal (r ^ s) := by
    intro x _ r hr
    have hsplit : ENNReal.ofReal (2 ^ s * D ^ (2 * s) * r ^ s)
        = ENNReal.ofReal (2 ^ s * D ^ (2 * s)) * ENNReal.ofReal (r ^ s) :=
      ENNReal.ofReal_mul (by positivity)
    calc μH[s] (E ∩ closedBall x r)
        ≤ ENNReal.ofReal (2 ^ s * D ^ (2 * s) * r ^ s) /
            (ENNReal.ofReal (4 ^ (-s) * D ^ (-s)) * hausdorffContent s E) := by
          rw [ENNReal.le_div_iff_mul_le (Or.inl hL0) (Or.inl hLtop), mul_comm]
          exact qss_ball_bound hD hE hQ hs hdim hdiam hfin x hr
      _ = (c : ℝ≥0∞) * ENNReal.ofReal (r ^ s) := by
          rw [hsplit, hcval, div_eq_mul_inv, div_eq_mul_inv]
          ring
  exact ⟨c, hc0, hball,
    fun A => ⟨hcontent_le A, measure_le_content_of_ball_bound hs hc0.ne' hball A⟩⟩

/-! ## Corollary 8.9 -/

/-- Exercise 8.11: the Hausdorff measure restricted to a compact set of finite measure is a finite
regular measure. -/
theorem hausdorffMeasure_restrict_isFiniteMeasure_regular {s : ℝ} {E : Set X} (hE : IsCompact E)
    (hfin : μH[s] E ≠ ∞) :
    IsFiniteMeasure (μH[s].restrict E) ∧ (μH[s].restrict E).Regular :=
  ⟨isFiniteMeasure_restrict.2 hfin, regular_restrict_of_isCompact hE hfin⟩

/-- Corollary 8.9: a quasi-self-similar set of dimension `s` is Ahlfors `s`-regular exactly when
its `s`-dimensional Hausdorff measure is positive. -/
theorem qss_isAhlforsRegularSet_iff {D : ℝ} (hD : 0 < D) {E : Set X} (hE : IsCompact E)
    (hQ : IsQuasiSelfSimilar D E) {s : ℝ} (hs : 0 < s)
    (hdim : dimH E = ENNReal.ofReal s) :
    IsAhlforsRegularSet s E ↔ 0 < μH[s] E := by
  refine ⟨fun ⟨μ, C, hμ⟩ => (ahlfors_hausdorff hμ hE).2.1, fun hpos => ?_⟩
  have hne : E.Nontrivial := nontrivial_of_dimH_eq hs hdim
  obtain ⟨c, hc0, hball, -⟩ := qss_measure_content hD hE hQ hs hdim
  have hfin : μH[s] E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (qss_packing_finite hD hE hne.nonempty hQ.lower hs hdim.le).2
  have hediam : ediam E ≠ ⊤ := hE.isBounded.ediam_ne_top
  obtain ⟨C₂, hC₂⟩ : ∃ C : ℝ≥0, (C : ℝ≥0∞) = ENNReal.ofReal ((2 * D) ^ s) / μH[s] E :=
    ⟨_, ENNReal.coe_toNNReal (ENNReal.div_ne_top ENNReal.ofReal_ne_top hpos.ne')⟩
  -- Quasi-self-similarity at half the radius gives the lower ball bound.
  have hlow : ∀ x ∈ E, ∀ r : ℝ, 0 < r → ENNReal.ofReal r ≤ ediam E →
      ENNReal.ofReal r ^ s ≤ (C₂ : ℝ≥0∞) * (μH[s].restrict E) (ball x r) := by
    intro x hx r hr hle
    have hrd : r ≤ diam E := by
      have h := ENNReal.toReal_mono hediam hle
      rwa [ENNReal.toReal_ofReal hr.le] at h
    obtain ⟨g, hgmap, hgd⟩ := hQ x hx (r / 2) (by linarith) (by linarith)
    have himg : g '' E ⊆ ball x r ∩ E := by
      rintro p ⟨u, hu, rfl⟩
      have h := hgmap hu
      exact ⟨mem_ball.2 ((mem_closedBall.1 h.2).trans_lt (by linarith)), h.1⟩
    have hkey : ENNReal.ofReal ((D⁻¹ * (r / 2)) ^ s) * μH[s] E
        ≤ (μH[s].restrict E) (ball x r) := by
      refine (le_hausdorffMeasure_image_of_dist_le hs.le (by positivity)
        fun u hu v hv => (hgd u hu v hv).1).trans ?_
      rw [Measure.restrict_apply measurableSet_ball]
      exact measure_mono himg
    have h2 : (2 : ℝ) ^ s ≠ 0 := (Real.rpow_pos_of_pos two_pos s).ne'
    have hDs : D ^ s ≠ 0 := (Real.rpow_pos_of_pos hD s).ne'
    have hid : ENNReal.ofReal ((D⁻¹ * (r / 2)) ^ s)
        = ENNReal.ofReal ((2 * D) ^ (-s)) * ENNReal.ofReal (r ^ s) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hD.le,
        Real.div_rpow hr.le (by norm_num), Real.rpow_neg (by positivity),
        Real.mul_rpow (by norm_num) hD.le]
      field_simp
    have heq : (C₂ : ℝ≥0∞) * (ENNReal.ofReal ((D⁻¹ * (r / 2)) ^ s) * μH[s] E)
        = ENNReal.ofReal (r ^ s) := by
      have h1 : ENNReal.ofReal ((2 * D) ^ s) * ENNReal.ofReal ((2 * D) ^ (-s)) = 1 := by
        rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add (by positivity)]
        simp
      have h3 : (μH[s] E)⁻¹ * μH[s] E = 1 := ENNReal.inv_mul_cancel hpos.ne' hfin
      calc (C₂ : ℝ≥0∞) * (ENNReal.ofReal ((D⁻¹ * (r / 2)) ^ s) * μH[s] E)
          = ENNReal.ofReal ((2 * D) ^ s) * ENNReal.ofReal ((2 * D) ^ (-s)) *
              ((μH[s] E)⁻¹ * μH[s] E) * ENNReal.ofReal (r ^ s) := by
            rw [hC₂, hid, div_eq_mul_inv]; ring
        _ = ENNReal.ofReal (r ^ s) := by rw [h1, h3, one_mul, one_mul]
    rw [ENNReal.ofReal_rpow_of_pos hr, ← heq]
    gcongr
  have hup : ∀ x ∈ E, ∀ r : ℝ, 0 < r →
      (μH[s].restrict E) (ball x r) ≤ (c : ℝ≥0∞) * ENNReal.ofReal r ^ s := by
    intro x hx r hr
    rw [Measure.restrict_apply measurableSet_ball, ENNReal.ofReal_rpow_of_pos hr]
    refine le_trans (measure_mono ?_) (hball x hx r hr)
    exact fun u hu => ⟨hu.2, ball_subset_closedBall hu.1⟩
  have hne_zero : ∀ (K m : ℝ≥0∞) (r : ℝ), 0 < r → ENNReal.ofReal r ^ s ≤ K * m → m ≠ 0 := by
    rintro K m r hr h rfl
    rw [mul_zero] at h
    exact absurd h
      (not_le.2 (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hr) ENNReal.ofReal_ne_top))
  have hsupp : (μH[s].restrict E).support = E := by
    ext x
    constructor
    · intro hx
      by_contra hxE
      refine ((Measure.mem_support_iff_forall x).1 hx Eᶜ
        (hE.isClosed.isOpen_compl.mem_nhds hxE)).ne' ?_
      rw [Measure.restrict_apply hE.isClosed.isOpen_compl.measurableSet, compl_inter_self,
        measure_empty]
    · intro hx
      rw [Measure.mem_support_iff_forall]
      intro U hU
      obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hU
      obtain ⟨r, hr, hrδ⟩ := ((eventually_pos_ofReal_le_ediam hne).and
        (nhdsWithin_le_nhds (eventually_lt_nhds hδ))).exists
      exact (pos_iff_ne_zero.2 (hne_zero _ _ r hr.1 (hlow x hx r hr.1 hr.2))).trans_le
        (measure_mono ((ball_subset_ball hrδ.le).trans hδU))
  exact ⟨μH[s].restrict E, max 1 (max c C₂),
    { isClosed := hE.isClosed
      nontrivial := hne
      pos := hs
      regular := regular_restrict_of_isCompact hE hfin
      support_eq := hsupp
      one_le := le_max_left _ _
      le_measure_ball := fun x hx r hr hrE => (hlow x hx r hr hrE).trans
        (by gcongr; exact (le_max_right c C₂).trans (le_max_right 1 _))
      measure_ball_le := fun x hx r hr _ => (hup x hx r hr).trans
        (by gcongr; exact (le_max_left c C₂).trans (le_max_right 1 _)) }⟩

end GeometricMeasureTheory
