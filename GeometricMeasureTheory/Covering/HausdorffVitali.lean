/-
# Section 3.1: Vitali's covering theorem for the Hausdorff measure

Fine covers and the Vitali covering theorem for Hausdorff measure. The theorem holds in every
metric space when the fineness and the sum are measured by radii; in a real normed space radii and
diameters of balls agree up to the factor two, which gives the form of the notes.

| Notes | Lean declaration | Location |
|---|---|---|
| Definition 3.3 (Vitali cover, fine cover) | `IsFineCover` | here |
| Theorem 3.4 (Vitali for `𝓗^s`) | `hausdorff_vitali` (metric spaces, radii), `hausdorff_vitali_diam` (normed spaces, diameters) | here |
-/
import GeometricMeasureTheory.Covering.VitaliLemmas
import GeometricMeasureTheory.Hausdorff.CoveringConventions

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

/-- Definition 3.3 (`def:fine-cover`): a family `V` of sets is a Vitali cover, or fine cover, of
`E` if every point of `E` lies in members of `V` of arbitrarily small positive diameter. -/
def IsFineCover {X : Type*} [PseudoEMetricSpace X] (V : Set (Set X)) (E : Set X) : Prop :=
  ∀ x ∈ E, ∀ δ : ℝ≥0∞, 0 < δ → ∃ B ∈ V, x ∈ B ∧ 0 < ediam B ∧ ediam B < δ

/-- If a family of terms in `ℝ≥0∞` has infinite sum over `u`, then so does a countable subfamily. -/
private theorem exists_countable_subset_tsum_eq_top {ι : Type*} (f : ι → ℝ≥0∞) {u : Set ι}
    (hu : ∑' i : u, f i = ∞) : ∃ v ⊆ u, v.Countable ∧ ∑' i : v, f i = ∞ := by
  classical
  rw [tsum_subtype] at hu
  have key : ∀ n : ℕ, ∃ G : Finset ι, (n : ℝ≥0∞) < ∑ i ∈ G, u.indicator f i := by
    intro n
    have : (n : ℝ≥0∞) < ∑' i, u.indicator f i := hu ▸ ENNReal.natCast_lt_top n
    rw [ENNReal.tsum_eq_iSup_sum] at this
    exact lt_iSup_iff.1 this
  choose G hG using key
  refine ⟨u ∩ ⋃ n, (G n : Set ι), inter_subset_left,
    (countable_iUnion fun n => (G n).countable_toSet).mono inter_subset_right, ?_⟩
  rw [tsum_subtype]
  by_contra h
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt h
  refine (hn.trans (hG n)).not_ge ?_
  calc ∑ i ∈ G n, u.indicator f i = ∑ i ∈ G n, (u ∩ ⋃ n, (G n : Set ι)).indicator f i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        by_cases hiu : i ∈ u
        · rw [indicator_of_mem hiu, indicator_of_mem (show i ∈ u ∩ ⋃ n, (G n : Set ι) from
            ⟨hiu, mem_iUnion.2 ⟨n, hi⟩⟩)]
        · rw [indicator_of_notMem hiu, indicator_of_notMem fun h => hiu h.1]
    _ ≤ _ := ENNReal.sum_le_tsum _

/-- Theorem 3.4 (`thm:hausdorff-vitali`) in a metric space: for a family of closed balls that
contains, at every point of `E`, balls through that point of arbitrarily small radius, there is a
countable pairwise disjoint subfamily that either covers `E` up to an `𝓗^s`-null set or has
`∑ rᵢ^s = ∞`. -/
theorem hausdorff_vitali {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {s : ℝ}
    (hs : 0 < s) {ι : Type*} (t : Set ι) (c : ι → X) (r : ι → ℝ) (hr : ∀ i ∈ t, 0 < r i)
    (E : Set X) (hfine : ∀ x ∈ E, ∀ δ : ℝ, 0 < δ → ∃ i ∈ t, x ∈ closedBall (c i) (r i) ∧ r i < δ) :
    ∃ u ⊆ t, u.Countable ∧ u.PairwiseDisjoint (fun i => closedBall (c i) (r i)) ∧
      (μH[s] (E \ ⋃ i ∈ u, closedBall (c i) (r i)) = 0 ∨
        ∑' i : u, ENNReal.ofReal (r i) ^ s = ∞) := by
  classical
  obtain ⟨u, hut', hdisj, hmeet, -⟩ := five_r_closedBall {i ∈ t | r i ≤ 1} c r
    (fun i hi => hr i hi.1) (R := 1) fun i hi => hi.2
  have hut : u ⊆ t := hut'.trans (sep_subset _ _)
  by_cases hsum : ∑' i : u, ENNReal.ofReal (r i) ^ s = ∞
  · obtain ⟨v, hvu, hvc, hv⟩ := exists_countable_subset_tsum_eq_top
      (fun i => ENNReal.ofReal (r i) ^ s) hsum
    exact ⟨v, hvu.trans hut, hvc, hdisj.subset hvu, Or.inr hv⟩
  have hcount : u.Countable := by
    have hsupp : Function.support (fun i : u => ENNReal.ofReal (r i) ^ s) = univ := by
      ext i
      simp only [Function.mem_support, mem_univ, iff_true]
      exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 (hr i (hut i.2))) ENNReal.ofReal_ne_top).ne'
    have := Summable.countable_support_ennreal hsum
    rw [hsupp] at this
    exact countable_coe_iff.1 (countable_univ_iff.1 this)
  refine ⟨u, hut, hcount, hdisj, Or.inl ?_⟩
  haveI : Countable u := hcount.to_subtype
  set A := E \ ⋃ i ∈ u, closedBall (c i) (r i)
  -- The points of `A` outside a finite part of `u` are covered by the enlarged remaining balls.
  have hcover : ∀ F : Finset u, A ⊆ ⋃ j : {j : u // j ∉ F}, closedBall (c j) (5 * r j) := by
    intro F z hz
    obtain ⟨hzE, hzu⟩ := hz
    have hKc : IsClosed (⋃ i ∈ F, closedBall (c (i : ι)) (r i)) :=
      isClosed_biUnion_finset fun i _ => isClosed_closedBall
    have hzK : z ∉ ⋃ i ∈ F, closedBall (c (i : ι)) (r i) := by
      intro hzK
      obtain ⟨i, -, hzi⟩ := mem_iUnion₂.1 hzK
      exact hzu (mem_biUnion i.2 hzi)
    obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.1 hKc.isOpen_compl z hzK
    obtain ⟨i, hit, hzi, hri⟩ := hfine z hzE (min (ε / 2) 1) (lt_min (half_pos εpos) one_pos)
    obtain ⟨j, hju, ⟨w, hwi, hwj⟩, hrij⟩ := hmeet i ⟨hit, hri.le.trans (min_le_right _ _)⟩
    rw [mem_closedBall] at hzi hwi
    have hwz : dist w z < ε := by
      calc dist w z ≤ dist w (c i) + dist z (c i) := dist_triangle_right _ _ _
        _ ≤ r i + r i := add_le_add hwi hzi
        _ < ε := by linarith [min_le_left (ε / 2) 1]
    have hjF : (⟨j, hju⟩ : u) ∉ F := fun hjF => hε (mem_ball.2 hwz) (mem_iUnion₂.2 ⟨_, hjF, hwj⟩)
    refine mem_iUnion.2 ⟨⟨⟨j, hju⟩, hjF⟩, ?_⟩
    rw [mem_closedBall] at hwj ⊢
    calc dist z (c j) ≤ dist z (c i) + dist (c i) w + dist w (c j) := dist_triangle4 _ _ _ _
      _ ≤ r i + r i + r j := by rw [dist_comm] at hwi; linarith
      _ ≤ 5 * r j := by linarith
  have htail := ENNReal.tendsto_tsum_compl_atTop_zero hsum
  set tail : Finset u → ℝ≥0∞ := fun F => ∑' b : {x : u // x ∉ F}, ENNReal.ofReal (r b) ^ s
    with htail_def
  have hρ : Tendsto (fun F => 10 * tail F ^ s⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun F => tail F ^ s⁻¹) atTop (𝓝 0) := by
      have := (ENNReal.continuous_rpow_const (y := s⁻¹)).tendsto 0 |>.comp htail
      rwa [ENNReal.zero_rpow_of_pos (inv_pos.2 hs)] at this
    rw [← mul_zero (10 : ℝ≥0∞)]
    exact ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.ofNat_ne_top)
  have hdiam : ∀ (F : Finset u) (j : {x : u // x ∉ F}),
      ediam (closedBall (c j) (5 * r j)) ≤ 10 * ENNReal.ofReal (r j) := by
    intro F j
    have hrj : 0 < r j := hr _ (hut j.1.2)
    refine (ediam_le_of_forall_dist_le (C := 10 * r j) fun y hy z hz => ?_).trans_eq ?_
    · rw [mem_closedBall] at hy hz
      linarith [dist_triangle_right y z (c j)]
    · rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hle := Measure.hausdorffMeasure_le_liminf_tsum s A (l := atTop) _ hρ
    (fun F (j : {x : u // x ∉ F}) => closedBall (c j) (5 * r j))
    (Eventually.of_forall fun F j => (hdiam F j).trans ?_) (Eventually.of_forall hcover)
  · have hlim : Tendsto (fun F : Finset u => ∑' j : {x : u // x ∉ F},
        ediam (closedBall (c j) (5 * r j)) ^ s) atTop (𝓝 0) := by
      have h1 : Tendsto (fun F => (10 : ℝ≥0∞) ^ s * tail F) atTop (𝓝 0) := by
        rw [← mul_zero ((10 : ℝ≥0∞) ^ s)]
        exact ENNReal.Tendsto.const_mul htail
          (Or.inr (ENNReal.rpow_ne_top_of_nonneg hs.le ENNReal.ofNat_ne_top))
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => zero_le)
        fun F => ?_
      simp only [htail_def, ← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun j => ?_
      rw [← ENNReal.mul_rpow_of_nonneg _ _ hs.le]
      exact ENNReal.rpow_le_rpow (hdiam F j) hs.le
    exact le_antisymm (hle.trans_eq hlim.liminf_eq) zero_le
  · gcongr
    rw [ENNReal.le_rpow_inv_iff hs]
    exact ENNReal.le_tsum (f := fun b : {x : u // x ∉ F} => ENNReal.ofReal (r b) ^ s) j

/-- Theorem 3.4 (`thm:hausdorff-vitali`) in the form of the notes, for a closed Vitali cover in a
real normed space: there is a countable pairwise disjoint subfamily that either covers `E` up to an
`𝓗^s`-null set or has `∑ |Bᵢ|^s = ∞`. -/
theorem hausdorff_vitali_diam {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [Nontrivial F]
    [MeasurableSpace F] [BorelSpace F] {s : ℝ} (hs : 0 < s) {V : Set (Set F)}
    (hV : ∀ B ∈ V, ∃ x : F, ∃ r : ℝ, 0 < r ∧ B = closedBall x r) {E : Set F}
    (hfine : IsFineCover V E) :
    ∃ V' ⊆ V, V'.Countable ∧ V'.PairwiseDisjoint id ∧
      (μH[s] (E \ ⋃₀ V') = 0 ∨ ∑' B : V', ediam (B : Set F) ^ s = ∞) := by
  classical
  choose! c r hr hB using hV
  have hdiam : ∀ B ∈ V, ediam B = 2 * ENNReal.ofReal (r B) := by
    intro B hBV
    calc ediam B = ediam (closedBall (c B) (r B)) := congrArg ediam (hB B hBV)
      _ = ENNReal.ofReal (Metric.diam (closedBall (c B) (r B))) :=
        (ENNReal.ofReal_toReal isBounded_closedBall.ediam_ne_top).symm
      _ = 2 * ENNReal.ofReal (r B) := by
        rw [Metric.diam_closedBall_eq _ (hr B hBV).le, ENNReal.ofReal_mul zero_le_two,
          ENNReal.ofReal_ofNat]
  have hfine' : ∀ x ∈ E, ∀ δ : ℝ, 0 < δ → ∃ B ∈ V, x ∈ closedBall (c B) (r B) ∧ r B < δ := by
    intro x hx δ hδ
    obtain ⟨B, hBV, hxB, -, hBδ⟩ := hfine x hx (ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ)
    refine ⟨B, hBV, by rw [← hB B hBV]; exact hxB, ?_⟩
    rw [hdiam B hBV] at hBδ
    exact (ENNReal.ofReal_lt_ofReal_iff'.1
      ((le_mul_of_one_le_left zero_le one_le_two).trans_lt hBδ)).1
  obtain ⟨u, huV, hucount, hudisj, hu⟩ := hausdorff_vitali hs V c r hr E hfine'
  refine ⟨u, huV, hucount, fun B hBu B' hB'u hne => ?_, ?_⟩
  · have := hudisj hBu hB'u hne
    simp only [Function.onFun, id] at this ⊢
    rwa [← hB B (huV hBu), ← hB B' (huV hB'u)] at this
  · have hunion : ⋃₀ u = ⋃ B ∈ u, closedBall (c B) (r B) := by
      rw [sUnion_eq_biUnion]
      exact iUnion₂_congr fun B hBu => hB B (huV hBu)
    rcases hu with h | h
    · left
      rwa [hunion]
    · right
      have h2 : ∀ B : u, ediam (B : Set F) ^ s = 2 ^ s * ENNReal.ofReal (r B) ^ s := fun B => by
        rw [hdiam B (huV B.2), ENNReal.mul_rpow_of_nonneg _ _ hs.le]
      rw [tsum_congr h2, ENNReal.tsum_mul_left, h, ENNReal.mul_top]
      exact (ENNReal.rpow_pos two_pos ENNReal.ofNat_ne_top).ne'

end GeometricMeasureTheory
