/-
# Exercise 8.12: a Vitali covering theorem for compact sets

The Vitali covering theorem of Section 3.1 with balls replaced by compact sets of positive
diameter. It is the covering theorem behind Proposition 8.4.

| Notes | Lean declaration | Location |
|---|---|---|
| Exercise 8.12 (`ex:compact-vitali`) | `hausdorff_vitali_compact` | here |
| Exercise 8.12, the general form for closed sets | `hausdorff_vitali_closed` | here |
| Exercise 8.12, the tail estimate of the hint | `hausdorffMeasure_eq_zero_of_tail_cover` | here |
| Theorem 3.4, the version for balls | `hausdorff_vitali` | `GeometricMeasureTheory.Covering.HausdorffVitali` |
-/
import GeometricMeasureTheory.CookieCutter.Basic

open MeasureTheory Filter Topology Set Metric

open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

section Diameter

variable {X : Type*} [MetricSpace X]

/-- A set of positive diameter is nonempty. -/
theorem nonempty_of_diam_pos {A : Set X} (hA : 0 < diam A) : A.Nonempty := by
  rcases A.eq_empty_or_nonempty with rfl | h
  · simp at hA
  · exact h

/-- A set of positive diameter is bounded, since an unbounded set has diameter `0`. -/
theorem isBounded_of_diam_pos {A : Set X} (hA : 0 < diam A) : Bornology.IsBounded A := by
  by_contra h
  rw [diam_eq_zero_of_unbounded h] at hA
  exact hA.false

/-- A bounded set `V` meeting a bounded set `W` of at least half its diameter lies in the closed
ball of radius `3 |W|` centred at any point of `W`. -/
theorem subset_closedBall_of_inter_nonempty {V W : Set X} (hV : Bornology.IsBounded V)
    (hW : Bornology.IsBounded W) (hVW : (V ∩ W).Nonempty) (hle : diam V ≤ 2 * diam W) {c : X}
    (hc : c ∈ W) : V ⊆ closedBall c (3 * diam W) := by
  obtain ⟨w, hwV, hwW⟩ := hVW
  intro z hz
  rw [mem_closedBall]
  calc dist z c ≤ dist z w + dist w c := dist_triangle _ _ _
    _ ≤ diam V + diam W :=
        add_le_add (dist_le_diam_of_mem hV hz hwV) (dist_le_diam_of_mem hW hwW hc)
    _ ≤ 3 * diam W := by linarith

end Diameter

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The tail estimate behind the Vitali covering theorems: a set covered, for every finite set `F`
of indices, by the closed balls `closedBall (c j) (ρ j)` with `j ∉ F` is `𝓗^s`-null as soon as
`∑ ρ j ^ s` converges. -/
theorem hausdorffMeasure_eq_zero_of_tail_cover {s : ℝ} (hs : 0 < s) {κ : Type*} [Countable κ]
    (c : κ → X) (ρ : κ → ℝ) {A : Set X} (hsum : ∑' j, ENNReal.ofReal (ρ j) ^ s ≠ ∞)
    (hcov : ∀ F : Finset κ, A ⊆ ⋃ j : {j : κ // j ∉ F}, closedBall (c j) (ρ j)) :
    μH[s] A = 0 := by
  set tail : Finset κ → ℝ≥0∞ := fun F => ∑' b : {x : κ // x ∉ F}, ENNReal.ofReal (ρ b) ^ s
    with htail_def
  have htail : Tendsto tail atTop (𝓝 0) := ENNReal.tendsto_tsum_compl_atTop_zero hsum
  have hr : Tendsto (fun F => 2 * tail F ^ s⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun F => tail F ^ s⁻¹) atTop (𝓝 0) := by
      have := (ENNReal.continuous_rpow_const (y := s⁻¹)).tendsto 0 |>.comp htail
      rwa [ENNReal.zero_rpow_of_pos (inv_pos.2 hs)] at this
    rw [← mul_zero (2 : ℝ≥0∞)]
    exact ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.ofNat_ne_top)
  have hdiam : ∀ (F : Finset κ) (j : {x : κ // x ∉ F}),
      ediam (closedBall (c j) (ρ j)) ≤ 2 * ENNReal.ofReal (ρ j) := by
    intro F j
    refine (ediam_le_of_forall_dist_le (C := 2 * ρ j) fun y hy z hz => ?_).trans_eq ?_
    · rw [mem_closedBall] at hy hz
      linarith [dist_triangle_right y z (c j)]
    · rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hle := Measure.hausdorffMeasure_le_liminf_tsum s A (l := atTop) _ hr
    (fun F (j : {x : κ // x ∉ F}) => closedBall (c j) (ρ j))
    (Eventually.of_forall fun F j => (hdiam F j).trans ?_) (Eventually.of_forall hcov)
  · have hlim : Tendsto (fun F : Finset κ => ∑' j : {x : κ // x ∉ F},
        ediam (closedBall (c j) (ρ j)) ^ s) atTop (𝓝 0) := by
      have h1 : Tendsto (fun F => (2 : ℝ≥0∞) ^ s * tail F) atTop (𝓝 0) := by
        rw [← mul_zero ((2 : ℝ≥0∞) ^ s)]
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
    exact ENNReal.le_tsum (f := fun b : {x : κ // x ∉ F} => ENNReal.ofReal (ρ b) ^ s) j

/-- Exercise 8.12 (`ex:compact-vitali`) for closed sets: from a countable fine cover of `A` by
closed sets of positive diameter one can select a pairwise disjoint subfamily which either covers
`A` up to an `𝓗^s`-null set or has divergent sum of `s`-th powers of diameters. Boundedness of the
members is automatic, since an unbounded set has `Metric.diam` equal to `0`, and this is why
compactness is not needed. -/
theorem hausdorff_vitali_closed {s : ℝ} (hs : 0 < s) {ι : Type*} (t : Set ι) (V : ι → Set X)
    (ht : t.Countable) (hV : ∀ i ∈ t, IsClosed (V i)) (hVd : ∀ i ∈ t, 0 < diam (V i))
    {A : Set X} (hfine : ∀ x ∈ A, ∀ δ : ℝ, 0 < δ → ∃ i ∈ t, x ∈ V i ∧ diam (V i) < δ) :
    ∃ u ⊆ t, u.PairwiseDisjoint V ∧
      (μH[s] (A \ ⋃ i ∈ u, V i) = 0 ∨ ∑' i : u, ENNReal.ofReal (diam (V i)) ^ s = ∞) := by
  classical
  -- Select greedily among the sets of diameter at most one, in decreasing diameter classes.
  obtain ⟨u, hut', hdisj, hmeet⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement V
    {i ∈ t | diam (V i) ≤ 1} (fun i => diam (V i)) 2 one_lt_two (fun i _ => diam_nonneg) 1
    (fun i hi => hi.2) fun i hi => nonempty_of_diam_pos (hVd i hi.1)
  have hut : u ⊆ t := fun i hi => (hut' hi).1
  refine ⟨u, hut, hdisj, ?_⟩
  by_cases hsum : ∑' i : u, ENNReal.ofReal (diam (V i)) ^ s = ∞
  · exact Or.inr hsum
  refine Or.inl ?_
  haveI : Countable u := (ht.mono hut).to_subtype
  choose c hc using fun i : u => nonempty_of_diam_pos (hVd i (hut i.2))
  -- Outside any finite part of the selection, the remainder is covered by the enlarged tail.
  have hcover : ∀ F : Finset u, A \ (⋃ i ∈ u, V i) ⊆
      ⋃ j : {j : u // j ∉ F}, closedBall (c j) (3 * diam (V j)) := by
    intro F z hz
    obtain ⟨hzA, hzu⟩ := hz
    have hKc : IsClosed (⋃ i ∈ F, V (i : ι)) :=
      isClosed_biUnion_finset fun i _ => hV i (hut i.2)
    have hzK : z ∉ ⋃ i ∈ F, V (i : ι) := by
      intro h
      obtain ⟨i, -, hzi⟩ := mem_iUnion₂.1 h
      exact hzu (mem_biUnion i.2 hzi)
    obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.1 hKc.isOpen_compl z hzK
    obtain ⟨i, hit, hzi, hdi⟩ := hfine z hzA (min ε 1) (lt_min εpos one_pos)
    obtain ⟨j, hju, ⟨w, hwi, hwj⟩, hdij⟩ :=
      hmeet i ⟨hit, (hdi.trans_le (min_le_right _ _)).le⟩
    have hbi : Bornology.IsBounded (V i) := isBounded_of_diam_pos (hVd i hit)
    have hbj : Bornology.IsBounded (V j) := isBounded_of_diam_pos (hVd j (hut hju))
    have hwz : dist w z < ε :=
      (dist_le_diam_of_mem hbi hwi hzi).trans_lt (hdi.trans_le (min_le_left _ _))
    have hjF : (⟨j, hju⟩ : u) ∉ F := fun hjF => hε (mem_ball.2 hwz) (mem_iUnion₂.2 ⟨_, hjF, hwj⟩)
    exact mem_iUnion.2 ⟨⟨⟨j, hju⟩, hjF⟩,
      subset_closedBall_of_inter_nonempty hbi hbj ⟨w, hwi, hwj⟩ hdij (hc ⟨j, hju⟩) hzi⟩
  refine hausdorffMeasure_eq_zero_of_tail_cover hs c (fun j => 3 * diam (V j)) ?_ hcover
  have h3 : ∀ j : u, ENNReal.ofReal (3 * diam (V j)) ^ s
      = 3 ^ s * ENNReal.ofReal (diam (V j)) ^ s := fun j => by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.mul_rpow_of_nonneg _ _ hs.le]
  rw [tsum_congr h3, ENNReal.tsum_mul_left]
  exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hs.le ENNReal.ofNat_ne_top) hsum

/-- Exercise 8.12 (`ex:compact-vitali`): from a countable fine cover of `A` by compact sets of
positive diameter one can select a pairwise disjoint subfamily which either covers `A` up to an
`𝓗^s`-null set or has divergent sum of `s`-th powers of diameters. -/
theorem hausdorff_vitali_compact {s : ℝ} (hs : 0 < s) {ι : Type*} (t : Set ι) (V : ι → Set X)
    (ht : t.Countable) (hV : ∀ i ∈ t, IsCompact (V i)) (hVd : ∀ i ∈ t, 0 < diam (V i))
    {A : Set X} (hfine : ∀ x ∈ A, ∀ δ : ℝ, 0 < δ → ∃ i ∈ t, x ∈ V i ∧ diam (V i) < δ) :
    ∃ u ⊆ t, u.PairwiseDisjoint V ∧
      (μH[s] (A \ ⋃ i ∈ u, V i) = 0 ∨ ∑' i : u, ENNReal.ofReal (diam (V i)) ^ s = ∞) :=
  hausdorff_vitali_closed hs t V ht (fun i hi => (hV i hi).isClosed) hVd hfine

end GeometricMeasureTheory
