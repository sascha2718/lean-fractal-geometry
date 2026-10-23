/-
# Section 2.4: Frostman's lemma for compact sets

Frostman's lemma for compact subsets of a finite-dimensional real normed space, which includes
`ℝ^d` with its Euclidean norm, and the resulting description of Hausdorff dimension by measures.

| Notes | Lean declaration | Location |
|---|---|---|
| Theorem 2.26 (Frostman's lemma for compact sets) | `frostman_compact`, `frostman_compact_iff` | here |
| Corollary 2.27 (dimension through Frostman measures) | `frostman_dimension` | here |

The proof transports the problem to `Fin d → ℝ` with the sup norm by a bi-Lipschitz map
(`frostman_of_biLipschitz`). The dyadic masses are built by the recursion
`c(Q) = min {ℓ(Q)^s, ∑ c(children)}` from the proof of Lemma 2.25, carried out directly on
measures, and a weak limit is taken with `weak_compactness`.
-/
import GeometricMeasureTheory.Hausdorff.Computing
import GeometricMeasureTheory.Hausdorff.FlowsAndCuts
import GeometricMeasureTheory.Hausdorff.CoveringConventions

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

/-! ## Measures on the dyadic tree -/

/-- The indices of the `2^d` dyadic children of the cube with index `z`. -/
private def dyadicChildren {d : ℕ} (z : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i => {2 * z i, 2 * z i + 1}

private theorem mem_dyadicChildren {d : ℕ} {z w : Fin d → ℤ} :
    w ∈ dyadicChildren z ↔ ∀ i, w i = 2 * z i ∨ w i = 2 * z i + 1 := by
  simp [dyadicChildren, Fintype.mem_piFinset]

section TreeMeasure

variable {X : Type*} [MeasurableSpace X] {d : ℕ} (idx : ℕ → X → Fin d → ℤ) (a : ℕ → ℝ≥0∞)

open Classical in
/-- The measure on the dyadic tree of depth `j` below the cube `{y | idx k y = z}`, with
capacity `a k` at level `k`: a point mass of weight `a k` at the leaves, and at an inner cube the
sum of the children's measures, scaled down so that the mass is `min (a k) (children's mass)`. -/
private def treeMeasure : ℕ → ℕ → (Fin d → ℤ) → Measure X
  | 0, k, z => if h : ∃ y, idx k y = z then a k • Measure.dirac h.choose else 0
  | j + 1, k, z =>
    (min (a k) ((∑ w ∈ dyadicChildren z, treeMeasure j (k + 1) w) univ) /
      (∑ w ∈ dyadicChildren z, treeMeasure j (k + 1) w) univ) •
      ∑ w ∈ dyadicChildren z, treeMeasure j (k + 1) w

variable {idx a}

/-- The mass of a tree measure is at most the capacity of its root. -/
private theorem treeMeasure_univ_le (j k : ℕ) (z : Fin d → ℤ) :
    treeMeasure idx a j k z univ ≤ a k := by
  induction j generalizing k z with
  | zero =>
    simp only [treeMeasure]
    split_ifs with h
    · simp
    · simp
  | succ j ih =>
    simp only [treeMeasure, Measure.smul_apply, smul_eq_mul]
    set S := (∑ w ∈ dyadicChildren z, treeMeasure idx a j (k + 1) w) univ
    calc min (a k) S / S * S = S * (min (a k) S / S) := mul_comm _ _
      _ ≤ min (a k) S := ENNReal.mul_div_le
      _ ≤ a k := min_le_left _ _

/-- A tree measure is supported on its root cube. -/
private theorem treeMeasure_compl_eq_zero [MeasurableSingletonClass X]
    (hch : ∀ k y z w, w ∈ dyadicChildren z → idx (k + 1) y = w → idx k y = z)
    (j k : ℕ) (z : Fin d → ℤ) : treeMeasure idx a j k z {y | idx k y = z}ᶜ = 0 := by
  induction j generalizing k z with
  | zero =>
    simp only [treeMeasure]
    split_ifs with h
    · simp [Measure.dirac_apply, h.choose_spec]
    · simp
  | succ j ih =>
    simp only [treeMeasure, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun w hw => ?_)
    refine measure_mono_null (fun y hy => ?_) (ih (k + 1) w)
    exact fun h => hy (hch k y z w hw h)

/-- A tree measure gives every cube of the tree at most its capacity. -/
private theorem treeMeasure_le [MeasurableSingletonClass X]
    (hch : ∀ k y z w, w ∈ dyadicChildren z → idx (k + 1) y = w → idx k y = z)
    (hnest : ∀ k m y y', idx (k + m) y = idx (k + m) y' → idx k y = idx k y')
    (j k : ℕ) (z : Fin d → ℤ) (m : ℕ) (hm : m ≤ j) (w : Fin d → ℤ) :
    treeMeasure idx a j k z {y | idx (k + m) y = w} ≤ a (k + m) := by
  induction j generalizing k z m with
  | zero =>
    obtain rfl : m = 0 := by omega
    exact (measure_mono (subset_univ _)).trans (treeMeasure_univ_le _ _ _)
  | succ j ih =>
    rcases m with _ | m
    · exact (measure_mono (subset_univ _)).trans (treeMeasure_univ_le _ _ _)
    have e : k + (m + 1) = k + 1 + m := by omega
    rw [e]
    simp only [treeMeasure, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
    set S := ∑ w ∈ dyadicChildren z, treeMeasure idx a j (k + 1) w univ
    have ht : min (a k) S / S ≤ 1 := ENNReal.div_le_of_le_mul (by simp)
    have key : ∑ w' ∈ dyadicChildren z,
        treeMeasure idx a j (k + 1) w' {y | idx (k + 1 + m) y = w} ≤ a (k + 1 + m) := by
      by_cases hT : ∃ y₀, idx (k + 1 + m) y₀ = w
      · obtain ⟨y₀, hy₀⟩ := hT
        classical
        calc ∑ w' ∈ dyadicChildren z,
              treeMeasure idx a j (k + 1) w' {y | idx (k + 1 + m) y = w}
            ≤ ∑ w' ∈ dyadicChildren z,
                if w' = idx (k + 1) y₀ then a (k + 1 + m) else 0 := by
              refine Finset.sum_le_sum fun w' _ => ?_
              split_ifs with hw'
              · subst hw'
                exact ih (k + 1) _ m (by omega)
              · refine le_of_eq (measure_mono_null (fun y hy => ?_)
                  (treeMeasure_compl_eq_zero hch j (k + 1) w'))
                intro hy'
                apply hw'
                rw [← hy', hnest (k + 1) m y y₀ (hy.trans hy₀.symm)]
          _ ≤ a (k + 1 + m) := by
              rw [Finset.sum_ite_eq']
              split_ifs <;> simp
      · have : {y | idx (k + 1 + m) y = w} = ∅ := by
          ext y; simpa using fun h => hT ⟨y, h⟩
        simp [this]
    exact (mul_le_mul' ht key).trans (one_mul _).le

/-- A function bounded by the capacities and subadditive along the tree, vanishing on empty
cubes, is bounded by the mass of the tree measure. -/
private theorem le_treeMeasure_univ (ha : ∀ k, a k ≠ ∞) (F : ℕ → (Fin d → ℤ) → ℝ≥0∞)
    (hFa : ∀ k z, F k z ≤ a k) (hFch : ∀ k z, F k z ≤ ∑ w ∈ dyadicChildren z, F (k + 1) w)
    (hF0 : ∀ k z, (¬∃ y, idx k y = z) → F k z = 0) (j k : ℕ) (z : Fin d → ℤ) :
    F k z ≤ treeMeasure idx a j k z univ := by
  induction j generalizing k z with
  | zero =>
    simp only [treeMeasure]
    split_ifs with h
    · simpa using hFa k z
    · simp [hF0 k z h]
  | succ j ih =>
    simp only [treeMeasure, Measure.smul_apply, smul_eq_mul]
    set S := (∑ w ∈ dyadicChildren z, treeMeasure idx a j (k + 1) w) univ with hS
    rw [Measure.finsetSum_apply] at hS
    have hSne : S ≠ ∞ := by
      refine ne_top_of_le_ne_top
        (ENNReal.sum_ne_top.2 fun w (_ : w ∈ dyadicChildren z) => ha (k + 1)) ?_
      rw [hS]
      exact Finset.sum_le_sum fun w _ => treeMeasure_univ_le _ _ _
    have hF : F k z ≤ min (a k) S := by
      refine le_min (hFa k z) ((hFch k z).trans ?_)
      rw [hS]
      exact Finset.sum_le_sum fun w _ => ih (k + 1) w
    by_cases hS0 : S = 0
    · rw [hS0] at hF
      simp [nonpos_iff_eq_zero.1 (hF.trans (min_le_right _ _))]
    · rwa [ENNReal.div_mul_cancel hS0 hSne]

end TreeMeasure

/-! ## Dyadic cubes -/

/-- `⌊u⌋ = c` exactly when `⌊2u⌋` is `2c` or `2c + 1`. -/
private theorem floor_eq_iff_floor_two_mul (u : ℝ) (c : ℤ) :
    ⌊u⌋ = c ↔ ⌊2 * u⌋ = 2 * c ∨ ⌊2 * u⌋ = 2 * c + 1 := by
  simp only [Int.floor_eq_iff]
  push_cast
  constructor
  · rintro ⟨h1, h2⟩
    by_cases h : u < c + 1 / 2
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨by linarith, by linarith⟩

section DyadicIndex

variable {X : Type*} {d : ℕ}

/-- The index of the dyadic cube of level `k` containing `f y`, for the grid with corner `p` and
side length `L` at level zero. -/
private def dyadicIndex (f : X → Fin d → ℝ) (p : Fin d → ℝ) (L : ℝ) (k : ℕ) (y : X) :
    Fin d → ℤ :=
  fun i => ⌊(f y i - p i) * 2 ^ k / L⌋

variable {f : X → Fin d → ℝ} {p : Fin d → ℝ} {L : ℝ}

/-- The cube of level `k + 1` containing a point is a child of the cube of level `k`. -/
private theorem dyadicIndex_succ_mem (k : ℕ) (y : X) :
    dyadicIndex f p L (k + 1) y ∈ dyadicChildren (dyadicIndex f p L k y) := by
  refine mem_dyadicChildren.2 fun i => ?_
  have e : (f y i - p i) * 2 ^ (k + 1) / L = 2 * ((f y i - p i) * 2 ^ k / L) := by ring
  simp only [dyadicIndex, e]
  exact (floor_eq_iff_floor_two_mul _ _).1 rfl

/-- A child cube lies in its parent. -/
private theorem dyadicIndex_of_succ {k : ℕ} {y : X} {z w : Fin d → ℤ}
    (hw : w ∈ dyadicChildren z) (h : dyadicIndex f p L (k + 1) y = w) :
    dyadicIndex f p L k y = z := by
  funext i
  have e : (f y i - p i) * 2 ^ (k + 1) / L = 2 * ((f y i - p i) * 2 ^ k / L) := by ring
  refine (floor_eq_iff_floor_two_mul _ _).2 ?_
  have := congrFun h i
  simp only [dyadicIndex, e] at this
  rw [this]
  exact mem_dyadicChildren.1 hw i

/-- Dyadic cubes are nested. -/
private theorem dyadicIndex_nest (k m : ℕ) (y y' : X)
    (h : dyadicIndex f p L (k + m) y = dyadicIndex f p L (k + m) y') :
    dyadicIndex f p L k y = dyadicIndex f p L k y' := by
  induction m with
  | zero => exact h
  | succ m ih => exact ih (dyadicIndex_of_succ (dyadicIndex_succ_mem (k + m) y') h)

/-- A cube of level `k` has diameter at most `B L 2^{-k}`. -/
private theorem dist_le_of_dyadicIndex_eq [PseudoMetricSpace X] {B : ℝ} (hB0 : 0 ≤ B)
    (hL : 0 < L) (hB : ∀ y y', dist y y' ≤ B * dist (f y) (f y')) {k : ℕ} {y y' : X}
    (h : dyadicIndex f p L k y = dyadicIndex f p L k y') : dist y y' ≤ B * (L / 2 ^ k) := by
  refine (hB y y').trans (mul_le_mul_of_nonneg_left ((dist_pi_le_iff (by positivity)).2
    fun i => ?_) hB0)
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor (congrFun h i)
  rw [show (f y i - p i) * 2 ^ k / L - (f y' i - p i) * 2 ^ k / L =
    (f y i - f y' i) * (2 ^ k / L) by ring, abs_mul, abs_of_pos (div_pos (pow_pos two_pos k) hL),
    ← lt_div_iff₀ (div_pos (pow_pos two_pos k) hL), one_div_div] at h1
  rw [Real.dist_eq]
  exact h1.le

/-- Points whose images are closer than `L 2^{-k}` lie in adjacent cubes of level `k`. -/
private theorem dyadicIndex_mem_Icc [PseudoMetricSpace X] (hL : 0 < L) {k : ℕ} {y x : X}
    (h : dist (f y) (f x) < L / 2 ^ k) :
    dyadicIndex f p L k y ∈
      Finset.Icc (dyadicIndex f p L k x - 1) (dyadicIndex f p L k x + 1) := by
  have key : ∀ i, |(f y i - p i) * 2 ^ k / L - (f x i - p i) * 2 ^ k / L| < 1 := by
    intro i
    rw [show (f y i - p i) * 2 ^ k / L - (f x i - p i) * 2 ^ k / L =
      (f y i - f x i) * (2 ^ k / L) by ring, abs_mul,
      abs_of_pos (div_pos (pow_pos two_pos k) hL),
      ← lt_div_iff₀ (div_pos (pow_pos two_pos k) hL), one_div_div]
    exact (Real.dist_eq _ _ ▸ dist_le_pi_dist (f y) (f x) i).trans_lt h
  simp only [Finset.mem_Icc, Pi.le_def, Pi.sub_apply, Pi.add_apply, Pi.one_apply, dyadicIndex]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · rw [← Int.floor_sub_one]
    exact Int.floor_mono (by linarith [(abs_sub_lt_iff.1 (key i)).2])
  · rw [← Int.floor_add_one]
    exact Int.floor_mono (by linarith [(abs_sub_lt_iff.1 (key i)).1])

/-- There are `3^d` cubes adjacent to a given one. -/
private theorem card_Icc_dyadic (c : Fin d → ℤ) : (Finset.Icc (c - 1) (c + 1)).card = 3 ^ d := by
  rw [Pi.card_Icc]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.one_apply, Int.card_Icc]
  rw [Finset.prod_congr rfl fun i _ => show (c i + 1 + 1 - (c i - 1)).toNat = 3 by omega]
  simp

/-- The points of the cube `p + [0, L)^d` lie in the cube of level zero with index zero. -/
private theorem dyadicIndex_zero (hL : 0 < L) {y : X} (h : ∀ i, p i ≤ f y i ∧ f y i < p i + L) :
    dyadicIndex f p L 0 y = 0 := by
  funext i
  simp only [dyadicIndex, pow_zero, mul_one, Pi.zero_apply, Int.floor_eq_zero_iff, mem_Ico]
  exact ⟨div_nonneg (by linarith [(h i).1]) hL.le, (div_lt_one hL).2 (by linarith [(h i).2])⟩

end DyadicIndex

/-! ## Frostman's lemma through a bi-Lipschitz map -/

section Construction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {d : ℕ}

/-- The dyadic masses: measures on a compact set `K` with uniformly bounded mass at least
`𝓗^s_∞(K)`, satisfying the ball bound for all large indices. -/
private theorem exists_frostman_sequence {f : X → Fin d → ℝ} {A B : ℝ} (hA0 : 0 < A)
    (hB0 : 0 < B) (hA : ∀ y y', dist (f y) (f y') ≤ A * dist y y')
    (hB : ∀ y y', dist y y' ≤ B * dist (f y) (f y')) {s : ℝ} (hs : 0 < s) {K : Set X}
    (hK : IsCompact K) :
    ∃ (μ : ℕ → Measure K) (b : ℝ≥0∞), b ≠ ∞ ∧ (∀ n, μ n univ ≤ b) ∧
      (∀ n, hausdorffContent s K ≤ μ n univ) ∧
      ∀ x : X, ∀ r : ℝ, 0 < r → ∃ N, ∀ n ≥ N,
        μ n (Subtype.val ⁻¹' ball x r) ≤ 3 ^ d * ENNReal.ofReal (2 * A * B * r) ^ s := by
  have hfc : Continuous f := (LipschitzWith.of_dist_le_mul (K := Real.toNNReal A) fun y y' => by
    rw [Real.coe_toNNReal _ hA0.le]; exact hA y y').continuous
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 (hK.image hfc).isBounded
  set L : ℝ := 2 * (|R| + 1) with hLdef
  have hL : 0 < L := by positivity
  set p : Fin d → ℝ := fun _ => -(|R| + 1) with hp
  have hbox : ∀ y ∈ K, ∀ i, p i ≤ f y i ∧ f y i < p i + L := by
    intro y hy i
    have h1 : |f y i| ≤ |R| := ((Real.norm_eq_abs (f y i) ▸ norm_le_pi_norm (f y) i).trans
      (hR _ ⟨y, hy, rfl⟩)).trans (le_abs_self R)
    have h2 := abs_le.1 h1
    simp only [hp, hLdef]
    constructor <;> linarith [h2.1, h2.2]
  set idx : ℕ → K → Fin d → ℤ := fun k y => dyadicIndex f p L k (y : X) with hidx
  set a : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (B * (L / 2 ^ k)) ^ s with ha_def
  have ha : ∀ k, a k ≠ ∞ := fun k => ENNReal.rpow_ne_top_of_nonneg hs.le ENNReal.ofReal_ne_top
  have hch : ∀ k (y : K) z w, w ∈ dyadicChildren z → idx (k + 1) y = w → idx k y = z :=
    fun k y z w hw h => dyadicIndex_of_succ hw h
  have hnest : ∀ k m (y y' : K), idx (k + m) y = idx (k + m) y' → idx k y = idx k y' :=
    fun k m y y' h => dyadicIndex_nest k m (y : X) y' h
  refine ⟨fun n => treeMeasure idx a n 0 0, a 0, ha 0, fun n => treeMeasure_univ_le _ _ _,
    fun n => ?_, ?_⟩
  · have hF := le_treeMeasure_univ (idx := idx) ha
      (fun k z => hausdorffContent s ((↑) '' {y : K | idx k y = z} : Set X)) ?_ ?_ ?_ n 0 0
    · have : {y : K | idx 0 y = 0} = univ :=
        eq_univ_of_forall fun y => dyadicIndex_zero hL (hbox y y.2)
      simpa [this] using hF
    · intro k z
      refine (hausdorffContent_le_ediam_rpow hs.le _).trans
        (ENNReal.rpow_le_rpow (ediam_le ?_) hs.le)
      rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal
        (dist_le_of_dyadicIndex_eq hB0.le hL hB (hy.trans hy'.symm))
    · intro k z
      have hsub : ((↑) '' {y : K | idx k y = z} : Set X) ⊆
          ⋃ w ∈ dyadicChildren z, ((↑) '' {y : K | idx (k + 1) y = w}) := by
        rintro _ ⟨y, hy, rfl⟩
        exact mem_biUnion (hy ▸ dyadicIndex_succ_mem k (y : X)) ⟨y, rfl, rfl⟩
      have h1 := measure_mono (μ := hausdorffContentOuter (X := X) s) hsub
      have h2 := measure_biUnion_finset_le (μ := hausdorffContentOuter (X := X) s)
        (dyadicChildren z) fun w => ((↑) '' {y : K | idx (k + 1) y = w} : Set X)
      simp only [coe_hausdorffContentOuter] at h1 h2
      exact h1.trans h2
    · intro k z hz
      have : {y : K | idx k y = z} = ∅ := eq_empty_of_forall_notMem fun y hy => hz ⟨y, hy⟩
      rw [this, image_empty]
      exact measure_empty (μ := hausdorffContentOuter (X := X) s)
  · intro x r hr
    have hball_sub : ∀ k, A * r ≤ L / 2 ^ k → Subtype.val ⁻¹' ball x r ⊆
        ⋃ w ∈ Finset.Icc (dyadicIndex f p L k x - 1) (dyadicIndex f p L k x + 1),
          {y : K | idx k y = w} := by
      intro k hk y hy
      refine mem_biUnion (dyadicIndex_mem_Icc hL ?_) rfl
      calc dist (f y) (f x) ≤ A * dist (y : X) x := hA _ _
        _ < A * r := mul_lt_mul_of_pos_left (mem_ball.1 hy) hA0
        _ ≤ L / 2 ^ k := hk
    have hbound : ∀ k n, k ≤ n → A * r ≤ L / 2 ^ k →
        treeMeasure idx a n 0 0 (Subtype.val ⁻¹' ball x r) ≤ 3 ^ d * a k := by
      intro k n hkn hk
      calc _ ≤ treeMeasure idx a n 0 0 (⋃ w ∈ Finset.Icc (dyadicIndex f p L k x - 1)
              (dyadicIndex f p L k x + 1), {y : K | idx k y = w}) :=
            measure_mono (hball_sub k hk)
        _ ≤ ∑ w ∈ Finset.Icc (dyadicIndex f p L k x - 1) (dyadicIndex f p L k x + 1),
              treeMeasure idx a n 0 0 {y : K | idx k y = w} := measure_biUnion_finset_le _ _
        _ ≤ ∑ w ∈ Finset.Icc (dyadicIndex f p L k x - 1) (dyadicIndex f p L k x + 1), a k :=
            Finset.sum_le_sum fun w _ => by
              simpa only [zero_add] using treeMeasure_le hch hnest n 0 0 k hkn w
        _ = 3 ^ d * a k := by
            rw [Finset.sum_const, card_Icc_dyadic, nsmul_eq_mul]
            norm_cast
    by_cases hAr : A * r ≤ L
    · obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near (x := L / (A * r)) (y := (2 : ℝ))
        ((one_le_div (by positivity)).2 hAr) one_lt_two
      rw [le_div_iff₀ (by positivity)] at hk1
      rw [div_lt_iff₀ (by positivity)] at hk2
      refine ⟨k, fun n hn => (hbound k n hn ?_).trans ?_⟩
      · rw [le_div_iff₀ (by positivity)]
        linarith
      · have h3 : L / 2 ^ k < 2 * A * r := by
          rw [div_lt_iff₀ (by positivity)]
          rw [pow_succ] at hk2
          linarith
        refine mul_le_mul_right (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hs.le) _
        nlinarith
    · refine ⟨0, fun n _ => ?_⟩
      replace hAr := not_le.1 hAr
      calc _ ≤ treeMeasure idx a n 0 0 univ := measure_mono (subset_univ _)
        _ ≤ a 0 := treeMeasure_univ_le _ _ _
        _ ≤ ENNReal.ofReal (2 * A * B * r) ^ s := by
            refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hs.le
            simp only [pow_zero, div_one]
            nlinarith
        _ ≤ 3 ^ d * ENNReal.ofReal (2 * A * B * r) ^ s :=
            le_mul_of_one_le_left zero_le (one_le_pow₀ (by norm_num))

/-- A weak limit of finite measures with bounded masses on a compact metric space keeps a lower
bound on the mass and every eventual upper bound on an open set. -/
private theorem exists_weak_limit {Y : Type*} [MetricSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (μ : ℕ → Measure Y) {M b : ℝ≥0∞} (hb : b ≠ ∞)
    (hmass : ∀ n, μ n univ ≤ b) (hM : ∀ n, M ≤ μ n univ) :
    ∃ ν : Measure Y, IsFiniteMeasure ν ∧ M ≤ ν univ ∧
      ∀ U : Set Y, IsOpen U → ∀ c : ℝ≥0∞, (∃ N, ∀ n ≥ N, μ n U ≤ c) → ν U ≤ c := by
  have hfin : ∀ n, IsFiniteMeasure (μ n) := fun n => ⟨(hmass n).trans_lt hb.lt_top⟩
  set μF : ℕ → FiniteMeasure Y := fun n => ⟨μ n, hfin n⟩ with hμF
  have hbd : ∃ C : ℝ≥0, ∀ n, (μF n).mass ≤ C := by
    refine ⟨b.toNNReal, fun n => ?_⟩
    rw [← ENNReal.coe_le_coe, FiniteMeasure.ennreal_mass, ENNReal.coe_toNNReal hb]
    exact hmass n
  obtain ⟨φ, ν, hφ, hlim, hmasslim⟩ := weak_compactness μF hbd
  refine ⟨ν, inferInstance, ?_, fun U hU c ⟨N, hN⟩ => ?_⟩
  · rw [← FiniteMeasure.ennreal_mass]
    refine ge_of_tendsto' (ENNReal.tendsto_coe.2 hmasslim) fun k => ?_
    rw [FiniteMeasure.ennreal_mass]
    exact hM _
  · refine (le_liminf_measure_open_of_tendsto hlim hU).trans
      (liminf_le_of_frequently_le' (Eventually.frequently ?_))
    exact eventually_atTop.2 ⟨N, fun n hn => hN (φ n) (hn.trans (hφ.id_le n))⟩

/-- Frostman's lemma for a compact set in a metric space with a bi-Lipschitz map into
`Fin d → ℝ`, with the explicit constant `3^d (2AB)^s`. -/
theorem frostman_of_biLipschitz {f : X → Fin d → ℝ} {A B : ℝ} (hA0 : 0 < A) (hB0 : 0 < B)
    (hA : ∀ y y', dist (f y) (f y') ≤ A * dist y y')
    (hB : ∀ y y', dist y y' ≤ B * dist (f y) (f y')) {s : ℝ} (hs : 0 < s) {K : Set X}
    (hK : IsCompact K) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ μ Kᶜ = 0 ∧
      (∀ x : X, ∀ r : ℝ, 0 < r →
        μ (ball x r) ≤ 3 ^ d * ENNReal.ofReal (2 * A * B) ^ s * ENNReal.ofReal r ^ s) ∧
      hausdorffContent s K ≤ μ K := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  obtain ⟨μ, b, hb, hmass, hM, hball⟩ := exists_frostman_sequence hA0 hB0 hA hB hs hK
  obtain ⟨ν, hν, hνM, hνU⟩ := exists_weak_limit μ hb hmass hM
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  refine ⟨Measure.map Subtype.val ν, inferInstance, ?_, fun x r hr => ?_, ?_⟩
  · rw [Measure.map_apply measurable_subtype_coe hKm.compl]
    simp
  · rw [Measure.map_apply measurable_subtype_coe measurableSet_ball, mul_assoc,
      ← ENNReal.mul_rpow_of_nonneg _ _ hs.le, ← ENNReal.ofReal_mul (by positivity)]
    exact hνU _ (isOpen_ball.preimage continuous_subtype_val) _ (hball x r hr)
  · rw [Measure.map_apply measurable_subtype_coe hKm]
    simpa using hνM

end Construction

/-! ## Theorem 2.26 and Corollary 2.27 -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Theorem 2.26 (Frostman's lemma for compact sets, `thm:frostman-compact`): there is a constant
`c > 0`, depending only on the space and on `s`, such that every compact set `K` carries a finite
Borel measure `μ` with `μ(B(x, r)) ≤ r^s` for all `x` and `r > 0` and `μ(K) ≥ c 𝓗^s_∞(K)`. -/
theorem frostman_compact {s : ℝ} (hs : 0 < s) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ K : Set E, IsCompact K →
      ∃ μ : Measure E, IsFiniteMeasure μ ∧ μ Kᶜ = 0 ∧
        (∀ x : E, ∀ r : ℝ, 0 < r → μ (ball x r) ≤ ENNReal.ofReal r ^ s) ∧
        (c : ℝ≥0∞) * hausdorffContent s K ≤ μ K := by
  set d := Module.finrank ℝ E
  let φ : E ≃L[ℝ] (Fin d → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  set A : ℝ := ‖(φ : E →L[ℝ] (Fin d → ℝ))‖ + 1 with hAdef
  set B : ℝ := ‖(φ.symm : (Fin d → ℝ) →L[ℝ] E)‖ + 1 with hBdef
  have hA0 : 0 < A := by positivity
  have hB0 : 0 < B := by positivity
  have hA : ∀ y y' : E, dist (φ y) (φ y') ≤ A * dist y y' := by
    intro y y'
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact ((φ : E →L[ℝ] (Fin d → ℝ)).le_opNorm (y - y')).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg _))
  have hB : ∀ y y' : E, dist y y' ≤ B * dist (φ y) (φ y') := by
    intro y y'
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    calc ‖y - y'‖ = ‖(φ.symm : (Fin d → ℝ) →L[ℝ] E) (φ (y - y'))‖ := by simp
      _ ≤ ‖(φ.symm : (Fin d → ℝ) →L[ℝ] E)‖ * ‖φ (y - y')‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ B * ‖φ (y - y')‖ :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)
  set C₀ : ℝ≥0∞ := 3 ^ d * ENNReal.ofReal (2 * A * B) ^ s with hC₀
  have hC₀0 : C₀ ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num))
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 (by positivity)) ENNReal.ofReal_ne_top).ne'
  have hC₀top : C₀ ≠ ∞ := ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num))
    (ENNReal.rpow_ne_top_of_nonneg hs.le ENNReal.ofReal_ne_top)
  refine ⟨C₀⁻¹.toNNReal, ENNReal.toNNReal_pos (ENNReal.inv_ne_zero.2 hC₀top)
    (ENNReal.inv_ne_top.2 hC₀0), fun K hK => ?_⟩
  obtain ⟨μ, hμ, hμK, hball, hcont⟩ :=
    frostman_of_biLipschitz (f := fun y => φ y) hA0 hB0 hA hB hs hK
  rw [ENNReal.coe_toNNReal (ENNReal.inv_ne_top.2 hC₀0)]
  refine ⟨C₀⁻¹ • μ, ⟨?_⟩, by simp [hμK], fun x r hr => ?_, ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hC₀0)) (measure_lt_top _ _)
  · rw [Measure.smul_apply, smul_eq_mul]
    calc C₀⁻¹ * μ (ball x r) ≤ C₀⁻¹ * (C₀ * ENNReal.ofReal r ^ s) := by
          gcongr
          exact hball x r hr
      _ = ENNReal.ofReal r ^ s := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hC₀0 hC₀top, one_mul]
  · rw [Measure.smul_apply, smul_eq_mul]
    gcongr

/-- The final assertion of Theorem 2.26 (`thm:frostman-compact`): `𝓗^s(K) > 0` if and only if `K`
supports a non-zero finite Borel measure with `μ(B(x, r)) ≤ C r^s`. -/
theorem frostman_compact_iff {K : Set E} (hK : IsCompact K) {s : ℝ} (hs : 0 < s) :
    0 < μH[s] K ↔ ∃ μ : Measure E, IsFiniteMeasure μ ∧ μ Kᶜ = 0 ∧ μ ≠ 0 ∧
      ∃ C : ℝ≥0, ∀ x : E, ∀ r : ℝ, 0 < r → μ (ball x r) ≤ C * ENNReal.ofReal r ^ s := by
  constructor
  · intro hpos
    have hcont : hausdorffContent s K ≠ 0 := fun h => hpos.ne' ((same_null_sets hs.le K).2 h)
    obtain ⟨c, hc, hfr⟩ := frostman_compact (E := E) hs
    obtain ⟨μ, hμ, hμK, hball, hμc⟩ := hfr K hK
    refine ⟨μ, hμ, hμK, fun h0 => ?_, 1, fun x r hr => by simpa using hball x r hr⟩
    have h1 : (c : ℝ≥0∞) * hausdorffContent s K = 0 := by simpa [h0] using hμc
    exact mul_ne_zero (by exact_mod_cast hc.ne') hcont h1
  · rintro ⟨μ, hμ, hμK, hμ0, C, hball⟩
    have hC : (C + 1 : ℝ≥0) ≠ 0 := by positivity
    have hball' : ∀ x ∈ K, ∀ r : ℝ, 0 < r →
        μ (ball x r) ≤ ((C + 1 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal r ^ s := by
      intro x _ r hr
      refine (hball x r hr).trans ?_
      gcongr
      exact le_self_add
    have h1 := (mass_distribution μ hs hC hball').1
    have hμK' : μ K ≠ 0 := by
      have h := measure_add_measure_compl (μ := μ) hK.isClosed.measurableSet
      rw [hμK, add_zero] at h
      rw [h]
      exact Measure.measure_univ_ne_zero.2 hμ0
    have h2 : 0 < μ K / ((C + 1 : ℝ≥0) : ℝ≥0∞) :=
      ENNReal.div_pos_iff.2 ⟨hμK', ENNReal.coe_ne_top⟩
    refine pos_iff_ne_zero.2 fun h => ?_
    rw [same_null_sets hs.le] at h
    exact (h2.trans_le h1).ne' h

/-- Corollary 2.27 (`thm:frostman-dimension`): the Hausdorff dimension of a non-empty compact set is
the supremum of the exponents `s` for which it supports a probability measure with
`μ(B(x, r)) ≤ C r^s`. -/
theorem frostman_dimension {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) :
    dimH K = ⨆ (s : ℝ≥0) (_ : ∃ μ : Measure E, IsProbabilityMeasure μ ∧ μ Kᶜ = 0 ∧
      ∃ C : ℝ≥0, ∀ x : E, ∀ r : ℝ, 0 < r → μ (ball x r) ≤ C * ENNReal.ofReal r ^ (s : ℝ)),
      (s : ℝ≥0∞) := by
  -- Non-emptiness is not needed: for `K = ∅` both sides vanish.
  obtain ⟨-, -⟩ := hne
  refine le_antisymm (le_of_forall_lt fun t ht => ?_)
    (iSup₂_le fun s ⟨μ, hμ, hμK, C, hball⟩ => ?_)
  · obtain ⟨s, hts, hs⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    have hs0 : 0 < (s : ℝ) := by
      have : (0 : ℝ≥0∞) < s := zero_le.trans_lt hts
      exact_mod_cast this
    have hinf : μH[s] K = ∞ := hausdorffMeasure_of_lt_dimH hs
    obtain ⟨μ, hμ, hμK, hμ0, C, hball⟩ :=
      (frostman_compact_iff hK hs0).1 (by rw [hinf]; exact ENNReal.zero_lt_top)
    have hne' : (μ univ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (Measure.measure_univ_ne_zero.2 hμ0)
    refine hts.trans_le (le_iSup₂_of_le s ⟨(μ univ)⁻¹ • μ, ⟨?_⟩, by simp [hμK],
      (μ univ)⁻¹.toNNReal * C, fun x r hr => ?_⟩ le_rfl)
    · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel
        (Measure.measure_univ_ne_zero.2 hμ0) (measure_ne_top μ univ)]
    · rw [Measure.smul_apply, smul_eq_mul, ENNReal.coe_mul, ENNReal.coe_toNNReal hne', mul_assoc]
      gcongr
      exact hball x r hr
  · rcases eq_or_ne s 0 with rfl | hs0
    · simp
    have hs : 0 < (s : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hs0)
    have hC : (C + 1 : ℝ≥0) ≠ 0 := by positivity
    have hball' : ∀ x ∈ K, ∀ r : ℝ, 0 < r →
        μ (ball x r) ≤ ((C + 1 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal r ^ (s : ℝ) := by
      intro x _ r hr
      refine (hball x r hr).trans ?_
      gcongr
      exact le_self_add
    have hμK1 : μ K = 1 := (prob_compl_eq_zero_iff hK.isClosed.measurableSet).1 hμK
    have := (mass_distribution μ hs hC hball').2 (by rw [hμK1]; exact one_pos)
    simpa using this

end GeometricMeasureTheory
