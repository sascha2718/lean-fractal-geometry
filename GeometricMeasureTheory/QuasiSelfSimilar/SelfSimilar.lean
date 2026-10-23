/-
# Section 8.2.1: Self-similar sets

A self-similar set is a nonempty compact set invariant under finitely many contracting
similarities. At its Hausdorff dimension its Hausdorff measure and Hausdorff content agree, and so
therefore do the measure and content of each of its subsets.

| Notes | Lean declaration | Location |
|---|---|---|
| Self-similar set, similarity dimension | `IsSelfSimilarSet`, `similarityDim` | here |
| Exercise 7.1 (uniqueness of the similarity dimension) | `existsUnique_similarityDim`, `sum_rpow_similarityDim`, `similarityDim_eq_of_sum_rpow_eq_one` | here |
| Proposition 8.4 (measure equals content) | `self_similar_measure_content` | here |
| Attractors of iterated function systems | `ContractingWith.fixedPoint` on `TopologicalSpace.NonemptyCompacts` | `Mathlib/Topology/MetricSpace/Contracting.lean` |
| Hutchinson's theorem and the similarity dimension for affine systems of the line | `FractalGeometry.System`, `System.exists_unique_isNatural`, `System.IsDimension`, `System.StronglySeparated`, `attractorSet_eq_iUnion` | the `FractalGeometry` library |
-/
import GeometricMeasureTheory.QuasiSelfSimilar.CompactVitali

open MeasureTheory Filter Topology Set Metric

open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A self-similar set: a nonempty compact set invariant under a finite family of contracting
similarities with ratios `c i`. -/
def IsSelfSimilarSet {ι : Type*} [Fintype ι] (F : ι → X → X) (c : ι → ℝ) (E : Set X) : Prop :=
  E.Nonempty ∧ IsCompact E ∧ (∀ i, c i ∈ Ioo (0 : ℝ) 1) ∧
    (∀ i, ∀ x y, dist (F i x) (F i y) = c i * dist x y) ∧ E = ⋃ i, F i '' E

/-! ## Exercise 7.1 -/

/-- The sum `s ↦ ∑ cᵢ^s` is strictly decreasing when the ratios lie in `(0, 1)`. -/
private theorem strictAnti_sum_rpow {ι : Type*} [Fintype ι] [Nonempty ι] {c : ι → ℝ}
    (hc : ∀ i, c i ∈ Ioo (0 : ℝ) 1) : StrictAnti fun s : ℝ => ∑ i, c i ^ s := by
  intro a b hab
  exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ =>
    Real.rpow_lt_rpow_of_exponent_gt (hc i).1 (hc i).2 hab

/-- The sum `s ↦ ∑ cᵢ^s` is continuous. -/
private theorem continuous_sum_rpow {ι : Type*} [Fintype ι] {c : ι → ℝ}
    (hc : ∀ i, c i ∈ Ioo (0 : ℝ) 1) : Continuous fun s : ℝ => ∑ i, c i ^ s :=
  continuous_finsetSum _ fun i _ => Real.continuous_const_rpow (hc i).1.ne'

/-- Exercise 7.1: the similarity dimension, the unique solution of `∑ cᵢ^s = 1`, is well defined. -/
theorem existsUnique_similarityDim {ι : Type*} [Fintype ι] [Nonempty ι] {c : ι → ℝ}
    (hc : ∀ i, c i ∈ Ioo (0 : ℝ) 1) : ∃! s : ℝ, ∑ i, c i ^ s = 1 := by
  set f : ℝ → ℝ := fun s => ∑ i, c i ^ s with hf
  -- The sum tends to zero along `s → ∞`, so it drops below one.
  have hlim : Tendsto f atTop (𝓝 0) := by
    have : Tendsto (fun s : ℝ => ∑ i, c i ^ s) atTop (𝓝 (∑ _i : ι, (0 : ℝ))) :=
      tendsto_finsetSum _ fun i _ =>
        tendsto_rpow_atTop_of_base_lt_one _ (by linarith [(hc i).1]) (hc i).2
    simpa using this
  obtain ⟨b, hb⟩ :=
    ((hlim.eventually (eventually_lt_nhds one_pos)).and (eventually_ge_atTop 0)).exists
  -- At `s = 0` the sum is the cardinality, at least one.
  have hf0 : 1 ≤ f 0 := by
    simp only [hf, Real.rpow_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Finset.card_ne_zero_of_mem (Finset.mem_univ
      (Classical.arbitrary ι)))
  obtain ⟨s, -, hs⟩ := intermediate_value_Icc' hb.2 (continuous_sum_rpow hc).continuousOn
    ⟨hb.1.le, hf0⟩
  refine ⟨s, hs, fun t ht => (strictAnti_sum_rpow hc).injective (ht.trans hs.symm)⟩

/-- The similarity dimension of a family of contraction ratios. -/
def similarityDim {ι : Type*} [Fintype ι] (c : ι → ℝ) : ℝ :=
  sInf {s : ℝ | ∑ i, c i ^ s ≤ 1}

/-- The similarity dimension solves `∑ cᵢ^s = 1`. -/
theorem sum_rpow_similarityDim {ι : Type*} [Fintype ι] [Nonempty ι] {c : ι → ℝ}
    (hc : ∀ i, c i ∈ Ioo (0 : ℝ) 1) : ∑ i, c i ^ similarityDim c = 1 := by
  obtain ⟨t, ht, -⟩ := existsUnique_similarityDim hc
  have hset : {s : ℝ | ∑ i, c i ^ s ≤ 1} = Ici t := by
    ext s
    simp only [mem_setOf_eq, mem_Ici, ← ht]
    exact StrictAnti.le_iff_ge (strictAnti_sum_rpow hc)
  rw [similarityDim, hset, csInf_Ici, ht]

/-- The similarity dimension is the unique solution of `∑ cᵢ^s = 1`. -/
theorem similarityDim_eq_of_sum_rpow_eq_one {ι : Type*} [Fintype ι] [Nonempty ι] {c : ι → ℝ}
    (hc : ∀ i, c i ∈ Ioo (0 : ℝ) 1) {s : ℝ} (hs : ∑ i, c i ^ s = 1) : similarityDim c = s :=
  (strictAnti_sum_rpow hc).injective ((sum_rpow_similarityDim hc).trans hs.symm)

section Words

/-- The composition of the maps of a family along a word:
`wordMap F [i₁, …, i_k] = F i₁ ∘ ⋯ ∘ F i_k`. -/
private def wordMap {Y ι : Type*} (F : ι → Y → Y) : List ι → Y → Y
  | [] => id
  | i :: w => F i ∘ wordMap F w

/-- The product of the contraction ratios along a word. -/
private def wordRatio {ι : Type*} (c : ι → ℝ) : List ι → ℝ
  | [] => 1
  | i :: w => c i * wordRatio c w

/-- The empty word gives the identity map. -/
private theorem wordMap_nil {Y ι : Type*} (F : ι → Y → Y) : wordMap F ([] : List ι) = id := rfl

/-- The first letter of a word acts last. -/
private theorem wordMap_cons {Y ι : Type*} (F : ι → Y → Y) (i : ι) (w : List ι) :
    wordMap F (i :: w) = F i ∘ wordMap F w := rfl

/-- The empty word has ratio one. -/
private theorem wordRatio_nil {ι : Type*} (c : ι → ℝ) : wordRatio c ([] : List ι) = 1 := rfl

/-- The ratio of a word is the ratio of its first letter times the ratio of its tail. -/
private theorem wordRatio_cons {ι : Type*} (c : ι → ℝ) (i : ι) (w : List ι) :
    wordRatio c (i :: w) = c i * wordRatio c w := rfl

/-- Concatenation of words corresponds to composition of the maps. -/
private theorem wordMap_append {Y ι : Type*} (F : ι → Y → Y) (v w : List ι) :
    wordMap F (v ++ w) = wordMap F v ∘ wordMap F w := by
  induction v with
  | nil => rfl
  | cons i v ih => simp only [List.cons_append, wordMap_cons, ih, Function.comp_assoc]

/-- Words have positive ratios. -/
private theorem wordRatio_pos {ι : Type*} {c : ι → ℝ} (hc : ∀ i, 0 < c i) (w : List ι) :
    0 < wordRatio c w := by
  induction w with
  | nil => simp [wordRatio_nil]
  | cons i w ih => exact mul_pos (hc i) ih

/-- The ratio of a word is at most the largest letter ratio to the power of its length. -/
private theorem wordRatio_le_pow {ι : Type*} {c : ι → ℝ} {r : ℝ} (hc : ∀ i, 0 < c i)
    (hr : ∀ i, c i ≤ r) (w : List ι) : wordRatio c w ≤ r ^ w.length := by
  induction w with
  | nil => simp [wordRatio_nil]
  | cons i w ih =>
      have h0 : 0 ≤ r := (hc i).le.trans (hr i)
      calc wordRatio c (i :: w) = c i * wordRatio c w := rfl
        _ ≤ r * r ^ w.length :=
            mul_le_mul (hr i) ih (wordRatio_pos hc w).le h0
        _ = r ^ (i :: w).length := by rw [List.length_cons, pow_succ]; ring

/-- The maps of a word compose to a similarity of ratio the ratio of the word. -/
private theorem dist_wordMap {Y ι : Type*} [PseudoMetricSpace Y] {F : ι → Y → Y} {c : ι → ℝ}
    (hsim : ∀ i x y, dist (F i x) (F i y) = c i * dist x y) (w : List ι) (x y : Y) :
    dist (wordMap F w x) (wordMap F w y) = wordRatio c w * dist x y := by
  induction w with
  | nil => simp only [wordMap_nil, wordRatio_nil, id_eq, one_mul]
  | cons i w ih =>
      simp only [wordMap_cons, Function.comp_apply, wordRatio_cons, hsim, ih, mul_assoc]

/-- The similarity relation of a word in terms of the extended distance. -/
private theorem edist_wordMap {Y ι : Type*} [PseudoMetricSpace Y] {F : ι → Y → Y} {c : ι → ℝ}
    (hc : ∀ i, 0 < c i) (hsim : ∀ i x y, dist (F i x) (F i y) = c i * dist x y) (w : List ι)
    (x y : Y) :
    edist (wordMap F w x) (wordMap F w y) =
      (Real.toNNReal (wordRatio c w) : ℝ≥0∞) * edist x y := by
  rw [edist_dist, edist_dist, dist_wordMap hsim]
  exact ENNReal.ofReal_mul (wordRatio_pos hc w).le

/-- An invariant set is mapped into itself by the maps of every word. -/
private theorem wordMap_image_subset {Y ι : Type*} {F : ι → Y → Y} {E : Set Y}
    (hsub : ∀ i, F i '' E ⊆ E) (w : List ι) : wordMap F w '' E ⊆ E := by
  induction w with
  | nil => simp [wordMap_nil]
  | cons i w ih =>
      rw [wordMap_cons, image_comp]
      exact (image_mono ih).trans (hsub i)

/-- Every point of an invariant set lies in the image of some word of any prescribed length. -/
private theorem exists_word_mem {Y ι : Type*} {F : ι → Y → Y} {E : Set Y}
    (hinv : E = ⋃ i, F i '' E) (n : ℕ) {x : Y} (hx : x ∈ E) :
    ∃ w : List ι, w.length = n ∧ x ∈ wordMap F w '' E := by
  induction n generalizing x with
  | zero => exact ⟨[], rfl, by simpa [wordMap_nil] using hx⟩
  | succ n ih =>
      obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.1 (hinv ▸ hx)
      obtain ⟨w, hw, hyw⟩ := ih hy
      exact ⟨i :: w, by simp [hw], by
        rw [wordMap_cons, image_comp]; exact mem_image_of_mem _ hyw⟩

end Words

section LevelSum

variable {β : Type*} [Fintype β]

/-- The sum of `f` over all words of length `n` in the alphabet `β`. -/
private def levelSum (f : List β → ℝ) (n : ℕ) : ℝ :=
  match n with
  | 0 => f []
  | n + 1 => ∑ b : β, levelSum (fun w => f (b :: w)) n

/-- The level zero sum is the value at the empty word. -/
private theorem levelSum_zero (f : List β → ℝ) : levelSum f 0 = f [] := rfl

/-- Splitting the sum over a level according to the first letter. -/
private theorem levelSum_succ (f : List β → ℝ) (n : ℕ) :
    levelSum f (n + 1) = ∑ b : β, levelSum (fun w => f (b :: w)) n := rfl

/-- Level sums are monotone in the summand. -/
private theorem levelSum_mono {f g : List β → ℝ} {n : ℕ}
    (h : ∀ w : List β, w.length = n → f w ≤ g w) : levelSum f n ≤ levelSum g n := by
  induction n generalizing f g with
  | zero => exact h [] rfl
  | succ n ih =>
      refine Finset.sum_le_sum fun b _ => ih fun w hw => h (b :: w) ?_
      simp [hw]

/-- The level sum of the zero function vanishes. -/
private theorem levelSum_fun_zero (n : ℕ) : levelSum (fun _ : List β => (0 : ℝ)) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [levelSum_succ, ih]

/-- Constants factor out of a level sum. -/
private theorem levelSum_const_mul (a : ℝ) (f : List β → ℝ) (n : ℕ) :
    levelSum (fun w => a * f w) n = a * levelSum f n := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp [levelSum_succ, ih, Finset.mul_sum]

/-- A level sum of a finite sum is the finite sum of the level sums. -/
private theorem levelSum_finsetSum {κ : Type*} (J : Finset κ) (f : κ → List β → ℝ) (n : ℕ) :
    levelSum (fun w => ∑ j ∈ J, f j w) n = ∑ j ∈ J, levelSum (f j) n := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      simp only [levelSum_succ]
      rw [show (∑ b : β, levelSum (fun w => ∑ j ∈ J, f j (b :: w)) n)
          = ∑ b : β, ∑ j ∈ J, levelSum (fun w => f j (b :: w)) n from
        Finset.sum_congr rfl fun b _ => ih (fun j w => f j (b :: w))]
      exact Finset.sum_comm

/-- The level sum of the `t`-th powers of the word ratios is a power of `∑ ρ_b^t`. -/
private theorem levelSum_wordRatio_rpow {ρ : β → ℝ} (hρ : ∀ b, 0 < ρ b) (t : ℝ) (n : ℕ) :
    levelSum (fun w => wordRatio ρ w ^ t) n = (∑ b, ρ b ^ t) ^ n := by
  induction n with
  | zero => simp [levelSum_zero, wordRatio_nil, Real.one_rpow]
  | succ n ih =>
      rw [levelSum_succ, pow_succ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hfun : (fun w : List β => wordRatio ρ (b :: w) ^ t)
          = fun w : List β => ρ b ^ t * wordRatio ρ w ^ t := by
        funext w
        rw [wordRatio_cons, Real.mul_rpow (hρ b).le (wordRatio_pos hρ w).le]
      rw [hfun, levelSum_const_mul, ih]
      exact mul_comm _ _

variable [DecidableEq β]

/-- If `∑ ρ_b^t = 1`, the words of a level extending a fixed word `P` carry mass `ρ_P^t`. -/
private theorem levelSum_prefix {ρ : β → ℝ} (hρ : ∀ b, 0 < ρ b) {t : ℝ}
    (hsum : ∑ b, ρ b ^ t = 1) :
    ∀ (P : List β) (n : ℕ), P.length ≤ n →
      levelSum (fun w => if P <+: w then wordRatio ρ w ^ t else 0) n = wordRatio ρ P ^ t := by
  intro P
  induction P with
  | nil =>
      intro n _
      simp only [List.nil_prefix, if_true, wordRatio_nil, Real.one_rpow]
      rw [levelSum_wordRatio_rpow hρ, hsum, one_pow]
  | cons b P ih =>
      intro n hn
      match n with
      | 0 => simp at hn
      | m + 1 =>
        have hm : P.length ≤ m := by simpa using hn
        rw [levelSum_succ]
        refine (Finset.sum_eq_single_of_mem b (Finset.mem_univ b) ?_).trans ?_
        · intro b' _ hb'
          have hfun : (fun w : List β =>
              if b :: P <+: b' :: w then wordRatio ρ (b' :: w) ^ t else 0)
              = fun _ : List β => (0 : ℝ) := by
            funext w
            rw [if_neg]
            rintro ⟨u, hu⟩
            rw [List.cons_append] at hu
            obtain ⟨rfl, -⟩ := List.cons_eq_cons.1 hu
            exact hb' rfl
          rw [hfun, levelSum_fun_zero]
        · have hfun : (fun w : List β =>
              if b :: P <+: b :: w then wordRatio ρ (b :: w) ^ t else 0)
              = fun w : List β => ρ b ^ t * (if P <+: w then wordRatio ρ w ^ t else 0) := by
            funext w
            by_cases hw : P <+: w
            · rw [if_pos (List.cons_prefix_cons.2 ⟨rfl, hw⟩), if_pos hw, wordRatio_cons,
                Real.mul_rpow (hρ b).le (wordRatio_pos hρ w).le]
            · rw [if_neg fun h => hw (List.cons_prefix_cons.1 h).2, if_neg hw, mul_zero]
          rw [hfun, levelSum_const_mul, ih m hm, wordRatio_cons,
            Real.mul_rpow (hρ b).le (wordRatio_pos hρ P).le]

end LevelSum

section Separated

/-- Taking one letter more than a prefix of length `A.length`. -/
private theorem take_append_length_succ {β : Type*} (A : List β) (b : β) (v : List β) :
    (A ++ b :: v).take (A.length + 1) = A ++ [b] := by
  induction A with
  | nil => simp
  | cons a A ih => simpa using ih

omit [MeasurableSpace X] [BorelSpace X] in
/-- The weight of a bounded covering set dominates the `t`-th power of its diameter. -/
private theorem ofReal_diam_rpow_le_gaugeWeight {t : ℝ} (ht : 0 < t) {U : Set X}
    (hU : Bornology.IsBounded U) :
    ENNReal.ofReal (diam U ^ t) ≤ gaugeWeight (fun r : ℝ≥0∞ => r ^ t) U := by
  rcases U.eq_empty_or_nonempty with rfl | hne
  · simp [Real.zero_rpow ht.ne']
  · have hdd : ediam U = ENNReal.ofReal (diam U) := (ENNReal.ofReal_toReal hU.ediam_ne_top).symm
    rw [gaugeWeight_of_nonempty _ hne, hdd, ENNReal.ofReal_rpow_of_nonneg diam_nonneg ht.le]

omit [MeasurableSpace X] [BorelSpace X] in
/-- A compact set carrying a family of pairwise disjoint scaled copies of itself whose ratios
solve `∑ ρ_b^t = 1` has positive `t`-dimensional Hausdorff content. -/
private theorem hausdorffContent_ne_zero_of_separated {β : Type*} [Fintype β] [Nonempty β]
    {G : β → X → X} {ρ : β → ℝ} {E : Set X} (hcomp : IsCompact E) (hne : E.Nonempty)
    (hρ : ∀ b, ρ b ∈ Ioo (0 : ℝ) 1)
    (hsim : ∀ b x y, dist (G b x) (G b y) = ρ b * dist x y) (hsub : ∀ b, G b '' E ⊆ E)
    (hdisj : ∀ b b' : β, b ≠ b' → Disjoint (G b '' E) (G b' '' E))
    {t : ℝ} (ht : 0 < t) (hsum : ∑ b, ρ b ^ t = 1) : hausdorffContent t E ≠ 0 := by
  classical
  have hρ0 : ∀ b, 0 < ρ b := fun b => (hρ b).1
  have hcont : ∀ b, Continuous (G b) := fun b =>
    (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (ρ b)) fun x y => by
      rw [hsim, Real.coe_toNNReal _ (hρ0 b).le]).continuous
  have himgc : ∀ b, IsCompact (G b '' E) := fun b => hcomp.image (hcont b)
  have himgne : ∀ b, (G b '' E).Nonempty := fun b => hne.image _
  -- A uniform separation constant for the images.
  have hpair : ∀ b b' : β, ∃ e : ℝ, 0 < e ∧ (b ≠ b' →
      ∀ x ∈ G b '' E, ∀ y ∈ G b' '' E, e ≤ dist x y) := by
    intro b b'
    by_cases hbb : b = b'
    · exact ⟨1, one_pos, fun h => absurd hbb h⟩
    obtain ⟨x₀, hx₀, hmin⟩ := (himgc b).exists_isMinOn (himgne b)
      (Metric.continuous_infDist_pt (G b' '' E)).continuousOn
    refine ⟨Metric.infDist x₀ (G b' '' E), ?_, fun _ x hx y hy => ?_⟩
    · exact ((himgc b').isClosed.notMem_iff_infDist_pos (himgne b')).1
        (Set.disjoint_left.1 (hdisj b b' hbb) hx₀)
    · exact (isMinOn_iff.1 hmin x hx).trans (Metric.infDist_le_dist_of_mem hy)
  choose e he0 he using hpair
  set d : ℝ := Finset.univ.inf' Finset.univ_nonempty fun p : β × β => e p.1 p.2 with hd
  have hd0 : 0 < d := (Finset.lt_inf'_iff _).2 fun p _ => he0 p.1 p.2
  have hdle : ∀ b b' : β, b ≠ b' → ∀ x ∈ G b '' E, ∀ y ∈ G b' '' E, d ≤ dist x y :=
    fun b b' hbb x hx y hy =>
      (Finset.inf'_le _ (Finset.mem_univ (b, b'))).trans (he b b' hbb x hx y hy)
  obtain ⟨q, hqE⟩ := hne
  intro h0
  -- An open cover of total weight less than `d ^ t / 2`.
  have hlt : hausdorffContent t E < ENNReal.ofReal (d ^ t / 2) := by
    rw [h0]
    exact ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨U, hlt⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hUo, hlt⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hEU, hlt⟩ := iInf_lt_iff.1 hlt
  have hUbdd : ∀ j, Bornology.IsBounded (U j) := by
    intro j
    have hfin : gaugeWeight (fun r : ℝ≥0∞ => r ^ t) (U j) ≠ ⊤ :=
      ((ENNReal.le_tsum (f := fun i => gaugeWeight (fun r : ℝ≥0∞ => r ^ t) (U i)) j).trans_lt
        (hlt.trans ENNReal.ofReal_lt_top)).ne
    rcases (U j).eq_empty_or_nonempty with h | h
    · simp [h]
    · rw [Metric.isBounded_iff_ediam_ne_top]
      intro htop
      exact hfin (by rw [gaugeWeight_of_nonempty _ h, htop, ENNReal.top_rpow_of_pos ht])
  obtain ⟨J, hJ⟩ := hcomp.elim_finite_subcover U hUo hEU
  -- The largest ratio.
  obtain ⟨r, hr0, hr1, hrle⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ b, ρ b ≤ r :=
    ⟨Finset.univ.sup' Finset.univ_nonempty ρ,
      (Finset.lt_sup'_iff _).2 ⟨Classical.arbitrary β, Finset.mem_univ _, hρ0 _⟩,
      (Finset.sup'_lt_iff _).2 fun b _ => (hρ b).2,
      fun b => Finset.le_sup' ρ (Finset.mem_univ b)⟩
  have hpow : ∀ m : ℕ, (r ^ m) ^ t = (r ^ t) ^ m := fun m => by
    rw [← Real.rpow_natCast r m, ← Real.rpow_natCast (r ^ t) m, ← Real.rpow_mul hr0.le,
      ← Real.rpow_mul hr0.le, mul_comm]
  -- A level at which the individual cylinders are negligible.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (J.card : ℝ) * (r ^ t) ^ n < 1 / 2 := by
    have hrt1 : r ^ t < 1 := Real.rpow_lt_one hr0.le hr1 ht
    have hrt0 : 0 < r ^ t := Real.rpow_pos_of_pos hr0 t
    have hcard : (0 : ℝ) < 1 / (2 * (J.card + 1)) := by positivity
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hcard hrt1
    refine ⟨n, ?_⟩
    have hm : (0 : ℝ) ≤ J.card := Nat.cast_nonneg _
    calc (J.card : ℝ) * (r ^ t) ^ n ≤ (J.card : ℝ) * (1 / (2 * (J.card + 1))) := by gcongr
      _ < 1 / 2 := by
          rw [mul_one_div, div_lt_iff₀ (by positivity)]
          linarith
  -- Every word names a point of `E`, and every such point lies in a set of the finite subcover.
  have hzE : ∀ w : List β, wordMap G w q ∈ E := fun w =>
    wordMap_image_subset hsub w ⟨q, hqE, rfl⟩
  have hcov : ∀ w : List β, ∃ j, j ∈ J ∧ wordMap G w q ∈ U j := fun w => by
    simpa using hJ (hzE w)
  choose φ hφJ hφU using hcov
  -- The mass of the words assigned to a single covering set.
  have perj : ∀ j ∈ J, levelSum (fun w => if φ w = j then wordRatio ρ w ^ t else 0) n
      ≤ (diam (U j) / d) ^ t + (r ^ t) ^ n := by
    intro j _
    have hn1 : (0 : ℝ) ≤ (diam (U j) / d) ^ t := Real.rpow_nonneg (by positivity) t
    have hn2 : (0 : ℝ) ≤ (r ^ t) ^ n := by positivity
    by_cases hA : ∃ w : List β, w.length = n ∧ φ w = j
    swap
    · refine le_trans (le_of_le_of_eq (levelSum_mono
        (g := fun _ : List β => (0 : ℝ)) fun w hw => ?_) (levelSum_fun_zero n)) (by positivity)
      rw [if_neg fun h => hA ⟨w, hw, h⟩]
    obtain ⟨w₀, hw₀len, hw₀j⟩ := hA
    set Q : ℕ → Prop := fun k => ∀ w : List β, w.length = n → φ w = j → w.take k = w₀.take k
      with hQdef
    have hQ0 : Q 0 := by intro w _ _; simp
    have hQK : Q (Nat.findGreatest Q n) := Nat.findGreatest_spec (Nat.zero_le n) hQ0
    set K := Nat.findGreatest Q n with hKdef
    have hKn : K ≤ n := Nat.findGreatest_le n
    set P₀ := w₀.take K with hP₀def
    have hP₀len : P₀.length = K := by rw [hP₀def, List.length_take, hw₀len, min_eq_left hKn]
    -- All the words assigned to `j` lie in the cylinder of `P₀`.
    have h1 : levelSum (fun w => if φ w = j then wordRatio ρ w ^ t else 0) n
        ≤ wordRatio ρ P₀ ^ t := by
      refine le_trans (levelSum_mono
        (g := fun w => if P₀ <+: w then wordRatio ρ w ^ t else 0) fun w hw => ?_)
        (le_of_eq (levelSum_prefix hρ0 hsum P₀ n (by rw [hP₀len]; exact hKn)))
      by_cases hwj : φ w = j
      · have hpre : P₀ <+: w := by
          rw [hP₀def, ← hQK w hw hwj]
          exact List.take_prefix K w
        rw [if_pos hwj, if_pos hpre]
      · rw [if_neg hwj]
        by_cases hpre : P₀ <+: w
        · rw [if_pos hpre]
          exact Real.rpow_nonneg (wordRatio_pos hρ0 w).le t
        · rw [if_neg hpre]
    refine h1.trans ?_
    rcases lt_or_eq_of_le hKn with hKlt | hKeq
    · -- Two words assigned to `j` already separate at level `K`.
      have hnotQ : ¬ Q (K + 1) := Nat.findGreatest_is_greatest (n := n) (by omega) (by omega)
      obtain ⟨w₁, hw₁len, hw₁j, hw₁ne⟩ : ∃ w : List β, w.length = n ∧ φ w = j ∧
          w.take (K + 1) ≠ w₀.take (K + 1) := by
        by_contra hcon
        exact hnotQ fun w hw hj => by
          by_contra hne'
          exact hcon ⟨w, hw, hj, hne'⟩
      have hw₁K : w₁.take K = P₀ := hQK w₁ hw₁len hw₁j
      -- Decompose both words after their common prefix.
      have hdrop₁ : (w₁.drop K).length = n - K := by rw [List.length_drop, hw₁len]
      have hdrop₀ : (w₀.drop K).length = n - K := by rw [List.length_drop, hw₀len]
      obtain ⟨b₁, v₁, hv₁⟩ : ∃ b v, w₁.drop K = b :: v := by
        rcases h : w₁.drop K with _ | ⟨b, v⟩
        · rw [h] at hdrop₁; simp at hdrop₁; omega
        · exact ⟨b, v, rfl⟩
      obtain ⟨b₀, v₀, hv₀⟩ : ∃ b v, w₀.drop K = b :: v := by
        rcases h : w₀.drop K with _ | ⟨b, v⟩
        · rw [h] at hdrop₀; simp at hdrop₀; omega
        · exact ⟨b, v, rfl⟩
      have hw₁eq : w₁ = P₀ ++ b₁ :: v₁ := by
        conv_lhs => rw [← List.take_append_drop K w₁, hw₁K, hv₁]
      have hw₀eq : w₀ = P₀ ++ b₀ :: v₀ := by
        conv_lhs => rw [← List.take_append_drop K w₀, ← hP₀def, hv₀]
      have hbne : b₁ ≠ b₀ := by
        intro hbb
        apply hw₁ne
        rw [hw₁eq, hw₀eq, ← hP₀len, take_append_length_succ, take_append_length_succ, hbb]
      -- The two points lie in different first-level pieces of the cylinder of `P₀`.
      have hx₁ : G b₁ (wordMap G v₁ q) ∈ G b₁ '' E := ⟨_, hzE v₁, rfl⟩
      have hx₀ : G b₀ (wordMap G v₀ q) ∈ G b₀ '' E := ⟨_, hzE v₀, rfl⟩
      have hz₁ : wordMap G w₁ q = wordMap G P₀ (G b₁ (wordMap G v₁ q)) := by
        rw [hw₁eq, wordMap_append]; rfl
      have hz₀ : wordMap G w₀ q = wordMap G P₀ (G b₀ (wordMap G v₀ q)) := by
        rw [hw₀eq, wordMap_append]; rfl
      have hdist : wordRatio ρ P₀ * d ≤ diam (U j) := by
        calc wordRatio ρ P₀ * d
            ≤ wordRatio ρ P₀ * dist (G b₁ (wordMap G v₁ q)) (G b₀ (wordMap G v₀ q)) := by
              exact mul_le_mul_of_nonneg_left (hdle b₁ b₀ hbne _ hx₁ _ hx₀)
                (wordRatio_pos hρ0 P₀).le
          _ = dist (wordMap G w₁ q) (wordMap G w₀ q) := by
              rw [hz₁, hz₀, dist_wordMap hsim]
          _ ≤ diam (U j) := dist_le_diam_of_mem (hUbdd j) (hw₁j ▸ hφU w₁) (hw₀j ▸ hφU w₀)
      have hle : wordRatio ρ P₀ ≤ diam (U j) / d := (le_div_iff₀ hd0).2 hdist
      calc wordRatio ρ P₀ ^ t ≤ (diam (U j) / d) ^ t :=
            Real.rpow_le_rpow (wordRatio_pos hρ0 P₀).le hle ht.le
        _ ≤ _ := le_add_of_nonneg_right hn2
    · -- The cylinder is a single word of level `n`.
      have hP₀w₀ : P₀ = w₀ := by rw [hP₀def, hKeq, ← hw₀len, List.take_length]
      have hbound : wordRatio ρ P₀ ≤ r ^ n := by
        rw [hP₀w₀, ← hw₀len]
        exact wordRatio_le_pow hρ0 hrle w₀
      calc wordRatio ρ P₀ ^ t ≤ (r ^ n) ^ t :=
            Real.rpow_le_rpow (wordRatio_pos hρ0 P₀).le hbound ht.le
        _ = (r ^ t) ^ n := hpow n
        _ ≤ _ := le_add_of_nonneg_left hn1
  -- The total mass of the level is one, so the covering sets cannot be too small.
  have key : (1 : ℝ) ≤ ∑ j ∈ J, ((diam (U j) / d) ^ t + (r ^ t) ^ n) := by
    calc (1 : ℝ) = levelSum (fun w => wordRatio ρ w ^ t) n := by
          rw [levelSum_wordRatio_rpow hρ0, hsum, one_pow]
      _ ≤ levelSum (fun w => ∑ j ∈ J, if φ w = j then wordRatio ρ w ^ t else 0) n := by
          refine levelSum_mono fun w _ => ?_
          rw [Finset.sum_ite_eq J (φ w) fun _ => wordRatio ρ w ^ t, if_pos (hφJ w)]
      _ = ∑ j ∈ J, levelSum (fun w => if φ w = j then wordRatio ρ w ^ t else 0) n :=
          levelSum_finsetSum J _ n
      _ ≤ _ := Finset.sum_le_sum perj
  have hsplit : ∑ j ∈ J, ((diam (U j) / d) ^ t + (r ^ t) ^ n)
      = (∑ j ∈ J, diam (U j) ^ t) / d ^ t + J.card * (r ^ t) ^ n := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_div]
    congr 1
    exact Finset.sum_congr rfl fun j _ => Real.div_rpow diam_nonneg hd0.le t
  have hdt : (0 : ℝ) < d ^ t := Real.rpow_pos_of_pos hd0 t
  have hbig : d ^ t / 2 < ∑ j ∈ J, diam (U j) ^ t := by
    rw [hsplit] at key
    have h2 : (1 : ℝ) / 2 < (∑ j ∈ J, diam (U j) ^ t) / d ^ t := by linarith
    rw [lt_div_iff₀ hdt] at h2
    linarith
  -- This contradicts the choice of the cover.
  refine absurd hlt (not_lt.2 ?_)
  calc ENNReal.ofReal (d ^ t / 2) ≤ ENNReal.ofReal (∑ j ∈ J, diam (U j) ^ t) :=
        ENNReal.ofReal_le_ofReal hbig.le
    _ = ∑ j ∈ J, ENNReal.ofReal (diam (U j) ^ t) :=
        ENNReal.ofReal_sum_of_nonneg fun j _ => Real.rpow_nonneg diam_nonneg t
    _ ≤ ∑ j ∈ J, gaugeWeight (fun r : ℝ≥0∞ => r ^ t) (U j) :=
        Finset.sum_le_sum fun j _ => ofReal_diam_rpow_le_gaugeWeight ht (hUbdd j)
    _ ≤ ∑' i, gaugeWeight (fun r : ℝ≥0∞ => r ^ t) (U i) := ENNReal.sum_le_tsum J

/-- Pairwise disjoint scaled copies of a compact set inside it obey `∑ ρ_b^s ≤ 1` at its Hausdorff
dimension `s`. -/
private theorem sum_rpow_le_one_of_disjoint {β : Type*} [Fintype β] {G : β → X → X} {ρ : β → ℝ}
    {E : Set X} (hcomp : IsCompact E) (hne : E.Nonempty) (hρ : ∀ b, ρ b ∈ Ioo (0 : ℝ) 1)
    (hsim : ∀ b x y, dist (G b x) (G b y) = ρ b * dist x y) (hsub : ∀ b, G b '' E ⊆ E)
    (hdisj : ∀ b b' : β, b ≠ b' → Disjoint (G b '' E) (G b' '' E))
    {s : ℝ} (hs : 0 < s) (hdim : dimH E = ENNReal.ofReal s) : ∑ b, ρ b ^ s ≤ 1 := by
  by_contra hcon
  rw [not_le] at hcon
  haveI : Nonempty β := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hcon
    linarith
  obtain ⟨t, ht1, -⟩ := existsUnique_similarityDim hρ
  have hst : s < t := by
    by_contra hts
    rw [not_lt] at hts
    have hmono := (strictAnti_sum_rpow hρ).antitone hts
    rw [ht1] at hmono
    linarith
  have ht0 : 0 < t := hs.trans hst
  have hmeas : μH[t] E ≠ 0 := fun h => (hausdorffContent_ne_zero_of_separated hcomp hne hρ hsim
    hsub hdisj ht0 ht1) ((same_null_sets ht0.le E).1 h)
  have hle : ENNReal.ofReal t ≤ dimH E :=
    le_dimH_of_hausdorffMeasure_ne_zero (d := Real.toNNReal t)
      (by rwa [Real.coe_toNNReal t ht0.le])
  rw [hdim] at hle
  exact absurd hle (not_le.2 ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs.le).2 hst))

end Separated

/-! ## Proposition 8.4 -/

section Proposition84

omit [MeasurableSpace X] [BorelSpace X] in
/-- The image of a set under the maps of a word has diameter scaled by the ratio of the word. -/
private theorem ediam_wordMap_image {ι : Type*} {F : ι → X → X} {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    (hsim : ∀ i x y, dist (F i x) (F i y) = c i * dist x y) (w : List ι) (A : Set X) :
    ediam (wordMap F w '' A) = ENNReal.ofReal (wordRatio c w) * ediam A := by
  simp only [ediam, iSup_image, edist_wordMap hc hsim, ENNReal.mul_iSup]
  rfl

omit [MeasurableSpace X] [BorelSpace X] in
/-- The image of a set under the maps of a word has its weight scaled by the `s`-th power of the
ratio of the word. -/
private theorem gaugeWeight_wordMap_image {ι : Type*} {F : ι → X → X} {c : ι → ℝ}
    (hc : ∀ i, 0 < c i) (hsim : ∀ i x y, dist (F i x) (F i y) = c i * dist x y) {s : ℝ}
    (hs : 0 ≤ s) (w : List ι) (A : Set X) :
    gaugeWeight (fun r : ℝ≥0∞ => r ^ s) (wordMap F w '' A)
      = ENNReal.ofReal (wordRatio c w) ^ s * gaugeWeight (fun r : ℝ≥0∞ => r ^ s) A := by
  simp only [gaugeWeight, image_nonempty, ediam_wordMap_image hc hsim,
    ENNReal.mul_rpow_of_nonneg _ _ hs, ENNReal.mul_iSup]

omit [MeasurableSpace X] [BorelSpace X] in
/-- The weight of the gauge `t ↦ t ^ s` is monotone for `s ≥ 0`. -/
private theorem gaugeWeight_rpow_mono {s : ℝ} (hs : 0 ≤ s) {A B : Set X} (h : A ⊆ B) :
    gaugeWeight (fun r : ℝ≥0∞ => r ^ s) A ≤ gaugeWeight (fun r : ℝ≥0∞ => r ^ s) B := by
  simp only [gaugeWeight]
  refine iSup_le fun hA => le_iSup_of_le (hA.mono h) ?_
  exact ENNReal.rpow_le_rpow (ediam_mono h) hs

omit [MeasurableSpace X] [BorelSpace X] in
/-- The image of a bounded set under the maps of a word has diameter scaled by the ratio. -/
private theorem diam_wordMap_image {ι : Type*} {F : ι → X → X} {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    (hsim : ∀ i x y, dist (F i x) (F i y) = c i * dist x y) (w : List ι) (A : Set X) :
    diam (wordMap F w '' A) = wordRatio c w * diam A := by
  have h : ediam (wordMap F w '' A) = ENNReal.ofReal (wordRatio c w) * ediam A :=
    ediam_wordMap_image hc hsim w A
  have : diam (wordMap F w '' A) = (ENNReal.ofReal (wordRatio c w) * ediam A).toReal := by
    rw [← h]
    rfl
  rw [this, ENNReal.toReal_mul, ENNReal.toReal_ofReal (wordRatio_pos hc w).le]
  rfl

/-- The Hausdorff content never exceeds the Hausdorff measure. -/
private theorem hausdorffContent_le_hausdorffMeasure {s : ℝ} (hs : 0 ≤ s) (A : Set X) :
    hausdorffContent s A ≤ μH[s] A := by
  rw [← hausdorffMeasureGauge_rpow hs]
  exact (hausdorffContentGauge_le_hausdorffDeltaGauge _ 1 A).trans
    (hausdorffDeltaGauge_le_hausdorffMeasureGauge _ zero_lt_one A)

/-- If measure and content agree on a measurable set of finite measure, they agree on every subset
of it, measurable or not. -/
private theorem measure_eq_content_of_subset {s : ℝ} (hs : 0 < s) {E : Set X}
    (hEmeas : MeasurableSet E) (hEc : μH[s] E = hausdorffContent s E) (hfin : μH[s] E ≠ ⊤)
    {A : Set X} (hA : A ⊆ E) : μH[s] A = hausdorffContent s A := by
  have hmono : ∀ {P Q : Set X}, P ⊆ Q → hausdorffContent s P ≤ hausdorffContent s Q :=
    fun h => (hausdorff_outer_measures (X := X) (fun r : ℝ≥0∞ => r ^ s) zero_lt_one).2.1.mono h
  have hfinA : hausdorffContent s A ≠ ⊤ := ne_top_of_le_ne_top (hEc ▸ hfin) (hmono hA)
  refine le_antisymm ?_ (hausdorffContent_le_hausdorffMeasure hs.le A)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨U, hlt⟩ := iInf_lt_iff.1 (ENNReal.lt_add_right hfinA (ENNReal.coe_ne_zero.2 hε.ne'))
  obtain ⟨hUo, hlt⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hAU, hlt⟩ := iInf_lt_iff.1 hlt
  have hV : MeasurableSet ((⋃ i, U i) ∩ E) := (isOpen_iUnion hUo).measurableSet.inter hEmeas
  calc μH[s] A ≤ μH[s] ((⋃ i, U i) ∩ E) := measure_mono (subset_inter hAU hA)
    _ = hausdorffContent s ((⋃ i, U i) ∩ E) :=
        equal_measure_content hs.le hEc hfin hV.nullMeasurableSet inter_subset_right
    _ ≤ hausdorffContent s (⋃ i, U i) := hmono inter_subset_left
    _ ≤ ∑' i, gaugeWeight (fun r : ℝ≥0∞ => r ^ s) (U i) :=
        iInf_le_of_le U (iInf_le_of_le hUo (iInf_le _ Subset.rfl))
    _ ≤ hausdorffContent s A + ε := hlt.le

/-- Proposition 8.4: on a self-similar set the Hausdorff measure and the Hausdorff content agree at
the Hausdorff dimension, and hence agree on every subset. -/
theorem self_similar_measure_content {ι : Type*} [Fintype ι] [Nonempty ι] {F : ι → X → X}
    {c : ι → ℝ} {E : Set X} (hE : IsSelfSimilarSet F c E) {s : ℝ} (hs : 0 < s)
    (hdim : dimH E = ENNReal.ofReal s) :
    μH[s] E = hausdorffContent s E ∧ ∀ A ⊆ E, μH[s] A = hausdorffContent s A := by
  obtain ⟨hne, hcomp, hcmem, hsim, hinv⟩ := hE
  have hc0 : ∀ i, 0 < c i := fun i => (hcmem i).1
  have hsubE : ∀ i, F i '' E ⊆ E := by
    intro i
    conv_rhs => rw [hinv]
    exact subset_iUnion (fun i => F i '' E) i
  have hbdd : Bornology.IsBounded E := hcomp.isBounded
  have hcontw : ∀ w : List ι, Continuous (wordMap F w) := fun w =>
    (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (wordRatio c w)) fun x y => by
      rw [dist_wordMap hsim, Real.coe_toNNReal _ (wordRatio_pos hc0 w).le]).continuous
  have hVcomp : ∀ w : List ι, IsCompact (wordMap F w '' E) := fun w => hcomp.image (hcontw w)
  have hVdiam : ∀ w : List ι, diam (wordMap F w '' E) = wordRatio c w * diam E := fun w =>
    diam_wordMap_image hc0 hsim w E
  -- The set is not a single point.
  have hdiam : 0 < diam E := by
    rcases eq_or_lt_of_le (diam_nonneg : (0 : ℝ) ≤ diam E) with h | h
    · exfalso
      have hsub : E.Subsingleton := fun x hx y hy =>
        dist_le_zero.1 (h ▸ dist_le_diam_of_mem hbdd hx hy)
      rw [dimH_subsingleton hsub] at hdim
      exact (ENNReal.ofReal_pos.2 hs).ne' hdim.symm
    · exact h
  have hVpos : ∀ w : List ι, 0 < diam (wordMap F w '' E) := fun w => by
    rw [hVdiam w]
    exact mul_pos (wordRatio_pos hc0 w) hdiam
  have hcontfin : hausdorffContent s E ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_nonneg hs.le hbdd.ediam_ne_top)
      (hausdorffContent_le_ediam_rpow hs.le E)
  obtain ⟨cmax, hcmax0, hcmax1, hcmaxle⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ i, c i ≤ r :=
    ⟨Finset.univ.sup' Finset.univ_nonempty c,
      (Finset.lt_sup'_iff _).2 ⟨Classical.arbitrary ι, Finset.mem_univ _, hc0 _⟩,
      (Finset.sup'_lt_iff _).2 fun i _ => (hcmem i).2,
      fun i => Finset.le_sup' c (Finset.mem_univ i)⟩
  -- The main inequality: the measure is at most the content.
  have main : μH[s] E ≤ hausdorffContent s E := by
    rw [← hausdorffMeasureGauge_rpow hs.le]
    refine iSup₂_le fun δ hδ => ?_
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    -- A real scale below `δ` and below the diameter of `E`.
    obtain ⟨δ', hδ'0, hδ'δ⟩ := exists_between hδ
    have hδ'top : δ' ≠ ⊤ := ne_top_of_lt hδ'δ
    obtain ⟨δ₀, hδ₀0, hδ₀E, hδ₀δ⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ diam E ∧ ENNReal.ofReal δ₀ < δ := by
      refine ⟨min (diam E) δ'.toReal, lt_min hdiam (ENNReal.toReal_pos hδ'0.ne' hδ'top),
        min_le_left _ _, lt_of_le_of_lt ?_ hδ'δ⟩
      exact (ENNReal.ofReal_le_ofReal (min_le_right (diam E) δ'.toReal)).trans_eq
        (ENNReal.ofReal_toReal hδ'top)
    -- A near optimal cover of `E`.
    obtain ⟨U, hcov⟩ :=
      iInf_lt_iff.1 (ENNReal.lt_add_right hcontfin (ENNReal.coe_ne_zero.2 hε.ne'))
    obtain ⟨hUo, hcov⟩ := iInf_lt_iff.1 hcov
    obtain ⟨hEU, hcov⟩ := iInf_lt_iff.1 hcov
    -- The images of `E` under the words of small diameter form a fine cover by compact sets.
    have hfine : ∀ x ∈ E, ∀ η : ℝ, 0 < η →
        ∃ w ∈ {w : List ι | diam (wordMap F w '' E) < δ₀}, x ∈ wordMap F w '' E ∧
          diam (wordMap F w '' E) < η := by
      intro x hx η hη
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos (lt_min hδ₀0 hη) hdiam) hcmax1
      obtain ⟨w, hwlen, hxw⟩ := exists_word_mem hinv n hx
      have hd : diam (wordMap F w '' E) < min δ₀ η := by
        rw [hVdiam w]
        calc wordRatio c w * diam E ≤ cmax ^ n * diam E :=
              mul_le_mul_of_nonneg_right (hwlen ▸ wordRatio_le_pow hc0 hcmaxle w) diam_nonneg
          _ < min δ₀ η / diam E * diam E := mul_lt_mul_of_pos_right hn hdiam
          _ = min δ₀ η := div_mul_cancel₀ _ hdiam.ne'
      exact ⟨w, hd.trans_le (min_le_left _ _), hxw, hd.trans_le (min_le_right _ _)⟩
    obtain ⟨u, huT, hudisj, halt⟩ := hausdorff_vitali_compact hs
      {w : List ι | diam (wordMap F w '' E) < δ₀} (fun w => wordMap F w '' E)
      (Set.to_countable _) (fun w _ => hVcomp w) (fun w _ => hVpos w) hfine
    -- The selected words are nontrivial contractions.
    have hratio1 : ∀ w ∈ u, wordRatio c w < 1 := by
      intro w hw
      refine (mul_lt_iff_lt_one_left hdiam).1 ?_
      calc wordRatio c w * diam E = diam (wordMap F w '' E) := (hVdiam w).symm
        _ < δ₀ := huT hw
        _ ≤ diam E := hδ₀E
    -- The selected words obey `∑ c_𝐢^s ≤ 1`.
    have hsum1 : ∑' w : u, ENNReal.ofReal (wordRatio c (w : List ι)) ^ s ≤ 1 := by
      rw [ENNReal.tsum_eq_iSup_sum]
      refine iSup_le fun S => ?_
      have hreal : ∑ b : {x // x ∈ S}, wordRatio c ((b : u) : List ι) ^ s ≤ 1 := by
        refine sum_rpow_le_one_of_disjoint
          (G := fun b : {x // x ∈ S} => wordMap F ((b : u) : List ι))
          hcomp hne (fun b => ⟨wordRatio_pos hc0 _, hratio1 _ (b : u).2⟩)
          (fun b => dist_wordMap hsim _) (fun b => wordMap_image_subset hsubE _) ?_ hs hdim
        intro b b' hbb
        exact hudisj (b : u).2 (b' : u).2 fun h => hbb (Subtype.ext (Subtype.ext h))
      calc ∑ i ∈ S, ENNReal.ofReal (wordRatio c ((i : u) : List ι)) ^ s
          = ∑ i ∈ S, ENNReal.ofReal (wordRatio c ((i : u) : List ι) ^ s) :=
            Finset.sum_congr rfl fun i _ =>
              ENNReal.ofReal_rpow_of_nonneg (wordRatio_pos hc0 _).le hs.le
        _ = ENNReal.ofReal (∑ i ∈ S, wordRatio c ((i : u) : List ι) ^ s) :=
            (ENNReal.ofReal_sum_of_nonneg fun i _ =>
              Real.rpow_nonneg (wordRatio_pos hc0 _).le s).symm
        _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (by
              have hcoe : ∑ i ∈ S, wordRatio c ((i : u) : List ι) ^ s
                  = ∑ b : {x // x ∈ S}, wordRatio c ((b : u) : List ι) ^ s :=
                (Finset.sum_coe_sort S fun i : u => wordRatio c (i : List ι) ^ s).symm
              rw [hcoe]
              exact hreal)
        _ = 1 := ENNReal.ofReal_one
    -- Hence the sum of diameters converges and the selected family covers `E` up to a null set.
    have hnull : μH[s] (E \ ⋃ w ∈ u, wordMap F w '' E) = 0 := by
      refine halt.resolve_right fun hdiv => ?_
      have heq : ∀ w : List ι, ENNReal.ofReal (diam (wordMap F w '' E)) ^ s
          = ENNReal.ofReal (wordRatio c w) ^ s * ENNReal.ofReal (diam E) ^ s := fun w => by
        rw [hVdiam w, ENNReal.ofReal_mul (wordRatio_pos hc0 w).le,
          ENNReal.mul_rpow_of_nonneg _ _ hs.le]
      have hle : ∑' w : u, ENNReal.ofReal (diam (wordMap F (w : List ι) '' E)) ^ s
          ≤ ENNReal.ofReal (diam E) ^ s := by
        calc ∑' w : u, ENNReal.ofReal (diam (wordMap F (w : List ι) '' E)) ^ s
            = (∑' w : u, ENNReal.ofReal (wordRatio c (w : List ι)) ^ s)
              * ENNReal.ofReal (diam E) ^ s := by
              rw [← ENNReal.tsum_mul_right]
              exact tsum_congr fun w => heq _
          _ ≤ 1 * ENNReal.ofReal (diam E) ^ s := by gcongr
          _ = ENNReal.ofReal (diam E) ^ s := one_mul _
      rw [hdiv] at hle
      exact absurd (top_le_iff.1 hle)
        (ENNReal.rpow_ne_top_of_nonneg hs.le ENNReal.ofReal_ne_top)
    -- Every piece is covered by the images of the near optimal cover.
    have hpiece : ∀ w ∈ u, hausdorffDelta s δ (wordMap F w '' E)
        ≤ ENNReal.ofReal (wordRatio c w) ^ s * (hausdorffContent s E + ε) := by
      intro w hw
      have hcovw : wordMap F w '' E ⊆ ⋃ i, wordMap F w '' (U i ∩ E) := by
        rw [← image_iUnion]
        refine image_mono fun x hx => ?_
        obtain ⟨i, hi⟩ := mem_iUnion.1 (hEU hx)
        exact mem_iUnion.2 ⟨i, hi, hx⟩
      have hdiamw : ∀ i, ediam (wordMap F w '' (U i ∩ E)) < δ := by
        intro i
        calc ediam (wordMap F w '' (U i ∩ E))
            = ENNReal.ofReal (wordRatio c w) * ediam (U i ∩ E) :=
              ediam_wordMap_image hc0 hsim w _
          _ ≤ ENNReal.ofReal (wordRatio c w) * ediam E := by gcongr; exact inter_subset_right
          _ = ediam (wordMap F w '' E) := (ediam_wordMap_image hc0 hsim w E).symm
          _ = ENNReal.ofReal (diam (wordMap F w '' E)) :=
              (ENNReal.ofReal_toReal (hVcomp w).isBounded.ediam_ne_top).symm
          _ < ENNReal.ofReal δ₀ := ENNReal.ofReal_lt_ofReal_iff_of_nonneg diam_nonneg |>.2 (huT hw)
          _ < δ := hδ₀δ
      calc hausdorffDelta s δ (wordMap F w '' E)
          ≤ ∑' i, gaugeWeight (fun r : ℝ≥0∞ => r ^ s) (wordMap F w '' (U i ∩ E)) := by
            rw [(arbitrary_covers hs.le δ (wordMap F w '' E)).1]
            exact iInf_le_of_le _ (iInf_le_of_le hdiamw (iInf_le _ hcovw))
        _ = ENNReal.ofReal (wordRatio c w) ^ s
              * ∑' i, gaugeWeight (fun r : ℝ≥0∞ => r ^ s) (U i ∩ E) := by
            rw [← ENNReal.tsum_mul_left]
            exact tsum_congr fun i => gaugeWeight_wordMap_image hc0 hsim hs.le w _
        _ ≤ ENNReal.ofReal (wordRatio c w) ^ s * (hausdorffContent s E + ε) := by
            gcongr
            exact le_trans (ENNReal.tsum_le_tsum fun i =>
              gaugeWeight_rpow_mono hs.le inter_subset_left) hcov.le
    -- Putting the pieces together.
    have hm : ∀ A : Set X,
        (hausdorff_outer_measures (X := X) (fun r : ℝ≥0∞ => r ^ s) hδ).1.toOuterMeasure A
          = hausdorffDelta s δ A := fun A => rfl
    calc hausdorffDelta s δ E
        = (hausdorff_outer_measures (X := X) (fun r : ℝ≥0∞ => r ^ s) hδ).1.toOuterMeasure E :=
          (hm E).symm
      _ ≤ (hausdorff_outer_measures (X := X) (fun r : ℝ≥0∞ => r ^ s) hδ).1.toOuterMeasure
            ((⋃ w ∈ u, wordMap F w '' E) ∪ (E \ ⋃ w ∈ u, wordMap F w '' E)) := by
          refine measure_mono fun x hx => ?_
          by_cases h : x ∈ ⋃ w ∈ u, wordMap F w '' E
          · exact Or.inl h
          · exact Or.inr ⟨hx, h⟩
      _ ≤ (hausdorff_outer_measures (X := X) (fun r : ℝ≥0∞ => r ^ s) hδ).1.toOuterMeasure
            (⋃ w ∈ u, wordMap F w '' E)
          + (hausdorff_outer_measures (X := X) (fun r : ℝ≥0∞ => r ^ s) hδ).1.toOuterMeasure
            (E \ ⋃ w ∈ u, wordMap F w '' E) := measure_union_le _ _
      _ ≤ (∑' w : u, hausdorffDelta s δ (wordMap F (w : List ι) '' E)) + 0 := by
          gcongr
          · exact measure_biUnion_le _ (Set.to_countable u) _
          · rw [hm]
            refine le_of_le_of_eq (le_trans (hausdorffDeltaGauge_le_hausdorffMeasureGauge _ hδ _)
              (le_of_eq (hausdorffMeasureGauge_rpow hs.le _))) hnull
      _ ≤ (∑' w : u, ENNReal.ofReal (wordRatio c (w : List ι)) ^ s
            * (hausdorffContent s E + ε)) + 0 :=
          add_le_add (ENNReal.tsum_le_tsum fun w : u => hpiece (w : List ι) w.2) le_rfl
      _ = (∑' w : u, ENNReal.ofReal (wordRatio c (w : List ι)) ^ s)
            * (hausdorffContent s E + ε) := by rw [add_zero, ENNReal.tsum_mul_right]
      _ ≤ 1 * (hausdorffContent s E + ε) := by gcongr
      _ = hausdorffContent s E + ε := one_mul _
  have h1 : μH[s] E = hausdorffContent s E :=
    le_antisymm main (hausdorffContent_le_hausdorffMeasure hs.le E)
  exact ⟨h1, fun A hA => measure_eq_content_of_subset hs hcomp.isClosed.measurableSet h1
    (by rw [h1]; exact hcontfin) hA⟩

end Proposition84

end GeometricMeasureTheory
