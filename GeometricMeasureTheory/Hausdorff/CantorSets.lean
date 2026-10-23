/-
# Section 2.3: Cantor sets

The Cantor examples of Section 2.3 for the symmetric Cantor set with ratio `0 < a < 1/2`: from
`[0, 1]`, keep the two end intervals of relative length `a` of every construction interval. The
middle-third Cantor set is `a = 1/3`, which is Mathlib's `cantorSet`, and the middle-half Cantor set
of Example 2.23 is `a = 1/4`. Throughout, `s = log 2 / log (1/a)`.

| Notes | Lean declaration | Location |
|---|---|---|
| Construction intervals and the Cantor set | `cantorInterval`, `cantorLevel`, `symmetricCantorSet`, `symmetricCantorSet_one_third` | here; `cantorSet` in `Mathlib/Topology/Instances/CantorSet.lean` |
| The Cantor upper bound | `cantor_upper_bound` | here |
| The Cantor measure | `cantorMeasure`, `exists_cantor_measure` | here |
| The Cantor lower bound and dimension | `cantor_lower_bound`, `dimH_symmetricCantorSet` | here |
| The middle-third Cantor set: `1/4 ≤ 𝓗^s_∞(𝓒) ≤ 𝓗^s(𝓒) ≤ 1` and `dim_H 𝓒 = log 2 / log 3` | `middle_third_cantor` | here |
| Example 2.23 (middle-half Cantor set) | `middle_half_cantor` | here |

The Cantor measure `cantorMeasure a` is the image of the product of fair coin measures on
`ℕ → Bool` under the coding map `ω ↦ ∑ⱼ ωⱼ (1 - a) a^j`. Distinct construction intervals of level
`n + 1` are separated by gaps of length at least `(1 - 2a) a^n`, so a ball of radius `r` with
`2r ≤ (1 - 2a) a^n` meets at most one of them; this gives the ball bound
`μ(B(x, r)) ≤ (2 / (1 - 2a))^s r^s`.
-/
import GeometricMeasureTheory.Hausdorff.Computing

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

/-- The construction interval with address `w`: the image of `[0, 1]` under the composition of the
maps `x ↦ a x` (letter `false`) and `x ↦ 1 - a + a x` (letter `true`) named by `w`. -/
def cantorInterval (a : ℝ) : List Bool → Set ℝ
  | [] => Icc 0 1
  | false :: w => (fun x => a * x) '' cantorInterval a w
  | true :: w => (fun x => 1 - a + a * x) '' cantorInterval a w

/-- The `n`th level of the construction: the union of the `2^n` construction intervals of length
`a^n`. -/
def cantorLevel (a : ℝ) (n : ℕ) : Set ℝ :=
  ⋃ (w : List Bool) (_ : w.length = n), cantorInterval a w

/-- The symmetric Cantor set with ratio `a`. -/
def symmetricCantorSet (a : ℝ) : Set ℝ :=
  ⋂ n, cantorLevel a n

/-! ## Construction intervals, levels and the Cantor set -/

section IntervalAPI

variable {a : ℝ}

/-- The similarity for the letter `b`: `x ↦ a x` for `false` and `x ↦ 1 - a + a x` for `true`. -/
def cantorMap (a : ℝ) : Bool → ℝ → ℝ
  | false, x => a * x
  | true, x => 1 - a + a * x

/-- Both similarities in one formula. -/
theorem cantorMap_eq (a : ℝ) (b : Bool) (x : ℝ) :
    cantorMap a b x = (if b then 1 - a else 0) + a * x := by
  cases b <;> simp [cantorMap]

/-- The left endpoint of the construction interval with address `w`. -/
def cantorLeft (a : ℝ) : List Bool → ℝ
  | [] => 0
  | b :: w => cantorMap a b (cantorLeft a w)

/-- The construction interval with the empty address is `[0, 1]`. -/
@[simp]
theorem cantorInterval_nil (a : ℝ) : cantorInterval a [] = Icc 0 1 :=
  rfl

/-- The recursion for construction intervals: the first letter is applied last. -/
theorem cantorInterval_cons (a : ℝ) (b : Bool) (w : List Bool) :
    cantorInterval a (b :: w) = cantorMap a b '' cantorInterval a w := by
  cases b <;> rfl

/-- For `0 ≤ a ≤ 1` both similarities map `[0, 1]` into itself. -/
theorem cantorMap_mem_Icc (ha₀ : 0 ≤ a) (ha : a ≤ 1) (b : Bool) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : cantorMap a b x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hx
  cases b <;> simp only [cantorMap, mem_Icc] <;> constructor <;> nlinarith

/-- The construction interval with address `w` is `[p, p + a^n]`, where `p = cantorLeft a w` and
`n` is the length of `w`. -/
theorem cantorInterval_eq_Icc (ha : 0 ≤ a) (w : List Bool) :
    cantorInterval a w = Icc (cantorLeft a w) (cantorLeft a w + a ^ w.length) := by
  induction w with
  | nil => simp [cantorLeft]
  | cons b w ih =>
    have hle : cantorLeft a w ≤ cantorLeft a w + a ^ w.length :=
      le_add_of_nonneg_right (pow_nonneg ha _)
    rw [cantorInterval_cons, ih]
    cases b
    · show (fun x => a * x) '' _ =
        Icc (a * cantorLeft a w) (a * cantorLeft a w + a ^ (w.length + 1))
      rw [image_mul_left_Icc ha hle, mul_add, ← pow_succ']
    · show (fun x => 1 - a + a * x) '' _ =
        Icc (1 - a + a * cantorLeft a w) (1 - a + a * cantorLeft a w + a ^ (w.length + 1))
      have hcomp : (fun x => 1 - a + a * x) = (fun x => 1 - a + x) ∘ (fun x => a * x) := rfl
      rw [hcomp, image_comp, image_mul_left_Icc ha hle, image_const_add_Icc, mul_add, ← pow_succ',
        add_assoc]

/-- The left endpoint lies in the construction interval. -/
theorem cantorLeft_mem_cantorInterval (ha : 0 ≤ a) (w : List Bool) :
    cantorLeft a w ∈ cantorInterval a w := by
  rw [cantorInterval_eq_Icc ha]
  exact ⟨le_rfl, le_add_of_nonneg_right (pow_nonneg ha _)⟩

/-- Construction intervals are closed. -/
theorem isClosed_cantorInterval (ha : 0 ≤ a) (w : List Bool) : IsClosed (cantorInterval a w) := by
  rw [cantorInterval_eq_Icc ha]
  exact isClosed_Icc

/-- Every construction interval lies in `[0, 1]`. -/
theorem cantorInterval_subset_Icc (ha₀ : 0 ≤ a) (ha : a ≤ 1) (w : List Bool) :
    cantorInterval a w ⊆ Icc 0 1 := by
  induction w with
  | nil => exact subset_rfl
  | cons b w ih =>
    rw [cantorInterval_cons]
    rintro _ ⟨x, hx, rfl⟩
    exact cantorMap_mem_Icc ha₀ ha b (ih hx)

/-- Extending an address shrinks the construction interval. -/
theorem cantorInterval_append_subset (ha₀ : 0 ≤ a) (ha : a ≤ 1) (w v : List Bool) :
    cantorInterval a (w ++ v) ⊆ cantorInterval a w := by
  induction w with
  | nil => exact cantorInterval_subset_Icc ha₀ ha v
  | cons b w ih =>
    rw [List.cons_append, cantorInterval_cons, cantorInterval_cons]
    exact image_mono ih

/-- A construction interval of level `n` has diameter `a^n`. -/
theorem ediam_cantorInterval (ha : 0 ≤ a) (w : List Bool) :
    ediam (cantorInterval a w) = ENNReal.ofReal (a ^ w.length) := by
  rw [cantorInterval_eq_Icc ha, Real.ediam_Icc, add_sub_cancel_left]

/-- A construction interval of level `n` has diameter `a^n`. -/
theorem diam_cantorInterval (ha : 0 ≤ a) (w : List Bool) :
    diam (cantorInterval a w) = a ^ w.length := by
  rw [cantorInterval_eq_Icc ha, Real.diam_Icc (le_add_of_nonneg_right (pow_nonneg ha _)),
    add_sub_cancel_left]

/-- A construction interval of level `n` lies in the closed ball of radius `a^n` about each of its
points. -/
theorem cantorInterval_subset_closedBall (ha : 0 ≤ a) {w : List Bool} {x : ℝ}
    (hx : x ∈ cantorInterval a w) : cantorInterval a w ⊆ closedBall x (a ^ w.length) := by
  rw [cantorInterval_eq_Icc ha] at hx ⊢
  intro y hy
  rw [mem_closedBall, Real.dist_eq, abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- The points of level `n` are the points of the construction intervals of level `n`. -/
theorem mem_cantorLevel {n : ℕ} {x : ℝ} :
    x ∈ cantorLevel a n ↔ ∃ w : List Bool, w.length = n ∧ x ∈ cantorInterval a w := by
  simp [cantorLevel]

/-- A construction interval lies in the level given by the length of its address. -/
theorem cantorInterval_subset_cantorLevel (w : List Bool) :
    cantorInterval a w ⊆ cantorLevel a w.length :=
  fun _ hx => mem_cantorLevel.2 ⟨w, rfl, hx⟩

/-- The level `0` is `[0, 1]`. -/
@[simp]
theorem cantorLevel_zero (a : ℝ) : cantorLevel a 0 = Icc 0 1 := by
  ext x
  simp [mem_cantorLevel]

/-- The level `n + 1` is the union of the images of level `n` under the two similarities. -/
theorem cantorLevel_succ (a : ℝ) (n : ℕ) :
    cantorLevel a (n + 1) =
      (fun x => a * x) '' cantorLevel a n ∪ (fun x => 1 - a + a * x) '' cantorLevel a n := by
  ext x
  simp only [mem_union, mem_image, mem_cantorLevel]
  constructor
  · rintro ⟨w, hw, hx⟩
    obtain ⟨b, v, rfl⟩ := List.exists_cons_of_length_eq_add_one hw
    have hv : v.length = n := by simpa using hw
    rw [cantorInterval_cons] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    cases b
    · exact Or.inl ⟨y, ⟨v, hv, hy⟩, rfl⟩
    · exact Or.inr ⟨y, ⟨v, hv, hy⟩, rfl⟩
  · rintro (⟨y, ⟨v, hv, hy⟩, rfl⟩ | ⟨y, ⟨v, hv, hy⟩, rfl⟩)
    · exact ⟨false :: v, by simp [hv], mem_image_of_mem _ hy⟩
    · exact ⟨true :: v, by simp [hv], mem_image_of_mem _ hy⟩

/-- The level `n + 1` lies in the level `n`. -/
theorem cantorLevel_succ_subset (ha₀ : 0 ≤ a) (ha : a ≤ 1) (n : ℕ) :
    cantorLevel a (n + 1) ⊆ cantorLevel a n := by
  intro x hx
  obtain ⟨w, hw, hx⟩ := mem_cantorLevel.1 hx
  refine mem_cantorLevel.2 ⟨w.take n, by simp [hw], ?_⟩
  rw [← List.take_append_drop n w] at hx
  exact cantorInterval_append_subset ha₀ ha _ _ hx

/-- The levels of the construction decrease. -/
theorem cantorLevel_antitone (ha₀ : 0 ≤ a) (ha : a ≤ 1) : Antitone (cantorLevel a) :=
  antitone_nat_of_succ_le (cantorLevel_succ_subset ha₀ ha)

/-- Every level lies in `[0, 1]`. -/
theorem cantorLevel_subset_Icc (ha₀ : 0 ≤ a) (ha : a ≤ 1) (n : ℕ) :
    cantorLevel a n ⊆ Icc 0 1 := by
  intro x hx
  obtain ⟨w, -, hx⟩ := mem_cantorLevel.1 hx
  exact cantorInterval_subset_Icc ha₀ ha w hx

/-- Every level is closed, as a finite union of closed intervals. -/
theorem isClosed_cantorLevel (ha : 0 ≤ a) (n : ℕ) : IsClosed (cantorLevel a n) :=
  (List.finite_length_eq Bool n).isClosed_biUnion fun w _ => isClosed_cantorInterval ha w

/-- A point of the Cantor set lies in a construction interval of every level. -/
theorem mem_symmetricCantorSet {x : ℝ} :
    x ∈ symmetricCantorSet a ↔ ∀ n, ∃ w : List Bool, w.length = n ∧ x ∈ cantorInterval a w := by
  simp only [symmetricCantorSet, mem_iInter, mem_cantorLevel]

/-- The Cantor set lies in every level. -/
theorem symmetricCantorSet_subset_cantorLevel (n : ℕ) : symmetricCantorSet a ⊆ cantorLevel a n :=
  iInter_subset _ n

/-- The Cantor set lies in `[0, 1]`. -/
theorem symmetricCantorSet_subset_Icc (a : ℝ) : symmetricCantorSet a ⊆ Icc 0 1 := by
  simpa using symmetricCantorSet_subset_cantorLevel (a := a) 0

/-- The Cantor set is closed. -/
theorem isClosed_symmetricCantorSet (ha : 0 ≤ a) : IsClosed (symmetricCantorSet a) :=
  isClosed_iInter (isClosed_cantorLevel ha)

/-- The Cantor set is compact. -/
theorem isCompact_symmetricCantorSet (ha : 0 ≤ a) : IsCompact (symmetricCantorSet a) :=
  isCompact_Icc.of_isClosed_subset (isClosed_symmetricCantorSet ha)
    (symmetricCantorSet_subset_Icc a)

/-- The point `0` lies in the leftmost construction interval of every level. -/
theorem zero_mem_cantorInterval_replicate (a : ℝ) (n : ℕ) :
    (0 : ℝ) ∈ cantorInterval a (List.replicate n false) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, cantorInterval_cons]
    exact ⟨0, ih, by simp [cantorMap]⟩

/-- The point `1` lies in the rightmost construction interval of every level. -/
theorem one_mem_cantorInterval_replicate (a : ℝ) (n : ℕ) :
    (1 : ℝ) ∈ cantorInterval a (List.replicate n true) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, cantorInterval_cons]
    exact ⟨1, ih, by simp [cantorMap]⟩

/-- The point `0` lies in the Cantor set. -/
theorem zero_mem_symmetricCantorSet (a : ℝ) : (0 : ℝ) ∈ symmetricCantorSet a :=
  mem_symmetricCantorSet.2 fun n =>
    ⟨_, List.length_replicate, zero_mem_cantorInterval_replicate a n⟩

/-- The point `1` lies in the Cantor set. -/
theorem one_mem_symmetricCantorSet (a : ℝ) : (1 : ℝ) ∈ symmetricCantorSet a :=
  mem_symmetricCantorSet.2 fun n =>
    ⟨_, List.length_replicate, one_mem_cantorInterval_replicate a n⟩

/-- The Cantor set is non-empty. -/
theorem symmetricCantorSet_nonempty (a : ℝ) : (symmetricCantorSet a).Nonempty :=
  ⟨0, zero_mem_symmetricCantorSet a⟩

/-- The Cantor set has at least two points. -/
theorem symmetricCantorSet_nontrivial (a : ℝ) : (symmetricCantorSet a).Nontrivial :=
  ⟨0, zero_mem_symmetricCantorSet a, 1, one_mem_symmetricCantorSet a, zero_ne_one⟩

/-- The Cantor set has diameter one. -/
theorem ediam_symmetricCantorSet (a : ℝ) : ediam (symmetricCantorSet a) = 1 := by
  refine le_antisymm ?_ ?_
  · calc ediam (symmetricCantorSet a) ≤ ediam (Icc (0 : ℝ) 1) :=
          ediam_mono (symmetricCantorSet_subset_Icc a)
      _ = 1 := by simp [Real.ediam_Icc]
  · calc (1 : ℝ≥0∞) = edist (0 : ℝ) 1 := by simp [edist_dist, Real.dist_eq]
      _ ≤ ediam (symmetricCantorSet a) :=
          edist_le_ediam_of_mem (zero_mem_symmetricCantorSet a) (one_mem_symmetricCantorSet a)

/-- Images of `[0, 1]` under the two different similarities are `1 - 2a` apart. -/
theorem one_sub_two_mul_le_abs_sub_cantorMap (ha₀ : 0 ≤ a) {b c : Bool} (hbc : b ≠ c) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    1 - 2 * a ≤ |cantorMap a b x - cantorMap a c y| := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  cases b <;> cases c
  · exact absurd rfl hbc
  · show 1 - 2 * a ≤ |a * x - (1 - a + a * y)|
    rw [abs_sub_comm]
    exact le_trans (by nlinarith) (le_abs_self _)
  · show 1 - 2 * a ≤ |1 - a + a * x - a * y|
    exact le_trans (by nlinarith) (le_abs_self _)
  · exact absurd rfl hbc

/-- Distinct construction intervals of level `n + 1` are separated by gaps of length at least
`(1 - 2a) a^n`. -/
theorem le_abs_sub_of_mem_cantorInterval (ha₀ : 0 ≤ a) (ha : a ≤ 1 / 2) {n : ℕ}
    {w v : List Bool} (hw : w.length = n + 1) (hv : v.length = n + 1) (hwv : w ≠ v) {x y : ℝ}
    (hx : x ∈ cantorInterval a w) (hy : y ∈ cantorInterval a v) :
    (1 - 2 * a) * a ^ n ≤ |x - y| := by
  have ha1 : a ≤ 1 := by linarith
  induction n using Nat.strong_induction_on generalizing w v x y with
  | _ n ih =>
    obtain ⟨b, w, rfl⟩ := List.exists_cons_of_length_eq_add_one hw
    obtain ⟨c, v, rfl⟩ := List.exists_cons_of_length_eq_add_one hv
    have hw' : w.length = n := by simpa using hw
    have hv' : v.length = n := by simpa using hv
    rw [cantorInterval_cons] at hx hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    by_cases hbc : b = c
    · subst hbc
      have hwv' : w ≠ v := fun h => hwv (h ▸ rfl)
      cases n with
      | zero =>
        exact absurd ((List.length_eq_zero_iff.1 hw').trans (List.length_eq_zero_iff.1 hv').symm)
          hwv'
      | succ m =>
        have h := ih m (Nat.lt_succ_self m) hw' hv' hwv' hx hy
        have hsub : cantorMap a b x - cantorMap a b y = a * (x - y) := by
          cases b <;> simp only [cantorMap] <;> ring
        rw [hsub, abs_mul, abs_of_nonneg ha₀, pow_succ']
        calc (1 - 2 * a) * (a * a ^ m) = a * ((1 - 2 * a) * a ^ m) := by ring
          _ ≤ a * |x - y| := mul_le_mul_of_nonneg_left h ha₀
    · have h := one_sub_two_mul_le_abs_sub_cantorMap ha₀ hbc
        (cantorInterval_subset_Icc ha₀ ha1 w hx) (cantorInterval_subset_Icc ha₀ ha1 v hy)
      calc (1 - 2 * a) * a ^ n ≤ (1 - 2 * a) * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ ha₀ ha1) (by linarith)
        _ = 1 - 2 * a := mul_one _
        _ ≤ _ := h

/-- Distinct construction intervals of the same level are disjoint. -/
theorem disjoint_cantorInterval (ha₀ : 0 < a) (ha : a < 1 / 2) {w v : List Bool}
    (hlen : w.length = v.length) (hwv : w ≠ v) :
    Disjoint (cantorInterval a w) (cantorInterval a v) := by
  rw [Set.disjoint_left]
  intro x hx hy
  cases hn : w.length with
  | zero =>
    exact hwv ((List.length_eq_zero_iff.1 hn).trans
      (List.length_eq_zero_iff.1 (hlen.symm.trans hn)).symm)
  | succ n =>
    have h := le_abs_sub_of_mem_cantorInterval ha₀.le ha.le hn (hlen.symm.trans hn) hwv hx hy
    rw [sub_self, abs_zero] at h
    have : 0 < (1 - 2 * a) * a ^ n := mul_pos (by linarith) (pow_pos ha₀ n)
    linarith

/-- A point lies in at most one construction interval of each level. -/
theorem eq_of_mem_cantorInterval (ha₀ : 0 < a) (ha : a < 1 / 2) {w v : List Bool}
    (hlen : w.length = v.length) {x : ℝ} (hw : x ∈ cantorInterval a w)
    (hv : x ∈ cantorInterval a v) : w = v := by
  by_contra h
  exact disjoint_left.1 (disjoint_cantorInterval ha₀ ha hlen h) hw hv

end IntervalAPI

/-- For `a = 1/3` the levels are Mathlib's pre-Cantor sets. -/
theorem cantorLevel_one_third (n : ℕ) : cantorLevel (1 / 3) n = preCantorSet n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (fun x : ℝ => 1 / 3 * x) = (· / 3) := by
      funext x
      ring
    have h2 : (fun x : ℝ => 1 - 1 / 3 + 1 / 3 * x) = fun x => (2 + x) / 3 := by
      funext x
      ring
    rw [cantorLevel_succ, preCantorSet_succ, ih, h1, h2]

/-- The middle-third Cantor set is Mathlib's `cantorSet`. -/
theorem symmetricCantorSet_one_third : symmetricCantorSet (1 / 3) = cantorSet := by
  simp only [symmetricCantorSet, cantorSet, cantorLevel_one_third]

variable {a : ℝ}

/-! ## The critical exponent -/

/-- The exponent `log 2 / log (1/a)` is positive for `0 < a < 1`. -/
theorem log_two_div_log_inv_pos (ha₀ : 0 < a) (ha : a < 1) : 0 < Real.log 2 / Real.log a⁻¹ :=
  div_pos (Real.log_pos one_lt_two) (Real.log_pos ((one_lt_inv₀ ha₀).2 ha))

/-- With `s = log 2 / log (1/a)`, `a^s = 1/2`. -/
theorem rpow_log_two_div_log_inv (ha₀ : 0 < a) (ha : a < 1) :
    a ^ (Real.log 2 / Real.log a⁻¹) = 2⁻¹ := by
  have hlog : Real.log a ≠ 0 := (Real.log_neg ha₀ ha).ne
  have h : Real.log a * (Real.log 2 / Real.log a⁻¹) = -Real.log 2 := by
    rw [Real.log_inv]
    field_simp
  rw [Real.rpow_def_of_pos ha₀, h, Real.exp_neg, Real.exp_log two_pos]

/-- With `s = log 2 / log (1/a)`, `(a^n)^s = 2^{-n}`. -/
theorem pow_rpow_log_two_div_log_inv (ha₀ : 0 < a) (ha : a < 1) (n : ℕ) :
    (a ^ n) ^ (Real.log 2 / Real.log a⁻¹) = 2⁻¹ ^ n := by
  rw [← Real.rpow_pow_comm ha₀.le, rpow_log_two_div_log_inv ha₀ ha]

/-! ## The Cantor upper bound -/

/-- The paragraph *The Cantor upper bound*: `𝓗^s(C) ≤ 1`, and `𝓗^t(C) = 0` for `t > s`. -/
theorem cantor_upper_bound (ha₀ : 0 < a) (ha : a < 1 / 2) :
    μH[Real.log 2 / Real.log a⁻¹] (symmetricCantorSet a) ≤ 1 ∧
      ∀ t : ℝ, Real.log 2 / Real.log a⁻¹ < t → μH[t] (symmetricCantorSet a) = 0 := by
  have ha1 : a < 1 := by linarith
  have key : ∀ d : ℝ, μH[d] (symmetricCantorSet a) ≤
      liminf (fun n : ℕ => ENNReal.ofReal ((2 * a ^ d) ^ n)) atTop := by
    intro d
    refine (Measure.hausdorffMeasure_le_liminf_sum (ι := fun n : ℕ => Fin n → Bool) (l := atTop)
      d _ (fun n => ENNReal.ofReal (a ^ n)) ?_
      (fun n (f : Fin n → Bool) => cantorInterval a (List.ofFn f)) ?_ ?_).trans (le_of_eq ?_)
    · simpa using ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one ha₀.le ha1)
    · exact Eventually.of_forall fun n f => by rw [ediam_cantorInterval ha₀.le, List.length_ofFn]
    · refine Eventually.of_forall fun n x hx => ?_
      obtain ⟨w, rfl, hxw⟩ := mem_symmetricCantorSet.1 hx n
      exact mem_iUnion.2 ⟨w.get, by rwa [List.ofFn_get]⟩
    · congr 1
      funext n
      simp only [ediam_cantorInterval ha₀.le, List.length_ofFn, Finset.sum_const, Finset.card_univ,
        Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow,
        Nat.cast_ofNat]
      rw [ENNReal.ofReal_rpow_of_pos (pow_pos ha₀ n), ← Real.rpow_pow_comm ha₀.le, mul_pow,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (p := 2) (by norm_num),
        ENNReal.ofReal_ofNat]
  refine ⟨(key _).trans ?_, fun t ht => ?_⟩
  · rw [rpow_log_two_div_log_inv ha₀ ha1]
    simp
  · have h2 : 2 * a ^ t < 1 := by
      have := Real.rpow_lt_rpow_of_exponent_gt ha₀ ha1 ht
      rw [rpow_log_two_div_log_inv ha₀ ha1] at this
      linarith
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal ((2 * a ^ t) ^ n)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) h2)
    exact nonpos_iff_eq_zero.1 ((key t).trans hlim.liminf_eq.le)

/-! ## The Cantor measure -/

/-- The coding map `ω ↦ ∑ⱼ ωⱼ (1 - a) a^j` from binary sequences to the Cantor set. -/
def cantorCode (a : ℝ) (ω : ℕ → Bool) : ℝ :=
  ∑' j, if ω j then (1 - a) * a ^ j else 0

/-- The terms of the coding series are non-negative. -/
theorem cantorCode_term_nonneg (ha₀ : 0 ≤ a) (ha : a ≤ 1) (ω : ℕ → Bool) (j : ℕ) :
    0 ≤ if ω j then (1 - a) * a ^ j else 0 := by
  split_ifs
  · exact mul_nonneg (by linarith) (pow_nonneg ha₀ j)
  · exact le_rfl

/-- The terms of the coding series are bounded by a geometric series. -/
theorem cantorCode_term_le (ha₀ : 0 ≤ a) (ha : a ≤ 1) (ω : ℕ → Bool) (j : ℕ) :
    (if ω j then (1 - a) * a ^ j else 0) ≤ (1 - a) * a ^ j := by
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (by linarith) (pow_nonneg ha₀ j)

/-- The coding series converges. -/
theorem summable_cantorCode (ha₀ : 0 ≤ a) (ha : a < 1) (ω : ℕ → Bool) :
    Summable fun j => if ω j then (1 - a) * a ^ j else 0 :=
  Summable.of_nonneg_of_le (cantorCode_term_nonneg ha₀ ha.le ω) (cantorCode_term_le ha₀ ha.le ω)
    ((summable_geometric_of_lt_one ha₀ ha).mul_left _)

/-- The coding map takes values in `[0, 1]`. -/
theorem cantorCode_mem_Icc (ha₀ : 0 ≤ a) (ha : a < 1) (ω : ℕ → Bool) :
    cantorCode a ω ∈ Icc (0 : ℝ) 1 := by
  refine ⟨tsum_nonneg (cantorCode_term_nonneg ha₀ ha.le ω), ?_⟩
  calc cantorCode a ω ≤ ∑' j : ℕ, (1 - a) * a ^ j :=
        Summable.tsum_le_tsum (cantorCode_term_le ha₀ ha.le ω) (summable_cantorCode ha₀ ha ω)
          ((summable_geometric_of_lt_one ha₀ ha).mul_left _)
    _ = 1 := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one ha₀ ha, mul_inv_cancel₀ (by linarith)]

/-- The coding map intertwines the shift with the similarity of the first letter. -/
theorem cantorCode_eq (ha₀ : 0 ≤ a) (ha : a < 1) (ω : ℕ → Bool) :
    cantorCode a ω = cantorMap a (ω 0) (cantorCode a fun j => ω (j + 1)) := by
  rw [cantorCode, (summable_cantorCode ha₀ ha ω).tsum_eq_zero_add, cantorCode]
  have h : ∀ j : ℕ, (if ω (j + 1) then (1 - a) * a ^ (j + 1) else 0) =
      a * (if ω (j + 1) then (1 - a) * a ^ j else 0) := by
    intro j
    split_ifs <;> ring
  simp_rw [h, tsum_mul_left]
  cases h0 : ω 0 <;> simp [cantorMap]

/-- The coding map sends the sequences starting with `w` into the construction interval `w`. -/
theorem cantorCode_mem_cantorInterval (ha₀ : 0 ≤ a) (ha : a < 1) (n : ℕ) (ω : ℕ → Bool) :
    cantorCode a ω ∈ cantorInterval a (List.ofFn fun i : Fin n => ω i) := by
  induction n generalizing ω with
  | zero => simpa using cantorCode_mem_Icc ha₀ ha ω
  | succ n ih =>
    rw [List.ofFn_succ, cantorInterval_cons, cantorCode_eq ha₀ ha]
    simp only [Fin.val_zero, Fin.val_succ]
    exact mem_image_of_mem _ (ih fun j => ω (j + 1))

/-- The coding map takes values in the Cantor set. -/
theorem cantorCode_mem_symmetricCantorSet (ha₀ : 0 ≤ a) (ha : a < 1) (ω : ℕ → Bool) :
    cantorCode a ω ∈ symmetricCantorSet a :=
  mem_symmetricCantorSet.2 fun n =>
    ⟨_, List.length_ofFn, cantorCode_mem_cantorInterval ha₀ ha n ω⟩

/-- The coding map is continuous. -/
theorem continuous_cantorCode (ha₀ : 0 ≤ a) (ha : a < 1) : Continuous (cantorCode a) := by
  show Continuous fun ω : ℕ → Bool => ∑' j, if ω j then (1 - a) * a ^ j else 0
  refine continuous_tsum (u := fun j => (1 - a) * a ^ j) (fun j => ?_)
    ((summable_geometric_of_lt_one ha₀ ha).mul_left _) (fun j ω => ?_)
  · exact (continuous_of_discreteTopology
      (f := fun b : Bool => if b then (1 - a) * a ^ j else 0)).comp (continuous_apply j)
  · rw [Real.norm_eq_abs, abs_of_nonneg (cantorCode_term_nonneg ha₀ ha.le ω j)]
    exact cantorCode_term_le ha₀ ha.le ω j

/-- The product of fair coin measures on `ℕ → Bool`. -/
def cantorCoinMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure

/-- The product of fair coin measures is a probability measure. -/
instance : IsProbabilityMeasure cantorCoinMeasure := by
  unfold cantorCoinMeasure
  infer_instance

/-- The sequences starting with a word of length `n` have probability `2^{-n}`. -/
theorem cantorCoinMeasure_pi (w : List Bool) :
    cantorCoinMeasure (Set.pi (Finset.range w.length : Set ℕ) fun i => {w.getD i false}) =
      2⁻¹ ^ w.length := by
  rw [cantorCoinMeasure, Measure.infinitePi_pi _ (fun i _ => measurableSet_singleton _)]
  simp [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

/-- The Cantor measure with ratio `a`: the image of the product of fair coin measures on
`ℕ → Bool` under the coding map `cantorCode a`. -/
def cantorMeasure (a : ℝ) : Measure ℝ :=
  cantorCoinMeasure.map (cantorCode a)

/-- The Cantor measure is a probability measure. -/
theorem isProbabilityMeasure_cantorMeasure (ha₀ : 0 ≤ a) (ha : a < 1) :
    IsProbabilityMeasure (cantorMeasure a) := by
  unfold cantorMeasure
  infer_instance

/-- The Cantor measure of a Borel set is the probability of its preimage under the coding map. -/
theorem cantorMeasure_apply (ha₀ : 0 ≤ a) (ha : a < 1) {E : Set ℝ} (hE : MeasurableSet E) :
    cantorMeasure a E = cantorCoinMeasure (cantorCode a ⁻¹' E) :=
  Measure.map_apply (continuous_cantorCode ha₀ ha).measurable hE

/-- The Cantor measure is concentrated on the Cantor set. -/
theorem cantorMeasure_compl_symmetricCantorSet (ha₀ : 0 ≤ a) (ha : a < 1) :
    cantorMeasure a (symmetricCantorSet a)ᶜ = 0 := by
  have h : cantorCode a ⁻¹' (symmetricCantorSet a)ᶜ = ∅ :=
    eq_empty_of_forall_notMem fun ω hω => hω (cantorCode_mem_symmetricCantorSet ha₀ ha ω)
  rw [cantorMeasure_apply ha₀ ha (isClosed_symmetricCantorSet ha₀).measurableSet.compl, h,
    measure_empty]

/-- The Cantor set has full Cantor measure. -/
theorem cantorMeasure_symmetricCantorSet (ha₀ : 0 ≤ a) (ha : a < 1) :
    cantorMeasure a (symmetricCantorSet a) = 1 := by
  haveI := isProbabilityMeasure_cantorMeasure ha₀ ha
  exact (prob_compl_eq_zero_iff (isClosed_symmetricCantorSet ha₀).measurableSet).1
    (cantorMeasure_compl_symmetricCantorSet ha₀ ha)

/-- A sequence starts with the word `w` if and only if it agrees with `w` letter by letter. -/
theorem ofFn_eq_iff_forall_getD {ω : ℕ → Bool} {w : List Bool} :
    (List.ofFn fun i : Fin w.length => ω i) = w ↔ ∀ i < w.length, ω i = w.getD i false := by
  constructor
  · intro h i hi
    conv_rhs => rw [← h]
    simp [hi]
  · intro h
    refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    rw [List.getElem_ofFn, h i h2, List.getD_eq_getElem _ _ h2]

/-- For `0 < a < 1/2` the coding map sends exactly the sequences starting with `w` into the
construction interval `w`. -/
theorem cantorCode_preimage_cantorInterval (ha₀ : 0 < a) (ha : a < 1 / 2) (w : List Bool) :
    cantorCode a ⁻¹' cantorInterval a w =
      Set.pi (Finset.range w.length : Set ℕ) fun i => {w.getD i false} := by
  ext ω
  simp only [mem_preimage, Set.mem_pi, Finset.coe_range, mem_Iio, mem_singleton_iff]
  have hmem := cantorCode_mem_cantorInterval ha₀.le (by linarith) w.length ω
  rw [← ofFn_eq_iff_forall_getD]
  constructor
  · intro h
    exact eq_of_mem_cantorInterval ha₀ ha (by simp) hmem h
  · intro h
    rwa [h] at hmem

/-- Each construction interval of level `n` has Cantor measure `2^{-n}`. -/
theorem cantorMeasure_cantorInterval (ha₀ : 0 < a) (ha : a < 1 / 2) (w : List Bool) :
    cantorMeasure a (cantorInterval a w) = 2⁻¹ ^ w.length := by
  rw [cantorMeasure_apply ha₀.le (by linarith) (isClosed_cantorInterval ha₀.le w).measurableSet,
    cantorCode_preimage_cantorInterval ha₀ ha, cantorCoinMeasure_pi]

/-- A ball of radius `r` with `2r ≤ (1 - 2a) a^n` meets at most one construction interval of level
`n + 1`, so its Cantor measure is at most `2^{-(n+1)}`. -/
theorem cantorMeasure_ball_le_of_le (ha₀ : 0 < a) (ha : a < 1 / 2) {n : ℕ} (x : ℝ) {r : ℝ}
    (hr : 2 * r ≤ (1 - 2 * a) * a ^ n) : cantorMeasure a (ball x r) ≤ 2⁻¹ ^ (n + 1) := by
  set C := symmetricCantorSet a
  have hC := cantorMeasure_compl_symmetricCantorSet ha₀.le (by linarith : a < 1)
  calc cantorMeasure a (ball x r) ≤ cantorMeasure a (ball x r ∩ C ∪ Cᶜ) :=
        measure_mono fun z hz => by
          by_cases h : z ∈ C
          exacts [Or.inl ⟨hz, h⟩, Or.inr h]
    _ ≤ cantorMeasure a (ball x r ∩ C) + cantorMeasure a Cᶜ := measure_union_le _ _
    _ = cantorMeasure a (ball x r ∩ C) := by rw [hC, add_zero]
    _ ≤ 2⁻¹ ^ (n + 1) := ?_
  rcases (ball x r ∩ C).eq_empty_or_nonempty with h | ⟨y, hyb, hyC⟩
  · simp [h]
  obtain ⟨w, hw, hyw⟩ := mem_symmetricCantorSet.1 hyC (n + 1)
  calc cantorMeasure a (ball x r ∩ C) ≤ cantorMeasure a (cantorInterval a w) := measure_mono ?_
    _ = 2⁻¹ ^ (n + 1) := by rw [cantorMeasure_cantorInterval ha₀ ha, hw]
  rintro z ⟨hzb, hzC⟩
  obtain ⟨v, hv, hzv⟩ := mem_symmetricCantorSet.1 hzC (n + 1)
  by_contra hzw
  have hwv : w ≠ v := by
    rintro rfl
    exact hzw hzv
  have h1 := le_abs_sub_of_mem_cantorInterval ha₀.le ha.le hw hv hwv hyw hzv
  rw [mem_ball, Real.dist_eq] at hyb hzb
  have h2 : |y - z| < 2 * r := by
    calc |y - z| ≤ |y - x| + |x - z| := abs_sub_le y x z
      _ < r + r := by
        rw [abs_sub_comm x z]
        exact add_lt_add hyb hzb
      _ = 2 * r := by ring
  linarith

/-- The ball bound for the Cantor measure: `μ(B(x, r)) ≤ (2 / (1 - 2a))^s r^s` for every centre `x`
and every radius `r > 0`, where `s = log 2 / log (1/a)`. -/
theorem cantorMeasure_ball_le (ha₀ : 0 < a) (ha : a < 1 / 2) (x : ℝ) {r : ℝ} (hr : 0 < r) :
    cantorMeasure a (ball x r) ≤
      ENNReal.ofReal ((2 / (1 - 2 * a)) ^ (Real.log 2 / Real.log a⁻¹)) *
        ENNReal.ofReal r ^ (Real.log 2 / Real.log a⁻¹) := by
  have ha1 : a < 1 := by linarith
  have hs := log_two_div_log_inv_pos ha₀ ha1
  set s := Real.log 2 / Real.log a⁻¹ with hs_def
  have h12a : 0 < 1 - 2 * a := by linarith
  have hc0 : 0 < 2 / (1 - 2 * a) := div_pos two_pos h12a
  haveI := isProbabilityMeasure_cantorMeasure ha₀.le ha1
  rw [ENNReal.ofReal_rpow_of_pos hr, ← ENNReal.ofReal_mul (Real.rpow_nonneg hc0.le s),
    ← Real.mul_rpow hc0.le hr.le]
  have hcr : ∀ t : ℝ, (1 - 2 * a) * t < 2 * r → t ≤ 2 / (1 - 2 * a) * r := by
    intro t ht
    rw [div_mul_eq_mul_div, le_div_iff₀ h12a]
    linarith
  have hex : ∃ k : ℕ, (1 - 2 * a) * a ^ k < 2 * r := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < 2 * r / (1 - 2 * a) by positivity) ha1
    exact ⟨k, by rwa [lt_div_iff₀ h12a, mul_comm] at hk⟩
  classical
  rcases hk : Nat.find hex with _ | m
  · have h := Nat.find_spec hex
    rw [hk, pow_zero, mul_one] at h
    calc cantorMeasure a (ball x r) ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal ((2 / (1 - 2 * a) * r) ^ s) :=
        ENNReal.ofReal_le_ofReal (Real.one_le_rpow (hcr 1 (by linarith)) hs.le)
  · have h1 := Nat.find_spec hex
    rw [hk] at h1
    have h2 : 2 * r ≤ (1 - 2 * a) * a ^ m :=
      not_lt.1 (Nat.find_min hex (by rw [hk]; exact Nat.lt_succ_self m))
    calc cantorMeasure a (ball x r) ≤ 2⁻¹ ^ (m + 1) := cantorMeasure_ball_le_of_le ha₀ ha x h2
      _ = ENNReal.ofReal ((a ^ (m + 1)) ^ s) := by
        rw [pow_rpow_log_two_div_log_inv ha₀ ha1, ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
      _ ≤ ENNReal.ofReal ((2 / (1 - 2 * a) * r) ^ s) :=
        ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow (pow_nonneg ha₀.le _) (hcr _ h1) hs.le)

/-- A ball about a point of a construction interval of level `n` with radius larger than `a^n`
contains that interval, so its Cantor measure is at least `2^{-n}`. -/
theorem cantorMeasure_ball_ge_of_mem (ha₀ : 0 < a) (ha : a < 1 / 2) {w : List Bool} {x r : ℝ}
    (hx : x ∈ cantorInterval a w) (hr : a ^ w.length < r) :
    2⁻¹ ^ w.length ≤ cantorMeasure a (ball x r) := by
  rw [← cantorMeasure_cantorInterval ha₀ ha w]
  exact measure_mono
    ((cantorInterval_subset_closedBall ha₀.le hx).trans (closedBall_subset_ball hr))

/-- The lower ball bound for the Cantor measure: `r^s ≤ 2 μ(B(x, r))` for every `x` in the Cantor
set and `0 < r ≤ 1`, where `s = log 2 / log (1/a)`. -/
theorem rpow_le_two_mul_cantorMeasure_ball (ha₀ : 0 < a) (ha : a < 1 / 2) {x : ℝ}
    (hx : x ∈ symmetricCantorSet a) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ENNReal.ofReal r ^ (Real.log 2 / Real.log a⁻¹) ≤ 2 * cantorMeasure a (ball x r) := by
  have ha1 : a < 1 := by linarith
  have hs := log_two_div_log_inv_pos ha₀ ha1
  set s := Real.log 2 / Real.log a⁻¹ with hs_def
  have hex : ∃ k : ℕ, a ^ k < r := exists_pow_lt_of_lt_one hr ha1
  classical
  rcases hk : Nat.find hex with _ | m
  · have h := Nat.find_spec hex
    rw [hk, pow_zero] at h
    linarith
  · have h1 := Nat.find_spec hex
    rw [hk] at h1
    have h2 : r ≤ a ^ m := not_lt.1 (Nat.find_min hex (by rw [hk]; exact Nat.lt_succ_self m))
    obtain ⟨w, hw, hxw⟩ := mem_symmetricCantorSet.1 hx (m + 1)
    have hmass := cantorMeasure_ball_ge_of_mem ha₀ ha hxw (by rwa [hw])
    rw [hw] at hmass
    have h2inv : (2 : ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top
    calc ENNReal.ofReal r ^ s = ENNReal.ofReal (r ^ s) := ENNReal.ofReal_rpow_of_pos hr
      _ ≤ ENNReal.ofReal ((a ^ m) ^ s) :=
        ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hr.le h2 hs.le)
      _ = 2⁻¹ ^ m := by
        rw [pow_rpow_log_two_div_log_inv ha₀ ha1, ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
      _ = 2 * 2⁻¹ * 2⁻¹ ^ m := by rw [h2inv, one_mul]
      _ = 2 * 2⁻¹ ^ (m + 1) := by ring
      _ ≤ 2 * cantorMeasure a (ball x r) := by gcongr

/-- The paragraph *The Cantor measure and lower bound*: a Borel probability measure on the Cantor
set giving each construction interval of level `n` mass `2^{-n}`, with a power bound on the mass of
balls. -/
theorem exists_cantor_measure (ha₀ : 0 < a) (ha : a < 1 / 2) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (symmetricCantorSet a)ᶜ = 0 ∧
      (∀ w : List Bool, μ (cantorInterval a w) = 2⁻¹ ^ w.length) ∧
      ∃ C : ℝ≥0, ∀ x : ℝ, ∀ r : ℝ, 0 < r →
        μ (ball x r) ≤ C * ENNReal.ofReal r ^ (Real.log 2 / Real.log a⁻¹) :=
  ⟨cantorMeasure a, isProbabilityMeasure_cantorMeasure ha₀.le (by linarith),
    cantorMeasure_compl_symmetricCantorSet ha₀.le (by linarith),
    cantorMeasure_cantorInterval ha₀ ha,
    ((2 / (1 - 2 * a)) ^ (Real.log 2 / Real.log a⁻¹)).toNNReal,
    fun x _ hr => cantorMeasure_ball_le ha₀ ha x hr⟩

/-! ## The Cantor lower bound and dimension -/

/-- The Cantor lower bound: the content at the critical exponent is positive. -/
theorem cantor_lower_bound (ha₀ : 0 < a) (ha : a < 1 / 2) :
    0 < hausdorffContent (Real.log 2 / Real.log a⁻¹) (symmetricCantorSet a) := by
  have ha1 : a < 1 := by linarith
  have hs := log_two_div_log_inv_pos ha₀ ha1
  have hc : 0 < (2 / (1 - 2 * a)) ^ (Real.log 2 / Real.log a⁻¹) :=
    Real.rpow_pos_of_pos (div_pos two_pos (by linarith)) _
  have h := (mass_distribution (cantorMeasure a) hs (Real.toNNReal_pos.2 hc).ne'
    (E := symmetricCantorSet a) fun x _ r hr => cantorMeasure_ball_le ha₀ ha x hr).1
  rw [cantorMeasure_symmetricCantorSet ha₀.le ha1] at h
  exact lt_of_lt_of_le (ENNReal.div_pos one_ne_zero ENNReal.coe_ne_top) h

/-- The Hausdorff dimension of the symmetric Cantor set with ratio `a` is `log 2 / log (1/a)`. -/
theorem dimH_symmetricCantorSet (ha₀ : 0 < a) (ha : a < 1 / 2) :
    dimH (symmetricCantorSet a) = ENNReal.ofReal (Real.log 2 / Real.log a⁻¹) := by
  have hs := log_two_div_log_inv_pos ha₀ (by linarith)
  have hne0 : μH[Real.log 2 / Real.log a⁻¹] (symmetricCantorSet a) ≠ 0 := fun h =>
    (cantor_lower_bound ha₀ ha).ne' ((same_null_sets hs.le _).1 h)
  have hnetop : μH[Real.log 2 / Real.log a⁻¹] (symmetricCantorSet a) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (cantor_upper_bound ha₀ ha).1
  exact dimH_of_hausdorffMeasure_ne_zero_ne_top (d := (Real.log 2 / Real.log a⁻¹).toNNReal)
    (by rwa [Real.coe_toNNReal _ hs.le]) (by rwa [Real.coe_toNNReal _ hs.le])

/-- The middle-third Cantor set with the constants of the notes:
`1/4 ≤ 𝓗^s_∞(𝓒) ≤ 𝓗^s(𝓒) ≤ 1` and `dim_H 𝓒 = log 2 / log 3`. -/
theorem middle_third_cantor :
    (4 : ℝ≥0∞)⁻¹ ≤ hausdorffContent (Real.log 2 / Real.log 3) cantorSet ∧
      hausdorffContent (Real.log 2 / Real.log 3) cantorSet ≤
        μH[Real.log 2 / Real.log 3] cantorSet ∧
      μH[Real.log 2 / Real.log 3] cantorSet ≤ 1 ∧
      dimH cantorSet = ENNReal.ofReal (Real.log 2 / Real.log 3) := by
  rw [← symmetricCantorSet_one_third]
  have h3 : ((1 : ℝ) / 3)⁻¹ = 3 := by norm_num
  have ha₀ : (0 : ℝ) < 1 / 3 := by norm_num
  have ha : (1 : ℝ) / 3 < 1 / 2 := by norm_num
  have hs : 0 < Real.log 2 / Real.log 3 := by
    simpa [h3] using log_two_div_log_inv_pos ha₀ (by norm_num)
  have hub := cantor_upper_bound ha₀ ha
  have hdim := dimH_symmetricCantorSet ha₀ ha
  rw [h3] at hub hdim
  refine ⟨?_, ?_, hub.1, hdim⟩
  · -- the ball bound with constant `6^s = 2 · 2^s ≤ 4`
    have h3s : (3 : ℝ) ^ (Real.log 2 / Real.log 3) = 2 := by
      rw [Real.rpow_def_of_pos (by norm_num), mul_div_cancel₀ _ (Real.log_pos (by norm_num)).ne',
        Real.exp_log two_pos]
    have h2s : (2 : ℝ) ^ (Real.log 2 / Real.log 3) ≤ 2 := by
      have hle : Real.log 2 / Real.log 3 ≤ 1 :=
        (div_le_one (Real.log_pos (by norm_num))).2 (Real.log_le_log two_pos (by norm_num))
      simpa using Real.rpow_le_rpow_of_exponent_le one_le_two hle
    have hball : ∀ x ∈ symmetricCantorSet (1 / 3), ∀ r : ℝ, 0 < r →
        cantorMeasure (1 / 3) (ball x r) ≤
          ((4 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal r ^ (Real.log 2 / Real.log 3) := by
      intro x _ r hr
      have h := cantorMeasure_ball_le ha₀ ha x hr
      rw [h3] at h
      refine h.trans ?_
      gcongr
      rw [show (2 : ℝ) / (1 - 2 * (1 / 3)) = 2 * 3 by norm_num,
        Real.mul_rpow (by norm_num) (by norm_num), h3s]
      calc ENNReal.ofReal (2 ^ (Real.log 2 / Real.log 3) * 2) ≤ ENNReal.ofReal 4 :=
            ENNReal.ofReal_le_ofReal (by linarith)
        _ = ((4 : ℝ≥0) : ℝ≥0∞) := by simp
    have h := (mass_distribution (cantorMeasure (1 / 3)) hs (by norm_num) hball).1
    rw [cantorMeasure_symmetricCantorSet ha₀.le (by norm_num)] at h
    simpa using h
  · rw [hausdorffContent, ← hausdorffMeasureGauge_rpow hs.le]
    exact (hausdorffContentGauge_le_hausdorffDeltaGauge _ 1 _).trans
      (hausdorffDeltaGauge_le_hausdorffMeasureGauge _ one_pos _)

/-- Example 2.23 (`ex:middle-half-cantor`): the middle-half Cantor set `K` has
`0 < 𝓗^{1/2}(K) ≤ 1` and `dim_H K = 1/2`. -/
theorem middle_half_cantor :
    μH[1 / 2] (symmetricCantorSet (1 / 4)) ≤ 1 ∧ 0 < μH[1 / 2] (symmetricCantorSet (1 / 4)) ∧
      dimH (symmetricCantorSet (1 / 4)) = ENNReal.ofReal (1 / 2) := by
  have ha₀ : (0 : ℝ) < 1 / 4 := by norm_num
  have ha : (1 : ℝ) / 4 < 1 / 2 := by norm_num
  have hs : Real.log 2 / Real.log (1 / 4 : ℝ)⁻¹ = 1 / 2 := by
    have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    rw [show ((1 : ℝ) / 4)⁻¹ = 2 ^ 2 by norm_num, Real.log_pow]
    field_simp
    norm_num
  have hub := (cantor_upper_bound ha₀ ha).1
  have hlb := cantor_lower_bound ha₀ ha
  have hdim := dimH_symmetricCantorSet ha₀ ha
  rw [hs] at hub hlb hdim
  exact ⟨hub, pos_iff_ne_zero.2 fun h => hlb.ne' ((same_null_sets (by norm_num) _).1 h), hdim⟩

end GeometricMeasureTheory
