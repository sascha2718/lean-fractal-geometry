/-
# Section 2.4: Flows and cuts

The finite tree identity used in the proof of Frostman's lemma: on a finite rooted tree with
capacities, the largest root mass of a flow equals the smallest cost of a cut.

A finite rooted tree is a finite partial order with a bottom element, the root, in which the
ancestors `Set.Iic v` of every vertex form a chain. The children of `v` are the vertices covering
`v`, the leaves are the maximal vertices, and the root-to-leaf paths are the sets `Set.Iic ℓ` for
leaves `ℓ`.

| Notes | Lean declaration | Location |
|---|---|---|
| Finite rooted trees, flows and cuts | `IsRootedTree`, `treeChildren`, `IsFlow`, `IsCut` | here |
| Lemma 2.25 (max flow equals min cut) | `finite_tree_allocation` | here |
| Recursive min-cut value `c` | `treeMinCut`, `IsFlow.le_treeMinCut` | here |
| Weak duality | `IsFlow.apply_bot_le_sum_of_isCut` | here |
-/
import Mathlib

open Set
open scoped BigOperators

noncomputable section

namespace GeometricMeasureTheory

variable {V : Type*} [PartialOrder V] [OrderBot V] [Fintype V]

/-- A finite partial order with a bottom element is a rooted tree if the ancestors of every vertex
form a chain. -/
def IsRootedTree (V : Type*) [PartialOrder V] : Prop :=
  ∀ v : V, IsChain (· ≤ ·) (Iic v)

open Classical in
/-- The children of a vertex: the vertices that cover it. -/
def treeChildren (v : V) : Finset V :=
  Finset.univ.filter fun w => v ⋖ w

/-- A flow with capacities `a`: `0 ≤ m ≤ a`, and at every vertex that is not a leaf the mass is the
sum of the masses of the children. -/
structure IsFlow (a m : V → ℝ) : Prop where
  nonneg : ∀ v, 0 ≤ m v
  le_capacity : ∀ v, m v ≤ a v
  conservation : ∀ v, ¬IsMax v → m v = ∑ w ∈ treeChildren v, m w

/-- A cut: a set of vertices meeting every root-to-leaf path exactly once. -/
def IsCut (D : Finset V) : Prop :=
  ∀ ℓ : V, IsMax ℓ → ∃! v, v ∈ D ∧ v ≤ ℓ

section RootFree

omit [OrderBot V]

/-! ### Children and the tree structure -/

/-- The children of `v` are exactly the vertices covering `v`. -/
@[simp]
theorem mem_treeChildren {v w : V} : w ∈ treeChildren v ↔ v ⋖ w := by
  simp [treeChildren]

/-- A vertex has a child if and only if it is not a leaf. -/
theorem treeChildren_nonempty_iff {v : V} : (treeChildren v).Nonempty ↔ ¬IsMax v := by
  constructor
  · rintro ⟨w, hw⟩ hv
    exact hv.not_lt (mem_treeChildren.1 hw).lt
  · intro hv
    obtain ⟨w, hw⟩ := exists_covBy_of_wellFoundedLT hv
    exact ⟨w, mem_treeChildren.2 hw⟩

namespace IsRootedTree

omit [Fintype V]

/-- In a rooted tree, every vertex strictly below a child `w` of `v` lies below `v`. -/
theorem le_of_lt_of_covBy (hT : IsRootedTree V) {u v w : V} (hvw : v ⋖ w) (huw : u < w) :
    u ≤ v := by
  rcases (hT w).total huw.le hvw.le with h | h
  · exact h
  · rcases h.lt_or_eq with h | h
    · exact (hvw.2 h huw).elim
    · exact h.ge

/-- In a rooted tree, every vertex has at most one parent. -/
theorem eq_of_covBy_of_covBy (hT : IsRootedTree V) {p q w : V} (hp : p ⋖ w) (hq : q ⋖ w) :
    p = q :=
  (hT.le_of_lt_of_covBy hq hp.lt).antisymm (hT.le_of_lt_of_covBy hp hq.lt)

/-- In a rooted tree, two children of `v` lying below a common vertex coincide. -/
theorem eq_of_covBy_of_le (hT : IsRootedTree V) {v w₁ w₂ u : V} (h₁ : v ⋖ w₁) (h₂ : v ⋖ w₂)
    (hu₁ : w₁ ≤ u) (hu₂ : w₂ ≤ u) : w₁ = w₂ := by
  rcases (hT u).total hu₁ hu₂ with h | h
  · rcases h.lt_or_eq with h | h
    · exact (h₂.2 h₁.lt h).elim
    · exact h
  · rcases h.lt_or_eq with h | h
    · exact (h₁.2 h₂.lt h).elim
    · exact h.symm

end IsRootedTree

/-! ### The recursive minimal cut value -/

open Classical in
/-- The minimal cut value of the subtree rooted at `v`, defined recursively from the leaves: it is
`a v` at a leaf and the minimum of `a v` and the sum of the values at the children otherwise. -/
def treeMinCut (a : V → ℝ) : V → ℝ :=
  (wellFounded_gt (α := V)).fix fun v IH =>
    if IsMax v then a v
    else min (a v) (∑ w ∈ (treeChildren v).attach, IH w.1 (mem_treeChildren.1 w.2).lt)

open Classical in
/-- The defining recursion of `treeMinCut`. -/
theorem treeMinCut_eq (a : V → ℝ) (v : V) :
    treeMinCut a v =
      if IsMax v then a v else min (a v) (∑ w ∈ treeChildren v, treeMinCut a w) := by
  rw [treeMinCut, WellFounded.fix_eq]
  simp only [Finset.sum_attach]

/-- At a leaf the minimal cut value is the capacity. -/
theorem treeMinCut_of_isMax {a : V → ℝ} {v : V} (hv : IsMax v) : treeMinCut a v = a v := by
  rw [treeMinCut_eq, if_pos hv]

/-- Away from the leaves the minimal cut value is the minimum of the capacity and the sum of the
values at the children. -/
theorem treeMinCut_of_not_isMax {a : V → ℝ} {v : V} (hv : ¬IsMax v) :
    treeMinCut a v = min (a v) (∑ w ∈ treeChildren v, treeMinCut a w) := by
  rw [treeMinCut_eq, if_neg hv]

/-- The minimal cut value is at most the capacity. -/
theorem treeMinCut_le (a : V → ℝ) (v : V) : treeMinCut a v ≤ a v := by
  by_cases hv : IsMax v
  · rw [treeMinCut_of_isMax hv]
  · rw [treeMinCut_of_not_isMax hv]
    exact min_le_left _ _

/-- Away from the leaves the minimal cut value is at most the sum of the values at the children.
-/
theorem treeMinCut_le_sum {a : V → ℝ} {v : V} (hv : ¬IsMax v) :
    treeMinCut a v ≤ ∑ w ∈ treeChildren v, treeMinCut a w := by
  rw [treeMinCut_of_not_isMax hv]
  exact min_le_right _ _

/-- The minimal cut value of nonnegative capacities is nonnegative. -/
theorem treeMinCut_nonneg {a : V → ℝ} (ha : ∀ v, 0 ≤ a v) (v : V) : 0 ≤ treeMinCut a v := by
  induction v using WellFoundedGT.induction with
  | _ v IH =>
  by_cases hv : IsMax v
  · rw [treeMinCut_of_isMax hv]
    exact ha v
  · rw [treeMinCut_of_not_isMax hv]
    exact le_min (ha v) (Finset.sum_nonneg fun w hw => IH w (mem_treeChildren.1 hw).lt)

/-- Every flow is bounded by the minimal cut value. -/
theorem IsFlow.le_treeMinCut {a m : V → ℝ} (hm : IsFlow a m) (v : V) : m v ≤ treeMinCut a v := by
  induction v using WellFoundedGT.induction with
  | _ v IH =>
  by_cases hv : IsMax v
  · rw [treeMinCut_of_isMax hv]
    exact hm.le_capacity v
  · rw [treeMinCut_of_not_isMax hv]
    refine le_min (hm.le_capacity v) ?_
    rw [hm.conservation v hv]
    exact Finset.sum_le_sum fun w hw => IH w (mem_treeChildren.1 hw).lt

end RootFree

/-! ### Weak duality -/

omit [OrderBot V] in
open Classical in
private theorem IsFlow.le_sum_filter_of_isCut (hT : IsRootedTree V) {a m : V → ℝ}
    (ha : ∀ v, 0 ≤ a v) (hm : IsFlow a m) {D : Finset V} (hD : IsCut D) (v : V)
    (hv : ∀ u ∈ D, ¬u < v) : m v ≤ ∑ u ∈ D.filter (v ≤ ·), a u := by
  induction v using WellFoundedGT.induction with
  | _ v IH =>
  by_cases hvD : v ∈ D
  · calc m v ≤ a v := hm.le_capacity v
      _ ≤ ∑ u ∈ D.filter (v ≤ ·), a u :=
        Finset.single_le_sum (f := a) (fun u _ => ha u) (Finset.mem_filter.2 ⟨hvD, le_rfl⟩)
  have hlt : ∀ u ∈ D, u ≤ v → u < v := fun u huD huv =>
    huv.lt_of_ne (by rintro rfl; exact hvD huD)
  have hmax : ¬IsMax v := by
    intro hmax
    obtain ⟨u, ⟨huD, huv⟩, -⟩ := hD v hmax
    exact hv u huD (hlt u huD huv)
  rw [hm.conservation v hmax]
  calc ∑ w ∈ treeChildren v, m w
      ≤ ∑ w ∈ treeChildren v, ∑ u ∈ D.filter (w ≤ ·), a u := by
        refine Finset.sum_le_sum fun w hw => ?_
        have hvw := mem_treeChildren.1 hw
        exact IH w hvw.lt fun u huD huw =>
          hv u huD (hlt u huD (hT.le_of_lt_of_covBy hvw huw))
    _ = ∑ u ∈ (treeChildren v).biUnion fun w => D.filter (w ≤ ·), a u := by
        refine (Finset.sum_biUnion ?_).symm
        intro w₁ hw₁ w₂ hw₂ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro u hu₁ hu₂
        exact hne (hT.eq_of_covBy_of_le (mem_treeChildren.1 hw₁) (mem_treeChildren.1 hw₂)
          (Finset.mem_filter.1 hu₁).2 (Finset.mem_filter.1 hu₂).2)
    _ ≤ ∑ u ∈ D.filter (v ≤ ·), a u := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun u _ _ => ha u
        intro u hu
        simp only [Finset.mem_biUnion, Finset.mem_filter, mem_treeChildren] at hu ⊢
        obtain ⟨w, hvw, huD, hwu⟩ := hu
        exact ⟨huD, hvw.le.trans hwu⟩

/-- Weak duality: the root mass of a flow is at most the cost of any cut. -/
theorem IsFlow.apply_bot_le_sum_of_isCut (hT : IsRootedTree V) {a m : V → ℝ}
    (ha : ∀ v, 0 ≤ a v) (hm : IsFlow a m) {D : Finset V} (hD : IsCut D) :
    m ⊥ ≤ ∑ v ∈ D, a v := by
  simpa using IsFlow.le_sum_filter_of_isCut hT ha hm hD ⊥ fun u _ => not_lt_bot

/-! ### An optimal cut and an optimal flow -/

omit [OrderBot V] in
open Classical in
/-- Every subtree has a cut whose cost is the minimal cut value: for every vertex `v` there is a set
of vertices above `v` meeting every path from `v` to a leaf exactly once, with cost
`treeMinCut a v`. -/
theorem exists_subtree_cut_sum_eq_treeMinCut (hT : IsRootedTree V) (a : V → ℝ) (v : V) :
    ∃ D : Finset V, (∀ u ∈ D, v ≤ u) ∧ (∀ ℓ, IsMax ℓ → v ≤ ℓ → ∃! u, u ∈ D ∧ u ≤ ℓ) ∧
      ∑ u ∈ D, a u = treeMinCut a v := by
  induction v using WellFoundedGT.induction with
  | _ v IH =>
  by_cases hv : IsMax v ∨ a v ≤ ∑ w ∈ treeChildren v, treeMinCut a w
  · refine ⟨{v}, by simp, fun ℓ _ hvℓ => ⟨v, ⟨Finset.mem_singleton_self v, hvℓ⟩,
      fun u hu => Finset.mem_singleton.1 hu.1⟩, ?_⟩
    rw [Finset.sum_singleton, treeMinCut_eq]
    split_ifs with hmax
    · rfl
    · exact (min_eq_left (hv.resolve_left hmax)).symm
  rw [not_or, not_le] at hv
  obtain ⟨hmax, hlt⟩ := hv
  choose! f hf₁ hf₂ hf₃ using IH
  refine ⟨(treeChildren v).biUnion f, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨w, hw, hu⟩ := Finset.mem_biUnion.1 hu
    have hvw := mem_treeChildren.1 hw
    exact hvw.le.trans (hf₁ w hvw.lt u hu)
  · intro ℓ hℓ hvℓ
    have hvℓ' : v < ℓ := hvℓ.lt_of_ne (by rintro rfl; exact hmax hℓ)
    obtain ⟨w, hvw, hwℓ⟩ := exists_covBy_le_of_lt hvℓ'
    obtain ⟨u, ⟨huD, huℓ⟩, huniq⟩ := hf₂ w hvw.lt ℓ hℓ hwℓ
    refine ⟨u, ⟨Finset.mem_biUnion.2 ⟨w, mem_treeChildren.2 hvw, huD⟩, huℓ⟩, ?_⟩
    rintro u' ⟨hu', hu'ℓ⟩
    obtain ⟨w', hw', hu'D⟩ := Finset.mem_biUnion.1 hu'
    have hvw' := mem_treeChildren.1 hw'
    obtain rfl : w' = w :=
      hT.eq_of_covBy_of_le hvw' hvw ((hf₁ w' hvw'.lt u' hu'D).trans hu'ℓ) hwℓ
    exact huniq u' ⟨hu'D, hu'ℓ⟩
  · rw [Finset.sum_biUnion, treeMinCut_of_not_isMax hmax, min_eq_right hlt.le]
    · exact Finset.sum_congr rfl fun w hw => hf₃ w (mem_treeChildren.1 hw).lt
    · intro w₁ hw₁ w₂ hw₂ hne
      have h₁ := mem_treeChildren.1 hw₁
      have h₂ := mem_treeChildren.1 hw₂
      rw [Function.onFun, Finset.disjoint_left]
      exact fun u hu₁ hu₂ => hne (hT.eq_of_covBy_of_le h₁ h₂ (hf₁ w₁ h₁.lt u hu₁)
        (hf₁ w₂ h₂.lt u hu₂))

/-- There is a cut whose cost is the minimal cut value at the root. -/
theorem exists_isCut_sum_eq_treeMinCut (hT : IsRootedTree V) (a : V → ℝ) :
    ∃ D : Finset V, IsCut D ∧ ∑ v ∈ D, a v = treeMinCut a ⊥ := by
  obtain ⟨D, -, hD, hsum⟩ := exists_subtree_cut_sum_eq_treeMinCut hT a ⊥
  exact ⟨D, fun ℓ hℓ => hD ℓ hℓ bot_le, hsum⟩

open Classical in
/-- There is a flow whose root mass is the minimal cut value at the root. The mass at a child `w`
of `v` is the proportion `treeMinCut a w / ∑ u ∈ treeChildren v, treeMinCut a u` of the mass at
`v`. -/
theorem exists_isFlow_apply_bot_eq_treeMinCut (hT : IsRootedTree V) {a : V → ℝ}
    (ha : ∀ v, 0 ≤ a v) : ∃ m : V → ℝ, IsFlow a m ∧ m ⊥ = treeMinCut a ⊥ := by
  have hc₀ : ∀ v, 0 ≤ treeMinCut a v := treeMinCut_nonneg ha
  have hS₀ : ∀ v, 0 ≤ ∑ w ∈ treeChildren v, treeMinCut a w :=
    fun v => Finset.sum_nonneg fun w _ => hc₀ w
  obtain ⟨ρ, hρ⟩ : ∃ ρ : V → ℝ, ∀ u, ρ u = if h : ∃ p, p ⋖ u then
      treeMinCut a u / ∑ w ∈ treeChildren h.choose, treeMinCut a w else 1 :=
    ⟨fun _ => _, fun _ => rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : V → ℝ,
      ∀ v, m v = treeMinCut a ⊥ * ∏ u ∈ Finset.univ.filter (· ≤ v), ρ u :=
    ⟨fun _ => _, fun _ => rfl⟩
  have hρ_nonneg : ∀ u, 0 ≤ ρ u := by
    intro u
    rw [hρ]
    split_ifs
    · exact div_nonneg (hc₀ u) (hS₀ _)
    · exact zero_le_one
  have hm_nonneg : ∀ v, 0 ≤ m v := fun v => by
    rw [hm]
    exact mul_nonneg (hc₀ ⊥) (Finset.prod_nonneg fun u _ => hρ_nonneg u)
  have hm_bot : m ⊥ = treeMinCut a ⊥ := by
    have hfilter : Finset.univ.filter (· ≤ (⊥ : V)) = {⊥} := by
      ext u
      simp
    have hρ_bot : ρ ⊥ = 1 := by
      rw [hρ, dif_neg]
      rintro ⟨p, hp⟩
      exact not_lt_bot hp.lt
    rw [hm, hfilter, Finset.prod_singleton, hρ_bot, mul_one]
  have hm_child : ∀ {v w : V}, v ⋖ w →
      m w = m v * (treeMinCut a w / ∑ u ∈ treeChildren v, treeMinCut a u) := by
    intro v w hvw
    have hfilter : Finset.univ.filter (· ≤ w) = insert w (Finset.univ.filter (· ≤ v)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hx
        rcases hx.lt_or_eq with hx | hx
        · exact Or.inr (hT.le_of_lt_of_covBy hvw hx)
        · exact Or.inl hx
      · rintro (rfl | hx)
        · exact le_rfl
        · exact hx.trans hvw.le
    have hw : w ∉ Finset.univ.filter (· ≤ v) := by
      simpa using hvw.lt.not_ge
    have hρw : ρ w = treeMinCut a w / ∑ u ∈ treeChildren v, treeMinCut a u := by
      have h : ∃ p, p ⋖ w := ⟨v, hvw⟩
      rw [hρ, dif_pos h, hT.eq_of_covBy_of_covBy h.choose_spec hvw]
    rw [hm, hm, hfilter, Finset.prod_insert hw, hρw]
    ring
  have hm_le : ∀ v, m v ≤ treeMinCut a v := by
    intro w
    induction w using WellFoundedLT.induction with
    | _ w IH =>
    rcases eq_or_ne w ⊥ with rfl | hw
    · rw [hm_bot]
    obtain ⟨v, -, hvw⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hw)
    have hv : m v ≤ ∑ u ∈ treeChildren v, treeMinCut a u :=
      (IH v hvw.lt).trans (treeMinCut_le_sum (not_isMax_of_lt hvw.lt))
    rw [hm_child hvw]
    rcases (hS₀ v).eq_or_lt with h0 | hpos
    · rw [← h0, div_zero, mul_zero]
      exact hc₀ w
    · calc m v * (treeMinCut a w / ∑ u ∈ treeChildren v, treeMinCut a u)
          = m v / (∑ u ∈ treeChildren v, treeMinCut a u) * treeMinCut a w := by ring
        _ ≤ 1 * treeMinCut a w :=
          mul_le_mul_of_nonneg_right ((div_le_one hpos).2 hv) (hc₀ w)
        _ = treeMinCut a w := one_mul _
  refine ⟨m, ⟨hm_nonneg, fun v => (hm_le v).trans (treeMinCut_le a v), fun v hv => ?_⟩, hm_bot⟩
  rw [Finset.sum_congr rfl fun w hw => hm_child (mem_treeChildren.1 hw), ← Finset.mul_sum,
    ← Finset.sum_div]
  rcases (hS₀ v).eq_or_lt with h0 | hpos
  · have hmv : m v = 0 :=
      le_antisymm ((hm_le v).trans ((treeMinCut_le_sum hv).trans h0.ge)) (hm_nonneg v)
    rw [hmv, zero_mul]
  · rw [div_self hpos.ne', mul_one]

/-- Lemma 2.25 (`thm:finite-tree-allocation`): the largest root mass of a flow equals the smallest
cost of a cut. -/
theorem finite_tree_allocation (hT : IsRootedTree V) (a : V → ℝ) (ha : ∀ v, 0 ≤ a v) :
    ∃ m : V → ℝ, IsFlow a m ∧ ∃ D : Finset V, IsCut D ∧ m ⊥ = ∑ v ∈ D, a v ∧
      (∀ m' : V → ℝ, IsFlow a m' → m' ⊥ ≤ m ⊥) ∧
      ∀ D' : Finset V, IsCut D' → ∑ v ∈ D, a v ≤ ∑ v ∈ D', a v := by
  obtain ⟨m, hm, hm_bot⟩ := exists_isFlow_apply_bot_eq_treeMinCut hT ha
  obtain ⟨D, hD, hD_sum⟩ := exists_isCut_sum_eq_treeMinCut hT a
  refine ⟨m, hm, D, hD, hm_bot.trans hD_sum.symm, fun m' hm' => ?_, fun D' hD' => ?_⟩
  · rw [hm_bot, ← hD_sum]
    exact hm'.apply_bot_le_sum_of_isCut hT ha hD
  · rw [hD_sum, ← hm_bot]
    exact hm.apply_bot_le_sum_of_isCut hT ha hD'

end GeometricMeasureTheory
