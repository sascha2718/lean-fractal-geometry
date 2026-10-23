/-
# Section 3: Covering lemmas

The opening part of Section 3 of the notes, *Covering theorems, densities, and regular sets*: the
finite Vitali covering lemma and the `5r`-covering lemma. Balls carry a specified centre and radius,
so families of balls are indexed families `i ↦ (x i, r i)`.

| Notes | Lean declaration | Location |
|---|---|---|
| Lemma 3.1 (finite Vitali covering lemma) | `finite_vitali` | here |
| Lemma 3.2 (`5r`-covering lemma) | `five_r`, `five_r_closedBall`; the selection is `Vitali.exists_disjoint_subfamily_covering_enlargement` | here; `Mathlib/MeasureTheory/Covering/Vitali.lean` |
| Disjoint families of open sets in a separable space are countable | `Set.PairwiseDisjoint.countable_of_isOpen` | `Mathlib/Topology/Bases.lean` |
-/
import Mathlib

open Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

variable {X : Type*} [PseudoMetricSpace X]

/-- Lemma 3.1 (finite Vitali covering lemma, `thm:finite-vitali`): a finite family of closed balls
has a pairwise disjoint subfamily whose threefold enlargements cover the family. -/
theorem finite_vitali {ι : Type*} (t : Finset ι) (x : ι → X) (r : ι → ℝ) :
    ∃ u ⊆ t, (u : Set ι).PairwiseDisjoint (fun i => closedBall (x i) (r i)) ∧
      ⋃ i ∈ t, closedBall (x i) (r i) ⊆ ⋃ j ∈ u, closedBall (x j) (3 * r j) := by
  classical
  induction t using Finset.strongInduction with
  | H t ih =>
  rcases t.eq_empty_or_nonempty with rfl | ht
  · exact ⟨∅, subset_refl _, by simp, by simp⟩
  obtain ⟨i₀, hi₀, hmax⟩ := t.exists_max_image r ht
  set t' := (t.erase i₀).filter
    (fun i => Disjoint (closedBall (x i) (r i)) (closedBall (x i₀) (r i₀)))
  have ht' : t' ⊂ t := (Finset.filter_subset _ _).trans_ssubset (Finset.erase_ssubset hi₀)
  obtain ⟨u', hu't', hu'disj, hu'cov⟩ := ih t' ht'
  refine ⟨insert i₀ u', Finset.insert_subset hi₀ (hu't'.trans ht'.subset), ?_, ?_⟩
  · rw [Finset.coe_insert]
    refine hu'disj.insert fun j hj _ => ?_
    exact (Finset.mem_filter.1 (hu't' hj)).2.symm
  · intro z hz
    simp only [mem_iUnion, exists_prop] at hz ⊢
    obtain ⟨i, hi, hzi⟩ := hz
    by_cases hii₀ : i = i₀
    · subst hii₀
      refine ⟨i, Finset.mem_insert_self _ _, ?_⟩
      have h0 : 0 ≤ r i := dist_nonneg.trans (mem_closedBall.1 hzi)
      exact closedBall_subset_closedBall (by linarith) hzi
    by_cases hdisj : Disjoint (closedBall (x i) (r i)) (closedBall (x i₀) (r i₀))
    · have hit' : i ∈ t' := Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨hii₀, hi⟩, hdisj⟩
      have := hu'cov (mem_biUnion (Finset.mem_coe.2 hit') hzi)
      simp only [mem_iUnion, exists_prop] at this
      obtain ⟨j, hj, hzj⟩ := this
      exact ⟨j, Finset.mem_insert_of_mem hj, hzj⟩
    · obtain ⟨w, hwi, hwi₀⟩ := not_disjoint_iff.1 hdisj
      refine ⟨i₀, Finset.mem_insert_self _ _, ?_⟩
      rw [mem_closedBall] at hzi hwi hwi₀ ⊢
      have := hmax i hi
      calc dist z (x i₀) ≤ dist z (x i) + dist (x i) w + dist w (x i₀) := dist_triangle4 _ _ _ _
        _ ≤ r i + r i + r i₀ := by rw [dist_comm] at hwi; linarith
        _ ≤ 3 * r i₀ := by linarith

/-- Lemma 3.2 (the `5r`-covering lemma, `thm:five-r`), for open balls: a family of balls with
positive radii bounded above has a pairwise disjoint subfamily such that every ball of the family
meets a selected ball of at least half its radius; in particular the fivefold enlargements of the
selected balls cover the family. -/
theorem five_r {ι : Type*} (t : Set ι) (x : ι → X) (r : ι → ℝ) (hr : ∀ i ∈ t, 0 < r i) {R : ℝ}
    (hR : ∀ i ∈ t, r i ≤ R) :
    ∃ u ⊆ t, u.PairwiseDisjoint (fun i => ball (x i) (r i)) ∧
      (∀ i ∈ t, ∃ j ∈ u, (ball (x i) (r i) ∩ ball (x j) (r j)).Nonempty ∧ r i ≤ 2 * r j) ∧
      ⋃ i ∈ t, ball (x i) (r i) ⊆ ⋃ j ∈ u, ball (x j) (5 * r j) := by
  obtain ⟨u, hut, hdisj, hmeet⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun i => ball (x i) (r i)) t r 2 one_lt_two (fun i hi => (hr i hi).le) R hR
    (fun i hi => nonempty_ball.2 (hr i hi))
  refine ⟨u, hut, hdisj, hmeet, ?_⟩
  intro z hz
  simp only [mem_iUnion, exists_prop] at hz ⊢
  obtain ⟨i, hi, hzi⟩ := hz
  obtain ⟨j, hj, ⟨w, hwi, hwj⟩, hrij⟩ := hmeet i hi
  refine ⟨j, hj, ?_⟩
  rw [mem_ball] at hzi hwi hwj ⊢
  calc dist z (x j) ≤ dist z (x i) + dist (x i) w + dist w (x j) := dist_triangle4 _ _ _ _
    _ < r i + r i + r j := by rw [dist_comm] at hwi; linarith
    _ ≤ 5 * r j := by linarith

/-- Lemma 3.2 (the `5r`-covering lemma, `thm:five-r`), for closed balls. -/
theorem five_r_closedBall {ι : Type*} (t : Set ι) (x : ι → X) (r : ι → ℝ)
    (hr : ∀ i ∈ t, 0 < r i) {R : ℝ} (hR : ∀ i ∈ t, r i ≤ R) :
    ∃ u ⊆ t, u.PairwiseDisjoint (fun i => closedBall (x i) (r i)) ∧
      (∀ i ∈ t, ∃ j ∈ u,
        (closedBall (x i) (r i) ∩ closedBall (x j) (r j)).Nonempty ∧ r i ≤ 2 * r j) ∧
      ⋃ i ∈ t, closedBall (x i) (r i) ⊆ ⋃ j ∈ u, closedBall (x j) (5 * r j) := by
  obtain ⟨u, hut, hdisj, hmeet⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun i => closedBall (x i) (r i)) t r 2 one_lt_two (fun i hi => (hr i hi).le) R hR
    (fun i hi => nonempty_closedBall.2 (hr i hi).le)
  refine ⟨u, hut, hdisj, hmeet, ?_⟩
  intro z hz
  simp only [mem_iUnion, exists_prop] at hz ⊢
  obtain ⟨i, hi, hzi⟩ := hz
  obtain ⟨j, hj, ⟨w, hwi, hwj⟩, hrij⟩ := hmeet i hi
  refine ⟨j, hj, ?_⟩
  rw [mem_closedBall] at hzi hwi hwj ⊢
  calc dist z (x j) ≤ dist z (x i) + dist (x i) w + dist w (x j) := dist_triangle4 _ _ _ _
    _ ≤ r i + r i + r j := by rw [dist_comm] at hwi; linarith
    _ ≤ 5 * r j := by linarith

/-! In a separable space the selected family is countable:
`Set.PairwiseDisjoint.countable_of_isOpen`. -/

example [TopologicalSpace.SeparableSpace X] {ι : Type*} {u : Set ι} (x : ι → X) (r : ι → ℝ)
    (hr : ∀ i ∈ u, 0 < r i) (hu : u.PairwiseDisjoint fun i => ball (x i) (r i)) :
    u.Countable :=
  hu.countable_of_isOpen (fun _ _ => isOpen_ball) fun i hi => nonempty_ball.2 (hr i hi)

end GeometricMeasureTheory
