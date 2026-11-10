module

/-
The separation conditions of `sec:box_like_self_affine` and their passage to the second
iterate `Φ^(2)` in `thm:two-block-normalisation`.

* `System.StrongSeparation`, `System.StrongOpenSet`, `System.RectangularOpenSet`: the strong
  separation condition, the strong open set condition and the rectangular open set condition.
* `System.attractor_subset_of_invariant`, `System.strongSeparation_of_invariant`: a non-empty
  compact set `L` with `φ_i(L) ⊆ L` contains `X`, and pairwise disjoint images `φ_i(L)` give
  the strong separation condition.
* `System.StrongSeparation.strongOpenSet`: the strong separation condition implies the strong
  open set condition, with `U` a small open neighbourhood of `X`.
* `System.pairwise_disjoint_sq`: if `φ_i(A) ⊆ A` for all `i` and the first-level images of `A`
  are pairwise disjoint, then the second-level images of `A` are pairwise disjoint.
* `System.StrongSeparation.sq`, `System.StrongOpenSet.sq`: both conditions pass from `Φ` to
  `Φ^(2)`.
-/
public import BoxLike.Attractor

@[expose] public section

namespace BoxLike

open Metric

namespace System

variable {ι : Type*} (S : System ι)

/-- The strong separation condition of `sec:box_like_self_affine`: the sets
`φ_1(X), …, φ_N(X)` are pairwise disjoint. -/
def StrongSeparation : Prop :=
  Pairwise fun i j => Disjoint (S.phi i '' S.attractor) (S.phi j '' S.attractor)

/-- The strong open set condition of `sec:box_like_self_affine`: there is an open set `U` with
`U ∩ X ≠ ∅`, `⋃_i φ_i(U) ⊆ U`, and `φ_i(U) ∩ φ_j(U) = ∅` whenever `i ≠ j`. -/
def StrongOpenSet : Prop :=
  ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (U ∩ S.attractor).Nonempty ∧ (∀ i, S.phi i '' U ⊆ U) ∧
    Pairwise fun i j => Disjoint (S.phi i '' U) (S.phi j '' U)

/-- The rectangular open set condition of `sec:box_like_self_affine`: there is a non-empty open
rectangle `R = (a, b) × (c, d)` with sides parallel to the coordinate axes such that the sets
`φ_1(R), …, φ_N(R)` are pairwise disjoint subsets of `R`. -/
def RectangularOpenSet : Prop :=
  ∃ a b c d : ℝ, a < b ∧ c < d ∧
    (∀ i, S.phi i '' (Set.Ioo a b ×ˢ Set.Ioo c d) ⊆ Set.Ioo a b ×ˢ Set.Ioo c d) ∧
    Pairwise fun i j => Disjoint (S.phi i '' (Set.Ioo a b ×ˢ Set.Ioo c d))
      (S.phi j '' (Set.Ioo a b ×ˢ Set.Ioo c d))

/-- A non-empty compact set `L` with `φ_i(L) ⊆ L` for all `i` contains the self-affine set
`X`. It is the step "`X ⊆ [0,1]²`" of `ex:projection_double_dimensional` and the step
"`X ⊆ R`" of `prop:ssc_no_overlap_not_pesc` (tex line 1398). -/
theorem attractor_subset_of_invariant [Finite ι] {L : Set (ℝ × ℝ)} (hL : IsCompact L)
    (hLne : L.Nonempty) (hLsub : ∀ i, S.phi i '' L ⊆ L) : S.attractor ⊆ L := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  exact hS.subset_of_invariant S.isCompact_attractor S.attractor_eq_iUnion.subset hL hLne hLsub

/-- If a non-empty compact set `L` satisfies `φ_i(L) ⊆ L` for all `i` and the images `φ_i(L)`
are pairwise disjoint, then the strong separation condition holds, as in
`ex:projection_double_dimensional` and `prop:ssc_no_overlap_not_pesc` (tex lines 1398 to
1480). -/
theorem strongSeparation_of_invariant [Finite ι] {L : Set (ℝ × ℝ)} (hL : IsCompact L)
    (hLne : L.Nonempty) (hLsub : ∀ i, S.phi i '' L ⊆ L)
    (hdisj : Pairwise fun i j => Disjoint (S.phi i '' L) (S.phi j '' L)) :
    S.StrongSeparation := fun _ _ hij =>
  (hdisj hij).mono (Set.image_mono (S.attractor_subset_of_invariant hL hLne hLsub))
    (Set.image_mono (S.attractor_subset_of_invariant hL hLne hLsub))

/-- The strong separation condition implies the strong open set condition, as in
`sec:box_like_self_affine`: the compact sets `φ_i(X)` have pairwise disjoint
`ε`-neighbourhoods for some `ε > 0`, and the `ε`-neighbourhood `U` of `X` is feasible, since
`φ_i(U)` lies in the `ε`-neighbourhood of `φ_i(X)`. -/
theorem StrongSeparation.strongOpenSet [Finite ι] [Nonempty ι] (h : S.StrongSeparation) :
    S.StrongOpenSet := by
  have hc : ∀ i, IsCompact (S.phi i '' S.attractor) := fun i =>
    S.isCompact_attractor.image (S.continuous_phi i)
  have hδ : ∀ p : ι × ι, ∃ δ : ℝ, 0 < δ ∧ (p.1 ≠ p.2 →
      Disjoint (thickening δ (S.phi p.1 '' S.attractor))
        (thickening δ (S.phi p.2 '' S.attractor))) := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨1, one_pos, fun hne => (hne hp).elim⟩
    · obtain ⟨δ, hδ, hd⟩ := (h hp).exists_thickenings (hc p.1) (hc p.2).isClosed
      exact ⟨δ, hδ, fun _ => hd⟩
  choose δ hδpos hδdisj using hδ
  obtain ⟨p₀, hp₀⟩ := Finite.exists_min δ
  refine ⟨thickening (δ p₀) S.attractor, isOpen_thickening, ?_, fun i => ?_, fun i j hij => ?_⟩
  · obtain ⟨z, hz⟩ := S.attractor_nonempty
    exact ⟨z, self_subset_thickening (hδpos p₀) _ hz, hz⟩
  · exact (S.image_thickening_subset i _ _).trans
      (thickening_subset_of_subset _ (S.image_attractor_subset i))
  · exact (hδdisj (i, j) hij).mono
      ((S.image_thickening_subset i _ _).trans (thickening_mono (hp₀ (i, j)) _))
      ((S.image_thickening_subset j _ _).trans (thickening_mono (hp₀ (i, j)) _))

/-- The separation step of `thm:two-block-normalisation`: if `φ_i(A) ⊆ A` for all `i` and the
sets `φ_i(A)` are pairwise disjoint, then the sets `φ_i(φ_j(A))` are pairwise disjoint. Two
distinct pairs differ in the first letter, where the first-level images are disjoint, or share
the first letter `i` and differ in the second, where `φ_i` is injective. -/
theorem pairwise_disjoint_sq {A : Set (ℝ × ℝ)} (hA : ∀ i, S.phi i '' A ⊆ A)
    (h : Pairwise fun i j => Disjoint (S.phi i '' A) (S.phi j '' A)) :
    Pairwise fun p q => Disjoint (S.sq.phi p '' A) (S.sq.phi q '' A) := by
  intro p q hpq
  rw [sq_phi_image, sq_phi_image]
  by_cases h1 : p.1 = q.1
  · have h2 : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h1 h2)
    rw [← h1]
    exact (Set.disjoint_image_iff (S.injective_phi p.1)).2 (h h2)
  · exact (h h1).mono (Set.image_mono (hA p.2)) (Set.image_mono (hA q.2))

/-- `thm:two-block-normalisation`, separation part: the strong separation condition passes
from `Φ` to `Φ^(2)`. Disjointness of the first-level images passes to the second-level images
by injectivity. -/
theorem StrongSeparation.sq [Finite ι] (h : S.StrongSeparation) : S.sq.StrongSeparation := by
  unfold StrongSeparation
  rw [attractor_sq]
  exact S.pairwise_disjoint_sq S.image_attractor_subset h

/-- `thm:two-block-normalisation`, separation part: the strong open set condition passes from
`Φ` to `Φ^(2)`. A feasible open set for `Φ` is also feasible for `Φ^(2)`. -/
theorem StrongOpenSet.sq [Finite ι] (h : S.StrongOpenSet) : S.sq.StrongOpenSet := by
  obtain ⟨U, hU, hne, hsub, hdisj⟩ := h
  refine ⟨U, hU, by rwa [attractor_sq], fun p => ?_, S.pairwise_disjoint_sq hsub hdisj⟩
  rw [sq_phi_image]
  exact (Set.image_mono (hsub p.2)).trans (hsub p.1)

end System

end BoxLike
