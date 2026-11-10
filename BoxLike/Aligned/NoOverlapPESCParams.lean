module

/-
The choice of the parameters in the proof of `prop:ssc_no_overlap_not_pesc`
(`sec:exponential_separation`), by the argument of the proof: the tuples
`(r_1, …, r_5, q, u, v, s_1, s_2, s_3)` that are not algebraically independent over `ℚ(λ, t)`
form a countable union of proper algebraic hypersurfaces, which cannot cover the open box of
the parameter intervals.

The eleven parameters are indexed by `Fin 11` in the order
`(r_1, r_2, r_3, r_4, r_5, q, u, v, s_1, s_2, s_3)`, as in `BoxLike.NoOverlapExample`.

* `zeroSet`, `isClosed_zeroSet`, `interior_zeroSet`: the hypersurface `{θ : P(θ) = 0}` of a
  polynomial `P` with coefficients in a subfield `K` of `ℝ`; it is closed, and for `P ≠ 0` it
  has empty interior, since a polynomial vanishing on a box with infinite sides is zero.
* `exceptionalSet`, `algebraicIndependent_iff_not_mem_exceptionalSet`: the forbidden tuples,
  the union of the hypersurfaces of the non-zero polynomials over `K`; a tuple is algebraically
  independent over `K` exactly when it is not forbidden.
* `countable_nonzero_mvPolynomial`: for countable `K` the union is countable.
* `exists_mem_box_not_mem_exceptionalSet`: by the Baire category theorem, a box of non-empty open
  intervals contains a tuple outside the countable union.
* `exists_params_not_mem_exceptionalSet`: parameters in the box of
  `prop:ssc_no_overlap_not_pesc` outside the exceptional set of `ℚ(λ, t)`, hence algebraically
  independent over `ℚ(λ, t)`.
-/
public import BoxLike.NoOverlapExample
public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

@[expose] public section

namespace BoxLike

namespace NoOverlap

open MvPolynomial Cardinal

variable {K : Subfield ℝ}

/-! ### Algebraic hypersurfaces -/

/-- The zero set `{θ : P(θ) = 0}` of a polynomial `P` in eleven variables with coefficients in a
subfield `K` of `ℝ`: an algebraic hypersurface of `ℝ^11` when `P ≠ 0`, as in the proof of
`prop:ssc_no_overlap_not_pesc`. -/
def zeroSet (p : MvPolynomial (Fin 11) K) : Set (Fin 11 → ℝ) := {θ | aeval θ p = 0}

/-- The value `P(θ)` is the evaluation of the polynomial `P` mapped to `ℝ[X_1, …, X_11]`. -/
theorem aeval_eq_eval_map (p : MvPolynomial (Fin 11) K) (θ : Fin 11 → ℝ) :
    aeval θ p = eval θ (map (algebraMap K ℝ) p) := by
  rw [aeval_def, eval_map]

/-- A hypersurface is closed: `θ ↦ P(θ)` is continuous. -/
theorem isClosed_zeroSet (p : MvPolynomial (Fin 11) K) : IsClosed (zeroSet p) := by
  have h : zeroSet p = (fun θ => eval θ (map (algebraMap K ℝ) p)) ⁻¹' {0} := by
    ext θ; simp [zeroSet, aeval_eq_eval_map]
  rw [h]
  exact isClosed_singleton.preimage (MvPolynomial.continuous_eval _)

/-- The hypersurface of a non-zero polynomial is proper: it has empty interior, since a
polynomial over `ℝ` that vanishes on a box with infinite sides is zero. -/
theorem interior_zeroSet {p : MvPolynomial (Fin 11) K} (hp : p ≠ 0) :
    interior (zeroSet p) = ∅ := by
  by_contra hne
  obtain ⟨θ₀, hθ₀⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior θ₀ hθ₀
  have hmap : map (algebraMap K ℝ) p = 0 := by
    refine funext_set (fun k => Metric.ball (θ₀ k) ε)
      (fun k => by rw [Real.ball_eq_Ioo]; exact Set.Ioo_infinite (by linarith)) fun θ hθ => ?_
    rw [← ball_pi θ₀ hε] at hθ
    have h := interior_subset (hball hθ)
    change aeval θ p = 0 at h
    rw [aeval_eq_eval_map] at h
    rw [h, map_zero]
  exact hp (map_injective (algebraMap K ℝ) (algebraMap K ℝ).injective (by rw [hmap, map_zero]))

/-! ### The exceptional set -/

/-- The forbidden tuples of the proof of `prop:ssc_no_overlap_not_pesc`: the union of the
hypersurfaces `{θ : P(θ) = 0}` over the non-zero polynomials `P` with coefficients in `K`. -/
def exceptionalSet (K : Subfield ℝ) : Set (Fin 11 → ℝ) :=
  ⋃ p : {p : MvPolynomial (Fin 11) K // p ≠ 0}, zeroSet p.1

/-- A tuple is algebraically independent over `K` exactly when no non-zero polynomial with
coefficients in `K` vanishes at it, that is, when it lies outside the exceptional set (proof of
`prop:ssc_no_overlap_not_pesc`). -/
theorem algebraicIndependent_iff_not_mem_exceptionalSet (θ : Fin 11 → ℝ) :
    AlgebraicIndependent K θ ↔ θ ∉ exceptionalSet K := by
  rw [algebraicIndependent_iff, exceptionalSet, Set.mem_iUnion]
  constructor
  · rintro h ⟨⟨p, hp⟩, hθ⟩
    exact hp (h p hθ)
  · intro h p hp
    by_contra hne
    exact h ⟨⟨p, hne⟩, hp⟩

/-- For a countable subfield `K` there are countably many polynomials in eleven variables over
`K`, so the exceptional set is a countable union of hypersurfaces. -/
theorem countable_nonzero_mvPolynomial [Countable K] :
    Countable {p : MvPolynomial (Fin 11) K // p ≠ 0} := by
  have : Countable (MvPolynomial (Fin 11) K) := by
    rw [← mk_le_aleph0_iff]
    exact MvPolynomial.cardinalMk_le_max.trans
      (max_le (max_le mk_le_aleph0 mk_le_aleph0) le_rfl)
  infer_instance

/-- A box of non-empty open intervals in `ℝ^11` is not covered by the exceptional set of a
countable subfield `K`: the complements of the countably many proper hypersurfaces are open and
dense, so their intersection is dense by the Baire category theorem and meets the open box. -/
theorem exists_mem_box_not_mem_exceptionalSet [Countable K] (lo hi : Fin 11 → ℝ)
    (h : ∀ k, lo k < hi k) :
    ∃ θ : Fin 11 → ℝ, (∀ k, θ k ∈ Set.Ioo (lo k) (hi k)) ∧ θ ∉ exceptionalSet K := by
  have := countable_nonzero_mvPolynomial (K := K)
  have hdense : Dense (⋂ p : {p : MvPolynomial (Fin 11) K // p ≠ 0}, (zeroSet p.1)ᶜ) :=
    dense_iInter_of_isOpen (fun p => (isClosed_zeroSet p.1).isOpen_compl)
      fun p => interior_eq_empty_iff_dense_compl.1 (interior_zeroSet p.2)
  have hbox : IsOpen (Set.univ.pi fun k => Set.Ioo (lo k) (hi k)) :=
    isOpen_set_pi Set.finite_univ fun k _ => isOpen_Ioo
  have hne : (Set.univ.pi fun k => Set.Ioo (lo k) (hi k)).Nonempty :=
    ⟨fun k => (lo k + hi k) / 2, fun k _ => ⟨by linarith [h k], by linarith [h k]⟩⟩
  obtain ⟨θ, hθbox, hθ⟩ := hdense.inter_open_nonempty _ hbox hne
  refine ⟨θ, fun k => hθbox k (Set.mem_univ k), ?_⟩
  rw [exceptionalSet, Set.mem_iUnion]
  rintro ⟨p, hp⟩
  exact Set.mem_iInter.1 hθ p hp

/-- The choice of the parameters in the proof of `prop:ssc_no_overlap_not_pesc` (tex lines 1354
to 1443): for `0 < λ < 1/3` and `0 < t < λ/(1-λ)` there are `r_1, …, r_5, q, u, v, s_1, s_2, s_3`
in the open intervals of the proof outside the exceptional set of `ℚ(λ, t)`, the subfield of
`ℝ` generated by `λ` and `t`. The forbidden tuples form a countable union of proper algebraic
hypersurfaces, which does not cover the open box. -/
theorem exists_params_not_mem_exceptionalSet {lam t : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 3)
    (ht0 : 0 < t) (ht1 : t < lam / (1 - lam)) :
    ∃ P : Params, P.lam = lam ∧ P.t = t ∧
      P.θ ∉ exceptionalSet (Subfield.closure ({lam, t} : Set ℝ)) := by
  have : Countable (Subfield.closure ({lam, t} : Set ℝ)) :=
    countable_closure (Set.to_countable _)
  obtain ⟨θ, hmem, hθ⟩ := exists_mem_box_not_mem_exceptionalSet
    (K := Subfield.closure ({lam, t} : Set ℝ)) paramLo paramHi paramLo_lt_paramHi
  exact ⟨⟨lam, t, θ, hlam0, hlam1, ht0, ht1, hmem⟩, rfl, rfl, hθ⟩

end NoOverlap

end BoxLike
