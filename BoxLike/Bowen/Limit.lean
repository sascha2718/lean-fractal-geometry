module

/-
The limit step of the proof of Bowen's theorem in `BoxLike/Bowen/`, the existence of an ergodic
Gibbs measure for a Hölder potential on the mixing sub-shift `Σ_Z` that `sec:gibbs_measures`
asserts at tex lines 2382 to 2384 with a citation of Sarig's notes. If for every length `N` some
invariant probability measure carried by `Σ_Z` satisfies the Gibbs bounds up to length `N`, with
constants `P` and `C` that do not depend on `N`, then some invariant probability measure carried
by `Σ_Z` is a Gibbs measure with the same constants. The sets of such measures are weak-star
closed, non-empty and decreasing in the compact space of Borel probability measures on the full
shift, so their intersection is non-empty.

* `continuous_measureReal_of_isClopen`: the mass of a clopen set is a weak-star continuous
  function of the measure.
* `notTransSet`, `isClopen_notTransSet`, `compl_subshift_eq_iUnion`: the complement of `Σ_Z` is
  the countable union of the clopen sets of the points with a forbidden transition at time `k`.
* `isClosed_setOf_carried`: being carried by `Σ_Z` is a weak-star closed condition.
* `isClosed_setOf_gibbsUpTo`: the Gibbs bounds up to length `N` are a weak-star closed
  condition.
* `GibbsUpTo.mono`: the Gibbs bounds up to length `N` give those up to every smaller length.
* `exists_isGibbsPotential_of_forall_gibbsUpTo`: the limit step.
-/
public import BoxLike.Bowen.Defs
public import BoxLike.InvariantMeasures
public import Mathlib.Topology.Algebra.Indicator

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set

/-! ### Clopen sets have weak-star continuous masses -/

section Clopen

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

/-- The mass `ν(U)` of a clopen set `U` of a compact space is a weak-star continuous function of
the Borel probability measure `ν`, since the indicator of `U` is continuous (tex lines 2382 to
2503, the limit step of Bowen's theorem). -/
theorem continuous_measureReal_of_isClopen {U : Set X} (hU : IsClopen U) :
    Continuous fun ν : ProbabilityMeasure X => (ν : Measure X).real U := by
  refine (ProbabilityMeasure.continuous_integral_continuousMap
    (⟨U.indicator 1, hU.continuous_indicator continuous_const⟩ : C(X, ℝ))).congr fun ν => ?_
  exact integral_indicator_one hU.isOpen.measurableSet

end Clopen

/-! ### The weak-star closed conditions -/

section Closed

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {o : ι → ZMod 2}

variable (o) in
/-- The set of the points of the full shift over `ι × ZMod 2` whose symbols at times `k` and
`k + 1` violate the transition rule of the matrix `Z` of `sec:subshift`. -/
def notTransSet (k : ℤ) : Set (ℤ → ι × ZMod 2) := {y | ¬ Trans o (y k) (y (k + 1))}

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The complement of `Σ_Z` is the union of the sets `notTransSet o k` over all times `k ∈ ℤ`. -/
theorem compl_subshift_eq_iUnion : (subshift o)ᶜ = ⋃ k : ℤ, notTransSet o k := by
  ext y
  simp [subshift, notTransSet]

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The set `notTransSet o k` is clopen for the product topology over a discrete alphabet: it is
determined by the symbols at times `k` and `k + 1`. -/
theorem isClopen_notTransSet [TopologicalSpace ι] [DiscreteTopology ι] (k : ℤ) :
    IsClopen (notTransSet o k) := by
  have hc : Continuous fun y : ℤ → ι × ZMod 2 => (y k, y (k + 1)) :=
    (continuous_apply k).prodMk (continuous_apply (k + 1))
  exact (isClopen_discrete {p : (ι × ZMod 2) × (ι × ZMod 2) | ¬ Trans o p.1 p.2}).preimage hc

variable [TopologicalSpace ι] [DiscreteTopology ι]

/-- Being carried by `Σ_Z` is a weak-star closed condition on the Borel probability measures on
the full shift: it is the vanishing of the continuous masses of the clopen sets
`notTransSet o k`, `k ∈ ℤ` (tex lines 2382 to 2384, the limit step of Bowen's theorem). -/
theorem isClosed_setOf_carried :
    IsClosed {ν : ProbabilityMeasure (ℤ → ι × ZMod 2) | (ν : Measure _) (subshift o)ᶜ = 0} := by
  have he : {ν : ProbabilityMeasure (ℤ → ι × ZMod 2) | (ν : Measure _) (subshift o)ᶜ = 0} =
      ⋂ k : ℤ, {ν : ProbabilityMeasure (ℤ → ι × ZMod 2) |
        (ν : Measure _).real (notTransSet o k) = 0} := by
    ext ν
    simp only [mem_ofPred_eq, mem_iInter, compl_subshift_eq_iUnion, measure_iUnion_null_iff]
    exact forall_congr' fun k => (measureReal_eq_zero_iff (measure_ne_top _ _)).symm
  rw [he]
  exact isClosed_iInter fun k =>
    isClosed_eq (continuous_measureReal_of_isClopen (isClopen_notTransSet k)) continuous_const

/-- The Gibbs bounds up to length `N` with constants `P` and `C` are a weak-star closed condition
on the Borel probability measures on the full shift: each bound concerns the continuous mass of
a clopen cylinder (tex lines 2382 to 2384, the limit step of Bowen's theorem). -/
theorem isClosed_setOf_gibbsUpTo (f : (ℤ → ι × ZMod 2) → ℝ) (P C : ℝ) (N : ℕ) :
    IsClosed {ν : ProbabilityMeasure (ℤ → ι × ZMod 2) | GibbsUpTo o f ν P C N} := by
  simp only [GibbsUpTo, ofPred_and, ofPred_forall]
  refine isClosed_const.inter (isClosed_iInter fun y => isClosed_iInter fun _ =>
    isClosed_iInter fun n => isClosed_iInter fun _ => isClosed_iInter fun _ => ?_)
  exact (isClosed_le continuous_const (continuous_measureReal_cylinder _)).inter
    (isClosed_le (continuous_measureReal_cylinder _) continuous_const)

end Closed

/-! ### The limit step -/

section Limit

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {o : ι → ZMod 2} {f : (ℤ → ι × ZMod 2) → ℝ} {ν : Measure (ℤ → ι × ZMod 2)} {P C : ℝ}

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- The Gibbs bounds up to length `N` give the Gibbs bounds up to every length `M ≤ N`. -/
theorem GibbsUpTo.mono {M N : ℕ} (h : GibbsUpTo o f ν P C N) (hMN : M ≤ N) :
    GibbsUpTo o f ν P C M :=
  ⟨h.1, fun y hy n hn hnM => h.2 y hy n hn (hnM.trans hMN)⟩

/-- The limit step of Bowen's theorem (tex lines 2382 to 2384): if for every length `N` some
invariant probability measure carried by `Σ_Z` has the Gibbs bounds up to length `N` with the
constants `P` and `C`, then some invariant probability measure carried by `Σ_Z` is a Gibbs
measure with the constants `P` and `C`. The sets of these measures form a decreasing sequence of
non-empty weak-star closed subsets of the compact space of Borel probability measures. -/
theorem exists_isGibbsPotential_of_forall_gibbsUpTo
    (h : ∀ N : ℕ, ∃ ν : Measure (ℤ → ι × ZMod 2), IsProbabilityMeasure ν ∧
      MeasurePreserving (shift 1) ν ν ∧ ν (subshift o)ᶜ = 0 ∧ GibbsUpTo o f ν P C N) :
    ∃ ν : Measure (ℤ → ι × ZMod 2), IsProbabilityMeasure ν ∧ MeasurePreserving (shift 1) ν ν ∧
      ν (subshift o)ᶜ = 0 ∧ IsGibbsPotential o f ν P C := by
  let : TopologicalSpace ι := ⊥
  have : DiscreteTopology ι := ⟨rfl⟩
  set K : ℕ → Set (ProbabilityMeasure (ℤ → ι × ZMod 2)) := fun N =>
    InvariantMeasures (ι × ZMod 2) ∩
      ({ν | (ν : Measure _) (subshift o)ᶜ = 0} ∩ {ν | GibbsUpTo o f ν P C N}) with hK
  have hclosed : ∀ N, IsClosed (K N) := fun N =>
    isClosed_invariantMeasures.inter
      (isClosed_setOf_carried.inter (isClosed_setOf_gibbsUpTo f P C N))
  have hmono : ∀ N, K (N + 1) ⊆ K N := fun N ν hν =>
    ⟨hν.1, hν.2.1, GibbsUpTo.mono hν.2.2 N.le_succ⟩
  have hne : ∀ N, (K N).Nonempty := fun N => by
    obtain ⟨ν, hp, hinv, hs, hg⟩ := h N
    exact ⟨⟨ν, hp⟩, hinv, hs, hg⟩
  obtain ⟨ν, hν⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hmono hne
    (hclosed 0).isCompact hclosed
  rw [mem_iInter] at hν
  exact ⟨ν, inferInstance, (hν 0).1, (hν 0).2.1,
    isGibbsPotential_iff_forall_gibbsUpTo.2 fun N => (hν N).2.2⟩

end Limit

end BoxLike
