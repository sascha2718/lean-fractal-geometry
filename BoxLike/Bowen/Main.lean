module

/-
Bowen's theorem for the mixing sub-shift `Σ_Z`, the sentence of `sec:gibbs_measures` at tex
lines 2501 to 2503: "since the sub-shift `Σ_Z` is mixing, for each Hölder continuous potential
`f` there exists a unique ergodic Gibbs measure", which the article cites from Sarig's notes,
Theorem 4.7 and Corollary 4.2. No literature premise is used.

The proof has three steps. The periodic-orbit measures of `BoxLike/Bowen/PeriodicMeasures.lean`
are invariant probability measures carried by `Σ_Z` with the Gibbs bounds up to every prescribed
length, with the constant `P_Z(f)` and a constant `C` that does not depend on the length
(`exists_gibbsUpTo_periodic`). A weak-star limit point is an invariant Gibbs measure
(`exists_isGibbsPotential_of_forall_gibbsUpTo` in `BoxLike/Bowen/Limit.lean`). A Gibbs measure is
ergodic when `Σ_Z` is mixing (`IsGibbsPotential.ergodic_of_isHolder` in
`BoxLike/Bowen/Ergodic.lean`). Uniqueness and the value `P = P_Z(f)` of the constant are
`IsGibbsPotential.eq_of_ergodic_of_isHolder` and `IsGibbsPotential.pressure_eq_of_isHolder`.

* `exists_ergodic_isGibbsPotential_of_forall_gibbsUpTo`: Gibbs bounds up to every length with
  fixed constants give an ergodic Gibbs measure with the same constants.
* `bowenGibbsExistence`: the existence of an ergodic Gibbs probability measure carried by `Σ_Z`
  for every Hölder potential, when both orientations occur.
* `existsUnique_ergodic_isGibbsPotential`: there is exactly one ergodic Gibbs probability measure
  carried by `Σ_Z`, and its constant is `P_Z(f)`.
-/
public import BoxLike.Bowen.Ergodic
public import BoxLike.Bowen.Limit
public import BoxLike.Bowen.PeriodicMeasures

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

/-- The assembly of Bowen's theorem (tex lines 2382 to 2384): if for every length `N` some
invariant probability measure carried by `Σ_Z` has the Gibbs bounds up to length `N` with the
constants `P` and `C`, then, for a Hölder potential and when both orientations occur, some
ergodic probability measure carried by `Σ_Z` is a Gibbs measure with the constants `P` and `C`. -/
theorem exists_ergodic_isGibbsPotential_of_forall_gibbsUpTo {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] {o : ι → ZMod 2} (h0 : ∃ i, o i = 0)
    (h1 : ∃ i, o i = 1) {f : (ℤ → ι × ZMod 2) → ℝ} (hf : IsHolderPotential o f) {P C : ℝ}
    (h : ∀ N : ℕ, ∃ ν : Measure (ℤ → ι × ZMod 2), IsProbabilityMeasure ν ∧
      MeasurePreserving (shift 1) ν ν ∧ ν (subshift o)ᶜ = 0 ∧ GibbsUpTo o f ν P C N) :
    ∃ ν : Measure (ℤ → ι × ZMod 2), IsProbabilityMeasure ν ∧ ν (subshift o)ᶜ = 0 ∧
      Ergodic (shift 1) ν ∧ IsGibbsPotential o f ν P C := by
  obtain ⟨ν, hp, hinv, hs, hg⟩ := exists_isGibbsPotential_of_forall_gibbsUpTo h
  exact ⟨ν, hp, hs, hg.ergodic_of_isHolder hinv hs hf h0 h1, hg⟩

/-- **Bowen's theorem**, existence half (tex lines 2382 to 2384): for a Hölder potential `f` on
the sub-shift `Σ_Z`, which is mixing when both orientations occur, there is an ergodic Gibbs
probability measure carried by `Σ_Z`. The source is Bowen, *Equilibrium states and the ergodic
theory of Anosov diffeomorphisms*, Lecture Notes in Mathematics 470, Chapter 1; the article cites
Sarig's notes. No literature premise is used. -/
theorem bowenGibbsExistence {ι : Type u} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (o : ι → ZMod 2) (h0 : ∃ i, o i = 0) (h1 : ∃ i, o i = 1)
    (f : (ℤ → ι × ZMod 2) → ℝ) (hf : IsHolderPotential o f) :
    ∃ ν : Measure (ℤ → ι × ZMod 2), IsProbabilityMeasure ν ∧ ν (subshift o)ᶜ = 0 ∧
      Ergodic (shift 1) ν ∧ ∃ P C : ℝ, IsGibbsPotential o f ν P C := by
  obtain ⟨C, -, hN⟩ := exists_gibbsUpTo_periodic h0 h1 hf
  obtain ⟨ν, hp, hs, herg, hg⟩ := exists_ergodic_isGibbsPotential_of_forall_gibbsUpTo h0 h1 hf hN
  exact ⟨ν, hp, hs, herg, _, C, hg⟩

/-- **Bowen's theorem** (tex lines 2382 to 2384): for a box-like tuple with rotations and a
Hölder potential `f : Σ_Z → ℝ` there is exactly one ergodic Gibbs probability measure carried by
`Σ_Z`, and its constant is the pressure `P_Z(f)`. Existence is `bowenGibbsExistence`, the value
of the constant is `IsGibbsPotential.pressure_eq_of_isHolder`, and uniqueness is
`IsGibbsPotential.eq_of_ergodic_of_isHolder`. -/
theorem existsUnique_ergodic_isGibbsPotential {ι : Type u} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (o : ι → ZMod 2) (h0 : ∃ i, o i = 0) (h1 : ∃ i, o i = 1)
    (f : (ℤ → ι × ZMod 2) → ℝ) (hf : IsHolderPotential o f) :
    ∃! ν : Measure (ℤ → ι × ZMod 2), IsProbabilityMeasure ν ∧ ν (subshift o)ᶜ = 0 ∧
      Ergodic (shift 1) ν ∧ ∃ C : ℝ, IsGibbsPotential o f ν (pressureZPot o f) C := by
  obtain ⟨ν, hprob, hsupp, herg, P, C, hg⟩ := bowenGibbsExistence o h0 h1 f hf
  have hP : P = pressureZPot o f := hg.pressure_eq_of_isHolder h0 hsupp hf
  subst hP
  refine ⟨ν, ⟨hprob, hsupp, herg, C, hg⟩, ?_⟩
  rintro ν' ⟨hprob', hsupp', herg', C', hg'⟩
  exact hg.eq_of_ergodic_of_isHolder hsupp hsupp' hg' hf herg herg'.toMeasurePreserving

end BoxLike
