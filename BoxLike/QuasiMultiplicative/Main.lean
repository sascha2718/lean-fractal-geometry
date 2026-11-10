module

/-
Feng–Käenmäki, Proposition 1.2 (Discrete Contin. Dyn. Syst. 30 (2011)), which the article quotes
as `thm:irred_eq_state` (tex lines 2113 to 2127), from the existence of an ergodic Gibbs measure
for a quasi-multiplicative tuple: `NormGibbsExistenceStatement` implies the literature premise
`FengKaenmakiNormEquilibrium` of `BoxLike/LiteratureFengKaenmaki.lean`.

An irreducible tuple of invertible planar matrices is quasi-multiplicative
(`MatrixTuple.normQuasiMultiplicative_of_irreducible`), so for `q > 0` it has an ergodic
probability measure `μ_q` on `Σ` with the Gibbs property of `‖·‖^q`. Every invariant
`q`-equilibrium state on `Σ` equals `μ_q` (`MatrixTuple.IsNormEquilibrium.eq_of_hasNormGibbs`).
On the one-sided shift `Σ^+`, an invariant `q`-equilibrium state `ν` is `η_*μ` for an invariant
`μ` on `Σ` (`exists_map_eta_eq`), which is a `q`-equilibrium state
(`MatrixTuple.isNormEquilibriumPlus_map_eta_iff`); so `ν = η_*μ_q`, which has the Gibbs property
(`MatrixTuple.hasNormGibbsPlus_map_eta_iff`).

* `MatrixTuple.exists_ergodic_hasNormGibbs_forall_eq`: the two-sided form, an ergodic measure
  with the Gibbs property that every invariant `q`-equilibrium state on `Σ` equals.
* `fengKaenmakiNormEquilibrium_of_normGibbsExistence`: `NormGibbsExistenceStatement` implies
  `FengKaenmakiNormEquilibrium`.
* `fengKaenmakiNormEquilibrium_holds`, `fengKaenmakiGibbs_holds`, `fengKaenmakiUnique_holds`: with
  the Gibbs measure of `normGibbsExistence` (`BoxLike/QuasiMultiplicative/GibbsMeasure.lean`), the
  statement `FengKaenmakiNormEquilibrium` and its box-like specialisations `FengKaenmakiGibbs`
  and `FengKaenmakiUnique` hold. No literature premise is used.
-/
public import BoxLike.LiteratureFengKaenmaki
public import BoxLike.QuasiMultiplicative.GibbsMeasure
public import BoxLike.QuasiMultiplicative.Irreducible
public import BoxLike.QuasiMultiplicative.Uniqueness

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

/-- Feng–Käenmäki, Proposition 1.2 (Discrete Contin. Dyn. Syst. 30 (2011)), quoted as
`thm:irred_eq_state` (tex lines 2113 to 2127), on the two-sided shift `Σ`, from
`NormGibbsExistenceStatement`: for an irreducible tuple of invertible planar matrices and
`q > 0` there is an ergodic probability measure with the Gibbs property of `‖·‖^q`, and every
invariant `q`-equilibrium state of `‖·‖^q` equals it. The tuple is quasi-multiplicative
(`MatrixTuple.normQuasiMultiplicative_of_irreducible`), and uniqueness is
`MatrixTuple.IsNormEquilibrium.eq_of_hasNormGibbs`. -/
theorem MatrixTuple.exists_ergodic_hasNormGibbs_forall_eq (h : NormGibbsExistenceStatement.{u})
    {ι : Type u} [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {A : ι → Matrix (Fin 2) (Fin 2) ℝ} (hA : ∀ i, (A i).det ≠ 0) (hirr : TupleIrreducible A)
    {q : ℝ} (hq : 0 < q) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ Ergodic (shift 1) μ ∧
      MatrixTuple.HasNormGibbs A q μ ∧
      ∀ μ' : Measure (ℤ → ι), IsProbabilityMeasure μ' → MeasurePreserving (shift 1) μ' μ' →
        MatrixTuple.IsNormEquilibrium A q μ' → μ' = μ := by
  obtain ⟨μ, hμ, herg, hG⟩ := h A hA (MatrixTuple.normQuasiMultiplicative_of_irreducible hirr) hq
  exact ⟨μ, hμ, herg, hG, fun μ' _ hinv' heq' => heq'.eq_of_hasNormGibbs hA hq.le hinv' herg hG⟩

/-- `NormGibbsExistenceStatement` implies `FengKaenmakiNormEquilibrium`, Feng–Käenmäki,
Proposition 1.2 (Discrete Contin. Dyn. Syst. 30 (2011)), quoted as `thm:irred_eq_state` (tex
lines 2225 to 2239): for an irreducible tuple of invertible planar matrices and `q > 0`, every
invariant `q`-equilibrium state of `‖·‖^q` on the one-sided shift `Σ^+` has the Gibbs property
and is the only one. An irreducible tuple has a non-empty alphabet, and an invariant measure on
`Σ^+` is `η_*μ` for an invariant measure `μ` on `Σ` with the same equilibrium property, which
equals the ergodic Gibbs measure of `MatrixTuple.exists_ergodic_hasNormGibbs_forall_eq`. -/
theorem fengKaenmakiNormEquilibrium_of_normGibbsExistence (h : NormGibbsExistenceStatement.{u}) :
    FengKaenmakiNormEquilibrium.{u} := by
  intro ι _ _ _ A hA hirr q hq ν _ hν heq
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure ν).some 0⟩
  obtain ⟨μG, hμG, -, hG, huniq⟩ := MatrixTuple.exists_ergodic_hasNormGibbs_forall_eq h hA hirr hq
  have key : ∀ (ν' : Measure (ℕ → ι)) [IsProbabilityMeasure ν'],
      MeasurePreserving shiftPlus ν' ν' → MatrixTuple.IsNormEquilibriumPlus A q ν' →
        ν' = μG.map eta := by
    intro ν' _ hν' heq'
    obtain ⟨μ, hμ, hinv, rfl⟩ := exists_map_eta_eq hν'
    rw [huniq μ hμ hinv ((MatrixTuple.isNormEquilibriumPlus_map_eta_iff μ).1 heq')]
  refine ⟨?_, fun ν' _ hν' heq' => (key ν' hν' heq').trans (key ν hν heq).symm⟩
  rw [key ν hν heq, MatrixTuple.hasNormGibbsPlus_map_eta_iff]
  exact hG

/-- Feng–Käenmäki, Proposition 1.2 (Discrete Contin. Dyn. Syst. 30 (2011)), quoted as
`thm:irred_eq_state` (tex lines 2113 to 2127): the statement `FengKaenmakiNormEquilibrium` holds.
The Gibbs measure is `normGibbsExistence`; no literature premise is used. -/
theorem fengKaenmakiNormEquilibrium_holds : FengKaenmakiNormEquilibrium.{u} :=
  fengKaenmakiNormEquilibrium_of_normGibbsExistence normGibbsExistence

/-- The Gibbs bounds of `thm:irred_eq_state` for irreducible box-like tuples and `0 < s < 2`: the
statement `FengKaenmakiGibbs` holds. -/
theorem fengKaenmakiGibbs_holds : FengKaenmakiGibbs.{u} :=
  fengKaenmakiNormEquilibrium_holds.fengKaenmakiGibbs

/-- The uniqueness part of `thm:irred_eq_state` for irreducible box-like tuples and `0 < s < 2`:
the statement `FengKaenmakiUnique` holds. -/
theorem fengKaenmakiUnique_holds : FengKaenmakiUnique.{u} :=
  fengKaenmakiNormEquilibrium_holds.fengKaenmakiUnique

end BoxLike
