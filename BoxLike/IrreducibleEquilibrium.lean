module

/-
`thm:irred_eq_state` for box-like systems: for an irreducible box-like tuple and every `s > 0`
there is a unique `s`-equilibrium state; it is ergodic and has the Gibbs bounds. The inputs
from the literature are the two parts of Feng–Käenmäki, Proposition 1.2, as the library states
them for box-like systems: the Gibbs bounds `FengKaenmakiGibbs` and the uniqueness
`FengKaenmakiUnique`, both for `0 < s < 2`. The library proves both (`fengKaenmakiGibbs_holds`,
`fengKaenmakiUnique_holds` in `BoxLike/QuasiMultiplicative/Main.lean`); that module builds on
this one, so the results here take them as hypotheses, and `Solution.lean` passes the proofs.
Existence is the variational construction of
`BoxLike/EquilibriumExistence.lean`; for `s ≥ 2` uniqueness and the Gibbs bounds are the
determinant calculation of `thm:bernoulli_equilibrium`; ergodicity follows from uniqueness,
since the extreme points of the set of equilibrium states are ergodic
(`System.ergodic_of_unique`). The general irreducible tuple of the article is treated in
`BoxLike/IrreducibleEquilibriumTuple.lean`. For tuples with rotations
`BoxLike/EquilibriumGibbs.lean` proves the proposition with no literature premise.

* `System.Irreducible.nonempty`: an irreducible tuple has a letter.
* `System.unique_of_irreducible`: two invariant `s`-equilibrium states of an irreducible tuple
  coincide, for every `s > 0`.
* `System.IsEquilibriumState.ergodic_of_irreducible`: the equilibrium state is ergodic.
* `System.IsEquilibriumState.hasGibbsBounds_of_irreducible`: the equilibrium state has the
  Gibbs bounds.
* `System.irred_eq_state`: `thm:irred_eq_state` for box-like systems.
-/
public import BoxLike.EquilibriumExistence
public import BoxLike.Literature
public import BoxLike.LiteratureRemarks
public import BoxLike.TupleEquilibriumLarge

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {s : ℝ}

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
variable {S} in
/-- An irreducible tuple has at least one matrix: over the empty alphabet every line is
invariant. -/
theorem Irreducible.nonempty (h : S.Irreducible) : Nonempty ι :=
  TupleIrreducible.nonempty (A := S.mat) h

/-- `thm:irred_eq_state`, uniqueness: two invariant `s`-equilibrium states of an irreducible
box-like tuple coincide, for every `s > 0`. For `0 < s < 2` this is `FengKaenmakiUnique`, which
`fengKaenmakiUnique_holds` proves; for `s ≥ 2` both are the Bernoulli measure of
`thm:bernoulli_equilibrium`. -/
theorem unique_of_irreducible (hfku : FengKaenmakiUnique.{u}) (hirr : S.Irreducible)
    (hs0 : 0 < s) (μ μ' : Measure (ℤ → ι)) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hinv : MeasurePreserving (shift 1) μ μ) (hinv' : MeasurePreserving (shift 1) μ' μ')
    (heq : S.IsEquilibriumState s μ) (heq' : S.IsEquilibriumState s μ') : μ = μ' := by
  rcases lt_or_ge s 2 with hs2 | hs2
  · exact hfku S hirr hs0 hs2 μ μ' hinv hinv' heq heq'
  · exact (heq.eq_bernoulli hinv hs2).trans (heq'.eq_bernoulli hinv' hs2).symm

variable {S}

/-- `thm:irred_eq_state`, ergodicity: the `s`-equilibrium state of an irreducible box-like
tuple is ergodic for every `s > 0`, since it is the only invariant `s`-equilibrium state. -/
theorem IsEquilibriumState.ergodic_of_irreducible (hfku : FengKaenmakiUnique.{u})
    (hirr : S.Irreducible) (hs0 : 0 < s) {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState s μ) :
    Ergodic (shift 1) μ :=
  S.ergodic_of_unique hs0.le hinv heq fun ν hν hνinv hνeq =>
    haveI := hν
    S.unique_of_irreducible hfku hirr hs0 ν μ hνinv hinv hνeq heq

/-- `thm:irred_eq_state`, the Gibbs bounds: the `s`-equilibrium state of an irreducible box-like
tuple satisfies `C⁻¹ exp(-|𝐢| P(𝖠, s)) φ^s(A_𝐢) ≤ μ([𝐢]) ≤ C exp(-|𝐢| P(𝖠, s)) φ^s(A_𝐢)` for
every `s > 0`. For `0 < s < 2` this is `FengKaenmakiGibbs`, which `fengKaenmakiGibbs_holds`
proves; for `s ≥ 2` the equilibrium state is the Bernoulli measure of `thm:bernoulli_equilibrium`
and `C = 1`. -/
theorem IsEquilibriumState.hasGibbsBounds_of_irreducible (hfk : FengKaenmakiGibbs.{u})
    (hirr : S.Irreducible) (hs0 : 0 < s) {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState s μ) :
    S.HasGibbsBounds s μ := by
  rcases lt_or_ge s 2 with hs2 | hs2
  · exact hfk S hirr hs0 hs2 μ hinv heq
  · have := hirr.nonempty
    rw [heq.eq_bernoulli hinv hs2]
    exact S.hasGibbsBounds_bernoulli hs2

variable (S)

/-- `thm:irred_eq_state` for box-like systems: if the box-like tuple `𝖠` is irreducible, then
for each `s > 0` there is an invariant `s`-equilibrium state `μ`, every invariant
`s`-equilibrium state equals `μ`, `μ` is ergodic, and there is a constant `C ≥ 1` with
`C⁻¹ exp(-|𝐢| P(𝖠, s)) φ^s(A_𝐢) ≤ μ([𝐢]) ≤ C exp(-|𝐢| P(𝖠, s)) φ^s(A_𝐢)` for all finite words
`𝐢`. The inputs from the literature are `FengKaenmakiGibbs` and `FengKaenmakiUnique`, used for
`0 < s < 2` only; the library proves both (`fengKaenmakiGibbs_holds`,
`fengKaenmakiUnique_holds`). -/
theorem irred_eq_state (hfk : FengKaenmakiGibbs.{u}) (hfku : FengKaenmakiUnique.{u})
    (hirr : S.Irreducible) (hs0 : 0 < s) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
      S.IsEquilibriumState s μ ∧
      (∀ ν : Measure (ℤ → ι), IsProbabilityMeasure ν → MeasurePreserving (shift 1) ν ν →
        S.IsEquilibriumState s ν → ν = μ) ∧
      Ergodic (shift 1) μ ∧ S.HasGibbsBounds s μ := by
  have := hirr.nonempty
  obtain ⟨μ, hprob, hinv, heq⟩ := S.exists_isEquilibriumState hs0.le
  refine ⟨μ, hprob, hinv, heq, fun ν hν hνinv hνeq => ?_, heq.ergodic_of_irreducible hfku hirr hs0
    hinv, heq.hasGibbsBounds_of_irreducible hfk hirr hs0 hinv⟩
  exact S.unique_of_irreducible hfku hirr hs0 ν μ hνinv hinv hνeq heq

end System

end BoxLike
