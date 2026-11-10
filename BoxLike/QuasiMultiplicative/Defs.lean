module

/-
The shared vocabulary of the proof of Feng–Käenmäki, Proposition 1.2, in
`BoxLike/QuasiMultiplicative/`: `thm:irred_eq_state` (tex lines 2113 to 2127) for every
irreducible tuple of invertible planar matrices. The proof runs through the quasi-multiplicativity
of the norm and the existence of an ergodic Gibbs measure for the potential `‖·‖^q`; this module
fixes the two statements that connect the parts.

* `MatrixTuple.NormQuasiMultiplicative`: there are `m` and `c > 0` such that any two words `𝐢`,
  `𝐣` can be joined by a word `𝐤` of length at most `m` with `‖A_{𝐢𝐤𝐣}‖ ≥ c ‖A_𝐢‖ ‖A_𝐣‖`.
* `NormGibbsExistenceStatement`: a quasi-multiplicative tuple of invertible matrices has, for
  every `q > 0`, an ergodic invariant probability measure on `Σ` with the Gibbs property of the
  potential `‖·‖^q`. It is a result of the library, not a literature hypothesis
  (`normGibbsExistence` in `BoxLike/QuasiMultiplicative/GibbsMeasure.lean`).
-/
public import BoxLike.TupleEquilibriumNorm

@[expose] public section

namespace BoxLike

open MeasureTheory
open scoped Matrix.Norms.L2Operator

universe u

namespace MatrixTuple

variable {ι : Type*}

/-- The norm of the tuple is quasi-multiplicative (Feng–Käenmäki, the step from irreducibility to
the Gibbs property): there are `m : ℕ` and `c > 0` such that for all finite words `𝐢`, `𝐣` some
word `𝐤` of length at most `m` satisfies `c ‖A_𝐢‖ ‖A_𝐣‖ ≤ ‖A_{𝐢𝐤𝐣}‖`. -/
def NormQuasiMultiplicative (A : ι → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ m : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ u v : List ι, ∃ k : List ι, k.length ≤ m ∧
    c * (‖word A u‖ * ‖word A v‖) ≤ ‖word A (u ++ k ++ v)‖

end MatrixTuple

/-- The existence of the Gibbs measure in Feng–Käenmäki, Proposition 1.2 (tex lines 2113 to 2122):
for a non-empty finite alphabet, a quasi-multiplicative tuple of invertible planar matrices and
`q > 0`, some ergodic invariant probability measure on the two-sided shift `Σ = ℤ → ι` has the
Gibbs property of the potential `‖·‖^q`. -/
def NormGibbsExistenceStatement : Prop :=
  ∀ {ι : Type u} [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (A : ι → Matrix (Fin 2) (Fin 2) ℝ), (∀ i, (A i).det ≠ 0) →
    MatrixTuple.NormQuasiMultiplicative A → ∀ {q : ℝ}, 0 < q →
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ Ergodic (shift 1) μ ∧
      MatrixTuple.HasNormGibbs A q μ

end BoxLike
