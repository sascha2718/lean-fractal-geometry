module

/-
`thm:irred_eq_state` at the article's scope: existence, uniqueness, ergodicity and the Gibbs
bounds of the `s`-equilibrium state of every irreducible tuple of invertible planar matrices
and every `s > 0`, from the theorem of Feng and Käenmäki that the article quotes
(`FengKaenmakiNormEquilibrium`, `BoxLike/LiteratureFengKaenmaki.lean`) for `0 < s < 2` and from
the determinant calculation for `s ≥ 2`. The library proves the statement
`FengKaenmakiNormEquilibrium` (`fengKaenmakiNormEquilibrium_holds` in
`BoxLike/QuasiMultiplicative/Main.lean`); the endpoint takes it as a hypothesis, and
`Solution.lean` passes the proof.

* `MatrixTuple.irred_eq_state_of_fengKaenmaki`: `thm:irred_eq_state`.
-/
public import BoxLike.LiteratureFengKaenmaki

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

/-! ### `thm:irred_eq_state` for every irreducible tuple -/

/-- `thm:irred_eq_state`, from the statement `FengKaenmakiNormEquilibrium` of Feng–Käenmäki,
Proposition 1.2, which the library proves (`fengKaenmakiNormEquilibrium_holds`). If
`𝖠 = (A_1, …, A_N)` is an irreducible tuple of invertible planar matrices, then for each `s > 0`
there is an invariant `s`-equilibrium state `μ`, every invariant `s`-equilibrium state equals
`μ`, `μ` is ergodic, and there is `C ≥ 1` with
`C⁻¹ exp(-|𝐢| P(𝖠, s)) φ^s(A_𝐢) ≤ μ([𝐢]) ≤ C exp(-|𝐢| P(𝖠, s)) φ^s(A_𝐢)` for all finite words.
Existence is the variational construction (`MatrixTuple.exists_isEquilibriumState`); for
`0 < s < 2` uniqueness and the Gibbs bounds come from the statement through the reductions of
tex lines 2123 to 2127 (`FengKaenmakiNormEquilibrium.svf`); for `s ≥ 2` they are the determinant
calculation (`MatrixTuple.irred_eq_state_of_two_le`); ergodicity follows from uniqueness
(`MatrixTuple.ergodic_of_unique`). -/
theorem MatrixTuple.irred_eq_state_of_fengKaenmaki (h : FengKaenmakiNormEquilibrium.{u})
    {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (hA : ∀ i, (A i).det ≠ 0) (hirr : TupleIrreducible A)
    {s : ℝ} (hs0 : 0 < s) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
      MatrixTuple.IsEquilibriumState A s μ ∧
      (∀ ν : Measure (ℤ → ι), IsProbabilityMeasure ν → MeasurePreserving (shift 1) ν ν →
        MatrixTuple.IsEquilibriumState A s ν → ν = μ) ∧
      Ergodic (shift 1) μ ∧ MatrixTuple.HasGibbsBounds A s μ := by
  have := hirr.nonempty
  rcases lt_or_ge s 2 with hs2 | hs2
  · obtain ⟨μ, hprob, hinv, heq⟩ := MatrixTuple.exists_isEquilibriumState hA hs0.le
    obtain ⟨hG, hU⟩ := h.svf hA hirr hs0 hs2 hinv heq
    exact ⟨μ, hprob, hinv, heq, hU,
      MatrixTuple.ergodic_of_unique hA hs0.le hinv heq hU, hG⟩
  · exact MatrixTuple.irred_eq_state_of_two_le hA hs2

end BoxLike
