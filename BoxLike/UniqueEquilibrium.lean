module

/-
The uniqueness part of `thm:irred_eq_state` for box-like tuples with rotations, as the article
uses it in the phrase "the unique `s`-equilibrium state" of `thm:main1`, `thm:main2`,
`thm:eq_state_proj_dim` and `thm:main_extended`. No literature premise is used: the library
proves `thm:irred_eq_state` for tuples with rotations (`BoxLike/EquilibriumGibbs.lean`).

* `System.unique_equilibrium_of_lt_two`: for `0 < s < 2` two invariant `s`-equilibrium states
  coincide, since both are the image `q_*μ_1` of the ergodic `s`-Gibbs measure `μ_1` on `Σ_Z`
  (`System.IsEquilibriumState.eq_map_unCode`).
* `System.unique_equilibrium_of_two_le`: for `s ≥ 2` both are the Bernoulli measure with the
  weights `|det A_i|^{s/2} / ∑_j |det A_j|^{s/2}`; no hypothesis on the tuple is needed.
* `System.unique_equilibrium`: uniqueness for every `s > 0` (`System.unique_of_withRotations`).
-/
public import BoxLike.BernoulliEquilibrium
public import BoxLike.EquilibriumGibbs
public import BoxLike.SigmaMeasure

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {s : ℝ}

/-- `thm:irred_eq_state`, uniqueness, for a box-like tuple with rotations and `0 < s < 2`: two
invariant `s`-equilibrium states coincide, since both are the image `q_*μ_1` of the ergodic
`s`-Gibbs measure `μ_1` for `f_{1,s}` on `Σ_Z` (`System.IsEquilibriumState.eq_map_unCode`). -/
theorem unique_equilibrium_of_lt_two (hrot : S.WithRotations) (hs0 : 0 < s) (hs2 : s < 2)
    (μ μ' : Measure (ℤ → ι)) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hinv : MeasurePreserving (shift 1) μ μ) (hinv' : MeasurePreserving (shift 1) μ' μ')
    (heq : S.IsEquilibriumState s μ) (heq' : S.IsEquilibriumState s μ') : μ = μ' := by
  obtain ⟨ν, hp, hν, herg, hg⟩ := S.exists_isGibbs_potential₁ hrot s
  rw [heq.eq_map_unCode hs0 hs2 hν herg hg hinv, heq'.eq_map_unCode hs0 hs2 hν herg hg hinv']

/-- `thm:irred_eq_state`, uniqueness, for `s ≥ 2` (`sec:normalisation`): every
`s`-equilibrium state is the Bernoulli measure with the weights
`|det A_i|^{s/2} / ∑_j |det A_j|^{s/2}`. -/
theorem unique_equilibrium_of_two_le (hs : 2 ≤ s) (μ μ' : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (hinv : MeasurePreserving (shift 1) μ μ)
    (hinv' : MeasurePreserving (shift 1) μ' μ') (heq : S.IsEquilibriumState s μ)
    (heq' : S.IsEquilibriumState s μ') : μ = μ' :=
  (heq.eq_bernoulli hinv hs).trans (heq'.eq_bernoulli hinv' hs).symm

/-- `thm:irred_eq_state`, uniqueness, for a box-like tuple with rotations and every `s > 0`
(`System.unique_of_withRotations`). -/
theorem unique_equilibrium (hrot : S.WithRotations) (hs0 : 0 < s) (μ μ' : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (hinv : MeasurePreserving (shift 1) μ μ)
    (hinv' : MeasurePreserving (shift 1) μ' μ') (heq : S.IsEquilibriumState s μ)
    (heq' : S.IsEquilibriumState s μ') : μ = μ' :=
  S.unique_of_withRotations hrot hs0 μ μ' hinv hinv' heq heq'

end System

end BoxLike
