module

/-
The Gibbs bounds of `thm:irred_eq_state` for box-like tuples with rotations, as the main line
uses them: every invariant `s`-equilibrium state with `0 < s < 2` satisfies the Gibbs bounds.
This module only states the result; the library proves it (`equilibriumGibbs` in
`BoxLike/EquilibriumGibbs.lean`). It is a theorem of the library, not a literature hypothesis: a
numbered result in `Solution` never takes it as a premise.

* `EquilibriumGibbsStatement`: for a box-like tuple with rotations and `0 < s < 2`, every
  invariant `s`-equilibrium state has the Gibbs bounds of `thm:irred_eq_state`.
-/
public import BoxLike.Thermodynamic

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

/-- The Gibbs bounds of `thm:irred_eq_state` for box-like tuples with rotations: for
`0 < s < 2` every invariant `s`-equilibrium state `μ` satisfies
`C⁻¹ exp(-|𝐢| P(𝖠, s)) φ^s(A_𝐢) ≤ μ([𝐢]) ≤ C exp(-|𝐢| P(𝖠, s)) φ^s(A_𝐢)` for all finite words
`𝐢`. The article quotes the bounds from Feng–Käenmäki for irreducible tuples
(`FengKaenmakiGibbs`, which the library proves, `fengKaenmakiGibbs_holds`); a tuple with
rotations need not be irreducible, and the statement does not assume it. -/
def EquilibriumGibbsStatement : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι),
    S.WithRotations → ∀ {s : ℝ}, 0 < s → s < 2 →
    ∀ (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ], MeasurePreserving (shift 1) μ μ →
    S.IsEquilibriumState s μ → S.HasGibbsBounds s μ

end BoxLike
