module

/-
The open question `q:coincident-projection-dimensions` of the introduction, recorded as a
proposition. The library neither proves nor refutes it.

* `CoincidentProjectionDimensionsQuestion`: can the coordinate projections of `π_*μ`, for the
  `s`-equilibrium state `μ` of a proximal box-like self-affine set with rotations, be
  exact-dimensional, with their two Gibbs components of equal dimension, when
  `s = dimaff(X) < 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)` and the projective system has no exact overlaps?
-/
public import BoxLike.AffinityDim
public import BoxLike.MeasureDim
public import BoxLike.Proximal
public import BoxLike.Separation
public import BoxLike.Thermodynamic

@[expose] public section

namespace BoxLike

open MeasureTheory

/-- `q:coincident-projection-dimensions`, an open question of the article, as the proposition
that an affirmative instance exists: a proximal box-like system with rotations over `N + 1` maps
whose projective system has no exact overlaps (with rotations there are at least two maps,
so indexing them by `Fin (N + 1)` loses nothing), an `s`-equilibrium state `μ` for
`s = dimaff(X) < 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)` with `s`-Gibbs measures `μ_1`, `μ_2`
(`thm:eq_state_is_sum`), and `d` such that both Gibbs components `\overline{π}_*μ_1` and
`\overline{π}_*μ_2` of `sec:dimension_of_projections` and both coordinate projections of
`π_*μ`, the marginals `S.marginal c μ`, are exact-dimensional of dimension `d`. The Gibbs
measures of `sec:gibbs_measures` belong to the normalised tuple; a proximal tuple becomes normalised after passing to the second iterate
(`thm:two-block-normalisation`), which keeps the attractor and the coordinate projections. -/
def CoincidentProjectionDimensionsQuestion : Prop :=
  ∃ (N : ℕ) (S : System (Fin (N + 1))) (μ : Measure (ℤ → Fin (N + 1)))
    (μ₁ μ₂ : Measure (ℤ → Fin (N + 1) × ZMod 2)) (d : ℝ),
    IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
    S.WithRotations ∧ S.Proximal ∧ S.NoExactOverlaps ∧
    S.IsEquilibriumState S.dimaff μ ∧ S.dimaff < 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∧
    S.GibbsDecomposition S.dimaff μ μ₁ μ₂ ∧
    IsExactDim (μ₁.map S.projBar) d ∧ IsExactDim (μ₂.map S.projBar) d ∧
    ∀ c : ZMod 2, IsExactDim (S.marginal c μ) d

end BoxLike
