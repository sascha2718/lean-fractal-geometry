module

/-
Rossi's bound `eq:hausdorff_ergodic_lyapunov` of `sec:ledrappier_young_formula` (tex lines 2598
to 2731), after Rossi, J. Math. Anal. Appl. 413 (2014), Theorem 2.2, which the article cites, as
a theorem of the library.

* `System.rossiBound`: the statement `System.RossiBound` of `BoxLike/DimensionFormula.lean`
  holds for every box-like system: `\overline{dim}_H(π_*μ) ≤ min{2, dimL(𝖠, μ)}` for every
  ergodic `μ ∈ M_σ(Σ)`. The covering argument is in `BoxLike/Rossi.lean`
  (`System.essSup_lowerLocalDim_map_proj_le`).
-/
public import BoxLike.DimensionFormula
public import BoxLike.Rossi

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι)

/-- Rossi's theorem `eq:hausdorff_ergodic_lyapunov` (Rossi, J. Math. Anal. Appl. 413 (2014),
Theorem 2.2; tex lines 2598 to 2601): for every ergodic `μ ∈ M_σ(Σ)`,
`\overline{dim}_H(π_*μ) ≤ min{2, dimL(𝖠, μ)}`. The upper Hausdorff dimension is the essential
supremum of the lower pointwise dimension, bounded by `essSup_lowerLocalDim_map_proj_le`. -/
theorem rossiBound : S.RossiBound := fun _ hμ herg =>
  have := hμ
  S.essSup_lowerLocalDim_map_proj_le herg

end System

end BoxLike
