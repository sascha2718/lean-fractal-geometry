module

/-
The literal conditional-entropy statement of Proposition 4.3, `thm:entropy_eq_gibbs`.
The entropy-rate equalities are proved by the two-to-one coding in `BoxLike/Main.lean`;
`BoxLike/PastEntropy.lean` separately identifies the conditional entropy given the past
with the entropy rate. This module assembles those results without literature input.

* `System.GibbsDecomposition.zero_entropy_identities`: the two projected conditional-past
  entropies equal the planar conditional-past entropy and its entropy rate.
* `System.GibbsDecomposition.dimEntropy_zero_eq_gibbs`: the literal equalities
  `h_0(μ) = \overline{h}_0(μ_1) = \overline{h}_0(μ_2)`.
-/
public import BoxLike.PastEntropy

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {S : System ι} {s : ℝ} {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]
  {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)}
  [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]

/-- The four conditional-past entropy identities underlying `thm:entropy_eq_gibbs`.
The hypothesis `hdec` is internal proof infrastructure, not an external literature axiom:
for the normalized equilibrium state of the manuscript it is constructed using
`EquilibriumGibbsStatement` (the Gibbs bounds of `thm:irred_eq_state`) and
`FraserJordanJurgaDecomposition` (`thm:eq_state_is_sum`), both proved in the library.
Once it is supplied, no rotations, proximality, range condition on `s`, or further cited
hypothesis is needed. Its factor decomposition gives ergodicity of `μ` and hence the
conullness of `Σ'`. The proof follows the two-to-one coding argument for entropy rates,
then uses the separately proved identification with conditional entropy given the past. -/
theorem GibbsDecomposition.zero_entropy_identities
    (hdec : S.GibbsDecomposition s μ μ₁ μ₂) :
    S.dimEntropy μ 0 = S.dimEntropyBar μ₁ 0 ∧
      S.dimEntropy μ 0 = S.dimEntropyBar μ₂ 0 ∧
      S.dimEntropyBar μ₁ 0 = entropy μ ∧
      S.dimEntropyBar μ₂ 0 = entropy μ := by
  have herg := S.ergodic_of_gibbsDecomposition hdec
  have hinv := herg.toMeasurePreserving
  have h₀ := S.dimEntropy_zero_eq_entropy' μ hinv
    (S.measure_SigmaPrime_compl μ hinv herg)
  have h₁ := (S.dimEntropyBar_zero_eq_entropy' μ₁
    hdec.ergodic₁.toMeasurePreserving hdec.supp₁).trans hdec.entropy_eq₁
  have h₂ := (S.dimEntropyBar_zero_eq_entropy' μ₂
    hdec.ergodic₂.toMeasurePreserving hdec.supp₂).trans hdec.entropy_eq₂
  exact ⟨h₀.trans h₁.symm, h₀.trans h₂.symm, h₁, h₂⟩

/-- Proposition 4.3, `thm:entropy_eq_gibbs`, in its literal conditional-past entropy
vocabulary. `hdec` is obtained from `thm:irred_eq_state` and `thm:eq_state_is_sum` as described
in `GibbsDecomposition.zero_entropy_identities`; this assembly uses no literature.
The proof combines the two-to-one coding argument with the proved past-entropy bridge. -/
theorem GibbsDecomposition.dimEntropy_zero_eq_gibbs
    (hdec : S.GibbsDecomposition s μ μ₁ μ₂) :
    S.dimEntropy μ 0 = S.dimEntropyBar μ₁ 0 ∧
      S.dimEntropy μ 0 = S.dimEntropyBar μ₂ 0 := by
  have h := hdec.zero_entropy_identities
  exact ⟨h.1, h.2.1⟩

end System

end BoxLike
