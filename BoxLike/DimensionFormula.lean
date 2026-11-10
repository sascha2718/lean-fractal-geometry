module

/-
Consequences of the full `thm:main_extended` for the Hausdorff dimension of the attractor, and
the statement of Rossi's bound `eq:hausdorff_ergodic_lyapunov` of `sec:ledrappier_young_formula`.

* `System.dimH_attractor_eq_min`: `dimH X = min{2, dimaff(𝖠)}` under the hypotheses of
  `thm:main_extended`, with no restriction on `dimaff(𝖠)`. The article reduces this formula to
  the lower bound `dim π_*μ ≥ min{2, dimL(𝖠, μ)}` in the paragraph after
  `eq:hausdorff_ergodic_lyapunov`.
* `System.dimH_attractor_of_strongOpenSet`: `dimH X = min{2, dimaff(𝖠)}` under the strong open
  set condition, with no measure assumed, since an `s`-equilibrium state exists.
* `System.dimH_attractor_of_two_le`: under the strong open set condition, `dimaff(𝖠) ≥ 2`
  gives `dimH X = 2`; the Bernoulli equilibrium state exists, so no measure is assumed.
* `upperHausdorffDim`: the upper Hausdorff dimension `\overline{dim}_H(μ)` of a measure.
* `System.RossiBound`: the statement of Rossi's theorem, `eq:hausdorff_ergodic_lyapunov`. The
  library proves it (`System.rossiBound` in `BoxLike/RossiBound.lean`); the article cites the
  bound as motivation, and no proof of a numbered result uses it.
* `System.upperHausdorffDim_map_proj_eq`: for the equilibrium state of `thm:main_extended` the
  bound of Rossi holds with equality.
-/
public import BoxLike.AffinityMain
public import BoxLike.BernoulliEquilibrium
public import BoxLike.EquilibriumExistence
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.MainExtended

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

/-- The upper Hausdorff dimension `\overline{dim}_H(μ)`: the essential supremum of the lower
pointwise dimension with respect to `μ`, as in `sec:ledrappier_young_formula`. -/
noncomputable def upperHausdorffDim {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) : ℝ := essSup (lowerLocalDim μ) μ

/-- For a non-zero exact-dimensional measure the upper Hausdorff dimension is `dim μ`. -/
theorem IsExactDim.upperHausdorffDim_eq {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    {μ : Measure X} {d : ℝ} (h : IsExactDim μ d) (hne : μ ≠ 0) : upperHausdorffDim μ = d := by
  have hae : lowerLocalDim μ =ᵐ[μ] fun _ => d := h.mono fun x hx => hx.lowerLocalDim_eq
  have : NeZero μ := ⟨hne⟩
  rw [upperHausdorffDim, essSup_congr_ae hae, essSup_const' d]

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι)

/-- `dimH X = min{2, dimaff(𝖠)}` under the hypotheses of `thm:main_extended`: the lower bound is
the mass distribution principle for the exact-dimensional measure `π_*μ`, the upper bound is
`eq:hausdorff_affinity_upper_bound`. For `dimaff(𝖠) < 2` and the first alternative in the form
`dimaff(X) ≤ 2 - λ_1/λ_2` this is `thm:main2`. -/
theorem dimH_attractor_eq_min (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hjr : JordanRapaportDimension.{u}) (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u})
    (hly : FengLedrappierYoung.{u}) (hlyb : FengLedrappierYoungBar.{u})
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    dimH S.attractor = ENNReal.ofReal (min 2 S.dimaff) :=
  le_antisymm S.dimH_attractor_le
    (S.le_dimH_attractor (S.main_extended_min hms hfk hfjj hjr hfi hfib hly hlyb hrot hprox
      (fun _ => hsep) μ hinv heq hor))

/-- Under the strong open set condition, `dimaff(𝖠) ≥ 2` gives `dimH X = 2`. The equilibrium
state for `s = dimaff(𝖠) ≥ 2` is the Bernoulli measure of `sec:normalisation`, which exists, so
the statement assumes no measure; rotations, proximality and the projective exponential
separation condition are not used. -/
theorem dimH_attractor_of_two_le [Nonempty ι] (hsosc : S.StrongOpenSet) (h2 : 2 ≤ S.dimaff) :
    dimH S.attractor = 2 := by
  have hdim := S.main_extended_ge_two hsosc h2 S.pressure_dimaff
    (bernoulli (S.detWeightMeasure S.dimaff)) (measurePreserving_shift_bernoulli _ 1)
    (S.isEquilibriumState_bernoulli h2)
  have hupper := S.dimH_attractor_le
  rw [min_eq_left h2] at hupper
  have hlower := S.le_dimH_attractor hdim
  have h2' : ENNReal.ofReal 2 = 2 := by simp
  rw [h2'] at hupper hlower
  exact le_antisymm hupper hlower

/-- `dimH X = min{2, dimaff(𝖠)}` for a proximal box-like self-affine set with rotations that
satisfies the projective exponential separation condition and the strong open set condition. No
measure is assumed: an `s`-equilibrium state exists for every `s ≥ 0`
(`System.exists_isEquilibriumState`). -/
theorem dimH_attractor_of_strongOpenSet (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hjr : JordanRapaportDimension.{u}) (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u})
    (hly : FengLedrappierYoung.{u}) (hlyb : FengLedrappierYoungBar.{u})
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal) (hsep : S.ProjExpSeparation)
    (hsosc : S.StrongOpenSet) :
    dimH S.attractor = ENNReal.ofReal (min 2 S.dimaff) := by
  obtain ⟨μ, hprob, hinv, heq⟩ := S.exists_isEquilibriumState S.dimaff_nonneg
  exact S.dimH_attractor_eq_min hms hfk hfjj hjr hfi hfib hly hlyb hrot hprox hsep μ hinv heq
    (Or.inr hsosc)

/-- The statement of Rossi's theorem, `eq:hausdorff_ergodic_lyapunov`: for every ergodic
`μ ∈ M_σ(Σ)`, `\overline{dim}_H(π_*μ) ≤ min{2, dimL(𝖠, μ)}`. The article cites it as motivation,
and no proof of a numbered result depends on it. The library proves it (`rossiBound` in
`BoxLike/RossiBound.lean`, by the covering argument of `BoxLike/Rossi.lean`). -/
def RossiBound : Prop :=
  ∀ μ : Measure (ℤ → ι), IsProbabilityMeasure μ → Ergodic (shift 1) μ →
    upperHausdorffDim (μ.map S.proj) ≤
      min 2 (lyapDim (entropy μ) (S.lyapunov₁ μ) (S.lyapunov₂ μ))

/-- For the equilibrium state of `thm:main_extended` the bound of Rossi,
`eq:hausdorff_ergodic_lyapunov`, holds with equality:
`\overline{dim}_H(π_*μ) = min{2, dimL(𝖠, μ)}`. -/
theorem upperHausdorffDim_map_proj_eq (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hjr : JordanRapaportDimension.{u}) (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u})
    (hly : FengLedrappierYoung.{u}) (hlyb : FengLedrappierYoungBar.{u})
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal) (hsep : S.ProjExpSeparation)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    upperHausdorffDim (μ.map S.proj) =
      min 2 (lyapDim (entropy μ) (S.lyapunov₁ μ) (S.lyapunov₂ μ)) := by
  rw [heq.lyapDim_eq_dimaff hinv]
  exact (S.main_extended_min hms hfk hfjj hjr hfi hfib hly hlyb hrot hprox (fun _ => hsep)
    μ hinv heq hor).upperHausdorffDim_eq (IsProbabilityMeasure.ne_zero _)

end System

end BoxLike
