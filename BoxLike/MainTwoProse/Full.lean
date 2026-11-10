module

/-
`thm:main2` in full: the dimension formula `\dim_H X = min{2, dimaff(X)}` under any of the three
conditions `it:main2_threshold`, `it:main2_sosc`, `it:main2_pesc`, and the furthermore clause,
"if `it:main2_pesc` holds together with `it:main2_threshold` or `it:main2_sosc`, then `π_*μ` is
exact-dimensional with `dim(π_*μ) = dimaff(X) ≤ 2`", along the prose of
`sec:dimension_result_proof`: "Suppose that `it:main2_pesc` holds together with
`it:main2_threshold` or `it:main2_sosc`. Under `it:main2_threshold`, we have `s < 2`, and
`eq:diml_min2`, `eq:simple_lyapunov` give `h_0(μ) ≤ -λ_2(𝖠, μ)`. In either case, the hypotheses
of `thm:main_extended` are satisfied, and hence `dim(π_*μ) = dimaff(X) ≤ 2`."

Cases `it:main2_threshold` and `it:main2_sosc` are `System.main2_prose` of
`BoxLike/MainTwoProse/Endpoint.lean`, where `dimaff(X) ≤ 2`
(`System.dimaff_le_two_of_main2_hypotheses`); case `it:main2_pesc` is `System.main2_pesc` of
`BoxLike/MainTwoProse/ProjExpBranch.lean`; the furthermore clause is `thm:main_extended`
(`System.main_extended_min`, the form `dim(π_*μ) = min{2, dimaff(X)}` of `System.main_extended`,
which concludes `dim(π_*μ) = dimaff(X) ≤ 2`).

* `System.main2_full`: `thm:main2`, the dimension formula, with the statements
  `ShannonMcMillanBreimanStatement`, `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`,
  `FraserJordanJurgaDecomposition`, `FengLedrappierYoung` and `KittleKoglerDimension`, which
  the library proves, and Rapaport's theorem, which the library proves as well
  (`Rapaport.rapaportDiagonalDimension_holds`).
* `System.main2_full_of_library`: the same with the library theorems plugged in, with no
  literature hypothesis.
* `System.main2_furthermore`: the furthermore clause, with the hypotheses of
  `System.main_extended_min`.
* `System.main2_furthermore_of_library`: the furthermore clause with the library theorems
  plugged in, without any literature hypothesis.
-/
public import BoxLike.FengIdentity
public import BoxLike.FengIdentityBar
public import BoxLike.FengLedrappierYoung
public import BoxLike.JordanRapaport
public import BoxLike.KittleKogler
public import BoxLike.MainExtended
public import BoxLike.MainTwoProse.Endpoint
public import BoxLike.MainTwoProse.ProjExpBranch
public import BoxLike.Shmerkin
public import BoxLike.Support.IntroductionClaims

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
  [Nonempty ι]

/-! ### The dimension formula -/

/-- `thm:main2`, the dimension formula. Let `X` be a proximal box-like self-affine set with
rotations whose projective system has no exact overlaps, and let `μ` be an `s`-equilibrium
state for `s = dimaff(X)`. Then `\dim_H X = min{2, dimaff(X)}` whenever
`dimaff(X) ≤ 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)` (`it:main2_threshold`), or `X` satisfies the strong open
set condition (`it:main2_sosc`), or `X` satisfies the projective exponential separation
condition (`it:main2_pesc`). Under `it:main2_threshold` or `it:main2_sosc` one has
`dimaff(X) ≤ 2` and `\dim_H X = dimaff(X)` by `main2_prose`; under `it:main2_pesc` the formula
is `main2_pesc`.
Depends on: `ShannonMcMillanBreimanStatement`,
`MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`,
`FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem main2_full (hsmb : ShannonMcMillanBreimanStatement.{u}) (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hly : FengLedrappierYoung.{u}) (hkk : KittleKoglerDimension.{u}) (hrot : S.WithRotations)
    (hprox : S.Proximal) (hfree : S.NoExactOverlaps) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet ∨
      S.ProjExpSeparation) :
    dimH S.attractor = ENNReal.ofReal (min 2 S.dimaff) := by
  rcases hor with h | h | h
  · rw [min_eq_right (S.dimaff_le_two_of_main2_hypotheses μ hinv (Or.inl h))]
    exact S.main2_prose hsmb hms hfk hfjj hly hkk hrot hprox hfree μ hinv heq (Or.inl h)
  · rw [min_eq_right (S.dimaff_le_two_of_main2_hypotheses μ hinv (Or.inr h))]
    exact S.main2_prose hsmb hms hfk hfjj hly hkk hrot hprox hfree μ hinv heq (Or.inr h)
  · exact S.main2_pesc hsmb hms hfk hfjj hrot hprox h

/-- `thm:main2`, the dimension formula, with the library theorems `shannonMcMillanBreiman`,
`morrisShmerkinLyapunov_holds`, `equilibriumGibbs`, `fraserJordanJurgaDecomposition_holds`,
`fengLedrappierYoung_holds` and `kittleKoglerDimension_holds` plugged in, with no literature
hypothesis. -/
theorem main2_full_of_library (hrot : S.WithRotations)
    (hprox : S.Proximal) (hfree : S.NoExactOverlaps) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet ∨
      S.ProjExpSeparation) :
    dimH S.attractor = ENNReal.ofReal (min 2 S.dimaff) :=
  S.main2_full shannonMcMillanBreiman morrisShmerkinLyapunov_holds equilibriumGibbs
    fraserJordanJurgaDecomposition_holds fengLedrappierYoung_holds kittleKoglerDimension_holds
    hrot hprox hfree μ hinv heq hor

/-! ### The furthermore clause -/

/-- `thm:main2`, the furthermore clause: if `it:main2_pesc` holds together with
`it:main2_threshold` or `it:main2_sosc`, then `π_*μ` is exact-dimensional with
`dim(π_*μ) = dimaff(X) ≤ 2`. The hypotheses force `dimaff(X) ≤ 2`
(`dimaff_le_two_of_main2_hypotheses`); under `it:main2_threshold` one has `dimaff(X) < 2`, and
`eq:diml_min2` with `eq:simple_lyapunov` turn the threshold into `h_0(μ) ≤ -λ_2(𝖠, μ)`
(`entropy_le_iff`); then `thm:main_extended` (`main_extended_min`) gives
`dim(π_*μ) = min{2, dimaff(X)} = dimaff(X)`.
Depends on: `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`,
`FraserJordanJurgaDecomposition`, `JordanRapaportDimension`, `FengInfoSum`, `FengInfoSumBar`,
`FengLedrappierYoung`, `FengLedrappierYoungBar`. -/
theorem main2_furthermore (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hjr : JordanRapaportDimension.{u}) (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u})
    (hly : FengLedrappierYoung.{u}) (hlyb : FengLedrappierYoungBar.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal) (hsep : S.ProjExpSeparation)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    IsExactDim (μ.map S.proj) S.dimaff ∧ S.dimaff ≤ 2 := by
  have h2 := S.dimaff_le_two_of_main2_hypotheses μ hinv hor
  -- the threshold in the entropy form
  have hor' : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet := by
    rcases hor with h | h
    · left
      have := S.nontrivial_of_withRotations hrot
      have hs2 := S.dimaff_lt_two_of_le_threshold μ hinv h
      have hl := S.simple_lyapunov hms hrot hprox S.dimaff_pos hs2 μ hinv heq
      have hl1 := S.lyapunov₁_neg hinv
      have henergy : entropy μ + energy (S.lyapunov₁ μ) (S.lyapunov₂ μ) S.dimaff = 0 := by
        rw [← heq.pressure_eq hinv S.dimaff_nonneg, S.pressure_dimaff]
      exact (entropy_le_iff hl hl1 hs2 henergy).2 h
    · exact Or.inr h
  refine ⟨?_, h2⟩
  have := S.main_extended_min hms hfk hfjj hjr hfi hfib hly hlyb hrot hprox (fun _ => hsep)
    μ hinv heq hor'
  rwa [min_eq_right h2] at this

/-- `thm:main2`, the furthermore clause, with the library theorems plugged in: no literature
hypothesis remains. -/
theorem main2_furthermore_of_library (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    IsExactDim (μ.map S.proj) S.dimaff ∧ S.dimaff ≤ 2 :=
  S.main2_furthermore morrisShmerkinLyapunov_holds equilibriumGibbs
    fraserJordanJurgaDecomposition_holds
    (jordanRapaportDimension_of_shmerkin shmerkinLqDimension_holds) fengInfoSum_holds
    fengInfoSumBar_holds fengLedrappierYoung_holds fengLedrappierYoungBar_holds hrot hprox hsep
    μ hinv heq hor

end System

end BoxLike
