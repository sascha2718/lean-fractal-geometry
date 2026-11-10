/-
Planar box-like self-affine sets with rotations: finite systems of contracting
affine maps whose linear parts are diagonal or anti-diagonal, with both types
present. The three headline results of Käenmäki, Prokaj, Simon and Troscheit are
stated here with every literature input supplied by the `BoxLike` library.

* `boxLike_coordinateProjections`: Theorem A, the coordinate projections of the
  equilibrium state at the affinity dimension are double-dimensional below the
  threshold `2 - λ₁/λ₂` and exact-dimensional of dimension one from it on.
* `boxLike_dimH_attractor`: Theorem B, `dim_H X = min{2, dimaff X}` without exact
  overlaps, with the exact dimensionality of the projected equilibrium state.
* `boxLike_exactDim_equilibrium`: Theorem 4.16, the projected equilibrium state is
  exact-dimensional of dimension `dimaff X ≤ 2`.

This subject entry point preserves the namespace of the source library.
See README.md for theorem names, hypotheses and provenance.
-/
import BoxLike
import BoxLike.Shmerkin.Bourgain.Cor

namespace FractalGeometry

open MeasureTheory

universe u

variable {ι : Type u} [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : BoxLike.System ι)

/-- Theorem A: under projective exponential separation, each coordinate projection of
`π_*μ` is double-dimensional when `dimaff X < 2 - λ₁/λ₂`, and exact-dimensional of
dimension one otherwise. -/
theorem boxLike_coordinateProjections (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (BoxLike.shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ) (c : ZMod 2) :
    (S.dimaff < 2 - S.lyapunov₁ μ / S.lyapunov₂ μ → BoxLike.IsDoubleDim (S.marginal c μ)) ∧
      (2 - S.lyapunov₁ μ / S.lyapunov₂ μ ≤ S.dimaff →
        BoxLike.IsExactDim (S.marginal c μ) 1) :=
  S.main1_dimaff_all BoxLike.morrisShmerkinLyapunov_holds BoxLike.equilibriumGibbs
    BoxLike.fraserJordanJurgaDecomposition_holds
    (BoxLike.jordanRapaportDimension_of_shmerkin BoxLike.shmerkinLqDimension_holds)
    hrot hprox hsep μ hinv heq c

/-- Theorem B: without exact overlaps, `dim_H X = min{2, dimaff X}` when
`dimaff X ≤ 2 - λ₁/λ₂`, the strong open set condition holds, or projective exponential
separation holds. Under projective exponential separation and either of the first two
conditions, `π_*μ` is exact-dimensional of dimension `dimaff X ≤ 2`. -/
theorem boxLike_dimH_attractor (hrot : S.WithRotations) (hprox : S.Proximal)
    (hfree : S.NoExactOverlaps) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (BoxLike.shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet ∨
      S.ProjExpSeparation) :
    dimH S.attractor = ENNReal.ofReal (min 2 S.dimaff) ∧
      (S.ProjExpSeparation →
        S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet →
        BoxLike.IsExactDim (μ.map S.proj) S.dimaff ∧ S.dimaff ≤ 2) :=
  ⟨S.main2_full_of_library hrot hprox hfree μ hinv heq hor,
    fun hsep hor' => S.main2_furthermore_of_library hrot hprox hsep μ hinv heq hor'⟩

/-- Theorem 4.16: if `h(μ) ≤ -λ₂` or the strong open set condition holds, then `π_*μ` is
exact-dimensional of dimension `dimaff X ≤ 2`. Projective exponential separation is
assumed only when `dimaff X < 2`. -/
theorem boxLike_exactDim_equilibrium (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.dimaff < 2 → S.ProjExpSeparation) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (BoxLike.shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : BoxLike.entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    BoxLike.IsExactDim (μ.map S.proj) S.dimaff ∧ S.dimaff ≤ 2 := by
  have := S.nontrivial_of_withRotations hrot
  exact S.main_extended BoxLike.morrisShmerkinLyapunov_holds BoxLike.equilibriumGibbs
    BoxLike.fraserJordanJurgaDecomposition_holds
    (BoxLike.jordanRapaportDimension_of_shmerkin BoxLike.shmerkinLqDimension_holds)
    BoxLike.fengInfoSum_holds BoxLike.fengInfoSumBar_holds BoxLike.fengLedrappierYoung_holds
    BoxLike.fengLedrappierYoungBar_holds hrot hprox hsep S.dimaff_pos S.pressure_dimaff
    μ hinv heq hor

end FractalGeometry
