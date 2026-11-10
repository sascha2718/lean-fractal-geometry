module

/-
The core theorem and Rapaport's theorem for homogeneous diagonal systems, with no
hypothesis left: `homogeneousCore` discharges `HomogeneousCore` through Proposition 1.7
(`Exps.proposition`) and the assembly `homogeneousCore_of_prop'`, and
`rapaportDiagonalDimension_homogeneous_holds` is `thm:rapaport` for every homogeneous diagonal
subsystem, the form that case (iii) of `thm:main2` uses.

* `homogeneousCore`: `HomogeneousCore`.
* `rapaportDiagonalDimension_homogeneous_holds`: for `T.IsHomDiag a b` with `|b| < |a|` and both
  axis systems exponentially separated, `dim_H X = min{2, dimaff(X)}`.
* `rapaportDiagonalDimension_holds`: `RapaportDiagonalDimension`, Rapaport's Theorem 1.3 in the
  plane for every proximal diagonal system with exponentially separated axis systems, through
  his Section 7 (`Diagonal.rapaportDiagonalDimension_of_core`).
-/
public import BoxLike.Rapaport.Entropy.Proposition
public import BoxLike.Rapaport.SelfAffine.Main
public import BoxLike.Rapaport.Glue
public import BoxLike.Rapaport.Diagonal.Reduction

@[expose] public section

namespace BoxLike.Rapaport

universe u

/-- The core theorem (Rapaport's Theorem 1.2 in the plane for homogeneous systems in the case of
two full-dimensional projections), with Proposition 1.7 supplied by `Exps.proposition`. -/
theorem homogeneousCore : HomogeneousCore.{u} :=
  homogeneousCore_of_prop' fun χ => χ.proposition

/-- `thm:rapaport` for homogeneous diagonal systems: for `T.IsHomDiag a b` with `|b| < |a|` and
both axis systems exponentially separated, `dim_H X = min{2, dimaff(X)}`. The hypothesis of case
(iii) of `thm:main2`, now a theorem. -/
theorem rapaportDiagonalDimension_homogeneous_holds :
    ∀ {κ : Type u} [Fintype κ] [Nonempty κ] (T : System κ) {a b : ℝ}, T.IsHomDiag a b →
      |b| < |a| → T.AxisExpSeparation 0 → T.AxisExpSeparation 1 →
      dimH T.attractor = ENNReal.ofReal (min 2 T.dimaff) :=
  rapaportDiagonalDimension_homogeneous homogeneousCore

/-- `thm:rapaport`: Rapaport's Theorem 1.3 in the plane (arXiv:2309.03985), the statement
`RapaportDiagonalDimension` of `BoxLike/LiteratureRapaport.lean`, proved. -/
theorem rapaportDiagonalDimension_holds : RapaportDiagonalDimension.{u} :=
  Diagonal.rapaportDiagonalDimension_of_core homogeneousCore

end BoxLike.Rapaport
