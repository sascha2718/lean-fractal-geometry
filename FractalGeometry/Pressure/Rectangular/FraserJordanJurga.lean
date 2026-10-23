import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.Pressure.Rectangular.Decomposition
import FractalGeometry.Pressure.Rectangular.DecompositionStatement
import FractalGeometry.Pressure.Rectangular.Defs
import FractalGeometry.Pressure.Rectangular.FlippedGibbs
import FractalGeometry.Pressure.Rectangular.FraserJordanJurgaStatement
import FractalGeometry.Pressure.Rectangular.LiftedExponents
import FractalGeometry.Pressure.Rectangular.LiftedGibbs
import FractalGeometry.Pressure.Rectangular.LyapunovStatement
import FractalGeometry.Pressure.Rectangular.Matrices
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.Symbolic.ParityFlip
import FractalGeometry.Symbolic.ParityShift
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

/-!
Jonathan M. Fraser, Thomas Jordan and Natalia Jurga, "Dimensions of equilibrium
measures on a class of planar self-affine sets", Journal of Fractal Geometry 7(1)
(2020), 87–111. DOI: 10.4171/JFG/85; arXiv:1706.06833v2, Section 1.4,
Lemma 1.3 and Corollaries 1.5–1.6.

The decomposition into Gibbs measures on the parity shift and the two Lyapunov
integral identities are proved here for the positive-coefficient setting of the
paper. `PositiveRatios` is an explicit hypothesis. Pressure equalities, strictness
of the exponent gap, and the paper's later dimension formula are not asserted by
this endpoint.
-/

namespace FractalGeometry

open MeasureTheory

universe u

namespace RectangularIFS

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : RectangularIFS ι) {s : ℝ}

variable [hpos : S.PositiveRatios]
include hpos

theorem gibbsDecomposition_map_unCode (μ₁ : Measure (ℤ → ι × ZMod 2))
    [IsProbabilityMeasure μ₁] (herg : Ergodic (shift 1) μ₁) (hsupp : μ₁ (subshift S.o)ᶜ = 0)
    (hg : IsGibbs S.o (S.potential₁ s) μ₁)
    (hl₁ : S.lyapunov₁ (μ₁.map unCode) = S.lyapBar μ₁)
    (hl₂ : S.lyapunov₂ (μ₁.map unCode) = S.lyapBar (μ₁.map flipAxis)) :
    S.GibbsDecomposition s (μ₁.map unCode) μ₁ (μ₁.map flipAxis) where
  positive := inferInstance
  prob₁ := inferInstance
  prob₂ := inferInstance
  ergodic₁ := herg
  ergodic₂ := ergodic_map_flipAxis herg
  supp₁ := hsupp
  supp₂ := map_flipAxis_subshift_compl hsupp
  gibbs₁ := hg
  gibbs₂ := S.isGibbs_potential₂_map_flipAxis hg
  eq_tau := map_unCode_eq_tau hsupp
  eq_omega := map_unCode_eq_omega hsupp
  eq₁ := map_unCode_eq₁ hsupp
  eq₂ := map_unCode_eq₂ hsupp
  lyapunov₁_eq := hl₁
  lyapunov₂_eq := hl₂

theorem eq_map_unCode_of_hasGibbsBounds (hs0 : 0 < s) (hs2 : s < 2)
    (μ₁ : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure μ₁] (herg : Ergodic (shift 1) μ₁)
    (hsupp : μ₁ (subshift S.o)ᶜ = 0) (hg : IsGibbs S.o (S.potential₁ s) μ₁)
    {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ)
    (hgμ : S.HasGibbsBounds s μ) : μ = μ₁.map unCode :=
  S.eq_of_hasGibbsBounds hμ (ergodic_map_unCode herg) hgμ
    (S.hasGibbsBounds_map_unCode hs0 hs2 hsupp hg)

theorem exists_gibbsDecomposition_of_lyapunov (hrot : S.HasBothOrientations) (hs0 : 0 < s)
    (hs2 : s < 2)
    (hlyap : ∀ (μ₁ : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure μ₁],
      Ergodic (shift 1) μ₁ → μ₁ (subshift S.o)ᶜ = 0 → IsGibbs S.o (S.potential₁ s) μ₁ →
      S.lyapunov₁ (μ₁.map unCode) = S.lyapBar μ₁ ∧
        S.lyapunov₂ (μ₁.map unCode) = S.lyapBar (μ₁.map flipAxis))
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ)
    (hgμ : S.HasGibbsBounds s μ) :
    ∃ μ₁ μ₂ : Measure (ℤ → ι × ZMod 2), S.GibbsDecomposition s μ μ₁ μ₂ := by
  obtain ⟨μ₁, hp, hsupp, herg, hg⟩ := S.exists_isGibbs_potential₁ hrot s
  have heq := S.eq_map_unCode_of_hasGibbsBounds hs0 hs2 μ₁ herg hsupp hg hμ hgμ
  obtain ⟨hl₁, hl₂⟩ := hlyap μ₁ herg hsupp hg
  subst heq
  exact ⟨μ₁, μ₁.map flipAxis, S.gibbsDecomposition_map_unCode μ₁ herg hsupp hg hl₁ hl₂⟩

end RectangularIFS

theorem fraserJordanJurgaDecomposition_of_lyapunov
    (hlyap : ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (S : RectangularIFS ι) [S.PositiveRatios], S.HasBothOrientations → ∀ {s : ℝ}, 0 < s → s < 2 →
      ∀ (μ₁ : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure μ₁], Ergodic (shift 1) μ₁ →
      μ₁ (subshift S.o)ᶜ = 0 → IsGibbs S.o (S.potential₁ s) μ₁ →
      S.lyapunov₁ (μ₁.map unCode) = S.lyapBar μ₁ ∧
        S.lyapunov₂ (μ₁.map unCode) = S.lyapBar (μ₁.map flipAxis)) :
    FraserJordanJurgaDecomposition.{u} := by
  intro ι _ _ _ S _ hrot _ s hs0 hs2 μ _ hμ hgμ
  exact S.exists_gibbsDecomposition_of_lyapunov hrot hs0 hs2
    (fun μ₁ _ => hlyap S hrot hs0 hs2 μ₁) μ hμ hgμ

theorem fraserJordanJurgaDecomposition_holds : FraserJordanJurgaDecomposition.{u} := by
  refine fraserJordanJurgaDecomposition_of_lyapunov ?_
  intro ι _ _ _ S _ hrot s hs0 hs2 μ₁ _ herg hsupp hg
  exact S.lyapunov_map_unCode_of_isGibbs hrot hs0 hs2 μ₁ herg hsupp hg

end FractalGeometry
