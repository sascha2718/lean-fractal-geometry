import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.Pressure.Rectangular.DecompositionStatement
import FractalGeometry.Pressure.Rectangular.Defs
import FractalGeometry.Pressure.Rectangular.LyapunovStatement
import FractalGeometry.Pressure.Rectangular.Matrices
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory

universe u

def FraserJordanJurgaDecomposition : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : RectangularIFS ι) [S.PositiveRatios],
    S.HasBothOrientations → S.HasProximalDiagonal → ∀ {s : ℝ}, 0 < s → s < 2 →
    ∀ (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ], MeasurePreserving (shift 1) μ μ →
    S.HasGibbsBounds s μ → ∃ μ₁ μ₂ : Measure (ℤ → ι × ZMod 2), S.GibbsDecomposition s μ μ₁ μ₂

end FractalGeometry
