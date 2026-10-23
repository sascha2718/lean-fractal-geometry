import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.Pressure.Rectangular.Defs
import FractalGeometry.Pressure.Rectangular.Matrices
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory

universe u

def EquilibriumGibbsStatement : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : RectangularIFS ι),
    S.HasBothOrientations → ∀ {s : ℝ}, 0 < s → s < 2 →
    ∀ (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ], MeasurePreserving (shift 1) μ μ →
    S.IsEquilibriumState s μ → S.HasGibbsBounds s μ

end FractalGeometry
