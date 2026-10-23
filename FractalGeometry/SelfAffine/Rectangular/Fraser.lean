import Mathlib
import GeometricMeasureTheory.Box.ModifiedBox
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.SelfAffine.Rectangular.DimensionStatements
import FractalGeometry.SelfAffine.Rectangular.LowerBound
import FractalGeometry.SelfAffine.Rectangular.UpperBound

/-!
Fraser's dimension theorem for rectangular planar affine iterated function systems.

Jonathan M. Fraser, "On the packing dimension of box-like self-affine sets in the
plane", Nonlinearity 25(7) (2012), 2075–2092, Theorem 2.3.
DOI: 10.1088/0951-7715/25/7/2075; arXiv:1108.2639.

`fraserBound_holds` identifies packing with upper box dimension and bounds it by
the zero of modified singular-value pressure. `fraserROSC_holds` identifies the
packing, lower box and upper box dimensions with this zero under the rectangular
open set condition. The model allows diagonal and anti-diagonal linear parts.
-/

open GeometricMeasureTheory

namespace FractalGeometry

namespace RectangularIFS

universe u

variable {ι : Type u} [Fintype ι] [Nonempty ι] (S : RectangularIFS ι)

theorem fraserROSC_holds : S.FraserROSC :=
  S.fraserROSC_of_fraserBound S.fraserBound_holds

end RectangularIFS

end FractalGeometry
