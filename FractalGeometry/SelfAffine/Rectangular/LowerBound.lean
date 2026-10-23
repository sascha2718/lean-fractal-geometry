import Mathlib
import GeometricMeasureTheory.Box.ModifiedBox
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.SelfAffine.Rectangular.DimensionStatements
import FractalGeometry.SelfAffine.Rectangular.LowerCover

open GeometricMeasureTheory

namespace FractalGeometry

universe u

namespace RectangularIFS

variable {ι : Type u} [Fintype ι] [Nonempty ι] (S : RectangularIFS ι)

theorem fraserROSC_of_fraserBound (hB : S.FraserBound) : S.FraserROSC :=
  S.fraserROSC_of_le hB S.dimmaff_le_lowerBoxDim

end RectangularIFS

end FractalGeometry
