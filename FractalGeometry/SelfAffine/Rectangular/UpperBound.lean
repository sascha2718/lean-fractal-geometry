import Mathlib
import GeometricMeasureTheory.Box.ModifiedBox
import FractalGeometry.SelfAffine.Rectangular.Coding
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.SelfAffine.Rectangular.DimensionStatements
import FractalGeometry.SelfAffine.Rectangular.ModifiedPressure
import FractalGeometry.SelfAffine.Rectangular.UpperCover
import GeometricMeasureTheory.Box.BoxDimension

open GeometricMeasureTheory

namespace FractalGeometry

namespace RectangularIFS

universe u

variable {ι : Type u} [Fintype ι] [Nonempty ι] (S : RectangularIFS ι)

theorem fraserBound_holds : S.FraserBound :=
  (S.fraserBound_iff).2 S.upperBoxDim_attractor_le_dimmaff

end RectangularIFS

end FractalGeometry
