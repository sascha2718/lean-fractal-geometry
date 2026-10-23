import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering

namespace FractalGeometry.Dimension.PhiAssouad

open Filter Topology MeasureTheory

noncomputable def boxCoverRate (Y : Set (ℝ × ℝ)) (r : ℝ) : ℝ :=
  Real.log (coverNum r Y).toNat / Real.log (1 / r)

noncomputable def upperBoxDim (Y : Set (ℝ × ℝ)) : ℝ :=
  limsup (boxCoverRate Y) (nhdsWithin 0 (Set.Ioi 0))

end FractalGeometry.Dimension.PhiAssouad
