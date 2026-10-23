import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open Set

open scoped ENNReal

noncomputable def gridScale (M k : ℕ) : ℝ :=
  (M : ℝ) ^ (-(k : ℝ))

end FractalGeometry.Probability.GridPercolation
