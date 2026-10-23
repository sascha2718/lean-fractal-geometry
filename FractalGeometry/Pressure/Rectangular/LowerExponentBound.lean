import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.Pressure.Rectangular.DecompositionStatement
import FractalGeometry.Pressure.Rectangular.Exponents
import FractalGeometry.Pressure.Rectangular.Matrices
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.SelfAffine.Rectangular.SingularValues

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology

open scoped Matrix.Norms.L2Operator

namespace RectangularIFS

section Word

variable {ι : Type*} (S : RectangularIFS ι)

variable {S} {δ r M : ℝ}

theorem RatioLowerBound.le_log_abs_det_div_norm_matWord (hδ : S.RatioLowerBound δ)
    (w : List ι) :
    Real.log δ * w.length ≤ Real.log (|(S.matWord w).det| / ‖S.matWord w‖) := by
  have h : δ ^ w.length ≤ |(S.matWord w).det| / ‖S.matWord w‖ := by
    rw [abs_det_div_norm_matWord]
    exact le_min (by simpa using hδ.le_abs_gDeriv (S.codeWord 0 w))
      (by simpa using hδ.le_abs_gDeriv (S.codeWord 1 w))
  have h' := Real.log_le_log (pow_pos hδ.1 _) h
  rwa [Real.log_pow, mul_comm] at h'

variable (S)

end Word

end RectangularIFS

end FractalGeometry
