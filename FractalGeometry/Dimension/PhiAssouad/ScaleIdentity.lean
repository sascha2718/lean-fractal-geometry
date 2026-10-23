import Mathlib
import FractalGeometry.Dimension.PhiAssouad.DimensionFunction

namespace FractalGeometry.Dimension.PhiAssouad

open Filter Set Topology

open scoped ENNReal

lemma phi_rpow_eq_exp_gap (phi : DimFun) {R s : ℝ} (hR0 : 0 < R) :
    R ^ (-(phi.toFun R) * s) =
      Real.exp (s * (phi.toFun R * Real.log (1 / R))) := by
  rw [Real.rpow_def_of_pos hR0, one_div, Real.log_inv]
  congr 1
  ring

end FractalGeometry.Dimension.PhiAssouad
