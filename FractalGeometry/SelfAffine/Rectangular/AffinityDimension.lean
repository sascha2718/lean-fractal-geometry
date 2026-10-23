import FractalGeometry.SelfAffine.AffinityDimension
import FractalGeometry.Pressure.Rectangular.Invertibility
import FractalGeometry.Pressure.Rectangular.Pressure
import FractalGeometry.LinearCocycles.MonomialSingularValues

/-! The standard planar affine interface and affinity dimension of rectangular systems. -/

namespace FractalGeometry.RectangularIFS

open scoped Matrix.Norms.L2Operator

variable {ι : Type*} (S : RectangularIFS ι)

def toAffineIFS : AffineIFS ι where
  mat := S.mat
  v := S.v
  det_ne_zero := S.det_mat_ne_zero
  norm_lt_one i := by
    rw [mat, norm_monomialMatrix]
    exact max_lt (S.abs_a_lt_one i) (S.abs_b_lt_one i)

variable [Fintype ι] [Nonempty ι]

noncomputable def dimaff : ℝ := S.toAffineIFS.dimaff

theorem pressure_eq_matrixPressure (s : ℝ) :
    S.pressure s = MatrixTuple.pressure S.mat s := rfl

theorem dimaff_nonneg : 0 ≤ S.dimaff := S.toAffineIFS.dimaff_nonneg

theorem pressure_dimaff : S.pressure S.dimaff = 0 := S.toAffineIFS.pressure_dimaff

theorem dimaff_eq {s : ℝ} (hs : 0 ≤ s) (hP : S.pressure s = 0) : S.dimaff = s :=
  S.toAffineIFS.existsUnique_pressure_eq_zero.unique
    ⟨S.dimaff_nonneg, S.pressure_dimaff⟩ ⟨hs, hP⟩

end FractalGeometry.RectangularIFS
