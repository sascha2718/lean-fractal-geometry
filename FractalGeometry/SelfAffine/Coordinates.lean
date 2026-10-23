import Mathlib
import GeometricMeasureTheory.Box.BoxDimension
import FractalGeometry.SelfAffine.Coding
import FractalGeometry.SelfAffine.Planar
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.OneSidedShift


open GeometricMeasureTheory

open Filter Topology Matrix

open scoped Matrix.Norms.L2Operator

namespace FractalGeometry.AffineIFS

variable {ι : Type*} (P : AffineIFS ι)

noncomputable def planeTrans (i : ι) : EuclideanSpace ℝ (Fin 2) := PlaneCoordinates.toPlane (P.v i)

theorem toPlane_phi (i : ι) (z : ℝ × ℝ) :
    PlaneCoordinates.toPlane (P.phi i z) =
      MatrixTuple.affineMap P.mat P.planeTrans i (PlaneCoordinates.toPlane z) := by
  simp only [phi, MatrixTuple.affineMap, planeTrans, PlaneCoordinates.toPlane]
  rw [planeLin_toLp, ← WithLp.toLp_add]
  congr 1
  ext j; fin_cases j <;> simp [ofVec, toVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem toPlane_phiWord (w : List ι) (z : ℝ × ℝ) :
    PlaneCoordinates.toPlane (P.phiWord w z) =
      MatrixTuple.affineWord P.mat P.planeTrans w (PlaneCoordinates.toPlane z) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [toPlane_phi, ih]

theorem toPlane_proj [Finite ι] (x : ℤ → ι) :
    PlaneCoordinates.toPlane (P.proj x) = MatrixTuple.canonicalProj P.mat P.planeTrans x := by
  obtain ⟨r, hA⟩ := MatrixTuple.exists_contractionBound P.mat P.norm_lt_one
  have h1 := (PlaneCoordinates.continuous_toPlane.tendsto _).comp (P.tendsto_phiWord x)
  have h2 := hA.tendsto_affineWord P.planeTrans (eta x)
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  rw [Function.comp_apply, toPlane_phiWord, futureWord_eq_futureWordPlus, PlaneCoordinates.toPlane_zero]

end FractalGeometry.AffineIFS
