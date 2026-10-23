import Mathlib
import GeometricMeasureTheory.Box.BoxDimension
import FractalGeometry.LinearCocycles.Pressure
import FractalGeometry.LinearCocycles.PressureBounds
import FractalGeometry.SelfAffine.Planar


open GeometricMeasureTheory

namespace FractalGeometry

open Filter Topology

namespace AffineIFS

variable {ι : Type*} [Fintype ι] [Nonempty ι] (P : AffineIFS ι)

theorem existsUnique_pressure_eq_zero :
    ∃! s : ℝ, 0 ≤ s ∧ MatrixTuple.pressure P.mat s = 0 :=
  MatrixTuple.pressure_existsUnique_eq_zero P.det_ne_zero P.norm_lt_one

noncomputable def dimaff : ℝ := P.existsUnique_pressure_eq_zero.exists.choose

theorem dimaff_nonneg : 0 ≤ P.dimaff :=
  P.existsUnique_pressure_eq_zero.exists.choose_spec.1

theorem pressure_dimaff : MatrixTuple.pressure P.mat P.dimaff = 0 :=
  P.existsUnique_pressure_eq_zero.exists.choose_spec.2

theorem pressure_neg_of_dimaff_lt {t : ℝ} (ht : P.dimaff < t) :
    MatrixTuple.pressure P.mat t < 0 := by
  have h := MatrixTuple.pressure_strictAntiOn_Ici P.det_ne_zero P.norm_lt_one
    (Set.mem_Ici.2 P.dimaff_nonneg) (Set.mem_Ici.2 (P.dimaff_nonneg.trans ht.le)) ht
  rwa [P.pressure_dimaff] at h

end AffineIFS

end FractalGeometry
