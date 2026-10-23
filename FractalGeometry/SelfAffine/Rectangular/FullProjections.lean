import FractalGeometry.SelfAffine.Rectangular.AffinityDimension
import FractalGeometry.SelfAffine.Rectangular.Fraser
import FractalGeometry.Dimension.PlaneCovering

/-!
Jonathan M. Fraser, "On the packing dimension of box-like self-affine sets in the
plane", Nonlinearity 25(7) (2012), 2075–2092, Corollary 2.5.
DOI: 10.1088/0951-7715/25/7/2075; arXiv:1108.2639.

Under the rectangular open set condition, full-dimensional coordinate projections
identify packing and box dimensions with the standard affinity dimension.
-/

namespace FractalGeometry.RectangularIFS

open GeometricMeasureTheory Filter Topology
open scoped ENNReal

variable {ι : Type*} [Fintype ι] [Nonempty ι] (S : RectangularIFS ι)

theorem modSvf_eq_svf_of_full_projections (h : ∀ c, S.projDim c = 1)
    {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (w : List ι) :
    S.modSvf s w = svf s (S.matWord w) := by
  have hw : S.wordDim w = 1 := by unfold wordDim; split_ifs <;> exact h _
  rw [modSvf, hw, Real.rpow_one, matWord_eq]
  rcases hs1.eq_or_lt with rfl | hs1
  · rw [svf_monomialMatrix_of_le_one le_rfl]
    simp only [sub_self, Real.rpow_zero, mul_one, Real.rpow_one]
    rfl
  · rw [svf_monomialMatrix_of_le_two hs1 hs2 _ _ (S.gDeriv_ne_zero _)]
    rfl

theorem modPressure_eq_pressure_of_full_projections (h : ∀ c, S.projDim c = 1)
    {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) : S.modPressure s = S.pressure s := by
  have heq : S.modSvfSum s = S.svfSum s := by
    funext n
    exact Finset.sum_congr rfl fun w _ => S.modSvf_eq_svf_of_full_projections h hs1 hs2 _
  obtain ⟨δ, hδ⟩ := S.exists_ratioLowerBound
  simpa [modPressure, heq] using (hδ.tendsto_pressure (by linarith : 0 ≤ s)).limsup_eq

theorem lipschitzWith_coord (c : ZMod 2) : LipschitzWith 1 (coord c) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rcases zmod_two_cases c with rfl | rfl
  · simpa only [coord_zero, NNReal.coe_one, one_mul, Prod.dist_eq] using
      le_max_left (dist z.1 w.1) (dist z.2 w.2)
  · simpa only [coord_one, NNReal.coe_one, one_mul, Prod.dist_eq] using
      le_max_right (dist z.1 w.1) (dist z.2 w.2)

theorem FraserROSC.dimmaff_eq_dimaff (hR : S.FraserROSC) (hrosc : S.RectangularOpenSet)
    (hproj : ∀ c, upperBoxDim (coord c '' S.attractor) = 1) : S.dimmaff = S.dimaff := by
  obtain ⟨-, -, hU⟩ := hR hrosc
  have hp : ∀ c, S.projDim c = 1 := fun c => by rw [projDim, hproj c, ENNReal.toReal_one]
  have h1 : 1 ≤ S.dimmaff := by
    have h := upperBoxDim_image_le ((lipschitzWith_coord 0).lipschitzOnWith) (E := S.attractor)
    rw [hproj, hU, ← ENNReal.ofReal_one] at h
    exact (ENNReal.ofReal_le_ofReal_iff S.dimmaff_nonneg).1 h
  have h2 : S.dimmaff ≤ 2 := by
    have h := upperBoxDim_le_two S.isCompact_attractor.isBounded
    rw [hU, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).1 h
  apply Eq.symm
  apply S.dimaff_eq S.dimmaff_nonneg
  rw [← S.modPressure_eq_pressure_of_full_projections hp h1 h2, S.modPressure_dimmaff]

theorem fraser_full_projections (hrosc : S.RectangularOpenSet)
    (hproj : ∀ c, upperBoxDim (coord c '' S.attractor) = 1) :
    packingDim S.attractor = ENNReal.ofReal S.dimaff ∧
      lowerBoxDim S.attractor = ENNReal.ofReal S.dimaff ∧
      upperBoxDim S.attractor = ENNReal.ofReal S.dimaff := by
  rw [← S.fraserROSC_holds.dimmaff_eq_dimaff S hrosc hproj]
  exact S.fraserROSC_holds hrosc

end FractalGeometry.RectangularIFS
