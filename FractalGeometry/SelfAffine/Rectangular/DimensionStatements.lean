import Mathlib
import GeometricMeasureTheory.Box.ModifiedBox
import FractalGeometry.Dimension.BoxTools
import FractalGeometry.SelfAffine.Rectangular.AffineMaps
import FractalGeometry.SelfAffine.Rectangular.Attractor
import FractalGeometry.SelfAffine.Rectangular.Coding
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.SelfAffine.Rectangular.ModifiedPressure
import FractalGeometry.SelfAffine.Rectangular.RectangularOpenSet
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.Shift
import GeometricMeasureTheory.Box.BoxDimension
import GeometricMeasureTheory.Box.PackingMeasure

open GeometricMeasureTheory

namespace FractalGeometry

open MeasureTheory

open scoped ENNReal NNReal

universe u

namespace RectangularIFS

variable {ι : Type u} [Fintype ι] [Nonempty ι] (S : RectangularIFS ι)

def FraserBound : Prop :=
  packingDim S.attractor = upperBoxDim S.attractor ∧
    upperBoxDim S.attractor ≤ ENNReal.ofReal S.dimmaff

def FraserROSC : Prop :=
  S.RectangularOpenSet →
    packingDim S.attractor = ENNReal.ofReal S.dimmaff ∧
      lowerBoxDim S.attractor = ENNReal.ofReal S.dimmaff ∧
      upperBoxDim S.attractor = ENNReal.ofReal S.dimmaff

omit [Fintype ι] [Nonempty ι] in

theorem upperBoxDim_image_phi (i : ι) (E : Set (ℝ × ℝ)) :
    upperBoxDim (S.phi i '' E) = upperBoxDim E := by
  have hm : 0 < min |S.a i| |S.b i| :=
    lt_min (abs_pos.2 (S.a_ne_zero i)) (abs_pos.2 (S.b_ne_zero i))
  have hanti : AntilipschitzWith (Real.toNNReal (min |S.a i| |S.b i|)⁻¹) (S.phi i) :=
    AntilipschitzWith.of_le_mul_dist fun z w => by
      rw [Real.coe_toNNReal _ (inv_nonneg.2 hm.le), inv_mul_eq_div, le_div_iff₀' hm]
      exact S.le_dist_phi i z w
  exact upperBoxDim_image_eq ((S.lipschitzWith_phi i).lipschitzOnWith)
    ((hanti.to_rightInverse (S.phi_phiInv i)).lipschitzOnWith) fun x _ => S.phiInv_phi i x

omit [Fintype ι] [Nonempty ι] in

theorem upperBoxDim_image_phiWord (w : List ι) (E : Set (ℝ × ℝ)) :
    upperBoxDim (S.phiWord w '' E) = upperBoxDim E := by
  induction w with
  | nil => simp
  | cons i w ih => rw [phiWord_cons, Set.image_comp, upperBoxDim_image_phi, ih]

theorem packingDim_attractor : packingDim S.attractor = upperBoxDim S.attractor := by
  refine GeometricMeasureTheory.local_box_packing S.isCompact_attractor S.attractor_nonempty fun U hU hne => ?_
  refine le_antisymm (upperBoxDim_mono Set.inter_subset_left) ?_
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  obtain ⟨_, ⟨x, rfl⟩, hzU⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU _ hzU
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.1 S.isCompact_attractor.isBounded
  obtain ⟨n, hn⟩ : ∃ n : ℕ, r ^ n * D < ε := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hS.r_nonneg hS.r_lt_one).mul_const D
    rw [zero_mul] at h
    exact (h.eventually (gt_mem_nhds hε)).exists
  have hsub : S.phiWord (futureWord x n) '' S.attractor ⊆ S.attractor ∩ U := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨S.phiWord_mem S.image_attractor_subset _ hy, hball ?_⟩
    rw [Metric.mem_ball, hS.proj_eq_phiWord x n]
    refine lt_of_le_of_lt (hS.dist_phiWord_le _ _ _) ?_
    rw [length_futureWord]
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (hD hy ⟨_, rfl⟩) (pow_nonneg hS.r_nonneg _)) hn
  calc upperBoxDim S.attractor
      = upperBoxDim (S.phiWord (futureWord x n) '' S.attractor) :=
        (S.upperBoxDim_image_phiWord _ _).symm
    _ ≤ upperBoxDim (S.attractor ∩ U) := upperBoxDim_mono hsub

theorem fraserBound_iff :
    S.FraserBound ↔ upperBoxDim S.attractor ≤ ENNReal.ofReal S.dimmaff :=
  ⟨fun h => h.2, fun h => ⟨S.packingDim_attractor, h⟩⟩

theorem fraserROSC_of_le (hB : S.FraserBound)
    (h : S.RectangularOpenSet → ENNReal.ofReal S.dimmaff ≤ lowerBoxDim S.attractor) :
    S.FraserROSC := fun hrosc => by
  have hL := le_antisymm ((lowerBoxDim_le_upperBoxDim _).trans hB.2) (h hrosc)
  have hU := le_antisymm hB.2 ((h hrosc).trans (lowerBoxDim_le_upperBoxDim _))
  exact ⟨hB.1.trans hU, hL, hU⟩

variable {S}

end RectangularIFS

end FractalGeometry
