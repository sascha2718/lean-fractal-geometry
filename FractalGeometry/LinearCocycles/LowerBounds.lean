import Mathlib
import FractalGeometry.LinearCocycles.Products

namespace FractalGeometry

open MeasureTheory Filter Topology ProbabilityTheory

open scoped Matrix.Norms.L2Operator ENNReal

namespace MatrixTuple

variable {ι : Type*} (A : ι → Matrix (Fin 2) (Fin 2) ℝ)

@[simp] theorem word_cons (i : ι) (w : List ι) : word A (i :: w) = A i * word A w := by
  simp [word]

variable {A}

theorem word_det_ne_zero (hA : ∀ i, (A i).det ≠ 0) (w : List ι) : (word A w).det ≠ 0 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [word_cons, Matrix.det_mul]
    exact mul_ne_zero (hA i) ih

theorem norm_word_pos (hA : ∀ i, (A i).det ≠ 0) (w : List ι) : 0 < ‖word A w‖ := by
  refine norm_pos_iff.2 fun h => word_det_ne_zero hA w ?_
  rw [h]
  simp

variable [Fintype ι]

variable (A) in

noncomputable def normLowerBound : ℝ := (1 + ∑ i, ‖(A i)⁻¹‖)⁻¹

omit [Fintype ι] in

theorem one_add_sum_pos {f : ι → ℝ} [Fintype ι] (hf : ∀ i, 0 ≤ f i) : 0 < 1 + ∑ i, f i :=
  add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ => hf i)

omit [Fintype ι] in

theorem le_one_add_sum {f : ι → ℝ} [Fintype ι] (hf : ∀ i, 0 ≤ f i) (i : ι) :
    f i ≤ 1 + ∑ j, f j := by
  have := Finset.single_le_sum (f := f) (fun j _ => hf j) (Finset.mem_univ i)
  linarith

theorem normLowerBound_pos : 0 < normLowerBound A :=
  inv_pos.2 (one_add_sum_pos fun _ => norm_nonneg _)

theorem normLowerBound_mul_le (i : ι) : normLowerBound A * ‖(A i)⁻¹‖ ≤ 1 := by
  rw [normLowerBound, inv_mul_le_iff₀ (one_add_sum_pos fun _ => norm_nonneg _), mul_one]
  exact le_one_add_sum (fun j => norm_nonneg ((A j)⁻¹)) i

theorem pow_le_norm_word (hA : ∀ i, (A i).det ≠ 0) (w : List ι) :
    normLowerBound A ^ w.length ≤ ‖word A w‖ := by
  induction w with
  | nil => simp
  | cons i w ih =>
    have hinv : (A i)⁻¹ * A i = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hA i))
    have hle : ‖word A w‖ ≤ ‖(A i)⁻¹‖ * ‖A i * word A w‖ := by
      calc ‖word A w‖ = ‖(A i)⁻¹ * (A i * word A w)‖ := by
            rw [← mul_assoc, hinv, one_mul]
        _ ≤ ‖(A i)⁻¹‖ * ‖A i * word A w‖ := Matrix.l2_opNorm_mul _ _
    have hδ := normLowerBound_pos (A := A)
    rw [word_cons, List.length_cons, pow_succ']
    calc normLowerBound A * normLowerBound A ^ w.length
        ≤ normLowerBound A * ‖word A w‖ := mul_le_mul_of_nonneg_left ih hδ.le
      _ ≤ normLowerBound A * (‖(A i)⁻¹‖ * ‖A i * word A w‖) :=
          mul_le_mul_of_nonneg_left hle hδ.le
      _ = (normLowerBound A * ‖(A i)⁻¹‖) * ‖A i * word A w‖ := by ring
      _ ≤ 1 * ‖A i * word A w‖ :=
          mul_le_mul_of_nonneg_right (normLowerBound_mul_le i) (norm_nonneg _)
      _ = ‖A i * word A w‖ := one_mul _

theorem le_log_norm_word (hA : ∀ i, (A i).det ≠ 0) (w : List ι) :
    Real.log (normLowerBound A) * w.length ≤ Real.log ‖word A w‖ := by
  have h := Real.log_le_log (pow_pos normLowerBound_pos _) (pow_le_norm_word hA w)
  rwa [Real.log_pow, mul_comm] at h

variable [MeasurableSpace ι] [MeasurableSingletonClass ι] {μ : Measure (ℤ → ι)}
  [IsProbabilityMeasure μ]

end MatrixTuple

end FractalGeometry
