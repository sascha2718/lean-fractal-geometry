module

public import Mathlib
public import FractalGeometry.Symbolic.Entropy
public import FractalGeometry.Symbolic.Shift

@[expose] public section

namespace FractalGeometry


open MeasureTheory Filter Topology Set

open scoped Matrix.Norms.L2Operator

universe u

theorem iterate_shift_neg_one {α : Type*} (n : ℕ) :
    (shift (-1) : (ℤ → α) → ℤ → α)^[n] = shift (-(n : ℤ)) := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    funext x
    rw [Function.iterate_succ_apply', ih, shift_shift]
    congr 1
    push_cast
    ring

section InverseShift

variable {α : Type*} [MeasurableSpace α]

def shiftEquiv : (ℤ → α) ≃ᵐ (ℤ → α) where
  toFun := shift 1
  invFun := shift (-1)
  left_inv x := by rw [shift_shift]; simp
  right_inv x := by rw [shift_shift]; simp
  measurable_toFun := measurable_shift 1
  measurable_invFun := measurable_shift (-1)

theorem ergodic_shift_neg_one {μ : Measure (ℤ → α)} (h : Ergodic (shift 1) μ) :
    Ergodic (shift (-1)) μ :=
  Ergodic.symm (e := shiftEquiv) h

theorem measurePreserving_shift_neg_one {μ : Measure (ℤ → α)}
    (h : MeasurePreserving (shift 1) μ μ) : MeasurePreserving (shift (-1)) μ μ :=
  MeasurePreserving.symm shiftEquiv h

theorem measurePreserving_shift_neg_natCast {μ : Measure (ℤ → α)}
    (h : MeasurePreserving (shift 1) μ μ) (n : ℕ) :
    MeasurePreserving (shift (-(n : ℤ))) μ μ := by
  rw [← iterate_shift_neg_one]
  exact (measurePreserving_shift_neg_one h).iterate n

theorem integral_comp_shift_neg {μ : Measure (ℤ → α)} (hμ : MeasurePreserving (shift 1) μ μ)
    (n : ℕ) {F : (ℤ → α) → ℝ} (hF : Measurable F) :
    ∫ x, F (shift (-(n : ℤ)) x) ∂μ = ∫ x, F x ∂μ := by
  have h := measurePreserving_shift_neg_natCast hμ n
  rw [← integral_map h.measurable.aemeasurable hF.aestronglyMeasurable, h.map_eq]

end InverseShift

end FractalGeometry
