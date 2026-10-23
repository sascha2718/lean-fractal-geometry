import Mathlib
import FractalGeometry.Symbolic.OneSidedShift

namespace FractalGeometry

open MeasureTheory Filter Topology Set

open scoped symmDiff

section Eta

variable {α : Type*}

@[simp] theorem shiftPlus_apply (y : ℕ → α) (k : ℕ) : shiftPlus y k = y (k + 1) := rfl

theorem iterate_shiftPlus_apply (j : ℕ) (y : ℕ → α) (k : ℕ) :
    shiftPlus^[j] y k = y (k + j) := by
  induction j generalizing y with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply, ih, shiftPlus_apply, add_assoc]

def etaFrom (m : ℕ) (x : ℤ → α) : ℕ → α := fun k => x (-(m : ℤ) + k)

theorem etaFrom_eq_iterate (m j : ℕ) (x : ℤ → α) :
    etaFrom m x = shiftPlus^[j] (etaFrom (m + j) x) := by
  funext k
  rw [iterate_shiftPlus_apply]
  simp only [etaFrom]
  congr 1
  push_cast
  ring

variable [TopologicalSpace α]

theorem continuous_shiftPlus : Continuous (shiftPlus : (ℕ → α) → ℕ → α) :=
  continuous_pi fun k => continuous_apply (k + 1)

end Eta

section EtaMeasure

variable {α : Type*} [MeasurableSpace α]

theorem measurable_eta : Measurable (eta : (ℤ → α) → ℕ → α) :=
  Measurable.of_eval fun k => measurable_pi_apply (k : ℤ)

theorem measurable_etaFrom (m : ℕ) : Measurable (etaFrom m : (ℤ → α) → ℕ → α) :=
  Measurable.of_eval fun k => measurable_pi_apply (-(m : ℤ) + k)

def futureSets (α : Type*) [MeasurableSpace α] : Set (Set (ℤ → α)) :=
  {C | ∃ (m : ℕ) (B : Set (ℕ → α)), MeasurableSet B ∧ C = etaFrom m ⁻¹' B}

end EtaMeasure

end FractalGeometry
