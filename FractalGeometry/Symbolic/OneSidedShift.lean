import Mathlib
import GeometricMeasureTheory.Box.BoxDimension


open GeometricMeasureTheory

namespace FractalGeometry

open MeasureTheory Filter Topology Set

open scoped symmDiff

section Eta

variable {α : Type*}

def eta (x : ℤ → α) : ℕ → α := fun k => x k

@[simp] theorem eta_apply (x : ℤ → α) (k : ℕ) : eta x k = x k := rfl

def shiftPlus (y : ℕ → α) : ℕ → α := fun k => y (k + 1)

theorem eta_surjective : Function.Surjective (eta : (ℤ → α) → ℕ → α) := fun y =>
  ⟨fun k => y k.toNat, funext fun k => by simp [eta]⟩

variable [TopologicalSpace α]

end Eta

end FractalGeometry
