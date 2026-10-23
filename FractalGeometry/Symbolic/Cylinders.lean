import Mathlib

namespace FractalGeometry

open MeasureTheory Filter Topology Metric

open scoped ENNReal BoundedContinuousFunction

section Future

variable {α : Type*}

def futureCylinder {n : ℕ} (w : Fin n → α) : Set (ℕ → α) := {y | ∀ k : Fin n, y k = w k}

variable [MeasurableSpace α]

variable [MeasurableSingletonClass α]

theorem measurableSet_futureCylinder {n : ℕ} (w : Fin n → α) :
    MeasurableSet (futureCylinder w) := by
  have : futureCylinder w = ⋂ k : Fin n, (fun y : ℕ → α => y k) ⁻¹' {w k} := by
    ext y
    simp [futureCylinder]
  rw [this]
  exact MeasurableSet.iInter fun k => measurable_pi_apply _ (measurableSet_singleton _)

end Future

end FractalGeometry
