import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.Symbolic.Entropy

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory ProbabilityTheory Filter Topology Set

universe u

section Typical

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]

open Classical in

noncomputable def typicalWords (μ : Measure (ℤ → α)) (h ε : ℝ) (n : ℕ) : Finset (Fin n → α) :=
  Finset.univ.filter fun w => Real.exp (-(n * (h + ε))) ≤ μ.real (cylinder w) ∧
    μ.real (cylinder w) ≤ Real.exp (-(n * (h - ε)))

omit [MeasurableSingletonClass α] [IsProbabilityMeasure μ] in

theorem mem_typicalWords {h ε : ℝ} {n : ℕ} {w : Fin n → α} :
    w ∈ typicalWords μ h ε n ↔ Real.exp (-(n * (h + ε))) ≤ μ.real (cylinder w) ∧
      μ.real (cylinder w) ≤ Real.exp (-(n * (h - ε))) := by
  classical
  simp [typicalWords]

end Typical

end FractalGeometry
