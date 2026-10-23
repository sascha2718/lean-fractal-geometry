import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.ParityCylinders
import FractalGeometry.Symbolic.ParityShift
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open Filter Topology MeasureTheory

section Measure

variable {ι : Type*} (o : ι → ZMod 2) {n : ℕ}

variable [MeasurableSpace ι]

theorem measurableSet_subshift [Fintype ι] [MeasurableSingletonClass ι] :
    MeasurableSet (subshift o) := by
  have h : subshift o = ⋂ n : ℤ, (fun y : ℤ → ι × ZMod 2 => (y n, y (n + 1))) ⁻¹'
      {pq | Trans o pq.1 pq.2} := by
    ext y
    simp [subshift]
  rw [h]
  exact MeasurableSet.iInter fun n =>
    ((measurable_pi_apply n).prodMk (measurable_pi_apply (n + 1)))
      (Set.to_countable _).measurableSet

variable {o} {ν : Measure (ℤ → ι × ZMod 2)}

theorem measurePreserving_shift_map_unCode (hinv : MeasurePreserving (shift 1) ν ν) :
    MeasurePreserving (shift 1) (ν.map unCode) (ν.map unCode) := by
  refine ⟨measurable_shift 1, ?_⟩
  rw [Measure.map_map (measurable_shift 1) measurable_unCode]
  have h : (shift 1 : (ℤ → ι) → ℤ → ι) ∘ unCode = unCode ∘ shift 1 := rfl
  rw [h, ← Measure.map_map measurable_unCode (measurable_shift 1), hinv.map_eq]

end Measure

end FractalGeometry
