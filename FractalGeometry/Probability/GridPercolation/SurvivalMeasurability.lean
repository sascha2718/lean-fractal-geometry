import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.ProcessMeasurability
import FractalGeometry.Probability.GridPercolation.Processes

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory

variable {A : GridLaw} {Ω : Type*}

@[simp] theorem retainedBelow_nil_iff_retained
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (ω : Ω) (w : Word A) :
    RetainedBelow X ω [] w ↔ Retained X ω w := by
  rfl

theorem hasInfiniteDescentBelow_nil_iff_mem_survival
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (ω : Ω) :
    HasInfiniteDescentBelow X ω [] ↔ ω ∈ survival X := by
  constructor
  · intro hdescent L
    obtain ⟨u, hu⟩ := hdescent L
    refine ⟨wordOfDigits u, by simp [wordOfDigits], ?_⟩
    simpa using hu
  · intro hsurvival L
    obtain ⟨w, hwlen, hwret⟩ := hsurvival L
    subst L
    refine ⟨w.get, ?_⟩
    simpa [wordOfDigits, List.ofFn_get] using hwret

theorem survival_eq_hasInfiniteDescentBelow
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) :
    survival X = {ω | HasInfiniteDescentBelow X ω []} := by
  ext ω
  exact (hasInfiniteDescentBelow_nil_iff_mem_survival X ω).symm

theorem measurableSet_survival [MeasurableSpace Ω] {P : Measure Ω}
    {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}
    (hX : IsPercolation P X) : MeasurableSet (survival X) := by
  rw [survival_eq_hasInfiniteDescentBelow X]
  exact measurableSet_hasInfiniteDescentBelow hX ([] : Word A)

end FractalGeometry.Probability.GridPercolation
