import Mathlib
import FractalGeometry.Probability.Branching.Law
import FractalGeometry.Probability.Branching.Process
import FractalGeometry.Probability.Branching.Words

namespace FractalGeometry.Probability.Branching

open MeasureTheory

variable {A : Law} {Ω : Type*}

section Measurability

variable [MeasurableSpace Ω]

theorem measurableSet_retainedBelow {P : Measure Ω}
    {X : Word A → (Fin A.arity) → Ω → Bool}
    (hX : IsPercolation P X) (root u : Word A) :
    MeasurableSet {ω | RetainedBelow X ω root u} := by
  have hcoord (l : Fin u.length) :
      MeasurableSet {ω | X (root ++ u.take l) (u.get l) ω = true} :=
    measurableSet_eq_fun (hX.measurable _ _) measurable_const
  simpa only [RetainedBelow, Set.ofPred_forall] using
    (MeasurableSet.iInter hcoord)

theorem measurableSet_hasInfiniteDescentBelow {P : Measure Ω}
    {X : Word A → (Fin A.arity) → Ω → Bool}
    (hX : IsPercolation P X) (root : Word A) :
    MeasurableSet {ω | HasInfiniteDescentBelow X ω root} := by
  simp only [HasInfiniteDescentBelow, Set.ofPred_forall, Set.ofPred_exists]
  exact MeasurableSet.iInter fun L =>
    MeasurableSet.iUnion fun u =>
      measurableSet_retainedBelow hX root (wordOfDigits u)

end Measurability

end FractalGeometry.Probability.Branching
