import Mathlib
import FractalGeometry.Probability.Branching.Configuration
import FractalGeometry.Probability.Branching.Law
import FractalGeometry.Probability.Branching.Process

namespace FractalGeometry.Probability.Branching

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {A : Law} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.arity) → Ω → Bool}

def retainedBelowConfig (x : Configuration A) (root u : Word A) : Prop :=
  ∀ l : Fin u.length, x (root ++ u.take l, u.get l) = true

lemma measurableSet_retainedBelowConfig (root u : Word A) :
    MeasurableSet {x : Configuration A | retainedBelowConfig x root u} := by
  have hcoord (l : Fin u.length) :
      MeasurableSet {x : Configuration A | x (root ++ u.take l, u.get l) = true} :=
    measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  simpa only [retainedBelowConfig, Set.ofPred_forall] using MeasurableSet.iInter hcoord

end FractalGeometry.Probability.Branching
