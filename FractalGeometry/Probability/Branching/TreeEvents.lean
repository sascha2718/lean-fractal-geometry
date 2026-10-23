import Mathlib
import FractalGeometry.Probability.Branching.Configuration
import FractalGeometry.Probability.Branching.Descendants
import FractalGeometry.Probability.Branching.Law
import FractalGeometry.Probability.Branching.Process
import FractalGeometry.Probability.Branching.RetainedWords

namespace FractalGeometry.Probability.Branching

variable {A : Law}

def RetainedTreeEq (x y : Configuration A) : Prop :=
  ∀ w : Word A, retainedBelowConfig x [] w ↔ retainedBelowConfig y [] w

def IsRetainedTreeEvent (E : Set (Configuration A)) : Prop :=
  ∀ ⦃x y⦄, RetainedTreeEq x y → (x ∈ E ↔ y ∈ E)

namespace RetainedTreeEq

lemma retainedBelowConfig_append_iff (x : Configuration A) (root a b : Word A) :
    retainedBelowConfig x root (a ++ b) ↔
      retainedBelowConfig x root a ∧ retainedBelowConfig x (root ++ a) b := by
  change RetainedBelow (fun q d (_ : Unit) => x (q, d)) () root (a ++ b) ↔ _
  exact retainedBelow_append_iff _ _ _ _ _

end RetainedTreeEq

end FractalGeometry.Probability.Branching
