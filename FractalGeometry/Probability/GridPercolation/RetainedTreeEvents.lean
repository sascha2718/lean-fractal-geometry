import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.Configuration
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.RootIndependence
import FractalGeometry.Probability.GridPercolation.WordSplitting

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

variable {A : GridLaw}

namespace RetainedTreeEq

lemma retainedBelowConfig_append_iff (x : Configuration A) (root a b : Word A) :
    retainedBelowConfig x root (a ++ b) ↔
      retainedBelowConfig x root a ∧ retainedBelowConfig x (root ++ a) b := by
  change RetainedBelow (fun q d (_ : Unit) => x (q, d)) () root (a ++ b) ↔ _
  exact retainedBelow_append_iff _ _ _ _ _

@[simp] lemma retainedBelowConfig_nil (x : Configuration A) (root : Word A) :
    retainedBelowConfig x root [] := by
  simp [retainedBelowConfig]

end RetainedTreeEq

end FractalGeometry.Probability.GridPercolation
