import Mathlib
import FractalGeometry.Probability.Branching.Law
import FractalGeometry.Probability.Branching.Process

namespace FractalGeometry.Probability.Branching

open Finset MeasureTheory ProbabilityTheory

open scoped BigOperators ENNReal

variable {A : Law} {Omega : Type*} [MeasurableSpace Omega]

abbrev Configuration (A : Law) :=
  (Word A × (Fin A.arity)) → Bool

def rebase (base : Word A) (x : Configuration A) :
    Configuration A :=
  fun q => x (base ++ q.1, q.2)

end FractalGeometry.Probability.Branching
