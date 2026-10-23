import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Process

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open Finset MeasureTheory ProbabilityTheory

open scoped BigOperators ENNReal

variable {A : GridLaw} {Omega : Type*} [MeasurableSpace Omega]

abbrev Configuration (A : GridLaw) :=
  (Word A × (Fin A.M × Fin A.N)) → Bool

def rebase (base : Word A) (x : Configuration A) :
    Configuration A :=
  fun q => x (base ++ q.1, q.2)

end FractalGeometry.Probability.GridPercolation
