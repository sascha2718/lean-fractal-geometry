import Mathlib
import FractalGeometry.Probability.Patterns.Defs

namespace FractalGeometry.Probability.Patterns

open Finset

namespace Weights

variable {ι X : Type*} [Fintype ι] [MetricSpace X] (p : Weights ι)

theorem wordProb_pos {n : ℕ} (w : Word ι n) : 0 < p.wordProb w :=
  prod_pos fun i _ => p.pos (w i)

end Weights

end FractalGeometry.Probability.Patterns
