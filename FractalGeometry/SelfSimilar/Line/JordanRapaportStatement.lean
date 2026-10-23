import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.Dimension.Exact
import FractalGeometry.SelfSimilar.Line.Coding
import FractalGeometry.SelfSimilar.Line.Defs
import FractalGeometry.SelfSimilar.Line.Lyapunov
import FractalGeometry.SelfSimilar.Line.Separation
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory

universe u

def JordanRapaportDimension : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : LineIFS ι),
    S.ExpSeparation → ∀ (ν : Measure (ℤ → ι)) [IsProbabilityMeasure ν],
    Ergodic (shift 1) ν → IsExactDim (ν.map S.code) (min 1 (-entropy ν / S.lyapunov ν))

end FractalGeometry
