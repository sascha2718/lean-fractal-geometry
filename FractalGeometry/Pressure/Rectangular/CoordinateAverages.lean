import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.Symbolic.PastWords

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology Set Matrix

namespace RectangularIFS

section BackRate

variable {ι : Type*} (S : RectangularIFS ι)

def HasBackRate (y : ℤ → ι × ZMod 2) (l : ℝ) : Prop :=
  Tendsto (fun n : ℕ => Real.log |S.gDeriv (pastWord y n)| / n) atTop (𝓝 l)

end BackRate

end RectangularIFS

end FractalGeometry
