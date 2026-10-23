import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman

open FractalGeometry.Ergodic

namespace FractalGeometry

noncomputable def energy (l1 l2 s : ℝ) : ℝ :=
  if s ≤ 1 then s * l1 else if s ≤ 2 then l1 + (s - 1) * l2 else s / 2 * (l1 + l2)

variable {h l1 l2 s : ℝ}

end FractalGeometry
