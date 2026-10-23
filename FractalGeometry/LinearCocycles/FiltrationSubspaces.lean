import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.LinearCocycles.Filtration

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology Set Matrix Module

theorem eucNorm_nonneg (v : Fin 2 → ℝ) : 0 ≤ eucNorm v := norm_nonneg _

end FractalGeometry
