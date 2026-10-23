import Mathlib
import GeometricMeasureTheory.Box.BoxDimension
import FractalGeometry.LinearCocycles.SingularValueExponents


open GeometricMeasureTheory

namespace FractalGeometry

open Filter Topology Matrix

open scoped ENNReal NNReal Matrix.Norms.L2Operator

theorem svfExp_eq_one {s : ℝ} (h1 : 1 ≤ s) (h2 : s ≤ 2) : svfExp s = 1 := by
  unfold svfExp
  split_ifs with h
  · exact le_antisymm h h1
  · rfl

end FractalGeometry
