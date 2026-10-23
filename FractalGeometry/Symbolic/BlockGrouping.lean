import Mathlib
import GeometricMeasureTheory.Box.ModifiedBox
import FractalGeometry.SelfAffine.Rectangular.Coding
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.FutureWords

open GeometricMeasureTheory

namespace FractalGeometry

open Filter Topology MeasureTheory

open scoped Matrix.Norms.L2Operator

section Group

variable {α : Type*}

theorem futureWord_eq_ofFn (x : ℤ → α) (n : ℕ) : futureWord x n = List.ofFn (block n x) := by
  rw [List.ofFn_eq_map, futureWord, ← List.map_coe_finRange_eq_range, List.map_map]
  rfl

end Group

end FractalGeometry
