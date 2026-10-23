import Mathlib

namespace FractalGeometry

/-- A finite alphabet of invertible contracting similarities of the real line. -/
structure LineIFS (ι : Type*) where
  ratio : ι → ℝ
  trans : ι → ℝ
  ratio_ne_zero : ∀ i, ratio i ≠ 0
  abs_ratio_lt_one : ∀ i, |ratio i| < 1

end FractalGeometry
