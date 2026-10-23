module

public import Mathlib

@[expose] public section

namespace FractalGeometry


open MeasureTheory Filter Topology Set Matrix

open scoped Real

universe u

theorem norm_fin_two (v : Fin 2 → ℝ) : ‖v‖ = max |v 0| |v 1| := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (le_max_of_le_left (abs_nonneg _))).2
    fun j => ?_) (max_le (norm_le_pi_norm v 0) (norm_le_pi_norm v 1))
  fin_cases j
  · exact le_max_left _ _
  · exact le_max_right _ _

end FractalGeometry
