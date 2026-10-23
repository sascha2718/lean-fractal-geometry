module

public import Mathlib

@[expose] public section

namespace FractalGeometry


open Matrix

variable {ι : Type*}

theorem mulVec_ne_zero_of_det_ne_zero {P : Matrix (Fin 2) (Fin 2) ℝ} (hP : P.det ≠ 0)
    {u : Fin 2 → ℝ} (hu : u ≠ 0) : P *ᵥ u ≠ 0 :=
  fun h => hu (Matrix.eq_zero_of_mulVec_eq_zero hP h)

end FractalGeometry
