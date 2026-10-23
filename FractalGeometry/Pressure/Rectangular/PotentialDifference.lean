import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.Pressure.Rectangular.Defs
import FractalGeometry.Pressure.Rectangular.Gibbs
import FractalGeometry.SelfAffine.Rectangular.Defs

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Set

open scoped Matrix.Norms.L2Operator

universe u

namespace RectangularIFS

section Potentials

variable {ι : Type u} (S : RectangularIFS ι) {s : ℝ}

theorem potential₁_sub_potential₂ (s : ℝ) (p : ι × ZMod 2) :
    S.potential₁ s p - S.potential₂ s p =
      gapExp s * (Real.log |S.ratio p| - Real.log |S.ratio (p.1, p.2 + 1)|) := by
  have h2 : p.2 + 1 + 1 = p.2 := by
    rw [add_assoc, show (1 : ZMod 2) + 1 = 0 from by decide, add_zero]
  unfold potential₂ potential₁ gapExp
  simp only [h2]
  split_ifs <;> ring

variable [MeasurableSpace ι]

variable {S} {μ : Measure (ℤ → ι)} {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)}

end Potentials

end RectangularIFS

end FractalGeometry
