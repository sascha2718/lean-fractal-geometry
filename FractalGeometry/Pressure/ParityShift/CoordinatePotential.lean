import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.Pressure.ParityShift.HolderPotential
import FractalGeometry.Pressure.ParityShift.SymbolicMetric
import FractalGeometry.Symbolic.ParityShift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology Set

section OneSymbol

variable {ι : Type*} [Fintype ι] {o : ι → ZMod 2}

theorem isHolderPotential_apply_zero (φ : ι × ZMod 2 → ℝ) :
    IsHolderPotential o fun z => φ (z 0) := by
  refine ⟨2 * ‖φ‖, 1, by positivity, one_pos, fun y _ z _ => ?_⟩
  rw [Real.rpow_one]
  by_cases h : z 0 = y 0
  · have : φ (y 0) - φ (z 0) = 0 := by rw [h, sub_self]
    rw [this, abs_zero]
    exact mul_nonneg (by positivity) (symDist_nonneg _ _)
  · have hd : symDist y z = 1 := by
      classical
      have hdiff : ∃ n, DiffersAt y z n := ⟨0, 0, rfl, Ne.symm h⟩
      unfold symDist
      rw [dite_eq_left hdiff]
      have : Nat.find hdiff = 0 := (Nat.find_eq_zero hdiff).2 ⟨0, rfl, Ne.symm h⟩
      rw [this, pow_zero]
    rw [hd, mul_one]
    have h1 : |φ (y 0)| ≤ ‖φ‖ := (Real.norm_eq_abs _).symm.trans_le (norm_le_pi_norm φ _)
    have h2 : |φ (z 0)| ≤ ‖φ‖ := (Real.norm_eq_abs _).symm.trans_le (norm_le_pi_norm φ _)
    calc |φ (y 0) - φ (z 0)| ≤ |φ (y 0)| + |φ (z 0)| := abs_sub _ _
      _ ≤ 2 * ‖φ‖ := by linarith

end OneSymbol

end FractalGeometry
