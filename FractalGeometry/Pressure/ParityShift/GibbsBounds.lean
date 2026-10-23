import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.Pressure.ParityShift.SymbolicMetric
import FractalGeometry.Pressure.Rectangular.Gibbs
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.ParityShift
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Set

section Gibbs

variable {ι : Type*} [MeasurableSpace ι] {o : ι → ZMod 2}
  {f : (ℤ → ι × ZMod 2) → ℝ} {ν : Measure (ℤ → ι × ZMod 2)} {P C : ℝ}

omit [MeasurableSpace ι] in

theorem birkhoffSum_apply_zero (φ : ι × ZMod 2 → ℝ) (n : ℕ) (y : ℤ → ι × ZMod 2) :
    birkhoffSum (shift 1) (fun z => φ (z 0)) n y = ∑ k ∈ Finset.range n, φ (y k) := by
  unfold birkhoffSum
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iterate_shift_one]
  simp

theorem isGibbsPotential_iff_isGibbsWith (φ : ι × ZMod 2 → ℝ) :
    IsGibbsPotential o (fun z => φ (z 0)) ν P C ↔ IsGibbsWith o φ ν P C := by
  simp only [IsGibbsPotential, IsGibbsWith, birkhoffSum_apply_zero]

variable [MeasurableSingletonClass ι]

end Gibbs

end FractalGeometry
