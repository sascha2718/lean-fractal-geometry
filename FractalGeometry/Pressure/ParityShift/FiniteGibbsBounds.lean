import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Pressure.ParityShift.SymbolicMetric
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.ParityShift
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory

variable {ι : Type*} [MeasurableSpace ι] {o : ι → ZMod 2}
  {f : (ℤ → ι × ZMod 2) → ℝ} {ν : Measure (ℤ → ι × ZMod 2)} {P C : ℝ}

def GibbsUpTo (o : ι → ZMod 2) (f : (ℤ → ι × ZMod 2) → ℝ) (ν : Measure (ℤ → ι × ZMod 2))
    (P C : ℝ) (N : ℕ) : Prop :=
  0 < C ∧ ∀ y ∈ subshift o, ∀ n : ℕ, 0 < n → n ≤ N →
    C⁻¹ * Real.exp (-(n * P) + birkhoffSum (shift 1) f n y) ≤
        ν.real (cylinder fun k : Fin n => y k) ∧
      ν.real (cylinder fun k : Fin n => y k) ≤
        C * Real.exp (-(n * P) + birkhoffSum (shift 1) f n y)

theorem isGibbsPotential_iff_forall_gibbsUpTo :
    IsGibbsPotential o f ν P C ↔ ∀ N : ℕ, GibbsUpTo o f ν P C N := by
  constructor
  · rintro ⟨hC, h⟩ N
    exact ⟨hC, fun y hy n hn _ => h y hy n hn⟩
  · intro h
    exact ⟨(h 0).1, fun y hy n hn => (h n).2 y hy n hn le_rfl⟩

end FractalGeometry
