import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.LinearCocycles.SingularValue
import FractalGeometry.Pressure.Rectangular.Matrices
import FractalGeometry.Pressure.Rectangular.Pressure
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.ParityShift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter

open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [MeasurableSpace ι]

def IsGibbs (o : ι → ZMod 2) (φ : ι × ZMod 2 → ℝ) (ν : Measure (ℤ → ι × ZMod 2)) : Prop :=
  ∃ P C : ℝ, 0 < C ∧ ∀ y ∈ subshift o, ∀ n : ℕ, 0 < n →
    C⁻¹ * Real.exp (-(n * P) + ∑ k ∈ Finset.range n, φ (y k)) ≤
        ν.real (cylinder fun k : Fin n => y k) ∧
      ν.real (cylinder fun k : Fin n => y k) ≤
        C * Real.exp (-(n * P) + ∑ k ∈ Finset.range n, φ (y k))

namespace RectangularIFS

variable [MeasurableSingletonClass ι] (S : RectangularIFS ι)

noncomputable def lyapunov₁ (μ : Measure (ℤ → ι)) : ℝ :=
  limUnder atTop fun n : ℕ => (∫ x, Real.log ‖S.matWord (futureWord x n)‖ ∂μ) / n

noncomputable def lyapunov₂ (μ : Measure (ℤ → ι)) : ℝ :=
  limUnder atTop fun n : ℕ =>
    (∫ x, Real.log (|(S.matWord (futureWord x n)).det| / ‖S.matWord (futureWord x n)‖) ∂μ) / n

noncomputable def energyLim (s : ℝ) (μ : Measure (ℤ → ι)) : ℝ :=
  limUnder atTop fun n : ℕ => (∫ x, Real.log (svf s (S.matWord (futureWord x n))) ∂μ) / n

def IsEquilibriumState [Fintype ι] (s : ℝ) (μ : Measure (ℤ → ι)) : Prop :=
  S.pressure s = entropy μ + S.energyLim s μ

def HasGibbsBounds [Fintype ι] (s : ℝ) (μ : Measure (ℤ → ι)) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ w : Fin n → ι,
    C⁻¹ * (Real.exp (-(n * S.pressure s)) * svf s (S.matWord (List.ofFn w))) ≤
        μ.real (cylinder w) ∧
      μ.real (cylinder w) ≤
        C * (Real.exp (-(n * S.pressure s)) * svf s (S.matWord (List.ofFn w)))

noncomputable def potential₁ (s : ℝ) (p : ι × ZMod 2) : ℝ :=
  if s < 1 then s * Real.log |S.ratio p|
  else Real.log |S.ratio p| + (s - 1) * Real.log |S.ratio (p.1, p.2 + 1)|

noncomputable def potential₂ (s : ℝ) (p : ι × ZMod 2) : ℝ := S.potential₁ s (p.1, p.2 + 1)

end RectangularIFS

end FractalGeometry
