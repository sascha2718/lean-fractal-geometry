import FractalGeometry.Pressure.Rectangular.PositiveRatios
import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.Pressure.Rectangular.Defs
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.Symbolic.OrientationCoding
import FractalGeometry.Symbolic.ParityShift
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter

open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [MeasurableSpace ι]

namespace RectangularIFS

variable [MeasurableSingletonClass ι] (S : RectangularIFS ι)

noncomputable def lyapBar (ν : Measure (ℤ → ι × ZMod 2)) : ℝ :=
  ∫ y, Real.log |S.ratio (y 0)| ∂ν

structure GibbsDecomposition (s : ℝ) (μ : Measure (ℤ → ι))
    (μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)) : Prop where
  positive : S.PositiveRatios
  prob₁ : IsProbabilityMeasure μ₁
  prob₂ : IsProbabilityMeasure μ₂
  ergodic₁ : Ergodic (shift 1) μ₁
  ergodic₂ : Ergodic (shift 1) μ₂
  supp₁ : μ₁ (subshift S.o)ᶜ = 0
  supp₂ : μ₂ (subshift S.o)ᶜ = 0
  gibbs₁ : IsGibbs S.o (S.potential₁ s) μ₁
  gibbs₂ : IsGibbs S.o (S.potential₂ s) μ₂
  eq_tau : μ = (μ₁.restrict (Set.range (tau S.o))).map unCode +
    (μ₂.restrict (Set.range (tau S.o))).map unCode
  eq_omega : μ = (μ₁.restrict (Set.range (omega S.o))).map unCode +
    (μ₂.restrict (Set.range (omega S.o))).map unCode
  eq₁ : μ = (μ₁.restrict (Set.range (tau S.o))).map unCode +
    (μ₁.restrict (Set.range (omega S.o))).map unCode
  eq₂ : μ = (μ₂.restrict (Set.range (tau S.o))).map unCode +
    (μ₂.restrict (Set.range (omega S.o))).map unCode
  lyapunov₁_eq : S.lyapunov₁ μ = S.lyapBar μ₁
  lyapunov₂_eq : S.lyapunov₂ μ = S.lyapBar μ₂

end RectangularIFS

end FractalGeometry
