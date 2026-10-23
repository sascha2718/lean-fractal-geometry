module

public import Mathlib
public import FractalGeometry.Ergodic.FurstenbergKesten
public import FractalGeometry.LinearCocycles.Products
public import FractalGeometry.Symbolic.Shift
public import FractalGeometry.LinearCocycles.Filtration
public import FractalGeometry.LinearCocycles.Regularity
public import FractalGeometry.LinearCocycles.Directions
public import FractalGeometry.LinearCocycles.SlowFastVectors
public import FractalGeometry.Symbolic.PastWords

/-!
Oseledets' multiplicative ergodic theorem for finite invertible planar matrix
families with distinct Lyapunov exponents. An ergodic shift-invariant probability
measure gives full measure to regular points, with a measurable invariant
filtration and the stated vector growth rates.
Reference: V. I. Oseledec, A multiplicative ergodic theorem. Characteristic
Ljapunov exponents of dynamical systems, Trudy Moskov. Mat. Obshch. 19 (1968),
179–210; English translation, Trans. Moscow Math. Soc. 19 (1968), 197–231.
-/

@[expose] public section

namespace FractalGeometry

open MeasureTheory Filter Topology Set Matrix

open scoped Matrix.Norms.L2Operator

universe u

namespace MatrixTuple

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {A : ι → Matrix (Fin 2) (Fin 2) ℝ} {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]

theorem ae_mem_regularSet (hA : ∀ i, (A i).det ≠ 0) (herg : Ergodic (shift 1) μ)
    (hlt : lyapunov₂ A μ < lyapunov₁ A μ) :
    ∀ᵐ x ∂μ, x ∈ regularSet A (lyapunov₁ A μ) (lyapunov₂ A μ) := by
  set K : ℝ := ∑ i, (‖A i‖ + ‖(A i)⁻¹‖) with hK_def
  have hKi : ∀ i, ‖A i‖ ≤ K ∧ ‖(A i)⁻¹‖ ≤ K := fun i => by
    have h := Finset.single_le_sum (f := fun j => ‖A j‖ + ‖(A j)⁻¹‖)
      (fun j _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ i)
    exact ⟨by linarith [norm_nonneg (A i)⁻¹], by linarith [norm_nonneg (A i)]⟩
  filter_upwards [tendsto_log_norm_pastProd hA herg, tendsto_log_alpha₂_pastProd hA herg]
    with x h₁ h₂
  obtain ⟨u, w, hu0, hw0, hu, hw⟩ := exists_slow_fast_of_tendsto
    (M := pastProd A x) (B := fun n => A (x (-((n : ℤ) + 1)))) (pastProd_succ x)
    (fun n => det_word_ne_zero hA _) (fun n => hA _) (fun n => (hKi _).1) (fun n => (hKi _).2)
    hlt h₁ h₂
  exact ⟨u, isRegularWith_of hA hlt hu0 hw0 hu hw⟩

theorem measure_regularSet_compl_of_ergodic (hA : ∀ i, (A i).det ≠ 0)
    (herg : Ergodic (shift 1) μ) (hlt : lyapunov₂ A μ < lyapunov₁ A μ) :
    μ (regularSet A (lyapunov₁ A μ) (lyapunov₂ A μ))ᶜ = 0 :=
  ae_iff.1 (ae_mem_regularSet hA herg hlt)

theorem nonempty_oseledetsSet_of_ergodic (hA : ∀ i, (A i).det ≠ 0)
    (herg : Ergodic (shift 1) μ) (hlt : lyapunov₂ A μ < lyapunov₁ A μ) :
    Nonempty (OseledetsSet A μ) :=
  (nonempty_oseledetsSet_iff hA hlt).2 (measure_regularSet_compl_of_ergodic hA herg hlt)

end MatrixTuple

end FractalGeometry
