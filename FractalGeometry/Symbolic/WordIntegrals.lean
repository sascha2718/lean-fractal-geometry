import Mathlib
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.WordAverages

namespace FractalGeometry

open MeasureTheory

section Integral

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem integral_comp_block_eq_sum (μ : Measure (ℤ → α)) [IsFiniteMeasure μ] {n : ℕ}
    (F : (Fin n → α) → ℝ) :
    ∫ x, F (block n x) ∂μ = ∑ w : Fin n → α, μ.real (cylinder w) * F w := by
  have hF : Measurable F := Measurable.of_discrete
  rw [← integral_map (measurable_block n).aemeasurable hF.aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_measureReal_apply (measurable_block n) (measurableSet_singleton w),
    cylinder_eq_preimage, smul_eq_mul]

theorem integral_comp_futureWord_eq_sum (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (G : List α → ℝ) (n : ℕ) :
    ∫ x, G (futureWord x n) ∂μ = ∑ w : Fin n → α, μ.real (cylinder w) * G (List.ofFn w) := by
  simp only [futureWord_eq_ofFn_block]
  exact integral_comp_block_eq_sum μ fun w => G (List.ofFn w)

end Integral

end FractalGeometry
