import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Symbolic.Conditional
import FractalGeometry.Symbolic.ConditionalRefinement
import FractalGeometry.Symbolic.Disintegration
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.Information
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology Set

universe u

section StandardBorel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]

theorem condMeas_eq_one_of_atom_subset (μ : Measure Ω) [IsFiniteMeasure μ] {ξ : Ω → Set Ω}
    (hξ : IsMeasurablePartition ξ) {R : Ω → Set Ω} (hsub : ∀ᵐ x ∂μ, ξ x ⊆ R x) :
    ∀ᵐ x ∂μ, condMeas μ ξ x (R x) = 1 := by
  filter_upwards [condMeas_atom μ hξ, hsub] with x hx hxR
  exact le_antisymm prob_le_one (hx.symm.le.trans (measure_mono hxR))

end StandardBorel

theorem birkhoffAverage_shift_one {α : Type*} (f : (ℤ → α) → ℝ) (n : ℕ) (x : ℤ → α) :
    birkhoffAverage ℝ (shift 1) f n x = (∑ k ∈ Finset.range n, f (shift k x)) / n := by
  rw [birkhoffAverage, birkhoffSum, smul_eq_mul, div_eq_inv_mul]
  simp only [iterate_shift_one]

section General

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem condMeas_cylinder_pos (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (ξ : (ℤ → α) → Set (ℤ → α)) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, 0 < condMeas μ ξ x (cylinder (block n x)) := by
  have h : ∀ᵐ x ∂μ, ∀ n : ℕ, ∀ w : Fin n → α,
      x ∈ cylinder w → 0 < condMeas μ ξ x (cylinder w) :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun w => condMeas_pos_of_mem μ ξ (measurableSet_cylinder w)
  filter_upwards [h] with x hx n
  exact hx n (block n x) fun _ => rfl

theorem tendsto_neg_log_condMeas_cylinder {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) {ξ : (ℤ → α) → Set (ℤ → α)}
    (hsum : ∀ᵐ x ∂μ, ∀ n : ℕ, -Real.log ((condMeas μ ξ x).real (cylinder (block n x))) =
      ∑ k ∈ Finset.range n, condInfo μ ξ (shift k x)) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => -Real.log ((condMeas μ ξ x).real (cylinder (block n x))) / n)
      atTop (𝓝 (localEntropy μ ξ x)) := by
  filter_upwards [birkhoff_ae hinv (integrable_condInfo μ ξ), hsum] with x hx hs
  have hx' : Tendsto (fun n : ℕ => birkhoffAverage ℝ (shift 1) (condInfo μ ξ) n x) atTop
      (𝓝 (localEntropy μ ξ x)) := hx
  simp only [birkhoffAverage_shift_one] at hx'
  simpa only [hs] using hx'

end General

end FractalGeometry
