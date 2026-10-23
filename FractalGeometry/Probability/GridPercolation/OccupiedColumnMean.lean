import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.ColumnTubeSurvival
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.ProcessMeasurability
import FractalGeometry.Probability.GridPercolation.Processes
import FractalGeometry.Probability.GridPercolation.PrunedComparison

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {A : GridLaw} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

theorem integral_occupiedColumnCount_eq_sum (hX : IsPercolation P X) (ℓ : ℕ) :
    ∫ ω, (occupiedColumnCount X ℓ ω : ℝ) ∂P =
      ∑ σ : ColumnWord A ℓ, (P {ω | 0 < tubePopulation X σ ω}).toReal := by
  let := hX.toIsProbabilityMeasure
  have hmeas : Measurable fun ω => (occupiedColumnCount X ℓ ω : ℝ) :=
    measurable_from_nat.comp (measurable_occupiedColumnCount hX ℓ)
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun _ => Nat.cast_nonneg _) hmeas.aestronglyMeasurable]
  have hfun : (fun ω => ENNReal.ofReal (occupiedColumnCount X ℓ ω : ℝ)) =
      fun ω => (occupiedColumnCount X ℓ ω : ℝ≥0∞) := by
    funext ω
    exact ENNReal.ofReal_natCast _
  rw [hfun, lintegral_occupiedColumnCount hX ℓ, ENNReal.toReal_sum]
  exact fun σ _ => measure_ne_top _ _

theorem sum_minPrefix_div_le_integral_occupiedColumnCount (hX : IsPercolation P X) (ℓ : ℕ) :
    (∑ σ ∈ (Finset.univ : Finset (ColumnWord A ℓ)).filter (fun σ => ∀ l, σ l ∈ A.cols),
        (Finset.range (ℓ + 1)).inf' Finset.nonempty_range_add_one
          (fun k => ∏ l ∈ Finset.univ.filter (fun l : Fin ℓ => (l : ℕ) < k), A.E (σ l))) /
        (4 * (1 + A.N * ℓ)) ≤
      ∫ ω, (occupiedColumnCount X ℓ ω : ℝ) ∂P := by
  classical
  rw [integral_occupiedColumnCount_eq_sum hX, Finset.sum_div]
  calc
    _ ≤ ∑ σ ∈ (Finset.univ : Finset (ColumnWord A ℓ)).filter (fun σ => ∀ l, σ l ∈ A.cols),
          (P {ω | 0 < tubePopulation X σ ω}).toReal :=
        Finset.sum_le_sum fun σ hσ =>
          minPrefix_div_le_measure_tubePopulation_pos hX σ (Finset.mem_filter.mp hσ).2
    _ ≤ ∑ σ : ColumnWord A ℓ, (P {ω | 0 < tubePopulation X σ ω}).toReal :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => ENNReal.toReal_nonneg

end FractalGeometry.Probability.GridPercolation
