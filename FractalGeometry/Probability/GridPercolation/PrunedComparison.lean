import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.ColumnOffspring
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.ProcessMeasurability
import FractalGeometry.Probability.GridPercolation.Processes
import FractalGeometry.Probability.GridPercolation.SurvivalMeasurability

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {A : GridLaw} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

omit [MeasurableSpace Ω] in

lemma tubePopulation_pos_iff' {L : ℕ} (v : ColumnWord A L) (ω : Ω) :
    0 < tubePopulation X v ω ↔ ∃ r : RowWord A L, RetainedBelow X ω [] (wordOfCoordinates v r) := by
  classical
  unfold tubePopulation tubePopulationBelow
  rw [Finset.card_pos]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, (Finset.mem_filter.mp hr).2⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩

def Counted (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (ω : Ω) {L : ℕ}
    (v : ColumnWord A L) : Prop :=
  ∃ r : RowWord A L, RetainedBelow X ω [] (wordOfCoordinates v r) ∧
    HasInfiniteDescentBelow X ω (wordOfCoordinates v r)

omit [MeasurableSpace Ω] in

open Classical in

lemma prunedColumnCount_eq_card_counted (L : ℕ) (ω : Ω) :
    prunedColumnCount X L ω =
      ((Finset.univ : Finset (ColumnWord A L)).filter fun v => Counted X ω v).card := by
  classical
  unfold prunedColumnCount prunedColumnCountBelow Counted
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.nil_append]

lemma measurableSet_tubePopulation_pos (hX : IsPercolation P X) {L : ℕ}
    (v : ColumnWord A L) : MeasurableSet {ω | 0 < tubePopulation X v ω} := by
  have : {ω | 0 < tubePopulation X v ω} =
      ⋃ r : RowWord A L, {ω | RetainedBelow X ω [] (wordOfCoordinates v r)} := by
    ext ω
    simp [tubePopulation_pos_iff']
  rw [this]
  exact MeasurableSet.iUnion fun r => measurableSet_retainedBelow hX _ _

omit [MeasurableSpace Ω] in

lemma occupiedColumnCount_eq_sum (L : ℕ) (ω : Ω) :
    (occupiedColumnCount X L ω : ℝ≥0∞) =
      ∑ v : ColumnWord A L, Set.indicator {ω | 0 < tubePopulation X v ω} (fun _ => 1) ω := by
  classical
  unfold occupiedColumnCount occupiedColumnCountBelow
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Set.indicator, Set.mem_ofPred_eq, tubePopulation]
  congr

theorem lintegral_occupiedColumnCount (hX : IsPercolation P X) (L : ℕ) :
    ∫⁻ ω, (occupiedColumnCount X L ω : ℝ≥0∞) ∂P =
      ∑ v : ColumnWord A L, P {ω | 0 < tubePopulation X v ω} := by
  simp_rw [occupiedColumnCount_eq_sum]
  rw [lintegral_finsetSum _ fun v _ =>
    (measurable_const.indicator (measurableSet_tubePopulation_pos hX v))]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [lintegral_indicator_const (measurableSet_tubePopulation_pos hX v), one_mul]

end FractalGeometry.Probability.GridPercolation
