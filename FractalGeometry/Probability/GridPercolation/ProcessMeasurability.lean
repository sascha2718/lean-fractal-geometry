import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.Processes

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory

variable {A : GridLaw} {Ω : Type*}

section Measurability

variable [MeasurableSpace Ω]

theorem measurableSet_retainedBelow {P : Measure Ω}
    {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}
    (hX : IsPercolation P X) (root u : Word A) :
    MeasurableSet {ω | RetainedBelow X ω root u} := by
  have hcoord (l : Fin u.length) :
      MeasurableSet {ω | X (root ++ u.take l) (u.get l) ω = true} :=
    measurableSet_eq_fun (hX.measurable _ _) measurable_const
  simpa only [RetainedBelow, Set.ofPred_forall] using
    (MeasurableSet.iInter hcoord)

theorem measurableSet_hasInfiniteDescentBelow {P : Measure Ω}
    {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}
    (hX : IsPercolation P X) (root : Word A) :
    MeasurableSet {ω | HasInfiniteDescentBelow X ω root} := by
  simp only [HasInfiniteDescentBelow, Set.ofPred_forall, Set.ofPred_exists]
  exact MeasurableSet.iInter fun L =>
    MeasurableSet.iUnion fun u =>
      measurableSet_retainedBelow hX root (wordOfDigits u)

theorem measurable_tubePopulationBelow {P : Measure Ω}
    {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}
    (hX : IsPercolation P X) (root : Word A) {L : ℕ} (v : ColumnWord A L) :
    Measurable (tubePopulationBelow X root v) := by
  classical
  rw [show tubePopulationBelow X root v = fun ω =>
      ∑ r ∈ (Finset.univ : Finset (RowWord A L)),
        if RetainedBelow X ω root (wordOfCoordinates v r) then 1 else 0 by
    funext ω
    exact Finset.card_filter _ _]
  exact Finset.measurable_fun_sum _ fun r _ =>
    Measurable.ite (measurableSet_retainedBelow hX root (wordOfCoordinates v r))
      measurable_const measurable_const

theorem measurable_tubePopulation {P : Measure Ω}
    {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}
    (hX : IsPercolation P X) {L : ℕ} (v : ColumnWord A L) :
    Measurable (tubePopulation X v) := by
  change Measurable (tubePopulationBelow X [] v)
  exact measurable_tubePopulationBelow hX ([] : Word A) v

theorem measurable_occupiedColumnCountBelow {P : Measure Ω}
    {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}
    (hX : IsPercolation P X) (root : Word A) (L : ℕ) :
    Measurable (occupiedColumnCountBelow X root L) := by
  classical
  rw [show occupiedColumnCountBelow X root L = fun ω =>
      ∑ v ∈ (Finset.univ : Finset (ColumnWord A L)),
        if 0 < tubePopulationBelow X root v ω then 1 else 0 by
    funext ω
    exact Finset.card_filter _ _]
  exact Finset.measurable_fun_sum _ fun v _ =>
    Measurable.ite
      (measurableSet_lt measurable_const (measurable_tubePopulationBelow hX root v))
      measurable_const measurable_const

theorem measurable_occupiedColumnCount {P : Measure Ω}
    {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}
    (hX : IsPercolation P X) (L : ℕ) :
    Measurable (occupiedColumnCount X L) := by
  change Measurable (occupiedColumnCountBelow X [] L)
  exact measurable_occupiedColumnCountBelow hX ([] : Word A) L

end Measurability

theorem tubePopulationBelow_le_pow
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (root : Word A)
    {L : ℕ} (v : ColumnWord A L) (ω : Ω) :
    tubePopulationBelow X root v ω ≤ A.N ^ L := by
  classical
  calc
    tubePopulationBelow X root v ω ≤ Fintype.card (RowWord A L) := by
      exact Finset.card_le_univ _
    _ = A.N ^ L := by simp [RowWord]

theorem tubePopulation_le_pow
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool)
    {L : ℕ} (v : ColumnWord A L) (ω : Ω) :
    tubePopulation X v ω ≤ A.N ^ L :=
  tubePopulationBelow_le_pow X [] v ω

end FractalGeometry.Probability.GridPercolation
