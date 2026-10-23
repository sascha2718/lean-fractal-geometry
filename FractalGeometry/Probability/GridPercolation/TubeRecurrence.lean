import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.ColumnOffspring
import FractalGeometry.Probability.GridPercolation.GenerationConditioning
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.Processes

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {A : GridLaw} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

noncomputable def nextTubeFromStates {L : ℕ} (past : ColumnPastState A L)
    (future : ColumnFutureState A L) (v : ColumnWord A L) (i : Fin A.M) : ℝ := by
  classical
  exact ((∑ r : RowWord A L, if retainedFromPast past v r then
    columnOffspringFromFuture future v r i else 0 : ℕ) : ℝ)

omit [MeasurableSpace Ω] in

lemma columnPrefix_succ (w : ℕ → Fin A.M) (L : ℕ) :
    columnPrefix w (L + 1) = snocColumnWord (columnPrefix w L) (w L) := by
  funext l
  refine Fin.lastCases ?_ (fun l' => ?_) l
  · simp [columnPrefix, snocColumnWord, snocFinWord]
  · simp [columnPrefix, snocColumnWord, snocFinWord]

omit [MeasurableSpace Ω] in

lemma nextTubeFromStates_states (w : ℕ → Fin A.M) (L : ℕ) (ω : Ω) :
    nextTubeFromStates (columnPastState X L ω) (columnFutureState X L ω)
        (columnPrefix w L) (w L) =
      (tubePopulation X (columnPrefix w (L + 1)) ω : ℝ) := by
  classical
  rw [columnPrefix_succ]
  unfold nextTubeFromStates tubePopulation
  rw [tubePopulationBelow_snocColumnWord]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [columnOffspringFromFuture_columnFutureState, List.nil_append]
  by_cases hr : retainedFromPast (columnPastState X L ω) (columnPrefix w L) r
  · rw [ite_eq_left hr, ite_eq_left ((retainedFromPast_columnPastState_iff X _ r ω).mp hr)]
  · rw [ite_eq_right hr, ite_eq_right ((not_congr (retainedFromPast_columnPastState_iff X _ r ω)).mp hr)]

omit [MeasurableSpace Ω] in

lemma nextTubeFromStates_columnFutureState {L : ℕ} (past : ColumnPastState A L)
    (v : ColumnWord A L) (i : Fin A.M) (ω : Ω) :
    nextTubeFromStates past (columnFutureState X L ω) v i =
      ∑ r : RowWord A L, if activeRowsFromPast past v r then
        (columnOffspring X (wordOfCoordinates v r) i ω : ℝ) else 0 := by
  classical
  unfold nextTubeFromStates
  rw [Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro r _
  rw [columnOffspringFromFuture_columnFutureState]
  simp only [activeRowsFromPast_eq_true_iff]

omit [MeasurableSpace Ω] in

lemma tubePopulation_columnPrefix_zero (w : ℕ → Fin A.M) (ω : Ω) :
    tubePopulation X (columnPrefix w 0) ω = 1 := by
  have h : columnPrefix w 0 = fun l : Fin 0 => Fin.elim0 l := by
    funext l
    exact Fin.elim0 l
  rw [h]
  exact tubePopulationBelow_zero X [] ω

end FractalGeometry.Probability.GridPercolation
