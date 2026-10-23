import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.Configuration
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.Processes

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {A : GridLaw} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

def retainedBelowConfig (x : Configuration A) (root u : Word A) : Prop :=
  ∀ l : Fin u.length, x (root ++ u.take l, u.get l) = true

noncomputable def tubePopulationConfig (x : Configuration A) (root : Word A) {L : ℕ}
    (v : ColumnWord A L) : ℕ := by
  classical
  exact ((Finset.univ : Finset (RowWord A L)).filter fun r =>
    retainedBelowConfig x root (wordOfCoordinates v r)).card

lemma tubePopulationConfig_rebase (base root : Word A) (x : Configuration A) {L : ℕ}
    (v : ColumnWord A L) :
    tubePopulationConfig (rebase base x) root v =
      tubePopulationConfig x (base ++ root) v := by
  classical
  unfold tubePopulationConfig
  congr 1
  ext r
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, retainedBelowConfig,
    rebase, List.append_assoc]

lemma measurableSet_retainedBelowConfig (root u : Word A) :
    MeasurableSet {x : Configuration A | retainedBelowConfig x root u} := by
  have hcoord (l : Fin u.length) :
      MeasurableSet {x : Configuration A | x (root ++ u.take l, u.get l) = true} :=
    measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  simpa only [retainedBelowConfig, Set.ofPred_forall] using MeasurableSet.iInter hcoord

lemma measurable_tubePopulationConfig (root : Word A) {L : ℕ} (v : ColumnWord A L) :
    Measurable fun x : Configuration A => tubePopulationConfig x root v := by
  classical
  rw [show (fun x : Configuration A => tubePopulationConfig x root v) = fun x =>
      ∑ r ∈ (Finset.univ : Finset (RowWord A L)),
        if retainedBelowConfig x root (wordOfCoordinates v r) then 1 else 0 by
    funext x
    exact Finset.card_filter _ _]
  exact Finset.measurable_fun_sum _ fun r _ =>
    Measurable.ite (measurableSet_retainedBelowConfig root (wordOfCoordinates v r))
      measurable_const measurable_const

end FractalGeometry.Probability.GridPercolation
