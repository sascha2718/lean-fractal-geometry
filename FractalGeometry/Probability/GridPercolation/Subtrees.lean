import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.Configuration
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.LawInvariance
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.Processes
import FractalGeometry.Probability.GridPercolation.RootIndependence
import FractalGeometry.Probability.GridPercolation.SurvivalMeasurability

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {A : GridLaw} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

def hasInfiniteDescentConfig (x : Configuration A) (root : Word A) : Prop :=
  ∀ L : ℕ, ∃ u : DigitWord A L, retainedBelowConfig x root (wordOfDigits u)

omit [MeasurableSpace Ω] in

lemma hasInfiniteDescentBelow_iff_config (ω : Ω) (root : Word A) :
    HasInfiniteDescentBelow X ω root ↔ hasInfiniteDescentConfig (config X ω) root :=
  Iff.rfl

lemma retainedBelowConfig_rebase (base root u : Word A) (x : Configuration A) :
    retainedBelowConfig (rebase base x) root u ↔
      retainedBelowConfig x (base ++ root) u := by
  simp [retainedBelowConfig, rebase, List.append_assoc]

lemma hasInfiniteDescentConfig_rebase (base root : Word A) (x : Configuration A) :
    hasInfiniteDescentConfig (rebase base x) root ↔
      hasInfiniteDescentConfig x (base ++ root) := by
  simp only [hasInfiniteDescentConfig, retainedBelowConfig_rebase]

lemma measurableSet_hasInfiniteDescentConfig (root : Word A) :
    MeasurableSet {x : Configuration A | hasInfiniteDescentConfig x root} := by
  have : {x : Configuration A | hasInfiniteDescentConfig x root} =
      ⋂ L : ℕ, ⋃ u : DigitWord A L, {x | retainedBelowConfig x root (wordOfDigits u)} := by
    ext x
    simp [hasInfiniteDescentConfig]
  rw [this]
  exact MeasurableSet.iInter fun L =>
    MeasurableSet.iUnion fun u => measurableSet_retainedBelowConfig root _

omit [MeasurableSpace Ω] in

lemma config_mem_survival_iff (ω : Ω) :
    hasInfiniteDescentConfig (config X ω) [] ↔ ω ∈ survival X := by
  rw [← hasInfiniteDescentBelow_iff_config]
  exact hasInfiniteDescentBelow_nil_iff_mem_survival X ω

end FractalGeometry.Probability.GridPercolation
