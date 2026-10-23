import Mathlib
import FractalGeometry.Probability.Branching.Configuration
import FractalGeometry.Probability.Branching.IdenticalLaws
import FractalGeometry.Probability.Branching.Law
import FractalGeometry.Probability.Branching.Process
import FractalGeometry.Probability.Branching.TreeEvents

namespace FractalGeometry.Probability.Branching

open Filter Topology MeasureTheory

open scoped ENNReal

variable {A : Law} {Ω : Type*} [MeasurableSpace Ω]

def TreeSecondBorelCantelli (P : Measure Ω)
    (X : Word A → (Fin A.arity) → Ω → Bool) : Prop :=
  ∀ (E : ℕ → Set (Configuration A)), (∀ n, MeasurableSet (E n)) →
    (∀ n, IsRetainedTreeEvent (E n)) →
    ∀ K : ℕ → ℝ, (∀ n, 0 ≤ K n) → Summable K →
      ¬ Summable (fun n => K n * (P (config X ⁻¹' E n)).toReal * A.m ^ n) →
      ∀ᵐ ω ∂P, ω ∈ survival X → ∃ᶠ n in atTop, ∃ v : Word A, v.length = n ∧
        Retained X ω v ∧ rebase v (config X ω) ∈ E n

end FractalGeometry.Probability.Branching
