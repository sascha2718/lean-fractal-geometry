import Mathlib
import FractalGeometry.Probability.Branching.Law

namespace FractalGeometry.Probability.Branching

open MeasureTheory ProbabilityTheory

open scoped ENNReal

abbrev Word (A : Law) := List (Fin A.arity)

structure IsPercolation {A : Law} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (X : Word A → (Fin A.arity) → Ω → Bool) : Prop where

  isProbabilityMeasure : IsProbabilityMeasure P

  measurable : ∀ w a, Measurable (X w a)

  indep : iIndepFun (fun q : Word A × (Fin A.arity) => X q.1 q.2) P

  prob : ∀ w a, P {ω | X w a ω = true} = ENNReal.ofReal (A.p a)

def Retained {A : Law} {Ω : Type*}
    (X : Word A → (Fin A.arity) → Ω → Bool)
    (ω : Ω) (w : Word A) : Prop :=
  ∀ l : Fin w.length, X (w.take l) (w.get l) ω = true

def survival {A : Law} {Ω : Type*}
    (X : Word A → (Fin A.arity) → Ω → Bool) : Set Ω :=
  {ω | ∀ k, ∃ w : Word A, w.length = k ∧ Retained X ω w}

variable {A : Law} {Ω : Type*} [MeasurableSpace Ω]

theorem IsPercolation.toIsProbabilityMeasure {P : Measure Ω}
    {X : Word A → (Fin A.arity) → Ω → Bool} (hX : IsPercolation P X) :
    IsProbabilityMeasure P := hX.isProbabilityMeasure

end FractalGeometry.Probability.Branching
