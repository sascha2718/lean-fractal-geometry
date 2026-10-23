import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.Law

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory ProbabilityTheory

open scoped ENNReal

abbrev Word (A : GridLaw) := List (Fin A.M × Fin A.N)

noncomputable def cellMap (A : GridLaw)
    (a : Fin A.M × Fin A.N) : ℝ × ℝ → ℝ × ℝ :=
  fun z => ((z.1 + (a.1 : ℕ)) / A.M, (z.2 + (a.2 : ℕ)) / A.N)

noncomputable def rect (A : GridLaw) : Word A → Set (ℝ × ℝ)
  | [] => Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  | a :: w => cellMap A a '' rect A w

structure IsPercolation {A : GridLaw} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) : Prop where

  isProbabilityMeasure : IsProbabilityMeasure P

  measurable : ∀ w a, Measurable (X w a)

  indep : iIndepFun (fun q : Word A × (Fin A.M × Fin A.N) => X q.1 q.2) P

  prob : ∀ w a, P {ω | X w a ω = true} = ENNReal.ofReal (A.p a.1 a.2)

def Retained {A : GridLaw} {Ω : Type*}
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool)
    (ω : Ω) (w : Word A) : Prop :=
  ∀ l : Fin w.length, X (w.take l) (w.get l) ω = true

noncomputable def levelSet {A : GridLaw} {Ω : Type*}
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool)
    (ω : Ω) (k : ℕ) : Set (ℝ × ℝ) :=
  ⋃ w ∈ {w : Word A | w.length = k ∧ Retained X ω w}, rect A w

noncomputable def limitSet {A : GridLaw} {Ω : Type*}
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool)
    (ω : Ω) : Set (ℝ × ℝ) :=
  ⋂ k, levelSet X ω k

def survival {A : GridLaw} {Ω : Type*}
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) : Set Ω :=
  {ω | ∀ k, ∃ w : Word A, w.length = k ∧ Retained X ω w}

variable {A : GridLaw} {Ω : Type*} [MeasurableSpace Ω]

theorem IsPercolation.toIsProbabilityMeasure {P : Measure Ω}
    {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool} (hX : IsPercolation P X) :
    IsProbabilityMeasure P := hX.isProbabilityMeasure

end FractalGeometry.Probability.GridPercolation
