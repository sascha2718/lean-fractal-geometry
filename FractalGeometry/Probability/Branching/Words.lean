import Mathlib
import FractalGeometry.Probability.Branching.Law
import FractalGeometry.Probability.Branching.Process

namespace FractalGeometry.Probability.Branching

open scoped ENNReal

variable {A : Law} {Ω : Type*}

abbrev DigitWord (A : Law) (L : ℕ) := Fin L → (Fin A.arity)

def wordOfDigits {L : ℕ} (u : DigitWord A L) : Word A := List.ofFn u

def RetainedBelow
    (X : Word A → (Fin A.arity) → Ω → Bool) (ω : Ω) (root u : Word A) : Prop :=
  ∀ l : Fin u.length, X (root ++ u.take l) (u.get l) ω = true

def HasInfiniteDescentBelow
    (X : Word A → (Fin A.arity) → Ω → Bool) (ω : Ω) (root : Word A) : Prop :=
  ∀ L : ℕ, ∃ u : DigitWord A L, RetainedBelow X ω root (wordOfDigits u)

end FractalGeometry.Probability.Branching
