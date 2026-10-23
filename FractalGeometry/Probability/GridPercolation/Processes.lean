import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Process

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open scoped ENNReal

variable {A : GridLaw} {Ω : Type*}

abbrev ColumnWord (A : GridLaw) (L : ℕ) := Fin L → Fin A.M

abbrev RowWord (A : GridLaw) (L : ℕ) := Fin L → Fin A.N

abbrev DigitWord (A : GridLaw) (L : ℕ) := Fin L → (Fin A.M × Fin A.N)

def wordOfCoordinates {L : ℕ} (v : ColumnWord A L) (r : RowWord A L) : Word A :=
  List.ofFn fun l => (v l, r l)

def wordOfDigits {L : ℕ} (u : DigitWord A L) : Word A := List.ofFn u

def RetainedBelow
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (ω : Ω) (root u : Word A) : Prop :=
  ∀ l : Fin u.length, X (root ++ u.take l) (u.get l) ω = true

noncomputable def tubePopulationBelow
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (root : Word A)
    {L : ℕ} (v : ColumnWord A L) (ω : Ω) : ℕ := by
  classical
  exact ((Finset.univ : Finset (RowWord A L)).filter fun r =>
    RetainedBelow X ω root (wordOfCoordinates v r)).card

noncomputable def tubePopulation
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool)
    {L : ℕ} (v : ColumnWord A L) (ω : Ω) : ℕ :=
  tubePopulationBelow X [] v ω

noncomputable def occupiedColumnCountBelow
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (root : Word A)
    (L : ℕ) (ω : Ω) : ℕ := by
  classical
  exact ((Finset.univ : Finset (ColumnWord A L)).filter fun v =>
    0 < tubePopulationBelow X root v ω).card

noncomputable def occupiedColumnCount
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (L : ℕ) (ω : Ω) : ℕ :=
  occupiedColumnCountBelow X [] L ω

def HasInfiniteDescentBelow
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (ω : Ω) (root : Word A) : Prop :=
  ∀ L : ℕ, ∃ u : DigitWord A L, RetainedBelow X ω root (wordOfDigits u)

noncomputable def prunedColumnCountBelow
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (root : Word A)
    (L : ℕ) (ω : Ω) : ℕ := by
  classical
  exact ((Finset.univ : Finset (ColumnWord A L)).filter fun v =>
    ∃ r : RowWord A L,
      RetainedBelow X ω root (wordOfCoordinates v r) ∧
        HasInfiniteDescentBelow X ω (root ++ wordOfCoordinates v r)).card

noncomputable def prunedColumnCount
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (L : ℕ) (ω : Ω) : ℕ :=
  prunedColumnCountBelow X [] L ω

def columnPrefix (v : ℕ → Fin A.M) (L : ℕ) : ColumnWord A L := fun l => v l

@[simp] theorem tubePopulationBelow_zero
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (root : Word A) (ω : Ω) :
    tubePopulationBelow X root (L := 0) (fun l => Fin.elim0 l) ω = 1 := by
  classical
  have hret (r : RowWord A 0) :
      RetainedBelow X ω root (wordOfCoordinates (fun l => Fin.elim0 l) r) := by
    have hw : wordOfCoordinates (fun l => Fin.elim0 l) r = [] := by
      simp [wordOfCoordinates]
    rw [hw]
    simp [RetainedBelow]
  simp only [tubePopulationBelow]
  rw [Finset.filter_eq_self.mpr fun r _ => hret r]
  simp

end FractalGeometry.Probability.GridPercolation
