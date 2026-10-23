import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.ApproxSquares
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.Processes
import FractalGeometry.Probability.GridPercolation.WordSplitting

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

variable {A : GridLaw} {Ω : Type*}

lemma colD_wordOfDigits {j : ℕ} (z : DigitWord A j) {i : ℕ} (hi : i < j) :
    colD (wordOfDigits z) i = ((z ⟨i, hi⟩).1 : ℕ) := by
  rw [colD_eq_get _ (by simpa using hi)]
  simp only [List.get_eq_getElem]
  rw [wordOfDigits_getElem z hi]

lemma rowD_wordOfDigits {j : ℕ} (z : DigitWord A j) {i : ℕ} (hi : i < j) :
    rowD (wordOfDigits z) i = ((z ⟨i, hi⟩).2 : ℕ) := by
  rw [rowD_eq_get _ (by simpa using hi)]
  simp only [List.get_eq_getElem]
  rw [wordOfDigits_getElem z hi]

variable {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

end FractalGeometry.Probability.GridPercolation
