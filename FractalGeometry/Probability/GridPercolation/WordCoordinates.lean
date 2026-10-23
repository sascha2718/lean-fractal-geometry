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

lemma colD_append_left (w₁ w₂ : Word A) {l : ℕ} (hl : l < w₁.length) :
    colD (w₁ ++ w₂) l = colD w₁ l := by
  unfold colD
  rw [List.map_append, List.getD_append _ _ _ _ (by simpa using hl)]

lemma colD_append_right (w₁ w₂ : Word A) {l : ℕ} (hl : w₁.length ≤ l) :
    colD (w₁ ++ w₂) l = colD w₂ (l - w₁.length) := by
  unfold colD
  rw [List.map_append, List.getD_append_right _ _ _ _ (by simpa using hl)]
  simp

lemma rowD_append_left (w₁ w₂ : Word A) {l : ℕ} (hl : l < w₁.length) :
    rowD (w₁ ++ w₂) l = rowD w₁ l := by
  unfold rowD
  rw [List.map_append, List.getD_append _ _ _ _ (by simpa using hl)]

lemma colD_wordOfCoordinates {L : ℕ} (v : ColumnWord A L) (r : RowWord A L) {l : ℕ}
    (hl : l < L) : colD (wordOfCoordinates v r) l = (v ⟨l, hl⟩ : ℕ) := by
  rw [colD_eq_get _ (by simpa using hl)]
  simp only [List.get_eq_getElem]
  rw [wordOfCoordinates_getElem v r hl]

variable {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

end FractalGeometry.Probability.GridPercolation
