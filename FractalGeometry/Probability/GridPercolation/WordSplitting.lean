import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.Processes

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

variable {A : GridLaw} {Ω : Type*}

@[simp] lemma length_wordOfCoordinates {L : ℕ} (v : ColumnWord A L) (r : RowWord A L) :
    (wordOfCoordinates v r).length = L := by
  simp [wordOfCoordinates]

@[simp] lemma length_wordOfDigits {L : ℕ} (u : DigitWord A L) :
    (wordOfDigits u).length = L := by
  simp [wordOfDigits]

lemma wordOfCoordinates_getElem {L : ℕ} (v : ColumnWord A L) (r : RowWord A L)
    {i : ℕ} (hi : i < L) :
    (wordOfCoordinates v r)[i]'(by simpa using hi) = (v ⟨i, hi⟩, r ⟨i, hi⟩) := by
  simp [wordOfCoordinates]

lemma wordOfDigits_getElem {L : ℕ} (u : DigitWord A L) {i : ℕ} (hi : i < L) :
    (wordOfDigits u)[i]'(by simpa using hi) = u ⟨i, hi⟩ := by
  simp [wordOfDigits]

lemma retained_iff_retainedBelow_nil
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (ω : Ω) (w : Word A) :
    Retained X ω w ↔ RetainedBelow X ω [] w := by
  unfold Retained RetainedBelow
  simp

lemma retainedBelow_append_iff
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (ω : Ω) (root a b : Word A) :
    RetainedBelow X ω root (a ++ b) ↔
      RetainedBelow X ω root a ∧ RetainedBelow X ω (root ++ a) b := by
  constructor
  · intro h
    constructor
    · intro l
      have hl : (l : ℕ) < (a ++ b).length := by
        simp only [List.length_append]
        have := l.isLt
        omega
      have h1 := h ⟨(l : ℕ), hl⟩
      have htake : (a ++ b).take (l : ℕ) = a.take (l : ℕ) :=
        List.take_append_of_le_length l.isLt.le
      have hget : (a ++ b).get ⟨(l : ℕ), hl⟩ = a.get l := by
        simp only [List.get_eq_getElem]
        exact List.getElem_append_left l.isLt
      rwa [htake, hget] at h1
    · intro i
      have hi : a.length + (i : ℕ) < (a ++ b).length := by
        simp only [List.length_append]
        have := i.isLt
        omega
      have h1 := h ⟨a.length + (i : ℕ), hi⟩
      have htake : (a ++ b).take (a.length + (i : ℕ)) = a ++ b.take (i : ℕ) := by
        rw [List.take_append]
        congr 1
        · exact List.take_of_length_le (Nat.le_add_right _ _)
        · congr 1
          omega
      have hget : (a ++ b).get ⟨a.length + (i : ℕ), hi⟩ = b.get i := by
        simp only [List.get_eq_getElem]
        rw [List.getElem_append_right (Nat.le_add_right a.length (i : ℕ))]
        congr 1
        omega
      rw [htake, hget, ← List.append_assoc] at h1
      exact h1
  · rintro ⟨ha, hb⟩ l
    rcases Nat.lt_or_ge (l : ℕ) a.length with hl | hl
    · have h1 := ha ⟨(l : ℕ), hl⟩
      have htake : (a ++ b).take (l : ℕ) = a.take (l : ℕ) :=
        List.take_append_of_le_length hl.le
      have hget : (a ++ b).get l = a.get ⟨(l : ℕ), hl⟩ := by
        simp only [List.get_eq_getElem]
        exact List.getElem_append_left hl
      rw [htake, hget]
      exact h1
    · have hi : (l : ℕ) - a.length < b.length := by
        have := l.isLt
        simp only [List.length_append] at this
        omega
      have h1 := hb ⟨(l : ℕ) - a.length, hi⟩
      have htake : (a ++ b).take (l : ℕ) = a ++ b.take ((l : ℕ) - a.length) := by
        rw [List.take_append, List.take_of_length_le hl]
      have hget : (a ++ b).get l = b.get ⟨(l : ℕ) - a.length, hi⟩ := by
        simp only [List.get_eq_getElem]
        rw [List.getElem_append_right hl]
      rw [htake, hget, ← List.append_assoc]
      exact h1

lemma RetainedBelow.take
    {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool} {ω : Ω} {root u : Word A}
    (h : RetainedBelow X ω root u) (m : ℕ) :
    RetainedBelow X ω root (u.take m) := by
  intro l
  have hlu : (l : ℕ) < u.length := by
    have := l.isLt
    simp only [List.length_take] at this
    omega
  have h1 := h ⟨(l : ℕ), hlu⟩
  have htake : (u.take m).take (l : ℕ) = u.take (l : ℕ) := by
    rw [List.take_take]
    congr 1
    have := l.isLt
    simp only [List.length_take] at this
    omega
  have hget : (u.take m).get l = u.get ⟨(l : ℕ), hlu⟩ := by
    simp only [List.get_eq_getElem]
    exact List.getElem_take
  rw [htake, hget]
  exact h1

noncomputable def descendantCountBelow
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (root : Word A) (j : ℕ)
    (ω : Ω) : ℕ := by
  classical
  exact {u : DigitWord A j | RetainedBelow X ω root (wordOfDigits u)}.toFinset.card

lemma descendantCountBelow_le
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (root : Word A) (j : ℕ) (ω : Ω) :
    descendantCountBelow X root j ω ≤ (A.M * A.N) ^ j := by
  classical
  unfold descendantCountBelow
  calc ({u : DigitWord A j | RetainedBelow X ω root (wordOfDigits u)}.toFinset).card
      ≤ (Finset.univ : Finset (DigitWord A j)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = (A.M * A.N) ^ j := by
        simp [Fintype.card_prod]

end FractalGeometry.Probability.GridPercolation
