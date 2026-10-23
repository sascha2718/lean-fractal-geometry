import FractalGeometry.Probability.GridPercolation.AssouadUpperBound
import FractalGeometry.Probability.GridPercolation.LowerCovering
import FractalGeometry.Probability.GridPercolation.DigitCoordinates

/-! The deterministic carpet associated to a finite rectangular digit set. -/

namespace FractalGeometry.Probability.GridPercolation

open FractalGeometry.Dimension.PhiAssouad
open scoped ENNReal

noncomputable def deterministicRetention (A : GridLaw) :
    Word A → (Fin A.M × Fin A.N) → Unit → Bool :=
  fun _ a _ => decide (Allowed A a)

noncomputable def carpet (A : GridLaw) : Set (ℝ × ℝ) :=
  limitSet (deterministicRetention A) ()

variable {A : GridLaw}

lemma deterministic_retained (w : Word A) :
    Retained (deterministicRetention A) () w ↔ ∀ a ∈ w, Allowed A a := by
  constructor
  · intro h a ha
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    simpa [deterministicRetention] using h i
  · intro h i
    simpa [deterministicRetention] using h (w.get i) (List.get_mem w i)

lemma deterministic_descent (ha : ∃ a, Allowed A a) (root : Word A) :
    HasInfiniteDescentBelow (deterministicRetention A) () root := by
  obtain ⟨a, ha⟩ := ha
  intro L
  refine ⟨fun _ => a, fun l => ?_⟩
  change decide (Allowed A ((wordOfDigits (fun _ : Fin L => a)).get l)) = true
  apply decide_eq_true
  rw [List.get_eq_getElem, wordOfDigits_getElem _ (by simpa using l.isLt)]
  exact ha

lemma deterministic_not_bad : () ∉ badEvent (deterministicRetention A) := by
  simp [badEvent, deterministicRetention]

lemma GridLaw.exists_allowedRow {i : Fin A.M} (hi : i ∈ A.cols) :
    ∃ j, j ∈ A.rows i := by
  simpa [GridLaw.cols, GridLaw.rows] using hi

def SquareCode.Admissible {a : ℕ} (c : SquareCode A a) : Prop :=
  (∀ l, c.col l ∈ A.cols) ∧
    ∀ l, c.row l ∈ A.rows (c.col (Fin.castLE (A.bfloor_le a) l))

lemma admissible_region_meets_carpet_and_truncate {a k : ℕ} (hka : k ≤ a) {c : SquareCode A a}
    (ha : ∃ d, Allowed A d) (hc : c.Admissible) :
    (c.region ∩ (carpet A ∩ (c.truncate hka).region)).Nonempty := by
  classical
  let u : DigitWord A a := fun l =>
    (c.col l, if h : (l : ℕ) < bfloor A.Gamma a then c.row ⟨l, h⟩
      else (A.exists_allowedRow (hc.1 l)).choose)
  have hu (l : Fin a) : Allowed A (u l) := by
    unfold Allowed
    dsimp [u]
    split_ifs with h
    · have := hc.2 ⟨l, h⟩
      simpa [GridLaw.rows] using this
    · have := (A.exists_allowedRow (hc.1 l)).choose_spec
      simpa [GridLaw.rows] using this
  have hret : Retained (deterministicRetention A) () (wordOfDigits u) := by
    intro l
    change decide (Allowed A ((wordOfDigits u).get l)) = true
    apply decide_eq_true
    rw [List.get_eq_getElem, wordOfDigits_getElem u (by simpa using l.isLt)]
    exact hu _
  have hcell : c.MemCell (wordOfDigits u) := by
    refine ⟨length_wordOfDigits u, fun l => ?_, fun l => ?_⟩
    · rw [colD_wordOfDigits u l.isLt]
    · rw [rowD_wordOfDigits u (lt_of_lt_of_le l.isLt (A.bfloor_le a))]
      simp [u, l.isLt]
  obtain ⟨z, hzw, hzK⟩ := rect_inter_limitSet_nonempty hret (deterministic_descent ha _)
  exact ⟨z, rect_subset_region_of_memCell hcell hzw, hzK,
    rect_subset_truncate_region hka hcell hzw⟩

lemma carpet_assouad_upper (hm : 1 < A.m) : dimA (carpet A) ≤ A.sAdet :=
  dimA_limitSet_le_sAdet hm deterministic_not_bad

end FractalGeometry.Probability.GridPercolation
