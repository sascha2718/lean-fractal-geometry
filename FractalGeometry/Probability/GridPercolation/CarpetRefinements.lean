import FractalGeometry.Probability.GridPercolation.DeterministicCarpet

namespace FractalGeometry.Probability.GridPercolation

open FractalGeometry.Dimension.PhiAssouad
open scoped ENNReal

variable {A : GridLaw}

def constantCode (i : Fin A.M) (j : Fin A.N) (k : ℕ) : SquareCode A k :=
  (fun _ => i, fun _ => j)

abbrev CarpetRowChoices (A : GridLaw) (i : Fin A.M) (k q : ℕ) :=
  Fin (bfloor A.Gamma (k + q) - bfloor A.Gamma k) → {j // j ∈ A.rows i}

abbrev CarpetColumnChoices (A : GridLaw) (q : ℕ) := Fin q → {i // i ∈ A.cols}

noncomputable def carpetRefinement (i : Fin A.M) (j : Fin A.N) (k q : ℕ)
    (s : CarpetRowChoices A i k q) (w : CarpetColumnChoices A q) : SquareCode A (k + q) :=
  (fun l => if h : (l : ℕ) < k then i else
      (w ⟨l - k, by have := l.isLt; omega⟩).1,
   fun l => if h : (l : ℕ) < bfloor A.Gamma k then j else
      (s ⟨l - bfloor A.Gamma k, by have := l.isLt; omega⟩).1)

lemma carpetRefinement_truncate (i : Fin A.M) (j : Fin A.N) (k q : ℕ)
    (s : CarpetRowChoices A i k q) (w : CarpetColumnChoices A q) :
    (carpetRefinement i j k q s w).truncate (Nat.le_add_right k q) = constantCode i j k := by
  apply Prod.ext <;> funext l <;>
    simp [SquareCode.truncate, SquareCode.col, SquareCode.row, carpetRefinement, constantCode, l.isLt]

lemma carpetRefinement_injective (i : Fin A.M) (j : Fin A.N) (k q : ℕ) :
    Function.Injective (fun p : CarpetRowChoices A i k q × CarpetColumnChoices A q =>
      carpetRefinement i j k q p.1 p.2) := by
  rintro ⟨s, w⟩ ⟨s', w'⟩ h
  have hs : s = s' := by
    funext l
    apply Subtype.ext
    have hb := A.bfloor_mono (Nat.le_add_right k q)
    have hidx : bfloor A.Gamma k + l < bfloor A.Gamma (k + q) := by have := l.isLt; omega
    have hrow := congrFun (congrArg Prod.snd h) ⟨bfloor A.Gamma k + l, hidx⟩
    simpa [carpetRefinement, show ¬ (bfloor A.Gamma k + (l : ℕ) < bfloor A.Gamma k) by omega]
      using hrow
  have hw : w = w' := by
    funext l
    apply Subtype.ext
    have hcol := congrFun (congrArg Prod.fst h) (Fin.natAdd k l)
    simpa [carpetRefinement, show ¬ (k + (l : ℕ) < k) by omega] using hcol
  exact Prod.ext hs hw

lemma carpetRefinement_admissible {i : Fin A.M} {j : Fin A.N} (hj : j ∈ A.rows i)
    {k q : ℕ} (hb : bfloor A.Gamma (k + q) ≤ k)
    (s : CarpetRowChoices A i k q) (w : CarpetColumnChoices A q) :
    (carpetRefinement i j k q s w).Admissible := by
  have hi : i ∈ A.cols := by
    have hp : 0 < A.p i j := by simpa [GridLaw.rows] using hj
    simpa [GridLaw.cols] using (show ∃ j, 0 < A.p i j from ⟨j, hp⟩)
  constructor
  · intro l
    dsimp [carpetRefinement, SquareCode.col]
    split_ifs
    · exact hi
    · exact (w _).2
  · intro l
    have hl : (l : ℕ) < k := l.isLt.trans_le hb
    simp only [carpetRefinement, SquareCode.row, SquareCode.col, Fin.val_castLE, dite_eq_left hl]
    split_ifs
    · exact hj
    · exact (s _).2

theorem carpet_local_cover_lower {i : Fin A.M} {j : Fin A.N} (hj : j ∈ A.rows i)
    {k q : ℕ} (hb : bfloor A.Gamma (k + q) ≤ k) :
    ((A.B i ^ (bfloor A.Gamma (k + q) - bfloor A.Gamma k) * A.Ax ^ q : ℕ) : ℕ∞) ≤
      25 * coverNum (gridScale A.M (k + q)) (carpet A ∩ (constantCode i j k).region) := by
  classical
  let f := fun p : CarpetRowChoices A i k q × CarpetColumnChoices A q =>
    carpetRefinement i j k q p.1 p.2
  let T := Finset.univ.image f
  have hT : ∀ c ∈ T, (c.region ∩ (carpet A ∩ (constantCode i j k).region)).Nonempty := by
    intro c hc
    obtain ⟨⟨s, w⟩, _, rfl⟩ := Finset.mem_image.mp hc
    have ha : ∃ d, Allowed A d := ⟨(i, j), by simpa [Allowed, GridLaw.rows] using hj⟩
    have h := admissible_region_meets_carpet_and_truncate (Nat.le_add_right k q) ha
      (carpetRefinement_admissible hj hb s w)
    simpa only [carpetRefinement_truncate] using h
  have hcard : T.card = A.B i ^ (bfloor A.Gamma (k + q) - bfloor A.Gamma k) * A.Ax ^ q := by
    rw [Finset.card_image_of_injective _ (carpetRefinement_injective i j k q), Finset.card_univ]
    simp [CarpetRowChoices, CarpetColumnChoices, Fintype.card_prod,
      GridLaw.B_eq_card_rows, GridLaw.Ax_eq_card_cols]
  have h := card_le_mul_coverNum (A := A) 1 T hT (r := gridScale A.M (k + q)) (by
    simp only [gridScale_eq_inv_pow, Nat.cast_one, one_mul, le_refl])
  rw [hcard] at h
  norm_num at h ⊢
  exact h

end FractalGeometry.Probability.GridPercolation
