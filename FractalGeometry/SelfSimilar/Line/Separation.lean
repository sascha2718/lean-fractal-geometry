import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.SelfSimilar.Line.Defs
import FractalGeometry.SelfSimilar.Line.Words
import FractalGeometry.SelfSimilar.SimilarityWords

open FractalGeometry.Ergodic

namespace FractalGeometry

open scoped ENNReal

namespace LineIFS

variable {ι : Type*} (S : LineIFS ι)

def gWord : List (ι) → ℝ → ℝ
  | [] => id
  | p :: u => S.g p ∘ gWord u

@[simp] theorem gWord_nil : S.gWord [] = id := rfl

@[simp] theorem gWord_cons (p : ι) (u : List (ι)) :
    S.gWord (p :: u) = S.g p ∘ S.gWord u := rfl

theorem gWord_apply (u : List (ι)) (t : ℝ) :
    S.gWord u t = S.gDeriv u * t + S.gWord u 0 := by
  induction u with
  | nil => simp
  | cons p u ih =>
    simp only [gWord_cons, Function.comp_apply, gDeriv_cons, g]
    rw [ih]; ring

theorem gWord_append (u u' : List (ι)) :
    S.gWord (u ++ u') = S.gWord u ∘ S.gWord u' := by
  induction u with
  | nil => rfl
  | cons p u ih => simp [ih, Function.comp_assoc]

theorem gDeriv_append (u u' : List (ι)) :
    S.gDeriv (u ++ u') = S.gDeriv u * S.gDeriv u' := by
  simp [gDeriv]

noncomputable def gap (n : ℕ) : ℝ≥0∞ :=
  ⨅ (u : List (ι)) (u' : List (ι)) (_ : u.length = n) (_ : u'.length = n)
    (_ : u ≠ u') (_ : S.gDeriv u = S.gDeriv u'), ENNReal.ofReal |S.gWord u 0 - S.gWord u' 0|

def ExpSeparation : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n : ℕ → ℕ, StrictMono n ∧ ∀ k, ENNReal.ofReal (c ^ n k) ≤ S.gap (n k)

theorem gap_le {n : ℕ} {u u' : List (ι)} (hu : u.length = n) (hu' : u'.length = n)
    (hne : u ≠ u') (hd : S.gDeriv u = S.gDeriv u') :
    S.gap n ≤ ENNReal.ofReal |S.gWord u 0 - S.gWord u' 0| :=
  iInf_le_of_le u <| iInf_le_of_le u' <| iInf_le_of_le hu <| iInf_le_of_le hu' <|
    iInf_le_of_le hne <| iInf_le _ hd

theorem gap_succ_le [Nonempty ι] (m : ℕ) : S.gap (m + 1) ≤ S.gap m := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine le_iInf fun u => le_iInf fun u' => le_iInf fun hu => le_iInf fun hu' =>
    le_iInf fun hne => le_iInf fun hd => ?_
  have key : S.gWord (u ++ [i]) 0 - S.gWord (u' ++ [i]) 0 =
      S.gWord u 0 - S.gWord u' 0 := by
    rw [gWord_append, gWord_append, Function.comp_apply, Function.comp_apply,
      S.gWord_apply u, S.gWord_apply u', hd]
    ring
  rw [← key]
  refine S.gap_le (by simp [hu]) (by simp [hu']) ?_ ?_
  · simpa using hne
  · rw [gDeriv_append, gDeriv_append, hd]

end LineIFS

end FractalGeometry
