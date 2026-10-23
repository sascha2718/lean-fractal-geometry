import Mathlib
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Process

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory ProbabilityTheory

open scoped ENNReal

def Allowed (A : GridLaw) (a : Fin A.M × Fin A.N) : Prop := 0 < A.p a.1 a.2

noncomputable instance (A : GridLaw) (a : Fin A.M × Fin A.N) : Decidable (Allowed A a) :=
  Classical.dec _

variable {A : GridLaw} {Ω : Type*} [MeasurableSpace Ω]

def badEvent (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) : Set Ω :=
  ⋃ q : Word A × (Fin A.M × Fin A.N),
    if Allowed A q.2 then (∅ : Set Ω) else {ω | X q.1 q.2 ω = true}

omit [MeasurableSpace Ω] in

lemma allowed_of_retained {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool} {ω : Ω}
    (hω : ω ∉ badEvent X) {w : Word A} (hw : Retained X ω w) :
    ∀ a ∈ w, Allowed A a := by
  intro a ha
  obtain ⟨l, hl⟩ := List.mem_iff_get.mp ha
  by_contra hcon
  refine hω ?_
  refine Set.mem_iUnion.mpr ⟨(w.take l, w.get l), ?_⟩
  rw [ite_eq_right (by rw [hl]; exact hcon)]
  exact hw l

end FractalGeometry.Probability.GridPercolation
