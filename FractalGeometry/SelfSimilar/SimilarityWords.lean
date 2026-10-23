import Mathlib

namespace FractalGeometry

open scoped ENNReal

def simWord {κ : Type*} (r t : κ → ℝ) : List κ → ℝ → ℝ
  | [] => id
  | j :: u => (fun x => r j * x + t j) ∘ simWord r t u

@[simp] theorem simWord_nil {κ : Type*} (r t : κ → ℝ) : simWord r t [] = id := rfl

@[simp] theorem simWord_cons {κ : Type*} (r t : κ → ℝ) (j : κ) (u : List κ) :
    simWord r t (j :: u) = (fun x => r j * x + t j) ∘ simWord r t u := rfl

theorem simWord_append {κ : Type*} (r t : κ → ℝ) (u u' : List κ) :
    simWord r t (u ++ u') = simWord r t u ∘ simWord r t u' := by
  induction u with
  | nil => rfl
  | cons j u ih => simp [ih, Function.comp_assoc]

theorem simWord_apply {κ : Type*} (r t : κ → ℝ) (u : List κ) (x : ℝ) :
    simWord r t u x = (u.map r).prod * x + simWord r t u 0 := by
  induction u with
  | nil => simp
  | cons j u ih =>
    simp only [simWord_cons, Function.comp_apply, List.map_cons, List.prod_cons]
    rw [ih]; ring

end FractalGeometry
