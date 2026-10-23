import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.LinearCocycles.Regularity
import FractalGeometry.Symbolic.Past

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology Set Matrix

open scoped Matrix.Norms.L2Operator Real

namespace MatrixTuple

variable {ι : Type*} (A : ι → Matrix (Fin 2) (Fin 2) ℝ)

variable {A}

variable (A) in

def filtration (l₂ : ℝ) (x : ℤ → ι) : ℕ → Set (Fin 2 → ℝ)
  | 0 => univ
  | 1 => slowLine A l₂ x
  | _ => {0}

@[simp] theorem filtration_add_two (l₂ : ℝ) (x : ℤ → ι) (i : ℕ) :
    filtration A l₂ x (i + 2) = {0} := rfl

theorem filtration_succ_subset (l₂ : ℝ) (x : ℤ → ι) (i : ℕ) :
    filtration A l₂ x (i + 1) ⊆ filtration A l₂ x i := by
  rcases i with _ | _ | i
  · exact subset_univ _
  · intro v hv
    rw [filtration_add_two, mem_singleton_iff] at hv
    exact Or.inl hv
  · exact subset_rfl

theorem slowLine_congr {x y : ℤ → ι} (h : SamePast x y) (l₂ : ℝ) :
    slowLine A l₂ x = slowLine A l₂ y := by
  ext v
  simp only [slowLine, mem_ofPred_eq, hasPastRate_congr h]

theorem filtration_congr {x y : ℤ → ι} (h : SamePast x y) (l₂ : ℝ) (i : ℕ) :
    filtration A l₂ x i = filtration A l₂ y i := by
  rcases i with _ | _ | i
  · rfl
  · exact slowLine_congr h l₂
  · rfl

theorem slowLine_eq_cross {l₁ l₂ : ℝ} (hlt : l₂ < l₁) {x : ℤ → ι}
    (hx : x ∈ regularSet A l₁ l₂) :
    slowLine A l₂ x = {v | cross (dirVec (slowAngle A l₁ l₂ x)) v = 0} := by
  rw [slowLine_eq_span hlt (isRegularWith_slowAngle hlt hx)]
  ext v
  exact mem_span_iff_cross (dirVec_ne_zero _) v

theorem slowAngle_congr {l₁ l₂ : ℝ} (hlt : l₂ < l₁) {x y : ℤ → ι} (h : SamePast x y) :
    slowAngle A l₁ l₂ x = slowAngle A l₁ l₂ y := by
  by_cases hx : x ∈ regularSet A l₁ l₂
  · have hy : y ∈ regularSet A l₁ l₂ := mem_regularSet_of_samePast h hx
    exact (slowAngle_eq hlt hy (slowAngle_spec hx).1
      ((hasPastRate_congr h).1 (slowAngle_spec hx).2)).symm
  · have hy : y ∉ regularSet A l₁ l₂ := fun hy => hx (mem_regularSet_of_samePast h.symm hy)
    rw [slowAngle_of_notMem hx, slowAngle_of_notMem hy]

end MatrixTuple

end FractalGeometry
