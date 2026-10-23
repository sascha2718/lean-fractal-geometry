import Mathlib
import FractalGeometry.LinearCocycles.Monomial

namespace FractalGeometry

open Polynomial Matrix

def IsProximalMatrix (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ l₁ l₂ : ℝ, |l₁| ≠ |l₂| ∧
    A.charpoly = (Polynomial.X - Polynomial.C l₁) * (Polynomial.X - Polynomial.C l₂)

theorem isProximalMatrix_iff_trace_det {A : Matrix (Fin 2) (Fin 2) ℝ} :
    IsProximalMatrix A ↔ ∃ l₁ l₂ : ℝ, |l₁| ≠ |l₂| ∧ A.trace = l₁ + l₂ ∧ A.det = l₁ * l₂ := by
  constructor
  · rintro ⟨l₁, l₂, hne, h⟩
    rw [Matrix.charpoly_fin_two] at h
    have h0 := congrArg (Polynomial.eval 0) h
    have h1 := congrArg (Polynomial.eval 1) h
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at h0 h1
    refine ⟨l₁, l₂, hne, ?_, ?_⟩
    · linarith
    · linarith
  · rintro ⟨l₁, l₂, hne, htr, hdet⟩
    refine ⟨l₁, l₂, hne, ?_⟩
    rw [Matrix.charpoly_fin_two, htr, hdet, C_add, C_mul]
    ring

theorem isProximalMatrix_monomialMatrix_zero {a b : ℝ} :
    IsProximalMatrix (monomialMatrix 0 a b) ↔ |a| ≠ |b| := by
  rw [isProximalMatrix_iff_trace_det]
  simp only [monomialMatrix_zero, Matrix.trace_fin_two_of, Matrix.det_fin_two_of, mul_zero, sub_zero]
  constructor
  · rintro ⟨l₁, l₂, hne, htr, hdet⟩
    have h : (l₁ - a) * (l₁ - b) = 0 := by
      have hb : b = l₁ + l₂ - a := by linarith
      subst hb
      linear_combination hdet
    rcases mul_eq_zero.1 h with h | h
    · have ha : l₁ = a := by linarith
      have hb : l₂ = b := by linarith
      rwa [ha, hb] at hne
    · have hb : l₁ = b := by linarith
      have ha : l₂ = a := by linarith
      rw [hb, ha] at hne
      exact hne.symm
  · intro h
    exact ⟨a, b, h, rfl, rfl⟩

theorem not_isProximalMatrix_monomialMatrix_one (a b : ℝ) : ¬ IsProximalMatrix (monomialMatrix 1 a b) := by
  rw [isProximalMatrix_iff_trace_det]
  simp only [monomialMatrix_one, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  rintro ⟨l₁, l₂, hne, htr, -⟩
  have h : l₂ = -l₁ := by linarith
  exact hne (by rw [h, abs_neg])

end FractalGeometry
