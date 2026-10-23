import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.ParityShift
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Set

section Metric

variable {α : Type*}

def DiffersAt (x y : ℤ → α) (n : ℕ) : Prop := ∃ k : ℤ, k.natAbs = n ∧ x k ≠ y k

open Classical in

noncomputable def symDist (x y : ℤ → α) : ℝ :=
  if h : ∃ n, DiffersAt x y n then (1 / 2 : ℝ) ^ Nat.find h else 0

theorem symDist_nonneg (x y : ℤ → α) : 0 ≤ symDist x y := by
  unfold symDist
  split_ifs <;> positivity

theorem symDist_lt_pow_iff {x y : ℤ → α} (m : ℕ) :
    symDist x y < (1 / 2 : ℝ) ^ m ↔ ∀ k : ℤ, k.natAbs ≤ m → y k = x k := by
  classical
  unfold symDist
  by_cases hd : ∃ n, DiffersAt x y n
  · rw [dite_eq_left hd, pow_lt_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num),
      Nat.lt_find_iff]
    constructor
    · intro h k hk
      by_contra hne
      exact h k.natAbs hk ⟨k, rfl, Ne.symm hne⟩
    · rintro h n hn ⟨k, rfl, hk⟩
      exact hk (h k hn).symm
  · rw [dite_eq_right hd]
    refine ⟨fun _ k _ => ?_, fun _ => by positivity⟩
    by_contra hne
    exact hd ⟨k.natAbs, k, rfl, Ne.symm hne⟩

theorem symDist_le_one (x y : ℤ → α) : symDist x y ≤ 1 := by
  unfold symDist
  split_ifs
  · exact pow_le_one₀ (by norm_num) (by norm_num)
  · exact zero_le_one

end Metric

section Gibbs

variable {ι : Type*} [MeasurableSpace ι] {o : ι → ZMod 2}
  {f : (ℤ → ι × ZMod 2) → ℝ} {ν : Measure (ℤ → ι × ZMod 2)} {P C : ℝ}

def IsGibbsPotential (o : ι → ZMod 2) (f : (ℤ → ι × ZMod 2) → ℝ) (ν : Measure (ℤ → ι × ZMod 2))
    (P C : ℝ) : Prop :=
  0 < C ∧ ∀ y ∈ subshift o, ∀ n : ℕ, 0 < n →
    C⁻¹ * Real.exp (-(n * P) + birkhoffSum (shift 1) f n y) ≤
        ν.real (cylinder fun k : Fin n => y k) ∧
      ν.real (cylinder fun k : Fin n => y k) ≤
        C * Real.exp (-(n * P) + birkhoffSum (shift 1) f n y)

theorem IsGibbsPotential.one_le (h : IsGibbsPotential o f ν P C) {y : ℤ → ι × ZMod 2}
    (hy : y ∈ subshift o) : 1 ≤ C := by
  obtain ⟨hC, hb⟩ := h
  have h1 : C⁻¹ ≤ C :=
    le_of_mul_le_mul_right ((hb y hy 1 one_pos).1.trans (hb y hy 1 one_pos).2) (Real.exp_pos _)
  by_contra hlt
  have h2 : 1 < C⁻¹ := (one_lt_inv₀ hC).2 (not_le.1 hlt)
  linarith

variable [MeasurableSingletonClass ι]

end Gibbs

end FractalGeometry
