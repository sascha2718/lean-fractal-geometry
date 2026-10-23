import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open Filter MeasureTheory Topology

open scoped ENNReal Matrix.Norms.L2Operator

section Concat

variable {α : Type*}

def concat (n : ℕ) [NeZero n] (y : ℤ → (Fin n → α)) : ℤ → α :=
  fun k => y (k / n) ⟨(k % n).toNat % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩

theorem concat_shift (n : ℕ) [NeZero n] (y : ℤ → (Fin n → α)) :
    concat n (shift 1 y) = shift (n : ℤ) (concat n y) := by
  have hn : (n : ℤ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  funext k
  have hsplit : (n : ℤ) + k = k + 1 * (n : ℤ) := by ring
  have hdiv : ((n : ℤ) + k) / (n : ℤ) = 1 + k / (n : ℤ) := by
    rw [hsplit, Int.add_mul_ediv_right _ _ hn, add_comm]
  have hmod : ((n : ℤ) + k) % (n : ℤ) = k % (n : ℤ) := by
    rw [hsplit, Int.add_mul_emod_self_right]
  simp only [concat, shift_apply]
  rw [hdiv]
  congr 1
  refine Fin.ext ?_
  show (k % (n : ℤ)).toNat % n = (((n : ℤ) + k) % (n : ℤ)).toNat % n
  rw [hmod]

theorem concat_coe (n : ℕ) [NeZero n] (y : ℤ → (Fin n → α)) (k : Fin n) :
    concat n y (k : ℤ) = y 0 k := by
  have h0 : (0 : ℤ) ≤ ((k : ℕ) : ℤ) := Int.natCast_nonneg _
  have h1 : ((k : ℕ) : ℤ) < (n : ℤ) := by exact_mod_cast k.2
  have hdiv : ((k : ℕ) : ℤ) / (n : ℤ) = 0 := Int.ediv_eq_zero_of_lt h0 h1
  have hidx : (((k : ℕ) : ℤ) % (n : ℤ)).toNat % n = (k : ℕ) := by
    rw [Int.emod_eq_of_lt h0 h1, Int.toNat_natCast, Nat.mod_eq_of_lt k.2]
  simp only [concat]
  rw [hdiv]
  congr 1
  exact Fin.ext hidx

variable [MeasurableSpace α]

theorem measurable_concat (n : ℕ) [NeZero n] :
    Measurable (concat n : (ℤ → (Fin n → α)) → ℤ → α) :=
  Measurable.of_eval fun _ => (measurable_pi_apply _).comp (measurable_pi_apply _)

end Concat

end FractalGeometry
