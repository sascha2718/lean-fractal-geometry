import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.SelfSimilar.Line.Defs
import FractalGeometry.SelfSimilar.Line.Separation
import FractalGeometry.SelfSimilar.Line.Words
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open Filter Topology Finset

namespace LineIFS

variable {ι : Type*} (S : LineIFS ι)

structure Bounds (r M : ℝ) : Prop where
  r_nonneg : 0 ≤ r
  r_lt_one : r < 1
  abs_ratio_le : ∀ p, |S.ratio p| ≤ r
  abs_trans_le : ∀ p, |S.trans p| ≤ M

theorem exists_bounds [Finite ι] : ∃ r M, S.Bounds r M := by
  classical
  have := Fintype.ofFinite ι
  by_cases hι : Nonempty (ι)
  · obtain ⟨p₁, -, h₁⟩ := Finset.exists_max_image Finset.univ (fun p => |S.ratio p|)
      Finset.univ_nonempty
    obtain ⟨p₂, -, h₂⟩ := Finset.exists_max_image Finset.univ (fun p => |S.trans p|)
      Finset.univ_nonempty
    exact ⟨|S.ratio p₁|, |S.trans p₂|, abs_nonneg _, S.abs_ratio_lt_one _,
      fun p => h₁ p (Finset.mem_univ _), fun p => h₂ p (Finset.mem_univ _)⟩
  · exact ⟨0, 0, le_rfl, zero_lt_one, fun p => (hι ⟨p⟩).elim, fun p => (hι ⟨p⟩).elim⟩

variable {S} {r M : ℝ}

theorem Bounds.abs_gDeriv_le (hS : S.Bounds r M) (u : List (ι)) :
    |S.gDeriv u| ≤ r ^ u.length := by
  induction u with
  | nil => simp
  | cons p u ih =>
    rw [gDeriv_cons, abs_mul, List.length_cons, pow_succ']
    exact mul_le_mul (hS.abs_ratio_le p) ih (abs_nonneg _) hS.r_nonneg

variable (S)

def codeTerm (y : ℤ → ι) (k : ℕ) : ℝ := S.gDeriv (futureWord y k) * S.trans (y k)

noncomputable def code (y : ℤ → ι) : ℝ := ∑' k, S.codeTerm y k

theorem gWord_futureWord (y : ℤ → ι) (n : ℕ) :
    S.gWord (futureWord y n) 0 = ∑ k ∈ range n, S.codeTerm y k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [futureWord_succ, gWord_append, Function.comp_apply, gWord_apply, ih, sum_range_succ,
      codeTerm]
    simp [g, add_comm]

variable {S}

theorem Bounds.summable_codeTerm (hS : S.Bounds r M) (y : ℤ → ι) :
    Summable (S.codeTerm y) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hS.abs_trans_le (y 0))
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hS.r_nonneg hS.r_lt_one).mul_right M) fun k => ?_
  rw [codeTerm, Real.norm_eq_abs, abs_mul]
  have h := hS.abs_gDeriv_le (futureWord y k)
  rw [length_futureWord] at h
  exact mul_le_mul h (hS.abs_trans_le _) (abs_nonneg _) (pow_nonneg hS.r_nonneg _)

theorem Bounds.tendsto_gWord (hS : S.Bounds r M) (y : ℤ → ι) :
    Tendsto (fun n => S.gWord (futureWord y n) 0) atTop (𝓝 (S.code y)) := by
  simp only [gWord_futureWord]
  exact (hS.summable_codeTerm y).hasSum.tendsto_sum_nat

theorem Bounds.code_eq (hS : S.Bounds r M) (y : ℤ → ι) :
    S.code y = S.g (y 0) (S.code (shift 1 y)) := by
  have h1 : Tendsto (fun n => S.gWord (futureWord y (n + 1)) 0) atTop (𝓝 (S.code y)) :=
    (tendsto_add_atTop_iff_nat 1).2 (hS.tendsto_gWord y)
  have h2 : Tendsto (fun n => S.g (y 0) (S.gWord (futureWord (shift 1 y) n) 0)) atTop
      (𝓝 (S.g (y 0) (S.code (shift 1 y)))) := by
    have hc : Continuous (S.g (y 0)) := by unfold g; fun_prop
    exact (hc.tendsto _).comp (hS.tendsto_gWord (shift 1 y))
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  rw [futureWord_succ', gWord_cons, Function.comp_apply]

variable (S)

theorem code_congr {y y' : ℤ → ι} (h : ∀ k : ℕ, y k = y' k) :
    S.code y = S.code y' := by
  unfold code codeTerm
  congr 1
  funext k
  rw [futureWord_congr y h k, h k]

variable {S}

variable (S)

variable {S}

end LineIFS

end FractalGeometry
