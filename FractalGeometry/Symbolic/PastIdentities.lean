module

public import Mathlib
public import FractalGeometry.Symbolic.Shift
public import FractalGeometry.Symbolic.PastWords

@[expose] public section

namespace FractalGeometry


open MeasureTheory Filter Topology Set

theorem pastWord_shift_one {α : Type*} (y : ℤ → α) (n : ℕ) :
    pastWord (shift 1 y) (n + 1) = pastWord y n ++ [y 0] := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (1 : ℤ) + -(((n + 1 : ℕ) : ℤ) + 1) = -((n : ℤ) + 1) := by push_cast; ring
    rw [pastWord_succ, ih, pastWord_succ, shift_apply, List.cons_append, e]

theorem tendsto_add_div_succ_iff (f : ℕ → ℝ) (c l : ℝ) :
    Tendsto (fun n : ℕ => (f n + c) / ((n : ℝ) + 1)) atTop (𝓝 l) ↔
      Tendsto (fun n : ℕ => f n / n) atTop (𝓝 l) := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) :=
    tendsto_natCast_div_add_atTop 1
  have h2 : Tendsto (fun n : ℕ => c / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul c
  have h3 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
    simpa using h1.inv₀ one_ne_zero
  have h4 : Tendsto (fun n : ℕ => c / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat c
  constructor
  · intro h
    have key := (h.mul h3).sub h4
    rw [mul_one, sub_zero] at key
    refine key.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    have hn'' : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  · intro h
    have key := (h.mul h1).add h2
    rw [mul_one, add_zero] at key
    refine key.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    have hn'' : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp

end FractalGeometry
