import Mathlib
import GeometricMeasureTheory.Box.ModifiedBox
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.SelfAffine.Rectangular.OpenSet
import FractalGeometry.SelfAffine.Rectangular.Orientation
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.OrientationCoding
import FractalGeometry.Symbolic.Shift

open GeometricMeasureTheory

namespace FractalGeometry

open Filter Topology Finset


namespace RectangularIFS

variable {ι : Type*} (S : RectangularIFS ι)

structure Bounds (r M : ℝ) : Prop where
  r_nonneg : 0 ≤ r
  r_lt_one : r < 1
  abs_ratio_le : ∀ p, |S.ratio p| ≤ r
  abs_trans_le : ∀ p, |S.trans p| ≤ M

theorem exists_bounds [Finite ι] : ∃ r M, S.Bounds r M := by
  classical
  have := Fintype.ofFinite ι
  by_cases hι : Nonempty (ι × ZMod 2)
  · obtain ⟨p₁, -, h₁⟩ := Finset.exists_max_image Finset.univ (fun p => |S.ratio p|)
      Finset.univ_nonempty
    obtain ⟨p₂, -, h₂⟩ := Finset.exists_max_image Finset.univ (fun p => |S.trans p|)
      Finset.univ_nonempty
    exact ⟨|S.ratio p₁|, |S.trans p₂|, abs_nonneg _, S.abs_ratio_lt_one _,
      fun p => h₁ p (Finset.mem_univ _), fun p => h₂ p (Finset.mem_univ _)⟩
  · exact ⟨0, 0, le_rfl, zero_lt_one, fun p => (hι ⟨p⟩).elim, fun p => (hι ⟨p⟩).elim⟩

variable {S} {r M : ℝ}

theorem Bounds.abs_gDeriv_le (hS : S.Bounds r M) (u : List (ι × ZMod 2)) :
    |S.gDeriv u| ≤ r ^ u.length := by
  induction u with
  | nil => simp
  | cons p u ih =>
    rw [gDeriv_cons, abs_mul, List.length_cons, pow_succ']
    exact mul_le_mul (hS.abs_ratio_le p) ih (abs_nonneg _) hS.r_nonneg

variable (S)

def projBarTerm (y : ℤ → ι × ZMod 2) (k : ℕ) : ℝ := S.gDeriv (futureWord y k) * S.trans (y k)

noncomputable def projBar (y : ℤ → ι × ZMod 2) : ℝ := ∑' k, S.projBarTerm y k

theorem gWord_futureWord (y : ℤ → ι × ZMod 2) (n : ℕ) :
    S.gWord (futureWord y n) 0 = ∑ k ∈ range n, S.projBarTerm y k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [futureWord_succ, gWord_append, Function.comp_apply, gWord_apply, ih, sum_range_succ,
      projBarTerm]
    simp [g, add_comm]

variable {S}

theorem Bounds.summable_projBarTerm (hS : S.Bounds r M) (y : ℤ → ι × ZMod 2) :
    Summable (S.projBarTerm y) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hS.abs_trans_le (y 0))
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hS.r_nonneg hS.r_lt_one).mul_right M) fun k => ?_
  rw [projBarTerm, Real.norm_eq_abs, abs_mul]
  have h := hS.abs_gDeriv_le (futureWord y k)
  rw [length_futureWord] at h
  exact mul_le_mul h (hS.abs_trans_le _) (abs_nonneg _) (pow_nonneg hS.r_nonneg _)

theorem Bounds.tendsto_gWord (hS : S.Bounds r M) (y : ℤ → ι × ZMod 2) :
    Tendsto (fun n => S.gWord (futureWord y n) 0) atTop (𝓝 (S.projBar y)) := by
  simp only [gWord_futureWord]
  exact (hS.summable_projBarTerm y).hasSum.tendsto_sum_nat

variable (S)

theorem projBar_congr {y y' : ℤ → ι × ZMod 2} (h : ∀ k : ℕ, y k = y' k) :
    S.projBar y = S.projBar y' := by
  unfold projBar projBarTerm
  congr 1
  funext k
  rw [futureWord_congr y h k, h k]

def phiWord : List ι → ℝ × ℝ → ℝ × ℝ
  | [] => id
  | i :: w => S.phi i ∘ phiWord w

@[simp] theorem phiWord_nil : S.phiWord [] = id := rfl

@[simp] theorem phiWord_cons (i : ι) (w : List ι) :
    S.phiWord (i :: w) = S.phi i ∘ S.phiWord w := rfl

theorem coord_phiWord (c : ZMod 2) (w : List ι) (z : ℝ × ℝ) :
    coord c (S.phiWord w z) = S.gWord (S.codeWord c w) (coord (c + S.oWord w) z) := by
  induction w generalizing c with
  | nil => simp
  | cons i w ih =>
    rw [phiWord_cons, Function.comp_apply, coord_phi, ih, codeWord_cons, gWord_cons,
      Function.comp_apply, oWord_cons, add_assoc]

theorem oWord_append (w w' : List ι) : S.oWord (w ++ w') = S.oWord w + S.oWord w' := by
  simp [oWord]

theorem codeWord_append (c : ZMod 2) (w w' : List ι) :
    S.codeWord c (w ++ w') = S.codeWord c w ++ S.codeWord (c + S.oWord w) w' := by
  induction w generalizing c with
  | nil => simp
  | cons i w ih => simp [ih, add_assoc]

theorem oWord_futureWord (x : ℤ → ι) (n : ℕ) : S.oWord (futureWord x n) = eps S.o x n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [futureWord_succ, oWord_append, ih, Nat.cast_succ, eps_add_one]
    simp

theorem codeWord_futureWord_tau (x : ℤ → ι) (n : ℕ) :
    S.codeWord 0 (futureWord x n) = futureWord (tau S.o x) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [futureWord_succ, futureWord_succ, codeWord_append, ih, oWord_futureWord]
    simp

theorem codeWord_futureWord_omega (x : ℤ → ι) (n : ℕ) :
    S.codeWord 1 (futureWord x n) = futureWord (omega S.o x) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [futureWord_succ, futureWord_succ, codeWord_append, ih, oWord_futureWord]
    simp [add_comm]

noncomputable def proj (x : ℤ → ι) : ℝ × ℝ :=
  (S.projBar (tau S.o x), S.projBar (omega S.o x))

variable {S}

theorem Bounds.tendsto_phiWord (hS : S.Bounds r M) (x : ℤ → ι) :
    Tendsto (fun n => S.phiWord (futureWord x n) 0) atTop (𝓝 (S.proj x)) := by
  have h0 : ∀ n, (S.phiWord (futureWord x n) 0).1 = S.gWord (futureWord (tau S.o x) n) 0 := by
    intro n
    have h := S.coord_phiWord 0 (futureWord x n) 0
    rw [codeWord_futureWord_tau] at h
    simpa [coord] using h
  have h1 : ∀ n, (S.phiWord (futureWord x n) 0).2 = S.gWord (futureWord (omega S.o x) n) 0 := by
    intro n
    have h := S.coord_phiWord 1 (futureWord x n) 0
    rw [codeWord_futureWord_omega] at h
    simpa [coord] using h
  have := (hS.tendsto_gWord (tau S.o x)).prodMk_nhds (hS.tendsto_gWord (omega S.o x))
  refine this.congr fun n => ?_
  exact Prod.ext (h0 n).symm (h1 n).symm

theorem continuous_phi (S : RectangularIFS ι) (i : ι) : Continuous (S.phi i) := by
  unfold phi coord
  split_ifs <;> fun_prop

theorem Bounds.proj_eq (hS : S.Bounds r M) (x : ℤ → ι) :
    S.proj x = S.phi (x 0) (S.proj (shift 1 x)) := by
  have h1 : Tendsto (fun n => S.phiWord (futureWord x (n + 1)) 0) atTop (𝓝 (S.proj x)) :=
    (tendsto_add_atTop_iff_nat 1).2 (hS.tendsto_phiWord x)
  have h2 : Tendsto (fun n => S.phi (x 0) (S.phiWord (futureWord (shift 1 x) n) 0)) atTop
      (𝓝 (S.phi (x 0) (S.proj (shift 1 x)))) :=
    ((S.continuous_phi (x 0)).tendsto _).comp (hS.tendsto_phiWord (shift 1 x))
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  rw [futureWord_succ', phiWord_cons, Function.comp_apply]

variable (S)

theorem eps_congr {x x' : ℤ → ι} (h : ∀ k : ℕ, x k = x' k) (n : ℕ) :
    eps S.o x n = eps S.o x' n := by
  rw [eps_natCast, eps_natCast]
  exact Finset.sum_congr rfl fun j _ => by rw [h j]

theorem proj_congr {x x' : ℤ → ι} (h : ∀ k : ℕ, x k = x' k) : S.proj x = S.proj x' := by
  unfold proj
  congr 1
  · exact S.projBar_congr fun k => by rw [tau_apply, tau_apply, h k, S.eps_congr h k]
  · exact S.projBar_congr fun k => by rw [omega_apply, omega_apply, h k, S.eps_congr h k]

def attractor : Set (ℝ × ℝ) := Set.range S.proj

variable {S}

theorem Bounds.attractor_eq_iUnion (hS : S.Bounds r M) :
    S.attractor = ⋃ i, S.phi i '' S.attractor := by
  ext z
  simp only [attractor, Set.mem_range, Set.mem_iUnion, Set.mem_image, exists_exists_eq_and]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x 0, shift 1 x, (hS.proj_eq x).symm⟩
  · rintro ⟨i, x, rfl⟩
    refine ⟨fun k => if k = 0 then i else x (k - 1), ?_⟩
    rw [hS.proj_eq]
    simp only [ite_true]
    congr 1
    apply S.proj_congr
    intro k
    have : (1 : ℤ) + k ≠ 0 := by omega
    simp [this]

end RectangularIFS

end FractalGeometry
