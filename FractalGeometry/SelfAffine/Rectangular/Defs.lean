import Mathlib
import GeometricMeasureTheory.Box.ModifiedBox
import FractalGeometry.LinearCocycles.Monomial

open GeometricMeasureTheory

namespace FractalGeometry

open Matrix

structure RectangularIFS (ι : Type*) where

  o : ι → ZMod 2

  a : ι → ℝ

  b : ι → ℝ

  v : ι → ℝ × ℝ
  a_ne_zero : ∀ i, a i ≠ 0
  b_ne_zero : ∀ i, b i ≠ 0
  abs_a_lt_one : ∀ i, |a i| < 1
  abs_b_lt_one : ∀ i, |b i| < 1

namespace RectangularIFS

variable {ι : Type*} (S : RectangularIFS ι)

def coord (c : ZMod 2) (z : ℝ × ℝ) : ℝ := if c = 0 then z.1 else z.2

@[simp] theorem coord_zero (z : ℝ × ℝ) : coord 0 z = z.1 := rfl
@[simp] theorem coord_one (z : ℝ × ℝ) : coord 1 z = z.2 := rfl

def ratio (p : ι × ZMod 2) : ℝ := if p.2 = 0 then S.a p.1 else S.b p.1

@[simp] theorem ratio_zero (i : ι) : S.ratio (i, 0) = S.a i := rfl
@[simp] theorem ratio_one (i : ι) : S.ratio (i, 1) = S.b i := rfl

def trans (p : ι × ZMod 2) : ℝ := coord p.2 (S.v p.1)

def g (p : ι × ZMod 2) (t : ℝ) : ℝ := S.ratio p * t + S.trans p

def phi (i : ι) (z : ℝ × ℝ) : ℝ × ℝ :=
  (S.a i * coord (S.o i) z + (S.v i).1, S.b i * coord (S.o i + 1) z + (S.v i).2)

theorem ratio_ne_zero (p : ι × ZMod 2) : S.ratio p ≠ 0 := by
  unfold ratio; split_ifs <;> [exact S.a_ne_zero _; exact S.b_ne_zero _]

theorem abs_ratio_lt_one (p : ι × ZMod 2) : |S.ratio p| < 1 := by
  unfold ratio; split_ifs <;> [exact S.abs_a_lt_one _; exact S.abs_b_lt_one _]

theorem coord_phi (c : ZMod 2) (i : ι) (z : ℝ × ℝ) :
    coord c (S.phi i z) = S.g (i, c) (coord (c + S.o i) z) := by
  rcases zmod_two_cases c with rfl | rfl
  · simp [phi, g, trans]
  · simp [phi, g, trans, add_comm]

def oWord (w : List ι) : ZMod 2 := (w.map S.o).sum

def codeWord : ZMod 2 → List ι → List (ι × ZMod 2)
  | _, [] => []
  | c, i :: w => (i, c) :: codeWord (c + S.o i) w

def gDeriv (u : List (ι × ZMod 2)) : ℝ := (u.map S.ratio).prod

@[simp] theorem gDeriv_nil : S.gDeriv [] = 1 := rfl
@[simp] theorem codeWord_nil (c : ZMod 2) : S.codeWord c [] = [] := rfl

@[simp] theorem oWord_nil : S.oWord [] = 0 := rfl

@[simp] theorem oWord_cons (i : ι) (w : List ι) : S.oWord (i :: w) = S.o i + S.oWord w := by
  simp [oWord]

@[simp] theorem codeWord_cons (c : ZMod 2) (i : ι) (w : List ι) :
    S.codeWord c (i :: w) = (i, c) :: S.codeWord (c + S.o i) w := rfl

@[simp] theorem length_codeWord (c : ZMod 2) (w : List ι) :
    (S.codeWord c w).length = w.length := by
  induction w generalizing c with
  | nil => rfl
  | cons i w ih => simp [ih]

@[simp] theorem gDeriv_cons (p : ι × ZMod 2) (u : List (ι × ZMod 2)) :
    S.gDeriv (p :: u) = S.ratio p * S.gDeriv u := by
  simp [gDeriv]

theorem gDeriv_ne_zero (u : List (ι × ZMod 2)) : S.gDeriv u ≠ 0 := by
  induction u with
  | nil => simp
  | cons p u ih => simpa using ⟨S.ratio_ne_zero p, ih⟩

end RectangularIFS

end FractalGeometry
