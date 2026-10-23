import Mathlib
import GeometricMeasureTheory.Box.ModifiedBox
import FractalGeometry.LinearCocycles.Monomial
import FractalGeometry.SelfAffine.Rectangular.Attractor
import FractalGeometry.SelfAffine.Rectangular.Coding
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.Shift

open GeometricMeasureTheory

namespace FractalGeometry

open MeasureTheory Filter Topology Set

universe u

namespace RectangularIFS

section Geometry

variable {ι : Type u} (S : RectangularIFS ι)

noncomputable def phiInv (i : ι) (w : ℝ × ℝ) : ℝ × ℝ :=
  if S.o i = 0 then ((w.1 - (S.v i).1) / S.a i, (w.2 - (S.v i).2) / S.b i)
  else ((w.2 - (S.v i).2) / S.b i, (w.1 - (S.v i).1) / S.a i)

theorem phiInv_phi (i : ι) (z : ℝ × ℝ) : S.phiInv i (S.phi i z) = z := by
  have ha := S.a_ne_zero i
  have hb := S.b_ne_zero i
  rcases zmod_two_cases (S.o i) with h | h
  · simp [phiInv, phi, h, ha, hb]
  · simp [phiInv, phi, h, ha, hb, show (1 : ZMod 2) + 1 = 0 from by decide]

theorem phi_phiInv (i : ι) (w : ℝ × ℝ) : S.phi i (S.phiInv i w) = w := by
  have ha := S.a_ne_zero i
  have hb := S.b_ne_zero i
  rcases zmod_two_cases (S.o i) with h | h
  · simp [phiInv, phi, h, mul_div_cancel₀, ha, hb]
  · simp [phiInv, phi, h, mul_div_cancel₀, ha, hb, show (1 : ZMod 2) + 1 = 0 from by decide]

theorem phiWord_mem {U : Set (ℝ × ℝ)} (hsub : ∀ i, S.phi i '' U ⊆ U) (w : List ι) {z : ℝ × ℝ}
    (hz : z ∈ U) : S.phiWord w z ∈ U := by
  induction w with
  | nil => exact hz
  | cons i w ih => exact hsub i ⟨_, ih, rfl⟩

variable {S} {r M : ℝ}

theorem Bounds.dist_phiWord_le (hS : S.Bounds r M) (w : List ι) (z z' : ℝ × ℝ) :
    dist (S.phiWord w z) (S.phiWord w z') ≤ r ^ w.length * dist z z' := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [phiWord_cons, Function.comp_apply, Function.comp_apply, List.length_cons, pow_succ',
      mul_assoc]
    exact (hS.dist_phi_le i _ _).trans (mul_le_mul_of_nonneg_left ih hS.r_nonneg)

theorem Bounds.proj_eq_phiWord (hS : S.Bounds r M) (x : ℤ → ι) (n : ℕ) :
    S.proj x = S.phiWord (futureWord x n) (S.proj (shift n x)) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [futureWord_succ', phiWord_cons, Function.comp_apply, hS.proj_eq x, ih (shift 1 x),
      shift_shift, Nat.cast_succ, add_comm]

variable (S)

end Geometry

end RectangularIFS

end FractalGeometry
