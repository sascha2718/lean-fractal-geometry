import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.LinearCocycles.Monomial
import FractalGeometry.LinearCocycles.MonomialSingularValues
import FractalGeometry.LinearCocycles.SingularValue
import FractalGeometry.Pressure.Rectangular.Defs
import FractalGeometry.Pressure.Rectangular.Exponents
import FractalGeometry.Pressure.Rectangular.Matrices
import FractalGeometry.SelfAffine.Rectangular.Coding
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.SelfAffine.Rectangular.Orientation
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.OrientationCoding

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory

theorem sum_mul_log_add_sum_negMulLog_le {W : Type*} [Fintype W] {p a : W → ℝ} {Z : ℝ}
    (hp : ∀ w, 0 ≤ p w) (hsum : ∑ w, p w = 1) (ha : ∀ w, 0 < a w) (hZ : 0 < Z) :
    ∑ w, p w * Real.log (a w) + ∑ w, Real.negMulLog (p w)
      ≤ Real.log Z + ((∑ w, a w) / Z - 1) := by
  have key : ∀ w, p w * Real.log (a w) + Real.negMulLog (p w)
      ≤ p w * Real.log Z + (a w / Z - p w) := by
    intro w
    rcases (hp w).eq_or_lt with h | h
    · rw [← h]
      simpa using (div_pos (ha w) hZ).le
    · have hlog := Real.log_le_sub_one_of_pos (div_pos (ha w) (mul_pos h hZ))
      rw [Real.log_div (ha w).ne' (mul_pos h hZ).ne', Real.log_mul h.ne' hZ.ne'] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog h.le
      have e : p w * (a w / (p w * Z) - 1) = a w / Z - p w := by
        field_simp
      rw [e] at hmul
      rw [Real.negMulLog]
      linarith
  calc ∑ w, p w * Real.log (a w) + ∑ w, Real.negMulLog (p w)
      = ∑ w, (p w * Real.log (a w) + Real.negMulLog (p w)) := Finset.sum_add_distrib.symm
    _ ≤ ∑ w, (p w * Real.log Z + (a w / Z - p w)) := Finset.sum_le_sum fun w _ => key w
    _ = Real.log Z + ((∑ w, a w) / Z - 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div,
          hsum, one_mul]

theorem svf_monomialMatrix_eq_max_exp {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) (c : ZMod 2) {a b : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    svf s (monomialMatrix c a b) =
      max (Real.exp (if s < 1 then s * Real.log |a| else Real.log |a| + (s - 1) * Real.log |b|))
        (Real.exp (if s < 1 then s * Real.log |b| else Real.log |b| + (s - 1) * Real.log |a|)) := by
  have hu : |a| = Real.exp (Real.log |a|) := (Real.exp_log (abs_pos.2 ha)).symm
  have hv : |b| = Real.exp (Real.log |b|) := (Real.exp_log (abs_pos.2 hb)).symm
  generalize Real.log |a| = u at hu ⊢
  generalize Real.log |b| = v at hv ⊢
  rw [← Real.exp_monotone.map_max]
  rcases le_or_gt s 1 with h1 | h1
  · rw [svf_monomialMatrix_of_le_one h1, hu, hv, ← Real.exp_monotone.map_max, ← Real.exp_mul]
    congr 1
    rcases h1.lt_or_eq with h1' | rfl
    · rw [ite_eq_left h1', ite_eq_left h1']
      rcases le_total u v with h | h
      · rw [max_eq_right h, max_eq_right (mul_le_mul_of_nonneg_left h hs0.le), mul_comm]
      · rw [max_eq_left h, max_eq_left (mul_le_mul_of_nonneg_left h hs0.le), mul_comm]
    · simp
  · rw [svf_monomialMatrix_of_le_two h1 hs2.le c b ha, hu, hv, ← Real.exp_monotone.map_max,
      ← Real.exp_monotone.map_min, ← Real.exp_mul, ← Real.exp_add, ite_eq_right (not_lt.2 h1.le),
      ite_eq_right (not_lt.2 h1.le)]
    congr 1
    rcases le_total u v with h | h
    · rw [max_eq_right h, min_eq_left h, max_eq_right (by nlinarith)]
      ring
    · rw [max_eq_left h, min_eq_right h, max_eq_left (by nlinarith)]
      ring

namespace RectangularIFS

section Gibbs

variable {ι : Type*} (S : RectangularIFS ι)

theorem sum_potential₁_tau (s : ℝ) (x : ℤ → ι) (n : ℕ) :
    ∑ k ∈ Finset.range n, S.potential₁ s (tau S.o x k) =
      if s < 1 then s * Real.log |S.gDeriv (futureWord (tau S.o x) n)|
      else Real.log |S.gDeriv (futureWord (tau S.o x) n)| +
        (s - 1) * Real.log |S.gDeriv (futureWord (omega S.o x) n)| := by
  rw [log_abs_gDeriv_futureWord, log_abs_gDeriv_futureWord]
  unfold potential₁
  split_ifs
  · rw [Finset.mul_sum]
  · rw [Finset.sum_add_distrib, Finset.mul_sum]
    rfl

theorem potential₂_tau (s : ℝ) (x : ℤ → ι) (k : ℤ) :
    S.potential₂ s (tau S.o x k) = S.potential₁ s (omega S.o x k) := rfl

theorem sum_potential₂_tau (s : ℝ) (x : ℤ → ι) (n : ℕ) :
    ∑ k ∈ Finset.range n, S.potential₂ s (tau S.o x k) =
      if s < 1 then s * Real.log |S.gDeriv (futureWord (omega S.o x) n)|
      else Real.log |S.gDeriv (futureWord (omega S.o x) n)| +
        (s - 1) * Real.log |S.gDeriv (futureWord (tau S.o x) n)| := by
  have hk : ∀ k : ℤ, ((omega S.o x k).1, (omega S.o x k).2 + 1) = tau S.o x k := fun k => by
    rw [omega_apply, tau_apply, add_assoc, show (1 : ZMod 2) + 1 = 0 from by decide, add_zero]
  rw [log_abs_gDeriv_futureWord, log_abs_gDeriv_futureWord]
  simp only [potential₂_tau]
  unfold potential₁
  split_ifs
  · rw [Finset.mul_sum]
  · rw [Finset.sum_add_distrib, Finset.mul_sum]
    simp only [hk]

theorem svf_matWord_futureWord (x : ℤ → ι) (n : ℕ) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    svf s (S.matWord (futureWord x n)) =
      max (Real.exp (∑ k ∈ Finset.range n, S.potential₁ s (tau S.o x k)))
        (Real.exp (∑ k ∈ Finset.range n, S.potential₂ s (tau S.o x k))) := by
  rw [matWord_eq, codeWord_futureWord_tau, codeWord_futureWord_omega,
    svf_monomialMatrix_eq_max_exp hs0 hs2 _ (S.gDeriv_ne_zero _) (S.gDeriv_ne_zero _),
    sum_potential₁_tau, sum_potential₂_tau]

end Gibbs

end RectangularIFS

end FractalGeometry
