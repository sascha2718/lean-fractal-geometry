import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.LinearCocycles.Monomial
import FractalGeometry.Pressure.Rectangular.CoordinateAverages
import FractalGeometry.Pressure.Rectangular.DecompositionStatement
import FractalGeometry.Pressure.Rectangular.Exponents
import FractalGeometry.Pressure.Rectangular.LowerExponentBound
import FractalGeometry.Pressure.Rectangular.Matrices
import FractalGeometry.SelfAffine.Rectangular.Coding
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.SelfAffine.Rectangular.Orientation
import FractalGeometry.SelfAffine.Rectangular.SingularValues
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.OrientationCoding
import FractalGeometry.Symbolic.ParityPastWords
import FractalGeometry.Symbolic.Past
import FractalGeometry.Symbolic.PastWords
import FractalGeometry.Symbolic.Shift
import FractalGeometry.Symbolic.ShiftMeasure
import FractalGeometry.Symbolic.WordAverages

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology Set

open scoped Matrix.Norms.L2Operator

universe u

namespace RectangularIFS

section BackRate

variable {ι : Type u} (S : RectangularIFS ι)

theorem log_abs_gDeriv_pastWord (y : ℤ → ι × ZMod 2) (n : ℕ) :
    Real.log |S.gDeriv (pastWord y n)| =
      birkhoffSum (shift (-1)) (fun z : ℤ → ι × ZMod 2 => Real.log |S.ratio (z (-1))|) n y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [birkhoffSum_succ_apply, ← ih, pastWord_succ, gDeriv_cons, abs_mul,
      Real.log_mul (abs_ne_zero.2 (S.ratio_ne_zero _)) (abs_ne_zero.2 (S.gDeriv_ne_zero _)),
      iterate_shift_neg_one, shift_apply, add_comm]
    congr 5
    ring

theorem hasBackRate_iff_birkhoffAverage (y : ℤ → ι × ZMod 2) (l : ℝ) :
    S.HasBackRate y l ↔ Tendsto (fun n : ℕ => birkhoffAverage ℝ (shift (-1))
      (fun z : ℤ → ι × ZMod 2 => Real.log |S.ratio (z (-1))|) n y) atTop (𝓝 l) := by
  unfold HasBackRate
  refine tendsto_congr fun n => ?_
  rw [birkhoffAverage, ← log_abs_gDeriv_pastWord, smul_eq_mul, div_eq_inv_mul]

end BackRate

section Gsystem

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : RectangularIFS ι)

theorem integrable_log_abs_ratio_neg_one (ν : Measure (ℤ → ι × ZMod 2)) [IsFiniteMeasure ν] :
    Integrable (fun z : ℤ → ι × ZMod 2 => Real.log |S.ratio (z (-1))|) ν :=
  (Integrable.of_finite (f := fun p : ι × ZMod 2 => Real.log |S.ratio p|)).comp_measurable
    (measurable_pi_apply (-1))

theorem lyapunov_exponent_gsystem (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν]
    (herg : Ergodic (shift 1) ν) : ∀ᵐ y ∂ν, S.HasBackRate y (S.lyapBar ν) := by
  have hval : ∫ z, Real.log |S.ratio (z (-1))| ∂ν = S.lyapBar ν := by
    have h := integral_comp_shift_neg herg.toMeasurePreserving 1
      (F := fun y : ℤ → ι × ZMod 2 => Real.log |S.ratio (y 0)|)
      ((Measurable.of_discrete (f := fun p : ι × ZMod 2 => Real.log |S.ratio p|)).comp
        (measurable_pi_apply 0))
    simpa [lyapBar] using h
  filter_upwards [birkhoff_ergodic (ergodic_shift_neg_one herg)
    (S.integrable_log_abs_ratio_neg_one ν)] with y hy
  rw [hasBackRate_iff_birkhoffAverage, ← hval]
  exact hy

end Gsystem

end RectangularIFS

section Dominated

variable {α : Type*} [MeasurableSpace α] [Finite α] [MeasurableSingletonClass α]

theorem tendsto_integral_futureWord_div_of_ae_pastWord {μ : Measure (ℤ → α)}
    [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ) {G : List α → ℝ} {C c : ℝ}
    (hG : ∀ w, |G w| ≤ C * w.length)
    (h : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => G (pastWord x n) / n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (∫ x, G (futureWord x n) ∂μ) / n) atTop (𝓝 c) := by
  have hmeas : ∀ n : ℕ, Measurable fun x : ℤ → α => G (pastWord x n) := fun n => by
    simp only [pastWord_eq_futureWord]
    exact (measurable_comp_futureWord G n).comp (measurable_shift _)
  have key : ∀ n : ℕ, (∫ x, G (futureWord x n) ∂μ) / n = ∫ x, G (pastWord x n) / n ∂μ :=
    fun n => by
      rw [integral_div, ← integral_comp_shift_neg hμ n (measurable_comp_futureWord G n)]
      simp only [pastWord_eq_futureWord]
  have hlim := tendsto_integral_of_dominated_convergence (fun _ => |C|)
    (F := fun (n : ℕ) (x : ℤ → α) => G (pastWord x n) / n) (f := fun _ => c)
    (fun n => ((hmeas n).div_const _).aestronglyMeasurable) (integrable_const _)
    (fun n => Eventually.of_forall fun x => ?_) h
  · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hlim
    exact hlim.congr fun n => (key n).symm
  · rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [div_le_iff₀ (Nat.cast_pos.2 hn)]
      calc |G (pastWord x n)| ≤ C * n := by simpa using hG (pastWord x n)
        _ ≤ |C| * n := mul_le_mul_of_nonneg_right (le_abs_self C) (Nat.cast_nonneg n)

end Dominated

theorem log_max_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (max a b) = max (Real.log a) (Real.log b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (Real.log_le_log ha h)]
  · rw [max_eq_left h, max_eq_left (Real.log_le_log hb h)]

theorem log_min_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (min a b) = min (Real.log a) (Real.log b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (Real.log_le_log ha h)]
  · rw [min_eq_right h, min_eq_right (Real.log_le_log hb h)]

namespace RectangularIFS

section PastWord

variable {ι : Type u} (S : RectangularIFS ι)

theorem norm_matWord_pastWord (x : ℤ → ι) (n : ℕ) :
    ‖S.matWord (pastWord x n)‖ =
      max |S.gDeriv (pastWord (tau S.o x) n)| |S.gDeriv (pastWord (omega S.o x) n)| := by
  rw [norm_matWord, ← S.codeWord_pastWord_tau, ← S.codeWord_pastWord_omega]
  rcases zmod_two_cases (eps S.o x (-(n : ℤ))) with h | h
  · rw [h, zero_add]
  · rw [h, show (1 : ZMod 2) + 1 = 0 by decide, max_comm]

theorem abs_det_div_norm_matWord_pastWord (x : ℤ → ι) (n : ℕ) :
    |(S.matWord (pastWord x n)).det| / ‖S.matWord (pastWord x n)‖ =
      min |S.gDeriv (pastWord (tau S.o x) n)| |S.gDeriv (pastWord (omega S.o x) n)| := by
  rw [abs_det_div_norm_matWord, ← S.codeWord_pastWord_tau, ← S.codeWord_pastWord_omega]
  rcases zmod_two_cases (eps S.o x (-(n : ℤ))) with h | h
  · rw [h, zero_add]
  · rw [h, show (1 : ZMod 2) + 1 = 0 by decide, min_comm]

theorem tendsto_log_norm_matWord_pastWord {x : ℤ → ι} {a b : ℝ}
    (ha : S.HasBackRate (tau S.o x) a) (hb : S.HasBackRate (omega S.o x) b) :
    Tendsto (fun n : ℕ => Real.log ‖S.matWord (pastWord x n)‖ / n) atTop (𝓝 (max a b)) := by
  refine (Filter.Tendsto.max ha hb).congr fun n => ?_
  rw [norm_matWord_pastWord, log_max_of_pos (abs_pos.2 (S.gDeriv_ne_zero _))
    (abs_pos.2 (S.gDeriv_ne_zero _)), max_div_div_right (Nat.cast_nonneg n)]

theorem tendsto_log_abs_det_div_norm_matWord_pastWord {x : ℤ → ι} {a b : ℝ}
    (ha : S.HasBackRate (tau S.o x) a) (hb : S.HasBackRate (omega S.o x) b) :
    Tendsto (fun n : ℕ => Real.log (|(S.matWord (pastWord x n)).det| /
      ‖S.matWord (pastWord x n)‖) / n) atTop (𝓝 (min a b)) := by
  refine (Filter.Tendsto.min ha hb).congr fun n => ?_
  rw [abs_det_div_norm_matWord_pastWord, log_min_of_pos (abs_pos.2 (S.gDeriv_ne_zero _))
    (abs_pos.2 (S.gDeriv_ne_zero _)), min_div_div_right (Nat.cast_nonneg n)]

theorem exists_abs_log_singularValue_le [Finite ι] [Nonempty ι] :
    ∃ C : ℝ, (∀ w : List ι, |Real.log ‖S.matWord w‖| ≤ C * w.length) ∧
      ∀ w : List ι, |Real.log (|(S.matWord w).det| / ‖S.matWord w‖)| ≤ C * w.length := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  obtain ⟨δ, hδ⟩ := S.exists_ratioLowerBound
  have hlow : ∀ w : List ι, -((|Real.log δ| + |Real.log r|) * w.length) ≤
      Real.log δ * w.length := fun w => by
    have h := mul_le_mul_of_nonneg_right (neg_abs_le (Real.log δ)) (Nat.cast_nonneg w.length)
    have h' := mul_nonneg (abs_nonneg (Real.log r)) (Nat.cast_nonneg (α := ℝ) w.length)
    linarith
  have hupp : ∀ w : List ι, Real.log r * w.length ≤
      (|Real.log δ| + |Real.log r|) * w.length := fun w => by
    have h := mul_le_mul_of_nonneg_right (le_abs_self (Real.log r)) (Nat.cast_nonneg w.length)
    have h' := mul_nonneg (abs_nonneg (Real.log δ)) (Nat.cast_nonneg (α := ℝ) w.length)
    linarith
  refine ⟨|Real.log δ| + |Real.log r|, fun w => abs_le.2 ⟨?_, ?_⟩, fun w => abs_le.2 ⟨?_, ?_⟩⟩
  · exact (hlow w).trans (hδ.le_log_norm_matWord w)
  · exact (hS.log_norm_matWord_le w).trans (hupp w)
  · exact (hlow w).trans (hδ.le_log_abs_det_div_norm_matWord w)
  · exact ((S.log_abs_det_div_norm_matWord_le w).trans (hS.log_norm_matWord_le w)).trans (hupp w)

end PastWord

end RectangularIFS

end FractalGeometry
