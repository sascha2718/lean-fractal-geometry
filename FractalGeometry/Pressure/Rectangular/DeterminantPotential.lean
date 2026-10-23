import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.LinearCocycles.SingularValue
import FractalGeometry.Pressure.Rectangular.Defs
import FractalGeometry.Pressure.Rectangular.Exponents
import FractalGeometry.Pressure.Rectangular.Matrices
import FractalGeometry.Pressure.Rectangular.Pressure
import FractalGeometry.Pressure.SingularValueEnergy
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.Symbolic.Concatenation
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.Shift
import FractalGeometry.Symbolic.WordAverages
import FractalGeometry.Symbolic.WordIntegrals

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology

open scoped Matrix.Norms.L2Operator

theorem svf_of_two_le {s : ℝ} (hs : 2 ≤ s) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    svf s A = |A.det| ^ (s / 2) := by
  rcases hs.eq_or_lt with rfl | h
  · rw [svf, ite_eq_right (by norm_num), ite_eq_left le_rfl]
    norm_num
  · rw [svf, ite_eq_right (by linarith), ite_eq_right (not_le.2 h)]

theorem svf_mul_of_two_le {s : ℝ} (hs : 2 ≤ s) (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    svf s (A * B) = svf s A * svf s B := by
  rw [svf_of_two_le hs, svf_of_two_le hs, svf_of_two_le hs, Matrix.det_mul, abs_mul,
    Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]

theorem energy_of_two_le {l1 l2 s : ℝ} (hs : 2 ≤ s) : energy l1 l2 s = s / 2 * (l1 + l2) := by
  unfold energy
  rcases hs.eq_or_lt with rfl | h
  · rw [ite_eq_right (by norm_num), ite_eq_left le_rfl]
    ring
  · rw [ite_eq_right (by linarith), ite_eq_right (not_le.2 h)]

section OneSymbol

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem integral_comp_apply_zero (μ : Measure (ℤ → α)) [IsFiniteMeasure μ] (f : α → ℝ) :
    ∫ x, f (x 0) ∂μ = ∑ a, μ.real (cylinder ![a]) * f a := by
  have h := integral_comp_block_eq_sum μ (n := 1) fun w => f (w 0)
  have hc : ∀ a : α, (Equiv.funUnique (Fin 1) α).symm a = ![a] := fun a => by
    funext k
    simp
  calc ∫ x, f (x 0) ∂μ = ∑ w : Fin 1 → α, μ.real (cylinder w) * f (w 0) := by
        rw [← h]
        simp
    _ = ∑ a, μ.real (cylinder ![a]) * f a :=
        (Fintype.sum_equiv (Equiv.funUnique (Fin 1) α).symm _ _ fun a => by
          rw [hc]
          simp).symm

end OneSymbol

namespace RectangularIFS

section Pressure

variable {ι : Type*} [Fintype ι] (S : RectangularIFS ι) {s : ℝ}

theorem svfSum_add_of_two_le (hs : 2 ≤ s) (m n : ℕ) :
    S.svfSum s (m + n) = S.svfSum s m * S.svfSum s n := by
  rw [svfSum, sum_ofFn_add m n fun w => svf s (S.matWord w), svfSum, svfSum,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => ?_
  rw [matWord_append, svf_mul_of_two_le hs]

theorem svfSum_one_of_two_le (hs : 2 ≤ s) :
    S.svfSum s 1 = ∑ i, |(S.mat i).det| ^ (s / 2) := by
  rw [svfSum]
  refine (Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι).symm _ _ fun i => ?_).symm
  rw [svf_of_two_le hs]
  simp

theorem svfSum_of_two_le (hs : 2 ≤ s) (n : ℕ) :
    S.svfSum s n = (∑ i, |(S.mat i).det| ^ (s / 2)) ^ n := by
  induction n with
  | zero => simp [svfSum, svf_of_two_le hs]
  | succ n ih => rw [svfSum_add_of_two_le S hs, ih, svfSum_one_of_two_le S hs, pow_succ]

theorem pressure_of_two_le (hs : 2 ≤ s) :
    S.pressure s = Real.log (∑ i, |(S.mat i).det| ^ (s / 2)) := by
  have h : (fun n : ℕ => Real.log (S.svfSum s n) / n) '' Set.Ici 1 =
      {Real.log (∑ i, |(S.mat i).det| ^ (s / 2))} := by
    ext t
    simp only [Set.mem_image, Set.mem_Ici, Set.mem_singleton_iff]
    constructor
    · rintro ⟨n, hn, rfl⟩
      rw [S.svfSum_of_two_le hs, Real.log_pow,
        mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 hn))]
    · rintro rfl
      exact ⟨1, le_rfl, by rw [S.svfSum_of_two_le hs]; simp⟩
  rw [pressure, h, csInf_singleton]

end Pressure

theorem log_abs_det_matWord_futureWord {ι : Type*} (S : RectangularIFS ι) (x : ℤ → ι) (n : ℕ) :
    Real.log |(S.matWord (futureWord x n)).det| =
      ∑ k ∈ Finset.range n, Real.log |(S.mat (x k)).det| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [futureWord_succ, log_abs_det_matWord_append, ih, Finset.sum_range_succ]
    simp

section Lyapunov

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : RectangularIFS ι) {s : ℝ} {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]

theorem integral_log_abs_det_mat_apply (hinv : MeasurePreserving (shift 1) μ μ) (k : ℕ) :
    ∫ x, Real.log |(S.mat (x k)).det| ∂μ =
      ∑ i, μ.real (cylinder ![i]) * Real.log |(S.mat i).det| := by
  have h := integral_comp_shift hinv k (F := fun x => Real.log |(S.mat (x 0)).det|)
    ((Measurable.of_discrete (f := fun i : ι => Real.log |(S.mat i).det|)).comp
      (measurable_pi_apply 0))
  simp only [shift_apply, add_zero] at h
  rw [h, integral_comp_apply_zero μ fun i => Real.log |(S.mat i).det|]

theorem integral_log_abs_det_matWord_futureWord (hinv : MeasurePreserving (shift 1) μ μ)
    (n : ℕ) :
    ∫ x, Real.log |(S.matWord (futureWord x n)).det| ∂μ =
      n * ∑ i, μ.real (cylinder ![i]) * Real.log |(S.mat i).det| := by
  have hint : ∀ k : ℕ, Integrable (fun x : ℤ → ι => Real.log |(S.mat (x k)).det|) μ :=
    fun k =>
      (Integrable.of_finite (f := fun i : ι => Real.log |(S.mat i).det|)).comp_measurable
        (measurable_pi_apply (k : ℤ))
  simp only [log_abs_det_matWord_futureWord]
  rw [integral_finsetSum _ fun k _ => hint k,
    Finset.sum_congr rfl fun k _ => S.integral_log_abs_det_mat_apply hinv k]
  simp

theorem lyapunov₁_add_lyapunov₂ (hinv : MeasurePreserving (shift 1) μ μ) :
    S.lyapunov₁ μ + S.lyapunov₂ μ = ∑ i, μ.real (cylinder ![i]) * Real.log |(S.mat i).det| := by
  refine tendsto_nhds_unique ((S.tendsto_lyapunov₁ hinv).add (S.tendsto_lyapunov₂ hinv)) ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have h₁ : Integrable (fun x => Real.log ‖S.matWord (futureWord x n)‖) μ :=
    integrable_comp_futureWord (fun w => Real.log ‖S.matWord w‖) n
  have h₂ : Integrable (fun x =>
      Real.log (|(S.matWord (futureWord x n)).det| / ‖S.matWord (futureWord x n)‖)) μ :=
    integrable_comp_futureWord (fun w => Real.log (|(S.matWord w).det| / ‖S.matWord w‖)) n
  rw [← add_div, ← integral_add h₁ h₂]
  simp only [log_abs_det_div_norm_matWord, add_sub_cancel]
  rw [S.integral_log_abs_det_matWord_futureWord hinv,
    mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 hn)]

variable {S} in

theorem IsEquilibriumState.log_sum_eq (heq : S.IsEquilibriumState s μ)
    (hinv : MeasurePreserving (shift 1) μ μ) (hs : 2 ≤ s) :
    Real.log (∑ i, |(S.mat i).det| ^ (s / 2)) =
      entropy μ + s / 2 * ∑ i, μ.real (cylinder ![i]) * Real.log |(S.mat i).det| := by
  rw [← S.pressure_of_two_le hs, heq.pressure_eq hinv (by linarith), energy_of_two_le hs,
    S.lyapunov₁_add_lyapunov₂ hinv]

end Lyapunov

end RectangularIFS

end FractalGeometry
