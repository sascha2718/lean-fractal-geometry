import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.LinearCocycles.LowerBounds
import FractalGeometry.LinearCocycles.Pressure
import FractalGeometry.LinearCocycles.PressureBounds
import FractalGeometry.LinearCocycles.Products
import FractalGeometry.LinearCocycles.SingularValue
import FractalGeometry.Pressure.Rectangular.PotentialSums
import FractalGeometry.Pressure.SingularValueStatement
import FractalGeometry.Symbolic.Concatenation
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.Shift
import FractalGeometry.Symbolic.WordAverages
import FractalGeometry.Symbolic.WordIntegrals

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology ProbabilityTheory

open scoped Matrix.Norms.L2Operator ENNReal

namespace MatrixTuple

variable {ι : Type*} (A : ι → Matrix (Fin 2) (Fin 2) ℝ)

variable {A}

theorem abs_det_word_pos (hA : ∀ i, (A i).det ≠ 0) (w : List ι) : 0 < |(word A w).det| :=
  abs_pos.2 (word_det_ne_zero hA w)

theorem svf_word_pos (hA : ∀ i, (A i).det ≠ 0) (s : ℝ) (w : List ι) :
    0 < svf s (word A w) := by
  have hn := norm_word_pos hA w
  have hd := abs_det_word_pos hA w
  unfold svf
  split_ifs
  · exact Real.rpow_pos_of_pos hn _
  · exact mul_pos (Real.rpow_pos_of_pos hn _) (Real.rpow_pos_of_pos hd _)
  · exact Real.rpow_pos_of_pos hd _

theorem log_svf_word_append_le (hA : ∀ i, (A i).det ≠ 0) {s : ℝ} (hs : 0 ≤ s)
    (w w' : List ι) :
    Real.log (svf s (word A (w ++ w'))) ≤
      Real.log (svf s (word A w)) + Real.log (svf s (word A w')) := by
  have h := svf_word_pos hA s (w ++ w')
  rw [word_append] at h
  rw [← Real.log_mul (svf_word_pos hA s w).ne' (svf_word_pos hA s w').ne', word_append]
  exact Real.log_le_log h (svf_mul_le hs _ _)

variable [Fintype ι]

variable (A) in

noncomputable def detLowerBound : ℝ := (1 + ∑ i, |(A i).det|⁻¹)⁻¹

theorem detLowerBound_pos : 0 < detLowerBound A :=
  inv_pos.2 (one_add_sum_pos fun _ => inv_nonneg.2 (abs_nonneg _))

theorem detLowerBound_le (hA : ∀ i, (A i).det ≠ 0) (i : ι) : detLowerBound A ≤ |(A i).det| := by
  have hpos := abs_pos.2 (hA i)
  rw [detLowerBound, inv_le_comm₀ (one_add_sum_pos fun _ => inv_nonneg.2 (abs_nonneg _)) hpos]
  exact le_one_add_sum (fun j => inv_nonneg.2 (abs_nonneg ((A j).det))) i

theorem pow_le_abs_det_word (hA : ∀ i, (A i).det ≠ 0) (w : List ι) :
    detLowerBound A ^ w.length ≤ |(word A w).det| := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [word_cons, Matrix.det_mul, abs_mul, List.length_cons, pow_succ']
    exact mul_le_mul (detLowerBound_le hA i) ih (pow_nonneg detLowerBound_pos.le _)
      (abs_nonneg _)

theorem le_log_abs_det_word (hA : ∀ i, (A i).det ≠ 0) (w : List ι) :
    Real.log (detLowerBound A) * w.length ≤ Real.log |(word A w).det| := by
  have h := Real.log_le_log (pow_pos detLowerBound_pos _) (pow_le_abs_det_word hA w)
  rwa [Real.log_pow, mul_comm] at h

theorem exists_le_log_svf_word (hA : ∀ i, (A i).det ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    ∃ c : ℝ, ∀ w : List ι, c * w.length ≤ Real.log (svf s (word A w)) := by
  have hn := fun w => norm_word_pos hA w
  have hd := fun w => abs_det_word_pos hA w
  have h1 := le_log_norm_word hA
  have h2 := le_log_abs_det_word hA
  by_cases hs1 : s ≤ 1
  · refine ⟨s * Real.log (normLowerBound A), fun w => ?_⟩
    rw [svf, ite_eq_left hs1, Real.log_rpow (hn w), mul_assoc]
    exact mul_le_mul_of_nonneg_left (h1 w) hs
  by_cases hs2 : s ≤ 2
  · refine ⟨(2 - s) * Real.log (normLowerBound A) + (s - 1) * Real.log (detLowerBound A),
      fun w => ?_⟩
    rw [svf, ite_eq_right hs1, ite_eq_left hs2,
      Real.log_mul (Real.rpow_pos_of_pos (hn w) _).ne' (Real.rpow_pos_of_pos (hd w) _).ne',
      Real.log_rpow (hn w), Real.log_rpow (hd w), add_mul, mul_assoc, mul_assoc]
    exact add_le_add (mul_le_mul_of_nonneg_left (h1 w) (by linarith))
      (mul_le_mul_of_nonneg_left (h2 w) (by linarith))
  · refine ⟨s / 2 * Real.log (detLowerBound A), fun w => ?_⟩
    rw [svf, ite_eq_right hs1, ite_eq_right hs2, Real.log_rpow (hd w), mul_assoc]
    exact mul_le_mul_of_nonneg_left (h2 w) (by linarith)

variable (A) in

theorem svfSum_add_le {s : ℝ} (hs : 0 ≤ s) (m n : ℕ) :
    svfSum A s (m + n) ≤ svfSum A s m * svfSum A s n := by
  rw [svfSum, sum_ofFn_add m n fun w => svf s (word A w), svfSum, svfSum, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun h _ => ?_
  rw [word_append]
  exact svf_mul_le hs _ _

theorem svfSum_pos [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) (s : ℝ) (n : ℕ) :
    0 < svfSum A s n :=
  Finset.sum_pos (fun _ _ => svf_word_pos hA s _) Finset.univ_nonempty

theorem subadditive_log_svfSum [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    Subadditive fun n => Real.log (svfSum A s n) := by
  intro m n
  rw [← Real.log_mul (svfSum_pos hA s m).ne' (svfSum_pos hA s n).ne']
  exact Real.log_le_log (svfSum_pos hA s _) (svfSum_add_le A hs m n)

theorem bddBelow_log_svfSum_div [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    BddBelow (Set.range fun n : ℕ => Real.log (svfSum A s n) / n) := by
  obtain ⟨c, hc⟩ := exists_le_log_svf_word hA hs
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine ⟨min 0 c, ?_⟩
  rintro _ ⟨n, rfl⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    refine (min_le_right _ _).trans ?_
    rw [le_div_iff₀ hn']
    have hw := hc (List.ofFn fun _ : Fin n => i)
    rw [List.length_ofFn] at hw
    have hle : svf s (word A (List.ofFn fun _ : Fin n => i)) ≤ svfSum A s n :=
      Finset.single_le_sum (f := fun w : Fin n → ι => svf s (word A (List.ofFn w)))
        (fun w _ => (svf_word_pos hA s _).le) (Finset.mem_univ _)
    exact hw.trans (Real.log_le_log (svf_word_pos hA s _) hle)

theorem tendsto_pressure [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun n : ℕ => Real.log (svfSum A s n) / n) atTop (𝓝 (pressure A s)) := by
  have h := (subadditive_log_svfSum hA hs).tendsto_lim (bddBelow_log_svfSum_div hA hs)
  rwa [Subadditive.lim] at h

variable [MeasurableSpace ι] [MeasurableSingletonClass ι] {μ : Measure (ℤ → ι)}
  [IsProbabilityMeasure μ]

theorem tendsto_energyLim (hA : ∀ i, (A i).det ≠ 0) (hμ : MeasurePreserving (shift 1) μ μ)
    {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun n : ℕ => (∫ x, Real.log (svf s (word A (futureWord x n))) ∂μ) / n) atTop
      (𝓝 (energyLim A s μ)) := by
  obtain ⟨c, hc⟩ := exists_le_log_svf_word hA hs
  obtain ⟨L, hL⟩ := exists_tendsto_integral_futureWord_div hμ
    (G := fun w => Real.log (svf s (word A w))) (log_svf_word_append_le hA hs) hc
  rw [energyLim, hL.limUnder_eq]
  exact hL

theorem integral_log_svf_add_blockEntropy_le (hA : ∀ i, (A i).det ≠ 0) (n : ℕ) (s : ℝ) :
    (∫ x, Real.log (svf s (word A (futureWord x n))) ∂μ) + blockEntropy μ n
      ≤ Real.log (svfSum A s n) := by
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
  have hZ : 0 < svfSum A s n := svfSum_pos hA s n
  have h := sum_mul_log_add_sum_negMulLog_le (p := fun w : Fin n → ι => μ.real (cylinder w))
    (a := fun w => svf s (word A (List.ofFn w))) (fun _ => measureReal_nonneg)
    (sum_measureReal_cylinder μ n) (fun _ => svf_word_pos hA s _) hZ
  rw [← svfSum, div_self hZ.ne', sub_self, add_zero] at h
  rw [integral_comp_futureWord_eq_sum μ fun w => Real.log (svf s (word A w))]
  exact h

theorem entropy_add_energyLim_le_pressure (hA : ∀ i, (A i).det ≠ 0)
    (hμ : MeasurePreserving (shift 1) μ μ) {s : ℝ} (hs : 0 ≤ s) :
    entropy μ + energyLim A s μ ≤ pressure A s := by
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
  refine le_of_tendsto_of_tendsto' ((tendsto_entropy hμ).add (tendsto_energyLim hA hμ hs))
    (tendsto_pressure hA hs) fun n => ?_
  rw [← add_div, add_comm]
  exact div_le_div_of_nonneg_right (integral_log_svf_add_blockEntropy_le hA n s)
    (Nat.cast_nonneg n)

end MatrixTuple

end FractalGeometry
