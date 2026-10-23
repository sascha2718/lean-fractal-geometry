import Mathlib
import FractalGeometry.Pressure.GibbsUniqueness
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.GibbsEntropy
import FractalGeometry.Symbolic.Shift

namespace FractalGeometry

open MeasureTheory Set

open scoped ENNReal symmDiff

section RelativeEntropy

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ ν : Measure (ℤ → α)}

noncomputable def blockRelEntropy (μ ν : Measure (ℤ → α)) (n : ℕ) : ℝ :=
  ∑ w : Fin n → α, μ.real (cylinder w) * Real.log (μ.real (cylinder w) / ν.real (cylinder w))

omit [MeasurableSingletonClass α] in

theorem blockRelEntropy_eq (n : ℕ) (hν : ∀ w : Fin n → α, ν.real (cylinder w) ≠ 0) :
    blockRelEntropy μ ν n =
      -blockEntropy μ n -
        ∑ w : Fin n → α, μ.real (cylinder w) * Real.log (ν.real (cylinder w)) := by
  rw [blockRelEntropy, blockEntropy, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rcases eq_or_ne (μ.real (cylinder w)) 0 with h | h
  · simp [h]
  · rw [Real.log_div h (hν w), Real.negMulLog]
    ring

omit [Fintype α] in

theorem measureReal_window_preimage [Finite α] [IsFiniteMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) (m : ℕ) (F : Finset (Fin (2 * m + 1) → α)) :
    μ.real (window m ⁻¹' (F : Set (Fin (2 * m + 1) → α))) = ∑ w ∈ F, μ.real (cylinder w) := by
  rw [measureReal_def, measure_window_preimage hμ m F,
    ENNReal.toReal_sum fun w _ => measure_ne_top _ _]
  rfl

theorem mul_measureReal_window_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MeasurePreserving (shift 1) μ μ) (hν : MeasurePreserving (shift 1) ν ν) (m : ℕ)
    (hpos : ∀ w : Fin (2 * m + 1) → α, 0 < ν.real (cylinder w))
    (F : Finset (Fin (2 * m + 1) → α)) (t : ℝ) :
    t * μ.real (window m ⁻¹' (F : Set (Fin (2 * m + 1) → α))) ≤
      blockRelEntropy μ ν (2 * m + 1) +
        Real.exp t * ν.real (window m ⁻¹' (F : Set (Fin (2 * m + 1) → α))) := by
  classical
  set p : (Fin (2 * m + 1) → α) → ℝ := fun w => μ.real (cylinder w)
  set f : (Fin (2 * m + 1) → α) → ℝ := fun w => if w ∈ F then t else 0
  set q : (Fin (2 * m + 1) → α) → ℝ := fun w => ν.real (cylinder w) * Real.exp (f w)
  have hq : ∀ w, 0 < q w := fun w => mul_pos (hpos w) (Real.exp_pos _)
  have hG := sum_negMulLog_add_sum_mul_log_le (p := p) (q := q) (fun _ => measureReal_nonneg)
    (sum_measureReal_cylinder μ _) hq
  have : Nonempty α := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
  have hpf : ∑ w, p w * f w = t * μ.real (window m ⁻¹' (F : Set (Fin (2 * m + 1) → α))) := by
    rw [measureReal_window_preimage hμ, Finset.mul_sum]
    simp only [f, mul_ite, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    exact Finset.sum_congr rfl fun w _ => mul_comm _ _
  have hlogq : ∑ w, p w * Real.log (q w) =
      ∑ w, p w * Real.log (ν.real (cylinder w)) +
        t * μ.real (window m ⁻¹' (F : Set (Fin (2 * m + 1) → α))) := by
    rw [← hpf, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [q]
    rw [Real.log_mul (hpos w).ne' (Real.exp_pos _).ne', Real.log_exp, mul_add]
  have hνf : ∑ w, ν.real (cylinder w) * (Real.exp (f w) - 1) =
      (Real.exp t - 1) * ν.real (window m ⁻¹' (F : Set (Fin (2 * m + 1) → α))) := by
    rw [measureReal_window_preimage hν, Finset.mul_sum]
    have e : ∀ w, ν.real (cylinder w) * (Real.exp (f w) - 1) =
        if w ∈ F then (Real.exp t - 1) * ν.real (cylinder w) else 0 := by
      intro w
      by_cases hw : w ∈ F
      · simp [f, hw, mul_comm]
      · simp [f, hw]
    simp only [e]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hsumq : ∑ w, q w = 1 + (Real.exp t - 1) * ν.real (window m ⁻¹' (F : Set _)) := by
    calc ∑ w, q w = ∑ w, (ν.real (cylinder w) + ν.real (cylinder w) * (Real.exp (f w) - 1)) :=
          Finset.sum_congr rfl fun w _ => by simp only [q]; ring
      _ = _ := by rw [Finset.sum_add_distrib, sum_measureReal_cylinder ν, hνf]
  have hlog := Real.log_le_sub_one_of_pos (Finset.sum_pos (fun w _ => hq w)
    Finset.univ_nonempty)
  have hνE : 0 ≤ ν.real (window m ⁻¹' (F : Set (Fin (2 * m + 1) → α))) := measureReal_nonneg
  rw [blockRelEntropy_eq _ fun w => (hpos w).ne']
  rw [hlogq, hsumq] at hG
  rw [hsumq] at hlog
  change ∑ w, Real.negMulLog (p w) + _ ≤ _ at hG
  rw [blockEntropy]
  nlinarith [Real.exp_pos t]

theorem absolutelyContinuous_of_blockRelEntropy_le [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : MeasurePreserving (shift 1) μ μ)
    (hν : MeasurePreserving (shift 1) ν ν)
    (hpos : ∀ n : ℕ, 0 < n → ∀ w : Fin n → α, 0 < ν.real (cylinder w)) {B : ℝ}
    (hB : ∀ n : ℕ, 0 < n → blockRelEntropy μ ν n ≤ B) : μ ≪ ν := by
  classical
  intro A hA0
  obtain ⟨A', hAA', hA'm, hA'0⟩ := exists_measurable_superset_of_null hA0
  refine measure_mono_null hAA' ?_
  by_contra hne
  set a := μ.real A'
  have ha : 0 < a := ENNReal.toReal_pos hne (measure_ne_top _ _)
  set t := 4 * (|B| + 1) / a with ht_def
  have ht : 0 < t := by positivity
  have hta : t * a = 4 * (|B| + 1) := by rw [ht_def]; field_simp
  set ε := min (a / 2) (Real.exp (-t))
  have hε : 0 < ε := lt_min (by positivity) (Real.exp_pos _)
  have hεa : ε ≤ a / 2 := min_le_left _ _
  have hεt : Real.exp t * ε ≤ 1 := by
    calc Real.exp t * ε ≤ Real.exp t * Real.exp (-t) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (Real.exp_pos t).le
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hdense := Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite (μ + ν)
    isSetAlgebra_windowSets generateFrom_windowSets.symm
  obtain ⟨E, hE, hAE⟩ := hdense.approx A' hA'm (measure_ne_top _ _) ε hε
  have hEm : MeasurableSet E := hdense.measurable E hE
  rw [Measure.add_apply] at hAE
  have hμd : μ.real (A' ∆ E) < ε :=
    ENNReal.toReal_lt_of_lt_ofReal (lt_of_le_of_lt le_self_add hAE)
  have hνd : ν.real (A' ∆ E) < ε :=
    ENNReal.toReal_lt_of_lt_ofReal (lt_of_le_of_lt le_add_self hAE)
  have hμE : a - ε ≤ μ.real E := by
    have h := abs_measureReal_sub_le_measureReal_symmDiff (μ := μ) hA'm.nullMeasurableSet
      hEm.nullMeasurableSet
    have h' := (le_abs_self _).trans h
    linarith
  have hνE : ν.real E ≤ ε := by
    have h := abs_measureReal_sub_le_measureReal_symmDiff (μ := ν) hEm.nullMeasurableSet
      hA'm.nullMeasurableSet
    have h' := (le_abs_self _).trans h
    rw [symmDiff_comm] at h'
    have hA'0' : ν.real A' = 0 := by rw [measureReal_def, hA'0, ENNReal.toReal_zero]
    linarith
  obtain ⟨m, F, rfl⟩ := hE
  have hF : (F : Set (Fin (2 * m + 1) → α)) = ((F.toFinset : Finset _) : Set _) := by simp
  have key := mul_measureReal_window_le hμ hν m (hpos _ (by omega)) F.toFinset t
  rw [← hF] at key
  have hD := hB (2 * m + 1) (by omega)
  have h1 : t * (a - ε) ≤ t * μ.real (window m ⁻¹' F) := mul_le_mul_of_nonneg_left hμE ht.le
  have h2 : Real.exp t * ν.real (window m ⁻¹' F) ≤ Real.exp t * ε :=
    mul_le_mul_of_nonneg_left hνE (Real.exp_pos t).le
  have h3 : t * (a / 2) ≤ t * (a - ε) := mul_le_mul_of_nonneg_left (by linarith) ht.le
  have h4 : t * (a / 2) = 2 * (|B| + 1) := by linarith
  have h5 := le_abs_self B
  have h6 := abs_nonneg B
  linarith

end RelativeEntropy

end FractalGeometry
