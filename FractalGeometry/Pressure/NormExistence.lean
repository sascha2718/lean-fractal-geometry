import FractalGeometry.Pressure.NormUniqueness

/-!
The Gibbs bounds imply the variational equality for matrix norm pressure.
Together with Gibbs existence this supplies the existence part of Proposition 1.2
of Feng–Käenmäki, Discrete and Continuous Dynamical Systems 30(3) (2011), 699–708,
doi:10.3934/dcds.2011.30.699, for invertible planar matrices.
-/

namespace FractalGeometry.MatrixTuple

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {A : ι → Matrix (Fin 2) (Fin 2) ℝ} {q : ℝ}

theorem HasNormGibbs.isNormEquilibrium (hA : ∀ i, (A i).det ≠ 0)
    {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (hg : HasNormGibbs A q μ) :
    IsNormEquilibrium A q μ := by
  obtain ⟨C, hC, hG⟩ := hg
  let B : ℕ → ℝ := fun n => blockEntropy μ n +
    q * ∫ x, Real.log ‖word A (futureWord x n)‖ ∂μ
  have hb : ∀ n : ℕ, 0 < n →
      n * normPressure A q - Real.log C ≤ B n ∧
      B n ≤ n * normPressure A q + Real.log C := by
    intro n hn
    have hlog : ∀ w : Fin n → ι,
        n * normPressure A q - Real.log C ≤
          -Real.log (μ.real (cylinder w)) + q * Real.log ‖word A (List.ofFn w)‖ ∧
        -Real.log (μ.real (cylinder w)) + q * Real.log ‖word A (List.ofFn w)‖ ≤
          n * normPressure A q + Real.log C := by
      intro w
      have hw := norm_word_pos hA (List.ofFn w)
      have he := Real.exp_pos (-(n * normPressure A q))
      have hr := Real.rpow_pos_of_pos hw q
      have hwgt := mul_pos he hr
      have hp := (mul_pos (inv_pos.mpr hC) hwgt).trans_le (hG n hn w).1
      have hlo := Real.log_le_log (mul_pos (inv_pos.mpr hC) hwgt) (hG n hn w).1
      have hhi := Real.log_le_log hp (hG n hn w).2
      rw [Real.log_mul (inv_ne_zero hC.ne') hwgt.ne', Real.log_inv,
        Real.log_mul he.ne' hr.ne', Real.log_exp, Real.log_rpow hw] at hlo
      rw [Real.log_mul hC.ne' hwgt.ne', Real.log_mul he.ne' hr.ne',
        Real.log_exp, Real.log_rpow hw] at hhi
      constructor <;> linarith
    have heq : (∑ w : Fin n → ι, μ.real (cylinder w) *
        (-Real.log (μ.real (cylinder w)) + q * Real.log ‖word A (List.ofFn w)‖)) = B n := by
      dsimp [B]
      rw [integral_comp_futureWord_eq_sum μ (fun w => Real.log ‖word A w‖), blockEntropy, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro w _
      simp only [Real.negMulLog]
      ring
    have hlo := Finset.sum_le_sum (s := Finset.univ) fun w _ =>
      mul_le_mul_of_nonneg_left (hlog w).1 (measureReal_nonneg : 0 ≤ μ.real (cylinder w))
    have hhi := Finset.sum_le_sum (s := Finset.univ) fun w _ =>
      mul_le_mul_of_nonneg_left (hlog w).2 (measureReal_nonneg : 0 ≤ μ.real (cylinder w))
    rw [heq, ← Finset.sum_mul, sum_measureReal_cylinder μ n, one_mul] at hlo hhi
    exact ⟨hlo, hhi⟩
  have hB : Tendsto (fun n : ℕ => B n / n) atTop
      (𝓝 (entropy μ + q * lyapunov₁ A μ)) := by
    convert (tendsto_entropy hinv).add ((tendsto_lyapunov₁ hA hinv).const_mul q) using 1
    ext n
    dsimp [B]
    ring
  have hzero := tendsto_const_div_atTop_nhds_zero_nat (Real.log C)
  have hlo : ∀ᶠ n : ℕ in atTop, normPressure A q - Real.log C / n ≤ B n / n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h := (div_le_div_iff_of_pos_right hn').2 (hb n hn).1
    simpa only [sub_div, mul_div_cancel_left₀ _ hn'.ne'] using h
  have hhi : ∀ᶠ n : ℕ in atTop, B n / n ≤ normPressure A q + Real.log C / n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h := (div_le_div_iff_of_pos_right hn').2 (hb n hn).2
    simpa only [add_div, mul_div_cancel_left₀ _ hn'.ne'] using h
  have h₁ := le_of_tendsto_of_tendsto (tendsto_const_nhds.sub hzero) hB hlo
  have h₂ := le_of_tendsto_of_tendsto hB (tendsto_const_nhds.add hzero) hhi
  simp only [sub_zero] at h₁
  simp only [add_zero] at h₂
  dsimp [IsNormEquilibrium]
  simpa only [add_comm] using le_antisymm h₁ h₂

end FractalGeometry.MatrixTuple
