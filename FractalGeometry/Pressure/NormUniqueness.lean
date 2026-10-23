import Mathlib
import FractalGeometry.LinearCocycles.LowerBounds
import FractalGeometry.LinearCocycles.Products
import FractalGeometry.Pressure.NormPotential
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.GibbsEntropy
import FractalGeometry.Symbolic.InvariantProbability
import FractalGeometry.Symbolic.RelativeEntropy
import FractalGeometry.Symbolic.Shift
import FractalGeometry.Symbolic.WordAverages
import FractalGeometry.Symbolic.WordIntegrals

namespace FractalGeometry

open MeasureTheory Filter Topology

open scoped Matrix.Norms.L2Operator

namespace MatrixTuple

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {A : ι → Matrix (Fin 2) (Fin 2) ℝ} {q : ℝ}

theorem lyapunov₁_le_div (hA : ∀ i, (A i).det ≠ 0) {μ : Measure (ℤ → ι)}
    [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ) {n : ℕ} (hn : n ≠ 0) :
    lyapunov₁ A μ ≤ (∫ x, Real.log ‖word A (futureWord x n)‖ ∂μ) / n := by
  have hsub := subadditive_integral_futureWord hμ (G := fun w => Real.log ‖word A w‖)
    fun w w' => by
      rw [← Real.log_mul (norm_word_pos hA w).ne' (norm_word_pos hA w').ne', word_append]
      exact Real.log_le_log (by rw [← word_append]; exact norm_word_pos hA _)
        (Matrix.l2_opNorm_mul _ _)
  have hbdd : BddBelow (Set.range fun n : ℕ =>
      (∫ x, Real.log ‖word A (futureWord x n)‖ ∂μ) / n) := by
    refine ⟨min 0 (Real.log (normLowerBound A)), ?_⟩
    rintro _ ⟨m, rfl⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · exact (min_le_right _ _).trans (le_integral_futureWord_div (le_log_norm_word hA) hm)
  rw [tendsto_nhds_unique (tendsto_lyapunov₁ hA hμ) (hsub.tendsto_lim hbdd)]
  exact hsub.lim_le_div hbdd hn

theorem IsNormEquilibrium.le_blockEntropy_add (hA : ∀ i, (A i).det ≠ 0) (hq : 0 ≤ q)
    {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ)
    (heq : IsNormEquilibrium A q μ) {n : ℕ} (hn : 0 < n) :
    n * normPressure A q ≤ blockEntropy μ n +
      q * ∑ w : Fin n → ι, μ.real (cylinder w) * Real.log ‖word A (List.ofFn w)‖ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := entropy_le_blockEntropy_div hμ hn.ne'
  have h2 := lyapunov₁_le_div hA hμ hn.ne'
  rw [integral_comp_futureWord_eq_sum μ fun w => Real.log ‖word A w‖] at h2
  rw [le_div_iff₀ hn'] at h1 h2
  have hP : normPressure A q = q * lyapunov₁ A μ + entropy μ := heq
  rw [hP]
  nlinarith [mul_le_mul_of_nonneg_left h2 hq]

theorem IsNormEquilibrium.blockRelEntropy_le (hA : ∀ i, (A i).det ≠ 0) (hq : 0 ≤ q)
    {μ ν : Measure (ℤ → ι)} [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ)
    (heq : IsNormEquilibrium A q μ) {C : ℝ} (hC : 0 < C)
    (hlow : ∀ n : ℕ, 0 < n → ∀ w : Fin n → ι,
      C⁻¹ * (Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn w)‖ ^ q) ≤
        ν.real (cylinder w))
    {n : ℕ} (hn : 0 < n) : blockRelEntropy μ ν n ≤ Real.log C := by
  have hpos : ∀ w : Fin n → ι, 0 < ν.real (cylinder w) := fun w => by
    have := norm_word_pos hA (List.ofFn w)
    exact lt_of_lt_of_le (by positivity) (hlow n hn w)
  have hblock := heq.le_blockEntropy_add hA hq hμ hn
  have hlog : ∀ w : Fin n → ι, q * Real.log ‖word A (List.ofFn w)‖ ≤
      Real.log C + n * normPressure A q + Real.log (ν.real (cylinder w)) := by
    intro w
    have hw := norm_word_pos hA (List.ofFn w)
    have hl := hlow n hn w
    have hφ : ‖word A (List.ofFn w)‖ ^ q ≤
        C * ν.real (cylinder w) * Real.exp (n * normPressure A q) := by
      rw [inv_mul_le_iff₀ hC] at hl
      calc ‖word A (List.ofFn w)‖ ^ q
          = Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn w)‖ ^ q *
              Real.exp (n * normPressure A q) := by
            rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
              mul_one]
        _ ≤ C * ν.real (cylinder w) * Real.exp (n * normPressure A q) :=
            mul_le_mul_of_nonneg_right hl (Real.exp_pos _).le
    have h := Real.log_le_log (Real.rpow_pos_of_pos hw q) hφ
    rwa [Real.log_rpow hw, Real.log_mul (mul_pos hC (hpos w)).ne' (Real.exp_pos _).ne',
      Real.log_exp, Real.log_mul hC.ne' (hpos w).ne', add_right_comm] at h
  have hsum : q * ∑ w : Fin n → ι, μ.real (cylinder w) * Real.log ‖word A (List.ofFn w)‖
      ≤ Real.log C + n * normPressure A q +
        ∑ w : Fin n → ι, μ.real (cylinder w) * Real.log (ν.real (cylinder w)) := by
    calc q * ∑ w : Fin n → ι, μ.real (cylinder w) * Real.log ‖word A (List.ofFn w)‖
        = ∑ w : Fin n → ι, μ.real (cylinder w) * (q * Real.log ‖word A (List.ofFn w)‖) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun w _ => by ring
      _ ≤ ∑ w : Fin n → ι, μ.real (cylinder w) *
            (Real.log C + n * normPressure A q + Real.log (ν.real (cylinder w))) :=
          Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hlog w) measureReal_nonneg
      _ = (∑ w : Fin n → ι, μ.real (cylinder w)) * (Real.log C + n * normPressure A q) +
            ∑ w : Fin n → ι, μ.real (cylinder w) * Real.log (ν.real (cylinder w)) := by
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun w _ => by ring
      _ = _ := by rw [sum_measureReal_cylinder μ n, one_mul]
  rw [blockRelEntropy_eq n fun w => (hpos w).ne']
  linarith

theorem IsNormEquilibrium.absolutelyContinuous_of_hasNormGibbs (hA : ∀ i, (A i).det ≠ 0)
    (hq : 0 ≤ q) {μ ν : Measure (ℤ → ι)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MeasurePreserving (shift 1) μ μ) (hν : MeasurePreserving (shift 1) ν ν)
    (heq : IsNormEquilibrium A q μ) (hg : HasNormGibbs A q ν) : μ ≪ ν := by
  obtain ⟨C, hC, hG⟩ := hg
  have hlow : ∀ n : ℕ, 0 < n → ∀ w : Fin n → ι,
      C⁻¹ * (Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn w)‖ ^ q) ≤
        ν.real (cylinder w) := fun n hn w => (hG n hn w).1
  refine absolutelyContinuous_of_blockRelEntropy_le hμ hν (fun n hn w => ?_)
    fun n hn => heq.blockRelEntropy_le hA hq hμ hC hlow hn
  have := norm_word_pos hA (List.ofFn w)
  exact lt_of_lt_of_le (by positivity) (hlow n hn w)

theorem IsNormEquilibrium.eq_of_hasNormGibbs (hA : ∀ i, (A i).det ≠ 0) (hq : 0 ≤ q)
    {μ ν : Measure (ℤ → ι)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MeasurePreserving (shift 1) μ μ) (hν : Ergodic (shift 1) ν)
    (heq : IsNormEquilibrium A q μ) (hg : HasNormGibbs A q ν) : μ = ν :=
  hν.eq_of_absolutelyContinuous hμ
    (heq.absolutelyContinuous_of_hasNormGibbs hA hq hμ hν.toMeasurePreserving hg)

end MatrixTuple

end FractalGeometry
