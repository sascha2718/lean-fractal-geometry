import Mathlib
import FractalGeometry.Probability.Branching.Law
import FractalGeometry.Probability.Branching.Offspring
import FractalGeometry.Probability.Branching.Process

namespace FractalGeometry.Probability.Branching

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

variable {A : Law} {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
  {X : Word A → (Fin A.arity) → Omega → Bool}

noncomputable def offspringSubgaussianParam (A : Law) : ℝ≥0 :=
  (‖((A.arity : ℝ)) - 0‖₊ / 2) ^ 2

lemma coe_offspringSubgaussianParam (A : Law) :
    (offspringSubgaussianParam A : ℝ) = ((A.arity : ℝ)) ^ 2 / 4 := by
  rw [offspringSubgaussianParam, NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, sub_zero,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  push_cast
  ring

lemma hasSubgaussianMGF_m_sub_totalOffspring (hX : IsPercolation P X) (w : Word A) :
    HasSubgaussianMGF (fun ω => A.m - (totalOffspring X w ω : ℝ))
      (offspringSubgaussianParam A) P := by
  let := hX.toIsProbabilityMeasure
  have hmeas : Measurable fun ω => (totalOffspring X w ω : ℝ) :=
    measurable_from_nat.comp (measurable_totalOffspring hX w)
  have hb : ∀ᵐ ω ∂P, (totalOffspring X w ω : ℝ) ∈ Set.Icc (0 : ℝ) ((A.arity : ℝ)) :=
    ae_of_all P fun ω => ⟨Nat.cast_nonneg _, by exact_mod_cast totalOffspring_le X w ω⟩
  have h := (hasSubgaussianMGF_of_mem_Icc hmeas.aemeasurable hb).neg
  rw [integral_totalOffspring hX w] at h
  refine h.congr (ae_of_all P fun ω => ?_)
  simp

theorem measure_sum_totalOffspring_le (hX : IsPercolation P X) (T : Finset (Word A)) {η : ℝ}
    (hη : 0 ≤ η) :
    P {ω | (∑ w ∈ T, (totalOffspring X w ω : ℝ)) ≤ (1 - η) * A.m * T.card} ≤
      ENNReal.ofReal (Real.exp (-(2 * η ^ 2 * A.m ^ 2 * T.card / ((A.arity : ℝ)) ^ 2))) := by
  let := hX.toIsProbabilityMeasure
  rcases Nat.eq_zero_or_pos T.card with hT | hT
  · simp only [hT, Nat.cast_zero, mul_zero, zero_div, neg_zero, Real.exp_zero,
      ENNReal.ofReal_one]
    exact prob_le_one
  set Y : T → Omega → ℝ := fun c ω => A.m - (totalOffspring X c.1 ω : ℝ) with hY
  have hind : iIndepFun Y P := by
    have h := iIndepFun_totalOffspring_of_injective hX (fun c : T => c.1) Subtype.val_injective
    exact h.comp (fun _ x => A.m - x) (fun _ => measurable_const.sub measurable_id)
  have hsub : ∀ c ∈ (Finset.univ : Finset T),
      HasSubgaussianMGF (Y c) (offspringSubgaussianParam A) P :=
    fun c _ => hasSubgaussianMGF_m_sub_totalOffspring hX c.1
  set ε : ℝ := η * A.m * T.card with hε
  have hε0 : 0 ≤ ε := mul_nonneg (mul_nonneg hη A.m_nonneg) (Nat.cast_nonneg _)
  have hH := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind
    (c := fun _ => offspringSubgaussianParam A) hsub hε0
  have hsumY : ∀ ω, ∑ c ∈ (Finset.univ : Finset T), Y c ω =
      A.m * T.card - ∑ w ∈ T, (totalOffspring X w ω : ℝ) := by
    intro ω
    rw [hY, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      nsmul_eq_mul, Finset.sum_coe_sort T (fun w => (totalOffspring X w ω : ℝ))]
    ring
  have hsubset : {ω | (∑ w ∈ T, (totalOffspring X w ω : ℝ)) ≤ (1 - η) * A.m * T.card} ⊆
      {ω | ε ≤ ∑ c ∈ (Finset.univ : Finset T), Y c ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [hsumY, hε]
    linarith
  have hparam : ((∑ _c ∈ (Finset.univ : Finset T), offspringSubgaussianParam A : ℝ≥0) : ℝ) =
      T.card * (((A.arity : ℝ)) ^ 2 / 4) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, NNReal.coe_mul,
      NNReal.coe_natCast, coe_offspringSubgaussianParam]
  have hMN : (0 : ℝ) < (A.arity : ℝ) := by
    exact_mod_cast A.arity_pos
  have hTpos : (0 : ℝ) < T.card := by exact_mod_cast hT
  have hexp : -ε ^ 2 /
      (2 * ((∑ _c ∈ (Finset.univ : Finset T), offspringSubgaussianParam A : ℝ≥0) : ℝ)) =
      -(2 * η ^ 2 * A.m ^ 2 * T.card / ((A.arity : ℝ)) ^ 2) := by
    rw [hparam, hε]
    field_simp
    ring
  calc P {ω | (∑ w ∈ T, (totalOffspring X w ω : ℝ)) ≤ (1 - η) * A.m * T.card}
      ≤ P {ω | ε ≤ ∑ c ∈ (Finset.univ : Finset T), Y c ω} := measure_mono hsubset
    _ = ENNReal.ofReal (P.real {ω | ε ≤ ∑ c ∈ (Finset.univ : Finset T), Y c ω}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (Real.exp (-ε ^ 2 /
          (2 * ((∑ _c ∈ (Finset.univ : Finset T), offspringSubgaussianParam A : ℝ≥0) : ℝ)))) :=
        ENNReal.ofReal_le_ofReal hH
    _ = ENNReal.ofReal (Real.exp (-(2 * η ^ 2 * A.m ^ 2 * T.card / ((A.arity : ℝ)) ^ 2))) := by
        rw [hexp]

end FractalGeometry.Probability.Branching
