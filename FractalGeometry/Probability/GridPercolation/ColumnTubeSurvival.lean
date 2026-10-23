import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.BranchingSecondMoment
import FractalGeometry.Probability.GridPercolation.ColumnExtensions
import FractalGeometry.Probability.GridPercolation.GenerationConditioning
import FractalGeometry.Probability.GridPercolation.Lambda
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.ProcessMeasurability
import FractalGeometry.Probability.GridPercolation.Processes
import FractalGeometry.Probability.GridPercolation.SecondMoments
import FractalGeometry.Probability.GridPercolation.TubeRecurrence

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open Filter MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {A : GridLaw} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

noncomputable def columnMeanProduct (A : GridLaw) (v : ℕ → Fin A.M) (L : ℕ) : ℝ :=
  ∏ l ∈ Finset.range L, A.E (v l)

@[simp] lemma columnMeanProduct_zero (v : ℕ → Fin A.M) : columnMeanProduct A v 0 = 1 := by
  simp [columnMeanProduct]

lemma columnMeanProduct_succ (v : ℕ → Fin A.M) (L : ℕ) :
    columnMeanProduct A v (L + 1) = columnMeanProduct A v L * A.E (v L) :=
  Finset.prod_range_succ _ _

lemma columnMeanProduct_pos {v : ℕ → Fin A.M} {L : ℕ} (hpos : ∀ l < L, 0 < A.E (v l)) :
    0 < columnMeanProduct A v L :=
  Finset.prod_pos fun l hl => hpos l (Finset.mem_range.mp hl)

lemma prod_filter_lt_eq_columnMeanProduct {ℓ : ℕ} (σ : ColumnWord A ℓ) {k : ℕ} (hk : k ≤ ℓ) :
    ∏ l ∈ Finset.univ.filter (fun l : Fin ℓ => (l : ℕ) < k), A.E (σ l) =
      columnMeanProduct A (extendColumnWord A σ) k := by
  classical
  have h1 : ∏ l ∈ Finset.univ.filter (fun l : Fin ℓ => (l : ℕ) < k), A.E (σ l) =
      ∏ l : Fin ℓ, (fun n : ℕ => if n < k then A.E (extendColumnWord A σ n) else 1) l := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun l _ => ?_
    simp [extendColumnWord, l.isLt]
  have hrange : Finset.range k = (Finset.range ℓ).filter (fun n => n < k) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_filter]
    omega
  refine h1.trans ((Fin.prod_univ_eq_prod_range
    (fun n : ℕ => if n < k then A.E (extendColumnWord A σ n) else 1) ℓ).trans ?_)
  rw [columnMeanProduct, hrange, Finset.prod_filter]

theorem integral_tubePopulation_columnPrefix_succ_eq (hX : IsPercolation P X)
    (v : ℕ → Fin A.M) (L : ℕ) :
    ∫ ω, (tubePopulation X (columnPrefix v (L + 1)) ω : ℝ) ∂P =
      A.E (v L) * ∫ ω, (tubePopulation X (columnPrefix v L) ω : ℝ) ∂P := by
  let : IsProbabilityMeasure P := hX.toIsProbabilityMeasure
  have hcoupled := integral_coupled_eq_of_indepFun_finite_states
    (hX.indepFun_columnPastState_columnFutureState L)
    (hX.measurable_columnPastState L)
    (hX.measurable_columnFutureState L)
    (fun past future => nextTubeFromStates past future (columnPrefix v L) (v L))
    (fun past => A.E (v L) * (pastTubePopulation past (columnPrefix v L) : ℝ))
    (fun past => integral_nextTubeFromStates_eq hX past (columnPrefix v L) (v L))
  have hnext : (fun ω => nextTubeFromStates (columnPastState X L ω)
      (columnFutureState X L ω) (columnPrefix v L) (v L)) =
      fun ω => (tubePopulation X (columnPrefix v (L + 1)) ω : ℝ) := by
    funext ω
    exact nextTubeFromStates_states (X := X) v L ω
  have hpast : (fun ω =>
      A.E (v L) * (pastTubePopulation (columnPastState X L ω) (columnPrefix v L) : ℝ)) =
      fun ω => A.E (v L) * (tubePopulation X (columnPrefix v L) ω : ℝ) := by
    funext ω
    rw [pastTubePopulation_columnPastState]
  rw [hnext, hpast] at hcoupled
  simpa only [integral_const_mul] using hcoupled

theorem integral_tubePopulation_columnPrefix_eq (hX : IsPercolation P X)
    (v : ℕ → Fin A.M) (L : ℕ) :
    ∫ ω, (tubePopulation X (columnPrefix v L) ω : ℝ) ∂P = columnMeanProduct A v L := by
  let : IsProbabilityMeasure P := hX.toIsProbabilityMeasure
  induction L with
  | zero =>
      simp [tubePopulation_columnPrefix_zero]
  | succ L ih =>
      rw [integral_tubePopulation_columnPrefix_succ_eq hX v L, ih, columnMeanProduct_succ]
      ring

theorem integral_sq_tubePopulation_columnPrefix_succ_le (hX : IsPercolation P X)
    (v : ℕ → Fin A.M) (L : ℕ) :
    ∫ ω, (tubePopulation X (columnPrefix v (L + 1)) ω : ℝ) ^ 2 ∂P ≤
      A.E (v L) ^ 2 * ∫ ω, (tubePopulation X (columnPrefix v L) ω : ℝ) ^ 2 ∂P +
        A.N * A.E (v L) * ∫ ω, (tubePopulation X (columnPrefix v L) ω : ℝ) ∂P := by
  let : IsProbabilityMeasure P := hX.toIsProbabilityMeasure
  have hcoupled := integral_coupled_le_of_indepFun_finite_states
    (hX.indepFun_columnPastState_columnFutureState L)
    (hX.measurable_columnPastState L)
    (hX.measurable_columnFutureState L)
    (fun past future => nextTubeFromStates past future (columnPrefix v L) (v L) ^ 2)
    (fun past => A.E (v L) ^ 2 * (pastTubePopulation past (columnPrefix v L) : ℝ) ^ 2 +
      A.N * A.E (v L) * (pastTubePopulation past (columnPrefix v L) : ℝ))
    (fun past => integral_nextTubeFromStates_sq_le hX past (columnPrefix v L) (v L))
  have hnext : (fun ω => nextTubeFromStates (columnPastState X L ω)
      (columnFutureState X L ω) (columnPrefix v L) (v L) ^ 2) =
      fun ω => (tubePopulation X (columnPrefix v (L + 1)) ω : ℝ) ^ 2 := by
    funext ω
    exact congrArg (fun z : ℝ => z ^ 2) (nextTubeFromStates_states (X := X) v L ω)
  let Z : Ω → ℝ := fun ω => (tubePopulation X (columnPrefix v L) ω : ℝ)
  have hpast : (fun ω =>
      A.E (v L) ^ 2 *
          (pastTubePopulation (columnPastState X L ω) (columnPrefix v L) : ℝ) ^ 2 +
        A.N * A.E (v L) *
          (pastTubePopulation (columnPastState X L ω) (columnPrefix v L) : ℝ)) =
      fun ω => A.E (v L) ^ 2 * Z ω ^ 2 + A.N * A.E (v L) * Z ω := by
    funext ω
    simp only [Z]
    rw [pastTubePopulation_columnPastState]
  rw [hnext, hpast] at hcoupled
  have hZbound (ω : Ω) : Z ω ≤ (A.N : ℝ) ^ L := by
    change (tubePopulation X (columnPrefix v L) ω : ℝ) ≤ (A.N : ℝ) ^ L
    exact_mod_cast tubePopulation_le_pow X (columnPrefix v L) ω
  have hZmeas : Measurable Z :=
    measurable_from_nat.comp (measurable_tubePopulation hX (columnPrefix v L))
  have hZint : Integrable Z P := by
    refine Integrable.of_bound hZmeas.aestronglyMeasurable ((A.N : ℝ) ^ L) ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact hZbound ω
  have hZ2int : Integrable (fun ω => Z ω ^ 2) P := by
    refine Integrable.of_bound (hZmeas.pow_const 2).aestronglyMeasurable
      (((A.N : ℝ) ^ L) ^ 2) ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hZbound ω) 2
  have hrhs : ∫ ω, (A.E (v L) ^ 2 * Z ω ^ 2 + A.N * A.E (v L) * Z ω) ∂P =
      A.E (v L) ^ 2 * ∫ ω, Z ω ^ 2 ∂P + A.N * A.E (v L) * ∫ ω, Z ω ∂P := by
    rw [integral_add (hZ2int.const_mul _) (hZint.const_mul _),
      integral_const_mul, integral_const_mul]
  rw [hrhs] at hcoupled
  exact hcoupled

theorem integral_sq_tubePopulation_columnPrefix_le (hX : IsPercolation P X)
    (v : ℕ → Fin A.M) (L : ℕ) (hpos : ∀ l < L, 0 < A.E (v l)) :
    ∫ ω, (tubePopulation X (columnPrefix v L) ω : ℝ) ^ 2 ∂P ≤
      columnMeanProduct A v L ^ 2 *
        (1 + A.N * ∑ k ∈ Finset.range L, (columnMeanProduct A v (k + 1))⁻¹) := by
  let : IsProbabilityMeasure P := hX.toIsProbabilityMeasure
  induction L with
  | zero =>
      simp [tubePopulation_columnPrefix_zero]
  | succ L ih =>
      have hposL : ∀ l < L, 0 < A.E (v l) := fun l hl => hpos l (by omega)
      have he : 0 < A.E (v L) := hpos L (by omega)
      have hPi : 0 < columnMeanProduct A v L := columnMeanProduct_pos hposL
      set S := ∑ k ∈ Finset.range L, (columnMeanProduct A v (k + 1))⁻¹ with hS
      calc ∫ ω, (tubePopulation X (columnPrefix v (L + 1)) ω : ℝ) ^ 2 ∂P
          ≤ A.E (v L) ^ 2 * ∫ ω, (tubePopulation X (columnPrefix v L) ω : ℝ) ^ 2 ∂P +
              A.N * A.E (v L) * ∫ ω, (tubePopulation X (columnPrefix v L) ω : ℝ) ∂P :=
            integral_sq_tubePopulation_columnPrefix_succ_le hX v L
        _ ≤ A.E (v L) ^ 2 * (columnMeanProduct A v L ^ 2 * (1 + A.N * S)) +
              A.N * A.E (v L) * columnMeanProduct A v L := by
            rw [integral_tubePopulation_columnPrefix_eq hX v L]
            gcongr
            exact ih hposL
        _ = columnMeanProduct A v (L + 1) ^ 2 *
              (1 + A.N * ∑ k ∈ Finset.range (L + 1), (columnMeanProduct A v (k + 1))⁻¹) := by
            rw [Finset.sum_range_succ, ← hS, columnMeanProduct_succ]
            field_simp
            ring

theorem one_div_le_measure_tubePopulation_columnPrefix_pos (hX : IsPercolation P X)
    (v : ℕ → Fin A.M) (L : ℕ) (hpos : ∀ l < L, 0 < A.E (v l)) :
    1 / (4 * (1 + A.N * ∑ k ∈ Finset.range L, (columnMeanProduct A v (k + 1))⁻¹)) ≤
      (P {ω | 0 < tubePopulation X (columnPrefix v L) ω}).toReal := by
  let : IsProbabilityMeasure P := hX.toIsProbabilityMeasure
  set S := ∑ k ∈ Finset.range L, (columnMeanProduct A v (k + 1))⁻¹ with hS
  let Z : Ω → ℝ := fun ω => (tubePopulation X (columnPrefix v L) ω : ℝ)
  have hPi : 0 < columnMeanProduct A v L := columnMeanProduct_pos hpos
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k hk =>
    (inv_pos.mpr (columnMeanProduct_pos fun l hl =>
      hpos l (by have := Finset.mem_range.mp hk; omega))).le
  let B : ℝ := columnMeanProduct A v L ^ 2 * (1 + A.N * S)
  have hZmeas : Measurable Z :=
    measurable_from_nat.comp (measurable_tubePopulation hX (columnPrefix v L))
  have hZnonneg (ω : Ω) : 0 ≤ Z ω := Nat.cast_nonneg _
  have hZbound : ∃ C : ℝ, ∀ ω, Z ω ≤ C := by
    refine ⟨(A.N : ℝ) ^ L, fun ω => ?_⟩
    change (tubePopulation X (columnPrefix v L) ω : ℝ) ≤ (A.N : ℝ) ^ L
    exact_mod_cast tubePopulation_le_pow X (columnPrefix v L) ω
  have hB : ∫ ω, Z ω ^ 2 ∂P ≤ B := integral_sq_tubePopulation_columnPrefix_le hX v L hpos
  have hfactor : 0 < 1 + (A.N : ℝ) * S := by positivity
  have hBpos : 0 < B := by
    dsimp only [B]
    positivity
  have hpaley := one_fourth_mul_sq_integral_div_le_measure_ge_half
    hZmeas hZnonneg hZbound hB hBpos
  have hmean : integral P Z = columnMeanProduct A v L :=
    integral_tubePopulation_columnPrefix_eq hX v L
  have hfrac : columnMeanProduct A v L ^ 2 / (4 * B) = 1 / (4 * (1 + A.N * S)) := by
    dsimp only [B]
    field_simp
  have hsub : {ω | integral P Z / 2 ≤ Z ω} ⊆
      {ω | 0 < tubePopulation X (columnPrefix v L) ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have hthreshold : 0 < integral P Z / 2 := by rw [hmean]; positivity
    have : 0 < Z ω := lt_of_lt_of_le hthreshold hω
    change 0 < (tubePopulation X (columnPrefix v L) ω : ℝ) at this
    exact_mod_cast this
  calc 1 / (4 * (1 + A.N * S)) = integral P Z ^ 2 / (4 * B) := by rw [hmean, hfrac]
    _ ≤ (P {ω | integral P Z / 2 ≤ Z ω}).toReal := hpaley
    _ ≤ (P {ω | 0 < tubePopulation X (columnPrefix v L) ω}).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)

theorem inf'_columnMeanProduct_div_le_measure_tubePopulation_pos (hX : IsPercolation P X)
    (v : ℕ → Fin A.M) (L : ℕ) (hpos : ∀ l < L, 0 < A.E (v l)) :
    (Finset.range (L + 1)).inf' Finset.nonempty_range_add_one (columnMeanProduct A v) /
        (4 * (1 + A.N * L)) ≤
      (P {ω | 0 < tubePopulation X (columnPrefix v L) ω}).toReal := by
  set μ := (Finset.range (L + 1)).inf' Finset.nonempty_range_add_one (columnMeanProduct A v)
    with hμ
  set S := ∑ k ∈ Finset.range L, (columnMeanProduct A v (k + 1))⁻¹ with hS
  have hμpos : 0 < μ := by
    rw [hμ, Finset.lt_inf'_iff]
    intro k hk
    exact columnMeanProduct_pos fun l hl =>
      hpos l (by have := Finset.mem_range.mp hk; omega)
  have hμ1 : μ ≤ 1 := by
    have h := Finset.inf'_le (columnMeanProduct A v) (Finset.mem_range.mpr (Nat.succ_pos L))
    rwa [columnMeanProduct_zero] at h
  have hμS : μ * S ≤ L := by
    rw [hS, Finset.mul_sum]
    calc ∑ k ∈ Finset.range L, μ * (columnMeanProduct A v (k + 1))⁻¹
        ≤ ∑ _k ∈ Finset.range L, (1 : ℝ) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' := Finset.mem_range.mp hk
          have hle : μ ≤ columnMeanProduct A v (k + 1) :=
            Finset.inf'_le (columnMeanProduct A v) (Finset.mem_range.mpr (by omega))
          have hPi : 0 < columnMeanProduct A v (k + 1) :=
            columnMeanProduct_pos fun l hl => hpos l (by omega)
          rw [← div_eq_mul_inv]
          exact div_le_one_of_le₀ hle hPi.le
      _ = L := by simp
  have hN : (0 : ℝ) ≤ A.N := Nat.cast_nonneg _
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k hk =>
    (inv_pos.mpr (columnMeanProduct_pos fun l hl =>
      hpos l (by have := Finset.mem_range.mp hk; omega))).le
  have hkey : μ / (4 * (1 + A.N * L)) ≤ 1 / (4 * (1 + A.N * S)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hμS hN]
  exact hkey.trans (one_div_le_measure_tubePopulation_columnPrefix_pos hX v L hpos)

theorem minPrefix_div_le_measure_tubePopulation_pos (hX : IsPercolation P X) {ℓ : ℕ}
    (σ : ColumnWord A ℓ) (hσ : ∀ l, σ l ∈ A.cols) :
    (Finset.range (ℓ + 1)).inf' Finset.nonempty_range_add_one
        (fun k => ∏ l ∈ Finset.univ.filter (fun l : Fin ℓ => (l : ℕ) < k), A.E (σ l)) /
        (4 * (1 + A.N * ℓ)) ≤
      (P {ω | 0 < tubePopulation X σ ω}).toReal := by
  have hpos : ∀ l < ℓ, 0 < A.E (extendColumnWord A σ l) := fun l hl => by
    simp only [extendColumnWord, dite_eq_left hl]
    exact A.E_pos_of_mem_cols (hσ _)
  have hinf : (Finset.range (ℓ + 1)).inf' Finset.nonempty_range_add_one
      (fun k => ∏ l ∈ Finset.univ.filter (fun l : Fin ℓ => (l : ℕ) < k), A.E (σ l)) =
      (Finset.range (ℓ + 1)).inf' Finset.nonempty_range_add_one
        (columnMeanProduct A (extendColumnWord A σ)) :=
    Finset.inf'_congr Finset.nonempty_range_add_one rfl fun k hk =>
      prod_filter_lt_eq_columnMeanProduct σ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  have h := inf'_columnMeanProduct_div_le_measure_tubePopulation_pos hX
    (extendColumnWord A σ) ℓ hpos
  rw [columnPrefix_extendColumnWord] at h
  rw [hinf]
  exact h

end FractalGeometry.Probability.GridPercolation
