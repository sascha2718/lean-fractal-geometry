import FractalGeometry.Probability.GridPercolation.OccupiedColumnMean
import FractalGeometry.Probability.GridPercolation.LambdaTilt

/-! First-moment bounds for occupied columns in rectangular fractal percolation. -/

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {A : GridLaw} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

lemma integral_tubePopulation_eq_product (hX : IsPercolation P X) {L : ℕ}
    (v : ColumnWord A L) :
    ∫ ω, (tubePopulation X v ω : ℝ) ∂P = ∏ l, A.E (v l) := by
  have h := integral_tubePopulation_columnPrefix_eq hX (extendColumnWord A v) L
  rw [columnPrefix_extendColumnWord] at h
  have hp := prod_filter_lt_eq_columnMeanProduct v (le_refl L)
  simp only [Fin.is_lt, Finset.filter_true] at hp
  exact h.trans hp.symm

lemma measure_tubePopulation_pos_le_mean (hX : IsPercolation P X) {L : ℕ}
    (v : ColumnWord A L) :
    (P {ω | 0 < tubePopulation X v ω}).toReal ≤ ∏ l, A.E (v l) := by
  let := hX.toIsProbabilityMeasure
  have hm := measurable_tubePopulation hX v
  have hi : Integrable (fun ω => (tubePopulation X v ω : ℝ)) P := by
    refine Integrable.of_bound (measurable_from_nat.comp hm).aestronglyMeasurable
      ((A.N : ℝ) ^ L) ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast tubePopulation_le_pow X v ω
  rw [← integral_tubePopulation_eq_product hX v]
  have hs := measurableSet_tubePopulation_pos hX v
  calc
    _ = ∫ ω, ({ω | 0 < tubePopulation X v ω} : Set Ω).indicator (fun _ => (1 : ℝ)) ω ∂P := by
      simp [integral_indicator_const, hs, measureReal_def]
    _ ≤ _ := integral_mono ((integrable_const 1).indicator hs) hi (fun ω => by
      by_cases h : 0 < tubePopulation X v ω
      · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left h]
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt h))
      · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right h]
        positivity)

lemma measure_tubePopulation_pos_eq_zero_of_not_allowed (hX : IsPercolation P X) {L : ℕ}
    {v : ColumnWord A L} (hv : v ∉ allowedColumnWords A L) :
    (P {ω | 0 < tubePopulation X v ω}).toReal = 0 := by
  classical
  rw [mem_allowedColumnWords] at hv
  push Not at hv
  obtain ⟨l, hl⟩ := hv
  have he : A.E (v l) = 0 := by
    have := not_lt.mp (mt (A.mem_cols_iff (v l)).mpr hl)
    exact le_antisymm this (A.E_nonneg _)
  have hp : ∏ i, A.E (v i) = 0 := Finset.prod_eq_zero (Finset.mem_univ l) he
  exact le_antisymm ((measure_tubePopulation_pos_le_mean hX v).trans_eq hp)
    ENNReal.toReal_nonneg

lemma measure_tubePopulation_pos_le_tiltWeight (hX : IsPercolation P X) {L : ℕ}
    {v : ColumnWord A L} (hv : v ∈ allowedColumnWords A L)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (P {ω | 0 < tubePopulation X v ω}).toReal ≤ tiltWeight β v := by
  let := hX.toIsProbabilityMeasure
  have hp : 0 < ∏ l, A.E (v l) :=
    Finset.prod_pos fun l _ => E_pos_of_mem_allowedColumnWords hv l
  have ht : tiltWeight β v = (∏ l, A.E (v l)) ^ β := by
    rw [tiltWeight, Real.finsetProd_rpow]
    exact fun l _ => (E_pos_of_mem_allowedColumnWords hv l).le
  rw [ht]
  by_cases h : 1 ≤ ∏ l, A.E (v l)
  · exact (measureReal_le_one (μ := P)).trans (Real.one_le_rpow h hβ0)
  · have hle : ∏ l, A.E (v l) ≤ 1 := (not_le.mp h).le
    refine (measure_tubePopulation_pos_le_mean hX v).trans ?_
    calc
      (∏ l, A.E (v l)) = (∏ l, A.E (v l)) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hp hle hβ1

theorem integral_occupiedColumnCount_le_lam_pow (hX : IsPercolation P X) (L : ℕ) :
    ∫ ω, (occupiedColumnCount X L ω : ℝ) ∂P ≤ A.lam ^ L := by
  classical
  obtain ⟨β, hβ, hval, -⟩ := A.lam_isMinOn
  rw [integral_occupiedColumnCount_eq_sum hX]
  calc
    _ = ∑ v ∈ allowedColumnWords A L, (P {ω | 0 < tubePopulation X v ω}).toReal := by
      symm
      exact Finset.sum_subset (Finset.subset_univ _) fun v _ hv =>
        measure_tubePopulation_pos_eq_zero_of_not_allowed hX hv
    _ ≤ ∑ v ∈ allowedColumnWords A L, tiltWeight β v :=
      Finset.sum_le_sum fun v hv => measure_tubePopulation_pos_le_tiltWeight hX hv hβ.1 hβ.2
    _ = A.lam ^ L := by rw [sum_tiltWeight_eq, hval]

end FractalGeometry.Probability.GridPercolation
