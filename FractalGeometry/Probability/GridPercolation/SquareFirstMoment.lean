import FractalGeometry.Probability.GridPercolation.ColumnFirstMoment
import FractalGeometry.Probability.GridPercolation.BlockColumnMoments
import FractalGeometry.Probability.GridPercolation.LowerBounds

/-! Counting approximate squares by retained prefixes and occupied columns. -/

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory ProbabilityTheory Filter
open FractalGeometry.Dimension.PhiAssouad
open scoped ENNReal

variable {A : GridLaw} {Ω : Type*}
  {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

noncomputable def activeColumns (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool)
    (root : Word A) (L : ℕ) (ω : Ω) : Finset (ColumnWord A L) := by
  classical
  exact Finset.univ.filter fun v => 0 < tubePopulationBelow X root v ω

noncomputable def squareCount (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool)
    (b L : ℕ) (ω : Ω) : ℕ :=
  ∑ u ∈ retainedDigitWords X b ω, occupiedColumnCountBelow X (wordOfDigits u) L ω

noncomputable def prefixEvent {b : ℕ} (u : DigitWord A b) : Set (ShallowCoord A b → Bool) :=
  {s | retainedBelowConfig (shallowExtend b s) [] (wordOfDigits u)}

open Classical in
lemma shallowInd_prefixEvent {b : ℕ} (u : DigitWord A b) (ω : Ω) :
    shallowInd X b (prefixEvent u) ω = if Retained X ω (wordOfDigits u) then 1 else 0 := by
  classical
  unfold shallowInd prefixEvent
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  have hiff := retainedBelowConfig_shallow_iff X b ω (root := []) (u := wordOfDigits u)
    (by simp only [List.length_nil, length_wordOfDigits, zero_add, le_refl])
  simp only [hiff, ← retained_iff_retainedBelow_nil]

lemma columnCountFun_deep (root : Word A) (L : ℕ) (ω : Ω) :
    columnCountFun L (deepVector X root ω) = (occupiedColumnCountBelow X root L ω : ℝ) := by
  rw [columnCountFun, deepVector_eq_rebase, occupiedColumnCountConfig_rebase, List.append_nil]
  rfl

lemma squareCount_eq_sum (b L : ℕ) (ω : Ω) :
    (squareCount X b L ω : ℝ) = ∑ u : DigitWord A b,
      shallowInd X b (prefixEvent u) ω * columnCountFun L (deepVector X (wordOfDigits u) ω) := by
  classical
  simp only [squareCount, Nat.cast_sum, shallowInd_prefixEvent, columnCountFun_deep]
  simp only [retainedDigitWords, Set.toFinset_ofPred, Finset.sum_filter,
    ← retained_iff_retainedBelow_nil]
  exact Finset.sum_congr rfl fun u _ => by split_ifs <;> simp_all

lemma descendantCount_eq_sum_prefix (b : ℕ) (ω : Ω) :
    (descendantCountBelow X [] b ω : ℝ) =
      ∑ u : DigitWord A b, shallowInd X b (prefixEvent u) ω := by
  classical
  simp only [descendantCountBelow, Set.toFinset_ofPred, Finset.card_filter, Nat.cast_sum,
    shallowInd_prefixEvent, retained_iff_retainedBelow_nil]
  exact Finset.sum_congr rfl fun u _ => by split_ifs <;> simp

variable [MeasurableSpace Ω] {P : Measure Ω}

lemma measurable_squareCount (hX : IsPercolation P X) (b L : ℕ) :
    Measurable fun ω => (squareCount X b L ω : ℝ) := by
  simp_rw [squareCount_eq_sum]
  exact Finset.measurable_sum _ fun u _ =>
    (measurable_shallowInd hX _ (measurableSet_shallowSet _ _)).mul
      ((measurable_columnCountFun L).comp (measurable_deepVector hX _))

lemma integrable_squareCount (hX : IsPercolation P X) (b L : ℕ) :
    Integrable (fun ω => (squareCount X b L ω : ℝ)) P := by
  simp_rw [squareCount_eq_sum]
  apply integrable_finsetSum
  intro u _
  refine integrable_of_abs_le hX
    ((measurable_shallowInd hX _ (measurableSet_shallowSet _ _)).mul
      ((measurable_columnCountFun L).comp (measurable_deepVector hX _)))
    ((A.M : ℝ) ^ L) fun ω => ?_
  rw [abs_mul, abs_of_nonneg (shallowInd_nonneg _ _ _),
    abs_of_nonneg (columnCountFun_nonneg _ _)]
  exact (mul_le_of_le_one_left (columnCountFun_nonneg _ _) (shallowInd_le_one _ _ _)).trans
    (columnCountFun_le _ _)

theorem integral_squareCount (hX : IsPercolation P X) (b L : ℕ) :
    ∫ ω, (squareCount X b L ω : ℝ) ∂P =
      A.m ^ b * ∫ ω, (occupiedColumnCount X L ω : ℝ) ∂P := by
  have hi (u : DigitWord A b) : Integrable (shallowInd X b (prefixEvent u)) P := by
    refine integrable_of_abs_le hX
      (measurable_shallowInd hX _ (measurableSet_shallowSet _ _)) 1 fun ω => ?_
    rw [abs_of_nonneg (shallowInd_nonneg _ _ _)]
    exact shallowInd_le_one _ _ _
  have hip (u : DigitWord A b) : Integrable (fun ω =>
      shallowInd X b (prefixEvent u) ω * columnCountFun L (deepVector X (wordOfDigits u) ω)) P := by
    refine integrable_of_abs_le hX
      ((measurable_shallowInd hX _ (measurableSet_shallowSet _ _)).mul
        ((measurable_columnCountFun L).comp (measurable_deepVector hX _)))
      ((A.M : ℝ) ^ L) fun ω => ?_
    rw [abs_mul, abs_of_nonneg (shallowInd_nonneg _ _ _),
      abs_of_nonneg (columnCountFun_nonneg _ _)]
    exact (mul_le_of_le_one_left (columnCountFun_nonneg _ _) (shallowInd_le_one _ _ _)).trans
      (columnCountFun_le _ _)
  rw [← integral_descendantCountBelow_nil_eq hX b]
  simp_rw [squareCount_eq_sum, descendantCount_eq_sum_prefix]
  rw [integral_finsetSum _ fun u _ => hip u, integral_finsetSum _ fun u _ => hi u,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  have key := integral_shallow_mul_deep hX (wordOfDigits (A := A) (L := b))
    (fun u => length_wordOfDigits u) (wordOfDigits_injective _) u
    ((prefixEvent u).indicator fun _ => (1 : ℝ)) (columnCountFun L)
    (measurable_const.indicator (measurableSet_shallowSet _ _)) (measurable_columnCountFun L)
  rw [integral_comp_deepVector hX _ (measurable_columnCountFun L)] at key
  exact key

theorem integral_squareCount_le (hX : IsPercolation P X) (b L : ℕ) :
    ∫ ω, (squareCount X b L ω : ℝ) ∂P ≤ A.m ^ b * A.lam ^ L := by
  rw [integral_squareCount hX]
  exact mul_le_mul_of_nonneg_left (integral_occupiedColumnCount_le_lam_pow hX L)
    (pow_nonneg A.m_nonneg _)

end FractalGeometry.Probability.GridPercolation
