import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.BlockColumnProcess
import FractalGeometry.Probability.GridPercolation.BlockIndependence
import FractalGeometry.Probability.GridPercolation.BranchingSecondMoment
import FractalGeometry.Probability.GridPercolation.Configuration
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.LawInvariance
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.Processes
import FractalGeometry.Probability.GridPercolation.PrunedSurvival
import FractalGeometry.Probability.GridPercolation.RootIndependence
import FractalGeometry.Probability.GridPercolation.SecondMomentRoots
import FractalGeometry.Probability.GridPercolation.SecondMoments
import FractalGeometry.Probability.GridPercolation.ShallowEvents
import FractalGeometry.Probability.GridPercolation.Subtrees
import FractalGeometry.Probability.GridPercolation.SurvivalGrowth
import FractalGeometry.Probability.GridPercolation.WordSplitting

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory ProbabilityTheory Filter Topology

open scoped ENNReal

variable {A : GridLaw}

instance finite_shallowCoord (c : ℕ) : Finite (ShallowCoord A c) := by
  have h : Finite ↥{u : Word A | u.length < c} := (List.finite_length_lt _ c).to_subtype
  exact @Finite.instProd _ _ h inferInstance

lemma measurableSet_shallowSet (c : ℕ) (S : Set (ShallowCoord A c → Bool)) :
    MeasurableSet S :=
  S.to_countable.measurableSet

lemma exists_wordOfDigits_eq_of_length {w : Word A} {L : ℕ} (hw : w.length = L) :
    ∃ u : DigitWord A L, wordOfDigits u = w := by
  refine ⟨fun l => w.get (Fin.cast hw.symm l), ?_⟩
  apply List.ext_getElem
  · simp [hw]
  · intro i h1 h2
    simp [wordOfDigits]

lemma sum_blockReps_eq (x : Configuration A) (ℓ t : ℕ) (f : Word A → ℝ) :
    ∑ c ∈ blockReps x ℓ t, f c = ∑ u : DigitWord A (t * ℓ),
      if wordOfDigits u ∈ blockReps x ℓ t then f (wordOfDigits u) else 0 := by
  classical
  rw [← Finset.sum_filter]
  have himage : blockReps x ℓ t = (Finset.univ.filter fun u : DigitWord A (t * ℓ) =>
      wordOfDigits u ∈ blockReps x ℓ t).image wordOfDigits := by
    ext w
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hw
      obtain ⟨u, hu⟩ := exists_wordOfDigits_eq_of_length (mem_blockReps hw).1
      exact ⟨u, hu ▸ hw, hu⟩
    · rintro ⟨u, hu, rfl⟩
      exact hu
  calc ∑ c ∈ blockReps x ℓ t, f c
      = ∑ c ∈ (Finset.univ.filter fun u : DigitWord A (t * ℓ) =>
          wordOfDigits u ∈ blockReps x ℓ t).image wordOfDigits, f c := by
        rw [← himage]
    _ = _ := Finset.sum_image fun u _ u' _ h => wordOfDigits_injective _ h

def blockActive (ℓ t : ℕ) (u : DigitWord A (t * ℓ)) : Set (ShallowCoord A (t * ℓ) → Bool) :=
  {v | wordOfDigits u ∈ blockReps (shallowExtend (t * ℓ) v) ℓ t}

noncomputable def columnCountFun (ℓ : ℕ) (x : Configuration A) : ℝ :=
  (occupiedColumnCountConfig x [] ℓ : ℝ)

noncomputable def descentFun (x : Configuration A) : ℝ :=
  {y : Configuration A | hasInfiniteDescentConfig y []}.indicator (fun _ => (1 : ℝ)) x

lemma measurable_columnCountFun (ℓ : ℕ) : Measurable (columnCountFun (A := A) ℓ) :=
  measurable_from_nat.comp (measurable_occupiedColumnCountConfig [] ℓ)

lemma measurable_descentFun : Measurable (descentFun (A := A)) :=
  measurable_const.indicator (measurableSet_hasInfiniteDescentConfig [])

lemma columnCountFun_nonneg (ℓ : ℕ) (x : Configuration A) : 0 ≤ columnCountFun ℓ x :=
  Nat.cast_nonneg _

lemma columnCountFun_le (ℓ : ℕ) (x : Configuration A) :
    columnCountFun ℓ x ≤ (A.M : ℝ) ^ ℓ := by
  classical
  unfold columnCountFun occupiedColumnCountConfig
  have h : ((Finset.univ : Finset (ColumnWord A ℓ)).filter fun v =>
      0 < tubePopulationConfig x [] v).card ≤ A.M ^ ℓ :=
    (Finset.card_filter_le _ _).trans (by simp)
  exact_mod_cast h

section Counts

variable {Ω : Type*} {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

variable (X) in

noncomputable def blockCount (ℓ t : ℕ) (ω : Ω) : ℕ :=
  (blockReps (config X ω) ℓ t).card

variable (X) in

open Classical in

noncomputable def blockSurvivorCount (ℓ t : ℕ) (ω : Ω) : ℕ :=
  ((blockReps (config X ω) ℓ t).filter fun w => hasInfiniteDescentConfig (config X ω) w).card

lemma blockReps_shallowExtend (ℓ t : ℕ) (ω : Ω) :
    blockReps (shallowExtend (t * ℓ) (shallowVector X (t * ℓ) ω)) ℓ t =
      blockReps (config X ω) ℓ t :=
  blockReps_congr t fun q hq => shallowExtend_shallowVector X (t * ℓ) ω q hq

lemma shallowInd_blockActive (ℓ t : ℕ) (u : DigitWord A (t * ℓ)) (ω : Ω) :
    shallowInd X (t * ℓ) (blockActive ℓ t u) ω =
      if wordOfDigits u ∈ blockReps (config X ω) ℓ t then 1 else 0 := by
  unfold shallowInd blockActive
  rw [Set.indicator_apply]
  simp only [Set.mem_ofPred_eq, blockReps_shallowExtend]

lemma blockCount_eq_sum (ℓ t : ℕ) (ω : Ω) :
    (blockCount X ℓ t ω : ℝ) = ∑ u : DigitWord A (t * ℓ), shallowInd X (t * ℓ) (blockActive ℓ t u) ω := by
  have h := sum_blockReps_eq (config X ω) ℓ t (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [blockCount, h]
  exact Finset.sum_congr rfl fun u _ => (shallowInd_blockActive ℓ t u ω).symm

lemma blockCount_succ_eq_sum (ℓ t : ℕ) (ω : Ω) :
    (blockCount X ℓ (t + 1) ω : ℝ) = ∑ u : DigitWord A (t * ℓ),
      shallowInd X (t * ℓ) (blockActive ℓ t u) ω *
        columnCountFun ℓ (deepVector X (wordOfDigits u) ω) := by
  rw [blockCount, card_blockReps_succ, Nat.cast_sum,
    sum_blockReps_eq (config X ω) ℓ t (fun c => (occupiedColumnCountConfig (config X ω) c ℓ : ℝ))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [shallowInd_blockActive, columnCountFun, deepVector_eq_rebase,
    occupiedColumnCountConfig_rebase, List.append_nil]
  split_ifs <;> simp

lemma blockSurvivorCount_eq_sum (ℓ t : ℕ) (ω : Ω) :
    (blockSurvivorCount X ℓ t ω : ℝ) = ∑ u : DigitWord A (t * ℓ),
      shallowInd X (t * ℓ) (blockActive ℓ t u) ω * descentFun (deepVector X (wordOfDigits u) ω) := by
  classical
  rw [blockSurvivorCount, Finset.card_filter, Nat.cast_sum,
    sum_blockReps_eq (config X ω) ℓ t
      (fun c => ((if hasInfiniteDescentConfig (config X ω) c then 1 else 0 : ℕ) : ℝ))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [shallowInd_blockActive, descentFun, deepVector_eq_rebase, Set.indicator_apply]
  simp only [Set.mem_ofPred_eq, hasInfiniteDescentConfig_rebase, List.append_nil]
  split_ifs <;> simp

lemma blockCount_le_card (ℓ t : ℕ) (ω : Ω) :
    (blockCount X ℓ t ω : ℝ) ≤ Fintype.card (DigitWord A (t * ℓ)) := by
  rw [blockCount_eq_sum]
  calc ∑ u : DigitWord A (t * ℓ), shallowInd X (t * ℓ) (blockActive ℓ t u) ω
      ≤ ∑ _u : DigitWord A (t * ℓ), (1 : ℝ) :=
        Finset.sum_le_sum fun u _ => shallowInd_le_one _ _ _
    _ = Fintype.card (DigitWord A (t * ℓ)) := by simp

open Classical in

lemma blockSurvivorCount_le_blockCount (ℓ t : ℕ) (ω : Ω) :
    blockSurvivorCount X ℓ t ω ≤ blockCount X ℓ t ω :=
  Finset.card_filter_le _ _

end Counts

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

lemma integral_comp_deepVector (hX : IsPercolation P X) (root : Word A)
    {F : Configuration A → ℝ} (hF : Measurable F) :
    ∫ ω, F (deepVector X root ω) ∂P = ∫ ω, F (config X ω) ∂P := by
  have h1 : ∫ ω, F (deepVector X root ω) ∂P =
      ∫ x, F x ∂(P.map (config (shiftFamily X root))) :=
    (integral_map (measurable_config (hX.shift root)).aemeasurable
      hF.aestronglyMeasurable).symm
  rw [h1, hX.map_config_shift_eq root,
    integral_map (measurable_config hX).aemeasurable hF.aestronglyMeasurable]

lemma measurable_blockCount (hX : IsPercolation P X) (ℓ t : ℕ) :
    Measurable fun ω => (blockCount X ℓ t ω : ℝ) := by
  simp_rw [blockCount_eq_sum]
  exact Finset.measurable_sum _ fun u _ =>
    measurable_shallowInd hX _ (measurableSet_shallowSet _ _)

lemma measurable_blockSurvivorCount (hX : IsPercolation P X) (ℓ t : ℕ) :
    Measurable fun ω => (blockSurvivorCount X ℓ t ω : ℝ) := by
  simp_rw [blockSurvivorCount_eq_sum]
  exact Finset.measurable_sum _ fun u _ =>
    (measurable_shallowInd hX _ (measurableSet_shallowSet _ _)).mul
      (measurable_descentFun.comp (measurable_deepVector hX _))

lemma integrable_of_abs_le (hX : IsPercolation P X) {f : Ω → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ ω, |f ω| ≤ C) : Integrable f P := by
  let := hX.toIsProbabilityMeasure
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)

theorem integral_blockCount_succ (hX : IsPercolation P X) (ℓ t : ℕ) :
    ∫ ω, (blockCount X ℓ (t + 1) ω : ℝ) ∂P =
      (∫ ω, (occupiedColumnCount X ℓ ω : ℝ) ∂P) * ∫ ω, (blockCount X ℓ t ω : ℝ) ∂P := by
  let := hX.toIsProbabilityMeasure
  have hYm : ∀ u : DigitWord A (t * ℓ),
      Measurable (shallowInd X (t * ℓ) (blockActive ℓ t u)) :=
    fun u => measurable_shallowInd hX _ (measurableSet_shallowSet _ _)
  have hint1 : ∀ u : DigitWord A (t * ℓ), Integrable (fun ω =>
      shallowInd X (t * ℓ) (blockActive ℓ t u) ω *
        columnCountFun ℓ (deepVector X (wordOfDigits u) ω)) P := by
    intro u
    refine integrable_of_abs_le hX ((hYm u).mul
      ((measurable_columnCountFun ℓ).comp (measurable_deepVector hX _))) ((A.M : ℝ) ^ ℓ)
      fun ω => ?_
    rw [abs_mul, abs_of_nonneg (shallowInd_nonneg _ _ _),
      abs_of_nonneg (columnCountFun_nonneg _ _)]
    exact (mul_le_of_le_one_left (columnCountFun_nonneg _ _) (shallowInd_le_one _ _ _)).trans
      (columnCountFun_le _ _)
  have hint2 : ∀ u : DigitWord A (t * ℓ),
      Integrable (shallowInd X (t * ℓ) (blockActive ℓ t u)) P := by
    intro u
    refine integrable_of_abs_le hX (hYm u) 1 fun ω => ?_
    rw [abs_of_nonneg (shallowInd_nonneg _ _ _)]
    exact shallowInd_le_one _ _ _
  simp_rw [blockCount_succ_eq_sum, blockCount_eq_sum]
  rw [integral_finsetSum _ fun u _ => hint1 u, integral_finsetSum _ fun u _ => hint2 u,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  have key := integral_shallow_mul_deep hX (wordOfDigits (A := A) (L := t * ℓ))
    (fun u => length_wordOfDigits u) (wordOfDigits_injective _) u
    (fun s => (blockActive ℓ t u).indicator (fun _ => (1 : ℝ)) s) (columnCountFun ℓ)
    (measurable_const.indicator (measurableSet_shallowSet _ _)) (measurable_columnCountFun ℓ)
  rw [integral_comp_deepVector hX _ (measurable_columnCountFun ℓ)] at key
  exact key.trans (mul_comm _ _)

theorem integral_blockCount (hX : IsPercolation P X) (ℓ t : ℕ) :
    ∫ ω, (blockCount X ℓ t ω : ℝ) ∂P = (∫ ω, (occupiedColumnCount X ℓ ω : ℝ) ∂P) ^ t := by
  let := hX.toIsProbabilityMeasure
  induction t with
  | zero => simp [blockCount, blockReps]
  | succ t ih => rw [integral_blockCount_succ hX, ih, pow_succ, mul_comm]

theorem integral_sq_blockCount_succ_le (hX : IsPercolation P X) (ℓ t : ℕ) :
    ∫ ω, (blockCount X ℓ (t + 1) ω : ℝ) ^ 2 ∂P ≤
      (∫ ω, (occupiedColumnCount X ℓ ω : ℝ) ∂P) ^ 2 * ∫ ω, (blockCount X ℓ t ω : ℝ) ^ 2 ∂P +
        (A.M : ℝ) ^ ℓ * (∫ ω, (occupiedColumnCount X ℓ ω : ℝ) ∂P) *
          ∫ ω, (blockCount X ℓ t ω : ℝ) ∂P := by
  classical
  let := hX.toIsProbabilityMeasure
  set μ := ∫ ω, (occupiedColumnCount X ℓ ω : ℝ) ∂P with hμ
  have hμc : ∫ ω, columnCountFun ℓ (config X ω) ∂P = μ := rfl
  set Y : DigitWord A (t * ℓ) → Ω → ℝ := fun u => shallowInd X (t * ℓ) (blockActive ℓ t u)
    with hY
  set Cn : DigitWord A (t * ℓ) → Ω → ℝ :=
    fun u ω => columnCountFun ℓ (deepVector X (wordOfDigits u) ω) with hCn
  have hYm : ∀ u, Measurable (Y u) :=
    fun u => measurable_shallowInd hX _ (measurableSet_shallowSet _ _)
  have hCm : ∀ u, Measurable (Cn u) :=
    fun u => (measurable_columnCountFun ℓ).comp (measurable_deepVector hX _)
  have hY0 : ∀ u ω, 0 ≤ Y u ω := fun u ω => shallowInd_nonneg _ _ _
  have hY1 : ∀ u ω, Y u ω ≤ 1 := fun u ω => shallowInd_le_one _ _ _
  have hC0 : ∀ u ω, 0 ≤ Cn u ω := fun u ω => columnCountFun_nonneg _ _
  have hC1 : ∀ u ω, Cn u ω ≤ (A.M : ℝ) ^ ℓ := fun u ω => columnCountFun_le _ _
  have hMℓ : (0 : ℝ) ≤ (A.M : ℝ) ^ ℓ := by positivity
  have hYC : ∀ u ω, |Y u ω * Cn u ω| ≤ (A.M : ℝ) ^ ℓ := by
    intro u ω
    rw [abs_mul, abs_of_nonneg (hY0 u ω), abs_of_nonneg (hC0 u ω)]
    exact (mul_le_of_le_one_left (hC0 u ω) (hY1 u ω)).trans (hC1 u ω)
  have hint : ∀ u u', Integrable (fun ω => (Y u ω * Cn u ω) * (Y u' ω * Cn u' ω)) P := by
    intro u u'
    refine integrable_of_abs_le hX (((hYm u).mul (hCm u)).mul ((hYm u').mul (hCm u')))
      ((A.M : ℝ) ^ ℓ * (A.M : ℝ) ^ ℓ) fun ω => ?_
    rw [abs_mul]
    exact mul_le_mul (hYC u ω) (hYC u' ω) (abs_nonneg _) hMℓ
  have hintY : ∀ u u', Integrable (fun ω => Y u ω * Y u' ω) P := by
    intro u u'
    refine integrable_of_abs_le hX ((hYm u).mul (hYm u')) 1 fun ω => ?_
    rw [abs_mul, abs_of_nonneg (hY0 u ω), abs_of_nonneg (hY0 u' ω)]
    exact (mul_le_of_le_one_left (hY0 u' ω) (hY1 u ω)).trans (hY1 u' ω)
  have hintY1 : ∀ u, Integrable (Y u) P := by
    intro u
    refine integrable_of_abs_le hX (hYm u) 1 fun ω => ?_
    rw [abs_of_nonneg (hY0 u ω)]
    exact hY1 u ω
  have hsq1 : ∀ ω, (blockCount X ℓ (t + 1) ω : ℝ) ^ 2 =
      ∑ u, ∑ u', (Y u ω * Cn u ω) * (Y u' ω * Cn u' ω) := by
    intro ω
    rw [blockCount_succ_eq_sum, sq, Finset.sum_mul_sum]
  have hsq0 : ∀ ω, (blockCount X ℓ t ω : ℝ) ^ 2 = ∑ u, ∑ u', Y u ω * Y u' ω := by
    intro ω
    rw [blockCount_eq_sum, sq, Finset.sum_mul_sum]
  have hsecond : ∫ ω, columnCountFun ℓ (config X ω) ^ 2 ∂P ≤ (A.M : ℝ) ^ ℓ * μ := by
    rw [← hμc, ← integral_const_mul]
    refine integral_mono ?_ ?_ fun ω => ?_
    · refine integrable_of_abs_le hX ((measurable_columnCountFun ℓ).comp
        (measurable_config hX) |>.pow_const 2) ((A.M : ℝ) ^ ℓ * (A.M : ℝ) ^ ℓ) fun ω => ?_
      rw [abs_pow, abs_of_nonneg (columnCountFun_nonneg _ _), sq]
      exact mul_le_mul (columnCountFun_le _ _) (columnCountFun_le _ _)
        (columnCountFun_nonneg _ _) hMℓ
    · refine integrable_of_abs_le hX (((measurable_columnCountFun ℓ).comp
        (measurable_config hX)).const_mul _) ((A.M : ℝ) ^ ℓ * (A.M : ℝ) ^ ℓ) fun ω => ?_
      rw [abs_mul, abs_of_nonneg hMℓ, abs_of_nonneg (columnCountFun_nonneg _ _)]
      exact mul_le_mul_of_nonneg_left (columnCountFun_le _ _) hMℓ
    · show columnCountFun ℓ (config X ω) ^ 2 ≤ (A.M : ℝ) ^ ℓ * columnCountFun ℓ (config X ω)
      rw [sq]
      exact mul_le_mul_of_nonneg_right (columnCountFun_le _ _) (columnCountFun_nonneg _ _)
  have hterm : ∀ u u', ∫ ω, (Y u ω * Cn u ω) * (Y u' ω * Cn u' ω) ∂P ≤
      μ ^ 2 * ∫ ω, Y u ω * Y u' ω ∂P +
        if u = u' then (A.M : ℝ) ^ ℓ * μ * ∫ ω, Y u ω ∂P else 0 := by
    intro u u'
    by_cases huu : u = u'
    · subst huu
      simp only [ite_true]
      have hrw : ∀ ω, (Y u ω * Cn u ω) * (Y u ω * Cn u ω) = Y u ω * Cn u ω ^ 2 := by
        intro ω
        have hself : Y u ω * Y u ω = Y u ω := shallowInd_mul_self (X := X) _ _ ω
        calc (Y u ω * Cn u ω) * (Y u ω * Cn u ω) = (Y u ω * Y u ω) * Cn u ω ^ 2 := by ring
          _ = Y u ω * Cn u ω ^ 2 := by rw [hself]
      have key := integral_shallow_mul_deep hX (wordOfDigits (A := A) (L := t * ℓ))
        (fun u => length_wordOfDigits u) (wordOfDigits_injective _) u
        (fun s => (blockActive ℓ t u).indicator (fun _ => (1 : ℝ)) s)
        (fun x => columnCountFun ℓ x ^ 2)
        (measurable_const.indicator (measurableSet_shallowSet _ _))
        ((measurable_columnCountFun ℓ).pow_const 2)
      rw [integral_comp_deepVector hX _ ((measurable_columnCountFun ℓ).pow_const 2)] at key
      have hYi0 : 0 ≤ ∫ ω, Y u ω ∂P := integral_nonneg fun ω => hY0 u ω
      have hYY0 : 0 ≤ ∫ ω, Y u ω * Y u ω ∂P :=
        integral_nonneg fun ω => mul_nonneg (hY0 u ω) (hY0 u ω)
      calc ∫ ω, (Y u ω * Cn u ω) * (Y u ω * Cn u ω) ∂P = ∫ ω, Y u ω * Cn u ω ^ 2 ∂P := by
            congr 1
            funext ω
            exact hrw ω
        _ = (∫ ω, Y u ω ∂P) * ∫ ω, columnCountFun ℓ (config X ω) ^ 2 ∂P := key
        _ ≤ (∫ ω, Y u ω ∂P) * ((A.M : ℝ) ^ ℓ * μ) := mul_le_mul_of_nonneg_left hsecond hYi0
        _ ≤ μ ^ 2 * ∫ ω, Y u ω * Y u ω ∂P + (A.M : ℝ) ^ ℓ * μ * ∫ ω, Y u ω ∂P := by
            nlinarith [mul_nonneg (sq_nonneg μ) hYY0]
    · simp only [huu, ite_false, add_zero]
      have key := integral_shallow_mul_deep_mul_deep hX (wordOfDigits (A := A) (L := t * ℓ))
        (fun u => length_wordOfDigits u) (wordOfDigits_injective _) huu
        (fun s => (blockActive ℓ t u).indicator (fun _ => (1 : ℝ)) s *
          (blockActive ℓ t u').indicator (fun _ => (1 : ℝ)) s)
        (columnCountFun ℓ) (columnCountFun ℓ)
        ((measurable_const.indicator (measurableSet_shallowSet _ _)).mul
          (measurable_const.indicator (measurableSet_shallowSet _ _)))
        (measurable_columnCountFun ℓ) (measurable_columnCountFun ℓ)
      simp only at key
      rw [integral_comp_deepVector hX _ (measurable_columnCountFun ℓ),
        integral_comp_deepVector hX _ (measurable_columnCountFun ℓ), hμc] at key
      refine le_of_eq ?_
      calc ∫ ω, (Y u ω * Cn u ω) * (Y u' ω * Cn u' ω) ∂P
          = ∫ ω, (Y u ω * Y u' ω) * (Cn u ω * Cn u' ω) ∂P := by
            congr 1
            funext ω
            ring
        _ = (∫ ω, Y u ω * Y u' ω ∂P) * (μ * μ) := key
        _ = μ ^ 2 * ∫ ω, Y u ω * Y u' ω ∂P := by ring
  calc ∫ ω, (blockCount X ℓ (t + 1) ω : ℝ) ^ 2 ∂P
      = ∑ u, ∑ u', ∫ ω, (Y u ω * Cn u ω) * (Y u' ω * Cn u' ω) ∂P := by
        simp_rw [hsq1]
        rw [integral_finsetSum _ fun u _ => integrable_finsetSum _ fun u' _ => hint u u']
        exact Finset.sum_congr rfl fun u _ => integral_finsetSum _ fun u' _ => hint u u'
    _ ≤ ∑ u, ∑ u', (μ ^ 2 * ∫ ω, Y u ω * Y u' ω ∂P +
          if u = u' then (A.M : ℝ) ^ ℓ * μ * ∫ ω, Y u ω ∂P else 0) :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun u' _ => hterm u u'
    _ = μ ^ 2 * ∑ u, ∑ u', ∫ ω, Y u ω * Y u' ω ∂P +
          (A.M : ℝ) ^ ℓ * μ * ∑ u, ∫ ω, Y u ω ∂P := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mul_sum]
        simp
    _ = μ ^ 2 * ∫ ω, (blockCount X ℓ t ω : ℝ) ^ 2 ∂P +
          (A.M : ℝ) ^ ℓ * μ * ∫ ω, (blockCount X ℓ t ω : ℝ) ∂P := by
        congr 2
        · simp_rw [hsq0]
          rw [integral_finsetSum _ fun u _ => integrable_finsetSum _ fun u' _ => hintY u u']
          exact (Finset.sum_congr rfl fun u _ => integral_finsetSum _ fun u' _ => hintY u u').symm
        · simp_rw [blockCount_eq_sum]
          rw [integral_finsetSum _ fun u _ => hintY1 u]

theorem integral_sq_blockCount_le (hX : IsPercolation P X) (ℓ : ℕ)
    (hμ : 1 < ∫ ω, (occupiedColumnCount X ℓ ω : ℝ) ∂P) (t : ℕ) :
    ∫ ω, (blockCount X ℓ t ω : ℝ) ^ 2 ∂P ≤
      (∫ ω, (occupiedColumnCount X ℓ ω : ℝ) ∂P) ^ (2 * t) *
        (1 + (A.M : ℝ) ^ ℓ / ((∫ ω, (occupiedColumnCount X ℓ ω : ℝ) ∂P) - 1)) := by
  let := hX.toIsProbabilityMeasure
  refine secondMoment_le_mean_sq_mul_uniform hμ (by positivity)
    (a := fun n => ∫ ω, (blockCount X ℓ n ω : ℝ) ∂P)
    (b := fun n => ∫ ω, (blockCount X ℓ n ω : ℝ) ^ 2 ∂P)
    (fun n => integral_blockCount hX ℓ n) ?_ (fun n => integral_sq_blockCount_succ_le hX ℓ n) t
  simp [blockCount, blockReps]

theorem integral_blockSurvivorCount (hX : IsPercolation P X) (ℓ t : ℕ) :
    ∫ ω, (blockSurvivorCount X ℓ t ω : ℝ) ∂P =
      (P (survival X)).toReal * (∫ ω, (occupiedColumnCount X ℓ ω : ℝ) ∂P) ^ t := by
  let := hX.toIsProbabilityMeasure
  have hYm : ∀ u : DigitWord A (t * ℓ),
      Measurable (shallowInd X (t * ℓ) (blockActive ℓ t u)) :=
    fun u => measurable_shallowInd hX _ (measurableSet_shallowSet _ _)
  have hint1 : ∀ u : DigitWord A (t * ℓ), Integrable (fun ω =>
      shallowInd X (t * ℓ) (blockActive ℓ t u) ω *
        descentFun (deepVector X (wordOfDigits u) ω)) P := by
    intro u
    refine integrable_of_abs_le hX ((hYm u).mul
      (measurable_descentFun.comp (measurable_deepVector hX _))) 1 fun ω => ?_
    have h0 : 0 ≤ descentFun (deepVector X (wordOfDigits u) ω) :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have h1 : descentFun (deepVector X (wordOfDigits u) ω) ≤ 1 :=
      Set.indicator_le_self' (fun _ _ => zero_le_one) _
    rw [abs_mul, abs_of_nonneg (shallowInd_nonneg _ _ _), abs_of_nonneg h0]
    exact (mul_le_of_le_one_left h0 (shallowInd_le_one _ _ _)).trans h1
  have hint2 : ∀ u : DigitWord A (t * ℓ),
      Integrable (shallowInd X (t * ℓ) (blockActive ℓ t u)) P := by
    intro u
    refine integrable_of_abs_le hX (hYm u) 1 fun ω => ?_
    rw [abs_of_nonneg (shallowInd_nonneg _ _ _)]
    exact shallowInd_le_one _ _ _
  have hdesc : ∫ ω, descentFun (config X ω) ∂P = (P (survival X)).toReal := by
    have h := integral_deepInd hX ([] : Word A) (measurableSet_hasInfiniteDescentConfig [])
    have hset : {ω | config X ω ∈ {y : Configuration A | hasInfiniteDescentConfig y []}} =
        survival X := by
      ext ω
      exact config_mem_survival_iff ω
    rw [hset] at h
    exact h
  rw [← integral_blockCount hX ℓ t]
  simp_rw [blockSurvivorCount_eq_sum, blockCount_eq_sum]
  rw [integral_finsetSum _ fun u _ => hint1 u, integral_finsetSum _ fun u _ => hint2 u,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  have key := integral_shallow_mul_deep hX (wordOfDigits (A := A) (L := t * ℓ))
    (fun u => length_wordOfDigits u) (wordOfDigits_injective _) u
    (fun s => (blockActive ℓ t u).indicator (fun _ => (1 : ℝ)) s) descentFun
    (measurable_const.indicator (measurableSet_shallowSet _ _)) measurable_descentFun
  rw [integral_comp_deepVector hX _ measurable_descentFun, hdesc] at key
  exact key.trans (mul_comm _ _)

theorem exists_measure_prunedColumnCount_block_ge (hX : IsPercolation P X) (hm : 1 < A.m)
    {ℓ : ℕ} (hμ : 1 < ∫ ω, (occupiedColumnCount X ℓ ω : ℝ) ∂P) :
    ∃ ρ > 0, ∀ t : ℕ, ENNReal.ofReal ρ ≤ P {ω | (P (survival X)).toReal / 2 *
      (∫ ω', (occupiedColumnCount X ℓ ω' : ℝ) ∂P) ^ t ≤ (prunedColumnCount X (t * ℓ) ω : ℝ)} := by
  let := hX.toIsProbabilityMeasure
  set μ := ∫ ω, (occupiedColumnCount X ℓ ω : ℝ) ∂P with hμdef
  set p := (P (survival X)).toReal with hp
  have hp0 : 0 < p :=
    ENNReal.toReal_pos (measure_survival_pos_of_one_lt_m hX hm).ne' (measure_ne_top _ _)
  have hμ0 : 0 < μ := by linarith
  set K := 1 + (A.M : ℝ) ^ ℓ / (μ - 1) with hK
  have hK0 : 0 < K := by
    have : 0 < μ - 1 := sub_pos.mpr hμ
    positivity
  refine ⟨p ^ 2 / (4 * K), by positivity, fun t => ?_⟩
  set Z : Ω → ℝ := fun ω => (blockSurvivorCount X ℓ t ω : ℝ) with hZ
  have hZmeas : Measurable Z := measurable_blockSurvivorCount hX ℓ t
  have hZnonneg : ∀ ω, 0 ≤ Z ω := fun ω => Nat.cast_nonneg _
  have hZT : ∀ ω, Z ω ≤ (blockCount X ℓ t ω : ℝ) := fun ω => by
    show (blockSurvivorCount X ℓ t ω : ℝ) ≤ _
    exact_mod_cast blockSurvivorCount_le_blockCount (X := X) ℓ t ω
  have hZbound : ∃ C : ℝ, ∀ ω, Z ω ≤ C :=
    ⟨Fintype.card (DigitWord A (t * ℓ)), fun ω => (hZT ω).trans (blockCount_le_card ℓ t ω)⟩
  set B := μ ^ (2 * t) * K with hB
  have hBpos : 0 < B := by positivity
  have hTbound : ∀ ω, |(blockCount X ℓ t ω : ℝ) ^ 2| ≤
      (Fintype.card (DigitWord A (t * ℓ)) : ℝ) ^ 2 := by
    intro ω
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (blockCount_le_card ℓ t ω) 2
  have hZ2 : ∫ ω, Z ω ^ 2 ∂P ≤ B := by
    refine (integral_mono ?_ ?_ fun ω => pow_le_pow_left₀ (hZnonneg ω) (hZT ω) 2).trans
      (integral_sq_blockCount_le hX ℓ hμ t)
    · refine integrable_of_abs_le hX (hZmeas.pow_const 2)
        ((Fintype.card (DigitWord A (t * ℓ)) : ℝ) ^ 2) fun ω => ?_
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (hZnonneg ω) ((hZT ω).trans (blockCount_le_card ℓ t ω)) 2
    · exact integrable_of_abs_le hX ((measurable_blockCount hX ℓ t).pow_const 2) _ hTbound
  have hpz := one_fourth_mul_sq_integral_div_le_measure_ge_half hZmeas hZnonneg hZbound hZ2 hBpos
  have hmean : ∫ ω, Z ω ∂P = p * μ ^ t := integral_blockSurvivorCount hX ℓ t
  rw [hmean] at hpz
  have hfrac : (p * μ ^ t) ^ 2 / (4 * B) = p ^ 2 / (4 * K) := by
    rw [hB, pow_mul']
    field_simp
  rw [hfrac] at hpz
  have hsub : {ω | p * μ ^ t / 2 ≤ Z ω} ⊆
      {ω | p / 2 * μ ^ t ≤ (prunedColumnCount X (t * ℓ) ω : ℝ)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have h1 : blockSurvivorCount X ℓ t ω ≤ prunedColumnCount X (t * ℓ) ω := by
      rw [prunedColumnCount, prunedColumnCountBelow_eq_config]
      exact card_filter_blockReps_le_prunedColumnCountConfig (config X ω) ℓ t
    have h2 : Z ω ≤ (prunedColumnCount X (t * ℓ) ω : ℝ) := by
      simp only [hZ]
      exact_mod_cast h1
    linarith
  calc ENNReal.ofReal (p ^ 2 / (4 * K))
      ≤ ENNReal.ofReal (P {ω | p * μ ^ t / 2 ≤ Z ω}).toReal := ENNReal.ofReal_le_ofReal hpz
    _ = P {ω | p * μ ^ t / 2 ≤ Z ω} := ENNReal.ofReal_toReal (measure_ne_top _ _)
    _ ≤ _ := measure_mono hsub

end FractalGeometry.Probability.GridPercolation
