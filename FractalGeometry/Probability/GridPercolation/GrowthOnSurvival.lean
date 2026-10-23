import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.BlockIndependence
import FractalGeometry.Probability.GridPercolation.Configuration
import FractalGeometry.Probability.GridPercolation.ExplorationParameters
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.LawInvariance
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.Processes
import FractalGeometry.Probability.GridPercolation.RootIndependence
import FractalGeometry.Probability.GridPercolation.SurvivalGrowth
import FractalGeometry.Probability.GridPercolation.TreeExploration
import FractalGeometry.Probability.GridPercolation.TreeExplorationProbability
import FractalGeometry.Probability.GridPercolation.TreeHitsPositive
import FractalGeometry.Probability.GridPercolation.WordSplitting

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory ProbabilityTheory Filter Topology

open scoped ENNReal

variable {A : GridLaw} {Ω : Type*}

lemma card_retainedLevel (x : Configuration A) (k : ℕ) :
    (retainedLevel x k).card = descendantCountConfig x [] k := by
  classical
  unfold retainedLevel descendantCountConfig
  rw [Finset.card_image_of_injective _ (wordOfDigits_injective k)]
  congr 1
  ext u
  simp

lemma descendantCountBelow_le_nil_length_add
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) {ω : Ω} {w : Word A}
    (hw : RetainedBelow X ω [] w) (n : ℕ) :
    descendantCountBelow X w n ω ≤ descendantCountBelow X [] (w.length + n) ω := by
  classical
  have hinj : Function.Injective fun u : DigitWord A n => w ++ wordOfDigits u :=
    fun u v h => wordOfDigits_injective n (List.append_cancel_left h)
  rw [descendantCountBelow_eq_config, descendantCountBelow_eq_config]
  calc descendantCountConfig (config X ω) w n
      = ((Finset.univ.filter fun u : DigitWord A n =>
          retainedBelowConfig (config X ω) w (wordOfDigits u)).image
            fun u => w ++ wordOfDigits u).card := by
        rw [Finset.card_image_of_injective _ hinj]
        unfold descendantCountConfig
        congr 1
        ext u
        simp
    _ ≤ (retainedLevel (config X ω) (w.length + n)).card := by
        refine Finset.card_le_card fun v hv => ?_
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
        rw [Finset.mem_filter] at hu
        refine mem_retainedLevel.mpr ⟨by rw [List.length_append, length_wordOfDigits], ?_⟩
        change RetainedBelow X ω [] (w ++ wordOfDigits u)
        rw [retainedBelow_append_iff, List.nil_append]
        exact ⟨hw, hu.2⟩
    _ = descendantCountConfig (config X ω) [] (w.length + n) := card_retainedLevel _ _

variable [MeasurableSpace Ω] {P : Measure Ω} {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

theorem measure_card_ge_inter_forall_rebase_not_mem_le (hX : IsPercolation P X)
    {D : Set (Configuration A)} (hD : MeasurableSet D) (k B : ℕ) :
    P {ω | B ≤ descendantCountBelow X [] k ω ∧ ∀ w : Word A, w.length = k →
        RetainedBelow X ω [] w → rebase w (config X ω) ∉ D} ≤
      (1 - P {ω | config X ω ∈ D}) ^ B := by
  classical
  let := hX.toIsProbabilityMeasure
  set big := (Finset.univ : Finset (Finset (DigitWord A k))).filter fun S => B ≤ S.card with hbig
  have hsub : {ω | B ≤ descendantCountBelow X [] k ω ∧ ∀ w : Word A, w.length = k →
        RetainedBelow X ω [] w → rebase w (config X ω) ∉ D} ⊆
      ⋃ S ∈ big, ({ω | retainedDigitWords X k ω = S} ∩
        ⋂ u ∈ S, {ω | deepVector X (wordOfDigits u) ω ∈ Dᶜ}) := by
    rintro ω ⟨hB, hnot⟩
    refine Set.mem_iUnion₂.mpr ⟨retainedDigitWords X k ω, ?_, rfl, ?_⟩
    · simp only [hbig, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [card_retainedDigitWords]
      exact hB
    · simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_compl_iff]
      intro u hu
      rw [deepVector_eq_rebase]
      exact hnot _ (length_wordOfDigits u) (mem_retainedDigitWords.mp hu)
  have hPD : P {ω | config X ω ∈ Dᶜ} = 1 - P {ω | config X ω ∈ D} := by
    change P (config X ⁻¹' Dᶜ) = 1 - P (config X ⁻¹' D)
    rw [Set.preimage_compl, prob_compl_eq_one_sub (measurable_config hX hD)]
  calc P {ω | B ≤ descendantCountBelow X [] k ω ∧ ∀ w : Word A, w.length = k →
        RetainedBelow X ω [] w → rebase w (config X ω) ∉ D}
      ≤ P (⋃ S ∈ big, ({ω | retainedDigitWords X k ω = S} ∩
          ⋂ u ∈ S, {ω | deepVector X (wordOfDigits u) ω ∈ Dᶜ})) := measure_mono hsub
    _ ≤ ∑ S ∈ big, P ({ω | retainedDigitWords X k ω = S} ∩
          ⋂ u ∈ S, {ω | deepVector X (wordOfDigits u) ω ∈ Dᶜ}) := measure_biUnion_finset_le _ _
    _ = ∑ S ∈ big, P {ω | retainedDigitWords X k ω = S} * P {ω | config X ω ∈ Dᶜ} ^ S.card :=
        Finset.sum_congr rfl fun S _ => measure_retainedDigitWords_eq_inter_deep hX k S hD.compl
    _ ≤ ∑ S ∈ big, P {ω | retainedDigitWords X k ω = S} * (1 - P {ω | config X ω ∈ D}) ^ B := by
        refine Finset.sum_le_sum fun S hS => mul_le_mul_of_nonneg_left ?_ zero_le
        have hSB : B ≤ S.card := (Finset.mem_filter.mp hS).2
        rw [hPD]
        exact pow_le_pow_of_le_one zero_le tsub_le_self hSB
    _ = (∑ S ∈ big, P {ω | retainedDigitWords X k ω = S}) *
          (1 - P {ω | config X ω ∈ D}) ^ B :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * (1 - P {ω | config X ω ∈ D}) ^ B := by
        gcongr
        rw [← measure_biUnion_finset]
        · exact prob_le_one
        · intro S _ S' _ hSS'
          rw [Function.onFun, Set.disjoint_left]
          intro ω h h'
          exact hSS' (h.symm.trans h')
        · exact fun S _ => measurableSet_retainedDigitWords_eq hX k S
    _ = (1 - P {ω | config X ω ∈ D}) ^ B := one_mul _

theorem ae_survival_exists_retained_rebase_mem (hX : IsPercolation P X) (hm : 1 < A.m)
    {H : Set (Configuration A)} (hH : MeasurableSet H)
    (hpos : 0 < P {ω | config X ω ∈ H}) :
    ∀ᵐ ω ∂P, ω ∈ survival X → ∃ w : Word A, RetainedBelow X ω [] w ∧
      rebase w (config X ω) ∈ H := by
  classical
  let := hX.toIsProbabilityMeasure
  set α := P {ω | config X ω ∈ H} with hα
  set bad := {ω | ω ∈ survival X ∧ ∀ w : Word A, RetainedBelow X ω [] w →
      rebase w (config X ω) ∉ H} with hbad
  have hbound : ∀ B : ℕ, P bad ≤ (1 - α) ^ B := by
    intro B
    have hlim := (tendsto_measure_survival_inter_descendantCount_lt hX hm B).add
      (tendsto_const_nhds (x := (1 - α) ^ B))
    rw [zero_add] at hlim
    refine ge_of_tendsto' hlim fun k => ?_
    calc P bad
        ≤ P ((survival X ∩ {ω | descendantCountBelow X [] k ω < B}) ∪
            {ω | B ≤ descendantCountBelow X [] k ω ∧ ∀ w : Word A, w.length = k →
              RetainedBelow X ω [] w → rebase w (config X ω) ∉ H}) := by
          refine measure_mono fun ω hω => ?_
          obtain ⟨hs, hnot⟩ := hω
          rcases lt_or_ge (descendantCountBelow X [] k ω) B with hlt | hge
          · exact Or.inl ⟨hs, hlt⟩
          · exact Or.inr ⟨hge, fun w _ hw => hnot w hw⟩
      _ ≤ P (survival X ∩ {ω | descendantCountBelow X [] k ω < B}) +
            P {ω | B ≤ descendantCountBelow X [] k ω ∧ ∀ w : Word A, w.length = k →
              RetainedBelow X ω [] w → rebase w (config X ω) ∉ H} :=
          measure_union_le _ _
      _ ≤ P (survival X ∩ {ω | descendantCountBelow X [] k ω < B}) + (1 - α) ^ B := by
          gcongr
          exact measure_card_ge_inter_forall_rebase_not_mem_le hX hH k B
  have hzero : P bad = 0 := by
    have hlt : 1 - α < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hpos.ne'
    exact le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt) hbound)
      zero_le
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hzero
  simp only [Set.mem_ofPred_eq, Classical.not_imp, not_exists, not_and] at hω
  exact hω

lemma three_quarters_mul_pow_le_explorationThreshold_zero (hm : 1 < A.m) (k₀ j : ℕ) :
    3 / 4 * A.m ^ (k₀ + j) ≤ explorationThreshold A (fun _ => 0) k₀ j := by
  have hm0 : 0 < A.m := by linarith
  have hp0 : ∀ j, 0 < A.m ^ (k₀ + j) := fun j => pow_pos hm0 _
  have hsize : ∀ j, (explorationSize A (fun _ => 0) k₀ j : ℝ) = 0 := by
    intro j
    simp [explorationSize]
  have hμ0 : explorationThreshold A (fun _ => 0) k₀ 0 / A.m ^ (k₀ + 0) = 1 := by
    simp only [explorationThreshold, add_zero]
    exact div_self (pow_ne_zero _ hm0.ne')
  have hstep : ∀ j, explorationThreshold A (fun _ => 0) k₀ (j + 1) / A.m ^ (k₀ + (j + 1)) =
      (1 - explorationEta A j) * (explorationThreshold A (fun _ => 0) k₀ j / A.m ^ (k₀ + j) -
        (explorationSize A (fun _ => 0) k₀ j : ℝ) / A.m ^ (k₀ + j)) := by
    intro j
    have h1 := (hp0 j).ne'
    have h2 := hm0.ne'
    simp only [explorationThreshold]
    rw [← add_assoc, pow_succ]
    field_simp
  have hinv := threshold_invariant_aux (fun j => explorationEta_nonneg A hm j)
    (fun j => explorationEta_le_one A hm j)
    (a := fun j => (explorationSize A (fun _ => 0) k₀ j : ℝ) / A.m ^ (k₀ + j))
    (μ := fun j => explorationThreshold A (fun _ => 0) k₀ j / A.m ^ (k₀ + j))
    (fun j => div_nonneg (Nat.cast_nonneg _) (hp0 j).le) hμ0 hstep j
  have h2 := hinv.2
  simp only [hsize, zero_div, add_zero] at h2
  have h3 := sum_explorationEta_le A hm j
  have hμ : 3 / 4 ≤ explorationThreshold A (fun _ => 0) k₀ j / A.m ^ (k₀ + j) := by linarith
  rwa [le_div_iff₀ (hp0 j)] at hμ

theorem exists_pos_measure_forall_descendantCount_ge (hX : IsPercolation P X) (hm : 1 < A.m) :
    ∃ k₀ : ℕ, ∃ c > 0, 0 < P {ω | ∀ j : ℕ, c * A.m ^ (k₀ + j) ≤
      (descendantCountBelow X [] (k₀ + j) ω : ℝ)} := by
  classical
  let := hX.toIsProbabilityMeasure
  obtain ⟨k₀, hk₀⟩ := exists_explorationStart A hm
  obtain ⟨hη, hcM, hS⟩ := hk₀ (fun _ => 0) (fun _ => le_rfl) summable_zero (by simp)
  set Φ := {ω | ∀ q ∈ fullBranchingCoords A k₀, X q.1 q.2 ω = true} with hΦ
  have hΦpos : 0 < (P Φ).toReal :=
    ENNReal.toReal_pos (measure_fullBranching_pos hX k₀).ne' (measure_ne_top _ _)
  set c := explorationSize A (fun _ => 0) k₀ with hc
  set M := explorationThreshold A (fun _ => 0) k₀ with hM
  set good : ℕ → Set Ω := fun J => config X ⁻¹' exploreGood k₀ c M J with hgood
  have hgood_meas : ∀ J, MeasurableSet (good J) := fun J =>
    measurable_config hX (measurableSet_exploreGood k₀ c M J)
  have hgood_ge : ∀ J, ENNReal.ofReal ((P Φ).toReal / 2) ≤ P (good J) := by
    intro J
    have h1 := measure_exploreGood_ge hX hη hcM hS J
    have h2 := hS J
    rw [← ENNReal.ofReal_toReal (measure_ne_top P (good J))]
    refine ENNReal.ofReal_le_ofReal (le_trans ?_ h1)
    nlinarith
  have hgoodInf_ge : ENNReal.ofReal ((P Φ).toReal / 2) ≤ P (⋂ J, good J) := by
    have htend := tendsto_measure_iInter_atTop (μ := P)
      (fun J => (hgood_meas J).nullMeasurableSet)
      (fun J J' hJJ' => Set.preimage_mono (exploreGood_anti hJJ')) ⟨0, measure_ne_top _ _⟩
    exact ge_of_tendsto' htend fun J => hgood_ge J
  refine ⟨k₀, 3 / 4, by norm_num, lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity))
    (hgoodInf_ge.trans (measure_mono fun ω hω j => ?_))⟩
  have hωj : config X ω ∈ exploreGood k₀ c M j := Set.mem_iInter.mp hω j
  have hMj : M j ≤ (exploreG (config X ω) k₀ c j).card := hωj j le_rfl
  have hsub : exploreG (config X ω) k₀ c j ⊆ retainedLevel (config X ω) (k₀ + j) :=
    fun w hw => mem_retainedLevel.mpr (mem_exploreG hw)
  have hcard := Finset.card_le_card hsub
  rw [card_retainedLevel] at hcard
  calc 3 / 4 * A.m ^ (k₀ + j) ≤ M j := three_quarters_mul_pow_le_explorationThreshold_zero hm k₀ j
    _ ≤ (exploreG (config X ω) k₀ c j).card := hMj
    _ ≤ (descendantCountConfig (config X ω) [] (k₀ + j) : ℝ) := by exact_mod_cast hcard
    _ = (descendantCountBelow X [] (k₀ + j) ω : ℝ) := by rw [descendantCountBelow_eq_config]

theorem ae_exists_pos_eventually_descendantCount_ge (hX : IsPercolation P X) (hm : 1 < A.m) :
    ∀ᵐ ω ∂P, ω ∈ survival X → ∃ c > 0, ∀ᶠ n in atTop,
      c * A.m ^ n ≤ (descendantCountBelow X [] n ω : ℝ) := by
  obtain ⟨k₀, c, hc, hpos⟩ := exists_pos_measure_forall_descendantCount_ge hX hm
  set H : Set (Configuration A) :=
    {x | ∀ j : ℕ, c * A.m ^ (k₀ + j) ≤ (descendantCountConfig x [] (k₀ + j) : ℝ)} with hH
  have hHmeas : MeasurableSet H := by
    rw [hH, Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_le measurable_const
      (measurable_from_nat.comp (measurable_descendantCountConfig [] (k₀ + j)))
  have hHpos : 0 < P {ω | config X ω ∈ H} := hpos
  have hm0 : 0 < A.m := by linarith
  filter_upwards [ae_survival_exists_retained_rebase_mem hX hm hHmeas hHpos] with ω hω hs
  obtain ⟨w, hw, hwH⟩ := hω hs
  have hpw : A.m ^ w.length ≠ 0 := pow_ne_zero _ hm0.ne'
  refine ⟨c * (A.m ^ w.length)⁻¹, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (w.length + k₀)] with n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = w.length + (k₀ + j) := ⟨n - (w.length + k₀), by omega⟩
  have h1 := hwH j
  rw [descendantCountConfig_rebase, List.append_nil] at h1
  have h2 := descendantCountBelow_le_nil_length_add X hw (k₀ + j)
  calc c * (A.m ^ w.length)⁻¹ * A.m ^ (w.length + (k₀ + j)) = c * A.m ^ (k₀ + j) := by
        rw [pow_add]
        field_simp
    _ ≤ (descendantCountConfig (config X ω) w (k₀ + j) : ℝ) := h1
    _ = (descendantCountBelow X w (k₀ + j) ω : ℝ) := by rw [descendantCountBelow_eq_config]
    _ ≤ (descendantCountBelow X [] (w.length + (k₀ + j)) ω : ℝ) := by exact_mod_cast h2

end FractalGeometry.Probability.GridPercolation
