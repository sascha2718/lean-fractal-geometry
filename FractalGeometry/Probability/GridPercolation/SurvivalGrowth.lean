import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.BlockIndependence
import FractalGeometry.Probability.GridPercolation.ColumnOffspring
import FractalGeometry.Probability.GridPercolation.Configuration
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.LawInvariance
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.ProcessMeasurability
import FractalGeometry.Probability.GridPercolation.Processes
import FractalGeometry.Probability.GridPercolation.PrunedSurvival
import FractalGeometry.Probability.GridPercolation.RootIndependence
import FractalGeometry.Probability.GridPercolation.SecondMoments
import FractalGeometry.Probability.GridPercolation.ShallowEvents
import FractalGeometry.Probability.GridPercolation.SurvivalMeasurability
import FractalGeometry.Probability.GridPercolation.WordSplitting

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory ProbabilityTheory Filter Topology

open scoped ENNReal

variable {A : GridLaw} {Ω : Type*}

noncomputable def retainedDigitWords (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (k : ℕ)
    (ω : Ω) : Finset (DigitWord A k) := by
  classical
  exact {u : DigitWord A k | RetainedBelow X ω [] (wordOfDigits u)}.toFinset

lemma mem_retainedDigitWords {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool} {k : ℕ} {ω : Ω}
    {u : DigitWord A k} :
    u ∈ retainedDigitWords X k ω ↔ RetainedBelow X ω [] (wordOfDigits u) := by
  classical
  simp [retainedDigitWords]

lemma card_retainedDigitWords (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (k : ℕ) (ω : Ω) :
    (retainedDigitWords X k ω).card = descendantCountBelow X [] k ω := by
  classical
  unfold retainedDigitWords descendantCountBelow
  congr 1

lemma wordOfDigits_injective (k : ℕ) :
    Function.Injective (wordOfDigits (A := A) (L := k)) :=
  fun _ _ h => List.ofFn_injective h

variable [MeasurableSpace Ω] {P : Measure Ω} {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

lemma measurableSet_retainedDigitWords_eq (hX : IsPercolation P X) (k : ℕ)
    (S : Finset (DigitWord A k)) : MeasurableSet {ω | retainedDigitWords X k ω = S} := by
  classical
  have hset : {ω | retainedDigitWords X k ω = S} =
      ⋂ u : DigitWord A k, {ω | RetainedBelow X ω [] (wordOfDigits u) ↔ u ∈ S} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · rintro h u
      rw [← h, mem_retainedDigitWords]
    · intro h
      ext u
      rw [mem_retainedDigitWords]
      exact h u
  rw [hset]
  refine MeasurableSet.iInter fun u => ?_
  by_cases hu : u ∈ S
  · simp only [hu, iff_true]
    exact measurableSet_retainedBelow hX [] _
  · simp only [hu, iff_false]
    exact (measurableSet_retainedBelow hX [] _).compl

theorem measure_retainedDigitWords_eq_inter_deep (hX : IsPercolation P X) (k : ℕ)
    (S : Finset (DigitWord A k)) {D : Set (Configuration A)} (hD : MeasurableSet D) :
    P ({ω | retainedDigitWords X k ω = S} ∩ ⋂ u ∈ S, {ω | deepVector X (wordOfDigits u) ω ∈ D}) =
      P {ω | retainedDigitWords X k ω = S} * P {ω | config X ω ∈ D} ^ S.card := by
  classical
  set C : Set (Configuration A) :=
    {x | ∀ u : DigitWord A k, retainedBelowConfig x [] (wordOfDigits u) ↔ u ∈ S} with hC
  have hCmeas : MeasurableSet C := by
    have hset : C = ⋂ u : DigitWord A k,
        {x : Configuration A | retainedBelowConfig x [] (wordOfDigits u) ↔ u ∈ S} := by
      ext x
      simp [hC]
    rw [hset]
    refine MeasurableSet.iInter fun u => ?_
    by_cases hu : u ∈ S
    · simp only [hu, iff_true]
      exact measurableSet_retainedBelowConfig [] _
    · simp only [hu, iff_false]
      exact (measurableSet_retainedBelowConfig [] _).compl
  have hshallow : {ω | shallowVector X k ω ∈ shallowExtend k ⁻¹' C} =
      {ω | retainedDigitWords X k ω = S} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hC]
    constructor
    · intro h
      ext u
      rw [mem_retainedDigitWords, ← h u]
      exact (retainedBelowConfig_shallow_iff X k ω (by simp)).symm
    · intro h u
      rw [← h, mem_retainedDigitWords]
      exact retainedBelowConfig_shallow_iff X k ω (by simp)
  have h := measure_shallow_inter_biInter hX (wordOfDigits (A := A) (L := k)) (c := k)
    (fun u => length_wordOfDigits u) (wordOfDigits_injective k)
    ((measurable_shallowExtend k) hCmeas) (S := fun _ => D) (fun _ => hD) S
  rw [hshallow] at h
  rw [h]
  congr 1
  have hdeep : ∀ u : DigitWord A k,
      P {ω | deepVector X (wordOfDigits u) ω ∈ D} = P {ω | config X ω ∈ D} := by
    intro u
    have h1 := hX.measure_config_functional_shift (wordOfDigits u) (G := id) measurable_id hD
    simpa only [id, deepVector_eq_rebase] using h1
  rw [Finset.prod_congr rfl (fun u _ => hdeep u), Finset.prod_const]

omit [MeasurableSpace Ω] in

lemma not_mem_survival_of_forall_not_hasInfiniteDescent {ω : Ω} {k : ℕ}
    (h : ∀ u : DigitWord A k, RetainedBelow X ω [] (wordOfDigits u) →
      ¬ HasInfiniteDescentBelow X ω (wordOfDigits u)) : ω ∉ survival X := by
  intro hs
  obtain ⟨w, hwk, hret, hdesc⟩ := exists_retained_hasInfiniteDescent_of_mem_survival hs k
  set u : DigitWord A k := fun l => w.get (Fin.cast hwk.symm l) with hu
  have hw : wordOfDigits u = w := by
    apply List.ext_getElem
    · simp [hwk]
    · intro i h1 h2
      simp [wordOfDigits, hu]
  refine h u ?_ ?_
  · rw [hw, retainedBelow_nil_iff_retained]
    exact hret
  · rw [hw]
    exact hdesc

def extinctConfig (A : GridLaw) : Set (Configuration A) :=
  {x | ¬ ∀ L : ℕ, ∃ u : DigitWord A L, retainedBelowConfig x [] (wordOfDigits u)}

lemma measurableSet_extinctConfig : MeasurableSet (extinctConfig A) := by
  have hset : extinctConfig A =
      (⋂ L : ℕ, ⋃ u : DigitWord A L,
        {x : Configuration A | retainedBelowConfig x [] (wordOfDigits u)})ᶜ := by
    ext x
    simp [extinctConfig]
  rw [hset]
  exact (MeasurableSet.iInter fun L => MeasurableSet.iUnion fun u =>
    measurableSet_retainedBelowConfig [] _).compl

omit [MeasurableSpace Ω] in

lemma deepVector_mem_extinctConfig_iff (root : Word A) (ω : Ω) :
    deepVector X root ω ∈ extinctConfig A ↔ ¬ HasInfiniteDescentBelow X ω root :=
  Iff.rfl

lemma measure_config_mem_extinctConfig :
    P {ω | config X ω ∈ extinctConfig A} = P (survival X)ᶜ := by
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
  rw [← hasInfiniteDescentBelow_nil_iff_mem_survival]
  exact Iff.rfl

lemma pow_mul_measure_card_lt_le (hX : IsPercolation P X) (k B : ℕ) :
    P (survival X)ᶜ ^ B * P {ω | 1 ≤ descendantCountBelow X [] k ω ∧
        descendantCountBelow X [] k ω < B} ≤
      P ((survival X)ᶜ ∩ {ω | 0 < descendantCountBelow X [] k ω}) := by
  classical
  let := hX.toIsProbabilityMeasure
  set T : Finset (Finset (DigitWord A k)) :=
    (Finset.univ : Finset (Finset (DigitWord A k))).filter
      (fun S => 1 ≤ S.card ∧ S.card < B) with hT
  have hunion : {ω | 1 ≤ descendantCountBelow X [] k ω ∧ descendantCountBelow X [] k ω < B} =
      ⋃ S ∈ T, {ω | retainedDigitWords X k ω = S} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, hT, Finset.mem_filter, Finset.mem_univ,
      true_and, exists_prop]
    constructor
    · intro h
      refine ⟨retainedDigitWords X k ω, ?_, rfl⟩
      rw [card_retainedDigitWords]
      exact h
    · rintro ⟨S, hS, hSeq⟩
      rw [← card_retainedDigitWords, hSeq]
      exact hS
  have hdisj : (T : Set (Finset (DigitWord A k))).PairwiseDisjoint
      (fun S => {ω | retainedDigitWords X k ω = S}) := by
    intro S _ S' _ hSS'
    refine Set.disjoint_left.mpr fun ω h h' => hSS' ?_
    simp only [Set.mem_ofPred_eq] at h h'
    rw [← h, ← h']
  have hdisj' : (T : Set (Finset (DigitWord A k))).PairwiseDisjoint
      (fun S => (survival X)ᶜ ∩ {ω | retainedDigitWords X k ω = S}) := by
    intro S hS S' hS' hSS'
    exact (hdisj hS hS' hSS').mono Set.inter_subset_right Set.inter_subset_right
  have hmeas : ∀ S ∈ T, MeasurableSet {ω | retainedDigitWords X k ω = S} :=
    fun S _ => measurableSet_retainedDigitWords_eq hX k S
  have hq1 : P (survival X)ᶜ ≤ 1 := prob_le_one
  have hterm : ∀ S ∈ T, P (survival X)ᶜ ^ B * P {ω | retainedDigitWords X k ω = S} ≤
      P ((survival X)ᶜ ∩ {ω | retainedDigitWords X k ω = S}) := by
    intro S hS
    have hSB : S.card ≤ B := (Finset.mem_filter.mp hS).2.2.le
    have hprod := measure_retainedDigitWords_eq_inter_deep hX k S measurableSet_extinctConfig
    rw [measure_config_mem_extinctConfig] at hprod
    calc P (survival X)ᶜ ^ B * P {ω | retainedDigitWords X k ω = S}
        ≤ P (survival X)ᶜ ^ S.card * P {ω | retainedDigitWords X k ω = S} := by
          exact mul_le_mul_of_nonneg_right (pow_le_pow_right_of_le_one' hq1 hSB) zero_le
      _ = P ({ω | retainedDigitWords X k ω = S} ∩
            ⋂ u ∈ S, {ω | deepVector X (wordOfDigits u) ω ∈ extinctConfig A}) := by
          rw [hprod, mul_comm]
      _ ≤ P ((survival X)ᶜ ∩ {ω | retainedDigitWords X k ω = S}) := by
          apply measure_mono
          rintro ω ⟨hSω, hdeep⟩
          refine ⟨?_, hSω⟩
          simp only [Set.mem_ofPred_eq] at hSω
          simp only [Set.mem_iInter] at hdeep
          refine not_mem_survival_of_forall_not_hasInfiniteDescent (k := k) fun u hu => ?_
          have huS : u ∈ S := by
            rw [← hSω, mem_retainedDigitWords]
            exact hu
          exact (deepVector_mem_extinctConfig_iff _ ω).mp (hdeep u huS)
  calc P (survival X)ᶜ ^ B * P {ω | 1 ≤ descendantCountBelow X [] k ω ∧
          descendantCountBelow X [] k ω < B}
      = ∑ S ∈ T, P (survival X)ᶜ ^ B * P {ω | retainedDigitWords X k ω = S} := by
        rw [hunion, measure_biUnion_finset hdisj hmeas, Finset.mul_sum]
    _ ≤ ∑ S ∈ T, P ((survival X)ᶜ ∩ {ω | retainedDigitWords X k ω = S}) :=
        Finset.sum_le_sum hterm
    _ = P (⋃ S ∈ T, (survival X)ᶜ ∩ {ω | retainedDigitWords X k ω = S}) :=
        (measure_biUnion_finset hdisj' fun S hS =>
          (measurableSet_survival hX).compl.inter (hmeas S hS)).symm
    _ ≤ P ((survival X)ᶜ ∩ {ω | 0 < descendantCountBelow X [] k ω}) := by
        apply measure_mono
        intro ω hω
        simp only [Set.mem_iUnion, exists_prop] at hω
        obtain ⟨S, hS, hext, hSω⟩ := hω
        refine ⟨hext, ?_⟩
        simp only [Set.mem_ofPred_eq] at hSω ⊢
        rw [← card_retainedDigitWords, hSω]
        exact (Finset.mem_filter.mp hS).2.1

lemma tendsto_measure_compl_survival_inter_pos (hX : IsPercolation P X) :
    Tendsto (fun k : ℕ => P ((survival X)ᶜ ∩ {ω | 0 < descendantCountBelow X [] k ω}))
      atTop (𝓝 0) := by
  let := hX.toIsProbabilityMeasure
  set s : ℕ → Set Ω := fun k => (survival X)ᶜ ∩ {ω | 0 < descendantCountBelow X [] k ω} with hs
  have hanti : Antitone s := by
    intro j k hjk ω hω
    exact ⟨hω.1, descendantCountBelow_nil_pos_mono X hjk ω hω.2⟩
  have hmeas : ∀ k, NullMeasurableSet (s k) P := fun k =>
    ((measurableSet_survival hX).compl.inter
      (measurableSet_descendantCountBelow_nil_pos hX k)).nullMeasurableSet
  have h := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top P _⟩
  have hempty : ⋂ k, s k = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
    by_contra hcon
    push Not at hcon
    have hsurv : ω ∈ survival X := by
      rw [survival_eq_iInter_descendantCountBelow_nil_pos X]
      exact Set.mem_iInter.mpr fun k => (hcon k).2
    exact (hcon 0).1 hsurv
  rw [hempty, measure_empty] at h
  exact h

lemma exists_prob_eq_one_of_measure_compl_survival_eq_zero (hX : IsPercolation P X)
    (hq : P (survival X)ᶜ = 0) : ∃ a : Fin A.M × Fin A.N, A.p a.1 a.2 = 1 := by
  classical
  let := hX.toIsProbabilityMeasure
  by_contra hcon
  push Not at hcon
  set S : Finset (Word A × (Fin A.M × Fin A.N)) :=
    (Finset.univ : Finset (Fin A.M × Fin A.N)).image (fun a => (([] : Word A), a)) with hS
  have hprod := hX.indep.meas_biInter (S := S) (s := fun q => {ω | X q.1 q.2 ω = false})
    fun q _ => MeasurableSpace.measurableSet_comap.mpr ⟨{false}, measurableSet_singleton false, rfl⟩
  have hfalse : ∀ q : Word A × (Fin A.M × Fin A.N),
      P {ω | X q.1 q.2 ω = false} = 1 - ENNReal.ofReal (A.p q.2.1 q.2.2) := by
    intro q
    have hset : {ω | X q.1 q.2 ω = false} = {ω | X q.1 q.2 ω = true}ᶜ := by
      ext ω
      simp
    rw [hset, prob_compl_eq_one_sub (measurableSet_eq_fun (hX.measurable _ _) measurable_const),
      hX.prob]
  have hpos : P (⋂ q ∈ S, {ω | X q.1 q.2 ω = false}) ≠ 0 := by
    rw [hprod, Finset.prod_ne_zero_iff]
    intro q hq'
    rw [hfalse]
    have hlt : A.p q.2.1 q.2.2 < 1 := lt_of_le_of_ne (A.p_le_one _ _) (hcon q.2)
    exact (tsub_pos_of_lt (ENNReal.ofReal_lt_one.mpr hlt)).ne'
  have hsub : (⋂ q ∈ S, {ω | X q.1 q.2 ω = false}) ⊆ (survival X)ᶜ := by
    intro ω hω hs
    obtain ⟨w, hw1, hret⟩ := hs 1
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hw1
    have h1 := hret ⟨0, by simp⟩
    simp only [Set.mem_iInter] at hω
    have h2 := hω ([], a) (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
    simp only [Set.mem_ofPred_eq] at h2
    simp [h2] at h1
  exact hpos (le_antisymm ((measure_mono hsub).trans hq.le) (zero_le))

lemma exists_ne_prob_pos_of_prob_eq_one (hm : 1 < A.m) {a₀ : Fin A.M × Fin A.N}
    (ha₀ : A.p a₀.1 a₀.2 = 1) : ∃ b : Fin A.M × Fin A.N, b ≠ a₀ ∧ 0 < A.p b.1 b.2 := by
  classical
  by_contra hcon
  push Not at hcon
  have hsum : A.m = ∑ b : Fin A.M × Fin A.N, A.p b.1 b.2 := by
    simp only [GridLaw.m, GridLaw.E]
    exact (Fintype.sum_prod_type' (fun i j => A.p i j)).symm
  have hsingle : ∑ b : Fin A.M × Fin A.N, A.p b.1 b.2 = A.p a₀.1 a₀.2 :=
    Finset.sum_eq_single a₀ (fun b _ hb => le_antisymm (hcon b hb) (A.p_nonneg _ _))
      (fun h => absurd (Finset.mem_univ a₀) h)
  rw [hsum, hsingle, ha₀] at hm
  exact lt_irrefl _ hm

omit [MeasurableSpace Ω] in

lemma card_branchings_le_descendantCount {a₀ b : Fin A.M × Fin A.N} (hba : b ≠ a₀) {ω : Ω}
    (hall : ∀ w : Word A, X w a₀ ω = true) (k : ℕ) :
    ((Finset.range k).filter (fun j => X (List.replicate j a₀) b ω = true)).card ≤
      descendantCountBelow X [] k ω := by
  classical
  set u : ℕ → DigitWord A k := fun j l => if (l : ℕ) = j then b else a₀ with hu
  rw [← card_retainedDigitWords]
  refine Finset.card_le_card_of_injOn u ?_ ?_
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hj
    obtain ⟨hjk, hX⟩ := hj
    rw [Finset.mem_coe, mem_retainedDigitWords]
    intro l
    simp only [List.nil_append]
    have hlk : (l : ℕ) < k := by
      have := l.isLt
      simpa [wordOfDigits] using this
    have hget : (wordOfDigits (u j)).get l = u j ⟨l, hlk⟩ := by
      rw [List.get_eq_getElem]
      simp [wordOfDigits]
    rw [hget]
    by_cases hlj : (l : ℕ) = j
    · have htake : (wordOfDigits (u j)).take l = List.replicate j a₀ := by
        apply List.ext_getElem
        · simp [wordOfDigits, hlj, hjk.le]
        · intro i h1 h2
          have hi : i < j := by simpa using h2
          simp [wordOfDigits, hu, show i ≠ j from hi.ne]
      rw [htake]
      simp only [hu, hlj, ite_true]
      exact hX
    · simp only [hu, hlj, ite_false]
      exact hall _
  · intro j hj j' hj' hjj'
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hj hj'
    by_contra hne
    have h := congrFun hjj' ⟨j, hj.1⟩
    simp only [hu, ite_true, show j ≠ j' from hne, ite_false] at h
    exact hba h

lemma measure_card_branchings_lt_le (hX : IsPercolation P X) {a₀ b : Fin A.M × Fin A.N}
    (B L : ℕ) :
    P {ω | ((Finset.range (B * L)).filter
        (fun j => X (List.replicate j a₀) b ω = true)).card < B} ≤
      B * (1 - ENNReal.ofReal (A.p b.1 b.2)) ^ L := by
  classical
  let := hX.toIsProbabilityMeasure
  have hsub : {ω | ((Finset.range (B * L)).filter
        (fun j => X (List.replicate j a₀) b ω = true)).card < B} ⊆
      ⋃ i ∈ Finset.range B, ⋂ j ∈ Finset.Ico (i * L) (i * L + L),
        {ω | X (List.replicate j a₀) b ω = false} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_iInter, Set.mem_ofPred_eq, exists_prop, not_exists,
      not_and, not_forall, Bool.not_eq_false] at hcon
    choose! g hg using hcon
    have hmaps : ∀ i ∈ Finset.range B, g i ∈ (Finset.range (B * L)).filter
        (fun j => X (List.replicate j a₀) b ω = true) := by
      intro i hi
      obtain ⟨hgI, hgX⟩ := hg i hi
      have hiB : i + 1 ≤ B := Finset.mem_range.mp hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hgX⟩
      have h1 := (Finset.mem_Ico.mp hgI).2
      calc g i < i * L + L := h1
        _ = (i + 1) * L := by ring
        _ ≤ B * L := Nat.mul_le_mul_right L hiB
    have hinj : Set.InjOn g (Finset.range B) := by
      intro i hi i' hi' hii'
      have h1 := Finset.mem_Ico.mp (hg i hi).1
      have h2 := Finset.mem_Ico.mp (hg i' hi').1
      have e1 : g i / L = i := Nat.div_eq_of_lt_le (by linarith [h1.1]) (by linarith [h1.2])
      have e2 : g i' / L = i' := Nat.div_eq_of_lt_le (by linarith [h2.1]) (by linarith [h2.2])
      rw [← e1, ← e2, hii']
    have hcard := Finset.card_le_card_of_injOn g hmaps hinj
    rw [Finset.card_range] at hcard
    omega
  have hfalse : ∀ j : ℕ, P {ω | X (List.replicate j a₀) b ω = false} =
      1 - ENNReal.ofReal (A.p b.1 b.2) := by
    intro j
    have hset : {ω | X (List.replicate j a₀) b ω = false} =
        {ω | X (List.replicate j a₀) b ω = true}ᶜ := by
      ext ω
      simp
    rw [hset, prob_compl_eq_one_sub (measurableSet_eq_fun (hX.measurable _ _) measurable_const),
      hX.prob]
  have hblock : ∀ i : ℕ, P (⋂ j ∈ Finset.Ico (i * L) (i * L + L),
      {ω | X (List.replicate j a₀) b ω = false}) = (1 - ENNReal.ofReal (A.p b.1 b.2)) ^ L := by
    intro i
    have hinjrep : Set.InjOn (fun j : ℕ => (List.replicate j a₀, b))
        (Finset.Ico (i * L) (i * L + L) : Set ℕ) := by
      intro j _ j' _ h
      have h1 := congrArg (fun q : Word A × (Fin A.M × Fin A.N) => q.1.length) h
      simpa using h1
    have h := hX.indep.meas_biInter
      (S := (Finset.Ico (i * L) (i * L + L)).image (fun j => (List.replicate j a₀, b)))
      (s := fun q => {ω | X q.1 q.2 ω = false})
      fun q _ => MeasurableSpace.measurableSet_comap.mpr
        ⟨{false}, measurableSet_singleton false, rfl⟩
    rw [Finset.set_biInter_finset_image, Finset.prod_image hinjrep] at h
    rw [h, Finset.prod_congr rfl (fun j _ => hfalse j), Finset.prod_const, Nat.card_Ico,
      Nat.add_sub_cancel_left]
  calc P {ω | ((Finset.range (B * L)).filter
          (fun j => X (List.replicate j a₀) b ω = true)).card < B}
      ≤ P (⋃ i ∈ Finset.range B, ⋂ j ∈ Finset.Ico (i * L) (i * L + L),
          {ω | X (List.replicate j a₀) b ω = false}) := measure_mono hsub
    _ ≤ ∑ i ∈ Finset.range B, P (⋂ j ∈ Finset.Ico (i * L) (i * L + L),
          {ω | X (List.replicate j a₀) b ω = false}) := measure_biUnion_finset_le _ _
    _ = B * (1 - ENNReal.ofReal (A.p b.1 b.2)) ^ L := by
        rw [Finset.sum_congr rfl (fun i _ => hblock i), Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]

lemma tendsto_measure_descendantCount_lt_of_prob_eq_one (hX : IsPercolation P X)
    {a₀ b : Fin A.M × Fin A.N} (ha₀ : A.p a₀.1 a₀.2 = 1) (hba : b ≠ a₀)
    (hb : 0 < A.p b.1 b.2) (B : ℕ) :
    Tendsto (fun k : ℕ => P {ω | descendantCountBelow X [] k ω < B}) atTop (𝓝 0) := by
  classical
  let := hX.toIsProbabilityMeasure
  set bad : Set Ω := ⋃ w : Word A, {ω | X w a₀ ω = false} with hbad
  have hbad0 : P bad = 0 := by
    refine measure_iUnion_null fun w => ?_
    have hset : {ω | X w a₀ ω = false} = {ω | X w a₀ ω = true}ᶜ := by
      ext ω
      simp
    rw [hset, prob_compl_eq_one_sub (measurableSet_eq_fun (hX.measurable _ _) measurable_const),
      hX.prob, ha₀, ENNReal.ofReal_one, tsub_self]
  have hlt : 1 - ENNReal.ofReal (A.p b.1 b.2) < 1 :=
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (ENNReal.ofReal_pos.mpr hb).ne'
  have hg : Tendsto (fun L : ℕ => (B : ℝ≥0∞) * (1 - ENNReal.ofReal (A.p b.1 b.2)) ^ L)
      atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt)
      (Or.inr (ENNReal.natCast_ne_top B))
    rwa [mul_zero] at h
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  obtain ⟨L, hL⟩ := ENNReal.tendsto_atTop_zero.mp hg ε hε
  refine ⟨B * L, fun k hk => ?_⟩
  have hsub : {ω | descendantCountBelow X [] k ω < B} ⊆ bad ∪
      {ω | ((Finset.range (B * L)).filter
        (fun j => X (List.replicate j a₀) b ω = true)).card < B} := by
    intro ω hω
    by_cases hω' : ω ∈ bad
    · exact Or.inl hω'
    · right
      have hall : ∀ w : Word A, X w a₀ ω = true := by
        intro w
        by_contra hw
        exact hω' (Set.mem_iUnion.mpr ⟨w, by simpa using hw⟩)
      simp only [Set.mem_ofPred_eq] at hω ⊢
      calc ((Finset.range (B * L)).filter
            (fun j => X (List.replicate j a₀) b ω = true)).card
          ≤ ((Finset.range k).filter (fun j => X (List.replicate j a₀) b ω = true)).card :=
            Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr hk))
        _ ≤ descendantCountBelow X [] k ω := card_branchings_le_descendantCount hba hall k
        _ < B := hω
  calc P {ω | descendantCountBelow X [] k ω < B}
      ≤ P (bad ∪ {ω | ((Finset.range (B * L)).filter
          (fun j => X (List.replicate j a₀) b ω = true)).card < B}) := measure_mono hsub
    _ ≤ P bad + P {ω | ((Finset.range (B * L)).filter
          (fun j => X (List.replicate j a₀) b ω = true)).card < B} := measure_union_le _ _
    _ ≤ 0 + (B : ℝ≥0∞) * (1 - ENNReal.ofReal (A.p b.1 b.2)) ^ L := by
        rw [hbad0]
        gcongr
        exact measure_card_branchings_lt_le hX B L
    _ ≤ ε := by
        rw [zero_add]
        exact hL L le_rfl

theorem tendsto_measure_survival_inter_descendantCount_lt (hX : IsPercolation P X)
    (hm : 1 < A.m) (B : ℕ) :
    Tendsto (fun k : ℕ => P (survival X ∩ {ω | descendantCountBelow X [] k ω < B})) atTop
      (𝓝 0) := by
  let := hX.toIsProbabilityMeasure
  by_cases hq : P (survival X)ᶜ = 0
  · obtain ⟨a₀, ha₀⟩ := exists_prob_eq_one_of_measure_compl_survival_eq_zero hX hq
    obtain ⟨b, hba, hb⟩ := exists_ne_prob_pos_of_prob_eq_one hm ha₀
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_measure_descendantCount_lt_of_prob_eq_one hX ha₀ hba hb B)
      (fun k => zero_le) (fun k => measure_mono Set.inter_subset_right)
  · have hqB : P (survival X)ᶜ ^ B ≠ 0 := pow_ne_zero _ hq
    have hlim := ENNReal.Tendsto.div_const (tendsto_measure_compl_survival_inter_pos hX)
      (b := P (survival X)ᶜ ^ B) (Or.inr hqB)
    rw [ENNReal.zero_div] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun k => zero_le) (fun k => ?_)
    have hle : P (survival X ∩ {ω | descendantCountBelow X [] k ω < B}) ≤
        P {ω | 1 ≤ descendantCountBelow X [] k ω ∧ descendantCountBelow X [] k ω < B} := by
      apply measure_mono
      rintro ω ⟨hs, hlt⟩
      exact ⟨one_le_descendantCountBelow_of_mem_survival hs k, hlt⟩
    refine hle.trans ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl hqB) (Or.inl (ENNReal.pow_ne_top (measure_ne_top _ _))),
      mul_comm]
    exact pow_mul_measure_card_lt_le hX k B

end FractalGeometry.Probability.GridPercolation
