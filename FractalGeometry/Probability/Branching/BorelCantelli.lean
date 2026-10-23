import Mathlib
import FractalGeometry.Probability.Branching.Configuration
import FractalGeometry.Probability.Branching.Descendants
import FractalGeometry.Probability.Branching.GenerationIndependence
import FractalGeometry.Probability.Branching.IdenticalLaws
import FractalGeometry.Probability.Branching.Law
import FractalGeometry.Probability.Branching.PopulationGrowth
import FractalGeometry.Probability.Branching.Process
import FractalGeometry.Probability.Branching.Recurrence
import FractalGeometry.Probability.Branching.RetainedWords
import FractalGeometry.Probability.Branching.Statement
import FractalGeometry.Probability.Branching.TreeEvents
import FractalGeometry.Probability.Branching.Words

/-!
Amlan Banaji, Alex Rutar and Sascha Troscheit, "Interpolating with generalized
Assouad dimensions", Journal of Geometric Analysis 35 (2025), article 270.
DOI: 10.1007/s12220-025-02099-w, Lemma 1.6(ii).

This is the finite Bernoulli-child specialisation: each vertex has finitely many
labelled child positions, retained independently with the same position-specific
probabilities at every vertex. The mean offspring count exceeds one. For measurable
events determined by the retained subtree, summable nonnegative weights `K n` and
divergence of `∑ K n * P(E n) * m^n` imply infinitely many event-bearing vertices,
almost surely on survival. No geometric model is part of the statement.
-/

namespace FractalGeometry.Probability.Branching

open MeasureTheory ProbabilityTheory Filter Topology

open scoped ENNReal

variable {A : Law}

lemma rebase_rebase (w u : Word A)
    (x : Configuration A) :
    rebase u (rebase w x) =
      rebase (w ++ u) x := by
  funext q
  simp [rebase, List.append_assoc]

lemma treeHits_of_rebase {E : ℕ → Set (Configuration A)} {x : Configuration A}
    {k : ℕ} {w : Word A} (hwlen : w.length = k) (hw : retainedBelowConfig x [] w)
    (h : rebase w x ∈ treeHits (fun n => E (k + n))) : x ∈ treeHits E := by
  simp only [treeHits, Set.mem_ofPred_eq, Filter.frequently_atTop] at h ⊢
  intro N
  obtain ⟨n, hn, u, hulen, huret, huE⟩ := h N
  refine ⟨k + n, by omega, w ++ u, by simp [hwlen, hulen], ?_, ?_⟩
  · rw [RetainedTreeEq.retainedBelowConfig_append_iff]
    refine ⟨hw, ?_⟩
    have h' : ∀ l : Fin u.length, x (w ++ u.take l, u.get l) = true := huret
    intro l
    simpa using h' l
  · rwa [rebase_rebase] at huE

lemma measurableSet_treeHits {E : ℕ → Set (Configuration A)}
    (hE : ∀ n, MeasurableSet (E n)) : MeasurableSet (treeHits E) := by
  have hrebase : ∀ v : Word A, Measurable (rebase (A := A) v) :=
    fun v => Measurable.of_eval fun _ => measurable_pi_apply _
  have hset : treeHits E = ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n), ⋃ v : Word A,
      ({_x : Configuration A | v.length = n} ∩
        {x | retainedBelowConfig x [] v}) ∩ rebase v ⁻¹' E n := by
    ext x
    simp only [treeHits, Filter.frequently_atTop, Set.mem_ofPred_eq, Set.mem_iInter,
      Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, exists_prop, and_assoc]
  rw [hset]
  exact MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iUnion fun v => ((MeasurableSet.const _).inter
      (measurableSet_retainedBelowConfig [] v)).inter (hrebase v (hE n))

lemma exists_shift_weights {p K : ℕ → ℝ} (hK0 : ∀ n, 0 ≤ K n) (hKsum : Summable K)
    (hdiv : ¬ Summable (fun n => K n * p n * A.m ^ n)) (hm : 1 < A.m) (k : ℕ) :
    ∃ K' : ℕ → ℝ, (∀ n, 0 ≤ K' n) ∧ Summable K' ∧ ∑' n, K' n ≤ 1 / 4 ∧
      ¬ Summable (fun n => K' n * p (k + n) * A.m ^ n) := by
  have hm0 : 0 < A.m := by linarith
  have hshift_sum : Summable (fun n => K (k + n)) := by
    have := (summable_nat_add_iff k).mpr hKsum
    simpa [add_comm] using this
  have hdiv_shift : ¬ Summable (fun n => K (k + n) * p (k + n) * A.m ^ (k + n)) := by
    intro hs
    apply hdiv
    rw [← summable_nat_add_iff k]
    simpa [add_comm] using hs
  set T := ∑' n, K (k + n) with hT
  have hTpos : 0 < T := by
    by_contra hle
    push Not at hle
    have hzero : ∀ n, K (k + n) = 0 := fun n =>
      le_antisymm ((hshift_sum.le_tsum n fun i _ => hK0 _).trans hle) (hK0 _)
    exact hdiv_shift (by simp [hzero])
  refine ⟨fun n => K (k + n) / (4 * T), fun n => div_nonneg (hK0 _) (by linarith),
    hshift_sum.div_const _, ?_, ?_⟩
  · rw [tsum_div_const, ← hT]
    field_simp
    rfl
  · intro hs
    apply hdiv_shift
    have h := hs.mul_left (4 * T * A.m ^ k)
    refine h.congr fun n => ?_
    field_simp
    ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.arity) → Ω → Bool}

theorem measure_not_treeHits_inter_card_ge_le (hX : IsPercolation P X)
    {E : ℕ → Set (Configuration A)} (hE : ∀ n, MeasurableSet (E n)) {k : ℕ} {α : ℝ≥0∞}
    (hα : α ≤ P (config X ⁻¹' treeHits (fun n => E (k + n)))) (B : ℕ) :
    P ((config X ⁻¹' treeHits E)ᶜ ∩ {ω | B ≤ descendantCountBelow X [] k ω}) ≤ (1 - α) ^ B := by
  classical
  let := hX.toIsProbabilityMeasure
  set D := (treeHits (fun n => E (k + n)))ᶜ with hD
  have hDmeas : MeasurableSet D := (measurableSet_treeHits fun n => hE (k + n)).compl
  have hPD : P {ω | config X ω ∈ D} ≤ 1 - α := by
    change P (config X ⁻¹' D) ≤ 1 - α
    rw [hD, Set.preimage_compl, prob_compl_eq_one_sub
      (measurable_config hX (measurableSet_treeHits fun n => hE (k + n)))]
    exact tsub_le_tsub_left hα 1
  set big := (Finset.univ : Finset (Finset (DigitWord A k))).filter fun S => B ≤ S.card with hbig
  have hsub : (config X ⁻¹' treeHits E)ᶜ ∩ {ω | B ≤ descendantCountBelow X [] k ω} ⊆
      ⋃ S ∈ big, ({ω | retainedDigitWords X k ω = S} ∩
        ⋂ u ∈ S, {ω | deepVector X (wordOfDigits u) ω ∈ D}) := by
    rintro ω ⟨hnot, hB⟩
    refine Set.mem_iUnion₂.mpr ⟨retainedDigitWords X k ω, ?_, rfl, ?_⟩
    · simp only [hbig, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [card_retainedDigitWords]
      exact hB
    · simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      intro u hu hhit
      apply hnot
      have hret := (mem_retainedDigitWords.mp hu)
      exact treeHits_of_rebase (length_wordOfDigits u) hret (by
        rw [← deepVector_eq_rebase]
        exact hhit)
  calc P ((config X ⁻¹' treeHits E)ᶜ ∩ {ω | B ≤ descendantCountBelow X [] k ω})
      ≤ P (⋃ S ∈ big, ({ω | retainedDigitWords X k ω = S} ∩
          ⋂ u ∈ S, {ω | deepVector X (wordOfDigits u) ω ∈ D})) := measure_mono hsub
    _ ≤ ∑ S ∈ big, P ({ω | retainedDigitWords X k ω = S} ∩
          ⋂ u ∈ S, {ω | deepVector X (wordOfDigits u) ω ∈ D}) := measure_biUnion_finset_le _ _
    _ = ∑ S ∈ big, P {ω | retainedDigitWords X k ω = S} * P {ω | config X ω ∈ D} ^ S.card :=
        Finset.sum_congr rfl fun S _ => measure_retainedDigitWords_eq_inter_deep hX k S hDmeas
    _ ≤ ∑ S ∈ big, P {ω | retainedDigitWords X k ω = S} * (1 - α) ^ B := by
        refine Finset.sum_le_sum fun S hS => mul_le_mul_of_nonneg_left ?_ zero_le
        have hSB : B ≤ S.card := (Finset.mem_filter.mp hS).2
        calc P {ω | config X ω ∈ D} ^ S.card ≤ (1 - α) ^ S.card := pow_le_pow_left₀ zero_le hPD _
          _ ≤ (1 - α) ^ B := pow_le_pow_of_le_one zero_le tsub_le_self hSB
    _ = (∑ S ∈ big, P {ω | retainedDigitWords X k ω = S}) * (1 - α) ^ B :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * (1 - α) ^ B := by
        gcongr
        rw [← measure_biUnion_finset]
        · exact prob_le_one
        · intro S _ S' _ hSS'
          rw [Function.onFun, Set.disjoint_left]
          intro ω h h'
          exact hSS' (h.symm.trans h')
        · exact fun S _ => measurableSet_retainedDigitWords_eq hX k S
    _ = (1 - α) ^ B := one_mul _

theorem treeSecondBorelCantelli_of_isPercolation (hX : IsPercolation P X) (hm : 1 < A.m) :
    TreeSecondBorelCantelli P X := by
  classical
  let := hX.toIsProbabilityMeasure
  obtain ⟨α, hα0, hα⟩ := exists_measure_treeHits_ge hX hm
  intro E hE _ K hK0 hKsum hdiv
  have hshift : ∀ k, α ≤ P (config X ⁻¹' treeHits (fun n => E (k + n))) := by
    intro k
    obtain ⟨K', hK'0, hK'sum, hK'4, hK'div⟩ :=
      exists_shift_weights (p := fun n => (P (config X ⁻¹' E n)).toReal) hK0 hKsum hdiv hm k
    exact hα (fun n => E (k + n)) (fun n => hE _) K' hK'0 hK'sum hK'4 hK'div
  have hα1 : α ≤ 1 := (hshift 0).trans prob_le_one
  have hbound : ∀ B : ℕ, P (survival X ∩ (config X ⁻¹' treeHits E)ᶜ) ≤ (1 - α) ^ B := by
    intro B
    have hlim := (tendsto_measure_survival_inter_descendantCount_lt hX hm B).add
      (tendsto_const_nhds (x := (1 - α) ^ B))
    rw [zero_add] at hlim
    refine ge_of_tendsto' hlim fun k => ?_
    calc P (survival X ∩ (config X ⁻¹' treeHits E)ᶜ)
        ≤ P ((survival X ∩ {ω | descendantCountBelow X [] k ω < B}) ∪
            ((config X ⁻¹' treeHits E)ᶜ ∩ {ω | B ≤ descendantCountBelow X [] k ω})) := by
          refine measure_mono fun ω ⟨hs, hnot⟩ => ?_
          rcases lt_or_ge (descendantCountBelow X [] k ω) B with hlt | hge
          · exact Or.inl ⟨hs, hlt⟩
          · exact Or.inr ⟨hnot, hge⟩
      _ ≤ P (survival X ∩ {ω | descendantCountBelow X [] k ω < B}) +
            P ((config X ⁻¹' treeHits E)ᶜ ∩ {ω | B ≤ descendantCountBelow X [] k ω}) :=
          measure_union_le _ _
      _ ≤ P (survival X ∩ {ω | descendantCountBelow X [] k ω < B}) + (1 - α) ^ B := by
          gcongr
          exact measure_not_treeHits_inter_card_ge_le hX hE (hshift k) B
  have hzero : P (survival X ∩ (config X ⁻¹' treeHits E)ᶜ) = 0 := by
    have hlt : 1 - α < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hα0.ne'
    exact le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt) hbound)
      zero_le
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hzero
  simp only [Set.mem_ofPred_eq, Classical.not_imp] at hω
  obtain ⟨hs, hnot⟩ := hω
  refine ⟨hs, fun hH => hnot ?_⟩
  simp only [Set.mem_preimage, treeHits, Set.mem_ofPred_eq] at hH
  exact hH.mono fun n ⟨v, hv, hret, hvE⟩ =>
    ⟨v, hv, (retained_iff_retainedBelow_nil X ω v).mpr hret, hvE⟩

end FractalGeometry.Probability.Branching
