import Mathlib
import FractalGeometry.Probability.Patterns.Defs
import FractalGeometry.Probability.Patterns.WaitingTime
import FractalGeometry.Probability.Patterns.Weights
import FractalGeometry.Probability.Patterns.WordProbability

/-!
Finite pattern waiting times for an i.i.d. process on a finite alphabet with
strictly positive symbol probabilities. All competing patterns have the same
positive length. `li_identity` relates the expected first hitting time to the
winning-pattern probabilities and suffix/prefix correlations; `sum_hitProb`
proves that the winning probabilities sum to one.

Literature: Shuo-Yen Robert Li, "A Martingale Approach to the Study of Occurrence
of Sequence Patterns in Repeated Experiments", Annals of Probability 8(6)
(1980), 1171–1176. DOI: 10.1214/aop/1176994578. This module supplies a direct
proof of the equal-length correlation identity, rather than asserting coverage
of every pattern or stopping-time result in the paper.
-/

namespace FractalGeometry.Probability.Patterns

open MeasureTheory ProbabilityTheory Finset Filter Topology

open scoped ENNReal

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace Ω]

section Words

variable (p : Weights ι) {m : ℕ}

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Ω]

noncomputable def Weights.suffixProb (z : Word ι m) (h : ℕ) : ℝ := by
  classical exact ∏ i ∈ univ.filter (fun i : Fin m => m - h ≤ (i : ℕ)), p.p (z i)

noncomputable def Weights.wcorr (u z : Word ι m) : ℝ := by
  classical exact ∑ h ∈ range m, if Overlap u z h then p.suffixProb z h else 0

theorem Weights.suffixProb_pos (z : Word ι m) (h : ℕ) : 0 < p.suffixProb z h := by
  unfold Weights.suffixProb
  exact prod_pos fun i _ => p.pos _

theorem Weights.prefixProb_pos (z : Word ι m) (k : ℕ) : 0 < p.prefixProb z k := by
  unfold Weights.prefixProb
  exact prod_pos fun i _ => p.pos _

theorem Weights.prefixProb_mul_suffixProb (z : Word ι m) {i : ℕ} (hi : i ≤ m) :
    p.prefixProb z i * p.suffixProb z (m - i) = p.wordProb z := by
  classical
  unfold Weights.prefixProb Weights.suffixProb Weights.wordProb
  rw [show m - (m - i) = i by omega]
  rw [← prod_filter_mul_prod_filter_not univ (fun j : Fin m => (j : ℕ) < i)]
  congr 1
  refine prod_congr ?_ fun _ _ => rfl
  ext j
  simp only [mem_filter, mem_univ, true_and, not_lt]

theorem Weights.suffixProb_succ (z : Word ι m) {i : ℕ} (hi : i < m) :
    p.suffixProb z (m - i) = p.p (z ⟨i, hi⟩) * p.suffixProb z (m - (i + 1)) := by
  classical
  unfold Weights.suffixProb
  have hset : univ.filter (fun j : Fin m => m - (m - i) ≤ (j : ℕ))
      = insert ⟨i, hi⟩ (univ.filter (fun j : Fin m => m - (m - (i + 1)) ≤ (j : ℕ))) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
    omega
  rw [hset, prod_insert (by simp only [mem_filter, mem_univ, true_and]; all_goals omega)]

theorem Weights.suffixProb_eq_wordProb (z : Word ι m) : p.suffixProb z m = p.wordProb z := by
  have := p.prefixProb_mul_suffixProb z (i := 0) (Nat.zero_le m)
  rw [Nat.sub_zero] at this
  rw [← this]
  unfold Weights.prefixProb
  rw [prod_eq_one (fun i hi => by simp at hi), one_mul]

theorem Weights.wcorr_eq (u z : Word ι m) : p.wcorr u z = p.wordProb z * p.corr u z := by
  classical
  unfold Weights.wcorr Weights.corr
  rw [mul_sum]
  refine sum_congr rfl fun h hh => ?_
  rw [mem_range] at hh
  split_ifs
  · rw [← p.prefixProb_mul_suffixProb z (i := m - h) (by omega), show m - (m - h) = h by omega,
      mul_comm, ← mul_assoc, inv_mul_cancel₀ (p.prefixProb_pos z _).ne', one_mul]
  · exact (mul_zero _).symm

theorem Weights.patternMass_pos {U : Finset (Word ι m)} (hU : U.Nonempty) :
    0 < p.patternMass U :=
  sum_pos (fun z _ => p.wordProb_pos z) hU

theorem Weights.patternMass_le_one (U : Finset (Word ι m)) : p.patternMass U ≤ 1 := by
  unfold Weights.patternMass
  calc ∑ z ∈ U, p.wordProb z ≤ ∑ z, p.wordProb z :=
        sum_le_sum_of_subset_of_nonneg (subset_univ U) fun z _ _ => (p.wordProb_pos z).le
    _ = 1 := p.sum_wordProb m

end Words

def PrefixMatch (I : ℕ → Ω → ι) (s i : ℕ) {m : ℕ} (z : Word ι m) (ω : Ω) : Prop :=
  ∀ j : Fin m, (j : ℕ) < i → I (s + 1 + j) ω = z j

def HitAt (I : ℕ → Ω → ι) (m : ℕ) (U : Finset (Word ι m)) (k : ℕ) (ω : Ω) : Prop :=
  m ≤ k ∧ NoOcc I m U (k - 1) ω ∧ block I m k ω ∈ U

section Li

variable {p : Weights ι} {P : Measure Ω} {I : ℕ → Ω → ι} (hI : IsIIDProcess p P I)
  {m : ℕ} {U : Finset (Word ι m)}

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Ω] in

theorem noOcc_iff_hitAt_or (t : ℕ) (ω : Ω) :
    NoOcc I m U t ω ↔ HitAt I m U (t + 1) ω ∨ NoOcc I m U (t + 1) ω := by
  unfold HitAt
  rw [Nat.add_sub_cancel]
  constructor
  · intro h
    by_cases hm : m ≤ t + 1
    · by_cases hb : block I m (t + 1) ω ∈ U
      · exact Or.inl ⟨hm, h, hb⟩
      · refine Or.inr fun k hk1 hk2 => ?_
        rcases Nat.lt_or_ge k (t + 1) with hk | hk
        · exact h k hk1 (by omega)
        · rw [show k = t + 1 by omega]; exact hb
    · refine Or.inr fun k hk1 hk2 => ?_
      exact h k hk1 (by omega)
  · rintro (⟨_, h, _⟩ | h)
    · exact h
    · exact fun k hk1 hk2 => h k hk1 (by omega)

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Ω] in

theorem not_hitAt_and_noOcc (t : ℕ) (ω : Ω) :
    ¬ (HitAt I m U (t + 1) ω ∧ NoOcc I m U (t + 1) ω) := by
  rintro ⟨⟨hm, _, hb⟩, h⟩
  exact h (t + 1) hm le_rfl hb

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Ω] in

theorem prefixMatch_zero (s : ℕ) (z : Word ι m) (ω : Ω) : PrefixMatch I s 0 z ω := by
  intro j hj
  exact absurd hj (Nat.not_lt_zero _)

include hI

theorem IsIIDProcess.measurableSet_prefixMatch (s i : ℕ) (z : Word ι m) :
    MeasurableSet {ω | PrefixMatch I s i z ω} := by
  have : {ω | PrefixMatch I s i z ω}
      = ⋂ j ∈ (univ : Finset (Fin m)).filter (fun j : Fin m => (j : ℕ) < i),
          (I (s + 1 + j)) ⁻¹' {z j} := by
    ext ω
    simp only [Set.mem_setOf_eq, PrefixMatch, Set.mem_iInter, mem_filter, mem_univ, true_and,
      Set.mem_preimage, Set.mem_singleton_iff]
  rw [this]
  exact MeasurableSet.biInter (Finset.countable_toSet _) fun j _ =>
    hI.measurable _ (measurableSet_singleton _)

theorem IsIIDProcess.measurableSet_hitAt (k : ℕ) : MeasurableSet {ω | HitAt I m U k ω} := by
  have : {ω | HitAt I m U k ω}
      = {ω | m ≤ k} ∩ ({ω | NoOcc I m U (k - 1) ω} ∩ (block I m k) ⁻¹' (U : Set (Word ι m))) := by
    ext ω; simp [HitAt]
  rw [this]
  exact (MeasurableSet.const _).inter ((hI.measurableSet_noOcc (k - 1)).inter
    ((measurable_pi_iff.mpr fun _ => hI.measurable _) U.finite_toSet.measurableSet))

theorem IsIIDProcess.measure_noOcc_inter (t : ℕ) {Q : Set Ω} (hQ : MeasurableSet Q) :
    P ({ω | NoOcc I m U t ω} ∩ Q)
      = P ({ω | HitAt I m U (t + 1) ω} ∩ Q) + P ({ω | NoOcc I m U (t + 1) ω} ∩ Q) := by
  have hset : {ω | NoOcc I m U t ω} ∩ Q
      = ({ω | HitAt I m U (t + 1) ω} ∩ Q) ∪ ({ω | NoOcc I m U (t + 1) ω} ∩ Q) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_union, noOcc_iff_hitAt_or t ω]
    tauto
  rw [hset, measure_union _ ((hI.measurableSet_noOcc (t + 1)).inter hQ)]
  rw [Set.disjoint_left]
  rintro ω ⟨h1, _⟩ ⟨h2, _⟩
  exact not_hitAt_and_noOcc t ω ⟨h1, h2⟩

theorem IsIIDProcess.measure_noOcc_prefixMatch_succ [Nonempty ι] (s : ℕ) {i : ℕ} (hi : i < m)
    (z : Word ι m) :
    P {ω | NoOcc I m U (s + i) ω ∧ PrefixMatch I s (i + 1) z ω}
      = P {ω | NoOcc I m U (s + i) ω ∧ PrefixMatch I s i z ω} * ENNReal.ofReal (p.p (z ⟨i, hi⟩)) := by
  classical

  let Q₁ : Word ι (s + i) → Prop := fun W =>
    WordNoOcc W m U ∧ ∀ j : Fin m, (hj : (j : ℕ) < i) → W ⟨s + j, by omega⟩ = z j
  let Q₂ : Word ι 1 → Prop := fun W => W 0 = z ⟨i, hi⟩
  have h₁ : ∀ ω, (NoOcc I m U (s + i) ω ∧ PrefixMatch I s i z ω) ↔ Q₁ (blockFrom I 0 (s + i) ω) := by
    intro ω
    have hno : NoOcc I m U (s + i) ω ↔ WordNoOcc (blockFrom I 0 (s + i) ω) m U := by
      have h := noOccIn_iff_wordNoOcc I m U 0 (s + i) ω
      rw [zero_add, zero_add] at h
      exact h
    simp only [Q₁, PrefixMatch, blockFrom]
    rw [hno]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun j hj => by rw [← h2 j hj]; congr 1; omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun j hj => by rw [← h2 j hj]; congr 1; omega⟩
  have h₂ : ∀ ω, (I (s + i + 1) ω = z ⟨i, hi⟩) ↔ Q₂ (blockFrom I (s + i) 1 ω) := by
    intro ω
    simp only [Q₂, blockFrom, Fin.val_zero, add_zero]
  have hsplit : {ω | NoOcc I m U (s + i) ω ∧ PrefixMatch I s (i + 1) z ω}
      = {ω | Q₁ (blockFrom I 0 (s + i) ω) ∧ Q₂ (blockFrom I (s + i) 1 ω)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [← h₁, ← h₂]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, fun j hj => h2 j (by omega)⟩, ?_⟩
      have := h2 ⟨i, hi⟩ (by simp)
      simpa [show s + 1 + i = s + i + 1 by omega] using this
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun j hj => ?_⟩
      rcases Nat.lt_or_ge (j : ℕ) i with hji | hji
      · exact h2 j hji
      · have hj' : j = ⟨i, hi⟩ := Fin.ext (by simp; omega)
        rw [hj']
        simpa [show s + 1 + i = s + i + 1 by omega] using h3
  rw [hsplit, hI.measure_window_and (by omega) Q₁ Q₂]
  congr 1
  · congr 1
    ext ω
    exact (h₁ ω).symm
  · rw [show {ω | Q₂ (blockFrom I (s + i) 1 ω)} = {ω | I (s + i + 1) ω = z ⟨i, hi⟩} by
      ext ω; exact (h₂ ω).symm]
    exact hI.law _ _

end Li

section Li2

variable {p : Weights ι} {P : Measure Ω} {I : ℕ → Ω → ι} (hI : IsIIDProcess p P I)
  {m : ℕ} {U : Finset (Word ι m)} (z : Word ι m)

variable (P I) (m U) (p) in

noncomputable def liA (s i : ℕ) : ℝ≥0∞ :=
  P {ω | NoOcc I m U (s + i) ω ∧ PrefixMatch I s (i + 1) z ω}
    * ENNReal.ofReal (p.suffixProb z (m - (i + 1)))

variable (P I) (m U) (p) in

noncomputable def liD (s i : ℕ) : ℝ≥0∞ :=
  P {ω | HitAt I m U (s + i + 1) ω ∧ PrefixMatch I s (i + 1) z ω}
    * ENNReal.ofReal (p.suffixProb z (m - (i + 1)))

variable (P I) (m U) (p) in

noncomputable def liE (k i : ℕ) : ℝ≥0∞ :=
  P {ω | HitAt I m U k ω ∧ PrefixMatch I (k - (i + 1)) (i + 1) z ω}
    * ENNReal.ofReal (p.suffixProb z (m - (i + 1)))

variable (P I) (m U) in

noncomputable def hitProb (u : Word ι m) : ℝ≥0∞ :=
  ∑' k : ℕ, P {ω | HitAt I m U k ω ∧ block I m k ω = u}

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Ω] in

theorem not_noOcc_prefixMatch_full (hz : z ∈ U) (s : ℕ) (ω : Ω)
    (h : NoOcc I m U (s + m) ω) (hpm : PrefixMatch I s m z ω) : False := by
  refine h (s + m) (by omega) le_rfl ?_
  have : block I m (s + m) ω = z := by
    funext j
    have := hpm j j.isLt
    rw [← this]
    simp only [block]
    congr 1
    omega
  rw [this]; exact hz

include hI

omit hI [MeasurableSpace ι] [MeasurableSingletonClass ι] in

theorem liA_m (hz : z ∈ U) (s : ℕ) : liA p P I m U z s m = 0 := by
  unfold liA
  have : {ω | NoOcc I m U (s + m) ω ∧ PrefixMatch I s (m + 1) z ω} = ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro h hpm
    exact not_noOcc_prefixMatch_full z hz s ω h fun j hj => hpm j (by omega)
  rw [this, measure_empty, zero_mul]

theorem IsIIDProcess.liA_succ [Nonempty ι] (hz : z ∈ U) (s : ℕ) {i : ℕ} (hi : i < m) :
    liA p P I m U z s i = liD p P I m U z s i + liA p P I m U z s (i + 1) := by
  have hsplit : P {ω | NoOcc I m U (s + i) ω ∧ PrefixMatch I s (i + 1) z ω}
      = P {ω | HitAt I m U (s + i + 1) ω ∧ PrefixMatch I s (i + 1) z ω}
        + P {ω | NoOcc I m U (s + i + 1) ω ∧ PrefixMatch I s (i + 1) z ω} := by
    rw [Set.setOf_and, Set.setOf_and, Set.setOf_and]
    exact hI.measure_noOcc_inter (s + i) (hI.measurableSet_prefixMatch s (i + 1) z)
  have hnext : liA p P I m U z s (i + 1)
      = P {ω | NoOcc I m U (s + i + 1) ω ∧ PrefixMatch I s (i + 1) z ω}
        * ENNReal.ofReal (p.suffixProb z (m - (i + 1))) := by
    rcases Nat.lt_or_ge (i + 1) m with hi1 | hi1
    · unfold liA
      have h := hI.measure_noOcc_prefixMatch_succ (U := U) s hi1 z
      rw [show s + (i + 1) = s + i + 1 by omega] at h
      rw [show s + (i + 1) = s + i + 1 by omega, h, mul_assoc,
        ← ENNReal.ofReal_mul (p.pos _).le, ← p.suffixProb_succ z hi1]
    · have hm : i + 1 = m := by omega
      have e1 : {ω | NoOcc I m U (s + i + 1) ω ∧ PrefixMatch I s (i + 1) z ω} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro h hpm
        rw [show s + i + 1 = s + m by omega] at h
        rw [hm] at hpm
        exact not_noOcc_prefixMatch_full z hz s ω h hpm
      rw [e1, measure_empty, zero_mul, hm, liA_m z hz s]
  calc liA p P I m U z s i
      = (P {ω | HitAt I m U (s + i + 1) ω ∧ PrefixMatch I s (i + 1) z ω}
          + P {ω | NoOcc I m U (s + i + 1) ω ∧ PrefixMatch I s (i + 1) z ω})
          * ENNReal.ofReal (p.suffixProb z (m - (i + 1))) := by
        unfold liA; rw [hsplit]
    _ = liD p P I m U z s i + liA p P I m U z s (i + 1) := by
        rw [add_mul, hnext]; rfl

theorem IsIIDProcess.liA_zero [Nonempty ι] (hm : 1 ≤ m) (s : ℕ) :
    liA p P I m U z s 0 = P {ω | NoOcc I m U s ω} * ENNReal.ofReal (p.wordProb z) := by
  unfold liA
  have h0 : (0 : ℕ) < m := hm
  have := hI.measure_noOcc_prefixMatch_succ (U := U) s h0 z
  rw [add_zero] at this
  rw [add_zero, this, mul_assoc, ← ENNReal.ofReal_mul (p.pos _).le, Nat.zero_add]
  congr 2
  · ext ω
    simp only [Set.mem_setOf_eq, and_iff_left_iff_imp]
    intro _
    exact prefixMatch_zero s z ω
  · have := p.suffixProb_succ z h0
    rw [Nat.sub_zero, p.suffixProb_eq_wordProb, Nat.zero_add] at this
    exact this.symm

theorem IsIIDProcess.measure_noOcc_mul_eq_sum_liD [Nonempty ι] (hm : 1 ≤ m) (hz : z ∈ U) (s : ℕ) :
    P {ω | NoOcc I m U s ω} * ENNReal.ofReal (p.wordProb z) = ∑ i ∈ range m, liD p P I m U z s i := by
  have key : ∀ j, j ≤ m → liA p P I m U z s (m - j) = ∑ i ∈ Ico (m - j) m, liD p P I m U z s i := by
    intro j
    induction j with
    | zero => intro _; simp [liA_m z hz s]
    | succ j ih =>
      intro hj
      rw [hI.liA_succ z hz s (i := m - (j + 1)) (by omega), show m - (j + 1) + 1 = m - j by omega,
        ih (by omega)]
      conv_rhs => rw [sum_eq_sum_Ico_succ_bot (by omega : m - (j + 1) < m)]
      rw [show m - (j + 1) + 1 = m - j by omega]
  rw [← hI.liA_zero z hm s]
  have := key m le_rfl
  rw [Nat.sub_self] at this
  rw [this, range_eq_Ico]

omit hI in

theorem tsum_finset_sum' {β : Type*} (s : Finset β) (f : β → ℕ → ℝ≥0∞) :
    ∑' n, ∑ b ∈ s, f b n = ∑ b ∈ s, ∑' n, f b n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [sum_insert ha, ENNReal.tsum_add, ih]

omit hI [MeasurableSpace ι] [MeasurableSingletonClass ι] in

theorem tsum_liD_eq {i : ℕ} (hi : i < m) :
    ∑' s, liD p P I m U z s i = ∑' k, liE p P I m U z k i := by
  have hD : ∀ s, liD p P I m U z s i = liE p P I m U z (s + i + 1) i := by
    intro s
    unfold liD liE
    rw [show s + i + 1 - (i + 1) = s by omega]
  simp_rw [hD]
  have hinj : Function.Injective (fun s : ℕ => s + i + 1) := fun a b h => by simpa using h
  refine Function.Injective.tsum_eq (f := fun k => liE p P I m U z k i) hinj ?_
  intro k hk
  rw [Function.mem_support] at hk
  have hne : {ω | HitAt I m U k ω ∧ PrefixMatch I (k - (i + 1)) (i + 1) z ω}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    unfold liE at hk
    rw [h, measure_empty, zero_mul] at hk
    exact hk rfl
  obtain ⟨ω, hω⟩ := hne
  have hk' : m ≤ k := hω.1.1
  exact ⟨k - i - 1, by simp; omega⟩

open scoped Classical in

theorem IsIIDProcess.measure_hitAt_prefixMatch (k : ℕ) {i : ℕ} (hi : i < m) :
    P {ω | HitAt I m U k ω ∧ PrefixMatch I (k - (i + 1)) (i + 1) z ω}
      = ∑ u, if Overlap u z (m - (i + 1)) then P {ω | HitAt I m U k ω ∧ block I m k ω = u} else 0 := by
  classical
  have hset : {ω | HitAt I m U k ω ∧ PrefixMatch I (k - (i + 1)) (i + 1) z ω}
      = ⋃ u ∈ (univ : Finset (Word ι m)).filter (fun u => Overlap u z (m - (i + 1))),
          {ω | HitAt I m U k ω ∧ block I m k ω = u} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, mem_filter, mem_univ, true_and, exists_prop]
    constructor
    · rintro ⟨hk, hpm⟩
      refine ⟨block I m k ω, ?_, hk, rfl⟩
      intro j hj
      have hkm : m ≤ k := hk.1
      have := hpm j (by omega)
      simp only [block]
      rw [← this]
      congr 1
      omega
    · rintro ⟨u, hov, hk, rfl⟩
      refine ⟨hk, fun j hj => ?_⟩
      have hkm : m ≤ k := hk.1
      have := hov j (by omega)
      simp only [block] at this
      rw [← this]
      congr 1
      omega
  rw [hset, measure_biUnion_finset]
  · rw [sum_filter]
  · intro u _ u' _ huu'
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨_, h1⟩ ⟨_, h2⟩
    exact huu' (h1.symm.trans h2)
  · intro u _
    exact (hI.measurableSet_hitAt k).inter
      ((measurable_pi_iff.mpr fun _ => hI.measurable _) (measurableSet_singleton u))

theorem IsIIDProcess.sum_liE (k : ℕ) :
    ∑ i ∈ range m, liE p P I m U z k i
      = ∑ u, P {ω | HitAt I m U k ω ∧ block I m k ω = u} * ENNReal.ofReal (p.wcorr u z) := by
  classical
  unfold liE
  have h1 : ∀ i ∈ range m, P {ω | HitAt I m U k ω ∧ PrefixMatch I (k - (i + 1)) (i + 1) z ω}
      * ENNReal.ofReal (p.suffixProb z (m - (i + 1)))
      = ∑ u, if Overlap u z (m - (i + 1)) then
          P {ω | HitAt I m U k ω ∧ block I m k ω = u}
            * ENNReal.ofReal (p.suffixProb z (m - (i + 1))) else 0 := by
    intro i hi
    rw [hI.measure_hitAt_prefixMatch z k (mem_range.mp hi), sum_mul]
    exact sum_congr rfl fun u _ => by rw [ite_mul, zero_mul]
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun u _ => ?_
  set Pu := P {ω | HitAt I m U k ω ∧ block I m k ω = u} with hPu
  have hL : (∑ i ∈ range m, if Overlap u z (m - (i + 1)) then
        Pu * ENNReal.ofReal (p.suffixProb z (m - (i + 1))) else 0)
      = ∑ h ∈ range m, if Overlap u z h then Pu * ENNReal.ofReal (p.suffixProb z h) else 0 := by
    rw [← sum_range_reflect (fun h => if Overlap u z h then Pu * ENNReal.ofReal (p.suffixProb z h)
      else 0) m]
    refine sum_congr rfl fun i hi => ?_
    rw [show m - 1 - i = m - (i + 1) by omega]
  rw [hL]
  unfold Weights.wcorr
  rw [ENNReal.ofReal_sum_of_nonneg (fun h _ => by split_ifs; exacts [(p.suffixProb_pos z h).le, le_rfl]),
    mul_sum]
  refine sum_congr rfl fun h _ => ?_
  rw [apply_ite ENNReal.ofReal, ENNReal.ofReal_zero, mul_ite, mul_zero]

theorem IsIIDProcess.li_identity [Nonempty ι] (hm : 1 ≤ m) (hz : z ∈ U) :
    expectedHitting P I m U * ENNReal.ofReal (p.wordProb z)
      = ∑ u, hitProb P I m U u * ENNReal.ofReal (p.wcorr u z) := by
  rw [hI.expectedHitting_eq_tsum, ← ENNReal.tsum_mul_right]
  simp_rw [hI.measure_noOcc_mul_eq_sum_liD z hm hz]
  rw [tsum_finset_sum']
  rw [sum_congr rfl fun i hi => tsum_liD_eq z (mem_range.mp hi), ← tsum_finset_sum']
  simp_rw [hI.sum_liE z]
  rw [tsum_finset_sum']
  refine sum_congr rfl fun u _ => ?_
  rw [hitProb, ENNReal.tsum_mul_right]

end Li2

section Finite

variable {p : Weights ι} {P : Measure Ω} {I : ℕ → Ω → ι} (hI : IsIIDProcess p P I)
  {m : ℕ} {U : Finset (Word ι m)}

include hI

theorem IsIIDProcess.avoid_submul [Nonempty ι] (s t : ℕ) :
    P {ω | NoOcc I m U (s + t) ω} ≤ P {ω | NoOcc I m U s ω} * P {ω | NoOcc I m U t ω} := by
  classical
  have hsub : {ω | NoOcc I m U (s + t) ω}
      ⊆ {ω | WordNoOcc (blockFrom I 0 s ω) m U ∧ WordNoOcc (blockFrom I s t ω) m U} := by
    intro ω h
    simp only [Set.mem_setOf_eq] at h ⊢
    constructor
    · have h1 : NoOcc I m U s ω := fun k hk1 hk2 => h k hk1 (by omega)
      have e := noOccIn_iff_wordNoOcc I m U 0 s ω
      rw [zero_add, zero_add] at e
      exact e.mp h1
    · exact (noOccIn_iff_wordNoOcc I m U s t ω).mp fun k hk1 hk2 => h k (by omega) hk2
  refine (measure_mono hsub).trans ?_
  rw [hI.measure_window_and (by omega) (fun W => WordNoOcc W m U) (fun W => WordNoOcc W m U)]
  have e1 : {ω | WordNoOcc (blockFrom I 0 s ω) m U} = {ω | NoOcc I m U s ω} := by
    ext ω
    have e := noOccIn_iff_wordNoOcc I m U 0 s ω
    rw [zero_add, zero_add] at e
    exact e.symm
  have e2 : {ω | WordNoOcc (blockFrom I s t ω) m U} = {ω | NoOccIn I m U (s + m) (s + t) ω} := by
    ext ω
    exact (noOccIn_iff_wordNoOcc I m U s t ω).symm
  rw [e1, e2, hI.measure_noOccIn s t, ← hI.measure_noOcc t]

theorem IsIIDProcess.measure_noOcc_m [Nonempty ι] :
    P {ω | NoOcc I m U m ω} = 1 - ENNReal.ofReal (p.patternMass U) := by
  classical
  haveI := hI.isProbability
  have hset : {ω | NoOcc I m U m ω} = {ω | block I m m ω ∈ U}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, NoOcc]
    constructor
    · intro h hmem
      exact h m le_rfl le_rfl hmem
    · intro h k hk1 hk2
      rw [show k = m by omega]
      exact h
  have e : {ω | block I m m ω ∈ U} = {ω | blockFrom I 0 m ω ∈ U} := by
    ext ω
    simp only [Set.mem_setOf_eq, block_eq_blockFrom, Nat.sub_self]
  have hc := prob_compl_eq_one_sub (μ := P) ((hI.measurable_blockFrom 0 m) U.finite_toSet.measurableSet)
  change P {ω | blockFrom I 0 m ω ∈ U}ᶜ = 1 - P {ω | blockFrom I 0 m ω ∈ U} at hc
  rw [hset, e, hc, hI.measure_window 0 m (fun W => W ∈ U), Weights.patternMass,
    ENNReal.ofReal_sum_of_nonneg fun w _ => (p.wordProb_pos w).le]
  congr 1
  refine sum_congr ?_ fun _ _ => rfl
  ext w; simp

theorem IsIIDProcess.measure_noOcc_mul_le [Nonempty ι] (k : ℕ) :
    P {ω | NoOcc I m U (k * m) ω} ≤ (1 - ENNReal.ofReal (p.patternMass U)) ^ k := by
  haveI := hI.isProbability
  induction k with
  | zero =>
    simp only [zero_mul, pow_zero]
    exact prob_le_one
  | succ k ih =>
    rw [Nat.succ_mul, pow_succ]
    exact (hI.avoid_submul (k * m) m).trans (mul_le_mul' ih hI.measure_noOcc_m.le)

theorem IsIIDProcess.measure_hittingTime_top [Nonempty ι] (hU : U.Nonempty) :
    P {ω | hittingTime I m U ω = ⊤} = 0 := by
  have ha : 0 < p.patternMass U := p.patternMass_pos hU
  have ha1 : p.patternMass U ≤ 1 := p.patternMass_le_one U
  have hle : ∀ k : ℕ, P {ω | hittingTime I m U ω = ⊤}
      ≤ ENNReal.ofReal ((1 - p.patternMass U) ^ k) := by
    intro k
    calc P {ω | hittingTime I m U ω = ⊤} ≤ P {ω | NoOcc I m U (k * m) ω} := by
          refine measure_mono fun ω hω => ?_
          have hω' : hittingTime I m U ω = ⊤ := hω
          rw [Set.mem_setOf_eq, ← lt_hittingTime_iff, hω']
          exact ENat.coe_lt_top _
      _ ≤ (1 - ENNReal.ofReal (p.patternMass U)) ^ k := hI.measure_noOcc_mul_le (m := m) (U := U) k
      _ = ENNReal.ofReal ((1 - p.patternMass U) ^ k) := by
          rw [ENNReal.ofReal_pow (by linarith), ENNReal.ofReal_sub _ ha.le, ENNReal.ofReal_one]
  have htend : Tendsto (fun k : ℕ => ENNReal.ofReal ((1 - p.patternMass U) ^ k)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : (0 : ℝ) ≤ 1 - p.patternMass U)
        (by linarith))
    rwa [ENNReal.ofReal_zero] at this
  exact le_antisymm (ge_of_tendsto' htend hle) zero_le

omit hI [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Ω] in

theorem hittingTime_eq_iff (hm : 1 ≤ m) (k : ℕ) (ω : Ω) :
    hittingTime I m U ω = k ↔ HitAt I m U k ω := by
  constructor
  · intro h
    have hmk : m ≤ k := by
      have := hittingTime_ge (I := I) (U := U) (m := m) ω
      rw [h] at this
      exact_mod_cast this
    have hno : NoOcc I m U (k - 1) ω := by
      rw [← lt_hittingTime_iff, h]
      exact_mod_cast (show k - 1 < k by omega)
    refine ⟨hmk, hno, ?_⟩
    by_contra hb
    have hno' : NoOcc I m U k ω := by
      intro k' hk1 hk2
      rcases Nat.lt_or_ge k' k with hk | hk
      · exact hno k' hk1 (by omega)
      · rw [show k' = k by omega]; exact hb
    have := (lt_hittingTime_iff k ω).mpr hno'
    rw [h] at this
    exact lt_irrefl _ this
  · rintro ⟨hmk, hno, hb⟩
    apply le_antisymm
    · unfold hittingTime
      exact iInf_le_of_le k (iInf_le_of_le hmk (iInf_le _ hb))
    · have := (lt_hittingTime_iff (k - 1) ω).mpr hno
      rw [← ENat.add_one_le_iff (ENat.coe_ne_top _)] at this
      have e : ((k - 1 : ℕ) : ℕ∞) + 1 = (k : ℕ∞) := by
        rw [← Nat.cast_succ]
        congr 1
        omega
      rwa [e] at this

theorem IsIIDProcess.measure_iUnion_hitAt [Nonempty ι] (hm : 1 ≤ m) (hU : U.Nonempty) :
    P (⋃ k : ℕ, {ω | HitAt I m U k ω}) = 1 := by
  haveI := hI.isProbability
  have hset : (⋃ k : ℕ, {ω | HitAt I m U k ω}) = {ω | hittingTime I m U ω = ⊤}ᶜ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff]
    show (∃ i, HitAt I m U i ω) ↔ hittingTime I m U ω ≠ ⊤
    rw [ENat.ne_top_iff_exists]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k, ((hittingTime_eq_iff hm k ω).mpr hk).symm⟩
    · rintro ⟨k, hk⟩; exact ⟨k, (hittingTime_eq_iff hm k ω).mp hk.symm⟩
  have hmeas : MeasurableSet {ω | hittingTime I m U ω = ⊤} := by
    have : {ω | hittingTime I m U ω = ⊤} = (⋃ k : ℕ, {ω | HitAt I m U k ω})ᶜ := by
      rw [hset, compl_compl]
    rw [this]
    exact (MeasurableSet.iUnion fun k => hI.measurableSet_hitAt k).compl
  rw [hset, prob_compl_eq_one_sub hmeas, hI.measure_hittingTime_top hU, tsub_zero]

omit hI [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Ω] in

theorem hitAt_pairwise_disjoint (hm : 1 ≤ m) :
    Pairwise (Function.onFun Disjoint fun k : ℕ => {ω | HitAt I m U k ω}) := by
  intro k k' hkk'
  rw [Function.onFun, Set.disjoint_left]
  intro ω h1 h2
  have e1 := (hittingTime_eq_iff hm k ω).mpr h1
  have e2 := (hittingTime_eq_iff hm k' ω).mpr h2
  exact hkk' (by exact_mod_cast e1.symm.trans e2)

theorem IsIIDProcess.sum_hitProb [Nonempty ι] (hm : 1 ≤ m) (hU : U.Nonempty) :
    ∑ u, hitProb P I m U u = 1 := by
  classical
  unfold hitProb
  rw [← tsum_finset_sum']
  have h1 : ∀ k, ∑ u, P {ω | HitAt I m U k ω ∧ block I m k ω = u} = P {ω | HitAt I m U k ω} := by
    intro k
    rw [← measure_biUnion_finset]
    · congr 1
      ext ω
      constructor
      · intro h
        obtain ⟨u, hu⟩ := Set.mem_iUnion.mp h
        obtain ⟨_, hu'⟩ := Set.mem_iUnion.mp hu
        exact hu'.1
      · intro h
        exact Set.mem_iUnion.mpr ⟨block I m k ω, Set.mem_iUnion.mpr ⟨mem_univ _, h, rfl⟩⟩
    · intro u _ u' _ huu'
      rw [Function.onFun, Set.disjoint_left]
      rintro ω ⟨_, h1⟩ ⟨_, h2⟩
      exact huu' (h1.symm.trans h2)
    · intro u _
      exact (hI.measurableSet_hitAt k).inter
        ((measurable_pi_iff.mpr fun _ => hI.measurable _) (measurableSet_singleton u))
  simp_rw [h1]
  rw [← measure_iUnion (hitAt_pairwise_disjoint hm) fun k => hI.measurableSet_hitAt k,
    hI.measure_iUnion_hitAt hm hU]

end Finite

end FractalGeometry.Probability.Patterns
