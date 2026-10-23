import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.ApproxSquares
import FractalGeometry.Probability.GridPercolation.Floor
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.Processes
import FractalGeometry.Probability.GridPercolation.SurvivalMeasurability
import FractalGeometry.Probability.GridPercolation.WordSplitting

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open Filter Topology Set

open scoped ENNReal

variable {A : GridLaw} {Ω : Type*}

lemma cellMap_continuous (a : Fin A.M × Fin A.N) : Continuous (cellMap A a) := by
  unfold cellMap
  fun_prop

lemma cellMap_unit_subset (a : Fin A.M × Fin A.N) :
    cellMap A a '' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ⊆
      Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
  rintro _ ⟨z, ⟨⟨hz1, hz2⟩, ⟨hz3, hz4⟩⟩, rfl⟩
  simp only [cellMap, Set.mem_prod, Set.mem_Icc]
  have hM : (0 : ℝ) < A.M := by exact_mod_cast A.hM_pos
  have hN : (0 : ℝ) < A.N := by exact_mod_cast A.hN_pos
  have ha1 : ((a.1 : ℕ) : ℝ) + 1 ≤ A.M := by exact_mod_cast a.1.isLt
  have ha2 : ((a.2 : ℕ) : ℝ) + 1 ≤ A.N := by exact_mod_cast a.2.isLt
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact div_nonneg (add_nonneg hz1 (Nat.cast_nonneg _)) hM.le
  · rw [div_le_one hM]
    linarith
  · exact div_nonneg (add_nonneg hz3 (Nat.cast_nonneg _)) hN.le
  · rw [div_le_one hN]
    linarith

lemma rect_subset_unit (w : Word A) :
    rect A w ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
  induction w with
  | nil => exact le_rfl
  | cons a w ih =>
    show cellMap A a '' rect A w ⊆ _
    exact (Set.image_mono ih).trans (cellMap_unit_subset a)

lemma rect_append_subset (w u : Word A) : rect A (w ++ u) ⊆ rect A w := by
  induction w with
  | nil =>
    rw [List.nil_append]
    exact rect_subset_unit u
  | cons a w ih =>
    show cellMap A a '' rect A (w ++ u) ⊆ cellMap A a '' rect A w
    exact Set.image_mono ih

lemma isCompact_rect (w : Word A) : IsCompact (rect A w) := by
  induction w with
  | nil => exact isCompact_Icc.prod isCompact_Icc
  | cons a w ih => exact ih.image (cellMap_continuous a)

lemma rect_nonempty (w : Word A) : (rect A w).Nonempty := by
  induction w with
  | nil => exact ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩⟩
  | cons a w ih => exact ih.image _

def descendantWords (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (ω : Ω) (w : Word A)
    (L : ℕ) : Set (Word A) :=
  {v | v.length = L ∧ RetainedBelow X ω w v}

lemma descendantWords_finite (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (ω : Ω)
    (w : Word A) (L : ℕ) : (descendantWords X ω w L).Finite :=
  (List.finite_length_eq _ L).subset fun _ hv => hv.1

theorem rect_inter_limitSet_nonempty {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool} {ω : Ω}
    {w : Word A} (hw : Retained X ω w) (hdesc : HasInfiniteDescentBelow X ω w) :
    (rect A w ∩ limitSet X ω).Nonempty := by
  classical
  set t : ℕ → Set (ℝ × ℝ) := fun L => ⋃ v ∈ descendantWords X ω w L, rect A (w ++ v) with ht
  have htd : ∀ L, t (L + 1) ⊆ t L := by
    intro L z hz
    obtain ⟨v, hv, hzv⟩ := Set.mem_iUnion₂.mp hz
    refine Set.mem_iUnion₂.mpr ⟨v.take L, ⟨?_, hv.2.take L⟩, ?_⟩
    · rw [List.length_take, hv.1]
      omega
    · have : w ++ v = (w ++ v.take L) ++ v.drop L := by
        rw [List.append_assoc, List.take_append_drop]
      rw [this] at hzv
      exact rect_append_subset _ _ hzv
  have htn : ∀ L, (t L).Nonempty := by
    intro L
    obtain ⟨u, hu⟩ := hdesc L
    obtain ⟨z, hz⟩ := rect_nonempty (w ++ wordOfDigits u)
    exact ⟨z, Set.mem_iUnion₂.mpr ⟨wordOfDigits u, ⟨length_wordOfDigits u, hu⟩, hz⟩⟩
  have htc : ∀ L, IsCompact (t L) := fun L =>
    (descendantWords_finite X ω w L).isCompact_biUnion fun _ _ => isCompact_rect _
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t htd htn
    (htc 0) fun L => (htc L).isClosed
  have hzw : z ∈ rect A w := by
    have h0 := Set.mem_iInter.mp hz 0
    obtain ⟨v, hv, hzv⟩ := Set.mem_iUnion₂.mp h0
    have hv0 : v = [] := List.eq_nil_of_length_eq_zero hv.1
    rw [hv0, List.append_nil] at hzv
    exact hzv
  refine ⟨z, hzw, Set.mem_iInter.mpr fun n => ?_⟩
  rcases le_or_gt w.length n with hn | hn
  · have hL := Set.mem_iInter.mp hz (n - w.length)
    obtain ⟨v, hv, hzv⟩ := Set.mem_iUnion₂.mp hL
    refine Set.mem_iUnion₂.mpr ⟨w ++ v, ⟨?_, ?_⟩, hzv⟩
    · rw [List.length_append, hv.1]
      omega
    · rw [retained_iff_retainedBelow_nil, retainedBelow_append_iff]
      refine ⟨(retained_iff_retainedBelow_nil X ω w).mp hw, ?_⟩
      simpa using hv.2
  · refine Set.mem_iUnion₂.mpr ⟨w.take n, ⟨?_, ?_⟩, ?_⟩
    · rw [List.length_take]
      omega
    · rw [retained_iff_retainedBelow_nil]
      exact ((retained_iff_retainedBelow_nil X ω w).mp hw).take n
    · have : w = w.take n ++ w.drop n := (List.take_append_drop n w).symm
      rw [this] at hzw
      exact rect_append_subset _ _ hzw

theorem mem_survival_iff_limitSet_nonempty
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (ω : Ω) :
    ω ∈ survival X ↔ (limitSet X ω).Nonempty := by
  constructor
  · intro hsurv
    have hdesc : HasInfiniteDescentBelow X ω [] :=
      (hasInfiniteDescentBelow_nil_iff_mem_survival X ω).mpr hsurv
    have hret : Retained X ω [] := fun l => l.elim0
    obtain ⟨z, -, hzF⟩ := rect_inter_limitSet_nonempty hret hdesc
    exact ⟨z, hzF⟩
  · rintro ⟨z, hzF⟩ k
    have hzk : z ∈ levelSet X ω k := Set.mem_iInter.mp hzF k
    simp only [levelSet, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hzk
    obtain ⟨w, ⟨hwlen, hwret⟩, -⟩ := hzk
    exact ⟨w, hwlen, hwret⟩

lemma nat_mem_Icc_of_near' {t : ℝ} {n j : ℕ} (hlow : t - (j : ℝ) ≤ n) (hhigh : (n : ℝ) < t) :
    n ∈ Finset.Icc (⌈t⌉₊ - (j + 1)) (⌈t⌉₊ - 1) := by
  have h1 : n < ⌈t⌉₊ := Nat.lt_ceil.mpr hhigh
  have h2 : ⌈t⌉₊ ≤ n + j + 1 := by
    apply Nat.ceil_le.mpr
    push_cast
    linarith
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

lemma card_Icc_sub_le (c j : ℕ) : (Finset.Icc (c - (j + 1)) (c - 1)).card ≤ j + 1 := by
  rw [Nat.card_Icc]
  omega

lemma index_mem_window' {L t z ρ : ℝ} {n K : ℕ} (hL : 0 < L)
    (h1 : (n : ℝ) / L ≤ z) (h2 : z ≤ (n : ℝ) / L + L⁻¹)
    (h3 : |z - t| ≤ ρ) (hρ : ρ ≤ K * L⁻¹) :
    n ∈ Finset.Icc (⌈t * L + K + 1⌉₊ - (2 * K + 2 + 1)) (⌈t * L + K + 1⌉₊ - 1) := by
  have hinv : L⁻¹ * L = 1 := inv_mul_cancel₀ hL.ne'
  obtain ⟨h3a, h3b⟩ := abs_le.mp h3
  have hup : (n : ℝ) < t * L + K + 1 := by
    have h4 : (n : ℝ) ≤ z * L := (div_le_iff₀ hL).mp h1
    have h5 : z ≤ t + K * L⁻¹ := by linarith
    have h6 : z * L ≤ (t + K * L⁻¹) * L := mul_le_mul_of_nonneg_right h5 hL.le
    have h7 : (t + K * L⁻¹) * L = t * L + K := by
      rw [add_mul, mul_assoc, hinv, mul_one]
    linarith
  have hlow : t * L + K + 1 - ((2 * K + 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
    have h4 : t - K * L⁻¹ ≤ z := by linarith
    have h5 : t - K * L⁻¹ - L⁻¹ ≤ (n : ℝ) / L := by linarith
    have h6 : (t - K * L⁻¹ - L⁻¹) * L ≤ (n : ℝ) := (le_div_iff₀ hL).mp h5
    have h7 : (t - K * L⁻¹ - L⁻¹) * L = t * L - K - 1 := by
      rw [sub_mul, sub_mul, mul_assoc, hinv, mul_one]
    push_cast
    linarith
  exact nat_mem_Icc_of_near' hlow hup

open Classical in

theorem card_codes_meeting_le (K : ℕ) {a : ℕ} (S : Set (ℝ × ℝ))
    (hS : Metric.ediam S ≤ ENNReal.ofReal (K * ((A.M : ℝ) ^ a)⁻¹)) :
    ((Finset.univ : Finset (SquareCode A a)).filter
      fun c : SquareCode A a => (c.region ∩ S).Nonempty).card ≤ (2 * K + 3) ^ 2 := by
  classical
  rcases S.eq_empty_or_nonempty with hempty | ⟨z, hz⟩
  · subst hempty
    simp
  have hM0 : (0 : ℝ) < A.M := by exact_mod_cast A.hM_pos
  have hN0 : (0 : ℝ) < A.N := by exact_mod_cast A.hN_pos
  have hMpow : (0 : ℝ) < (A.M : ℝ) ^ a := by positivity
  have hNpow : (0 : ℝ) < (A.N : ℝ) ^ (bfloor A.Gamma a) := by positivity
  have hRN : ((A.M : ℝ) ^ a)⁻¹ ≤ ((A.N : ℝ) ^ (bfloor A.Gamma a))⁻¹ := by
    rw [inv_le_inv₀ hMpow hNpow]
    exact A.pow_bfloor_le a
  set ρ : ℝ := K * ((A.M : ℝ) ^ a)⁻¹ with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hnear : ∀ p ∈ S, |p.1 - z.1| ≤ ρ ∧ |p.2 - z.2| ≤ ρ := by
    intro p hp
    have h := le_trans (Metric.edist_le_ediam_of_mem hp hz) hS
    rw [Prod.edist_eq, max_le_iff, edist_dist, edist_dist,
      ENNReal.ofReal_le_ofReal_iff hρ0, ENNReal.ofReal_le_ofReal_iff hρ0,
      Real.dist_eq, Real.dist_eq] at h
    exact h
  have hρK : ρ ≤ K * ((A.M : ℝ) ^ a)⁻¹ := le_rfl
  have hρN : ρ ≤ K * ((A.N : ℝ) ^ (bfloor A.Gamma a))⁻¹ :=
    mul_le_mul_of_nonneg_left hRN (Nat.cast_nonneg K)
  have hcard : (Finset.Icc (⌈z.1 * (A.M : ℝ) ^ a + K + 1⌉₊ - (2 * K + 2 + 1))
        (⌈z.1 * (A.M : ℝ) ^ a + K + 1⌉₊ - 1) ×ˢ
      Finset.Icc (⌈z.2 * (A.N : ℝ) ^ (bfloor A.Gamma a) + K + 1⌉₊ - (2 * K + 2 + 1))
        (⌈z.2 * (A.N : ℝ) ^ (bfloor A.Gamma a) + K + 1⌉₊ - 1)).card ≤ (2 * K + 3) ^ 2 := by
    rw [Finset.card_product, sq]
    exact Nat.mul_le_mul (card_Icc_sub_le _ _) (card_Icc_sub_le _ _)
  refine le_trans (Finset.card_le_card_of_injOn
    (fun c => (colIndex c, rowIndex c)) ?_ ?_) hcard
  · intro c hc
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hc
    obtain ⟨p, hpr, hpS⟩ := hc
    obtain ⟨⟨hpx1, hpx2⟩, ⟨hpy1, hpy2⟩⟩ := hpr
    obtain ⟨hd1, hd2⟩ := hnear p hpS
    rw [c.xLeft_eq_colIndex_div] at hpx1 hpx2
    rw [c.yLeft_eq_rowIndex_div] at hpy1 hpy2
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe]
    exact ⟨index_mem_window' hMpow hpx1 hpx2 hd1 hρK,
      index_mem_window' hNpow hpy1 hpy2 hd2 hρN⟩
  · intro c _ c' _ h
    exact index_pair_injective a h

theorem card_le_mul_coverNum (K : ℕ) {a : ℕ} (T : Finset (SquareCode A a))
    {F : Set (ℝ × ℝ)} (hT : ∀ c ∈ T, (c.region ∩ F).Nonempty) {r : ℝ}
    (hr : r ≤ K * ((A.M : ℝ) ^ a)⁻¹) :
    (T.card : ℕ∞) ≤ (((2 * K + 3) ^ 2 : ℕ) : ℕ∞) * coverNum r F := by
  classical
  have hK0 : (((2 * K + 3) ^ 2 : ℕ) : ℕ∞) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * K + 3) ^ 2 ≠ 0)
  have key : ∀ C : Set (Set (ℝ × ℝ)), F ⊆ ⋃₀ C →
      (∀ S ∈ C, Metric.ediam S ≤ ENNReal.ofReal r) →
      (T.card : ℕ∞) ≤ (((2 * K + 3) ^ 2 : ℕ) : ℕ∞) * C.encard := by
    intro C hcov hdiam
    rcases eq_or_ne C.encard ⊤ with htop | hfin
    · rw [htop, ENat.mul_top hK0]
      exact le_top
    · have hCfin : C.Finite := Set.encard_ne_top_iff.mp hfin
      have hchoice : ∀ c ∈ T, ∃ S ∈ C, (c.region ∩ S).Nonempty := by
        intro c hc
        obtain ⟨p, hpr, hpF⟩ := hT c hc
        obtain ⟨S, hSC, hpS⟩ := Set.mem_sUnion.mp (hcov hpF)
        exact ⟨S, hSC, ⟨p, hpr, hpS⟩⟩
      choose! f hfC hfmeet using hchoice
      have hmaps : ∀ c ∈ T, f c ∈ hCfin.toFinset := fun c hc =>
        hCfin.mem_toFinset.mpr (hfC c hc)
      have hfib : ∀ S ∈ hCfin.toFinset,
          (T.filter fun c => f c = S).card ≤ (2 * K + 3) ^ 2 := by
        intro S hS
        refine le_trans (Finset.card_le_card (t := (Finset.univ : Finset (SquareCode A a)).filter
          fun c : SquareCode A a => (c.region ∩ S).Nonempty) ?_) (card_codes_meeting_le K S ?_)
        · intro c hc
          rw [Finset.mem_filter] at hc
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hc.2 ▸ hfmeet c hc.1⟩
        · exact le_trans (hdiam S (hCfin.mem_toFinset.mp hS)) (ENNReal.ofReal_le_ofReal hr)
      have h := Finset.card_le_mul_card_image_of_maps_to hmaps _ hfib
      rw [hCfin.encard_eq_coe_toFinset_card]
      exact_mod_cast h
  unfold coverNum
  set I : ℕ∞ := ⨅ (C : Set (Set (ℝ × ℝ))) (_ : F ⊆ ⋃₀ C)
    (_ : ∀ S ∈ C, Metric.ediam S ≤ ENNReal.ofReal r), C.encard with hI
  rcases eq_or_ne I ⊤ with htop | hfin
  · rw [htop, ENat.mul_top hK0]
    exact le_top
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
    have hlt : I < (n : ℕ∞) + 1 := by
      rw [← hn]
      exact_mod_cast Nat.lt_succ_self n
    rw [hI, iInf_lt_iff] at hlt
    obtain ⟨C, hC⟩ := hlt
    rw [iInf_lt_iff] at hC
    obtain ⟨hcov, hC⟩ := hC
    rw [iInf_lt_iff] at hC
    obtain ⟨hdiam, hC⟩ := hC
    have hCle : C.encard ≤ n := Order.le_of_lt_add_one hC
    rw [← hn]
    calc (T.card : ℕ∞) ≤ (((2 * K + 3) ^ 2 : ℕ) : ℕ∞) * C.encard := key C hcov hdiam
      _ ≤ (((2 * K + 3) ^ 2 : ℕ) : ℕ∞) * n := by gcongr

end FractalGeometry.Probability.GridPercolation
