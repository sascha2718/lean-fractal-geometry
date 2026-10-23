import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.ApproxSquares
import FractalGeometry.Probability.GridPercolation.Floor
import FractalGeometry.Probability.GridPercolation.GridCoveringReduction
import FractalGeometry.Probability.GridPercolation.GridNeighbors
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.Processes
import FractalGeometry.Probability.GridPercolation.Support

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open Finset Set

open scoped ENNReal

namespace GridLaw

variable (A : GridLaw)

lemma bfloor_mono {k a : ℕ} (h : k ≤ a) : bfloor A.Gamma k ≤ bfloor A.Gamma a :=
  Nat.floor_le_floor (mul_le_mul_of_nonneg_right (by exact_mod_cast h) A.Gamma_pos.le)

end GridLaw

variable {A : GridLaw}

namespace SquareCode

variable {a : ℕ}

noncomputable def truncate {k : ℕ} (h : k ≤ a) (c : SquareCode A a) : SquareCode A k :=
  (c.col ∘ Fin.castLE h, c.row ∘ Fin.castLE (A.bfloor_mono h))

def Occupied {Ω : Type*} (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (ω : Ω)
    (c : SquareCode A a) : Prop :=
  ∃ w : Word A, c.MemCell w ∧ Retained X ω w

end SquareCode

lemma memCell_compat_truncate {a k : ℕ} (h : k ≤ a) {c : SquareCode A a} {w : Word A}
    (hmem : c.MemCell w) :
    (∀ l : Fin k, colD w l = (c.truncate h).col l) ∧
      (∀ l : Fin (bfloor A.Gamma k), rowD w l = (c.truncate h).row l) := by
  obtain ⟨hlen, hcol, hrow⟩ := hmem
  exact ⟨fun l => hcol (Fin.castLE h l), fun l => hrow (Fin.castLE (A.bfloor_mono h) l)⟩

theorem rect_subset_truncate_region {a k : ℕ} (h : k ≤ a) {c : SquareCode A a}
    {w : Word A} (hmem : c.MemCell w) :
    rect A w ⊆ (c.truncate h).region := by
  obtain ⟨hcol, hrow⟩ := memCell_compat_truncate h hmem
  exact rect_subset_region_of_compat _ w (hmem.1 ▸ h) hcol hrow

variable {Ω : Type*}

noncomputable def occupiedExtensions (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool)
    (ω : Ω) (k q : ℕ) (c : SquareCode A k) : Finset (SquareCode A (k + q)) := by
  classical
  exact {c' : SquareCode A (k + q) |
    c'.truncate (Nat.le_add_right k q) = c ∧ c'.Occupied X ω}.toFinset

lemma mem_occupiedExtensions {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}
    {ω : Ω} {k q : ℕ} {c : SquareCode A k} {c' : SquareCode A (k + q)} :
    c' ∈ occupiedExtensions X ω k q c ↔
      c'.truncate (Nat.le_add_right k q) = c ∧ c'.Occupied X ω := by
  simp [occupiedExtensions]

noncomputable def SQ (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (ω : Ω)
    (k q : ℕ) (c : SquareCode A k) : ℕ :=
  (occupiedExtensions X ω k q c).card

noncomputable def meetingCodes (A : GridLaw) (x : ℝ × ℝ) (k : ℕ) :
    Finset (SquareCode A k) := by
  classical
  exact {c : SquareCode A k |
    (c.region ∩ Metric.eball x (ENNReal.ofReal (gridScale A.M k))).Nonempty}.toFinset

lemma mem_meetingCodes {x : ℝ × ℝ} {k : ℕ} {c : SquareCode A k} :
    c ∈ meetingCodes A x k ↔
      (c.region ∩ Metric.eball x (ENNReal.ofReal (gridScale A.M k))).Nonempty := by
  simp [meetingCodes]

lemma index_mem_window {L t z r : ℝ} {n : ℕ} (hL : 0 < L)
    (h1 : (n : ℝ) / L ≤ z) (h2 : z ≤ (n : ℝ) / L + L⁻¹)
    (h3 : |z - t| < r) (hr : r ≤ L⁻¹) :
    n ∈ Finset.Icc (⌈t * L + 1⌉₊ - 3) (⌈t * L + 1⌉₊ - 1) := by
  have hinv : L⁻¹ * L = 1 := inv_mul_cancel₀ hL.ne'
  obtain ⟨h3a, h3b⟩ := abs_lt.mp h3
  have hup : (n : ℝ) < t * L + 1 := by
    have h4 : (n : ℝ) ≤ z * L := (div_le_iff₀ hL).mp h1
    have h5 : z < t + L⁻¹ := by linarith
    have h6 : z * L < (t + L⁻¹) * L := mul_lt_mul_of_pos_right h5 hL
    nlinarith
  have hlow : t * L - 2 < (n : ℝ) := by
    have h4 : t - L⁻¹ < z := by linarith
    have h5 : z ≤ (n : ℝ) / L + L⁻¹ := h2
    have h6 : t - 2 * L⁻¹ < (n : ℝ) / L := by linarith
    have h7 : (t - 2 * L⁻¹) * L < (n : ℝ) := (lt_div_iff₀ hL).mp h6
    nlinarith
  exact nat_mem_Icc_of_near hlow hup

theorem card_meetingCodes_le_nine (A : GridLaw) (x : ℝ × ℝ) (k : ℕ) :
    (meetingCodes A x k).card ≤ 9 := by
  classical
  set b := bfloor A.Gamma k with hb
  have hMpow : (0 : ℝ) < (A.M : ℝ) ^ k := by
    have : (0 : ℝ) < A.M := by exact_mod_cast A.hM_pos
    positivity
  have hNpow : (0 : ℝ) < (A.N : ℝ) ^ b := by
    have : (0 : ℝ) < A.N := by exact_mod_cast A.hN_pos
    positivity
  have hRN : ((A.M : ℝ) ^ k)⁻¹ ≤ ((A.N : ℝ) ^ b)⁻¹ := by
    rw [inv_le_inv₀ hMpow hNpow]
    exact A.pow_bfloor_le k
  have hcard : (Finset.Icc (⌈x.1 * (A.M : ℝ) ^ k + 1⌉₊ - 3)
        (⌈x.1 * (A.M : ℝ) ^ k + 1⌉₊ - 1) ×ˢ
      Finset.Icc (⌈x.2 * (A.N : ℝ) ^ b + 1⌉₊ - 3)
        (⌈x.2 * (A.N : ℝ) ^ b + 1⌉₊ - 1)).card ≤ 9 := by
    rw [Finset.card_product]
    calc _ ≤ 3 * 3 := Nat.mul_le_mul (card_Icc_sub_three_le _) (card_Icc_sub_three_le _)
      _ = 9 := by norm_num
  refine le_trans (Finset.card_le_card_of_injOn
    (fun c => (colIndex c, rowIndex c)) ?_ ?_) hcard
  · intro c hc
    simp only [Finset.mem_coe, mem_meetingCodes] at hc
    obtain ⟨z, hzr, hzb⟩ := hc
    obtain ⟨⟨hzx1, hzx2⟩, ⟨hzy1, hzy2⟩⟩ := hzr
    rw [Metric.mem_eball, Prod.edist_eq, max_lt_iff] at hzb
    have hR0 : 0 < gridScale A.M k := by
      rw [gridScale_eq_inv_pow]
      positivity
    have hdist1 : |z.1 - x.1| < gridScale A.M k := by
      have := hzb.1
      rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hR0] at this
      rwa [Real.dist_eq] at this
    have hdist2 : |z.2 - x.2| < gridScale A.M k := by
      have := hzb.2
      rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hR0] at this
      rwa [Real.dist_eq] at this
    rw [c.xLeft_eq_colIndex_div] at hzx1 hzx2
    rw [c.yLeft_eq_rowIndex_div] at hzy1 hzy2
    rw [gridScale_eq_inv_pow] at hdist1 hdist2
    simp only [Finset.mem_coe, Finset.mem_product]
    exact ⟨index_mem_window hMpow hzx1 hzx2 hdist1 le_rfl,
      index_mem_window hNpow hzy1 hzy2 hdist2 hRN⟩
  · intro c _ c' _ h
    exact index_pair_injective k h

theorem coverNum_grid_le_sup_SQ (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (ω : Ω)
    (k q : ℕ) (x : ℝ × ℝ) :
    coverNum (gridScale A.M (k + q))
        (limitSet X ω ∩ Metric.eball x (ENNReal.ofReal (gridScale A.M k))) ≤
      ((9 * A.N * (meetingCodes A x k).sup (SQ X ω k q) : ℕ) : ℕ∞) := by
  classical
  set T : Finset (SquareCode A (k + q)) :=
    (meetingCodes A x k).biUnion (fun c => occupiedExtensions X ω k q c) with hT
  set I : Finset (SquareCode A (k + q) × ℕ) := T ×ˢ Finset.range A.N with hI
  set C : Set (Set (ℝ × ℝ)) :=
    (fun p : SquareCode A (k + q) × ℕ => p.1.slice p.2) '' ↑I with hC
  have hcov : limitSet X ω ∩ Metric.eball x (ENNReal.ofReal (gridScale A.M k)) ⊆
      ⋃₀ C := by
    rintro z ⟨hzF, hzB⟩
    have hzlevel : z ∈ levelSet X ω (k + q) := Set.iInter_subset _ (k + q) hzF
    simp only [levelSet, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hzlevel
    obtain ⟨w, ⟨hwlen, hwret⟩, hzw⟩ := hzlevel
    set c' : SquareCode A (k + q) := wordCode w hwlen with hc'
    have hmem : c'.MemCell w := memCell_wordCode w hwlen
    have hzc' : z ∈ c'.region := rect_subset_region_of_memCell hmem hzw
    have hztr : z ∈ (c'.truncate (Nat.le_add_right k q)).region :=
      rect_subset_truncate_region _ hmem hzw
    have htrmem : c'.truncate (Nat.le_add_right k q) ∈ meetingCodes A x k :=
      mem_meetingCodes.mpr ⟨z, hztr, hzB⟩
    have hc'T : c' ∈ T :=
      Finset.mem_biUnion.mpr ⟨_, htrmem,
        mem_occupiedExtensions.mpr ⟨rfl, ⟨w, hmem, hwret⟩⟩⟩
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp (region_subset_iUnion_slice c' hzc')
    exact ⟨c'.slice i,
      ⟨(c', i), Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hc'T, hi⟩), rfl⟩, hzi⟩
  have hdiam : ∀ S ∈ C, Metric.ediam S ≤
      ENNReal.ofReal (gridScale A.M (k + q)) := by
    rintro S ⟨p, _, rfl⟩
    rw [gridScale_eq_inv_pow]
    exact ediam_slice_le p.1 p.2
  calc coverNum (gridScale A.M (k + q))
        (limitSet X ω ∩ Metric.eball x (ENNReal.ofReal (gridScale A.M k)))
      ≤ C.encard := coverNum_le_of_isCover hcov hdiam
    _ ≤ (↑I : Set (SquareCode A (k + q) × ℕ)).encard := Set.encard_image_le _ _
    _ = (I.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard I
    _ ≤ ((9 * A.N * (meetingCodes A x k).sup (SQ X ω k q) : ℕ) : ℕ∞) := by
        have hTcard : T.card ≤ 9 * (meetingCodes A x k).sup (SQ X ω k q) := by
          calc T.card ≤ ∑ c ∈ meetingCodes A x k,
                (occupiedExtensions X ω k q c).card := Finset.card_biUnion_le
            _ ≤ ∑ _c ∈ meetingCodes A x k,
                (meetingCodes A x k).sup (SQ X ω k q) :=
              Finset.sum_le_sum fun c hc => Finset.le_sup (f := SQ X ω k q) hc
            _ = (meetingCodes A x k).card *
                (meetingCodes A x k).sup (SQ X ω k q) := by
              rw [Finset.sum_const, smul_eq_mul]
            _ ≤ 9 * (meetingCodes A x k).sup (SQ X ω k q) :=
              Nat.mul_le_mul_right _ (card_meetingCodes_le_nine A x k)
        have hIcard : I.card = T.card * A.N := by
          rw [hI, Finset.card_product, Finset.card_range]
        have hfinal : I.card ≤ 9 * A.N * (meetingCodes A x k).sup (SQ X ω k q) := by
          calc I.card = T.card * A.N := hIcard
            _ ≤ 9 * (meetingCodes A x k).sup (SQ X ω k q) * A.N :=
              Nat.mul_le_mul_right _ hTcard
            _ = 9 * A.N * (meetingCodes A x k).sup (SQ X ω k q) := by ring
        exact_mod_cast hfinal

theorem coverNum_grid_le_univ_sup_SQ (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool)
    (ω : Ω) (k q : ℕ) (x : ℝ × ℝ) :
    coverNum (gridScale A.M (k + q))
        (limitSet X ω ∩ Metric.eball x (ENNReal.ofReal (gridScale A.M k))) ≤
      ((9 * A.N * (Finset.univ : Finset (SquareCode A k)).sup (SQ X ω k q) : ℕ) :
        ℕ∞) := by
  refine le_trans (coverNum_grid_le_sup_SQ X ω k q x) ?_
  have hle : (meetingCodes A x k).sup (SQ X ω k q) ≤
      (Finset.univ : Finset (SquareCode A k)).sup (SQ X ω k q) :=
    Finset.sup_mono (Finset.subset_univ _)
  exact_mod_cast Nat.mul_le_mul_left _ hle

def SquareCode.tailCols {k q : ℕ} (c' : SquareCode A (k + q)) : ColumnWord A q :=
  fun l => c'.col (Fin.natAdd k l)

noncomputable def occupiedCylinders (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool)
    (ω : Ω) (k q : ℕ) (c : SquareCode A k) (v : ColumnWord A q) :
    Finset (SquareCode A (k + q)) := by
  classical
  exact {c' : SquareCode A (k + q) |
    c' ∈ occupiedExtensions X ω k q c ∧ SquareCode.tailCols c' = v}.toFinset

lemma mem_occupiedCylinders {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}
    {ω : Ω} {k q : ℕ} {c : SquareCode A k} {v : ColumnWord A q}
    {c' : SquareCode A (k + q)} :
    c' ∈ occupiedCylinders X ω k q c v ↔
      c' ∈ occupiedExtensions X ω k q c ∧ SquareCode.tailCols c' = v := by
  simp [occupiedCylinders]

noncomputable def SC (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (ω : Ω)
    (k q : ℕ) (c : SquareCode A k) (v : ColumnWord A q) : ℕ :=
  (occupiedCylinders X ω k q c v).card

lemma SQ_eq_sum_SC (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (ω : Ω)
    (k q : ℕ) (c : SquareCode A k) :
    SQ X ω k q c = ∑ v : ColumnWord A q, SC X ω k q c v := by
  classical
  unfold SQ SC
  rw [Finset.card_eq_sum_card_fiberwise
    (f := SquareCode.tailCols) (t := Finset.univ) (fun c' _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  ext c'
  simp only [Finset.mem_filter, mem_occupiedCylinders]

lemma SC_eq_zero_of_not_allowed
    {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}
    {ω : Ω} (hω : ω ∉ badEvent X) (k q : ℕ) (c : SquareCode A k)
    {v : ColumnWord A q} (hv : ¬ ∀ l, v l ∈ A.cols) :
    SC X ω k q c v = 0 := by
  rw [SC, Finset.card_eq_zero]
  by_contra hne
  obtain ⟨c', hc'⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨hocc, htail⟩ := mem_occupiedCylinders.mp hc'
  obtain ⟨-, w, hmem, hret⟩ := mem_occupiedExtensions.mp hocc
  refine hv fun l => ?_
  have hlen : (k + (l : ℕ)) < w.length := by
    rw [hmem.1]
    have := l.isLt
    omega
  have hdigit : colD w ((Fin.natAdd k l : Fin (k + q)) : ℕ) =
      (c'.col (Fin.natAdd k l) : ℕ) := hmem.2.1 (Fin.natAdd k l)
  have hval : ((Fin.natAdd k l : Fin (k + q)) : ℕ) = k + (l : ℕ) := rfl
  rw [hval] at hdigit
  have hget : colD w (k + (l : ℕ)) = ((w.get ⟨k + (l : ℕ), hlen⟩).1 : ℕ) :=
    colD_eq_get w hlen
  have hallowed : Allowed A (w.get ⟨k + (l : ℕ), hlen⟩) :=
    allowed_of_retained hω hret _ (w.get_mem _)
  have hvl : v l = (w.get ⟨k + (l : ℕ), hlen⟩).1 := by
    have h1 : (v l : ℕ) = ((w.get ⟨k + (l : ℕ), hlen⟩).1 : ℕ) := by
      rw [← htail]
      show (c'.col (Fin.natAdd k l) : ℕ) = _
      rw [← hdigit, hget]
    exact Fin.ext h1
  rw [hvl]
  have hp : 0 < A.p (w.get ⟨k + (l : ℕ), hlen⟩).1 (w.get ⟨k + (l : ℕ), hlen⟩).2 :=
    hallowed
  simp only [GridLaw.cols, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨_, hp⟩

lemma SQ_le_Ax_pow_mul_sup_SC
    {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}
    {ω : Ω} (hω : ω ∉ badEvent X) (k q : ℕ) (c : SquareCode A k) :
    SQ X ω k q c ≤ A.Ax ^ q *
      (Finset.univ : Finset (ColumnWord A q)).sup (SC X ω k q c) := by
  classical
  rw [SQ_eq_sum_SC]
  have hzero : ∀ v ∈ (Finset.univ : Finset (ColumnWord A q)),
      v ∉ Fintype.piFinset (fun _ : Fin q => A.cols) → SC X ω k q c v = 0 := by
    intro v _ hv
    refine SC_eq_zero_of_not_allowed hω k q c fun hall => hv ?_
    exact Fintype.mem_piFinset.mpr hall
  rw [← Finset.sum_subset (Finset.subset_univ _) hzero]
  calc ∑ v ∈ Fintype.piFinset (fun _ : Fin q => A.cols), SC X ω k q c v
      ≤ (Fintype.piFinset (fun _ : Fin q => A.cols)).card •
        (Finset.univ : Finset (ColumnWord A q)).sup (SC X ω k q c) :=
      Finset.sum_le_card_nsmul _ _ _ fun v _ => Finset.le_sup (Finset.mem_univ v)
    _ = A.Ax ^ q *
        (Finset.univ : Finset (ColumnWord A q)).sup (SC X ω k q c) := by
      rw [smul_eq_mul]
      congr 1
      rw [Fintype.card_piFinset]
      simp [GridLaw.Ax_eq_card_cols]

end FractalGeometry.Probability.GridPercolation
