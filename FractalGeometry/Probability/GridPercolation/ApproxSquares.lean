import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Dimension.PhiAssouad.PlaneRectangles
import FractalGeometry.Probability.GridPercolation.DigitGeometry
import FractalGeometry.Probability.GridPercolation.Floor
import FractalGeometry.Probability.GridPercolation.GridCoveringReduction
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Process

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open Finset Set

open scoped ENNReal

namespace GridLaw

variable (A : GridLaw)

lemma one_le_M_real : (1 : ℝ) ≤ A.M := by
  exact_mod_cast le_trans (by norm_num) A.hM

lemma one_lt_N_real : (1 : ℝ) < A.N := by
  have h2 : 2 < A.N := lt_of_le_of_lt A.hM A.hMN
  exact_mod_cast lt_trans one_lt_two (by exact_mod_cast h2)

lemma bfloor_le (a : ℕ) : bfloor A.Gamma a ≤ a :=
  bfloor_le_self A.Gamma_lt_one.le a

lemma rpow_gamma_mul (a : ℕ) :
    (A.N : ℝ) ^ ((a : ℝ) * A.Gamma) = (A.M : ℝ) ^ (a : ℕ) := by
  have hN0 : (0 : ℝ) < A.N := by exact_mod_cast A.hN_pos
  have hM0 : (0 : ℝ) < A.M := by exact_mod_cast A.hM_pos
  have hlogN : Real.log A.N ≠ 0 := A.log_N_pos.ne'
  rw [← Real.rpow_natCast (A.M : ℝ) a]
  rw [Real.rpow_def_of_pos hN0, Real.rpow_def_of_pos hM0]
  congr 1
  rw [Gamma]
  field_simp

lemma pow_bfloor_le (a : ℕ) :
    (A.N : ℝ) ^ (bfloor A.Gamma a) ≤ (A.M : ℝ) ^ a := by
  have hN1 : (1 : ℝ) ≤ A.N := A.one_lt_N_real.le
  have hfloor : ((bfloor A.Gamma a : ℕ) : ℝ) ≤ (a : ℝ) * A.Gamma :=
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg a) A.Gamma_pos.le)
  calc (A.N : ℝ) ^ (bfloor A.Gamma a)
      = (A.N : ℝ) ^ ((bfloor A.Gamma a : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (A.N : ℝ) ^ ((a : ℝ) * A.Gamma) :=
        Real.rpow_le_rpow_of_exponent_le hN1 hfloor
    _ = (A.M : ℝ) ^ a := A.rpow_gamma_mul a

lemma lt_pow_bfloor_succ (a : ℕ) :
    (A.M : ℝ) ^ a < (A.N : ℝ) ^ (bfloor A.Gamma a + 1) := by
  have hN1 : (1 : ℝ) < A.N := A.one_lt_N_real
  have hlt : (a : ℝ) * A.Gamma < ((bfloor A.Gamma a + 1 : ℕ) : ℝ) := by
    push_cast
    exact Nat.lt_floor_add_one _
  calc (A.M : ℝ) ^ a = (A.N : ℝ) ^ ((a : ℝ) * A.Gamma) := (A.rpow_gamma_mul a).symm
    _ < (A.N : ℝ) ^ (((bfloor A.Gamma a + 1 : ℕ) : ℝ)) :=
        Real.rpow_lt_rpow_of_exponent_lt hN1 hlt
    _ = (A.N : ℝ) ^ (bfloor A.Gamma a + 1) := Real.rpow_natCast _ _

end GridLaw

lemma gridScale_eq_inv_pow (M k : ℕ) :
    gridScale M k = ((M : ℝ) ^ k)⁻¹ := by
  rw [gridScale, Real.rpow_neg (Nat.cast_nonneg M), Real.rpow_natCast]

variable {A : GridLaw}

def colD (w : Word A) (l : ℕ) : ℕ := (w.map fun p => ((p.1 : ℕ))).getD l 0

def rowD (w : Word A) (l : ℕ) : ℕ := (w.map fun p => ((p.2 : ℕ))).getD l 0

lemma colD_eq_get (w : Word A) {l : ℕ} (hl : l < w.length) :
    colD w l = ((w.get ⟨l, hl⟩).1 : ℕ) := by
  unfold colD
  rw [List.getD_eq_getElem _ _ (by simpa using hl)]
  simp

lemma rowD_eq_get (w : Word A) {l : ℕ} (hl : l < w.length) :
    rowD w l = ((w.get ⟨l, hl⟩).2 : ℕ) := by
  unfold rowD
  rw [List.getD_eq_getElem _ _ (by simpa using hl)]
  simp

lemma colD_lt (w : Word A) {l : ℕ} (hl : l < w.length) : colD w l < A.M := by
  rw [colD_eq_get w hl]
  exact (w.get ⟨l, hl⟩).1.isLt

lemma rowD_lt (w : Word A) {l : ℕ} (hl : l < w.length) : rowD w l < A.N := by
  rw [rowD_eq_get w hl]
  exact (w.get ⟨l, hl⟩).2.isLt

theorem rect_subset_digit_prod (w : Word A) :
    rect A w ⊆
      Set.Icc (digitLeft A.M (colD w) w.length)
          (digitLeft A.M (colD w) w.length + ((A.M : ℝ) ^ w.length)⁻¹) ×ˢ
        Set.Icc (digitLeft A.N (rowD w) w.length)
          (digitLeft A.N (rowD w) w.length + ((A.N : ℝ) ^ w.length)⁻¹) := by
  induction w with
  | nil =>
      intro z hz
      simp only [rect] at hz
      simpa [digitLeft, Set.mem_prod] using hz
  | cons p w ih =>
      intro z hz
      obtain ⟨y, hy, rfl⟩ := hz
      have hyb := ih hy
      obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩ := hyb
      have hM0 : (0 : ℝ) < A.M := by exact_mod_cast A.hM_pos
      have hN0 : (0 : ℝ) < A.N := by exact_mod_cast A.hN_pos
      have hcol : digitLeft A.M (colD (p :: w)) (w.length + 1) =
          (((p.1 : ℕ) : ℝ) + digitLeft A.M (colD w) w.length) / A.M := by
        rw [digitLeft_succ_head]
        congr 2
      have hrow : digitLeft A.N (rowD (p :: w)) (w.length + 1) =
          (((p.2 : ℕ) : ℝ) + digitLeft A.N (rowD w) w.length) / A.N := by
        rw [digitLeft_succ_head]
        congr 2
      have hlen : (p :: w).length = w.length + 1 := rfl
      rw [hlen]
      constructor
      · constructor
        · rw [hcol]
          exact div_le_div_of_nonneg_right (by linarith) hM0.le
        · rw [hcol]
          have hpow : ((A.M : ℝ) ^ (w.length + 1))⁻¹ =
              ((A.M : ℝ) ^ w.length)⁻¹ / A.M := by
            rw [pow_succ, mul_inv, div_eq_mul_inv]
          rw [hpow, ← add_div]
          exact div_le_div_of_nonneg_right (by linarith) hM0.le
      · constructor
        · rw [hrow]
          exact div_le_div_of_nonneg_right (by linarith) hN0.le
        · rw [hrow]
          have hpow : ((A.N : ℝ) ^ (w.length + 1))⁻¹ =
              ((A.N : ℝ) ^ w.length)⁻¹ / A.N := by
            rw [pow_succ, mul_inv, div_eq_mul_inv]
          rw [hpow, ← add_div]
          exact div_le_div_of_nonneg_right (by linarith) hN0.le

abbrev SquareCode (A : GridLaw) (a : ℕ) :=
  (Fin a → Fin A.M) × (Fin (bfloor A.Gamma a) → Fin A.N)

abbrev SquareCode.col {A : GridLaw} {a : ℕ} (c : SquareCode A a) : Fin a → Fin A.M := c.1

abbrev SquareCode.row {A : GridLaw} {a : ℕ} (c : SquareCode A a) :
    Fin (bfloor A.Gamma a) → Fin A.N := c.2

lemma card_squareCode (A : GridLaw) (a : ℕ) :
    Fintype.card (SquareCode A a) = A.M ^ a * A.N ^ (bfloor A.Gamma a) := by
  simp [SquareCode]

namespace SquareCode

def padDigits {n m : ℕ} (f : Fin n → Fin m) : ℕ → ℕ :=
  fun l => if h : l < n then (f ⟨l, h⟩ : ℕ) else 0

lemma padDigits_apply {n m : ℕ} (f : Fin n → Fin m) (l : Fin n) :
    padDigits f (l : ℕ) = (f l : ℕ) := by
  unfold padDigits
  rw [dite_eq_left l.isLt]

variable {a : ℕ}

noncomputable def xLeft (c : SquareCode A a) : ℝ :=
  digitLeft A.M (padDigits c.col) a

noncomputable def yLeft (c : SquareCode A a) : ℝ :=
  digitLeft A.N (padDigits c.row) (bfloor A.Gamma a)

noncomputable def region (c : SquareCode A a) : Set (ℝ × ℝ) :=
  Set.Icc c.xLeft (c.xLeft + ((A.M : ℝ) ^ a)⁻¹) ×ˢ
    Set.Icc c.yLeft (c.yLeft + ((A.N : ℝ) ^ (bfloor A.Gamma a))⁻¹)

def MemCell (c : SquareCode A a) (w : Word A) : Prop :=
  w.length = a ∧ (∀ l : Fin a, colD w l = c.col l) ∧
    (∀ l : Fin (bfloor A.Gamma a), rowD w l = c.row l)

end SquareCode

noncomputable def wordCode (w : Word A) {a : ℕ} (h : w.length = a) : SquareCode A a :=
  (fun l => (w.get (Fin.cast h.symm l)).1,
   fun l => (w.get (Fin.cast h.symm (Fin.castLE (A.bfloor_le a) l))).2)

lemma memCell_wordCode (w : Word A) {a : ℕ} (h : w.length = a) :
    (wordCode w h).MemCell w := by
  refine ⟨h, fun l => ?_, fun l => ?_⟩
  · rw [colD_eq_get w (by omega : (l : ℕ) < w.length)]
    rfl
  · have hl : (l : ℕ) < w.length := by
      have := l.isLt
      have := A.bfloor_le a
      omega
    rw [rowD_eq_get w hl]
    rfl

theorem rect_subset_region_of_compat {k : ℕ} (c : SquareCode A k) (w : Word A)
    (hk : k ≤ w.length)
    (hcol : ∀ l : Fin k, colD w l = c.col l)
    (hrow : ∀ l : Fin (bfloor A.Gamma k), rowD w l = c.row l) :
    rect A w ⊆ c.region := by
  have hbk : bfloor A.Gamma k ≤ k := A.bfloor_le k
  have hM1 : 1 ≤ A.M := le_trans (by norm_num) A.hM
  have hN1 : 1 ≤ A.N := le_of_lt (lt_of_le_of_lt (le_trans one_le_two A.hM) A.hMN)
  refine (rect_subset_digit_prod w).trans ?_
  have hxL : c.xLeft = digitLeft A.M (colD w) k := by
    refine (digitLeft_congr A.M k fun l hl => ?_).symm
    rw [hcol ⟨l, hl⟩]
    simp [SquareCode.padDigits, hl]
  have hyL : c.yLeft = digitLeft A.N (rowD w) (bfloor A.Gamma k) := by
    refine (digitLeft_congr A.N (bfloor A.Gamma k) fun l hl => ?_).symm
    rw [hrow ⟨l, hl⟩]
    simp [SquareCode.padDigits, hl]
  refine Set.prod_mono ?_ ?_
  · rw [hxL]
    intro t ht
    refine ⟨le_trans (digitLeft_mono A.M (colD w) hk) ht.1, le_trans ht.2 ?_⟩
    exact digitLeft_add_inv_le A.M hM1 (colD w) hk fun l _ hl => colD_lt w hl
  · rw [hyL]
    intro t ht
    have hblen : bfloor A.Gamma k ≤ w.length := le_trans hbk hk
    refine ⟨le_trans (digitLeft_mono A.N (rowD w) hblen) ht.1, le_trans ht.2 ?_⟩
    exact digitLeft_add_inv_le A.N hN1 (rowD w) hblen fun l _ hl => rowD_lt w hl

theorem rect_subset_region_of_memCell {a : ℕ} {c : SquareCode A a} {w : Word A}
    (hmem : c.MemCell w) : rect A w ⊆ c.region :=
  rect_subset_region_of_compat c w hmem.1.ge hmem.2.1 hmem.2.2

variable {Ω : Type*}

noncomputable def colIndex {k : ℕ} (c : SquareCode A k) : ℕ :=
  (finFunctionFinEquiv (fun i => c.col i.rev) : ℕ)

noncomputable def rowIndex {k : ℕ} (c : SquareCode A k) : ℕ :=
  (finFunctionFinEquiv (fun i => c.row i.rev) : ℕ)

lemma finFunctionFinEquiv_rev_eq_digitIndex {n m : ℕ} (f : Fin n → Fin m) :
    (finFunctionFinEquiv (fun i => f i.rev) : ℕ) =
      digitIndex m (SquareCode.padDigits f) n := by
  rw [finFunctionFinEquiv_apply]
  unfold digitIndex
  rw [← Fin.sum_univ_eq_sum_range fun l => SquareCode.padDigits f l * m ^ (n - 1 - l)]
  refine Fintype.sum_equiv (Fin.revPerm) _ _ fun i => ?_
  show ((f i.rev : Fin m) : ℕ) * m ^ (i : ℕ) =
    SquareCode.padDigits f ((Fin.revPerm i : Fin n) : ℕ) *
      m ^ (n - 1 - ((Fin.revPerm i : Fin n) : ℕ))
  simp only [Fin.revPerm_apply]
  have h1 : ((i.rev : Fin n) : ℕ) = n - 1 - (i : ℕ) := by
    rw [Fin.val_rev]
    omega
  have h2 : SquareCode.padDigits f ((i.rev : Fin n) : ℕ) = ((f i.rev : Fin m) : ℕ) :=
    SquareCode.padDigits_apply f i.rev
  have h3 : n - 1 - (n - 1 - (i : ℕ)) = (i : ℕ) := by
    have := i.isLt
    omega
  rw [h2, h1, h3]

lemma SquareCode.xLeft_eq_colIndex_div {k : ℕ} (c : SquareCode A k) :
    c.xLeft = (colIndex c : ℝ) / (A.M : ℝ) ^ k := by
  rw [xLeft, digitLeft_eq_digitIndex_div A.M (le_trans one_le_two A.hM) _ k,
    colIndex, finFunctionFinEquiv_rev_eq_digitIndex]

lemma SquareCode.yLeft_eq_rowIndex_div {k : ℕ} (c : SquareCode A k) :
    c.yLeft = (rowIndex c : ℝ) / (A.N : ℝ) ^ (bfloor A.Gamma k) := by
  have hN1 : 1 ≤ A.N := le_of_lt (lt_of_le_of_lt (le_trans one_le_two A.hM) A.hMN)
  rw [yLeft, digitLeft_eq_digitIndex_div A.N hN1 _ (bfloor A.Gamma k),
    rowIndex, finFunctionFinEquiv_rev_eq_digitIndex]

lemma index_pair_injective (k : ℕ) :
    Function.Injective fun c : SquareCode A k => (colIndex c, rowIndex c) := by
  intro c c' h
  have hcol : colIndex c = colIndex c' := congrArg Prod.fst h
  have hrow : rowIndex c = rowIndex c' := congrArg Prod.snd h
  have hcol' : (fun i : Fin k => c.col i.rev) = fun i : Fin k => c'.col i.rev := by
    apply finFunctionFinEquiv.injective
    exact Fin.val_injective hcol
  have hrow' : (fun i : Fin (bfloor A.Gamma k) => c.row i.rev) =
      fun i : Fin (bfloor A.Gamma k) => c'.row i.rev := by
    apply finFunctionFinEquiv.injective
    exact Fin.val_injective hrow
  have hcolEq : c.col = c'.col := by
    funext l
    have h5 := congrFun hcol' l.rev
    simpa [Fin.rev_rev] using h5
  have hrowEq : c.row = c'.row := by
    funext l
    have h5 := congrFun hrow' l.rev
    simpa [Fin.rev_rev] using h5
  exact Prod.ext hcolEq hrowEq

noncomputable def SquareCode.slice {a : ℕ} (c : SquareCode A a) (i : ℕ) : Set (ℝ × ℝ) :=
  Set.Icc c.xLeft (c.xLeft + ((A.M : ℝ) ^ a)⁻¹) ×ˢ
    Set.Icc (c.yLeft + (i : ℝ) * ((A.M : ℝ) ^ a)⁻¹)
      (c.yLeft + ((i : ℝ) + 1) * ((A.M : ℝ) ^ a)⁻¹)

lemma ediam_slice_le {a : ℕ} (c : SquareCode A a) (i : ℕ) :
    Metric.ediam (c.slice i) ≤ ENNReal.ofReal ((A.M : ℝ) ^ a)⁻¹ := by
  apply ediam_prod_Icc_le
  · have h : c.xLeft + ((A.M : ℝ) ^ a)⁻¹ - c.xLeft = ((A.M : ℝ) ^ a)⁻¹ := by ring
    rw [h]
  · have h : c.yLeft + ((i : ℝ) + 1) * ((A.M : ℝ) ^ a)⁻¹ -
        (c.yLeft + (i : ℝ) * ((A.M : ℝ) ^ a)⁻¹) = ((A.M : ℝ) ^ a)⁻¹ := by ring
    rw [h]

lemma region_subset_iUnion_slice {a : ℕ} (c : SquareCode A a) :
    c.region ⊆ ⋃ i ∈ Finset.range A.N, c.slice i := by
  rintro z ⟨⟨hzx1, hzx2⟩, ⟨hzy1, hzy2⟩⟩
  have hM0 : (0 : ℝ) < A.M := by exact_mod_cast A.hM_pos
  have hN0 : (0 : ℝ) < A.N := by exact_mod_cast A.hN_pos
  have hMpow : (0 : ℝ) < (A.M : ℝ) ^ a := by positivity
  have hNpow : (0 : ℝ) < (A.N : ℝ) ^ (bfloor A.Gamma a) := by positivity
  set v : ℝ := ((A.M : ℝ) ^ a)⁻¹ with hv
  have hv0 : 0 < v := by positivity
  have hcancel : (A.M : ℝ) ^ a * v = 1 := mul_inv_cancel₀ hMpow.ne'
  set u : ℝ := z.2 - c.yLeft with hu
  have hu0 : 0 ≤ u := by simp only [hu]; linarith
  have huN : u ≤ ((A.N : ℝ) ^ (bfloor A.Gamma a))⁻¹ := by simp only [hu]; linarith
  have hheight : ((A.N : ℝ) ^ (bfloor A.Gamma a))⁻¹ ≤ (A.N : ℝ) * v := by
    have hMN : (A.M : ℝ) ^ a ≤ (A.N : ℝ) ^ (bfloor A.Gamma a) * A.N := by
      have h := (A.lt_pow_bfloor_succ a).le
      rwa [pow_succ] at h
    have hgoal : (1 : ℝ) / (A.N : ℝ) ^ (bfloor A.Gamma a) ≤
        (A.N : ℝ) / (A.M : ℝ) ^ a := by
      rw [div_le_div_iff₀ hNpow hMpow]
      nlinarith
    calc ((A.N : ℝ) ^ (bfloor A.Gamma a))⁻¹
        = 1 / (A.N : ℝ) ^ (bfloor A.Gamma a) := (one_div _).symm
      _ ≤ (A.N : ℝ) / (A.M : ℝ) ^ a := hgoal
      _ = (A.N : ℝ) * v := by rw [hv, div_eq_mul_inv]
  set i0 : ℕ := min ⌊u * (A.M : ℝ) ^ a⌋₊ (A.N - 1) with hi0
  have hNpos : 0 < A.N := A.hN_pos
  have hi0N : i0 < A.N := by
    have : i0 ≤ A.N - 1 := min_le_right _ _
    omega
  have hlower : (i0 : ℝ) * v ≤ u := by
    have h1 : (i0 : ℝ) ≤ u * (A.M : ℝ) ^ a := by
      calc (i0 : ℝ) ≤ (⌊u * (A.M : ℝ) ^ a⌋₊ : ℝ) :=
            Nat.cast_le.mpr (min_le_left _ _)
        _ ≤ u * (A.M : ℝ) ^ a := Nat.floor_le (by positivity)
    calc (i0 : ℝ) * v ≤ u * (A.M : ℝ) ^ a * v :=
          mul_le_mul_of_nonneg_right h1 hv0.le
      _ = u * ((A.M : ℝ) ^ a * v) := by ring
      _ = u := by rw [hcancel, mul_one]
  have hupper : u ≤ ((i0 : ℝ) + 1) * v := by
    rcases le_total (⌊u * (A.M : ℝ) ^ a⌋₊) (A.N - 1) with hcase | hcase
    · have hi0eq : i0 = ⌊u * (A.M : ℝ) ^ a⌋₊ := min_eq_left hcase
      have h1 : u * (A.M : ℝ) ^ a < (i0 : ℝ) + 1 := by
        rw [hi0eq]
        exact Nat.lt_floor_add_one _
      calc u = u * ((A.M : ℝ) ^ a * v) := by rw [hcancel, mul_one]
        _ = u * (A.M : ℝ) ^ a * v := by ring
        _ ≤ ((i0 : ℝ) + 1) * v := mul_le_mul_of_nonneg_right h1.le hv0.le
    · have hi0eq : i0 = A.N - 1 := min_eq_right hcase
      have h1 : ((i0 : ℝ) + 1) = (A.N : ℝ) := by
        rw [hi0eq]
        have h2 : (A.N - 1 : ℕ) + 1 = A.N := by omega
        exact_mod_cast h2
      rw [h1]
      exact le_trans huN hheight
  refine Set.mem_iUnion₂.mpr ⟨i0, Finset.mem_range.mpr hi0N, ?_⟩
  refine ⟨⟨hzx1, hzx2⟩, ?_, ?_⟩
  · simp only [hu] at hlower
    linarith
  · simp only [hu] at hupper
    linarith

end FractalGeometry.Probability.GridPercolation
