import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Assouad
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.ApproxSquares
import FractalGeometry.Probability.GridPercolation.AssouadGridBounds
import FractalGeometry.Probability.GridPercolation.ColumnCardinality
import FractalGeometry.Probability.GridPercolation.Floor
import FractalGeometry.Probability.GridPercolation.GridCoveringReduction
import FractalGeometry.Probability.GridPercolation.Lambda
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.Processes
import FractalGeometry.Probability.GridPercolation.RefinementCounts
import FractalGeometry.Probability.GridPercolation.Support
import FractalGeometry.Probability.GridPercolation.UnitSquare

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open Filter MeasureTheory

open scoped ENNReal

variable {A : GridLaw} {Ω : Type*}

lemma SquareCode.col_eq_append {k q : ℕ} {c : SquareCode A k} {v : ColumnWord A q}
    {c' : SquareCode A (k + q)} (htr : c'.truncate (Nat.le_add_right k q) = c)
    (htail : SquareCode.tailCols c' = v) :
    c'.col = Fin.append c.col v := by
  subst htr htail
  funext i
  induction i using Fin.addCases with
  | left l =>
      exact (Fin.append_left (c'.truncate (Nat.le_add_right k q)).col
        (SquareCode.tailCols c') l).symm
  | right l =>
      exact (Fin.append_right (c'.truncate (Nat.le_add_right k q)).col
        (SquareCode.tailCols c') l).symm

lemma SquareCode.row_mem_rows_of_occupied {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}
    {ω : Ω} (hω : ω ∉ badEvent X) {a : ℕ} {c : SquareCode A a} (hocc : c.Occupied X ω)
    (j : Fin (bfloor A.Gamma a)) :
    c.row j ∈ A.rows (c.col (Fin.castLE (A.bfloor_le a) j)) := by
  obtain ⟨w, ⟨hlen, hcol, hrow⟩, hret⟩ := hocc
  have hj : (j : ℕ) < w.length := by
    rw [hlen]
    exact lt_of_lt_of_le j.isLt (A.bfloor_le a)
  have hallowed : Allowed A (w.get ⟨j, hj⟩) := allowed_of_retained hω hret _ (w.get_mem _)
  have h1 : c.col (Fin.castLE (A.bfloor_le a) j) = (w.get ⟨j, hj⟩).1 := by
    apply Fin.ext
    rw [← colD_eq_get w hj]
    exact (hcol (Fin.castLE (A.bfloor_le a) j)).symm
  have h2 : c.row j = (w.get ⟨j, hj⟩).2 := by
    apply Fin.ext
    rw [← rowD_eq_get w hj]
    exact (hrow j).symm
  rw [h1, h2]
  simp only [GridLaw.rows, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hallowed

noncomputable def newRowPos (A : GridLaw) (k q : ℕ)
    (j : Fin (bfloor A.Gamma (k + q) - bfloor A.Gamma k)) : Fin (bfloor A.Gamma (k + q)) :=
  ⟨bfloor A.Gamma k + j, by have := j.isLt; omega⟩

theorem SC_le_Bmax_pow {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool} {ω : Ω}
    (hω : ω ∉ badEvent X) (k q : ℕ) (c : SquareCode A k) (v : ColumnWord A q) :
    SC X ω k q c v ≤ A.Bmax ^ (bfloor A.Gamma (k + q) - bfloor A.Gamma k) := by
  classical
  set T : Finset (Fin (bfloor A.Gamma (k + q) - bfloor A.Gamma k) → Fin A.N) :=
    Fintype.piFinset fun j =>
      A.rows (Fin.append c.col v (Fin.castLE (A.bfloor_le (k + q)) (newRowPos A k q j)))
    with hT
  set f : SquareCode A (k + q) → Fin (bfloor A.Gamma (k + q) - bfloor A.Gamma k) → Fin A.N :=
    fun c' j => c'.row (newRowPos A k q j) with hf
  have hmaps : ∀ c' ∈ occupiedCylinders X ω k q c v, f c' ∈ T := by
    intro c' hc'
    obtain ⟨hext, htail⟩ := mem_occupiedCylinders.mp hc'
    obtain ⟨htr, hocc⟩ := mem_occupiedExtensions.mp hext
    refine Fintype.mem_piFinset.mpr fun j => ?_
    have h := SquareCode.row_mem_rows_of_occupied hω hocc (newRowPos A k q j)
    rw [SquareCode.col_eq_append htr htail] at h
    exact h
  have hinj : Set.InjOn f (occupiedCylinders X ω k q c v : Set (SquareCode A (k + q))) := by
    intro c₁ hc₁ c₂ hc₂ hf₁₂
    obtain ⟨hext₁, htail₁⟩ := mem_occupiedCylinders.mp (Finset.mem_coe.mp hc₁)
    obtain ⟨htr₁, -⟩ := mem_occupiedExtensions.mp hext₁
    obtain ⟨hext₂, htail₂⟩ := mem_occupiedCylinders.mp (Finset.mem_coe.mp hc₂)
    obtain ⟨htr₂, -⟩ := mem_occupiedExtensions.mp hext₂
    refine Prod.ext ?_ ?_
    · show c₁.col = c₂.col
      rw [SquareCode.col_eq_append htr₁ htail₁, SquareCode.col_eq_append htr₂ htail₂]
    · funext i
      by_cases hi : (i : ℕ) < bfloor A.Gamma k
      · have e₁ : c₁.row i = c.row ⟨i, hi⟩ := congrFun (congrArg Prod.snd htr₁) ⟨i, hi⟩
        have e₂ : c₂.row i = c.row ⟨i, hi⟩ := congrFun (congrArg Prod.snd htr₂) ⟨i, hi⟩
        exact e₁.trans e₂.symm
      · have hj : (i : ℕ) - bfloor A.Gamma k < bfloor A.Gamma (k + q) - bfloor A.Gamma k := by
          have := i.isLt
          omega
        have e : c₁.row (newRowPos A k q ⟨i - bfloor A.Gamma k, hj⟩) =
            c₂.row (newRowPos A k q ⟨i - bfloor A.Gamma k, hj⟩) :=
          congrFun hf₁₂ ⟨i - bfloor A.Gamma k, hj⟩
        have hpos : newRowPos A k q ⟨i - bfloor A.Gamma k, hj⟩ = i := by
          apply Fin.ext
          show bfloor A.Gamma k + (i - bfloor A.Gamma k) = i
          omega
        rw [hpos] at e
        exact e
  calc SC X ω k q c v = (occupiedCylinders X ω k q c v).card := rfl
    _ ≤ T.card := Finset.card_le_card_of_injOn f hmaps hinj
    _ = ∏ j, (A.rows (Fin.append c.col v
          (Fin.castLE (A.bfloor_le (k + q)) (newRowPos A k q j)))).card :=
        Fintype.card_piFinset _
    _ ≤ ∏ _j : Fin (bfloor A.Gamma (k + q) - bfloor A.Gamma k), A.Bmax :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) fun j _ => A.B_le_Bmax _
    _ = A.Bmax ^ (bfloor A.Gamma (k + q) - bfloor A.Gamma k) := by simp

theorem SQ_le_Ax_pow_mul_Bmax_pow {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool} {ω : Ω}
    (hω : ω ∉ badEvent X) (k q : ℕ) (c : SquareCode A k) :
    SQ X ω k q c ≤ A.Ax ^ q * A.Bmax ^ (bfloor A.Gamma (k + q) - bfloor A.Gamma k) :=
  le_trans (SQ_le_Ax_pow_mul_sup_SC hω k q c)
    (Nat.mul_le_mul_left _ (Finset.sup_le fun v _ => SC_le_Bmax_pow hω k q c v))

lemma GridLaw.rpow_sAdet_eq (A : GridLaw) (hm : 1 < A.m) (q : ℕ) :
    ((A.M : ℝ) ^ (q : ℝ)) ^ A.sAdet =
      (A.Ax : ℝ) ^ q * (A.Bmax : ℝ) ^ ((q : ℝ) * A.Gamma) := by
  have hM0 : (0 : ℝ) < A.M := by exact_mod_cast A.hM_pos
  have hAx0 : (0 : ℝ) < A.Ax := by exact_mod_cast A.one_le_Ax hm
  have hB0 : (0 : ℝ) < A.Bmax := by exact_mod_cast A.Bmax_pos_of_m_pos (by linarith)
  have hlogM : Real.log A.M ≠ 0 := A.log_M_pos.ne'
  have hlogN : Real.log A.N ≠ 0 := A.log_N_pos.ne'
  rw [← Real.rpow_natCast (A.Ax : ℝ) q, Real.rpow_def_of_pos (Real.rpow_pos_of_pos hM0 _),
    Real.log_rpow hM0, Real.rpow_def_of_pos hAx0, Real.rpow_def_of_pos hB0, ← Real.exp_add]
  congr 1
  rw [GridLaw.sAdet, GridLaw.Gamma]
  field_simp

theorem SQ_le_Bmax_mul_rpow_sAdet (hm : 1 < A.m)
    {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool} {ω : Ω} (hω : ω ∉ badEvent X)
    (k q : ℕ) (c : SquareCode A k) :
    (SQ X ω k q c : ℝ) ≤ A.Bmax * ((A.M : ℝ) ^ (q : ℝ)) ^ A.sAdet := by
  have hB1 : (1 : ℝ) ≤ A.Bmax := by exact_mod_cast A.Bmax_pos_of_m_pos (by linarith)
  have hB0 : (0 : ℝ) < A.Bmax := by linarith
  have hb : bfloor A.Gamma k ≤ bfloor A.Gamma (k + q) := A.bfloor_mono (Nat.le_add_right k q)
  have hΔ : ((bfloor A.Gamma (k + q) - bfloor A.Gamma k : ℕ) : ℝ) ≤ (q : ℝ) * A.Gamma + 1 := by
    rw [Nat.cast_sub hb]
    have h1 : (bfloor A.Gamma (k + q) : ℝ) ≤ ((k + q : ℕ) : ℝ) * A.Gamma :=
      Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) A.Gamma_pos.le)
    have h2 : (k : ℝ) * A.Gamma < bfloor A.Gamma k + 1 := Nat.lt_floor_add_one _
    push_cast at h1
    linarith
  have hpow : (A.Bmax : ℝ) ^ (bfloor A.Gamma (k + q) - bfloor A.Gamma k) ≤
      A.Bmax * (A.Bmax : ℝ) ^ ((q : ℝ) * A.Gamma) := by
    calc (A.Bmax : ℝ) ^ (bfloor A.Gamma (k + q) - bfloor A.Gamma k)
        = (A.Bmax : ℝ) ^ ((bfloor A.Gamma (k + q) - bfloor A.Gamma k : ℕ) : ℝ) :=
          (Real.rpow_natCast _ _).symm
      _ ≤ (A.Bmax : ℝ) ^ ((q : ℝ) * A.Gamma + 1) := Real.rpow_le_rpow_of_exponent_le hB1 hΔ
      _ = A.Bmax * (A.Bmax : ℝ) ^ ((q : ℝ) * A.Gamma) := by
          rw [Real.rpow_add hB0, Real.rpow_one, mul_comm]
  calc (SQ X ω k q c : ℝ)
      ≤ (A.Ax : ℝ) ^ q * (A.Bmax : ℝ) ^ (bfloor A.Gamma (k + q) - bfloor A.Gamma k) := by
        exact_mod_cast SQ_le_Ax_pow_mul_Bmax_pow hω k q c
    _ ≤ (A.Ax : ℝ) ^ q * (A.Bmax * (A.Bmax : ℝ) ^ ((q : ℝ) * A.Gamma)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = A.Bmax * ((A.M : ℝ) ^ (q : ℝ)) ^ A.sAdet := by
        rw [A.rpow_sAdet_eq hm q]
        ring

theorem dimA_limitSet_le_sAdet (hm : 1 < A.m)
    {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool} {ω : Ω} (hω : ω ∉ badEvent X) :
    dimA (limitSet X ω) ≤ A.sAdet := by
  have hB0 : (0 : ℝ) < A.Bmax := by exact_mod_cast A.Bmax_pos_of_m_pos (by linarith)
  have hN0 : (0 : ℝ) < A.N := by exact_mod_cast A.hN_pos
  have hs : 0 ≤ A.sAdet := by
    have h1 : 0 ≤ Real.log A.Ax := Real.log_nonneg (by exact_mod_cast A.one_le_Ax hm)
    have h2 : 0 ≤ Real.log A.Bmax :=
      Real.log_nonneg (by exact_mod_cast A.Bmax_pos_of_m_pos (by linarith))
    exact add_nonneg (div_nonneg h1 A.log_M_pos.le) (div_nonneg h2 A.log_N_pos.le)
  refine dimA_le_of_eventually_grid_bound A.hM (limitSet_subset_unitSquare X ω) hs
    (show (0 : ℝ) < 9 * A.N * A.Bmax by positivity) 0 fun k _ q x _ => ?_
  have hbound0 : 0 ≤ (A.Bmax : ℝ) * ((A.M : ℝ) ^ (q : ℝ)) ^ A.sAdet := by positivity
  have hsup : (((Finset.univ : Finset (SquareCode A k)).sup (SQ X ω k q) : ℕ) : ℝ) ≤
      A.Bmax * ((A.M : ℝ) ^ (q : ℝ)) ^ A.sAdet := by
    have hle : (Finset.univ : Finset (SquareCode A k)).sup (SQ X ω k q) ≤
        ⌊(A.Bmax : ℝ) * ((A.M : ℝ) ^ (q : ℝ)) ^ A.sAdet⌋₊ :=
      Finset.sup_le fun c _ => Nat.le_floor (SQ_le_Bmax_mul_rpow_sAdet hm hω k q c)
    exact le_trans (by exact_mod_cast hle) (Nat.floor_le hbound0)
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal
    (show (((9 * A.N * (Finset.univ : Finset (SquareCode A k)).sup (SQ X ω k q) : ℕ) : ℝ)) ≤
      9 * A.N * A.Bmax * ((A.M : ℝ) ^ (q : ℝ)) ^ A.sAdet from ?_))
  · have hcast : (↑(coverNum (gridScale A.M (k + q))
        (limitSet X ω ∩ Metric.eball x (ENNReal.ofReal (gridScale A.M k)))) : ℝ≥0∞) ≤
        ((9 * A.N * (Finset.univ : Finset (SquareCode A k)).sup (SQ X ω k q) : ℕ) :
          ℝ≥0∞) := by
      exact_mod_cast coverNum_grid_le_univ_sup_SQ X ω k q x
    refine le_trans hcast ?_
    rw [← ENNReal.ofReal_natCast]
  · push_cast
    nlinarith [hsup, hN0]

end FractalGeometry.Probability.GridPercolation
