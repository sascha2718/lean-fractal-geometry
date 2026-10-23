import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open Finset

structure GridLaw where

  M : ℕ

  N : ℕ

  hM : 2 ≤ M

  hMN : M < N

  p : Fin M → Fin N → ℝ

  p_nonneg : ∀ i j, 0 ≤ p i j

  p_le_one : ∀ i j, p i j ≤ 1

namespace GridLaw

variable (A : GridLaw)

lemma hM_pos : 0 < A.M := lt_of_lt_of_le (by norm_num) A.hM

lemma hN_pos : 0 < A.N := lt_trans A.hM_pos A.hMN

instance : NeZero A.M := ⟨A.hM_pos.ne'⟩
instance : NeZero A.N := ⟨A.hN_pos.ne'⟩
instance : Nonempty (Fin A.M) := Fin.pos_iff_nonempty.mp A.hM_pos
instance : Nonempty (Fin A.N) := Fin.pos_iff_nonempty.mp A.hN_pos

def E (i : Fin A.M) : ℝ := ∑ j, A.p i j

def m : ℝ := ∑ i, A.E i

lemma E_nonneg (i : Fin A.M) : 0 ≤ A.E i := Finset.sum_nonneg fun j _ => A.p_nonneg i j

lemma m_nonneg : 0 ≤ A.m := Finset.sum_nonneg fun i _ => A.E_nonneg i

noncomputable def cols : Finset (Fin A.M) := {i | ∃ j, 0 < A.p i j}

noncomputable def Ax : ℕ := #{i | ∃ j, 0 < A.p i j}

lemma Ax_eq_card_cols : A.Ax = A.cols.card := rfl

lemma mem_cols_iff (i : Fin A.M) : i ∈ A.cols ↔ 0 < A.E i := by
  simp only [cols, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    exact Finset.sum_pos' (fun j _ => A.p_nonneg i j) ⟨j, Finset.mem_univ j, hj⟩
  · intro h
    by_contra hc
    push Not at hc
    have : A.E i ≤ 0 := Finset.sum_nonpos fun j _ => hc j
    linarith

noncomputable def colSum (β : ℝ) : ℝ := ∑ i ∈ A.cols, (A.E i) ^ β

noncomputable def lam : ℝ :=
  sInf ((fun β : ℝ => ∑ i with 0 < A.E i, A.E i ^ β) '' Set.Icc 0 1)

lemma cols_eq_filter : A.cols = ({i | 0 < A.E i} : Finset (Fin A.M)) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← A.mem_cols_iff]

lemma lam_eq_sInf_colSum : A.lam = sInf (A.colSum '' Set.Icc 0 1) := by
  have h : A.colSum = fun β : ℝ => ∑ i with 0 < A.E i, A.E i ^ β := by
    funext β
    rw [colSum, cols_eq_filter]
  rw [h, lam]

noncomputable def sproj : ℝ := Real.log A.lam / Real.log A.M

noncomputable def Gamma : ℝ := Real.log A.M / Real.log A.N

noncomputable def sbox : ℝ :=
  Real.log A.m / Real.log A.N + (1 - A.Gamma) * A.sproj

lemma log_M_pos : 0 < Real.log A.M :=
  Real.log_pos (by exact_mod_cast lt_of_lt_of_le (by norm_num) A.hM)

lemma log_N_pos : 0 < Real.log A.N :=
  Real.log_pos (by exact_mod_cast lt_trans (lt_of_lt_of_le (by norm_num) A.hM) A.hMN)

lemma log_M_lt_log_N : Real.log A.M < Real.log A.N := by
  refine Real.log_lt_log ?_ ?_
  · exact_mod_cast A.hM_pos
  · exact_mod_cast A.hMN

lemma Gamma_pos : 0 < A.Gamma := div_pos A.log_M_pos A.log_N_pos

lemma Gamma_lt_one : A.Gamma < 1 := by
  rw [Gamma, div_lt_one A.log_N_pos]; exact A.log_M_lt_log_N

end GridLaw

end FractalGeometry.Probability.GridPercolation
