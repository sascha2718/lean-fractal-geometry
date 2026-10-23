import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.Law

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open Finset Set

namespace GridLaw

variable (A : GridLaw)

lemma E_pos_of_mem_cols {i : Fin A.M} (hi : i ∈ A.cols) : 0 < A.E i :=
  (A.mem_cols_iff i).mp hi

lemma continuous_colSum : Continuous A.colSum := by
  refine continuous_finsetSum _ fun i hi => ?_
  exact Real.continuous_const_rpow (A.E_pos_of_mem_cols hi).ne'

lemma colSum_image_nonempty : (A.colSum '' Set.Icc 0 1).Nonempty :=
  ⟨A.colSum 0, ⟨0, by norm_num, rfl⟩⟩

lemma bddBelow_colSum_image : BddBelow (A.colSum '' Set.Icc 0 1) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨β, -, rfl⟩
  exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (A.E_nonneg i) _

lemma lam_isMinOn : ∃ β ∈ Set.Icc (0:ℝ) 1, A.colSum β = A.lam ∧
    ∀ γ ∈ Set.Icc (0:ℝ) 1, A.colSum β ≤ A.colSum γ := by
  obtain ⟨β, hβmem, hβmin⟩ :=
    isCompact_Icc.exists_isMinOn (s := Set.Icc (0:ℝ) 1) ⟨0, by norm_num⟩
      A.continuous_colSum.continuousOn
  have hmin : ∀ γ ∈ Set.Icc (0:ℝ) 1, A.colSum β ≤ A.colSum γ := fun γ hγ => hβmin hγ
  refine ⟨β, hβmem, ?_, hmin⟩
  rw [A.lam_eq_sInf_colSum]
  refine le_antisymm ?_ ?_
  · exact le_csInf A.colSum_image_nonempty (by rintro _ ⟨γ, hγ, rfl⟩; exact hmin γ hγ)
  · exact csInf_le A.bddBelow_colSum_image ⟨β, hβmem, rfl⟩

lemma colSum_zero : A.colSum 0 = A.Ax := by
  simp [colSum, Real.rpow_zero, Ax_eq_card_cols]

lemma colSum_one : A.colSum 1 = A.m := by
  have : ∑ i ∈ A.cols, A.E i = ∑ i, A.E i := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro i _ hi
    by_contra hne
    exact hi ((A.mem_cols_iff i).mpr (lt_of_le_of_ne (A.E_nonneg i) (Ne.symm hne)))
  simpa [colSum, Real.rpow_one, m] using this

lemma rpow_sum_le_sum_rpow {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) : (∑ i ∈ s, a i) ^ β ≤ ∑ i ∈ s, (a i) ^ β := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow hβ0.ne']
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have hai : 0 ≤ a i := ha i (Finset.mem_insert_self i s)
      have hs : ∀ j ∈ s, 0 ≤ a j := fun j hj => ha j (Finset.mem_insert_of_mem hj)
      have hsum : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg hs
      calc (a i + ∑ j ∈ s, a j) ^ β ≤ (a i) ^ β + (∑ j ∈ s, a j) ^ β :=
            Real.rpow_add_le_add_rpow hai hsum hβ0.le hβ1
        _ ≤ (a i) ^ β + ∑ j ∈ s, (a j) ^ β := by gcongr; exact ih hs

lemma rpow_m_le_colSum {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) : A.m ^ β ≤ A.colSum β := by
  have hm : A.m = ∑ i ∈ A.cols, A.E i := by
    rw [← A.colSum_one]; simp [colSum, Real.rpow_one]
  rw [hm]
  exact rpow_sum_le_sum_rpow A.cols A.E (fun i _ => A.E_nonneg i) hβ0 hβ1

lemma cols_nonempty (hm : 1 < A.m) : A.cols.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have : A.m = 0 := by rw [← A.colSum_one]; simp [colSum, h]
  linarith

lemma one_le_Ax (hm : 1 < A.m) : 1 ≤ A.Ax :=
  Finset.card_pos.mpr (A.cols_nonempty hm)

lemma one_le_colSum (hm : 1 < A.m) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    1 ≤ A.colSum β := by
  rcases hβ0.eq_or_lt with rfl | hβpos
  · rw [A.colSum_zero]
    exact_mod_cast A.one_le_Ax hm
  · calc (1:ℝ) = 1 ^ β := (Real.one_rpow β).symm
      _ ≤ A.m ^ β := Real.rpow_le_rpow (by norm_num) hm.le hβpos.le
      _ ≤ A.colSum β := A.rpow_m_le_colSum hβpos hβ1

lemma one_le_lam (hm : 1 < A.m) : 1 ≤ A.lam := by
  obtain ⟨β, hβ, hval, -⟩ := A.lam_isMinOn
  rw [← hval]
  exact A.one_le_colSum hm hβ.1 hβ.2

lemma lam_pos (hm : 1 < A.m) : 0 < A.lam := lt_of_lt_of_le zero_lt_one (A.one_le_lam hm)

end GridLaw

end FractalGeometry.Probability.GridPercolation
