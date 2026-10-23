import Mathlib
import FractalGeometry.Probability.GridPercolation.Law

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open Finset

namespace GridLaw

variable (A : GridLaw)

noncomputable def rows (i : Fin A.M) : Finset (Fin A.N) := {j | 0 < A.p i j}

noncomputable def B (i : Fin A.M) : ℕ := #{j | 0 < A.p i j}

lemma B_eq_card_rows (i : Fin A.M) : A.B i = (A.rows i).card := rfl

noncomputable def Bmax : ℕ := ⨆ i, A.B i

lemma Bmax_eq_sup : A.Bmax = Finset.univ.sup A.B := (Finset.sup_univ_eq_ciSup A.B).symm

lemma B_le_Bmax (i : Fin A.M) : A.B i ≤ A.Bmax := by
  rw [Bmax_eq_sup]
  exact Finset.le_sup (Finset.mem_univ i)

lemma Bmax_pos_of_m_pos (hm : 0 < A.m) : 0 < A.Bmax := by
  classical
  have hex : ∃ i, 0 < A.E i := by
    by_contra h
    push Not at h
    have : A.m ≤ 0 := Finset.sum_nonpos fun i _ => h i
    linarith
  obtain ⟨i, hi⟩ := hex
  have hc : i ∈ A.cols := (A.mem_cols_iff i).mpr hi
  obtain ⟨j, hj⟩ := (by simpa [cols] using hc : ∃ j, 0 < A.p i j)
  have hBi : 0 < A.B i := Finset.card_pos.mpr ⟨j, by simpa [B] using hj⟩
  exact hBi.trans_le (A.B_le_Bmax i)

noncomputable def sAdet : ℝ :=
  Real.log A.Ax / Real.log A.M + Real.log A.Bmax / Real.log A.N

end GridLaw

end FractalGeometry.Probability.GridPercolation
