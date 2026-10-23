import FractalGeometry.Probability.GridPercolation.CarpetDimension

/-!
# Assouad dimension of Bedford–McMullen carpets

John M. Mackay, "Assouad dimension of self-affine carpets",
Conformal Geometry and Dynamics 15 (2011), 177–187, Theorem 1.1.
DOI: 10.1090/S1088-4173-2011-00232-3; arXiv:1003.0930v2.

The coordinate axes are exchanged relative to the paper. `M` is the slower
contraction denominator and `N` the faster one. The interface is a finite digit
set, with no random-retention assumptions.
-/

namespace FractalGeometry.BedfordMcMullen

open Probability.GridPercolation

structure System where
  M : ℕ
  N : ℕ
  two_le_M : 2 ≤ M
  M_lt_N : M < N
  digits : Finset (Fin M × Fin N)

namespace System

noncomputable abbrev grid (S : System) : GridLaw where
  M := S.M
  N := S.N
  hM := S.two_le_M
  hMN := S.M_lt_N
  p i j := if (i, j) ∈ S.digits then 1 else 0
  p_nonneg i j := by split_ifs <;> norm_num
  p_le_one i j := by split_ifs <;> norm_num

noncomputable def attractor (S : System) : Set (ℝ × ℝ) := carpet S.grid

def columnRows (S : System) (i : Fin S.M) : Finset (Fin S.N) :=
  Finset.univ.filter fun j => (i, j) ∈ S.digits

noncomputable def nonemptyColumns (S : System) : Finset (Fin S.M) :=
  Finset.univ.filter fun i => ∃ j, (i, j) ∈ S.digits

def maxColumnSize (S : System) : ℕ := Finset.univ.sup fun i => (S.columnRows i).card

/-- Theorem 1.1 of Mackay (2011). The elementary empty and single-digit cases
are included, with dimension zero. -/
theorem mackay_dimension (S : System) :
    Dimension.PhiAssouad.dimA S.attractor =
      Real.log S.nonemptyColumns.card / Real.log S.M +
        Real.log S.maxColumnSize / Real.log S.N := by
  have hpos (i : Fin S.M) (j : Fin S.N) : 0 < S.grid.p i j ↔ (i, j) ∈ S.digits := by
    by_cases h : (i, j) ∈ S.digits <;> simp [h]
  have hc : S.grid.cols = S.nonemptyColumns := by
    ext i
    simp only [GridLaw.cols, nonemptyColumns, Finset.mem_filter, Finset.mem_univ, true_and, hpos]
  have hr (i : Fin S.M) : S.grid.rows i = S.columnRows i := by
    ext j
    simp only [GridLaw.rows, columnRows, Finset.mem_filter, Finset.mem_univ, true_and, hpos]
  have hmax : S.grid.Bmax = S.maxColumnSize := by
    rw [GridLaw.Bmax_eq_sup]
    exact Finset.sup_congr rfl fun i _ => congrArg Finset.card (hr i)
  have h := mackay_carpet_dimension S.grid
  simpa only [attractor, GridLaw.sAdet, GridLaw.Ax_eq_card_cols, hc, hmax, grid] using h

end System
end FractalGeometry.BedfordMcMullen
