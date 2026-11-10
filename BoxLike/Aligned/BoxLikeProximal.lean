module

/-
The all-anti-diagonal case of `sec:irreducibility` (tex lines 663 to 665 and 777 to 779). The
argument of the proof of `thm:box_like_proximal` is in `BoxLike/Proximal.lean`
(`System.Proximal.box_like_proximal`).

* `System.sq_o_of_forall_anti`: the second iterate of an all-anti-diagonal tuple is diagonal.
* `antiDiagonalExample`, `antiDiagonalExample_proximal`, `antiDiagonalExample_irreducible`,
  `antiDiagonalExample_not_stronglyIrreducible`, `antiDiagonalExample_not_withRotations`,
  `antiDiagonalExample_sq_o`: a proximal tuple of two anti-diagonal matrices is irreducible and
  not strongly irreducible, has no diagonal generator, and its second iterate is diagonal.
* `antiDiagonalExample_conj`, `antiDiagonalExample_not_withRotations_conj`: in every basis in
  which its matrices are simultaneously diagonal or anti-diagonal they are all anti-diagonal, so
  the tuple is in case (2) of `thm:A_classification` without being box-like with rotations in
  any basis.
-/
public import BoxLike.Classification

@[expose] public section

namespace BoxLike

open Matrix

namespace System

variable {ι : Type*}

/-- If every generator is anti-diagonal, every matrix `A_i A_j` of the second iterate is diagonal
(tex line 665); `Φ^(2)` has the attractor `X` (`System.attractor_sq`). -/
theorem sq_o_of_forall_anti {S : System ι} (h : ∀ i, S.o i = 1) (p : ι × ι) : S.sq.o p = 0 := by
  change S.o p.1 + S.o p.2 = 0
  rw [h, h]
  decide

end System

/-! ### The all-anti-diagonal case -/

/-- A tuple of two anti-diagonal matrices, `A_1` with entries `1/2`, `1/3` and `A_2` with entries
`1/3`, `1/2` in the first and second rows, and zero translations: the all-anti-diagonal case of
`sec:irreducibility` (tex lines 663 to 665). -/
noncomputable def antiDiagonalExample : System (Fin 2) where
  o _ := 1
  a := ![1 / 2, 1 / 3]
  b := ![1 / 3, 1 / 2]
  v _ := (0, 0)
  a_ne_zero i := by fin_cases i <;> norm_num
  b_ne_zero i := by fin_cases i <;> norm_num
  abs_a_lt_one i := by fin_cases i <;> norm_num [abs_of_pos]
  abs_b_lt_one i := by fin_cases i <;> norm_num [abs_of_pos]

/-- `A_1 A_2 = diag(1/4, 1/9)`. -/
theorem antiDiagonalExample_matWord :
    antiDiagonalExample.matWord [0, 1] = boxMat 0 (1 / 4) (1 / 9) := by
  have h1 : (1 : ZMod 2) + 1 = 0 := by decide
  have h2 : ¬ ((1 : ZMod 2) = 0) := by decide
  rw [System.matWord_cons, System.matWord_cons, System.matWord_nil, Matrix.mul_one,
    System.mat, System.mat, boxMat_mul]
  simp only [antiDiagonalExample, Matrix.cons_val_zero, Matrix.cons_val_one, h1, h2, ite_false]
  norm_num

/-- The all-anti-diagonal tuple is proximal: `A_1 A_2 = diag(1/4, 1/9)`. -/
theorem antiDiagonalExample_proximal : antiDiagonalExample.Proximal := by
  refine ⟨[0, 1], by simp, ?_⟩
  rw [antiDiagonalExample_matWord, isProximalMatrix_boxMat_zero]
  norm_num [abs_of_pos]

/-- The all-anti-diagonal tuple is irreducible. -/
theorem antiDiagonalExample_irreducible : TupleIrreducible antiDiagonalExample.mat :=
  antiDiagonalExample.tupleIrreducible_of_proximal ⟨0, rfl⟩ antiDiagonalExample_proximal

/-- The all-anti-diagonal tuple is not strongly irreducible: the union of the coordinate axes
is invariant. -/
theorem antiDiagonalExample_not_stronglyIrreducible :
    ¬ TupleStronglyIrreducible antiDiagonalExample.mat :=
  antiDiagonalExample.not_tupleStronglyIrreducible

/-- The all-anti-diagonal tuple has no diagonal generator, so it is not with rotations. -/
theorem antiDiagonalExample_not_withRotations : ¬ antiDiagonalExample.WithRotations := by
  rintro ⟨⟨i, hi⟩, -⟩
  exact (show (1 : ZMod 2) ≠ 0 by decide) hi

/-- All matrices of the second iterate of the all-anti-diagonal tuple are diagonal (tex line
746). -/
theorem antiDiagonalExample_sq_o (p : Fin 2 × Fin 2) : antiDiagonalExample.sq.o p = 0 :=
  System.sq_o_of_forall_anti (fun _ => rfl) p

/-- In every basis in which the matrices of the all-anti-diagonal tuple are simultaneously
diagonal or anti-diagonal, both are anti-diagonal. The proximal product `A_1 A_2` stays diagonal
after the change of basis, so the two matrices have the same type; if both were diagonal, the
first basis vector would span an invariant line. -/
theorem antiDiagonalExample_conj {P : Matrix (Fin 2) (Fin 2) ℝ} (hP : P.det ≠ 0)
    (h : ∀ i, ∃ c : ZMod 2, ∃ a b : ℝ, P⁻¹ * antiDiagonalExample.mat i * P = boxMat c a b)
    (i : Fin 2) : ∃ a b : ℝ, P⁻¹ * antiDiagonalExample.mat i * P = boxMat 1 a b := by
  obtain ⟨c₀, a₀, b₀, h₀⟩ := h 0
  obtain ⟨c₁, a₁, b₁, h₁⟩ := h 1
  -- The conjugate of the proximal product `A_1 A_2` is proximal, hence diagonal.
  have hprod : P⁻¹ * antiDiagonalExample.matWord [0, 1] * P =
      boxMat c₀ a₀ b₀ * boxMat c₁ a₁ b₁ := by
    rw [System.matWord, conj_list_prod hP]
    simp [h₀, h₁]
  have hc : c₀ + c₁ = 0 := by
    have hB : IsProximalMatrix (P⁻¹ * antiDiagonalExample.matWord [0, 1] * P) := by
      refine IsProximalMatrix.conj ?_ hP
      rw [antiDiagonalExample_matWord, isProximalMatrix_boxMat_zero]
      norm_num [abs_of_pos]
    rw [hprod, boxMat_mul] at hB
    rcases zmod_two_cases (c₀ + c₁) with h0 | h0
    · exact h0
    · rw [h0] at hB
      exact absurd hB (not_isProximalMatrix_boxMat_one _ _)
  -- Both matrices diagonal would give the invariant line spanned by `P e_1`.
  have hc₀ : c₀ = 1 := by
    rcases zmod_two_cases c₀ with h0 | h0
    · exfalso
      have hc₁ : c₁ = 0 := by rw [h0, zero_add] at hc; exact hc
      refine antiDiagonalExample_irreducible ⟨P *ᵥ ![1, 0],
        mulVec_ne_zero_of_det_ne_zero hP (fun he => by simpa using congrFun he 0),
        Fin.forall_fin_two.2 ⟨⟨a₀, ?_⟩, ⟨a₁, ?_⟩⟩⟩
      · rw [mulVec_conj hP, h₀, h0, boxMat_mulVec, ← Matrix.mulVec_smul]
        congr 1; ext k; fin_cases k <;> simp
      · rw [mulVec_conj hP, h₁, hc₁, boxMat_mulVec, ← Matrix.mulVec_smul]
        congr 1; ext k; fin_cases k <;> simp
    · exact h0
  have hc₁ : c₁ = 1 := by
    rw [hc₀] at hc
    rcases zmod_two_cases c₁ with h1 | h1
    · rw [h1] at hc; exact absurd hc (by decide)
    · exact h1
  revert i
  exact Fin.forall_fin_two.2 ⟨⟨a₀, b₀, by rw [h₀, hc₀]⟩, ⟨a₁, b₁, by rw [h₁, hc₁]⟩⟩

/-- The all-anti-diagonal tuple is in case (2) of `thm:A_classification`, irreducible and not
strongly irreducible, but it is not box-like with rotations in any basis: no change of basis
makes its matrices simultaneously diagonal or anti-diagonal with both types present. The
identification of the intermediate class with box-like tuples with rotations therefore needs the
exception of the all-anti-diagonal tuples, which the paragraph after `thm:box_like_proximal`
makes (tex lines 696 to 698). -/
theorem antiDiagonalExample_not_withRotations_conj :
    TupleIrreducible antiDiagonalExample.mat ∧
      ¬ TupleStronglyIrreducible antiDiagonalExample.mat ∧
      ¬ ∃ P : Matrix (Fin 2) (Fin 2) ℝ, P.det ≠ 0 ∧
        (∀ i, ∃ c : ZMod 2, ∃ a b : ℝ, P⁻¹ * antiDiagonalExample.mat i * P = boxMat c a b) ∧
        ∃ i, ∃ a b : ℝ, P⁻¹ * antiDiagonalExample.mat i * P = boxMat 0 a b := by
  refine ⟨antiDiagonalExample_irreducible, antiDiagonalExample_not_stronglyIrreducible, ?_⟩
  rintro ⟨P, hP, h, i, a, b, hi⟩
  obtain ⟨a', b', hi'⟩ := antiDiagonalExample_conj hP h i
  have he : boxMat 0 a b = boxMat 1 a' b' := hi.symm.trans hi'
  have ha : a = 0 := by simpa using congrFun (congrFun he 0) 0
  have hb : b = 0 := by simpa using congrFun (congrFun he 1) 1
  have hdet := det_inv_mul_mul hP (antiDiagonalExample.mat i)
  rw [hi, ha, hb] at hdet
  exact antiDiagonalExample.det_mat_ne_zero i (by rw [← hdet]; simp [Matrix.det_fin_two_of])

end BoxLike
