module

/-
`thm:box_like_sa` of `sec:box_like_self_affine` for a whole tuple: a planar self-affine set is
box-like with rotations if and only if the matrices of `𝖠` are simultaneously diagonal or
anti-diagonal and `𝖠` contains both diagonal and anti-diagonal matrices.

A tuple `𝖠` is box-like if every `A_i` is `D_i R_i` with `D_i ∈ GL_2(ℝ)` diagonal, `‖D_i‖ < 1`,
and `R_i` a linear isometry with `R_i([-1,1]²) = [-1,1]²` (`IsSquareIsometry`); it is box-like
with rotations if both rotating and non-rotating isometries occur. The manuscript does not define
"rotating"; it is read here as "`R_i` moves the coordinate axes", `R_i e_1 ∉ ℝ e_1`, that is
`(R_i)_{21} ≠ 0`. For a square isometry this is the anti-diagonal case
(`IsSquareIsometry.orientation`). The lemma needs this reading: the rotation `-I` by `π` is
diagonal, and the reflection in the diagonal is anti-diagonal.

The proof follows the manuscript and is assembled from `BoxLike/BoxLikeMatrix.lean`: every
square isometry is a signed permutation matrix (`isSquareIsometry_iff`, which uses the images of
the corners of the square where the manuscript uses the images of `e_1` and `e_2`), so
`A_i = D_i R_i` is diagonal or anti-diagonal, and it is anti-diagonal exactly when `R_i` is
rotating (`IsSquareIsometry.boxMat_zero_mul_orientation`); conversely an anti-diagonal matrix
with entries `a, b` is `diag(a, b)` times the coordinate swap `boxMat 1 1 1`.

* `IsBoxLikeWithRotations`: the tuple `𝖠` is box-like with rotations.
* `box_like_sa`: `thm:box_like_sa` with the entry bounds made explicit, for every tuple.
* `box_like_sa_of_contracting`: `thm:box_like_sa` as stated, for a tuple of invertible matrices
  of norm less than one, the linear parts of a planar self-affine set.
* `PlanarSystem.box_like_sa`: the same for the linear parts of a `PlanarSystem`.
* `System.isBoxLikeWithRotations_iff`: the tuple of a box-like system is box-like with rotations
  exactly when `System.WithRotations` holds.
* `PlanarSystem.isBoxLikeWithRotations_iff_exists_system`: a planar system is box-like with
  rotations exactly when it is `System.toPlanar` of a box-like system with rotations.
-/
public import BoxLike.BoxLikeMatrix
public import BoxLike.Planar.System

@[expose] public section

namespace BoxLike

open Matrix
open scoped Matrix.Norms.L2Operator

variable {ι : Type*}

/-- The tuple `𝖠` is box-like with rotations (`sec:box_like_self_affine`, tex lines 570 to 579):
every `A_i` is `D_i R_i` with `D_i = diag(d_1(i), d_2(i))` invertible, `‖D_i‖ < 1`, and `R_i` a
linear isometry with `R_i([-1,1]²) = [-1,1]²`, and both rotating and non-rotating isometries
occur. The isometry `R_i` is rotating when it moves the coordinate axes, `R_i e_1 ∉ ℝ e_1`, that
is `(R_i)_{21} ≠ 0`. -/
def IsBoxLikeWithRotations (A : ι → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ (d₁ d₂ : ι → ℝ) (R : ι → Matrix (Fin 2) (Fin 2) ℝ),
    (∀ i, d₁ i ≠ 0 ∧ d₂ i ≠ 0 ∧ ‖boxMat 0 (d₁ i) (d₂ i)‖ < 1 ∧ IsSquareIsometry (R i) ∧
      A i = boxMat 0 (d₁ i) (d₂ i) * R i) ∧
    (∃ i, R i 1 0 ≠ 0) ∧ ∃ i, R i 1 0 = 0

/-- Two diagonal or anti-diagonal matrices with a non-zero first entry `a` that agree have the
same type. -/
theorem boxMat_type_eq {c c' : ZMod 2} {a b a' b' : ℝ} (ha : a ≠ 0)
    (h : boxMat c a b = boxMat c' a' b') : c = c' := by
  rcases zmod_two_cases c with rfl | rfl <;> rcases zmod_two_cases c' with rfl | rfl
  · rfl
  · exact absurd (by simpa using congrFun (congrFun h 0) 0) ha
  · exact absurd (by simpa using congrFun (congrFun h 0) 1) ha
  · rfl

/-- `thm:box_like_sa` for an arbitrary tuple, with the bounds on the entries made explicit: `𝖠`
is box-like with rotations if and only if every `A_i` is diagonal or anti-diagonal with entries
in `(-1, 1) ∖ {0}` and `𝖠` contains both a diagonal and an anti-diagonal matrix. The forward
direction is the first paragraph of the proof: `R_i` is a signed permutation matrix, so
`A_i = D_i R_i` is diagonal or anti-diagonal, anti-diagonal exactly when `R_i` is rotating. The
converse writes an anti-diagonal matrix as `diag(a, b)` times the coordinate swap. -/
theorem box_like_sa (A : ι → Matrix (Fin 2) (Fin 2) ℝ) :
    IsBoxLikeWithRotations A ↔
      (∀ i, ∃ c : ZMod 2, ∃ a b : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ |a| < 1 ∧ |b| < 1 ∧ A i = boxMat c a b) ∧
      (∃ i, ∃ a b : ℝ, A i = boxMat 0 a b) ∧ ∃ i, ∃ a b : ℝ, A i = boxMat 1 a b := by
  constructor
  · rintro ⟨d₁, d₂, R, hA, ⟨i, hi⟩, ⟨j, hj⟩⟩
    refine ⟨fun k => isBoxLikeMatrix_iff.1 ⟨d₁ k, d₂ k, (hA k).1, (hA k).2.1, (hA k).2.2.1,
      R k, (hA k).2.2.2.1, (hA k).2.2.2.2⟩, ?_, ?_⟩
    · obtain ⟨-, -, -, hR, he⟩ := hA j
      obtain ⟨c, a, b, -, hb, hRe⟩ := isSquareIsometry_iff.1 hR
      rcases zmod_two_cases c with rfl | rfl
      · refine ⟨j, d₁ j * a, d₂ j * b, ?_⟩
        rw [he, hRe, boxMat_mul]
        simp
      · rw [hRe] at hj
        exact absurd hj (by simpa using ne_zero_of_abs_eq_one hb)
    · obtain ⟨h₁, h₂, -, hR, he⟩ := hA i
      obtain ⟨a, b, -, -, hab⟩ := (hR.boxMat_zero_mul_orientation h₁ h₂).1 hi
      exact ⟨i, a, b, he.trans hab⟩
  · rintro ⟨h, ⟨j, aj, bj, hj⟩, ⟨i, ai, bi, hi⟩⟩
    choose c a b ha hb ha1 hb1 hA using h
    have htype : ∀ k (c' : ZMod 2) a' b', A k = boxMat c' a' b' → c k = c' := fun k c' a' b' hk =>
      boxMat_type_eq (ha k) ((hA k).symm.trans hk)
    refine ⟨a, b, fun k => boxMat (c k) 1 1, fun k => ⟨ha k, hb k, ?_,
      isSquareIsometry_boxMat (c k) (by simp) (by simp), ?_⟩, ⟨i, ?_⟩, ⟨j, ?_⟩⟩
    · rw [norm_boxMat]
      exact max_lt (ha1 k) (hb1 k)
    · rw [hA k, boxMat_mul]
      simp
    · show boxMat (c i) 1 1 1 0 ≠ 0
      rw [htype i 1 ai bi hi]
      simp
    · show boxMat (c j) 1 1 1 0 = 0
      rw [htype j 0 aj bj hj]
      simp

/-- An invertible diagonal or anti-diagonal matrix of norm less than one has entries in
`(-1, 1) ∖ {0}`: `|det| = |a| |b|` and `‖boxMat c a b‖ = max {|a|, |b|}`. -/
theorem boxMat_entries_of_contracting {c : ZMod 2} {a b : ℝ} (hdet : (boxMat c a b).det ≠ 0)
    (hnorm : ‖boxMat c a b‖ < 1) : a ≠ 0 ∧ b ≠ 0 ∧ |a| < 1 ∧ |b| < 1 := by
  have h := abs_det_boxMat c a b
  have hab : |a| * |b| ≠ 0 := by rw [← h]; exact abs_ne_zero.2 hdet
  rw [norm_boxMat, max_lt_iff] at hnorm
  exact ⟨fun h0 => hab (by rw [h0, abs_zero, zero_mul]),
    fun h0 => hab (by rw [h0, abs_zero, mul_zero]), hnorm.1, hnorm.2⟩

/-- `thm:box_like_sa` as stated: for the tuple `𝖠 ∈ GL_2(ℝ)^N` of a planar self-affine set, with
`‖A_i‖ < 1`, the tuple is box-like with rotations if and only if its matrices are diagonal or
anti-diagonal and `𝖠` contains both diagonal and anti-diagonal matrices. The entry bounds of
`box_like_sa` come from `det A_i ≠ 0` and `‖A_i‖ < 1`. -/
theorem box_like_sa_of_contracting {A : ι → Matrix (Fin 2) (Fin 2) ℝ}
    (hdet : ∀ i, (A i).det ≠ 0) (hnorm : ∀ i, ‖A i‖ < 1) :
    IsBoxLikeWithRotations A ↔
      (∀ i, ∃ c : ZMod 2, ∃ a b : ℝ, A i = boxMat c a b) ∧
      (∃ i, ∃ a b : ℝ, A i = boxMat 0 a b) ∧ ∃ i, ∃ a b : ℝ, A i = boxMat 1 a b := by
  rw [box_like_sa]
  refine and_congr ⟨fun h i => ?_, fun h i => ?_⟩ Iff.rfl
  · obtain ⟨c, a, b, -, -, -, -, he⟩ := h i
    exact ⟨c, a, b, he⟩
  · obtain ⟨c, a, b, he⟩ := h i
    have hd := hdet i
    have hn := hnorm i
    rw [he] at hd hn
    exact ⟨c, a, b, boxMat_entries_of_contracting hd hn |>.1,
      (boxMat_entries_of_contracting hd hn).2.1, (boxMat_entries_of_contracting hd hn).2.2.1,
      (boxMat_entries_of_contracting hd hn).2.2.2, he⟩

/-- `thm:box_like_sa` for a planar self-affine set `X` given by a `PlanarSystem`: `X` is box-like
with rotations if and only if the matrices of `𝖠` are simultaneously diagonal or anti-diagonal
and `𝖠` contains both diagonal and anti-diagonal matrices. -/
theorem PlanarSystem.box_like_sa (P : PlanarSystem ι) :
    IsBoxLikeWithRotations P.mat ↔
      (∀ i, ∃ c : ZMod 2, ∃ a b : ℝ, P.mat i = boxMat c a b) ∧
      (∃ i, ∃ a b : ℝ, P.mat i = boxMat 0 a b) ∧ ∃ i, ∃ a b : ℝ, P.mat i = boxMat 1 a b :=
  box_like_sa_of_contracting P.det_ne_zero P.norm_lt_one

/-- The tuple of a box-like system `S` is box-like with rotations exactly when both orientations
occur, `System.WithRotations` (`thm:box_like_sa`). -/
theorem System.isBoxLikeWithRotations_iff (S : System ι) :
    IsBoxLikeWithRotations S.mat ↔ S.WithRotations := by
  rw [← S.toPlanar_mat, PlanarSystem.box_like_sa, S.toPlanar_mat]
  constructor
  · rintro ⟨-, ⟨i, a, b, hi⟩, ⟨j, a', b', hj⟩⟩
    exact ⟨⟨i, boxMat_type_eq (S.a_ne_zero i) hi⟩, ⟨j, boxMat_type_eq (S.a_ne_zero j) hj⟩⟩
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    refine ⟨fun k => ⟨S.o k, S.a k, S.b k, rfl⟩, ⟨i, S.a i, S.b i, ?_⟩, ⟨j, S.a j, S.b j, ?_⟩⟩
    · rw [System.mat, hi]
    · rw [System.mat, hj]

/-- A planar self-affine system is box-like with rotations exactly when it is the planar system
`System.toPlanar` of a box-like system with rotations, the representation used for the main
results (`thm:box_like_sa`). -/
theorem PlanarSystem.isBoxLikeWithRotations_iff_exists_system (P : PlanarSystem ι) :
    IsBoxLikeWithRotations P.mat ↔ ∃ S : System ι, S.WithRotations ∧ S.toPlanar = P := by
  constructor
  · intro h
    obtain ⟨hbox, -, -⟩ := (BoxLike.box_like_sa P.mat).1 h
    choose c a b ha hb ha1 hb1 hA using hbox
    let S : System ι :=
      { o := c, a := a, b := b, v := P.v, a_ne_zero := ha, b_ne_zero := hb,
        abs_a_lt_one := ha1, abs_b_lt_one := hb1 }
    have hmat : S.mat = P.mat := funext fun i => (hA i).symm
    refine ⟨S, S.isBoxLikeWithRotations_iff.1 (hmat ▸ h), ?_⟩
    · cases P
      simp only [System.toPlanar, PlanarSystem.mk.injEq]
      exact ⟨hmat, rfl⟩
  · rintro ⟨S, hS, rfl⟩
    rw [S.toPlanar_mat]
    exact S.isBoxLikeWithRotations_iff.2 hS

end BoxLike
