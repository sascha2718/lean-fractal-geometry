module

/-
Box-like matrices of `sec:box_like_self_affine` and the matrix form of `thm:box_like_sa`.

A tuple `𝖠` is box-like if every `A_i` is of the form `D_i R_i`, where `D_i ∈ GL_2(ℝ)` is
diagonal with `‖D_i‖ < 1` and `R_i` is a linear isometry with `R_i([-1,1]²) = [-1,1]²`. Vectors
of the plane are functions `Fin 2 → ℝ`, matrices act by `Matrix.mulVec`, and the Euclidean norm
enters through its square `v 0 ^ 2 + v 1 ^ 2`. The norm of a matrix is the `ℓ²` operator norm.

* `square`, `IsSquareIsometry`: the square `[-1,1]²` and the linear isometries `R` of the plane
  with `R([-1,1]²) = [-1,1]²`.
* `sq_mulVec_of_transpose_mul_self`, `sq_eq_one_of_mem_square`: an orthogonal matrix preserves
  the squared Euclidean norm, and the points of the square of squared norm `2` are the four
  corners.
* `isSquareIsometry_iff`: the square isometries are the eight matrices `boxMat c a b` with
  `a, b ∈ {1, -1}`.
* `IsSquareIsometry.orientation`: a square isometry is rotating exactly when it is
  anti-diagonal.
* `IsBoxLikeMatrix`, `isBoxLikeMatrix_iff`: `thm:box_like_sa` for a single matrix, `A = D R`
  if and only if `A` is diagonal or anti-diagonal with entries in `(-1, 1) ∖ {0}`. These are
  the matrices `System.mat`, and the clause on rotations is `System.WithRotations`.
* `IsSquareIsometry.boxMat_zero_mul_orientation`: in `A = D R` the isometry `R` is rotating
  exactly when `A` is anti-diagonal.
-/
public import BoxLike.SingularValue
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace BoxLike

open Matrix
open scoped Matrix.Norms.L2Operator

/-- The square `[-1,1]²`. -/
def square : Set (Fin 2 → ℝ) := {v | ∀ i, |v i| ≤ 1}

/-- Membership of the square `[-1,1]²` in coordinates. -/
theorem mem_square {v : Fin 2 → ℝ} : v ∈ square ↔ |v 0| ≤ 1 ∧ |v 1| ≤ 1 := by
  simp [square, Fin.forall_fin_two]

/-- A linear isometry `R` of the Euclidean plane with `R([-1,1]²) = [-1,1]²`, as a matrix. The
isometry condition is orthogonality, `Rᵀ R = 1`. -/
def IsSquareIsometry (R : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  R.transpose * R = 1 ∧ (fun v => R.mulVec v) '' square = square

/-- The action of a diagonal or anti-diagonal matrix on a vector. -/
theorem boxMat_mulVec (c : ZMod 2) (a b : ℝ) (v : Fin 2 → ℝ) :
    boxMat c a b *ᵥ v = if c = 0 then ![a * v 0, b * v 1] else ![a * v 1, b * v 0] := by
  rcases zmod_two_cases c with rfl | rfl <;>
    ext j <;> fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- A real number of square `1` has absolute value `1`. -/
theorem abs_eq_one_of_sq_eq_one {x : ℝ} (h : x ^ 2 = 1) : |x| = 1 := by
  simpa using (sq_eq_sq_iff_abs_eq_abs x 1).1 (by rw [h, one_pow])

/-- A real number of absolute value `1` is non-zero. -/
theorem ne_zero_of_abs_eq_one {x : ℝ} (h : |x| = 1) : x ≠ 0 :=
  abs_pos.1 (by rw [h]; exact one_pos)

/-- A real number of absolute value `1` has square `1`, in the form `x * x = 1`. -/
theorem mul_self_eq_one_of_abs_eq_one {x : ℝ} (h : |x| = 1) : x * x = 1 := by
  rw [← abs_mul_abs_self, h, mul_one]

/-- An orthogonal matrix preserves the squared Euclidean norm. The proof of `thm:box_like_sa`
uses the isometry property of `R` in this form. -/
theorem sq_mulVec_of_transpose_mul_self {R : Matrix (Fin 2) (Fin 2) ℝ} (h : Rᵀ * R = 1)
    (v : Fin 2 → ℝ) : (R *ᵥ v) 0 ^ 2 + (R *ᵥ v) 1 ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h11 := congrFun (congrFun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne, ne_eq, zero_ne_one, not_false_eq_true] at h00 h01 h11
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination v 0 ^ 2 * h00 + 2 * v 0 * v 1 * h01 + v 1 ^ 2 * h11

/-- The points of the square `[-1,1]²` of squared Euclidean norm `2` are the four corners
`(±1, ±1)`. -/
theorem sq_eq_one_of_mem_square {v : Fin 2 → ℝ} (hv : v ∈ square)
    (h : v 0 ^ 2 + v 1 ^ 2 = 2) : v 0 ^ 2 = 1 ∧ v 1 ^ 2 = 1 := by
  rw [mem_square] at hv
  have h0 := (sq_le_one_iff_abs_le_one (v 0)).2 hv.1
  have h1 := (sq_le_one_iff_abs_le_one (v 1)).2 hv.2
  constructor <;> linarith

/-- A square isometry maps corners of the square to corners. -/
theorem IsSquareIsometry.sq_mulVec_eq_one {R : Matrix (Fin 2) (Fin 2) ℝ}
    (hR : IsSquareIsometry R) {v : Fin 2 → ℝ} (h0 : v 0 ^ 2 = 1) (h1 : v 1 ^ 2 = 1) :
    (R *ᵥ v) 0 ^ 2 = 1 ∧ (R *ᵥ v) 1 ^ 2 = 1 := by
  have hv : v ∈ square :=
    mem_square.2 ⟨(abs_eq_one_of_sq_eq_one h0).le, (abs_eq_one_of_sq_eq_one h1).le⟩
  refine sq_eq_one_of_mem_square (hR.2.subset (Set.mem_image_of_mem _ hv)) ?_
  rw [sq_mulVec_of_transpose_mul_self hR.1, h0, h1]
  norm_num

/-- A diagonal or anti-diagonal matrix with entries `a, b ∈ {1, -1}` maps the square into
itself. -/
theorem boxMat_mulVec_mem_square (c : ZMod 2) {a b : ℝ} (ha : |a| = 1) (hb : |b| = 1)
    {v : Fin 2 → ℝ} (hv : v ∈ square) : boxMat c a b *ᵥ v ∈ square := by
  rw [mem_square] at hv
  rw [boxMat_mulVec, mem_square]
  rcases zmod_two_cases c with rfl | rfl
  · simpa [abs_mul, ha, hb] using hv
  · simpa [abs_mul, ha, hb] using hv.symm

/-- The eight matrices `boxMat c a b` with `a, b ∈ {1, -1}` are square isometries. The inverse
of `diag(a, b)` is `diag(a, b)`, and the inverse of the anti-diagonal matrix with entries
`a, b` is the anti-diagonal matrix with entries `b, a`. -/
theorem isSquareIsometry_boxMat (c : ZMod 2) {a b : ℝ} (ha : |a| = 1) (hb : |b| = 1) :
    IsSquareIsometry (boxMat c a b) := by
  have ha' := mul_self_eq_one_of_abs_eq_one ha
  have hb' := mul_self_eq_one_of_abs_eq_one hb
  refine ⟨?_, Set.Subset.antisymm ?_ ?_⟩
  · rcases zmod_two_cases c with rfl | rfl <;>
      ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ha', hb']
  · rintro _ ⟨v, hv, rfl⟩
    exact boxMat_mulVec_mem_square c ha hb hv
  · intro w hw
    rcases zmod_two_cases c with rfl | rfl
    · refine ⟨boxMat 0 a b *ᵥ w, boxMat_mulVec_mem_square 0 ha hb hw, ?_⟩
      show boxMat 0 a b *ᵥ boxMat 0 a b *ᵥ w = w
      rw [boxMat_mulVec, boxMat_mulVec]
      ext j
      fin_cases j <;> simp [← mul_assoc, ha', hb']
    · refine ⟨boxMat 1 b a *ᵥ w, boxMat_mulVec_mem_square 1 hb ha hw, ?_⟩
      show boxMat 1 a b *ᵥ boxMat 1 b a *ᵥ w = w
      rw [boxMat_mulVec, boxMat_mulVec]
      ext j
      fin_cases j <;> simp [← mul_assoc, ha', hb']

/-- The linear isometries `R` with `R([-1,1]²) = [-1,1]²` are the diagonal and anti-diagonal
matrices with entries `a, b ∈ {1, -1}`, as in the proof of `thm:box_like_sa`. The images of the
corners `(1, 1)` and `(1, -1)` are corners, which gives `R_{11} R_{12} = 0` and
`R_{11}² + R_{12}² = 1 = R_{21}² + R_{22}²`, and the first column of `R` is a unit vector. The
proof uses the inclusion `R([-1,1]²) ⊆ [-1,1]²` only. -/
theorem isSquareIsometry_iff {R : Matrix (Fin 2) (Fin 2) ℝ} :
    IsSquareIsometry R ↔ ∃ c : ZMod 2, ∃ a b : ℝ, |a| = 1 ∧ |b| = 1 ∧ R = boxMat c a b := by
  constructor
  · intro hR
    obtain ⟨h1, h2⟩ := hR.sq_mulVec_eq_one (v := ![1, 1]) (by simp) (by simp)
    obtain ⟨h3, h4⟩ := hR.sq_mulVec_eq_one (v := ![1, -1]) (by simp) (by simp)
    have h5 := sq_mulVec_of_transpose_mul_self hR.1 ![1, 0]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one] at h1 h2 h3 h4 h5
    have hpq : R 0 0 * R 0 1 = 0 := by linear_combination (h1 - h3) / 4
    have hpq2 : R 0 0 ^ 2 + R 0 1 ^ 2 = 1 := by linear_combination (h1 + h3) / 2
    have hrs2 : R 1 0 ^ 2 + R 1 1 ^ 2 = 1 := by linear_combination (h2 + h4) / 2
    have hpr2 : R 0 0 ^ 2 + R 1 0 ^ 2 = 1 := by linear_combination h5
    rcases mul_eq_zero.1 hpq with hp | hq
    · have hs : R 1 1 = 0 := by
        have : R 1 1 ^ 2 = 0 := by rw [hp] at hpr2; linarith
        exact pow_eq_zero_iff two_ne_zero |>.1 this
      refine ⟨1, R 0 1, R 1 0, abs_eq_one_of_sq_eq_one ?_, abs_eq_one_of_sq_eq_one ?_, ?_⟩
      · rw [hp] at hpq2; linarith
      · rw [hp] at hpr2; linarith
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [hp, hs]
    · have hr : R 1 0 = 0 := by
        have : R 1 0 ^ 2 = 0 := by rw [hq] at hpq2; linarith
        exact pow_eq_zero_iff two_ne_zero |>.1 this
      refine ⟨0, R 0 0, R 1 1, abs_eq_one_of_sq_eq_one ?_, abs_eq_one_of_sq_eq_one ?_, ?_⟩
      · rw [hq] at hpq2; linarith
      · rw [hr] at hrs2; linarith
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [hq, hr]
  · rintro ⟨c, a, b, ha, hb, rfl⟩
    exact isSquareIsometry_boxMat c ha hb

/-- A rotating square isometry is an anti-diagonal one. The entry `R 1 0` is the second
coordinate of `R e_1`, so `R 1 0 ≠ 0` says that `R` moves the first coordinate axis. -/
theorem IsSquareIsometry.orientation {R : Matrix (Fin 2) (Fin 2) ℝ} (hR : IsSquareIsometry R) :
    R 1 0 ≠ 0 ↔ ∃ a b : ℝ, |a| = 1 ∧ |b| = 1 ∧ R = boxMat 1 a b := by
  obtain ⟨c, a, b, ha, hb, rfl⟩ := isSquareIsometry_iff.1 hR
  rcases zmod_two_cases c with rfl | rfl
  · refine ⟨fun h => absurd (by simp) h, ?_⟩
    rintro ⟨a', b', -, -, h⟩
    have h00 := congrFun (congrFun h 0) 0
    simp only [boxMat_zero, boxMat_one, Matrix.of_apply, Matrix.cons_val_zero] at h00
    rw [h00] at ha
    simp at ha
  · exact ⟨fun _ => ⟨a, b, ha, hb, rfl⟩, fun _ => by simpa using ne_zero_of_abs_eq_one hb⟩

/-- `A = D R` with `D` diagonal, invertible, `‖D‖ < 1`, and `R` a square isometry: the
condition of `sec:box_like_self_affine` on each matrix of a box-like tuple. -/
def IsBoxLikeMatrix (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ d₁ d₂ : ℝ, d₁ ≠ 0 ∧ d₂ ≠ 0 ∧ ‖boxMat 0 d₁ d₂‖ < 1 ∧
    ∃ R, IsSquareIsometry R ∧ A = boxMat 0 d₁ d₂ * R

/-- `thm:box_like_sa`, matrix form: `A = D R` with `D ∈ GL_2(ℝ)` diagonal, `‖D‖ < 1`, and `R` a
square isometry if and only if `A` is diagonal or anti-diagonal with entries in
`(-1, 1) ∖ {0}`. For the converse, the anti-diagonal matrix with entries `a, b` is `diag(a, b)`
times the coordinate swap `boxMat 1 1 1`. -/
theorem isBoxLikeMatrix_iff {A : Matrix (Fin 2) (Fin 2) ℝ} :
    IsBoxLikeMatrix A ↔
      ∃ c : ZMod 2, ∃ a b : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ |a| < 1 ∧ |b| < 1 ∧ A = boxMat c a b := by
  constructor
  · rintro ⟨d₁, d₂, h₁, h₂, hn, R, hR, rfl⟩
    obtain ⟨c, a, b, ha, hb, rfl⟩ := isSquareIsometry_iff.1 hR
    rw [norm_boxMat, max_lt_iff] at hn
    refine ⟨c, d₁ * a, d₂ * b, mul_ne_zero h₁ (ne_zero_of_abs_eq_one ha),
      mul_ne_zero h₂ (ne_zero_of_abs_eq_one hb), ?_, ?_, ?_⟩
    · rw [abs_mul, ha, mul_one]
      exact hn.1
    · rw [abs_mul, hb, mul_one]
      exact hn.2
    · rw [boxMat_mul]
      simp
  · rintro ⟨c, a, b, ha, hb, ha1, hb1, rfl⟩
    refine ⟨a, b, ha, hb, ?_, boxMat c 1 1, isSquareIsometry_boxMat c (by simp) (by simp), ?_⟩
    · rw [norm_boxMat]
      exact max_lt ha1 hb1
    · rw [boxMat_mul]
      simp

/-- In a decomposition `A = D R` with `D = diag(d₁, d₂)` invertible, the square isometry `R` is
rotating exactly when `A` is anti-diagonal. A box-like tuple therefore contains both rotating
and non-rotating isometries exactly when it contains both diagonal and anti-diagonal matrices,
which is `System.WithRotations`. -/
theorem IsSquareIsometry.boxMat_zero_mul_orientation {R : Matrix (Fin 2) (Fin 2) ℝ}
    (hR : IsSquareIsometry R) {d₁ d₂ : ℝ} (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) :
    R 1 0 ≠ 0 ↔ ∃ a b : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ boxMat 0 d₁ d₂ * R = boxMat 1 a b := by
  rw [hR.orientation]
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    refine ⟨d₁ * a, d₂ * b, mul_ne_zero h₁ (ne_zero_of_abs_eq_one ha),
      mul_ne_zero h₂ (ne_zero_of_abs_eq_one hb), ?_⟩
    rw [boxMat_mul]
    simp
  · rintro ⟨a, b, -, -, h⟩
    obtain ⟨c, a', b', ha', hb', rfl⟩ := isSquareIsometry_iff.1 hR
    rcases zmod_two_cases c with rfl | rfl
    · have h00 := congrFun (congrFun h 0) 0
      rw [boxMat_mul] at h00
      simp only [boxMat_zero, boxMat_one, Matrix.of_apply, Matrix.cons_val_zero, add_zero,
        ite_true] at h00
      exact absurd h00 (mul_ne_zero h₁ (ne_zero_of_abs_eq_one ha'))
    · exact ⟨a', b', ha', hb', rfl⟩

end BoxLike
