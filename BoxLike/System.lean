module

/-
Box-like affine iterated function systems in box-like coordinates and their projective
systems: `sec:box_like_self_affine`, `sec:subshift` and `sec:projective_system`.

* `boxMat`, `boxMat_mul`: the diagonal and anti-diagonal matrices and their product rule.
* `System`: the data `a_i, b_i ∈ (-1, 1) ∖ {0}`, the orientation `o i` and the translation
  `v_i` of a box-like system; `System.WithRotations` says that both orientations occur, and
  `System.HasProximalDiagonal` is the normalisation of `sec:gibbs_measures`.
* `System.mat`, `System.phi`: the matrices `A_i` and the maps `φ_i`.
* `System.ratio`, `System.trans`, `System.g`: the projective system `Ψ` of
  `eq:def_of_g_system`, over the alphabet `ι × ZMod 2`.
* `System.coord_phi`: `eq:phi_def_by_g` in the uniform form
  `proj_c ∘ φ_i = g_(i,c) ∘ proj_(c + o i)`.
* `System.codeWord`, `System.gDeriv`, `System.matWord_eq`: the product `A_𝐢` is the box
  matrix whose row-`c` entry is the derivative of `g` along the path of `Σ_Z` over `𝐢`
  starting on the axis `c`.
* `System.matWord_mulVec_e1`, `System.matWord_mulVec_e2`,
  `System.abs_matWord_e1`, `System.abs_matWord_e2`: `thm:matrix_products_g_derivatives`
  for finite words.
* `pastWord`, `System.codeWord_pastWord_tau`, `System.codeWord_pastWord_omega`,
  `System.abs_matWord_pastWord_e1`, `System.abs_matWord_pastWord_e2`:
  `thm:matrix_products_g_derivatives` as stated, along `i_{-n} ⋯ i_{-1}`.
-/
public import BoxLike.Coding
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Ring

@[expose] public section

namespace BoxLike

open Matrix

/-- The diagonal matrix `diag(a, b)` for `c = 0` and the anti-diagonal matrix with
first-row entry `a` and second-row entry `b` for `c = 1`. -/
def boxMat (c : ZMod 2) (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if c = 0 then !![a, 0; 0, b] else !![0, a; b, 0]

@[simp] theorem boxMat_zero (a b : ℝ) : boxMat 0 a b = !![a, 0; 0, b] := rfl

@[simp] theorem boxMat_one (a b : ℝ) : boxMat 1 a b = !![0, a; b, 0] := rfl

theorem zmod_two_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide

/-- The product rule for diagonal and anti-diagonal matrices: orientations add, and an
anti-diagonal left factor exchanges the rows of the right factor. -/
theorem boxMat_mul (c c' : ZMod 2) (a b a' b' : ℝ) :
    boxMat c a b * boxMat c' a' b' =
      boxMat (c + c') (a * if c = 0 then a' else b') (b * if c = 0 then b' else a') := by
  rcases zmod_two_cases c with rfl | rfl <;> rcases zmod_two_cases c' with rfl | rfl <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, show (1 : ZMod 2) + 1 = 0 from by decide]

/-- A planar box-like affine iterated function system in box-like coordinates, as in
`sec:subshift` and `sec:projective_system`: the linear part of the `i`-th map is
`diag(a_i, b_i)` when `o i = 0` and the anti-diagonal matrix with first-row entry `a_i` and
second-row entry `b_i` when `o i = 1`; the translation part is `v_i`. -/
structure System (ι : Type*) where
  /-- The orientation: `0` for a diagonal linear part, `1` for an anti-diagonal one. -/
  o : ι → ZMod 2
  /-- The non-zero entry `a_i` of the first row of `A_i`. -/
  a : ι → ℝ
  /-- The non-zero entry `b_i` of the second row of `A_i`. -/
  b : ι → ℝ
  /-- The translation part `v_i = (v_i^{(1)}, v_i^{(2)})`. -/
  v : ι → ℝ × ℝ
  a_ne_zero : ∀ i, a i ≠ 0
  b_ne_zero : ∀ i, b i ≠ 0
  abs_a_lt_one : ∀ i, |a i| < 1
  abs_b_lt_one : ∀ i, |b i| < 1

namespace System

variable {ι : Type*} (S : System ι)

/-- The system is box-like with rotations: both diagonal and anti-diagonal linear parts
occur, as in `thm:box_like_sa`. -/
def WithRotations : Prop := (∃ i, S.o i = 0) ∧ ∃ i, S.o i = 1

/-- The normalisation of `sec:gibbs_measures`: some diagonal generator has entries of distinct
absolute values, that is, the tuple contains a proximal diagonal generator. -/
def HasProximalDiagonal : Prop := ∃ i, S.o i = 0 ∧ |S.a i| ≠ |S.b i|

/-- The linear part `A_i`. -/
def mat (i : ι) : Matrix (Fin 2) (Fin 2) ℝ := boxMat (S.o i) (S.a i) (S.b i)

/-- The coordinate `proj_x` for `c = 0` and `proj_y` for `c = 1`. -/
def coord (c : ZMod 2) (z : ℝ × ℝ) : ℝ := if c = 0 then z.1 else z.2

@[simp] theorem coord_zero (z : ℝ × ℝ) : coord 0 z = z.1 := rfl

@[simp] theorem coord_one (z : ℝ × ℝ) : coord 1 z = z.2 := rfl

/-- The contraction ratio `g_j'` of the projective system: `a_i` for the symbol `(i, 0)`
and `b_i` for the symbol `(i, 1)`. -/
def ratio (p : ι × ZMod 2) : ℝ := if p.2 = 0 then S.a p.1 else S.b p.1

/-- The translation `g_j(0)` of the projective system: `v_i^{(1)}` for the symbol `(i, 0)`
and `v_i^{(2)}` for the symbol `(i, 1)`. -/
def trans (p : ι × ZMod 2) : ℝ := coord p.2 (S.v p.1)

/-- The maps `g_j` of the projective system `Ψ` of `eq:def_of_g_system`. -/
def g (p : ι × ZMod 2) (t : ℝ) : ℝ := S.ratio p * t + S.trans p

/-- The affine map `φ_i(z) = A_i z + v_i`. -/
def phi (i : ι) (z : ℝ × ℝ) : ℝ × ℝ :=
  (S.a i * coord (S.o i) z + (S.v i).1, S.b i * coord (S.o i + 1) z + (S.v i).2)

@[simp] theorem ratio_zero (i : ι) : S.ratio (i, 0) = S.a i := rfl

@[simp] theorem ratio_one (i : ι) : S.ratio (i, 1) = S.b i := rfl

theorem ratio_ne_zero (p : ι × ZMod 2) : S.ratio p ≠ 0 := by
  unfold ratio; split_ifs <;> [exact S.a_ne_zero _; exact S.b_ne_zero _]

theorem abs_ratio_lt_one (p : ι × ZMod 2) : |S.ratio p| < 1 := by
  unfold ratio; split_ifs <;> [exact S.abs_a_lt_one _; exact S.abs_b_lt_one _]

/-- `φ_i` is `z ↦ A_i z + v_i`. -/
theorem phi_eq_mulVec (i : ι) (z : ℝ × ℝ) :
    ![(S.phi i z).1, (S.phi i z).2] = S.mat i *ᵥ ![z.1, z.2] + ![(S.v i).1, (S.v i).2] := by
  rcases zmod_two_cases (S.o i) with h | h <;>
    ext j <;> fin_cases j <;>
    simp [phi, mat, h, coord, mul_comm, show (1 : ZMod 2) + 1 = 0 from by decide]

/-- `eq:phi_def_by_g` in uniform form: `proj_c ∘ φ_i = g_(i,c) ∘ proj_(c + o i)`. -/
theorem coord_phi (c : ZMod 2) (i : ι) (z : ℝ × ℝ) :
    coord c (S.phi i z) = S.g (i, c) (coord (c + S.o i) z) := by
  rcases zmod_two_cases c with rfl | rfl
  · simp [phi, g, trans]
  · simp [phi, g, trans, add_comm]

/-- `eq:phi_def_by_g` for a diagonal generator: `φ_i(x, y) = (g_i(x), g_{i+N}(y))`. -/
theorem phi_of_o_eq_zero {i : ι} (h : S.o i = 0) (z : ℝ × ℝ) :
    S.phi i z = (S.g (i, 0) z.1, S.g (i, 1) z.2) := by
  simp [phi, g, trans, h]

/-- `eq:phi_def_by_g` for an anti-diagonal generator: `φ_i(x, y) = (g_i(y), g_{i+N}(x))`. -/
theorem phi_of_o_eq_one {i : ι} (h : S.o i = 1) (z : ℝ × ℝ) :
    S.phi i z = (S.g (i, 0) z.2, S.g (i, 1) z.1) := by
  simp [phi, g, trans, h, show (1 : ZMod 2) + 1 = 0 from by decide]

/-! ### Finite words -/

/-- The parity of the number of anti-diagonal generators in the word `𝐢`. -/
def oWord (w : List ι) : ZMod 2 := (w.map S.o).sum

/-- The product `A_𝐢 = A_{i_0} ⋯ A_{i_{n-1}}`. -/
def matWord (w : List ι) : Matrix (Fin 2) (Fin 2) ℝ := (w.map S.mat).prod

/-- The path of `Σ_Z` over the word `𝐢` starting on the axis `c`: the symbol `i_k` is
followed on the axis `c + o(i_0) + ⋯ + o(i_{k-1})`. -/
def codeWord : ZMod 2 → List ι → List (ι × ZMod 2)
  | _, [] => []
  | c, i :: w => (i, c) :: codeWord (c + S.o i) w

/-- The derivative `g_𝐣'` of `g_𝐣 = g_{j_0} ∘ ⋯ ∘ g_{j_{n-1}}`, a constant. -/
def gDeriv (u : List (ι × ZMod 2)) : ℝ := (u.map S.ratio).prod

@[simp] theorem oWord_nil : S.oWord [] = 0 := rfl

@[simp] theorem oWord_cons (i : ι) (w : List ι) : S.oWord (i :: w) = S.o i + S.oWord w := by
  simp [oWord]

@[simp] theorem matWord_nil : S.matWord [] = 1 := rfl

@[simp] theorem matWord_cons (i : ι) (w : List ι) :
    S.matWord (i :: w) = S.mat i * S.matWord w := by
  simp [matWord]

@[simp] theorem codeWord_nil (c : ZMod 2) : S.codeWord c [] = [] := rfl

@[simp] theorem codeWord_cons (c : ZMod 2) (i : ι) (w : List ι) :
    S.codeWord c (i :: w) = (i, c) :: S.codeWord (c + S.o i) w := rfl

@[simp] theorem length_codeWord (c : ZMod 2) (w : List ι) :
    (S.codeWord c w).length = w.length := by
  induction w generalizing c with
  | nil => rfl
  | cons i w ih => simp [ih]

@[simp] theorem gDeriv_nil : S.gDeriv [] = 1 := rfl

@[simp] theorem gDeriv_cons (p : ι × ZMod 2) (u : List (ι × ZMod 2)) :
    S.gDeriv (p :: u) = S.ratio p * S.gDeriv u := by
  simp [gDeriv]

theorem gDeriv_ne_zero (u : List (ι × ZMod 2)) : S.gDeriv u ≠ 0 := by
  induction u with
  | nil => simp
  | cons p u ih => simpa using ⟨S.ratio_ne_zero p, ih⟩

/-- The product `A_𝐢` is diagonal or anti-diagonal according to the parity of the number
of anti-diagonal factors, and its row-`c` entry is the derivative of `g` along the path of
`Σ_Z` over `𝐢` starting on the axis `c`. -/
theorem matWord_eq (w : List ι) :
    S.matWord w =
      boxMat (S.oWord w) (S.gDeriv (S.codeWord 0 w)) (S.gDeriv (S.codeWord 1 w)) := by
  induction w with
  | nil =>
    ext i j; fin_cases i <;> fin_cases j <;> simp
  | cons i w ih =>
    rw [matWord_cons, ih, mat, boxMat_mul]
    rcases zmod_two_cases (S.o i) with h | h <;>
      simp [h, show (1 : ZMod 2) + 1 = 0 from by decide]

/-- The first column of `A_𝐢`: the image of `e_1` lies on the axis `oWord 𝐢`. -/
theorem matWord_mulVec_e1 (w : List ι) :
    S.matWord w *ᵥ ![1, 0] =
      if S.oWord w = 0 then ![S.gDeriv (S.codeWord 0 w), 0]
      else ![0, S.gDeriv (S.codeWord 1 w)] := by
  rw [matWord_eq]
  rcases zmod_two_cases (S.oWord w) with h | h <;>
    ext j <;> fin_cases j <;> simp [h, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The second column of `A_𝐢`: the image of `e_2` lies on the axis `oWord 𝐢 + 1`. -/
theorem matWord_mulVec_e2 (w : List ι) :
    S.matWord w *ᵥ ![0, 1] =
      if S.oWord w = 0 then ![0, S.gDeriv (S.codeWord 1 w)]
      else ![S.gDeriv (S.codeWord 0 w), 0] := by
  rw [matWord_eq]
  rcases zmod_two_cases (S.oWord w) with h | h <;>
    ext j <;> fin_cases j <;> simp [h, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `thm:matrix_products_g_derivatives`, first identity, for finite words: the non-zero
entry of `A_𝐢 e_1` has modulus `|g'|` along the path of `Σ_Z` over `𝐢` that ends on the
first axis. The entries are summed, since exactly one of them is non-zero. -/
theorem abs_matWord_e1 (w : List ι) :
    |(S.matWord w *ᵥ ![1, 0]) 0| + |(S.matWord w *ᵥ ![1, 0]) 1| =
      |S.gDeriv (S.codeWord (S.oWord w) w)| := by
  rw [matWord_mulVec_e1]
  rcases zmod_two_cases (S.oWord w) with h | h <;> simp [h]

/-- `thm:matrix_products_g_derivatives`, second identity, for finite words: the non-zero
entry of `A_𝐢 e_2` has modulus `|g'|` along the path of `Σ_Z` over `𝐢` that ends on the
second axis. -/
theorem abs_matWord_e2 (w : List ι) :
    |(S.matWord w *ᵥ ![0, 1]) 0| + |(S.matWord w *ᵥ ![0, 1]) 1| =
      |S.gDeriv (S.codeWord (S.oWord w + 1) w)| := by
  rw [matWord_mulVec_e2]
  rcases zmod_two_cases (S.oWord w) with h | h <;>
    simp [h, show (1 : ZMod 2) + 1 = 0 from by decide]

/-! ### The past of a two-sided sequence -/

end System

/-- The word `i_{-n} ⋯ i_{-1}` of the past of `𝐢`. -/
def pastWord {α : Type*} (x : ℤ → α) : ℕ → List α
  | 0 => []
  | n + 1 => x (-((n : ℤ) + 1)) :: pastWord x n

@[simp] theorem pastWord_zero {α : Type*} (x : ℤ → α) : pastWord x 0 = [] := rfl

@[simp] theorem pastWord_succ {α : Type*} (x : ℤ → α) (n : ℕ) :
    pastWord x (n + 1) = x (-((n : ℤ) + 1)) :: pastWord x n := rfl

@[simp] theorem length_pastWord {α : Type*} (x : ℤ → α) (n : ℕ) :
    (pastWord x n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

namespace System

variable {ι : Type*} (S : System ι)

/-- The product `A_{i_{-n}} ⋯ A_{i_{-1}}` is diagonal exactly when `ε_{-n}(𝐢) = 0`. -/
theorem oWord_pastWord (x : ℤ → ι) (n : ℕ) :
    S.oWord (pastWord x n) = eps S.o x (-(n : ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := eps_sub_one S.o x (-(n : ℤ))
    rw [show -(n : ℤ) - 1 = -((n : ℤ) + 1) by ring] at h
    rw [pastWord_succ, oWord_cons, ih, Nat.cast_succ, h, add_comm]

/-- The path of `Σ_Z` over `i_{-n} ⋯ i_{-1}` that ends on the first axis is
`τ_{-n}(𝐢) ⋯ τ_{-1}(𝐢)`. -/
theorem codeWord_pastWord_tau (x : ℤ → ι) (n : ℕ) :
    S.codeWord (eps S.o x (-(n : ℤ))) (pastWord x n) = pastWord (tau S.o x) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := eps_add_one S.o x (-((n : ℤ) + 1))
    rw [show -((n : ℤ) + 1) + 1 = -(n : ℤ) by ring] at h
    rw [pastWord_succ, pastWord_succ, Nat.cast_succ, codeWord_cons, ← h, ih, tau_apply]

/-- The path of `Σ_Z` over `i_{-n} ⋯ i_{-1}` that ends on the second axis is
`ω_{-n}(𝐢) ⋯ ω_{-1}(𝐢)`. -/
theorem codeWord_pastWord_omega (x : ℤ → ι) (n : ℕ) :
    S.codeWord (eps S.o x (-(n : ℤ)) + 1) (pastWord x n) = pastWord (omega S.o x) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := eps_add_one S.o x (-((n : ℤ) + 1))
    rw [show -((n : ℤ) + 1) + 1 = -(n : ℤ) by ring] at h
    rw [pastWord_succ, pastWord_succ, Nat.cast_succ, codeWord_cons, add_right_comm, ← h, ih,
      omega_apply]

/-- `thm:matrix_products_g_derivatives`, first identity:
`|A_{i_{-n}} ⋯ A_{i_{-1}} (1,0)| = |g'_{τ_{-n}(𝐢) ⋯ τ_{-1}(𝐢)}(0)|`. The two entries of the
vector are summed, since exactly one of them is non-zero. -/
theorem abs_matWord_pastWord_e1 (x : ℤ → ι) (n : ℕ) :
    |(S.matWord (pastWord x n) *ᵥ ![1, 0]) 0| + |(S.matWord (pastWord x n) *ᵥ ![1, 0]) 1| =
      |S.gDeriv (pastWord (tau S.o x) n)| := by
  rw [abs_matWord_e1, oWord_pastWord, codeWord_pastWord_tau]

/-- `thm:matrix_products_g_derivatives`, second identity:
`|A_{i_{-n}} ⋯ A_{i_{-1}} (0,1)| = |g'_{ω_{-n}(𝐢) ⋯ ω_{-1}(𝐢)}(0)|`. -/
theorem abs_matWord_pastWord_e2 (x : ℤ → ι) (n : ℕ) :
    |(S.matWord (pastWord x n) *ᵥ ![0, 1]) 0| + |(S.matWord (pastWord x n) *ᵥ ![0, 1]) 1| =
      |S.gDeriv (pastWord (omega S.o x) n)| := by
  rw [abs_matWord_e2, oWord_pastWord, codeWord_pastWord_omega]

end System

end BoxLike
