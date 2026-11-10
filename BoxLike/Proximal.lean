module

/-
Proximal matrices and proximal tuples of `sec:irreducibility`, and
`thm:box_like_proximal`: a proximal box-like tuple `𝖠` has a diagonal matrix with diagonal
entries of distinct absolute values in `𝖠` or in `𝖠²`.

* `IsProximalMatrix`, `isProximalMatrix_iff_trace_det`: a `2 × 2` real matrix is proximal if
  its characteristic polynomial has two real roots of distinct absolute values, equivalently
  if its trace and determinant are the sum and the product of two such numbers.
* `isProximalMatrix_boxMat_zero`, `not_isProximalMatrix_boxMat_one`: `diag(a, b)` is proximal
  exactly when `|a| ≠ |b|`, and an anti-diagonal matrix is never proximal.
* `System.Proximal`, `System.HasProximalDiagonal.proximal`: the tuple is proximal if some
  product `A_𝐢` over a non-empty word is proximal; a proximal diagonal generator is such a
  product.
* `System.abs_gDeriv_codeWord_mul`: a weight `f` on the two axes that is balanced along every
  letter is balanced along every word.
* `System.abs_gDeriv_codeWord_eq`: if neither `𝖠` nor `𝖠²` contains a proximal diagonal
  generator, then every diagonal product `A_𝐢` has diagonal entries of equal absolute value.
* `absMat`, `pairs`, `System.isProximalMatrix_matWord`, `System.absMat_matWord_eq_smul_pairs`,
  `System.sq_o_of_mem_pairs`, `System.prod_absMat_sq_mat_eq_smul`: the argument of the proof of
  `thm:box_like_proximal`: a proximal product is diagonal with an even number of anti-diagonal
  factors; removing the conformal diagonal factors and pairing the anti-diagonal ones gives
  `|B| = c |B_1 B_2| ⋯ |B_{2k-1} B_{2k}|` with diagonal matrices `B_{2i-1} B_{2i}` of `𝖠²`.
* `System.Proximal.box_like_proximal`, `System.Proximal.hasProximalDiagonal_or_sq`:
  `thm:box_like_proximal`, by that argument; `System.Proximal.hasProximalDiagonal_or_sq_of_cocycle`
  is a second proof by a weighted cocycle.
* `System.Irreducible`, `System.irreducible_of_hasProximalDiagonal`: irreducible tuples, and
  the irreducibility of a box-like tuple with rotations containing a proximal diagonal
  generator.
-/
public import BoxLike.SecondIterate
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

@[expose] public section

namespace BoxLike

open Polynomial Matrix

/-- A `2 × 2` real matrix is proximal, as in `sec:irreducibility`, if it has two real
eigenvalues with different absolute values. The eigenvalues are stated through the
characteristic polynomial: it is the product of `X - l₁` and `X - l₂` with `|l₁| ≠ |l₂|`.
The paper states the definition for `A ∈ GL_2(ℝ)`; the products `A_𝐢` of a `System` are
invertible. -/
def IsProximalMatrix (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ l₁ l₂ : ℝ, |l₁| ≠ |l₂| ∧
    A.charpoly = (Polynomial.X - Polynomial.C l₁) * (Polynomial.X - Polynomial.C l₂)

/-- A `2 × 2` real matrix is proximal exactly when its trace and its determinant are the sum
and the product of two real numbers with different absolute values. -/
theorem isProximalMatrix_iff_trace_det {A : Matrix (Fin 2) (Fin 2) ℝ} :
    IsProximalMatrix A ↔ ∃ l₁ l₂ : ℝ, |l₁| ≠ |l₂| ∧ A.trace = l₁ + l₂ ∧ A.det = l₁ * l₂ := by
  constructor
  · rintro ⟨l₁, l₂, hne, h⟩
    rw [Matrix.charpoly_fin_two] at h
    have h0 := congrArg (Polynomial.eval 0) h
    have h1 := congrArg (Polynomial.eval 1) h
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at h0 h1
    refine ⟨l₁, l₂, hne, ?_, ?_⟩
    · linarith
    · linarith
  · rintro ⟨l₁, l₂, hne, htr, hdet⟩
    refine ⟨l₁, l₂, hne, ?_⟩
    rw [Matrix.charpoly_fin_two, htr, hdet, C_add, C_mul]
    ring

/-- The diagonal matrix `diag(a, b)` is proximal exactly when `|a| ≠ |b|`. -/
theorem isProximalMatrix_boxMat_zero {a b : ℝ} :
    IsProximalMatrix (boxMat 0 a b) ↔ |a| ≠ |b| := by
  rw [isProximalMatrix_iff_trace_det]
  simp only [boxMat_zero, Matrix.trace_fin_two_of, Matrix.det_fin_two_of, mul_zero, sub_zero]
  constructor
  · rintro ⟨l₁, l₂, hne, htr, hdet⟩
    have h : (l₁ - a) * (l₁ - b) = 0 := by
      have hb : b = l₁ + l₂ - a := by linarith
      subst hb
      linear_combination hdet
    rcases mul_eq_zero.1 h with h | h
    · have ha : l₁ = a := by linarith
      have hb : l₂ = b := by linarith
      rwa [ha, hb] at hne
    · have hb : l₁ = b := by linarith
      have ha : l₂ = a := by linarith
      rw [hb, ha] at hne
      exact hne.symm
  · intro h
    exact ⟨a, b, h, rfl, rfl⟩

/-- An anti-diagonal matrix has trace `0`, so its two eigenvalues are opposite and it is not
proximal. -/
theorem not_isProximalMatrix_boxMat_one (a b : ℝ) : ¬ IsProximalMatrix (boxMat 1 a b) := by
  rw [isProximalMatrix_iff_trace_det]
  simp only [boxMat_one, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  rintro ⟨l₁, l₂, hne, htr, -⟩
  have h : l₂ = -l₁ := by linarith
  exact hne (by rw [h, abs_neg])

/-! ### Entrywise absolute values -/

/-- The entrywise absolute value `|C|` of a `2 × 2` matrix, as in the proof of
`thm:box_like_proximal`. -/
def absMat (C : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ := C.map abs

/-- `|C|` of a diagonal or anti-diagonal matrix `C` is the matrix of the same type whose entries
are the moduli of those of `C` (proof of `thm:box_like_proximal`). -/
theorem absMat_boxMat (c : ZMod 2) (a b : ℝ) : absMat (boxMat c a b) = boxMat c |a| |b| := by
  rcases zmod_two_cases c with rfl | rfl <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [absMat]

/-- `|CD| = |C||D|` for diagonal or anti-diagonal matrices `C`, `D` (proof of
`thm:box_like_proximal`). -/
theorem absMat_boxMat_mul (c c' : ZMod 2) (a b a' b' : ℝ) :
    absMat (boxMat c a b * boxMat c' a' b') =
      absMat (boxMat c a b) * absMat (boxMat c' a' b') := by
  rw [boxMat_mul, absMat_boxMat, absMat_boxMat, absMat_boxMat, boxMat_mul, abs_mul, abs_mul]
  rcases zmod_two_cases c with rfl | rfl <;> simp

/-- The identity matrix is its own modulus. -/
theorem absMat_one : absMat (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [absMat]

/-! ### Consecutive pairs of a word -/

/-- The consecutive pairs `(B_1, B_2), (B_3, B_4), …` of a word `B_1 ⋯ B_{2k}`, as in the proof of
`thm:box_like_proximal`. A final unpaired letter is dropped; the proof applies it to words of even
length. -/
def pairs {α : Type*} : List α → List (α × α)
  | [] => []
  | [_] => []
  | x :: y :: r => (x, y) :: pairs r

/-- For a word `B_1 ⋯ B_{2k}` of even length,
`f(B_1) ⋯ f(B_{2k}) = (f(B_1) f(B_2)) ⋯ (f(B_{2k-1}) f(B_{2k}))` (proof of
`thm:box_like_proximal`). -/
theorem prod_map_pairs {α M : Type*} [Monoid M] (f : α → M) :
    ∀ v : List α, Even v.length →
      (v.map f).prod = ((pairs v).map fun p => f p.1 * f p.2).prod
  | [], _ => rfl
  | [_], h => absurd h (by simp)
  | x :: y :: r, h => by
    have hr : Even r.length := by
      rw [List.length_cons, List.length_cons, Nat.even_add_one, Nat.even_add_one, not_not] at h
      exact h
    simp [pairs, prod_map_pairs f r hr, mul_assoc]

/-- Both letters of a pair `(B_{2i-1}, B_{2i})` are letters of the word. -/
theorem mem_pairs {α : Type*} :
    ∀ {v : List α} {p : α × α}, p ∈ pairs v → p.1 ∈ v ∧ p.2 ∈ v
  | [], _, h => by simp [pairs] at h
  | [_], _, h => by simp [pairs] at h
  | x :: y :: r, p, h => by
    rw [pairs, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · obtain ⟨h1, h2⟩ := mem_pairs h
      exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h1),
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h2)⟩

namespace System

variable {ι : Type*}

/-- The tuple `𝖠` is proximal, as in `sec:irreducibility`: the semigroup generated by `𝖠`
contains a proximal matrix, that is, some product `A_𝐢` over a non-empty word is proximal. -/
def Proximal (S : System ι) : Prop :=
  ∃ w : List ι, w ≠ [] ∧ IsProximalMatrix (S.matWord w)

/-- A tuple that contains a proximal diagonal generator is proximal. -/
theorem HasProximalDiagonal.proximal {S : System ι} (h : S.HasProximalDiagonal) :
    S.Proximal := by
  obtain ⟨i, hi, hne⟩ := h
  refine ⟨[i], List.cons_ne_nil _ _, ?_⟩
  rw [matWord_cons, matWord_nil, mul_one, mat, hi]
  exact isProximalMatrix_boxMat_zero.2 hne

/-- A weight `f` on the two axes that is balanced along every letter is balanced along every
word: if `|g_(i,c)'| f(c + o i) = |g_(i,c+1)'| f(c)` for every letter `i` and every axis `c`,
then the derivatives along the two paths of `Σ_Z` over `𝐢` satisfy the same identity with
`o i` replaced by the orientation of `A_𝐢`. This is the induction in the proof of
`thm:box_like_proximal`. -/
theorem abs_gDeriv_codeWord_mul (S : System ι) (f : ZMod 2 → ℝ)
    (hf : ∀ i c, |S.ratio (i, c)| * f (c + S.o i) = |S.ratio (i, c + 1)| * f c)
    (c : ZMod 2) (w : List ι) :
    |S.gDeriv (S.codeWord c w)| * f (c + S.oWord w) =
      |S.gDeriv (S.codeWord (c + 1) w)| * f c := by
  induction w generalizing c with
  | nil => simp
  | cons i w ih =>
    have h := ih (c + S.o i)
    rw [add_right_comm c (S.o i) 1] at h
    rw [codeWord_cons, codeWord_cons, gDeriv_cons, gDeriv_cons, oWord_cons, abs_mul, abs_mul,
      ← add_assoc]
    calc |S.ratio (i, c)| * |S.gDeriv (S.codeWord (c + S.o i) w)| *
          f (c + S.o i + S.oWord w)
        = |S.ratio (i, c)| *
            (|S.gDeriv (S.codeWord (c + S.o i) w)| * f (c + S.o i + S.oWord w)) := by ring
      _ = |S.gDeriv (S.codeWord (c + 1 + S.o i) w)| *
            (|S.ratio (i, c)| * f (c + S.o i)) := by rw [h]; ring
      _ = |S.ratio (i, c + 1)| * |S.gDeriv (S.codeWord (c + 1 + S.o i) w)| * f c := by
          rw [hf]; ring

/-- If neither `𝖠` nor `𝖠²` contains a diagonal matrix with diagonal entries of distinct
absolute values, then the diagonal entries of every diagonal product `A_𝐢` have equal
absolute values. The weight is `f(0) = |a_{i₀}| / |b_{i₀}|` and `f(1) = 1` for an
anti-diagonal generator `i₀`, and `f = 1` if there is none. This is the core of the proof of
`thm:box_like_proximal`. -/
theorem abs_gDeriv_codeWord_eq (S : System ι) (h1 : ¬ S.HasProximalDiagonal)
    (h2 : ¬ S.sq.HasProximalDiagonal) {w : List ι} (hw : S.oWord w = 0) :
    |S.gDeriv (S.codeWord 0 w)| = |S.gDeriv (S.codeWord 1 w)| := by
  -- Diagonal generators have entries of equal absolute value.
  have hdiag : ∀ i, S.o i = 0 → |S.a i| = |S.b i| := fun i hi =>
    not_not.1 fun hne => h1 ⟨i, hi, hne⟩
  -- Two anti-diagonal generators have proportional entries, by the diagonal matrix `A_i A_j`.
  have hanti : ∀ i j, S.o i = 1 → S.o j = 1 → |S.a i| * |S.b j| = |S.b i| * |S.a j| := by
    intro i j hi hj
    have h := not_not.1 fun hne => h2 ⟨(i, j), by
      change S.o i + S.o j = 0
      rw [hi, hj]; decide, hne⟩
    change |S.a i * S.ratio (j, S.o i)| = |S.b i * S.ratio (j, S.o i + 1)| at h
    rw [hi, show (1 : ZMod 2) + 1 = 0 from by decide, ratio_one, ratio_zero, abs_mul,
      abs_mul] at h
    exact h
  -- The weight on the first axis.
  obtain ⟨κ, hκ, hκanti⟩ : ∃ κ : ℝ, 0 < κ ∧ ∀ i, S.o i = 1 → |S.a i| = |S.b i| * κ := by
    by_cases hex : ∃ i₀, S.o i₀ = 1
    · obtain ⟨i₀, hi₀⟩ := hex
      have hb : 0 < |S.b i₀| := abs_pos.2 (S.b_ne_zero i₀)
      refine ⟨|S.a i₀| / |S.b i₀|, div_pos (abs_pos.2 (S.a_ne_zero i₀)) hb, fun i hi => ?_⟩
      rw [mul_div_assoc', ← hanti i i₀ hi hi₀, mul_div_assoc, div_self hb.ne', mul_one]
    · exact ⟨1, one_pos, fun i hi => (hex ⟨i, hi⟩).elim⟩
  have hf : ∀ i c, |S.ratio (i, c)| * (if c + S.o i = 0 then κ else 1) =
      |S.ratio (i, c + 1)| * (if c = 0 then κ else 1) := by
    intro i c
    rcases zmod_two_cases (S.o i) with hi | hi <;> rcases zmod_two_cases c with rfl | rfl <;>
      simp [hi, hdiag i, hκanti i, show (1 : ZMod 2) + 1 = 0 from by decide]
  have h := S.abs_gDeriv_codeWord_mul (fun c => if c = 0 then κ else 1) hf 0 w
  simp only [zero_add, hw, ite_true] at h
  exact mul_right_cancel₀ hκ.ne' h

section Aligned

variable (S : System ι)

/-! ### The proximal product -/

/-- The parity of the number of anti-diagonal letters of `𝐢` is `oWord 𝐢`. -/
theorem oWord_eq_length_filter (w : List ι) :
    S.oWord w = ((w.filter fun i => S.o i = 1).length : ZMod 2) := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [oWord_cons, ih]
    rcases zmod_two_cases (S.o i) with h | h
    · simp [h]
    · simp [h, add_comm]

/-- A proximal product `B = A_𝐢` is diagonal: its diagonal entries have distinct absolute values,
and the number of anti-diagonal factors of `𝐢` is even (proof of `thm:box_like_proximal`). An
anti-diagonal matrix is never proximal. -/
theorem isProximalMatrix_matWord {w : List ι} (hB : IsProximalMatrix (S.matWord w)) :
    S.oWord w = 0 ∧ |S.gDeriv (S.codeWord 0 w)| ≠ |S.gDeriv (S.codeWord 1 w)| ∧
      Even (w.filter fun i => S.o i = 1).length := by
  rw [matWord_eq] at hB
  have ho : S.oWord w = 0 := by
    rcases zmod_two_cases (S.oWord w) with h | h
    · exact h
    · rw [h] at hB
      exact absurd hB (not_isProximalMatrix_boxMat_one _ _)
  rw [ho] at hB
  refine ⟨ho, isProximalMatrix_boxMat_zero.1 hB, ?_⟩
  rw [oWord_eq_length_filter] at ho
  exact (ZMod.natCast_eq_zero_iff_even).1 ho

/-! ### Removing the conformal diagonal factors -/

/-- `|A_𝐢| = |A_{i_1}| ⋯ |A_{i_n}|`: the modulus is multiplicative on diagonal and anti-diagonal
matrices (proof of `thm:box_like_proximal`). -/
theorem absMat_matWord (w : List ι) :
    absMat (S.matWord w) = (w.map fun i => absMat (S.mat i)).prod := by
  induction w with
  | nil => simp [absMat_one]
  | cons i w ih =>
    rw [matWord_cons, List.map_cons, List.prod_cons, ← ih, mat, matWord_eq, absMat_boxMat_mul]

/-- `|A_{i𝐢}| = |A_i| |A_𝐢|`. -/
theorem absMat_matWord_cons (i : ι) (w : List ι) :
    absMat (S.matWord (i :: w)) = absMat (S.mat i) * absMat (S.matWord w) := by
  rw [absMat_matWord, absMat_matWord, List.map_cons, List.prod_cons]

/-- The modulus of a diagonal generator whose diagonal entries have equal absolute value is the
positive scalar matrix `|a_i| I` (proof of `thm:box_like_proximal`). -/
theorem absMat_mat_of_diag {i : ι} (ho : S.o i = 0) (hab : |S.a i| = |S.b i|) :
    absMat (S.mat i) = |S.a i| • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [mat, ho, absMat_boxMat, ← hab]
  ext j k; fin_cases j <;> fin_cases k <;> simp

/-- Removing the conformal diagonal factors (proof of `thm:box_like_proximal`): if every
diagonal letter of `𝐢` has diagonal entries of equal absolute value, then `|A_𝐢| = c |A_{𝐢'}|`,
where `𝐢'` is the subword of the anti-diagonal letters of `𝐢` and `c` is the product of the
moduli `|a_i|` of the diagonal letters. -/
theorem absMat_matWord_eq_smul (w : List ι) (hw : ∀ i ∈ w, S.o i = 0 → |S.a i| = |S.b i|) :
    absMat (S.matWord w) =
      ((w.filter fun i => S.o i = 0).map fun i => |S.a i|).prod •
        absMat (S.matWord (w.filter fun i => S.o i = 1)) := by
  induction w with
  | nil => simp
  | cons i w ih =>
    have ih' := ih fun j hj => hw j (List.mem_cons_of_mem _ hj)
    rw [S.absMat_matWord (i :: w), List.map_cons, List.prod_cons, ← S.absMat_matWord w, ih']
    rcases zmod_two_cases (S.o i) with h | h
    · have hi : |S.a i| = |S.b i| := hw i (List.mem_cons_self ..) h
      rw [S.absMat_mat_of_diag h hi, smul_mul_assoc, one_mul, smul_smul]
      simp [h]
    · have e1 : (i :: w).filter (fun j => S.o j = 0) = w.filter (fun j => S.o j = 0) :=
        List.filter_cons_of_neg (by simp [h])
      have e2 : (i :: w).filter (fun j => S.o j = 1) = i :: w.filter (fun j => S.o j = 1) :=
        List.filter_cons_of_pos (by simp [h])
      rw [e1, e2, S.absMat_matWord_cons, Matrix.mul_smul]

/-- The constant `c` of `absMat_matWord_eq_smul` is positive. -/
theorem prod_abs_a_pos (w : List ι) : 0 < (w.map fun i => |S.a i|).prod := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_pos (abs_pos.2 (S.a_ne_zero i)) ih

/-! ### Pairing the anti-diagonal factors -/

/-- `|B_{2i-1} B_{2i}| = |B_{2i-1}| |B_{2i}|` for the matrix `B_{2i-1} B_{2i}` of `𝖠²`. -/
theorem absMat_sq_mat (p : ι × ι) :
    absMat (S.sq.mat p) = absMat (S.mat p.1) * absMat (S.mat p.2) := by
  rw [sq_mat, mat, mat, absMat_boxMat_mul]

/-- The display of the proof of `thm:box_like_proximal`: if every diagonal factor of `B = A_𝐢`
has diagonal entries of equal absolute value and the number of anti-diagonal factors
`B_1, …, B_{2k}` is even, then `|B| = c |B_1 B_2| |B_3 B_4| ⋯ |B_{2k-1} B_{2k}|` with `c > 0`;
the products `B_{2i-1} B_{2i}` are the matrices of `𝖠²` indexed by the consecutive pairs of
anti-diagonal letters. -/
theorem absMat_matWord_eq_smul_pairs (w : List ι)
    (hw : ∀ i ∈ w, S.o i = 0 → |S.a i| = |S.b i|)
    (heven : Even (w.filter fun i => S.o i = 1).length) :
    absMat (S.matWord w) =
      ((w.filter fun i => S.o i = 0).map fun i => |S.a i|).prod •
        ((pairs (w.filter fun i => S.o i = 1)).map fun p => absMat (S.sq.mat p)).prod := by
  rw [S.absMat_matWord_eq_smul w hw, S.absMat_matWord,
    prod_map_pairs (fun i => absMat (S.mat i)) _ heven]
  simp only [S.absMat_sq_mat]

/-- The products `B_{2i-1} B_{2i}` of two anti-diagonal factors are diagonal (proof of
`thm:box_like_proximal`). -/
theorem sq_o_of_mem_pairs {w : List ι} {p : ι × ι}
    (hp : p ∈ pairs (w.filter fun i => S.o i = 1)) : S.sq.o p = 0 := by
  obtain ⟨h1, h2⟩ := mem_pairs hp
  have h1' : S.o p.1 = 1 := by simpa using (List.mem_filter.1 h1).2
  have h2' : S.o p.2 = 1 := by simpa using (List.mem_filter.1 h2).2
  change S.o p.1 + S.o p.2 = 0
  rw [h1', h2']
  decide

/-- If every diagonal matrix `B_{2i-1} B_{2i}` of `𝖠²` in the product has diagonal entries of
equal absolute value, then `|B_1 B_2| ⋯ |B_{2k-1} B_{2k}|` is a positive scalar matrix. -/
theorem prod_absMat_sq_mat_eq_smul (ps : List (ι × ι))
    (hps : ∀ p ∈ ps, S.sq.o p = 0 ∧ |S.sq.a p| = |S.sq.b p|) :
    (ps.map fun p => absMat (S.sq.mat p)).prod =
      (ps.map fun p => |S.sq.a p|).prod • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨ho, hab⟩ := hps p (List.mem_cons_self ..)
    rw [List.map_cons, List.prod_cons, ih fun q hq => hps q (List.mem_cons_of_mem _ hq),
      S.sq.absMat_mat_of_diag ho hab, List.map_cons, List.prod_cons, smul_mul_smul_comm,
      one_mul]

/-- A proximal product contains at least one anti-diagonal factor when all its diagonal factors
have diagonal entries of equal absolute value, since otherwise `|B|` would be a positive scalar
matrix (proof of `thm:box_like_proximal`). -/
theorem exists_anti_of_isProximalMatrix {w : List ι} (hB : IsProximalMatrix (S.matWord w))
    (hw : ∀ i ∈ w, S.o i = 0 → |S.a i| = |S.b i|) : ∃ i ∈ w, S.o i = 1 := by
  by_contra hcon
  push Not at hcon
  have hnil : (w.filter fun i => S.o i = 1) = [] := by
    rw [List.filter_eq_nil_iff]
    intro i hi
    simpa using hcon i hi
  obtain ⟨ho, hne, -⟩ := S.isProximalMatrix_matWord hB
  have h := S.absMat_matWord_eq_smul w hw
  rw [hnil, matWord_nil, absMat_one, matWord_eq, ho, absMat_boxMat] at h
  have h0 := congrFun (congrFun h 0) 0
  have h1 := congrFun (congrFun h 1) 1
  simp at h0 h1
  exact hne (h0.trans h1.symm)

/-- `thm:box_like_proximal`: if the box-like tuple `𝖠` is proximal, then `𝖠` or `𝖠²` contains a
diagonal matrix whose diagonal entries have distinct absolute values.

The proof is that of the article. A proximal product `B = A_𝐢` is diagonal, with an even number
of anti-diagonal factors (`isProximalMatrix_matWord`). If one of its diagonal factors has
diagonal entries of distinct absolute values, it is the required generator. Otherwise
`|B| = c |B_1 B_2| ⋯ |B_{2k-1} B_{2k}|` with `c > 0` (`absMat_matWord_eq_smul_pairs`), each
`B_{2i-1} B_{2i}` is a diagonal matrix of `𝖠²` (`sq_o_of_mem_pairs`), and if all of them had
diagonal entries of equal absolute value, `|B|` would be a scalar matrix
(`prod_absMat_sq_mat_eq_smul`), contradicting the proximality of `B`. The hypothesis
`System.WithRotations` is not used. -/
theorem Proximal.box_like_proximal {S : System ι} (h : S.Proximal) :
    S.HasProximalDiagonal ∨ S.sq.HasProximalDiagonal := by
  obtain ⟨w, -, hB⟩ := h
  obtain ⟨ho, hne, heven⟩ := S.isProximalMatrix_matWord hB
  -- A diagonal factor with diagonal entries of distinct absolute values completes the proof.
  by_cases hfac : ∃ i ∈ w, S.o i = 0 ∧ |S.a i| ≠ |S.b i|
  · obtain ⟨i, -, hi, hab⟩ := hfac
    exact Or.inl ⟨i, hi, hab⟩
  push Not at hfac
  -- Otherwise one of the products `B_{2i-1} B_{2i}` has this property.
  right
  by_contra hcon
  have hps : ∀ p ∈ pairs (w.filter fun i => S.o i = 1),
      S.sq.o p = 0 ∧ |S.sq.a p| = |S.sq.b p| := fun p hp =>
    ⟨S.sq_o_of_mem_pairs hp, not_not.1 fun hab => hcon ⟨p, S.sq_o_of_mem_pairs hp, hab⟩⟩
  have h := S.absMat_matWord_eq_smul_pairs w hfac heven
  rw [S.prod_absMat_sq_mat_eq_smul _ hps, smul_smul, matWord_eq, ho, absMat_boxMat] at h
  have h0 := congrFun (congrFun h 0) 0
  have h1 := congrFun (congrFun h 1) 1
  simp at h0 h1
  exact hne (h0.trans h1.symm)

end Aligned

/-- A second proof of `thm:box_like_proximal`, by a weighted cocycle: if neither `𝖠` nor `𝖠²`
contains a diagonal matrix whose diagonal entries have distinct absolute values, every diagonal
product has diagonal entries of equal absolute value (`System.abs_gDeriv_codeWord_eq`), while an
anti-diagonal product is never proximal. The certified statement
`Proximal.hasProximalDiagonal_or_sq` uses the argument of the article instead. -/
theorem Proximal.hasProximalDiagonal_or_sq_of_cocycle {S : System ι} (h : S.Proximal) :
    S.HasProximalDiagonal ∨ S.sq.HasProximalDiagonal := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨w, -, hw⟩ := h
  rw [matWord_eq] at hw
  rcases zmod_two_cases (S.oWord w) with ho | ho
  · rw [ho] at hw
    exact isProximalMatrix_boxMat_zero.1 hw (S.abs_gDeriv_codeWord_eq hcon.1 hcon.2 ho)
  · rw [ho] at hw
    exact not_isProximalMatrix_boxMat_one _ _ hw


/-- `thm:box_like_proximal`: if the box-like tuple `𝖠` is proximal, then `𝖠` or `𝖠²` contains
a diagonal matrix whose diagonal entries have distinct absolute values, by the argument of the
article (`System.Proximal.box_like_proximal`). The hypothesis `System.WithRotations` of the paper
is not used. -/
theorem Proximal.hasProximalDiagonal_or_sq {S : System ι} (h : S.Proximal) :
    S.HasProximalDiagonal ∨ S.sq.HasProximalDiagonal :=
  Proximal.box_like_proximal h
/-- The tuple `𝖠` is irreducible (`sec:irreducibility`): no line through the origin is
invariant under every `A_i`, that is, the matrices have no common eigenvector. -/
def Irreducible (S : System ι) : Prop :=
  ¬ ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ ∀ i, ∃ c : ℝ, S.mat i *ᵥ v = c • v

/-- A box-like tuple with rotations containing a proximal diagonal generator is irreducible:
the only invariant lines of that generator are the coordinate axes, and an anti-diagonal
generator exchanges them. This is the observation in the proofs of
`prop:ssc_no_overlap_not_pesc` and `thm:two-block-normalisation`. -/
theorem irreducible_of_hasProximalDiagonal {S : System ι} (hrot : S.WithRotations)
    (hprox : S.HasProximalDiagonal) : S.Irreducible := by
  rintro ⟨v, hv, h⟩
  obtain ⟨i₀, ho₀, hab⟩ := hprox
  obtain ⟨i₁, ho₁⟩ := hrot.2
  obtain ⟨c₀, hc₀⟩ := h i₀
  obtain ⟨c₁, hc₁⟩ := h i₁
  have e00 := congrFun hc₀ 0
  have e01 := congrFun hc₀ 1
  have e10 := congrFun hc₁ 0
  have e11 := congrFun hc₁ 1
  simp only [mat, ho₀, ho₁, boxMat_zero, boxMat_one, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Pi.smul_apply,
    smul_eq_mul, zero_mul, add_zero, zero_add] at e00 e01 e10 e11
  have hne : S.a i₀ ≠ S.b i₀ := fun he => hab (by rw [he])
  have hv01 : v 0 = 0 ∨ v 1 = 0 := by
    by_contra hcon
    rw [not_or] at hcon
    have h1 : S.a i₀ = c₀ := mul_right_cancel₀ hcon.1 e00
    have h2 : S.b i₀ = c₀ := mul_right_cancel₀ hcon.2 e01
    exact hne (h1.trans h2.symm)
  apply hv
  funext j
  rcases hv01 with h0 | h1
  · have h1 : v 1 = 0 := by
      rw [h0, mul_zero] at e10
      exact (mul_eq_zero.1 e10).resolve_left (S.a_ne_zero i₁)
    fin_cases j <;> simp [h0, h1]
  · have h0 : v 0 = 0 := by
      rw [h1, mul_zero] at e11
      exact (mul_eq_zero.1 e11).resolve_left (S.b_ne_zero i₁)
    fin_cases j <;> simp [h0, h1]

end System

end BoxLike
