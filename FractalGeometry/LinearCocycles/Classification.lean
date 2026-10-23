import Mathlib
import FractalGeometry.LinearCocycles.Invertibility
import FractalGeometry.LinearCocycles.Monomial
import FractalGeometry.LinearCocycles.MonomialDeterminant
import FractalGeometry.LinearCocycles.Proximal

namespace FractalGeometry

/-!
Classification of proximal invertible planar matrix families, corresponding to
Lemma 2.7 of Balázs Bárány, Antti Käenmäki and Han Yu, "Finer geometry of planar
self-affine sets", Advances in Mathematics 493 (2026), 110914,
doi:10.1016/j.aim.2026.110914. Numbering follows arXiv:2107.00983v2.
`TupleProximal` requires a nonempty product with eigenvalues of distinct moduli.
-/

open Matrix

variable {ι : Type*}

def TupleIrreducible (A : ι → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ¬ ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ ∀ i, ∃ c : ℝ, A i *ᵥ v = c • v

def TupleStronglyIrreducible (A : ι → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ¬ ∃ s : Finset (Fin 2 → ℝ), s.Nonempty ∧ (∀ v ∈ s, v ≠ 0) ∧
    ∀ i, ∀ v ∈ s, ∃ w ∈ s, ∃ c : ℝ, A i *ᵥ v = c • w

def TupleProximal (A : ι → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ w : List ι, w ≠ [] ∧ IsProximalMatrix (w.map A).prod

def SimultaneouslyMonomial (A : ι → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ P : Matrix (Fin 2) (Fin 2) ℝ, P.det ≠ 0 ∧
    (∀ i, ∃ c : ZMod 2, ∃ a b : ℝ, P⁻¹ * A i * P = monomialMatrix c a b) ∧
    ∃ i, ∃ a b : ℝ, P⁻¹ * A i * P = monomialMatrix 1 a b

def SimultaneouslyTriangular (A : ι → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ P : Matrix (Fin 2) (Fin 2) ℝ, P.det ≠ 0 ∧ ∀ i, (P⁻¹ * A i * P) 1 0 = 0

def colMat (x y : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![x 0, y 0; x 1, y 1]

theorem det_colMat (x y : Fin 2 → ℝ) : (colMat x y).det = x 0 * y 1 - y 0 * x 1 :=
  Matrix.det_fin_two_of _ _ _ _

theorem colMat_mulVec (x y u : Fin 2 → ℝ) : colMat x y *ᵥ u = u 0 • x + u 1 • y := by
  ext j
  fin_cases j <;> simp [colMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem mul_colMat (M : Matrix (Fin 2) (Fin 2) ℝ) (x y : Fin 2 → ℝ) :
    M * colMat x y = colMat (M *ᵥ x) (M *ᵥ y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colMat, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem colMat_mul (x y : Fin 2 → ℝ) (p q r t : ℝ) :
    colMat x y * !![p, q; r, t] = colMat (p • x + r • y) (q • x + t • y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem conj_colMat {x y : Fin 2 → ℝ} (h : (colMat x y).det ≠ 0)
    {M : Matrix (Fin 2) (Fin 2) ℝ} {p q r t : ℝ} (hx : M *ᵥ x = p • x + r • y)
    (hy : M *ᵥ y = q • x + t • y) : (colMat x y)⁻¹ * M * colMat x y = !![p, q; r, t] := by
  rw [Matrix.mul_assoc, mul_colMat, hx, hy, ← colMat_mul, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h), Matrix.one_mul]

theorem exists_eq_smul_add_smul {x y : Fin 2 → ℝ} (h : (colMat x y).det ≠ 0) (v : Fin 2 → ℝ) :
    ∃ α β : ℝ, v = α • x + β • y := by
  refine ⟨((colMat x y)⁻¹ *ᵥ v) 0, ((colMat x y)⁻¹ *ᵥ v) 1, ?_⟩
  rw [← colMat_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h),
    Matrix.one_mulVec]

theorem eq_zero_of_smul_add_smul_eq_zero {x y : Fin 2 → ℝ} (h : (colMat x y).det ≠ 0)
    {e f : ℝ} (hef : e • x + f • y = 0) : e = 0 ∧ f = 0 := by
  have h0 : colMat x y *ᵥ ![e, f] = 0 := by rw [colMat_mulVec]; simpa using hef
  have h1 := Matrix.eq_zero_of_mulVec_eq_zero h h0
  exact ⟨by simpa using congrFun h1 0, by simpa using congrFun h1 1⟩

theorem exists_eq_smul_of_det_colMat_eq_zero {x y : Fin 2 → ℝ} (hx : x ≠ 0)
    (h : (colMat x y).det = 0) : ∃ d : ℝ, y = d • x := by
  rw [det_colMat] at h
  by_cases h0 : x 0 = 0
  · have h1 : x 1 ≠ 0 := by
      intro h1
      apply hx
      ext j
      fin_cases j <;> simp [h0, h1]
    refine ⟨y 1 / x 1, ?_⟩
    ext j
    fin_cases j
    · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
      rw [h0] at h ⊢
      have h3 : y 0 * x 1 = 0 := by linarith
      rcases mul_eq_zero.1 h3 with h2 | h2
      · rw [h2]; simp
      · exact absurd h2 h1
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      field_simp
  · refine ⟨y 0 / x 0, ?_⟩
    ext j
    fin_cases j
    · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
      field_simp
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      field_simp
      linarith

theorem mulVec_conj {P : Matrix (Fin 2) (Fin 2) ℝ} (hP : P.det ≠ 0)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (u : Fin 2 → ℝ) :
    M *ᵥ (P *ᵥ u) = P *ᵥ ((P⁻¹ * M * P) *ᵥ u) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hP), Matrix.one_mul]

theorem trace_inv_mul_mul {P : Matrix (Fin 2) (Fin 2) ℝ} (hP : P.det ≠ 0)
    (M : Matrix (Fin 2) (Fin 2) ℝ) : (P⁻¹ * M * P).trace = M.trace := by
  rw [Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hP),
    Matrix.one_mul]

theorem det_inv_mul_mul {P : Matrix (Fin 2) (Fin 2) ℝ} (hP : P.det ≠ 0)
    (M : Matrix (Fin 2) (Fin 2) ℝ) : (P⁻¹ * M * P).det = M.det :=
  Matrix.det_conj' ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hP)) M

theorem conj_list_prod {P : Matrix (Fin 2) (Fin 2) ℝ} (hP : P.det ≠ 0)
    (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (w : List ι) :
    P⁻¹ * (w.map A).prod * P = (w.map fun i => P⁻¹ * A i * P).prod := by
  have hPP := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hP)
  induction w with
  | nil =>
    rw [List.map_nil, List.prod_nil, List.map_nil, List.prod_nil, Matrix.mul_one,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hP)]
  | cons i w ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ← ih]
    calc P⁻¹ * (A i * (w.map A).prod) * P
        = P⁻¹ * A i * (P * P⁻¹) * (w.map A).prod * P := by
          rw [hPP, Matrix.mul_one, ← Matrix.mul_assoc]
      _ = P⁻¹ * A i * P * (P⁻¹ * (w.map A).prod * P) := by simp only [Matrix.mul_assoc]

theorem IsProximalMatrix.conj {B P : Matrix (Fin 2) (Fin 2) ℝ} (hB : IsProximalMatrix B)
    (hP : P.det ≠ 0) : IsProximalMatrix (P⁻¹ * B * P) := by
  rw [isProximalMatrix_iff_trace_det] at hB ⊢
  obtain ⟨l₁, l₂, hne, htr, hdet⟩ := hB
  exact ⟨l₁, l₂, hne, by rw [trace_inv_mul_mul hP, htr], by rw [det_inv_mul_mul hP, hdet]⟩

theorem false_of_mulVec_eq_smul {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.det ≠ 0)
    {x y z : Fin 2 → ℝ} (hxy : (colMat x y).det ≠ 0) {p q : ℝ} (hx : M *ᵥ x = p • z)
    (hy : M *ᵥ y = q • z) : False := by
  have h1 : (M * colMat x y).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero hM hxy
  rw [mul_colMat, hx, hy, det_colMat] at h1
  apply h1
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem det_list_prod_ne_zero {A : ι → Matrix (Fin 2) (Fin 2) ℝ} (hdet : ∀ i, (A i).det ≠ 0)
    (w : List ι) : (w.map A).prod.det ≠ 0 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [List.map_cons, List.prod_cons, Matrix.det_mul]
    exact mul_ne_zero (hdet i) ih

theorem exists_list_prod_mulVec_eq_smul {A : ι → Matrix (Fin 2) (Fin 2) ℝ} {v : Fin 2 → ℝ}
    (h : ∀ i, ∃ c : ℝ, A i *ᵥ v = c • v) (w : List ι) :
    ∃ c : ℝ, (w.map A).prod *ᵥ v = c • v := by
  induction w with
  | nil => exact ⟨1, by rw [List.map_nil, List.prod_nil, Matrix.one_mulVec, one_smul]⟩
  | cons i w ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨d, hd⟩ := h i
    exact ⟨c * d, by
      rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, hd,
        smul_smul]⟩

theorem exists_list_prod_eq_monomialMatrix {N : ι → Matrix (Fin 2) (Fin 2) ℝ}
    (h : ∀ i, ∃ c : ZMod 2, ∃ a b : ℝ, N i = monomialMatrix c a b) (w : List ι) :
    ∃ c : ZMod 2, ∃ a b : ℝ, (w.map N).prod = monomialMatrix c a b := by
  induction w with
  | nil => exact ⟨0, 1, 1, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩
  | cons i w ih =>
    obtain ⟨c, a, b, hc⟩ := ih
    obtain ⟨c', a', b', hc'⟩ := h i
    exact ⟨_, _, _, by rw [List.map_cons, List.prod_cons, hc, hc', monomialMatrix_mul]⟩

def MapsLines (s : Finset (Fin 2 → ℝ)) (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ v ∈ s, ∃ w ∈ s, ∃ c : ℝ, M *ᵥ v = c • w

theorem MapsLines.one (s : Finset (Fin 2 → ℝ)) : MapsLines s 1 := fun v hv =>
  ⟨v, hv, 1, by rw [Matrix.one_mulVec, one_smul]⟩

theorem MapsLines.mul {s : Finset (Fin 2 → ℝ)} {M N : Matrix (Fin 2) (Fin 2) ℝ}
    (hM : MapsLines s M) (hN : MapsLines s N) : MapsLines s (M * N) := by
  intro v hv
  obtain ⟨w, hw, c, hc⟩ := hN v hv
  obtain ⟨u, hu, d, hd⟩ := hM w hw
  exact ⟨u, hu, c * d, by rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, hd, smul_smul]⟩

theorem MapsLines.list_prod {s : Finset (Fin 2 → ℝ)} {A : ι → Matrix (Fin 2) (Fin 2) ℝ}
    (h : ∀ i, MapsLines s (A i)) (w : List ι) : MapsLines s (w.map A).prod := by
  induction w with
  | nil => exact MapsLines.one s
  | cons i w ih =>
    rw [List.map_cons, List.prod_cons]
    exact (h i).mul ih

theorem MapsLines.pow {s : Finset (Fin 2 → ℝ)} {M : Matrix (Fin 2) (Fin 2) ℝ}
    (h : MapsLines s M) (n : ℕ) : MapsLines s (M ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact MapsLines.one s
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem MapsLines.exists_pow_mulVec_eq_smul {s : Finset (Fin 2 → ℝ)}
    {B : Matrix (Fin 2) (Fin 2) ℝ} (h : MapsLines s B) (hs0 : ∀ v ∈ s, v ≠ 0)
    (hB : B.det ≠ 0) {v : Fin 2 → ℝ} (hv : v ∈ s) :
    ∃ k : ℕ, 0 < k ∧ ∃ c : ℝ, (B ^ k) *ᵥ v = c • v := by
  have hpow := fun n => h.pow n v hv
  choose f hf c hc using hpow
  have hdetpow : ∀ n, (B ^ n).det ≠ 0 := fun n => by
    rw [Matrix.det_pow]; exact pow_ne_zero n hB
  have hc0 : ∀ n, c n ≠ 0 := by
    intro n hn
    have h0 : (B ^ n) *ᵥ v = 0 := by rw [hc n, hn, zero_smul]
    exact hs0 v hv (Matrix.eq_zero_of_mulVec_eq_zero (hdetpow n) h0)
  have key : ∀ n m, n < m → f n = f m → ∃ k : ℕ, 0 < k ∧ ∃ c : ℝ, (B ^ k) *ᵥ v = c • v := by
    intro n m hnm hfeq
    refine ⟨m - n, Nat.sub_pos_of_lt hnm, c m / c n, ?_⟩
    have h1 : (B ^ n) *ᵥ ((B ^ (m - n)) *ᵥ v - (c m / c n) • v) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← pow_add, Nat.add_sub_cancel' hnm.le,
        Matrix.mulVec_smul, hc m, hc n, ← hfeq, smul_smul, div_mul_cancel₀ _ (hc0 n), sub_self]
    exact sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero (hdetpow n) h1)
  obtain ⟨n, m, hnm, hfeq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n => (⟨f n, hf n⟩ : {x // x ∈ s}))
  have hfeq' : f n = f m := congrArg Subtype.val hfeq
  rcases lt_or_gt_of_ne hnm with hlt | hlt
  · exact key n m hlt hfeq'
  · exact key m n hlt hfeq'.symm

theorem mul_self_eq_trace_smul_sub (B : Matrix (Fin 2) (Fin 2) ℝ) :
    B * B = B.trace • B - B.det • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem pow_eq_smul_add_smul {B : Matrix (Fin 2) (Fin 2) ℝ} {l₁ l₂ : ℝ}
    (htr : B.trace = l₁ + l₂) (hdet : B.det = l₁ * l₂) (k : ℕ) :
    ∃ p q : ℝ, B ^ k = p • B + q • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
      p * (l₁ - l₂) = l₁ ^ k - l₂ ^ k ∧ q * (l₁ - l₂) = l₁ * l₂ ^ k - l₂ * l₁ ^ k := by
  induction k with
  | zero => exact ⟨0, 1, by simp, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨p, q, hpq, hp, hq⟩ := ih
    refine ⟨p * (l₁ + l₂) + q, -(p * (l₁ * l₂)), ?_, ?_, ?_⟩
    · rw [pow_succ, hpq, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
        mul_self_eq_trace_smul_sub, htr, hdet]
      module
    · linear_combination (l₁ + l₂) * hp + hq
    · linear_combination (-(l₁ * l₂)) * hp

theorem IsProximalMatrix.exists_mulVec_eq_smul_of_pow {B : Matrix (Fin 2) (Fin 2) ℝ}
    (hB : IsProximalMatrix B) {k : ℕ} (hk : 0 < k) {v : Fin 2 → ℝ} {c : ℝ}
    (h : (B ^ k) *ᵥ v = c • v) : ∃ μ : ℝ, B *ᵥ v = μ • v := by
  obtain ⟨l₁, l₂, hne, htr, hdet⟩ := isProximalMatrix_iff_trace_det.1 hB
  obtain ⟨p, q, hpq, hp, -⟩ := pow_eq_smul_add_smul htr hdet k
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hp
    have h1 : |l₁| ^ k = |l₂| ^ k := by rw [← abs_pow, ← abs_pow, sub_eq_zero.1 hp.symm]
    exact hne ((pow_left_inj₀ (abs_nonneg _) (abs_nonneg _) hk.ne').1 h1)
  refine ⟨(c - q) / p, ?_⟩
  rw [hpq, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
  have h2 : p • (B *ᵥ v) = (c - q) • v := by
    rw [sub_smul, ← h, add_sub_cancel_right]
  rw [div_eq_inv_mul, ← smul_smul, ← h2, smul_smul, inv_mul_cancel₀ hp0, one_smul]

theorem TupleStronglyIrreducible.tupleIrreducible {A : ι → Matrix (Fin 2) (Fin 2) ℝ}
    (h : TupleStronglyIrreducible A) : TupleIrreducible A := by
  rintro ⟨v, hv, hline⟩
  refine h ⟨{v}, Finset.singleton_nonempty v, fun u hu => ?_, fun i u hu => ?_⟩
  · rw [Finset.mem_singleton.1 hu]
    exact hv
  · rw [Finset.mem_singleton.1 hu]
    obtain ⟨c, hc⟩ := hline i
    exact ⟨v, Finset.mem_singleton_self v, c, hc⟩

theorem tuple_trichotomy (A : ι → Matrix (Fin 2) (Fin 2) ℝ) :
    (TupleStronglyIrreducible A ∧ TupleIrreducible A) ∨
      (¬ TupleStronglyIrreducible A ∧ TupleIrreducible A) ∨
      (¬ TupleStronglyIrreducible A ∧ ¬ TupleIrreducible A) := by
  by_cases hsi : TupleStronglyIrreducible A
  · exact Or.inl ⟨hsi, hsi.tupleIrreducible⟩
  · by_cases hi : TupleIrreducible A
    · exact Or.inr (Or.inl ⟨hsi, hi⟩)
    · exact Or.inr (Or.inr ⟨hsi, hi⟩)

theorem not_tupleIrreducible_iff_simultaneouslyTriangular
    {A : ι → Matrix (Fin 2) (Fin 2) ℝ} :
    ¬ TupleIrreducible A ↔ SimultaneouslyTriangular A := by
  constructor
  · intro h
    obtain ⟨v, hv, hline⟩ := not_not.1 h
    have hdetv : (colMat v ![-v 1, v 0]).det ≠ 0 := by
      rw [det_colMat]
      intro h0
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0
      have h1 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
      have h2 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
      exact hv (by ext j; fin_cases j <;> simp [h1, h2])
    refine ⟨_, hdetv, fun i => ?_⟩
    obtain ⟨c, hc⟩ := hline i
    obtain ⟨q, t, hqt⟩ := exists_eq_smul_add_smul hdetv (A i *ᵥ ![-v 1, v 0])
    rw [conj_colMat hdetv (p := c) (r := 0) (by rw [hc, zero_smul, add_zero]) hqt]
    simp
  · rintro ⟨P, hP, h⟩
    refine not_not.2 ⟨P *ᵥ ![1, 0], mulVec_ne_zero_of_det_ne_zero hP ?_,
      fun i => ⟨(P⁻¹ * A i * P) 0 0, ?_⟩⟩
    · intro h0
      simpa using congrFun h0 0
    · rw [mulVec_conj hP, ← Matrix.mulVec_smul]
      congr 1
      ext j
      fin_cases j
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h i]

theorem simultaneouslyMonomial_of_proximal {A : ι → Matrix (Fin 2) (Fin 2) ℝ}
    (hdet : ∀ i, (A i).det ≠ 0) (hprox : TupleProximal A) (hirr : TupleIrreducible A)
    (hnsi : ¬ TupleStronglyIrreducible A) : SimultaneouslyMonomial A := by
  obtain ⟨s, hne, hs0, hinv⟩ := not_not.1 hnsi
  obtain ⟨w, -, hB⟩ := hprox
  have hBs : MapsLines s (w.map A).prod := MapsLines.list_prod hinv w

  have heig : ∀ v ∈ s, ∃ μ : ℝ, (w.map A).prod *ᵥ v = μ • v := fun v hv => by
    obtain ⟨k, hk, c, hc⟩ :=
      hBs.exists_pow_mulVec_eq_smul hs0 (det_list_prod_ne_zero hdet w) hv
    exact hB.exists_mulVec_eq_smul_of_pow hk hc

  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ s, (colMat x y).det ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hirr ⟨x, hs0 x hx, fun i => ?_⟩
    obtain ⟨u, hu, c, hc⟩ := hinv i x hx
    obtain ⟨d, hd⟩ := exists_eq_smul_of_det_colMat_eq_zero (hs0 x hx) (hcon u hu)
    exact ⟨c * d, by rw [hc, hd, smul_smul]⟩

  obtain ⟨μ₁, hμ₁⟩ := heig x hx
  obtain ⟨μ₂, hμ₂⟩ := heig y hy
  have hBconj : (colMat x y)⁻¹ * (w.map A).prod * colMat x y = monomialMatrix 0 μ₁ μ₂ := by
    rw [monomialMatrix_zero]
    exact conj_colMat hxy (by rw [hμ₁, zero_smul, add_zero]) (by rw [hμ₂, zero_smul, zero_add])
  have hμ : |μ₁| ≠ |μ₂| := isProximalMatrix_monomialMatrix_zero.1 (hBconj ▸ hB.conj hxy)

  have haxis : ∀ v ∈ s, (∃ d : ℝ, v = d • x) ∨ ∃ d : ℝ, v = d • y := by
    intro v hv
    obtain ⟨μ, hμv⟩ := heig v hv
    obtain ⟨α, β, rfl⟩ := exists_eq_smul_add_smul hxy v
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hμ₁, hμ₂] at hμv
    have h0 : (α * (μ₁ - μ)) • x + (β * (μ₂ - μ)) • y = 0 := by
      ext j
      have hj := congrFun hμv j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj ⊢
      linear_combination hj
    obtain ⟨h1, h2⟩ := eq_zero_of_smul_add_smul_eq_zero hxy h0
    rcases mul_eq_zero.1 h1 with hα | hα
    · exact Or.inr ⟨β, by rw [hα, zero_smul, zero_add]⟩
    · rcases mul_eq_zero.1 h2 with hβ | hβ
      · exact Or.inl ⟨α, by rw [hβ, zero_smul, add_zero]⟩
      · exact absurd (by rw [sub_eq_zero.1 hα, sub_eq_zero.1 hβ]) hμ
  have himg : ∀ i, ∀ v ∈ s, (∃ d : ℝ, A i *ᵥ v = d • x) ∨ ∃ d : ℝ, A i *ᵥ v = d • y := by
    intro i v hv
    obtain ⟨u, hu, c, hc⟩ := hinv i v hv
    rcases haxis u hu with ⟨d, hd⟩ | ⟨d, hd⟩
    · exact Or.inl ⟨c * d, by rw [hc, hd, smul_smul]⟩
    · exact Or.inr ⟨c * d, by rw [hc, hd, smul_smul]⟩

  have hdich : ∀ i, (∃ p t : ℝ, A i *ᵥ x = p • x ∧ A i *ᵥ y = t • y) ∨
      ∃ q r : ℝ, A i *ᵥ x = r • y ∧ A i *ᵥ y = q • x := by
    intro i
    rcases himg i x hx with ⟨p, hp⟩ | ⟨r, hr⟩ <;> rcases himg i y hy with ⟨q, hq⟩ | ⟨t, ht⟩
    · exact (false_of_mulVec_eq_smul (hdet i) hxy hp hq).elim
    · exact Or.inl ⟨p, t, hp, ht⟩
    · exact Or.inr ⟨q, r, hr, hq⟩
    · exact (false_of_mulVec_eq_smul (hdet i) hxy hr ht).elim
  have hanti : ∀ i q r, A i *ᵥ x = r • y → A i *ᵥ y = q • x →
      (colMat x y)⁻¹ * A i * colMat x y = monomialMatrix 1 q r := by
    intro i q r hr hq
    rw [monomialMatrix_one]
    exact conj_colMat hxy (by rw [hr, zero_smul, zero_add]) (by rw [hq, zero_smul, add_zero])
  refine ⟨colMat x y, hxy, fun i => ?_, ?_⟩
  · rcases hdich i with ⟨p, t, hp, ht⟩ | ⟨q, r, hr, hq⟩
    · refine ⟨0, p, t, ?_⟩
      rw [monomialMatrix_zero]
      exact conj_colMat hxy (by rw [hp, zero_smul, add_zero]) (by rw [ht, zero_smul, zero_add])
    · exact ⟨1, q, r, hanti i q r hr hq⟩
  · by_contra hcon
    push Not at hcon
    refine hirr ⟨x, hs0 x hx, fun i => ?_⟩
    rcases hdich i with ⟨p, t, hp, -⟩ | ⟨q, r, hr, hq⟩
    · exact ⟨p, hp⟩
    · exact absurd (hanti i q r hr hq) (hcon i q r)

theorem not_tupleStronglyIrreducible_of_conj_monomialMatrix {A : ι → Matrix (Fin 2) (Fin 2) ℝ}
    {P : Matrix (Fin 2) (Fin 2) ℝ} (hP : P.det ≠ 0)
    (hbox : ∀ i, ∃ c : ZMod 2, ∃ a b : ℝ, P⁻¹ * A i * P = monomialMatrix c a b) :
    ¬ TupleStronglyIrreducible A := by
  classical
  have he1 : (![1, 0] : Fin 2 → ℝ) ≠ 0 := fun h => by simpa using congrFun h 0
  have he2 : (![0, 1] : Fin 2 → ℝ) ≠ 0 := fun h => by simpa using congrFun h 1
  refine not_not.2 ⟨{P *ᵥ ![1, 0], P *ᵥ ![0, 1]}, ⟨_, Finset.mem_insert_self _ _⟩, ?_, ?_⟩
  · intro v hv
    rw [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact mulVec_ne_zero_of_det_ne_zero hP he1
    · exact mulVec_ne_zero_of_det_ne_zero hP he2
  · intro i v hv
    obtain ⟨c, a, b, hc⟩ := hbox i
    have hm1 : P *ᵥ ![1, 0] ∈ ({P *ᵥ ![1, 0], P *ᵥ ![0, 1]} : Finset (Fin 2 → ℝ)) :=
      Finset.mem_insert_self _ _
    have hm2 : P *ᵥ ![0, 1] ∈ ({P *ᵥ ![1, 0], P *ᵥ ![0, 1]} : Finset (Fin 2 → ℝ)) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rw [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> rw [mulVec_conj hP, hc, monomialMatrix_mulVec] <;>
      rcases zmod_two_cases c with rfl | rfl
    · refine ⟨_, hm1, a, ?_⟩
      rw [← Matrix.mulVec_smul]
      congr 1
      ext j
      fin_cases j <;> simp
    · refine ⟨_, hm2, b, ?_⟩
      rw [← Matrix.mulVec_smul]
      congr 1
      ext j
      fin_cases j <;> simp
    · refine ⟨_, hm2, b, ?_⟩
      rw [← Matrix.mulVec_smul]
      congr 1
      ext j
      fin_cases j <;> simp
    · refine ⟨_, hm1, a, ?_⟩
      rw [← Matrix.mulVec_smul]
      congr 1
      ext j
      fin_cases j <;> simp

theorem SimultaneouslyMonomial.not_tupleStronglyIrreducible
    {A : ι → Matrix (Fin 2) (Fin 2) ℝ} (h : SimultaneouslyMonomial A) :
    ¬ TupleStronglyIrreducible A := by
  obtain ⟨P, hP, hbox, -⟩ := h
  exact not_tupleStronglyIrreducible_of_conj_monomialMatrix hP hbox

theorem SimultaneouslyMonomial.tupleIrreducible {A : ι → Matrix (Fin 2) (Fin 2) ℝ}
    (h : SimultaneouslyMonomial A) (hdet : ∀ i, (A i).det ≠ 0) (hprox : TupleProximal A) :
    TupleIrreducible A := by
  obtain ⟨P, hP, hbox, i₁, a₁, b₁, h₁⟩ := h
  rintro ⟨v, hv, hline⟩
  obtain ⟨w, -, hB⟩ := hprox
  have hPv : P *ᵥ (P⁻¹ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hP),
      Matrix.one_mulVec]
  have hu0 : P⁻¹ *ᵥ v ≠ 0 := by
    intro h0
    apply hv
    rw [← hPv, h0, Matrix.mulVec_zero]
  have hline' : ∀ i, ∃ c : ℝ, (P⁻¹ * A i * P) *ᵥ (P⁻¹ *ᵥ v) = c • (P⁻¹ *ᵥ v) := by
    intro i
    obtain ⟨c, hc⟩ := hline i
    refine ⟨c, ?_⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPv, hc, Matrix.mulVec_smul]
  generalize P⁻¹ *ᵥ v = u at hu0 hline'
  obtain ⟨μ, hμ⟩ := exists_list_prod_mulVec_eq_smul hline' w
  obtain ⟨c, a, b, hcab⟩ := exists_list_prod_eq_monomialMatrix hbox w
  have hprox' : IsProximalMatrix (monomialMatrix c a b) := by
    rw [← hcab, ← conj_list_prod hP]
    exact hB.conj hP
  rcases zmod_two_cases c with rfl | rfl
  swap
  · exact not_isProximalMatrix_monomialMatrix_one _ _ hprox'
  have hab := isProximalMatrix_monomialMatrix_zero.1 hprox'
  obtain ⟨c₁, hc₁⟩ := hline' i₁
  rw [h₁, monomialMatrix_mulVec] at hc₁
  rw [hcab, monomialMatrix_mulVec] at hμ
  have hd : (P⁻¹ * A i₁ * P).det ≠ 0 := by
    rw [det_inv_mul_mul hP]
    exact hdet i₁
  rw [h₁, monomialMatrix_one, Matrix.det_fin_two_of] at hd
  have ha₁ : a₁ ≠ 0 := fun h => hd (by rw [h]; ring)
  have hb₁ : b₁ ≠ 0 := fun h => hd (by rw [h]; ring)
  have e0 : a₁ * u 1 = c₁ * u 0 := by simpa using congrFun hc₁ 0
  have e1 : b₁ * u 0 = c₁ * u 1 := by simpa using congrFun hc₁ 1
  have f0 : a * u 0 = μ * u 0 := by simpa using congrFun hμ 0
  have f1 : b * u 1 = μ * u 1 := by simpa using congrFun hμ 1
  have hu0' : u 0 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at e0
    have h1 : u 1 = 0 := (mul_eq_zero.1 e0).resolve_left ha₁
    exact hu0 (by ext j; fin_cases j <;> simp [h0, h1])
  have hu1' : u 1 ≠ 0 := by
    intro h1
    rw [h1, mul_zero] at e1
    have h0 : u 0 = 0 := (mul_eq_zero.1 e1).resolve_left hb₁
    exact hu0 (by ext j; fin_cases j <;> simp [h0, h1])
  exact hab (by rw [mul_right_cancel₀ hu0' f0, mul_right_cancel₀ hu1' f1])

theorem simultaneouslyMonomial_iff {A : ι → Matrix (Fin 2) (Fin 2) ℝ}
    (hdet : ∀ i, (A i).det ≠ 0) (hprox : TupleProximal A) :
    SimultaneouslyMonomial A ↔ TupleIrreducible A ∧ ¬ TupleStronglyIrreducible A :=
  ⟨fun h => ⟨h.tupleIrreducible hdet hprox, h.not_tupleStronglyIrreducible⟩,
    fun h => simultaneouslyMonomial_of_proximal hdet hprox h.1 h.2⟩

theorem tuple_classification {A : ι → Matrix (Fin 2) (Fin 2) ℝ}
    (hdet : ∀ i, (A i).det ≠ 0) (hprox : TupleProximal A) :
    ((TupleStronglyIrreducible A ∧ ¬ SimultaneouslyMonomial A ∧ ¬ SimultaneouslyTriangular A) ∨
      (¬ TupleStronglyIrreducible A ∧ SimultaneouslyMonomial A ∧ ¬ SimultaneouslyTriangular A) ∨
      (¬ TupleStronglyIrreducible A ∧ ¬ SimultaneouslyMonomial A ∧
        SimultaneouslyTriangular A)) ∧
    (SimultaneouslyMonomial A ↔ TupleIrreducible A ∧ ¬ TupleStronglyIrreducible A) ∧
    (SimultaneouslyTriangular A ↔ ¬ TupleIrreducible A) := by
  have h2 := simultaneouslyMonomial_iff hdet hprox
  have h3 := not_tupleIrreducible_iff_simultaneouslyTriangular (A := A)
  refine ⟨?_, h2, h3.symm⟩
  rcases tuple_trichotomy A with ⟨hsi, hi⟩ | ⟨hsi, hi⟩ | ⟨hsi, hi⟩
  · exact Or.inl ⟨hsi, fun h => (h2.1 h).2 hsi, fun h => h3.2 h hi⟩
  · exact Or.inr (Or.inl ⟨hsi, h2.2 ⟨hi, hsi⟩, fun h => h3.2 h hi⟩)
  · exact Or.inr (Or.inr ⟨hsi, fun h => hi (h2.1 h).1, h3.1 hi⟩)

end FractalGeometry
