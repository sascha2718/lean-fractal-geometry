module

/-
The `n`-th iterate of a probability vector grouped by linear part: the combinatorial and
probabilistic part of Rapaport's proof of Theorem 1.3 (arXiv:2309.03985, lines 2095 to 2137 of
`rapaport.tex`), in the plane. For a strictly positive probability vector `p` on `ι` and the
product vector `p^{×n} = (p_u)_{u ∈ ι^n}`, the words are grouped by the pair of products
`(∏ A(u_k), ∏ B(u_k))`, for the diagonal entries `A = a`, `B = b` of a diagonal system the
linear part `diag(r_{u,1}, r_{u,2})` of `φ_u`. The group of `r` has the mass `α_r` and the
conditional vector `q_r = p^{×n}|_{W_r} / α_r` of entropy `H(q_r)`.

* `pw`, `pw_pos`, `sum_pw_mul_prod`, `sum_pw`, `sum_pw_mul_apply`, `sum_pw_mul_apply_mul_apply`:
  the product vector `p^{×n}` and the expectations of functions of one or two coordinates.
* `sum_negMulLog_pw`: `H(p^{×n}) = n H(p)`.
* `sum_pw_mul_sq`, `sum_pw_filter_le`: the variance of `∑_k g(u_k)` is `n Var_p(g)`, and the
  weak law of large numbers in Chebyshev's form (lines 2131 to 2134).
* `fibMass`, `fibEnt`, `mem_filter_key`, `fibMass_pos`, `sum_div_fibMass`, `fibEnt_nonneg`,
  `sum_fibMass_mul`, `sum_fibMass`: the masses `α_r` and the entropies `H(q_r)` of the groups of
  a key `K`.
* `sum_negMulLog_le_log_card_finset`, `fibEnt_le_log_card`: `H ≤ log` of the number of atoms.
* `sum_negMulLog_eq_mixture`: the exact mixture identity
  `H(p^{×n}) = ∑_r (α_r H(q_r) + η(α_r))`, the convexity bound of lines 2111 to 2116.
* `lin`, `log_abs_lin_fst`, `log_abs_lin_snd`, `prod_apply_eq_prod_pow`, `card_image_lin_le`:
  the linear parts and `|R| ≤ (n + 1)^{|ι|}` (lines 2106 to 2110).
* `tendsto_log_succ_div`: `log (n + 1) / n → 0`.
* `eventually_exists_good_group`: for every `ε > 0` and every large `n` there is a group `r` with
  `H(q_r) ≥ n (H(p) - ε)` and `|log |r_j| - n λ_j| < n ε` for both coordinates, the group found
  at lines 2142 to 2147 of the source, without the condition `|r_1| ≠ |r_2|` (see
  `Rapaport/Diagonal/Reduction.lean`).
-/
public import BoxLike.Rapaport.Entropy.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

@[expose] public section

namespace BoxLike.Rapaport.Diagonal

open Finset Filter Topology

/-! ### The product vector `p^{×n}` -/

section Words

variable {ι : Type*} {p : ι → ℝ}

/-- The weight `p_u = p_{u_0} ⋯ p_{u_{n-1}}` of a word `u ∈ ι^n` under the product vector
`p^{×n}` (line 2097 of the source). -/
noncomputable def pw (p : ι → ℝ) {n : ℕ} (u : Fin n → ι) : ℝ := ∏ k, p (u k)

/-- The product vector of a strictly positive vector is strictly positive. -/
theorem pw_pos (hp : ∀ i, 0 < p i) {n : ℕ} (u : Fin n → ι) : 0 < pw p u :=
  prod_pos fun k _ => hp (u k)

variable [Fintype ι]

/-- The expectation of a product of functions of the coordinates under `p^{×n}` is the product
of the expectations. -/
theorem sum_pw_mul_prod (p : ι → ℝ) {n : ℕ} (F : Fin n → ι → ℝ) :
    ∑ u : Fin n → ι, pw p u * ∏ k, F k (u k) = ∏ k, ∑ i, p i * F k i := by
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun u _ => ?_
  rw [pw, ← prod_mul_distrib]

/-- `p^{×n}` is a probability vector. -/
theorem sum_pw (hp1 : ∑ i, p i = 1) (n : ℕ) : ∑ u : Fin n → ι, pw p u = 1 := by
  have h := sum_pw_mul_prod p (fun (_ : Fin n) (_ : ι) => (1 : ℝ))
  simpa [hp1] using h

/-- The expectation of a function of the `k`-th coordinate under `p^{×n}`. -/
theorem sum_pw_mul_apply (hp1 : ∑ i, p i = 1) {n : ℕ} (k : Fin n) (f : ι → ℝ) :
    ∑ u : Fin n → ι, pw p u * f (u k) = ∑ i, p i * f i := by
  have h := sum_pw_mul_prod p (fun m i => if m = k then f i else 1)
  have e : ∀ u : Fin n → ι, (∏ m, if m = k then f (u m) else 1) = f (u k) := fun u => by
    simp [prod_ite_eq']
  have e2 : ∀ m, ∑ i, p i * (if m = k then f i else 1) = if m = k then ∑ i, p i * f i else 1 :=
    fun m => by split_ifs <;> simp [hp1]
  simp only [e, e2] at h
  rw [h]
  simp [prod_ite_eq']

/-- The expectation of the product of functions of two distinct coordinates under `p^{×n}`. -/
theorem sum_pw_mul_apply_mul_apply (hp1 : ∑ i, p i = 1) {n : ℕ} {k l : Fin n} (hkl : k ≠ l)
    (f g : ι → ℝ) :
    ∑ u : Fin n → ι, pw p u * (f (u k) * g (u l)) = (∑ i, p i * f i) * ∑ i, p i * g i := by
  have h := sum_pw_mul_prod p
    (fun m i => (if m = k then f i else 1) * (if m = l then g i else 1))
  have e : ∀ u : Fin n → ι,
      (∏ m, (if m = k then f (u m) else 1) * (if m = l then g (u m) else 1)) =
        f (u k) * g (u l) := fun u => by
    rw [prod_mul_distrib]
    simp [prod_ite_eq']
  have e2 : ∀ m, ∑ i, p i * ((if m = k then f i else 1) * (if m = l then g i else 1)) =
      (if m = k then ∑ i, p i * f i else 1) * (if m = l then ∑ i, p i * g i else 1) := fun m => by
    by_cases hk : m = k
    · subst hk
      simp [hkl]
    · by_cases hl : m = l
      · subst hl
        simp [hk]
      · simp [hk, hl, hp1]
  simp only [e, e2] at h
  rw [h, prod_mul_distrib]
  simp [prod_ite_eq']

/-- `H(p^{×n}) = n H(p)` (line 2111 of the source). -/
theorem sum_negMulLog_pw (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1) (n : ℕ) :
    ∑ u : Fin n → ι, Real.negMulLog (pw p u) = n * ∑ i, Real.negMulLog (p i) := by
  have e : ∀ u : Fin n → ι,
      Real.negMulLog (pw p u) = -∑ k, pw p u * Real.log (p (u k)) := fun u => by
    rw [Real.negMulLog, pw, Real.log_prod (fun k _ => (hp (u k)).ne'), ← mul_sum, ← pw]
    ring
  calc ∑ u : Fin n → ι, Real.negMulLog (pw p u)
      = -∑ k : Fin n, ∑ u : Fin n → ι, pw p u * Real.log (p (u k)) := by
        rw [sum_congr rfl fun u _ => e u, sum_neg_distrib, sum_comm]
    _ = -∑ k : Fin n, ∑ i, p i * Real.log (p i) := by
        rw [sum_congr rfl fun k _ => sum_pw_mul_apply hp1 k (fun i => Real.log (p i))]
    _ = n * ∑ i, Real.negMulLog (p i) := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Real.negMulLog, neg_mul,
          sum_neg_distrib, mul_neg]

/-- The variance of `∑_k g(u_k)` under `p^{×n}` for a centred `g`: `n Var_p(g)`. -/
theorem sum_pw_mul_sq (hp1 : ∑ i, p i = 1) {g : ι → ℝ} (hg : ∑ i, p i * g i = 0) (n : ℕ) :
    ∑ u : Fin n → ι, pw p u * (∑ k, g (u k)) ^ 2 = n * ∑ i, p i * g i ^ 2 := by
  calc ∑ u : Fin n → ι, pw p u * (∑ k, g (u k)) ^ 2
      = ∑ u : Fin n → ι, ∑ k, ∑ l, pw p u * (g (u k) * g (u l)) := by
        refine sum_congr rfl fun u _ => ?_
        rw [sq, sum_mul_sum, mul_sum]
        exact sum_congr rfl fun k _ => by rw [mul_sum]
    _ = ∑ k : Fin n, ∑ l : Fin n, ∑ u : Fin n → ι, pw p u * (g (u k) * g (u l)) := by
        rw [sum_comm]
        exact sum_congr rfl fun k _ => sum_comm
    _ = ∑ k : Fin n, ∑ l : Fin n, if k = l then ∑ i, p i * g i ^ 2 else 0 := by
        refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
        split_ifs with hkl
        · subst hkl
          rw [← sum_pw_mul_apply hp1 k (fun i => g i ^ 2)]
          exact sum_congr rfl fun u _ => by ring
        · rw [sum_pw_mul_apply_mul_apply hp1 hkl, hg, zero_mul]
    _ = n * ∑ i, p i * g i ^ 2 := by simp

/-- The weak law of large numbers in Chebyshev's form (lines 2131 to 2134 of the source): the
`p^{×n}`-mass of the words with `|∑_k f(u_k) - n λ| ≥ n ε`, `λ = ∑ p_i f_i`, is at most
`Var_p(f) / (n ε²)`. -/
theorem sum_pw_filter_le (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1) (f : ι → ℝ) {n : ℕ}
    (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    ∑ u ∈ univ.filter (fun u : Fin n → ι => n * ε ≤ |∑ k, f (u k) - n * ∑ i, p i * f i|),
        pw p u ≤ (∑ i, p i * (f i - ∑ j, p j * f j) ^ 2) / (n * ε ^ 2) := by
  set m := ∑ j, p j * f j with hm
  set g : ι → ℝ := fun i => f i - m with hg_def
  have hg : ∑ i, p i * g i = 0 := by
    simp only [hg_def, mul_sub, sum_sub_distrib, ← sum_mul, hp1, one_mul, hm, sub_self]
  have hX : ∀ u : Fin n → ι, ∑ k, f (u k) - n * m = ∑ k, g (u k) := fun u => by
    simp [hg_def, sum_sub_distrib]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnε : 0 < (n : ℝ) * ε := mul_pos hn' hε
  calc ∑ u ∈ univ.filter (fun u : Fin n → ι => n * ε ≤ |∑ k, f (u k) - n * m|), pw p u
      ≤ ∑ u ∈ univ.filter (fun u : Fin n → ι => n * ε ≤ |∑ k, f (u k) - n * m|),
          pw p u * ((∑ k, g (u k)) ^ 2 / (n * ε) ^ 2) := by
        refine sum_le_sum fun u hu => ?_
        have hu' := (mem_filter.1 hu).2
        rw [hX u] at hu'
        have h1 : 1 ≤ (∑ k, g (u k)) ^ 2 / (n * ε) ^ 2 := by
          rw [one_le_div (by positivity), ← sq_abs (∑ k, g (u k))]
          exact pow_le_pow_left₀ hnε.le hu' 2
        exact le_mul_of_one_le_right (pw_pos hp u).le h1
    _ ≤ ∑ u : Fin n → ι, pw p u * ((∑ k, g (u k)) ^ 2 / (n * ε) ^ 2) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          fun u _ _ => mul_nonneg (pw_pos hp u).le (by positivity)
    _ = (∑ u : Fin n → ι, pw p u * (∑ k, g (u k)) ^ 2) / (n * ε) ^ 2 := by
        rw [sum_div]
        exact sum_congr rfl fun u _ => by ring
    _ = (∑ i, p i * g i ^ 2) / (n * ε ^ 2) := by
        rw [sum_pw_mul_sq hp1 hg]
        field_simp

end Words

/-! ### Grouping by a key: masses and conditional entropies -/

section Mixture

variable {Ω β : Type*} [Fintype Ω] [DecidableEq β] {P : Ω → ℝ}

/-- The mass `α_r = p^{×n}(W_r)` of the group `W_r = {ω : K ω = r}` (line 2101 of the
source). -/
noncomputable def fibMass (P : Ω → ℝ) (K : Ω → β) (r : β) : ℝ :=
  ∑ ω ∈ univ.filter (fun ω => K ω = r), P ω

/-- The entropy `H(q_r)` of the conditional vector `q_r = P|_{W_r} / α_r` (lines 2102 to 2105
of the source). -/
noncomputable def fibEnt (P : Ω → ℝ) (K : Ω → β) (r : β) : ℝ :=
  ∑ ω ∈ univ.filter (fun ω => K ω = r), Real.negMulLog (P ω / fibMass P K r)

/-- Every `ω` lies in its own group `W_{K ω}`. -/
theorem mem_filter_key (K : Ω → β) (ω : Ω) : ω ∈ univ.filter (fun ω' => K ω' = K ω) :=
  mem_filter.2 ⟨mem_univ _, rfl⟩

/-- The mass `α_r` of a non-empty group is positive for a strictly positive `P`. -/
theorem fibMass_pos (hP : ∀ ω, 0 < P ω) (K : Ω → β) (ω₀ : Ω) : 0 < fibMass P K (K ω₀) :=
  sum_pos (fun ω _ => hP ω) ⟨ω₀, mem_filter_key K ω₀⟩

/-- The conditional vector `q_r` is a probability vector. -/
theorem sum_div_fibMass (hP : ∀ ω, 0 < P ω) (K : Ω → β) (ω₀ : Ω) :
    ∑ ω ∈ univ.filter (fun ω => K ω = K ω₀), P ω / fibMass P K (K ω₀) = 1 := by
  rw [← sum_div, div_eq_one_iff_eq (fibMass_pos hP K ω₀).ne']
  rfl

/-- `H(q_r) ≥ 0`: the conditional weights lie in `[0, 1]`. -/
theorem fibEnt_nonneg (hP : ∀ ω, 0 < P ω) (K : Ω → β) (r : β) : 0 ≤ fibEnt P K r := by
  refine sum_nonneg fun ω hω => ?_
  have hle : P ω ≤ fibMass P K r := single_le_sum (fun ω _ => (hP ω).le) hω
  have hα : 0 < fibMass P K r := (hP ω).trans_le hle
  exact Real.negMulLog_nonneg (div_nonneg (hP ω).le hα.le) ((div_le_one hα).2 hle)

/-- Averaging over the groups: `∑_r α_r φ(r) = ∑_ω P(ω) φ(K ω)`. -/
theorem sum_fibMass_mul (P : Ω → ℝ) (K : Ω → β) (φ : β → ℝ) :
    ∑ r ∈ univ.image K, fibMass P K r * φ r = ∑ ω, P ω * φ (K ω) := by
  rw [← sum_fiberwise_of_maps_to (fun ω _ => mem_image_of_mem K (mem_univ ω))
    (fun ω => P ω * φ (K ω))]
  refine sum_congr rfl fun r _ => ?_
  rw [fibMass, sum_mul]
  exact sum_congr rfl fun ω hω => by rw [(mem_filter.1 hω).2]

/-- The masses `α_r` form a probability vector when `P` does. -/
theorem sum_fibMass (P : Ω → ℝ) (K : Ω → β) :
    ∑ r ∈ univ.image K, fibMass P K r = ∑ ω, P ω := by
  simpa using sum_fibMass_mul P K (fun _ => 1)

/-- The entropy of a probability vector supported on a finite set is at most the logarithm of
its size. -/
theorem sum_negMulLog_le_log_card_finset {γ : Type*} {s : Finset γ} {w : γ → ℝ}
    (hw0 : ∀ x ∈ s, 0 ≤ w x) (hw1 : ∑ x ∈ s, w x = 1) :
    ∑ x ∈ s, Real.negMulLog (w x) ≤ Real.log s.card := by
  have h := sum_negMulLog_le_log_card (ι := s) (w := fun x => w x) (fun x => hw0 x x.2)
    (by rw [sum_coe_sort s w]; exact hw1)
  rwa [sum_coe_sort s (fun x => Real.negMulLog (w x)), Fintype.card_coe] at h

/-- `H(q_r) ≤ log |Ω|`. -/
theorem fibEnt_le_log_card (hP : ∀ ω, 0 < P ω) (K : Ω → β) (ω₀ : Ω) :
    fibEnt P K (K ω₀) ≤ Real.log (Fintype.card Ω) := by
  refine (sum_negMulLog_le_log_card_finset
    (fun ω _ => (div_pos (hP ω) (fibMass_pos hP K ω₀)).le) (sum_div_fibMass hP K ω₀)).trans ?_
  exact Real.log_le_log (by exact_mod_cast card_pos.2 ⟨ω₀, mem_filter_key K ω₀⟩)
    (by exact_mod_cast card_le_univ _)

/-- The exact mixture identity `H(P) = ∑_r (α_r H(q_r) + η(α_r))`, `η = negMulLog`, behind the
convexity bound (2.4) as used at lines 2111 to 2116 of the source. -/
theorem sum_negMulLog_eq_mixture (hP : ∀ ω, 0 < P ω) (K : Ω → β) :
    ∑ ω, Real.negMulLog (P ω) = ∑ r ∈ univ.image K,
      (fibMass P K r * fibEnt P K r + Real.negMulLog (fibMass P K r)) := by
  rw [← sum_fiberwise_of_maps_to (fun ω _ => mem_image_of_mem K (mem_univ ω))
    (fun ω => Real.negMulLog (P ω))]
  refine sum_congr rfl fun r hr => ?_
  obtain ⟨ω₀, -, rfl⟩ := mem_image.1 hr
  have hα := (fibMass_pos hP K ω₀).ne'
  calc ∑ ω ∈ univ.filter (fun ω => K ω = K ω₀), Real.negMulLog (P ω)
      = ∑ ω ∈ univ.filter (fun ω => K ω = K ω₀),
          Real.negMulLog (fibMass P K (K ω₀) * (P ω / fibMass P K (K ω₀))) :=
        sum_congr rfl fun ω _ => by rw [mul_div_cancel₀ _ hα]
    _ = ∑ ω ∈ univ.filter (fun ω => K ω = K ω₀),
          (P ω / fibMass P K (K ω₀) * Real.negMulLog (fibMass P K (K ω₀)) +
            fibMass P K (K ω₀) * Real.negMulLog (P ω / fibMass P K (K ω₀))) :=
        sum_congr rfl fun ω _ => Real.negMulLog_mul _ _
    _ = _ := by
        rw [sum_add_distrib, ← sum_mul, ← mul_sum, sum_div_fibMass hP K ω₀, one_mul, fibEnt]
        ring

end Mixture

/-! ### The linear parts of the words of length `n` -/

section Linear

variable {ι : Type*}

/-- The pair of products `(∏_k A(u_k), ∏_k B(u_k))`: for the diagonal entries of a diagonal
system, the linear part `diag(r_{u,1}, r_{u,2})` of `φ_u` (line 2098 of the source). -/
noncomputable def lin (A B : ι → ℝ) {n : ℕ} (u : Fin n → ι) : ℝ × ℝ :=
  (∏ k, A (u k), ∏ k, B (u k))

/-- `log |r_{u,1}| = ∑_k log |A(u_k)|`: the first exponent of a word is a sum along the word. -/
theorem log_abs_lin_fst {A : ι → ℝ} (hA : ∀ i, A i ≠ 0) (B : ι → ℝ) {n : ℕ} (u : Fin n → ι) :
    Real.log |(lin A B u).1| = ∑ k, Real.log |A (u k)| := by
  rw [lin, abs_prod, Real.log_prod fun k _ => abs_ne_zero.2 (hA (u k))]

/-- `log |r_{u,2}| = ∑_k log |B(u_k)|`: the second exponent of a word is a sum along the word. -/
theorem log_abs_lin_snd (A : ι → ℝ) {B : ι → ℝ} (hB : ∀ i, B i ≠ 0) {n : ℕ} (u : Fin n → ι) :
    Real.log |(lin A B u).2| = ∑ k, Real.log |B (u k)| := by
  rw [lin, abs_prod, Real.log_prod fun k _ => abs_ne_zero.2 (hB (u k))]

variable [Fintype ι]

/-- The product of a function along a word depends only on the number of occurrences of each
letter. -/
theorem prod_apply_eq_prod_pow [DecidableEq ι] (A : ι → ℝ) {n : ℕ} (u : Fin n → ι) :
    ∏ k, A (u k) = ∏ i, A i ^ (univ.filter fun k => u k = i).card := by
  rw [← prod_fiberwise' univ u A]
  exact prod_congr rfl fun i _ => prod_const _

/-- `|R| ≤ (n + 1)^{|ι|}` (lines 2106 to 2110 of the source): the linear part of a word is
determined by its vector of letter counts. -/
theorem card_image_lin_le [DecidableEq ι] (A B : ι → ℝ) (n : ℕ) :
    ((univ : Finset (Fin n → ι)).image (lin A B)).card ≤ (n + 1) ^ Fintype.card ι := by
  have hcnt : ∀ (u : Fin n → ι) (i : ι), (univ.filter fun k => u k = i).card < n + 1 :=
    fun u i => Nat.lt_succ_of_le ((card_filter_le _ _).trans (by simp))
  let cnt : (Fin n → ι) → ι → Fin (n + 1) := fun u i => ⟨_, hcnt u i⟩
  let G : (ι → Fin (n + 1)) → ℝ × ℝ :=
    fun N => (∏ i, A i ^ (N i : ℕ), ∏ i, B i ^ (N i : ℕ))
  have hG : ∀ u : Fin n → ι, lin A B u = G (cnt u) := fun u => by
    simp only [lin, G, cnt, prod_apply_eq_prod_pow A u, prod_apply_eq_prod_pow B u]
  calc ((univ : Finset (Fin n → ι)).image (lin A B)).card
      ≤ ((univ : Finset (ι → Fin (n + 1))).image G).card :=
        card_le_card (image_subset_iff.2 fun u _ => mem_image.2 ⟨cnt u, mem_univ _, (hG u).symm⟩)
    _ ≤ (univ : Finset (ι → Fin (n + 1))).card := card_image_le
    _ = (n + 1) ^ Fintype.card ι := by simp

end Linear

/-- `log (n + 1) / n → 0`. -/
theorem tendsto_log_succ_div :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  refine h.congr fun n => ?_
  simp

/-! ### A group with large entropy and typical exponents -/

section Selection

variable {ι : Type*} [Fintype ι] {p : ι → ℝ}

/-- The group found at lines 2111 to 2147 of the source, without the condition
`|r_1| ≠ |r_2|`: for a strictly positive probability vector `p`, non-zero entries `A`, `B` and
`ε > 0`, for every large `n` there is a word `u₀ ∈ ι^n` whose group `r = lin A B u₀` has
`H(q_r) ≥ n (H(p) - ε)`, `|log |r_1| - n λ_A| < n ε` and `|log |r_2| - n λ_B| < n ε`, where
`λ_A = ∑ p_i log |A_i|` and `λ_B = ∑ p_i log |B_i|`. Otherwise the mixture identity
`n H(p) = ∑_r (α_r H(q_r) + η(α_r))`, the bounds `H(q_r) ≤ n log |ι|`, `H(α) ≤ log |R|`,
`|R| ≤ (n + 1)^{|ι|}` and the weak law of large numbers for the mass of the atypical groups
give `ε ≤ (ε + log |ι|) (V_A + V_B) / (n ε²) + |ι| log (n + 1) / n`, which fails for large
`n`. -/
theorem eventually_exists_good_group (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1) {A B : ι → ℝ}
    (hA : ∀ i, A i ≠ 0) (hB : ∀ i, B i ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ u₀ : Fin n → ι,
      n * (∑ i, Real.negMulLog (p i) - ε) ≤ fibEnt (pw p (n := n)) (lin A B) (lin A B u₀) ∧
      |Real.log |(lin A B u₀).1| - n * ∑ i, p i * Real.log (|A i|)| < n * ε ∧
      |Real.log |(lin A B u₀).2| - n * ∑ i, p i * Real.log (|B i|)| < n * ε := by
  classical
  have : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hp1
  set H := ∑ i, Real.negMulLog (p i) with hH_def
  set fa : ι → ℝ := fun i => Real.log |A i| with hfa
  set fb : ι → ℝ := fun i => Real.log |B i| with hfb
  set la := ∑ i, p i * fa i with hla
  set lb := ∑ i, p i * fb i with hlb
  set Va := ∑ i, p i * (fa i - la) ^ 2 with hVa
  set Vb := ∑ i, p i * (fb i - lb) ^ 2 with hVb
  set L := Real.log (Fintype.card ι) with hL
  have hH : 0 ≤ H := sum_nonneg fun i _ => Real.negMulLog_nonneg (hp i).le
    (hp1 ▸ single_le_sum (fun j _ => (hp j).le) (mem_univ i))
  have hlim : Tendsto (fun n : ℕ => (ε + L) * ((Va + Vb) / ε ^ 2) / n +
      Fintype.card ι * (Real.log ((n : ℝ) + 1) / n)) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat ((ε + L) * ((Va + Vb) / ε ^ 2))).add
      (tendsto_log_succ_div.const_mul (Fintype.card ι : ℝ))
  filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_gt_atTop 0] with n hn hn0
  by_contra hcon
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  -- the typical groups
  let good : ℝ × ℝ → Prop := fun r =>
    |Real.log |r.1| - n * la| < n * ε ∧ |Real.log |r.2| - n * lb| < n * ε
  have hgood : ∀ u₀ : Fin n → ι, good (lin A B u₀) →
      fibEnt (pw p) (lin A B) (lin A B u₀) < n * (H - ε) := fun u₀ hu₀ => by
    by_contra hle
    exact hcon ⟨u₀, not_lt.1 hle, hu₀.1, hu₀.2⟩
  -- the bound on the entropy of every group
  have hLn : Real.log (Fintype.card (Fin n → ι)) = n * L := by
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow]
  have hpt : ∀ u : Fin n → ι, fibEnt (pw p) (lin A B) (lin A B u) ≤
      n * (H - ε) + n * (ε + L) * (if good (lin A B u) then 0 else 1) := fun u => by
    split_ifs with hu
    · linarith [hgood u hu]
    · have := fibEnt_le_log_card (pw_pos hp) (lin A B) u
      rw [hLn] at this
      nlinarith
  -- the mass of the atypical groups
  have hbad : ∑ u : Fin n → ι, pw p u * (if good (lin A B u) then 0 else 1) ≤
      Va / (n * ε ^ 2) + Vb / (n * ε ^ 2) := by
    have h1 := sum_pw_filter_le hp hp1 fa hn0 hε
    have h2 := sum_pw_filter_le hp hp1 fb hn0 hε
    rw [sum_filter] at h1 h2
    refine le_trans ?_ (add_le_add h1 h2)
    rw [← sum_add_distrib]
    refine sum_le_sum fun u _ => ?_
    have hu1 := log_abs_lin_fst hA B u
    have hu2 := log_abs_lin_snd A hB u
    have hpu := (pw_pos hp u).le
    by_cases hu : good (lin A B u)
    · rw [ite_eq_left hu, mul_zero]
      split_ifs <;> linarith
    · rw [ite_eq_right hu, mul_one]
      simp only [good, not_and_or, not_lt, hu1, hu2] at hu
      rcases hu with hu | hu
      · rw [ite_eq_left hu]
        split_ifs <;> linarith
      · rw [ite_eq_left hu]
        split_ifs <;> linarith
  -- the mixture identity and the entropy of the masses
  have hmix := sum_negMulLog_eq_mixture (pw_pos hp) (lin A B (n := n))
  rw [sum_negMulLog_pw hp hp1, sum_add_distrib, sum_fibMass_mul] at hmix
  have hα : ∑ r ∈ (univ : Finset (Fin n → ι)).image (lin A B),
      Real.negMulLog (fibMass (pw p (n := n)) (lin A B) r) ≤
        Fintype.card ι * Real.log ((n : ℝ) + 1) := by
    refine (sum_negMulLog_le_log_card_finset (fun r _ => sum_nonneg fun u _ => (pw_pos hp u).le)
      ((sum_fibMass _ _).trans (sum_pw hp1 n))).trans ?_
    have hc := card_image_lin_le A B n
    have hc0 : (0 : ℝ) < ((univ : Finset (Fin n → ι)).image (lin A B)).card := by
      exact_mod_cast (univ_nonempty.image _).card_pos
    calc Real.log ((univ : Finset (Fin n → ι)).image (lin A B)).card
        ≤ Real.log (((n : ℝ) + 1) ^ Fintype.card ι) :=
          Real.log_le_log hc0 (by exact_mod_cast hc)
      _ = Fintype.card ι * Real.log ((n : ℝ) + 1) := Real.log_pow _ _
  have hsum : ∑ u : Fin n → ι, pw p u * fibEnt (pw p (n := n)) (lin A B) (lin A B u) ≤
      n * (H - ε) + n * (ε + L) * (Va / (n * ε ^ 2) + Vb / (n * ε ^ 2)) := by
    calc ∑ u : Fin n → ι, pw p u * fibEnt (pw p (n := n)) (lin A B) (lin A B u)
        ≤ ∑ u : Fin n → ι, pw p u * (n * (H - ε) +
            n * (ε + L) * (if good (lin A B u) then 0 else 1)) :=
          sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hpt u) (pw_pos hp u).le
      _ = n * (H - ε) * ∑ u : Fin n → ι, pw p u +
            n * (ε + L) * ∑ u : Fin n → ι, pw p u * (if good (lin A B u) then 0 else 1) := by
          simp only [mul_add, sum_add_distrib, mul_sum]
          congr 1 <;> exact sum_congr rfl fun u _ => by ring
      _ ≤ n * (H - ε) + n * (ε + L) * (Va / (n * ε ^ 2) + Vb / (n * ε ^ 2)) := by
          rw [sum_pw hp1, mul_one]
          have hεL : 0 ≤ ε + L := add_nonneg hε.le (Real.log_natCast_nonneg _)
          gcongr
  -- the contradiction
  have key : n * ε ≤ n * ((ε + L) * ((Va + Vb) / ε ^ 2) / n +
      Fintype.card ι * (Real.log ((n : ℝ) + 1) / n)) := by
    have e : n * ((ε + L) * ((Va + Vb) / ε ^ 2) / n +
        Fintype.card ι * (Real.log ((n : ℝ) + 1) / n)) =
        n * (ε + L) * (Va / (n * ε ^ 2) + Vb / (n * ε ^ 2)) +
          Fintype.card ι * Real.log ((n : ℝ) + 1) := by
      field_simp
    rw [e]
    linarith
  have := lt_of_le_of_lt ((mul_le_mul_iff_right₀ hn').1 key) hn
  exact lt_irrefl _ this

end Selection

end BoxLike.Rapaport.Diagonal
