module

/-
The freeness of the projective semigroup in the proof of `prop:ssc_no_overlap_not_pesc`
(`sec:exponential_separation`), by the argument of the proof: multiplicative independence of
the ratios, equality of the symbol counts, coefficient comparison at the first non-`λ` symbol,
and cancellation of the common prefix.

The eleven parameters are indexed by `Fin 11` in the order
`(r_1, r_2, r_3, r_4, r_5, q, u, v, s_1, s_2, s_3)`, and the eight symbols of the projective
system by `Fin 4 × ZMod 2`, as in `BoxLike.NoOverlapExample`: the `λ`-symbols `1, 2, 3` are
`lamSym i = (i, 0)` for `i < 3`, and the symbols `4, 5, 6, 7, 8` of the maps
`g_4(x) = r_4 x + u`, `g_5(x) = r_1 x + s_1`, `g_6(x) = r_2 x + s_2`, `g_7(x) = r_3 x + s_3` and
`g_8(x) = r_5 x + v` are `(3, 0)`, `(0, 1)`, `(1, 1)`, `(2, 1)` and `(3, 1)`.

* `Params.ratios`, `Params.prod_ratios_pow_injective`, `Params.mulIndependent`: the ratios
  `λ, r_1, …, r_5` are multiplicatively independent, since `r_1, …, r_5` are algebraically
  independent over `ℚ(λ, t)` and `0 < λ < 1`.
* `symIdx`, `symCount`, `Params.sys_gDeriv_eq_prod`: `g_𝐢'` is the product of the ratios raised
  to the numbers of symbols of `𝐢` that carry them.
* `Params.symCount_eq_of_gDeriv_eq`, `Params.count_eq_of_gDeriv_eq`,
  `Params.length_eq_of_gDeriv_eq`: words with equal derivatives use each of the symbols
  `4, …, 8` equally often and contain the same number of `λ`-symbols; in particular they have
  the same length.
* `Params.lamWord_eq`: the three-map subsystem `(g_1, g_2, g_3)`, conjugate to the homogeneous
  system, generates a free semigroup.
* `valPoly`, `noR`, `coeff_noR_valPoly`, `eq_of_valPoly_eq`: `g_𝐢(0)` as a polynomial in the
  parameters over `ℚ(λ, t)`; the substitution `r_1 = ⋯ = r_5 = 0`, which keeps the terms with
  no factor from `r_1, …, r_5`; the no-`r` coefficient of the translation variable of the first
  non-`λ` symbol; the coefficient step `j = j'`, `|𝐤| = |𝐤'|` and the comparison of the
  remaining terms.
* `Params.freeProjective_of_mulIndependent`: the maps of `Ψ` generate a free semigroup.
-/
public import BoxLike.NoOverlapExample

@[expose] public section

namespace BoxLike

namespace NoOverlap

open MvPolynomial

/-! ### Words over the alphabet of the projective system -/

/-- The index in `(λ, r_1, r_2, r_3, r_4, r_5)` of the ratio of a symbol of the projective
system of `prop:ssc_no_overlap_not_pesc`: `0` for the `λ`-symbols `1, 2, 3`, and `4, 1, 2, 3, 5`
for the symbols `4, 5, 6, 7, 8`. -/
def symIdx (p : Fin 4 × ZMod 2) : Fin 6 := if p.2 = 0 then ![0, 0, 0, 4] p.1 else ![1, 2, 3, 5] p.1

/-- A symbol carries the ratio `λ` exactly when it is one of the `λ`-symbols `1, 2, 3`. -/
theorem symIdx_eq_zero_iff : ∀ p : Fin 4 × ZMod 2, symIdx p = 0 ↔ ∃ i, p = lamSym i := by
  decide

/-- Each of the ratios `r_1, …, r_5` is carried by exactly one symbol. -/
theorem symIdx_eq_iff : ∀ p q : Fin 4 × ZMod 2, (∀ i, p ≠ lamSym i) →
    (symIdx q = symIdx p ↔ q = p) := by
  decide

/-- The number of symbols of the word `𝐢` that carry the `k`-th ratio of `(λ, r_1, …, r_5)`:
for `k = 0` the number of `λ`-symbols. -/
def symCount (u : List (Fin 4 × ZMod 2)) (k : Fin 6) : ℕ := (u.map symIdx).count k

/-- For a symbol `p` among `4, …, 8`, its number of occurrences in `𝐢` is the number of symbols
of `𝐢` that carry its ratio. -/
theorem count_eq_symCount {p : Fin 4 × ZMod 2} (hp : ∀ i, p ≠ lamSym i)
    (u : List (Fin 4 × ZMod 2)) : u.count p = symCount u (symIdx p) := by
  induction u with
  | nil => simp [symCount]
  | cons q u ih =>
    rw [List.count_cons, ih]
    simp only [symCount, List.map_cons, List.count_cons, beq_iff_eq, symIdx_eq_iff p q hp]

namespace Params

variable (P : Params)

/-! ### Multiplicative independence of the ratios -/

/-- The six ratios `λ, r_1, r_2, r_3, r_4, r_5` of the maps of the projective system of
`prop:ssc_no_overlap_not_pesc`. -/
noncomputable def ratios : Fin 6 → ℝ := ![P.lam, P.r₁, P.r₂, P.r₃, P.r₄, P.r₅]

/-- The ratios are positive. -/
theorem ratios_pos (k : Fin 6) : 0 < P.ratios k := by
  have := P.lam_pos
  have := P.r₁_mem.1
  have := P.r₂_mem.1
  have := P.r₃_mem.1
  have := P.r₄_mem.1
  have := P.r₅_mem.1
  fin_cases k <;> simp [ratios] <;> linarith

/-- Equal monomials in `λ, r_1, …, r_5` have equal exponents (proof of
`prop:ssc_no_overlap_not_pesc`): the identity
`λ^{m_0} r_1^{m_1} ⋯ r_5^{m_5} = λ^{m'_0} r_1^{m'_1} ⋯ r_5^{m'_5}` is a polynomial identity in
`r_1, …, r_5` over `K ∋ λ`, so the two monomials coincide, and `0 < λ < 1` gives `m_0 = m'_0`. -/
theorem prod_ratios_pow_injective {K : Subfield ℝ} (hlamK : P.lam ∈ K)
    (hx : AlgebraicIndependent K P.θ) {m m' : Fin 6 → ℕ}
    (h : ∏ k, P.ratios k ^ m k = ∏ k, P.ratios k ^ m' k) : m = m' := by
  set l : K := ⟨P.lam, hlamK⟩ with hl
  -- The monomial `λ^{m_0} r_1^{m_1} ⋯ r_5^{m_5}` with coefficients in `K`.
  let mono : (Fin 6 → ℕ) → MvPolynomial (Fin 11) K := fun m =>
    C (l ^ m 0) * X 0 ^ m 1 * X 1 ^ m 2 * X 2 ^ m 3 * X 3 ^ m 4 * X 4 ^ m 5
  have heval : ∀ m, aeval P.θ (mono m) = ∏ k, P.ratios k ^ m k := by
    intro m
    simp only [mono, map_mul, map_pow, aeval_C, aeval_X, Fin.prod_univ_six]
    rfl
  have hmono : ∀ m, mono m = monomial (Finsupp.single 0 (m 1) + Finsupp.single 1 (m 2) +
      Finsupp.single 2 (m 3) + Finsupp.single 3 (m 4) + Finsupp.single 4 (m 5)) (l ^ m 0) := by
    intro m
    simp only [mono, X_pow_eq_monomial, C_mul_monomial, monomial_mul_monomial, mul_one]
  have hpoly : mono m = mono m' := hx (by rw [heval, heval, h])
  rw [hmono, hmono, monomial_eq_monomial_iff] at hpoly
  have hl0 : l ≠ 0 := fun h0 => P.lam_pos.ne' (congrArg Subtype.val h0)
  rcases hpoly with ⟨hs, hc⟩ | ⟨h0, -⟩
  · have hpow : P.lam ^ m 0 = P.lam ^ m' 0 := by
      have := congrArg Subtype.val hc
      simpa [hl] using this
    have h0 : m 0 = m' 0 :=
      pow_right_injective₀ P.lam_pos (by linarith [P.lam_lt]) hpow
    have h1 := DFunLike.congr_fun hs 0
    have h2 := DFunLike.congr_fun hs 1
    have h3 := DFunLike.congr_fun hs 2
    have h4 := DFunLike.congr_fun hs 3
    have h5 := DFunLike.congr_fun hs 4
    simp at h1 h2 h3 h4 h5
    funext k
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · exact absurd (pow_eq_zero_iff'.1 h0).1 hl0

/-- The ratios `λ, r_1, …, r_5` are multiplicatively independent (proof of
`prop:ssc_no_overlap_not_pesc`): since `r_1, …, r_5` are algebraically independent over
`ℚ(λ, t)` and `λ ∈ (0, 1)`, `λ^{m_0} r_1^{m_1} ⋯ r_5^{m_5} = 1` with integer exponents forces
`m = 0`. Here `K` is any subfield of `ℝ` containing `λ`. -/
theorem mulIndependent {K : Subfield ℝ} (hlamK : P.lam ∈ K) (hx : AlgebraicIndependent K P.θ)
    (m : Fin 6 → ℤ) (h : ∏ k, P.ratios k ^ m k = 1) : m = 0 := by
  have hpos := P.ratios_pos
  have hsplit : ∀ k, P.ratios k ^ m k =
      P.ratios k ^ (m k).toNat / P.ratios k ^ (-m k).toNat := by
    intro k
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (hpos k).ne', Int.toNat_sub_toNat_neg]
  have hne : ∏ k, P.ratios k ^ (-m k).toNat ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hpos k).ne'
  have heq : ∏ k, P.ratios k ^ (m k).toNat = ∏ k, P.ratios k ^ (-m k).toNat := by
    simp only [hsplit, Finset.prod_div_distrib] at h
    exact (div_eq_one_iff_eq hne).1 h
  have hm := P.prod_ratios_pow_injective hlamK hx heq
  funext k
  have hk := congrFun hm k
  rw [Pi.zero_apply, ← Int.toNat_sub_toNat_neg (m k), hk, sub_self]

/-! ### Symbol counts -/

/-- The ratio of a symbol is the `symIdx`-th of `λ, r_1, …, r_5`. -/
theorem sys_ratio_eq (p : Fin 4 × ZMod 2) : P.sys.ratio p = P.ratios (symIdx p) := by
  obtain ⟨i, c⟩ := p
  fin_cases i <;> rcases zmod_two_cases c with rfl | rfl <;>
    simp [System.ratio, sys, ratios, symIdx]

/-- `g_𝐢' = λ^{n_λ} r_1^{n_5} r_2^{n_6} r_3^{n_7} r_4^{n_4} r_5^{n_8}`, where `n_λ` is the number
of `λ`-symbols of `𝐢` and `n_j` the number of occurrences of the symbol `j` (proof of
`prop:ssc_no_overlap_not_pesc`). -/
theorem sys_gDeriv_eq_prod (u : List (Fin 4 × ZMod 2)) :
    P.sys.gDeriv u = ∏ k, P.ratios k ^ symCount u k := by
  induction u with
  | nil => simp [symCount]
  | cons p u ih =>
    rw [System.gDeriv_cons, ih, sys_ratio_eq]
    simp only [symCount, List.map_cons, List.count_cons, beq_iff_eq, pow_add,
      Finset.prod_mul_distrib, Finset.prod_pow_boole, Finset.mem_univ, ite_true]
    ring

/-- Words with equal derivatives have equal symbol counts (proof of
`prop:ssc_no_overlap_not_pesc`), by the multiplicative independence of the ratios. -/
theorem symCount_eq_of_gDeriv_eq {K : Subfield ℝ} (hlamK : P.lam ∈ K)
    (hx : AlgebraicIndependent K P.θ) {u u' : List (Fin 4 × ZMod 2)}
    (h : P.sys.gDeriv u = P.sys.gDeriv u') : symCount u = symCount u' := by
  rw [P.sys_gDeriv_eq_prod, P.sys_gDeriv_eq_prod] at h
  have hpos := P.ratios_pos
  have hm := P.mulIndependent hlamK hx (fun k => (symCount u k : ℤ) - symCount u' k) (by
    simp only [zpow_sub₀ (hpos _).ne', zpow_natCast, Finset.prod_div_distrib, h]
    exact div_self (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hpos k).ne'))
  funext k
  have hk := congrFun hm k
  simp only [Pi.zero_apply, sub_eq_zero, Nat.cast_inj] at hk
  exact hk

/-- Words with equal derivatives use each of the symbols `4, 5, 6, 7, 8` equally often and contain
the same total number of the `λ`-symbols `1, 2, 3` (proof of `prop:ssc_no_overlap_not_pesc`). -/
theorem count_eq_of_gDeriv_eq {K : Subfield ℝ} (hlamK : P.lam ∈ K)
    (hx : AlgebraicIndependent K P.θ) {u u' : List (Fin 4 × ZMod 2)}
    (h : P.sys.gDeriv u = P.sys.gDeriv u') :
    (∀ p, (∀ i, p ≠ lamSym i) → u.count p = u'.count p) ∧ symCount u 0 = symCount u' 0 := by
  have hc := P.symCount_eq_of_gDeriv_eq hlamK hx h
  exact ⟨fun p hp => by rw [count_eq_symCount hp, count_eq_symCount hp, hc], by rw [hc]⟩

/-- Words with equal derivatives have the same length (proof of
`prop:ssc_no_overlap_not_pesc`). -/
theorem length_eq_of_gDeriv_eq {K : Subfield ℝ} (hlamK : P.lam ∈ K)
    (hx : AlgebraicIndependent K P.θ) {u u' : List (Fin 4 × ZMod 2)}
    (h : P.sys.gDeriv u = P.sys.gDeriv u') : u.length = u'.length := by
  have hc := P.symCount_eq_of_gDeriv_eq hlamK hx h
  have hperm : (u.map symIdx).Perm (u'.map symIdx) :=
    List.perm_iff_count.2 fun k => congrFun hc k
  simpa using hperm.length_eq

/-! ### The three-map subsystem -/

/-- A word of `λ`-symbols is a word of the first axis over `{1, 2, 3} ⊆ Fin 4`. -/
theorem map_lamSym_eq_firstAxis (w : List (Fin 3)) :
    w.map lamSym = System.firstAxis (w.map Fin.castSucc) := by
  simp [System.firstAxis, lamSym, List.map_map, Function.comp_def]

/-- The maps `g_1, g_2, g_3` generate a free semigroup (proof of
`prop:ssc_no_overlap_not_pesc`): they are conjugate to the homogeneous system by a common
translation, so two words `𝐤, 𝐤'` of `λ`-symbols of the same length with `g_𝐤(0) = g_{𝐤'}(0)`
are equal when the homogeneous system generates a free semigroup. -/
theorem lamWord_eq (hfree : HomFree P.lam P.t) {w w' : List (Fin 3)}
    (hlen : w.length = w'.length)
    (h0 : P.sys.gWord (w.map lamSym) 0 = P.sys.gWord (w'.map lamSym) 0) : w = w' := by
  rw [map_lamSym_eq_firstAxis, map_lamSym_eq_firstAxis] at h0
  have h := P.gWord_firstAxis_sub hlen
  rw [h0, sub_self] at h
  exact hfree.eq_of_length_eq hlen (sub_eq_zero.1 h.symm)

end Params

/-! ### The coefficient of the first non-`λ` symbol -/

section Generic

variable {A : Type*} [CommRing A]

omit [CommRing A] in
/-- The maps `g_1, g_2, g_3` have ratio `λ`, at every tuple. -/
theorem genRatio_lamSym' (l : A) (θ : Fin 11 → A) (i : Fin 3) : genRatio l θ (lamSym i) = l := by
  fin_cases i <;> simp [genRatio, lamSym]

/-- At a tuple with `r_1 = ⋯ = r_5 = 0` the maps `g_4, …, g_8` have ratio `0`. -/
theorem genRatio_of_ne' (l : A) {θ : Fin 11 → A} (hθ : ∀ k : Fin 11, (k : ℕ) < 5 → θ k = 0)
    {p : Fin 4 × ZMod 2} (hp : ∀ i, p ≠ lamSym i) : genRatio l θ p = 0 := by
  have h0 := hθ 0 (by decide)
  have h1 := hθ 1 (by decide)
  have h2 := hθ 2 (by decide)
  have h3 := hθ 3 (by decide)
  have h4 := hθ 4 (by decide)
  obtain ⟨i, c⟩ := p
  fin_cases i <;> rcases zmod_two_cases c with rfl | rfl <;>
    first
    | exact absurd rfl (hp 0)
    | exact absurd rfl (hp 1)
    | exact absurd rfl (hp 2)
    | simp [genRatio, h0, h1, h2, h3, h4]

/-- The translation of each of the maps `g_4, …, g_8` is its translation variable among
`u, s_1, s_2, s_3, v`, at every tuple. -/
theorem genTrans_of_ne' (τ : A) (θ : Fin 11 → A) {p : Fin 4 × ZMod 2}
    (hp : ∀ i, p ≠ lamSym i) : genTrans τ θ p = θ (slot p) := by
  obtain ⟨i, c⟩ := p
  fin_cases i <;> rcases zmod_two_cases c with rfl | rfl <;>
    first
    | exact absurd rfl (hp 0)
    | exact absurd rfl (hp 1)
    | exact absurd rfl (hp 2)
    | simp [genTrans, slot]

/-- A word of `n` symbols among `1, 2, 3` has derivative `λ^n`, at every tuple. -/
theorem genDeriv_map_lamSym' (l : A) (θ : Fin 11 → A) (w : List (Fin 3)) :
    genDeriv l θ (w.map lamSym) = l ^ w.length := by
  induction w with
  | nil => simp
  | cons i w ih => simp [ih, genRatio_lamSym', pow_succ']

/-- The value `g_𝐤(0)` of a word of `λ`-symbols depends on the parameters only through `q`. -/
theorem genVal_map_lamSym_congr (l τ : A) {θ θ' : Fin 11 → A} (h : θ 5 = θ' 5)
    (w : List (Fin 3)) : genVal l τ θ (w.map lamSym) = genVal l τ θ' (w.map lamSym) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [List.map_cons, genVal_cons, genRatio_lamSym', ih]
    fin_cases i <;> simp [genTrans, lamSym, h]

end Generic

section Coefficient

variable {K : Subfield ℝ}

/-- The value `g_𝐢(0)` as a polynomial in the parameters `r_1, …, r_5, q, u, v, s_1, s_2, s_3`
with coefficients in `K ∋ λ, t` (proof of `prop:ssc_no_overlap_not_pesc`). -/
noncomputable def valPoly (l τ : K) (u : List (Fin 4 × ZMod 2)) : MvPolynomial (Fin 11) K :=
  genVal (C l) (C τ) X u

/-- Evaluating the polynomial `valPoly` at a tuple gives `g_𝐢(0)` at that tuple. -/
theorem aeval_valPoly (l τ : K) (θ : Fin 11 → ℝ) (u : List (Fin 4 × ZMod 2)) :
    aeval θ (valPoly l τ u) = genVal (l : ℝ) (τ : ℝ) θ u := by
  rw [valPoly, map_genVal]
  congr 1
  · rw [aeval_C]; rfl
  · rw [aeval_C]; rfl
  · funext k; simp

/-- The variables with `r_1 = ⋯ = r_5 = 0`. -/
noncomputable def noRVars : Fin 11 → MvPolynomial (Fin 11) K :=
  fun k => if (k : ℕ) < 5 then 0 else X k

/-- The substitution `r_1 = ⋯ = r_5 = 0`. It keeps exactly the terms of a polynomial with no
factor from `r_1, …, r_5`, the terms that the proof of `prop:ssc_no_overlap_not_pesc` compares. -/
noncomputable def noR : MvPolynomial (Fin 11) K →ₐ[K] MvPolynomial (Fin 11) K := aeval noRVars

/-- The no-`r` part of `g_𝐢(0)`. -/
theorem noR_valPoly (l τ : K) (u : List (Fin 4 × ZMod 2)) :
    noR (valPoly l τ u) = genVal (C l) (C τ) noRVars u := by
  rw [valPoly, noR, map_genVal]
  congr 1
  · rw [aeval_C]; rfl
  · rw [aeval_C]; rfl
  · funext k; simp

/-- The no-`r` part of `g_𝐤(0)` for a word `𝐤` of `λ`-symbols is affine in `q`. -/
theorem exists_noR_valPoly_map_lamSym (l τ : K) (w : List (Fin 3)) :
    ∃ α β : K, noR (valPoly l τ (w.map lamSym)) = C α * X 5 + C β := by
  rw [noR_valPoly]
  induction w with
  | nil => exact ⟨0, 0, by simp⟩
  | cons i w ih =>
    obtain ⟨α, β, h⟩ := ih
    have h5 : (noRVars 5 : MvPolynomial (Fin 11) K) = X 5 := by simp [noRVars]
    simp only [List.map_cons, genVal_cons, genRatio_lamSym', h]
    fin_cases i
    · refine ⟨l * α + 1, l * β, ?_⟩
      simp [genTrans, lamSym, h5]; ring
    · refine ⟨l * α + 1, l * β + τ, ?_⟩
      simp [genTrans, lamSym, h5]; ring
    · refine ⟨l * α + 1, l * β + 1, ?_⟩
      simp [genTrans, lamSym, h5]; ring

/-- The no-`r` part of `g_𝐤(0)` for a word `𝐤` of `λ`-symbols has no term in the translation
variables `u, v, s_1, s_2, s_3`. -/
theorem coeff_noR_valPoly_map_lamSym (l τ : K) (w : List (Fin 3)) {s : Fin 11} (hs : s ≠ 5) :
    (noR (valPoly l τ (w.map lamSym))).coeff (Finsupp.single s 1) = 0 := by
  obtain ⟨α, β, h⟩ := exists_noR_valPoly_map_lamSym l τ w
  have h1 : Finsupp.single (5 : Fin 11) 1 ≠ Finsupp.single s 1 :=
    fun he => hs ((Finsupp.single_left_inj one_ne_zero).1 he).symm
  have h2 : (0 : Fin 11 →₀ ℕ) ≠ Finsupp.single s 1 :=
    (Finsupp.single_ne_zero.2 one_ne_zero).symm
  rw [h]
  simp [coeff_C_mul, coeff_X, coeff_C, h1, h2]

/-- The no-`r` part of `g_{𝐤 j 𝐥}(0)`, for a word `𝐤` of `λ`-symbols and a symbol `j` among
`4, …, 8`: the earlier symbols contribute the no-`r` part of `g_𝐤(0)`, the symbol `j` its
translation variable with coefficient `λ^{|𝐤|}`, and every later contribution is multiplied by
the ratio of `j` (proof of `prop:ssc_no_overlap_not_pesc`). -/
theorem noR_valPoly_split (l τ : K) (w : List (Fin 3)) {j : Fin 4 × ZMod 2}
    (hj : ∀ i, j ≠ lamSym i) (rest : List (Fin 4 × ZMod 2)) :
    noR (valPoly l τ (w.map lamSym ++ j :: rest)) =
      C (l ^ w.length) * X (slot j) + noR (valPoly l τ (w.map lamSym)) := by
  have hθ : ∀ k : Fin 11, (k : ℕ) < 5 → (noRVars k : MvPolynomial (Fin 11) K) = 0 :=
    fun k hk => by simp [noRVars, hk]
  have hslot : (noRVars (slot j) : MvPolynomial (Fin 11) K) = X (slot j) := by
    have := six_le_slot j
    simp only [noRVars]
    rw [ite_eq_right (by omega)]
  rw [noR_valPoly, noR_valPoly, genVal_append, genVal_cons, genRatio_of_ne' _ hθ hj, zero_mul,
    zero_add, genTrans_of_ne' _ _ hj, hslot, genDeriv_map_lamSym', map_pow]

/-- The no-`r` coefficient of the translation variable of the first non-`λ` symbol `j` in
`g_{𝐤 j 𝐥}(0)` is `λ^{|𝐤|}`, and the no-`r` coefficient of the translation variable of any other
symbol among `4, …, 8` vanishes (proof of `prop:ssc_no_overlap_not_pesc`). -/
theorem coeff_noR_valPoly (l τ : K) (w : List (Fin 3)) {j : Fin 4 × ZMod 2}
    (hj : ∀ i, j ≠ lamSym i) (rest : List (Fin 4 × ZMod 2)) (s : Fin 11) (hs : 6 ≤ (s : ℕ)) :
    (noR (valPoly l τ (w.map lamSym ++ j :: rest))).coeff (Finsupp.single s 1) =
      if slot j = s then l ^ w.length else 0 := by
  have hs5 : s ≠ 5 := by
    intro h
    rw [h] at hs
    simp at hs
  have hk := coeff_noR_valPoly_map_lamSym l τ w hs5
  rw [noR_valPoly_split l τ w hj, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C_mul, hk,
    add_zero, coeff_X]
  by_cases h : slot j = s
  · rw [ite_eq_left (by rw [h]), ite_eq_left h, mul_one]
  · rw [ite_eq_right (fun he => h ((Finsupp.single_left_inj one_ne_zero).1 he)), ite_eq_right h,
      mul_zero]

/-- The coefficient step of the proof of `prop:ssc_no_overlap_not_pesc`. Let `0 < λ < 1` and let
`g_{𝐤 j 𝐥}(0) = g_{𝐤' j' 𝐥'}(0)` be a polynomial identity over `K ∋ λ, t`, with `𝐤, 𝐤'` words of
`λ`-symbols and `j, j'` among `4, …, 8`. Matching the no-`r` coefficient of the translation
variable of `j` gives `j = j'` and `λ^{|𝐤|} = λ^{|𝐤'|}`, hence `|𝐤| = |𝐤'|`; the remaining terms
with no factor from `r_1, …, r_5` then agree. -/
theorem eq_of_valPoly_eq {l τ : K} (hl0 : 0 < (l : ℝ)) (hl1 : (l : ℝ) < 1) {w w' : List (Fin 3)}
    {j j' : Fin 4 × ZMod 2} (hj : ∀ i, j ≠ lamSym i) (hj' : ∀ i, j' ≠ lamSym i)
    {rest rest' : List (Fin 4 × ZMod 2)}
    (h : valPoly l τ (w.map lamSym ++ j :: rest) = valPoly l τ (w'.map lamSym ++ j' :: rest')) :
    j = j' ∧ w.length = w'.length ∧
      noR (valPoly l τ (w.map lamSym)) = noR (valPoly l τ (w'.map lamSym)) := by
  have hl : l ≠ 0 := fun h0 => hl0.ne' (by rw [h0]; rfl)
  have hc := congrArg (fun p => (noR p).coeff (Finsupp.single (slot j) 1)) h
  rw [coeff_noR_valPoly l τ w hj rest _ (six_le_slot j), ite_eq_left rfl,
    coeff_noR_valPoly l τ w' hj' rest' _ (six_le_slot j)] at hc
  have hjj : slot j' = slot j := by
    by_contra hne
    rw [ite_eq_right hne] at hc
    exact pow_ne_zero _ hl hc
  have hjj' : j = j' := slot_injOn j j' hj hj' hjj.symm
  subst hjj'
  rw [ite_eq_left rfl] at hc
  have hpow : (l : ℝ) ^ w.length = (l : ℝ) ^ w'.length := by
    have := congrArg Subtype.val hc
    simpa using this
  have hw : w.length = w'.length := pow_right_injective₀ hl0 hl1.ne hpow
  refine ⟨rfl, hw, ?_⟩
  have hn := congrArg noR h
  rw [noR_valPoly_split l τ w hj, noR_valPoly_split l τ w' hj, hw] at hn
  exact add_left_cancel hn

/-- Evaluating the no-`r` part of `g_𝐤(0)`, for a word `𝐤` of `λ`-symbols, at a tuple gives
`g_𝐤(0)` at that tuple: `g_𝐤(0)` has no factor from `r_1, …, r_5`. -/
theorem aeval_noR_valPoly_map_lamSym (l τ : K) (θ : Fin 11 → ℝ) (w : List (Fin 3)) :
    aeval θ (noR (valPoly l τ (w.map lamSym))) = genVal (l : ℝ) (τ : ℝ) θ (w.map lamSym) := by
  rw [noR_valPoly, map_genVal]
  have h1 : aeval θ (C l) = (l : ℝ) := by rw [aeval_C]; rfl
  have h2 : aeval θ (C τ) = (τ : ℝ) := by rw [aeval_C]; rfl
  rw [h1, h2]
  exact genVal_map_lamSym_congr _ _ (by simp [noRVars]) w

end Coefficient

/-! ### Freeness -/

namespace Params

variable (P : Params)

/-- The maps of the projective system `Ψ` generate a free semigroup (tex lines 1407 to 1436), by
the argument of the proof of `prop:ssc_no_overlap_not_pesc`. Let the homogeneous system
`(λx, λx + t, λx + 1)` generate a free semigroup and let the parameters be algebraically
independent over a subfield `K ∋ λ, t` of `ℝ`. Let `g_𝐢 = g_𝐣`.

Their derivatives agree, so by the multiplicative independence of `λ, r_1, …, r_5`
(`mulIndependent`) the words use each of the symbols `4, …, 8` equally often and contain the same
number of `λ`-symbols (`count_eq_of_gDeriv_eq`); in particular `|𝐢| = |𝐣|`
(`length_eq_of_gDeriv_eq`). If both words consist of `λ`-symbols, they agree by the freeness of
the three-map subsystem (`lamWord_eq`). Otherwise both have a first non-`λ` symbol,
`𝐢 = 𝐤 j 𝐥` and `𝐣 = 𝐤' j' 𝐥'`. The identity `g_𝐢(0) = g_𝐣(0)` is a polynomial identity in the
algebraically independent parameters, and the no-`r` coefficient of the translation variable of
`j` gives `j = j'` and `|𝐤| = |𝐤'|`; the remaining no-`r` terms give `g_𝐤(0) = g_{𝐤'}(0)`, hence
`𝐤 = 𝐤'` (`eq_of_valPoly_eq`, `lamWord_eq`). Cancelling the invertible affine map `g_{𝐤 j}`
gives `g_𝐥 = g_{𝐥'}`, and induction on the length gives `𝐥 = 𝐥'`. -/
theorem freeProjective_of_mulIndependent {K : Subfield ℝ} (hlamK : P.lam ∈ K) (htK : P.t ∈ K)
    (hfree : HomFree P.lam P.t) (hx : AlgebraicIndependent K P.θ) : P.sys.FreeProjective := by
  intro u u' h
  induction hn : u.length using Nat.strong_induction_on generalizing u u' with
  | _ n ih =>
    have hD : P.sys.gDeriv u = P.sys.gDeriv u' := ((P.sys.gWord_eq_iff u u').1 h).1
    have hV : P.sys.gWord u 0 = P.sys.gWord u' 0 := ((P.sys.gWord_eq_iff u u').1 h).2
    -- The symbol counts agree, and so do the lengths.
    obtain ⟨hcount, -⟩ := P.count_eq_of_gDeriv_eq hlamK hx hD
    have hlen := P.length_eq_of_gDeriv_eq hlamK hx hD
    -- A non-`λ` symbol of one word occurs in the other.
    have hmem : ∀ p, (∀ i, p ≠ lamSym i) → (p ∈ u ↔ p ∈ u') := fun p hp => by
      rw [← List.count_pos_iff, ← List.count_pos_iff, hcount p hp]
    have hnot : ∀ (w : List (Fin 3)) p, (∀ i, p ≠ lamSym i) → p ∉ w.map lamSym := by
      intro w p hp hpw
      obtain ⟨i, -, hi⟩ := List.mem_map.1 hpw
      exact hp i hi.symm
    obtain ⟨w, rest, rfl, hrest⟩ := exists_lamSym_prefix u
    obtain ⟨w', rest', rfl, hrest'⟩ := exists_lamSym_prefix u'
    rcases hrest with rfl | ⟨j, l, hj, rfl⟩ <;> rcases hrest' with rfl | ⟨j', l', hj', rfl⟩
    · -- Both words consist of `λ`-symbols.
      simp only [List.append_nil, List.length_map] at hV hlen
      rw [P.lamWord_eq hfree hlen hV]
    · exact absurd ((hmem j' hj').2 (by simp)) (by simpa using hnot w j' hj')
    · exact absurd ((hmem j hj).1 (by simp)) (by simpa using hnot w' j hj)
    · -- Both words have a first non-`λ` symbol: the coefficient step.
      set lK : K := ⟨P.lam, hlamK⟩
      set tK : K := ⟨P.t, htK⟩
      have hpoly : valPoly lK tK (w.map lamSym ++ j :: l) =
          valPoly lK tK (w'.map lamSym ++ j' :: l') := by
        apply hx
        rw [aeval_valPoly, aeval_valPoly]
        rw [P.sys_gWord_zero, P.sys_gWord_zero] at hV
        exact hV
      obtain ⟨rfl, hw, hrem⟩ :=
        eq_of_valPoly_eq (l := lK) (τ := tK) P.lam_pos (by linarith [P.lam_lt]) hj hj' hpoly
      have h0 : P.sys.gWord (w.map lamSym) 0 = P.sys.gWord (w'.map lamSym) 0 := by
        rw [P.sys_gWord_zero, P.sys_gWord_zero]
        have e := congrArg (aeval P.θ) hrem
        rwa [aeval_noR_valPoly_map_lamSym, aeval_noR_valPoly_map_lamSym] at e
      obtain rfl := P.lamWord_eq hfree hw h0
      -- Cancel the invertible affine map `g_{𝐤 j}`.
      have e : ∀ l : List (Fin 4 × ZMod 2),
          w.map lamSym ++ j :: l = (w.map lamSym ++ [j]) ++ l := fun l => by simp
      rw [e l, e l', P.sys.gWord_append (w.map lamSym ++ [j]) l,
        P.sys.gWord_append (w.map lamSym ++ [j]) l'] at h
      have hne : P.sys.gDeriv (w.map lamSym ++ [j]) ≠ 0 := P.sys.gDeriv_ne_zero _
      have hl : P.sys.gWord l = P.sys.gWord l' := by
        funext y
        have hy := congrFun h y
        simp only [Function.comp_apply] at hy
        rw [P.sys.gWord_apply (w.map lamSym ++ [j]) (P.sys.gWord l y),
          P.sys.gWord_apply (w.map lamSym ++ [j]) (P.sys.gWord l' y)] at hy
        exact mul_left_cancel₀ hne (add_right_cancel hy)
      have hlt : l.length < n := by
        rw [← hn]; simp; omega
      rw [ih l.length hlt hl rfl]

end Params

end NoOverlap

end BoxLike
