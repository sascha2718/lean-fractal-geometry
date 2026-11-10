module

/-
`NoOverlap.BaranyKaenmakiPair`: there are `0 < λ < 1/3` transcendental, `0 < t < λ/(1-λ)` and
`C_0 > 0` such that `(λx, λx + t, λx + 1)` generates a free semigroup and
`Δ_n^{λ,t} ≤ C_0 exp(-n²)` for every `n ≥ 1`, the form of Bárány–Käenmäki, Adv. Math. 379
(2021), arXiv:1910.04623v4, that `prop:ssc_no_overlap_not_pesc` uses; and a corrected form of
their Theorem 2.1: for every positive sequence `η` the free pairs with `Δ_n < η_n` for every
`n ≥ 5` have uncountably many transcendental first coordinates.

Proof by Baire category. The zero set of `h_𝐰(0) - h_{𝐰'}(0) = U_π(λ) + t V_π(λ)` is a curve;
concatenation produces crossings of curves arbitrarily close to every point of the set `D_η` of
crossing points near the crossing of Bárány and Käenmäki (their Lemma 3.8), so in `closure D_η`
the conditions `Δ_n < η_n`, `h_𝐰(0) ≠ h_{𝐰'}(0)` and `λ ∉ L` (`L` countable) are dense open.

In the namespace `BoxLike.NoOverlap`:

* `pairDiff`, `pU`, `pV`, `pairCross`, `extPair`: the polynomials of a pair and concatenation.
* `IsCrossPt`, `exists_root_near`, `exists_crossPt_near`: the crossing lemma.
* `basePair₁`, `basePair₂`, `lamB`, `isCrossPt_base`: the crossing of Bárány and Käenmäki.
* `goodCross`, `exists_goodCross_pairDiff_ne`, `exists_good_point`: the Baire argument.
* `baranyKaenmakiPair_holds`, `not_countable_fst_condensation`, `not_countable_condensation`.
* `prop_ssc_no_overlap_not_pesc_holds`, `planar_separation_not_pesc_holds`: the proposition and
  the paragraph after it with no hypothesis.
-/
public import BoxLike.Aligned.NoOverlapPESC
public import BoxLike.NoOverlapExample
public import Mathlib.Algebra.AlgebraicCard
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

namespace BoxLike

namespace NoOverlap

open Polynomial Filter Topology

/-! ### Words -/

/-- `h_{𝐩𝐬}(x) = h_𝐩(h_𝐬(x))`. -/
theorem homWord_append (lam t : ℝ) (p s : List (Fin 3)) (x : ℝ) :
    homWord lam t (p ++ s) x = homWord lam t p (homWord lam t s x) := by
  induction p with
  | nil => rfl
  | cons i p ih => simp [ih]

/-- `h_{0^k}(0) = 0`. -/
theorem homWord_replicate_zero (lam t : ℝ) (k : ℕ) : homWord lam t (List.replicate k 0) 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih, homTrans]

/-- Appending zeros does not change `h_𝐩(0)`. -/
theorem homWord_append_replicate_zero (lam t : ℝ) (p : List (Fin 3)) (k : ℕ) :
    homWord lam t (p ++ List.replicate k 0) 0 = homWord lam t p 0 := by
  rw [homWord_append, homWord_replicate_zero]

/-- The translations `0, t, 1` lie in `[0, 1]` for `0 ≤ t ≤ 1`. -/
theorem homTrans_mem_Icc {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (i : Fin 3) :
    0 ≤ homTrans t i ∧ homTrans t i ≤ 1 := by
  fin_cases i <;> simp [homTrans, ht0, ht1]

/-- For `0 ≤ λ ≤ 1/3` and `0 ≤ t ≤ 1`, every `h_𝐩(0)` lies in `[0, 3/2]`. -/
theorem homWord_zero_mem_Icc {lam t : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1 / 3) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (w : List (Fin 3)) : 0 ≤ homWord lam t w 0 ∧ homWord lam t w 0 ≤ 3 / 2 := by
  induction w with
  | nil => norm_num
  | cons i w ih =>
    obtain ⟨h0, h1⟩ := ih
    obtain ⟨a0, a1⟩ := homTrans_mem_Icc ht0 ht1 i
    rw [homWord_cons]
    constructor
    · positivity
    · nlinarith

/-! ### Integer polynomials of a pair of words -/

/-- The coefficient of `1` in `h_i(0) - h_j(0)`: `[i = 2] - [j = 2]`. -/
def difU (i j : Fin 3) : ℤ := (if i = 2 then 1 else 0) - (if j = 2 then 1 else 0)

/-- The coefficient of `t` in `h_i(0) - h_j(0)`: `[i = 1] - [j = 1]`. -/
def difV (i j : Fin 3) : ℤ := (if i = 1 then 1 else 0) - (if j = 1 then 1 else 0)

/-- `h_i(0) - h_j(0) = [i = 2] - [j = 2] + t([i = 1] - [j = 1])`. -/
theorem homTrans_sub (t : ℝ) (i j : Fin 3) :
    homTrans t i - homTrans t j = difU i j + t * difV i j := by
  fin_cases i <;> fin_cases j <;> simp [homTrans, difU, difV] <;> ring

/-- The digits of `difU` lie in `{-1, 0, 1}`. -/
theorem abs_difU_le (i j : Fin 3) : |difU i j| ≤ 1 := by
  fin_cases i <;> fin_cases j <;> simp [difU]

/-- The digits of `difV` lie in `{-1, 0, 1}`. -/
theorem abs_difV_le (i j : Fin 3) : |difV i j| ≤ 1 := by
  fin_cases i <;> fin_cases j <;> simp [difV]

/-- The integer polynomial `∑_k d(p_k, q_k) X^k` of a pair of words for a digit function `d`;
the sum stops at the end of the shorter word. -/
noncomputable def polyD (d : Fin 3 → Fin 3 → ℤ) : List (Fin 3) → List (Fin 3) → ℤ[X]
  | i :: p, j :: q => C (d i j) + X * polyD d p q
  | _, _ => 0

/-- `polyD d` of an empty first word is `0`. -/
@[simp] theorem polyD_nil_left (d : Fin 3 → Fin 3 → ℤ) (q : List (Fin 3)) :
    polyD d [] q = 0 := rfl

/-- `polyD d` of an empty second word is `0`. -/
@[simp] theorem polyD_nil_right (d : Fin 3 → Fin 3 → ℤ) (p : List (Fin 3)) :
    polyD d p [] = 0 := by
  cases p <;> rfl

/-- `polyD d (i𝐩) (j𝐪) = d(i, j) + X polyD d 𝐩 𝐪`. -/
@[simp] theorem polyD_cons (d : Fin 3 → Fin 3 → ℤ) (i j : Fin 3) (p q : List (Fin 3)) :
    polyD d (i :: p) (j :: q) = C (d i j) + X * polyD d p q := rfl

/-- The coefficients of `polyD d` are digits of `d`. -/
theorem abs_coeff_polyD_le {d : Fin 3 → Fin 3 → ℤ} (hd : ∀ i j, |d i j| ≤ 1) :
    ∀ (p q : List (Fin 3)) (j : ℕ), |(polyD d p q).coeff j| ≤ 1 := by
  intro p
  induction p with
  | nil => intro q j; simp
  | cons i p ih =>
    intro q j
    obtain _ | ⟨i', q⟩ := q
    · simp
    obtain _ | j := j
    · simpa using hd i i'
    · rw [polyD_cons, coeff_add, coeff_C, coeff_X_mul]
      simpa using ih q j

/-- `polyD d 𝐩 𝐪` has no coefficient of degree at least `|𝐩|`. -/
theorem coeff_polyD_eq_zero (d : Fin 3 → Fin 3 → ℤ) :
    ∀ (p q : List (Fin 3)) (j : ℕ), p.length ≤ j → (polyD d p q).coeff j = 0 := by
  intro p
  induction p with
  | nil => intro q j _; simp
  | cons i p ih =>
    intro q j hj
    obtain _ | ⟨i', q⟩ := q
    · simp
    obtain _ | j := j
    · simp at hj
    · rw [polyD_cons, coeff_add, coeff_C, coeff_X_mul]
      simpa using ih q j (by simpa using hj)

/-- The coefficients of `polyD d 𝐩 𝐪` are at most `|𝐩|` in modulus. -/
theorem abs_coeff_polyD_le_length {d : Fin 3 → Fin 3 → ℤ} (hd : ∀ i j, |d i j| ≤ 1)
    (p q : List (Fin 3)) (j : ℕ) : |(polyD d p q).coeff j| ≤ p.length := by
  by_cases hj : p.length ≤ j
  · simp [coeff_polyD_eq_zero d p q j hj]
  · exact (abs_coeff_polyD_le hd p q j).trans (by exact_mod_cast (by omega : 1 ≤ p.length))

/-- The value of `polyD d` at `λ`: `d(i, j) + λ · (polyD d 𝐩 𝐪)(λ)`. -/
theorem aeval_polyD_cons (d : Fin 3 → Fin 3 → ℤ) (lam : ℝ) (i j : Fin 3) (p q : List (Fin 3)) :
    aeval lam (polyD d (i :: p) (j :: q)) = d i j + lam * aeval lam (polyD d p q) := by
  simp

/-- For `0 ≤ λ ≤ 1/3`, `|(polyD d 𝐩 𝐪)(λ)| ≤ 3/2`. -/
theorem abs_aeval_polyD_le {d : Fin 3 → Fin 3 → ℤ} (hd : ∀ i j, |d i j| ≤ 1) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1 / 3) :
    ∀ p q : List (Fin 3), |aeval lam (polyD d p q)| ≤ 3 / 2 := by
  intro p
  induction p with
  | nil => intro q; norm_num
  | cons i p ih =>
    intro q
    obtain _ | ⟨i', q⟩ := q
    · norm_num
    rw [aeval_polyD_cons]
    have h1 : |(d i i' : ℝ)| ≤ 1 := by exact_mod_cast hd i i'
    have h2 := ih q
    calc |(d i i' : ℝ) + lam * aeval lam (polyD d p q)|
        ≤ |(d i i' : ℝ)| + |lam * aeval lam (polyD d p q)| := abs_add_le _ _
      _ = |(d i i' : ℝ)| + lam * |aeval lam (polyD d p q)| := by
          rw [abs_mul, abs_of_nonneg hlam0]
      _ ≤ 1 + 1 / 3 * (3 / 2) := by gcongr
      _ = 3 / 2 := by norm_num

/-- `h_𝐩(0) - h_𝐪(0) = U(λ) + t V(λ)` for words of a common length, with `U = polyD difU 𝐩 𝐪`
and `V = polyD difV 𝐩 𝐪`. -/
theorem homWord_sub_eq (lam t : ℝ) :
    ∀ p q : List (Fin 3), q.length = p.length →
      homWord lam t p 0 - homWord lam t q 0 =
        aeval lam (polyD difU p q) + t * aeval lam (polyD difV p q) := by
  intro p
  induction p with
  | nil => intro q hq; simp [List.length_eq_zero_iff.1 hq]
  | cons i p ih =>
    intro q hq
    obtain _ | ⟨j, q⟩ := q
    · simp at hq
    rw [homWord_cons, homWord_cons, aeval_polyD_cons, aeval_polyD_cons]
    have := ih q (by simpa using hq)
    have h2 := homTrans_sub t i j
    linear_combination lam * this + h2


/-- `polyD d (𝐩𝐬) (𝐪𝐬') = polyD d 𝐩 𝐪 + X^{|𝐩|} polyD d 𝐬 𝐬'` for `|𝐩| = |𝐪|`. -/
theorem polyD_append (d : Fin 3 → Fin 3 → ℤ) :
    ∀ (p q s s' : List (Fin 3)), q.length = p.length →
      polyD d (p ++ s) (q ++ s') = polyD d p q + X ^ p.length * polyD d s s' := by
  intro p
  induction p with
  | nil => intro q s s' hq; simp [List.length_eq_zero_iff.1 hq]
  | cons i p ih =>
    intro q s s' hq
    obtain _ | ⟨j, q⟩ := q
    · simp at hq
    simp only [List.cons_append, polyD_cons, List.length_cons]
    rw [ih q s s' (by simpa using hq)]
    ring

/-- A block of zeros contributes nothing to `polyD d` when `d 0 0 = 0`. -/
theorem polyD_replicate (d : Fin 3 → Fin 3 → ℤ) (hd : d 0 0 = 0) (a : ℕ) :
    polyD d (List.replicate a 0) (List.replicate a 0) = 0 := by
  induction a with
  | zero => rfl
  | succ a ih => simp [List.replicate_succ, ih, hd]

/-- A block of `a` zeros in front multiplies `polyD d` by `X^a` when `d 0 0 = 0`. -/
theorem polyD_replicate_append (d : Fin 3 → Fin 3 → ℤ) (hd : d 0 0 = 0) (a : ℕ)
    (s s' : List (Fin 3)) :
    polyD d (List.replicate a 0 ++ s) (List.replicate a 0 ++ s') = X ^ a * polyD d s s' := by
  rw [polyD_append d _ _ _ _ rfl, polyD_replicate d hd, List.length_replicate, zero_add]

/-! ### Pairs of words -/

/-- A pair `(𝐰, 𝐰')` of words. -/
abbrev WordPair := List (Fin 3) × List (Fin 3)

/-- A pair of distinct words of a common length. -/
def WordPair.Valid (π : WordPair) : Prop := π.2.length = π.1.length ∧ π.1 ≠ π.2

/-- The difference `h_𝐰(0) - h_{𝐰'}(0)` of a pair. -/
noncomputable def pairDiff (lam t : ℝ) (π : WordPair) : ℝ :=
  homWord lam t π.1 0 - homWord lam t π.2 0

/-- The polynomial `U_π`, the coefficient of `1` in the difference of a pair. -/
noncomputable def pU (π : WordPair) : ℤ[X] := polyD difU π.1 π.2

/-- The polynomial `V_π`, the coefficient of `t` in the difference of a pair. -/
noncomputable def pV (π : WordPair) : ℤ[X] := polyD difV π.1 π.2

/-- `h_𝐰(0) - h_{𝐰'}(0) = U_π(λ) + t V_π(λ)`. -/
theorem pairDiff_eq (lam t : ℝ) {π : WordPair} (h : π.2.length = π.1.length) :
    pairDiff lam t π = aeval lam (pU π) + t * aeval lam (pV π) :=
  homWord_sub_eq lam t π.1 π.2 h

/-- The crossing polynomial `U_π V_{π'} - U_{π'} V_π` of two pairs: the curves
`t = -U_π/V_π` and `t = -U_{π'}/V_{π'}` meet at its roots. -/
noncomputable def pairCross (π π' : WordPair) : ℤ[X] := pU π * pV π' - pU π' * pV π

/-- The polynomials of a pair of distinct words of a common length do not both vanish. -/
theorem pU_ne_zero_or_pV_ne_zero :
    ∀ (p q : List (Fin 3)), q.length = p.length → p ≠ q →
      polyD difU p q ≠ 0 ∨ polyD difV p q ≠ 0 := by
  intro p
  induction p with
  | nil => intro q hq hne; exact absurd (List.length_eq_zero_iff.1 hq).symm hne
  | cons i p ih =>
    intro q hq hne
    obtain _ | ⟨j, q⟩ := q
    · simp at hq
    by_cases hij : i = j
    · subst hij
      have hne' : p ≠ q := fun h => hne (h ▸ rfl)
      have hdu : difU i i = 0 := by simp [difU]
      have hdv : difV i i = 0 := by simp [difV]
      rcases ih q (by simpa using hq) hne' with h | h
      · left
        rw [polyD_cons, hdu, C_0, zero_add]
        exact mul_ne_zero X_ne_zero h
      · right
        rw [polyD_cons, hdv, C_0, zero_add]
        exact mul_ne_zero X_ne_zero h
    · have : difU i j ≠ 0 ∨ difV i j ≠ 0 := by
        fin_cases i <;> fin_cases j <;> simp [difU, difV] at hij ⊢
      rcases this with h | h
      · left
        intro h0
        have := congrArg (fun P : ℤ[X] => P.coeff 0) h0
        simp at this
        exact h this
      · right
        intro h0
        have := congrArg (fun P : ℤ[X] => P.coeff 0) h0
        simp at this
        exact h this

/-- If a pair of distinct words of length `m` has equal values at `(λ, t)`, then `Δ_n = 0` for
every `n ≥ m`: append the same zeros to both words. -/
theorem homGap_eq_zero_of_pairDiff {lam t : ℝ} {π : WordPair} (hπ : π.Valid)
    (h : pairDiff lam t π = 0) {n : ℕ} (hn : π.1.length ≤ n) : homGap lam t n = 0 := by
  refine le_antisymm ?_ zero_le
  have hlen1 : (π.1 ++ List.replicate (n - π.1.length) 0).length = n := by simp; omega
  have hlen2 : (π.2 ++ List.replicate (n - π.1.length) 0).length = n := by
    simp [hπ.1]; omega
  have hne : π.1 ++ List.replicate (n - π.1.length) 0 ≠ π.2 ++ List.replicate (n - π.1.length) 0 :=
    fun he => hπ.2 (List.append_inj he hπ.1.symm).1
  unfold homGap
  refine (iInf_le _ (π.1 ++ List.replicate (n - π.1.length) 0)).trans ?_
  refine (iInf_le _ (π.2 ++ List.replicate (n - π.1.length) 0)).trans ?_
  refine (iInf_le _ hlen1).trans ((iInf_le _ hlen2).trans ((iInf_le _ hne).trans ?_))
  rw [homWord_append_replicate_zero, homWord_append_replicate_zero]
  rw [pairDiff, sub_eq_zero] at h
  simp [h]

/-! ### Continuity and openness -/

/-- `(λ, t) ↦ h_𝐰(0)` is continuous. -/
theorem continuous_homWord (w : List (Fin 3)) :
    Continuous fun z : ℝ × ℝ => homWord z.1 z.2 w 0 := by
  induction w with
  | nil => exact continuous_const
  | cons i w ih =>
    simp only [homWord_cons]
    refine (continuous_fst.mul ih).add ?_
    fin_cases i <;> simp [homTrans]
    · exact continuous_const
    · exact continuous_snd
    · exact continuous_const

/-- `(λ, t) ↦ h_𝐰(0) - h_{𝐰'}(0)` is continuous. -/
theorem continuous_pairDiff (π : WordPair) : Continuous fun z : ℝ × ℝ => pairDiff z.1 z.2 π :=
  (continuous_homWord π.1).sub (continuous_homWord π.2)

/-- `{(λ, t) : Δ_n^{λ,t} < c}` is open: `Δ_n` is the minimum of finitely many continuous
functions. -/
theorem isOpen_homGap_lt (n : ℕ) (c : ENNReal) :
    IsOpen {z : ℝ × ℝ | homGap z.1 z.2 n < c} := by
  have : {z : ℝ × ℝ | homGap z.1 z.2 n < c} =
      ⋃ (w : List (Fin 3)) (w' : List (Fin 3)) (_ : w.length = n) (_ : w'.length = n)
        (_ : w ≠ w'),
        {z : ℝ × ℝ | ENNReal.ofReal |homWord z.1 z.2 w 0 - homWord z.1 z.2 w' 0| < c} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, homGap, iInf_lt_iff]
  rw [this]
  refine isOpen_iUnion fun w => isOpen_iUnion fun w' => isOpen_iUnion fun _ =>
    isOpen_iUnion fun _ => isOpen_iUnion fun _ => ?_
  exact isOpen_lt (ENNReal.continuous_ofReal.comp
    ((continuous_homWord w).sub (continuous_homWord w')).abs) continuous_const

/-! ### Concatenation -/

/-- The concatenation `π'' = (𝐰 0^a 𝐯 0^b 1, 𝐰' 0^a 𝐯' 0^b 0)` of `π = (𝐰, 𝐰')` and
`π' = (𝐯, 𝐯')`. -/
def extPair (π π' : WordPair) (a b : ℕ) : WordPair :=
  (π.1 ++ (List.replicate a 0 ++ (π'.1 ++ (List.replicate b 0 ++ [1]))),
    π.2 ++ (List.replicate a 0 ++ (π'.2 ++ (List.replicate b 0 ++ [0]))))

/-- The concatenation of two valid pairs is valid. -/
theorem valid_extPair {π π' : WordPair} (hπ : π.Valid) (hπ' : π'.Valid) (a b : ℕ) :
    (extPair π π' a b).Valid := by
  refine ⟨?_, fun he => hπ.2 (List.append_inj he hπ.1.symm).1⟩
  simp [extPair, hπ.1, hπ'.1]

/-- `U_{π''} = U_π + X^{|π| + a} U_{π'}`. -/
theorem pU_extPair {π π' : WordPair} (hπ : π.2.length = π.1.length)
    (hπ' : π'.2.length = π'.1.length) (a b : ℕ) :
    pU (extPair π π' a b) = pU π + X ^ (π.1.length + a) * pU π' := by
  have h00 : difU 0 0 = 0 := by simp [difU]
  simp only [pU, extPair]
  rw [polyD_append difU _ _ _ _ hπ, polyD_replicate_append difU h00,
    polyD_append difU _ _ _ _ hπ', polyD_replicate_append difU h00]
  simp [difU, pow_add]
  ring

/-- `V_{π''} = V_π + X^{|π| + a} (V_{π'} + X^{|π'| + b})`. -/
theorem pV_extPair {π π' : WordPair} (hπ : π.2.length = π.1.length)
    (hπ' : π'.2.length = π'.1.length) (a b : ℕ) :
    pV (extPair π π' a b) =
      pV π + X ^ (π.1.length + a) * (pV π' + X ^ (π'.1.length + b)) := by
  have h00 : difV 0 0 = 0 := by simp [difV]
  simp only [pV, extPair]
  rw [polyD_append difV _ _ _ _ hπ, polyD_replicate_append difV h00,
    polyD_append difV _ _ _ _ hπ', polyD_replicate_append difV h00]
  simp [difV, pow_add]
  ring

/-- The crossing polynomial of `π` and its concatenation:
`U_π V_{π''} - U_{π''} V_π = X^{|π| + a} (U_π V_{π'} - U_{π'} V_π + X^{|π'| + b} U_π)`. -/
theorem pairCross_extPair {π π' : WordPair} (hπ : π.2.length = π.1.length)
    (hπ' : π'.2.length = π'.1.length) (a b : ℕ) :
    pairCross π (extPair π π' a b) =
      X ^ (π.1.length + a) * (pairCross π π' + X ^ (π'.1.length + b) * pU π) := by
  rw [pairCross, pairCross, pU_extPair hπ hπ', pV_extPair hπ hπ']
  ring

/-! ### Evaluation -/

/-- The value of an integer polynomial at a real point is the value of its image in `ℝ[X]`. -/
theorem aeval_int_eq_eval_map (x : ℝ) (P : ℤ[X]) :
    aeval x P = (P.map (Int.castRingHom ℝ)).eval x := by
  rw [Polynomial.eval_map, Polynomial.aeval_def]
  rfl

/-- For `0 ≤ λ ≤ 1/3`, `|(polyD d 𝐩 𝐪)'(λ)| ≤ 9/4`. -/
theorem abs_aeval_derivative_polyD_le {d : Fin 3 → Fin 3 → ℤ} (hd : ∀ i j, |d i j| ≤ 1)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1 / 3) :
    ∀ p q : List (Fin 3), |aeval lam (derivative (polyD d p q))| ≤ 9 / 4 := by
  intro p
  induction p with
  | nil => intro q; norm_num
  | cons i p ih =>
    intro q
    obtain _ | ⟨i', q⟩ := q
    · norm_num
    rw [polyD_cons, derivative_add, derivative_C, zero_add, derivative_mul, derivative_X,
      one_mul, map_add, map_mul, aeval_X]
    have h1 := abs_aeval_polyD_le hd hlam0 hlam1 p q
    have h2 := ih q
    calc |aeval lam (polyD d p q) + lam * aeval lam (derivative (polyD d p q))|
        ≤ |aeval lam (polyD d p q)| + |lam * aeval lam (derivative (polyD d p q))| :=
          abs_add_le _ _
      _ = |aeval lam (polyD d p q)| + lam * |aeval lam (derivative (polyD d p q))| := by
          rw [abs_mul, abs_of_nonneg hlam0]
      _ ≤ 3 / 2 + 1 / 3 * (9 / 4) := by gcongr
      _ = 9 / 4 := by norm_num

/-! ### A simple root of a perturbation -/

/-- The case `R'(x₀) > 0` of `exists_root_near`. -/
theorem exists_root_near_of_pos {R S : ℝ[X]} {x₀ r A A' : ℝ} (hx₀ : 0 < x₀) (hxr : x₀ < r)
    (hr : r < 1) (hS : ∀ y ∈ Set.Icc 0 r, |S.eval y| ≤ A)
    (hS' : ∀ y ∈ Set.Icc 0 r, |(derivative S).eval y| ≤ A')
    (hR : R.eval x₀ = 0) (hR' : 0 < (derivative R).eval x₀) (hSx : S.eval x₀ ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m ≥ N, ∃ y, |y - x₀| < ε ∧ y ≠ x₀ ∧ (R + X ^ m * S).eval y = 0 ∧
      (derivative (R + X ^ m * S)).eval y ≠ 0 := by
  set c := (derivative R).eval x₀ with hc
  have hr0 : 0 < r := hx₀.trans hxr
  have hA : 0 ≤ A := (abs_nonneg _).trans (hS x₀ ⟨hx₀.le, hxr.le⟩)
  have hA' : 0 ≤ A' := (abs_nonneg _).trans (hS' x₀ ⟨hx₀.le, hxr.le⟩)
  -- continuity of `R'`
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ : ∃ δ₁ > 0, ∀ y, |y - x₀| < δ₁ → c / 2 < (derivative R).eval y := by
    have := (derivative R).continuous.continuousAt (x := x₀)
    rw [Metric.continuousAt_iff] at this
    obtain ⟨δ, hδ, h⟩ := this (c / 2) (by linarith)
    refine ⟨δ, hδ, fun y hy => ?_⟩
    have := h (by rwa [Real.dist_eq])
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.1]
  set δ := min (min (δ₁ / 2) (ε / 2)) (min (x₀ / 2) ((r - x₀) / 2)) with hδdef
  have hδ1 : δ ≤ δ₁ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ ε / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : δ ≤ x₀ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ4 : δ ≤ (r - x₀) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hδ0 : 0 < δ := by
    simp only [hδdef, lt_min_iff]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  set a := x₀ - δ with hadef
  set b := x₀ + δ with hbdef
  have hab : a ≤ b := by linarith
  have hsub : ∀ y ∈ Set.Icc a b, y ∈ Set.Icc 0 r := fun y hy => ⟨by linarith [hy.1], by
    linarith [hy.2]⟩
  have hderiv : ∀ y ∈ Set.Icc a b, c / 2 < (derivative R).eval y := fun y hy =>
    hδ₁' y (by rw [abs_lt]; constructor <;> linarith [hy.1, hy.2])
  -- the mean value theorem
  have hmvt := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc a b) R.continuousOn
    R.differentiable.differentiableOn (C := c / 2) (fun y hy => by
      rw [interior_Icc] at hy
      rw [Polynomial.deriv]
      exact (hderiv y ⟨hy.1.le, hy.2.le⟩).le)
  have hRb : c / 2 * δ ≤ R.eval b := by
    have := hmvt x₀ ⟨by linarith, by linarith⟩ b ⟨hab, le_rfl⟩ (by linarith)
    rw [hR] at this
    simpa [hbdef] using this
  have hRa : c / 2 * δ ≤ -R.eval a := by
    have := hmvt a ⟨le_rfl, hab⟩ x₀ ⟨by linarith, by linarith⟩ (by linarith)
    rw [hR] at this
    simpa [hadef] using this
  -- the size of the perturbation
  have t1 : Tendsto (fun m : ℕ => r ^ m * A) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr).mul_const A
  have t2 : Tendsto (fun m : ℕ => (m : ℝ) * r ^ m * (A / r) + r ^ m * A') atTop (𝓝 0) := by
    simpa using ((tendsto_self_mul_const_pow_of_lt_one hr0.le hr).mul_const (A / r)).add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr).mul_const A')
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((t1.eventually (gt_mem_nhds (show (0 : ℝ) < c / 2 * δ by positivity))).and
      (t2.eventually (gt_mem_nhds (show (0 : ℝ) < c / 4 by positivity))))
  refine ⟨N, fun m hm => ?_⟩
  obtain ⟨h1, h2⟩ := hN m hm
  have hpow : ∀ y ∈ Set.Icc a b, y ^ m ≤ r ^ m := fun y hy =>
    pow_le_pow_left₀ (hsub y hy).1 (hsub y hy).2 m
  have hpert : ∀ y ∈ Set.Icc a b, |y ^ m * S.eval y| ≤ r ^ m * A := by
    intro y hy
    rw [abs_mul, abs_of_nonneg (pow_nonneg (hsub y hy).1 m)]
    exact mul_le_mul (hpow y hy) (hS y (hsub y hy)) (abs_nonneg _) (pow_nonneg hr0.le m)
  have heval : ∀ y, (R + X ^ m * S).eval y = R.eval y + y ^ m * S.eval y := fun y => by
    simp
  have hFb : 0 < (R + X ^ m * S).eval b := by
    rw [heval]
    have := hpert b ⟨hab, le_rfl⟩
    rw [abs_le] at this
    linarith [this.1]
  have hFa : (R + X ^ m * S).eval a < 0 := by
    rw [heval]
    have := hpert a ⟨le_rfl, hab⟩
    rw [abs_le] at this
    linarith [this.2]
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc hab (R + X ^ m * S).continuousOn
    (show (0 : ℝ) ∈ Set.Icc ((R + X ^ m * S).eval a) ((R + X ^ m * S).eval b) from
      ⟨hFa.le, hFb.le⟩)
  simp only at hy0
  refine ⟨y, ?_, ?_, hy0, ?_⟩
  · rw [abs_lt]; constructor <;> linarith [hy.1, hy.2]
  · rintro rfl
    rw [heval, hR, zero_add] at hy0
    exact mul_ne_zero (pow_ne_zero m hx₀.ne') hSx hy0
  · have hy' := hsub y hy
    have hd : (derivative (R + X ^ m * S)).eval y =
        (derivative R).eval y + ((m : ℝ) * y ^ (m - 1) * S.eval y +
          y ^ m * (derivative S).eval y) := by
      simp [derivative_mul, derivative_X_pow]
    have hb1 : |(m : ℝ) * y ^ (m - 1) * S.eval y| ≤ (m : ℝ) * r ^ m * (A / r) := by
      have hm' : (m : ℝ) * r ^ (m - 1) = (m : ℝ) * r ^ m / r := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · simp [h0]
        · rw [eq_div_iff hr0.ne', mul_assoc, ← pow_succ, Nat.sub_add_cancel h0]
      rw [abs_mul, abs_mul, Nat.abs_cast, abs_of_nonneg (pow_nonneg hy'.1 _)]
      calc (m : ℝ) * y ^ (m - 1) * |S.eval y| ≤ (m : ℝ) * r ^ (m - 1) * A := by
            gcongr
            · exact hy'.1
            · exact hy'.2
            · exact hS y hy'
        _ = (m : ℝ) * r ^ m * (A / r) := by rw [hm']; ring
    have hb2 : |y ^ m * (derivative S).eval y| ≤ r ^ m * A' := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hy'.1 m)]
      exact mul_le_mul (hpow y hy) (hS' y hy') (abs_nonneg _) (pow_nonneg hr0.le m)
    have hRy := hderiv y hy
    rw [hd]
    rw [abs_le] at hb1 hb2
    intro h0
    linarith [hb1.1, hb2.1]

/-- A perturbation `R + X^m S` of a polynomial `R` with a simple root at `x₀ ∈ (0, 1)` with
`S(x₀) ≠ 0` has, for every large `m`, a simple root `y ≠ x₀` within `ε` of `x₀`. -/
theorem exists_root_near {R S : ℝ[X]} {x₀ r A A' : ℝ} (hx₀ : 0 < x₀) (hxr : x₀ < r)
    (hr : r < 1) (hS : ∀ y ∈ Set.Icc 0 r, |S.eval y| ≤ A)
    (hS' : ∀ y ∈ Set.Icc 0 r, |(derivative S).eval y| ≤ A')
    (hR : R.eval x₀ = 0) (hR' : (derivative R).eval x₀ ≠ 0) (hSx : S.eval x₀ ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m ≥ N, ∃ y, |y - x₀| < ε ∧ y ≠ x₀ ∧ (R + X ^ m * S).eval y = 0 ∧
      (derivative (R + X ^ m * S)).eval y ≠ 0 := by
  rcases lt_or_gt_of_ne hR' with hneg | hpos
  · obtain ⟨N, hN⟩ := exists_root_near_of_pos (R := -R) (S := -S) hx₀ hxr hr
      (fun y hy => by simpa using hS y hy) (fun y hy => by simpa using hS' y hy)
      (by simp [hR]) (by simpa using hneg) (by simpa using hSx) hε
    refine ⟨N, fun m hm => ?_⟩
    obtain ⟨y, h1, h2, h3, h4⟩ := hN m hm
    have he : -R + X ^ m * -S = -(R + X ^ m * S) := by ring
    rw [he, eval_neg, neg_eq_zero] at h3
    rw [he, derivative_neg, eval_neg, neg_ne_zero] at h4
    exact ⟨y, h1, h2, h3, h4⟩
  · exact exists_root_near_of_pos hx₀ hxr hr hS hS' hR hpos hSx hε

/-! ### Crossing points -/

/-- The curves of `π` and `π'` cross transversally at `x = (λ, t)`: `V_π(λ) ≠ 0`,
`V_{π'}(λ) ≠ 0`, the point `x` lies on the curve `U_π + t V_π = 0` of `π`, and `λ` is a simple
root of the crossing polynomial `U_π V_{π'} - U_{π'} V_π`. -/
def IsCrossPt (π π' : WordPair) (x : ℝ × ℝ) : Prop :=
  aeval x.1 (pV π) ≠ 0 ∧ aeval x.1 (pV π') ≠ 0 ∧ pairDiff x.1 x.2 π = 0 ∧
    aeval x.1 (pairCross π π') = 0 ∧ aeval x.1 (derivative (pairCross π π')) ≠ 0

/-- A crossing point lies on both curves. -/
theorem IsCrossPt.pairDiff_right {π π' : WordPair} (hπ : π.2.length = π.1.length)
    (hπ' : π'.2.length = π'.1.length) {x : ℝ × ℝ} (hx : IsCrossPt π π' x) :
    pairDiff x.1 x.2 π' = 0 := by
  obtain ⟨hV, -, hD, hC, -⟩ := hx
  rw [pairDiff_eq _ _ hπ] at hD
  rw [pairDiff_eq _ _ hπ']
  rw [pairCross, map_sub, map_mul, map_mul] at hC
  have : (aeval x.1 (pU π') + x.2 * aeval x.1 (pV π')) * aeval x.1 (pV π) = 0 := by
    linear_combination (-1 : ℝ) * hC + aeval x.1 (pV π') * hD
  exact (mul_eq_zero.1 this).resolve_right hV

/-- Crossing is symmetric. -/
theorem IsCrossPt.symm {π π' : WordPair} (hπ : π.2.length = π.1.length)
    (hπ' : π'.2.length = π'.1.length) {x : ℝ × ℝ} (hx : IsCrossPt π π' x) :
    IsCrossPt π' π x := by
  have hD' := hx.pairDiff_right hπ hπ'
  obtain ⟨hV, hV', -, hC, hC'⟩ := hx
  have hsw : pairCross π' π = -pairCross π π' := by rw [pairCross, pairCross]; ring
  refine ⟨hV', hV, hD', ?_, ?_⟩
  · rw [hsw, map_neg, hC, neg_zero]
  · rw [hsw, derivative_neg, map_neg, neg_ne_zero]
    exact hC'

/-- The crossing lemma. Let `π, π'` cross transversally at `x = (λ, t)` with `0 < λ < 1/3` and
`t > 0`. Every neighbourhood `W` of `x` contains a point `y ≠ x` with `y.1 ≠ λ` on the curve of
`π` at which `π` crosses transversally a concatenation `π'' = (𝐰 0^a 𝐯 0^b 1, 𝐰' 0^a 𝐯' 0^b 0)`.
The root of `U_π V_{π''} - U_{π''} V_π = X^{|π|+a}(U_π V_{π'} - U_{π'} V_π + X^{|π'|+b} U_π)`
near `λ` is a perturbation of `λ` (`exists_root_near`). -/
theorem exists_crossPt_near {π π' : WordPair} (hπ : π.Valid) (hπ' : π'.Valid) {x : ℝ × ℝ}
    (hx : IsCrossPt π π' x) (hx1 : 0 < x.1) (hx2 : x.1 < 1 / 3) (ht : 0 < x.2)
    {W : Set (ℝ × ℝ)} (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ y ∈ W, y.1 ≠ x.1 ∧ ∃ π'' : WordPair, π''.Valid ∧ IsCrossPt π π'' y := by
  obtain ⟨hV, hV', hD, hC, hC'⟩ := hx
  set lam₀ := x.1 with hlam₀
  set U := pU π
  set V := pV π
  -- the curve of `π` near `λ`
  set g : ℝ → ℝ × ℝ := fun l => (l, -aeval l U / aeval l V) with hg
  have hD2 : aeval lam₀ U + x.2 * aeval lam₀ V = 0 := by rwa [pairDiff_eq _ _ hπ.1] at hD
  have hgx : g lam₀ = x := by
    refine Prod.ext rfl ?_
    show -aeval lam₀ U / aeval lam₀ V = x.2
    rw [div_eq_iff hV]
    linarith
  have hgc : ContinuousAt g lam₀ :=
    continuousAt_id.prodMk ((Polynomial.continuous_aeval U).continuousAt.neg.div
      (Polynomial.continuous_aeval V).continuousAt hV)
  obtain ⟨ε₁, hε₁, hε₁'⟩ : ∃ ε₁ > 0, ∀ l, |l - lam₀| < ε₁ → g l ∈ W := by
    have : g ⁻¹' W ∈ 𝓝 lam₀ := hgc.preimage_mem_nhds (by rw [hgx]; exact hW.mem_nhds hxW)
    obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.1 this
    exact ⟨ε, hε, fun l hl => h (by rwa [Metric.mem_ball, Real.dist_eq])⟩
  set v₀ := |aeval lam₀ V| with hv₀
  have hv₀pos : 0 < v₀ := abs_pos.2 hV
  obtain ⟨ε₂, hε₂, hε₂'⟩ : ∃ ε₂ > 0, ∀ l, |l - lam₀| < ε₂ → v₀ / 2 < |aeval l V| := by
    have := (Polynomial.continuous_aeval V).continuousAt (x := lam₀)
    rw [Metric.continuousAt_iff] at this
    obtain ⟨δ, hδ, h⟩ := this (v₀ / 2) (by linarith)
    refine ⟨δ, hδ, fun l hl => ?_⟩
    have h1 := h (by rwa [Real.dist_eq])
    rw [Real.dist_eq] at h1
    have h2 := abs_sub_abs_le_abs_sub (aeval lam₀ V) (aeval l V)
    rw [abs_sub_comm] at h1
    linarith
  set ε := min (min ε₁ ε₂) (min lam₀ (1 / 3 - lam₀)) with hεdef
  have hε0 : 0 < ε := by
    simp only [hεdef, lt_min_iff]
    refine ⟨⟨hε₁, hε₂⟩, hx1, by linarith⟩
  -- the perturbed crossing polynomial
  set ι := Int.castRingHom ℝ
  have hSb : ∀ y ∈ Set.Icc (0 : ℝ) (1 / 3), |(U.map ι).eval y| ≤ 3 / 2 := fun y hy => by
    rw [← aeval_int_eq_eval_map]
    exact abs_aeval_polyD_le abs_difU_le hy.1 hy.2 _ _
  have hSb' : ∀ y ∈ Set.Icc (0 : ℝ) (1 / 3), |(derivative (U.map ι)).eval y| ≤ 9 / 4 :=
    fun y hy => by
      rw [derivative_map, ← aeval_int_eq_eval_map]
      exact abs_aeval_derivative_polyD_le abs_difU_le hy.1 hy.2 _ _
  have hUx : aeval lam₀ U ≠ 0 := by
    intro h0
    rw [h0, zero_add] at hD2
    exact (mul_ne_zero ht.ne' hV) hD2
  obtain ⟨N, hN⟩ := exists_root_near (R := (pairCross π π').map ι) (S := U.map ι)
    (r := 1 / 3) hx1 hx2 (by norm_num) hSb hSb'
    (by rw [← aeval_int_eq_eval_map]; exact hC)
    (by rw [derivative_map, ← aeval_int_eq_eval_map]; exact hC')
    (by rw [← aeval_int_eq_eval_map]; exact hUx) hε0
  obtain ⟨mu, hmu1, hmu2, hmu3, hmu4⟩ := hN (π'.1.length + N) (by omega)
  have hmuε1 : |mu - lam₀| < ε₁ := hmu1.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hmuε2 : |mu - lam₀| < ε₂ := hmu1.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hmu0 : 0 < mu := by
    have := hmu1.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    rw [abs_lt] at this
    linarith
  have hmu13 : mu < 1 / 3 := by
    have := hmu1.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    rw [abs_lt] at this
    linarith
  -- the length `a` of the first block of zeros
  obtain ⟨a, ha⟩ := exists_pow_lt_of_lt_one (show 0 < v₀ / 5 by positivity)
    (show (1 / 3 : ℝ) < 1 by norm_num)
  set M := π.1.length + a with hM
  have hpowM : mu ^ M * (5 / 2) < v₀ / 2 := by
    have h1 : mu ^ M ≤ (1 / 3) ^ M := pow_le_pow_left₀ hmu0.le hmu13.le M
    have h2 : (1 / 3 : ℝ) ^ M ≤ (1 / 3) ^ a := pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (by omega)
    nlinarith
  refine ⟨g mu, hε₁' mu hmuε1, hmu2, extPair π π' a N, valid_extPair hπ hπ' a N, ?_⟩
  have hVmu : v₀ / 2 < |aeval mu V| := hε₂' mu hmuε2
  have hVmu0 : aeval mu V ≠ 0 := fun h0 => by rw [h0, abs_zero] at hVmu; linarith
  have hP : (pairCross π π' + X ^ (π'.1.length + N) * U).map ι =
      (pairCross π π').map ι + X ^ (π'.1.length + N) * U.map ι := by
    simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]
  refine ⟨hVmu0, ?_, ?_, ?_, ?_⟩
  · -- `V_{π''}(μ) ≠ 0`
    show aeval mu (pV (extPair π π' a N)) ≠ 0
    rw [pV_extPair hπ.1 hπ'.1, map_add, map_mul, map_pow, aeval_X, map_add, map_pow, aeval_X]
    have hb : |aeval mu (pV π')| ≤ 3 / 2 :=
      abs_aeval_polyD_le abs_difV_le hmu0.le hmu13.le _ _
    have hmuN : mu ^ (π'.1.length + N) ≤ 1 := pow_le_one₀ hmu0.le (by linarith)
    have hmuN0 : 0 ≤ mu ^ (π'.1.length + N) := pow_nonneg hmu0.le _
    have hsmall : |mu ^ M * (aeval mu (pV π') + mu ^ (π'.1.length + N))| < v₀ / 2 := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hmu0.le M)]
      calc mu ^ M * |aeval mu (pV π') + mu ^ (π'.1.length + N)|
          ≤ mu ^ M * (5 / 2) := by
            gcongr
            calc _ ≤ |aeval mu (pV π')| + |mu ^ (π'.1.length + N)| := abs_add_le _ _
              _ ≤ 3 / 2 + 1 := by
                  rw [abs_of_nonneg hmuN0]
                  linarith
              _ = 5 / 2 := by norm_num
        _ < v₀ / 2 := hpowM
    intro h0
    have h1 : aeval mu V = -(mu ^ M * (aeval mu (pV π') + mu ^ (π'.1.length + N))) := by
      linarith
    rw [h1, abs_neg] at hVmu
    linarith
  · -- `y` lies on the curve of `π`
    show pairDiff mu (-aeval mu U / aeval mu V) π = 0
    rw [pairDiff_eq _ _ hπ.1]
    field_simp
    ring
  · -- `μ` is a root
    show aeval mu (pairCross π (extPair π π' a N)) = 0
    rw [pairCross_extPair hπ.1 hπ'.1, map_mul, map_pow, aeval_X, aeval_int_eq_eval_map _
      (pairCross π π' + _), hP, hmu3, mul_zero]
  · -- the root is simple
    show aeval mu (derivative (pairCross π (extPair π π' a N))) ≠ 0
    rw [pairCross_extPair hπ.1 hπ'.1, derivative_mul, map_add, map_mul, map_mul,
      aeval_int_eq_eval_map _ (pairCross π π' + _), aeval_int_eq_eval_map _
      (derivative (pairCross π π' + _)), ← derivative_map, hP, hmu3, mul_zero, zero_add,
      map_pow, aeval_X]
    exact mul_ne_zero (pow_ne_zero _ hmu0.ne') hmu4

/-! ### Accumulating roots -/

/-- An integer polynomial with roots `μ ≠ x₀` arbitrarily close to `x₀` is zero. -/
theorem eq_zero_of_roots_accumulate {P : ℤ[X]} {x₀ : ℝ}
    (h : ∀ ε > 0, ∃ μ : ℝ, μ ≠ x₀ ∧ |μ - x₀| < ε ∧ aeval μ P = 0) : P = 0 := by
  by_contra hP
  set Q := P.map (Int.castRingHom ℝ)
  have hQ : Q ≠ 0 := fun h0 => hP (Polynomial.map_injective (Int.castRingHom ℝ)
    Int.cast_injective (by rw [Polynomial.map_zero]; exact h0))
  have hfin : ({x | Q.IsRoot x} \ {x₀}).Finite :=
    (Polynomial.finite_setOfPred_isRoot hQ).sdiff
  have hopen : IsOpen ({x | Q.IsRoot x} \ {x₀})ᶜ := hfin.isClosed.isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen x₀ (fun hx => hx.2 rfl)
  obtain ⟨μ, hμ1, hμ2, hμ3⟩ := h ε hε
  have hμball : μ ∈ Metric.ball x₀ ε := by rwa [Metric.mem_ball, Real.dist_eq]
  refine hball hμball ⟨?_, hμ1⟩
  show Q.IsRoot μ
  rw [IsRoot, ← aeval_int_eq_eval_map]
  exact hμ3

/-! ### The base crossing -/

/-- The pair `(12111, 13223)` of Bárány and Käenmäki (Lemma 3.8, the sequence
`(0,1)(1,1)(0,-1)(0,-1)(1,0)`), with the letters `0, 1, 2` for their `1, 2, 3`. -/
def basePair₁ : WordPair := ([1, 1, 0, 0, 0], [0, 2, 1, 1, 2])

/-- The pair `(21223, 13111)` of Bárány and Käenmäki (Lemma 3.8, the sequence
`(0,1)(1,0)(0,1)(0,1)(-1,0)`), with the letters `0, 1, 2` for their `1, 2, 3`. -/
def basePair₂ : WordPair := ([1, 0, 1, 1, 2], [0, 2, 0, 0, 0])

/-- `U = -X - X⁴` for the first base pair. -/
theorem pU_basePair₁ : pU basePair₁ = -X - X ^ 4 := by
  simp [basePair₁, pU, difU]; ring

/-- `V = 1 + X - X² - X³` for the first base pair. -/
theorem pV_basePair₁ : pV basePair₁ = 1 + X - X ^ 2 - X ^ 3 := by
  simp [basePair₁, pV, difV]; ring

/-- `U = -X + X⁴` for the second base pair. -/
theorem pU_basePair₂ : pU basePair₂ = -X + X ^ 4 := by
  simp [basePair₂, pU, difU]; ring

/-- `V = 1 + X² + X³` for the second base pair. -/
theorem pV_basePair₂ : pV basePair₂ = 1 + X ^ 2 + X ^ 3 := by
  simp [basePair₂, pV, difV]; ring

/-- The crossing polynomial of the base pairs is `-X²(1 + X)(X² + 3X - 1)`. -/
theorem pairCross_basePair :
    pairCross basePair₁ basePair₂ = -(X ^ 2 * (1 + X)) * (X ^ 2 + 3 * X - 1) := by
  rw [pairCross, pU_basePair₁, pV_basePair₁, pU_basePair₂, pV_basePair₂]
  ring

/-- The base pairs are valid. -/
theorem valid_basePair₁ : basePair₁.Valid := by
  refine ⟨rfl, ?_⟩; simp [basePair₁]

/-- The base pairs are valid. -/
theorem valid_basePair₂ : basePair₂.Valid := by
  refine ⟨rfl, ?_⟩; simp [basePair₂]

/-- The crossing parameter `λ' = (√13 - 3)/2`, the root of `λ² + 3λ - 1` in `(1/4, 1/3)`. -/
noncomputable def lamB : ℝ := (Real.sqrt 13 - 3) / 2

/-- `λ'² + 3λ' - 1 = 0`. -/
theorem lamB_sq : lamB ^ 2 + 3 * lamB - 1 = 0 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)
  simp only [lamB]
  linear_combination h / 4

/-- `0.3 < λ' < 0.305`. -/
theorem lamB_mem : 3 / 10 < lamB ∧ lamB < 61 / 200 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)
  have h0 := Real.sqrt_nonneg 13
  simp only [lamB]
  constructor <;> nlinarith

/-- The translation `t' = (λ' + λ'⁴)/(1 + λ' - λ'² - λ'³)` of the base crossing. -/
noncomputable def tB : ℝ := (lamB + lamB ^ 4) / (1 + lamB - lamB ^ 2 - lamB ^ 3)

/-- `1 + λ' - λ'² - λ'³ > 1`. -/
theorem denom_pos : 1 < 1 + lamB - lamB ^ 2 - lamB ^ 3 := by
  obtain ⟨h1, h2⟩ := lamB_mem
  nlinarith

/-- `1/4 < t' < 7/25`. -/
theorem tB_mem : 1 / 4 < tB ∧ tB < 7 / 25 := by
  obtain ⟨h1, h2⟩ := lamB_mem
  have hd := denom_pos
  simp only [tB]
  constructor
  · rw [lt_div_iff₀ (by linarith)]; nlinarith
  · rw [div_lt_iff₀ (by linarith)]; nlinarith

/-- The base crossing point `(λ', t')`. -/
noncomputable def baseCross : ℝ × ℝ := (lamB, tB)

/-- The base pairs cross transversally at `(λ', t')`. -/
theorem isCrossPt_base : IsCrossPt basePair₁ basePair₂ baseCross := by
  obtain ⟨h1, h2⟩ := lamB_mem
  have hd := denom_pos
  have hroot := lamB_sq
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show aeval lamB (pV basePair₁) ≠ 0
    rw [pV_basePair₁]; simp; nlinarith
  · show aeval lamB (pV basePair₂) ≠ 0
    rw [pV_basePair₂]; simp; positivity
  · show pairDiff lamB tB basePair₁ = 0
    rw [pairDiff_eq _ _ rfl, pU_basePair₁, pV_basePair₁, tB]
    simp
    field_simp
    ring
  · show aeval lamB (pairCross basePair₁ basePair₂) = 0
    rw [pairCross_basePair]
    simp only [map_mul, map_neg, map_add, map_sub, map_pow, aeval_X, map_one, map_ofNat]
    linear_combination (-(lamB ^ 2 * (1 + lamB))) * hroot
  · show aeval lamB (derivative (pairCross basePair₁ basePair₂)) ≠ 0
    have hval : aeval lamB (derivative (pairCross basePair₁ basePair₂)) =
        -(lamB ^ 2 * (1 + lamB) * (2 * lamB + 3)) := by
      rw [pairCross_basePair]
      simp only [derivative_mul, derivative_X_pow, derivative_one, derivative_X,
        derivative_ofNat, map_mul, map_neg,
        map_add, map_sub, map_pow, aeval_X, map_one, map_ofNat, map_zero, map_natCast]
      linear_combination (-(2 * lamB * (1 + lamB) + lamB ^ 2)) * hroot
    rw [hval]
    have : 0 < lamB ^ 2 * (1 + lamB) * (2 * lamB + 3) := by positivity
    linarith

/-! ### The set of good crossing points -/

/-- The open ball of radius `1/100` around the base crossing. -/
noncomputable def baseBall : Set (ℝ × ℝ) := Metric.ball baseCross (1 / 100)

/-- The closed ball of radius `1/100` around the base crossing lies in the parameter region,
with `λ < 1/3` and `t > 0`. -/
theorem mem_region_of_mem_closedBall {y : ℝ × ℝ} (hy : y ∈ Metric.closedBall baseCross (1 / 100)) :
    0 < y.1 ∧ y.1 < 1 / 3 ∧ 0 < y.2 ∧ y.2 < y.1 / (1 - y.1) := by
  obtain ⟨h1, h2⟩ := lamB_mem
  obtain ⟨h3, h4⟩ := tB_mem
  rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq] at hy
  obtain ⟨hy1, hy2⟩ := hy
  rw [abs_le] at hy1 hy2
  simp only [baseCross] at hy1 hy2
  refine ⟨by linarith [hy1.1], by linarith [hy1.2], by linarith [hy2.1], ?_⟩
  rw [lt_div_iff₀ (by linarith [hy1.2])]
  nlinarith [hy1.1, hy1.2, hy2.2]

/-- The set `D_η` of good crossing points for a sequence `η`: points of the ball at which two
valid pairs cross transversally and `Δ_n < η_n` for every `n ≥ 5`. -/
def goodCross (η : ℕ → ℝ) : Set (ℝ × ℝ) :=
  {y | y ∈ baseBall ∧ (∀ n : ℕ, 5 ≤ n → homGap y.1 y.2 n < ENNReal.ofReal (η n)) ∧
    ∃ π π' : WordPair, π.Valid ∧ π'.Valid ∧ IsCrossPt π π' y}

/-- The base crossing is good for every positive sequence: `Δ_n = 0` for `n ≥ 5`. -/
theorem baseCross_mem_goodCross {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) :
    baseCross ∈ goodCross η := by
  refine ⟨Metric.mem_ball_self (by norm_num), fun n hn => ?_,
    basePair₁, basePair₂, valid_basePair₁, valid_basePair₂, isCrossPt_base⟩
  rw [homGap_eq_zero_of_pairDiff valid_basePair₁ isCrossPt_base.2.2.1 (by simpa [basePair₁])]
  exact ENNReal.ofReal_pos.2 (hη n)

/-- The region bounds at a good crossing point. -/
theorem region_of_mem_goodCross {η : ℕ → ℝ} {y : ℝ × ℝ} (hy : y ∈ goodCross η) :
    0 < y.1 ∧ y.1 < 1 / 3 ∧ 0 < y.2 ∧ y.2 < y.1 / (1 - y.1) :=
  mem_region_of_mem_closedBall (Metric.ball_subset_closedBall hy.1)

/-- Near a good crossing point `x` of `π` and `π'` there are good crossing points `y` with
`y.1 ≠ x.1` on the curve of `π`. -/
theorem exists_goodCross_near {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) {x : ℝ × ℝ}
    (hx : x ∈ goodCross η) {π π' : WordPair} (hπ : π.Valid) (hπ' : π'.Valid)
    (hc : IsCrossPt π π' x) {W : Set (ℝ × ℝ)} (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ y ∈ goodCross η, y ∈ W ∧ y.1 ≠ x.1 ∧ pairDiff y.1 y.2 π = 0 := by
  obtain ⟨hx1, hx2, hx3, -⟩ := region_of_mem_goodCross hx
  set W' := W ∩ baseBall ∩ ⋂ n ∈ Finset.Ico 5 π.1.length,
    {z : ℝ × ℝ | homGap z.1 z.2 n < ENNReal.ofReal (η n)} with hW'
  have hW'o : IsOpen W' :=
    (hW.inter Metric.isOpen_ball).inter (isOpen_biInter_finset fun n _ => isOpen_homGap_lt n _)
  have hxW' : x ∈ W' := by
    refine ⟨⟨hxW, hx.1⟩, ?_⟩
    simp only [Set.mem_iInter, Finset.mem_Ico]
    exact fun n hn => hx.2.1 n hn.1
  obtain ⟨y, hyW', hy1, π'', hπ'', hyc⟩ := exists_crossPt_near hπ hπ' hc hx1 hx2 hx3 hW'o hxW'
  refine ⟨y, ⟨hyW'.1.2, fun n hn => ?_, π, π'', hπ, hπ'', hyc⟩, hyW'.1.1, hy1, hyc.2.2.1⟩
  by_cases hnπ : π.1.length ≤ n
  · rw [homGap_eq_zero_of_pairDiff hπ hyc.2.2.1 hnπ]
    exact ENNReal.ofReal_pos.2 (hη n)
  · have := hyW'.2
    simp only [Set.mem_iInter, Finset.mem_Ico] at this
    exact this n ⟨hn, by omega⟩

/-- Near every good crossing point, every curve `U_ρ + t V_ρ = 0` of a valid pair misses some
good crossing point: otherwise the crossing polynomials of `ρ` with both curves through the
point would vanish, and with them `U_ρ` and `V_ρ`. -/
theorem exists_goodCross_pairDiff_ne {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) {x : ℝ × ℝ}
    (hx : x ∈ goodCross η) {ρ : WordPair} (hρ : ρ.Valid) {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hxW : x ∈ W) : ∃ y ∈ goodCross η, y ∈ W ∧ pairDiff y.1 y.2 ρ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨π, π', hπ, hπ', hc⟩ := hx.2.2
  have key : ∀ σ σ' : WordPair, σ.Valid → σ'.Valid → IsCrossPt σ σ' x →
      pairCross ρ σ = 0 := by
    intro σ σ' hσ hσ' hcσ
    refine eq_zero_of_roots_accumulate (x₀ := x.1) fun ε hε => ?_
    obtain ⟨y, hyD, hyW, hy1, hyσ⟩ := exists_goodCross_near hη hx hσ hσ' hcσ
      (hW.inter Metric.isOpen_ball) ⟨hxW, Metric.mem_ball_self hε⟩
    have hyρ := hcon y hyD hyW.1
    have hyb := hyW.2
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq] at hyb
    refine ⟨y.1, hy1, hyb.1, ?_⟩
    rw [pairDiff_eq _ _ hσ.1] at hyσ
    rw [pairDiff_eq _ _ hρ.1] at hyρ
    rw [pairCross, map_sub, map_mul, map_mul]
    linear_combination aeval y.1 (pV σ) * hyρ - aeval y.1 (pV ρ) * hyσ
  have h1 := key π π' hπ hπ' hc
  have h2 := key π' π hπ' hπ (hc.symm hπ.1 hπ'.1)
  have hcross : pairCross π π' ≠ 0 := by
    intro h0; apply hc.2.2.2.2; rw [h0, derivative_zero, map_zero]
  have hVπ : pV π ≠ 0 := by
    intro h0; apply hc.1; rw [h0, map_zero]
  have hVρ : pV ρ = 0 := by
    have : pV ρ * pairCross π π' = 0 := by
      rw [pairCross] at h1 h2 ⊢
      linear_combination (-pV π') * h1 + pV π * h2
    exact (mul_eq_zero.1 this).resolve_right hcross
  have hUρ : pU ρ = 0 := by
    rw [pairCross, hVρ, mul_zero, sub_zero] at h1
    exact (mul_eq_zero.1 h1).resolve_right hVπ
  rcases pU_ne_zero_or_pV_ne_zero ρ.1 ρ.2 hρ.1 hρ.2 with h | h
  · exact h hUρ
  · exact h hVρ

/-! ### The Baire category argument -/

/-- A set of the closure `K` of `D_η` that contains, near every point of `D_η`, a point of `D_η`
is dense in `K`. -/
theorem dense_preimage_of_forall {η : ℕ → ℝ} {O : Set (ℝ × ℝ)}
    (h : ∀ x ∈ goodCross η, ∀ W : Set (ℝ × ℝ), IsOpen W → x ∈ W →
      ∃ y ∈ goodCross η, y ∈ W ∧ y ∈ O) :
    Dense (Subtype.val ⁻¹' O : Set (closure (goodCross η))) := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨z, hz⟩
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.1 hU
  obtain ⟨x, hxV, hxD⟩ := mem_closure_iff.1 z.2 V hV hz
  obtain ⟨y, hyD, hyV, hyO⟩ := h x hxD V hV hxV
  exact ⟨⟨y, subset_closure hyD⟩, hyV, hyO⟩

/-- A set `{z | P → z ∈ s}` with `s` open is open. -/
theorem isOpen_setOf_imp (P : Prop) {s : Set (ℝ × ℝ)} (hs : IsOpen s) :
    IsOpen {z : ℝ × ℝ | P → z ∈ s} := by
  by_cases hP : P
  · simpa [hP] using hs
  · simp [hP]

/-- The Baire category argument. For every positive sequence `η` and every countable set `L` of
reals there is a point `(λ, t)` of the closure of `D_η` with `Δ_n < η_n` for every `n ≥ 5`, on no
curve of a valid pair, with `λ` transcendental and `λ ∉ L`. -/
theorem exists_good_point {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) {L : Set ℝ} (hL : L.Countable) :
    ∃ z ∈ closure (goodCross η),
      (∀ n : ℕ, 5 ≤ n → homGap z.1 z.2 n < ENNReal.ofReal (η n)) ∧
      (∀ ρ : WordPair, ρ.Valid → pairDiff z.1 z.2 ρ ≠ 0) ∧ Transcendental ℚ z.1 ∧ z.1 ∉ L := by
  set K := closure (goodCross η)
  have : CompleteSpace K := isClosed_closure.completeSpace_coe
  have : Nonempty K := ⟨⟨baseCross, subset_closure (baseCross_mem_goodCross hη)⟩⟩
  have hL' : ({x : ℝ | IsAlgebraic ℚ x} ∪ L).Countable := (Algebraic.countable ℚ ℝ).union hL
  have : Countable ↥({x : ℝ | IsAlgebraic ℚ x} ∪ L) := hL'.to_subtype
  set O : ℕ ⊕ WordPair ⊕ ↥({x : ℝ | IsAlgebraic ℚ x} ∪ L) → Set (ℝ × ℝ) := fun i =>
    match i with
    | .inl n => {z | 5 ≤ n → z ∈ {w : ℝ × ℝ | homGap w.1 w.2 n < ENNReal.ofReal (η n)}}
    | .inr (.inl ρ) => {z | ρ.Valid → z ∈ {w : ℝ × ℝ | pairDiff w.1 w.2 ρ ≠ 0}}
    | .inr (.inr α) => {z | z.1 ≠ α.1} with hO
  have hopen : ∀ i, IsOpen (Subtype.val ⁻¹' O i : Set K) := by
    intro i
    refine continuous_subtype_val.isOpen_preimage _ ?_
    rcases i with n | ρ | α
    · exact isOpen_setOf_imp _ (isOpen_homGap_lt n _)
    · exact isOpen_setOf_imp _ (isOpen_ne_fun (continuous_pairDiff ρ) continuous_const)
    · exact isOpen_ne_fun continuous_fst continuous_const
  have hdense : ∀ i, Dense (Subtype.val ⁻¹' O i : Set K) := by
    intro i
    refine dense_preimage_of_forall fun x hx W hW hxW => ?_
    rcases i with n | ρ | α
    · exact ⟨x, hx, hxW, fun hn => hx.2.1 n hn⟩
    · by_cases hρ : ρ.Valid
      · obtain ⟨y, hyD, hyW, hy⟩ := exists_goodCross_pairDiff_ne hη hx hρ hW hxW
        exact ⟨y, hyD, hyW, fun _ => hy⟩
      · exact ⟨x, hx, hxW, fun h => absurd h hρ⟩
    · by_cases hxα : x.1 = α.1
      · obtain ⟨π, π', hπ, hπ', hc⟩ := hx.2.2
        obtain ⟨y, hyD, hyW, hy1, -⟩ := exists_goodCross_near hη hx hπ hπ' hc hW hxW
        exact ⟨y, hyD, hyW, fun h => hy1 (h.trans hxα.symm)⟩
      · exact ⟨x, hx, hxW, hxα⟩
  obtain ⟨z, hz⟩ := (dense_iInter_of_isOpen hopen hdense).nonempty
  rw [Set.mem_iInter] at hz
  refine ⟨z.1, z.2, fun n hn => hz (.inl n) hn, fun ρ hρ => hz (.inr (.inl ρ)) hρ, ?_, ?_⟩
  · intro halg
    exact hz (.inr (.inr ⟨z.1.1, Or.inl halg⟩)) rfl
  · intro hzL
    exact hz (.inr (.inr ⟨z.1.1, Or.inr hzL⟩)) rfl

/-! ### The theorem -/

/-- `Δ_n^{λ,t} ≤ t` for every `n ≥ 1`: the words `1 0^{n-1}` and `0^n`. -/
theorem homGap_le_t (lam t : ℝ) (ht : 0 ≤ t) {n : ℕ} (hn : 1 ≤ n) :
    homGap lam t n ≤ ENNReal.ofReal t := by
  have hl1 : (1 :: List.replicate (n - 1) (0 : Fin 3)).length = n := by simp; omega
  have hl2 : (List.replicate n (0 : Fin 3)).length = n := by simp
  have hne : (1 :: List.replicate (n - 1) (0 : Fin 3)) ≠ List.replicate n 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp [List.replicate_succ]
  unfold homGap
  refine (iInf_le _ (1 :: List.replicate (n - 1) (0 : Fin 3))).trans ?_
  refine (iInf_le _ (List.replicate n (0 : Fin 3))).trans ?_
  refine (iInf_le _ hl1).trans ((iInf_le _ hl2).trans ((iInf_le _ hne).trans ?_))
  rw [homWord_cons, homWord_replicate_zero, homWord_replicate_zero]
  simp [homTrans, abs_of_nonneg ht]

/-- A pair `(λ, t)` with `0 < λ < 1` at which no valid pair of words has equal values generates a
free semigroup: words of different lengths give maps of different slopes. -/
theorem homFree_of_forall_pairDiff_ne {lam t : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (h : ∀ ρ : WordPair, ρ.Valid → pairDiff lam t ρ ≠ 0) : HomFree lam t := by
  intro w w' hww
  by_contra hne
  by_cases hlen : w'.length = w.length
  · apply h (w, w') ⟨hlen, hne⟩
    simp [pairDiff, hww]
  · apply hlen
    have h0 := congrFun hww 0
    have h1 := congrFun hww 1
    rw [homWord_apply lam t w 1, homWord_apply lam t w' 1, h0] at h1
    have : lam ^ w.length = lam ^ w'.length := by linarith
    exact (pow_right_injective₀ hlam0 hlam1.ne this).symm

/-- A corrected form of Theorem 2.1 of Bárány and Käenmäki (arXiv:1910.04623v4), proved: for
every sequence `η` of positive numbers the pairs `(λ, t)` with `0 < λ < 1/3` transcendental and
`0 < t < λ/(1-λ)`, outside the exact overlapping set, with `Δ_n^{λ,t} < η_n` for every `n ≥ 5`,
have uncountably many first coordinates. The source states `Δ_n < η_n` for every `n ≥ 1`, which
fails for some admissible `η` (`not_baranyKaenmakiTheorem`); its proof gives the bound for all
large `n`. -/
theorem not_countable_fst_condensation {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) :
    ¬ (Prod.fst '' {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 1 / 3 ∧ 0 < p.2 ∧ p.2 < p.1 / (1 - p.1) ∧
        Transcendental ℚ p.1 ∧ HomFree p.1 p.2 ∧
        ∀ n : ℕ, 5 ≤ n → homGap p.1 p.2 n < ENNReal.ofReal (η n)}).Countable := by
  intro hc
  obtain ⟨z, hzK, hgap, hfree, htr, hzL⟩ := exists_good_point hη hc
  have hzB : z ∈ Metric.closedBall baseCross (1 / 100) :=
    Metric.closure_ball_subset_closedBall (closure_mono (fun y hy => hy.1) hzK)
  obtain ⟨h1, h2, h3, h4⟩ := mem_region_of_mem_closedBall hzB
  exact hzL ⟨z, ⟨h1, h2, h3, h4, htr, homFree_of_forall_pairDiff_ne h1 (by linarith) hfree,
    hgap⟩, rfl⟩

/-- The set of the corrected form of Theorem 2.1 is uncountable. -/
theorem not_countable_condensation {η : ℕ → ℝ} (hη : ∀ n, 0 < η n) :
    ¬ {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 1 / 3 ∧ 0 < p.2 ∧ p.2 < p.1 / (1 - p.1) ∧
        HomFree p.1 p.2 ∧ ∀ n : ℕ, 5 ≤ n → homGap p.1 p.2 n < ENNReal.ofReal (η n)}.Countable := by
  intro hc
  refine not_countable_fst_condensation hη ((hc.image Prod.fst).mono ?_)
  rintro _ ⟨p, ⟨h1, h2, h3, h4, -, h6, h7⟩, rfl⟩
  exact ⟨p, ⟨h1, h2, h3, h4, h6, h7⟩, rfl⟩

/-- The theorem of Bárány and Käenmäki in the form `BaranyKaenmakiPair`, proved: there are
`0 < λ < 1/3` transcendental, `0 < t < λ/(1-λ)` and `C_0 > 0` such that the homogeneous system
`(λx, λx + t, λx + 1)` generates a free semigroup and `Δ_n^{λ,t} ≤ C_0 exp(-n²)` for every
`n ≥ 1`. Source: B. Bárány and A. Käenmäki, Adv. Math. 379 (2021), arXiv:1910.04623v4,
Theorem 2.1 and the base crossing of Lemma 3.8; the proof is a Baire category argument. -/
theorem baranyKaenmakiPair_holds : BaranyKaenmakiPair := by
  obtain ⟨z, hzK, hgap, hfree, htr, -⟩ :=
    exists_good_point (fun n => Real.exp_pos (-(n : ℝ) ^ 2)) Set.countable_empty
  have hzB : z ∈ Metric.closedBall baseCross (1 / 100) :=
    Metric.closure_ball_subset_closedBall (closure_mono (fun y hy => hy.1) hzK)
  obtain ⟨h1, h2, h3, h4⟩ := mem_region_of_mem_closedBall hzB
  refine ⟨z.1, z.2, Real.exp 25, h1, h2, h3, h4, htr, Real.exp_pos _,
    homFree_of_forall_pairDiff_ne h1 (by linarith) hfree, fun n hn => ?_⟩
  by_cases hn5 : 5 ≤ n
  · refine (hgap n hn5).le.trans (ENNReal.ofReal_le_ofReal ?_)
    have := Real.exp_pos (-(n : ℝ) ^ 2)
    have h25 : 1 ≤ Real.exp 25 := Real.one_le_exp (by norm_num)
    nlinarith
  · refine (homGap_le_t z.1 z.2 h3.le hn).trans (ENNReal.ofReal_le_ofReal ?_)
    have hn' : (n : ℝ) ≤ 4 := by exact_mod_cast (by omega : n ≤ 4)
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    rw [← Real.exp_add]
    have : 0 ≤ 25 + -(n : ℝ) ^ 2 := by nlinarith
    have h1' : 1 ≤ Real.exp (25 + -(n : ℝ) ^ 2) := Real.one_le_exp this
    have : z.2 < 1 := by
      rw [lt_div_iff₀ (by linarith)] at h4
      nlinarith
    linarith

/-! ### Consequences -/

open Matrix in
/-- `prop:ssc_no_overlap_not_pesc` with no literature hypothesis: the article's proof
(`exists_system_of_homFree_of_exceptionalSet`) applied to the pair of
`baranyKaenmakiPair_holds`. -/
theorem prop_ssc_no_overlap_not_pesc_holds :
    ∃ S : System (Fin 4), S.o = ![0, 0, 0, 1] ∧ S.Proximal ∧ S.Irreducible ∧
      ¬ TupleStronglyIrreducible S.mat ∧
      (∀ i (v : Fin 2 → ℝ), v 0 = 0 ∨ v 1 = 0 →
        (S.mat i *ᵥ v) 0 = 0 ∨ (S.mat i *ᵥ v) 1 = 0) ∧
      (∃ i₀, S.o i₀ = 0 ∧ |S.a i₀| ≠ |S.b i₀|) ∧
      S.StrongSeparation ∧ S.FreeProjective ∧ ¬ S.ProjExpSeparation ∧
      ∑ i, |(S.mat i).det| < 1 := by
  obtain ⟨lam, t, C₀, hlam0, hlam1, ht0, ht1, -, hC, hfree, hgap⟩ := baranyKaenmakiPair_holds
  exact exists_system_of_homFree_of_exceptionalSet hlam0 hlam1 ht0 ht1 hfree fun c hc =>
    homGap_lt_of_le_mul_exp hC hgap hc

/-- The paragraph after `prop:ssc_no_overlap_not_pesc` (tex lines 1452 to 1460) with no
literature hypothesis: `planar_separation_not_pesc` applied to `baranyKaenmakiPair_holds`. -/
theorem planar_separation_not_pesc_holds :
    ∃ S : System (Fin 4), S.StrongSeparation ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ w w' : List (Fin 4), w.length = w'.length →
        w ≠ w' → ∀ x ∈ S.attractor, ∀ y ∈ S.attractor,
          δ * S.minSingular ^ (w.length - 1) ≤ dist (S.phiWord w x) (S.phiWord w' y)) ∧
      ¬ S.ProjExpSeparation ∧ ¬ TupleStronglyIrreducible S.mat :=
  planar_separation_not_pesc baranyKaenmakiPair_holds

end NoOverlap

end BoxLike
