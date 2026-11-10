module

/-
`NoOverlap.BaranyKaenmakiTheorem`, Theorem 2.1 of Bárány–Käenmäki, Adv. Math. 379 (2021),
arXiv:1910.04623v4, as stated, is false: for `η_n = (6n + 3)^{-3n} / 15`, no free pair `(λ, t)`
has `Δ_n^{λ,t} < η_n` for every `n ≥ 1`. For words `𝐩, 𝐪` of a common length `k`,
`φ(𝐩, 𝐪) = h_{1𝐩}(0) - h_{0𝐪}(0) = t + λ(U + tV)` with integer polynomials `U, V`; a combination
of two such values has no `t`-term and is a non-zero integer polynomial with coefficients at most
`3k + 1`, hence at least `λ^{deg}/2` in modulus when `λ` is small, which separates the minimal
gaps at lengths `k` and `M` by `λ^{k+M}`.

In the namespace `BoxLike.NoOverlap`:

* `oneZeroDiff`, `le_abs_homWord_sub`, `le_homGap_of_forall`: the difference and the minimal gap.
* `crossPoly`, `oneZeroDiff_cross`, `pow_le_two_mul_abs_aeval`, `separation`: the cross
  polynomial, the lower bound and the separation of two pairs.
* `fastEta`, `antitone_fastEta`, `fastEta_pos`, `tendsto_log_fastEta`: the sequence.
* `false_of_forall_homGap_lt`, `not_baranyKaenmakiTheorem`.
-/
public import BoxLike.BaranyKaenmaki
public import BoxLike.NoOverlapExample
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.Set.Finite.List

@[expose] public section

namespace BoxLike

namespace NoOverlap

open Polynomial Filter

/-! ### Words -/

/-- The difference `φ(𝐩, 𝐪) = h_{1𝐩}(0) - h_{0𝐪}(0)` of the values of two words whose first
letters are `1` and `0`. -/
noncomputable def oneZeroDiff (lam t : ℝ) (p q : List (Fin 3)) : ℝ :=
  homWord lam t (1 :: p) 0 - homWord lam t (0 :: q) 0

/-- `φ(𝐩, 𝐪) = t + λ (h_𝐩(0) - h_𝐪(0))`. -/
theorem oneZeroDiff_eq (lam t : ℝ) (p q : List (Fin 3)) :
    oneZeroDiff lam t p q = t + lam * (homWord lam t p 0 - homWord lam t q 0) := by
  simp [oneZeroDiff, homTrans]
  ring

/-- Appending zeros to both words does not change `φ`. -/
theorem oneZeroDiff_append_replicate (lam t : ℝ) (p q : List (Fin 3)) (k : ℕ) :
    oneZeroDiff lam t (p ++ List.replicate k 0) (q ++ List.replicate k 0) =
      oneZeroDiff lam t p q := by
  simp only [oneZeroDiff_eq, homWord_append_replicate_zero]

/-- A lower bound for `|φ|` at length `N` holds at every length `m ≤ N`. -/
theorem le_abs_oneZeroDiff_of_le {lam t δ : ℝ} {N : ℕ}
    (H : ∀ p q : List (Fin 3), p.length = N → q.length = N → δ ≤ |oneZeroDiff lam t p q|)
    (p q : List (Fin 3)) (hp : p.length ≤ N) (hq : q.length = p.length) :
    δ ≤ |oneZeroDiff lam t p q| := by
  have h := H (p ++ List.replicate (N - p.length) 0) (q ++ List.replicate (N - p.length) 0)
    (by simp; omega) (by simp; omega)
  rwa [oneZeroDiff_append_replicate] at h

/-! ### A lower bound for the minimal gap -/

/-- The common-prefix argument. Let `t ≤ 1/4` and let every `|φ(𝐩, 𝐪)|` with `|𝐩| = |𝐪| ≤ N`
be at least `0 ≤ δ ≤ 1/4`. Then distinct words `𝐰, 𝐰'` of a common length `n ≤ N + 1` satisfy
`|h_𝐰(0) - h_{𝐰'}(0)| ≥ λ^{n-1} δ`: after the common prefix the first letters differ, and a
difference that does not involve the letters `1` and `0` is at least `1/4`. -/
theorem le_abs_homWord_sub {lam t δ : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 3) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1 / 4) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 4) {N : ℕ}
    (H : ∀ p q : List (Fin 3), p.length ≤ N → q.length = p.length →
      δ ≤ |oneZeroDiff lam t p q|) :
    ∀ w w' : List (Fin 3), w'.length = w.length → w.length ≤ N + 1 → w ≠ w' →
      lam ^ (w.length - 1) * δ ≤ |homWord lam t w 0 - homWord lam t w' 0| := by
  intro w
  induction w with
  | nil =>
    intro w' hlen _ hne
    exact absurd (List.length_eq_zero_iff.1 hlen).symm hne
  | cons i w ih =>
    intro w' hlen hle hne
    obtain _ | ⟨i', w'⟩ := w'
    · simp at hlen
    simp only [List.length_cons, add_tsub_cancel_right] at hlen hle ⊢
    have hlen' : w'.length = w.length := by omega
    have hpow : lam ^ w.length * δ ≤ δ :=
      mul_le_of_le_one_left hδ0 (pow_le_one₀ hlam0.le (by linarith))
    have bw := homWord_zero_mem_Icc hlam0.le hlam1.le ht0 (by linarith) w
    have bw' := homWord_zero_mem_Icc hlam0.le hlam1.le ht0 (by linarith) w'
    have hd1 : -(1 / 2) ≤ lam * (homWord lam t w 0 - homWord lam t w' 0) := by nlinarith
    have hd2 : lam * (homWord lam t w 0 - homWord lam t w' 0) ≤ 1 / 2 := by nlinarith
    by_cases hii : i = i'
    · subst hii
      have hne' : w ≠ w' := fun h => hne (h ▸ rfl)
      have hw0 : w.length ≠ 0 := by
        intro h0
        exact hne' ((List.length_eq_zero_iff.1 h0).trans
          (List.length_eq_zero_iff.1 (hlen'.trans h0)).symm)
      have := ih w' hlen' (by omega) hne'
      rw [homWord_cons, homWord_cons, add_sub_add_right_eq_sub, ← mul_sub, abs_mul,
        abs_of_pos hlam0]
      calc lam ^ w.length * δ = lam * (lam ^ (w.length - 1) * δ) := by
            rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hw0)]
        _ ≤ lam * |homWord lam t w 0 - homWord lam t w' 0| :=
            mul_le_mul_of_nonneg_left this hlam0.le
    · refine hpow.trans ?_
      have h10 : δ ≤ |oneZeroDiff lam t w w'| := H w w' (by omega) hlen'
      have h01 : δ ≤ |oneZeroDiff lam t w' w| := H w' w (by omega) hlen'.symm
      rw [oneZeroDiff_eq] at h10 h01
      rw [homWord_cons, homWord_cons]
      fin_cases i <;> fin_cases i' <;> simp [homTrans] at hii ⊢
      · rw [abs_sub_comm]; convert h01 using 2; ring
      · exact hδ1.trans (le_abs.2 (Or.inr (by linarith)))
      · convert h10 using 2; ring
      · exact hδ1.trans (le_abs.2 (Or.inr (by linarith)))
      · exact hδ1.trans (le_abs.2 (Or.inl (by linarith)))
      · exact hδ1.trans (le_abs.2 (Or.inl (by linarith)))

/-- A pointwise lower bound for the distances of distinct words of length `n` bounds `Δ_n` from
below. -/
theorem le_homGap_of_forall {lam t c : ℝ} {n : ℕ}
    (h : ∀ w w' : List (Fin 3), w.length = n → w'.length = n → w ≠ w' →
      c ≤ |homWord lam t w 0 - homWord lam t w' 0|) :
    ENNReal.ofReal c ≤ homGap lam t n := by
  unfold homGap
  exact le_iInf fun w => le_iInf fun w' => le_iInf fun hw => le_iInf fun hw' =>
    le_iInf fun hne => ENNReal.ofReal_le_ofReal (h w w' hw hw' hne)

/-! ### The cross polynomial -/

/-- A coefficient of `A B` is at most `k` in modulus when the coefficients of `A` and `B` are
digits and those of `A` vanish from degree `k` on. -/
theorem abs_coeff_mul_le {A B : ℤ[X]} {k : ℕ} (hA : ∀ j, |A.coeff j| ≤ 1)
    (hA0 : ∀ j, k ≤ j → A.coeff j = 0) (hB : ∀ j, |B.coeff j| ≤ 1) (i : ℕ) :
    |(A * B).coeff i| ≤ k := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc |∑ a ∈ Finset.range i.succ, A.coeff a * B.coeff (i - a)|
      ≤ ∑ a ∈ Finset.range i.succ, |A.coeff a * B.coeff (i - a)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.range i.succ, (if a < k then (1 : ℤ) else 0) := by
        refine Finset.sum_le_sum fun a _ => ?_
        split_ifs with ha
        · rw [abs_mul]
          calc |A.coeff a| * |B.coeff (i - a)| ≤ 1 * 1 :=
                mul_le_mul (hA a) (hB _) (abs_nonneg _) zero_le_one
            _ = 1 := one_mul 1
        · simp [hA0 a (not_lt.1 ha)]
    _ = ((Finset.range i.succ).filter (· < k)).card := by
        rw [Finset.sum_boole]
    _ ≤ k := by
        have : (Finset.range i.succ).filter (· < k) ⊆ Finset.range k := by
          intro a ha
          simp only [Finset.mem_filter] at ha
          exact Finset.mem_range.2 ha.2
        exact_mod_cast (Finset.card_le_card this).trans (Finset.card_range k).le

/-- The cross polynomial `N = U - U' + X(UV' - U'V)` of two pairs of words, with
`U = polyD difU 𝐩 𝐪`, `V = polyD difV 𝐩 𝐪` and `U'`, `V'` those of `(𝐩', 𝐪')`. -/
noncomputable def crossPoly (p q p' q' : List (Fin 3)) : ℤ[X] :=
  polyD difU p q - polyD difU p' q' +
    X * (polyD difU p q * polyD difV p' q' - polyD difU p' q' * polyD difV p q)

/-- The identity without `t`:
`φ(𝐩, 𝐪)(1 + λV'(λ)) - φ(𝐩', 𝐪')(1 + λV(λ)) = λ N(λ)`. -/
theorem oneZeroDiff_cross (lam t : ℝ) {p q p' q' : List (Fin 3)} (hq : q.length = p.length)
    (hq' : q'.length = p'.length) :
    oneZeroDiff lam t p q * (1 + lam * aeval lam (polyD difV p' q')) -
        oneZeroDiff lam t p' q' * (1 + lam * aeval lam (polyD difV p q)) =
      lam * aeval lam (crossPoly p q p' q') := by
  rw [oneZeroDiff_eq, oneZeroDiff_eq, homWord_sub_eq lam t p q hq,
    homWord_sub_eq lam t p' q' hq']
  simp only [crossPoly, map_add, map_sub, map_mul, aeval_X]
  ring

/-- The coefficient bound for `U - U' + X(UV' - U'V)` when all coefficients are digits and those
of `U` and `V` vanish from degree `k` on. -/
theorem abs_coeff_cross_le {U V U' V' : ℤ[X]} {k : ℕ} (hU : ∀ j, |U.coeff j| ≤ 1)
    (hU0 : ∀ j, k ≤ j → U.coeff j = 0) (hV : ∀ j, |V.coeff j| ≤ 1)
    (hV0 : ∀ j, k ≤ j → V.coeff j = 0) (hU' : ∀ j, |U'.coeff j| ≤ 1)
    (hV' : ∀ j, |V'.coeff j| ≤ 1) (j : ℕ) :
    |(U - U' + X * (U * V' - U' * V)).coeff j| ≤ 3 * (k : ℤ) + 1 := by
  have hUk : |U.coeff j| ≤ (k : ℤ) := by
    by_cases hj : k ≤ j
    · simp [hU0 j hj]
    · exact (hU j).trans (by exact_mod_cast (by omega : 1 ≤ k))
  have hX : |(X * (U * V' - U' * V)).coeff j| ≤ 2 * (k : ℤ) := by
    obtain _ | i := j
    · rw [coeff_X_mul_zero, abs_zero]; positivity
    rw [coeff_X_mul, coeff_sub]
    have h1 := abs_coeff_mul_le hU hU0 hV' i
    have h2 := abs_coeff_mul_le hV hV0 hU' i
    rw [mul_comm V] at h2
    calc _ ≤ |(U * V').coeff i| + |(U' * V).coeff i| := abs_sub _ _
      _ ≤ _ := by linarith
  rw [coeff_add, coeff_sub]
  have h3 := abs_add_le (U.coeff j - U'.coeff j) ((X * (U * V' - U' * V)).coeff j)
  have h4 := abs_sub (U.coeff j) (U'.coeff j)
  have h5 := hU' j
  linarith

/-- The coefficients of the cross polynomial are at most `3|𝐩| + 1` in modulus. -/
theorem abs_coeff_crossPoly_le (p q p' q' : List (Fin 3)) (j : ℕ) :
    |(crossPoly p q p' q').coeff j| ≤ 3 * (p.length : ℤ) + 1 :=
  abs_coeff_cross_le (abs_coeff_polyD_le abs_difU_le p q) (coeff_polyD_eq_zero difU p q)
    (abs_coeff_polyD_le abs_difV_le p q) (coeff_polyD_eq_zero difV p q)
    (abs_coeff_polyD_le abs_difU_le p' q') (abs_coeff_polyD_le abs_difV_le p' q') j

/-- The cross polynomial has no coefficient of degree at least `|𝐩| + |𝐩'|`. -/
theorem coeff_crossPoly_eq_zero (p q p' q' : List (Fin 3)) (j : ℕ)
    (hj : p.length + p'.length ≤ j) : (crossPoly p q p' q').coeff j = 0 := by
  have hU0 := coeff_polyD_eq_zero difU
  have hV0 := coeff_polyD_eq_zero difV
  simp only [crossPoly, coeff_add, coeff_sub]
  rw [hU0 p q j (by omega), hU0 p' q' j (by omega)]
  obtain _ | i := j
  · simp
  rw [coeff_X_mul, coeff_sub, coeff_mul, coeff_mul]
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
  · simp
  · intro x hx
    rw [Finset.mem_antidiagonal] at hx
    by_cases h : p.length ≤ x.2
    · simp [hV0 p q x.2 h]
    · simp [hU0 p' q' x.1 (by omega)]
  · intro x hx
    rw [Finset.mem_antidiagonal] at hx
    by_cases h : p.length ≤ x.1
    · simp [hU0 p q x.1 h]
    · simp [hV0 p' q' x.2 (by omega)]

/-! ### A lower bound for the values of integer polynomials -/

/-- A non-zero value of an integer polynomial with coefficients bounded by `C`, all of degree
less than `D`, at a point `0 < λ < 1` with `Cλ ≤ (1 - λ)/2` is at least `λ^{D-1}/2`, in the
form `λ^D ≤ 2λ|N(λ)|`: the lowest non-zero coefficient dominates. -/
theorem pow_le_two_mul_abs_aeval {N : ℤ[X]} {lam C : ℝ} {D : ℕ} (hlam0 : 0 < lam)
    (hlam1 : lam < 1) (hC : C * lam ≤ (1 - lam) / 2) (hcoeff : ∀ j, |(N.coeff j : ℝ)| ≤ C)
    (hD : ∀ j, D ≤ j → N.coeff j = 0) (hN : aeval lam N ≠ 0) :
    lam ^ D ≤ 2 * lam * |aeval lam N| := by
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  have hex : ∃ j, N.coeff j ≠ 0 := by
    by_contra h
    push Not at h
    exact hN0 (Polynomial.ext fun j => by simp [h j])
  classical
  set j0 := Nat.find hex with hj0def
  have hj0 : N.coeff j0 ≠ 0 := Nat.find_spec hex
  have hlt : ∀ j < j0, N.coeff j = 0 := fun j hj => by
    by_contra h
    exact Nat.find_min hex hj h
  have hj0D : j0 < D := by
    by_contra h
    exact hj0 (hD j0 (not_lt.1 h))
  have hdeg : N.natDegree < D := by
    by_contra h
    push Not at h
    have := hD _ h
    rw [coeff_natDegree, leadingCoeff_eq_zero] at this
    exact hN0 this
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hcoeff 0)
  rw [aeval_eq_sum_range' hdeg]
  simp only [zsmul_eq_mul]
  rw [← Finset.sum_range_add_sum_Ico _ hj0D.le, Finset.sum_eq_sum_Ico_succ_bot hj0D]
  rw [Finset.sum_eq_zero (fun j hj => by simp [hlt j (Finset.mem_range.1 hj)]), zero_add]
  set T := ∑ x ∈ Finset.Ico (j0 + 1) D, (N.coeff x : ℝ) * lam ^ x
  have hT : |T| ≤ C * (lam ^ (j0 + 1) / (1 - lam)) := by
    calc |T| ≤ ∑ x ∈ Finset.Ico (j0 + 1) D, |(N.coeff x : ℝ) * lam ^ x| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ Finset.Ico (j0 + 1) D, C * lam ^ x := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [abs_mul, abs_of_pos (pow_pos hlam0 x)]
          exact mul_le_mul_of_nonneg_right (hcoeff x) (pow_pos hlam0 x).le
      _ = C * ∑ x ∈ Finset.Ico (j0 + 1) D, lam ^ x := by rw [Finset.mul_sum]
      _ ≤ C * (lam ^ (j0 + 1) / (1 - lam)) :=
          mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hlam0.le hlam1) hC0
  have hc1 : (1 : ℝ) ≤ |(N.coeff j0 : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hj0
  have hpow : 0 < lam ^ j0 := pow_pos hlam0 j0
  have h1l : 0 < 1 - lam := by linarith
  have hT' : |T| ≤ lam ^ j0 / 2 := by
    refine hT.trans ?_
    rw [pow_succ, mul_div_assoc', div_le_iff₀ h1l]
    calc C * (lam ^ j0 * lam) = lam ^ j0 * (C * lam) := by ring
      _ ≤ lam ^ j0 * ((1 - lam) / 2) := mul_le_mul_of_nonneg_left hC hpow.le
      _ = lam ^ j0 / 2 * (1 - lam) := by ring
  have hmain : lam ^ j0 / 2 ≤ |(N.coeff j0 : ℝ) * lam ^ j0 + T| := by
    have h2 : lam ^ j0 ≤ |(N.coeff j0 : ℝ) * lam ^ j0| := by
      rw [abs_mul, abs_of_pos hpow]
      nlinarith
    have h3 := abs_add_le (((N.coeff j0 : ℝ) * lam ^ j0) + T) (-T)
    rw [add_neg_cancel_right, abs_neg] at h3
    linarith
  calc lam ^ D ≤ lam ^ (j0 + 1) := pow_le_pow_of_le_one hlam0.le hlam1.le hj0D
    _ = 2 * lam * (lam ^ j0 / 2) := by ring
    _ ≤ 2 * lam * |(N.coeff j0 : ℝ) * lam ^ j0 + T| :=
        mul_le_mul_of_nonneg_left hmain (by positivity)

/-! ### Separation -/

/-- The separation of two pairs. Let `(3k + 1)λ ≤ (1 - λ)/2`, let `|𝐩| = |𝐪| = k` and
`|𝐩'| = |𝐪'| = M`, and let `|φ(𝐩', 𝐪')| < ε/4` with `ε = |φ(𝐩, 𝐪)|`. Then
`ε ≥ (4/15) λ^{k + M}`. -/
theorem separation {lam t : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 3) {k M : ℕ}
    (hk : (3 * k + 1 : ℝ) * lam ≤ (1 - lam) / 2) {p q p' q' : List (Fin 3)}
    (hp : p.length = k) (hq : q.length = k) (hp' : p'.length = M) (hq' : q'.length = M)
    {ε : ℝ} (hε : |oneZeroDiff lam t p q| = ε) (hε' : |oneZeroDiff lam t p' q'| < ε / 4) :
    4 / 15 * lam ^ (k + M) ≤ ε := by
  set V := aeval lam (polyD difV p q)
  set V' := aeval lam (polyD difV p' q')
  have hV := abs_aeval_polyD_le abs_difV_le hlam0.le hlam1.le p q
  have hV' := abs_aeval_polyD_le abs_difV_le hlam0.le hlam1.le p' q'
  rw [abs_le] at hV hV'
  have hb1 : 1 / 2 ≤ 1 + lam * V := by nlinarith
  have hb2 : 1 + lam * V ≤ 3 / 2 := by nlinarith
  have hb1' : 1 / 2 ≤ 1 + lam * V' := by nlinarith
  have hb2' : 1 + lam * V' ≤ 3 / 2 := by nlinarith
  have hcross := oneZeroDiff_cross lam t (hq.trans hp.symm) (hq'.trans hp'.symm)
  set φ := oneZeroDiff lam t p q
  set φ' := oneZeroDiff lam t p' q'
  have hε0 : 0 < ε := by linarith [abs_nonneg φ']
  have hΨ1 : |φ * (1 + lam * V') - φ' * (1 + lam * V)| ≤ 15 / 8 * ε := by
    calc _ ≤ |φ * (1 + lam * V')| + |φ' * (1 + lam * V)| := abs_sub _ _
      _ = ε * (1 + lam * V') + |φ'| * (1 + lam * V) := by
          rw [abs_mul, abs_mul, hε, abs_of_pos (by linarith : 0 < 1 + lam * V'),
            abs_of_pos (by linarith : 0 < 1 + lam * V)]
      _ ≤ ε * (3 / 2) + ε / 4 * (3 / 2) := by
          gcongr
      _ = 15 / 8 * ε := by ring
  have hΨ2 : ε / 8 ≤ |φ * (1 + lam * V') - φ' * (1 + lam * V)| := by
    have h1 : ε / 2 ≤ |φ * (1 + lam * V')| := by
      rw [abs_mul, hε, abs_of_pos (by linarith : 0 < 1 + lam * V')]
      nlinarith
    have h2 : |φ' * (1 + lam * V)| ≤ ε / 4 * (3 / 2) := by
      rw [abs_mul, abs_of_pos (by linarith : 0 < 1 + lam * V)]
      gcongr
    have h3 := abs_sub_abs_le_abs_sub (φ * (1 + lam * V')) (φ' * (1 + lam * V))
    linarith
  rw [hcross] at hΨ1 hΨ2
  rw [abs_mul, abs_of_pos hlam0] at hΨ1 hΨ2
  have hN : aeval lam (crossPoly p q p' q') ≠ 0 := by
    intro h
    rw [h, abs_zero, mul_zero] at hΨ2
    linarith
  have hcoeff : ∀ j, |((crossPoly p q p' q').coeff j : ℝ)| ≤ (3 * k + 1 : ℝ) := by
    intro j
    have := abs_coeff_crossPoly_le p q p' q' j
    rw [hp] at this
    rw [← Int.cast_abs]
    exact_mod_cast this
  have hlow := pow_le_two_mul_abs_aeval hlam0 (by linarith) hk hcoeff
    (fun j hj => coeff_crossPoly_eq_zero p q p' q' j hj) hN
  rw [hp, hp'] at hlow
  linarith

/-! ### The minimal gap from a lower bound for `φ` -/

/-- If `t ≤ 1/4`, `0 ≤ δ ≤ 1/4`, `n ≥ 1` and every `|φ(𝐩, 𝐪)|` with `|𝐩| = |𝐪| ≤ n - 1` is at
least `δ`, then `Δ_n ≥ λ^{n-1} δ`. -/
theorem le_homGap_of_le_abs_oneZeroDiff {lam t δ : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 3)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 4) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 4) {n : ℕ} (hn : 1 ≤ n)
    (H : ∀ p q : List (Fin 3), p.length ≤ n - 1 → q.length = p.length →
      δ ≤ |oneZeroDiff lam t p q|) :
    ENNReal.ofReal (lam ^ (n - 1) * δ) ≤ homGap lam t n := by
  refine le_homGap_of_forall fun w w' hw hw' hne => ?_
  have := le_abs_homWord_sub hlam0 hlam1 ht0 ht1 hδ0 hδ1 H w w' (hw'.trans hw.symm)
    (by omega) hne
  rwa [hw] at this

/-- `t ≤ Δ_1` for `t ≤ 1/2`: the values of the words of length one are `0`, `t` and `1`. -/
theorem le_homGap_one {lam t : ℝ} (ht1 : t ≤ 1 / 2) :
    ENNReal.ofReal t ≤ homGap lam t 1 := by
  refine le_homGap_of_forall fun w w' hw hw' hne => ?_
  obtain ⟨i, rfl⟩ := List.length_eq_one_iff.1 hw
  obtain ⟨j, rfl⟩ := List.length_eq_one_iff.1 hw'
  have hij : i ≠ j := fun h => hne (h ▸ rfl)
  simp only [homWord_cons, homWord_nil, id_eq, mul_zero, zero_add]
  fin_cases i <;> fin_cases j <;> simp [homTrans] at hij ⊢ <;>
    first
    | linarith
    | (rw [le_abs]; left; linarith)
    | (rw [le_abs]; right; linarith)

/-! ### The sequence -/

/-- The sequence `η_n = (6n + 3)^{-3n} / 15`. -/
noncomputable def fastEta (n : ℕ) : ℝ := ((6 * (n : ℝ) + 3)⁻¹) ^ (3 * n) / 15

/-- `η_n > 0`. -/
theorem fastEta_pos (n : ℕ) : 0 < fastEta n := by
  unfold fastEta; positivity

/-- `η` is monotone decreasing. -/
theorem antitone_fastEta : Antitone fastEta := by
  intro m n hmn
  unfold fastEta
  have hm : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
  have hx0 : 0 ≤ (6 * (n : ℝ) + 3)⁻¹ := by positivity
  have hxy : (6 * (n : ℝ) + 3)⁻¹ ≤ (6 * (m : ℝ) + 3)⁻¹ :=
    inv_anti₀ (by positivity) (by linarith)
  have hy1 : (6 * (m : ℝ) + 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [m.cast_nonneg (α := ℝ)])
  gcongr ?_ / 15
  calc ((6 * (n : ℝ) + 3)⁻¹) ^ (3 * n) ≤ ((6 * (m : ℝ) + 3)⁻¹) ^ (3 * n) :=
        pow_le_pow_left₀ hx0 hxy _
    _ ≤ ((6 * (m : ℝ) + 3)⁻¹) ^ (3 * m) :=
        pow_le_pow_of_le_one (hx0.trans hxy) hy1 (by omega)

/-- `n⁻¹ log η_n → -∞`. -/
theorem tendsto_log_fastEta :
    Tendsto (fun n : ℕ => Real.log (fastEta n) / n) atTop atBot := by
  have h6 : Tendsto (fun n : ℕ => 6 * (n : ℝ) + 3) atTop atTop :=
    tendsto_atTop_add_const_right _ 3
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have hg : Tendsto (fun n : ℕ => -(3 * Real.log (6 * (n : ℝ) + 3))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp
      ((Real.tendsto_log_atTop.comp h6).const_mul_atTop (by norm_num))
  refine tendsto_atBot_mono' atTop ?_ hg
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < 6 * n + 3 := by linarith
  have hlog15 : 0 ≤ Real.log 15 := Real.log_nonneg (by norm_num)
  simp only [fastEta]
  rw [Real.log_div (by positivity) (by norm_num), Real.log_pow, Real.log_inv,
    div_le_iff₀ hn0]
  push_cast
  nlinarith

/-! ### The counterexample -/

/-- No pair `(λ, t)` with `0 < λ < 1/3` and `0 < t < λ/(1-λ)` whose homogeneous system generates
a free semigroup satisfies `Δ_n^{λ,t} < η_n` for every `n ≥ 1`, where
`η_n = (6n + 3)^{-3n} / 15`. -/
theorem false_of_forall_homGap_lt {lam t : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 3)
    (ht0 : 0 < t) (ht1 : t < lam / (1 - lam)) (hfree : HomFree lam t)
    (hgap : ∀ n : ℕ, 1 ≤ n → homGap lam t n < ENNReal.ofReal (fastEta n)) : False := by
  -- `t < η_1 < 1/4`
  have ht12 : t ≤ 1 / 2 := by
    rw [lt_div_iff₀ (by linarith)] at ht1
    nlinarith
  have ht14 : t ≤ 1 / 4 := by
    have h1 := (le_homGap_one (lam := lam) ht12).trans_lt (hgap 1 le_rfl)
    rw [ENNReal.ofReal_lt_ofReal_iff (fastEta_pos 1)] at h1
    have : fastEta 1 ≤ 1 / 4 := by norm_num [fastEta]
    linarith
  -- the length `k`
  set k := ⌊(1 - 3 * lam) / (6 * lam)⌋₊ with hkdef
  have hk1 : (k : ℝ) ≤ (1 - 3 * lam) / (6 * lam) := Nat.floor_le (by
    apply div_nonneg <;> linarith)
  have hk2 : (1 - 3 * lam) / (6 * lam) < k + 1 := Nat.lt_floor_add_one _
  rw [le_div_iff₀ (by linarith)] at hk1
  rw [div_lt_iff₀ (by linarith)] at hk2
  have hksep : (3 * k + 1 : ℝ) * lam ≤ (1 - lam) / 2 := by nlinarith
  have hklam : 1 < lam * (6 * k + 9) := by nlinarith
  -- the pair minimising `|φ|` at length `k`
  set S : Set (List (Fin 3) × List (Fin 3)) := {x | x.1.length = k ∧ x.2.length = k}
  have hfin : S.Finite := (List.finite_length_eq (Fin 3) k).prod (List.finite_length_eq (Fin 3) k)
  have hne : S.Nonempty := ⟨(List.replicate k 0, List.replicate k 0), by simp [S]⟩
  obtain ⟨⟨p₀, q₀⟩, ⟨hp₀, hq₀⟩, hmin⟩ :=
    Set.exists_min_image S (fun x => |oneZeroDiff lam t x.1 x.2|) hfin hne
  set ε := |oneZeroDiff lam t p₀ q₀| with hεdef
  have hε0 : 0 < ε := by
    refine abs_pos.2 fun h => ?_
    rw [oneZeroDiff, sub_eq_zero] at h
    have := hfree.eq_of_length_eq (by simp [hp₀, hq₀]) h
    exact absurd (List.cons.inj this).1 (by decide)
  have hεt : ε ≤ t := by
    have := hmin (List.replicate k 0, List.replicate k 0) ⟨by simp, by simp⟩
    simp only [oneZeroDiff_eq, homWord_replicate_zero, sub_self, mul_zero, add_zero,
      abs_of_pos ht0] at this
    exact this
  have hεall : ∀ p q : List (Fin 3), p.length ≤ k → q.length = p.length →
      ε ≤ |oneZeroDiff lam t p q| :=
    le_abs_oneZeroDiff_of_le (fun p q hp hq => hmin (p, q) ⟨hp, hq⟩)
  -- a pair with `|φ| < ε/4` exists
  have hex : ∃ m, ∃ p q : List (Fin 3), p.length = m ∧ q.length = m ∧
      |oneZeroDiff lam t p q| < ε / 4 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨N₁, hN₁⟩ := exists_pow_lt_of_lt_one (by linarith : (0 : ℝ) < ε / 4)
      (by norm_num : (1 / 2 : ℝ) < 1)
    obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 / lam)
    set n := max (max N₁ N₂) 1 with hndef
    have hn1 : 1 ≤ n := le_max_right _ _
    have hnN₁ : N₁ ≤ n := (le_max_left _ _).trans (le_max_left _ _)
    have hnN₂ : N₂ ≤ n := (le_max_right _ _).trans (le_max_left _ _)
    have hlow := le_homGap_of_le_abs_oneZeroDiff hlam0 hlam1 ht0.le ht14 (by linarith)
      (by linarith) hn1 (fun p q _ hq => hcon p.length p q rfl hq)
    have hx : (6 * (n : ℝ) + 3)⁻¹ ≤ lam / 2 := by
      have h2 : 2 / lam < 6 * (n : ℝ) + 3 := by
        have : (N₂ : ℝ) ≤ n := Nat.cast_le.2 hnN₂
        linarith
      rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]
      exact h2.le
    have hη : fastEta n ≤ lam ^ (n - 1) * (ε / 4) := by
      have hx0 : 0 ≤ (6 * (n : ℝ) + 3)⁻¹ := by positivity
      have hx1 : (6 * (n : ℝ) + 3)⁻¹ ≤ 1 := by linarith
      calc fastEta n ≤ ((6 * (n : ℝ) + 3)⁻¹) ^ (3 * n) := by
            unfold fastEta; linarith [pow_nonneg hx0 (3 * n)]
        _ ≤ ((6 * (n : ℝ) + 3)⁻¹) ^ n := pow_le_pow_of_le_one hx0 hx1 (by omega)
        _ ≤ (lam / 2) ^ n := pow_le_pow_left₀ hx0 hx _
        _ = lam ^ n * (1 / 2) ^ n := by rw [div_pow, one_div_pow]; ring
        _ ≤ lam ^ (n - 1) * (ε / 4) := by
            apply mul_le_mul (pow_le_pow_of_le_one hlam0.le (by linarith) (by omega))
              (((pow_le_pow_of_le_one (by norm_num) (by norm_num) hnN₁)).trans hN₁.le)
              (by positivity) (by positivity)
    exact absurd ((hgap n hn1).trans_le ((ENNReal.ofReal_le_ofReal hη).trans hlow)) (lt_irrefl _)
  -- the least length `M` of such a pair
  classical
  set M := Nat.find hex with hMdef
  obtain ⟨p', q', hp', hq', hsmall⟩ := Nat.find_spec hex
  have hminM : ∀ m < M, ∀ p q : List (Fin 3), p.length = m → q.length = m →
      ε / 4 ≤ |oneZeroDiff lam t p q| := by
    intro m hm p q hp hq
    by_contra h
    exact Nat.find_min hex hm ⟨p, q, hp, hq, not_le.1 h⟩
  have hkM : k < M := by
    by_contra h
    have := hεall p' q' (by rw [hp']; omega) (by rw [hp', hq'])
    linarith
  -- separation
  have hsep : 4 / 15 * lam ^ (k + M) ≤ ε :=
    separation hlam0 hlam1 hksep hp₀ hq₀ hp' hq' rfl hsmall
  -- the gap at length `M`
  have hlowM := le_homGap_of_le_abs_oneZeroDiff hlam0 hlam1 ht0.le ht14 (by linarith)
    (by linarith) (by omega : 1 ≤ M)
    (fun p q hp hq => hminM p.length (by omega) p q rfl hq)
  have hηM : fastEta M ≤ lam ^ (M - 1) * (ε / 4) := by
    have hM : (k : ℝ) + 1 ≤ M := by exact_mod_cast hkM
    have hxlam : (6 * (M : ℝ) + 3)⁻¹ ≤ lam := by
      rw [inv_le_comm₀ (by positivity) hlam0]
      calc lam⁻¹ = lam⁻¹ * 1 := (mul_one _).symm
        _ ≤ lam⁻¹ * (lam * (6 * k + 9)) :=
            mul_le_mul_of_nonneg_left hklam.le (inv_pos.2 hlam0).le
        _ = 6 * k + 9 := by field_simp
        _ ≤ 6 * M + 3 := by linarith
    have hx0 : 0 ≤ (6 * (M : ℝ) + 3)⁻¹ := by positivity
    calc fastEta M ≤ lam ^ (3 * M) / 15 := by
          unfold fastEta
          gcongr
      _ ≤ lam ^ (M - 1 + (k + M)) / 15 := by
          gcongr ?_ / 15
          exact pow_le_pow_of_le_one hlam0.le (by linarith) (by omega)
      _ = lam ^ (M - 1) * (lam ^ (k + M) / 15) := by rw [pow_add]; ring
      _ ≤ lam ^ (M - 1) * (ε / 4) :=
          mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hlam0.le _)
  exact absurd ((hgap M (by omega)).trans_le ((ENNReal.ofReal_le_ofReal hηM).trans hlowM))
    (lt_irrefl _)

/-- The transcription of Theorem 2.1 of Bárány and Käenmäki (arXiv:1910.04623v4) is false: for
`η_n = (6n + 3)^{-3n} / 15` the set `𝒞_η ∖ ℰ` is empty. -/
theorem not_baranyKaenmakiTheorem : ¬ BaranyKaenmakiTheorem := by
  intro h
  refine h fastEta antitone_fastEta fastEta_pos tendsto_log_fastEta
    (Set.countable_empty.mono fun p hp => ?_)
  obtain ⟨h0, h1, h2, h3, hfree, hgap⟩ := hp
  exact (false_of_forall_homGap_lt h0 h1 h2 h3 hfree hgap).elim

end NoOverlap

end BoxLike
