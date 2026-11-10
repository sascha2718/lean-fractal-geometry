module

/-
The `δ`-stoppings in the proof of `thm:fraser` (tex lines 398 to 473), after Fraser, "On the
packing dimension of box-like self-affine sets in the plane", §5, numbering of
arXiv:1108.2639v1: the stopping `I_δ = {𝐢 : α_2(𝐢) < δ ≤ α_2(𝐢^-)}`, where `𝐢^-` drops the
last letter, and Fraser's Lemma 5.1 (2), the lower bound `∑_{𝐢 ∈ I_δ} ψ^t(𝐢) ≥ L(t) > 0` for
`0 ≤ t < dimmaff(X)`, uniform in `δ ∈ (0, 1]`.

The sum of `f` over `I_δ` is `fraserStopSum δ f k []`, which explores the tree of words to the
depth `k`; once `r^k < δ`, with `r` a bound for all `|a_i|, |b_i|`, every word of length `k`
has `α_2 < δ` and the sum runs over all of `I_δ`. Two tree inequalities take the place of the
combinatorics of prefix codes: a function with `F(𝐢) ≤ ∑_j F(𝐢j)` below `δ` is at most its
stopped sum (`le_fraserStopSum`), and a non-negative function with `∑_j g(𝐢j) ≤ g(𝐢)` is at
least its stopped sum (`fraserStopSum_le`).

Fraser's Lemma 5.1 (2) has two cases. For `t ≤ s_1 + s_2` the function `ψ^t` is
sub-multiplicative, and `∑_{|𝐢| = n} ψ^t(𝐢) ≤ ∑_{𝐢 ∈ I_δ} ψ^t(𝐢) Ψ_{n - |𝐢|}^t` for large `n`;
if the stopped sum were at most `1`, the sums `Ψ_n^t` would be bounded and the modified pressure
at `t` would be non-positive, so `t ≥ dimmaff(X)`. For `t ≥ s_1 + s_2` Fraser uses blocks of `k`
letters with `Ψ_k^t ≥ 1`; here the same idea enters through the function
`F(𝐢) = ∑_{m < k} ∑_{|𝐣| = m} ψ^t(𝐢𝐣)`, which satisfies `F(𝐢) ≤ ∑_j F(𝐢j)` by
super-multiplicativity and is comparable with `ψ^t`, since `ψ^t(𝐢𝐣) ≤ ψ^t(𝐢)` for
`t ≥ s_1 + s_2`.

* `System.fraserStopSum`, `System.fraserStopSum_mono`, `System.fraserStopSum_const_mul`,
  `System.fraserStopSum_sum`: the sum over `I_δ` and its order and linearity.
* `System.le_fraserStopSum`, `System.fraserStopSum_le`: the two tree inequalities.
* `System.Bounds.fraserStop_length_lt`: a word `𝐢` with `α_2(𝐢) ≥ δ > r^k` has fewer than `k`
  letters.
* `System.fraserTail`, `System.fraserTail_succ`, `System.fraserTail_nil`: the sums
  `∑_{|𝐣| = m} ψ^t(𝐢𝐣)`.
* `System.fraserModSvf_append_le`: `ψ^t(𝐢𝐣) ≤ ψ^t(𝐢)` for `t ≥ s_1 + s_2`.
* `System.fraserTail_le_fraserStopSum`: the renewal inequality of the sub-multiplicative case.
* `System.one_lt_fraserStopSum_of_le`, `System.exists_le_fraserStopSum_of_ge`: the two cases of
  Fraser's Lemma 5.1 (2).
* `System.exists_le_fraserStopSum`: Fraser's Lemma 5.1 (2).
-/
public import BoxLike.FalconerBound

@[expose] public section

namespace BoxLike

open Filter Topology

namespace System

variable {ι : Type*} (S : System ι)

/-! ### The sum over a `δ`-stopping -/

section StopSum

variable [Fintype ι]

/-- The sum of `f` over the words below `u` of Fraser's `δ`-stopping
`I_δ = {𝐢 : α_2(𝐢) < δ ≤ α_2(𝐢^-)}` (proof of his Theorem 2.3, cited as `thm:fraser`, tex
lines 422 to 436), explored to the depth `k`: a child `uj` with `α_2(uj) < δ` contributes
`f(uj)`, and the sum continues below every other child. -/
noncomputable def fraserStopSum (δ : ℝ) (f : List ι → ℝ) : ℕ → List ι → ℝ
  | 0, _ => 0
  | k + 1, u => ∑ j, if S.alpha₂ (u ++ [j]) < δ then f (u ++ [j])
      else fraserStopSum δ f k (u ++ [j])

/-- The stopped sum of depth `0` is empty (lower bound of `thm:fraser`). -/
@[simp] theorem fraserStopSum_zero (δ : ℝ) (f : List ι → ℝ) (u : List ι) :
    S.fraserStopSum δ f 0 u = 0 := rfl

/-- One step of the stopped sum (lower bound of `thm:fraser`). -/
theorem fraserStopSum_succ (δ : ℝ) (f : List ι → ℝ) (k : ℕ) (u : List ι) :
    S.fraserStopSum δ f (k + 1) u = ∑ j, if S.alpha₂ (u ++ [j]) < δ then f (u ++ [j])
      else S.fraserStopSum δ f k (u ++ [j]) := rfl

variable {S}

/-- The stopped sum is monotone in the function, which is compared on the words `uj` of the
stopping only: `α_2(u) ≥ δ > α_2(uj)` (lower bound of `thm:fraser`). -/
theorem fraserStopSum_mono {δ : ℝ} {f g : List ι → ℝ}
    (hfg : ∀ u j, δ ≤ S.alpha₂ u → S.alpha₂ (u ++ [j]) < δ → f (u ++ [j]) ≤ g (u ++ [j])) :
    ∀ (k : ℕ) (u : List ι), δ ≤ S.alpha₂ u → S.fraserStopSum δ f k u ≤ S.fraserStopSum δ g k u
  | 0, _, _ => le_rfl
  | k + 1, u, hu => by
    rw [fraserStopSum_succ, fraserStopSum_succ]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs with h
    · exact hfg u j hu h
    · exact fraserStopSum_mono hfg k (u ++ [j]) (not_lt.1 h)

variable (S)

/-- The stopped sum is homogeneous (lower bound of `thm:fraser`). -/
theorem fraserStopSum_const_mul (δ c : ℝ) (f : List ι → ℝ) :
    ∀ (k : ℕ) (u : List ι),
      S.fraserStopSum δ (fun w => c * f w) k u = c * S.fraserStopSum δ f k u
  | 0, _ => by simp
  | k + 1, u => by
    rw [fraserStopSum_succ, fraserStopSum_succ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rfl
    · exact fraserStopSum_const_mul δ c f k (u ++ [j])

/-- The stopped sum commutes with finite sums (lower bound of `thm:fraser`). -/
theorem fraserStopSum_sum {α : Type*} (δ : ℝ) (D : Finset α) (f : α → List ι → ℝ) :
    ∀ (k : ℕ) (u : List ι), S.fraserStopSum δ (fun w => ∑ z ∈ D, f z w) k u =
      ∑ z ∈ D, S.fraserStopSum δ (f z) k u
  | 0, _ => by simp
  | k + 1, u => by
    simp_rw [fraserStopSum_succ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : S.alpha₂ (u ++ [j]) < δ
    · simp only [h, ite_true]
    · simp only [h, ite_false]
      exact fraserStopSum_sum δ D f k (u ++ [j])

variable {S}

/-- The first tree inequality of the lower bound of `thm:fraser`: a function with
`F(u) ≤ ∑_j F(uj)` whenever `α_2(u) ≥ δ` is at most its stopped sum, once the depth `k` reaches
`r^{|u| + k} < δ`. -/
theorem le_fraserStopSum {δ r M : ℝ} (hS : S.Bounds r M) {F : List ι → ℝ}
    (hF : ∀ u, δ ≤ S.alpha₂ u → F u ≤ ∑ j, F (u ++ [j])) :
    ∀ (k : ℕ) (u : List ι), δ ≤ S.alpha₂ u → r ^ (u.length + k) < δ →
      F u ≤ S.fraserStopSum δ F k u
  | 0, u, hu, hk => absurd ((hS.alpha₂_le u).trans_lt hk) (not_lt.2 hu)
  | k + 1, u, hu, hk => by
    refine (hF u hu).trans ?_
    rw [fraserStopSum_succ]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs with h
    · exact le_rfl
    · refine le_fraserStopSum hS hF k (u ++ [j]) (not_lt.1 h) ?_
      rwa [List.length_append, List.length_singleton, add_right_comm, add_assoc]

/-- The second tree inequality of the lower bound of `thm:fraser`: a non-negative function with
`∑_j g(uj) ≤ g(u)` whenever `α_2(u) ≥ δ` is at least its stopped sum. -/
theorem fraserStopSum_le {δ : ℝ} {g : List ι → ℝ} (hg0 : ∀ w, 0 ≤ g w)
    (hg : ∀ u, δ ≤ S.alpha₂ u → ∑ j, g (u ++ [j]) ≤ g u) :
    ∀ (k : ℕ) (u : List ι), δ ≤ S.alpha₂ u → S.fraserStopSum δ g k u ≤ g u
  | 0, u, _ => hg0 u
  | k + 1, u, hu => by
    refine le_trans ?_ (hg u hu)
    rw [fraserStopSum_succ]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs with h
    · exact le_rfl
    · exact fraserStopSum_le hg0 hg k (u ++ [j]) (not_lt.1 h)

end StopSum

/-- A word `u` with `α_2(u) ≥ δ > r^k` has fewer than `k` letters, so the words `uj` of the
stopping found from the root have at most `k` letters (lower bound of `thm:fraser`). -/
theorem Bounds.fraserStop_length_lt {S : System ι} {r M δ : ℝ} (hS : S.Bounds r M) {k : ℕ}
    (hk : r ^ k < δ) {u : List ι} (hu : δ ≤ S.alpha₂ u) : u.length < k := by
  by_contra h
  have h' := (hS.alpha₂_le u).trans (pow_le_pow_of_le_one hS.r_nonneg hS.r_lt_one.le (not_lt.1 h))
  linarith

/-! ### Sums below a word -/

section Tail

variable [Fintype ι]

/-- The sum `∑_{|𝐣| = m} ψ^t(𝐢𝐣)` over the words of length `m` below `𝐢`, in the proof of
Fraser's Lemma 5.1 (2) for `thm:fraser`. -/
noncomputable def fraserTail (t : ℝ) (u : List ι) (m : ℕ) : ℝ :=
  ∑ v : Fin m → ι, S.modSvf t (u ++ List.ofFn v)

omit [Fintype ι] in
/-- `ψ^t(∅) = 1` (lower bound of `thm:fraser`). -/
theorem fraserModSvf_nil (t : ℝ) : S.modSvf t [] = 1 := by
  simp [modSvf, alpha₁_nil, alpha₂_nil]

/-- The sum of length `0` below `𝐢` is `ψ^t(𝐢)` (lower bound of `thm:fraser`). -/
theorem fraserTail_zero (t : ℝ) (u : List ι) : S.fraserTail t u 0 = S.modSvf t u := by
  simp [fraserTail]

/-- Splitting off the first letter below `𝐢` (lower bound of `thm:fraser`). -/
theorem fraserTail_succ (t : ℝ) (u : List ι) (m : ℕ) :
    S.fraserTail t u (m + 1) = ∑ j, S.fraserTail t (u ++ [j]) m := by
  unfold fraserTail
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Fin.consEquiv fun _ => ι).symm _ _ fun v => ?_
  simp [Fin.consEquiv, List.ofFn_succ]
  rfl

/-- Below the empty word the sums are `Ψ_n^t` (lower bound of `thm:fraser`). -/
theorem fraserTail_nil (t : ℝ) (n : ℕ) : S.fraserTail t [] n = S.modSvfSum t n := by
  simp [fraserTail, modSvfSum]

/-- The sums below a word are positive (lower bound of `thm:fraser`). -/
theorem fraserTail_pos [Nonempty ι] (t : ℝ) (u : List ι) (m : ℕ) : 0 < S.fraserTail t u m :=
  Finset.sum_pos (fun _ _ => S.modSvf_pos t _) Finset.univ_nonempty

/-- `∑_{|𝐣| = m} ψ^t(𝐢𝐣) ≤ ψ^t(𝐢) Ψ_m^t` for `t ≤ s_1 + s_2`, by Fraser's Lemma 2.1 (a1)
(lower bound of `thm:fraser`). -/
theorem fraserTail_le_mul {t : ℝ} (ht : t ≤ S.projDim 0 + S.projDim 1) (u : List ι) (m : ℕ) :
    S.fraserTail t u m ≤ S.modSvf t u * S.modSvfSum t m := by
  rw [fraserTail, modSvfSum, Finset.mul_sum]
  exact Finset.sum_le_sum fun v _ => S.modSvf_append_le ht u _

/-- `ψ^t(𝐢) Ψ_m^t ≤ ∑_{|𝐣| = m} ψ^t(𝐢𝐣)` for `t ≥ s_1 + s_2`, by Fraser's Lemma 2.1 (a3)
(lower bound of `thm:fraser`). -/
theorem mul_le_fraserTail {t : ℝ} (ht : S.projDim 0 + S.projDim 1 ≤ t) (u : List ι) (m : ℕ) :
    S.modSvf t u * S.modSvfSum t m ≤ S.fraserTail t u m := by
  rw [fraserTail, modSvfSum, Finset.mul_sum]
  exact Finset.sum_le_sum fun v _ => S.le_modSvf_append ht u _

/-- The sides of `A_𝐢([0,1]²)` are at most `1` (lower bound of `thm:fraser`). -/
theorem fraserSide_le_one (c : ZMod 2) (w : List ι) : S.side c w ≤ 1 := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  exact (hS.abs_gDeriv_le (S.codeWord c w)).trans (pow_le_one₀ hS.r_nonneg hS.r_lt_one.le)

/-- `sideSvf t c 𝐣 ≤ 1` for `t ≥ s_1 + s_2`: both exponents are non-negative (lower bound of
`thm:fraser`). -/
theorem fraserSideSvf_le_one {t : ℝ} (ht : S.projDim 0 + S.projDim 1 ≤ t) (c : ZMod 2)
    (w : List ι) : S.sideSvf t c w ≤ 1 := by
  have hp := S.projDim_nonneg (c + S.oWord w)
  have hq : S.projDim (c + S.oWord w) ≤ t := by
    have h1 := S.projDim_add_projDim (c + S.oWord w)
    have h2 := S.projDim_nonneg (c + S.oWord w + 1)
    linarith
  unfold sideSvf
  calc _ ≤ (1 : ℝ) * 1 := mul_le_mul
        (Real.rpow_le_one (S.side_pos _ _).le (S.fraserSide_le_one _ _) hp)
        (Real.rpow_le_one (S.side_pos _ _).le (S.fraserSide_le_one _ _) (by linarith))
        (Real.rpow_nonneg (S.side_pos _ _).le _) zero_le_one
    _ = 1 := one_mul 1

/-- `ψ^t(𝐢𝐣) ≤ ψ^t(𝐢)` for `t ≥ s_1 + s_2`: `ψ^t(𝐢𝐣)` is at most
`sideSvf t c (𝐢𝐣) = sideSvf t c 𝐢 · sideSvf t (c + o(𝐢)) 𝐣`, where `c` is the axis with
`ψ^t(𝐢) = sideSvf t c 𝐢`, and the second factor is at most `1`. It enters the
super-multiplicative case of Fraser's Lemma 5.1 (2) for `thm:fraser`. -/
theorem fraserModSvf_append_le {t : ℝ} (ht : S.projDim 0 + S.projDim 1 ≤ t) (u v : List ι) :
    S.modSvf t (u ++ v) ≤ S.modSvf t u := by
  obtain ⟨c, hc⟩ := S.modSvf_eq_sideSvf t u
  calc S.modSvf t (u ++ v) ≤ S.sideSvf t c (u ++ v) := S.modSvf_le_sideSvf ht c _
    _ = S.sideSvf t c u * S.sideSvf t (c + S.oWord u) v := S.sideSvf_append t c u v
    _ ≤ S.sideSvf t c u * 1 := mul_le_mul_of_nonneg_left (S.fraserSideSvf_le_one ht _ _)
        (by rw [← hc]; exact (S.modSvf_pos t u).le)
    _ = S.modSvf t u := by rw [mul_one, hc]

/-- `∑_{|𝐣| = m} ψ^t(𝐢𝐣) ≤ N^m ψ^t(𝐢)` for `t ≥ s_1 + s_2` (lower bound of
`thm:fraser`). -/
theorem fraserTail_le_card {t : ℝ} (ht : S.projDim 0 + S.projDim 1 ≤ t) (u : List ι) (m : ℕ) :
    S.fraserTail t u m ≤ (Fintype.card ι : ℝ) ^ m * S.modSvf t u := by
  calc S.fraserTail t u m ≤ ∑ _v : Fin m → ι, S.modSvf t u :=
        Finset.sum_le_sum fun v _ => S.fraserModSvf_append_le ht u _
    _ = (Fintype.card ι : ℝ) ^ m * S.modSvf t u := by simp

variable {S}

/-- The renewal inequality of the sub-multiplicative case of Fraser's Lemma 5.1 (2), for
`thm:fraser`: for `t ≤ s_1 + s_2`, a word `u` with `α_2(u) ≥ δ` and `n = |u| + m`,
`∑_{|𝐣| = m} ψ^t(u𝐣) ≤ ∑_{𝐢} ψ^t(𝐢) Ψ_{n - |𝐢|}^t`, the sum running over the words `𝐢` of the
`δ`-stopping below `u`. Each word `u𝐣` splits as `𝐢𝐣'` with `𝐢` in the stopping. -/
theorem fraserTail_le_fraserStopSum {δ r M t : ℝ} (hS : S.Bounds r M)
    (ht : t ≤ S.projDim 0 + S.projDim 1) (n : ℕ) :
    ∀ (k : ℕ) (u : List ι) (m : ℕ), δ ≤ S.alpha₂ u → r ^ (u.length + k) < δ → k ≤ m →
      u.length + m = n → S.fraserTail t u m ≤
        S.fraserStopSum δ (fun w => S.modSvf t w * S.modSvfSum t (n - w.length)) k u
  | 0, u, _, hu, hk, _, _ => absurd ((hS.alpha₂_le u).trans_lt hk) (not_lt.2 hu)
  | k + 1, u, m, hu, hk, hkm, hn => by
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [fraserTail_succ, fraserStopSum_succ]
    refine Finset.sum_le_sum fun j _ => ?_
    have hlen : (u ++ [j]).length = u.length + 1 := by simp
    split_ifs with h
    · rw [show n - (u ++ [j]).length = m by omega]
      exact S.fraserTail_le_mul ht _ _
    · refine fraserTail_le_fraserStopSum hS ht n k (u ++ [j]) m (not_lt.1 h) ?_ (by omega)
        (by omega)
      rwa [hlen, add_right_comm, add_assoc]

variable (S)

/-- Fraser's Lemma 5.1 (2) for `thm:fraser`, sub-multiplicative case `0 ≤ t ≤ s_1 + s_2`,
`t < dimmaff(X)`: `∑_{𝐢 ∈ I_δ} ψ^t(𝐢) > 1` for every `δ ≤ 1`. If the sum were at most `1`, the
renewal inequality `fraserTail_le_fraserStopSum` would bound every `Ψ_n^t` by
`∑_{m ≤ k} Ψ_m^t`, so the modified pressure at `t` would be non-positive and
`t ≥ dimmaff(X)`. -/
theorem one_lt_fraserStopSum_of_le [Nonempty ι] {δ r M t : ℝ} (hS : S.Bounds r M)
    (ht0 : 0 ≤ t) (ht : t ≤ S.projDim 0 + S.projDim 1) (htd : t < S.dimmaff) (hδ1 : δ ≤ 1)
    {k : ℕ} (hk : r ^ k < δ) : 1 < S.fraserStopSum δ (S.modSvf t) k [] := by
  by_contra hZ
  replace hZ := not_lt.1 hZ
  set B := ∑ m ∈ Finset.range (k + 1), S.modSvfSum t m with hB
  have hpos := fun n => S.modSvfSum_pos t n
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun m _ => (hpos m).le
  have hroot : δ ≤ S.alpha₂ [] := by rw [alpha₂_nil]; exact hδ1
  have hbound : ∀ n, S.modSvfSum t n ≤ B := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n ≤ k
      · exact Finset.single_le_sum (f := fun m => S.modSvfSum t m) (fun m _ => (hpos m).le)
          (Finset.mem_range.2 (by omega))
      replace hn := not_le.1 hn
      rw [← S.fraserTail_nil]
      refine (fraserTail_le_fraserStopSum hS ht n k [] n hroot (by simpa using hk) hn.le
        (by simp)).trans ?_
      refine (fraserStopSum_mono (g := fun w => B * S.modSvf t w) ?_ k [] hroot).trans ?_
      · intro u j hu _
        have hlu := hS.fraserStop_length_lt hk hu
        rw [mul_comm]
        refine mul_le_mul_of_nonneg_right (ih _ ?_) (S.modSvf_pos t _).le
        simp only [List.length_append, List.length_singleton]
        omega
      · rw [S.fraserStopSum_const_mul δ B (S.modSvf t) k []]
        calc B * S.fraserStopSum δ (S.modSvf t) k [] ≤ B * 1 :=
              mul_le_mul_of_nonneg_left hZ hB0
          _ = B := mul_one B
  have hP : S.modPressure t ≤ 0 := by
    refine le_of_tendsto_of_tendsto' (S.tendsto_modPressure ht0)
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log B)) fun n => ?_
    exact div_le_div_of_nonneg_right (Real.log_le_log (hpos n) (hbound n)) (Nat.cast_nonneg n)
  exact absurd (S.dimmaff_le_of_modPressure_nonpos ht0 hP) (not_le.2 htd)

/-- Fraser's Lemma 5.1 (2) for `thm:fraser`, super-multiplicative case `t ≥ s_1 + s_2`,
`t < dimmaff(X)`: the modified pressure at `t` is positive, so `Ψ_b^t ≥ 1` for some `b ≥ 1`.
The function `F(𝐢) = ∑_{m < b} ∑_{|𝐣| = m} ψ^t(𝐢𝐣)` satisfies `F(𝐢) ≤ ∑_j F(𝐢j)`, since
`∑_{|𝐣| = b} ψ^t(𝐢𝐣) ≥ ψ^t(𝐢) Ψ_b^t ≥ ψ^t(𝐢)`, and `ψ^t ≤ F ≤ K ψ^t` with
`K = ∑_{m < b} N^m`; the first tree inequality gives `∑_{𝐢 ∈ I_δ} ψ^t(𝐢) ≥ F(∅)/K ≥ 1/K`. -/
theorem exists_le_fraserStopSum_of_ge [Nonempty ι] {r M t : ℝ} (hS : S.Bounds r M)
    (ht0 : 0 ≤ t) (ht : S.projDim 0 + S.projDim 1 ≤ t) (htd : t < S.dimmaff) :
    ∃ L : ℝ, 0 < L ∧ ∀ δ : ℝ, δ ≤ 1 → ∀ k : ℕ, r ^ k < δ →
      L ≤ S.fraserStopSum δ (S.modSvf t) k [] := by
  have hP : 0 < S.modPressure t := by
    have h := S.strictAntiOn_modPressure ht0 S.dimmaff_nonneg htd
    rwa [S.modPressure_dimmaff] at h
  obtain ⟨b, hb1, hb⟩ : ∃ b : ℕ, 0 < b ∧ 0 < Real.log (S.modSvfSum t b) / b :=
    ((eventually_gt_atTop 0).and ((S.tendsto_modPressure ht0).eventually
      (lt_mem_nhds hP))).exists
  have hΨ : 1 ≤ S.modSvfSum t b := by
    by_contra h
    have hlog := Real.log_neg (S.modSvfSum_pos t b) (not_le.1 h)
    have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb1
    have := div_neg_of_neg_of_pos hlog hb'
    linarith
  set K : ℝ := ∑ m ∈ Finset.range b, (Fintype.card ι : ℝ) ^ m with hK
  have hK1 : 1 ≤ K := by
    have h := Finset.single_le_sum (f := fun m => (Fintype.card ι : ℝ) ^ m)
      (fun m _ => pow_nonneg (Nat.cast_nonneg _) m) (Finset.mem_range.2 hb1)
    simpa using h
  set F : List ι → ℝ := fun u => ∑ m ∈ Finset.range b, S.fraserTail t u m with hF
  have hFtree : ∀ u, F u ≤ ∑ j, F (u ++ [j]) := by
    intro u
    have h1 := Finset.sum_range_succ (fun m => S.fraserTail t u m) b
    have h2 := Finset.sum_range_succ' (fun m => S.fraserTail t u m) b
    have h3 : S.fraserTail t u 0 ≤ S.fraserTail t u b := by
      rw [S.fraserTail_zero]
      exact (le_mul_of_one_le_right (S.modSvf_pos t u).le hΨ).trans (S.mul_le_fraserTail ht u b)
    have h4 : ∑ j, F (u ++ [j]) = ∑ m ∈ Finset.range b, S.fraserTail t u (m + 1) := by
      simp only [hF]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ => (S.fraserTail_succ t u m).symm
    rw [h4]
    simp only [hF]
    linarith
  have hFup : ∀ u, F u ≤ K * S.modSvf t u := by
    intro u
    simp only [hF, hK, Finset.sum_mul]
    exact Finset.sum_le_sum fun m _ => S.fraserTail_le_card ht u m
  have hF1 : 1 ≤ F [] := by
    have h := Finset.single_le_sum (f := fun m => S.fraserTail t [] m)
      (fun m _ => (S.fraserTail_pos t [] m).le) (Finset.mem_range.2 hb1)
    simp only [S.fraserTail_zero, S.fraserModSvf_nil] at h
    exact h
  refine ⟨1 / K, by positivity, fun δ hδ1 k hk => ?_⟩
  have hroot : δ ≤ S.alpha₂ [] := by rw [alpha₂_nil]; exact hδ1
  have h1 : F [] ≤ S.fraserStopSum δ F k [] :=
    le_fraserStopSum hS (fun u _ => hFtree u) k [] hroot (by simpa using hk)
  have h2 : S.fraserStopSum δ F k [] ≤ S.fraserStopSum δ (fun w => K * S.modSvf t w) k [] :=
    fraserStopSum_mono (fun u j _ _ => hFup _) k [] hroot
  rw [S.fraserStopSum_const_mul δ K (S.modSvf t) k []] at h2
  rw [div_le_iff₀ (by linarith)]
  calc (1 : ℝ) ≤ F [] := hF1
    _ ≤ K * S.fraserStopSum δ (S.modSvf t) k [] := h1.trans h2
    _ = S.fraserStopSum δ (S.modSvf t) k [] * K := mul_comm _ _

/-- Fraser's Lemma 5.1 (2), in the proof of `thm:fraser` (tex lines 398 to 473): for
`0 ≤ t < dimmaff(X)` there is `L > 0` with `∑_{𝐢 ∈ I_δ} ψ^t(𝐢) ≥ L` for all `δ ≤ 1`. -/
theorem exists_le_fraserStopSum [Nonempty ι] {r M t : ℝ} (hS : S.Bounds r M) (ht0 : 0 ≤ t)
    (htd : t < S.dimmaff) :
    ∃ L : ℝ, 0 < L ∧ ∀ δ : ℝ, δ ≤ 1 → ∀ k : ℕ, r ^ k < δ →
      L ≤ S.fraserStopSum δ (S.modSvf t) k [] := by
  rcases le_total t (S.projDim 0 + S.projDim 1) with ht | ht
  · exact ⟨1, one_pos, fun δ hδ1 k hk => (S.one_lt_fraserStopSum_of_le hS ht0 ht htd hδ1 hk).le⟩
  · exact S.exists_le_fraserStopSum_of_ge hS ht0 ht htd

end Tail

end System

end BoxLike
