module

/-
Falconer's upper bound for the upper Minkowski dimension of a box-like self-affine set, in
`sec:affinity_dim`: `eq:hausdorff_affinity_upper_bound` (tex lines 2063 to 2074) and the bound
of tex lines 510 to 510, after Falconer, Math. Proc. Cambridge Philos. Soc. 103 (1988),
Theorem 5.4, which the article cites.

The plane `ℝ × ℝ` carries the sup metric, so closed balls are squares. For a word `𝐢` the copy
`φ_𝐢(X)` lies in a rectangle with sides `2 α_1(A_𝐢) D` and `2 α_2(A_𝐢) D`, where `D` bounds
the diameter of `X`. Fix `t ≤ 2` with `P(𝖠, t) < 0`, so that
`∑_n ∑_{|𝐢| = n} φ^t(A_𝐢) ≤ K`. At the scale `ρD` every point of `X` lies in a copy `φ_𝐢(X)`
whose singular value `α_k(A_𝐢)` lies between `δ₀ρ` and `ρ`, with `k = 1` for `t ≤ 1` and
`k = 2` for `1 < t ≤ 2`, and `δ₀` the least modulus of an entry of a generator. The rectangle of
such a word is covered by `(α_1/ρ + 1)(α_2/ρ + 1) ≤ 4 (δ₀ρ)^{-t} φ^t(A_𝐢)` squares of radius
`ρD`, so `N_{ρD}(X) ≤ 4 K (δ₀ρ)^{-t}`. No separation condition enters.

* `exists_stop`: the stopping time of a sequence that decreases by at most the factor `δ₀`.
* `gridFinset`, `card_gridFinset_le`: the centres of `gridCentres` as a finite set.
* `System.Bounds.exists_proj_eq_phiWord`: `π(𝐢) ∈ φ_{𝐢|_n}(X)` for every `n`.
* `System.abs_coord_phiWord_sub_le`: `φ_𝐢(X)` lies in a rectangle with sides
  `2 b(𝐢) D` and `2 h(𝐢) D`.
* `System.RatioLowerBound.alpha₁_append_ge`, `System.RatioLowerBound.alpha₂_append_ge`:
  appending a letter shrinks `α_1` and `α_2` by at most the factor `δ₀`.
* `System.card_le_svf_of_alpha₁`, `System.card_le_svf_of_alpha₂`: the number of squares for a
  single word, against `φ^t(A_𝐢)`.
* `System.externalCoveringNumber_attractor_le`: the covering count `N_{ρD}(X) ≤ BK` for a
  stopping rule and a per-word bound `B φ^t(A_𝐢)`.
* `System.upperBoxDim_attractor_le_two`: `\overline{\dim}_M X ≤ 2`.
* `System.upperBoxDim_attractor_le_of_pressure_neg_of_le_two`,
  `System.upperBoxDim_attractor_le_of_pressure_neg`: `\overline{\dim}_M X ≤ t` for every
  `t ≥ 0` with `P(𝖠, t) < 0`.
* `System.upperBoxDim_attractor_le_dimaff`, `System.upperBoxDim_attractor_le`,
  `System.dimH_attractor_le`: `\dim_H X ≤ \overline{\dim}_M X ≤ min{2, dimaff(X)}`.
-/
public import BoxLike.ModifiedAffinity

@[expose] public section

namespace BoxLike

open Filter Topology
open scoped ENNReal NNReal

/-! ### Two elementary lemmas -/

/-- A sequence with `F(0) ≥ ρ ≥ 0` that shrinks by at most the factor `δ₀ ∈ [0, 1]` at each step
and eventually drops to `ρ` takes a value in `[δ₀ρ, ρ]`: the first `n` with `F(n) ≤ ρ`. -/
theorem exists_stop {F : ℕ → ℝ} {δ₀ ρ : ℝ} (hδ₀ : 0 ≤ δ₀) (hδ₀1 : δ₀ ≤ 1) (hρ : 0 ≤ ρ)
    (h0 : ρ ≤ F 0) (hδ : ∀ n, δ₀ * F n ≤ F (n + 1)) (hex : ∃ n, F n ≤ ρ) :
    ∃ n, δ₀ * ρ ≤ F n ∧ F n ≤ ρ := by
  classical
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  cases h : Nat.find hex with
  | zero => exact (mul_le_of_le_one_left hρ hδ₀1).trans h0
  | succ m =>
    have hm : ¬ F m ≤ ρ := Nat.find_min hex (by omega)
    exact (mul_le_mul_of_nonneg_left (not_le.1 hm).le hδ₀).trans (hδ m)

/-- `(a/ρ + 1)(b/ρ + 1) = (max{a, b}/ρ + 1)(min{a, b}/ρ + 1)`. -/
theorem div_add_one_mul_div_add_one (a b ρ : ℝ) :
    (a / ρ + 1) * (b / ρ + 1) = (max a b / ρ + 1) * (min a b / ρ + 1) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_left h]
    ring
  · rw [max_eq_left h, min_eq_right h]

/-- The centres of `gridCentres a b r` as a finite set. -/
noncomputable def gridFinset (a b r : ℝ) : Finset ℝ :=
  (Finset.range (⌊(b - a) / (2 * r)⌋₊ + 1)).image fun k : ℕ => a + (2 * (k : ℝ) + 1) * r

/-- The finite set `gridFinset a b r` is `gridCentres a b r`. -/
theorem coe_gridFinset (a b r : ℝ) : (gridFinset a b r : Set ℝ) = gridCentres a b r := by
  rw [gridFinset, Finset.coe_image]
  rfl

/-- The subdivision of `[a, b]` into intervals of length `2r` has at most
`⌊(b - a)/(2r)⌋ + 1` centres. -/
theorem card_gridFinset_le (a b r : ℝ) :
    ((gridFinset a b r).card : ℝ) ≤ ⌊(b - a) / (2 * r)⌋₊ + 1 := by
  have h : (gridFinset a b r).card ≤ ⌊(b - a) / (2 * r)⌋₊ + 1 :=
    Finset.card_image_le.trans (Finset.card_range _).le
  exact_mod_cast h

namespace System

variable {ι : Type*} (S : System ι)

/-! ### Copies of `X` along a coding -/

variable {S} in
/-- `π(𝐢) = φ_{𝐢|_n}(π(𝐣))` for some `𝐣`: the point `π(𝐢)` lies in `φ_{𝐢|_n}(X)`. -/
theorem Bounds.exists_proj_eq_phiWord {r M : ℝ} (hS : S.Bounds r M) (n : ℕ) (x : ℤ → ι) :
    ∃ y, S.proj x = S.phiWord (futureWord x n) (S.proj y) := by
  induction n generalizing x with
  | zero => exact ⟨x, rfl⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih (shift 1 x)
    refine ⟨y, ?_⟩
    rw [hS.proj_eq x, futureWord_succ', phiWord_cons, Function.comp_apply, hy]

/-- The coordinate `c` of `φ_𝐢` stretches the coordinate `c + o(𝐢)` by the side `b(𝐢)` or
`h(𝐢)` of `A_𝐢([0,1]²)` along the axis `c`, so `φ_𝐢(X)` lies in a rectangle with sides
`2 b(𝐢) D` and `2 h(𝐢) D` when `D` bounds the diameter of `X`. -/
theorem abs_coord_phiWord_sub_le {D : ℝ}
    (hdist : ∀ x ∈ S.attractor, ∀ x' ∈ S.attractor, dist x x' ≤ D) (c : ZMod 2) (w : List ι)
    {p q : ℝ × ℝ} (hp : p ∈ S.attractor) (hq : q ∈ S.attractor) :
    |coord c (S.phiWord w p) - coord c (S.phiWord w q)| ≤ S.side c w * D := by
  rw [coord_phiWord, coord_phiWord, S.gWord_apply (S.codeWord c w) (coord (c + S.oWord w) p),
    S.gWord_apply (S.codeWord c w) (coord (c + S.oWord w) q)]
  calc |S.gDeriv (S.codeWord c w) * coord (c + S.oWord w) p + S.gWord (S.codeWord c w) 0 -
        (S.gDeriv (S.codeWord c w) * coord (c + S.oWord w) q + S.gWord (S.codeWord c w) 0)|
      = S.side c w * |coord (c + S.oWord w) p - coord (c + S.oWord w) q| := by
        unfold side
        rw [← abs_mul]
        ring_nf
    _ ≤ S.side c w * D := mul_le_mul_of_nonneg_left
        ((abs_coord_sub_le _ p q).trans (hdist p hp q hq)) (S.side_pos c w).le

/-! ### The singular values along a coding -/

/-- `α_1(A_∅) = 1`. -/
theorem alpha₁_nil : S.alpha₁ [] = 1 := by
  simp [alpha₁, wordBase, wordHeight]

/-- `α_2(A_∅) = 1`. -/
theorem alpha₂_nil : S.alpha₂ [] = 1 := by
  simp [alpha₂, wordBase, wordHeight]

variable {S} {r M δ₀ : ℝ}

/-- `α_2(A_𝐢) ≤ r^{|𝐢|}` when every `|a_i|` and `|b_i|` is at most `r`. -/
theorem Bounds.alpha₂_le (hS : S.Bounds r M) (w : List ι) : S.alpha₂ w ≤ r ^ w.length :=
  (S.alpha₂_le_alpha₁ w).trans (hS.alpha₁_le w)

/-- Appending a letter shrinks the side of `A_𝐢([0,1]²)` along the axis `c` by at most the
factor `δ₀`. -/
theorem RatioLowerBound.side_append_ge (hδ₀ : S.RatioLowerBound δ₀) (c : ZMod 2) (w : List ι)
    (j : ι) : δ₀ * S.side c w ≤ S.side c (w ++ [j]) := by
  rw [side_append, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (S.side_pos c w).le
  simpa [side] using hδ₀.2 (j, c + S.oWord w)

/-- `α_1(A_{𝐢j}) ≥ δ₀ α_1(A_𝐢)`. -/
theorem RatioLowerBound.alpha₁_append_ge (hδ₀ : S.RatioLowerBound δ₀) (w : List ι) (j : ι) :
    δ₀ * S.alpha₁ w ≤ S.alpha₁ (w ++ [j]) := by
  change δ₀ * max (S.side 0 w) (S.side 1 w) ≤ max (S.side 0 (w ++ [j])) (S.side 1 (w ++ [j]))
  rw [mul_max_of_nonneg _ _ hδ₀.1.le]
  exact max_le_max (hδ₀.side_append_ge 0 w j) (hδ₀.side_append_ge 1 w j)

/-- `α_2(A_{𝐢j}) ≥ δ₀ α_2(A_𝐢)`. -/
theorem RatioLowerBound.alpha₂_append_ge (hδ₀ : S.RatioLowerBound δ₀) (w : List ι) (j : ι) :
    δ₀ * S.alpha₂ w ≤ S.alpha₂ (w ++ [j]) := by
  change δ₀ * min (S.side 0 w) (S.side 1 w) ≤ min (S.side 0 (w ++ [j])) (S.side 1 (w ++ [j]))
  rw [mul_min_of_nonneg _ _ hδ₀.1.le]
  exact min_le_min (hδ₀.side_append_ge 0 w j) (hδ₀.side_append_ge 1 w j)

variable (S)

/-! ### Squares per word -/

/-- For `0 ≤ t ≤ 1` and `δ₀ρ ≤ α_1(A_𝐢) ≤ ρ` the rectangle of `𝐢` needs at most
`4 ≤ 4 (δ₀ρ)^{-t} φ^t(A_𝐢)` squares, since `φ^t(A_𝐢) = α_1(A_𝐢)^t`. -/
theorem card_le_svf_of_alpha₁ {t ρ : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hδρ : 0 < δ₀ * ρ)
    (hρ : 0 < ρ) {w : List ι} (h1 : δ₀ * ρ ≤ S.alpha₁ w) (h2 : S.alpha₁ w ≤ ρ) :
    (S.alpha₁ w / ρ + 1) * (S.alpha₂ w / ρ + 1) ≤ 4 * (δ₀ * ρ) ^ (-t) * svf t (S.matWord w) := by
  have ha₁ : S.alpha₁ w / ρ ≤ 1 := (div_le_one hρ).2 h2
  have ha₂ : S.alpha₂ w / ρ ≤ 1 := (div_le_one hρ).2 ((S.alpha₂_le_alpha₁ w).trans h2)
  have ha₂0 : 0 ≤ S.alpha₂ w / ρ := div_nonneg (S.alpha₂_pos w).le hρ.le
  have hsvf : svf t (S.matWord w) = S.alpha₁ w ^ t := by
    rw [svf_matWord_eq, svfExp, ite_eq_left ht1, sub_self, Real.rpow_zero, mul_one]
  have hpow : (δ₀ * ρ) ^ (-t) * (δ₀ * ρ) ^ t = 1 := by
    rw [Real.rpow_neg hδρ.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hδρ t).ne']
  calc (S.alpha₁ w / ρ + 1) * (S.alpha₂ w / ρ + 1) ≤ 2 * 2 :=
        mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
    _ = 4 * ((δ₀ * ρ) ^ (-t) * (δ₀ * ρ) ^ t) := by rw [hpow]; norm_num
    _ ≤ 4 * ((δ₀ * ρ) ^ (-t) * S.alpha₁ w ^ t) := by gcongr
    _ =4 * (δ₀ * ρ) ^ (-t) * svf t (S.matWord w) := by rw [hsvf, mul_assoc]

/-- For `1 < t ≤ 2` and `δ₀ρ ≤ α_2(A_𝐢) ≤ ρ` the rectangle of `𝐢` needs at most
`4 α_1(A_𝐢)/(δ₀ρ) ≤ 4 (δ₀ρ)^{-t} φ^t(A_𝐢)` squares, since
`φ^t(A_𝐢) = α_1(A_𝐢) α_2(A_𝐢)^{t-1}`. -/
theorem card_le_svf_of_alpha₂ {t ρ : ℝ} (ht1 : 1 < t) (ht2 : t ≤ 2) (hδ₀ : 0 < δ₀)
    (hδ₀1 : δ₀ ≤ 1) (hρ : 0 < ρ) {w : List ι} (h1 : δ₀ * ρ ≤ S.alpha₂ w)
    (h2 : S.alpha₂ w ≤ ρ) :
    (S.alpha₁ w / ρ + 1) * (S.alpha₂ w / ρ + 1) ≤ 4 * (δ₀ * ρ) ^ (-t) * svf t (S.matWord w) := by
  have hδρ : 0 < δ₀ * ρ := mul_pos hδ₀ hρ
  have hδρρ : δ₀ * ρ ≤ ρ := mul_le_of_le_one_left hρ.le hδ₀1
  have ha₁0 : 0 ≤ S.alpha₁ w := (S.alpha₁_pos w).le
  have ha₂ : S.alpha₂ w / ρ ≤ 1 := (div_le_one hρ).2 h2
  have ha₂0 : 0 ≤ S.alpha₂ w / ρ := div_nonneg (S.alpha₂_pos w).le hρ.le
  have hq1 : S.alpha₁ w / ρ ≤ S.alpha₁ w / (δ₀ * ρ) :=
    div_le_div_of_nonneg_left ha₁0 hδρ hδρρ
  have hq2 : 1 ≤ S.alpha₁ w / (δ₀ * ρ) :=
    (one_le_div hδρ).2 (h1.trans (S.alpha₂_le_alpha₁ w))
  have hsvf : S.alpha₁ w * (δ₀ * ρ) ^ (t - 1) ≤ svf t (S.matWord w) := by
    rw [svf_matWord_eq, svfExp_eq_one ht1.le ht2, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδρ.le h1 (by linarith)) ha₁0
  have hpow : (δ₀ * ρ) ^ (-t) * (δ₀ * ρ) ^ (t - 1) = (δ₀ * ρ)⁻¹ := by
    rw [← Real.rpow_add hδρ, show -t + (t - 1) = -1 by ring, Real.rpow_neg_one]
  calc (S.alpha₁ w / ρ + 1) * (S.alpha₂ w / ρ + 1)
      ≤ (2 * (S.alpha₁ w / (δ₀ * ρ))) * 2 :=
        mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    _ = 4 * ((δ₀ * ρ) ^ (-t) * (δ₀ * ρ) ^ (t - 1)) * S.alpha₁ w := by
        rw [hpow, div_eq_mul_inv]
        ring
    _ = 4 * (δ₀ * ρ) ^ (-t) * (S.alpha₁ w * (δ₀ * ρ) ^ (t - 1)) := by ring
    _ ≤ 4 * (δ₀ * ρ) ^ (-t) * svf t (S.matWord w) :=
        mul_le_mul_of_nonneg_left hsvf (by positivity)

end System

/-! ### The covering count -/

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι) {r M δ₀ : ℝ}

/-- The covering argument. Let `f` be `α_1` or `α_2`, or any function of words with
`f(∅) = 1`, `f(𝐢j) ≥ δ₀ f(𝐢)` and `f(𝐢) ≤ r^{|𝐢|}`, and let every word with
`δ₀ρ ≤ f(𝐢) ≤ ρ` satisfy `(α_1/ρ + 1)(α_2/ρ + 1) ≤ B φ^t(A_𝐢)`. If
`∑_{n < L} ∑_{|𝐢| = n} φ^t(A_𝐢) ≤ K` for all `L`, then `N_{ρD}(X) ≤ BK`. Every point of `X`
lies in a copy `φ_𝐢(X)` with `δ₀ρ ≤ f(𝐢) ≤ ρ`, and the rectangle of side lengths
`2 b(𝐢) D`, `2 h(𝐢) D` around it is covered by a grid of `(b(𝐢)/ρ + 1)(h(𝐢)/ρ + 1)` squares
of radius `ρD`. -/
theorem externalCoveringNumber_attractor_le [Nonempty ι] {f : List ι → ℝ} {D t K B ρ : ℝ}
    (hδ₀ : S.RatioLowerBound δ₀) (hδ₀1 : δ₀ ≤ 1) (hS : S.Bounds r M) (hD : 0 < D)
    (hdist : ∀ x ∈ S.attractor, ∀ x' ∈ S.attractor, dist x x' ≤ D)
    (hf0 : f [] = 1) (hfδ : ∀ w j, δ₀ * f w ≤ f (w ++ [j])) (hfr : ∀ w, f w ≤ r ^ w.length)
    (hK : ∀ L, ∑ n ∈ Finset.range L, S.svfSum t n ≤ K) (hB0 : 0 ≤ B) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1)
    (hB : ∀ w, δ₀ * ρ ≤ f w → f w ≤ ρ →
      (S.alpha₁ w / ρ + 1) * (S.alpha₂ w / ρ + 1) ≤ B * svf t (S.matWord w)) :
    (Metric.externalCoveringNumber (ρ * D).toNNReal S.attractor : ℝ≥0∞) ≤
      ENNReal.ofReal (B * K) := by
  classical
  obtain ⟨x₀, hx₀⟩ := S.attractor_nonempty
  have hε : 0 < ρ * D := mul_pos hρ hD
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one (mul_pos hδ₀.1 hρ) hS.r_lt_one
  set G : ZMod 2 → List ι → Finset ℝ := fun c w =>
    gridFinset (coord c (S.phiWord w x₀) - S.side c w * D)
      (coord c (S.phiWord w x₀) + S.side c w * D) (ρ * D) with hG
  set W : (n : ℕ) → Finset (Fin n → ι) := fun n => Finset.univ.filter fun w =>
    δ₀ * ρ ≤ f (List.ofFn w) ∧ f (List.ofFn w) ≤ ρ with hW
  set C : Finset (ℝ × ℝ) := (Finset.range L).biUnion fun n =>
    (W n).biUnion fun w => G 0 (List.ofFn w) ×ˢ G 1 (List.ofFn w) with hC
  have hcov : Metric.IsCover (ρ * D).toNNReal S.attractor (C : Set (ℝ × ℝ)) := by
    rintro _ ⟨x, rfl⟩
    have hex : ∃ n, f (futureWord x n) ≤ ρ := by
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hρ hS.r_lt_one
      refine ⟨k, (hfr _).trans ?_⟩
      rw [length_futureWord]
      exact hk.le
    obtain ⟨n, hn1, hn2⟩ := exists_stop (F := fun n => f (futureWord x n)) hδ₀.1.le hδ₀1 hρ.le
      (by rw [futureWord_zero, hf0]; exact hρ1)
      (fun n => by rw [futureWord_succ]; exact hfδ _ _) hex
    obtain ⟨y, hy⟩ := hS.exists_proj_eq_phiWord n x
    have hlen : n < L := by
      by_contra h
      rw [not_lt] at h
      have h1 := hfr (futureWord x n)
      rw [length_futureWord] at h1
      have h2 : r ^ n ≤ r ^ L := pow_le_pow_of_le_one hS.r_nonneg hS.r_lt_one.le h
      linarith
    have hmem : ∀ c, coord c (S.proj x) ∈ Set.Icc
        (coord c (S.phiWord (futureWord x n) x₀) - S.side c (futureWord x n) * D)
        (coord c (S.phiWord (futureWord x n) x₀) + S.side c (futureWord x n) * D) := by
      intro c
      rw [hy]
      have h := S.abs_coord_phiWord_sub_le hdist c (futureWord x n) ⟨y, rfl⟩ hx₀
      exact ⟨by linarith [(abs_le.1 h).1], by linarith [(abs_le.1 h).2]⟩
    rw [futureWord_eq_ofFn] at hmem hn1 hn2
    obtain ⟨u, hu, hxu⟩ := isCover_gridCentres hε (hmem 0)
    obtain ⟨v, hv, hyv⟩ := isCover_gridCentres hε (hmem 1)
    replace hxu : edist (S.proj x).1 u ≤ ((ρ * D).toNNReal : ℝ≥0∞) := hxu
    replace hyv : edist (S.proj x).2 v ≤ ((ρ * D).toNNReal : ℝ≥0∞) := hyv
    refine ⟨(u, v), ?_, (Prod.edist_eq _ _).trans_le (max_le hxu hyv)⟩
    rw [Finset.mem_coe, hC, Finset.mem_biUnion]
    refine ⟨n, Finset.mem_range.2 hlen, Finset.mem_biUnion.2 ⟨block n x, ?_, ?_⟩⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hn1, hn2⟩
    · rw [Finset.mem_product, hG, ← Finset.mem_coe, ← Finset.mem_coe, coe_gridFinset,
        coe_gridFinset]
      exact ⟨hu, hv⟩
  have hgrid : ∀ c w, ((G c w).card : ℝ) ≤ S.side c w / ρ + 1 := by
    intro c w
    refine (card_gridFinset_le _ _ _).trans ?_
    have heq : (coord c (S.phiWord w x₀) + S.side c w * D -
        (coord c (S.phiWord w x₀) - S.side c w * D)) / (2 * (ρ * D)) = S.side c w / ρ := by
      field_simp
      ring
    rw [heq]
    have := Nat.floor_le (div_nonneg (S.side_pos c w).le hρ.le)
    linarith
  have hword : ∀ w, ((G 0 w ×ˢ G 1 w).card : ℝ) ≤
      (S.alpha₁ w / ρ + 1) * (S.alpha₂ w / ρ + 1) := by
    intro w
    rw [Finset.card_product, Nat.cast_mul]
    refine (mul_le_mul (hgrid 0 w) (hgrid 1 w) (Nat.cast_nonneg _)
      (by have := S.side_pos 0 w; positivity)).trans (le_of_eq ?_)
    exact div_add_one_mul_div_add_one _ _ _
  have hsum : (C.card : ℝ) ≤ B * K := by
    calc (C.card : ℝ)
        ≤ ∑ n ∈ Finset.range L, ∑ w ∈ W n, ((G 0 (List.ofFn w) ×ˢ G 1 (List.ofFn w)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le.trans
            (Finset.sum_le_sum fun n _ => Finset.card_biUnion_le)
      _ ≤ ∑ n ∈ Finset.range L, ∑ w ∈ W n, B * svf t (S.matWord (List.ofFn w)) := by
          refine Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun w hw => ?_
          rw [hW, Finset.mem_filter] at hw
          exact (hword _).trans (hB _ hw.2.1 hw.2.2)
      _ ≤ ∑ n ∈ Finset.range L, B * S.svfSum t n := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) fun w _ _ => svf_nonneg _ _) hB0
      _ = B * ∑ n ∈ Finset.range L, S.svfSum t n := (Finset.mul_sum _ _ _).symm
      _ ≤ B * K := mul_le_mul_of_nonneg_left (hK L) hB0
  calc (Metric.externalCoveringNumber (ρ * D).toNNReal S.attractor : ℝ≥0∞)
      ≤ (C.card : ℝ≥0∞) := by
        have h := hcov.externalCoveringNumber_le_encard
        rw [Set.encard_coe_eq_coe_finsetCard] at h
        exact_mod_cast ENat.toENNReal_le.2 h
    _ = ENNReal.ofReal (C.card : ℝ) := (ENNReal.ofReal_natCast _).symm
    _ ≤ ENNReal.ofReal (B * K) := ENNReal.ofReal_le_ofReal hsum

/-! ### Falconer's bound -/

/-- A box-like self-affine set is a bounded subset of the plane, so
`\overline{\dim}_M X ≤ 2`. -/
theorem upperBoxDim_attractor_le_two : upperBoxDim S.attractor ≤ 2 :=
  upperBoxDim_le_two S.isCompact_attractor.isBounded

/-- Falconer's covering argument, Theorem 5.4 of his 1988 article, for `0 ≤ t ≤ 2`:
`\overline{\dim}_M X ≤ t` when `P(𝖠, t) < 0`. The stopping rule is `α_1(A_𝐢) ≤ ρ` for `t ≤ 1`
and `α_2(A_𝐢) ≤ ρ` for `1 < t ≤ 2`, and `N_{ρD}(X) ≤ 4 K (δ₀ρ)^{-t}` by
`externalCoveringNumber_attractor_le`. -/
theorem upperBoxDim_attractor_le_of_pressure_neg_of_le_two [Nonempty ι] {t : ℝ≥0}
    (ht2 : (t : ℝ) ≤ 2) (hP : S.pressure t < 0) : upperBoxDim S.attractor ≤ t := by
  obtain ⟨K, hK0, hK⟩ := S.exists_sum_svfSum_le t.coe_nonneg hP
  obtain ⟨δ₀, hδ₀⟩ := S.exists_ratioLowerBound
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  obtain ⟨i⟩ : Nonempty ι := inferInstance
  have hδ₀1 : δ₀ ≤ 1 := (hδ₀.2 (i, 0)).trans (S.abs_ratio_lt_one _).le
  have hδ₀0 := hδ₀.1
  obtain ⟨D₀, hD₀⟩ := Metric.isBounded_iff.1 S.isCompact_attractor.isBounded
  have hD1 : 1 ≤ max D₀ 1 := le_max_right _ _
  have hD0 : 0 < max D₀ 1 := one_pos.trans_le hD1
  have hdist : ∀ x ∈ S.attractor, ∀ x' ∈ S.attractor, dist x x' ≤ max D₀ 1 :=
    fun x hx x' hx' => (hD₀ hx hx').trans (le_max_left _ _)
  have hcount : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      (Metric.externalCoveringNumber (ρ * max D₀ 1).toNNReal S.attractor : ℝ≥0∞) ≤
        ENNReal.ofReal (4 * (δ₀ * ρ) ^ (-(t : ℝ)) * K) := by
    intro ρ hρ hρ1
    have hB0 : 0 ≤ 4 * (δ₀ * ρ) ^ (-(t : ℝ)) := by positivity
    by_cases ht1 : (t : ℝ) ≤ 1
    · exact S.externalCoveringNumber_attractor_le hδ₀ hδ₀1 hS hD0 hdist S.alpha₁_nil
        hδ₀.alpha₁_append_ge hS.alpha₁_le hK hB0 hρ hρ1 fun w h1 h2 =>
          S.card_le_svf_of_alpha₁ t.coe_nonneg ht1 (mul_pos hδ₀0 hρ) hρ h1 h2
    · exact S.externalCoveringNumber_attractor_le hδ₀ hδ₀1 hS hD0 hdist S.alpha₂_nil
        hδ₀.alpha₂_append_ge hS.alpha₂_le hK hB0 hρ hρ1 fun w h1 h2 =>
          S.card_le_svf_of_alpha₂ (not_le.1 ht1) ht2 hδ₀0 hδ₀1 hρ h1 h2
  refine upperBoxDim_le_of_forall (C := (4 * K * (δ₀ / max D₀ 1) ^ (-(t : ℝ))).toNNReal)
    (Real.toNNReal_pos.2 (by positivity)) ?_
  filter_upwards [eventually_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one' ℝ))] with ε hε0 hε1
  have hε : (0 : ℝ) < ε := hε0
  have hρ : 0 < ε / max D₀ 1 := div_pos hε hD0
  have hρ1 : ε / max D₀ 1 ≤ 1 := (div_le_one hD0).2 ((le_of_lt hε1).trans hD1)
  have h := hcount _ hρ hρ1
  rw [div_mul_cancel₀ ε hD0.ne'] at h
  calc (Metric.externalCoveringNumber ε.toNNReal S.attractor : ℝ≥0∞)
      ≤ ENNReal.ofReal (4 * (δ₀ * (ε / max D₀ 1)) ^ (-(t : ℝ)) * K) := h
    _ = ENNReal.ofReal (4 * K * (δ₀ / max D₀ 1) ^ (-(t : ℝ)) * ε ^ (-(t : ℝ))) := by
        rw [show δ₀ * (ε / max D₀ 1) = δ₀ / max D₀ 1 * ε by ring,
          Real.mul_rpow (by positivity) hε.le]
        ring_nf
    _ = ((4 * K * (δ₀ / max D₀ 1) ^ (-(t : ℝ))).toNNReal : ℝ≥0∞) *
        ENNReal.ofReal (ε ^ (-(t : ℝ))) := ENNReal.ofReal_mul (by positivity)

/-- Falconer's bound for every exponent: `\overline{\dim}_M X ≤ t` for every `t ≥ 0` with
`P(𝖠, t) < 0`. For `t > 2` it is `upperBoxDim_attractor_le_two`. -/
theorem upperBoxDim_attractor_le_of_pressure_neg [Nonempty ι] {t : ℝ} (ht : 0 ≤ t)
    (hP : S.pressure t < 0) : upperBoxDim S.attractor ≤ ENNReal.ofReal t := by
  rcases le_or_gt t 2 with ht2 | ht2
  · have h := S.upperBoxDim_attractor_le_of_pressure_neg_of_le_two (t := t.toNNReal)
      (by rwa [Real.coe_toNNReal _ ht]) (by rwa [Real.coe_toNNReal _ ht])
    exact h
  · calc upperBoxDim S.attractor ≤ 2 := S.upperBoxDim_attractor_le_two
      _ = ENNReal.ofReal 2 := ENNReal.ofReal_ofNat 2 |>.symm
      _ ≤ ENNReal.ofReal t := ENNReal.ofReal_le_ofReal ht2.le

/-- `\overline{\dim}_M X ≤ dimaff(X)`: the pressure is negative at every `t > dimaff(X)`. -/
theorem upperBoxDim_attractor_le_dimaff [Nonempty ι] :
    upperBoxDim S.attractor ≤ ENNReal.ofReal S.dimaff := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hsum : ENNReal.ofReal S.dimaff + ε = ENNReal.ofReal (S.dimaff + ε) := by
    rw [ENNReal.ofReal_add S.dimaff_nonneg ε.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  rw [hsum]
  have hpos : 0 ≤ S.dimaff + ε := add_nonneg S.dimaff_nonneg ε.coe_nonneg
  refine S.upperBoxDim_attractor_le_of_pressure_neg hpos ?_
  have h' := S.strictAntiOn_pressure (Set.mem_Ici.2 S.dimaff_nonneg) (Set.mem_Ici.2 hpos)
    (show S.dimaff < S.dimaff + ε by
      have : (0 : ℝ) < ε := hε
      linarith)
  rwa [S.pressure_dimaff] at h'

/-- Falconer's bound, Theorem 5.4 of his 1988 article, for the upper Minkowski dimension:
`\overline{\dim}_M X ≤ min{2, dimaff(X)}`, the bound of tex lines 510 to 510. It holds for every
box-like self-affine set, without a separation condition. -/
theorem upperBoxDim_attractor_le [Nonempty ι] :
    upperBoxDim S.attractor ≤ ENNReal.ofReal (min 2 S.dimaff) := by
  rcases le_total 2 S.dimaff with hd | hd
  · rw [min_eq_left hd, ENNReal.ofReal_ofNat]
    exact S.upperBoxDim_attractor_le_two
  · rw [min_eq_right hd]
    exact S.upperBoxDim_attractor_le_dimaff

/-- `eq:hausdorff_affinity_upper_bound`: `\dim_H X ≤ min{2, dimaff(X)}`, Falconer's
Theorem 5.4, from `\dim_H X ≤ \overline{\dim}_M X`. -/
theorem dimH_attractor_le [Nonempty ι] : dimH S.attractor ≤ ENNReal.ofReal (min 2 S.dimaff) :=
  (dimH_le_upperBoxDim _).trans S.upperBoxDim_attractor_le

end System

end BoxLike
