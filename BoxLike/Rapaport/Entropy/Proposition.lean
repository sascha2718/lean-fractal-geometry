module

/-
Proposition 1.7 of Rapaport (arXiv:2309.03985v1, lines 1075 to 1188 of the source) for `d = 2`:
`Exps.proposition χ : Prop17 χ`, for the statement `Prop17` of
`Rapaport/Entropy/PropositionStatement.lean`.

* Lemma 3.2 in the form used here (lines 1138 to 1153): `Exps.slice_one_good`,
  `Exps.slice_two_good`.
* The parameters (private): `lt_of_ceil_add_one_le`, `le_min_floor`, `min_floor_le`.
* The split of the levels of Lemma 3.6 (lines 1095 to 1110): `ind_or_le_add` (private),
  `Exps.levels_split`.
* Proposition 1.7: `Exps.proposition`.

The parameters, for `0 < ε < 1` and `δ₀` from Lemma 3.6 (`exists_many_levels_var_gt`): the
output `δ = δ₀ / 4`; the variance thresholds `η₂ = δ₀` and `η₁ = min δ₀ (1 / (k₂ + 1))`; the
parameters `ε₂ = min (ε / 4) δ₀` and `ε₁ = min (ε / 4) η₁` of Lemma 3.2; `m_j > 2 propConst / ε`;
the number `min ⌊δ₀ k_j / 4⌋ k_j` of good components; `k_j > 32 χ₂ / (δ₀ ε)`, so that the tuples
with fewer good components carry mass at most `ε / (4 χ₂)`; and `n ≥ 4 (|q₁| + |q₂|) / δ₀` for
the levels `q_j` of Lemma 3.2. Rapaport takes `δ` small against `ε` (line 1095); here `δ₀` is the
output of Lemma 3.6 as it stands, and the factor `k_j` makes the mass of the tuples with few good
components small instead.
-/
public import BoxLike.Rapaport.Entropy.PropositionAux
public import BoxLike.Rapaport.Entropy.PropositionStatement

@[expose] public section

namespace BoxLike.Rapaport

open MeasureTheory ProbabilityTheory

namespace Exps

variable {χ : Exps}

/-- Lemma 3.2 of the source for `j = 1` (`Exps.slices_one`) in the form used for one direction of
Proposition 1.7 (lines 1138 to 1153): at its level `q`, a convolution of `k` measures carried by
unit balls with `Var(π₁ ·) > η ≥ ε` each has `H(·, ℰ_{q+m} ∣ ℰ_q ∨ π₂⁻¹ ℰ_{q+m}) ≥ (χ₁ - ε) m`. -/
theorem slice_one_good {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hεη : ε ≤ η) {m k : ℕ}
    (hm : 0 < m) {q : ℤ}
    (hq : ∀ (θ : Fin k → Measure (ℝ × ℝ)) [∀ i, IsProbabilityMeasure (θ i)]
      (c : Fin k → ℝ × ℝ), (∀ i, InBall (θ i) (c i) ε⁻¹) → ε * k ≤ var₁ (convk k θ) →
      χ.χ₁ - ε < cent (convk k θ) (χ.E (q + m)) (fun z => (χ.E q z, χ.E₂ (q + m) z)) / m) :
    ∀ (θ' : Fin k → Measure (ℝ × ℝ)) [∀ i, IsProbabilityMeasure (θ' i)],
      (∀ i, ∃ z, InBall (θ' i) z 1) → (∀ i, η < var₁ (θ' i)) →
        (χ.χ₁ - ε) * m ≤
          cent (convk k θ') (χ.E (q + m)) (fun z => (χ.E q z, χ.E₂ (q + m) z)) := by
  intro θ' _ hz hgood
  choose c hc using hz
  have hb : ∀ i, BddSupp (θ' i) := fun i => ⟨c i, 1, hc i⟩
  have hR : (1 : ℝ) ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1.le
  have hv : ε * k ≤ var₁ (convk k θ') := by
    rw [var₁_convk hb]
    calc ε * k = ∑ _i : Fin k, ε := by simp [mul_comm]
      _ ≤ ∑ i, var₁ (θ' i) := Finset.sum_le_sum fun i _ => hεη.trans (hgood i).le
  have h := hq θ' c (fun i => (hc i).mono hR) hv
  rw [lt_div_iff₀ (by exact_mod_cast hm)] at h
  exact h.le

/-- Lemma 3.2 of the source for `j = 2` (`Exps.slices_two`) in the form used for one direction of
Proposition 1.7 (lines 1138 to 1153): at its level `q`, a convolution of `k` measures carried by
unit balls with `Var(π₂ ·) > η ≥ ε` and `Var(π₁ ·) ≤ η₁` each, where `k η₁ ≤ 1`, has
`H(·, ℰ_{q+m} ∣ ℰ_q ∨ π₁⁻¹ ℰ_{q+m}) ≥ (χ₂ - ε) m`. -/
theorem slice_two_good {ε η η₁ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hεη : ε ≤ η) {m k : ℕ}
    (hm : 0 < m) (hkη : k * η₁ ≤ 1) {q : ℤ}
    (hq : ∀ (θ : Fin k → Measure (ℝ × ℝ)) [∀ i, IsProbabilityMeasure (θ i)]
      (c : Fin k → ℝ × ℝ), (∀ i, InBall (θ i) (c i) ε⁻¹) → ε * k ≤ var₂ (convk k θ) →
      var₁ (convk k θ) ≤ ε⁻¹ →
      χ.χ₂ - ε < cent (convk k θ) (χ.E (q + m)) (fun z => (χ.E q z, χ.E₁ (q + m) z)) / m) :
    ∀ (θ' : Fin k → Measure (ℝ × ℝ)) [∀ i, IsProbabilityMeasure (θ' i)],
      (∀ i, ∃ z, InBall (θ' i) z 1) → (∀ i, η < var₂ (θ' i) ∧ var₁ (θ' i) ≤ η₁) →
        (χ.χ₂ - ε) * m ≤
          cent (convk k θ') (χ.E (q + m)) (fun z => (χ.E q z, χ.E₁ (q + m) z)) := by
  intro θ' _ hz hgood
  choose c hc using hz
  have hb : ∀ i, BddSupp (θ' i) := fun i => ⟨c i, 1, hc i⟩
  have hR : (1 : ℝ) ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1.le
  have hv : ε * k ≤ var₂ (convk k θ') := by
    rw [var₂_convk hb]
    calc ε * k = ∑ _i : Fin k, ε := by simp [mul_comm]
      _ ≤ ∑ i, var₂ (θ' i) := Finset.sum_le_sum fun i _ => hεη.trans (hgood i).1.le
  have hv₁ : var₁ (convk k θ') ≤ ε⁻¹ := by
    rw [var₁_convk hb]
    calc ∑ i, var₁ (θ' i) ≤ ∑ _i : Fin k, η₁ := Finset.sum_le_sum fun i _ => (hgood i).2
      _ = k * η₁ := by simp
      _ ≤ ε⁻¹ := hkη.trans hR
  have h := hq θ' c (fun i => (hc i).mono hR) hv hv₁
  rw [lt_div_iff₀ (by exact_mod_cast hm)] at h
  exact h.le

end Exps

/-! ### The parameters -/

/-- `⌈x⌉₊ + 1 ≤ m` gives `x < m` (for the parameters `m_j`, `k_j` of Proposition 1.7). -/
private theorem lt_of_ceil_add_one_le {x : ℝ} {m : ℕ} (h : ⌈x⌉₊ + 1 ≤ m) : x < m :=
  (Nat.le_ceil x).trans_lt (by exact_mod_cast (by omega : ⌈x⌉₊ < m))

/-- The number `min ⌊δ k / 4⌋ k` of good components of Proposition 1.7 of the source (Rapaport's
`k = ⌊δ k_j / (2d)⌋`, line 1120, capped by `k`) is at least `K'` once `k ≥ ⌈4 K' / δ⌉ + K'`. -/
private theorem le_min_floor {δ : ℝ} (hδ : 0 < δ) {K' k : ℕ} (hk : ⌈4 * K' / δ⌉₊ + K' ≤ k) :
    K' ≤ min ⌊δ * k / 4⌋₊ k := by
  refine le_min (Nat.le_floor ?_) (by omega)
  have h1 : 4 * (K' : ℝ) / δ ≤ k :=
    (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈4 * (K' : ℝ) / δ⌉₊ ≤ k))
  rw [div_le_iff₀ hδ] at h1
  rw [le_div_iff₀ (by norm_num)]
  linarith

/-- The number `min ⌊δ k / 4⌋ k` of good components (line 1120 of the source) is at most
`δ k / 4`. -/
private theorem min_floor_le {δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    ((min ⌊δ * k / 4⌋₊ k : ℕ) : ℝ) ≤ δ * k / 4 :=
  (Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le (by positivity))

/-! ### The split of the levels of Lemma 3.6 -/

/-- The pointwise form of the split of lines 1102 to 1108 of the source: for `η₁ ≤ δ₀`,
`1[v₁ > δ₀ ∨ v₂ > δ₀] ≤ 1[v₁ > η₁] + 1[v₂ > δ₀ ∧ v₁ ≤ η₁]`. -/
private theorem ind_or_le_add {v₁ v₂ δ₀ η₁ : ℝ} (h : η₁ ≤ δ₀) :
    (if δ₀ < v₁ ∨ δ₀ < v₂ then (1 : ℝ) else 0) ≤
      (if η₁ < v₁ then 1 else 0) + (if δ₀ < v₂ ∧ v₁ ≤ η₁ then 1 else 0) := by
  have h0 : (if δ₀ < v₁ ∨ δ₀ < v₂ then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have h0' : (0 : ℝ) ≤ if δ₀ < v₂ ∧ v₁ ≤ η₁ then 1 else 0 := by split_ifs <;> norm_num
  by_cases h1 : η₁ < v₁
  · rw [ite_eq_left h1]
    linarith
  · have hv₁ : v₁ ≤ η₁ := le_of_not_gt h1
    by_cases h2 : δ₀ < v₂
    · rw [ite_eq_right h1, ite_eq_left (show δ₀ < v₂ ∧ v₁ ≤ η₁ from ⟨h2, hv₁⟩)]
      linarith
    · have h3 : ¬ (δ₀ < v₁ ∨ δ₀ < v₂) := fun h3 => h3.elim (fun h4 => by linarith) h2
      rw [ite_eq_right h1, ite_eq_right h3,
        ite_eq_right (show ¬ (δ₀ < v₂ ∧ v₁ ≤ η₁) from fun h4 => h2 h4.1)]
      norm_num

/-- The split of the levels in the proof of Proposition 1.7 of the source for `d = 2` (lines 1095
to 1110, with `η₂ = δ₀` and `η₁ ≤ δ₀`): if more than `δ₀ n` levels `b ∈ [1, n]` carry
components `θ_{x,b}` of mass `> δ₀` with `Var(π₁ A_χ^b θ_{x,b}) > δ₀` or
`Var(π₂ A_χ^b θ_{x,b}) > δ₀` (Lemma 3.6), then more than `δ₀ n / 2` levels carry components of
mass `> δ₀ / 2` with `Var(π₁ ·) > η₁` (the set `B₁`), or more than `δ₀ n / 2` levels carry
components of mass `> δ₀ / 2` with `Var(π₂ ·) > δ₀` and `Var(π₁ ·) ≤ η₁` (the set `B₂`). -/
theorem Exps.levels_split (χ : Exps) {θ : Measure (ℝ × ℝ)} (hθ : BddSupp θ) {n : ℕ}
    {δ₀ η₁ : ℝ} (hη₁ : η₁ ≤ δ₀)
    (hB : δ₀ * n < (((Finset.range n).filter (fun i => δ₀ < cavg θ (χ.E (i + 1 : ℕ))
      (fun ρ => if δ₀ < var₁ (ρ.map (χ.resc (i + 1 : ℕ))) ∨
        δ₀ < var₂ (ρ.map (χ.resc (i + 1 : ℕ))) then 1 else 0))).card : ℝ)) :
    δ₀ / 2 * n < (((Finset.range n).filter fun i => δ₀ / 2 <
      cavg θ (χ.E ((i + 1 : ℕ) : ℤ)) fun ρ =>
        if η₁ < var₁ (ρ.map (χ.resc ((i + 1 : ℕ) : ℤ))) then 1 else 0).card : ℝ) ∨
    δ₀ / 2 * n < (((Finset.range n).filter fun i => δ₀ / 2 <
      cavg θ (χ.E ((i + 1 : ℕ) : ℤ)) fun ρ =>
        if δ₀ < var₂ (ρ.map (χ.resc ((i + 1 : ℕ) : ℤ))) ∧
          var₁ (ρ.map (χ.resc ((i + 1 : ℕ) : ℤ))) ≤ η₁ then 1 else 0).card : ℝ) := by
  have hsub : ((Finset.range n).filter (fun i => δ₀ < cavg θ (χ.E (i + 1 : ℕ))
      (fun ρ => if δ₀ < var₁ (ρ.map (χ.resc (i + 1 : ℕ))) ∨
        δ₀ < var₂ (ρ.map (χ.resc (i + 1 : ℕ))) then 1 else 0))) ⊆
      ((Finset.range n).filter fun i => δ₀ / 2 <
        cavg θ (χ.E ((i + 1 : ℕ) : ℤ)) fun ρ =>
          if η₁ < var₁ (ρ.map (χ.resc ((i + 1 : ℕ) : ℤ))) then 1 else 0) ∪
      ((Finset.range n).filter fun i => δ₀ / 2 <
        cavg θ (χ.E ((i + 1 : ℕ) : ℤ)) fun ρ =>
          if δ₀ < var₂ (ρ.map (χ.resc ((i + 1 : ℕ) : ℤ))) ∧
            var₁ (ρ.map (χ.resc ((i + 1 : ℕ) : ℤ))) ≤ η₁ then 1 else 0) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    have hfin := hθ.finiteLabels_E χ ((i + 1 : ℕ) : ℤ)
    have hle := cavg_mono hfin (F := fun ρ =>
      if δ₀ < var₁ (ρ.map (χ.resc (i + 1 : ℕ))) ∨ δ₀ < var₂ (ρ.map (χ.resc (i + 1 : ℕ)))
        then 1 else 0) (G := fun ρ =>
      (if η₁ < var₁ (ρ.map (χ.resc ((i + 1 : ℕ) : ℤ))) then 1 else 0) +
        (if δ₀ < var₂ (ρ.map (χ.resc ((i + 1 : ℕ) : ℤ))) ∧
          var₁ (ρ.map (χ.resc ((i + 1 : ℕ) : ℤ))) ≤ η₁ then 1 else 0))
      (fun _ _ => ind_or_le_add hη₁)
    rw [cavg_add hfin] at hle
    by_contra h
    rcases not_or.1 h with ⟨h1, h2⟩
    have h1' := le_of_not_gt fun h' => h1 ⟨hi.1, h'⟩
    have h2' := le_of_not_gt fun h' => h2 ⟨hi.1, h'⟩
    linarith [hi.2]
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcard' : (((Finset.range n).filter (fun i => δ₀ < cavg θ (χ.E (i + 1 : ℕ))
      (fun ρ => if δ₀ < var₁ (ρ.map (χ.resc (i + 1 : ℕ))) ∨
        δ₀ < var₂ (ρ.map (χ.resc (i + 1 : ℕ))) then 1 else 0))).card : ℝ) ≤
      (((Finset.range n).filter fun i => δ₀ / 2 <
        cavg θ (χ.E ((i + 1 : ℕ) : ℤ)) fun ρ =>
          if η₁ < var₁ (ρ.map (χ.resc ((i + 1 : ℕ) : ℤ))) then 1 else 0).card : ℝ) +
      (((Finset.range n).filter fun i => δ₀ / 2 <
        cavg θ (χ.E ((i + 1 : ℕ) : ℤ)) fun ρ =>
          if δ₀ < var₂ (ρ.map (χ.resc ((i + 1 : ℕ) : ℤ))) ∧
            var₁ (ρ.map (χ.resc ((i + 1 : ℕ) : ℤ))) ≤ η₁ then 1 else 0).card : ℝ) := by
    exact_mod_cast hcard
  by_contra h
  rcases not_or.1 h with ⟨h1, h2⟩
  linarith [le_of_not_gt h1, le_of_not_gt h2]

/-! ### Proposition 1.7 -/

/-- Proposition 1.7 of the source for `d = 2` (lines 1075 to 1188): for every `0 < ε < 1` there
is `δ > 0` such that for `ε⁻¹ ≪ m₂ ≪ k₂ ≪ m₁ ≪ k₁ ≪ n` and every probability measure `θ` carried
by a ball of radius `ε⁻¹` with `H(θ, ℰ_n) / n > ε`, for some `j ∈ {1, 2}` more than `δ n` levels
`q ∈ [1, n]` satisfy `H(θ^{∗k_j}, ℰ_{q+m_j} ∣ ℰ_q ∨ π_{j'}⁻¹ ℰ_{q+m_j}) / m_j > χ_j - ε`. -/
theorem Exps.proposition (χ : Exps) : Prop17 χ := by
  intro ε hε hε1
  obtain ⟨δ₀, hδ₀, N₀, hN₀⟩ := exists_many_levels_var_gt χ ε hε hε1
  have hχ₁ := χ.pos
  have hχ₂ := χ.pos₂
  have hχ₁₂ := χ.lt
  refine ⟨δ₀ / 4, by positivity, ?_⟩
  -- direction `2`: the slice parameter `ε₂ = min (ε / 4) δ₀` and Lemma 3.2
  have hε₂0 : 0 < min (ε / 4) δ₀ := lt_min (by positivity) hδ₀
  have hε₂1 : min (ε / 4) δ₀ < 1 := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨M₂', hM₂'⟩ := χ.slices_two _ hε₂0 hε₂1
  refine ⟨max M₂' (⌈2 * propConst / ε⌉₊ + 1), fun m₂ hm₂ => ?_⟩
  obtain ⟨K₂', hK₂'⟩ := hM₂' m₂ (le_of_max_le_left hm₂)
  refine ⟨max (⌈4 * K₂' / δ₀⌉₊ + K₂') (⌈32 * χ.χ₂ / (δ₀ * ε)⌉₊ + 1), fun k₂ hk₂ => ?_⟩
  obtain ⟨q₂, hq₂⟩ := hK₂' (min ⌊δ₀ * k₂ / 4⌋₊ k₂) (le_min_floor hδ₀ (le_of_max_le_left hk₂))
  -- direction `1`: the threshold `η₁ = min δ₀ (1 / (k₂ + 1))`, the slice parameter
  -- `ε₁ = min (ε / 4) η₁` and Lemma 3.2
  set η₁ : ℝ := min δ₀ (1 / (k₂ + 1)) with hη₁
  have hη₁0 : 0 < η₁ := lt_min hδ₀ (by positivity)
  have hε₁0 : 0 < min (ε / 4) η₁ := lt_min (by positivity) hη₁0
  have hε₁1 : min (ε / 4) η₁ < 1 := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨M₁', hM₁'⟩ := χ.slices_one _ hε₁0 hε₁1
  refine ⟨max M₁' (⌈2 * propConst / ε⌉₊ + 1), fun m₁ hm₁ => ?_⟩
  obtain ⟨K₁', hK₁'⟩ := hM₁' m₁ (le_of_max_le_left hm₁)
  refine ⟨max (⌈4 * K₁' / δ₀⌉₊ + K₁') (⌈32 * χ.χ₂ / (δ₀ * ε)⌉₊ + 1), fun k₁ hk₁ => ?_⟩
  obtain ⟨q₁, hq₁⟩ := hK₁' (min ⌊δ₀ * k₁ / 4⌋₊ k₁) (le_min_floor hδ₀ (le_of_max_le_left hk₁))
  -- the length `n` absorbs the shifts by `q₁` and `q₂`
  refine ⟨max N₀ ⌈4 * (|(q₁ : ℝ)| + |(q₂ : ℝ)|) / δ₀⌉₊, fun n hn θ _ c hθ hent => ?_⟩
  have hθb : BddSupp θ := ⟨c, ε⁻¹, hθ⟩
  have hB := hN₀ n (le_of_max_le_left hn) θ c hθ hent
  have hnq : 4 * (|(q₁ : ℝ)| + |(q₂ : ℝ)|) / δ₀ ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hn)
  have hq₁0 := abs_nonneg (q₁ : ℝ)
  have hq₂0 := abs_nonneg (q₂ : ℝ)
  have hn₁ : 4 * |(q₁ : ℝ)| / δ₀ ≤ n :=
    (div_le_div_of_nonneg_right (by linarith) hδ₀.le).trans hnq
  have hn₂ : 4 * |(q₂ : ℝ)| / δ₀ ≤ n :=
    (div_le_div_of_nonneg_right (by linarith) hδ₀.le).trans hnq
  have hm₁0 : 0 < m₁ := by have := le_of_max_le_right hm₁; omega
  have hm₂0 : 0 < m₂ := by have := le_of_max_le_right hm₂; omega
  rcases χ.levels_split hθb (min_le_left δ₀ _ : η₁ ≤ δ₀) hB with h1 | h2
  · left
    exact Exps.card_levels_gt χ.coordLab_E₂ hθb (fun ρ' => η₁ < var₁ ρ') hχ₁.le hχ₁₂.le hε
      hε₁0.le (min_le_left _ _) hδ₀ (lt_of_ceil_add_one_le (le_of_max_le_right hm₁))
      (lt_of_ceil_add_one_le (le_of_max_le_right hk₁)) (min_floor_le hδ₀ k₁)
      (Exps.slice_one_good hε₁0 hε₁1 (min_le_right _ _) hm₁0 hq₁) hn₁ h1
  · right
    have hkη : ((min ⌊δ₀ * k₂ / 4⌋₊ k₂ : ℕ) : ℝ) * η₁ ≤ 1 := by
      have e1 : ((min ⌊δ₀ * k₂ / 4⌋₊ k₂ : ℕ) : ℝ) ≤ k₂ := by exact_mod_cast min_le_right _ _
      have e2 : η₁ ≤ 1 / (k₂ + 1) := min_le_right _ _
      calc ((min ⌊δ₀ * k₂ / 4⌋₊ k₂ : ℕ) : ℝ) * η₁ ≤ (k₂ : ℝ) * (1 / (k₂ + 1)) :=
            mul_le_mul e1 e2 hη₁0.le (Nat.cast_nonneg _)
        _ ≤ 1 := by
            rw [mul_one_div, div_le_one (by positivity)]
            linarith
    exact Exps.card_levels_gt χ.coordLab_E₁ hθb (fun ρ' => δ₀ < var₂ ρ' ∧ var₁ ρ' ≤ η₁) hχ₂.le
      le_rfl hε hε₂0.le (min_le_left _ _) hδ₀ (lt_of_ceil_add_one_le (le_of_max_le_right hm₂))
      (lt_of_ceil_add_one_le (le_of_max_le_right hk₂)) (min_floor_le hδ₀ k₂)
      (Exps.slice_two_good hε₂0 hε₂1 (min_le_right _ _) hm₂0 hkη hq₂) hn₂ h2

end BoxLike.Rapaport
