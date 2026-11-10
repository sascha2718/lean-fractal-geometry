module

/-
The entropy increase theorem for the self-affine measure of a homogeneous diagonal planar system,
Theorem 1.4 of Rapaport (arXiv:2309.03985v1, lines 1434 to 1515 of the source) in the plane,
proved against the statement `Prop17` of his Proposition 1.7 (lines 1075 to 1188), which is
taken as the hypothesis `hprop`.

* The chain rule for the slices (the conditional entropy formula (2.3) used at lines 1472 to
  1477): `Exps.cent_E_eq_cent_E₂_add` and `Exps.cent_E_eq_cent_E₁_add`.
* Convolution lower bounds for a level of `θ^{∗k} ∗ μ` (lines 1465 to 1477):
  `Exps.cent_conv_E_ge_split₂` (levels of `Q_1`), `Exps.cent_conv_E_ge_split₁` (levels of
  `Q_2`), and `Exps.cent_conv_E_ge'` (all levels, through `μ`).
* The averaging step (Lemma 2.1 of the source with the splits of lines 1460 to 1470 and 1491 to
  1500): `Exps.ent_E_div_ge_of_levels`.
* The step through Corollary 5.2 (lines 1502 to 1513): `kv_gain`; the auxiliary
  `div_natCast_le_of_ceil_le`.
* Theorem 1.4: `HomSystem.entropyIncrease`.
-/
public import BoxLike.Rapaport.Entropy.PropositionStatement
public import BoxLike.Rapaport.Entropy.KV
public import BoxLike.Rapaport.Entropy.Conv
public import BoxLike.Rapaport.Entropy.Multiscale
public import BoxLike.Rapaport.SelfAffine.Asymptotics

@[expose] public section

namespace BoxLike.Rapaport

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-! ### The chain rule for slices -/

section ChainRule

/-- The conditional entropy formula (2.3) of the source in the form used at lines 1472 to 1477:
`H(θ, ℰ_{n+m} ∣ ℰ_n) = H(θ, π₂⁻¹ ℰ_{n+m} ∣ ℰ_n) + H(θ, ℰ_{n+m} ∣ ℰ_n ∨ π₂⁻¹ ℰ_{n+m})`. -/
theorem Exps.cent_E_eq_cent_E₂_add (χ : Exps) (θ : Measure (ℝ × ℝ)) (n m : ℤ) :
    cent θ (χ.E (n + m)) (χ.E n) = cent θ (χ.E₂ (n + m)) (χ.E n) +
      cent θ (χ.E (n + m)) (fun z => (χ.E n z, χ.E₂ (n + m) z)) := by
  have h1 : cent θ (χ.E (n + m)) (χ.E n) =
      cent θ (fun z => (χ.E₂ (n + m) z, χ.E (n + m) z)) (χ.E n) :=
    (cent_comp_left_eq_of_injective (φ := fun b : ℤ × ℤ => (b.2, b))
      (fun a b h => (Prod.mk.inj h).2) (χ.E (n + m)) (χ.E n)).symm
  have h2 : cent θ (χ.E (n + m)) (fun z => (χ.E₂ (n + m) z, χ.E n z)) =
      cent θ (χ.E (n + m)) (fun z => (χ.E n z, χ.E₂ (n + m) z)) :=
    cent_comp_right_eq_of_injective (ψ := Prod.swap) Prod.swap_injective (χ.E (n + m))
      (fun z => (χ.E n z, χ.E₂ (n + m) z))
  rw [h1, cent_pair_left, h2]

/-- The conditional entropy formula (2.3) of the source for the second slice direction:
`H(θ, ℰ_{n+m} ∣ ℰ_n) = H(θ, π₁⁻¹ ℰ_{n+m} ∣ ℰ_n) + H(θ, ℰ_{n+m} ∣ ℰ_n ∨ π₁⁻¹ ℰ_{n+m})`. -/
theorem Exps.cent_E_eq_cent_E₁_add (χ : Exps) (θ : Measure (ℝ × ℝ)) (n m : ℤ) :
    cent θ (χ.E (n + m)) (χ.E n) = cent θ (χ.E₁ (n + m)) (χ.E n) +
      cent θ (χ.E (n + m)) (fun z => (χ.E n z, χ.E₁ (n + m) z)) := by
  have h1 : cent θ (χ.E (n + m)) (χ.E n) =
      cent θ (fun z => (χ.E₁ (n + m) z, χ.E (n + m) z)) (χ.E n) :=
    (cent_comp_left_eq_of_injective (φ := fun b : ℤ × ℤ => (b.1, b))
      (fun a b h => (Prod.mk.inj h).2) (χ.E (n + m)) (χ.E n)).symm
  have h2 : cent θ (χ.E (n + m)) (fun z => (χ.E₁ (n + m) z, χ.E n z)) =
      cent θ (χ.E (n + m)) (fun z => (χ.E n z, χ.E₁ (n + m) z)) :=
    cent_comp_right_eq_of_injective (ψ := Prod.swap) Prod.swap_injective (χ.E (n + m))
      (fun z => (χ.E n z, χ.E₁ (n + m) z))
  rw [h1, cent_pair_left, h2]

end ChainRule

/-! ### Convolution lower bounds for a level -/

section Levels

variable {σ τ : Measure (ℝ × ℝ)} [IsProbabilityMeasure σ] [IsProbabilityMeasure τ]

/-- `H(σ ∗ τ, π₂⁻¹ ℰ_{n+m} ∣ ℰ_n) ≥ H(σ, π₂⁻¹ ℰ_{n+m} ∣ ℰ_n) - log 2 - 2 log 4` for bounded
probability measures, the companion of `Exps.cent_conv_E₁_ge` (concavity and (2.5) of the
source). -/
private theorem Exps.cent_conv_E₂_ge_aux (χ : Exps) (hσ : BddSupp σ) (hτ : BddSupp τ)
    (n m : ℤ) :
    cent σ (χ.E₂ (n + m)) (χ.E n) - (Real.log 2 + 2 * Real.log 4) ≤
      cent (σ ∗ τ) (χ.E₂ (n + m)) (χ.E n) := by
  have h := cent_conv_ge_of_fiberBound hσ hτ (f := χ.E₂ (n + m)) (g := χ.E n)
    (χ.measurable_E₂ _) (χ.measurable_E _)
    (χ.ballFinite_E₂ _) (χ.ballFinite_E _) (N := 2) (N' := 4)
    (fun y => fiberBound_vLabel_translate _ y) (fun y => fiberBound_rect_translate _ _ y)
    (fun y => fiberBound_rect_translate_symm _ _ y)
  exact_mod_cast h

/-- The lower bound for a level of `Q_1` (lines 1472 to 1485 of the source, `j = 1`):
`H(σ ∗ τ, ℰ_{n+m} ∣ ℰ_n) ≥ H(τ, π₂⁻¹ ℰ_{n+m} ∣ ℰ_n) + H(σ, ℰ_{n+m} ∣ ℰ_n ∨ π₂⁻¹ ℰ_{n+m}) - O(1)`,
by the chain rule, concavity and (2.5). -/
theorem Exps.cent_conv_E_ge_split₂ (χ : Exps) (hσ : BddSupp σ) (hτ : BddSupp τ) (n m : ℤ) :
    cent τ (χ.E₂ (n + m)) (χ.E n) +
        cent σ (χ.E (n + m)) (fun z => (χ.E n z, χ.E₂ (n + m) z)) -
        ((Real.log 2 + 2 * Real.log 4) + (Real.log 4 + 2 * Real.log 8)) ≤
      cent (σ ∗ τ) (χ.E (n + m)) (χ.E n) := by
  have h1 := χ.cent_conv_E₂_ge_aux hτ hσ n m
  rw [Measure.conv_comm] at h1
  have h2 := χ.cent_conv_E_E₂_ge hσ hτ n m
  rw [χ.cent_E_eq_cent_E₂_add (σ ∗ τ) n m]
  linarith

/-- The lower bound for a level of `Q_2` (lines 1472 to 1485 of the source, `j = 2`):
`H(σ ∗ τ, ℰ_{n+m} ∣ ℰ_n) ≥ H(τ, π₁⁻¹ ℰ_{n+m} ∣ ℰ_n) + H(σ, ℰ_{n+m} ∣ ℰ_n ∨ π₁⁻¹ ℰ_{n+m}) - O(1)`. -/
theorem Exps.cent_conv_E_ge_split₁ (χ : Exps) (hσ : BddSupp σ) (hτ : BddSupp τ) (n m : ℤ) :
    cent τ (χ.E₁ (n + m)) (χ.E n) +
        cent σ (χ.E (n + m)) (fun z => (χ.E n z, χ.E₁ (n + m) z)) -
        ((Real.log 2 + 2 * Real.log 4) + (Real.log 4 + 2 * Real.log 8)) ≤
      cent (σ ∗ τ) (χ.E (n + m)) (χ.E n) := by
  have h1 := χ.cent_conv_E₁_ge hτ hσ n m
  rw [Measure.conv_comm] at h1
  have h2 := χ.cent_conv_E_E₁_ge hσ hτ n m
  rw [χ.cent_E_eq_cent_E₁_add (σ ∗ τ) n m]
  linarith

/-- The lower bound for every level through the second factor (lines 1465 to 1470 of the
source, with Lemma 1.5 at lines 1487 to 1490):
`H(σ ∗ τ, ℰ_{n+m} ∣ ℰ_n) ≥ H(τ, ℰ_{n+m} ∣ ℰ_n) - 3 log 4`. -/
theorem Exps.cent_conv_E_ge' (χ : Exps) (hσ : BddSupp σ) (hτ : BddSupp τ) (n m : ℤ) :
    cent τ (χ.E (n + m)) (χ.E n) - 3 * Real.log 4 ≤ cent (σ ∗ τ) (χ.E (n + m)) (χ.E n) := by
  have h := χ.cent_conv_E_ge hτ hσ n m
  rwa [Measure.conv_comm] at h

end Levels

/-! ### Averaging over the levels -/

/-- Lemma 2.1 of the source with the splits of lines 1460 to 1470 and 1491 to 1500: if every
level `i + 1`, `i < n`, has `H(σ, ℰ_{i+1+m} ∣ ℰ_{i+1}) / m ≥ base` and the levels of a set `Q`
with more than `δ₀ n` elements gain `gain ≥ 0` on top of it, then
`H(σ, ℰ_n) / n ≥ base + gain δ₀ - (c₀ m + H(σ, ℰ_0)) / n`. -/
theorem Exps.ent_E_div_ge_of_levels (χ : Exps) {σ : Measure (ℝ × ℝ)} [IsProbabilityMeasure σ]
    (hσ : BddSupp σ) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) {Q : Finset ℕ}
    (hQ : Q ⊆ Finset.range n) {base gain δ₀ : ℝ} (hgain : 0 ≤ gain)
    (hcard : δ₀ * n < Q.card)
    (hall : ∀ i ∈ Finset.range n,
      base ≤ cent σ (χ.E ((i + 1 : ℕ) + m)) (χ.E (i + 1 : ℕ)) / m)
    (hgood : ∀ i ∈ Q,
      base + gain ≤ cent σ (χ.E ((i + 1 : ℕ) + m)) (χ.E (i + 1 : ℕ)) / m) :
    base + gain * δ₀ - (χ.c₀ * m + ent σ (χ.E 0)) / n ≤ ent σ (χ.E n) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h21 := avg_le_ent_E_div_add χ hσ n hm
  have e1 : ∑ i ∈ Finset.range n,
        (cent σ (χ.E ((i + 1 : ℕ) + m)) (χ.E (i + 1 : ℕ)) / m - base) =
      ∑ i ∈ Finset.range n, cent σ (χ.E ((i + 1 : ℕ) + m)) (χ.E (i + 1 : ℕ)) / m - n * base := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have e2 : ∑ i ∈ Q, (cent σ (χ.E ((i + 1 : ℕ) + m)) (χ.E (i + 1 : ℕ)) / m - base) ≤
      ∑ i ∈ Finset.range n,
        (cent σ (χ.E ((i + 1 : ℕ) + m)) (χ.E (i + 1 : ℕ)) / m - base) :=
    Finset.sum_le_sum_of_subset_of_nonneg hQ fun i hi _ => sub_nonneg.2 (hall i hi)
  have e3 : ∑ i ∈ Q, gain ≤
      ∑ i ∈ Q, (cent σ (χ.E ((i + 1 : ℕ) + m)) (χ.E (i + 1 : ℕ)) / m - base) :=
    Finset.sum_le_sum fun i hi => by linarith [hgood i hi]
  rw [Finset.sum_const, nsmul_eq_mul] at e3
  have e4 : gain * (δ₀ * n) ≤ gain * Q.card := mul_le_mul_of_nonneg_left hcard.le hgain
  have havg : base + gain * δ₀ ≤
      (∑ i ∈ Finset.range n, cent σ (χ.E ((i + 1 : ℕ) + m)) (χ.E (i + 1 : ℕ)) / m) / n := by
    rw [le_div_iff₀ hn0]
    nlinarith
  linarith

/-! ### The step through Corollary 5.2 -/

/-- The arithmetic of lines 1502 to 1513 of the source: from the Kaimanovich–Vershik bound
`s - a ≤ k (b - a) + e` (Corollary 5.2, `s = H(θ^{∗k} ∗ μ, ℰ_n)/n`, `a = H(μ, ℰ_n)/n`,
`b = H(θ ∗ μ, ℰ_n)/n`), the gain `s > κ + δ₁`, a small error `e ≤ δ₁ / 4` and Lemma 4.1 in the
form `|a - κ| < δ₁ / (8K)` with `1 ≤ k ≤ K`, it follows that `b > κ + δ₁ / (4K)`. -/
theorem kv_gain {k K a b s κ δ₁ e : ℝ} (hk : 1 ≤ k) (hkK : k ≤ K) (hδ₁ : 0 < δ₁)
    (hkv : s - a ≤ k * (b - a) + e) (hs : κ + δ₁ < s) (he : e ≤ δ₁ / 4)
    (ha : |a - κ| < δ₁ / (8 * K)) : κ + δ₁ / (4 * K) < b := by
  have hK : 1 ≤ K := hk.trans hkK
  have hK0 : 0 < K := by linarith
  have ha' := abs_lt.1 ha
  have h8 : δ₁ / (8 * K) ≤ δ₁ / 8 :=
    div_le_div_of_nonneg_left hδ₁.le (by norm_num) (by linarith)
  have h1 : δ₁ / 2 < k * (b - a) := by linarith [ha'.2]
  have hba : 0 < b - a := by
    by_contra hcon
    have : k * (b - a) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.1 hcon)
    linarith
  have h2 : δ₁ / 2 < K * (b - a) := lt_of_lt_of_le h1 (mul_le_mul_of_nonneg_right hkK hba.le)
  have hx : 0 < δ₁ / (8 * K) := by positivity
  have e4 : δ₁ / (4 * K) = 2 * (δ₁ / (8 * K)) := by field_simp; ring
  have e2 : δ₁ / 2 = K * (4 * (δ₁ / (8 * K))) := by field_simp; ring
  have h3 : 4 * (δ₁ / (8 * K)) < b - a := by
    rw [e2] at h2
    exact lt_of_mul_lt_mul_left h2 hK0.le
  linarith [ha'.1]

/-- `C / m ≤ x` once `m ≥ ⌈C / x⌉₊` and `m ≥ 1`. -/
theorem div_natCast_le_of_ceil_le {C x : ℝ} {m : ℕ} (hx : 0 < x) (hm : ⌈C / x⌉₊ ≤ m) (hm1 : 1 ≤ m) :
    C / m ≤ x := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have h1 : C / x ≤ m := (Nat.le_ceil _).trans (by exact_mod_cast hm)
  rw [div_le_iff₀ hm0]
  rw [div_le_iff₀ hx] at h1
  linarith [mul_comm x (m : ℝ)]

/-! ### Theorem 1.4 -/

namespace HomSystem

variable {ι : Type*} [Fintype ι] (S : HomSystem ι) {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]

/-- Theorem 1.4 of the source (lines 1434 to 1515) for a homogeneous planar system, assuming
Proposition 1.7 as `hprop`: if `dim μ < 2` and both coordinate projections of `μ` have dimension
`1`, then for every `0 < ε < 1` there is `δ > 0` such that for `n` large, every probability
measure `θ` carried by a ball of radius `ε⁻¹` with `H(θ, ℰ_n) / n > ε` satisfies
`H(θ ∗ μ, ℰ_n) / n > κ + δ`. -/
theorem entropyIncrease (hprop : Prop17 S.exps) (hμ : S.IsInvariant μ) (hb : BddSupp μ)
    {α : ℝ} (hα : IsExactDim μ α) (hα2 : α < 2) (h1 : IsExactDim (μ.map Prod.fst) 1)
    (h2 : IsExactDim (μ.map Prod.snd) 1) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (θ : Measure (ℝ × ℝ)) [IsProbabilityMeasure θ] (c : ℝ × ℝ), InBall θ c ε⁻¹ →
        ε < ent θ (S.exps.E n) / n → S.kappa α + δ < ent (θ ∗ μ) (S.exps.E n) / n := by
  intro ε hε hε1
  have hχ₁ : S.exps.χ₁ = S.χ₁ := rfl
  have hχ₂ : S.exps.χ₂ = S.χ₂ := rfl
  -- the gap `χ₁ + χ₂ - κ = 2 g` (line 1452)
  have hgap := S.kappa_lt hα2
  set κ := S.kappa α with hκ
  set g : ℝ := (S.χ₁ + S.χ₂ - κ) / 2 with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  set ε' : ℝ := min ε g with hε'
  have hε'0 : 0 < ε' := lt_min hε hg0
  have hε'1 : ε' < 1 := lt_of_le_of_lt (min_le_left _ _) hε1
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'g : ε' ≤ g := min_le_right _ _
  -- Proposition 1.7
  obtain ⟨δ₀, hδ₀, hchain⟩ := hprop ε' hε'0 hε'1
  set η : ℝ := g * δ₀ / 8 with hη
  have hη0 : 0 < η := div_pos (mul_pos hg0 hδ₀) (by norm_num)
  -- Lemmas 1.5 and 1.6
  obtain ⟨Ma, hMa⟩ := S.cent_E₁_ge hμ hb h1 η hη0
  obtain ⟨Mb, hMb⟩ := S.cent_E₂_ge hμ hb h2 η hη0
  obtain ⟨Mc, hMc⟩ := S.cent_E_ge hμ hb hα h1 η hη0
  set CQ : ℝ := (Real.log 2 + 2 * Real.log 4) + (Real.log 4 + 2 * Real.log 8) with hCQ
  set C : ℝ := CQ + 3 * Real.log 4 with hC
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hl8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hCQ0 : 0 ≤ CQ := by rw [hCQ]; linarith
  set Mreq : ℕ := max (max Ma Mb) (max Mc (max 1 ⌈C / η⌉₊)) with hMreq
  -- the parameters `m₂ ≪ k₂ ≪ m₁ ≪ k₁`
  obtain ⟨M₂, hM₂⟩ := hchain
  set m₂ : ℕ := max M₂ Mreq with hm₂
  obtain ⟨K₂, hK₂⟩ := hM₂ m₂ (le_max_left _ _)
  set k₂ : ℕ := max K₂ 1 with hk₂
  obtain ⟨M₁, hM₁⟩ := hK₂ k₂ (le_max_left _ _)
  set m₁ : ℕ := max M₁ Mreq with hm₁
  obtain ⟨K₁, hK₁⟩ := hM₁ m₁ (le_max_left _ _)
  set k₁ : ℕ := max K₁ 1 with hk₁
  obtain ⟨N₀, hN₀⟩ := hK₁ k₁ (le_max_left _ _)
  -- the gain
  set δ₁ : ℝ := 4 * η with hδ₁
  have hδ₁0 : 0 < δ₁ := mul_pos (by norm_num) hη0
  set Kk : ℝ := (k₁ : ℝ) + k₂ with hKk
  have hk₁1 : 1 ≤ k₁ := le_max_right _ _
  have hk₂1 : 1 ≤ k₂ := le_max_right _ _
  have hKk1 : (1 : ℝ) ≤ Kk := by
    have : (1 : ℝ) ≤ k₁ := by exact_mod_cast hk₁1
    have : (0 : ℝ) ≤ k₂ := Nat.cast_nonneg _
    linarith
  refine ⟨δ₁ / (4 * Kk), div_pos hδ₁0 (by linarith), ?_⟩
  -- Lemma 4.1
  obtain ⟨NA, hNA⟩ := Metric.tendsto_atTop.1 (S.tendsto_ent_E_div hμ hb hα h1)
    (δ₁ / (8 * Kk)) (div_pos hδ₁0 (by linarith))
  obtain ⟨cμ, Rμ, hcR⟩ := hb
  have hRμ : 0 ≤ Rμ := by
    obtain ⟨z, hz⟩ := hcR.exists
    exact (norm_nonneg _).trans hz
  have hbμ : BddSupp μ := ⟨cμ, Rμ, hcR⟩
  set D : ℕ → ℕ → ℝ := fun k m =>
    S.exps.c₀ * m + 2 * Real.log (2 * ((k : ℝ) * ε⁻¹ + Rμ) + 2) with hD
  set Er : ℕ → ℝ := fun k => 6 * ((k : ℝ) + 1) * Real.log ((k : ℝ) + 2) with hEr
  refine ⟨max (max N₀ NA) (max 1 (max (max ⌈D k₁ m₁ / η⌉₊ ⌈D k₂ m₂ / η⌉₊)
    (max ⌈Er k₁ / η⌉₊ ⌈Er k₂ / η⌉₊))), ?_⟩
  intro n hn θ _ c hθ hent
  have hnN₀ : N₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnNA : NA ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : 1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnrest := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
  have hnD₁ : ⌈D k₁ m₁ / η⌉₊ ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hnrest
  have hnD₂ : ⌈D k₂ m₂ / η⌉₊ ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hnrest
  have hnE₁ : ⌈Er k₁ / η⌉₊ ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hnrest
  have hnE₂ : ⌈Er k₂ / η⌉₊ ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hnrest
  have hθb : BddSupp θ := ⟨c, ε⁻¹, hθ⟩
  -- the common conclusion for `j = 1, 2` (lines 1460 to 1513)
  have key : ∀ (k m : ℕ) (Q : Finset ℕ), 1 ≤ k → Mreq ≤ m → (k : ℝ) ≤ Kk →
      Q ⊆ Finset.range n → δ₀ * n < Q.card →
      (∀ i ∈ Q, κ + g - η - C / m ≤
        cent (convPow θ k ∗ μ) (S.exps.E ((i + 1 : ℕ) + m)) (S.exps.E (i + 1 : ℕ)) / m) →
      D k m / n ≤ η → Er k / n ≤ η →
      κ + δ₁ / (4 * Kk) < ent (θ ∗ μ) (S.exps.E n) / n := by
    intro k m Q hk hm hkK hQ hcard hgood hDn hErn
    have hmc : Mc ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
    have hm1 : 1 ≤ m :=
      le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hm
    have hmC : ⌈C / η⌉₊ ≤ m :=
      le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hCm : C / m ≤ η := div_natCast_le_of_ceil_le hη0 hmC hm1
    have hσb : BddSupp (convPow θ k ∗ μ) := (hθb.convPow k).conv hbμ
    -- every level (Lemma 1.5)
    have hall : ∀ i ∈ Finset.range n, κ - η - C / m ≤
        cent (convPow θ k ∗ μ) (S.exps.E ((i + 1 : ℕ) + m)) (S.exps.E (i + 1 : ℕ)) / m := by
      intro i _
      have hc := S.exps.cent_conv_E_ge' (hθb.convPow k) hbμ ((i + 1 : ℕ) : ℤ) (m : ℤ)
      have hA3 := hMc m hmc (i + 1)
      have h3C : 3 * Real.log 4 / m ≤ C / m := by
        apply div_le_div_of_nonneg_right _ hm0.le
        rw [hC]
        linarith
      have : (cent μ (S.exps.E ((i + 1 : ℕ) + m)) (S.exps.E (i + 1 : ℕ)) - 3 * Real.log 4) / m
          ≤ cent (convPow θ k ∗ μ) (S.exps.E ((i + 1 : ℕ) + m)) (S.exps.E (i + 1 : ℕ)) / m :=
        div_le_div_of_nonneg_right hc hm0.le
      rw [sub_div] at this
      linarith
    -- Lemma 2.1 and the split (lines 1460 to 1500)
    have hlev := S.exps.ent_E_div_ge_of_levels hσb hn1 hm1 hQ hg0.le hcard hall
      (fun i hi => by have := hgood i hi; linarith)
    have hE0 : ent (convPow θ k ∗ μ) (S.exps.E 0) ≤
        2 * Real.log (2 * ((k : ℝ) * ε⁻¹ + Rμ) + 2) :=
      ent_E_zero_le S.exps ((hθ.convPow k).conv hcR) (add_nonneg (by positivity) hRμ)
    have hDn' : (S.exps.c₀ * m + ent (convPow θ k ∗ μ) (S.exps.E 0)) / n ≤ η := by
      refine le_trans ?_ hDn
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      simp only [hD]
      linarith
    have hgδ : g * δ₀ = 8 * η := by rw [hη]; ring
    have hs : κ + δ₁ < ent (convPow θ k ∗ μ) (S.exps.E n) / n := by
      rw [hδ₁]
      linarith
    -- Corollary 5.2 and Lemma 4.1 (lines 1502 to 1513)
    have hkv := S.exps.kv_E_div hθb hbμ n k
    have ha := hNA n hnNA
    rw [Real.dist_eq] at ha
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    exact kv_gain hk' hkK hδ₁0 hkv hs (by rw [hδ₁]; simp only [hEr] at hErn; linarith) ha
  -- Proposition 1.7 at the level `n`
  have hθ' : InBall θ c ε'⁻¹ := hθ.mono (inv_anti₀ hε'0 hε'ε)
  have hent' : ε' < ent θ (S.exps.E n) / n := lt_of_le_of_lt hε'ε hent
  have hκg : S.χ₁ + S.χ₂ = κ + 2 * g := by rw [hg]; ring
  rcases hN₀ n hnN₀ θ c hθ' hent' with hQ₁ | hQ₂
  · -- `j = 1`: the slices in the first coordinate
    refine key k₁ m₁ _ hk₁1 (le_max_right _ _) (by rw [hKk]; simp) (Finset.filter_subset _ _)
      hQ₁ ?_ (div_natCast_le_of_ceil_le hη0 hnD₁ hn1) (div_natCast_le_of_ceil_le hη0 hnE₁ hn1)
    intro i hi
    have hiQ := (Finset.mem_filter.1 hi).2
    rw [Nat.cast_add (i + 1) m₁] at hiQ
    have hm₁b : Mb ≤ m₁ :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
    have hm₁1 : 1 ≤ m₁ := le_trans (le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))) (le_max_right _ _)
    have hm0 : (0 : ℝ) < m₁ := by exact_mod_cast hm₁1
    have hA2 := hMb m₁ hm₁b (i + 1)
    have hsplit := S.exps.cent_conv_E_ge_split₂ (hθb.convPow k₁) hbμ ((i + 1 : ℕ) : ℤ)
      (m₁ : ℤ)
    have hdiv := div_le_div_of_nonneg_right hsplit hm0.le
    rw [sub_div, add_div] at hdiv
    have hCQm : CQ / m₁ ≤ C / m₁ := by
      apply div_le_div_of_nonneg_right _ hm0.le
      rw [hC]
      linarith
    rw [hχ₁] at hiQ
    linarith
  · -- `j = 2`: the slices in the second coordinate
    refine key k₂ m₂ _ hk₂1 (le_max_right _ _) (by rw [hKk]; simp) (Finset.filter_subset _ _)
      hQ₂ ?_ (div_natCast_le_of_ceil_le hη0 hnD₂ hn1) (div_natCast_le_of_ceil_le hη0 hnE₂ hn1)
    intro i hi
    have hiQ := (Finset.mem_filter.1 hi).2
    rw [Nat.cast_add (i + 1) m₂] at hiQ
    have hm₂a : Ma ≤ m₂ :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
    have hm₂1 : 1 ≤ m₂ := le_trans (le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))) (le_max_right _ _)
    have hm0 : (0 : ℝ) < m₂ := by exact_mod_cast hm₂1
    have hA2 := hMa m₂ hm₂a (i + 1)
    have hsplit := S.exps.cent_conv_E_ge_split₁ (hθb.convPow k₂) hbμ ((i + 1 : ℕ) : ℤ)
      (m₂ : ℤ)
    have hdiv := div_le_div_of_nonneg_right hsplit hm0.le
    rw [sub_div, add_div] at hdiv
    have hCQm : CQ / m₂ ≤ C / m₂ := by
      apply div_le_div_of_nonneg_right _ hm0.le
      rw [hC]
      linarith
    rw [hχ₂] at hiQ
    linarith

end HomSystem

end BoxLike.Rapaport
