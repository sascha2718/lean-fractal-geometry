module

/-
Theorem 6.3 of Rapaport (arXiv:2309.03985v1, lines 1594 to 1711 of the source) for the
self-affine measure of a homogeneous diagonal planar system, and the core theorem
(lines 1905 to 1926, the case of Section 6.3 where both coordinate projections have dimension
one), proved against the statement `Prop17` of Proposition 1.7.

For a homogeneous system every linear part `A_φ`, `φ ∈ supp ν^{(n)}`, equals `A^n`, so the
partition `ℒ_{Aff(d)}` of the source is trivial, the set `F` of lines 1624 to 1628 is the whole
support of `ν_n`, and the components `ν^{(n)}_{ℰ'_n ∨ ℒ(φ)}` are the components of `ν_n` for
`ℰ_n`. A component `ρ` is carried by a cell of `ℰ_n`, so `θ' = A^{-n} ρ` is carried by a ball of
radius `1` and Theorem 1.4 applies to `θ'` itself (no further level-`0` components are needed).

* `natCast_mul_eq_add_natCast`: `M n = n + (M - 1) n` for the levels.
* `exists_rescaled_piece`: the rescaling of a component and the bounds of lines 1632 to 1668.
* `eventually_cent_ν_div_le`, `tendsto_cent_ν_div`: Theorem 6.3,
  `H(ν_n, ℰ_{Mn} ∣ ℰ_n) / n → 0` for every natural `M ≥ 2`.
* `dim_eq_of_prop`: the core theorem for one system (lines 1905 to 1926).
* `homogeneousCore_of_prop`, `homogeneousCore_of_prop'`: `HomogeneousCore` from Proposition 1.7.
-/
public import BoxLike.Rapaport.SelfAffine.EntropyIncrease

@[expose] public section

namespace BoxLike.Rapaport

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

universe u

namespace HomSystem

variable {ι : Type*} [Fintype ι] (S : HomSystem ι) {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]

/-- `M n = n + (M - 1) n` for `M ≥ 1`, as integers. -/
theorem natCast_mul_eq_add_natCast {M : ℕ} (hM : 1 ≤ M) (n : ℕ) :
    ((M : ℤ) * (n : ℤ)) = (n : ℤ) + (((M - 1) * n : ℕ) : ℤ) := by
  rw [Nat.cast_mul, Nat.cast_sub hM]
  push_cast
  ring

/-- The rescaling of a component in the proof of Theorem 6.3 (lines 1632 to 1668 of the source,
homogeneous form). A probability measure `ρ` carried by a cell of `ℰ_n` is `A^n θ'` for a
probability measure `θ'` carried by a ball of radius `1`; by the scaling (2.6),
`H(ρ, ℰ_{n+m}) ≤ H(θ', ℰ_m) + log 9`; and since `ρ ∗ A^n μ = A^n (θ' ∗ μ)`,
`H(ρ ∗ A^n μ, ℰ_{n+m} ∣ ℰ_n) ≥ H(θ' ∗ μ, ℰ_m) - 2 log (2 (1 + R) + 2) - 3 log 9`. -/
theorem exists_rescaled_piece {cμ : ℝ × ℝ} {R : ℝ} (hcR : InBall μ cμ R) (hR : 0 ≤ R)
    (n m : ℕ) (ρ : Measure (ℝ × ℝ)) [IsProbabilityMeasure ρ] (b : ℤ × ℤ)
    (hρ : ∀ᵐ z ∂ρ, S.exps.E n z = b) :
    ∃ θ' : Measure (ℝ × ℝ), IsProbabilityMeasure θ' ∧ (∃ z, InBall θ' z 1) ∧
      ent ρ (S.exps.E ((n : ℤ) + m)) ≤ ent θ' (S.exps.E m) + Real.log 9 ∧
      ent (θ' ∗ μ) (S.exps.E m) - (2 * Real.log (2 * (1 + R) + 2) + 3 * Real.log 9) ≤
        cent (ρ ∗ μ.map (S.Apow n)) (S.exps.E ((n : ℤ) + m)) (S.exps.E n) := by
  have hr₁ : S.r₁ ^ n ≠ 0 := pow_ne_zero _ S.r₁_ne_zero
  have hr₂ : S.r₂ ^ n ≠ 0 := pow_ne_zero _ S.r₂_ne_zero
  have hDm : Measurable (diagMap (S.r₁ ^ n)⁻¹ (S.r₂ ^ n)⁻¹) := measurable_diagMap _ _
  have hAm : Measurable (S.Apow n) := S.measurable_Apow n
  obtain ⟨θ', hθ'⟩ : ∃ θ', θ' = ρ.map (diagMap (S.r₁ ^ n)⁻¹ (S.r₂ ^ n)⁻¹) := ⟨_, rfl⟩
  have hθ'p : IsProbabilityMeasure θ' := by rw [hθ']; infer_instance
  have hAD : S.Apow n ∘ diagMap (S.r₁ ^ n)⁻¹ (S.r₂ ^ n)⁻¹ = id := by
    show diagMap _ _ ∘ diagMap _ _ = id
    rw [diagMap_comp_diagMap, mul_inv_cancel₀ hr₁, mul_inv_cancel₀ hr₂, diagMap_one_one]
  have hθ'A : θ'.map (S.Apow n) = ρ := by
    rw [hθ', Measure.map_map hAm hDm, hAD, Measure.map_id]
  -- `θ'` is carried by a ball of radius `1`
  have hrect : InRect ρ (rectCentre (lvl S.exps.χ₁ n) (lvl S.exps.χ₂ n) b)
      ((2 : ℝ) ^ (-lvl S.exps.χ₁ n) / 2) ((2 : ℝ) ^ (-lvl S.exps.χ₂ n) / 2) :=
    inRect_of_ae_rect_eq hρ
  have hs₁ : |(S.r₁ ^ n)⁻¹| * ((2 : ℝ) ^ (-lvl S.exps.χ₁ n) / 2) ≤ 1 := by
    have h := exp_mul_half_mesh_le S.exps.χ₁ (n : ℤ)
    rw [Int.cast_natCast] at h
    rw [abs_inv, S.abs_r₁_pow, neg_mul, Real.exp_neg, inv_inv]
    exact h
  have hs₂ : |(S.r₂ ^ n)⁻¹| * ((2 : ℝ) ^ (-lvl S.exps.χ₂ n) / 2) ≤ 1 := by
    have h := exp_mul_half_mesh_le S.exps.χ₂ (n : ℤ)
    rw [Int.cast_natCast] at h
    rw [abs_inv, S.abs_r₂_pow, neg_mul, Real.exp_neg, inv_inv]
    exact h
  have hz : InBall θ' (diagMap (S.r₁ ^ n)⁻¹ (S.r₂ ^ n)⁻¹
      (rectCentre (lvl S.exps.χ₁ n) (lvl S.exps.χ₂ n) b)) 1 := by
    have h := ((hrect.map_diagMap (S.r₁ ^ n)⁻¹ (S.r₂ ^ n)⁻¹).mono hs₁ hs₂).inBall
    rw [max_self, ← hθ'] at h
    exact h
  have hθ'b : BddSupp θ' := ⟨_, 1, hz⟩
  have hbμ : BddSupp μ := ⟨cμ, R, hcR⟩
  have hθ'Ab : BddSupp (θ'.map (S.Apow n)) := hθ'b.map_diagMap (S.r₁ ^ n) (S.r₂ ^ n)
  refine ⟨θ', hθ'p, ⟨_, hz⟩, ?_, ?_⟩
  · -- the scaling (2.6) for the entropy of `ρ`
    rw [← hθ'A, ent_map hAm (S.exps.measurable_E _)]
    have hfin : FiniteLabels θ' (S.exps.E ((n : ℤ) + m) ∘ S.Apow n) :=
      (finiteLabels_map_iff hAm (S.exps.measurable_E _)).1 (hθ'Ab.finiteLabels_E S.exps _)
    have h := ent_le_ent_add_log_of_fiber_card ((S.exps.measurable_E _).comp hAm)
      (S.exps.measurable_E m) hfin (hθ'b.finiteLabels_E S.exps m)
      (S.fiberBound_E_Apow_symm n m)
    exact_mod_cast h
  · -- the conditional entropy of the piece
    have hconv : ρ ∗ μ.map (S.Apow n) = (θ' ∗ μ).map (S.Apow n) := by
      rw [← hθ'A]
      exact (map_diagMap_conv (S.r₁ ^ n) (S.r₂ ^ n)).symm
    have hσb : BddSupp (θ' ∗ μ) := hθ'b.conv hbμ
    have hσAb : BddSupp ((θ' ∗ μ).map (S.Apow n)) := hσb.map_diagMap (S.r₁ ^ n) (S.r₂ ^ n)
    rw [hconv, cent_map hAm (S.exps.measurable_E _) (S.exps.measurable_E _)]
    have h₂ := S.fiberBound_E_Apow n 0
    have h₃ := S.fiberBound_E_Apow_symm n 0
    rw [add_zero] at h₂ h₃
    have hfin₁ : FiniteLabels (θ' ∗ μ) (S.exps.E ((n : ℤ) + m) ∘ S.Apow n) :=
      (finiteLabels_map_iff hAm (S.exps.measurable_E _)).1 (hσAb.finiteLabels_E S.exps _)
    have hfin₂ : FiniteLabels (θ' ∗ μ) (S.exps.E n ∘ S.Apow n) :=
      (finiteLabels_map_iff hAm (S.exps.measurable_E _)).1 (hσAb.finiteLabels_E S.exps _)
    have hcomp := cent_le_cent_add_of_fiberBound (θ := θ' ∗ μ) (f := S.exps.E m)
      (f' := S.exps.E ((n : ℤ) + m) ∘ S.Apow n) (g := S.exps.E 0) (g' := S.exps.E n ∘ S.Apow n)
      (S.exps.measurable_E _) ((S.exps.measurable_E _).comp hAm) (S.exps.measurable_E _)
      ((S.exps.measurable_E _).comp hAm) (hσb.finiteLabels_E _ _) hfin₁
      (hσb.finiteLabels_E _ _) hfin₂ (S.fiberBound_E_Apow n m) h₂ h₃
    simp only [Nat.cast_ofNat] at hcomp
    have hsub := ent_sub_ent_le_cent (θ := θ' ∗ μ) (S.exps.measurable_E m)
      (S.exps.measurable_E 0) (hσb.finiteLabels_E _ _) (hσb.finiteLabels_E _ _)
    have hE0 := ent_E_zero_le S.exps (θ := θ' ∗ μ) (hz.conv hcR) (by linarith)
    linarith

/-- Theorem 6.3 of the source (lines 1594 to 1711) for a homogeneous system, quantitative form:
for `M ≥ 2` and `ε > 0`, eventually `H(ν_n, ℰ_{Mn} ∣ ℰ_n) / n ≤ ε`. Otherwise the components of
`ν_n` with `H(·, ℰ_{Mn}) > ε n / 2` carry mass at least `ε / (2 C_M)` (Markov), Theorem 1.4 at
the level `(M - 1) n` raises the entropy of the corresponding pieces of
`μ = ∑ ν_n(c) (ν_n)_c ∗ A^n μ` by `δ (M - 1) n`, and concavity contradicts Lemma 4.1 in the form
`H(μ, ℰ_{Mn} ∣ ℰ_n) / n → (M - 1) κ`. -/
theorem eventually_cent_ν_div_le (hprop : Prop17 S.exps) (hμ : S.IsInvariant μ)
    (hb : BddSupp μ) {α : ℝ} (hα : IsExactDim μ α) (hα2 : α < 2)
    (h1 : IsExactDim (μ.map Prod.fst) 1) (h2 : IsExactDim (μ.map Prod.snd) 1) {M : ℕ}
    (hM : 2 ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, cent (S.ν n) (S.exps.E (M * n)) (S.exps.E n) / n ≤ ε := by
  have hM1 : 1 ≤ M := le_trans (by norm_num) hM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hχ₂ : 0 < S.χ₂ := S.χ₁_pos.trans S.χ₁_lt_χ₂
  have hχ₂' : S.exps.χ₂ = S.χ₂ := rfl
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hl9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  -- the constants
  obtain ⟨CM, hCM⟩ : ∃ CM : ℝ, CM = 2 * Real.log 4 + Real.log 9 + 2 * S.χ₂ * M := ⟨_, rfl⟩
  have hCM0 : 0 < CM := by
    have : 0 < 2 * S.χ₂ * M := by positivity
    rw [hCM]
    linarith
  obtain ⟨ε'', hε''⟩ : ∃ ε'' : ℝ, ε'' = min (ε / (4 * M)) (1 / 2) := ⟨_, rfl⟩
  have hε''0 : 0 < ε'' := by rw [hε'']; exact lt_min (by positivity) (by norm_num)
  have hε''1 : ε'' < 1 := by rw [hε'']; exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hε''ε : ε'' ≤ ε / (4 * M) := by rw [hε'']; exact min_le_left _ _
  have hε''inv : (1 : ℝ) ≤ ε''⁻¹ := (one_le_inv₀ hε''0).2 hε''1.le
  -- Theorem 1.4 with `ε''`
  obtain ⟨δ, hδ, N₁, hN₁⟩ := S.entropyIncrease hprop hμ hb hα hα2 h1 h2 ε'' hε''0 hε''1
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = δ * ε / (8 * CM) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hb' := hb
  obtain ⟨cμ, R, hcR⟩ := hb'
  have hR : 0 ≤ R := by
    obtain ⟨z, hz⟩ := hcR.exists
    exact (norm_nonneg _).trans hz
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * Real.log (2 * (1 + R) + 2) + 3 * Real.log 9 := ⟨_, rfl⟩
  -- Lemma 4.1 at the level `(M - 1) n` and its consequence for `ℰ_{Mn} ∣ ℰ_n`
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 (S.tendsto_ent_E_div hμ hb hα h1) η hη0
  obtain ⟨N₃, hN₃⟩ :=
    Metric.tendsto_atTop.1 (S.tendsto_cent_E_mul_div hμ hb hα h1 M hM1) η hη0
  filter_upwards [eventually_ge_atTop (max (max N₁ N₂) (max N₃ (max 1
    (max ⌈4 * Real.log 9 / ε⌉₊ ⌈(Real.log 4 + K) / η⌉₊))))] with n hn
  have hnN₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN₂ : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnN₃ : N₃ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnrest := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hnrest
  have hn9 : ⌈4 * Real.log 9 / ε⌉₊ ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hnrest
  have hnK : ⌈(Real.log 4 + K) / η⌉₊ ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hnrest
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn9' : 4 * Real.log 9 ≤ ε * n := by
    have h := (Nat.le_ceil (4 * Real.log 9 / ε)).trans (show (⌈4 * Real.log 9 / ε⌉₊ : ℝ) ≤ n
      by exact_mod_cast hn9)
    rw [div_le_iff₀ hε] at h
    linarith [mul_comm ε (n : ℝ)]
  have hnK' : Real.log 4 + K ≤ η * n := by
    have h := (Nat.le_ceil ((Real.log 4 + K) / η)).trans
      (show (⌈(Real.log 4 + K) / η⌉₊ : ℝ) ≤ n by exact_mod_cast hnK)
    rw [div_le_iff₀ hη0] at h
    linarith [mul_comm η (n : ℝ)]
  -- the level `m = (M - 1) n`
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = (M - 1) * n := ⟨_, rfl⟩
  have hcast : ((M : ℤ) * (n : ℤ)) = (n : ℤ) + (m : ℤ) := by
    rw [hmdef]
    exact natCast_mul_eq_add_natCast hM1 n
  have hmR : (m : ℝ) = ((M : ℝ) - 1) * n := by
    rw [hmdef, Nat.cast_mul, Nat.cast_sub hM1, Nat.cast_one]
  have hnm : n ≤ m := by
    rw [hmdef]
    exact Nat.le_mul_of_pos_left n (by omega)
  have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le hn0 hnmR
  have hmMn : (m : ℝ) ≤ M * n := by rw [hmR, sub_mul, one_mul]; linarith
  rw [hcast]
  by_contra hcon
  have hcon' := not_le.1 hcon
  -- the upper bound from Lemma 4.1 (lines 1700 to 1703)
  have hup : cent μ (S.exps.E ((n : ℤ) + m)) (S.exps.E n) < m * S.kappa α + η * n := by
    have h := hN₃ n hnN₃
    rw [Real.dist_eq, hcast] at h
    have h' := (abs_lt.1 h).2
    have h'' : cent μ (S.exps.E ((n : ℤ) + m)) (S.exps.E n) / n < (M - 1) * S.kappa α + η := by
      linarith
    rw [div_lt_iff₀ hn0] at h''
    have e : ((M : ℝ) - 1) * S.kappa α * n = m * S.kappa α := by rw [hmR]; ring
    linarith
  -- the components of `ν_n` for `ℰ_n`
  have hνb := S.bddSupp_ν n
  have hEm := S.exps.measurable_E (n : ℤ)
  have hfin : FiniteLabels (S.ν n) (S.exps.E n) := hνb.finiteLabels_E _ _
  have hcavg := cent_E_eq_cavg S.exps hνb (n : ℤ) (m : ℤ)
  -- every component has `H(·, ℰ_{n+m}) ≤ B` (lines 1674 to 1677)
  have hB : ∀ b, (S.ν n) (S.exps.E n ⁻¹' {b}) ≠ 0 →
      ent (comp (S.ν n) (S.exps.E n) b) (S.exps.E ((n : ℤ) + m)) ≤
        2 * Real.log 4 + 2 * S.χ₂ * m + Real.log 9 := by
    intro b _
    have h₁ := ent_comp_E_le_ent_map_resc_add S.exps hνb (n : ℤ) (m : ℤ) b
    obtain ⟨z, hz⟩ := exists_inBall_map_resc_comp S.exps (S.ν n) (n : ℤ) b
    have h₂ := ent_E_le_two_log_four_add S.exps hz (Int.natCast_nonneg m)
    rw [Int.cast_natCast, hχ₂'] at h₂
    linarith
  -- Markov: the good components carry mass at least `ε / (2 C_M)` (lines 1678 to 1682)
  have hcent_lt : ε * n < cent (S.ν n) (S.exps.E ((n : ℤ) + m)) (S.exps.E n) := by
    rw [lt_div_iff₀ hn0] at hcon'
    exact hcon'
  have hcent_le : cent (S.ν n) (S.exps.E ((n : ℤ) + m)) (S.exps.E n) ≤
      2 * Real.log 4 + 2 * S.χ₂ * m + Real.log 9 := by
    rw [hcavg]
    exact cavg_le_of_le hEm hfin hB
  have hεn : 0 < ε * n := by positivity
  have htB : ε * n / 2 < 2 * Real.log 4 + 2 * S.χ₂ * m + Real.log 9 := by linarith
  have hmk := cavg_indicator_ge hEm hfin (F := fun ρ => ent ρ (S.exps.E ((n : ℤ) + m))) htB hB
  rw [← hcavg] at hmk
  have hBv : 2 * Real.log 4 + 2 * S.χ₂ * m + Real.log 9 ≤ n * CM := by
    have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have a₁ : 2 * Real.log 4 + Real.log 9 ≤ n * (2 * Real.log 4 + Real.log 9) :=
      le_mul_of_one_le_left (by linarith) hn1R
    have a₂ : 2 * S.χ₂ * m ≤ 2 * S.χ₂ * (M * n) :=
      mul_le_mul_of_nonneg_left hmMn (by linarith)
    have e : (n : ℝ) * CM = n * (2 * Real.log 4 + Real.log 9) + 2 * S.χ₂ * (M * n) := by
      rw [hCM]
      ring
    linarith
  have hgood_mass : ε / (2 * CM) ≤ cavg (S.ν n) (S.exps.E n)
      (fun ρ => if ε * n / 2 < ent ρ (S.exps.E ((n : ℤ) + m)) then (1 : ℝ) else 0) := by
    refine le_trans ?_ hmk
    have e : ε / (2 * CM) = (ε * n / 2) / (n * CM) := by field_simp
    rw [e]
    exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)
  -- every piece (lines 1647 to 1652 and 1683 to 1689)
  have hpiece : ∀ b ∈ hfin.toFinset, (m : ℝ) * (S.kappa α - η) - Real.log 4 - K +
      m * δ * (if ε * n / 2 < ent (comp (S.ν n) (S.exps.E n) b) (S.exps.E ((n : ℤ) + m))
        then (1 : ℝ) else 0) ≤
      cent (comp (S.ν n) (S.exps.E n) b ∗ μ.map (S.Apow n)) (S.exps.E ((n : ℤ) + m))
        (S.exps.E n) := by
    intro b hbF
    have := comp_isProbabilityMeasure ((FiniteLabels.mem_toFinset hfin).1 hbF)
    obtain ⟨θ', hθ'p, ⟨z, hz⟩, hent, hcent⟩ := S.exists_rescaled_piece hcR hR n m
      (comp (S.ν n) (S.exps.E n) b) b (ae_comp_mem hEm b)
    have := hθ'p
    have hθ'b : BddSupp θ' := ⟨z, 1, hz⟩
    rw [← hK] at hcent
    have hmη : 0 ≤ (m : ℝ) * η := by positivity
    -- the bad bound (A5) with Lemma 4.1
    have hbad : (m : ℝ) * (S.kappa α - η) - Real.log 4 ≤ ent (θ' ∗ μ) (S.exps.E m) := by
      have h4 : ent μ (S.exps.E m) - Real.log 4 ≤ ent (θ' ∗ μ) (S.exps.E m) :=
        ent_conv_ge_sub_log_four' hθ'b hb _ _
      have hA1 := hN₂ m (le_trans hnN₂ hnm)
      rw [Real.dist_eq] at hA1
      have hA1' := (abs_lt.1 hA1).1
      have : S.kappa α - η < ent μ (S.exps.E m) / m := by linarith
      rw [lt_div_iff₀ hm0] at this
      linarith
    by_cases hgood : ε * n / 2 < ent (comp (S.ν n) (S.exps.E n) b) (S.exps.E ((n : ℤ) + m))
    · rw [ite_eq_left hgood, mul_one]
      -- Theorem 1.4 for `θ'` at the level `m`
      have hθ'ent : ε'' < ent θ' (S.exps.E m) / m := by
        rw [lt_div_iff₀ hm0]
        have e₁ : ε'' * m ≤ ε * n / 4 := by
          calc ε'' * m ≤ ε / (4 * M) * m := mul_le_mul_of_nonneg_right hε''ε hm0.le
            _ ≤ ε / (4 * M) * (M * n) := mul_le_mul_of_nonneg_left hmMn (by positivity)
            _ = ε * n / 4 := by field_simp
        linarith
      have hinc := hN₁ m (le_trans hnN₁ hnm) θ' z (hz.mono hε''inv) hθ'ent
      rw [lt_div_iff₀ hm0] at hinc
      linarith
    · rw [ite_eq_right hgood, mul_zero, add_zero]
      linarith
  -- concavity over the decomposition `μ = ∑ ν_n(c) (ν_n)_c ∗ A^n μ` (lines 1632 to 1646)
  have hcompP : ∀ i : hfin.toFinset, IsProbabilityMeasure (comp (S.ν n) (S.exps.E n) i) :=
    fun i => comp_isProbabilityMeasure ((FiniteLabels.mem_toFinset hfin).1 i.2)
  have hdec : μ = ∑ i : hfin.toFinset,
      ENNReal.ofReal ((S.ν n).real (S.exps.E n ⁻¹' {(i : ℤ × ℤ)})) •
        (comp (S.ν n) (S.exps.E n) i ∗ μ.map (S.Apow n)) := by
    calc μ = S.ν n ∗ μ.map (S.Apow n) := S.eq_ν_conv_map_Apow hμ n
      _ = (∑ b ∈ hfin.toFinset, (S.ν n) (S.exps.E n ⁻¹' {b}) • comp (S.ν n) (S.exps.E n) b) ∗
          μ.map (S.Apow n) := congrArg (· ∗ μ.map (S.Apow n)) (eq_sum_comp hEm hfin)
      _ = ∑ b ∈ hfin.toFinset, ((S.ν n) (S.exps.E n ⁻¹' {b}) • comp (S.ν n) (S.exps.E n) b) ∗
          μ.map (S.Apow n) := Rapaport.finset_sum_conv _ _ _
      _ = _ := by
        rw [← Finset.sum_coe_sort]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Measure.conv_smul_left, ofReal_measureReal]
  have hw1 : ∑ b ∈ hfin.toFinset, (S.ν n).real (S.exps.E n ⁻¹' {b}) = 1 :=
    sum_measureReal_fiber hEm _ fun b hb => (FiniteLabels.mem_toFinset hfin).2 hb
  have hconc := sum_cent_le_cent (θ := μ)
    (θs := fun i : hfin.toFinset => comp (S.ν n) (S.exps.E n) i ∗ μ.map (S.Apow n))
    (w := fun i : hfin.toFinset => (S.ν n).real (S.exps.E n ⁻¹' {(i : ℤ × ℤ)}))
    (fun _ => measureReal_nonneg)
    ((Finset.sum_coe_sort hfin.toFinset fun b => (S.ν n).real (S.exps.E n ⁻¹' {b})).trans hw1)
    hdec
    (S.exps.measurable_E ((n : ℤ) + m)) hEm (hb.finiteLabels_E _ _) (hb.finiteLabels_E _ _)
  rw [Finset.sum_coe_sort (f := fun b => (S.ν n).real (S.exps.E n ⁻¹' {b}) *
    cent (comp (S.ν n) (S.exps.E n) b ∗ μ.map (S.Apow n)) (S.exps.E ((n : ℤ) + m))
      (S.exps.E n))] at hconc
  have hlow := Finset.sum_le_sum fun b hb =>
    mul_le_mul_of_nonneg_left (hpiece b hb) (measureReal_nonneg (μ := S.ν n)
      (s := S.exps.E n ⁻¹' {b}))
  have hInd := cavg_eq_sum hfin
    (fun ρ => if ε * n / 2 < ent ρ (S.exps.E ((n : ℤ) + m)) then (1 : ℝ) else 0)
  rw [hInd] at hgood_mass
  have hexp : ∑ b ∈ hfin.toFinset, (S.ν n).real (S.exps.E n ⁻¹' {b}) *
      ((m : ℝ) * (S.kappa α - η) - Real.log 4 - K +
        m * δ * (if ε * n / 2 < ent (comp (S.ν n) (S.exps.E n) b) (S.exps.E ((n : ℤ) + m))
          then (1 : ℝ) else 0)) =
      ((m : ℝ) * (S.kappa α - η) - Real.log 4 - K) *
          ∑ b ∈ hfin.toFinset, (S.ν n).real (S.exps.E n ⁻¹' {b}) +
        m * δ * ∑ b ∈ hfin.toFinset, (S.ν n).real (S.exps.E n ⁻¹' {b}) *
          (if ε * n / 2 < ent (comp (S.ν n) (S.exps.E n) b) (S.exps.E ((n : ℤ) + m))
            then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hexp, hw1, mul_one] at hlow
  -- the contradiction (lines 1691 to 1709)
  have hmδ : 0 ≤ (m : ℝ) * δ := by positivity
  have hgain := mul_le_mul_of_nonneg_left hgood_mass hmδ
  have e : (m : ℝ) * δ * (ε / (2 * CM)) = 4 * (m * η) := by
    rw [hη]
    field_simp
    ring
  have hηnm : η * n ≤ η * m := mul_le_mul_of_nonneg_left hnmR hη0.le
  have hmη : 0 ≤ (m : ℝ) * η := by positivity
  linarith

/-- Theorem 6.3 of the source (lines 1594 to 1711) for a homogeneous system, assuming
Proposition 1.7 as `hprop`: if `dim μ < 2` and both coordinate projections have dimension `1`,
then `H(ν_n, ℰ_{Mn} ∣ ℰ_n) / n → 0` for every natural `M ≥ 2`. -/
theorem tendsto_cent_ν_div (hprop : Prop17 S.exps) (hμ : S.IsInvariant μ) (hb : BddSupp μ)
    {α : ℝ} (hα : IsExactDim μ α) (hα2 : α < 2) (h1 : IsExactDim (μ.map Prod.fst) 1)
    (h2 : IsExactDim (μ.map Prod.snd) 1) {M : ℕ} (hM : 2 ≤ M) :
    Tendsto (fun n : ℕ => cent (S.ν n) (S.exps.E (M * n)) (S.exps.E n) / n) atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun n => lt_of_lt_of_le ha ?_, fun a ha => ?_⟩
  · exact div_nonneg (cent_nonneg (S.exps.measurable_E _) (S.exps.measurable_E _)
      ((S.bddSupp_ν n).finiteLabels_E _ _) ((S.bddSupp_ν n).finiteLabels_E _ _))
      (Nat.cast_nonneg n)
  · filter_upwards [S.eventually_cent_ν_div_le hprop hμ hb hα hα2 h1 h2 hM
      (half_pos ha)] with n hn
    linarith

/-- The core theorem for one system (lines 1905 to 1926 of the source), assuming
Proposition 1.7 as `hprop`: under exponential separation of the first coordinate system,
`H(ν_n, ℰ_{Mn}) = n H(p)` along infinitely many `n` for a fixed `M ≥ 2`; Theorem 6.3 gives
`H(ν_n, ℰ_n) = n H(p) - o(n)` along them, Lemma 6.4 and Lemma 4.1 give `H(ν_n, ℰ_n) / n → κ`,
hence `κ = H(p)` and `dim μ = 1 + (H(p) - χ₁) / χ₂`. -/
theorem dim_eq_of_prop (hprop : Prop17 S.exps) (hμ : S.IsInvariant μ) (hb : BddSupp μ)
    {α : ℝ} (hα : IsExactDim μ α) (hα2 : α < 2) (h1 : IsExactDim (μ.map Prod.fst) 1)
    (h2 : IsExactDim (μ.map Prod.snd) 1) (hsep : S.XSep) :
    α = 1 + (S.H - S.χ₁) / S.χ₂ := by
  obtain ⟨M₀, -, hM₀⟩ := hsep.exists_ent_ν_E_eq
  have hM : 2 ≤ max 2 M₀ := le_max_left _ _
  have hM1 : 1 ≤ max 2 M₀ := le_trans (by norm_num) hM
  have hfreq := hM₀ (max 2 M₀) (le_max_right _ _)
  have hcent := S.tendsto_cent_ν_div hprop hμ hb hα hα2 h1 h2 hM
  obtain ⟨C, hC⟩ := S.abs_ent_sub_ent_ν_le hμ hb
  have hA1 := S.tendsto_ent_E_div hμ hb hα h1
  -- Lemma 6.4: `H(ν_n, ℰ_n) / n → κ`
  have hd : Tendsto (fun n : ℕ => (ent μ (S.exps.E n) - ent (S.ν n) (S.exps.E n)) / n) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (tendsto_const_div_atTop_nhds_zero_nat C)
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (hC n) (Nat.cast_nonneg n)
  have hν : Tendsto (fun n : ℕ => ent (S.ν n) (S.exps.E n) / n) atTop (𝓝 (S.kappa α)) := by
    have h := hA1.sub hd
    rw [sub_zero] at h
    refine h.congr fun n => ?_
    rw [sub_div]
    ring
  have hsum := hν.add hcent
  rw [add_zero] at hsum
  -- along the separated lengths the sum equals `H(p)`
  have hfreq' : ∃ᶠ n : ℕ in atTop, ent (S.ν n) (S.exps.E n) / n +
      cent (S.ν n) (S.exps.E ((max 2 M₀ : ℕ) * n)) (S.exps.E n) / n = S.H := by
    refine (hfreq.and_eventually (eventually_ge_atTop 1)).mono fun n hn => ?_
    obtain ⟨hn, hn1⟩ := hn
    have hn0 : (n : ℝ) ≠ 0 := by
      have : (0 : ℝ) < n := by exact_mod_cast hn1
      exact this.ne'
    rw [natCast_mul_eq_add_natCast hM1 n] at hn ⊢
    rw [← add_div, ← ent_E_sub_eq_cent S.exps (n : ℤ) (Int.natCast_nonneg _), add_sub_cancel,
      hn, mul_div_cancel_left₀ _ hn0]
  have hκH := tendsto_nhds_unique_of_frequently_eq hsum tendsto_const_nhds hfreq'
  -- `κ = H(p)` gives the dimension
  have hχ₂ : 0 < S.χ₂ := S.χ₁_pos.trans S.χ₁_lt_χ₂
  unfold kappa at hκH
  have e : (S.H - S.χ₁) / S.χ₂ = α - 1 := by
    rw [div_eq_iff hχ₂.ne']
    linarith
  linarith

end HomSystem

/-- `HomogeneousCore` (`Rapaport/Defs.lean`) from Proposition 1.7 for every homogeneous system:
the core theorem, Rapaport's lines 1905 to 1926. -/
theorem homogeneousCore_of_prop
    (hprop : ∀ {ι : Type u} [Fintype ι] (S : HomSystem ι), Prop17 S.exps) :
    HomogeneousCore.{u} := by
  unfold HomogeneousCore
  intro ι _ S μ _ hμ hb α hα hα2 h1 h2 hsep
  exact S.dim_eq_of_prop (hprop S) hμ hb hα hα2 h1 h2 hsep

/-- `HomogeneousCore` from Proposition 1.7 for every pair of exponents. -/
theorem homogeneousCore_of_prop' (hprop : ∀ χ : Exps, Prop17 χ) : HomogeneousCore.{u} :=
  homogeneousCore_of_prop fun S => hprop S.exps

end BoxLike.Rapaport
