module

/-
Asymptotic entropies of the self-affine measure of a homogeneous diagonal planar system, for the
proof of Rapaport's theorem (arXiv:2309.03985v1): Section 4 of the source (lines 1190 to 1358,
Lemma 4.1 and Lemmas 1.5 and 1.6) and Lemma 6.4 (lines 1713 to 1772), in the plane, for
`S : HomSystem ι` and its self-affine measure `μ`.

For a homogeneous system every word `u` of length `n` has `diag(|r_{u,1}|, |r_{u,2}|) = A_χ^{-n}`,
so Rapaport's stopping sets `𝒰_n` are the words of length `n` and the decomposition
`μ = ∑_{u ∈ 𝒰_n} p_u φ_u μ` of lines 1241 and 1326 is `eq_sum_map_add_point`.

* `kappa`, `kappa_lt`: `κ = χ₂ dim μ - (χ₂ - χ₁)` (lines 1192 to 1195) and `κ < χ₁ + χ₂` for
  `dim μ < 2` (line 1455).
* General tools: `ent_eq_ent_add_cent_of_factor` (the chain rule (2.3) for a refinement),
  `FiniteLabels.congr_ae`, `cent_le_cent_add_of_fiberBound` (commensurable partitions change
  conditional entropy by a constant), `tendsto_ent_hLabel_lvl_div_of_isExactDim` and
  `tendsto_ent_vLabel_lvl_div_of_isExactDim` (the vendored one-dimensional entropy limit for a
  marginal of dimension one), `Exps.cent_Dsq_E_le` (lines 1231 to 1238).
* The decomposition step: `cent_map_Apow_le` (concavity over the decomposition and translation,
  lines 1240 to 1246 and 1326 to 1331) and `cent_le_cent_of_scaling` (with the scaling (2.6),
  lines 1247 to 1250 and 1332 to 1335).
* Lemma 4.1 (lines 1218 to 1291): `ratio_bounds`, `cent_Dsq_E_ge`, `tendsto_cent_Dsq_E_div` and
  `tendsto_ent_E_div`.
* Lemma 1.6 (lines 1293 to 1338) for `J = {1}` and `J = {2}`: `cent_E₁_ge_ent`, `cent_E₂_ge_ent`,
  `cent_E₁_ge`, `cent_E₂_ge`.
* Lemma 1.5 (lines 1340 to 1357): `cent_E_ge_ent`, `cent_E_ge`; and the consequence
  `tendsto_cent_E_mul_div` of Lemma 4.1 used in Section 6 (lines 1700 to 1703).
* Lemma 6.4 for a homogeneous system (lines 1713 to 1772): `abs_ent_sub_ent_ν_le_log` with the
  explicit constant `2 log (2 ⌈R + ‖c‖⌉ + 3)`, and `abs_ent_sub_ent_ν_le`.
-/
public import BoxLike.Rapaport.SelfAffine.Basic
public import BoxLike.Rapaport.Entropy.Basic
public import BoxLike.Rapaport.Entropy.Rect
public import BoxLike.Rapaport.Entropy.ExactDimEntropy
public import ExactOverlaps.SelfSimilar.ExactDimensionEntropy
public import ExactOverlaps.SelfSimilar.EntropyLevelLimits

@[expose] public section

namespace BoxLike.Rapaport

open MeasureTheory ProbabilityTheory Filter Topology ExactOverlaps.Entropy
open scoped ENNReal

/-! ### General tools -/

section General

variable {X : Type*} [MeasurableSpace X] {θ : Measure X}
variable {L L' M M' : Type*}

/-- The chain rule (2.3) of the source (line 694) for a refinement: if `g = φ ∘ f`, then
`H(θ, f) = H(θ, g) + H(θ, f ∣ g)`. -/
theorem ent_eq_ent_add_cent_of_factor {f : X → L} {g : X → L'} (φ : L → L') (h : g = φ ∘ f) :
    ent θ f = ent θ g + cent θ f g := by
  rw [← ent_pair_eq_add_cent]
  refine (ent_eq_of_injective (φ := fun b => (b, φ b))
    (fun a b hab => (Prod.mk.inj hab).1) ?_).symm
  subst h
  rfl

/-- Labellings which agree almost everywhere have the same labels of positive mass. -/
theorem FiniteLabels.congr_ae {f g : X → L} (hf : FiniteLabels θ f) (h : f =ᵐ[θ] g) :
    FiniteLabels θ g := by
  have e : (fun b : L => θ (g ⁻¹' {b})) = fun b => θ (f ⁻¹' {b}) :=
    funext fun b => measure_congr (h.preimage {b}).symm
  unfold FiniteLabels
  rw [e]
  exact hf

variable [MeasurableSpace L] [MeasurableSingletonClass L] [Countable L]
  [MeasurableSpace L'] [MeasurableSingletonClass L'] [Countable L']
  [MeasurableSpace M] [MeasurableSingletonClass M] [Countable M]
  [MeasurableSpace M'] [MeasurableSingletonClass M'] [Countable M']
  [IsProbabilityMeasure θ]

/-- Commensurability for conditional entropy (lines 724 to 735 of the source, with (2.3)): if
every cell of `f'` meets at most `N₁` cells of `f`, and `g`, `g'` are `N₂`-commensurable, then
`H(θ, f ∣ g) ≤ H(θ, f' ∣ g') + log N₁ + 2 log N₂`. -/
theorem cent_le_cent_add_of_fiberBound {f : X → L} {f' : X → M} {g : X → L'} {g' : X → M'}
    (hf : Measurable f) (hf' : Measurable f') (hg : Measurable g) (hg' : Measurable g')
    (hfinf : FiniteLabels θ f) (hfinf' : FiniteLabels θ f') (hfing : FiniteLabels θ g)
    (hfing' : FiniteLabels θ g') {N₁ N₂ : ℕ} (h₁ : FiberBound f' f N₁)
    (h₂ : FiberBound g' g N₂) (h₃ : FiberBound g g' N₂) :
    cent θ f g ≤ cent θ f' g' + (Real.log N₁ + 2 * Real.log N₂) := by
  have e₁ := cent_le_cent_add_two_log_of_commensurable_cond hf hg hg' hfinf hfing hfing' h₂ h₃
  have e₂ := cent_le_cent_add_log_of_fiber_card hf hf' hg' hfinf hfinf' hfing'
    (FiberBound.of_refine_left (f := fun x => (f' x, g' x)) (f' := f') (φ := Prod.fst) rfl h₁)
  linarith

end General

section Planar

variable {θ : Measure (ℝ × ℝ)} [IsProbabilityMeasure θ]

/-- A bounded planar measure whose first marginal is exact-dimensional of dimension `1` has
`H(θ, π₁⁻¹ 𝒟_{χ n}) / n → χ` (lines 1265 to 1268 and 1312 to 1315 of the source, for
`J = {1}`), from the vendored one-dimensional entropy limit. -/
theorem tendsto_ent_hLabel_lvl_div_of_isExactDim (hθ : BddSupp θ)
    (h1 : IsExactDim (θ.map Prod.fst) 1) {χ : ℝ} (hχ : 0 < χ) :
    Tendsto (fun n : ℕ => ent θ (hLabel (lvl χ n)) / n) atTop (𝓝 χ) := by
  have hlim := normalized_entropy_limit_of_exact_dimension
    (⟨θ.map Prod.fst, inferInstance⟩ : ProbabilityMeasure ℝ) (hasBoundedSupport_fst hθ) (d := 1) h1
  have h := dyadicEntropy_level_div_tendsto _ (hasBoundedSupport_fst hθ) hlim
    (div_pos hχ (Real.log_pos one_lt_two)) (lvl_div_tendsto χ)
  have e : (1 : ℝ) * (χ / Real.log 2) * Real.log 2 = χ := by
    field_simp
  rw [e] at h
  exact h.congr fun n => by rw [ent_hLabel_eq_dyadicEntropy hθ]

/-- A bounded planar measure whose second marginal is exact-dimensional of dimension `1` has
`H(θ, π₂⁻¹ 𝒟_{χ n}) / n → χ` (lines 1312 to 1315 of the source, for `J = {2}`), from the
vendored one-dimensional entropy limit. -/
theorem tendsto_ent_vLabel_lvl_div_of_isExactDim (hθ : BddSupp θ)
    (h2 : IsExactDim (θ.map Prod.snd) 1) {χ : ℝ} (hχ : 0 < χ) :
    Tendsto (fun n : ℕ => ent θ (vLabel (lvl χ n)) / n) atTop (𝓝 χ) := by
  have hlim := normalized_entropy_limit_of_exact_dimension
    (⟨θ.map Prod.snd, inferInstance⟩ : ProbabilityMeasure ℝ) (hasBoundedSupport_snd hθ) (d := 1) h2
  have h := dyadicEntropy_level_div_tendsto _ (hasBoundedSupport_snd hθ) hlim
    (div_pos hχ (Real.log_pos one_lt_two)) (lvl_div_tendsto χ)
  have e : (1 : ℝ) * (χ / Real.log 2) * Real.log 2 = χ := by
    field_simp
  rw [e] at h
  exact h.congr fun n => by rw [ent_vLabel_eq_dyadicEntropy hθ]

/-- The upper bound in the proof of Lemma 4.1 (lines 1231 to 1238 of the source): a cell of
`ℰ_n` meets at most `2 e^{(χ₂ - χ₁) n}` squares of `𝒟²_{χ₂ n}`, so
`H(θ, 𝒟²_{χ₂ n} ∣ ℰ_n) ≤ log 2 + (χ₂ - χ₁) n`. -/
theorem Exps.cent_Dsq_E_le (χ : Exps) (hθ : BddSupp θ) (n : ℕ) :
    cent θ (χ.Dsq n) (χ.E n) ≤ Real.log 2 + (χ.χ₂ - χ.χ₁) * n := by
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  have h := cent_le_log_of_fiber_card (χ.measurable_Dsq n) (χ.measurable_E n)
    (hθ.finiteLabels_Dsq χ n) (hθ.finiteLabels_E χ n) (χ.fiberBound_E_Dsq hn)
  have hx : 0 ≤ (χ.χ₂ - χ.χ₁) * ((n : ℤ) : ℝ) :=
    mul_nonneg (sub_nonneg.2 χ.lt.le) (by positivity)
  have hpos : (0 : ℝ) < ⌊2 * Real.exp ((χ.χ₂ - χ.χ₁) * ((n : ℤ) : ℝ))⌋₊ := by
    have h1 : (1 : ℝ) ≤ 2 * Real.exp ((χ.χ₂ - χ.χ₁) * ((n : ℤ) : ℝ)) := by
      have := Real.one_le_exp hx
      linarith
    exact_mod_cast Nat.floor_pos.2 h1
  have h2 := Real.log_le_log hpos (χ.floor_two_exp_le n)
  rw [Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_exp] at h2
  push_cast at h h2
  linarith

end Planar

/-! ### Homogeneous systems -/

namespace HomSystem

variable {ι : Type*} [Fintype ι] (S : HomSystem ι)

/-- Rapaport's `κ = χ₂ dim μ - (χ₂ - χ₁)` (lines 1192 to 1195 of the source, `d = 2`), for a
measure of dimension `α`. -/
noncomputable def kappa (α : ℝ) : ℝ := S.χ₂ * α - (S.χ₂ - S.χ₁)

/-- `κ < χ₁ + χ₂` when `dim μ < 2`: the gap used in the proof of Theorem 1.4 (line 1455 of the
source). -/
theorem kappa_lt {α : ℝ} (hα : α < 2) : S.kappa α < S.χ₁ + S.χ₂ := by
  have h₁ := S.χ₁_pos
  have h₂ := S.χ₁_lt_χ₂
  unfold kappa
  nlinarith

variable {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]

section Decomposition

variable {L L' M M' : Type*} [MeasurableSpace L] [MeasurableSingletonClass L] [Countable L]
  [MeasurableSpace L'] [MeasurableSingletonClass L'] [Countable L']
  [MeasurableSpace M] [MeasurableSingletonClass M] [Countable M]
  [MeasurableSpace M'] [MeasurableSingletonClass M'] [Countable M']

/-- The decomposition step of Lemmas 4.1, 1.5 and 1.6 (lines 1240 to 1246 and 1326 to 1331 of
the source): from `μ = ∑_u p_u (A^n μ) ∗ δ_{φ_u(0)}`, the concavity of conditional entropy and
the translation comparison (2.5), `H(A^n μ, f ∣ g) ≤ H(μ, f ∣ g) + log N₁ + 2 log N₂` for
labellings `f`, `g` whose translates are `N₁`- and `N₂`-commensurable with them. -/
theorem cent_map_Apow_le (hμ : S.IsInvariant μ) (hb : BddSupp μ) (n : ℕ) {f : ℝ × ℝ → L}
    {g : ℝ × ℝ → L'} (hf : Measurable f) (hg : Measurable g)
    (hfinf : ∀ θ : Measure (ℝ × ℝ), BddSupp θ → FiniteLabels θ f)
    (hfing : ∀ θ : Measure (ℝ × ℝ), BddSupp θ → FiniteLabels θ g) {N₁ N₂ : ℕ}
    (h₁ : ∀ v, FiberBound (f ∘ (· + v)) f N₁) (h₂ : ∀ v, FiberBound (g ∘ (· + v)) g N₂)
    (h₃ : ∀ v, FiberBound g (g ∘ (· + v)) N₂) :
    cent (μ.map (S.Apow n)) f g ≤ cent μ f g + (Real.log N₁ + 2 * Real.log N₂) := by
  have hbτ : BddSupp (μ.map (S.Apow n)) := hb.map_diagMap (S.r₁ ^ n) (S.r₂ ^ n)
  have hconc := sum_cent_le_cent (θ := μ)
    (θs := fun u : Fin n → ι => (μ.map (S.Apow n)).map (· + S.point u)) (w := S.weight)
    (fun u => S.weight_nonneg u) (S.sum_weight n) (S.eq_sum_map_add_point hμ n) hf hg
    (hfinf μ hb) (hfing μ hb)
  have hpiece : ∀ u : Fin n → ι, cent (μ.map (S.Apow n)) f g ≤
      cent ((μ.map (S.Apow n)).map (· + S.point u)) f g +
        (Real.log N₁ + 2 * Real.log N₂) := by
    intro u
    have hT : Measurable (· + S.point u : ℝ × ℝ → ℝ × ℝ) := measurable_add_const _
    have hbT : BddSupp ((μ.map (S.Apow n)).map (· + S.point u)) := hbτ.map_add_const _
    rw [cent_map hT hf hg]
    exact cent_le_cent_add_of_fiberBound hf (hf.comp hT) hg (hg.comp hT) (hfinf _ hbτ)
      ((finiteLabels_map_iff hT hf).1 (hfinf _ hbT)) (hfing _ hbτ)
      ((finiteLabels_map_iff hT hg).1 (hfing _ hbT)) (h₁ _) (h₂ _) (h₃ _)
  calc cent (μ.map (S.Apow n)) f g = ∑ u : Fin n → ι, S.weight u * cent (μ.map (S.Apow n)) f g := by
        rw [← Finset.sum_mul, S.sum_weight, one_mul]
    _ ≤ ∑ u : Fin n → ι, S.weight u * (cent ((μ.map (S.Apow n)).map (· + S.point u)) f g +
          (Real.log N₁ + 2 * Real.log N₂)) :=
        Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hpiece u) (S.weight_nonneg u)
    _ = ∑ u : Fin n → ι, S.weight u * cent ((μ.map (S.Apow n)).map (· + S.point u)) f g +
          (Real.log N₁ + 2 * Real.log N₂) := by
        rw [Finset.sum_congr rfl fun u _ => mul_add (S.weight u) _ _, Finset.sum_add_distrib,
          ← Finset.sum_mul, S.sum_weight, one_mul]
    _ ≤ cent μ f g + (Real.log N₁ + 2 * Real.log N₂) := by linarith

/-- The decomposition step followed by the scaling comparison (2.6) (lines 1247 to 1250 and
1332 to 1335 of the source): if `f ∘ A^n` and `g ∘ A^n` are commensurable with `F` and `G`, then
`H(μ, F ∣ G) ≤ H(μ, f ∣ g) + log N₁ + 2 log N₂ + log N₃ + 2 log N₄`. -/
theorem cent_le_cent_of_scaling (hμ : S.IsInvariant μ) (hb : BddSupp μ) (n : ℕ)
    {f : ℝ × ℝ → L} {g : ℝ × ℝ → L'} {F : ℝ × ℝ → M} {G : ℝ × ℝ → M'} (hf : Measurable f)
    (hg : Measurable g) (hF : Measurable F) (hG : Measurable G)
    (hfinf : ∀ θ : Measure (ℝ × ℝ), BddSupp θ → FiniteLabels θ f)
    (hfing : ∀ θ : Measure (ℝ × ℝ), BddSupp θ → FiniteLabels θ g) (hfinF : FiniteLabels μ F)
    (hfinG : FiniteLabels μ G) {N₁ N₂ N₃ N₄ : ℕ}
    (h₁ : ∀ v, FiberBound (f ∘ (· + v)) f N₁) (h₂ : ∀ v, FiberBound (g ∘ (· + v)) g N₂)
    (h₃ : ∀ v, FiberBound g (g ∘ (· + v)) N₂) (h₄ : FiberBound (f ∘ S.Apow n) F N₃)
    (h₅ : FiberBound (g ∘ S.Apow n) G N₄) (h₆ : FiberBound G (g ∘ S.Apow n) N₄) :
    cent μ F G ≤ cent μ f g + (Real.log N₁ + 2 * Real.log N₂) +
      (Real.log N₃ + 2 * Real.log N₄) := by
  have hA := S.measurable_Apow n
  have hbA : BddSupp (μ.map (S.Apow n)) := hb.map_diagMap (S.r₁ ^ n) (S.r₂ ^ n)
  have e₁ := cent_le_cent_add_of_fiberBound hF (hf.comp hA) hG (hg.comp hA) hfinF
    ((finiteLabels_map_iff hA hf).1 (hfinf _ hbA)) hfinG
    ((finiteLabels_map_iff hA hg).1 (hfing _ hbA)) h₄ h₅ h₆
  rw [← cent_map hA hf hg] at e₁
  have e₂ := S.cent_map_Apow_le hμ hb n hf hg hfinf hfing h₁ h₂ h₃
  linarith

end Decomposition

/-! ### Lemma 4.1 -/

/-- The mesh ratio behind the comparison of `𝒟²_{χ₂ n} ∘ A^n` with `π₁⁻¹ 𝒟_{(χ₂ - χ₁) n}`
(lines 1251 to 1254 of the source): `2^{lvl χ₂ n} |r₁^n| / 2^{lvl (χ₂ - χ₁) n} ∈ [1/2, 2]`. -/
theorem ratio_bounds (n : ℕ) :
    1 / 2 ≤ 2 ^ lvl S.χ₂ n * |S.r₁ ^ n| / 2 ^ lvl (S.χ₂ - S.χ₁) n ∧
      2 ^ lvl S.χ₂ n * |S.r₁ ^ n| / 2 ^ lvl (S.χ₂ - S.χ₁) n ≤ 2 := by
  have hA := two_zpow_lvl_le S.χ₂ n
  have hA' := exp_lt_two_mul_two_zpow_lvl S.χ₂ n
  have hB := two_zpow_lvl_le (S.χ₂ - S.χ₁) n
  have hB' := exp_lt_two_mul_two_zpow_lvl (S.χ₂ - S.χ₁) n
  have hBpos : (0 : ℝ) < 2 ^ lvl (S.χ₂ - S.χ₁) n := zpow_pos two_pos _
  have hrpos : 0 < |S.r₁ ^ n| := by
    rw [S.abs_r₁_pow]
    exact Real.exp_pos _
  have he : Real.exp (S.χ₂ * ((n : ℤ) : ℝ)) * |S.r₁ ^ n| =
      Real.exp ((S.χ₂ - S.χ₁) * ((n : ℤ) : ℝ)) := by
    rw [S.abs_r₁_pow, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have h₁ : 2 ^ lvl S.χ₂ n * |S.r₁ ^ n| ≤ Real.exp ((S.χ₂ - S.χ₁) * ((n : ℤ) : ℝ)) := by
    rw [← he]
    exact mul_le_mul_of_nonneg_right hA hrpos.le
  have h₂ : Real.exp ((S.χ₂ - S.χ₁) * ((n : ℤ) : ℝ)) < 2 * (2 ^ lvl S.χ₂ n * |S.r₁ ^ n|) := by
    rw [← he, ← mul_assoc]
    exact mul_lt_mul_of_pos_right hA' hrpos
  rw [le_div_iff₀ hBpos, div_le_iff₀ hBpos]
  constructor <;> linarith

/-- The lower bound in the proof of Lemma 4.1 (lines 1240 to 1257 of the source): by the
decomposition, the translation comparison and the scaling `𝒟²_{χ₂ n} ∘ A^n ≈ π₁⁻¹ 𝒟_{(χ₂ - χ₁) n}`,
`ℰ_n ∘ A^n ≈ ℰ_0`, `H(μ, 𝒟²_{χ₂ n} ∣ ℰ_n) ≥ H(μ, π₁⁻¹ 𝒟_{(χ₂ - χ₁) n}) - H(μ, ℰ_0) - O(1)`. For
`d = 2` the partition `⋁_{j < d} π_j⁻¹ 𝒟_{(χ_d - χ_j) n}` of line 1256 is `π₁⁻¹ 𝒟_{(χ₂ - χ₁) n}`,
so the correction of lines 1259 to 1276 vanishes. -/
theorem cent_Dsq_E_ge (hμ : S.IsInvariant μ) (hb : BddSupp μ) (n : ℕ) :
    ent μ (hLabel (lvl (S.χ₂ - S.χ₁) n)) - ent μ (S.exps.E 0) -
        ((Real.log 4 + 2 * Real.log 4) + (Real.log 3 + 2 * Real.log 9)) ≤
      cent μ (S.exps.Dsq n) (S.exps.E n) := by
  have hr := S.ratio_bounds n
  have hE₀ := S.fiberBound_E_Apow n 0
  have hE₀' := S.fiberBound_E_Apow_symm n 0
  rw [add_zero] at hE₀ hE₀'
  have key := S.cent_le_cent_of_scaling hμ hb n (F := hLabel (lvl (S.χ₂ - S.χ₁) n))
    (S.exps.measurable_Dsq n) (S.exps.measurable_E n) (measurable_hLabel _)
    (S.exps.measurable_E 0) (fun _ h => h.finiteLabels_Dsq _ _) (fun _ h => h.finiteLabels_E _ _)
    (hb.finiteLabels_hLabel _) (hb.finiteLabels_E _ _)
    (fun v => fiberBound_rect_translate _ _ v) (fun v => fiberBound_rect_translate _ _ v)
    (fun v => fiberBound_rect_translate_symm _ _ v)
    (FiberBound.of_refine_left (φ := Prod.fst) rfl
      (fiberBound_hLabel_diagMap (S.r₂ ^ n) hr.1 hr.2)) hE₀ hE₀'
  have hsub := ent_sub_ent_le_cent (measurable_hLabel (lvl (S.χ₂ - S.χ₁) n))
    (S.exps.measurable_E 0) (hb.finiteLabels_hLabel _) (hb.finiteLabels_E _ _) (θ := μ)
  push_cast at key
  linarith

/-- The first claim in the proof of Lemma 4.1 (lines 1227 to 1282 of the source):
`H(μ, 𝒟²_{χ₂ n} ∣ ℰ_n) / n → χ₂ - χ₁` when `π₁ μ` has dimension `1`. -/
theorem tendsto_cent_Dsq_E_div (hμ : S.IsInvariant μ) (hb : BddSupp μ)
    (h1 : IsExactDim (μ.map Prod.fst) 1) :
    Tendsto (fun n : ℕ => cent μ (S.exps.Dsq n) (S.exps.E n) / n) atTop
      (𝓝 (S.χ₂ - S.χ₁)) := by
  set K : ℝ := (Real.log 4 + 2 * Real.log 4) + (Real.log 3 + 2 * Real.log 9)
  have hlow : Tendsto (fun n : ℕ =>
      (ent μ (hLabel (lvl (S.χ₂ - S.χ₁) n)) - ent μ (S.exps.E 0) - K) / n) atTop
        (𝓝 (S.χ₂ - S.χ₁)) := by
    have h := (tendsto_ent_hLabel_lvl_div_of_isExactDim hb h1 (sub_pos.2 S.χ₁_lt_χ₂)).sub
      (tendsto_const_div_atTop_nhds_zero_nat (ent μ (S.exps.E 0) + K))
    rw [sub_zero] at h
    refine h.congr fun n => ?_
    ring
  have hup : Tendsto (fun n : ℕ => (Real.log 2 + (S.χ₂ - S.χ₁) * n) / n) atTop
      (𝓝 (S.χ₂ - S.χ₁)) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)).add
      (tendsto_const_nhds (x := S.χ₂ - S.χ₁))
    rw [zero_add] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun n => ?_) (fun n => ?_)
  · exact div_le_div_of_nonneg_right (S.cent_Dsq_E_ge hμ hb n) (Nat.cast_nonneg n)
  · exact div_le_div_of_nonneg_right (S.exps.cent_Dsq_E_le hb n) (Nat.cast_nonneg n)

/-- Lemma 4.1 of the source (lines 1218 to 1291), for `d = 2`: if `μ` is exact-dimensional of
dimension `α` and `π₁ μ` has dimension `1`, then `H(μ, ℰ_n) / n → κ`. -/
theorem tendsto_ent_E_div (hμ : S.IsInvariant μ) (hb : BddSupp μ) {α : ℝ}
    (hα : IsExactDim μ α) (h1 : IsExactDim (μ.map Prod.fst) 1) :
    Tendsto (fun n : ℕ => ent μ (S.exps.E n) / n) atTop (𝓝 (S.kappa α)) := by
  have h := (S.exps.tendsto_ent_Dsq_div_of_isExactDim hb hα).sub
    (S.tendsto_cent_Dsq_E_div hμ hb h1)
  have e : α * S.exps.χ₂ - (S.χ₂ - S.χ₁) = S.kappa α := by
    show α * S.χ₂ - (S.χ₂ - S.χ₁) = S.χ₂ * α - (S.χ₂ - S.χ₁)
    ring
  rw [e] at h
  refine h.congr fun n => ?_
  obtain ⟨φ, hφ⟩ := S.exps.E_factor_Dsq (Int.natCast_nonneg n)
  rw [ent_eq_ent_add_cent_of_factor (θ := μ) φ hφ]
  ring

/-- The consequence of Lemma 4.1 used in Section 6 of the source (lines 1700 to 1703): for every
natural `M ≥ 1`, `H(μ, ℰ_{M n} ∣ ℰ_n) / n → (M - 1) κ`. -/
theorem tendsto_cent_E_mul_div (hμ : S.IsInvariant μ) (hb : BddSupp μ) {α : ℝ}
    (hα : IsExactDim μ α) (h1 : IsExactDim (μ.map Prod.fst) 1) (M : ℕ) (hM : 1 ≤ M) :
    Tendsto (fun n : ℕ => cent μ (S.exps.E (M * n)) (S.exps.E n) / n) atTop
      (𝓝 ((M - 1) * S.kappa α)) := by
  have hA := S.tendsto_ent_E_div hμ hb hα h1
  have hMn : Tendsto (fun n : ℕ => M * n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n hM) tendsto_id
  have hAM : Tendsto (fun n : ℕ => ent μ (S.exps.E (M * n)) / n) atTop
      (𝓝 (M * S.kappa α)) := by
    refine ((hA.comp hMn).const_mul (M : ℝ)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    have hM' : (M : ℝ) ≠ 0 := by positivity
    simp only [Function.comp_apply]
    push_cast
    field_simp
  have e : (M : ℝ) * S.kappa α - S.kappa α = (M - 1) * S.kappa α := by ring
  refine (e ▸ hAM.sub hA).congr fun n => ?_
  have hle : (n : ℤ) ≤ M * n :=
    le_mul_of_one_le_left (Int.natCast_nonneg n) (by exact_mod_cast hM)
  obtain ⟨φ, hφ⟩ := S.exps.E_factor hle
  rw [ent_eq_ent_add_cent_of_factor (θ := μ) φ hφ]
  ring

/-! ### Lemmas 1.5 and 1.6 -/

/-- If `a m / m → ℓ`, then for every `ε > 0` eventually `(a m - C) / m ≥ ℓ - ε`. -/
private theorem exists_le_sub_div {a : ℕ → ℝ} {ℓ : ℝ} (h : Tendsto (fun m : ℕ => a m / m) atTop
    (𝓝 ℓ)) (C : ℝ) {ε : ℝ} (hε : 0 < ε) : ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ℓ - ε ≤ (a m - C) / m := by
  have h' := h.sub (tendsto_const_div_atTop_nhds_zero_nat C)
  rw [sub_zero] at h'
  obtain ⟨M, hM⟩ := eventually_atTop.1 (h'.eventually (Ioi_mem_nhds (sub_lt_self ℓ hε)))
  refine ⟨M, fun m hm => ?_⟩
  have h₁ : ℓ - ε < a m / m - C / m := hM m hm
  rw [sub_div]
  exact h₁.le

/-- The decomposition bound in the proof of Lemma 1.6 for `J = {1}` (lines 1326 to 1335 of the
source): `H(μ, π₁⁻¹ ℰ_{n+m} ∣ ℰ_n) ≥ H(μ, π₁⁻¹ ℰ_m) - H(μ, ℰ_0) - O(1)`. -/
theorem cent_E₁_ge_ent (hμ : S.IsInvariant μ) (hb : BddSupp μ) (n m : ℕ) :
    ent μ (S.exps.E₁ m) - ent μ (S.exps.E 0) -
        ((Real.log 2 + 2 * Real.log 4) + (Real.log 3 + 2 * Real.log 9)) ≤
      cent μ (S.exps.E₁ (n + m)) (S.exps.E n) := by
  have hE₀ := S.fiberBound_E_Apow n 0
  have hE₀' := S.fiberBound_E_Apow_symm n 0
  rw [add_zero] at hE₀ hE₀'
  have key := S.cent_le_cent_of_scaling hμ hb n (S.exps.measurable_E₁ _)
    (S.exps.measurable_E n) (S.exps.measurable_E₁ m) (S.exps.measurable_E 0)
    (fun _ h => h.finiteLabels_E₁ _ _) (fun _ h => h.finiteLabels_E _ _)
    (hb.finiteLabels_E₁ _ _) (hb.finiteLabels_E _ _)
    (fun v => fiberBound_hLabel_translate _ v) (fun v => fiberBound_rect_translate _ _ v)
    (fun v => fiberBound_rect_translate_symm _ _ v) (S.fiberBound_E₁_Apow n m) hE₀ hE₀'
  have hsub := ent_sub_ent_le_cent (S.exps.measurable_E₁ m) (S.exps.measurable_E 0)
    (hb.finiteLabels_E₁ _ _) (hb.finiteLabels_E _ _) (θ := μ)
  push_cast at key
  linarith

/-- The decomposition bound in the proof of Lemma 1.6 for `J = {2}` (lines 1326 to 1335 of the
source): `H(μ, π₂⁻¹ ℰ_{n+m} ∣ ℰ_n) ≥ H(μ, π₂⁻¹ ℰ_m) - H(μ, ℰ_0) - O(1)`. -/
theorem cent_E₂_ge_ent (hμ : S.IsInvariant μ) (hb : BddSupp μ) (n m : ℕ) :
    ent μ (S.exps.E₂ m) - ent μ (S.exps.E 0) -
        ((Real.log 2 + 2 * Real.log 4) + (Real.log 3 + 2 * Real.log 9)) ≤
      cent μ (S.exps.E₂ (n + m)) (S.exps.E n) := by
  have hE₀ := S.fiberBound_E_Apow n 0
  have hE₀' := S.fiberBound_E_Apow_symm n 0
  rw [add_zero] at hE₀ hE₀'
  have key := S.cent_le_cent_of_scaling hμ hb n (S.exps.measurable_E₂ _)
    (S.exps.measurable_E n) (S.exps.measurable_E₂ m) (S.exps.measurable_E 0)
    (fun _ h => h.finiteLabels_E₂ _ _) (fun _ h => h.finiteLabels_E _ _)
    (hb.finiteLabels_E₂ _ _) (hb.finiteLabels_E _ _)
    (fun v => fiberBound_vLabel_translate _ v) (fun v => fiberBound_rect_translate _ _ v)
    (fun v => fiberBound_rect_translate_symm _ _ v) (S.fiberBound_E₂_Apow n m) hE₀ hE₀'
  have hsub := ent_sub_ent_le_cent (S.exps.measurable_E₂ m) (S.exps.measurable_E 0)
    (hb.finiteLabels_E₂ _ _) (hb.finiteLabels_E _ _) (θ := μ)
  push_cast at key
  linarith

/-- Lemma 1.6 of the source (lines 1293 to 1338) for `J = {1}`: if `π₁ μ` has dimension `1`,
then for every `ε > 0` there is `M` with `H(μ, π₁⁻¹ ℰ_{n+m} ∣ ℰ_n) / m ≥ χ₁ - ε` for all
`m ≥ M` and all `n`. -/
theorem cent_E₁_ge (hμ : S.IsInvariant μ) (hb : BddSupp μ)
    (h1 : IsExactDim (μ.map Prod.fst) 1) :
    ∀ ε > 0, ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ∀ n : ℕ,
      S.χ₁ - ε ≤ cent μ (S.exps.E₁ (n + m)) (S.exps.E n) / m := by
  intro ε hε
  have h : Tendsto (fun m : ℕ => ent μ (S.exps.E₁ m) / m) atTop (𝓝 S.χ₁) :=
    tendsto_ent_hLabel_lvl_div_of_isExactDim hb h1 S.χ₁_pos
  obtain ⟨M, hM⟩ := exists_le_sub_div h (ent μ (S.exps.E 0) +
    ((Real.log 2 + 2 * Real.log 4) + (Real.log 3 + 2 * Real.log 9))) hε
  refine ⟨M, fun m hm n => (hM m hm).trans ?_⟩
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg m)
  have := S.cent_E₁_ge_ent hμ hb n m
  linarith

/-- Lemma 1.6 of the source (lines 1293 to 1338) for `J = {2}`: if `π₂ μ` has dimension `1`,
then for every `ε > 0` there is `M` with `H(μ, π₂⁻¹ ℰ_{n+m} ∣ ℰ_n) / m ≥ χ₂ - ε` for all
`m ≥ M` and all `n`. -/
theorem cent_E₂_ge (hμ : S.IsInvariant μ) (hb : BddSupp μ)
    (h2 : IsExactDim (μ.map Prod.snd) 1) :
    ∀ ε > 0, ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ∀ n : ℕ,
      S.χ₂ - ε ≤ cent μ (S.exps.E₂ (n + m)) (S.exps.E n) / m := by
  intro ε hε
  have h : Tendsto (fun m : ℕ => ent μ (S.exps.E₂ m) / m) atTop (𝓝 S.χ₂) :=
    tendsto_ent_vLabel_lvl_div_of_isExactDim hb h2 (S.χ₁_pos.trans S.χ₁_lt_χ₂)
  obtain ⟨M, hM⟩ := exists_le_sub_div h (ent μ (S.exps.E 0) +
    ((Real.log 2 + 2 * Real.log 4) + (Real.log 3 + 2 * Real.log 9))) hε
  refine ⟨M, fun m hm n => (hM m hm).trans ?_⟩
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg m)
  have := S.cent_E₂_ge_ent hμ hb n m
  linarith

/-- The decomposition bound in the proof of Lemma 1.5 (lines 1351 to 1354 of the source):
`H(μ, ℰ_{n+m} ∣ ℰ_n) ≥ H(μ, ℰ_m) - H(μ, ℰ_0) - O(1)`. -/
theorem cent_E_ge_ent (hμ : S.IsInvariant μ) (hb : BddSupp μ) (n m : ℕ) :
    ent μ (S.exps.E m) - ent μ (S.exps.E 0) -
        ((Real.log 4 + 2 * Real.log 4) + (Real.log 9 + 2 * Real.log 9)) ≤
      cent μ (S.exps.E (n + m)) (S.exps.E n) := by
  have hE₀ := S.fiberBound_E_Apow n 0
  have hE₀' := S.fiberBound_E_Apow_symm n 0
  rw [add_zero] at hE₀ hE₀'
  have key := S.cent_le_cent_of_scaling hμ hb n (S.exps.measurable_E _)
    (S.exps.measurable_E n) (S.exps.measurable_E m) (S.exps.measurable_E 0)
    (fun _ h => h.finiteLabels_E _ _) (fun _ h => h.finiteLabels_E _ _)
    (hb.finiteLabels_E _ _) (hb.finiteLabels_E _ _)
    (fun v => fiberBound_rect_translate _ _ v) (fun v => fiberBound_rect_translate _ _ v)
    (fun v => fiberBound_rect_translate_symm _ _ v) (S.fiberBound_E_Apow n m) hE₀ hE₀'
  have hsub := ent_sub_ent_le_cent (S.exps.measurable_E m) (S.exps.measurable_E 0)
    (hb.finiteLabels_E _ _) (hb.finiteLabels_E _ _) (θ := μ)
  push_cast at key
  linarith

/-- Lemma 1.5 of the source (lines 1340 to 1357): if `μ` is exact-dimensional of dimension `α`
and `π₁ μ` has dimension `1`, then for every `ε > 0` there is `M` with
`H(μ, ℰ_{n+m} ∣ ℰ_n) / m ≥ κ - ε` for all `m ≥ M` and all `n`. -/
theorem cent_E_ge (hμ : S.IsInvariant μ) (hb : BddSupp μ) {α : ℝ} (hα : IsExactDim μ α)
    (h1 : IsExactDim (μ.map Prod.fst) 1) :
    ∀ ε > 0, ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ∀ n : ℕ,
      S.kappa α - ε ≤ cent μ (S.exps.E (n + m)) (S.exps.E n) / m := by
  intro ε hε
  obtain ⟨M, hM⟩ := exists_le_sub_div (S.tendsto_ent_E_div hμ hb hα h1) (ent μ (S.exps.E 0) +
    ((Real.log 4 + 2 * Real.log 4) + (Real.log 9 + 2 * Real.log 9))) hε
  refine ⟨M, fun m hm n => (hM m hm).trans ?_⟩
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg m)
  have := S.cent_E_ge_ent hμ hb n m
  linarith

/-! ### Lemma 6.4 -/

/-- The clamp `max (-a) (min a x)` of `x` to the interval `[-a, a]`. -/
private noncomputable def clampCoord (a x : ℝ) : ℝ := max (-a) (min a x)

/-- The clamp is continuous. -/
@[fun_prop] private theorem continuous_clampCoord (a : ℝ) : Continuous (clampCoord a) := by
  unfold clampCoord
  fun_prop

/-- The clamp takes values in `[-a, a]`. -/
private theorem abs_clampCoord_le {a : ℝ} (ha : 0 ≤ a) (x : ℝ) : |clampCoord a x| ≤ a := by
  unfold clampCoord
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- The clamp fixes the points of `[-a, a]`. -/
private theorem clampCoord_eq {a x : ℝ} (h : |x| ≤ a) : clampCoord a x = x := by
  unfold clampCoord
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

/-- Lemma 6.4 of the source (lines 1713 to 1772) for a homogeneous system, with an explicit
constant: `μ = ν_n ∗ A^n μ` and `A^n μ` is carried by the rectangle of half-sides
`(R + ‖c‖) |r_j|^n ≤ (R + ‖c‖) 2^{-lvl χ_j n}` about `0`, so the perturbation comparison (2.7)
gives `|H(μ, ℰ_n) - H(ν_n, ℰ_n)| ≤ 2 log (2 ⌈R + ‖c‖⌉ + 3)` for every `n`. -/
theorem abs_ent_sub_ent_ν_le_log (hμ : S.IsInvariant μ) {c : ℝ × ℝ} {R : ℝ}
    (hb : InBall μ c R) (n : ℕ) :
    |ent μ (S.exps.E n) - ent (S.ν n) (S.exps.E n)| ≤
      2 * Real.log (2 * ⌈R + ‖c‖⌉₊ + 3) := by
  set R' := R + ‖c‖
  have hR : 0 ≤ R := by
    obtain ⟨z, hz⟩ := hb.exists
    exact (norm_nonneg _).trans hz
  have hR' : 0 ≤ R' := add_nonneg hR (norm_nonneg c)
  have hb0 : InBall μ 0 R' := by
    have := hb.recentre 0
    rwa [sub_zero] at this
  set a₁ := R' * |S.r₁| ^ n
  set a₂ := R' * |S.r₂| ^ n
  have ha₁ : 0 ≤ a₁ := mul_nonneg hR' (by positivity)
  have ha₂ : 0 ≤ a₂ := mul_nonneg hR' (by positivity)
  have ha₁le : a₁ ≤ R' * 2 ^ (-lvl S.exps.χ₁ n) := by
    refine mul_le_mul_of_nonneg_left ?_ hR'
    rw [← abs_pow, S.abs_r₁_pow]
    have := exp_neg_le_two_zpow_neg_lvl S.χ₁ n
    rwa [Int.cast_natCast] at this
  have ha₂le : a₂ ≤ R' * 2 ^ (-lvl S.exps.χ₂ n) := by
    refine mul_le_mul_of_nonneg_left ?_ hR'
    rw [← abs_pow, S.abs_r₂_pow]
    have := exp_neg_le_two_zpow_neg_lvl S.χ₂ n
    rwa [Int.cast_natCast] at this
  have hτ : ∀ᵐ w ∂(μ.map (S.Apow n)), |w.1| ≤ a₁ ∧ |w.2| ≤ a₂ := by
    have := hb0.ae_abs_sub_Apow_le S n
    simpa only [S.Apow_apply_zero, Prod.fst_zero, Prod.snd_zero, sub_zero] using this
  set P := (S.ν n).prod (μ.map (S.Apow n)) with hPdef
  have hP : ∀ᵐ p ∂P, |p.2.1| ≤ a₁ ∧ |p.2.2| ≤ a₂ :=
    Measure.quasiMeasurePreserving_snd.ae hτ
  have hconv : P.map (fun p => p.1 + p.2) = μ := (S.eq_ν_conv_map_Apow hμ n).symm
  let Fp : (ℝ × ℝ) × (ℝ × ℝ) → ℝ × ℝ := fun p => p.1 + (clampCoord a₁ p.2.1, clampCoord a₂ p.2.2)
  have hFp : Measurable Fp := by
    have : Continuous Fp := by fun_prop
    exact this.measurable
  have hE := S.exps.measurable_E n
  have hae : (S.exps.E n ∘ fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1 + p.2) =ᵐ[P] (S.exps.E n ∘ Fp) := by
    filter_upwards [hP] with p hp
    show S.exps.E n (p.1 + p.2) = S.exps.E n (p.1 + (clampCoord a₁ p.2.1, clampCoord a₂ p.2.2))
    rw [clampCoord_eq hp.1, clampCoord_eq hp.2]
  have e₁ : ent μ (S.exps.E n) = ent P (S.exps.E n ∘ Fp) := by
    rw [← ent_congr_ae hae, ← ent_map measurable_add hE, hconv]
  have hfst : P.map Prod.fst = S.ν n := by
    rw [hPdef, Measure.map_fst_prod, measure_univ, one_smul]
  have e₂ : ent (S.ν n) (S.exps.E n) = ent P (S.exps.E n ∘ Prod.fst) := by
    rw [← ent_map measurable_fst hE, hfst]
  have hfinA : FiniteLabels P (S.exps.E n ∘ fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1 + p.2) := by
    refine (finiteLabels_map_iff measurable_add hE).1 ?_
    rw [hconv]
    exact BddSupp.finiteLabels_E ⟨c, R, hb⟩ _ _
  have hfinF : FiniteLabels P (S.exps.E n ∘ Fp) := hfinA.congr_ae hae
  have hfinG : FiniteLabels P (S.exps.E n ∘ Prod.fst) := by
    refine (finiteLabels_map_iff measurable_fst hE).1 ?_
    rw [hfst]
    exact (S.bddSupp_ν n).finiteLabels_E _ _
  have hpert₁ : ∀ p : (ℝ × ℝ) × (ℝ × ℝ), |(Fp p).1 - (Prod.fst p).1| ≤
      R' * 2 ^ (-lvl S.exps.χ₁ n) := by
    intro p
    show |p.1.1 + clampCoord a₁ p.2.1 - p.1.1| ≤ _
    rw [add_sub_cancel_left]
    exact (abs_clampCoord_le ha₁ _).trans ha₁le
  have hpert₂ : ∀ p : (ℝ × ℝ) × (ℝ × ℝ), |(Fp p).2 - (Prod.fst p).2| ≤
      R' * 2 ^ (-lvl S.exps.χ₂ n) := by
    intro p
    show |p.1.2 + clampCoord a₂ p.2.2 - p.1.2| ≤ _
    rw [add_sub_cancel_left]
    exact (abs_clampCoord_le ha₂ _).trans ha₂le
  have key := abs_ent_sub_ent_le_log_of_commensurable (hE.comp hFp) (hE.comp measurable_fst)
    hfinF hfinG (fiberBound_rect_perturb_symm hpert₁ hpert₂)
    (fiberBound_rect_perturb hpert₁ hpert₂)
  rw [e₁, e₂]
  refine key.trans (le_of_eq ?_)
  have hpos : (0 : ℝ) < 2 * ⌈R'⌉₊ + 3 := by positivity
  push_cast
  rw [Real.log_mul hpos.ne' hpos.ne']
  ring

/-- Lemma 6.4 of the source (lines 1713 to 1772) for a homogeneous system:
`|H(μ, ℰ_n) - H(ν_n, ℰ_n)|` is bounded uniformly in `n`, which gives the limit
`|H(μ, ℰ_n) / n - H(ν_n, ℰ_n) / n| → 0` of the source. -/
theorem abs_ent_sub_ent_ν_le (hμ : S.IsInvariant μ) (hb : BddSupp μ) :
    ∃ C : ℝ, ∀ n : ℕ, |ent μ (S.exps.E n) - ent (S.ν n) (S.exps.E n)| ≤ C := by
  obtain ⟨c, R, hcR⟩ := hb
  exact ⟨_, S.abs_ent_sub_ent_ν_le_log hμ hcR⟩

end HomSystem

end BoxLike.Rapaport
