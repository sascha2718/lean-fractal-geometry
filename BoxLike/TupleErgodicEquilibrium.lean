module

/-
The existence of an ergodic `s`-equilibrium state for every tuple `𝖠 = (A_1, …, A_N)` of
invertible planar matrices and every `s ≥ 0`, with no irreducibility hypothesis: the assertion of
`sec:affinity_dim` (tex lines 2105 to 2106) that the article attributes to Käenmäki, Ann. Acad.
Sci. Fenn. Math. 29 (2004), Theorems 2.6 and 4.1. No literature premise is used.

The set `𝒦` of invariant `s`-equilibrium states is a non-empty compact subset of the space of
Borel probability measures on `Σ` with the weak-star topology. It is non-empty by
`MatrixTuple.exists_isEquilibriumState`. It is closed since, for an invariant measure,
`eq:eq_state_def` is equivalent to the family of closed conditions
`m P(𝖠, s) ≤ H_μ(𝒫_0^{m-1}) + ∫ log φ^s(A_{𝐢|_m}) dμ(𝐢)`, `m ≥ 1`; this is the upper
semicontinuity of `h_0 + Λ(𝖠, ·, s)`. Mathlib's Krein–Milman theorem needs a real locally convex
space, and the measures form only an `ℝ≥0`-module, so the extreme point of `𝒦` is produced as a
maximiser of the strictly convex weak-star continuous functional
`Q(μ) = ∑_𝐢 2^{-e(𝐢)} μ([𝐢])²`, the sum over all finite words `𝐢` for an injective enumeration
`e` of the words. If such a maximiser `μ` were the combination `t μ_1 + (1 - t) μ_2`,
`0 < t < 1`, of two distinct members of `𝒦`, then `Q(μ) < t Q(μ_1) + (1 - t) Q(μ_2) ≤ Q(μ)`,
because invariant measures are determined by their values on the cylinders. An extreme point
of `𝒦` is ergodic: a non-trivial invariant set `E` splits `μ` into the combination of `μ[·|E]`
and `μ[·|Eᶜ]`, which are distinct and, by `MatrixTuple.IsEquilibriumState.of_mix`, both
equilibrium states.

* `cylinderQuad`, `summable_cylinderQuad`, `continuous_cylinderQuad`: the functional `Q` and its
  weak-star continuity.
* `cylinderQuad_mix_lt`: `Q` is strictly convex along a combination of two measures that differ
  on a cylinder.
* `eq_of_measureReal_cylinder_eq`: invariant probability measures that agree on the cylinders
  `[𝐢]` are equal.
* `eq_of_mix_of_cylinderQuad_le`: if `μ = t μ_1 + (1 - t) μ_2` on the cylinders with
  `0 < t < 1` and `Q(μ_1), Q(μ_2) ≤ Q(μ)`, then `μ_1 = μ_2`.
* `MatrixTuple.energyLim_le_blockEnergy_div`, `MatrixTuple.isEquilibriumState_iff_forall`:
  `Λ(𝖠, μ, s) ≤ m⁻¹ ∫ log φ^s(A_{𝐢|_m}) dμ(𝐢)`, and `eq:eq_state_def` as the family of block
  inequalities.
* `MatrixTuple.IsEquilibriumState.ergodic_of_extreme`: an extreme point of the set of
  equilibrium states is ergodic.
* `MatrixTuple.EquilibriumStates`, `MatrixTuple.isClosed_equilibriumStates`,
  `MatrixTuple.isCompact_equilibriumStates`, `MatrixTuple.equilibriumStates_nonempty`: the set
  `𝒦` is a non-empty compact set.
* `MatrixTuple.exists_ergodic_isEquilibriumState`: an ergodic `s`-equilibrium state exists.
* `System.exists_ergodic_isEquilibriumState`: the specialisation to box-like systems.
-/
public import BoxLike.InvariantMeasures
public import BoxLike.TupleEquilibriumExistence
public import Mathlib.Analysis.Normed.Group.FunctionSeries

@[expose] public section

namespace BoxLike

open Filter MeasureTheory Topology ProbabilityTheory
open scoped ENNReal Matrix.Norms.L2Operator

/-! ### A strictly convex functional of the cylinder masses -/

/-- The weights `2^{-e(c)}` of an injective map `e` into `ℕ` are summable; they are the weights
of the functional `cylinderQuad` (tex lines 2105 to 2106). -/
theorem summable_half_pow_of_injective {β : Type*} {e : β → ℕ} (he : Function.Injective e) :
    Summable fun c => (1 / 2 : ℝ) ^ e c :=
  summable_geometric_two.comp_injective he

section Quad

variable {ι : Type*} [MeasurableSpace ι]

/-- The functional `Q(μ) = ∑_𝐢 2^{-e(𝐢)} μ([𝐢])²` over all finite words `𝐢`, for an enumeration
`e` of the words. For injective `e` it is weak-star continuous and strictly convex on the
invariant probability measures; its maximisers over the set of equilibrium states are extreme
points of that set (tex lines 2105 to 2106). -/
noncomputable def cylinderQuad (e : (Σ n : ℕ, Fin n → ι) → ℕ) (μ : Measure (ℤ → ι)) : ℝ :=
  ∑' c : (Σ n : ℕ, Fin n → ι), (1 / 2 : ℝ) ^ e c * μ.real (cylinder c.2) ^ 2

/-- Every term of `cylinderQuad` for a probability measure is at most its weight `2^{-e(𝐢)}`. -/
theorem cylinderQuad_term_le (e : (Σ n : ℕ, Fin n → ι) → ℕ) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (c : Σ n : ℕ, Fin n → ι) :
    (1 / 2 : ℝ) ^ e c * μ.real (cylinder c.2) ^ 2 ≤ (1 / 2 : ℝ) ^ e c := by
  have hsq : μ.real (cylinder c.2) ^ 2 ≤ 1 := pow_le_one₀ measureReal_nonneg measureReal_le_one
  calc (1 / 2 : ℝ) ^ e c * μ.real (cylinder c.2) ^ 2 ≤ (1 / 2 : ℝ) ^ e c * 1 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (1 / 2 : ℝ) ^ e c := mul_one _

/-- The series defining `cylinderQuad` converges for a probability measure and an injective
enumeration of the words. -/
theorem summable_cylinderQuad {e : (Σ n : ℕ, Fin n → ι) → ℕ} (he : Function.Injective e)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] :
    Summable fun c : (Σ n : ℕ, Fin n → ι) => (1 / 2 : ℝ) ^ e c * μ.real (cylinder c.2) ^ 2 :=
  (summable_half_pow_of_injective he).of_nonneg_of_le (fun _ => by positivity)
    (cylinderQuad_term_le e μ)

/-- Strict convexity of `cylinderQuad`: if `μ = t μ_1 + (1 - t) μ_2` on the cylinders with
`0 < t < 1`, and `μ_1([𝐢]) ≠ μ_2([𝐢])` for some word `𝐢`, then
`Q(μ) < t Q(μ_1) + (1 - t) Q(μ_2)`. The defect of each term is
`2^{-e(𝐢)} t (1 - t) (μ_1([𝐢]) - μ_2([𝐢]))²` (tex lines 2105 to 2106). -/
theorem cylinderQuad_mix_lt {e : (Σ n : ℕ, Fin n → ι) → ℕ} (he : Function.Injective e)
    {μ μ₁ μ₂ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hmix : ∀ {n : ℕ} (w : Fin n → ι),
      μ.real (cylinder w) = t * μ₁.real (cylinder w) + (1 - t) * μ₂.real (cylinder w))
    {n : ℕ} {w : Fin n → ι} (hw : μ₁.real (cylinder w) ≠ μ₂.real (cylinder w)) :
    cylinderQuad e μ < t * cylinderQuad e μ₁ + (1 - t) * cylinderQuad e μ₂ := by
  have ht : 0 < 1 - t := by linarith
  have key : ∀ c : (Σ n : ℕ, Fin n → ι),
      t * ((1 / 2 : ℝ) ^ e c * μ₁.real (cylinder c.2) ^ 2)
        + (1 - t) * ((1 / 2 : ℝ) ^ e c * μ₂.real (cylinder c.2) ^ 2)
        - (1 / 2 : ℝ) ^ e c * μ.real (cylinder c.2) ^ 2
      = (1 / 2 : ℝ) ^ e c * (t * (1 - t))
        * (μ₁.real (cylinder c.2) - μ₂.real (cylinder c.2)) ^ 2 := by
    intro c
    rw [hmix c.2]
    ring
  have hle : ∀ c : (Σ n : ℕ, Fin n → ι), (1 / 2 : ℝ) ^ e c * μ.real (cylinder c.2) ^ 2 ≤
      t * ((1 / 2 : ℝ) ^ e c * μ₁.real (cylinder c.2) ^ 2)
        + (1 - t) * ((1 / 2 : ℝ) ^ e c * μ₂.real (cylinder c.2) ^ 2) := by
    intro c
    have h := key c
    have : 0 ≤ (1 / 2 : ℝ) ^ e c * (t * (1 - t)) *
        (μ₁.real (cylinder c.2) - μ₂.real (cylinder c.2)) ^ 2 := by positivity
    linarith
  have hlt : (1 / 2 : ℝ) ^ e ⟨n, w⟩ * μ.real (cylinder w) ^ 2 <
      t * ((1 / 2 : ℝ) ^ e ⟨n, w⟩ * μ₁.real (cylinder w) ^ 2)
        + (1 - t) * ((1 / 2 : ℝ) ^ e ⟨n, w⟩ * μ₂.real (cylinder w) ^ 2) := by
    have h := key ⟨n, w⟩
    have : (μ₁.real (cylinder w) - μ₂.real (cylinder w)) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (sub_ne_zero.2 hw)
    have : 0 < (1 / 2 : ℝ) ^ e ⟨n, w⟩ * (t * (1 - t)) *
        (μ₁.real (cylinder w) - μ₂.real (cylinder w)) ^ 2 := by positivity
    simp only at h
    linarith
  have hs₁ := summable_cylinderQuad he μ₁
  have hs₂ := summable_cylinderQuad he μ₂
  have hsum := Summable.tsum_lt_tsum hle hlt (summable_cylinderQuad he μ)
    ((hs₁.mul_left t).add (hs₂.mul_left (1 - t)))
  rw [(hs₁.mul_left t).tsum_add (hs₂.mul_left (1 - t)), tsum_mul_left, tsum_mul_left] at hsum
  exact hsum

/-- Two invariant probability measures on `Σ` that agree on every cylinder `[𝐢]` are equal: by
invariance they agree on every translate `σ^{-k}[𝐢]`, and these determine a finite measure. -/
theorem eq_of_measureReal_cylinder_eq [Fintype ι] [MeasurableSingletonClass ι]
    {μ ν : Measure (ℤ → ι)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MeasurePreserving (shift 1) μ μ) (hν : MeasurePreserving (shift 1) ν ν)
    (h : ∀ (n : ℕ) (w : Fin n → ι), μ.real (cylinder w) = ν.real (cylinder w)) : μ = ν := by
  refine measure_ext_of_cylinder fun k n w => ?_
  have hset : {x : ℤ → ι | ∀ j : Fin n, x (k + j) = w j} = shift k ⁻¹' cylinder w := rfl
  rw [hset, ← ofReal_measureReal (measure_ne_top μ _), ← ofReal_measureReal (measure_ne_top ν _),
    measureReal_preimage_shift hμ k (measurableSet_cylinder w),
    measureReal_preimage_shift hν k (measurableSet_cylinder w), h]

/-- A maximiser of `cylinderQuad` is not a non-trivial combination of two distinct invariant
probability measures with smaller values of `Q`: if `μ = t μ_1 + (1 - t) μ_2` on the cylinders
with `0 < t < 1` and `Q(μ_1), Q(μ_2) ≤ Q(μ)`, then `μ_1 = μ_2`, since otherwise
`Q(μ) < t Q(μ_1) + (1 - t) Q(μ_2) ≤ Q(μ)` (tex lines 2105 to 2106). -/
theorem eq_of_mix_of_cylinderQuad_le [Fintype ι] [MeasurableSingletonClass ι]
    {e : (Σ n : ℕ, Fin n → ι) → ℕ} (he : Function.Injective e) {μ μ₁ μ₂ : Measure (ℤ → ι)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hμ₁ : MeasurePreserving (shift 1) μ₁ μ₁) (hμ₂ : MeasurePreserving (shift 1) μ₂ μ₂)
    (hle₁ : cylinderQuad e μ₁ ≤ cylinderQuad e μ) (hle₂ : cylinderQuad e μ₂ ≤ cylinderQuad e μ)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hmix : ∀ {n : ℕ} (w : Fin n → ι),
      μ.real (cylinder w) = t * μ₁.real (cylinder w) + (1 - t) * μ₂.real (cylinder w)) :
    μ₁ = μ₂ := by
  by_contra hne
  obtain ⟨n, w, hw⟩ : ∃ (n : ℕ) (w : Fin n → ι), μ₁.real (cylinder w) ≠ μ₂.real (cylinder w) := by
    by_contra hall
    simp only [not_exists, ne_eq, not_not] at hall
    exact hne (eq_of_measureReal_cylinder_eq hμ₁ hμ₂ hall)
  have hlt := cylinderQuad_mix_lt he ht0 ht1 hmix hw
  have h1 := mul_le_mul_of_nonneg_left hle₁ ht0.le
  have h2 := mul_le_mul_of_nonneg_left hle₂ (by linarith : (0 : ℝ) ≤ 1 - t)
  linarith

end Quad

section QuadContinuity

variable {ι : Type*} [Fintype ι] [TopologicalSpace ι] [DiscreteTopology ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

/-- `cylinderQuad` is weak-star continuous on the Borel probability measures on `Σ`: each term
is a continuous function of the mass of a clopen cylinder, and the terms are dominated by the
summable weights `2^{-e(𝐢)}` (tex lines 2105 to 2106). -/
theorem continuous_cylinderQuad {e : (Σ n : ℕ, Fin n → ι) → ℕ} (he : Function.Injective e) :
    Continuous fun ν : ProbabilityMeasure (ℤ → ι) => cylinderQuad e (ν : Measure (ℤ → ι)) := by
  refine continuous_tsum (u := fun c => (1 / 2 : ℝ) ^ e c)
    (fun c => continuous_const.mul ((continuous_measureReal_cylinder c.2).pow 2))
    (summable_half_pow_of_injective he) fun c ν => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact cylinderQuad_term_le e ν c

end QuadContinuity

namespace MatrixTuple

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {A : ι → Matrix (Fin 2) (Fin 2) ℝ} {s : ℝ}

/-! ### The equilibrium states as the solutions of a family of block inequalities -/

/-- `Λ(𝖠, μ, s) ≤ m⁻¹ ∫ log φ^s(A_{𝐢|_m}) dμ(𝐢)` for an invariant probability measure and every
`m ≥ 1`: by Fekete's lemma the limit in `eq:energy_def` is the infimum of these averages. -/
theorem energyLim_le_blockEnergy_div (hA : ∀ i, (A i).det ≠ 0) (hs : 0 ≤ s)
    {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ)
    {m : ℕ} (hm : m ≠ 0) : energyLim A s μ ≤ blockEnergy A s μ m / m := by
  obtain ⟨c, hc⟩ := exists_le_log_svf_word hA hs
  have hsub := subadditive_integral_futureWord hμ (G := fun w => Real.log (svf s (word A w)))
    (log_svf_word_append_le hA hs)
  have hbdd : BddBelow (Set.range fun n : ℕ =>
      (∫ x, Real.log (svf s (word A (futureWord x n))) ∂μ) / n) := by
    refine ⟨min 0 c, ?_⟩
    rintro _ ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact (min_le_right _ _).trans (le_integral_futureWord_div hc hn)
  rw [tendsto_nhds_unique (tendsto_energyLim hA hμ hs) (hsub.tendsto_lim hbdd),
    blockEnergy_eq_integral]
  exact hsub.lim_le_div hbdd hm

/-- An invariant probability measure is an `s`-equilibrium state, `eq:eq_state_def`, if and only
if `m P(𝖠, s) ≤ H_μ(𝒫_0^{m-1}) + ∫ log φ^s(A_{𝐢|_m}) dμ(𝐢)` for every `m ≥ 1`. The entropy and
the energy are the infima of the averages at level `m`, and `eq:variational` gives the reverse
inequality. Each condition is weak-star closed, which is the upper semicontinuity of
`h_0 + Λ(𝖠, ·, s)` (tex lines 2105 to 2106). -/
theorem isEquilibriumState_iff_forall (hA : ∀ i, (A i).det ≠ 0) (hs : 0 ≤ s)
    {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ) :
    IsEquilibriumState A s μ ↔
      ∀ m : ℕ, 0 < m → m * pressure A s ≤ blockEntropy μ m + blockEnergy A s μ m := by
  constructor
  · intro heq m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have h1 := entropy_le_blockEntropy_div hμ hm.ne'
    have h2 := energyLim_le_blockEnergy_div hA hs hμ hm.ne'
    have hP : pressure A s = entropy μ + energyLim A s μ := heq
    calc (m : ℝ) * pressure A s = m * (entropy μ + energyLim A s μ) := by rw [hP]
      _ ≤ m * (blockEntropy μ m / m + blockEnergy A s μ m / m) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) hm'.le
      _ = blockEntropy μ m + blockEnergy A s μ m := by field_simp
  · intro h
    refine le_antisymm ?_ (entropy_add_energyLim_le_pressure hA hμ hs)
    have hlim := (tendsto_entropy hμ).add (tendsto_energyLim hA hμ hs)
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_gt_atTop 0] with m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    rw [← blockEnergy_eq_integral μ m, ← add_div, le_div_iff₀ hm', mul_comm]
    exact h m hm

/-! ### Extreme equilibrium states are ergodic -/

/-- An extreme point of the set of invariant `s`-equilibrium states is ergodic, the remark of
Feng–Käenmäki recorded at `MatrixTuple.ergodic_of_unique`. Extremality is stated on the
cylinders: whenever `μ([𝐢]) = t μ_1([𝐢]) + (1 - t) μ_2([𝐢])` for all words, with `0 < t < 1` and
invariant equilibrium states `μ_1`, `μ_2`, then `μ_1 = μ_2`. If an invariant set `E` had
`0 < μ(E) < 1`, the conditional measures `μ[·|E]` and `μ[·|Eᶜ]` would be such a pair, both
equilibrium states by `IsEquilibriumState.of_mix`, but `μ[E|E] = 1` and `μ[E|Eᶜ] = 0`
(tex lines 2105 to 2106). -/
theorem IsEquilibriumState.ergodic_of_extreme (hA : ∀ i, (A i).det ≠ 0) (hs : 0 ≤ s)
    {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ)
    (heq : IsEquilibriumState A s μ)
    (hext : ∀ μ₁ μ₂ : Measure (ℤ → ι), IsProbabilityMeasure μ₁ → IsProbabilityMeasure μ₂ →
      MeasurePreserving (shift 1) μ₁ μ₁ → MeasurePreserving (shift 1) μ₂ μ₂ →
      IsEquilibriumState A s μ₁ → IsEquilibriumState A s μ₂ → ∀ t : ℝ, 0 < t → t < 1 →
      (∀ {n : ℕ} (w : Fin n → ι),
        μ.real (cylinder w) = t * μ₁.real (cylinder w) + (1 - t) * μ₂.real (cylinder w)) →
      μ₁ = μ₂) :
    Ergodic (shift 1) μ := by
  refine ⟨hμ, ⟨fun E hE hinv => ?_⟩⟩
  rw [eventuallyEmptyOrUniv_iff', ae_eq_empty, ae_eq_univ]
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hE0, hE1⟩ := hcon
  have hinvc : shift 1 ⁻¹' Eᶜ = Eᶜ := by rw [Set.preimage_compl, hinv]
  have := cond_isProbabilityMeasure (μ := μ) hE0
  have := cond_isProbabilityMeasure (μ := μ) hE1
  have hμ₁ := cond_measurePreserving hμ hE hinv
  have hμ₂ := cond_measurePreserving hμ hE.compl hinvc
  have ht0 : 0 < μ.real E := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hE0 (measure_ne_top _ _)
  have ht0' : 0 < μ.real Eᶜ := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hE1 (measure_ne_top _ _)
  have hc : 1 - μ.real E = μ.real Eᶜ := by rw [measureReal_compl hE, probReal_univ]
  have ht1 : μ.real E < 1 := by linarith
  have hmix : ∀ {n : ℕ} (w : Fin n → ι), μ.real (cylinder w) =
      μ.real E * (μ[|E]).real (cylinder w) + (1 - μ.real E) * (μ[|Eᶜ]).real (cylinder w) :=
    fun w => measureReal_eq_mix_cond hE hE0 hE1 (cylinder w)
  have heq₁ := heq.of_mix hA hs hμ hμ₁ hμ₂ ht0 ht1.le hmix
  have heq₂ := heq.of_mix hA hs hμ hμ₂ hμ₁ (t := 1 - μ.real E) (by linarith) (by linarith)
    (fun w => by rw [hmix w]; ring)
  have h := hext _ _ inferInstance inferInstance hμ₁ hμ₂ heq₁ heq₂ _ ht0 ht1 hmix
  have h1 : μ[E|E] = 1 := cond_apply_self hE0 (measure_ne_top _ _)
  have h2 : μ[E|Eᶜ] = 0 := by
    rw [cond_apply hE.compl, Set.compl_inter_self, measure_empty, mul_zero]
  rw [h] at h1
  rw [h1] at h2
  exact one_ne_zero h2

/-! ### The compact set of equilibrium states -/

variable (A s) in
/-- The set `𝒦` of invariant Borel probability measures on `Σ` that are `s`-equilibrium states
of the tuple, `eq:eq_state_def` (tex lines 2100 to 2104). -/
def EquilibriumStates : Set (ProbabilityMeasure (ℤ → ι)) :=
  {ν | ν ∈ InvariantMeasures ι ∧ IsEquilibriumState A s (ν : Measure (ℤ → ι))}

/-- The set of `s`-equilibrium states is non-empty, by `exists_isEquilibriumState`. -/
theorem equilibriumStates_nonempty [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) (hs : 0 ≤ s) :
    (EquilibriumStates A s).Nonempty := by
  obtain ⟨μ, hp, hμ, heq⟩ := exists_isEquilibriumState hA hs
  exact ⟨⟨μ, hp⟩, hμ, heq⟩

section Compact

variable [TopologicalSpace ι] [DiscreteTopology ι]

/-- The energy `∫ log φ^s(A_{𝐢|_m}) dν(𝐢)` at level `m` is a weak-star continuous function of
`ν`: it is a finite combination of the masses of clopen cylinders. -/
theorem continuous_blockEnergy (m : ℕ) :
    Continuous fun ν : ProbabilityMeasure (ℤ → ι) => blockEnergy A s (ν : Measure (ℤ → ι)) m :=
  continuous_finsetSum _ fun w _ => (continuous_measureReal_cylinder w).mul continuous_const

/-- The set of `s`-equilibrium states is weak-star closed: it is the intersection of the closed
set `ℳ_σ(Σ)` with the closed conditions of `isEquilibriumState_iff_forall`. -/
theorem isClosed_equilibriumStates (hA : ∀ i, (A i).det ≠ 0) (hs : 0 ≤ s) :
    IsClosed (EquilibriumStates A s) := by
  have he : EquilibriumStates A s = InvariantMeasures ι ∩ ⋂ m : ℕ,
      {ν : ProbabilityMeasure (ℤ → ι) | ((m + 1 : ℕ) : ℝ) * pressure A s ≤
        blockEntropy (ν : Measure (ℤ → ι)) (m + 1) + blockEnergy A s ν (m + 1)} := by
    ext ν
    simp only [EquilibriumStates, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hν, heq⟩
      exact ⟨hν, fun m => (isEquilibriumState_iff_forall hA hs hν).1 heq (m + 1) m.succ_pos⟩
    · rintro ⟨hν, h⟩
      refine ⟨hν, (isEquilibriumState_iff_forall hA hs hν).2 fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact h k
  rw [he]
  exact isClosed_invariantMeasures.inter (isClosed_iInter fun m =>
    isClosed_le continuous_const ((continuous_blockEntropy _).add (continuous_blockEnergy _)))

/-- The set of `s`-equilibrium states is weak-star compact, as a closed subset of the compact
space of Borel probability measures on `Σ`. -/
theorem isCompact_equilibriumStates (hA : ∀ i, (A i).det ≠ 0) (hs : 0 ≤ s) :
    IsCompact (EquilibriumStates A s) :=
  (isClosed_equilibriumStates hA hs).isCompact

end Compact

/-! ### Existence of an ergodic equilibrium state -/

/-- **Existence of an ergodic `s`-equilibrium state** for every tuple of invertible planar
matrices and every `s ≥ 0`, reducible or not: the assertion of `sec:affinity_dim` (tex lines 2105
to 2218) that the article attributes to Käenmäki, Theorems 2.6 and 4.1. A maximiser of the
weak-star continuous functional `cylinderQuad` over the non-empty compact set of equilibrium
states is an extreme point of that set (`eq_of_mix_of_cylinderQuad_le`), hence ergodic
(`IsEquilibriumState.ergodic_of_extreme`). -/
theorem exists_ergodic_isEquilibriumState [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0)
    (hs : 0 ≤ s) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
      Ergodic (shift 1) μ ∧ IsEquilibriumState A s μ := by
  let : TopologicalSpace ι := ⊥
  have : DiscreteTopology ι := ⟨rfl⟩
  obtain ⟨e, he⟩ := Countable.exists_injective_nat (Σ n : ℕ, Fin n → ι)
  obtain ⟨P, ⟨hP, heqP⟩, hmax⟩ := (isCompact_equilibriumStates hA hs).exists_isMaxOn
    (equilibriumStates_nonempty hA hs) (continuous_cylinderQuad he).continuousOn
  refine ⟨P, inferInstance, hP, ?_, heqP⟩
  refine heqP.ergodic_of_extreme hA hs hP
    fun μ₁ μ₂ h₁ h₂ hμ₁ hμ₂ heq₁ heq₂ t ht0 ht1 hmix => ?_
  exact eq_of_mix_of_cylinderQuad_le he hμ₁ hμ₂
    (isMaxOn_iff.1 hmax (⟨μ₁, h₁⟩ : ProbabilityMeasure (ℤ → ι)) ⟨hμ₁, heq₁⟩)
    (isMaxOn_iff.1 hmax (⟨μ₂, h₂⟩ : ProbabilityMeasure (ℤ → ι)) ⟨hμ₂, heq₂⟩) ht0 ht1 hmix

end MatrixTuple

/-! ### Box-like systems -/

namespace System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [Nonempty ι]
  (S : System ι) {s : ℝ}

/-- `MatrixTuple.exists_ergodic_isEquilibriumState` for a box-like system, whose linear parts are
invertible by `System.det_mat_ne_zero`: an ergodic `s`-equilibrium state exists for every
`s ≥ 0` (tex lines 2105 to 2106). -/
theorem exists_ergodic_isEquilibriumState (hs : 0 ≤ s) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
      Ergodic (shift 1) μ ∧ S.IsEquilibriumState s μ :=
  MatrixTuple.exists_ergodic_isEquilibriumState S.det_mat_ne_zero hs

end System

end BoxLike
