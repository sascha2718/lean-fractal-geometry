module

/-
`thm:two-block-normalisation` of `sec:normalisation`, assembled, and the consequences stated
after it (tex lines 2230 to 2232) and in tex lines 2243 to 2250. Let `Φ` be a proximal box-like
system with rotations, `Φ^(2)` its second iterate with linear parts `𝖠²`, `β` the grouping map,
`s > 0`, `μ` the `s`-equilibrium state of `𝖠` and `μ^(2) = β_*μ`.

* `System.HasProximalDiagonal.sq`, `System.Proximal.sq_hasProximalDiagonal`: the square of a
  proximal diagonal generator is a proximal diagonal generator of `𝖠²`; hence, by
  `thm:box_like_proximal`, `𝖠²` always contains a proximal diagonal generator.
* `System.sq_irreducible`: `𝖠²` is irreducible.
* `System.map_proj_sq_map_group`: `π^(2)_*μ^(2) = π_*μ`.
* `System.two_block_normalisation`: every conclusion of `thm:two-block-normalisation`: the
  attractor, both matrix types, a proximal diagonal generator, the passage of the strong
  separation, strong open set and projective exponential separation conditions, `μ^(2)` the
  unique ergodic `s`-equilibrium state of `𝖠²`, the scalings of the pressure, the entropy and
  both Lyapunov exponents, and the equality of the projected measures.
* `lyapDim_two_mul`, `System.two_block_normalisation_consequences`: the affinity dimension, the
  Lyapunov dimension of the equilibrium state and both coordinate projections are unchanged,
  and grouping a Bernoulli measure in pairs gives a Bernoulli measure.
* `System.IsEquilibriumState.not_isBernoulli_of_two_block`: the equilibrium state is not
  Bernoulli for `0 < s < 2`, through `𝖠²` and the grouping of Bernoulli measures when `𝖠` has
  no proximal diagonal generator, as in tex lines 2243 to 2250.

The uniqueness and the ergodicity of `μ^(2)` come from `thm:irred_eq_state` for the tuple `𝖠²`,
as in the prose; `𝖠²` has rotations, and the library proves `thm:irred_eq_state` for tuples with
rotations with no literature premise (`System.unique_of_withRotations`,
`System.IsEquilibriumState.ergodic_of_withRotations`). The Gibbs bounds of the last item are
`EquilibriumGibbsStatement`, which the library proves (`equilibriumGibbs`).
-/
public import BoxLike.AffinityDim
public import BoxLike.BernoulliGrouping
public import BoxLike.EquilibriumGibbs
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.General
public import BoxLike.SeparationConditions

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

/-- The Lyapunov dimension of `eq:diml_min2` is unchanged when the entropy and both exponents
are doubled. -/
theorem lyapDim_two_mul (h l1 l2 : ℝ) :
    lyapDim (2 * h) (2 * l1) (2 * l2) = lyapDim h l1 l2 := by
  unfold lyapDim
  have e1 : (2 * h ≤ -(2 * l1)) ↔ h ≤ -l1 := by constructor <;> intro <;> linarith
  have e2 : (2 * h ≤ -(2 * l1) - 2 * l2) ↔ h ≤ -l1 - l2 := by
    constructor <;> intro <;> linarith
  have d1 : -(2 * h) / (2 * l1) = -h / l1 := neg_two_mul_div_two_mul h l1
  have d2 : (2 * h + 2 * l1) / (2 * l2) = (h + l1) / l2 := by
    rw [← mul_add, mul_div_mul_left _ _ two_ne_zero]
  have d3 : -(2 * (2 * h)) / (2 * l1 + 2 * l2) = -(2 * h) / (l1 + l2) := by
    rw [← mul_add, ← mul_neg, mul_div_mul_left _ _ two_ne_zero]
  simp only [e1, e2, d1, d2, d3]

namespace System

variable {ι : Type u} (S : System ι)

variable {S} in
/-- The square of a proximal diagonal generator: if `A_i = diag(a_i, b_i)` with
`|a_i| ≠ |b_i|`, then `A_i A_i = diag(a_i², b_i²)` is a proximal diagonal generator of `𝖠²`. -/
theorem HasProximalDiagonal.sq (h : S.HasProximalDiagonal) : S.sq.HasProximalDiagonal := by
  obtain ⟨i, hi, hab⟩ := h
  refine ⟨(i, i), ?_, ?_⟩
  · change S.o i + S.o i = 0
    rw [hi, add_zero]
  · change |S.a i * S.ratio (i, S.o i)| ≠ |S.b i * S.ratio (i, S.o i + 1)|
    rw [hi, zero_add, ratio_zero, ratio_one, abs_mul, abs_mul]
    exact fun he => hab ((mul_self_inj (abs_nonneg _) (abs_nonneg _)).1 he)

variable {S} in
/-- `thm:two-block-normalisation`: `𝖠²` contains a proximal diagonal generator. By
`thm:box_like_proximal` either `𝖠²` already contains one or `𝖠` contains one, whose square
belongs to `𝖠²`. -/
theorem Proximal.sq_hasProximalDiagonal (h : S.Proximal) : S.sq.HasProximalDiagonal :=
  h.hasProximalDiagonal_or_sq.elim HasProximalDiagonal.sq id

/-- `𝖠²` is irreducible, as in the proof of `thm:two-block-normalisation`: a common invariant
line of `𝖠²` would be an axis, since `𝖠²` contains a proximal diagonal generator, whereas an
anti-diagonal generator of `𝖠²` exchanges the axes. -/
theorem sq_irreducible (hrot : S.WithRotations) (hprox : S.Proximal) : S.sq.Irreducible :=
  irreducible_of_hasProximalDiagonal (S.sq_withRotations hrot) hprox.sq_hasProximalDiagonal

/-- `π^(2)_*μ^(2) = π_*μ`, as in `thm:two-block-normalisation`: `π^(2) ∘ β = π`. -/
theorem map_proj_sq_map_group [Finite ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure (ℤ → ι)) : (μ.map group).map S.sq.proj = μ.map S.proj := by
  obtain ⟨r', M', hS'⟩ := S.sq.exists_bounds
  have hcomp : S.sq.proj ∘ group = S.proj := funext fun x => S.proj_sq_group x
  rw [Measure.map_map hS'.measurable_proj measurable_group, hcomp]

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] {s : ℝ}

/-- `thm:two-block-normalisation`. Let `Φ` be a proximal box-like system with rotations, let
`s > 0`, let `μ` be the `s`-equilibrium state of `𝖠` and `μ^(2) = β_*μ`. Then `Φ^(2)` has
attractor `X`; `𝖠²` contains both matrix types and a proximal diagonal generator; the strong
separation, strong open set and projective exponential separation conditions pass from `Φ`
to `Φ^(2)`; `μ^(2)` is an invariant probability measure and the unique ergodic
`s`-equilibrium state of `𝖠²`; `P(𝖠², t) = 2 P(𝖠, t)` for `t ≥ 0`,
`h_0(μ^(2)) = 2 h_0(μ)`, `λ_i(𝖠², μ^(2)) = 2 λ_i(𝖠, μ)` for `i ∈ {1, 2}`, and
`π^(2)_*μ^(2) = π_*μ`. Uniqueness and ergodicity come from `thm:irred_eq_state` for the tuple
`𝖠²`, which has rotations (`System.unique_of_withRotations`,
`System.IsEquilibriumState.ergodic_of_withRotations`); no literature premise is used. -/
theorem two_block_normalisation (hrot : S.WithRotations)
    (hprox : S.Proximal) (hs0 : 0 < s) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState s μ) :
    S.sq.attractor = S.attractor ∧
    S.sq.WithRotations ∧ S.sq.HasProximalDiagonal ∧
    (S.StrongSeparation → S.sq.StrongSeparation) ∧
    (S.StrongOpenSet → S.sq.StrongOpenSet) ∧
    (S.ProjExpSeparation → S.sq.ProjExpSeparation) ∧
    (IsProbabilityMeasure (μ.map group) ∧
      MeasurePreserving (shift 1) (μ.map group) (μ.map group) ∧
      S.sq.IsEquilibriumState s (μ.map group) ∧
      (∀ ν : Measure (ℤ → ι × ι), IsProbabilityMeasure ν → MeasurePreserving (shift 1) ν ν →
        S.sq.IsEquilibriumState s ν → ν = μ.map group) ∧
      Ergodic (shift 1) (μ.map group)) ∧
    (∀ t : ℝ, 0 ≤ t → S.sq.pressure t = 2 * S.pressure t) ∧
    entropy (μ.map group) = 2 * entropy μ ∧
    S.sq.lyapunov₁ (μ.map group) = 2 * S.lyapunov₁ μ ∧
    S.sq.lyapunov₂ (μ.map group) = 2 * S.lyapunov₂ μ ∧
    (μ.map group).map S.sq.proj = μ.map S.proj := by
  have := nonempty_of_measure μ
  have hinv₂ := measurePreserving_shift_map_group hinv
  have heq₂ := heq.map_group hinv hs0.le
  have hrot₂ := S.sq_withRotations hrot
  refine ⟨S.attractor_sq, hrot₂, hprox.sq_hasProximalDiagonal,
    StrongSeparation.sq S, StrongOpenSet.sq S, ProjExpSeparation.sq S,
    ⟨inferInstance, hinv₂, heq₂, fun ν hν hνinv hνeq => ?_,
      heq₂.ergodic_of_withRotations hrot₂ hs0 hinv₂⟩,
    fun t ht => S.pressure_sq ht, entropy_map_group hinv,
    S.lyapunov₁_sq_map_group (S.tendsto_lyapunov₁ hinv),
    S.lyapunov₂_sq_map_group (S.tendsto_lyapunov₂ hinv), S.map_proj_sq_map_group μ⟩
  exact S.sq.unique_of_withRotations hrot₂ hs0 ν (μ.map group) hνinv hinv₂ hνeq heq₂

/-- The consequences of `thm:two-block-normalisation` stated after it (tex lines 2230 to 2232)
and in tex lines 2248 to 2249: the affinity dimension of `𝖠²` is that of `𝖠`, the Lyapunov
dimension of `μ^(2)` for `𝖠²` is that of `μ` for `𝖠`, both coordinate projections of the
projected measure are unchanged, and `μ^(2)` is Bernoulli when `μ` is, so that `μ` is not
Bernoulli when `μ^(2)` is not. -/
theorem two_block_normalisation_consequences [Nonempty ι] (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ) :
    S.sq.dimaff = S.dimaff ∧
    lyapDim (entropy (μ.map group)) (S.sq.lyapunov₁ (μ.map group))
        (S.sq.lyapunov₂ (μ.map group)) =
      lyapDim (entropy μ) (S.lyapunov₁ μ) (S.lyapunov₂ μ) ∧
    (∀ c : ZMod 2, S.sq.marginal c (μ.map group) = S.marginal c μ) ∧
    (IsBernoulli μ → IsBernoulli (μ.map group)) := by
  refine ⟨S.sq.dimaff_eq S.dimaff_nonneg ?_, ?_, fun c => S.marginal_sq_map_group c μ,
    IsBernoulli.map_group⟩
  · rw [S.pressure_sq S.dimaff_nonneg, S.pressure_dimaff, mul_zero]
  · rw [entropy_map_group hinv, S.lyapunov₁_sq_map_group (S.tendsto_lyapunov₁ hinv),
      S.lyapunov₂_sq_map_group (S.tendsto_lyapunov₂ hinv), lyapDim_two_mul]

variable {S} in
/-- Tex lines 2362 to 2369, by the route of the prose: for a proximal box-like tuple with
rotations and `0 < s < 2` the `s`-equilibrium state `μ` is not Bernoulli. If `𝖠` contains a
proximal diagonal generator, the Gibbs bounds of `μ` exclude a Bernoulli measure; otherwise the
same argument applies to `𝖠²` and `μ^(2)` by `thm:two-block-normalisation`, and since grouping
a Bernoulli measure in pairs gives a Bernoulli measure, `μ` is not Bernoulli either. The Gibbs
bounds come from `EquilibriumGibbsStatement`, which the library proves (`equilibriumGibbs`). -/
theorem IsEquilibriumState.not_isBernoulli_of_two_block (hfk : EquilibriumGibbsStatement.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal) (hs0 : 0 < s) (hs2 : s < 2)
    {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) : ¬ IsBernoulli μ := by
  rcases hprox.hasProximalDiagonal_or_sq with h | h
  · exact S.not_isBernoulli hrot h.proximal hs0 hs2 (hfk S hrot hs0 hs2 μ hinv heq)
  · have := nonempty_of_measure μ
    refine not_isBernoulli_of_map_group ?_
    exact S.sq.not_isBernoulli (S.sq_withRotations hrot) h.proximal hs0 hs2
      (hfk S.sq (S.sq_withRotations hrot) hs0 hs2 _
        (measurePreserving_shift_map_group hinv) (heq.map_group hinv hs0.le))

end System

end BoxLike
