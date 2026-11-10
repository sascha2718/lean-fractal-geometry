module

/-
`thm:eq_state_proj_dim` and `thm:main1` for every proximal box-like tuple with rotations. By
`thm:box_like_proximal` the tuple `𝖠` or its second iterate `𝖠²` contains a proximal diagonal
generator, and `thm:two-block-normalisation` transfers the hypotheses and the conclusions
between `(Φ, μ)` and `(Φ^(2), β_*μ)`.

* `System.IsEquilibriumState.map_group`: `μ^(2) = β_*μ` is an `s`-equilibrium state of `𝖠²`,
  from `thm:two-block-normalisation`.
* `System.simple_lyapunov`: `eq:simple_lyapunov`, `λ_2(𝖠, μ) < λ_1(𝖠, μ)`.
* `System.marginal_decomposition`: `eq:proj_eq_is_sum` and `eq:gibbs_proj_dim` for the
  coordinate marginals.
* `System.eq_state_proj_dim`: `thm:eq_state_proj_dim`.
* `System.main1`: `thm:main1`.
-/
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.Grouping
public import BoxLike.Lyapunov
public import BoxLike.Main
public import BoxLike.MeasureDimBounds
public import BoxLike.Proximal

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

/-- The ratio `-h/λ` is unchanged when the entropy and the exponent are doubled. -/
theorem neg_two_mul_div_two_mul (h l : ℝ) : -(2 * h) / (2 * l) = -h / l := by
  rw [← mul_neg, mul_div_mul_left _ _ two_ne_zero]

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {s : ℝ}

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- A probability measure on `Σ` forces a non-empty alphabet. -/
theorem nonempty_of_measure (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] : Nonempty ι := by
  obtain ⟨x⟩ : Nonempty (ℤ → ι) := nonempty_of_isProbabilityMeasure μ
  exact ⟨x 0⟩

variable {S} in
/-- `thm:two-block-normalisation`: `μ^(2) = β_*μ` is an `s`-equilibrium state of `𝖠²`, since
`P(𝖠², s) = 2P(𝖠, s)`, `h_0(μ^(2)) = 2h_0(μ)` and `λ_i(𝖠², μ^(2)) = 2λ_i(𝖠, μ)`. -/
theorem IsEquilibriumState.map_group {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]
    (heq : S.IsEquilibriumState s μ) (hinv : MeasurePreserving (shift 1) μ μ) (hs : 0 ≤ s) :
    S.sq.IsEquilibriumState s (μ.map group) := by
  have := nonempty_of_measure μ
  refine IsEquilibriumState.of_pressure_eq (measurePreserving_shift_map_group hinv) hs ?_
  rw [S.pressure_sq hs, entropy_map_group hinv,
    S.lyapunov₁_sq_map_group (S.tendsto_lyapunov₁ hinv),
    S.lyapunov₂_sq_map_group (S.tendsto_lyapunov₂ hinv), energy_two_mul,
    heq.pressure_eq hinv hs, mul_add]

/-- `eq:simple_lyapunov`: for a proximal box-like tuple with rotations and `0 < s < 2` the
Lyapunov exponents of the `s`-equilibrium state are distinct. For a tuple without a proximal
diagonal generator the inequality is transferred from `𝖠²`, as in `sec:normalisation`. -/
theorem simple_lyapunov (hms : MorrisShmerkinLyapunov.{u}) (hrot : S.WithRotations)
    (hprox : S.Proximal) (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState s μ) :
    S.lyapunov₂ μ < S.lyapunov₁ μ := by
  rcases hprox.hasProximalDiagonal_or_sq with h | h
  · exact hms S hrot h hs0 hs2 μ hinv heq
  · have key := hms S.sq (S.sq_withRotations hrot) h hs0 hs2 (μ.map group)
      (measurePreserving_shift_map_group hinv) (heq.map_group hinv hs0.le)
    rw [S.lyapunov₁_sq_map_group (S.tendsto_lyapunov₁ hinv),
      S.lyapunov₂_sq_map_group (S.tendsto_lyapunov₂ hinv)] at key
    linarith

/-- `eq:proj_eq_is_sum`, `eq:restricted-projection-dimensions` and `eq:gibbs_proj_dim` for a
proximal box-like tuple with rotations: each coordinate marginal of the `s`-equilibrium state,
`0 < s < 2`, is the sum of two non-zero exact-dimensional measures of dimensions
`min{1, -h_0(μ)/λ_1(𝖠, μ)}` and `min{1, -h_0(μ)/λ_2(𝖠, μ)}`. Grouping preserves the marginals
and the ratios of entropy to Lyapunov exponents. -/
theorem marginal_decomposition (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hjr : JordanRapaportDimension.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal) (hsep : S.ProjExpSeparation) (hs0 : 0 < s)
    (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState s μ) (c : ZMod 2) :
    ∃ ν₁ ν₂ : Measure ℝ, IsFiniteMeasure ν₁ ∧ IsFiniteMeasure ν₂ ∧ ν₁ ≠ 0 ∧ ν₂ ≠ 0 ∧
      S.marginal c μ = ν₁ + ν₂ ∧
      IsExactDim ν₁ (min 1 (-entropy μ / S.lyapunov₁ μ)) ∧
      IsExactDim ν₂ (min 1 (-entropy μ / S.lyapunov₂ μ)) := by
  rcases hprox.hasProximalDiagonal_or_sq with h | h
  · exact S.marginal_decomposition_normalised hfk hfjj hjr hrot h hsep hs0 hs2 μ hinv heq c
  · have := nonempty_of_measure μ
    have key := S.sq.marginal_decomposition_normalised hfk hfjj hjr (S.sq_withRotations hrot) h
      (ProjExpSeparation.sq S hsep) hs0 hs2 (μ.map group)
      (measurePreserving_shift_map_group hinv) (heq.map_group hinv hs0.le) c
    rwa [S.marginal_sq_map_group, entropy_map_group hinv,
      S.lyapunov₁_sq_map_group (S.tendsto_lyapunov₁ hinv),
      S.lyapunov₂_sq_map_group (S.tendsto_lyapunov₂ hinv), neg_two_mul_div_two_mul,
      neg_two_mul_div_two_mul] at key

/-- The case `0 < s < 2` of `thm:eq_state_proj_dim`: if `X` is a proximal box-like self-affine
set with rotations satisfying the projective exponential separation condition and `μ` is the
`s`-equilibrium state with `0 < s < 2`, then the pointwise dimension of each of
`(proj_x)_*(π_*μ)` and `(proj_y)_*(π_*μ)` exists almost everywhere and takes only the values
`min{1, -h_0(μ)/λ_1(𝖠, μ)}`, the upper packing dimension, and `min{1, -h_0(μ)/λ_2(𝖠, μ)}`, the
lower Hausdorff dimension, each on a set of positive measure. -/
theorem eq_state_proj_dim (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hjr : JordanRapaportDimension.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal) (hsep : S.ProjExpSeparation) (hs0 : 0 < s)
    (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState s μ) (c : ZMod 2) :
    HasLocalDimPair (S.marginal c μ) (min 1 (-entropy μ / S.lyapunov₁ μ))
        (min 1 (-entropy μ / S.lyapunov₂ μ)) ∧
      upperPackingDim (S.marginal c μ) = min 1 (-entropy μ / S.lyapunov₁ μ) ∧
      lowerHausdorffDim (S.marginal c μ) = min 1 (-entropy μ / S.lyapunov₂ μ) ∧
      0 < S.marginal c μ
        {x | HasLocalDim (S.marginal c μ) x (min 1 (-entropy μ / S.lyapunov₁ μ))} ∧
      0 < S.marginal c μ
        {x | HasLocalDim (S.marginal c μ) x (min 1 (-entropy μ / S.lyapunov₂ μ))} := by
  obtain ⟨ν₁, ν₂, hf₁, hf₂, hne₁, hne₂, hsum, hd₁, hd₂⟩ :=
    S.marginal_decomposition hfk hfjj hjr hrot hprox hsep hs0 hs2 μ hinv heq c
  have hl := S.simple_lyapunov hms hrot hprox hs0 hs2 μ hinv heq
  have hle := min_neg_div_le hl.le (S.lyapunov₁_neg hinv) (entropy_nonneg hinv)
  have hdd := hd₁.hasLocalDimPair_add hd₂
  have hp₁ := hd₁.measure_hasLocalDim_add_left_pos (ν₂ := ν₂) hne₁
  have hp₂ := hd₂.measure_hasLocalDim_add_right_pos (ν₁ := ν₁) hne₂
  rw [hsum]
  exact ⟨hdd, hdd.upperPackingDim_eq hle hp₁, hdd.lowerHausdorffDim_eq hle hp₂, hp₁, hp₂⟩

/-- The case `0 < s < 2` of `thm:main1`, with the values. Let `X` be a proximal box-like
self-affine set with rotations satisfying the projective exponential separation condition, let
`0 < s < 2` be a zero of the pressure, that is `s = dimaff(X) < 2`, and let `μ` be the
`s`-equilibrium state. Then the pointwise dimension of each coordinate projection of `μ` is
`min{1, -h_0(μ)/λ_1(𝖠, μ)}` or `min{1, -h_0(μ)/λ_2(𝖠, μ)}` almost everywhere; the projections
fail to be exact-dimensional precisely when `s < 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)`; at equality and
above they are exact-dimensional of dimension one. -/
theorem main1 (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hjr : JordanRapaportDimension.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal) (hsep : S.ProjExpSeparation) (hs0 : 0 < s)
    (hs2 : s < 2) (hP : S.pressure s = 0) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState s μ) (c : ZMod 2) :
    HasLocalDimPair (S.marginal c μ) (min 1 (-entropy μ / S.lyapunov₁ μ))
        (min 1 (-entropy μ / S.lyapunov₂ μ)) ∧
      ((¬ ∃ d, IsExactDim (S.marginal c μ) d) ↔ s < 2 - S.lyapunov₁ μ / S.lyapunov₂ μ) ∧
      (2 - S.lyapunov₁ μ / S.lyapunov₂ μ ≤ s → IsExactDim (S.marginal c μ) 1) := by
  obtain ⟨ν₁, ν₂, hf₁, hf₂, hne₁, hne₂, hsum, hd₁, hd₂⟩ :=
    S.marginal_decomposition hfk hfjj hjr hrot hprox hsep hs0 hs2 μ hinv heq c
  have hl := S.simple_lyapunov hms hrot hprox hs0 hs2 μ hinv heq
  have hl1 := S.lyapunov₁_neg hinv
  have henergy : entropy μ + energy (S.lyapunov₁ μ) (S.lyapunov₂ μ) s = 0 := by
    rw [← heq.pressure_eq hinv hs0.le, hP]
  rw [hsum]
  refine ⟨hd₁.hasLocalDimPair_add hd₂, ?_, fun hs => ?_⟩
  · rw [isExactDim_add_iff hd₁ hd₂ hne₁ hne₂]
    exact min_ne_min_iff hl hl1 hs0 hs2 henergy
  · obtain ⟨e₁, e₂⟩ := min_eq_one_of_le hl hl1 hs2 henergy hs
    rw [e₁] at hd₁
    rw [e₂] at hd₂
    exact hasLocalDimPair_self_iff.1 (hd₁.hasLocalDimPair_add hd₂)

end System

end BoxLike
