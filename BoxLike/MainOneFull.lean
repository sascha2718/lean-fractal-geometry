module

/-
`thm:main1` for every affinity parameter: the proof of `thm:main1` in
`sec:dimension_of_projections`. Below the threshold `2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)` the coordinate
projections are double-dimensional, with the two values of `thm:eq_state_proj_dim` distinct and
each on a set of positive measure, since the projection is the sum of two nonzero
exact-dimensional measures (`thm:exact-dimensional-mixture`). At the threshold and above they are
exact-dimensional of dimension one. For `s ≥ 2` the proof of `thm:eq_state_proj_dim` gives
`λ_1(𝖠, μ) = λ_2(𝖠, μ)`, and `eq:eq_state_def` with `eq:energy_def` gives
`h_0(μ) = -s λ_1(𝖠, μ)`, so both projections are exact-dimensional of dimension one and the
threshold is one. For `0 < s < 2` the values are in `System.main1`.

* `System.main1_of_two_le`: the case `s ≥ 2`, with the values.
* `System.main1_all`: `thm:main1` for every zero `s > 0` of the pressure, with the values.
* `System.main1_values_all`: `thm:main1` with `s = dimaff(X)`, with the values, for every
  invariant `s`-equilibrium state.
* `System.main1_isDoubleDim`: below the threshold, for `0 < s < 2`, the coordinate projections
  are double-dimensional.
* `System.main1_dichotomy_all`: `thm:main1` for every zero `s > 0` of the pressure.
* `System.main1_dimaff_all`: `thm:main1` with `s = dimaff(X)`, for every invariant
  `s`-equilibrium state, in the form of `Challenge.audit_main1`.
-/
public import BoxLike.AffinityMain
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.MeasureDimDouble
public import BoxLike.ProjectionLarge

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {s : ℝ}

/-- The case `s ≥ 2` of `thm:main1`, with the values. Let `X` be a box-like self-affine set
with rotations satisfying the projective exponential separation condition, let `s ≥ 2` be a zero
of the pressure and let `μ` be an `s`-equilibrium state. Then the coordinate projections of `μ`
are exact-dimensional of dimension one, so their pointwise dimension is
`min{1, -h_0(μ)/λ_1(𝖠, μ)} = min{1, -h_0(μ)/λ_2(𝖠, μ)} = 1` almost everywhere; they are never
non-exact-dimensional, and `s` is at least the threshold `2 - λ_1(𝖠, μ)/λ_2(𝖠, μ) = 1`. -/
theorem main1_of_two_le (hjr : JordanRapaportDimension.{u}) (hrot : S.WithRotations)
    (hsep : S.ProjExpSeparation) (hs : 2 ≤ s) (hP : S.pressure s = 0) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) (c : ZMod 2) :
    HasLocalDimPair (S.marginal c μ) (min 1 (-entropy μ / S.lyapunov₁ μ))
        (min 1 (-entropy μ / S.lyapunov₂ μ)) ∧
      ((¬ ∃ d, IsExactDim (S.marginal c μ) d) ↔ s < 2 - S.lyapunov₁ μ / S.lyapunov₂ μ) ∧
      (2 - S.lyapunov₁ μ / S.lyapunov₂ μ ≤ s → IsExactDim (S.marginal c μ) 1) := by
  obtain ⟨hl, hd⟩ := S.isExactDim_marginal_of_two_le hjr hrot hsep hs μ hinv heq c
  have hl1 := S.lyapunov₁_neg hinv
  -- `h_0(μ) = -s λ_1(𝖠, μ)` from `eq:eq_state_def` and `eq:energy_def`.
  have henergy : entropy μ + energy (S.lyapunov₁ μ) (S.lyapunov₂ μ) s = 0 := by
    rw [← heq.pressure_eq hinv (by linarith), hP]
  rw [energy_of_two_le hs, ← hl] at henergy
  have hmin : min 1 (-entropy μ / S.lyapunov₁ μ) = 1 := by
    refine min_eq_left ?_
    rw [le_div_iff_of_neg hl1]
    nlinarith
  rw [hmin] at hd
  rw [← hl, hmin, div_self hl1.ne]
  exact ⟨hd.hasLocalDimPair, ⟨fun h => absurd ⟨1, hd⟩ h, fun h => by linarith⟩, fun _ => hd⟩

/-- `thm:main1` for every zero `s > 0` of the pressure, with the values. Let `X` be a proximal
box-like self-affine set with rotations satisfying the projective exponential separation
condition, let `s > 0` be a zero of the pressure, that is `s = dimaff(X)`, and let `μ` be an
`s`-equilibrium state. Then the pointwise dimension of each coordinate projection of `μ` is
`min{1, -h_0(μ)/λ_1(𝖠, μ)}` or `min{1, -h_0(μ)/λ_2(𝖠, μ)}` almost everywhere; the projections
fail to be exact-dimensional precisely when `s < 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)`; at equality and above
they are exact-dimensional of dimension one. -/
theorem main1_all (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hjr : JordanRapaportDimension.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal) (hsep : S.ProjExpSeparation) (hs0 : 0 < s)
    (hP : S.pressure s = 0) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState s μ) (c : ZMod 2) :
    HasLocalDimPair (S.marginal c μ) (min 1 (-entropy μ / S.lyapunov₁ μ))
        (min 1 (-entropy μ / S.lyapunov₂ μ)) ∧
      ((¬ ∃ d, IsExactDim (S.marginal c μ) d) ↔ s < 2 - S.lyapunov₁ μ / S.lyapunov₂ μ) ∧
      (2 - S.lyapunov₁ μ / S.lyapunov₂ μ ≤ s → IsExactDim (S.marginal c μ) 1) := by
  rcases lt_or_ge s 2 with hs2 | hs2
  · exact S.main1 hms hfk hfjj hjr hrot hprox hsep hs0 hs2 hP μ hinv heq c
  · exact S.main1_of_two_le hjr hrot hsep hs2 hP μ hinv heq c

/-- `thm:main1` with the values. Let `X` be a proximal box-like self-affine set with rotations
satisfying the projective exponential separation condition, and let `μ` be an `s`-equilibrium
state for `s = dimaff(X)`. Then the pointwise dimension of each coordinate projection of `μ`,
the marginal `(proj_x)_*(π_*μ)` for `c = 0` and `(proj_y)_*(π_*μ)` for `c = 1`, is
`min{1, -h_0(μ)/λ_1(𝖠, μ)}` or `min{1, -h_0(μ)/λ_2(𝖠, μ)}` almost everywhere. Both projections
fail to be exact-dimensional, with any dimension, precisely when
`s < 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)`. At equality and above, both projections are exact-dimensional of
dimension one. The conclusion holds for every invariant `s`-equilibrium state. -/
theorem main1_values_all (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hjr : JordanRapaportDimension.{u})
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal) (hsep : S.ProjExpSeparation)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ)
    (c : ZMod 2) :
    HasLocalDimPair (S.marginal c μ) (min 1 (-entropy μ / S.lyapunov₁ μ))
        (min 1 (-entropy μ / S.lyapunov₂ μ)) ∧
      ((¬ ∃ d, IsExactDim (S.marginal c μ) d) ↔
        S.dimaff < 2 - S.lyapunov₁ μ / S.lyapunov₂ μ) ∧
      (2 - S.lyapunov₁ μ / S.lyapunov₂ μ ≤ S.dimaff → IsExactDim (S.marginal c μ) 1) := by
  have := S.nontrivial_of_withRotations hrot
  exact S.main1_all hms hfk hfjj hjr hrot hprox hsep S.dimaff_pos S.pressure_dimaff μ hinv heq c

/-- `thm:main1` below the threshold, for `0 < s < 2`. Let `X` be a proximal box-like
self-affine set with rotations satisfying the projective exponential separation condition, let
`0 < s < 2` be a zero of the pressure and let `μ` be an `s`-equilibrium state with
`s < 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)`. Then the coordinate projections of `μ` are double-dimensional:
by `eq:proj_eq_is_sum` each is the sum of two nonzero exact-dimensional measures of dimensions
`min{1, -h_0(μ)/λ_1(𝖠, μ)}` and `min{1, -h_0(μ)/λ_2(𝖠, μ)}`, which differ below the threshold,
and `thm:exact-dimensional-mixture` applies. -/
theorem main1_isDoubleDim (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hjr : JordanRapaportDimension.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal) (hsep : S.ProjExpSeparation) (hs0 : 0 < s)
    (hs2 : s < 2) (hP : S.pressure s = 0) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState s μ) (c : ZMod 2)
    (hthr : s < 2 - S.lyapunov₁ μ / S.lyapunov₂ μ) : IsDoubleDim (S.marginal c μ) := by
  obtain ⟨ν₁, ν₂, hf₁, hf₂, hne₁, hne₂, hsum, hd₁, hd₂⟩ :=
    S.marginal_decomposition hfk hfjj hjr hrot hprox hsep hs0 hs2 μ hinv heq c
  have hl := S.simple_lyapunov hms hrot hprox hs0 hs2 μ hinv heq
  have hl1 := S.lyapunov₁_neg hinv
  have henergy : entropy μ + energy (S.lyapunov₁ μ) (S.lyapunov₂ μ) s = 0 := by
    rw [← heq.pressure_eq hinv hs0.le, hP]
  rw [hsum]
  exact hd₁.isDoubleDim_add hd₂ hne₁ hne₂ ((min_ne_min_iff hl hl1 hs0 hs2 henergy).2 hthr)

/-- `thm:main1` for every zero `s > 0` of the pressure. Let `X` be a proximal box-like
self-affine set with rotations satisfying the projective exponential separation condition, let
`s > 0` be a zero of the pressure, that is `s = dimaff(X)`, and let `μ` be an `s`-equilibrium
state. Then the coordinate projections of `μ` are double-dimensional if
`s < 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)`, and exact-dimensional of dimension one otherwise. For `s ≥ 2`
the threshold is one, so only the second case occurs. -/
theorem main1_dichotomy_all (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hjr : JordanRapaportDimension.{u}) (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (hs0 : 0 < s) (hP : S.pressure s = 0) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) (c : ZMod 2) :
    (s < 2 - S.lyapunov₁ μ / S.lyapunov₂ μ → IsDoubleDim (S.marginal c μ)) ∧
      (2 - S.lyapunov₁ μ / S.lyapunov₂ μ ≤ s → IsExactDim (S.marginal c μ) 1) := by
  rcases lt_or_ge s 2 with hs2 | hs2
  · exact ⟨S.main1_isDoubleDim hms hfk hfjj hjr hrot hprox hsep hs0 hs2 hP μ hinv heq c,
      (S.main1 hms hfk hfjj hjr hrot hprox hsep hs0 hs2 hP μ hinv heq c).2.2⟩
  · -- For `s ≥ 2` the exponents agree, so the threshold is one and `s` lies above it.
    obtain ⟨hl, -⟩ := S.isExactDim_marginal_of_two_le hjr hrot hsep hs2 μ hinv heq c
    obtain ⟨-, -, hone⟩ := S.main1_of_two_le hjr hrot hsep hs2 hP μ hinv heq c
    have hthr : 2 - S.lyapunov₁ μ / S.lyapunov₂ μ = 1 := by
      rw [← hl, div_self (S.lyapunov₁_neg hinv).ne]
      norm_num
    rw [hthr] at hone ⊢
    exact ⟨fun h => absurd h (not_lt.2 (by linarith)), hone⟩

/-- `thm:main1`. Let `X` be a proximal box-like self-affine set with rotations satisfying the
projective exponential separation condition, and let `μ` be an `s`-equilibrium state for
`s = dimaff(X)`. Then the coordinate projections of `μ`, the marginal `(proj_x)_*(π_*μ)` for
`c = 0` and `(proj_y)_*(π_*μ)` for `c = 1`, are double-dimensional if
`s < 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)`, and exact-dimensional of dimension one otherwise. The conclusion
holds for every invariant `s`-equilibrium state. This is the library form of
`Challenge.audit_main1`; the two values are in `main1_values_all` and
`thm:eq_state_proj_dim`. -/
theorem main1_dimaff_all (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hjr : JordanRapaportDimension.{u})
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal) (hsep : S.ProjExpSeparation)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ)
    (c : ZMod 2) :
    (S.dimaff < 2 - S.lyapunov₁ μ / S.lyapunov₂ μ → IsDoubleDim (S.marginal c μ)) ∧
      (2 - S.lyapunov₁ μ / S.lyapunov₂ μ ≤ S.dimaff → IsExactDim (S.marginal c μ) 1) := by
  have := S.nontrivial_of_withRotations hrot
  exact S.main1_dichotomy_all hms hfk hfjj hjr hrot hprox hsep S.dimaff_pos S.pressure_dimaff μ
    hinv heq c

end System

end BoxLike
