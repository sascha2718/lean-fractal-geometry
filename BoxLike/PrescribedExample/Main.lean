module

/-
`ex:projection_double_dimensional`, tex lines 2764 to 2894: for every `0 < s_2 < s_1 ≤ 1` there
is a proximal box-like self-affine set with rotations, defined by four maps and satisfying strong
separation and projective exponential separation, with `dimaff(X) = s_1`, whose
`s_1`-equilibrium state has double-dimensional coordinate projections with the pointwise
dimension values `s_1` and `s_2`.

The parameter `p`, the translation vector `t`, the separation conditions and `dimaff(X) = s_1`
come from `BoxLike/PrescribedExample/Geometry.lean`; the equilibrium state, its entropy, its
Lyapunov exponents and the dimensions of its projections from
`BoxLike/PrescribedExample/Measure.lean` and `BoxLike/PrescribedExample/Dimensions.lean`.

* `PrescribedExample.prob_paramsOf`, `PrescribedExample.two_mul_rpow_add_paramsOf`: for
  `a = (p/2)^{1/s_1}`, `b = ((1-p)/2)^{1/s_1}`, `2 a^{s_1} = p` and `2 a^{s_1} + 2 b^{s_1} = 1`.
* `PrescribedExample.equilibrium_spec`: the measure-theoretic part of the example for given `p`
  and `t`, assuming the projective exponential separation condition.
* `PrescribedExample.projection_double_dimensional_of_geometry`: the example, assuming the
  geometric facts (the choice of `p`, a translation with strong separation and projective
  exponential separation, and `dimaff(X) = s_1`).
* `PrescribedExample.projection_double_dimensional`: `ex:projection_double_dimensional`.
-/
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.PrescribedExample.Dimensions
public import BoxLike.PrescribedExample.Geometry

@[expose] public section

namespace BoxLike

namespace PrescribedExample

open MeasureTheory

/-- `2 a^{s_1} = p` for `a = (p/2)^{1/s_1}` (`ex:projection_double_dimensional`), so that the
parameter `Gibbs.prob` of the Gibbs measures is the `p` of the example. -/
theorem prob_paramsOf {s₁ p : ℝ} (hs₀ : 0 < s₁) (hs₁ : s₁ ≤ 1) (hp₀ : 1 / 2 < p)
    (hp₁ : p < 1) : Gibbs.prob (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁) s₁ = p := by
  rw [Gibbs.prob, paramsOf_a, aOf, ← Real.rpow_mul (by linarith), one_div_mul_cancel hs₀.ne',
    Real.rpow_one]
  ring

/-- `2 a^{s_1} + 2 b^{s_1} = p + (1 - p) = 1` for the parameters of
`ex:projection_double_dimensional`. -/
theorem two_mul_rpow_add_paramsOf {s₁ p : ℝ} (hs₀ : 0 < s₁) (hs₁ : s₁ ≤ 1) (hp₀ : 1 / 2 < p)
    (hp₁ : p < 1) :
    2 * (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁).a ^ s₁ + 2 * (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁).b ^ s₁ =
      1 := by
  rw [paramsOf_a, paramsOf_b, aOf, bOf, ← Real.rpow_mul (by linarith),
    ← Real.rpow_mul (by linarith), one_div_mul_cancel hs₀.ne', Real.rpow_one, Real.rpow_one]
  ring

/-- The measure-theoretic part of `ex:projection_double_dimensional`, tex lines 2858 to 2893,
for `0 < s_2 < s_1 ≤ 1`, a parameter `1/2 < p < 1` with `(log 2 + H(p))/(log 2 + J(p)) = s_2/s_1`
and a translation vector `t` with the projective exponential separation condition. The
`s_1`-equilibrium state exists and is unique; for every invariant `s_1`-equilibrium state `μ`,
`h_0(μ) = log 2 + H(p)`, `λ_1(𝖠, μ) = p log a + (1 - p) log b = -(log 2 + H(p))/s_1`,
`λ_2(𝖠, μ) = p log b + (1 - p) log a = -(log 2 + J(p))/s_1`, `-h_0(μ)/λ_1(𝖠, μ) = s_1`,
`-h_0(μ)/λ_2(𝖠, μ) = s_2`, and by `thm:eq_state_proj_dim` both coordinate projections are
double-dimensional with the pointwise dimension values `s_1` and `s_2`, upper packing dimension
`s_1`, lower Hausdorff dimension `s_2` and each value on a set of positive measure. -/
theorem equilibrium_spec (hms : MorrisShmerkinLyapunov.{0}) (hfk : EquilibriumGibbsStatement.{0})
    (hfjj : FraserJordanJurgaDecomposition.{0}) (hjr : JordanRapaportDimension.{0})
    {s₁ s₂ p : ℝ} (hs₀ : 0 < s₁) (hs₁ : s₁ ≤ 1) (hp₀ : 1 / 2 < p) (hp₁ : p < 1)
    (hratio : ratio p = s₂ / s₁) (t : Fin 8 → ℝ)
    (hsep : (sys (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁) t).ProjExpSeparation) :
    (∃! μ : Measure (ℤ → Fin 4), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
        (sys (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁) t).IsEquilibriumState s₁ μ) ∧
      ∀ (μ : Measure (ℤ → Fin 4)) [IsProbabilityMeasure μ], MeasurePreserving (shift 1) μ μ →
        (sys (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁) t).IsEquilibriumState s₁ μ →
        entropy μ = Real.log 2 + H p ∧
        (sys (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁) t).lyapunov₁ μ =
          p * Real.log (aOf s₁ p) + (1 - p) * Real.log (bOf s₁ p) ∧
        (sys (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁) t).lyapunov₁ μ = -(Real.log 2 + H p) / s₁ ∧
        (sys (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁) t).lyapunov₂ μ =
          p * Real.log (bOf s₁ p) + (1 - p) * Real.log (aOf s₁ p) ∧
        (sys (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁) t).lyapunov₂ μ = -(Real.log 2 + J p) / s₁ ∧
        -entropy μ / (sys (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁) t).lyapunov₁ μ = s₁ ∧
        -entropy μ / (sys (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁) t).lyapunov₂ μ = s₂ ∧
        ∀ c : ZMod 2,
          IsDoubleDim ((sys (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁) t).marginal c μ) ∧
          HasLocalDimPair ((sys (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁) t).marginal c μ) s₁ s₂ ∧
          upperPackingDim ((sys (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁) t).marginal c μ) = s₁ ∧
          lowerHausdorffDim ((sys (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁) t).marginal c μ) = s₂ ∧
          0 < (sys (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁) t).marginal c μ
            {x | HasLocalDim ((sys (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁) t).marginal c μ) x s₁} ∧
          0 < (sys (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁) t).marginal c μ
            {x | HasLocalDim ((sys (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁) t).marginal c μ) x s₂} := by
  set P := paramsOf s₁ p hs₀ hs₁ hp₀ hp₁
  have hP : 2 * P.a ^ s₁ + 2 * P.b ^ s₁ = 1 := two_mul_rpow_add_paramsOf hs₀ hs₁ hp₀ hp₁
  have hprob : Gibbs.prob P s₁ = p := prob_paramsOf hs₀ hs₁ hp₀ hp₁
  have hs₂ : s₁ * ratio p = s₂ := by rw [hratio, mul_div_cancel₀ _ hs₀.ne']
  refine ⟨Gibbs.existsUnique_isEquilibriumState P t hfk hfjj hs₀ hs₁ hP,
    fun μ _ hinv heq => ?_⟩
  obtain ⟨-, hent, -, hl₁, hl₂⟩ := Gibbs.isEquilibriumState_spec P t hfk hfjj hs₀ hs₁ hP μ hinv heq
  obtain ⟨hv₁, hv₂, hr₁, hr₂⟩ := Gibbs.isEquilibriumState_ratios P t hfk hfjj hs₀ hs₁ hP μ hinv heq
  rw [hprob] at hent hl₁ hl₂ hv₁ hv₂ hr₂
  rw [hs₂] at hr₂
  refine ⟨hent, hl₁, hv₁, hl₂, hv₂, hr₁, hr₂, fun c => ?_⟩
  obtain ⟨-, hdbl, hdd, hup, hlow, hpos₁, hpos₂⟩ :=
    Gibbs.marginal_spec hms hfk hfjj hjr P t hsep hs₀ hs₁ hP μ hinv heq c
  rw [hprob, hs₂] at hdd hlow hpos₂
  exact ⟨hdbl, hdd, hup, hlow, hpos₁, hpos₂⟩

/-- `ex:projection_double_dimensional` from its geometric part. Let `0 < s_2 < s_1 ≤ 1` and
suppose that exactly one `1/2 < p < 1` satisfies `(log 2 + H(p))/(log 2 + J(p)) = s_2/s_1`, and
that some translation vector `t` makes the system `Φ` of four maps with `a = (p/2)^{1/s_1}`,
`b = ((1-p)/2)^{1/s_1}` satisfy strong separation and projective exponential separation, with
`dimaff(X) = s_1`. Then `Φ` is a proximal box-like system with rotations, its
`s_1`-equilibrium state `μ` exists and is unique, and the conclusions of `equilibrium_spec`
hold: `h_0(μ) = log 2 + H(p)`, the two Lyapunov exponents, `-h_0/λ_1 = s_1`, `-h_0/λ_2 = s_2`,
and both coordinate projections are double-dimensional with pointwise dimension values `s_1`
and `s_2`, upper packing dimension `s_1`, lower Hausdorff dimension `s_2`, and each value on a
set of positive measure. -/
theorem projection_double_dimensional_of_geometry (hms : MorrisShmerkinLyapunov.{0})
    (hfk : EquilibriumGibbsStatement.{0}) (hfjj : FraserJordanJurgaDecomposition.{0})
    (hjr : JordanRapaportDimension.{0}) {s₁ s₂ : ℝ} (hs₂ : 0 < s₂) (h₂₁ : s₂ < s₁)
    (hs₁ : s₁ ≤ 1)
    (hgeom : ∃ p : ℝ, ∃ hp : 1 / 2 < p ∧ p < 1, ratio p = s₂ / s₁ ∧
      (∀ q ∈ Set.Ioo (1 / 2 : ℝ) 1, ratio q = s₂ / s₁ → q = p) ∧ ∃ t : Fin 8 → ℝ,
      (sys (paramsOf s₁ p (hs₂.trans h₂₁) hs₁ hp.1 hp.2) t).StrongSeparation ∧
      (sys (paramsOf s₁ p (hs₂.trans h₂₁) hs₁ hp.1 hp.2) t).ProjExpSeparation ∧
      (sys (paramsOf s₁ p (hs₂.trans h₂₁) hs₁ hp.1 hp.2) t).dimaff = s₁) :
    ∃ p : ℝ, ∃ hp : 1 / 2 < p ∧ p < 1, ratio p = s₂ / s₁ ∧
      (∀ q ∈ Set.Ioo (1 / 2 : ℝ) 1, ratio q = s₂ / s₁ → q = p) ∧ ∃ t : Fin 8 → ℝ,
      let S := sys (paramsOf s₁ p (hs₂.trans h₂₁) hs₁ hp.1 hp.2) t
      S.WithRotations ∧ S.Proximal ∧ S.StrongSeparation ∧ S.ProjExpSeparation ∧
      S.dimaff = s₁ ∧
      (∃! μ : Measure (ℤ → Fin 4), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
        S.IsEquilibriumState s₁ μ) ∧
      ∀ (μ : Measure (ℤ → Fin 4)) [IsProbabilityMeasure μ], MeasurePreserving (shift 1) μ μ →
        S.IsEquilibriumState s₁ μ →
        entropy μ = Real.log 2 + H p ∧
        S.lyapunov₁ μ = p * Real.log (aOf s₁ p) + (1 - p) * Real.log (bOf s₁ p) ∧
        S.lyapunov₁ μ = -(Real.log 2 + H p) / s₁ ∧
        S.lyapunov₂ μ = p * Real.log (bOf s₁ p) + (1 - p) * Real.log (aOf s₁ p) ∧
        S.lyapunov₂ μ = -(Real.log 2 + J p) / s₁ ∧
        -entropy μ / S.lyapunov₁ μ = s₁ ∧ -entropy μ / S.lyapunov₂ μ = s₂ ∧
        ∀ c : ZMod 2,
          IsDoubleDim (S.marginal c μ) ∧ HasLocalDimPair (S.marginal c μ) s₁ s₂ ∧
          upperPackingDim (S.marginal c μ) = s₁ ∧ lowerHausdorffDim (S.marginal c μ) = s₂ ∧
          0 < S.marginal c μ {x | HasLocalDim (S.marginal c μ) x s₁} ∧
          0 < S.marginal c μ {x | HasLocalDim (S.marginal c μ) x s₂} := by
  obtain ⟨p, hp, hratio, hpuniq, t, hssc, hsep, hdim⟩ := hgeom
  obtain ⟨huniq, hspec⟩ := equilibrium_spec hms hfk hfjj hjr (hs₂.trans h₂₁) hs₁ hp.1 hp.2
    hratio t hsep
  exact ⟨p, hp, hratio, hpuniq, t, Gibbs.withRotations _ t, Gibbs.proximal _ t, hssc, hsep, hdim,
    huniq, hspec⟩

/-- `ex:projection_double_dimensional`, tex lines 2764 to 2894. For every `0 < s_2 < s_1 ≤ 1`
the equation `(log 2 + H(p))/(log 2 + J(p)) = s_2/s_1` has exactly one solution `1/2 < p < 1`,
and for some translation vector `t ∈ ℝ^8` the system `Φ` of the four maps
`φ_i(x, y) = (a x + t_i, b y + t_{i+4})`, `i ∈ {1, 2}`, and
`φ_i(x, y) = (a y + t_i, b x + t_{i+4})`, `i ∈ {3, 4}`, with `a = (p/2)^{1/s_1}` and
`b = ((1-p)/2)^{1/s_1}`, is a proximal box-like system with rotations satisfying strong
separation and projective exponential separation, with `dimaff(X) = s_1`. Its
`s_1`-equilibrium state `μ` exists and is unique, `h_0(μ) = log 2 + H(p)`,
`λ_1(𝖠, μ) = p log a + (1 - p) log b = -(log 2 + H(p))/s_1`,
`λ_2(𝖠, μ) = p log b + (1 - p) log a = -(log 2 + J(p))/s_1`, `-h_0(μ)/λ_1(𝖠, μ) = s_1` and
`-h_0(μ)/λ_2(𝖠, μ) = s_2`; both coordinate projections `ν_x`, `ν_y` are double-dimensional with
pointwise dimension values `s_1` and `s_2`, `\overline{dim}_p(ν_x) = \overline{dim}_p(ν_y) = s_1`,
`\underline{dim}_H(ν_x) = \underline{dim}_H(ν_y) = s_2`, and each value occurs on a set of
positive measure in each projection. The hypotheses are those of `thm:eq_state_proj_dim`: the
statements `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement` and
`FraserJordanJurgaDecomposition`, which the library proves, and the cited theorem of
Jordan–Rapaport. -/
theorem projection_double_dimensional (hms : MorrisShmerkinLyapunov.{0})
    (hfk : EquilibriumGibbsStatement.{0}) (hfjj : FraserJordanJurgaDecomposition.{0})
    (hjr : JordanRapaportDimension.{0}) {s₁ s₂ : ℝ} (hs₂ : 0 < s₂) (h₂₁ : s₂ < s₁)
    (hs₁ : s₁ ≤ 1) :
    ∃ p : ℝ, ∃ hp : 1 / 2 < p ∧ p < 1, ratio p = s₂ / s₁ ∧
      (∀ q ∈ Set.Ioo (1 / 2 : ℝ) 1, ratio q = s₂ / s₁ → q = p) ∧ ∃ t : Fin 8 → ℝ,
      let S := sys (paramsOf s₁ p (hs₂.trans h₂₁) hs₁ hp.1 hp.2) t
      S.WithRotations ∧ S.Proximal ∧ S.StrongSeparation ∧ S.ProjExpSeparation ∧
      S.dimaff = s₁ ∧
      (∃! μ : Measure (ℤ → Fin 4), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
        S.IsEquilibriumState s₁ μ) ∧
      ∀ (μ : Measure (ℤ → Fin 4)) [IsProbabilityMeasure μ], MeasurePreserving (shift 1) μ μ →
        S.IsEquilibriumState s₁ μ →
        entropy μ = Real.log 2 + H p ∧
        S.lyapunov₁ μ = p * Real.log (aOf s₁ p) + (1 - p) * Real.log (bOf s₁ p) ∧
        S.lyapunov₁ μ = -(Real.log 2 + H p) / s₁ ∧
        S.lyapunov₂ μ = p * Real.log (bOf s₁ p) + (1 - p) * Real.log (aOf s₁ p) ∧
        S.lyapunov₂ μ = -(Real.log 2 + J p) / s₁ ∧
        -entropy μ / S.lyapunov₁ μ = s₁ ∧ -entropy μ / S.lyapunov₂ μ = s₂ ∧
        ∀ c : ZMod 2,
          IsDoubleDim (S.marginal c μ) ∧ HasLocalDimPair (S.marginal c μ) s₁ s₂ ∧
          upperPackingDim (S.marginal c μ) = s₁ ∧ lowerHausdorffDim (S.marginal c μ) = s₂ ∧
          0 < S.marginal c μ {x | HasLocalDim (S.marginal c μ) x s₁} ∧
          0 < S.marginal c μ {x | HasLocalDim (S.marginal c μ) x s₂} := by
  refine projection_double_dimensional_of_geometry hms hfk hfjj hjr hs₂ h₂₁ hs₁ ?_
  obtain ⟨p, hp, hratio, hpuniq, t, -, hg, hdim⟩ := exists_geometry hs₂ h₂₁ hs₁
  exact ⟨p, hp, hratio, hpuniq, t, hg.strongSeparation, hg.projExpSeparation, hdim⟩

end PrescribedExample

end BoxLike
