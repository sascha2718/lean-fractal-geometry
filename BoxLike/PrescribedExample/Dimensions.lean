module

/-
The dimensions of the coordinate projections of the equilibrium state in
`ex:projection_double_dimensional`, tex lines 2872 to 2893: the exponents
`λ_1(𝖠, μ) = -(log 2 + H(p))/s` and `λ_2(𝖠, μ) = -(log 2 + J(p))/s`, the ratios
`-h_0(μ)/λ_1(𝖠, μ) = s` and `-h_0(μ)/λ_2(𝖠, μ) = s (log 2 + H(p))/(log 2 + J(p))`, and the
double-dimensionality of both coordinate projections from `thm:eq_state_proj_dim`.

As in `BoxLike/PrescribedExample/Measure.lean`, `P : Params` gives `0 < b < a < 1/2`, the
exponent satisfies `0 < s ≤ 1` and `2 a^s + 2 b^s = 1`, and `p = 2 a^s`. The translation vector
`t` enters only through the projective exponential separation condition, which
`thm:eq_state_proj_dim` assumes.

* `Gibbs.log_two_add_H_pos`, `Gibbs.log_two_add_J_pos`, `Gibbs.H_lt_J`, `Gibbs.ratio_pos`,
  `Gibbs.ratio_lt_one`: `log 2 + H(p) > 0`, `log 2 + J(p) > 0`, `H(p) < J(p)` and
  `0 < (log 2 + H(p))/(log 2 + J(p)) < 1` for `1/2 < p < 1`.
* `Gibbs.half_lt_prob`: `p = 2 a^s > 1/2`, since `a > b`.
* `Gibbs.mul_log_a`, `Gibbs.mul_log_b`, `Gibbs.lyap₁_value`, `Gibbs.lyap₂_value`: the display of
  tex lines 2875 to 2878.
* `Gibbs.isEquilibriumState_ratios`: `-h_0(μ)/λ_1(𝖠, μ) = s` and
  `-h_0(μ)/λ_2(𝖠, μ) = s (log 2 + H(p))/(log 2 + J(p))`, tex lines 2879 to 2885.
* `Gibbs.marginal_spec`: `thm:eq_state_proj_dim` for the example: both coordinate projections
  are double-dimensional with the values `s` and `s (log 2 + H(p))/(log 2 + J(p))`, each on a
  set of positive measure, tex lines 3056 to 3063.
-/
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.General
public import BoxLike.MeasureDimDouble
public import BoxLike.PrescribedExample.Measure

@[expose] public section

namespace BoxLike

namespace PrescribedExample

namespace Gibbs

open MeasureTheory

/-! ### The functions `H` and `J` -/

section HJ

variable {p : ℝ}

/-- `log 2 + H(p) > 0` for `0 < p < 1`, used in `ex:projection_double_dimensional`. -/
theorem log_two_add_H_pos (hp0 : 0 < p) (hp1 : p < 1) : 0 < Real.log 2 + H p := by
  have h1 : Real.log p < 0 := Real.log_neg hp0 hp1
  have h2 : Real.log (1 - p) < 0 := Real.log_neg (by linarith) (by linarith)
  have h3 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h4 : 0 ≤ -p * Real.log p := by nlinarith
  have h5 : 0 ≤ -(1 - p) * Real.log (1 - p) := by nlinarith
  unfold H
  linarith

/-- `log 2 + J(p) > 0` for `0 < p < 1`, used in `ex:projection_double_dimensional`. -/
theorem log_two_add_J_pos (hp0 : 0 < p) (hp1 : p < 1) : 0 < Real.log 2 + J p := by
  have h1 : Real.log p < 0 := Real.log_neg hp0 hp1
  have h2 : Real.log (1 - p) < 0 := Real.log_neg (by linarith) (by linarith)
  have h3 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h4 : 0 ≤ -p * Real.log (1 - p) := by nlinarith
  have h5 : 0 ≤ -(1 - p) * Real.log p := by nlinarith
  unfold J
  linarith

/-- `H(p) < J(p)` for `1/2 < p < 1`: `J(p) - H(p) = (2p - 1)(log p - log(1 - p))`. Hence the
second dimension value of `ex:projection_double_dimensional` is smaller than the first. -/
theorem H_lt_J (hp0 : 1 / 2 < p) (hp1 : p < 1) : H p < J p := by
  have hlog : Real.log (1 - p) < Real.log p := Real.log_lt_log (by linarith) (by linarith)
  have e : J p - H p = (2 * p - 1) * (Real.log p - Real.log (1 - p)) := by
    unfold H J
    ring
  have : 0 < (2 * p - 1) * (Real.log p - Real.log (1 - p)) :=
    mul_pos (by linarith) (by linarith)
  linarith

/-- `(log 2 + H(p))/(log 2 + J(p)) > 0` for `0 < p < 1`. -/
theorem ratio_pos (hp0 : 0 < p) (hp1 : p < 1) : 0 < ratio p :=
  div_pos (log_two_add_H_pos hp0 hp1) (log_two_add_J_pos hp0 hp1)

/-- `(log 2 + H(p))/(log 2 + J(p)) < 1` for `1/2 < p < 1`. -/
theorem ratio_lt_one (hp0 : 1 / 2 < p) (hp1 : p < 1) : ratio p < 1 := by
  rw [ratio, div_lt_one (log_two_add_J_pos (by linarith) hp1)]
  linarith [H_lt_J hp0 hp1]

end HJ

/-! ### The Lyapunov exponents -/

section Exponents

variable (P : Params) {s : ℝ}

/-- `p = 2 a^s > 1/2`: since `b < a`, `2 a^s > 2 b^s = 1 - 2 a^s`. -/
theorem half_lt_prob (hs0 : 0 < s) (hP : 2 * P.a ^ s + 2 * P.b ^ s = 1) :
    1 / 2 < prob P s := by
  have h := Real.rpow_lt_rpow P.b_pos.le P.b_lt_a hs0
  unfold prob
  linarith

/-- `s log a = log(p/2)`, since `a^s = p/2`. -/
theorem mul_log_a : s * Real.log P.a = Real.log (prob P s / 2) := by
  rw [prob, mul_div_cancel_left₀ _ two_ne_zero, Real.log_rpow P.a_pos]

/-- `s log b = log((1 - p)/2)`, since `b^s = (1 - p)/2`. -/
theorem mul_log_b (hP : 2 * P.a ^ s + 2 * P.b ^ s = 1) :
    s * Real.log P.b = Real.log ((1 - prob P s) / 2) := by
  rw [show (1 - prob P s) / 2 = P.b ^ s by unfold prob; linarith, Real.log_rpow P.b_pos]

/-- `λ_1 = p log a + (1 - p) log b = -(log 2 + H(p))/s`, tex line 2876. -/
theorem lyap₁_value (hs0 : 0 < s) (hP : 2 * P.a ^ s + 2 * P.b ^ s = 1) :
    prob P s * Real.log P.a + (1 - prob P s) * Real.log P.b =
      -(Real.log 2 + H (prob P s)) / s := by
  obtain ⟨h0, h1⟩ := prob_pos_lt_one P hP
  have ha := mul_log_a P (s := s)
  have hb := mul_log_b P hP
  rw [Real.log_div h0.ne' two_ne_zero] at ha
  rw [Real.log_div (by linarith) two_ne_zero] at hb
  rw [eq_div_iff hs0.ne', H]
  linear_combination prob P s * ha + (1 - prob P s) * hb

/-- `λ_2 = p log b + (1 - p) log a = -(log 2 + J(p))/s`, tex line 2877. -/
theorem lyap₂_value (hs0 : 0 < s) (hP : 2 * P.a ^ s + 2 * P.b ^ s = 1) :
    prob P s * Real.log P.b + (1 - prob P s) * Real.log P.a =
      -(Real.log 2 + J (prob P s)) / s := by
  obtain ⟨h0, h1⟩ := prob_pos_lt_one P hP
  have ha := mul_log_a P (s := s)
  have hb := mul_log_b P hP
  rw [Real.log_div h0.ne' two_ne_zero] at ha
  rw [Real.log_div (by linarith) two_ne_zero] at hb
  rw [eq_div_iff hs0.ne', J]
  linear_combination prob P s * hb + (1 - prob P s) * ha

variable (t : Fin 8 → ℝ)

/-- The two exponents and the two ratios of `ex:projection_double_dimensional`, tex lines 2872
to 3055: for every invariant `s`-equilibrium state `μ`,
`λ_1(𝖠, μ) = -(log 2 + H(p))/s`, `λ_2(𝖠, μ) = -(log 2 + J(p))/s`, `-h_0(μ)/λ_1(𝖠, μ) = s` and
`-h_0(μ)/λ_2(𝖠, μ) = s (log 2 + H(p))/(log 2 + J(p))`. The entropy and the exponents are those of
`isEquilibriumState_spec`, computed through `thm:entropy_eq_gibbs` and
`thm:eq_state_is_sum`. -/
theorem isEquilibriumState_ratios (hfk : EquilibriumGibbsStatement.{0})
    (hfjj : FraserJordanJurgaDecomposition.{0}) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hP : 2 * P.a ^ s + 2 * P.b ^ s = 1) (μ : Measure (ℤ → Fin 4)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : (sys P t).IsEquilibriumState s μ) :
    (sys P t).lyapunov₁ μ = -(Real.log 2 + H (prob P s)) / s ∧
      (sys P t).lyapunov₂ μ = -(Real.log 2 + J (prob P s)) / s ∧
      -entropy μ / (sys P t).lyapunov₁ μ = s ∧
      -entropy μ / (sys P t).lyapunov₂ μ = s * ratio (prob P s) := by
  obtain ⟨h0, h1⟩ := prob_pos_lt_one P hP
  obtain ⟨-, hent, -, hl₁, hl₂⟩ := isEquilibriumState_spec P t hfk hfjj hs0 hs1 hP μ hinv heq
  rw [lyap₁_value P hs0 hP] at hl₁
  rw [lyap₂_value P hs0 hP] at hl₂
  have hH := log_two_add_H_pos h0 h1
  have hJ := log_two_add_J_pos h0 h1
  refine ⟨hl₁, hl₂, ?_, ?_⟩
  · rw [hent, hl₁]
    field_simp
  · rw [hent, hl₂, ratio]
    field_simp

end Exponents

/-! ### The dimensions of the coordinate projections -/

/-- `thm:eq_state_proj_dim` for `ex:projection_double_dimensional`, tex lines 2886 to 2893:
under the projective exponential separation condition, for every invariant `s`-equilibrium state
`μ` with `0 < s ≤ 1`, `2 a^s + 2 b^s = 1` and `p = 2 a^s`, both coordinate projections
`(proj_c)_*(π_*μ)` are double-dimensional with the pointwise dimension values `s` and
`s (log 2 + H(p))/(log 2 + J(p)) < s`, upper packing dimension `s` and lower Hausdorff dimension
`s (log 2 + H(p))/(log 2 + J(p))`, and each value occurs on a set of positive measure. The values
come from `isEquilibriumState_ratios` and `min{1, ·}` leaves them unchanged. -/
theorem marginal_spec (hms : MorrisShmerkinLyapunov.{0}) (hfk : EquilibriumGibbsStatement.{0})
    (hfjj : FraserJordanJurgaDecomposition.{0}) (hjr : JordanRapaportDimension.{0})
    (P : Params) (t : Fin 8 → ℝ) (hsep : (sys P t).ProjExpSeparation) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s ≤ 1) (hP : 2 * P.a ^ s + 2 * P.b ^ s = 1) (μ : Measure (ℤ → Fin 4))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : (sys P t).IsEquilibriumState s μ) (c : ZMod 2) :
    s * ratio (prob P s) < s ∧
      IsDoubleDim ((sys P t).marginal c μ) ∧
      HasLocalDimPair ((sys P t).marginal c μ) s (s * ratio (prob P s)) ∧
      upperPackingDim ((sys P t).marginal c μ) = s ∧
      lowerHausdorffDim ((sys P t).marginal c μ) = s * ratio (prob P s) ∧
      0 < (sys P t).marginal c μ {x | HasLocalDim ((sys P t).marginal c μ) x s} ∧
      0 < (sys P t).marginal c μ
        {x | HasLocalDim ((sys P t).marginal c μ) x (s * ratio (prob P s))} := by
  obtain ⟨h0, h1⟩ := prob_pos_lt_one P hP
  have hhalf := half_lt_prob P hs0 hP
  obtain ⟨-, -, e₁, e₂⟩ := isEquilibriumState_ratios P t hfk hfjj hs0 hs1 hP μ hinv heq
  have hlt : s * ratio (prob P s) < s :=
    mul_lt_of_lt_one_right hs0 (ratio_lt_one hhalf h1)
  have m₁ : min 1 (-entropy μ / (sys P t).lyapunov₁ μ) = s := by rw [e₁, min_eq_right hs1]
  have m₂ : min 1 (-entropy μ / (sys P t).lyapunov₂ μ) = s * ratio (prob P s) := by
    rw [e₂, min_eq_right (by linarith)]
  obtain ⟨hdd, hup, hlow, hpos₁, hpos₂⟩ := (sys P t).eq_state_proj_dim hms hfk hfjj hjr
    (withRotations P t) (proximal P t) hsep hs0 (by linarith) μ hinv heq c
  rw [m₁, m₂] at hdd
  rw [m₁] at hup hpos₁
  rw [m₂] at hlow hpos₂
  exact ⟨hlt, hdd.isDoubleDim hlt.ne' hpos₁ hpos₂, hdd, hup, hlow, hpos₁, hpos₂⟩

end Gibbs

end PrescribedExample

end BoxLike
