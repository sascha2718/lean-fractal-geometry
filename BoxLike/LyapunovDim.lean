module

/-
The real-variable part of `sec:affinity_dim`, `sec:dimension_of_projections` and
`sec:dimension_result_proof`. The entropy `h = h_0(μ)` and the Lyapunov exponents
`l1 = λ_1(𝖠, μ)`, `l2 = λ_2(𝖠, μ)` are real parameters with `l2 ≤ l1 < 0`.

* `energy`: the `s`-energy `Λ(𝖠, μ, s)` as the piecewise linear function of `eq:energy_def`.
* `lyapDim`, `lyapDim_eq`: the Lyapunov dimension as the piecewise formula `eq:diml_min2`,
  and the fact that it is the unique `s ≥ 0` with `h + Λ(s) = 0`.
* `entropy_lt_iff`, `entropy_le_iff`: the equivalence of `h_0(μ) < -λ_2` with
  `s < 2 - λ_1/λ_2`, from the proofs of `thm:main1` and `thm:main2`.
* `min_neg_div_le`: the two values of `thm:eq_state_proj_dim` are ordered.
* `min_ne_min_iff`, `min_eq_one_of_le`: the two values of `thm:eq_state_proj_dim` are distinct
  exactly below the threshold of `thm:main1`, and both equal one at and above it.
* `ledrappierYoung_small`, `ledrappierYoung_large`: `eq:main_extended1` and
  `eq:main_extended2`.
-/
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic

@[expose] public section

namespace BoxLike

/-- The `s`-energy `Λ(𝖠, μ, s)` of `eq:energy_def` as a function of the Lyapunov exponents. -/
noncomputable def energy (l1 l2 s : ℝ) : ℝ :=
  if s ≤ 1 then s * l1 else if s ≤ 2 then l1 + (s - 1) * l2 else s / 2 * (l1 + l2)

/-- The Lyapunov dimension `dim_L(𝖠, μ)` in the form `eq:diml_min2`. -/
noncomputable def lyapDim (h l1 l2 : ℝ) : ℝ :=
  if h ≤ -l1 then -h / l1 else if h ≤ -l1 - l2 then 1 - (h + l1) / l2 else -(2 * h) / (l1 + l2)

variable {h l1 l2 s : ℝ}

/-- `eq:diml_min2`: the piecewise formula is the unique `s ≥ 0` with `h_0(μ) + Λ(𝖠, μ, s) = 0`.
In particular `dim_L(𝖠, μ) = dimaff(𝖠)` for an equilibrium state at `s = dimaff(𝖠)`. -/
theorem lyapDim_eq (hl : l2 ≤ l1) (hl1 : l1 < 0) (heq : h + energy l1 l2 s = 0) :
    lyapDim h l1 l2 = s := by
  have hl2 : l2 < 0 := lt_of_le_of_lt hl hl1
  have hl1' : l1 ≠ 0 := hl1.ne
  have hl2' : l2 ≠ 0 := hl2.ne
  unfold energy at heq
  unfold lyapDim
  split_ifs at heq with hs1 hs2
  · have hh : h = -(s * l1) := by linarith
    have hle : h ≤ -l1 := by
      have := mul_nonneg (sub_nonneg.2 hs1) (neg_nonneg.2 hl1.le)
      rw [hh]; nlinarith
    rw [ite_eq_left hle, hh]
    field_simp
  · have hh : h = -(l1 + (s - 1) * l2) := by linarith
    have hs1' : 0 < s - 1 := by linarith
    have hn : ¬ h ≤ -l1 := by
      have := mul_pos hs1' (neg_pos.2 hl2)
      rw [hh, not_le]; nlinarith
    have hle : h ≤ -l1 - l2 := by
      have := mul_nonneg (show 0 ≤ 2 - s by linarith) (neg_nonneg.2 hl2.le)
      rw [hh]; nlinarith
    rw [ite_eq_right hn, ite_eq_left hle, hh]
    field_simp
    ring
  · have hh : h = -(s / 2 * (l1 + l2)) := by linarith
    have hs2' : 0 < s / 2 - 1 := by linarith
    have hsum : l1 + l2 < 0 := by linarith
    have hn2 : ¬ h ≤ -l1 - l2 := by
      have := mul_pos hs2' (neg_pos.2 hsum)
      rw [hh, not_le]; nlinarith
    have hn1 : ¬ h ≤ -l1 := fun hle => hn2 (by linarith)
    rw [ite_eq_right hn1, ite_eq_right hn2, hh]
    have : l1 + l2 ≠ 0 := hsum.ne
    field_simp

/-- The entropy of an equilibrium state at a parameter `0 < s` is positive. -/
theorem entropy_pos (hl : l2 ≤ l1) (hl1 : l1 < 0) (hs : 0 < s)
    (heq : h + energy l1 l2 s = 0) : 0 < h := by
  have hl2 : l2 < 0 := lt_of_le_of_lt hl hl1
  unfold energy at heq
  split_ifs at heq with hs1 hs2
  · have := mul_pos hs (neg_pos.2 hl1); nlinarith
  · have := mul_pos (show 0 < s - 1 by linarith) (neg_pos.2 hl2); nlinarith
  · have := mul_pos (show 0 < s / 2 by linarith) (neg_pos.2 (show l1 + l2 < 0 by linarith))
    nlinarith

/-- From the proofs of `thm:main1` and `thm:main2`: for `s < 2` the inequality
`h_0(μ) < -λ_2(𝖠, μ)` holds exactly when `s < 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)`. -/
theorem entropy_lt_iff (hl : l2 < l1) (hl1 : l1 < 0) (hs2 : s < 2)
    (heq : h + energy l1 l2 s = 0) : h < -l2 ↔ s < 2 - l1 / l2 := by
  have hl2 : l2 < 0 := lt_trans hl hl1
  have hratio : l1 / l2 < 1 := by
    rw [div_lt_one_of_neg hl2]; exact hl
  have key : s < 2 - l1 / l2 ↔ (2 - s) * l2 < l1 := by
    rw [← div_lt_iff_of_neg hl2]; constructor <;> intro H <;> linarith
  unfold energy at heq
  split_ifs at heq with hs1 hs2'
  · have hh : h = -(s * l1) := by linarith
    have h1 : h < -l2 := by
      have := mul_nonneg (sub_nonneg.2 hs1) (neg_nonneg.2 hl1.le)
      rw [hh]; nlinarith
    exact iff_of_true h1 (by linarith)
  · have hh : h = -(l1 + (s - 1) * l2) := by linarith
    rw [key, hh]
    constructor <;> intro H <;> nlinarith
  · exact absurd hs2.le hs2'

/-- The non-strict form of `entropy_lt_iff`, used in the proof of `thm:main2`:
`dimaff(𝖠) ≤ 2 - λ_1/λ_2` if and only if `h_0(μ) ≤ -λ_2`. -/
theorem entropy_le_iff (hl : l2 < l1) (hl1 : l1 < 0) (hs2 : s < 2)
    (heq : h + energy l1 l2 s = 0) : h ≤ -l2 ↔ s ≤ 2 - l1 / l2 := by
  have hl2 : l2 < 0 := lt_trans hl hl1
  have hratio : l1 / l2 < 1 := by
    rw [div_lt_one_of_neg hl2]; exact hl
  have key : s ≤ 2 - l1 / l2 ↔ (2 - s) * l2 ≤ l1 := by
    rw [← div_le_iff_of_neg hl2]; constructor <;> intro H <;> linarith
  unfold energy at heq
  split_ifs at heq with hs1 hs2'
  · have hh : h = -(s * l1) := by linarith
    have h1 : h ≤ -l2 := by
      have := mul_nonneg (sub_nonneg.2 hs1) (neg_nonneg.2 hl1.le)
      rw [hh]; nlinarith
    exact iff_of_true h1 (by linarith)
  · have hh : h = -(l1 + (s - 1) * l2) := by linarith
    rw [key, hh]
    constructor <;> intro H <;> nlinarith
  · exact absurd hs2.le hs2'

/-- The two values `min{1, -h_0/λ_1}` and `min{1, -h_0/λ_2}` of `thm:eq_state_proj_dim` are
distinct exactly when `h_0(μ) < -λ_2(𝖠, μ)`. -/
theorem min_ne_min_iff_entropy_lt (hl : l2 < l1) (hl1 : l1 < 0) (hh : 0 < h) :
    min 1 (-h / l1) ≠ min 1 (-h / l2) ↔ h < -l2 := by
  have hl2 : l2 < 0 := lt_trans hl hl1
  constructor
  · intro hne
    by_contra hge
    rw [not_lt] at hge
    have h2 : 1 ≤ -h / l2 := by
      rw [le_div_iff_of_neg hl2]; linarith
    have h1 : 1 ≤ -h / l1 := by
      rw [le_div_iff_of_neg hl1]; linarith
    exact hne (by rw [min_eq_left h1, min_eq_left h2])
  · intro hlt
    have h2 : -h / l2 < 1 := by
      rw [div_lt_iff_of_neg hl2]; linarith
    have ht1 : 0 < -h / l1 := div_pos_of_neg_of_neg (by linarith) hl1
    have hm : -h / l1 * l1 = -h := div_mul_cancel₀ _ hl1.ne
    have h12 : -h / l2 < -h / l1 := by
      rw [div_lt_iff_of_neg hl2]
      nlinarith [mul_pos ht1 (sub_pos.2 hl)]
    rw [min_eq_right h2.le]
    exact (ne_of_gt (lt_min h2 h12))

/-- The two values of `thm:eq_state_proj_dim` are ordered:
`min{1, -h_0/λ_2} ≤ min{1, -h_0/λ_1}`. -/
theorem min_neg_div_le (hl : l2 ≤ l1) (hl1 : l1 < 0) (hh : 0 ≤ h) :
    min 1 (-h / l2) ≤ min 1 (-h / l1) := by
  have hl2 : l2 < 0 := lt_of_le_of_lt hl hl1
  refine min_le_min le_rfl ?_
  rw [div_le_iff_of_neg hl2]
  have ht1 : 0 ≤ -h / l1 := div_nonneg_of_nonpos (by linarith) hl1.le
  have hm : -h / l1 * l1 = -h := div_mul_cancel₀ _ hl1.ne
  nlinarith [mul_nonneg ht1 (sub_nonneg.2 hl)]

/-- `thm:main1`, the dichotomy: the two pointwise dimensions of the coordinate projections
are distinct exactly when `s < 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)`. -/
theorem min_ne_min_iff (hl : l2 < l1) (hl1 : l1 < 0) (hs0 : 0 < s) (hs2 : s < 2)
    (heq : h + energy l1 l2 s = 0) :
    min 1 (-h / l1) ≠ min 1 (-h / l2) ↔ s < 2 - l1 / l2 :=
  (min_ne_min_iff_entropy_lt hl hl1 (entropy_pos hl.le hl1 hs0 heq)).trans
    (entropy_lt_iff hl hl1 hs2 heq)

/-- `thm:main1`, at equality and above: both values are one. -/
theorem min_eq_one_of_le (hl : l2 < l1) (hl1 : l1 < 0) (hs2 : s < 2)
    (heq : h + energy l1 l2 s = 0) (hs : 2 - l1 / l2 ≤ s) :
    min 1 (-h / l1) = 1 ∧ min 1 (-h / l2) = 1 := by
  have hl2 : l2 < 0 := lt_trans hl hl1
  have hge : -l2 ≤ h := by
    by_contra hlt
    rw [not_le] at hlt
    exact absurd ((entropy_lt_iff hl hl1 hs2 heq).1 hlt) (not_lt.2 hs)
  refine ⟨min_eq_left ?_, min_eq_left ?_⟩
  · rw [le_div_iff_of_neg hl1]; linarith
  · rw [le_div_iff_of_neg hl2]; linarith

/-- `eq:main_extended1`: if `h_0(μ) ≤ -λ_1` and `h_1(μ) = h_2(μ) = 0`, then the
Ledrappier–Young formula `eq:feng_ledrappier_young` evaluates to `dim_L(𝖠, μ)`. -/
theorem ledrappierYoung_small (hle : h ≤ -l1) :
    (0 - h) / l1 + (0 - 0) / l2 = lyapDim h l1 l2 := by
  rw [lyapDim, ite_eq_left hle]; simp

/-- `eq:main_extended2`: if `-λ_1 < h_0(μ) ≤ -λ_1 - λ_2`, `h_1(μ) = h_0(μ) + λ_1` and
`h_2(μ) = 0`, then the Ledrappier–Young formula evaluates to `dim_L(𝖠, μ)`. -/
theorem ledrappierYoung_large (hl1 : l1 < 0) (hlt : -l1 < h) (hle : h ≤ -l1 - l2) :
    (h + l1 - h) / l1 + (0 - (h + l1)) / l2 = lyapDim h l1 l2 := by
  rw [lyapDim, ite_eq_right (not_le.2 hlt), ite_eq_left hle]
  have : l1 ≠ 0 := hl1.ne
  field_simp
  ring

/-- For `s < 2` the entropy of an equilibrium state satisfies `h_0(μ) < -λ_1 - λ_2`, so the
third case of `eq:diml_min2` does not occur in `thm:main_extended`. -/
theorem entropy_lt_of_lt_two (hl : l2 ≤ l1) (hl1 : l1 < 0) (hs2 : s < 2)
    (heq : h + energy l1 l2 s = 0) : h < -l1 - l2 := by
  have hl2 : l2 < 0 := lt_of_le_of_lt hl hl1
  unfold energy at heq
  split_ifs at heq with hs1 hs2'
  · have := mul_nonneg (sub_nonneg.2 hs1) (neg_nonneg.2 hl1.le); nlinarith
  · have := mul_pos (show 0 < 2 - s by linarith) (neg_pos.2 hl2); nlinarith
  · linarith

end BoxLike
