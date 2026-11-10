module

/-
`rem:threshold_bound` in `sec:dimension_result_proof`: the proof of `thm:main2` gives
`\dim_H X ≥ min{dimaff(X), 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)}` for every proximal box-like self-affine set
with rotations whose projective system has no exact overlaps and `dimaff(X) < 2`, without the
strong open set condition or projective exponential separation. "In the notation of that
proof, suppose that `h > -λ_2` and reduce `W_n` to `⌊|b_n|⁻¹⌋` words. Then `#W_n ≤ |b_n|⁻¹` gives
`h_2(ν_n) = 0` by the same argument. Since `n⁻¹ log #W_n → -λ_2 > -λ_1`, we have
`dim((proj_x ∘ π_n)_*ν_n) = 1` for all sufficiently large `n`, and hence
`dim((π_n)_*ν_n) = 1 + (log #W_n + log |a_n|)/(-log |b_n|) → 2 - λ_1/λ_2`." Each `(π_n)_*ν_n` is
supported on `X`, so `\dim_H X ≥ 2 - λ_1/λ_2`; the case `h ≤ -λ_2` is `thm:main2` itself, and
`h ≤ -λ_2` is equivalent to `dimaff(X) ≤ 2 - λ_1/λ_2` by `eq:diml_min2`.

The typical families `W_n`, the diagonal subsystems and their Bernoulli measures `ν_n`, the
vanishing of `q_n = h_2(ν_n)` from `log #W_n ≤ -log |b_n|`, and the dimension formula
`dim((π_n)_*ν_n) = d_{x,n} + (log #W_n + d_{x,n} log |a_n|) / (-log |b_n|)` with
`d_{x,n} = min{1, log #W_n / (-log |a_n|)}` are those of `BoxLike/MainTwoProse/Endpoint.lean`.
The reduction to `⌊|b_n|⁻¹⌋` words is possible for
all large `n`, since `log #W_n / n → h > -λ_2` and `log ⌊|b_n|⁻¹⌋ / n → -λ_2`, by the squeeze
`|b_n|⁻¹ / 2 ≤ ⌊|b_n|⁻¹⌋ ≤ |b_n|⁻¹`. The reduction to a proximal diagonal generator through
`thm:two-block-normalisation` is as in `System.main2_prose_of_pressure`, the attractor, `dimaff`
and the ratio `λ_1/λ_2` being invariant under the second iterate.

* `eventually_subsystemDim_eq_of_tendsto`: `d_{x,n} = 1` for all large `n`, so
  `dim((π_n)_*ν_n) = 1 + (log #W_n + log |a_n|) / (-log |b_n|)`.
* `tendsto_one_add_sub_div`: `1 + (log #W_n + log |a_n|) / (-log |b_n|) → 2 - λ_1/λ_2`.
* `lyapDim_neg_eq_threshold`: the limit is the middle case of `eq:diml_min2` at `h_0 = -λ_2`.
* `System.le_dimH_attractor_of_entropy_gt_normalised`: `\dim_H X ≥ 2 - λ_1/λ_2` when `h > -λ_2`,
  for a tuple containing a proximal diagonal generator.
* `System.le_dimH_attractor_of_entropy_gt`, `System.le_dimH_attractor_of_entropy_gt_prose`:
  the same for every proximal tuple, with and without the statement hypotheses.
* `System.threshold_bound`: `rem:threshold_bound`, with the statement hypotheses of
  `System.main2_prose`.
* `System.threshold_bound_prose`: `rem:threshold_bound` with no literature hypothesis, the
  statements being the library theorems `shannonMcMillanBreiman`, `morrisShmerkinLyapunov_holds`,
  `equilibriumGibbs`, `fraserJordanJurgaDecomposition_holds`, `fengLedrappierYoung_holds` and
  `kittleKoglerDimension_holds`.
-/
public import BoxLike.EquilibriumGibbs
public import BoxLike.FengLedrappierYoung
public import BoxLike.FraserJordanJurga.Main
public import BoxLike.KittleKogler
public import BoxLike.LyapunovDim
public import BoxLike.MainTwoFree
public import BoxLike.MainTwoProse.Endpoint
public import BoxLike.MainTwoProse.TypicalWordsSMB
public import BoxLike.MorrisShmerkin
public import BoxLike.ShannonMcMillanBreiman

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set

universe u

/-! ### The limit of the dimensions -/

/-- `rem:threshold_bound`, "since `n⁻¹ log #W_n → -λ_2 > -λ_1`, we have
`dim((proj_x ∘ π_n)_*ν_n) = 1` for all sufficiently large `n`, and hence
`dim((π_n)_*ν_n) = 1 + (log #W_n + log |a_n|)/(-log |b_n|)`": the ratio `log #W_n / (-log |a_n|)`
tends to `λ_2/λ_1 > 1`, so `d_{x,n} = min{1, log #W_n / (-log |a_n|)} = 1` for all large `n`, and
the formula `dim((π_n)_*ν_n) = d_{x,n} + (log #W_n + d_{x,n} log |a_n|) / (-log |b_n|)` of
`System.IsHomDiag.isExactDim_map_proj` becomes `1 + (log #W_n + log |a_n|) / (-log |b_n|)`. -/
theorem eventually_subsystemDim_eq_of_tendsto {H χ₁ : ℕ → ℝ} (χ₂ : ℕ → ℝ) {n : ℕ → ℝ} {l₁ l₂ : ℝ}
    (hl : l₂ < l₁) (hl₁ : l₁ < 0) (hn : ∀ᶠ m in atTop, n m ≠ 0)
    (hH : Tendsto (fun m => H m / n m) atTop (𝓝 (-l₂)))
    (h₁ : Tendsto (fun m => χ₁ m / n m) atTop (𝓝 (-l₁))) :
    ∀ᶠ m in atTop, subsystemDim (H m) (χ₁ m) (χ₂ m) = 1 + (H m - χ₁ m) / χ₂ m := by
  have hratio : Tendsto (fun m => H m / n m / (χ₁ m / n m)) atTop (𝓝 (-l₂ / -l₁)) :=
    hH.div h₁ (neg_ne_zero.2 hl₁.ne)
  have h1 : 1 < -l₂ / -l₁ := by
    rw [neg_div_neg_eq, one_lt_div_of_neg hl₁]
    exact hl
  filter_upwards [hn, hratio.eventually (lt_mem_nhds h1)] with m hm hlt
  rw [div_div_div_cancel_right₀ hm] at hlt
  rw [subsystemDim, min_eq_left hlt.le, mul_one]

/-- `rem:threshold_bound`, "`dim((π_n)_*ν_n) = 1 + (log #W_n + log |a_n|)/(-log |b_n|) →
2 - λ_1/λ_2`": when `log #W_n / n → -λ_2`, `log |a_n| / n → λ_1` and `log |b_n| / n → λ_2`, the
quotient tends to
`(-λ_2 + λ_1) / (-λ_2) = 1 - λ_1/λ_2`. -/
theorem tendsto_one_add_sub_div {H χ₁ χ₂ : ℕ → ℝ} {n : ℕ → ℝ} {l₁ l₂ : ℝ} (hl : l₂ < l₁)
    (hl₁ : l₁ < 0) (hn : ∀ᶠ m in atTop, n m ≠ 0)
    (hH : Tendsto (fun m => H m / n m) atTop (𝓝 (-l₂)))
    (h₁ : Tendsto (fun m => χ₁ m / n m) atTop (𝓝 (-l₁)))
    (h₂ : Tendsto (fun m => χ₂ m / n m) atTop (𝓝 (-l₂))) :
    Tendsto (fun m => 1 + (H m - χ₁ m) / χ₂ m) atTop (𝓝 (2 - l₁ / l₂)) := by
  have hl₂ : l₂ ≠ 0 := (hl.trans hl₁).ne
  have hlim : Tendsto (fun m => 1 + (H m / n m - χ₁ m / n m) / (χ₂ m / n m)) atTop
      (𝓝 (1 + (-l₂ - -l₁) / -l₂)) :=
    tendsto_const_nhds.add ((hH.sub h₁).div h₂ (neg_ne_zero.2 hl₂))
  have he : 1 + (-l₂ - -l₁) / -l₂ = 2 - l₁ / l₂ := by
    field_simp
    ring
  rw [he] at hlim
  refine hlim.congr' ?_
  filter_upwards [hn] with m hm
  rw [← sub_div, div_div_div_cancel_right₀ hm]

/-- `rem:threshold_bound`: the limit `2 - λ_1/λ_2` is the middle case of `eq:diml_min2` at the
entropy `h_0 = -λ_2`, which lies in `(-λ_1, -λ_1 - λ_2]` for `λ_2 < λ_1 < 0`, and evaluates to
`1 - (-λ_2 + λ_1)/λ_2 = 2 - λ_1/λ_2`. -/
theorem lyapDim_neg_eq_threshold {l₁ l₂ : ℝ} (hl : l₂ < l₁) (hl₁ : l₁ < 0) :
    lyapDim (-l₂) l₁ l₂ = 2 - l₁ / l₂ := by
  have hl₂ : l₂ < 0 := hl.trans hl₁
  have hn : ¬ -l₂ ≤ -l₁ := not_le.2 (by linarith)
  have hle : -l₂ ≤ -l₁ - l₂ := by linarith
  have h2 : l₂ ≠ 0 := hl₂.ne
  unfold lyapDim
  rw [ite_eq_right hn, ite_eq_left hle]
  field_simp
  ring

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)

/-! ### The bound above the threshold -/

/-- `rem:threshold_bound`, the bound `\dim_H X ≥ 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)` for an `s`-equilibrium
state `μ` with `0 < s < 2` and `h_0(μ) > -λ_2(𝖠, μ)`, for a tuple containing a proximal diagonal
generator whose projective system has no exact overlaps. The typical families of the proof of
`thm:main2` (`exists_typical_words_prose`) are reduced to `⌊|b_n|⁻¹⌋` words, as under
`it:main2_threshold`, which is possible for all large `n` since `log #W_n / n → h > -λ_2` and
`log ⌊|b_n|⁻¹⌋ / n → -λ_2`. Then `log #W_n = log ⌊|b_n|⁻¹⌋ ≤ -log |b_n|`, so `q_{y,n} = 0` and
`q_n = h_2(ν_n) = 0`, and `le_dimH_attractor_of_family` gives `\dim_H X ≥ dim((π_n)_*ν_n)`;
`log #W_n / n → -λ_2 > -λ_1`, so `dim((proj_x ∘ π_n)_*ν_n) = 1` for all large `n` and
`dim((π_n)_*ν_n) = 1 + (log #W_n + log |a_n|) / (-log |b_n|)`
(`eventually_subsystemDim_eq_of_tendsto`), which tends to `2 - λ_1/λ_2`
(`tendsto_one_add_sub_div`).
Depends on: `ShannonMcMillanBreimanStatement`, `MorrisShmerkinLyapunov`,
`EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, `FengLedrappierYoung`,
`KittleKoglerDimension`. -/
theorem le_dimH_attractor_of_entropy_gt_normalised (hsmb : ShannonMcMillanBreimanStatement.{u})
    (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal)
    (hfree : S.NoExactOverlaps) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) (hent : -S.lyapunov₂ μ < entropy μ) :
    ENNReal.ofReal (2 - S.lyapunov₁ μ / S.lyapunov₂ μ) ≤ dimH S.attractor := by
  classical
  have : Nonempty ι := nonempty_of_measure μ
  have hl := hms S hrot hdiag hs0 hs2 μ hinv heq
  have hl1 := S.lyapunov₁_neg hinv
  obtain ⟨n, W, a, b, hn, hnpos, hWne, hWn, hH, ha, hb⟩ :=
    S.exists_typical_words_prose hsmb hfk hfjj hrot hdiag hs0 hs2 μ hinv heq
  -- the entries `a_m`, `b_m` are non-zero with modulus below one
  have hab0 : ∀ m, a m ≠ 0 ∧ b m ≠ 0 ∧ |b m| < 1 := fun m => by
    obtain ⟨w, hw⟩ := hWne m
    obtain ⟨hw0, hwa, hwb⟩ := (S.matWord_eq_boxMat_zero_iff _ _ _).1 (hWn m w hw).2
    have hne : w ≠ [] := by
      rintro rfl
      have hl0 := (hWn m _ hw).1
      have hp := hnpos m
      simp at hl0
      omega
    refine ⟨hwa ▸ S.gDeriv_ne_zero _, hwb ▸ S.gDeriv_ne_zero _, ?_⟩
    rw [← hwb]
    exact S.abs_gDeriv_lt_one fun h =>
      hne (List.length_eq_zero_iff.1 (by simpa using congrArg List.length h))
  -- eventually `|b_m| < |a_m|`, from `λ_2 < λ_1`: finitely many lengths are discarded
  have hlt : ∀ᶠ m in atTop, |b m| < |a m| := by
    filter_upwards [hb.eventually_lt ha hl] with m hm
    have hnm : (0 : ℝ) < n m := by exact_mod_cast hnpos m
    rw [div_lt_div_iff_of_pos_right hnm] at hm
    exact (Real.log_lt_log_iff (abs_pos.2 (hab0 m).2.1) (abs_pos.2 (hab0 m).1)).1 hm
  have hn0 : ∀ᶠ m in atTop, (n m : ℝ) ≠ 0 := Eventually.of_forall fun m => by
    exact_mod_cast (hnpos m).ne'
  have ha' : Tendsto (fun m => -Real.log |a m| / n m) atTop (𝓝 (-S.lyapunov₁ μ)) := by
    simpa only [neg_div] using ha.neg
  have hb' : Tendsto (fun m => -Real.log |b m| / n m) atTop (𝓝 (-S.lyapunov₂ μ)) := by
    simpa only [neg_div] using hb.neg
  have hfloor : ∀ m, 1 ≤ ⌊|b m|⁻¹⌋₊ := fun m =>
    (Nat.one_le_floor_iff _).2 (one_le_inv_iff₀.2 ⟨abs_pos.2 (hab0 m).2.1, (hab0 m).2.2.le⟩)
  have hWpos : ∀ m, (0 : ℝ) < (W m).card := fun m => by
    exact_mod_cast Finset.card_pos.2 (hWne m)
  have hflpos : ∀ m, (0 : ℝ) < ⌊|b m|⁻¹⌋₊ := fun m => by exact_mod_cast hfloor m
  -- `log ⌊|b_m|⁻¹⌋ / m → -λ_2`, since `|b_m|⁻¹ / 2 ≤ ⌊|b_m|⁻¹⌋ ≤ |b_m|⁻¹`
  have hfl : Tendsto (fun m => Real.log ⌊|b m|⁻¹⌋₊ / n m) atTop (𝓝 (-S.lyapunov₂ μ)) := by
    have hlow : Tendsto (fun m => (-Real.log 2 + -Real.log |b m|) / ((n m : ℝ) + 0)) atTop
        (𝓝 (-S.lyapunov₂ μ)) :=
      tendsto_add_div_add le_rfl hn hb'
    simp only [add_zero] at hlow
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hb'
      (Eventually.of_forall fun m => ?_) (Eventually.of_forall fun m => ?_)
    · have hnm : (0 : ℝ) ≤ n m := Nat.cast_nonneg _
      refine div_le_div_of_nonneg_right ?_ hnm
      have hx : (0 : ℝ) < |b m|⁻¹ := inv_pos.2 (abs_pos.2 (hab0 m).2.1)
      have h2 : |b m|⁻¹ / 2 ≤ ⌊|b m|⁻¹⌋₊ := by
        have := Nat.lt_floor_add_one |b m|⁻¹
        have h1 : (1 : ℝ) ≤ ⌊|b m|⁻¹⌋₊ := by exact_mod_cast hfloor m
        linarith
      have := Real.log_le_log (by positivity) h2
      rwa [Real.log_div hx.ne' two_ne_zero, Real.log_inv, sub_eq_add_neg, add_comm] at this
    · have hnm : (0 : ℝ) ≤ n m := Nat.cast_nonneg _
      refine div_le_div_of_nonneg_right ?_ hnm
      rw [← Real.log_inv]
      exact Real.log_le_log (hflpos m) (Nat.floor_le (inv_nonneg.2 (abs_nonneg _)))
  -- `⌊|b_m|⁻¹⌋ ≤ #W_m` for all large `m`, since `log ⌊|b_m|⁻¹⌋ / m → -λ_2 < h ← log #W_m / m`
  have hcard : ∀ᶠ m in atTop, ⌊|b m|⁻¹⌋₊ ≤ (W m).card := by
    filter_upwards [hfl.eventually_lt hH hent] with m hm
    have hnm : (0 : ℝ) < n m := by exact_mod_cast hnpos m
    rw [div_lt_div_iff_of_pos_right hnm] at hm
    exact_mod_cast ((Real.log_lt_log_iff (hflpos m) (hWpos m)).1 hm).le
  -- reduce `W_m` to `⌊|b_m|⁻¹⌋` words, as in the case `h ≤ -λ_2`
  have hex : ∀ m, ∃ W' ⊆ W m, ⌊|b m|⁻¹⌋₊ ≤ (W m).card → W'.card = ⌊|b m|⁻¹⌋₊ := fun m => by
    by_cases h : ⌊|b m|⁻¹⌋₊ ≤ (W m).card
    · obtain ⟨W', hsub, hW'⟩ := Finset.exists_subset_card_eq h
      exact ⟨W', hsub, fun _ => hW'⟩
    · exact ⟨W m, le_rfl, fun h' => absurd h' h⟩
  choose W' hW'sub hW'card using hex
  have hW'card' : ∀ᶠ m in atTop, (W' m).card = ⌊|b m|⁻¹⌋₊ :=
    hcard.mono fun m hm => hW'card m hm
  have hW'ne : ∀ᶠ m in atTop, (W' m).Nonempty := by
    filter_upwards [hW'card'] with m hm
    rw [← Finset.card_pos, hm]
    exact hfloor m
  -- `log #W_m = log ⌊|b_m|⁻¹⌋ ≤ -log |b_m|`, so `q_m = 0` and `\dim_H X ≥ dim((π_m)_*ν_m)`
  have hle : ∀ᶠ m in atTop, ENNReal.ofReal (subsystemDim (Real.log (W' m).card)
      (-Real.log |a m|) (-Real.log |b m|)) ≤ dimH S.attractor := by
    filter_upwards [hlt, hW'card', hW'ne] with m hm hmc hmne
    have key := S.le_dimH_attractor_of_family hly hkk hfree (v := []) (by simp) hmne
      (hnpos m) (fun w hw => hWn m w (hW'sub m hw)) (by simpa using hm) (Or.inl ?_)
    · simpa using key
    · simp only [codeWord_nil, gDeriv_nil, one_mul]
      rw [← Real.log_inv, hmc]
      exact Real.log_le_log (hflpos m) (Nat.floor_le (inv_nonneg.2 (abs_nonneg _)))
  -- `log #W_m / m → -λ_2`
  have hH' : Tendsto (fun m => Real.log (W' m).card / n m) atTop (𝓝 (-S.lyapunov₂ μ)) :=
    hfl.congr' (hW'card'.mono fun m hm => by simp only [hm])
  -- `d_{x,m} = 1` for all large `m`, so
  -- `dim((π_m)_*ν_m) = 1 + (log #W_m + log |a_m|) / (-log |b_m|)`
  have hle' : ∀ᶠ m in atTop, ENNReal.ofReal (1 + (Real.log (W' m).card - -Real.log |a m|) /
      -Real.log |b m|) ≤ dimH S.attractor := by
    filter_upwards [hle, eventually_subsystemDim_eq_of_tendsto (fun m => -Real.log |b m|) hl hl1
      hn0 hH' ha'] with m hm he
    rwa [he] at hm
  -- `dim ν_m → 2 - λ_1/λ_2`, and each `ν_m` is supported on `X`
  have hlim := tendsto_one_add_sub_div hl hl1 hn0 hH' ha' hb'
  exact le_of_tendsto (ENNReal.continuous_ofReal.tendsto _ |>.comp hlim)
    (hle'.mono fun m hm => hm)

/-- `rem:threshold_bound`, the bound `\dim_H X ≥ 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)` for an `s`-equilibrium
state `μ` with `0 < s < 2` and `h_0(μ) > -λ_2(𝖠, μ)`, for every proximal tuple with rotations
whose projective system has no exact overlaps: the reduction to a proximal diagonal generator
through `thm:two-block-normalisation`, the absence of exact overlaps passing to the second
iterate, which has the same attractor, the entropy `2h_0(μ)` and the exponents `2λ_i(𝖠, μ)`, so
that the hypothesis `h_0 > -λ_2` and the ratio `λ_1/λ_2` are unchanged.
Depends on: `ShannonMcMillanBreimanStatement`, `MorrisShmerkinLyapunov`,
`EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, `FengLedrappierYoung`,
`KittleKoglerDimension`. -/
theorem le_dimH_attractor_of_entropy_gt (hsmb : ShannonMcMillanBreimanStatement.{u})
    (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (hrot : S.WithRotations) (hprox : S.Proximal)
    (hfree : S.NoExactOverlaps) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) (hent : -S.lyapunov₂ μ < entropy μ) :
    ENNReal.ofReal (2 - S.lyapunov₁ μ / S.lyapunov₂ μ) ≤ dimH S.attractor := by
  have := nonempty_of_measure μ
  rcases hprox.hasProximalDiagonal_or_sq with h | h
  · exact S.le_dimH_attractor_of_entropy_gt_normalised hsmb hms hfk hfjj hly hkk hrot h hfree
      hs0 hs2 μ hinv heq hent
  · have e1 := S.lyapunov₁_sq_map_group (S.tendsto_lyapunov₁ hinv)
    have e2 := S.lyapunov₂_sq_map_group (S.tendsto_lyapunov₂ hinv)
    have hent2 : -S.sq.lyapunov₂ (μ.map group) < entropy (μ.map group) := by
      rw [entropy_map_group hinv, e2]
      linarith
    have key := S.sq.le_dimH_attractor_of_entropy_gt_normalised hsmb hms hfk hfjj hly hkk
      (S.sq_withRotations hrot) h hfree.sq hs0 hs2 (μ.map group)
      (measurePreserving_shift_map_group hinv) (heq.map_group hinv hs0.le) hent2
    rwa [S.attractor_sq, e1, e2, mul_div_mul_left _ _ two_ne_zero] at key

/-- `rem:threshold_bound`, the bound `\dim_H X ≥ 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)` for `h_0(μ) > -λ_2(𝖠, μ)`
with no literature hypothesis: the statements of `le_dimH_attractor_of_entropy_gt` are the
library theorems `shannonMcMillanBreiman`, `morrisShmerkinLyapunov_holds`, `equilibriumGibbs`,
`fraserJordanJurgaDecomposition_holds`, `fengLedrappierYoung_holds` and
`kittleKoglerDimension_holds`. -/
theorem le_dimH_attractor_of_entropy_gt_prose (hrot : S.WithRotations) (hprox : S.Proximal)
    (hfree : S.NoExactOverlaps) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) (hent : -S.lyapunov₂ μ < entropy μ) :
    ENNReal.ofReal (2 - S.lyapunov₁ μ / S.lyapunov₂ μ) ≤ dimH S.attractor :=
  S.le_dimH_attractor_of_entropy_gt shannonMcMillanBreiman morrisShmerkinLyapunov_holds
    equilibriumGibbs fraserJordanJurgaDecomposition_holds fengLedrappierYoung_holds
    kittleKoglerDimension_holds hrot hprox hfree hs0 hs2 μ hinv heq hent

/-! ### The remark -/

/-- `rem:threshold_bound`. Let `X` be a proximal box-like self-affine set with rotations whose
projective system has no exact overlaps, with `dimaff(X) < 2`, and let `μ` be an `s`-equilibrium
state for `s = dimaff(X)`. Then `\dim_H X ≥ min{dimaff(X), 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)}`, without the
strong open set condition or projective exponential separation. If `h_0(μ) ≤ -λ_2(𝖠, μ)`, then
`dimaff(X) ≤ 2 - λ_1/λ_2` by `eq:diml_min2` and `eq:simple_lyapunov`, and `thm:main2` gives
`\dim_H X = dimaff(X)`; otherwise `le_dimH_attractor_of_entropy_gt` gives
`\dim_H X ≥ 2 - λ_1/λ_2`.
Depends on: `ShannonMcMillanBreimanStatement`, `MorrisShmerkinLyapunov`,
`EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, `FengLedrappierYoung`,
`KittleKoglerDimension`. -/
theorem threshold_bound (hsmb : ShannonMcMillanBreimanStatement.{u})
    (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal)
    (hfree : S.NoExactOverlaps) (h2 : S.dimaff < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ) :
    ENNReal.ofReal (min S.dimaff (2 - S.lyapunov₁ μ / S.lyapunov₂ μ)) ≤ dimH S.attractor := by
  have := S.nontrivial_of_withRotations hrot
  have hs0 := S.dimaff_pos
  rcases le_or_gt (entropy μ) (-S.lyapunov₂ μ) with hent | hent
  · -- the case `h_0(μ) ≤ -λ_2` of `thm:main2`: `\dim_H X = dimaff(X)`
    have hl := S.simple_lyapunov hms hrot hprox hs0 h2 μ hinv heq
    have hl1 := S.lyapunov₁_neg hinv
    have henergy : entropy μ + energy (S.lyapunov₁ μ) (S.lyapunov₂ μ) S.dimaff = 0 := by
      rw [← heq.pressure_eq hinv hs0.le, S.pressure_dimaff]
    have key := S.main2_prose_lt_two hsmb hms hfk hfjj hly hkk hrot hprox hfree h2 μ hinv heq
      (Or.inl ((entropy_le_iff hl hl1 h2 henergy).1 hent))
    rw [key]
    exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
  · -- the case `h_0(μ) > -λ_2`: `\dim_H X ≥ 2 - λ_1/λ_2`
    exact (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans
      (S.le_dimH_attractor_of_entropy_gt hsmb hms hfk hfjj hly hkk hrot hprox hfree hs0 h2 μ
        hinv heq hent)

/-- `rem:threshold_bound` with no literature hypothesis: the statements of `threshold_bound` are
the library theorems `shannonMcMillanBreiman`, `morrisShmerkinLyapunov_holds`,
`equilibriumGibbs`, `fraserJordanJurgaDecomposition_holds`, `fengLedrappierYoung_holds` and
`kittleKoglerDimension_holds`. -/
theorem threshold_bound_prose [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal)
    (hfree : S.NoExactOverlaps) (h2 : S.dimaff < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ) :
    ENNReal.ofReal (min S.dimaff (2 - S.lyapunov₁ μ / S.lyapunov₂ μ)) ≤ dimH S.attractor :=
  S.threshold_bound shannonMcMillanBreiman morrisShmerkinLyapunov_holds equilibriumGibbs
    fraserJordanJurgaDecomposition_holds fengLedrappierYoung_holds kittleKoglerDimension_holds
    hrot hprox hfree h2 μ hinv heq

end System

end BoxLike
