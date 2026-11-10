module

/-
The Lyapunov identities of `thm:eq_state_is_sum` in `sec:gibbs_measures`, second and third
lines: `λ_1(𝖠, μ) = \overline{λ}(𝖠, μ_1)` and `λ_2(𝖠, μ) = \overline{λ}(𝖠, μ_2)` for the image
`μ = \overline{τ}_*μ_1 + \overline{ω}_*μ_1 = q_*μ_1` of an ergodic `s`-Gibbs measure `μ_1` of the
potential `f_{1,s}` carried by `Σ_Z`, with `μ_2 = flip_*μ_1`, for `0 < s < 2`. Here `q = unCode`
forgets the axis.

The proof has two steps.

1. Along `𝐣 ∈ Σ_Z` over `𝐢 = q(𝐣)` the two lifts of `𝐢` are `𝐣` and `flip(𝐣)`. By
   `thm:matrix_products_g_derivatives` the singular values of `A_{i_{-n}} ⋯ A_{i_{-1}}` are the
   larger and the smaller of `|g'|` along the pasts of `𝐣` and of `flip(𝐣)`. Birkhoff's theorem
   for the ergodic measures `μ_1` and `flip_*μ_1` (`eq:lyapunov_exponent_gsystem`) and dominated
   convergence give `λ_1(𝖠, μ) = max{\overline{λ}(𝖠, μ_1), \overline{λ}(𝖠, μ_2)}` and
   `λ_2(𝖠, μ) = min{\overline{λ}(𝖠, μ_1), \overline{λ}(𝖠, μ_2)}`.
2. `\overline{λ}(𝖠, μ_2) ≤ \overline{λ}(𝖠, μ_1)`. The Gibbs bounds of `μ_1` at `𝐣` and at
   `flip(𝐣)` give `μ_2[𝐣|_n] ≥ C⁻² exp(S_n f_{2,s}(𝐣) - S_n f_{1,s}(𝐣)) μ_1[𝐣|_n]`. With
   `t ≤ e^t - 1` this yields
   `∑_{|w| = n} μ_1[w] (S_n (f_{2,s} - f_{1,s})(w) - 2 log C) ≤ ∑ μ_2[w] - ∑ μ_1[w] = 0`, the
   non-negativity of the relative entropy of the partition into cylinders. By invariance the
   left-hand side is `n ∫ (f_{2,s} - f_{1,s}) dμ_1 - 2 log C`, and
   `f_{2,s} - f_{1,s} = c_s (log |g'_{j_0 ± N}| - log |g'_{j_0}|)` with `c_s > 0`, so
   `n c_s (\overline{λ}(𝖠, μ_2) - \overline{λ}(𝖠, μ_1)) ≤ 2 log C` for every `n`.

No literature premise is used. The rotations hypothesis of the main statement is not needed.

* `integral_comp_apply_natCast`: every coordinate of an invariant measure has the distribution
  of the coordinate at time `0`.
* `System.lyapunov_map_unCode_eq_max_min`: step 1.
* `System.lyapBar_map_flipAxis_le_of_isGibbs`: step 2.
* `System.lyapunov_map_unCode_of_isGibbs`: the fields `lyapunov₁_eq` and `lyapunov₂_eq` of
  `System.GibbsDecomposition` for `μ = q_*μ_1` and `μ_2 = flip_*μ_1`.
-/
public import BoxLike.GibbsProperties
public import BoxLike.PressureZ
public import BoxLike.SigmaMeasure

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

/-- For an invariant measure on `ℤ → α` every coordinate has the distribution of the coordinate
at time `0`: `∫ v(x_k) dν(x) = ∫ v(x_0) dν(x)` for `k ∈ ℕ`, as used for `thm:eq_state_is_sum`. -/
theorem integral_comp_apply_natCast {α : Type*} [MeasurableSpace α] [Finite α]
    [MeasurableSingletonClass α] {ν : Measure (ℤ → α)} (hinv : MeasurePreserving (shift 1) ν ν)
    (v : α → ℝ) (k : ℕ) : ∫ x, v (x k) ∂ν = ∫ x, v (x 0) ∂ν := by
  have h := integral_comp_shift hinv k (F := fun x : ℤ → α => v (x 0))
    ((Measurable.of_discrete (f := v)).comp (measurable_pi_apply 0))
  simpa using h

namespace System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι)

/-! ### Step 1: the exponents are the larger and the smaller backward rate -/

/-- For an ergodic invariant probability measure `μ_1` carried by `Σ_Z` and `μ = q_*μ_1`,
`λ_1(𝖠, μ) = max{\overline{λ}(𝖠, μ_1), \overline{λ}(𝖠, flip_*μ_1)}` and
`λ_2(𝖠, μ) = min{\overline{λ}(𝖠, μ_1), \overline{λ}(𝖠, flip_*μ_1)}`, the first step of the
Lyapunov identities of `thm:eq_state_is_sum`. For `μ_1`-almost every `𝐣` the backward rates of
`|g'|` along `𝐣` and along `flip(𝐣)` are `\overline{λ}(𝖠, μ_1)` and `\overline{λ}(𝖠, flip_*μ_1)`
(`eq:lyapunov_exponent_gsystem`); these are the two lifts `τ(𝐢)`, `ω(𝐢)` of `𝐢 = q(𝐣)`, so by
`thm:matrix_products_g_derivatives` the singular values of `A_{i_{-n}} ⋯ A_{i_{-1}}` grow at the
larger and the smaller rate, and dominated convergence turns the backward limits into the
forward limits defining `λ_1` and `λ_2`. -/
theorem lyapunov_map_unCode_eq_max_min (μ₁ : Measure (ℤ → ι × ZMod 2))
    [IsProbabilityMeasure μ₁] (herg : Ergodic (shift 1) μ₁) (hsupp : μ₁ (subshift S.o)ᶜ = 0) :
    S.lyapunov₁ (μ₁.map unCode) = max (S.lyapBar μ₁) (S.lyapBar (μ₁.map flipAxis)) ∧
      S.lyapunov₂ (μ₁.map unCode) = min (S.lyapBar μ₁) (S.lyapBar (μ₁.map flipAxis)) := by
  have : Nonempty ι := ⟨((nonempty_of_isProbabilityMeasure μ₁).some 0).1⟩
  have hinv := measurePreserving_shift_map_unCode herg.toMeasurePreserving
  have h₁ := S.lyapunov_exponent_gsystem μ₁ herg
  -- `flip_*μ_1` is ergodic: the exchange of the axes commutes with the shift
  have herg₂ : Ergodic (shift 1) (μ₁.map flipAxis) :=
    (MeasurePreserving.mk measurable_flipAxis rfl).ergodic_of_ergodic_semiconj herg
      (measurable_shift 1) fun _ => rfl
  have h₂ := ae_of_ae_map measurable_flipAxis.aemeasurable (S.lyapunov_exponent_gsystem _ herg₂)
  generalize S.lyapBar μ₁ = a at h₁ ⊢
  generalize S.lyapBar (μ₁.map flipAxis) = b at h₂ ⊢
  have hsub : ∀ᵐ y ∂μ₁, y ∈ subshift S.o := mem_ae_iff.2 hsupp
  have hmeas : ∀ (G : List ι → ℝ) (n : ℕ),
      Measurable fun x : ℤ → ι => G (pastWord x n) / n := fun G n => by
    simp only [pastWord_eq_futureWord]
    exact ((measurable_comp_futureWord G n).comp (measurable_shift _)).div_const _
  have hset : MeasurableSet {x : ℤ → ι |
      Tendsto (fun n : ℕ => Real.log ‖S.matWord (pastWord x n)‖ / n) atTop (𝓝 (max a b)) ∧
      Tendsto (fun n : ℕ => Real.log (|(S.matWord (pastWord x n)).det| /
        ‖S.matWord (pastWord x n)‖) / n) atTop (𝓝 (min a b))} :=
    (measurableSet_tendsto _ (hmeas fun w => Real.log ‖S.matWord w‖)).inter
      (measurableSet_tendsto _ (hmeas fun w => Real.log (|(S.matWord w).det| / ‖S.matWord w‖)))
  have hae : ∀ᵐ x ∂(μ₁.map unCode),
      Tendsto (fun n : ℕ => Real.log ‖S.matWord (pastWord x n)‖ / n) atTop (𝓝 (max a b)) ∧
      Tendsto (fun n : ℕ => Real.log (|(S.matWord (pastWord x n)).det| /
        ‖S.matWord (pastWord x n)‖) / n) atTop (𝓝 (min a b)) := by
    rw [ae_map_iff measurable_unCode.aemeasurable hset]
    filter_upwards [h₁, h₂, hsub] with y ha hb hy
    rw [← range_tau_union_range_omega] at hy
    rcases hy with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · rw [flipAxis_tau] at hb
      rw [unCode_tau]
      exact ⟨S.tendsto_log_norm_matWord_pastWord ha hb,
        S.tendsto_log_abs_det_div_norm_matWord_pastWord ha hb⟩
    · rw [flipAxis_omega] at hb
      rw [unCode_omega, max_comm, min_comm]
      exact ⟨S.tendsto_log_norm_matWord_pastWord hb ha,
        S.tendsto_log_abs_det_div_norm_matWord_pastWord hb ha⟩
  obtain ⟨C, hC₁, hC₂⟩ := S.exists_abs_log_singularValue_le
  exact ⟨tendsto_nhds_unique (S.tendsto_lyapunov₁ hinv)
      (tendsto_integral_futureWord_div_of_ae_pastWord hinv hC₁ (hae.mono fun _ hx => hx.1)),
    tendsto_nhds_unique (S.tendsto_lyapunov₂ hinv)
      (tendsto_integral_futureWord_div_of_ae_pastWord hinv hC₂ (hae.mono fun _ hx => hx.2))⟩

/-! ### Step 2: the first Gibbs measure has the larger exponent -/

/-- `\overline{λ}(𝖠, flip_*μ_1) ≤ \overline{λ}(𝖠, μ_1)` for an invariant probability measure
`μ_1` carried by `Σ_Z` with the Gibbs property for `f_{1,s}`, `0 < s < 2`: the second step of the
Lyapunov identities of `thm:eq_state_is_sum`. The Gibbs bounds of `μ_1` at `𝐣` and at `flip(𝐣)`
compare `μ_2 = flip_*μ_1` with `μ_1` on the cylinders,
`μ_2[𝐣|_n] ≥ C⁻² exp(S_n (f_{2,s} - f_{1,s})(𝐣)) μ_1[𝐣|_n]`, and the non-negativity of the relative
entropy of `μ_1` and `μ_2` on the cylinders of length `n` gives
`n ∫ (f_{2,s} - f_{1,s}) dμ_1 ≤ 2 log C`. By the calculation of tex lines 2551 to 2555,
`f_{2,s} - f_{1,s} = c_s (log |g'_{j_0 ± N}| - log |g'_{j_0}|)` with `c_s > 0`. -/
theorem lyapBar_map_flipAxis_le_of_isGibbs {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2)
    (μ₁ : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure μ₁]
    (hinv : MeasurePreserving (shift 1) μ₁ μ₁) (hsupp : μ₁ (subshift S.o)ᶜ = 0)
    (hg : IsGibbs S.o (S.potential₁ s) μ₁) :
    S.lyapBar (μ₁.map flipAxis) ≤ S.lyapBar μ₁ := by
  obtain ⟨P, C, hC, hb⟩ := hg
  set u : ι × ZMod 2 → ℝ := fun p => Real.log |S.ratio (flipSymbol p)| - Real.log |S.ratio p|
    with hu
  have hpot : ∀ p, S.potential₂ s p - S.potential₁ s p = gapExp s * u p := fun p => by
    have := S.potential₁_sub_potential₂ s p
    simp only [hu, flipSymbol]
    linarith
  -- the relative entropy inequality on each cylinder
  have key : ∀ n : ℕ, 0 < n → ∀ w : Fin n → ι × ZMod 2,
      μ₁.real (cylinder w) * (∑ k, gapExp s * u (w k) - 2 * Real.log C) ≤
        (μ₁.map flipAxis).real (cylinder w) - μ₁.real (cylinder w) := by
    intro n hn w
    -- `flip^{-1}[w] = [flip(w)]`
    have hpre : flipAxis ⁻¹' cylinder w = cylinder fun k => flipSymbol (w k) := by
      ext y
      refine forall_congr' fun k => ?_
      change flipSymbol (y k) = w k ↔ y k = flipSymbol (w k)
      exact ⟨fun h => by rw [← h, flipSymbol_flipSymbol], fun h => by
        rw [h, flipSymbol_flipSymbol]⟩
    rw [map_measureReal_apply measurable_flipAxis (measurableSet_cylinder w), hpre]
    by_cases hw : ∃ y ∈ subshift S.o, (fun k : Fin n => y k) = w
    · obtain ⟨y, hy, rfl⟩ := hw
      -- `flip(𝐣) ∈ Σ_Z`: the matrix `Z` of `sec:subshift` is invariant under the exchange
      have hfy : flipAxis y ∈ subshift S.o := fun m =>
        (trans_flipSymbol_iff (y m) (y (m + 1))).2 (hy m)
      have h1 := (hb y hy n hn).2
      have h2 := (hb (flipAxis y) hfy n hn).1
      change C⁻¹ * Real.exp (-(n * P) + ∑ k ∈ Finset.range n, S.potential₂ s (y k)) ≤
        μ₁.real (cylinder fun k : Fin n => flipSymbol (y k)) at h2
      have hsum : ∑ k : Fin n, gapExp s * u (y k) =
          ∑ k ∈ Finset.range n, S.potential₂ s (y k) -
            ∑ k ∈ Finset.range n, S.potential₁ s (y k) := by
        rw [← Finset.sum_sub_distrib]
        simp only [← hpot]
        exact Fin.sum_univ_eq_sum_range
          (fun k : ℕ => S.potential₂ s (y k) - S.potential₁ s (y k)) n
      rw [hsum]
      set A := -(n * P) + ∑ k ∈ Finset.range n, S.potential₁ s (y k)
      set B := -(n * P) + ∑ k ∈ Finset.range n, S.potential₂ s (y k)
      set t := ∑ k ∈ Finset.range n, S.potential₂ s (y k) -
        ∑ k ∈ Finset.range n, S.potential₁ s (y k) - 2 * Real.log C
      have hexp : C * Real.exp A * Real.exp t = C⁻¹ * Real.exp B := by
        have e : A + t = B - Real.log C - Real.log C := by
          simp only [A, B, t]
          ring
        rw [mul_assoc, ← Real.exp_add, e, Real.exp_sub, Real.exp_sub, Real.exp_log hC]
        field_simp
      have ht := Real.add_one_le_exp t
      have hp : 0 ≤ μ₁.real (cylinder fun k : Fin n => y k) := measureReal_nonneg
      calc μ₁.real (cylinder fun k : Fin n => y k) * t
          ≤ μ₁.real (cylinder fun k : Fin n => y k) * (Real.exp t - 1) :=
            mul_le_mul_of_nonneg_left (by linarith) hp
        _ = μ₁.real (cylinder fun k : Fin n => y k) * Real.exp t -
            μ₁.real (cylinder fun k : Fin n => y k) := by ring
        _ ≤ C * Real.exp A * Real.exp t - μ₁.real (cylinder fun k : Fin n => y k) := by
            gcongr
        _ = C⁻¹ * Real.exp B - μ₁.real (cylinder fun k : Fin n => y k) := by rw [hexp]
        _ ≤ μ₁.real (cylinder fun k : Fin n => flipSymbol (y k)) -
            μ₁.real (cylinder fun k : Fin n => y k) := by linarith
    · have hsub : cylinder w ⊆ (subshift S.o)ᶜ := fun z hz hzs =>
        hw ⟨z, hzs, funext fun k => hz k⟩
      have h0 : μ₁.real (cylinder w) = 0 := by
        rw [measureReal_def, measure_mono_null hsub hsupp, ENNReal.toReal_zero]
      rw [h0, zero_mul, sub_zero]
      exact measureReal_nonneg
  -- integrating the inequality
  have hint : ∀ k : ℕ, Integrable (fun y : ℤ → ι × ZMod 2 => gapExp s * u (y k)) μ₁ := fun k =>
    (Integrable.of_finite (f := fun p : ι × ZMod 2 => gapExp s * u p)).comp_measurable
      (measurable_pi_apply (k : ℤ))
  have hbound : ∀ n : ℕ, 0 < n →
      n * ∫ y, gapExp s * u (y 0) ∂μ₁ - 2 * Real.log C ≤ 0 := by
    intro n hn
    have hS := Finset.sum_le_sum fun w (_ : w ∈ Finset.univ) => key n hn w
    rw [Finset.sum_sub_distrib, sum_measureReal_cylinder, sum_measureReal_cylinder, sub_self,
      ← integral_comp_block_eq_sum μ₁
        (fun w : Fin n → ι × ZMod 2 => ∑ k, gapExp s * u (w k) - 2 * Real.log C)] at hS
    simp only [block_apply] at hS
    have hk : ∀ k : Fin n, ∫ x, gapExp s * u (x k) ∂μ₁ = ∫ y, gapExp s * u (y 0) ∂μ₁ :=
      fun k => integral_comp_apply_natCast hinv (fun p => gapExp s * u p) k
    rw [integral_sub (integrable_finsetSum _ fun (k : Fin n) _ => hint k) (integrable_const _),
      integral_finsetSum _ fun (k : Fin n) _ => hint k, Finset.sum_congr rfl fun k _ => hk k]
      at hS
    simpa using hS
  have hI : ∫ y, gapExp s * u (y 0) ∂μ₁ =
      gapExp s * (S.lyapBar (μ₁.map flipAxis) - S.lyapBar μ₁) := by
    have hm : Measurable fun y : ℤ → ι × ZMod 2 => Real.log |S.ratio (y 0)| :=
      (Measurable.of_discrete (f := fun p : ι × ZMod 2 => Real.log |S.ratio p|)).comp
        (measurable_pi_apply 0)
    have hi : ∀ f : ι × ZMod 2 → ℝ, Integrable (fun y : ℤ → ι × ZMod 2 => f (y 0)) μ₁ := fun f =>
      (Integrable.of_finite (f := f)).comp_measurable (measurable_pi_apply 0)
    rw [integral_const_mul, lyapBar, lyapBar,
      integral_map measurable_flipAxis.aemeasurable hm.aestronglyMeasurable, hu,
      integral_sub (hi fun p => Real.log |S.ratio (flipSymbol p)|)
        (hi fun p => Real.log |S.ratio p|)]
    rfl
  have hc := gapExp_pos hs0 hs2
  by_contra hlt
  have hpos : 0 < ∫ y, gapExp s * u (y 0) ∂μ₁ := by
    rw [hI]
    exact mul_pos hc (by linarith)
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * Real.log C / ∫ y, gapExp s * u (y 0) ∂μ₁)
  have h := hbound (n + 1) n.succ_pos
  rw [div_lt_iff₀ hpos] at hn
  push_cast at h
  nlinarith

end System

/-! ### The Lyapunov identities -/

section Main

variable {ι : Type*}

/-- `thm:eq_state_is_sum`, second and third lines, for the measures of its proof: if `μ_1` is an
ergodic invariant probability measure carried by `Σ_Z` with the Gibbs property for `f_{1,s}`,
`0 < s < 2`, then `μ = q_*μ_1` and `μ_2 = flip_*μ_1` satisfy
`λ_1(𝖠, μ) = \overline{λ}(𝖠, μ_1)` and `λ_2(𝖠, μ) = \overline{λ}(𝖠, μ_2)`, the fields
`lyapunov₁_eq` and `lyapunov₂_eq` of `System.GibbsDecomposition`. The exponents are the larger
and the smaller of `\overline{λ}(𝖠, μ_1)`, `\overline{λ}(𝖠, μ_2)`
(`System.lyapunov_map_unCode_eq_max_min`), and the first is the larger
(`System.lyapBar_map_flipAxis_le_of_isGibbs`). The rotations hypothesis is not used. -/
theorem System.lyapunov_map_unCode_of_isGibbs (S : System ι) [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (_hrot : S.WithRotations) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2)
    (μ₁ : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure μ₁] (herg : Ergodic (shift 1) μ₁)
    (hsupp : μ₁ (subshift S.o)ᶜ = 0) (hg : IsGibbs S.o (S.potential₁ s) μ₁) :
    S.lyapunov₁ (μ₁.map unCode) = S.lyapBar μ₁ ∧
      S.lyapunov₂ (μ₁.map unCode) = S.lyapBar (μ₁.map flipAxis) := by
  obtain ⟨h₁, h₂⟩ := S.lyapunov_map_unCode_eq_max_min μ₁ herg hsupp
  have hle := S.lyapBar_map_flipAxis_le_of_isGibbs hs0 hs2 μ₁ herg.toMeasurePreserving hsupp hg
  exact ⟨h₁.trans (max_eq_left hle), h₂.trans (min_eq_right hle)⟩

end Main

end BoxLike
