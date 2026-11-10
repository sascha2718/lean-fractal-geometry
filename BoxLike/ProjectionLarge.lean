module

/-
`thm:eq_state_proj_dim` for every `s > 0`, in `sec:dimension_of_projections`: the pointwise
dimension of each coordinate projection exists almost everywhere and takes at most the two values
`min{1, -h_0(μ)/λ_1(𝖠, μ)}` and `min{1, -h_0(μ)/λ_2(𝖠, μ)}`, the upper packing and the lower
Hausdorff dimension, each on a set of positive measure. The case `0 < s < 2` is
`System.eq_state_proj_dim`. For `s ≥ 2` the proof follows the first paragraph of
the proof of `thm:eq_state_proj_dim`: by `thm:bernoulli_equilibrium` the equilibrium state `μ`
is Bernoulli with the weights `p_i = |det A_i|^{s/2} / ∑_j |det A_j|^{s/2}`; its orientation lift
`\widetilde μ = (τ_*μ + ω_*μ) / 2` is a mixing Markov measure, hence ergodic, with
`\overline{h}_0(\widetilde μ) = h_0(μ)`; Birkhoff's theorem along both lifts and
`thm:matrix_products_g_derivatives` give `λ_1(𝖠, μ) = λ_2(𝖠, μ) = \overline{λ}(𝖠, \widetilde μ)`;
Jordan–Rapaport gives `\overline{π}_* \widetilde μ = (ν_x + ν_y) / 2` the exact dimension
`min{1, -h_0(μ)/λ_1(𝖠, μ)}`, and both coordinate projections are absolutely continuous with
respect to this average.

* `hasLocalDim_smul_iff`, `isExactDim_smul_iff`: a positive multiple of a measure has the same
  pointwise dimensions.
* `System.IsEquilibriumState.ergodic_orientationLift_of_two_le`: the orientation lift of the
  `s`-equilibrium state, `s ≥ 2`, is ergodic.
* `System.IsEquilibriumState.lyapunov_eq_of_two_le`:
  `λ_1(𝖠, μ) = λ_2(𝖠, μ) = (1/2) ∑_i p_i log |det A_i|` for `s ≥ 2`.
* `System.isExactDim_marginal_of_two_le`: both coordinate projections of the `s`-equilibrium
  state, `s ≥ 2`, are exact-dimensional of dimension `min{1, -h_0(μ)/λ_1(𝖠, μ)}`.
* `System.eq_state_proj_dim_of_two_le`: the conclusions of `thm:eq_state_proj_dim` for `s ≥ 2`.
* `System.eq_state_proj_dim_all`: `thm:eq_state_proj_dim` for every `s > 0`.
-/
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.General
public import BoxLike.OrientationLift

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

universe u

section Scaling

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {μ : Measure X} {d : ℝ}
  {c : ℝ≥0}

/-- A positive multiple `c • μ` of a measure has the pointwise dimensions of `μ`: the
logarithms of the ball measures differ by `log c` or by `0`, and `log r → -∞`. It passes from
the average `(ν_x + ν_y) / 2` to `ν_x + ν_y` in the proof of `thm:eq_state_proj_dim`. -/
theorem hasLocalDim_smul_iff (hc : c ≠ 0) (x : X) :
    HasLocalDim (c • μ) x d ↔ HasLocalDim μ x d := by
  unfold HasLocalDim
  have hdiff : Tendsto (fun r : ℝ => Real.log ((c • μ).real (closedBall x r)) / Real.log r -
      Real.log (μ.real (closedBall x r)) / Real.log r) (𝓝[>] 0) (𝓝 0) := by
    have hbound : ∀ r : ℝ, ‖Real.log ((c • μ).real (closedBall x r)) / Real.log r -
        Real.log (μ.real (closedBall x r)) / Real.log r‖ ≤
        ‖|Real.log (c : ℝ)| / Real.log r‖ := by
      intro r
      rw [measureReal_nnreal_smul_apply, ← sub_div, norm_div, norm_div, Real.norm_eq_abs,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
      refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
      by_cases hm : μ.real (closedBall x r) = 0
      · simp [hm]
      · rw [Real.log_mul (NNReal.coe_ne_zero.2 hc) hm]
        simp
    refine squeeze_zero_norm hbound ?_
    have h := (tendsto_const_nhds (x := |Real.log (c : ℝ)|)).div_atBot
      Real.tendsto_log_nhdsGT_zero
    simpa using h.norm
  constructor
  · intro h
    simpa using h.sub hdiff
  · intro h
    simpa using h.add hdiff

/-- A positive multiple `c • μ` of a measure is exact-dimensional exactly when `μ` is, with the
same dimension, as used in the proof of `thm:eq_state_proj_dim` for `s ≥ 2`. -/
theorem isExactDim_smul_iff (hc : c ≠ 0) : IsExactDim (c • μ) d ↔ IsExactDim μ d := by
  unfold IsExactDim
  rw [Measure.ae_smul_measure_eq hc]
  simp only [hasLocalDim_smul_iff hc]

end Scaling

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {s : ℝ}

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- The coordinate marginals `(proj_x)_*(π_*μ)` and `(proj_y)_*(π_*μ)` of
`sec:dimension_of_projections` of a probability measure are probability measures. -/
instance isProbabilityMeasure_marginal (c : ZMod 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (S.marginal c μ) := by
  unfold marginal
  infer_instance

variable {S} in
/-- The orientation lift `(τ_*μ + ω_*μ) / 2` of the `s`-equilibrium state, `s ≥ 2`, of a tuple
with rotations is ergodic: by `thm:bernoulli_equilibrium` the state is Bernoulli with the
positive weights `p_i = |det A_i|^{s/2} / ∑_j |det A_j|^{s/2}`, so both matrix types have
positive probability and the lift is mixing (`ergodic_orientationLift_bernoulli`). -/
theorem IsEquilibriumState.ergodic_orientationLift_of_two_le {μ : Measure (ℤ → ι)}
    [IsProbabilityMeasure μ] (heq : S.IsEquilibriumState s μ) (hrot : S.WithRotations)
    (hinv : MeasurePreserving (shift 1) μ μ) (hs : 2 ≤ s) :
    Ergodic (shift 1) (orientationLift S.o μ) := by
  have : Nonempty ι := nonempty_of_measure μ
  obtain ⟨⟨i₀, hi₀⟩, ⟨i₁, hi₁⟩⟩ := hrot
  rw [heq.eq_bernoulli hinv hs]
  exact ergodic_orientationLift_bernoulli S.o _ hi₀
    (by rw [measureReal_detWeightMeasure_singleton]; exact S.detWeight_pos s i₀) hi₁
    (by rw [measureReal_detWeightMeasure_singleton]; exact S.detWeight_pos s i₁)

variable {S} in
/-- The Lyapunov exponents of the `s`-equilibrium state, `s ≥ 2`, of a tuple with rotations,
as in the proof of `thm:eq_state_proj_dim`:
`λ_1(𝖠, μ) = λ_2(𝖠, μ) = \overline{λ}(𝖠, \widetilde μ) = (1/2) ∑_i p_i log |det A_i|`, with the
weights `p_i = |det A_i|^{s/2} / ∑_j |det A_j|^{s/2}` of `thm:bernoulli_equilibrium`. -/
theorem IsEquilibriumState.lyapunov_eq_of_two_le {μ : Measure (ℤ → ι)}
    [IsProbabilityMeasure μ] (heq : S.IsEquilibriumState s μ) (hrot : S.WithRotations)
    (hinv : MeasurePreserving (shift 1) μ μ) (hs : 2 ≤ s) :
    S.lyapunov₁ μ = S.lyapBar (orientationLift S.o μ) ∧
      S.lyapunov₂ μ = S.lyapBar (orientationLift S.o μ) ∧
      S.lyapBar (orientationLift S.o μ) =
        (1 / 2) * ∑ i, S.detWeight s i * Real.log |(S.mat i).det| := by
  have : Nonempty ι := nonempty_of_measure μ
  obtain ⟨h1, h2⟩ := S.lyapunov_eq_of_ergodic_orientationLift hinv
    (heq.ergodic_orientationLift_of_two_le hrot hinv hs)
  refine ⟨h1, h2, ?_⟩
  rw [S.lyapBar_orientationLift hinv, S.lyapunov₁_add_lyapunov₂ hinv]
  have hw : ∀ i, μ.real (cylinder ![i]) = S.detWeight s i := fun i => by
    rw [heq.eq_bernoulli hinv hs, measureReal_bernoulli_cylinder, Fin.prod_univ_one,
      Matrix.cons_val_zero, measureReal_detWeightMeasure_singleton]
  simp only [hw]
  ring

/-- For `s ≥ 2` both coordinate projections of the `s`-equilibrium state of a box-like tuple
with rotations satisfying the projective exponential separation condition are exact-dimensional
of dimension `min{1, -h_0(μ)/λ_1(𝖠, μ)}`, and `λ_1(𝖠, μ) = λ_2(𝖠, μ)`. This is the case `s ≥ 2`
of the proof of `thm:eq_state_proj_dim`: Jordan–Rapaport for the ergodic lift
`\widetilde μ`, `\overline{h}_0(\widetilde μ) = h_0(μ)`, `\overline{π}_* \widetilde μ =
(ν_x + ν_y) / 2`, and the differentiation argument of `thm:exact-dimensional-mixture` for
`ν_x, ν_y ≤ ν_x + ν_y`. -/
theorem isExactDim_marginal_of_two_le (hjr : JordanRapaportDimension.{u})
    (hrot : S.WithRotations) (hsep : S.ProjExpSeparation) (hs : 2 ≤ s) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) (c : ZMod 2) :
    S.lyapunov₁ μ = S.lyapunov₂ μ ∧
      IsExactDim (S.marginal c μ) (min 1 (-entropy μ / S.lyapunov₁ μ)) := by
  have herg := heq.ergodic_orientationLift_of_two_le hrot hinv hs
  obtain ⟨h1, h2⟩ := S.lyapunov_eq_of_ergodic_orientationLift hinv herg
  refine ⟨h1.trans h2.symm, ?_⟩
  have hdim := hjr S hsep (orientationLift S.o μ) herg
  rw [S.map_projBar_orientationLift, entropy_orientationLift S.o μ hinv, ← h1] at hdim
  have hle : (2⁻¹ : ℝ≥0) • S.marginal c μ ≤ avgMeasure (S.marginal 0 μ) (S.marginal 1 μ) := by
    unfold avgMeasure
    refine smul_le_smul_left _ ?_
    rcases zmod_two_cases c with rfl | rfl
    · exact Measure.le_add_right le_rfl
    · exact Measure.le_add_left le_rfl
  exact (isExactDim_smul_iff (by norm_num)).1 (hdim.of_le hle)

/-- `thm:eq_state_proj_dim` for `s ≥ 2`: the pointwise dimension of each coordinate projection
of the `s`-equilibrium state is `min{1, -h_0(μ)/λ_1(𝖠, μ)}` or `min{1, -h_0(μ)/λ_2(𝖠, μ)}`
almost everywhere, and the two values coincide; the upper packing dimension is
`min{1, -h_0(μ)/λ_1(𝖠, μ)}`, the lower Hausdorff dimension is `min{1, -h_0(μ)/λ_2(𝖠, μ)}`, and
each value occurs on a set of positive measure, namely a set of full measure. -/
theorem eq_state_proj_dim_of_two_le (hjr : JordanRapaportDimension.{u})
    (hrot : S.WithRotations) (hsep : S.ProjExpSeparation) (hs : 2 ≤ s) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) (c : ZMod 2) :
    HasLocalDimPair (S.marginal c μ) (min 1 (-entropy μ / S.lyapunov₁ μ))
        (min 1 (-entropy μ / S.lyapunov₂ μ)) ∧
      upperPackingDim (S.marginal c μ) = min 1 (-entropy μ / S.lyapunov₁ μ) ∧
      lowerHausdorffDim (S.marginal c μ) = min 1 (-entropy μ / S.lyapunov₂ μ) ∧
      0 < S.marginal c μ
        {x | HasLocalDim (S.marginal c μ) x (min 1 (-entropy μ / S.lyapunov₁ μ))} ∧
      0 < S.marginal c μ
        {x | HasLocalDim (S.marginal c μ) x (min 1 (-entropy μ / S.lyapunov₂ μ))} := by
  obtain ⟨hl, hd⟩ := S.isExactDim_marginal_of_two_le hjr hrot hsep hs μ hinv heq c
  rw [← hl]
  have hpos := hd.measure_hasLocalDim_pos (IsProbabilityMeasure.ne_zero _)
  exact ⟨hd.hasLocalDimPair, hd.upperPackingDim_eq (IsProbabilityMeasure.ne_zero _),
    hd.lowerHausdorffDim_eq (IsProbabilityMeasure.ne_zero _), hpos, hpos⟩

/-- `thm:eq_state_proj_dim`: if `X` is a proximal box-like self-affine set with rotations
satisfying the projective exponential separation condition and `μ` is the `s`-equilibrium
state with `s > 0`, then the pointwise dimension of each of `(proj_x)_*(π_*μ)` (`c = 0`) and
`(proj_y)_*(π_*μ)` (`c = 1`) exists almost everywhere and takes at most two values, the upper
packing dimension `min{1, -h_0(μ)/λ_1(𝖠, μ)}` and the lower Hausdorff dimension
`min{1, -h_0(μ)/λ_2(𝖠, μ)}`, each on a set of positive measure. The conclusion holds for every
invariant `s`-equilibrium state. For `s ≥ 2` the proof uses the orientation lift
(`eq_state_proj_dim_of_two_le`), for `0 < s < 2` the Gibbs decomposition
(`eq_state_proj_dim`). -/
theorem eq_state_proj_dim_all (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hjr : JordanRapaportDimension.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal) (hsep : S.ProjExpSeparation) (hs0 : 0 < s)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState s μ) (c : ZMod 2) :
    HasLocalDimPair (S.marginal c μ) (min 1 (-entropy μ / S.lyapunov₁ μ))
        (min 1 (-entropy μ / S.lyapunov₂ μ)) ∧
      upperPackingDim (S.marginal c μ) = min 1 (-entropy μ / S.lyapunov₁ μ) ∧
      lowerHausdorffDim (S.marginal c μ) = min 1 (-entropy μ / S.lyapunov₂ μ) ∧
      0 < S.marginal c μ
        {x | HasLocalDim (S.marginal c μ) x (min 1 (-entropy μ / S.lyapunov₁ μ))} ∧
      0 < S.marginal c μ
        {x | HasLocalDim (S.marginal c μ) x (min 1 (-entropy μ / S.lyapunov₂ μ))} := by
  rcases lt_or_ge s 2 with hs2 | hs2
  · exact S.eq_state_proj_dim hms hfk hfjj hjr hrot hprox hsep hs0 hs2 μ hinv heq c
  · exact S.eq_state_proj_dim_of_two_le hjr hrot hsep hs2 μ hinv heq c

end System

end BoxLike
