module

/-
The pointwise one-dimensional entropy of the average Gibbs measure: `sec:average_gibbs_entropy`.

For an ergodic measure `ν` on `Σ_Z`, Jordan–Rapaport gives
`dim \overline{π}_*ν = min{1, -\overline{h}_0(ν)/\overline{λ}(𝖠, ν)}` and the scalar part of
`thm:feng1` gives
`dim \overline{π}_*ν = (\overline{h}_1(ν) - \overline{h}_0(ν))/\overline{λ}(𝖠, ν)`.
The dimension of a non-zero exact-dimensional measure is unique, so `\overline{h}_1(ν) = 0` when
`\overline{h}_0(ν) ≤ -\overline{λ}(𝖠, ν)`. On the part of `Σ_Z` that carries the Gibbs measure
`μ_k`, `thm:conditional_two_ways` identifies the conditional measures of the average
`\overline{μ}` with those of `μ_k`. There the entropy limits of `thm:feng_entropy_as_limit`
agree, so `\overline{h}_1(\overline{μ}, 𝐢) = \overline{h}_1(μ_k)`, and the Dirac conditional
measures of `μ_k`, which `thm:feng_entropy_zero` gives when `\overline{h}_1(μ_k) = 0`, are Dirac
conditional measures of `\overline{μ}`.

* `ae_avgMeasure_iff`, `absolutelyContinuous_avgMeasure_left`,
  `absolutelyContinuous_avgMeasure_right`, `avgMeasure_eq_zero`,
  `measurePreserving_shift_avgMeasure`: almost everywhere statements, null sets and invariance
  of the average `\overline{μ}` of `eq:average_gibbs`.
* `System.dimEntropyBar_one_eq_zero`: `\overline{h}_1(ν) = 0` for ergodic `ν` on `Σ_Z` with
  `\overline{h}_0(ν) ≤ -\overline{λ}(𝖠, ν)`, which is `eq:h1_gibbs_entropy_zero`.
* `System.condMeas_xiBar_eq_dirac`: `\overline{h}_1(ν) = 0` gives
  `ν_𝐢^{\overline{ξ}_1} = δ_𝐢` almost everywhere.
* `System.dimEntropyBarAt_eq_of_condMeas_eq`: where the conditional measures of an invariant
  measure `m` agree with those of an ergodic measure `ν ≪ m`, the pointwise entropy of `m` is
  `\overline{h}_1(ν)`.
* `System.ae_mem_fastPart`, `System.ae_mem_slowPart`, `System.measure_slowPart_eq_zero`,
  `System.measure_fastPart_eq_zero`: `μ_1` is carried by `τ(Σ^τ) ∪ ω(Σ^ω)` and `μ_2` by
  `ω(Σ^τ) ∪ τ(Σ^ω)`, from `thm:gibbs_tau_omega_positive`.
* `System.dimEntropyBarAt_avgMeasure_fast`, `System.dimEntropyBarAt_avgMeasure_slow`:
  `\overline{h}_1(\overline{μ}, 𝐢)` is `\overline{h}_1(μ_1)` on `τ(Σ^τ) ∪ ω(Σ^ω)` and
  `\overline{h}_1(μ_2)` on `ω(Σ^τ) ∪ τ(Σ^ω)`.
* `System.condMeas_avgMeasure_eq_dirac_slow`: Dirac conditional measures of `μ_2` give Dirac
  conditional measures of `\overline{μ}` on `ω(Σ^τ) ∪ τ(Σ^ω)`.
* `System.overline_h1_zero`: `thm:overline_h1_zero`.
* `System.overline_h1_zero_large`: `thm:overline_h1_zero_large`.
-/
public import BoxLike.Aligned.ConditionalTwoWays
public import BoxLike.ConditionalTwoWays
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.FengEntropy
public import BoxLike.General
public import BoxLike.PastEntropy

@[expose] public section

namespace BoxLike

open MeasureTheory Set

universe u

/-! ### The average measure -/

section Average

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A property holds almost everywhere for the average `(μ_1 + μ_2) / 2` of `eq:average_gibbs`
if and only if it holds almost everywhere for `μ_1` and for `μ_2`. -/
theorem ae_avgMeasure_iff {m₁ m₂ : Measure Ω} {p : Ω → Prop} :
    (∀ᵐ y ∂avgMeasure m₁ m₂, p y) ↔ (∀ᵐ y ∂m₁, p y) ∧ ∀ᵐ y ∂m₂, p y := by
  rw [ae_iff, ae_iff, ae_iff]
  simp [avgMeasure, ENNReal.smul_def]

/-- `μ_1` is absolutely continuous with respect to the average `\overline{μ}` of
`eq:average_gibbs`. -/
theorem absolutelyContinuous_avgMeasure_left {m₁ m₂ : Measure Ω} : m₁ ≪ avgMeasure m₁ m₂ := by
  intro A h
  exact measure_eq_zero_iff_ae_notMem.2
    (ae_avgMeasure_iff.1 (measure_eq_zero_iff_ae_notMem.1 h)).1

/-- `μ_2` is absolutely continuous with respect to the average `\overline{μ}` of
`eq:average_gibbs`. -/
theorem absolutelyContinuous_avgMeasure_right {m₁ m₂ : Measure Ω} : m₂ ≪ avgMeasure m₁ m₂ := by
  intro A h
  exact measure_eq_zero_iff_ae_notMem.2
    (ae_avgMeasure_iff.1 (measure_eq_zero_iff_ae_notMem.1 h)).2

/-- A set that is null for `μ_1` and for `μ_2` is null for their average `\overline{μ}` of
`eq:average_gibbs`. -/
theorem avgMeasure_eq_zero {m₁ m₂ : Measure Ω} {A : Set Ω} (h₁ : m₁ A = 0) (h₂ : m₂ A = 0) :
    avgMeasure m₁ m₂ A = 0 := by
  simp [avgMeasure, h₁, h₂]

/-- The average `\overline{μ}` of `eq:average_gibbs` of two invariant measures is invariant
(`sec:average_gibbs`: `\overline{μ} ∈ ℳ_σ(Σ_Z)`). -/
theorem measurePreserving_shift_avgMeasure {α : Type*} [MeasurableSpace α]
    {m₁ m₂ : Measure (ℤ → α)} (h₁ : MeasurePreserving (shift 1) m₁ m₁)
    (h₂ : MeasurePreserving (shift 1) m₂ m₂) :
    MeasurePreserving (shift 1) (avgMeasure m₁ m₂) (avgMeasure m₁ m₂) := by
  refine ⟨h₁.measurable, ?_⟩
  rw [avgMeasure, Measure.map_smul _ h₁.measurable.aemeasurable, Measure.map_add _ _ h₁.measurable,
    h₁.map_eq, h₂.map_eq]

end Average

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {s : ℝ}

/-! ### The one-dimensional entropy of an ergodic measure on `Σ_Z` -/

/-- `eq:h1_gibbs_entropy_zero` and the first half of the proof of `thm:overline_h1_zero_large`:
under projective exponential separation, an ergodic measure `ν` on `Σ_Z` with
`\overline{h}_0(ν) ≤ -\overline{λ}(𝖠, ν)` has `\overline{h}_1(ν) = 0`. Jordan–Rapaport gives
`dim \overline{π}_*ν = -\overline{h}_0(ν)/\overline{λ}(𝖠, ν)`, the scalar part of `thm:feng1`
gives `dim \overline{π}_*ν = (\overline{h}_1(ν) - \overline{h}_0(ν))/\overline{λ}(𝖠, ν)`, and the
dimension of the probability measure `\overline{π}_*ν` is unique.
Depends on: `JordanRapaportDimension`, `thm:feng1` (scalar), `dimEntropyBar_zero_eq_entropy`,
`IsExactDim.unique`. -/
theorem dimEntropyBar_one_eq_zero (hjr : JordanRapaportDimension.{u})
    (hlyb : FengLedrappierYoungBar.{u}) (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν]
    (herg : Ergodic (shift 1) ν) (hsupp : ν (subshift S.o)ᶜ = 0)
    (hent : entropy ν ≤ -S.lyapBar ν) : S.dimEntropyBar ν 1 = 0 := by
  have hinv := herg.toMeasurePreserving
  have hl := S.lyapBar_neg ν
  have h := IsExactDim.unique (IsProbabilityMeasure.ne_zero _)
    (hjr S hsep ν herg) (hlyb S hrot hprox ν hinv herg hsupp)
  have hmin : -entropy ν / S.lyapBar ν ≤ 1 := by
    rw [div_le_one_of_neg hl]
    linarith
  rw [S.dimEntropyBar_zero_eq_entropy hrot hprox ν hinv herg hsupp, min_eq_right hmin,
    div_left_inj' hl.ne] at h
  linarith

/-- `thm:feng_entropy_zero`, scalar part, for an ergodic measure: if `\overline{h}_1(ν) = 0`,
then `ν_𝐢^{\overline{ξ}_1} = δ_𝐢` for `ν`-almost every `𝐢`, because the pointwise entropy of an
ergodic measure is almost everywhere `\overline{h}_1(ν)` (`eq:ergodic_entropy_constant`). -/
theorem condMeas_xiBar_eq_dirac (hfib : FengInfoSumBar.{u}) (hrot : S.WithRotations)
    (hprox : S.Proximal) (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν]
    (herg : Ergodic (shift 1) ν) (hsupp : ν (subshift S.o)ᶜ = 0) (h0 : S.dimEntropyBar ν 1 = 0) :
    ∀ᵐ y ∂ν, condMeas ν (S.xiBar 1) y = Measure.dirac y := by
  filter_upwards [S.feng_entropy_zero_bar hfib hrot hprox ν herg.toMeasurePreserving hsupp 1,
    localEntropy_ae_eq ν herg (S.xiBar 1)] with y h1 h2
  exact h1.1 (h2.trans h0)

/-- Proof of `thm:overline_h1_zero`, the comparison of the entropy limits: let `m` be an invariant
probability measure carried by `Σ_Z` and `ν ≪ m` an ergodic one. For `ν`-almost every `𝐢` with
`m_𝐢^{\overline{ξ}_1} = ν_𝐢^{\overline{ξ}_1}`, the limits of `thm:feng_entropy_as_limit` for `m`
and for `ν` agree, so `\overline{h}_1(m, 𝐢) = \overline{h}_1(ν, 𝐢) = \overline{h}_1(ν)`.
Depends on: `thm:feng_entropy_as_limit` (scalar), `eq:ergodic_entropy_constant`. -/
theorem dimEntropyBarAt_eq_of_condMeas_eq (hfib : FengInfoSumBar.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal) (m ν : Measure (ℤ → ι × ZMod 2))
    [IsProbabilityMeasure m] [IsProbabilityMeasure ν]
    (hm : MeasurePreserving (shift 1) m m) (hmsupp : m (subshift S.o)ᶜ = 0)
    (herg : Ergodic (shift 1) ν) (hsupp : ν (subshift S.o)ᶜ = 0) (hac : ν ≪ m) :
    ∀ᵐ y ∂ν, condMeas m (S.xiBar 1) y = condMeas ν (S.xiBar 1) y →
      S.dimEntropyBarAt m 1 y = S.dimEntropyBar ν 1 := by
  filter_upwards [hac.ae_le (S.feng_entropy_as_limit_bar hfib hrot hprox m hm hmsupp 1),
    S.feng_entropy_as_limit_bar hfib hrot hprox ν herg.toMeasurePreserving hsupp 1,
    localEntropy_ae_eq ν herg (S.xiBar 1)] with y h1 h2 h3 he
  rw [he] at h1
  exact (tendsto_nhds_unique h1 h2).trans h3

/-! ### The parts of `Σ_Z` that carry the Gibbs measures -/

variable {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)}

/-- `thm:gibbs_tau_omega_positive`: `μ_1(ω(Σ^τ) ∪ τ(Σ^ω)) = 0`. -/
theorem measure_slowPart_eq_zero (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u})
    (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal)
    (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (heq : S.IsEquilibriumState s μ) (hdec : S.GibbsDecomposition s μ μ₁ μ₂) :
    μ₁ (S.slowPart μ) = 0 := by
  obtain ⟨-, ⟨-, -, z3, z4⟩, -⟩ :=
    S.gibbs_tau_omega_positive hms hfk hrot hdiag hs0 hs2 μ hinv herg heq hdec
  exact measure_union_null z3 z4

/-- `thm:gibbs_tau_omega_positive`: `μ_2(τ(Σ^τ) ∪ ω(Σ^ω)) = 0`. -/
theorem measure_fastPart_eq_zero (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u})
    (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal)
    (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (heq : S.IsEquilibriumState s μ) (hdec : S.GibbsDecomposition s μ μ₁ μ₂) :
    μ₂ (S.fastPart μ) = 0 := by
  obtain ⟨-, ⟨z1, z2, -, -⟩, -⟩ :=
    S.gibbs_tau_omega_positive hms hfk hrot hdiag hs0 hs2 μ hinv herg heq hdec
  exact measure_union_null z1 z2

/-- `thm:gibbs_tau_omega_positive`: `μ_1`-almost every point lies in `τ(Σ^τ) ∪ ω(Σ^ω)`. -/
theorem ae_mem_fastPart (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal)
    (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (heq : S.IsEquilibriumState s μ) [IsProbabilityMeasure μ₁]
    (hdec : S.GibbsDecomposition s μ μ₁ μ₂) : ∀ᵐ y ∂μ₁, y ∈ S.fastPart μ := by
  obtain ⟨⟨h1, -⟩, -, -⟩ :=
    S.gibbs_tau_omega_positive hms hfk hrot hdiag hs0 hs2 μ hinv herg heq hdec
  have hm := measurableSet_omega_image S.o (S.measurableSet_SigmaOmega μ)
  have hdisj : Disjoint (tau S.o '' S.SigmaTau μ) (omega S.o '' S.SigmaOmega μ) :=
    disjoint_range_tau_range_omega.mono (image_subset_range _ _) (image_subset_range _ _)
  rw [← measure_union hdisj hm] at h1
  exact (prob_compl_eq_zero_iff
    ((measurableSet_tau_image S.o (S.measurableSet_SigmaTau μ)).union hm)).2 h1

/-- `thm:gibbs_tau_omega_positive`: `μ_2`-almost every point lies in `ω(Σ^τ) ∪ τ(Σ^ω)`. -/
theorem ae_mem_slowPart (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal)
    (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (heq : S.IsEquilibriumState s μ) [IsProbabilityMeasure μ₂]
    (hdec : S.GibbsDecomposition s μ μ₁ μ₂) : ∀ᵐ y ∂μ₂, y ∈ S.slowPart μ := by
  obtain ⟨⟨-, h2⟩, -, -⟩ :=
    S.gibbs_tau_omega_positive hms hfk hrot hdiag hs0 hs2 μ hinv herg heq hdec
  have hm := measurableSet_tau_image S.o (S.measurableSet_SigmaOmega μ)
  have hdisj : Disjoint (omega S.o '' S.SigmaTau μ) (tau S.o '' S.SigmaOmega μ) :=
    disjoint_range_tau_range_omega.symm.mono (image_subset_range _ _) (image_subset_range _ _)
  rw [← measure_union hdisj hm] at h2
  exact (prob_compl_eq_zero_iff
    ((measurableSet_omega_image S.o (S.measurableSet_SigmaTau μ)).union hm)).2 h2

/-! ### The average measure on the two parts -/

/-- Proof of `thm:overline_h1_zero`, first case of the display, and `thm:overline_h1_large`:
`\overline{h}_1(\overline{μ}, 𝐢) = \overline{h}_1(μ_1)` for `\overline{μ}`-almost every
`𝐢 ∈ τ(Σ^τ) ∪ ω(Σ^ω)`. On this set `\overline{μ}_𝐢^{\overline{ξ}_1} = (μ_1)_𝐢^{\overline{ξ}_1}`
by `thm:conditional_two_ways`, and `μ_2` does not charge it.
Depends on: `thm:feng_entropy_as_limit` (scalar), `eq:ergodic_entropy_constant`,
`thm:conditional_two_ways`, `thm:gibbs_tau_omega_positive`. -/
theorem dimEntropyBarAt_avgMeasure_fast (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfib : FengInfoSumBar.{u}) (hrot : S.WithRotations)
    (hdiag : S.HasProximalDiagonal) (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (hdec : S.GibbsDecomposition s μ μ₁ μ₂) :
    ∀ᵐ y ∂avgMeasure μ₁ μ₂, y ∈ S.fastPart μ →
      S.dimEntropyBarAt (avgMeasure μ₁ μ₂) 1 y = S.dimEntropyBar μ₁ 1 := by
  have := isProbabilityMeasure_avgMeasure μ₁ μ₂
  have hc := (ae_of_ae_avgMeasure
    (S.conditional_two_ways_normalised hms hfk hrot hdiag hs0 hs2 μ hinv herg heq hdec)).1
  have hlim := S.dimEntropyBarAt_eq_of_condMeas_eq hfib hrot hdiag.proximal (avgMeasure μ₁ μ₂) μ₁
    (measurePreserving_shift_avgMeasure hdec.ergodic₁.toMeasurePreserving
      hdec.ergodic₂.toMeasurePreserving) (avgMeasure_eq_zero hdec.supp₁ hdec.supp₂)
    hdec.ergodic₁ hdec.supp₁ absolutelyContinuous_avgMeasure_left
  refine ae_avgMeasure_iff.2 ⟨?_, ?_⟩
  · filter_upwards [hc, hlim] with y hc hlim hy
    exact hlim (hy.elim (fun h => (hc.1 h).1) fun h => (hc.2.2.1 h).1)
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (S.measure_fastPart_eq_zero hms hfk hrot hdiag hs0 hs2 μ hinv herg heq hdec)] with y hy hy'
    exact absurd hy' hy

/-- Proof of `thm:overline_h1_zero`, second case of the display:
`\overline{h}_1(\overline{μ}, 𝐢) = \overline{h}_1(μ_2)` for `\overline{μ}`-almost every
`𝐢 ∈ ω(Σ^τ) ∪ τ(Σ^ω)`. On this set `\overline{μ}_𝐢^{\overline{ξ}_1} = (μ_2)_𝐢^{\overline{ξ}_1}`
by `thm:conditional_two_ways`, and `μ_1` does not charge it.
Depends on: `thm:feng_entropy_as_limit` (scalar), `eq:ergodic_entropy_constant`,
`thm:conditional_two_ways`, `thm:gibbs_tau_omega_positive`. -/
theorem dimEntropyBarAt_avgMeasure_slow (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfib : FengInfoSumBar.{u}) (hrot : S.WithRotations)
    (hdiag : S.HasProximalDiagonal) (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (hdec : S.GibbsDecomposition s μ μ₁ μ₂) :
    ∀ᵐ y ∂avgMeasure μ₁ μ₂, y ∈ S.slowPart μ →
      S.dimEntropyBarAt (avgMeasure μ₁ μ₂) 1 y = S.dimEntropyBar μ₂ 1 := by
  have := isProbabilityMeasure_avgMeasure μ₁ μ₂
  have hc := (ae_of_ae_avgMeasure
    (S.conditional_two_ways_normalised hms hfk hrot hdiag hs0 hs2 μ hinv herg heq hdec)).2
  have hlim := S.dimEntropyBarAt_eq_of_condMeas_eq hfib hrot hdiag.proximal (avgMeasure μ₁ μ₂) μ₂
    (measurePreserving_shift_avgMeasure hdec.ergodic₁.toMeasurePreserving
      hdec.ergodic₂.toMeasurePreserving) (avgMeasure_eq_zero hdec.supp₁ hdec.supp₂)
    hdec.ergodic₂ hdec.supp₂ absolutelyContinuous_avgMeasure_right
  refine ae_avgMeasure_iff.2 ⟨?_, ?_⟩
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (S.measure_slowPart_eq_zero hms hfk hrot hdiag hs0 hs2 μ hinv herg heq hdec)] with y hy hy'
    exact absurd hy' hy
  · filter_upwards [hc, hlim] with y hc hlim hy
    exact hlim (hy.elim (fun h => (hc.2.1 h).1) fun h => (hc.2.2.2 h).1)

/-- Proof of `thm:overline_h1_zero_large`, the part that carries `μ_2`: if
`(μ_2)_𝐢^{\overline{ξ}_1} = δ_𝐢` for `μ_2`-almost every `𝐢`, then
`\overline{μ}_𝐢^{\overline{ξ}_1} = δ_𝐢` for `\overline{μ}`-almost every
`𝐢 ∈ ω(Σ^τ) ∪ τ(Σ^ω)`, by `thm:conditional_two_ways`; the measure `μ_1` does not charge this set.
Depends on: `thm:conditional_two_ways`, `thm:gibbs_tau_omega_positive`. -/
theorem condMeas_avgMeasure_eq_dirac_slow (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hrot : S.WithRotations)
    (hdiag : S.HasProximalDiagonal) (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (hdec : S.GibbsDecomposition s μ μ₁ μ₂)
    (hd : ∀ᵐ y ∂μ₂, condMeas μ₂ (S.xiBar 1) y = Measure.dirac y) :
    ∀ᵐ y ∂avgMeasure μ₁ μ₂, y ∈ S.slowPart μ →
      condMeas (avgMeasure μ₁ μ₂) (S.xiBar 1) y = Measure.dirac y := by
  have hc := (ae_of_ae_avgMeasure
    (S.conditional_two_ways_normalised hms hfk hrot hdiag hs0 hs2 μ hinv herg heq hdec)).2
  refine ae_avgMeasure_iff.2 ⟨?_, ?_⟩
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1
      (S.measure_slowPart_eq_zero hms hfk hrot hdiag hs0 hs2 μ hinv herg heq hdec)] with y hy hy'
    exact absurd hy' hy
  · filter_upwards [hc, hd] with y hc hd hy
    rcases hy with hy | hy
    · rw [(hc.2.1 hy).1, hd]
    · rw [(hc.2.2.2 hy).1, hd]

/-! ### `sec:average_gibbs_entropy` -/

/-- `thm:overline_h1_zero`: under projective exponential separation, if
`h_0(μ) ≤ -λ_1(𝖠, μ)`, then `\overline{h}_1(\overline{μ}, 𝐢) = 0` for `\overline{μ}`-almost
every `𝐢`. Here `h_0(μ)` is `entropy μ`.
Depends on: `JordanRapaportDimension`, `thm:entropy_eq_gibbs`, `thm:eq_state_is_sum`,
`eq:simple_lyapunov`, `thm:feng1` (scalar), `dimEntropyBar_zero_eq_entropy`,
`thm:feng_entropy_as_limit` (scalar), `eq:ergodic_entropy_constant`,
`thm:conditional_two_ways`, `thm:gibbs_tau_omega_positive`. -/
theorem overline_h1_zero (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hjr : JordanRapaportDimension.{u}) (hfib : FengInfoSumBar.{u})
    (hlyb : FengLedrappierYoungBar.{u}) (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal)
    (hsep : S.ProjExpSeparation) (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ)
    (hent : entropy μ ≤ -S.lyapunov₁ μ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hdec : S.GibbsDecomposition s μ μ₁ μ₂) :
    ∀ᵐ y ∂avgMeasure μ₁ μ₂, S.dimEntropyBarAt (avgMeasure μ₁ μ₂) 1 y = 0 := by
  have hprox := hdiag.proximal
  have hlt := S.simple_lyapunov hms hrot hprox hs0 hs2 μ hinv heq
  -- `eq:h1_gibbs_entropy_zero`.
  have h₁ : S.dimEntropyBar μ₁ 1 = 0 :=
    S.dimEntropyBar_one_eq_zero hjr hlyb hrot hprox hsep μ₁ hdec.ergodic₁ hdec.supp₁
      (by rw [hdec.entropy_eq₁, ← hdec.lyapunov₁_eq]; exact hent)
  have h₂ : S.dimEntropyBar μ₂ 1 = 0 :=
    S.dimEntropyBar_one_eq_zero hjr hlyb hrot hprox hsep μ₂ hdec.ergodic₂ hdec.supp₂
      (by rw [hdec.entropy_eq₂, ← hdec.lyapunov₂_eq]; linarith)
  -- The two cases of the display in the proof.
  have hfast :=
    S.dimEntropyBarAt_avgMeasure_fast hms hfk hfib hrot hdiag hs0 hs2 μ hinv herg heq hdec
  have hslow :=
    S.dimEntropyBarAt_avgMeasure_slow hms hfk hfib hrot hdiag hs0 hs2 μ hinv herg heq hdec
  have hmem : ∀ᵐ y ∂avgMeasure μ₁ μ₂, y ∈ S.fastPart μ ∪ S.slowPart μ :=
    ae_avgMeasure_iff.2
      ⟨(S.ae_mem_fastPart hms hfk hrot hdiag hs0 hs2 μ hinv herg heq hdec).mono
          fun _ h => Or.inl h,
        (S.ae_mem_slowPart hms hfk hrot hdiag hs0 hs2 μ hinv herg heq hdec).mono
          fun _ h => Or.inr h⟩
  filter_upwards [hfast, hslow, hmem] with y hf hs hm
  rcases hm with h | h
  · rw [hf h, h₁]
  · rw [hs h, h₂]

/-- `thm:overline_h1_zero_large`: under projective exponential separation, if
`h_0(μ) ≤ -λ_2(𝖠, μ)`, then `\overline{h}_1(μ_2) = 0` and
`\overline{μ}_𝐢^{\overline{ξ}_1} = δ_𝐢` for `\overline{μ}`-almost every
`𝐢 ∈ ω(Σ^τ) ∪ τ(Σ^ω)`. The article writes the second assertion as an equality of measures of
sets.
Depends on: `thm:entropy_eq_gibbs`, `thm:eq_state_is_sum`, `JordanRapaportDimension`,
`thm:feng1` (scalar), `dimEntropyBar_zero_eq_entropy`, `thm:feng_entropy_zero` (scalar),
`eq:ergodic_entropy_constant`, `thm:conditional_two_ways`, `thm:gibbs_tau_omega_positive`. -/
theorem overline_h1_zero_large (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u})
    (hjr : JordanRapaportDimension.{u}) (hfib : FengInfoSumBar.{u})
    (hlyb : FengLedrappierYoungBar.{u}) (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal)
    (hsep : S.ProjExpSeparation) (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ)
    (hent₂ : entropy μ ≤ -S.lyapunov₂ μ)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hdec : S.GibbsDecomposition s μ μ₁ μ₂) :
    S.dimEntropyBar μ₂ 1 = 0 ∧
      ∀ᵐ y ∂avgMeasure μ₁ μ₂, y ∈ S.slowPart μ →
        condMeas (avgMeasure μ₁ μ₂) (S.xiBar 1) y = Measure.dirac y := by
  have hprox := hdiag.proximal
  have h₂ : S.dimEntropyBar μ₂ 1 = 0 :=
    S.dimEntropyBar_one_eq_zero hjr hlyb hrot hprox hsep μ₂ hdec.ergodic₂ hdec.supp₂
      (by rw [hdec.entropy_eq₂, ← hdec.lyapunov₂_eq]; exact hent₂)
  exact ⟨h₂, S.condMeas_avgMeasure_eq_dirac_slow hms hfk hrot hdiag hs0 hs2 μ hinv herg heq hdec
    (S.condMeas_xiBar_eq_dirac hfib hrot hprox μ₂ hdec.ergodic₂ hdec.supp₂ h₂)⟩

end System

end BoxLike
