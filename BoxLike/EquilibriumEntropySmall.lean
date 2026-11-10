module

/-
The vanishing of the higher dimensional entropies of the equilibrium state:
`thm:eq_state_h1_zero`, `thm:eq_state_h2_zero` and `thm:orto_partition_dirac` of
`sec:higher_dimensional_entropies`.

The Gibbs measures `μ_1`, `μ_2` come from `thm:irred_eq_state` and `thm:eq_state_is_sum`. By
`sec:average_gibbs_entropy` the conditional measures `\overline{μ}_𝐣^{\overline{ξ}_1}` of their
average are Dirac masses, on all of `Σ_Z` when `h_0(μ) ≤ -λ_1(𝖠, μ)` and on
`ω(Σ^τ) ∪ τ(Σ^ω)` when `h_0(μ) ≤ -λ_2(𝖠, μ)`. For a coding `T ∈ {τ, ω}` and
`E ∈ {Σ^τ, Σ^ω}`, `thm:conditional_two_ways` identifies `\overline{μ}_𝐣^{\overline{ξ}_1}` on
`T(E)` with `T_*μ_𝐢^ζ`, where `ζ` is `ξ_1` or `ξ_1^⊥`, and `eq:orientation-restrictions` carries
almost everywhere statements from `T(E)` to `E`. Since `T` is injective, `μ_𝐢^ζ = δ_𝐢` for
`μ`-almost every `𝐢`. The partition `ξ_2` refines `ξ_1` and `ξ_1^⊥`, so
`thm:finer_partition_dirac_mass` gives `μ_𝐢^{ξ_2} = δ_𝐢`, and `thm:feng_entropy_zero` turns
Dirac conditional measures into vanishing entropy.

* `eq_dirac_of_map_coding`: `T_*m = δ_{T(𝐢)}` gives `m = δ_𝐢` for a coding `T ∈ {τ, ω}`.
* `System.ae_of_ae_avgMeasure_image`: almost everywhere statements pass from `T(E)` and
  `\overline{μ}` to `E` and `μ`, by `eq:orientation-restrictions`.
* `System.condMeas_eq_dirac_of_avgMeasure`: the transport of Dirac conditional measures from
  `\overline{μ}` on `T(E)` to `μ` on `E`.
* `System.dimEntropy_eq_zero_of_condMeas_eq_dirac`: `μ_𝐢^{ξ_i} = δ_𝐢` almost everywhere gives
  `h_i(μ) = 0`, from `thm:feng_entropy_zero` and `eq:ergodic_entropy_constant`.
* `System.eq_state_h1_zero`: `thm:eq_state_h1_zero`.
* `System.eq_state_h2_zero`: `thm:eq_state_h2_zero`.
* `System.orto_partition_dirac`: `thm:orto_partition_dirac`.
-/
public import BoxLike.AverageEntropy
public import BoxLike.EquilibriumGibbsStatement
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

@[expose] public section

namespace BoxLike

open MeasureTheory Set

universe u

section Coding

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- "Since `T` is injective" in the proofs of `thm:eq_state_h1_zero` and
`thm:orto_partition_dirac`: for a coding `T ∈ {τ, ω}`, a measure `m` on `Σ` with
`T_*m = δ_{T(𝐢)}` is `δ_𝐢`, because the map `q` that forgets the axis is a Borel left inverse of
`T`. -/
theorem eq_dirac_of_map_coding {o : ι → ZMod 2} {T : (ℤ → ι) → ℤ → ι × ZMod 2}
    (hT : T = tau o ∨ T = omega o) {m : Measure (ℤ → ι)} {x : ℤ → ι}
    (h : m.map T = Measure.dirac (T x)) : m = Measure.dirac x := by
  have hTm : Measurable T := by
    rcases hT with rfl | rfl
    exacts [measurable_tau o, measurable_omega o]
  have hun : ∀ z, unCode (T z) = z := by
    rcases hT with rfl | rfl
    exacts [fun z => unCode_tau z, fun z => unCode_omega z]
  have h' := congrArg (Measure.map unCode) h
  rw [Measure.map_map measurable_unCode hTm, Measure.map_dirac' measurable_unCode, hun] at h'
  rw [← h', show unCode ∘ T = id from funext hun, Measure.map_id]

end Coding

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {s : ℝ}

/-! ### From the average measure to the equilibrium state -/

section Transport

variable {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)}

/-- `eq:orientation-restrictions` for almost everywhere statements: for `T ∈ {τ, ω}` and
`E ∈ {Σ^τ, Σ^ω}`, a property that holds for `\overline{μ}`-almost every point of `T(E)` holds at
`T(𝐢)` for `μ`-almost every `𝐢 ∈ E`, because `\overline{μ}|_{T(E)} = ½ T_*(μ|_E)`. -/
theorem ae_of_ae_avgMeasure_image (hfk : EquilibriumGibbsStatement.{u})
    (hrot : S.WithRotations) (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ)
    (hdec : S.GibbsDecomposition s μ μ₁ μ₂)
    {T : (ℤ → ι) → ℤ → ι × ZMod 2} (hT : T = tau S.o ∨ T = omega S.o) {E : Set (ℤ → ι)}
    (hE : E = S.SigmaTau μ ∨ E = S.SigmaOmega μ) {p : (ℤ → ι × ZMod 2) → Prop}
    (h : ∀ᵐ y ∂avgMeasure μ₁ μ₂, y ∈ T '' E → p y) : ∀ᵐ x ∂μ, x ∈ E → p (T x) := by
  have hEm : MeasurableSet E := by
    rcases hE with rfl | rfl
    exacts [S.measurableSet_SigmaTau μ, S.measurableSet_SigmaOmega μ]
  have hTm : Measurable T := by
    rcases hT with rfl | rfl
    exacts [measurable_tau S.o, measurable_omega S.o]
  have hF : MeasurableSet (T '' E) := by
    rcases hT with rfl | rfl
    exacts [measurableSet_tau_image S.o hEm, measurableSet_omega_image S.o hEm]
  have h1 : ∀ᵐ y ∂(avgMeasure μ₁ μ₂).restrict (T '' E), p y := (ae_restrict_iff' hF).2 h
  rw [(S.orientation_restrictions hfk hrot hs0 hs2 μ hinv herg heq hdec hT hE).1,
    Measure.ae_smul_measure_iff (by norm_num)] at h1
  exact (ae_restrict_iff' hEm).1 (ae_of_ae_map hTm.aemeasurable h1)

/-- Proofs of `thm:eq_state_h1_zero` and `thm:orto_partition_dirac`: let `T ∈ {τ, ω}`,
`E ∈ {Σ^τ, Σ^ω}` and let `ζ` be a partition of `Σ`. If `T_*μ_{\overline{T}(𝐣)}^ζ = δ_𝐣` for
`\overline{μ}`-almost every `𝐣 ∈ T(E)`, then `μ_𝐢^ζ = δ_𝐢` for `μ`-almost every `𝐢 ∈ E`.
Depends on: `eq:orientation-restrictions`. -/
theorem condMeas_eq_dirac_of_avgMeasure (hfk : EquilibriumGibbsStatement.{u})
    (hrot : S.WithRotations) (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ)
    (hdec : S.GibbsDecomposition s μ μ₁ μ₂) {T : (ℤ → ι) → ℤ → ι × ZMod 2}
    (hT : T = tau S.o ∨ T = omega S.o) {E : Set (ℤ → ι)}
    (hE : E = S.SigmaTau μ ∨ E = S.SigmaOmega μ) (ζ : (ℤ → ι) → Set (ℤ → ι))
    (h : ∀ᵐ y ∂avgMeasure μ₁ μ₂, y ∈ T '' E →
      (condMeas μ ζ (unCode y)).map T = Measure.dirac y) :
    ∀ᵐ x ∂μ, x ∈ E → condMeas μ ζ x = Measure.dirac x := by
  have hun : ∀ z, unCode (T z) = z := by
    rcases hT with rfl | rfl
    exacts [fun z => unCode_tau z, fun z => unCode_omega z]
  filter_upwards [S.ae_of_ae_avgMeasure_image hfk hrot hs0 hs2 μ hinv herg heq hdec hT hE h]
    with x hx hxE
  have h' := hx hxE
  rw [hun] at h'
  exact eq_dirac_of_map_coding hT h'

end Transport

/-- `thm:feng_entropy_zero` with `eq:ergodic_entropy_constant`: for ergodic `μ` with
`λ_2 < λ_1`, if `μ_𝐢^{ξ_i} = δ_𝐢` for `μ`-almost every `𝐢`, then `h_i(μ) = 0`. -/
theorem dimEntropy_eq_zero_of_condMeas_eq_dirac (hfi : FengInfoSum.{u}) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) (i : ℕ)
    (h : ∀ᵐ x ∂μ, condMeas μ (S.xi μ i) x = Measure.dirac x) : S.dimEntropy μ i = 0 := by
  obtain ⟨x, h1, h2, h3⟩ := (h.and ((S.feng_entropy_zero hfi μ hinv herg hlt i).and
    (localEntropy_ae_eq μ herg (S.xi μ i)))).exists
  exact h3.symm.trans (h2.2 h1)

/-! ### `sec:higher_dimensional_entropies` -/

/-- `thm:eq_state_h1_zero`: under projective exponential separation, if
`h_0(μ) ≤ -λ_1(𝖠, μ)`, then `h_1(μ) = 0` and `μ_𝐢^{ξ_1} = δ_𝐢` for `μ`-almost every `𝐢`. The
Gibbs measures are obtained inside the proof from the Gibbs bounds of `thm:irred_eq_state`,
`EquilibriumGibbsStatement`, and the decomposition of `thm:eq_state_is_sum`,
`FraserJordanJurgaDecomposition`.
Depends on: `thm:overline_h1_zero`, `thm:feng_entropy_zero` (both parts),
`thm:conditional_two_ways`, `eq:orientation-restrictions`, `eq:tau_omega_partition2`,
`measure_SigmaPrime_compl`, `eq:ergodic_entropy_constant`. -/
theorem eq_state_h1_zero (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hjr : JordanRapaportDimension.{u})
    (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u}) (hlyb : FengLedrappierYoungBar.{u})
    (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal) (hsep : S.ProjExpSeparation)
    (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (heq : S.IsEquilibriumState s μ) (hent : entropy μ ≤ -S.lyapunov₁ μ) :
    S.dimEntropy μ 1 = 0 ∧ ∀ᵐ x ∂μ, condMeas μ (S.xi μ 1) x = Measure.dirac x := by
  have hprox := hdiag.proximal
  have hlt := S.simple_lyapunov hms hrot hprox hs0 hs2 μ hinv heq
  have hgibbs := hfk S hrot hs0 hs2 μ hinv heq
  obtain ⟨μ₁, μ₂, hdec⟩ := hfjj S hrot hdiag hs0 hs2 μ hinv hgibbs
  have := hdec.prob₁
  have := hdec.prob₂
  have := isProbabilityMeasure_avgMeasure μ₁ μ₂
  -- `\overline{μ}_𝐣^{\overline{ξ}_1} = δ_𝐣` for `\overline{μ}`-almost every `𝐣`.
  have hbar : ∀ᵐ y ∂avgMeasure μ₁ μ₂,
      condMeas (avgMeasure μ₁ μ₂) (S.xiBar 1) y = Measure.dirac y := by
    filter_upwards [S.overline_h1_zero hms hfk hjr hfib hlyb hrot hdiag hsep hs0 hs2 μ hinv herg
        heq hent hdec,
      S.feng_entropy_zero_bar hfib hrot hprox (avgMeasure μ₁ μ₂)
        (measurePreserving_shift_avgMeasure hdec.ergodic₁.toMeasurePreserving
          hdec.ergodic₂.toMeasurePreserving) (avgMeasure_eq_zero hdec.supp₁ hdec.supp₂) 1]
      with y h0 hiff
    exact hiff.1 h0
  have hc := S.conditional_two_ways_normalised hms hfk hrot hdiag hs0 hs2 μ hinv herg heq hdec
  -- `T_*μ_𝐢^{ξ_1} = δ_{T(𝐢)}` on `Σ^τ` for `T = τ` and on `Σ^ω` for `T = ω`.
  have hτ : ∀ᵐ x ∂μ, x ∈ S.SigmaTau μ → condMeas μ (S.xi μ 1) x = Measure.dirac x := by
    refine S.condMeas_eq_dirac_of_avgMeasure hfk hrot hs0 hs2 μ hinv herg heq hdec
      (Or.inl rfl) (Or.inl rfl) _ ?_
    filter_upwards [hbar, hc] with y hb hy hyF
    rw [← (hy.1 hyF).2, ← (hy.1 hyF).1, hb]
  have hω : ∀ᵐ x ∂μ, x ∈ S.SigmaOmega μ → condMeas μ (S.xi μ 1) x = Measure.dirac x := by
    refine S.condMeas_eq_dirac_of_avgMeasure hfk hrot hs0 hs2 μ hinv herg heq hdec
      (Or.inr rfl) (Or.inr rfl) _ ?_
    filter_upwards [hbar, hc] with y hb hy hyF
    rw [← (hy.2.2.1 hyF).2, ← (hy.2.2.1 hyF).1, hb]
  -- The sets `Σ^τ` and `Σ^ω` cover `Σ'`, which has full measure.
  have hfull : ∀ᵐ x ∂μ, x ∈ S.SigmaPrime μ :=
    (measure_eq_zero_iff_ae_notMem.1 (S.measure_SigmaPrime_compl μ hinv herg)).mono
      fun x hx => not_not.1 hx
  have hd : ∀ᵐ x ∂μ, condMeas μ (S.xi μ 1) x = Measure.dirac x := by
    filter_upwards [hτ, hω, hfull] with x h1 h2 hx
    exact hx.elim h1 h2
  exact ⟨S.dimEntropy_eq_zero_of_condMeas_eq_dirac hfi μ hinv herg hlt 1 hd, hd⟩

/-- `thm:eq_state_h2_zero`: under projective exponential separation, if
`h_0(μ) ≤ -λ_1(𝖠, μ)`, then `h_2(μ) = 0`.
Depends on: `thm:eq_state_h1_zero`, `thm:finer_partition_dirac_mass`, `thm:feng_entropy_zero`,
`isMeasurablePartition_xi`, `eq:ergodic_entropy_constant`. -/
theorem eq_state_h2_zero (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hjr : JordanRapaportDimension.{u})
    (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u}) (hlyb : FengLedrappierYoungBar.{u})
    (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal) (hsep : S.ProjExpSeparation)
    (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (heq : S.IsEquilibriumState s μ) (hent : entropy μ ≤ -S.lyapunov₁ μ) :
    S.dimEntropy μ 2 = 0 := by
  have hlt := S.simple_lyapunov hms hrot hdiag.proximal hs0 hs2 μ hinv heq
  have h1 := (S.eq_state_h1_zero hms hfk hfjj hjr hfi hfib hlyb hrot hdiag hsep hs0 hs2 μ hinv
    herg heq hent).2
  have h2 := finer_partition_dirac_mass μ (S.isMeasurablePartition_xi μ 1)
    (S.isMeasurablePartition_xi μ 2) (S.xi_succ_subset μ 1) h1
  exact S.dimEntropy_eq_zero_of_condMeas_eq_dirac hfi μ hinv herg hlt 2 h2

/-- `thm:orto_partition_dirac`: under projective exponential separation, if
`h_0(μ) ≤ -λ_2(𝖠, μ)`, then `h_2(μ) = 0`.
Depends on: `thm:overline_h1_zero_large`, `thm:conditional_two_ways`,
`eq:orientation-restrictions`, `thm:finer_partition_dirac_mass`, `thm:feng_entropy_zero`,
`isMeasurablePartition_xi`, `isMeasurablePartition_xiPerp`, `eq:ergodic_entropy_constant`. -/
theorem orto_partition_dirac (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hjr : JordanRapaportDimension.{u})
    (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u}) (hlyb : FengLedrappierYoungBar.{u})
    (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal) (hsep : S.ProjExpSeparation)
    (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (heq : S.IsEquilibriumState s μ)
    (hent₂ : entropy μ ≤ -S.lyapunov₂ μ) : S.dimEntropy μ 2 = 0 := by
  have hlt := S.simple_lyapunov hms hrot hdiag.proximal hs0 hs2 μ hinv heq
  have hgibbs := hfk S hrot hs0 hs2 μ hinv heq
  obtain ⟨μ₁, μ₂, hdec⟩ := hfjj S hrot hdiag hs0 hs2 μ hinv hgibbs
  have := hdec.prob₁
  have := hdec.prob₂
  -- `\overline{μ}_𝐣^{\overline{ξ}_1} = δ_𝐣` for `\overline{μ}`-almost every
  -- `𝐣 ∈ ω(Σ^τ) ∪ τ(Σ^ω)`.
  have hbar := (S.overline_h1_zero_large hms hfk hjr hfib hlyb hrot hdiag hsep hs0 hs2 μ hinv
    herg heq hent₂ hdec).2
  have hc := S.conditional_two_ways_normalised hms hfk hrot hdiag hs0 hs2 μ hinv herg heq hdec
  -- `T_*μ_𝐢^{ξ_1^⊥} = δ_{T(𝐢)}` on `Σ^τ` for `T = ω` and on `Σ^ω` for `T = τ`.
  have hτ : ∀ᵐ x ∂μ, x ∈ S.SigmaTau μ → condMeas μ (S.xiPerp μ) x = Measure.dirac x := by
    refine S.condMeas_eq_dirac_of_avgMeasure hfk hrot hs0 hs2 μ hinv herg heq hdec
      (Or.inr rfl) (Or.inl rfl) _ ?_
    filter_upwards [hbar, hc] with y hb hy hyF
    rw [← (hy.2.1 hyF).2, ← (hy.2.1 hyF).1, hb (Or.inl hyF)]
  have hω : ∀ᵐ x ∂μ, x ∈ S.SigmaOmega μ → condMeas μ (S.xiPerp μ) x = Measure.dirac x := by
    refine S.condMeas_eq_dirac_of_avgMeasure hfk hrot hs0 hs2 μ hinv herg heq hdec
      (Or.inl rfl) (Or.inr rfl) _ ?_
    filter_upwards [hbar, hc] with y hb hy hyF
    rw [← (hy.2.2.2 hyF).2, ← (hy.2.2.2 hyF).1, hb (Or.inr hyF)]
  have hfull : ∀ᵐ x ∂μ, x ∈ S.SigmaPrime μ :=
    (measure_eq_zero_iff_ae_notMem.1 (S.measure_SigmaPrime_compl μ hinv herg)).mono
      fun x hx => not_not.1 hx
  have hd : ∀ᵐ x ∂μ, condMeas μ (S.xiPerp μ) x = Measure.dirac x := by
    filter_upwards [hτ, hω, hfull] with x h1 h2 hx
    exact hx.elim h1 h2
  -- `ξ_2` refines `ξ_1^⊥`.
  have h2 := finer_partition_dirac_mass μ (S.isMeasurablePartition_xiPerp μ)
    (S.isMeasurablePartition_xi μ 2) (S.xi_two_subset_xiPerp μ) hd
  exact S.dimEntropy_eq_zero_of_condMeas_eq_dirac hfi μ hinv herg hlt 2 h2

end System

end BoxLike
