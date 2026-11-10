module

/-
The one-dimensional entropy of the equilibrium state when its Kolmogorov–Sinai entropy is large:
`thm:overline_h1_large` of `sec:average_gibbs_entropy` and `thm:eq_state_h1_large` of
`sec:higher_dimensional_entropies`.

Let `(T, E)` be `(τ, Σ^τ)` or `(ω, Σ^ω)`. On `T(E)` the conditional measures of
`\overline{μ} = (μ_1 + μ_2)/2` and of `μ_1` given `\overline{ξ}_1` agree, and they are the images
under `T` of the conditional measures of `μ` given `ξ_1` (`thm:conditional_two_ways`). Since
`T⁻¹(\overline{𝒫}_0^{n-1}(T(𝐢))) = 𝒫_0^{n-1}(𝐢)`, the three conditional measures give the same
mass to the cylinders of length `n`, so the three limits of `thm:feng_entropy_as_limit` agree. The
limits for the ergodic measures `μ_1` and `μ` are the constants `\overline{h}_1(μ_1)` and
`h_1(μ)`, by `eq:ergodic_entropy_constant`. Null sets pass from `μ_1` and from `μ` to
`\overline{μ}|_{T(E)}` through `thm:gibbs_tau_omega_positive` and `eq:orientation-restrictions`.

For `thm:eq_state_h1_large`, Jordan–Rapaport and the scalar part of `thm:feng1` give two values of
`dim \overline{π}_*μ_1`; they agree, and `\overline{h}_0(μ_1) = h_0(μ)`,
`\overline{λ}(𝖠, μ_1) = λ_1(𝖠, μ)`, `\overline{h}_1(μ_1) = h_1(μ)` turn the equality into
`h_1(μ) = h_0(μ) + λ_1(𝖠, μ)`.

* `h1Large_measurePreserving_avgMeasure`: the average of two invariant measures is invariant.
* `h1Large_ae_avgMeasure_of_measure_eq_zero`: a `μ_1`-almost sure property holds
  `\overline{μ}`-almost everywhere on a `μ_2`-null set.
* `h1Large_ae_unCode_of_restrict`: a `μ`-almost sure property holds at `\overline{T}(𝐣)` for
  `ν`-almost every `𝐣 ∈ F`, when `ν|_F` is a multiple of `T_*(μ|_E)`.
* `h1Large_map_cylinder_block`: `T_*ρ(\overline{𝒫}_0^{n-1}(T(𝐢))) = ρ(𝒫_0^{n-1}(𝐢))`.
* `System.h1Large_aux`: `thm:overline_h1_large` on one of the two sets `T(E)`.
* `System.overline_h1_large`: `thm:overline_h1_large`.
* `System.eq_state_h1_large`: `thm:eq_state_h1_large`.
-/
public import BoxLike.Aligned.ConditionalTwoWays
public import BoxLike.ConditionalTwoWays
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.FengEntropy
public import BoxLike.General
public import BoxLike.PastEntropy
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

@[expose] public section

namespace BoxLike

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

universe u

/-! ### The average measure -/

section Average

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The average `\overline{μ} = (μ_1 + μ_2)/2` of `eq:average_gibbs` of two measures invariant
under `f` is invariant under `f`. For the two Gibbs measures this is
`\overline{μ} ∈ ℳ_σ(Σ_Z)` of `sec:average_gibbs`. -/
theorem h1Large_measurePreserving_avgMeasure {f : Ω → Ω} {m₁ m₂ : Measure Ω}
    (h₁ : MeasurePreserving f m₁ m₁) (h₂ : MeasurePreserving f m₂ m₂) :
    MeasurePreserving f (avgMeasure m₁ m₂) (avgMeasure m₁ m₂) := by
  refine ⟨h₁.measurable, ?_⟩
  rw [avgMeasure, Measure.map_smul _ h₁.measurable.aemeasurable, Measure.map_add _ _ h₁.measurable,
    h₁.map_eq, h₂.map_eq]

/-- Proof of `thm:overline_h1_large`, "after discarding a `\overline{μ}`-null subset of `T(E)`":
on a set `F` with `μ_2(F) = 0` the average `\overline{μ}` of `eq:average_gibbs` is `½ μ_1`, so a
property that holds `μ_1`-almost everywhere holds for `\overline{μ}`-almost every point of `F`. -/
theorem h1Large_ae_avgMeasure_of_measure_eq_zero {m₁ m₂ : Measure Ω} {F : Set Ω}
    (hF : m₂ F = 0) {p : Ω → Prop} (hp : ∀ᵐ y ∂m₁, p y) :
    ∀ᵐ y ∂avgMeasure m₁ m₂, y ∈ F → p y := by
  have h₁ : ∀ᵐ y ∂m₁, y ∈ F → p y := hp.mono fun y hy _ => hy
  have h₂ : ∀ᵐ y ∂m₂, y ∈ F → p y := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hF] with y hy hyF
    exact absurd hyF hy
  exact Measure.ae_smul_measure (ae_add_measure_iff.2 ⟨h₁, h₂⟩) (2⁻¹ : ℝ≥0)

end Average

/-! ### The codings -/

section Coding

variable {ι : Type u} [MeasurableSpace ι]

/-- Proof of `thm:overline_h1_large`, "the corresponding base points satisfy the entropy limit for
`μ`": if `ν|_F = c T_*(μ|_E)`, as in `eq:orientation-restrictions`, and `\overline{T} ∘ T = id`,
then a property that holds `μ`-almost everywhere holds at `\overline{T}(𝐣)` for `ν`-almost every
`𝐣 ∈ F`. The map `\overline{T}` sends `T_*(μ|_E)` to `μ|_E`. -/
theorem h1Large_ae_unCode_of_restrict {μ : Measure (ℤ → ι)} {ν : Measure (ℤ → ι × ZMod 2)}
    {T : (ℤ → ι) → ℤ → ι × ZMod 2} (hT : Measurable T) (hun : ∀ x, unCode (T x) = x)
    {E : Set (ℤ → ι)} {F : Set (ℤ → ι × ZMod 2)} (hF : MeasurableSet F) (c : ℝ≥0)
    (hres : ν.restrict F = c • (μ.restrict E).map T) {p : (ℤ → ι) → Prop}
    (hp : ∀ᵐ x ∂μ, p x) : ∀ᵐ y ∂ν, y ∈ F → p (unCode y) := by
  rw [← ae_restrict_iff' hF, hres]
  refine Measure.ae_smul_measure ?_ c
  have hmp : MeasurePreserving (unCode : (ℤ → ι × ZMod 2) → ℤ → ι) ((μ.restrict E).map T)
      (μ.restrict E) := by
    refine ⟨measurable_unCode, ?_⟩
    rw [Measure.map_map measurable_unCode hT, show unCode ∘ T = id from funext hun,
      Measure.map_id]
  exact hmp.quasiMeasurePreserving.ae (ae_restrict_of_ae hp)

variable [MeasurableSingletonClass ι] [Countable ι]

/-- Proof of `thm:overline_h1_large`, the second equality of its display: for a coding
`T ∈ {τ, ω}` and a measure `ρ` on `Σ`,
`T_*ρ(\overline{𝒫}_0^{n-1}(T(𝐢))) = ρ(𝒫_0^{n-1}(𝐢))`, because
`T⁻¹(\overline{𝒫}_0^{n-1}(T(𝐢))) = 𝒫_0^{n-1}(𝐢)` by the proof of `thm:partition_tau_conj`. -/
theorem h1Large_map_cylinder_block {o : ι → ZMod 2} {T : (ℤ → ι) → ℤ → ι × ZMod 2}
    (hT : T = tau o ∨ T = omega o) (ρ : Measure (ℤ → ι)) (x : ℤ → ι) (n : ℕ) :
    ρ.map T (cylinder (block n (T x))) = ρ (cylinder (block n x)) := by
  have hTm : Measurable T := by
    rcases hT with rfl | rfl
    exacts [measurable_tau o, measurable_omega o]
  have hpre : T ⁻¹' cylinder (block n (T x)) = cylinder (block n x) := by
    ext y
    rcases hT with rfl | rfl
    exacts [tau_mem_cylinder_block_iff o x y n, omega_mem_cylinder_block_iff o x y n]
  rw [Measure.map_apply hTm (measurableSet_cylinder _), hpre]

end Coding

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {s : ℝ}

variable {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)}

/-! ### `sec:average_gibbs_entropy` -/

/-- `thm:overline_h1_large` on one set `T(E)`, for a coding `T ∈ {τ, ω}` and a Borel set `E`:
if `\overline{μ}|_{T(E)} = c T_*(μ|_E)`, `μ_2(T(E)) = 0`, and
`\overline{μ}_𝐣^{\overline{ξ}_1} = (μ_1)_𝐣^{\overline{ξ}_1} = T_*μ_{\overline{T}(𝐣)}^{ξ_1}` for
`\overline{μ}`-almost every `𝐣 ∈ T(E)`, then
`\overline{h}_1(\overline{μ}, 𝐣) = \overline{h}_1(μ_1)` and `\overline{h}_1(μ_1) = h_1(μ)` for
`\overline{μ}`-almost every `𝐣 ∈ T(E)`. The second equality is between constants; it is obtained
at every such point, hence holds as soon as `\overline{μ}(T(E)) > 0`.
Depends on: `thm:feng_entropy_as_limit` (both parts), `eq:ergodic_entropy_constant`,
`h1Large_map_cylinder_block`. -/
theorem h1Large_aux (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (herg₁ : Ergodic (shift 1) μ₁) (hinv₂ : MeasurePreserving (shift 1) μ₂ μ₂)
    (hsupp₁ : μ₁ (subshift S.o)ᶜ = 0) (hsupp₂ : μ₂ (subshift S.o)ᶜ = 0)
    {T : (ℤ → ι) → ℤ → ι × ZMod 2} (hT : T = tau S.o ∨ T = omega S.o) {E : Set (ℤ → ι)}
    (hE : MeasurableSet E) (c : ℝ≥0)
    (hres : (avgMeasure μ₁ μ₂).restrict (T '' E) = c • (μ.restrict E).map T)
    (hnull : μ₂ (T '' E) = 0)
    (hcond : ∀ᵐ y ∂avgMeasure μ₁ μ₂, y ∈ T '' E →
      condMeas (avgMeasure μ₁ μ₂) (S.xiBar 1) y = condMeas μ₁ (S.xiBar 1) y ∧
      condMeas μ₁ (S.xiBar 1) y = (condMeas μ (S.xi μ 1) (unCode y)).map T) :
    ∀ᵐ y ∂avgMeasure μ₁ μ₂, y ∈ T '' E →
      S.dimEntropyBarAt (avgMeasure μ₁ μ₂) 1 y = S.dimEntropyBar μ₁ 1 ∧
      S.dimEntropyBar μ₁ 1 = S.dimEntropy μ 1 := by
  have := isProbabilityMeasure_avgMeasure μ₁ μ₂
  have hTm : Measurable T := by
    rcases hT with rfl | rfl
    exacts [measurable_tau S.o, measurable_omega S.o]
  have hun : ∀ x, unCode (T x) = x := by
    rcases hT with rfl | rfl
    exacts [unCode_tau, unCode_omega]
  have hF : MeasurableSet (T '' E) := by
    rcases hT with rfl | rfl
    exacts [measurableSet_tau_image S.o hE, measurableSet_omega_image S.o hE]
  have hsupp : avgMeasure μ₁ μ₂ (subshift S.o)ᶜ = 0 := by
    simp [avgMeasure, hsupp₁, hsupp₂]
  -- The entropy limits of `thm:feng_entropy_as_limit` for `\overline{μ}`, `μ_1` and `μ`; the
  -- last two are constants by `eq:ergodic_entropy_constant`.
  have l₀ := S.feng_entropy_as_limit_bar hfib hrot hprox (avgMeasure μ₁ μ₂)
    (h1Large_measurePreserving_avgMeasure herg₁.toMeasurePreserving hinv₂) hsupp 1
  have l₁ : ∀ᵐ y ∂μ₁, Tendsto
      (fun n : ℕ => -Real.log ((condMeas μ₁ (S.xiBar 1) y).real (cylinder (block n y))) / n)
      atTop (𝓝 (S.dimEntropyBar μ₁ 1)) := by
    filter_upwards [S.feng_entropy_as_limit_bar hfib hrot hprox μ₁ herg₁.toMeasurePreserving
        hsupp₁ 1, localEntropy_ae_eq μ₁ herg₁ (S.xiBar 1)] with y hy hc
    rw [dimEntropyBarAt, hc] at hy
    exact hy
  have l₂ : ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => -Real.log ((condMeas μ (S.xi μ 1) x).real (cylinder (block n x))) / n)
      atTop (𝓝 (S.dimEntropy μ 1)) := by
    filter_upwards [S.feng_entropy_as_limit hfi μ hinv herg hlt 1,
      localEntropy_ae_eq μ herg (S.xi μ 1)] with x hx hc
    rw [dimEntropyAt, hc] at hx
    exact hx
  filter_upwards [hcond, l₀, h1Large_ae_avgMeasure_of_measure_eq_zero hnull l₁,
    h1Large_ae_unCode_of_restrict hTm hun hF c hres l₂] with y hy h₀ h₁ h₂ hyF
  obtain ⟨e₁, e₂⟩ := hy hyF
  have h₁' := h₁ hyF
  have h₂' := h₂ hyF
  obtain ⟨x, -, rfl⟩ := hyF
  rw [hun] at h₂' e₂
  -- The three conditional measures give the same mass to the cylinders.
  have e₃ : ∀ n : ℕ, (condMeas μ₁ (S.xiBar 1) (T x)).real (cylinder (block n (T x))) =
      (condMeas μ (S.xi μ 1) x).real (cylinder (block n x)) := fun n => by
    rw [measureReal_def, measureReal_def, e₂, h1Large_map_cylinder_block hT]
  simp only [e₃] at h₁'
  rw [e₁] at h₀
  simp only [e₃] at h₀
  exact ⟨tendsto_nhds_unique h₀ h₁', tendsto_nhds_unique h₁' h₂'⟩

/-- `thm:overline_h1_large`: `\overline{h}_1(\overline{μ}, 𝐢) = \overline{h}_1(μ_1) =
h_1(μ)` for `\overline{μ}`-almost every `𝐢 ∈ τ(Σ^τ) ∪ ω(Σ^ω)`. Projective exponential
separation is not assumed. The equality of the constants `\overline{h}_1(μ_1)` and `h_1(μ)` uses
`\overline{μ}(τ(Σ^τ)) > 0`.
Depends on: `thm:gibbs_tau_omega_positive`, `eq:orientation-restrictions`,
`thm:conditional_two_ways`, `thm:partition_tau_conj`, `thm:feng_entropy_as_limit` (both parts),
`eq:ergodic_entropy_constant`. -/
theorem overline_h1_large (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u}) (hrot : S.WithRotations)
    (hdiag : S.HasProximalDiagonal) (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (hdec : S.GibbsDecomposition s μ μ₁ μ₂) :
    S.dimEntropyBar μ₁ 1 = S.dimEntropy μ 1 ∧
      ∀ᵐ y ∂avgMeasure μ₁ μ₂, y ∈ S.fastPart μ →
        S.dimEntropyBarAt (avgMeasure μ₁ μ₂) 1 y = S.dimEntropyBar μ₁ 1 := by
  have hlt := S.simple_lyapunov hms hrot hdiag.proximal hs0 hs2 μ hinv heq
  obtain ⟨-, ⟨z1, z2, -, -⟩, -⟩ :=
    S.gibbs_tau_omega_positive hms hfk hrot hdiag hs0 hs2 μ hinv herg heq hdec
  obtain ⟨r1, -, p1⟩ := S.orientation_restrictions hfk hrot hs0 hs2 μ hinv herg heq hdec
    (Or.inl rfl) (Or.inl rfl)
  obtain ⟨r2, -, -⟩ := S.orientation_restrictions hfk hrot hs0 hs2 μ hinv herg heq hdec
    (Or.inr rfl) (Or.inr rfl)
  have hc := S.conditional_two_ways_normalised hms hfk hrot hdiag hs0 hs2 μ hinv herg heq hdec
  have a1 := S.h1Large_aux hfi hfib hrot hdiag.proximal μ hinv herg hlt hdec.ergodic₁
    hdec.ergodic₂.toMeasurePreserving hdec.supp₁ hdec.supp₂ (Or.inl rfl)
    (S.measurableSet_SigmaTau μ) _ r1 z1 (hc.mono fun y hy => hy.1)
  have a2 := S.h1Large_aux hfi hfib hrot hdiag.proximal μ hinv herg hlt hdec.ergodic₁
    hdec.ergodic₂.toMeasurePreserving hdec.supp₁ hdec.supp₂ (Or.inr rfl)
    (S.measurableSet_SigmaOmega μ) _ r2 z2 (hc.mono fun y hy => hy.2.2.1)
  refine ⟨?_, ?_⟩
  · by_contra hne
    have h0 : ∀ᵐ y ∂avgMeasure μ₁ μ₂, y ∉ tau S.o '' S.SigmaTau μ :=
      a1.mono fun y hy hyF => hne (hy hyF).2
    exact p1.ne' (measure_eq_zero_iff_ae_notMem.2 h0)
  · filter_upwards [a1, a2] with y h1 h2 hy
    rcases hy with hy | hy
    exacts [(h1 hy).1, (h2 hy).1]

/-! ### `sec:higher_dimensional_entropies` -/

/-- `thm:eq_state_h1_large`: under projective exponential separation, if
`h_0(μ) ≥ -λ_1(𝖠, μ)`, then `h_1(μ) = h_0(μ) + λ_1(𝖠, μ)`. Here `h_0(μ)` is `entropy μ`. The
Gibbs measures are obtained inside the proof from the Gibbs bounds of `thm:irred_eq_state`,
`EquilibriumGibbsStatement`, and the decomposition of `thm:eq_state_is_sum`,
`FraserJordanJurgaDecomposition`. The two values of `dim \overline{π}_*μ_1` are those of
`eq:eq_state_h1_large1` and `eq:eq_state_h1_large2`.
Depends on: the dimension formula of Jordan–Rapaport, `JordanRapaportDimension`,
`thm:entropy_eq_gibbs`, `thm:eq_state_is_sum`, `thm:feng1` (scalar),
`dimEntropyBar_zero_eq_entropy`, `thm:overline_h1_large`. -/
theorem eq_state_h1_large (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hjr : JordanRapaportDimension.{u})
    (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u}) (hlyb : FengLedrappierYoungBar.{u})
    (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal) (hsep : S.ProjExpSeparation)
    (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (heq : S.IsEquilibriumState s μ) (hent : -S.lyapunov₁ μ ≤ entropy μ) :
    S.dimEntropy μ 1 = entropy μ + S.lyapunov₁ μ := by
  have hgibbs := hfk S hrot hs0 hs2 μ hinv heq
  obtain ⟨μ₁, μ₂, hdec⟩ := hfjj S hrot hdiag hs0 hs2 μ hinv hgibbs
  have := hdec.prob₁
  have := hdec.prob₂
  have hinv₁ := hdec.ergodic₁.toMeasurePreserving
  have hl1 := S.lyapunov₁_neg hinv
  have hne : μ₁.map S.projBar ≠ 0 := IsProbabilityMeasure.ne_zero _
  -- `eq:eq_state_h1_large1` and `eq:eq_state_h1_large2` give the same dimension.
  have hdim := (hjr S hsep μ₁ hdec.ergodic₁).unique hne
    (hlyb S hrot hdiag.proximal μ₁ hinv₁ hdec.ergodic₁ hdec.supp₁)
  rw [S.dimEntropyBar_zero_eq_entropy hrot hdiag.proximal μ₁ hinv₁ hdec.ergodic₁ hdec.supp₁,
    hdec.entropy_eq₁, ← hdec.lyapunov₁_eq,
    (S.overline_h1_large hms hfk hfi hfib hrot hdiag hs0 hs2 μ hinv herg heq hdec).1,
    min_eq_left ((le_div_iff_of_neg hl1).2 (by linarith))] at hdim
  rw [eq_div_iff hl1.ne] at hdim
  linarith

end System

end BoxLike
