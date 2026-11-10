module

/-
`thm:conditional_two_ways` of `sec:average_gibbs` by the argument of its proof: normalise on
the positive pieces, transport the conditional measures, and remove the restrictions with
`thm:conditional_measures_of_a_conditional_measure`.

Fix one of the four cases, with coding `T ∈ {τ, ω}`, set `E ∈ {Σ^τ, Σ^ω}`, planar partition
`ζ ∈ {ξ_1, ξ_1^⊥}`, `F = T(E)` and Gibbs index `k`. By `eq:orientation-restrictions` and
`thm:gibbs_tau_omega_positive`, the normalised restrictions satisfy
`\overline{μ}_F = T_*μ_E = (μ_k)_F` (`eq:normalised-orientation-restrictions`). By
`thm:partitions_xi1`, `E` and `F` are unions of atoms and `T` maps `ζ|_E` onto
`\overline{ξ}_1|_F`, so the push-forward of the conditional measures of `μ_E` is a disintegration
of `\overline{μ}_F`, and uniqueness gives
`(\overline{μ}_F)_𝐣^{\overline{ξ}_1} = ((μ_k)_F)_𝐣^{\overline{ξ}_1} = T_*(μ_E)_{T^{-1}(𝐣)}^ζ`.
Three applications of the saturated case of `thm:conditional_measures_of_a_conditional_measure`,
to `\overline{μ}` and `F`, to `μ_k` and `F`, and to `μ` and `E`, remove the restrictions.

* `cond_eq_inv_smul_of_restrict_eq_smul`, `cond_image_eq_map_cond`: a restriction proportional to
  `T_*(μ|_E)` normalises to `T_*μ_E`.
* `ae_imp_of_ae_cond`: an almost sure property for `ν_F` holds `ν`-almost everywhere on `F`.
* `condMeas_map_of_ae_mem`: the push-forward of the conditional measures of a measure carried by
  a union of atoms `E` is the conditional measure of its image, by uniqueness of the
  disintegration.
* `System.normalised_orientation_restrictions`: `eq:normalised-orientation-restrictions` and the
  observation following it.
* `System.conditional_two_ways_normalised_case`: one of the four cases.
* `System.conditional_two_ways_normalised`: `thm:conditional_two_ways`.
-/
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.GibbsOrientation
public import BoxLike.ConditionalTwoWays

@[expose] public section

namespace BoxLike

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

universe u

/-! ### Normalised restrictions -/

section Normalise

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A restriction `ν|_F = c m` with `0 < c < ∞` and `m` finite normalises to `ν_F = m(univ)⁻¹ m`:
the normalised restriction of `sec:conditional` (tex lines 1688 to 1691) removes the factor `c`. -/
theorem cond_eq_inv_smul_of_restrict_eq_smul {ν m : Measure X} [IsFiniteMeasure m] {F : Set X}
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞) (h : ν.restrict F = c • m) :
    ν[|F] = (m univ)⁻¹ • m := by
  have hF : ν F = c * m univ := by
    rw [← Measure.restrict_apply_univ, h, Measure.smul_apply, smul_eq_mul]
  rw [ProbabilityTheory.cond, h, hF, smul_smul, ENNReal.mul_inv (Or.inl hc0) (Or.inl hct),
    mul_comm c⁻¹, mul_assoc, ENNReal.inv_mul_cancel hc0 hct, mul_one]

/-- `eq:normalised-orientation-restrictions` from `eq:orientation-restrictions`: if
`ν|_{T(E)} = c T_*(μ|_E)` with `0 < c < ∞`, then `ν_{T(E)} = T_*μ_E`. -/
theorem cond_image_eq_map_cond {μ : Measure X} [IsFiniteMeasure μ] {ν : Measure Y} {T : X → Y}
    (hT : Measurable T) {E : Set X} {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (h : ν.restrict (T '' E) = c • (μ.restrict E).map T) :
    ν[|T '' E] = (μ[|E]).map T := by
  rw [cond_eq_inv_smul_of_restrict_eq_smul hc0 hct h, Measure.map_apply hT MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ, ProbabilityTheory.cond,
    Measure.map_smul _ hT.aemeasurable]

/-- An almost sure property for the normalised restriction `ν_F` of a finite measure holds
`ν`-almost everywhere on `F`. -/
theorem ae_imp_of_ae_cond {ν : Measure X} [IsFiniteMeasure ν] {F : Set X} (hF : MeasurableSet F)
    {p : X → Prop} (h : ∀ᵐ x ∂ν[|F], p x) : ∀ᵐ x ∂ν, x ∈ F → p x := by
  rw [ProbabilityTheory.cond,
    Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.2 (measure_ne_top ν F))] at h
  exact (ae_restrict_iff' hF).1 h

end Normalise

/-! ### Transport of conditional measures of a normalised restriction -/

section Transport

variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y]
  [StandardBorelSpace Y]

/-- Equal finite measures have the same conditional measures. -/
theorem condMeas_congr {μ μ' : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    (h : μ = μ') (ξ : X → Set X) : condMeas μ ξ = condMeas μ' ξ := by
  subst h
  rfl

/-- The uniqueness step in the proof of `thm:conditional_two_ways`: let `ρ` be a finite measure
carried by a Borel union `E` of atoms of `ξ`, let `T` be a Borel map with a Borel left inverse `g`
on `E` that maps the atom `ξ(x)` onto the atom `η(T(x))` for `x ∈ E`, and let `ρ' = T_*ρ`. Then
pushing forward the conditional measures of `ρ` gives a disintegration of `ρ'`, and uniqueness
gives `ρ'_y^η = T_*ρ_{g(y)}^ξ` for `ρ'`-almost every `y ∈ T(E)`. In the article `ρ = μ_E` and
`ρ' = \overline{μ}_F = (μ_k)_F`.
Depends on: `condMeas_transport` with the constant `1`. -/
theorem condMeas_map_of_ae_mem (ρ : Measure X) [IsFiniteMeasure ρ] (ρ' : Measure Y)
    [IsFiniteMeasure ρ'] {ξ : X → Set X} {η : Y → Set Y} (hξ : IsMeasurablePartition ξ)
    (hη : IsMeasurablePartition η) {T : X → Y} (hT : Measurable T) {g : Y → X}
    (hg : Measurable g) {E : Set X} (hE : MeasurableSet E) (hF : MeasurableSet (T '' E))
    (hgT : ∀ x ∈ E, g (T x) = x) (hsat : ∀ x ∈ E, ξ x ⊆ E)
    (hatom : ∀ x ∈ E, η (T x) = T '' ξ x) (hρE : ∀ᵐ x ∂ρ, x ∈ E) (hρ' : ρ' = ρ.map T) :
    ∀ᵐ y ∂ρ', y ∈ T '' E → condMeas ρ' η y = (condMeas ρ ξ (g y)).map T := by
  have hρ'F : ∀ᵐ y ∂ρ', y ∈ T '' E := by
    rw [hρ']
    exact (ae_map_iff hT.aemeasurable hF).2 (hρE.mono fun x hx => mem_image_of_mem T hx)
  refine condMeas_transport ρ ρ' hξ hη hT hg hE hgT hsat hatom (1 : ℝ≥0∞) ?_
  rw [one_smul, Measure.restrict_eq_self_of_ae_mem hρE, Measure.restrict_eq_self_of_ae_mem hρ'F,
    hρ']

end Transport

namespace System

/-! ### `thm:conditional_two_ways` -/

section AverageGibbs

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {s : ℝ}

variable {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)}

/-- `eq:normalised-orientation-restrictions` and the observation following it: for
`T ∈ {τ, ω}` and `E ∈ {Σ^τ, Σ^ω}`, `\overline{μ}_{T(E)} = T_*μ_E`, and this normalised
restriction is `(μ_1)_{T(E)}` when `μ_2(T(E)) = 0` and `(μ_2)_{T(E)}` when `μ_1(T(E)) = 0`, which
`thm:gibbs_tau_omega_positive` provides in each of the four cases.
Depends on: `eq:orientation-restrictions`, `thm:eq_state_is_sum`,
`eq:inverse-coding-restrictions`. -/
theorem normalised_orientation_restrictions (hfk : EquilibriumGibbsStatement.{u})
    (hrot : S.WithRotations) (hs0 : 0 < s) (hs2 : s < 2)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ)
    (hdec : S.GibbsDecomposition s μ μ₁ μ₂) {T : (ℤ → ι) → ℤ → ι × ZMod 2}
    (hT : T = tau S.o ∨ T = omega S.o) {E : Set (ℤ → ι)}
    (hE : E = S.SigmaTau μ ∨ E = S.SigmaOmega μ) :
    (avgMeasure μ₁ μ₂)[|T '' E] = (μ[|E]).map T ∧
      (μ₂ (T '' E) = 0 → μ₁[|T '' E] = (μ[|E]).map T) ∧
      (μ₁ (T '' E) = 0 → μ₂[|T '' E] = (μ[|E]).map T) := by
  have hTm : Measurable T := by
    rcases hT with rfl | rfl
    exacts [measurable_tau S.o, measurable_omega S.o]
  have hEm : MeasurableSet E := by
    rcases hE with rfl | rfl
    exacts [S.measurableSet_SigmaTau μ, S.measurableSet_SigmaOmega μ]
  have hres : (μ₁ + μ₂).restrict (T '' E) = (μ.restrict E).map T := by
    rcases hT with rfl | rfl
    exacts [hdec.restrict_tau_image hEm, hdec.restrict_omega_image hEm]
  have h1 := (S.orientation_restrictions hfk hrot hs0 hs2 μ hinv herg heq hdec hT hE).1
  have h2 : (2⁻¹ : ℝ≥0) • (μ.restrict E).map T = ((2⁻¹ : ℝ≥0) : ℝ≥0∞) • (μ.restrict E).map T :=
    rfl
  refine ⟨cond_image_eq_map_cond hTm (by simp) ENNReal.coe_ne_top (h1.trans h2), fun h => ?_,
    fun h => ?_⟩
  · refine cond_image_eq_map_cond hTm one_ne_zero ENNReal.one_ne_top ?_
    rw [one_smul, ← hres, Measure.restrict_add, Measure.restrict_eq_zero.2 h, add_zero]
  · refine cond_image_eq_map_cond hTm one_ne_zero ENNReal.one_ne_top ?_
    rw [one_smul, ← hres, Measure.restrict_add, Measure.restrict_eq_zero.2 h, zero_add]

/-- One of the four cases of `thm:conditional_two_ways`, as in its proof: for a coding
`T ∈ {τ, ω}`, a Borel set `E` with `μ(E) > 0` that is a union of atoms of a planar partition
`ζ` with `ζ(𝐢) = \overline{T}(\overline{ξ}_1(T(𝐢)))` on `E` (`thm:partitions_xi1`), and two
probability measures `ν`, `ν'` with `ν(T(E)) > 0`, `ν'(T(E)) > 0` and `ν_{T(E)} = T_*μ_E =
ν'_{T(E)}`, the conditional measures given `\overline{ξ}_1` satisfy
`ν_𝐣^{\overline{ξ}_1} = ν'_𝐣^{\overline{ξ}_1} = T_*μ_{\overline{T}(𝐣)}^ζ` for `ν`-almost every
`𝐣 ∈ T(E)`. The transport is applied to the normalised restrictions and the three restrictions
are removed by `thm:conditional_measures_of_a_conditional_measure`.
Depends on: `condMeas_map_of_ae_mem`, `condMeas_cond_of_saturated`. -/
theorem conditional_two_ways_normalised_case (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (ν ν' : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    {T : (ℤ → ι) → ℤ → ι × ZMod 2} (hT : T = tau S.o ∨ T = omega S.o) {E : Set (ℤ → ι)}
    (hE : MeasurableSet E) {ζ : (ℤ → ι) → Set (ℤ → ι)} (hζ : IsMeasurablePartition ζ)
    (hsat : ∀ x ∈ E, ζ x ⊆ E) (hatom : ∀ x ∈ E, ζ x = unCode '' S.xiBar 1 (T x))
    (hEpos : 0 < μ E) (hνpos : 0 < ν (T '' E)) (hν'pos : 0 < ν' (T '' E))
    (hn : ν[|T '' E] = (μ[|E]).map T) (hn' : ν'[|T '' E] = (μ[|E]).map T) :
    ∀ᵐ y ∂ν, y ∈ T '' E →
      condMeas ν (S.xiBar 1) y = condMeas ν' (S.xiBar 1) y ∧
      condMeas ν' (S.xiBar 1) y = (condMeas μ ζ (unCode y)).map T := by
  have hTm : Measurable T := by
    rcases hT with rfl | rfl
    exacts [measurable_tau S.o, measurable_omega S.o]
  have hun : ∀ x, unCode (T x) = x := by
    rcases hT with rfl | rfl
    exacts [fun x => unCode_tau x, fun x => unCode_omega x]
  have hF : MeasurableSet (T '' E) := by
    rcases hT with rfl | rfl
    exacts [measurableSet_tau_image S.o hE, measurableSet_omega_image S.o hE]
  have hxi := S.isMeasurablePartition_xiBar 1
  -- `T` maps the atoms of `ζ` in `E` onto the atoms of `\overline{ξ}_1` in `F = T(E)`.
  have hatom' : ∀ x ∈ E, S.xiBar 1 (T x) = T '' ζ x := fun x hx => by
    rw [hatom x hx, S.image_image_unCode_xiBar hT]
  have hFsat : ∀ y ∈ T '' E, S.xiBar 1 y ⊆ T '' E := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hatom' x hx]
    exact image_mono (hsat x hx)
  -- Transport for the normalised restrictions: `(ν_F)^{\overline{ξ}_1} = T_*(μ_E)^ζ`.
  have htr : ∀ᵐ y ∂ν[|T '' E], y ∈ T '' E →
      condMeas ν[|T '' E] (S.xiBar 1) y = (condMeas μ[|E] ζ (unCode y)).map T :=
    condMeas_map_of_ae_mem μ[|E] ν[|T '' E] hζ hxi hTm measurable_unCode hE hF
      (fun x _ => hun x) hsat hatom' (ae_cond_mem hE) hn
  -- The restrictions are removed by `thm:conditional_measures_of_a_conditional_measure`.
  have h1 := condMeas_cond_of_saturated ν hxi hF hνpos hFsat
  have h2 : ∀ᵐ y ∂ν, y ∈ T '' E →
      condMeas ν'[|T '' E] (S.xiBar 1) y = condMeas ν' (S.xiBar 1) y := by
    refine ae_imp_of_ae_cond hF ?_
    rw [hn, ← hn']
    filter_upwards [cond_absolutelyContinuous.ae_le
      (condMeas_cond_of_saturated ν' hxi hF hν'pos hFsat), ae_cond_mem hF] with y hy hyF
    exact hy hyF
  have h3 : ∀ᵐ y ∂ν, y ∈ T '' E →
      (unCode y ∈ E → condMeas μ[|E] ζ (unCode y) = condMeas μ ζ (unCode y)) := by
    refine ae_imp_of_ae_cond hF ?_
    have hmap : ((μ[|E]).map T).map unCode = μ[|E] := by
      have hid : unCode ∘ T = id := funext hun
      rw [Measure.map_map measurable_unCode hTm, hid, Measure.map_id]
    rw [hn]
    refine ae_of_ae_map (p := fun x => x ∈ E → condMeas μ[|E] ζ x = condMeas μ ζ x)
      measurable_unCode.aemeasurable ?_
    rw [hmap]
    exact cond_absolutelyContinuous.ae_le (condMeas_cond_of_saturated μ hζ hE hEpos hsat)
  have htr' := ae_imp_of_ae_cond hF htr
  have hνν' : condMeas ν[|T '' E] (S.xiBar 1) = condMeas ν'[|T '' E] (S.xiBar 1) :=
    condMeas_congr (hn.trans hn'.symm) _
  filter_upwards [htr', h1, h2, h3] with y ht h1 h2 h3 hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hux : unCode (T x) ∈ E := (hun x).symm ▸ hx
  have e1 : condMeas ν (S.xiBar 1) (T x) = condMeas ν' (S.xiBar 1) (T x) := by
    rw [← h1 (mem_image_of_mem T hx), ← h2 (mem_image_of_mem T hx), hνν']
  refine ⟨e1, ?_⟩
  rw [← e1, ← h1 (mem_image_of_mem T hx), ht (mem_image_of_mem T hx) (mem_image_of_mem T hx),
    h3 (mem_image_of_mem T hx) hux]

/-- `thm:conditional_two_ways`: for `\overline{μ}`-almost every `𝐣 ∈ Σ_Z`, the conditional
measure `\overline{μ}_𝐣^{\overline{ξ}_1}` equals `(μ_1)_𝐣^{\overline{ξ}_1} = τ_*μ^{ξ_1}` on
`τ(Σ^τ)`, `(μ_2)_𝐣^{\overline{ξ}_1} = ω_*μ^{ξ_1^⊥}` on `ω(Σ^τ)`,
`(μ_1)_𝐣^{\overline{ξ}_1} = ω_*μ^{ξ_1}` on `ω(Σ^ω)` and
`(μ_2)_𝐣^{\overline{ξ}_1} = τ_*μ^{ξ_1^⊥}` on `τ(Σ^ω)`, the planar conditional measures being taken
at `\overline{τ}(𝐣)`, respectively `\overline{ω}(𝐣)`, which is `unCode 𝐣`. The statement is that
of `conditional_two_ways`. In each case the normalised restrictions agree,
`\overline{μ}_F = T_*μ_E = (μ_k)_F`, the conditional measures of `μ_E` are transported to those
of `\overline{μ}_F`, and the restrictions are removed by
`thm:conditional_measures_of_a_conditional_measure`.
Depends on: `eq:normalised-orientation-restrictions`, `thm:gibbs_tau_omega_positive`,
`thm:sigma_tau_omega_positive_eq_measure`, `thm:partitions_xi1`,
`thm:conditional_measures_of_a_conditional_measure`, `condMeas_unique`. -/
theorem conditional_two_ways_normalised (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal)
    (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (heq : S.IsEquilibriumState s μ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hdec : S.GibbsDecomposition s μ μ₁ μ₂) :
    ∀ᵐ y ∂avgMeasure μ₁ μ₂,
      (y ∈ tau S.o '' S.SigmaTau μ →
        condMeas (avgMeasure μ₁ μ₂) (S.xiBar 1) y = condMeas μ₁ (S.xiBar 1) y ∧
        condMeas μ₁ (S.xiBar 1) y = (condMeas μ (S.xi μ 1) (unCode y)).map (tau S.o)) ∧
      (y ∈ omega S.o '' S.SigmaTau μ →
        condMeas (avgMeasure μ₁ μ₂) (S.xiBar 1) y = condMeas μ₂ (S.xiBar 1) y ∧
        condMeas μ₂ (S.xiBar 1) y = (condMeas μ (S.xiPerp μ) (unCode y)).map (omega S.o)) ∧
      (y ∈ omega S.o '' S.SigmaOmega μ →
        condMeas (avgMeasure μ₁ μ₂) (S.xiBar 1) y = condMeas μ₁ (S.xiBar 1) y ∧
        condMeas μ₁ (S.xiBar 1) y = (condMeas μ (S.xi μ 1) (unCode y)).map (omega S.o)) ∧
      (y ∈ tau S.o '' S.SigmaOmega μ →
        condMeas (avgMeasure μ₁ μ₂) (S.xiBar 1) y = condMeas μ₂ (S.xiBar 1) y ∧
        condMeas μ₂ (S.xiBar 1) y = (condMeas μ (S.xiPerp μ) (unCode y)).map (tau S.o)) := by
  have := isProbabilityMeasure_avgMeasure μ₁ μ₂
  have hlt := S.simple_lyapunov hms hrot hdiag.proximal hs0 hs2 μ hinv heq
  have hmτ := S.measurableSet_SigmaTau μ
  have hmω := S.measurableSet_SigmaOmega μ
  -- `μ(Σ^τ) > 0` and `μ(Σ^ω) > 0`: `thm:sigma_tau_omega_positive_eq_measure`.
  obtain ⟨pτ, pω⟩ :=
    S.sigma_tau_omega_positive_eq_measure hfk hrot hs0 hs2 μ hinv herg heq
  -- The zero and positive terms of `thm:gibbs_tau_omega_positive`.
  obtain ⟨-, ⟨z1, z2, z3, z4⟩, ⟨q1, q2, q3, q4⟩⟩ :=
    S.gibbs_tau_omega_positive hms hfk hrot hdiag hs0 hs2 μ hinv herg heq hdec
  -- `\overline{μ}(T(E)) = ½ μ(E) > 0`: `eq:orientation-restrictions`.
  have hpos := fun {T : (ℤ → ι) → ℤ → ι × ZMod 2} (hT : T = tau S.o ∨ T = omega S.o)
      {E : Set (ℤ → ι)} (hE : E = S.SigmaTau μ ∨ E = S.SigmaOmega μ) =>
    (S.orientation_restrictions hfk hrot hs0 hs2 μ hinv herg heq hdec hT hE).2.2
  -- `\overline{μ}_{T(E)} = T_*μ_E = (μ_k)_{T(E)}`: `eq:normalised-orientation-restrictions`.
  have hnor := fun {T : (ℤ → ι) → ℤ → ι × ZMod 2} (hT : T = tau S.o ∨ T = omega S.o)
      {E : Set (ℤ → ι)} (hE : E = S.SigmaTau μ ∨ E = S.SigmaOmega μ) =>
    S.normalised_orientation_restrictions hfk hrot hs0 hs2 μ hinv herg heq hdec hT hE
  have c1 := S.conditional_two_ways_normalised_case μ (avgMeasure μ₁ μ₂) μ₁ (Or.inl rfl) hmτ
    (S.isMeasurablePartition_xi μ 1) (fun x hx => (S.xi_one_of_mem_SigmaTau μ hx).2)
    (fun x hx => (S.xi_one_of_mem_SigmaTau μ hx).1) pτ (hpos (Or.inl rfl) (Or.inl rfl)) q1
    (hnor (Or.inl rfl) (Or.inl rfl)).1 ((hnor (Or.inl rfl) (Or.inl rfl)).2.1 z1)
  have c2 := S.conditional_two_ways_normalised_case μ (avgMeasure μ₁ μ₂) μ₂ (Or.inr rfl) hmτ
    (S.isMeasurablePartition_xiPerp μ) (fun x hx => (S.xiPerp_of_mem_SigmaTau μ hx).2)
    (fun x hx => (S.xiPerp_of_mem_SigmaTau μ hx).1) pτ (hpos (Or.inr rfl) (Or.inl rfl)) q3
    (hnor (Or.inr rfl) (Or.inl rfl)).1 ((hnor (Or.inr rfl) (Or.inl rfl)).2.2 z3)
  have c3 := S.conditional_two_ways_normalised_case μ (avgMeasure μ₁ μ₂) μ₁ (Or.inr rfl) hmω
    (S.isMeasurablePartition_xi μ 1) (fun x hx => (S.xi_one_of_mem_SigmaOmega μ hlt hx).2)
    (fun x hx => (S.xi_one_of_mem_SigmaOmega μ hlt hx).1) pω (hpos (Or.inr rfl) (Or.inr rfl))
    q2 (hnor (Or.inr rfl) (Or.inr rfl)).1 ((hnor (Or.inr rfl) (Or.inr rfl)).2.1 z2)
  have c4 := S.conditional_two_ways_normalised_case μ (avgMeasure μ₁ μ₂) μ₂ (Or.inl rfl) hmω
    (S.isMeasurablePartition_xiPerp μ) (fun x hx => (S.xiPerp_of_mem_SigmaOmega μ hlt hx).2)
    (fun x hx => (S.xiPerp_of_mem_SigmaOmega μ hlt hx).1) pω (hpos (Or.inl rfl) (Or.inr rfl))
    q4 (hnor (Or.inl rfl) (Or.inr rfl)).1 ((hnor (Or.inl rfl) (Or.inr rfl)).2.2 z4)
  filter_upwards [c1, c2, c3, c4] with y h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end AverageGibbs

end System

end BoxLike
