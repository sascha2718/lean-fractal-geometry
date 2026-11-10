module

/-
The two Gibbs measures on the four sets `τ(Σ^τ)`, `ω(Σ^ω)`, `ω(Σ^τ)`, `τ(Σ^ω)` of
`sec:average_gibbs`: `thm:gibbs_tau_omega_positive` and `eq:orientation-restrictions`.

For a coding `T ∈ {τ, ω}` and a Borel set `E ⊆ Σ` the image `T(E)` is the Borel set
`T(Σ) ∩ q⁻¹(E)`, where `q` forgets the axis. The decomposition
`μ = \overline{T}_*μ_1 + \overline{T}_*μ_2` of `thm:eq_state_is_sum` and
`eq:inverse-coding-restrictions` give `(μ_1 + μ_2)|_{T(E)} = T_*(μ|_E)`. The backward rate of
`eq:lyapunov_exponent_gsystem` is `λ_1(𝖠, μ)` almost everywhere for `μ_1` and `λ_2(𝖠, μ)` almost
everywhere for `μ_2`, and on the four sets it is `λ_1`, `λ_1`, `λ_2`, `λ_2` by definition of
`Σ^τ` and `Σ^ω`; since `λ_2 < λ_1`, this separates the supports.

* `tau_image_eq`, `omega_image_eq`, `measurableSet_tau_image`, `measurableSet_omega_image`: the
  images `τ(E)` and `ω(E)` of a Borel set are Borel.
* `restrict_image_eq_map_restrict`: `ν|_{T(E)} = T_*((\overline{T}_*ν)|_E)`, from
  `eq:inverse-coding-restrictions`.
* `System.GibbsDecomposition.restrict_tau_image`,
  `System.GibbsDecomposition.restrict_omega_image`, `System.GibbsDecomposition.measure_tau_image`,
  `System.GibbsDecomposition.measure_omega_image`: `(μ_1 + μ_2)|_{T(E)} = T_*(μ|_E)` and
  `μ(E) = μ_1(T(E)) + μ_2(T(E))`.
* `System.gibbs_tau_omega_positive`: `thm:gibbs_tau_omega_positive`.
* `System.orientation_restrictions`: `eq:orientation-restrictions`.
-/
public import BoxLike.Aligned.SigmaTauOmega
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.SigmaMeasure

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

universe u

/-! ### Images of Borel sets under the codings -/

section Image

variable {ι : Type u}

/-- `τ(E) = τ(Σ) ∩ q⁻¹(E)`, where `q` forgets the axis (`sec:subshift`). -/
theorem tau_image_eq (o : ι → ZMod 2) (E : Set (ℤ → ι)) :
    tau o '' E = range (tau o) ∩ unCode ⁻¹' E := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨mem_range_self x, by simpa using hx⟩
  · rintro ⟨⟨x, rfl⟩, hx⟩
    exact ⟨x, by simpa using hx, rfl⟩

/-- `ω(E) = ω(Σ) ∩ q⁻¹(E)`, where `q` forgets the axis (`sec:subshift`). -/
theorem omega_image_eq (o : ι → ZMod 2) (E : Set (ℤ → ι)) :
    omega o '' E = range (omega o) ∩ unCode ⁻¹' E := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨mem_range_self x, by simpa using hx⟩
  · rintro ⟨⟨x, rfl⟩, hx⟩
    exact ⟨x, by simpa using hx, rfl⟩

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The image `τ(E)` of a Borel set is Borel. -/
theorem measurableSet_tau_image (o : ι → ZMod 2) {E : Set (ℤ → ι)} (hE : MeasurableSet E) :
    MeasurableSet (tau o '' E) := by
  rw [tau_image_eq]
  exact (measurableSet_range_tau o).inter (measurable_unCode hE)

/-- The image `ω(E)` of a Borel set is Borel. -/
theorem measurableSet_omega_image (o : ι → ZMod 2) {E : Set (ℤ → ι)} (hE : MeasurableSet E) :
    MeasurableSet (omega o '' E) := by
  rw [omega_image_eq]
  exact (measurableSet_range_omega o).inter (measurable_unCode hE)

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- `eq:inverse-coding-restrictions` on a Borel set `E`: for a coding `κ` with
`κ ∘ \overline{κ} = id` on `R = κ(Σ)` and `κ(E) = R ∩ q⁻¹(E)`, the restriction of `ν` to `κ(E)` is
the push-forward under `κ` of the restriction to `E` of `\overline{κ}_*ν`. -/
theorem restrict_image_eq_map_restrict {κ : (ℤ → ι) → ℤ → ι × ZMod 2} (hκ : Measurable κ)
    {R : Set (ℤ → ι × ZMod 2)} (hRm : MeasurableSet R) (hR : ∀ y ∈ R, κ (unCode y) = y)
    {E : Set (ℤ → ι)} (hE : MeasurableSet E) (himage : κ '' E = R ∩ unCode ⁻¹' E)
    (ν : Measure (ℤ → ι × ZMod 2)) :
    (((ν.restrict R).map unCode).restrict E).map κ = ν.restrict (κ '' E) := by
  have hEm : MeasurableSet (unCode ⁻¹' E : Set (ℤ → ι × ZMod 2)) := measurable_unCode hE
  rw [Measure.restrict_map measurable_unCode hE, Measure.restrict_restrict hEm,
    Measure.map_map hκ measurable_unCode, himage, inter_comm R]
  conv_rhs => rw [← Measure.map_id (μ := ν.restrict (unCode ⁻¹' E ∩ R))]
  refine Measure.map_congr ?_
  filter_upwards [ae_restrict_mem (hEm.inter hRm)] with y hy
  exact hR y hy.2

end Image

namespace System

/-! ### The decomposition of `thm:eq_state_is_sum` on the images -/

section Decomposition

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {S : System ι} {s : ℝ} {μ : Measure (ℤ → ι)} {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)}

/-- `(μ_1 + μ_2)|_{τ(E)} = τ_*(μ|_E)` for a Borel set `E`, by `thm:eq_state_is_sum` and
`eq:inverse-coding-restrictions`. This is `eq:orientation-restrictions` for `T = τ` before the
factor `½`. -/
theorem GibbsDecomposition.restrict_tau_image (hdec : S.GibbsDecomposition s μ μ₁ μ₂)
    {E : Set (ℤ → ι)} (hE : MeasurableSet E) :
    (μ₁ + μ₂).restrict (tau S.o '' E) = (μ.restrict E).map (tau S.o) := by
  have hR : ∀ y ∈ range (tau S.o), tau S.o (unCode y) = y := by rintro _ ⟨x, rfl⟩; rfl
  have h := fun ν => restrict_image_eq_map_restrict (measurable_tau S.o)
    (measurableSet_range_tau S.o) hR hE (tau_image_eq S.o E) ν
  rw [Measure.restrict_add, ← h μ₁, ← h μ₂, ← Measure.map_add _ _ (measurable_tau S.o),
    ← Measure.restrict_add, ← hdec.eq_tau]

/-- `(μ_1 + μ_2)|_{ω(E)} = ω_*(μ|_E)` for a Borel set `E`, by `thm:eq_state_is_sum` and
`eq:inverse-coding-restrictions`. This is `eq:orientation-restrictions` for `T = ω` before the
factor `½`. -/
theorem GibbsDecomposition.restrict_omega_image (hdec : S.GibbsDecomposition s μ μ₁ μ₂)
    {E : Set (ℤ → ι)} (hE : MeasurableSet E) :
    (μ₁ + μ₂).restrict (omega S.o '' E) = (μ.restrict E).map (omega S.o) := by
  have hR : ∀ y ∈ range (omega S.o), omega S.o (unCode y) = y := by rintro _ ⟨x, rfl⟩; rfl
  have h := fun ν => restrict_image_eq_map_restrict (measurable_omega S.o)
    (measurableSet_range_omega S.o) hR hE (omega_image_eq S.o E) ν
  rw [Measure.restrict_add, ← h μ₁, ← h μ₂, ← Measure.map_add _ _ (measurable_omega S.o),
    ← Measure.restrict_add, ← hdec.eq_omega]

/-- `μ(E) = μ_1(τ(E)) + μ_2(τ(E))` for a Borel set `E`, by `thm:eq_state_is_sum`. -/
theorem GibbsDecomposition.measure_tau_image (hdec : S.GibbsDecomposition s μ μ₁ μ₂)
    {E : Set (ℤ → ι)} (hE : MeasurableSet E) :
    μ E = μ₁ (tau S.o '' E) + μ₂ (tau S.o '' E) := by
  have h := congrArg (fun m : Measure (ℤ → ι × ZMod 2) => m univ) (hdec.restrict_tau_image hE)
  simp only [Measure.restrict_apply_univ, Measure.add_apply,
    Measure.map_apply (measurable_tau S.o) MeasurableSet.univ, preimage_univ] at h
  exact h.symm

/-- `μ(E) = μ_1(ω(E)) + μ_2(ω(E))` for a Borel set `E`, by `thm:eq_state_is_sum`. -/
theorem GibbsDecomposition.measure_omega_image (hdec : S.GibbsDecomposition s μ μ₁ μ₂)
    {E : Set (ℤ → ι)} (hE : MeasurableSet E) :
    μ E = μ₁ (omega S.o '' E) + μ₂ (omega S.o '' E) := by
  have h := congrArg (fun m : Measure (ℤ → ι × ZMod 2) => m univ)
    (hdec.restrict_omega_image hE)
  simp only [Measure.restrict_apply_univ, Measure.add_apply,
    Measure.map_apply (measurable_omega S.o) MeasurableSet.univ, preimage_univ] at h
  exact h.symm

end Decomposition

/-! ### Separation of the supports by the backward rate -/

section Rates

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι)

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- Proof of `thm:gibbs_tau_omega_positive`: if the backward rate of
`eq:lyapunov_exponent_gsystem` is `l` for `ν`-almost every point, then a set on which it is
`l' ≠ l` is `ν`-null, by uniqueness of limits. -/
theorem measure_eq_zero_of_hasBackRate {ν : Measure (ℤ → ι × ZMod 2)} {l l' : ℝ} (hne : l ≠ l')
    (hrate : ∀ᵐ y ∂ν, S.HasBackRate y l) {A : Set (ℤ → ι × ZMod 2)}
    (hA : ∀ y ∈ A, S.HasBackRate y l') : ν A = 0 :=
  measure_mono_null (fun y hy hy' => hne (tendsto_nhds_unique hy' (hA y hy))) (ae_iff.1 hrate)

/-- Proof of `thm:gibbs_tau_omega_positive`, first claim: let `ν` be a probability measure
carried by `Σ_Z` with `q_*ν = μ` along which the backward rate is `l` almost everywhere. If `P`
and `Q` are Borel sets covering `μ`-almost all of `Σ`, the rate along `τ(𝐢)` is `l' ≠ l` on `Q`,
and the rate along `ω(𝐢)` is `l'` on `P`, then `ν(τ(P)) + ν(ω(Q)) = 1`, by
`eq:tau_omega_partition`. -/
theorem measure_tau_image_add_measure_omega_image {μ : Measure (ℤ → ι)}
    {ν : Measure (ℤ → ι × ZMod 2)} [IsProbabilityMeasure ν] (hsupp : ν (subshift S.o)ᶜ = 0)
    (hmap : ν.map unCode = μ) {P Q : Set (ℤ → ι)} (hP : MeasurableSet P) (hQ : MeasurableSet Q)
    (hfull : μ (P ∪ Q)ᶜ = 0) {l l' : ℝ} (hne : l ≠ l') (hrate : ∀ᵐ y ∂ν, S.HasBackRate y l)
    (hQτ : ∀ x ∈ Q, S.HasBackRate (tau S.o x) l')
    (hPω : ∀ x ∈ P, S.HasBackRate (omega S.o x) l') :
    ν (tau S.o '' P) + ν (omega S.o '' Q) = 1 := by
  have hdisj : Disjoint (tau S.o '' P) (omega S.o '' Q) :=
    disjoint_range_tau_range_omega.mono (image_subset_range _ _) (image_subset_range _ _)
  have hmem : ∀ᵐ y ∂ν, y ∈ subshift S.o := hsupp
  have hcover : ∀ᵐ y ∂ν, unCode y ∈ P ∪ Q := by
    refine ae_of_ae_map measurable_unCode.aemeasurable ?_
    rw [hmap]
    exact hfull
  rw [← measure_union hdisj (measurableSet_omega_image S.o hQ),
    ← prob_compl_eq_zero_iff ((measurableSet_tau_image S.o hP).union
      (measurableSet_omega_image S.o hQ))]
  change ∀ᵐ y ∂ν, y ∈ tau S.o '' P ∪ omega S.o '' Q
  filter_upwards [hmem, hcover, hrate] with y hy hPQ hl
  rw [← range_tau_union_range_omega] at hy
  rcases hy with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · rcases hPQ with hx | hx
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact absurd (tendsto_nhds_unique hl (hQτ x hx)) hne
  · rcases hPQ with hx | hx
    · exact absurd (tendsto_nhds_unique hl (hPω x hx)) hne
    · exact Or.inr ⟨x, hx, rfl⟩

end Rates

/-! ### `thm:gibbs_tau_omega_positive` and `eq:orientation-restrictions` -/

section AverageGibbs

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {s : ℝ}

variable {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)}

/-- `thm:gibbs_tau_omega_positive`: `μ_1` is carried by `τ(Σ^τ) ∪ ω(Σ^ω)` and `μ_2` by
`ω(Σ^τ) ∪ τ(Σ^ω)`, the four cross terms vanish, and the four summands are positive. The sets
`Σ^τ`, `Σ^ω` are those of the equilibrium state `μ`, and `μ_1`, `μ_2` enter through the
conclusion `hdec` of `thm:eq_state_is_sum`.
Depends on: `thm:eq_state_is_sum`, `eq:lyapunov_exponent_gsystem`,
`thm:lyapunov_exponents_via_g_system`, `eq:simple_lyapunov`, `measure_SigmaPrime_compl`,
`eq:tau_omega_partition`, `eq:tau_omega_partition2`,
`thm:sigma_tau_omega_positive_eq_measure`. -/
theorem gibbs_tau_omega_positive (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u})
    (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal) (hs0 : 0 < s) (hs2 : s < 2)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (heq : S.IsEquilibriumState s μ) (hdec : S.GibbsDecomposition s μ μ₁ μ₂) :
    (μ₁ (tau S.o '' S.SigmaTau μ) + μ₁ (omega S.o '' S.SigmaOmega μ) = 1 ∧
      μ₂ (omega S.o '' S.SigmaTau μ) + μ₂ (tau S.o '' S.SigmaOmega μ) = 1) ∧
    (μ₂ (tau S.o '' S.SigmaTau μ) = 0 ∧ μ₂ (omega S.o '' S.SigmaOmega μ) = 0 ∧
      μ₁ (omega S.o '' S.SigmaTau μ) = 0 ∧ μ₁ (tau S.o '' S.SigmaOmega μ) = 0) ∧
    (0 < μ₁ (tau S.o '' S.SigmaTau μ) ∧ 0 < μ₁ (omega S.o '' S.SigmaOmega μ) ∧
      0 < μ₂ (omega S.o '' S.SigmaTau μ) ∧ 0 < μ₂ (tau S.o '' S.SigmaOmega μ)) := by
  have := hdec.prob₁
  have := hdec.prob₂
  have hlt := S.simple_lyapunov hms hrot hdiag.proximal hs0 hs2 μ hinv heq
  -- The backward rate is `λ_1` almost everywhere for `μ_1` and `λ_2` for `μ_2`.
  have hr₁ : ∀ᵐ y ∂μ₁, S.HasBackRate y (S.lyapunov₁ μ) := by
    rw [hdec.lyapunov₁_eq]
    exact S.lyapunov_exponent_gsystem μ₁ hdec.ergodic₁
  have hr₂ : ∀ᵐ y ∂μ₂, S.HasBackRate y (S.lyapunov₂ μ) := by
    rw [hdec.lyapunov₂_eq]
    exact S.lyapunov_exponent_gsystem μ₂ hdec.ergodic₂
  have hmτ := S.measurableSet_SigmaTau μ
  have hmω := S.measurableSet_SigmaOmega μ
  have hfull : μ (S.SigmaTau μ ∪ S.SigmaOmega μ)ᶜ = 0 := S.measure_SigmaPrime_compl μ hinv herg
  -- The four cross terms vanish, by `thm:lyapunov_exponents_via_g_system`.
  have z1 : μ₂ (tau S.o '' S.SigmaTau μ) = 0 :=
    S.measure_eq_zero_of_hasBackRate hlt.ne hr₂ (by rintro _ ⟨x, hx, rfl⟩; exact hx.1)
  have z2 : μ₂ (omega S.o '' S.SigmaOmega μ) = 0 :=
    S.measure_eq_zero_of_hasBackRate hlt.ne hr₂ (by rintro _ ⟨x, hx, rfl⟩; exact hx.2)
  have z3 : μ₁ (omega S.o '' S.SigmaTau μ) = 0 :=
    S.measure_eq_zero_of_hasBackRate hlt.ne' hr₁ (by rintro _ ⟨x, hx, rfl⟩; exact hx.2)
  have z4 : μ₁ (tau S.o '' S.SigmaOmega μ) = 0 :=
    S.measure_eq_zero_of_hasBackRate hlt.ne' hr₁ (by rintro _ ⟨x, hx, rfl⟩; exact hx.1)
  obtain ⟨pτ, pω⟩ := S.sigma_tau_omega_positive_eq_measure hfk hrot hs0 hs2 μ hinv herg heq
  refine ⟨⟨?_, ?_⟩, ⟨z1, z2, z3, z4⟩, ?_, ?_, ?_, ?_⟩
  · exact S.measure_tau_image_add_measure_omega_image hdec.supp₁
      (map_unCode_of_decomposition hdec.supp₁ hdec.eq₁) hmτ hmω hfull hlt.ne' hr₁
      (fun x hx => hx.1) (fun x hx => hx.2)
  · rw [add_comm]
    refine S.measure_tau_image_add_measure_omega_image hdec.supp₂
      (map_unCode_of_decomposition hdec.supp₂ hdec.eq₂) hmω hmτ ?_ hlt.ne hr₂
      (fun x hx => hx.1) (fun x hx => hx.2)
    rwa [union_comm]
  · have h := hdec.measure_tau_image hmτ
    rw [z1, add_zero] at h
    rwa [← h]
  · have h := hdec.measure_omega_image hmω
    rw [z2, add_zero] at h
    rwa [← h]
  · have h := hdec.measure_omega_image hmτ
    rw [z3, zero_add] at h
    rwa [← h]
  · have h := hdec.measure_tau_image hmω
    rw [z4, zero_add] at h
    rwa [← h]

/-- `eq:orientation-restrictions`: for `T ∈ {τ, ω}` and `E ∈ {Σ^τ, Σ^ω}`,
`\overline{μ}|_{T(E)} = ½ T_*(μ|_E)` and `\overline{μ}(T(E)) = ½ μ(E) > 0`.
Depends on: `thm:eq_state_is_sum`, `eq:inverse-coding-restrictions`,
`thm:gibbs_tau_omega_positive`, `thm:sigma_tau_omega_positive_eq_measure`. -/
theorem orientation_restrictions (hfk : EquilibriumGibbsStatement.{u}) (hrot : S.WithRotations)
    (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (heq : S.IsEquilibriumState s μ) (hdec : S.GibbsDecomposition s μ μ₁ μ₂)
    {T : (ℤ → ι) → ℤ → ι × ZMod 2} (hT : T = tau S.o ∨ T = omega S.o) {E : Set (ℤ → ι)}
    (hE : E = S.SigmaTau μ ∨ E = S.SigmaOmega μ) :
    (avgMeasure μ₁ μ₂).restrict (T '' E) = (2⁻¹ : ℝ≥0) • (μ.restrict E).map T ∧
      avgMeasure μ₁ μ₂ (T '' E) = 2⁻¹ * μ E ∧ 0 < avgMeasure μ₁ μ₂ (T '' E) := by
  obtain ⟨pτ, pω⟩ := S.sigma_tau_omega_positive_eq_measure hfk hrot hs0 hs2 μ hinv herg heq
  have hEm : MeasurableSet E := by
    rcases hE with rfl | rfl
    exacts [S.measurableSet_SigmaTau μ, S.measurableSet_SigmaOmega μ]
  have hEpos : 0 < μ E := by
    rcases hE with rfl | rfl
    exacts [pτ, pω]
  have hTm : Measurable T := by
    rcases hT with rfl | rfl
    exacts [measurable_tau S.o, measurable_omega S.o]
  have hres : (μ₁ + μ₂).restrict (T '' E) = (μ.restrict E).map T := by
    rcases hT with rfl | rfl
    exacts [hdec.restrict_tau_image hEm, hdec.restrict_omega_image hEm]
  have h1 : (avgMeasure μ₁ μ₂).restrict (T '' E) = (2⁻¹ : ℝ≥0) • (μ.restrict E).map T := by
    rw [avgMeasure, Measure.restrict_smul, hres]
  have h2 : avgMeasure μ₁ μ₂ (T '' E) = 2⁻¹ * μ E := by
    have h := congrArg (fun m : Measure (ℤ → ι × ZMod 2) => m univ) h1
    simp only [Measure.restrict_apply_univ, Measure.smul_apply,
      Measure.map_apply hTm MeasurableSet.univ, preimage_univ] at h
    rw [h, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_inv two_ne_zero, ENNReal.coe_ofNat]
  refine ⟨h1, h2, ?_⟩
  rw [h2]
  exact ENNReal.mul_pos (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top) hEpos.ne'

end AverageGibbs

end System

end BoxLike
