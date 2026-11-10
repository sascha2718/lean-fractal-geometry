module

/-
The dimension of the coordinate projections of the equilibrium state, for a tuple containing a
proximal diagonal generator: `sec:entropy_eq_state` and the decomposition of
`sec:dimension_of_projections`. `General.lean` removes the normalisation and proves
`thm:eq_state_proj_dim` and `thm:main1`.

* `measurableSet_range_tau`, `measurableSet_range_omega`: `τ(Σ)` and `ω(Σ)` are Borel.
* `map_unCode_of_decomposition`: `q_*μ_k = μ` in the proof of `thm:entropy_eq_gibbs`.
* `System.GibbsDecomposition.entropy_eq₁`, `System.GibbsDecomposition.entropy_eq₂`:
  `thm:entropy_eq_gibbs`.
* `System.marginal_decomposition_normalised`: `eq:proj_eq_is_sum`,
  `eq:restricted-projection-dimensions` and `eq:gibbs_proj_dim`.
-/
public import BoxLike.EntropyFactor
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.Literature

@[expose] public section

namespace BoxLike

open MeasureTheory Set

universe u

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- `τ(Σ) = ⋃_{i ≤ N} [i]` is a Borel subset of `Σ_Z`. -/
theorem measurableSet_range_tau (o : ι → ZMod 2) : MeasurableSet (range (tau o)) := by
  have h2 : MeasurableSet {y : ℤ → ι × ZMod 2 | (y 0).2 = 0} :=
    (measurable_snd.comp (measurable_pi_apply 0)) (measurableSet_singleton (0 : ZMod 2))
  rw [range_tau]
  exact (measurableSet_subshift o).inter h2

/-- `ω(Σ) = ⋃_{i > N} [i]` is a Borel subset of `Σ_Z`. -/
theorem measurableSet_range_omega (o : ι → ZMod 2) : MeasurableSet (range (omega o)) := by
  have h2 : MeasurableSet {y : ℤ → ι × ZMod 2 | (y 0).2 = 1} :=
    (measurable_snd.comp (measurable_pi_apply 0)) (measurableSet_singleton (1 : ZMod 2))
  rw [range_omega]
  exact (measurableSet_subshift o).inter h2

/-- `q_*ν = \overline{τ}_*ν + \overline{ω}_*ν` for a measure `ν` carried by `Σ_Z`, the first
step of the proof of `thm:entropy_eq_gibbs`. -/
theorem map_unCode_of_decomposition {o : ι → ZMod 2} {μ : Measure (ℤ → ι)}
    {ν : Measure (ℤ → ι × ZMod 2)} (hν : ν (subshift o)ᶜ = 0)
    (h : μ = (ν.restrict (range (tau o))).map unCode +
      (ν.restrict (range (omega o))).map unCode) : ν.map unCode = μ := by
  have hmem : ∀ᵐ y ∂ν, y ∈ subshift o := hν
  have hunion : ν.restrict (range (tau o)) + ν.restrict (range (omega o)) = ν := by
    rw [← Measure.restrict_union disjoint_range_tau_range_omega (measurableSet_range_omega o),
      range_tau_union_range_omega]
    exact Measure.restrict_eq_self_of_ae_mem hmem
  rw [h, ← Measure.map_add _ _ measurable_unCode, hunion]

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- Transport of a restricted measure through a coding `κ` with `κ ∘ \overline{κ} = id` on
`R = κ(Σ)`, as in `eq:inverse-coding-restrictions`. -/
theorem map_comp_coding {κ : (ℤ → ι) → ℤ → ι × ZMod 2} (hκ : Measurable κ)
    {R : Set (ℤ → ι × ZMod 2)} (hRm : MeasurableSet R) (hR : ∀ y ∈ R, κ (unCode y) = y)
    {f : (ℤ → ι × ZMod 2) → ℝ} (hf : Measurable f) (ν : Measure (ℤ → ι × ZMod 2)) :
    ((ν.restrict R).map unCode).map (f ∘ κ) = (ν.restrict R).map f := by
  rw [Measure.map_map (hf.comp hκ) measurable_unCode]
  refine Measure.map_congr ?_
  filter_upwards [ae_restrict_mem hRm] with y hy
  simp [hR y hy]

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- A Gibbs measure carried by `Σ_Z` charges `τ(Σ)`. -/
theorem IsGibbs.measure_range_tau_pos [Nonempty ι] {o : ι → ZMod 2} {φ : ι × ZMod 2 → ℝ}
    {ν : Measure (ℤ → ι × ZMod 2)} (h : IsGibbs o φ ν) (hν : ν (subshift o)ᶜ = 0) :
    0 < ν (range (tau o)) := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hpos := h.measureReal_cylinder_pos (tau_mem_subshift fun _ => i) one_pos
  have hpos' : 0 < ν (cylinder fun k : Fin 1 => tau o (fun _ => i) k) := by
    rw [measureReal_def] at hpos
    exact (ENNReal.toReal_pos_iff.1 hpos).1
  have hsub : (cylinder fun k : Fin 1 => tau o (fun _ => i) k) ∩ subshift o ⊆
      range (tau o) := by
    rintro y ⟨hy, hys⟩
    rw [range_tau]
    refine ⟨hys, ?_⟩
    have h0 := hy 0
    simp only [Fin.val_zero, Nat.cast_zero, tau_apply, eps_zero] at h0
    rw [h0]
  calc 0 < ν (cylinder fun k : Fin 1 => tau o (fun _ => i) k) := hpos'
    _ = ν ((cylinder fun k : Fin 1 => tau o (fun _ => i) k) ∩ subshift o) :=
        (measure_inter_conull hν).symm
    _ ≤ ν (range (tau o)) := measure_mono hsub

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- A Gibbs measure carried by `Σ_Z` charges `ω(Σ)`. -/
theorem IsGibbs.measure_range_omega_pos [Nonempty ι] {o : ι → ZMod 2} {φ : ι × ZMod 2 → ℝ}
    {ν : Measure (ℤ → ι × ZMod 2)} (h : IsGibbs o φ ν) (hν : ν (subshift o)ᶜ = 0) :
    0 < ν (range (omega o)) := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hpos := h.measureReal_cylinder_pos (omega_mem_subshift fun _ => i) one_pos
  have hpos' : 0 < ν (cylinder fun k : Fin 1 => omega o (fun _ => i) k) := by
    rw [measureReal_def] at hpos
    exact (ENNReal.toReal_pos_iff.1 hpos).1
  have hsub : (cylinder fun k : Fin 1 => omega o (fun _ => i) k) ∩ subshift o ⊆
      range (omega o) := by
    rintro y ⟨hy, hys⟩
    rw [range_omega]
    refine ⟨hys, ?_⟩
    have h0 := hy 0
    simp only [Fin.val_zero, Nat.cast_zero, omega_apply, eps_zero, zero_add] at h0
    rw [h0]
  calc 0 < ν (cylinder fun k : Fin 1 => omega o (fun _ => i) k) := hpos'
    _ = ν ((cylinder fun k : Fin 1 => omega o (fun _ => i) k) ∩ subshift o) :=
        (measure_inter_conull hν).symm
    _ ≤ ν (range (omega o)) := measure_mono hsub

namespace System

variable {S : System ι} {s : ℝ} {μ : Measure (ℤ → ι)} {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)}

/-- `thm:entropy_eq_gibbs`, first half: `h_0(μ) = \overline{h}_0(μ_1)`. -/
theorem GibbsDecomposition.entropy_eq₁ (h : S.GibbsDecomposition s μ μ₁ μ₂) :
    entropy μ₁ = entropy μ := by
  have := h.prob₁
  rw [← map_unCode_of_decomposition h.supp₁ h.eq₁]
  exact (entropy_map_unCode S.o μ₁ h.ergodic₁.toMeasurePreserving h.supp₁).symm

/-- `thm:entropy_eq_gibbs`, second half: `h_0(μ) = \overline{h}_0(μ_2)`. -/
theorem GibbsDecomposition.entropy_eq₂ (h : S.GibbsDecomposition s μ μ₁ μ₂) :
    entropy μ₂ = entropy μ := by
  have := h.prob₂
  rw [← map_unCode_of_decomposition h.supp₂ h.eq₂]
  exact (entropy_map_unCode S.o μ₂ h.ergodic₂.toMeasurePreserving h.supp₂).symm

/-- The marginal `(proj_c)_*(π_*μ)` is the push-forward of `μ` under `proj_c ∘ π`. -/
theorem marginal_eq_map {r M : ℝ} (hS : S.Bounds r M) (c : ZMod 2) (μ : Measure (ℤ → ι)) :
    S.marginal c μ = μ.map fun x => coord c (S.proj x) := by
  have hc : Measurable (coord c) := by
    unfold coord
    split_ifs
    · exact measurable_fst
    · exact measurable_snd
  rw [marginal, Measure.map_map hc hS.measurable_proj]
  rfl

/-- The core of `sec:dimension_of_projections` for one coding `κ ∈ {τ, ω}` with image `R`:
the push-forward of `μ = \overline{κ}_*μ_1 + \overline{κ}_*μ_2` under `\overline{π} ∘ κ` is
the sum `ν_{a,1} + ν_{a,2}` of `eq:proj_eq_is_sum`, the summands are non-zero, and by
`eq:restricted-projection-dimensions` and Jordan–Rapaport they are exact-dimensional with the
dimensions of `eq:gibbs_proj_dim`. -/
theorem exists_decomposition_of_coding (hjr : JordanRapaportDimension.{u}) {r M : ℝ}
    (hS : S.Bounds r M) (hsep : S.ProjExpSeparation) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂]
    (he₁ : Ergodic (shift 1) μ₁) (he₂ : Ergodic (shift 1) μ₂)
    {κ : (ℤ → ι) → ℤ → ι × ZMod 2} (hκ : Measurable κ) {R : Set (ℤ → ι × ZMod 2)}
    (hRm : MeasurableSet R) (hR : ∀ y ∈ R, κ (unCode y) = y) (hpos₁ : 0 < μ₁ R)
    (hpos₂ : 0 < μ₂ R)
    (hμ : μ = (μ₁.restrict R).map unCode + (μ₂.restrict R).map unCode) :
    ∃ ν₁ ν₂ : Measure ℝ, IsFiniteMeasure ν₁ ∧ IsFiniteMeasure ν₂ ∧ ν₁ ≠ 0 ∧ ν₂ ≠ 0 ∧
      μ.map (S.projBar ∘ κ) = ν₁ + ν₂ ∧
      IsExactDim ν₁ (min 1 (-entropy μ₁ / S.lyapBar μ₁)) ∧
      IsExactDim ν₂ (min 1 (-entropy μ₂ / S.lyapBar μ₂)) := by
  have hpb := hS.measurable_projBar
  have hne : ∀ ν : Measure (ℤ → ι × ZMod 2), 0 < ν R → (ν.restrict R).map S.projBar ≠ 0 := by
    intro ν hν h0
    have := congrArg (fun m : Measure ℝ => m univ) h0
    simp only [Measure.map_apply hpb MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, univ_inter, Measure.coe_zero,
      Pi.zero_apply] at this
    exact hν.ne' this
  refine ⟨(μ₁.restrict R).map S.projBar, (μ₂.restrict R).map S.projBar, inferInstance,
    inferInstance, hne μ₁ hpos₁, hne μ₂ hpos₂, ?_, ?_, ?_⟩
  · rw [hμ, Measure.map_add _ _ (hpb.comp hκ), map_comp_coding hκ hRm hR hpb,
      map_comp_coding hκ hRm hR hpb]
  · exact (hjr S hsep μ₁ he₁).of_le
      (Measure.map_mono Measure.restrict_le_self hpb)
  · exact (hjr S hsep μ₂ he₂).of_le
      (Measure.map_mono Measure.restrict_le_self hpb)

variable (S)

/-- `eq:proj_eq_is_sum`, `eq:restricted-projection-dimensions` and `eq:gibbs_proj_dim`: each
coordinate marginal of the `s`-equilibrium state, `0 < s < 2`, is the sum of two non-zero
exact-dimensional measures, of dimensions `min{1, -h_0(μ)/λ_1(𝖠, μ)}` and
`min{1, -h_0(μ)/λ_2(𝖠, μ)}`. -/
theorem marginal_decomposition_normalised (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hjr : JordanRapaportDimension.{u})
    (hrot : S.WithRotations) (hprox : S.HasProximalDiagonal) (hsep : S.ProjExpSeparation)
    (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) (c : ZMod 2) :
    ∃ ν₁ ν₂ : Measure ℝ, IsFiniteMeasure ν₁ ∧ IsFiniteMeasure ν₂ ∧ ν₁ ≠ 0 ∧ ν₂ ≠ 0 ∧
      S.marginal c μ = ν₁ + ν₂ ∧
      IsExactDim ν₁ (min 1 (-entropy μ / S.lyapunov₁ μ)) ∧
      IsExactDim ν₂ (min 1 (-entropy μ / S.lyapunov₂ μ)) := by
  have hgibbs := hfk S hrot hs0 hs2 μ hinv heq
  obtain ⟨μ₁, μ₂, h⟩ := hfjj S hrot hprox hs0 hs2 μ hinv hgibbs
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  have := h.prob₁
  have := h.prob₂
  have : Nonempty ι := ⟨hrot.1.choose⟩
  have e₁ : min 1 (-entropy μ₁ / S.lyapBar μ₁) = min 1 (-entropy μ / S.lyapunov₁ μ) := by
    rw [h.entropy_eq₁, h.lyapunov₁_eq]
  have e₂ : min 1 (-entropy μ₂ / S.lyapBar μ₂) = min 1 (-entropy μ / S.lyapunov₂ μ) := by
    rw [h.entropy_eq₂, h.lyapunov₂_eq]
  rw [← e₁, ← e₂, S.marginal_eq_map hS]
  rcases zmod_two_cases c with rfl | rfl
  · exact exists_decomposition_of_coding hjr hS hsep h.ergodic₁ h.ergodic₂ (measurable_tau S.o)
      (measurableSet_range_tau S.o) (by rintro _ ⟨x, rfl⟩; rfl)
      (h.gibbs₁.measure_range_tau_pos h.supp₁) (h.gibbs₂.measure_range_tau_pos h.supp₂)
      h.eq_tau
  · exact exists_decomposition_of_coding hjr hS hsep h.ergodic₁ h.ergodic₂
      (measurable_omega S.o) (measurableSet_range_omega S.o) (by rintro _ ⟨x, rfl⟩; rfl)
      (h.gibbs₁.measure_range_omega_pos h.supp₁) (h.gibbs₂.measure_range_omega_pos h.supp₂)
      h.eq_omega

end System

end BoxLike
