module

/-
The Kolmogorov–Sinai entropy of `sec:entropies` (tex lines 1877 to 1884, after Bowen, §2):
`h(μ) = sup_𝒬 lim_n n⁻¹ H_μ(⋁_{i<n} σ^{-i} 𝒬)`, the supremum over the finite Borel partitions
`𝒬` of `Σ`, and its equality with `lim_n n⁻¹ H_μ(𝒫_0^{n-1})`, the entropy rate `entropy μ` of the
library, by the generator theorem for the time-zero partition `𝒫` of the two-sided shift.

A finite Borel partition `𝒬 = {Q_1, …, Q_m}` is represented by the Borel map `Q : Ω → Fin m`
sending a point to the index of its atom, so that the atoms are the fibres `Q⁻¹{j}`; empty
fibres add null atoms and do not change any entropy. The join `⋁_{i<n} T^{-i} 𝒬` is the
partition into the fibres of `x ↦ (Q(T^i x))_{i<n}`.

The finite partition calculus is proved here: invariance under injective relabelling and under
a measure-preserving map, the conditional entropy `H(𝒬 | ℛ) = H(𝒬 ∨ ℛ) - H(ℛ)` as an integral of
conditional expectations, its monotonicity in the conditioning partition (conditional Jensen),
the chain rule and the sub-additivity. The generator argument: for the partition `ℛ_k` by the
coordinates `x_{-k}, …, x_k`,
`H(⋁_{i<n} σ^{-i} 𝒬) ≤ H(⋁_{i<n} σ^{-i} ℛ_k) + n H(𝒬 | ℛ_k) ≤ H(𝒫_0^{n+2k-1}) + n H(𝒬 | ℛ_k)`,
so the rate of `𝒬` is at most `h(μ) + H(𝒬 | ℛ_k)`, and `H(𝒬 | ℛ_k) → 0` by Lévy's upward
theorem, since the `ℛ_k` generate the Borel `σ`-algebra of `ℤ → α`.

* `partEntropy`, `condPartEntropy`, `partJoin`, `partEntropyRate`, `ksEntropy`: `H_μ(𝒬)`,
  `H_μ(𝒬 | ℛ)`, `⋁_{i<n} T^{-i} 𝒬`, `lim_n n⁻¹ H_μ(⋁_{i<n} T^{-i} 𝒬)` and the Kolmogorov–Sinai
  entropy.
* `partEntropy_comp_injective`, `partEntropy_comp_measurePreserving`, `partEntropy_nonneg`:
  relabelling and invariance.
* `condPartEntropy_eq_integral`, `condPartEntropy_nonneg`, `integral_negMulLog_condExp_le`,
  `condPartEntropy_le_of_comap_le`, `condPartEntropy_pair`, `condPartEntropy_pair_le`,
  `condPartEntropy_le_partEntropy`, `partEntropy_comp_le`: the conditional entropy calculus.
* `partEntropy_partJoin_add_le`, `tendsto_partEntropyRate`: the limit defining the rate exists.
* `twoSidedFiltration`, `iSup_twoSidedFiltration`, `tendsto_condPartEntropy_twoSidedBlock`: the
  generating partitions `ℛ_k` and `H(𝒬 | ℛ_k) → 0`.
* `partEntropy_partJoin_le`, `partEntropyRate_le_entropy`: the generator inequality.
* `partEntropyRate_coord_zero`, `isGreatest_partEntropyRate`, `ksEntropy_shift_eq_entropy`:
  `h(μ) = lim_n n⁻¹ H_μ(𝒫_0^{n-1})`, with the supremum attained at `𝒫`.
* `tendsto_neg_log_cylinder_ksEntropy`: the Shannon–McMillan–Breiman theorem of tex lines 1885
  to 1977 with the Kolmogorov–Sinai entropy.
-/
public import BoxLike.PastEntropy
public import BoxLike.ShannonMcMillanBreiman
public import BoxLike.SigmaMeasure
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

@[expose] public section

namespace BoxLike

open MeasureTheory ProbabilityTheory Filter Topology Set

/-! ### The entropy of a finite partition -/

section PartEntropy

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  {β γ δ : Type*} [Fintype β] [Fintype γ] [Fintype δ]

/-- The Shannon entropy `H_μ(𝒬) = -∑_{Q ∈ 𝒬} μ(Q) log μ(Q)` of `sec:conditional` (tex lines 1664
to 1746) for the finite partition `𝒬` into the fibres of `f`. -/
noncomputable def partEntropy (f : Ω → β) : ℝ :=
  ∑ b, Real.negMulLog (μ.real (f ⁻¹' {b}))

/-- The conditional entropy `H_μ(𝒬 | ℛ) = H_μ(𝒬 ∨ ℛ) - H_μ(ℛ)` of the finite partition into the
fibres of `f` given the finite partition into the fibres of `g`. -/
noncomputable def condPartEntropy (f : Ω → β) (g : Ω → γ) : ℝ :=
  partEntropy μ (fun x => (f x, g x)) - partEntropy μ g

/-- The join `⋁_{i<n} T^{-i} 𝒬` of `sec:entropies` (tex lines 1877 to 1884), as the map
`x ↦ (f(T^i x))_{i<n}` whose fibres are its atoms. -/
def partJoin (T : Ω → Ω) (f : Ω → β) (n : ℕ) (x : Ω) : Fin n → β :=
  fun i => f (T^[i] x)

/-- The entropy rate `lim_n n⁻¹ H_μ(⋁_{i<n} T^{-i} 𝒬)` of a finite partition (tex lines 1877 to
1972). The limit exists for an invariant measure (`tendsto_partEntropyRate`). -/
noncomputable def partEntropyRate (T : Ω → Ω) (f : Ω → β) : ℝ :=
  limUnder atTop fun n : ℕ => partEntropy μ (partJoin T f n) / n

/-- The Kolmogorov–Sinai entropy `h(μ) = sup_𝒬 lim_n n⁻¹ H_μ(⋁_{i<n} T^{-i} 𝒬)` of
`sec:entropies` (tex lines 1877 to 1884), the supremum over the finite Borel partitions `𝒬`,
each given by the Borel map `Q : Ω → Fin m` to the indices of its atoms. -/
noncomputable def ksEntropy (T : Ω → Ω) : ℝ :=
  sSup {r | ∃ (m : ℕ) (Q : Ω → Fin m), Measurable Q ∧ partEntropyRate μ T Q = r}

variable {μ}

/-- The entropy is invariant under an injective relabelling of the atoms. -/
theorem partEntropy_comp_injective {φ : β → γ} (hφ : Function.Injective φ) (f : Ω → β) :
    partEntropy μ (φ ∘ f) = partEntropy μ f := by
  symm
  refine Fintype.sum_of_injective φ hφ _ _ (fun c hc => ?_) (fun b => ?_)
  · have : (φ ∘ f) ⁻¹' {c} = ∅ := by
      ext x
      simp only [mem_preimage, Function.comp_apply, mem_singleton_iff, mem_empty_iff_false,
        iff_false]
      exact fun h => hc ⟨f x, h⟩
    rw [this, measureReal_empty, Real.negMulLog_zero]
  · have : (φ ∘ f) ⁻¹' {φ b} = f ⁻¹' {b} := by
      ext x
      simp [hφ.eq_iff]
    rw [this]

/-- The entropy of a partition by a function of the atoms of another partition is the entropy
of the latter when the function is injective; in the form `f = φ ∘ g` for a later rewrite. -/
theorem partEntropy_eq_of_comp {φ : γ → β} (hφ : Function.Injective φ) {f : Ω → β}
    {g : Ω → γ} (h : f = φ ∘ g) : partEntropy μ f = partEntropy μ g := by
  rw [h, partEntropy_comp_injective hφ]

/-- A measure-preserving map does not change the entropy of a Borel partition. -/
theorem partEntropy_comp_measurePreserving {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    [MeasurableSpace β] [MeasurableSingletonClass β] {f : Ω → β} (hf : Measurable f) :
    partEntropy μ (f ∘ T) = partEntropy μ f := by
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Set.preimage_comp, hT.measureReal_preimage (hf (measurableSet_singleton b)).nullMeasurableSet]

/-- The entropy of a partition is non-negative. -/
theorem partEntropy_nonneg [IsProbabilityMeasure μ] (f : Ω → β) : 0 ≤ partEntropy μ f :=
  Finset.sum_nonneg fun _ _ => Real.negMulLog_nonneg measureReal_nonneg measureReal_le_one

/-- The trivial partition has entropy zero. -/
theorem partEntropy_of_subsingleton [IsProbabilityMeasure μ] [Subsingleton β] (f : Ω → β) :
    partEntropy μ f = 0 := by
  rcases isEmpty_or_nonempty β with hβ | hβ
  · simp [partEntropy]
  · obtain ⟨b⟩ := hβ
    have : Unique β := uniqueOfSubsingleton b
    have hpre : f ⁻¹' {default} = univ := by
      ext x
      simp [Subsingleton.elim (f x) default]
    rw [partEntropy, Fintype.sum_unique, hpre, probReal_univ, Real.negMulLog_one]

omit [MeasurableSpace Ω] [Fintype β] [Fintype γ] in
/-- The preimage of a point under the pair `(f, g)` is the intersection of the fibres. -/
theorem preimage_pair_singleton (f : Ω → β) (g : Ω → γ) (b : β) (c : γ) :
    (fun x => (f x, g x)) ⁻¹' {(b, c)} = f ⁻¹' {b} ∩ g ⁻¹' {c} := by
  ext x
  simp [Prod.ext_iff]

end PartEntropy

/-- A function of a map generates a coarser `σ`-algebra than the map. -/
theorem comap_comp_le {Ω γ δ : Type*} [MeasurableSpace γ] [MeasurableSpace δ] {g : Ω → γ}
    (φ : γ → δ) (hφ : Measurable φ) :
    MeasurableSpace.comap (φ ∘ g) (inferInstance : MeasurableSpace δ) ≤
      MeasurableSpace.comap g inferInstance := by
  rw [← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hφ.comap_le

/-! ### Conditional entropy -/

section CondEntropy

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {β γ δ : Type*} [Fintype β] [Fintype γ] [Fintype δ]
  [MeasurableSpace β] [MeasurableSingletonClass β] [MeasurableSpace γ]
  [MeasurableSingletonClass γ] [MeasurableSpace δ] [MeasurableSingletonClass δ]

/-- The conditional entropy of finite partitions as an integral of conditional expectations:
`H_μ(𝒬 | ℛ) = ∫ ∑_{Q ∈ 𝒬} η(E_μ(1_Q | ℛ)) dμ` with `η(t) = -t log t`, which is
`∫ I_μ(𝒬 | ℛ) dμ` of `sec:conditional` (tex lines 1652 to 1662). -/
theorem condPartEntropy_eq_integral [IsFiniteMeasure μ] {f : Ω → β} {g : Ω → γ}
    (hf : Measurable f) (hg : Measurable g) :
    condPartEntropy μ f g =
      ∫ x, ∑ b, Real.negMulLog ((μ⟦f ⁻¹' {b} | MeasurableSpace.comap g inferInstance⟧) x) ∂μ := by
  rw [integral_sum_negMulLog_condExp_comap hf hg, condPartEntropy, partEntropy, partEntropy,
    Fintype.sum_prod_type, Finset.sum_comm]
  simp only [preimage_pair_singleton]

/-- The conditional entropy of finite partitions is non-negative. -/
theorem condPartEntropy_nonneg [IsFiniteMeasure μ] {f : Ω → β} {g : Ω → γ}
    (hf : Measurable f) (hg : Measurable g) : 0 ≤ condPartEntropy μ f g := by
  rw [condPartEntropy_eq_integral hf hg]
  have h : ∀ᵐ x ∂μ, ∀ b, (μ⟦f ⁻¹' {b} | MeasurableSpace.comap g inferInstance⟧) x ∈
      Icc (0 : ℝ) 1 :=
    ae_all_iff.2 fun b => condExp_indicator_mem_Icc hg.comap_le (hf (measurableSet_singleton b))
  exact integral_nonneg_of_ae (h.mono fun x hx =>
    Finset.sum_nonneg fun b _ => (negMulLog_mem_Icc (hx b)).1)

omit [Fintype β] [Fintype γ] [Fintype δ] [MeasurableSpace β] [MeasurableSingletonClass β]
  [MeasurableSpace γ] [MeasurableSingletonClass γ] [MeasurableSpace δ]
  [MeasurableSingletonClass δ] [MeasurableSpace Ω] in
/-- `η` of a conditional probability is integrable, since it takes values in `[0, 1]`. -/
theorem integrable_negMulLog_condExp {m m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hm : m ≤ m0) {A : Set Ω} (hA : MeasurableSet A) :
    Integrable (fun x => Real.negMulLog ((μ⟦A | m⟧) x)) μ :=
  Integrable.of_bound (Real.continuous_negMulLog.comp_aestronglyMeasurable
    (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable) 1
    ((condExp_indicator_mem_Icc hm hA).mono fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (negMulLog_mem_Icc hx).1]
      exact (negMulLog_mem_Icc hx).2)

omit [Fintype β] [Fintype γ] [Fintype δ] [MeasurableSpace β] [MeasurableSingletonClass β]
  [MeasurableSpace γ] [MeasurableSingletonClass γ] [MeasurableSpace δ]
  [MeasurableSingletonClass δ] [MeasurableSpace Ω] in
/-- Conditioning on a finer `σ`-algebra decreases the integrated `η` of a conditional
probability, by the conditional Jensen inequality for the concave function `η(t) = -t log t`
on `[0, 1]` and the tower property. -/
theorem integral_negMulLog_condExp_le {m₁ m₂ m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ m0) {A : Set Ω} (hA : MeasurableSet A) :
    ∫ x, Real.negMulLog ((μ⟦A | m₂⟧) x) ∂μ ≤ ∫ x, Real.negMulLog ((μ⟦A | m₁⟧) x) ∂μ := by
  have h₁ : m₁ ≤ m0 := h₁₂.trans h₂
  have hη : ∀ {m : MeasurableSpace Ω}, m ≤ m0 →
      Integrable (fun x => Real.negMulLog ((μ⟦A | m⟧) x)) μ := fun hm =>
    integrable_negMulLog_condExp hm hA
  have hconc : ConcaveOn ℝ (Icc (0 : ℝ) 1) Real.negMulLog :=
    Real.concaveOn_negMulLog.subset Icc_subset_Ici_self (convex_Icc 0 1)
  have hJ := hconc.condExp_map_le h₁ Real.continuous_negMulLog.continuousOn.upperSemicontinuousOn
    (condExp_indicator_mem_Icc h₂ hA) isClosed_Icc integrable_condExp (hη h₂)
  have htower : μ[μ⟦A | m₂⟧ | m₁] =ᵐ[μ] μ⟦A | m₁⟧ := condExp_condExp_of_le h₁₂ h₂
  calc ∫ x, Real.negMulLog ((μ⟦A | m₂⟧) x) ∂μ
      = ∫ x, (μ[Real.negMulLog ∘ μ⟦A | m₂⟧ | m₁]) x ∂μ := (integral_condExp h₁).symm
    _ ≤ ∫ x, Real.negMulLog ((μ[μ⟦A | m₂⟧ | m₁]) x) ∂μ :=
        integral_mono_ae integrable_condExp
          ((hη h₁).congr (htower.mono fun x hx => by simp only [hx])) hJ
    _ = ∫ x, Real.negMulLog ((μ⟦A | m₁⟧) x) ∂μ :=
        integral_congr_ae (htower.mono fun x hx => by simp only [hx])

/-- Monotonicity of the conditional entropy in the conditioning partition: if the partition by
`g'` is coarser than the partition by `g` (`σ(g') ≤ σ(g)`), then
`H_μ(𝒬 | g) ≤ H_μ(𝒬 | g')`. -/
theorem condPartEntropy_le_of_comap_le [IsFiniteMeasure μ] {f : Ω → β} {g : Ω → γ}
    {g' : Ω → δ} (hf : Measurable f) (hg : Measurable g) (hg' : Measurable g')
    (hle : MeasurableSpace.comap g' inferInstance ≤ MeasurableSpace.comap g inferInstance) :
    condPartEntropy μ f g ≤ condPartEntropy μ f g' := by
  rw [condPartEntropy_eq_integral hf hg, condPartEntropy_eq_integral hf hg',
    integral_finsetSum _ fun b _ =>
      integrable_negMulLog_condExp hg.comap_le (hf (measurableSet_singleton b)),
    integral_finsetSum _ fun b _ =>
      integrable_negMulLog_condExp hg'.comap_le (hf (measurableSet_singleton b))]
  exact Finset.sum_le_sum fun b _ =>
    integral_negMulLog_condExp_le hle hg.comap_le (hf (measurableSet_singleton b))

/-- Monotonicity of the conditional entropy for a function of the conditioning partition. -/
theorem condPartEntropy_le_comp [IsFiniteMeasure μ] {f : Ω → β} {g : Ω → γ}
    (hf : Measurable f) (hg : Measurable g) (φ : γ → δ) :
    condPartEntropy μ f g ≤ condPartEntropy μ f (φ ∘ g) :=
  condPartEntropy_le_of_comap_le hf hg ((measurable_of_countable φ).comp hg)
    (comap_comp_le φ (measurable_of_countable φ))

omit [MeasurableSpace β] [MeasurableSingletonClass β] [MeasurableSpace γ]
  [MeasurableSingletonClass γ] [MeasurableSpace δ] [MeasurableSingletonClass δ] in
/-- The conditional entropy is invariant under an injective relabelling of the atoms of the
partition whose entropy is taken. -/
theorem condPartEntropy_comp_injective {φ : β → δ} (hφ : Function.Injective φ) (f : Ω → β)
    (g : Ω → γ) : condPartEntropy μ (φ ∘ f) g = condPartEntropy μ f g := by
  have hinj : Function.Injective (Prod.map φ (id : γ → γ)) := fun p q h => by
    simp only [Prod.map, Prod.mk.injEq, id] at h
    exact Prod.ext (hφ h.1) h.2
  have h : partEntropy μ (fun x => ((φ ∘ f) x, g x)) = partEntropy μ (fun x => (f x, g x)) :=
    partEntropy_eq_of_comp (φ := Prod.map φ id) hinj rfl
  rw [condPartEntropy, condPartEntropy, h]

omit [MeasurableSpace β] [MeasurableSingletonClass β] [MeasurableSpace γ]
  [MeasurableSingletonClass γ] [MeasurableSpace δ] [MeasurableSingletonClass δ] in
/-- The chain rule `H(𝒬 ∨ 𝒬' | ℛ) = H(𝒬 | ℛ) + H(𝒬' | 𝒬 ∨ ℛ)`. -/
theorem condPartEntropy_pair (f : Ω → β) (f' : Ω → δ) (g : Ω → γ) :
    condPartEntropy μ (fun x => (f x, f' x)) g =
      condPartEntropy μ f g + condPartEntropy μ f' fun x => (f x, g x) := by
  have h : partEntropy μ (fun x => (f' x, (f x, g x))) =
      partEntropy μ (fun x => ((f x, f' x), g x)) :=
    partEntropy_eq_of_comp (φ := fun p : (β × δ) × γ => (p.1.2, (p.1.1, p.2)))
      (fun p q hpq => by
        simp only [Prod.mk.injEq] at hpq
        exact Prod.ext (Prod.ext hpq.2.1 hpq.1) hpq.2.2) rfl
  rw [condPartEntropy, condPartEntropy, condPartEntropy, h]
  ring

/-- Sub-additivity of the conditional entropy: `H(𝒬 ∨ 𝒬' | ℛ) ≤ H(𝒬 | ℛ) + H(𝒬' | ℛ)`. -/
theorem condPartEntropy_pair_le [IsFiniteMeasure μ] {f : Ω → β} {f' : Ω → δ} {g : Ω → γ}
    (hf : Measurable f) (hf' : Measurable f') (hg : Measurable g) :
    condPartEntropy μ (fun x => (f x, f' x)) g ≤
      condPartEntropy μ f g + condPartEntropy μ f' g := by
  rw [condPartEntropy_pair]
  have h := condPartEntropy_le_comp (μ := μ) hf' (hf.prodMk hg) Prod.snd
  have e : (Prod.snd ∘ fun x => (f x, g x)) = g := rfl
  rw [e] at h
  linarith

omit [MeasurableSpace β] [MeasurableSingletonClass β] in
/-- The conditional entropy given the trivial partition is the entropy. -/
theorem condPartEntropy_unit [IsProbabilityMeasure μ] (f : Ω → β) :
    condPartEntropy μ f (fun _ => ()) = partEntropy μ f := by
  rw [condPartEntropy, partEntropy_of_subsingleton (fun _ : Ω => ()), sub_zero]
  exact partEntropy_eq_of_comp (φ := fun b => (b, ())) (fun b b' h => (Prod.mk.inj h).1) rfl

/-- Conditioning does not increase entropy: `H(𝒬 | ℛ) ≤ H(𝒬)`. -/
theorem condPartEntropy_le_partEntropy [IsProbabilityMeasure μ] {f : Ω → β} {g : Ω → γ}
    (hf : Measurable f) (hg : Measurable g) : condPartEntropy μ f g ≤ partEntropy μ f := by
  rw [← condPartEntropy_unit f]
  exact condPartEntropy_le_comp hf hg fun _ => ()

/-- A refinement has larger entropy: `H(ℛ) ≤ H(𝒬 ∨ ℛ)`. -/
theorem partEntropy_le_pair [IsFiniteMeasure μ] {f : Ω → β} {g : Ω → γ} (hf : Measurable f)
    (hg : Measurable g) : partEntropy μ g ≤ partEntropy μ fun x => (f x, g x) := by
  have := condPartEntropy_nonneg (μ := μ) hf hg
  rw [condPartEntropy] at this
  linarith

/-- A coarsening has smaller entropy: `H(φ ∘ g) ≤ H(g)`. -/
theorem partEntropy_comp_le [IsFiniteMeasure μ] {g : Ω → γ} (hg : Measurable g) (φ : γ → δ) :
    partEntropy μ (φ ∘ g) ≤ partEntropy μ g := by
  have h := partEntropy_le_pair (μ := μ) hg ((measurable_of_countable φ).comp hg)
  have e : partEntropy μ (fun x => (g x, (φ ∘ g) x)) = partEntropy μ g :=
    partEntropy_eq_of_comp (φ := fun c => (c, φ c)) (fun c c' h => (Prod.mk.inj h).1) rfl
  rw [e] at h
  exact h

/-- A measure-preserving map does not change the conditional entropy. -/
theorem condPartEntropy_comp_measurePreserving {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → β} {g : Ω → γ} (hf : Measurable f) (hg : Measurable g) :
    condPartEntropy μ (f ∘ T) (g ∘ T) = condPartEntropy μ f g := by
  rw [condPartEntropy, condPartEntropy, partEntropy_comp_measurePreserving hT hg]
  have : (fun x => ((f ∘ T) x, (g ∘ T) x)) = (fun x => (f x, g x)) ∘ T := rfl
  rw [this, partEntropy_comp_measurePreserving hT (hf.prodMk hg)]

end CondEntropy

/-! ### Joins and the entropy rate -/

section Join

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}
  {β γ : Type*} [Fintype β] [Fintype γ] [MeasurableSpace β] [MeasurableSingletonClass β]
  [MeasurableSpace γ] [MeasurableSingletonClass γ]

omit [MeasurableSpace Ω] [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ] in
/-- The join of length `m + n` is the join of length `m` followed by the join of length `n`
along `T^m`. -/
theorem partJoin_add (f : Ω → β) (m n : ℕ) :
    partJoin T f (m + n) = (Fin.appendEquiv m n) ∘ fun x =>
      (partJoin T f m x, partJoin T f n (T^[m] x)) := by
  funext x i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [partJoin]
  · simp only [partJoin, Function.comp_apply, Fin.appendEquiv_apply, Fin.append_right,
      Fin.val_natAdd]
    rw [← Function.iterate_add_apply, add_comm]

omit [Fintype β] [MeasurableSingletonClass β] [Fintype γ] [MeasurableSpace γ]
  [MeasurableSingletonClass γ] in
/-- The join of a Borel partition is Borel. -/
theorem measurable_partJoin (hT : Measurable T) {f : Ω → β} (hf : Measurable f) (n : ℕ) :
    Measurable (partJoin T f n) :=
  Measurable.of_eval fun i => hf.comp (hT.iterate i)

omit [MeasurableSpace Ω] [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ] in
/-- The join along `T` composed with `T^m` is the join of `f ∘ T^m`. -/
theorem partJoin_comp_iterate (f : Ω → β) (m n : ℕ) :
    (fun x => partJoin T f n (T^[m] x)) = partJoin T (f ∘ T^[m]) n := by
  funext x i
  simp only [partJoin, Function.comp_apply]
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, add_comm]

/-- Sub-additivity of the entropies of the joins of a Borel partition under a measure-preserving
map: `H(⋁_{i<m+n} T^{-i} 𝒬) ≤ H(⋁_{i<m} T^{-i} 𝒬) + H(⋁_{i<n} T^{-i} 𝒬)`. -/
theorem partEntropy_partJoin_add_le [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : Ω → β} (hf : Measurable f) (m n : ℕ) :
    partEntropy μ (partJoin T f (m + n)) ≤
      partEntropy μ (partJoin T f m) + partEntropy μ (partJoin T f n) := by
  have hm := measurable_partJoin hT.measurable hf m
  have hn : Measurable fun x => partJoin T f n (T^[m] x) :=
    (measurable_partJoin hT.measurable hf n).comp (hT.measurable.iterate m)
  rw [partJoin_add, partEntropy_comp_injective (Fin.appendEquiv m n).injective]
  have h := condPartEntropy_le_partEntropy (μ := μ) hm hn
  have hinv : partEntropy μ (fun x => partJoin T f n (T^[m] x)) =
      partEntropy μ (partJoin T f n) :=
    partEntropy_comp_measurePreserving (hT.iterate m) (measurable_partJoin hT.measurable hf n)
  rw [condPartEntropy] at h
  linarith

/-- The limit defining the entropy rate of a Borel partition exists for an invariant measure, by
Fekete's lemma (tex lines 1877 to 1884). -/
theorem tendsto_partEntropyRate [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : Ω → β} (hf : Measurable f) :
    Tendsto (fun n : ℕ => partEntropy μ (partJoin T f n) / n) atTop
      (𝓝 (partEntropyRate μ T f)) := by
  have hsub : Subadditive fun n => partEntropy μ (partJoin T f n) := fun m n =>
    partEntropy_partJoin_add_le hT hf m n
  have hbdd : BddBelow (range fun n : ℕ => partEntropy μ (partJoin T f n) / n) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact div_nonneg (partEntropy_nonneg _) (Nat.cast_nonneg n)⟩
  have h := hsub.tendsto_lim hbdd
  rw [partEntropyRate, h.limUnder_eq]
  exact h

/-- Sub-additivity of the conditional entropy over a join: the conditional entropy of
`⋁_{i<n} T^{-i} 𝒬` given `ℛ` is at most `∑_{i<n} H(T^{-i} 𝒬 | ℛ)`. -/
theorem condPartEntropy_partJoin_le [IsProbabilityMeasure μ] (hT : Measurable T) {f : Ω → β}
    (hf : Measurable f) {g : Ω → γ} (hg : Measurable g) (n : ℕ) :
    condPartEntropy μ (partJoin T f n) g ≤
      ∑ i ∈ Finset.range n, condPartEntropy μ (f ∘ T^[i]) g := by
  induction n with
  | zero =>
    rw [Finset.sum_range_zero]
    exact (condPartEntropy_le_partEntropy (measurable_partJoin hT hf 0) hg).trans_eq
      (partEntropy_of_subsingleton _)
  | succ n ih =>
    rw [partJoin_add, condPartEntropy_comp_injective (Fin.appendEquiv n 1).injective,
      Finset.sum_range_succ]
    have h1 : partJoin T f 1 ∘ T^[n] = (fun b (_ : Fin 1) => b) ∘ (f ∘ T^[n]) := by
      funext x i
      simp [partJoin]
    refine (condPartEntropy_pair_le (measurable_partJoin hT hf n)
      ((measurable_partJoin hT hf 1).comp (hT.iterate n)) hg).trans ?_
    rw [h1, condPartEntropy_comp_injective (fun b b' h => congrFun h 0)]
    exact add_le_add_left ih _

end Join

/-! ### The generating partitions of the two-sided shift -/

section Generator

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The partition `ℛ_k` of `ℤ → α` by the coordinates `x_{-k}, …, x_k`. -/
def twoSidedBlock (k : ℕ) (x : ℤ → α) : Fin (2 * k + 1) → α :=
  fun j => x ((j : ℤ) - k)

omit [Fintype α] [MeasurableSingletonClass α] in
/-- `ℛ_k` is Borel. -/
theorem measurable_twoSidedBlock (k : ℕ) : Measurable (twoSidedBlock k : (ℤ → α) → _) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `ℛ_k` is a function of `ℛ_{k+1}`. -/
theorem twoSidedBlock_eq_comp_succ (k : ℕ) :
    (twoSidedBlock k : (ℤ → α) → _) =
      (fun w (j : Fin (2 * k + 1)) => w ⟨j + 1, by omega⟩) ∘ twoSidedBlock (k + 1) := by
  funext x j
  simp only [twoSidedBlock, Function.comp_apply]
  congr 1
  push_cast
  ring

/-- The filtration `k ↦ σ(x_{-k}, …, x_k)` of the two-sided shift. -/
def twoSidedFiltration (α : Type*) [MeasurableSpace α] :
    Filtration ℕ (inferInstance : MeasurableSpace (ℤ → α)) where
  seq k := MeasurableSpace.comap (twoSidedBlock k) inferInstance
  mono' := monotone_nat_of_le_succ fun k => by
    rw [twoSidedBlock_eq_comp_succ k, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono
      (Measurable.comap_le (Measurable.of_eval fun _ => measurable_pi_apply _))
  le' k := (measurable_twoSidedBlock k).comap_le

omit [Fintype α] [MeasurableSingletonClass α] in
/-- The partitions `ℛ_k` generate the Borel `σ`-algebra of `ℤ → α`. -/
theorem iSup_twoSidedFiltration :
    ⨆ k, twoSidedFiltration α k = (inferInstance : MeasurableSpace (ℤ → α)) := by
  refine le_antisymm (iSup_le fun k => (twoSidedFiltration α).le k) ?_
  change MeasurableSpace.pi ≤ _
  refine iSup_le fun j => le_trans ?_ (le_iSup _ j.natAbs)
  change _ ≤ MeasurableSpace.comap (twoSidedBlock j.natAbs) _
  have hlt : (j + j.natAbs).toNat < 2 * j.natAbs + 1 := by omega
  have e : (fun x : ℤ → α => x j) =
      (fun w : Fin (2 * j.natAbs + 1) → α => w ⟨(j + j.natAbs).toNat, hlt⟩) ∘
        twoSidedBlock j.natAbs := by
    funext x
    simp only [Function.comp_apply, twoSidedBlock]
    congr 1
    omega
  rw [e, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (Measurable.comap_le (measurable_pi_apply _))

/-- Lévy's upward theorem for the generating partitions: `H_μ(𝒬 | ℛ_k) → 0` for every finite
Borel partition `𝒬` of `ℤ → α`. -/
theorem tendsto_condPartEntropy_twoSidedBlock {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    {f : (ℤ → α) → β} (hf : Measurable f) :
    Tendsto (fun k => condPartEntropy μ f (twoSidedBlock k)) atTop (𝓝 0) := by
  have hA : ∀ b, MeasurableSet (f ⁻¹' {b}) := fun b => hf (measurableSet_singleton b)
  have h := tendsto_integral_sum_negMulLog_condExp (μ := μ) (twoSidedFiltration α) hA
  rw [iSup_twoSidedFiltration] at h
  have hlim : ∫ x, ∑ b, Real.negMulLog ((μ⟦f ⁻¹' {b} |
      (inferInstance : MeasurableSpace (ℤ → α))⟧) x) ∂μ = 0 := by
    refine integral_eq_zero_of_ae (ae_of_all _ fun x => Finset.sum_eq_zero fun b _ => ?_)
    rw [condExp_of_stronglyMeasurable le_rfl
      ((measurable_const.indicator (hA b)).stronglyMeasurable)
      ((integrable_const (1 : ℝ)).indicator (hA b))]
    by_cases hx : x ∈ f ⁻¹' {b}
    · simp [hx]
    · simp [hx]
  rw [hlim] at h
  refine h.congr fun k => ?_
  rw [condPartEntropy_eq_integral hf (measurable_twoSidedBlock k)]
  rfl

variable {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]

/-- The join of `ℛ_k` of length `n` is a function of the block of length `n + 2k` of `σ^{-k} x`,
so its entropy is at most `H_μ(𝒫_0^{n+2k-1})`. -/
theorem partEntropy_partJoin_twoSidedBlock_le (hinv : MeasurePreserving (shift 1) μ μ)
    (k n : ℕ) : partEntropy μ (partJoin (shift 1) (twoSidedBlock k) n) ≤
      blockEntropy μ (n + 2 * k) := by
  have e : partJoin (shift 1) (twoSidedBlock k) n =
      (fun (w : Fin (n + 2 * k) → α) (i : Fin n) (j : Fin (2 * k + 1)) =>
        w ⟨i + j, by omega⟩) ∘ (block (n + 2 * k) ∘ shift (-(k : ℤ))) := by
    funext x i j
    simp only [partJoin, iterate_shift_one, twoSidedBlock, Function.comp_apply, block,
      shift_apply]
    congr 1
    push_cast
    ring
  rw [e]
  refine (partEntropy_comp_le ((measurable_block _).comp (measurable_shift _)) _).trans_eq ?_
  rw [partEntropy_comp_measurePreserving (measurePreserving_shift_neg_natCast hinv k)
    (measurable_block _)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [cylinder_eq_preimage]

/-- The key inequality of the generator theorem:
`H(⋁_{i<n} σ^{-i} 𝒬) ≤ H_μ(𝒫_0^{n+2k-1}) + n H_μ(𝒬 | ℛ_k)`. -/
theorem partEntropy_partJoin_le (hinv : MeasurePreserving (shift 1) μ μ) {β : Type*}
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] {f : (ℤ → α) → β}
    (hf : Measurable f) (k n : ℕ) :
    partEntropy μ (partJoin (shift 1) f n) ≤
      blockEntropy μ (n + 2 * k) + n * condPartEntropy μ f (twoSidedBlock k) := by
  have hT := hinv.measurable
  have hR := measurable_twoSidedBlock (α := α) k
  have hJf := measurable_partJoin hT hf n
  have hJR := measurable_partJoin hT hR n
  have h1 : partEntropy μ (partJoin (shift 1) f n) ≤ partEntropy μ (fun x =>
      (partJoin (shift 1) f n x, partJoin (shift 1) (twoSidedBlock k) n x)) := by
    have e : partEntropy μ (fun x =>
        (partJoin (shift 1) f n x, partJoin (shift 1) (twoSidedBlock k) n x)) =
        partEntropy μ (fun x =>
          (partJoin (shift 1) (twoSidedBlock k) n x, partJoin (shift 1) f n x)) :=
      partEntropy_eq_of_comp (φ := Prod.swap) Prod.swap_injective rfl
    rw [e]
    exact partEntropy_le_pair hJR hJf
  have h2 : partEntropy μ (fun x => (partJoin (shift 1) f n x,
      partJoin (shift 1) (twoSidedBlock k) n x)) =
      partEntropy μ (partJoin (shift 1) (twoSidedBlock k) n) +
        condPartEntropy μ (partJoin (shift 1) f n) (partJoin (shift 1) (twoSidedBlock k) n) := by
    rw [condPartEntropy]
    ring
  -- conditional entropy of the join given the join of `ℛ_k`
  have h5 : condPartEntropy μ (partJoin (shift 1) f n) (partJoin (shift 1) (twoSidedBlock k) n) ≤
      n * condPartEntropy μ f (twoSidedBlock k) := by
    refine (condPartEntropy_partJoin_le hT hf hJR n).trans ?_
    have hterm : ∀ i ∈ Finset.range n,
        condPartEntropy μ (f ∘ (shift 1)^[i]) (partJoin (shift 1) (twoSidedBlock k) n) ≤
          condPartEntropy μ f (twoSidedBlock k) := fun i hi => by
      have hi' : i < n := Finset.mem_range.1 hi
      have e : twoSidedBlock k ∘ (shift 1)^[i] =
          (fun w : Fin n → Fin (2 * k + 1) → α => w ⟨i, hi'⟩) ∘
            partJoin (shift 1) (twoSidedBlock k) n := rfl
      refine (condPartEntropy_le_comp (hf.comp (hT.iterate i)) hJR
        (fun w : Fin n → Fin (2 * k + 1) → α => w ⟨i, hi'⟩)).trans_eq ?_
      rw [← e, condPartEntropy_comp_measurePreserving (hinv.iterate i) hf hR]
    refine (Finset.sum_le_sum hterm).trans_eq ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h6 := partEntropy_partJoin_twoSidedBlock_le hinv k n
  linarith

/-- The generator theorem for the time-zero partition of the two-sided shift: for every finite
Borel partition `𝒬` of `ℤ → α` and every invariant probability measure,
`lim_n n⁻¹ H_μ(⋁_{i<n} σ^{-i} 𝒬) ≤ lim_n n⁻¹ H_μ(𝒫_0^{n-1}) = h(μ)` (tex lines 1877 to 1884). -/
theorem partEntropyRate_le_entropy (hinv : MeasurePreserving (shift 1) μ μ) {β : Type*}
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] {f : (ℤ → α) → β}
    (hf : Measurable f) : partEntropyRate μ (shift 1) f ≤ entropy μ := by
  have hrate := tendsto_partEntropyRate hinv hf
  have hk : ∀ k : ℕ, partEntropyRate μ (shift 1) f ≤
      entropy μ + condPartEntropy μ f (twoSidedBlock k) := fun k => by
    -- `H_μ(𝒫_0^{n+2k-1}) / n → h(μ)`
    have hb : Tendsto (fun n : ℕ => blockEntropy μ (n + 2 * k) / n) atTop (𝓝 (entropy μ)) := by
      have h1 := (tendsto_entropy hinv).comp (tendsto_add_atTop_nat (2 * k))
      have h2 : Tendsto (fun n : ℕ => ((n + 2 * k : ℕ) : ℝ) / n) atTop (𝓝 1) := by
        have : Tendsto (fun n : ℕ => 1 + (2 * k : ℝ) / n) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat _)
        rw [add_zero] at this
        refine this.congr' ((eventually_gt_atTop 0).mono fun n hn => ?_)
        have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
        push_cast
        field_simp
      have h3 := h1.mul h2
      rw [mul_one] at h3
      refine h3.congr' ((eventually_gt_atTop 0).mono fun n hn => ?_)
      have hn' : ((n + 2 * k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      simp only [Function.comp_apply]
      field_simp
    have hbound : ∀ᶠ n : ℕ in atTop, partEntropy μ (partJoin (shift 1) f n) / n ≤
        blockEntropy μ (n + 2 * k) / n + condPartEntropy μ f (twoSidedBlock k) :=
      (eventually_gt_atTop 0).mono fun n hn => by
        have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
        rw [div_add' _ _ _ hn'.ne', div_le_div_iff_of_pos_right hn']
        linarith [partEntropy_partJoin_le hinv hf k n]
    exact le_of_tendsto_of_tendsto hrate (hb.add_const _) hbound
  have hlim := (tendsto_condPartEntropy_twoSidedBlock (μ := μ) hf).const_add (entropy μ)
  rw [add_zero] at hlim
  exact ge_of_tendsto hlim (Eventually.of_forall hk)

omit [MeasurableSingletonClass α] [IsProbabilityMeasure μ] in
/-- The rate of the time-zero partition `𝒫` is the entropy rate `entropy μ`: the join
`⋁_{i<n} σ^{-i} 𝒫` is the partition `𝒫_0^{n-1}` into the cylinders of length `n`. -/
theorem partEntropyRate_coord_zero :
    partEntropyRate μ (shift 1) (fun x : ℤ → α => x 0) = entropy μ := by
  have e : ∀ n, partEntropy μ (partJoin (shift 1) (fun x : ℤ → α => x 0) n) =
      blockEntropy μ n := fun n => by
    have hj : partJoin (shift 1) (fun x : ℤ → α => x 0) n = block n := by
      funext x i
      simp [partJoin, iterate_shift_one, block]
    rw [hj]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [cylinder_eq_preimage]
  simp only [partEntropyRate, entropy, e]

/-- `sec:entropies`, tex lines 1877 to 1884: the rates of the finite Borel partitions of the
two-sided shift have the greatest element `lim_n n⁻¹ H_μ(𝒫_0^{n-1})`, attained at the time-zero
partition `𝒫`, relabelled by `Fin #α`. -/
theorem isGreatest_partEntropyRate (hinv : MeasurePreserving (shift 1) μ μ) :
    IsGreatest {r | ∃ (m : ℕ) (Q : (ℤ → α) → Fin m), Measurable Q ∧
      partEntropyRate μ (shift 1) Q = r} (entropy μ) := by
  refine ⟨⟨Fintype.card α, (Fintype.equivFin α) ∘ fun x => x 0,
    (measurable_of_countable _).comp (measurable_pi_apply 0), ?_⟩, ?_⟩
  · have e : ∀ n, partEntropy μ (partJoin (shift 1) ((Fintype.equivFin α) ∘ fun x => x 0) n) =
        partEntropy μ (partJoin (shift 1) (fun x : ℤ → α => x 0) n) := fun n =>
      partEntropy_eq_of_comp (φ := fun w => (Fintype.equivFin α) ∘ w)
        (fun w w' h => funext fun i => (Fintype.equivFin α).injective (congrFun h i)) rfl
    rw [← partEntropyRate_coord_zero]
    simp only [partEntropyRate, e]
  · rintro _ ⟨m, Q, hQ, rfl⟩
    exact partEntropyRate_le_entropy hinv hQ

/-- `sec:entropies`, tex lines 1877 to 1884: the Kolmogorov–Sinai entropy of an invariant
probability measure on the two-sided shift over a finite alphabet, the supremum over finite Borel
partitions, is `lim_n n⁻¹ H_μ(𝒫_0^{n-1})`, the entropy rate `entropy μ` of the library. -/
theorem ksEntropy_shift_eq_entropy (hinv : MeasurePreserving (shift 1) μ μ) :
    ksEntropy μ (shift 1) = entropy μ :=
  (isGreatest_partEntropyRate hinv).csSup_eq

/-- The Shannon–McMillan–Breiman theorem as `sec:entropies` states it (tex lines 1885 to 1889),
with `h(μ)` the Kolmogorov–Sinai entropy, the supremum over finite Borel partitions: for an
ergodic `μ`, `h(μ) = -lim_n n⁻¹ log μ(𝒫_0^{n-1}(𝐢))` for `μ`-almost every `𝐢`. -/
theorem tendsto_neg_log_cylinder_ksEntropy (herg : Ergodic (shift 1) μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => -Real.log (μ.real (cylinder (block n x))) / n) atTop
      (𝓝 (ksEntropy μ (shift 1))) := by
  rw [ksEntropy_shift_eq_entropy herg.toMeasurePreserving]
  exact tendsto_neg_log_cylinder_entropy herg

end Generator

end BoxLike
