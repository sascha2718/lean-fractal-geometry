module

/-
The natural extension of an invariant measure of the one-sided shift, `sec:two_sided_shift_space`
(tex lines 755 to 769): every `μ^+ ∈ ℳ_σ(Σ^+)` is `η_*μ` for a unique `μ ∈ ℳ_σ(Σ)`, so that
`η_* : ℳ_σ(Σ) → ℳ_σ(Σ^+)` is a bijection, and it preserves ergodicity in both directions.

The alphabet `ι` is finite with the discrete `σ`-algebra. The measure `μ` is the Carathéodory
extension of the content `μ((η ∘ σ^{-m})^{-1} B) = μ^+(B)` on the algebra of the sets
`(η ∘ σ^{-m})^{-1} B` with `B ⊆ Σ^+` clopen, which contains the cylinders `[i_k ⋯ i_ℓ]` of the
article. The content is `σ`-additive since `Σ` is compact and the sets of the algebra are closed.

* `padFrom`, `etaFrom_padFrom_add`, `etaFrom_surjective`: a section of `η ∘ σ^{-m}`.
* `etaFrom_shift_one`, `etaFrom_zero`: `(η ∘ σ^{-m}) ∘ σ = σ^+ ∘ (η ∘ σ^{-m})` and
  `η ∘ σ^0 = η`.
* `futureFun`, `futureFun_preimage_etaFrom`, `futureFun_union`: the set function
  `μ((η ∘ σ^{-m})^{-1} B) = μ^+(B)`; it is well defined and finitely additive on `futureSets`
  for an arbitrary measurable alphabet.
* `clopenFutureSets`, `isSetAlgebra_clopenFutureSets`, `generateFrom_clopenFutureSets`: the
  algebra of the sets `(η ∘ σ^{-m})^{-1} B` with `B` clopen; it generates the `σ`-algebra of `Σ`.
* `futureContent`, `isSigmaSubadditive_futureContent`: the content on this algebra and its
  `σ`-subadditivity over a finite alphabet.
* `exists_isFiniteMeasure_map_eta_eq`, `exists_map_eta_eq`: `η_*` is surjective.
* `existsUnique_map_eta_eq`: `η_*` is bijective.
* `ergodic_of_map_eta_eq`, `exists_ergodic_map_eta_eq`: the extension of an ergodic measure is
  ergodic.
* `mapEtaEquiv`, `ergodic_mapEtaEquiv_iff`, `ergodic_mapEtaEquiv_symm_iff`: the bijection
  `η_* : ℳ_σ(Σ) ≃ ℳ_σ(Σ^+)`.
-/
public import BoxLike.CodingTopology
public import Mathlib.MeasureTheory.OuterMeasure.OfAddContent

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-! ### A section of the map `𝐢 ↦ (i_k)_{k ≥ -m}` -/

section Pad

variable {α : Type*}

/-- A section `Σ^+ → Σ` of the map `η ∘ σ^{-m}`: the sequence `y` occupies the coordinates
`k ≥ -m`, and the coordinates `k < -m` repeat the symbol `y 0`. It plays the role of the embedding
`e` of tex line 723, without a padding symbol. -/
def padFrom (m : ℕ) (y : ℕ → α) : ℤ → α := fun k => y ((m : ℤ) + k).toNat

/-- The coordinates `k ≥ -m` of the sequence `y` placed at the coordinates `k ≥ -(m + j)` are
`(σ^+)^j y`. -/
theorem etaFrom_padFrom_add (m j : ℕ) (y : ℕ → α) :
    etaFrom m (padFrom (m + j) y) = shiftPlus^[j] y := by
  funext k
  rw [iterate_shiftPlus_apply]
  simp only [etaFrom, padFrom]
  congr 1
  omega

/-- The map `padFrom m` is a section of `η ∘ σ^{-m}`. -/
@[simp] theorem etaFrom_padFrom (m : ℕ) (y : ℕ → α) : etaFrom m (padFrom m y) = y :=
  etaFrom_padFrom_add m 0 y

/-- The map `η ∘ σ^{-m}` is surjective. -/
theorem etaFrom_surjective (m : ℕ) : Function.Surjective (etaFrom m : (ℤ → α) → ℕ → α) :=
  fun y => ⟨padFrom m y, etaFrom_padFrom m y⟩

/-- `(η ∘ σ^{-m}) ∘ σ = σ^+ ∘ (η ∘ σ^{-m})`, the identity `η ∘ σ = σ^+ ∘ η` of tex line 730 at
the coordinates `k ≥ -m`. -/
theorem etaFrom_shift_one (m : ℕ) (x : ℤ → α) :
    etaFrom m (shift 1 x) = shiftPlus (etaFrom m x) := by
  funext k
  simp only [etaFrom, shift_apply, shiftPlus_apply]
  congr 1
  push_cast
  ring

/-- `η ∘ σ^0 = η`. -/
theorem etaFrom_zero : (etaFrom 0 : (ℤ → α) → ℕ → α) = eta := by
  funext x k
  simp [etaFrom]

/-- The section `padFrom m` is measurable. -/
theorem measurable_padFrom [MeasurableSpace α] (m : ℕ) :
    Measurable (padFrom m : (ℕ → α) → ℤ → α) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- The map `η ∘ σ^{-m}` is continuous. -/
theorem continuous_etaFrom [TopologicalSpace α] (m : ℕ) :
    Continuous (etaFrom m : (ℤ → α) → ℕ → α) :=
  continuous_pi fun _ => continuous_apply _

end Pad

/-! ### The premeasure of the natural extension -/

section Content

variable {α : Type*} [MeasurableSpace α] {ν : Measure (ℕ → α)}

/-- The set function `μ([i_k ⋯ i_ℓ]) = μ^+(\{j_0 = i_k, …, j_{ℓ-k} = i_ℓ\})` of tex lines 756 and
838, as the limit of the measures `(padFrom j)_*μ^+`. On a set `(η ∘ σ^{-m})^{-1} B` the sequence
is constant from `j = m` on, and the value is `μ^+(B)`; see `futureFun_preimage_etaFrom`. -/
noncomputable def futureFun (ν : Measure (ℕ → α)) (s : Set (ℤ → α)) : ℝ≥0∞ :=
  limsup (fun j => ν (padFrom j ⁻¹' s)) atTop

/-- The set function `futureFun` takes the eventual value of the sequence that defines it. -/
theorem futureFun_eq_of_eventually_eq {s : Set (ℤ → α)} {c : ℝ≥0∞}
    (h : ∀ᶠ j in atTop, ν (padFrom j ⁻¹' s) = c) : futureFun ν s = c := by
  rw [futureFun, limsup_congr h, limsup_const]

/-- For a `σ^+`-invariant measure `μ^+` and `j ≥ m`, the measure `(padFrom j)_*μ^+` of the set
`(η ∘ σ^{-m})^{-1} B` is `μ^+(B)`. -/
theorem measure_preimage_padFrom (hν : MeasurePreserving shiftPlus ν ν) {m j : ℕ} (hmj : m ≤ j)
    {B : Set (ℕ → α)} (hB : MeasurableSet B) :
    ν (padFrom j ⁻¹' (etaFrom m ⁻¹' B)) = ν B := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hmj
  rw [← (hν.iterate i).measure_preimage hB.nullMeasurableSet]
  congr 1
  ext y
  simp only [mem_preimage, etaFrom_padFrom_add]

/-- The set function of tex lines 756 and 757 is well defined: its value at
`(η ∘ σ^{-m})^{-1} B` is `μ^+(B)`, whatever the representation of the set. This uses the
invariance of `μ^+`. -/
theorem futureFun_preimage_etaFrom (hν : MeasurePreserving shiftPlus ν ν) (m : ℕ)
    {B : Set (ℕ → α)} (hB : MeasurableSet B) : futureFun ν (etaFrom m ⁻¹' B) = ν B :=
  futureFun_eq_of_eventually_eq <|
    (eventually_ge_atTop m).mono fun _ hj => measure_preimage_padFrom hν hj hB

/-- The set function of tex lines 756 and 757 vanishes at the empty set. -/
@[simp] theorem futureFun_empty (ν : Measure (ℕ → α)) : futureFun ν ∅ = 0 :=
  futureFun_eq_of_eventually_eq <| Eventually.of_forall fun _ => by simp

/-- The set function of tex lines 756 and 757 is finitely additive on the algebra of the sets
that depend on the coordinates `k ≥ -m` for some `m`. -/
theorem futureFun_union (hν : MeasurePreserving shiftPlus ν ν) {s t : Set (ℤ → α)}
    (hs : s ∈ futureSets α) (ht : t ∈ futureSets α) (hst : Disjoint s t) :
    futureFun ν (s ∪ t) = futureFun ν s + futureFun ν t := by
  obtain ⟨m, B, hB, rfl⟩ := hs
  obtain ⟨m', B', hB', rfl⟩ := ht
  rw [futureFun_preimage_etaFrom hν m hB, futureFun_preimage_etaFrom hν m' hB']
  refine futureFun_eq_of_eventually_eq ((eventually_ge_atTop (max m m')).mono fun j hj => ?_)
  rw [preimage_union, measure_union (hst.preimage _)
    (measurable_padFrom j (measurable_etaFrom m' hB')),
    measure_preimage_padFrom hν ((le_max_left m m').trans hj) hB,
    measure_preimage_padFrom hν ((le_max_right m m').trans hj) hB']

end Content

/-! ### The algebra of clopen sets that depend on the coordinates `k ≥ -m` -/

section Clopen

variable {α : Type*} [TopologicalSpace α]

variable (α) in
/-- The sets `(η ∘ σ^{-m})^{-1} B` with `m ∈ ℕ` and `B ⊆ Σ^+` clopen. For a discrete alphabet
they contain the cylinders `[i_k ⋯ i_ℓ]` of tex line 721, and over a finite alphabet they are the
finite unions of cylinders. -/
def clopenFutureSets : Set (Set (ℤ → α)) :=
  {C | ∃ (m : ℕ) (B : Set (ℕ → α)), IsClopen B ∧ C = etaFrom m ⁻¹' B}

/-- The sets of `clopenFutureSets` are clopen. -/
theorem isClopen_of_mem_clopenFutureSets {s : Set (ℤ → α)} (hs : s ∈ clopenFutureSets α) :
    IsClopen s := by
  obtain ⟨m, B, hB, rfl⟩ := hs
  exact hB.preimage (continuous_etaFrom m)

/-- The sets `(η ∘ σ^{-m})^{-1} B` with `B` clopen form an algebra of sets. -/
theorem isSetAlgebra_clopenFutureSets : IsSetAlgebra (clopenFutureSets α) where
  empty_mem := ⟨0, ∅, isClopen_empty, rfl⟩
  compl_mem := by
    rintro _ ⟨m, B, hB, rfl⟩
    exact ⟨m, Bᶜ, hB.compl, rfl⟩
  union_mem := by
    rintro _ _ ⟨m₁, B₁, hB₁, rfl⟩ ⟨m₂, B₂, hB₂, rfl⟩
    refine ⟨m₁ + m₂, shiftPlus^[m₂] ⁻¹' B₁ ∪ shiftPlus^[m₁] ⁻¹' B₂,
      (hB₁.preimage (continuous_shiftPlus.iterate m₂)).union
        (hB₂.preimage (continuous_shiftPlus.iterate m₁)), ?_⟩
    ext x
    rw [mem_union, mem_preimage, mem_preimage, etaFrom_eq_iterate m₁ m₂ x,
      etaFrom_eq_iterate m₂ m₁ x, Nat.add_comm m₂ m₁]
    rfl

variable [MeasurableSpace α]

/-- A clopen set that depends on the coordinates `k ≥ -m` belongs to the algebra `futureSets`. -/
theorem clopenFutureSets_subset_futureSets [OpensMeasurableSpace (ℕ → α)] :
    clopenFutureSets α ⊆ futureSets α := by
  rintro _ ⟨m, B, hB, rfl⟩
  exact ⟨m, B, hB.isOpen.measurableSet, rfl⟩

variable [DiscreteTopology α] [MeasurableSingletonClass α]

/-- For a countable discrete alphabet the sets `(η ∘ σ^{-m})^{-1} B` with `B` clopen generate the
product `σ`-algebra of `Σ`. -/
theorem generateFrom_clopenFutureSets [Countable α] :
    MeasurableSpace.generateFrom (clopenFutureSets α) =
      (inferInstance : MeasurableSpace (ℤ → α)) := by
  refine le_antisymm (MeasurableSpace.generateFrom_le fun s hs => ?_) ?_
  · exact (isClopen_of_mem_clopenFutureSets hs).isOpen.measurableSet
  · refine iSup_le fun k => ?_
    rintro _ ⟨T, -, rfl⟩
    refine MeasurableSpace.measurableSet_generateFrom
      ⟨k.natAbs, (fun y : ℕ → α => y (k + k.natAbs).toNat) ⁻¹' T,
        (isClopen_discrete T).preimage (continuous_apply _), ?_⟩
    ext x
    have h : -(k.natAbs : ℤ) + ((k + k.natAbs).toNat : ℤ) = k := by omega
    change x k ∈ T ↔ x (-(k.natAbs : ℤ) + ((k + k.natAbs).toNat : ℤ)) ∈ T
    rw [h]

/-- For a countable discrete alphabet the clopen sets generate the product `σ`-algebra of
`Σ^+`. -/
theorem generateFrom_isClopen_oneSided [Countable α] :
    MeasurableSpace.generateFrom {B : Set (ℕ → α) | IsClopen B} =
      (inferInstance : MeasurableSpace (ℕ → α)) := by
  refine le_antisymm (MeasurableSpace.generateFrom_le fun B hB => ?_) ?_
  · exact (show IsClopen B from hB).isOpen.measurableSet
  · refine iSup_le fun k => ?_
    rintro _ ⟨T, -, rfl⟩
    exact MeasurableSpace.measurableSet_generateFrom
      ((isClopen_discrete T).preimage (continuous_apply k))

variable {ν : Measure (ℕ → α)}

/-- The content `μ((η ∘ σ^{-m})^{-1} B) = μ^+(B)` of tex lines 756 and 757 on the algebra of the
sets `(η ∘ σ^{-m})^{-1} B` with `B` clopen. -/
noncomputable def futureContent [Countable α] (hν : MeasurePreserving shiftPlus ν ν) :
    AddContent ℝ≥0∞ (clopenFutureSets α) :=
  isSetAlgebra_clopenFutureSets.isSetRing.addContent_of_union (futureFun ν) (futureFun_empty ν)
    fun hs ht hst => futureFun_union hν (clopenFutureSets_subset_futureSets hs)
      (clopenFutureSets_subset_futureSets ht) hst

/-- The content of tex lines 756 and 757 at `(η ∘ σ^{-m})^{-1} B` is `μ^+(B)`. -/
theorem futureContent_apply [Countable α] (hν : MeasurePreserving shiftPlus ν ν) (m : ℕ)
    {B : Set (ℕ → α)} (hB : IsClopen B) : futureContent hν (etaFrom m ⁻¹' B) = ν B :=
  futureFun_preimage_etaFrom hν m hB.isOpen.measurableSet

/-- Over a finite alphabet the content of tex lines 756 and 757 is `σ`-subadditive. The space `Σ`
is compact and the sets of the algebra are closed, so a decreasing sequence of them with empty
intersection is eventually empty; the content is therefore continuous at `∅`. This is the
hypothesis of the Hahn–Kolmogorov extension theorem of tex line 758. -/
theorem isSigmaSubadditive_futureContent [Finite α] [IsFiniteMeasure ν]
    (hν : MeasurePreserving shiftPlus ν ν) : (futureContent hν).IsSigmaSubadditive := by
  have hC := (isSetAlgebra_clopenFutureSets (α := α)).isSetRing
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum hC fun f hf hUf hdisj =>
    addContent_iUnion_eq_sum_of_tendsto_zero hC _ ?_ ?_ hf hUf hdisj
  · rintro _ ⟨m, B, hB, rfl⟩
    rw [futureContent_apply hν m hB]
    exact measure_ne_top ν B
  · intro s hs hanti hempty
    obtain ⟨n, hn⟩ : ∃ n, s n = ∅ := by
      by_contra hne
      push Not at hne
      have h := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed s
        (fun i => hanti (Nat.le_succ i)) hne
        (isClopen_of_mem_clopenFutureSets (hs 0)).isClosed.isCompact
        fun i => (isClopen_of_mem_clopenFutureSets (hs i)).isClosed
      rw [hempty] at h
      exact not_nonempty_empty h
    refine tendsto_atTop_of_eventually_const (i₀ := n) fun i hi => ?_
    have hi' : s i = ∅ := subset_empty_iff.1 (hn ▸ hanti hi)
    rw [hi', addContent_empty]

end Clopen

/-! ### The push-forward `η_*` is a bijection -/

section Extension

variable {ι : Type*} [Finite ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Every finite `σ^+`-invariant measure `μ^+` on `Σ^+` over a finite alphabet is `η_*μ` for a
finite `σ`-invariant measure `μ` on `Σ` (tex lines 755 to 765). The measure `μ` is the
Carathéodory extension of the content `μ((η ∘ σ^{-m})^{-1} B) = μ^+(B)`, `B` clopen. -/
theorem exists_isFiniteMeasure_map_eta_eq {ν : Measure (ℕ → ι)} [IsFiniteMeasure ν]
    (hν : MeasurePreserving shiftPlus ν ν) :
    ∃ μ : Measure (ℤ → ι), IsFiniteMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
      μ.map eta = ν := by
  let : TopologicalSpace ι := ⊥
  have : DiscreteTopology ι := ⟨rfl⟩
  have hC := (isSetAlgebra_clopenFutureSets (α := ι)).isSetRing
  set μ : Measure (ℤ → ι) := (futureContent hν).measure hC.isSetSemiring
    generateFrom_clopenFutureSets.ge (isSigmaSubadditive_futureContent hν) with hμdef
  have hμ : ∀ (m : ℕ) {B : Set (ℕ → ι)}, IsClopen B → μ (etaFrom m ⁻¹' B) = ν B := by
    intro m B hB
    rw [hμdef, AddContent.measure_eq _ _ generateFrom_clopenFutureSets.symm _ ⟨m, B, hB, rfl⟩,
      futureContent_apply hν m hB]
  have huniv : μ univ = ν univ := by
    simpa using hμ 0 isClopen_univ
  have : IsFiniteMeasure μ := ⟨by rw [huniv]; exact measure_lt_top ν univ⟩
  refine ⟨μ, inferInstance, ⟨measurable_shift 1, ?_⟩, ?_⟩
  · refine ext_of_generate_finite (clopenFutureSets ι) generateFrom_clopenFutureSets.symm
      (fun s hs t ht _ => isSetAlgebra_clopenFutureSets.inter_mem hs ht) ?_ ?_
    · rintro _ ⟨m, B, hB, rfl⟩
      have hpre : shift 1 ⁻¹' (etaFrom m ⁻¹' B) = etaFrom m ⁻¹' (shiftPlus ⁻¹' B) := by
        ext x
        simp only [mem_preimage, etaFrom_shift_one]
      rw [Measure.map_apply (measurable_shift 1) (measurable_etaFrom m hB.isOpen.measurableSet),
        hpre, hμ m (hB.preimage continuous_shiftPlus), hμ m hB,
        hν.measure_preimage hB.isOpen.measurableSet.nullMeasurableSet]
    · rw [Measure.map_apply (measurable_shift 1) MeasurableSet.univ, preimage_univ]
  · refine ext_of_generate_finite {B : Set (ℕ → ι) | IsClopen B}
      generateFrom_isClopen_oneSided.symm (fun s hs t ht _ => IsClopen.inter hs ht) ?_ ?_
    · intro B hB
      have hB' : IsClopen B := hB
      rw [Measure.map_apply measurable_eta hB'.isOpen.measurableSet, ← etaFrom_zero, hμ 0 hB']
    · rw [Measure.map_apply measurable_eta MeasurableSet.univ, preimage_univ, huniv]

/-- The push-forward `η_* : ℳ_σ(Σ) → ℳ_σ(Σ^+)` is surjective (tex lines 755 to 765): every
`σ^+`-invariant Borel probability measure `μ^+` on `Σ^+` is `η_*μ` for a `σ`-invariant Borel
probability measure `μ` on `Σ`. -/
theorem exists_map_eta_eq {ν : Measure (ℕ → ι)} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving shiftPlus ν ν) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
      μ.map eta = ν := by
  obtain ⟨μ, -, hinv, hmap⟩ := exists_isFiniteMeasure_map_eta_eq hν
  refine ⟨μ, ⟨?_⟩, hinv, hmap⟩
  rw [← preimage_univ (f := eta), ← Measure.map_apply measurable_eta MeasurableSet.univ, hmap,
    measure_univ]

/-- The push-forward `η_* : ℳ_σ(Σ) → ℳ_σ(Σ^+)` is bijective (tex lines 765 and 766): every
`μ^+ ∈ ℳ_σ(Σ^+)` is `η_*μ` for exactly one `μ ∈ ℳ_σ(Σ)`. -/
theorem existsUnique_map_eta_eq {ν : Measure (ℕ → ι)} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving shiftPlus ν ν) :
    ∃! μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
      μ.map eta = ν := by
  obtain ⟨μ, hμ, hinv, hmap⟩ := exists_map_eta_eq hν
  refine ⟨μ, ⟨hμ, hinv, hmap⟩, ?_⟩
  rintro μ' ⟨hμ', hinv', hmap'⟩
  exact map_eta_injective hinv' hinv (hmap'.trans hmap.symm)

omit [Finite ι] [MeasurableSingletonClass ι] in
/-- An invariant measure `μ` on `Σ` whose image `η_*μ = μ^+` is ergodic is ergodic (tex lines 767
and 849). -/
theorem ergodic_of_map_eta_eq {μ : Measure (ℤ → ι)} [IsFiniteMeasure μ] {ν : Measure (ℕ → ι)}
    (hμ : MeasurePreserving (shift 1) μ μ) (hmap : μ.map eta = ν) (hν : Ergodic shiftPlus ν) :
    Ergodic (shift 1) μ := by
  subst hmap
  exact (ergodic_map_eta_iff hμ).1 hν

/-- Every ergodic `μ^+ ∈ ℳ_σ(Σ^+)` is `η_*μ` for an ergodic `μ ∈ ℳ_σ(Σ)` (tex lines 765 to
849). -/
theorem exists_ergodic_map_eta_eq {ν : Measure (ℕ → ι)} [IsProbabilityMeasure ν]
    (hν : Ergodic shiftPlus ν) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ Ergodic (shift 1) μ ∧ μ.map eta = ν := by
  obtain ⟨μ, hμ, hinv, hmap⟩ := exists_map_eta_eq hν.toMeasurePreserving
  exact ⟨μ, hμ, ergodic_of_map_eta_eq hinv hmap hν, hmap⟩

variable (ι) in
/-- The bijection `η_* : ℳ_σ(Σ) → ℳ_σ(Σ^+)` of tex lines 765 and 766 between the invariant Borel
probability measures of the two-sided and of the one-sided full shift. Its inverse sends `μ^+`
to the measure `μ = (η_*)^{-1}μ^+` of tex line 769. -/
noncomputable def mapEtaEquiv :
    {μ : Measure (ℤ → ι) // IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ} ≃
      {ν : Measure (ℕ → ι) // IsProbabilityMeasure ν ∧ MeasurePreserving shiftPlus ν ν} :=
  Equiv.ofBijective
    (fun μ => ⟨μ.1.map eta, by
      have := μ.2.1
      infer_instance,
      measurePreserving_shiftPlus_map_eta μ.2.2⟩)
    ⟨fun μ μ' h => by
      have := μ.2.1
      exact Subtype.ext (map_eta_injective μ.2.2 μ'.2.2 (congrArg Subtype.val h)),
    fun ν => by
      have := ν.2.1
      obtain ⟨μ, hμ, hinv, hmap⟩ := exists_map_eta_eq ν.2.2
      exact ⟨⟨μ, hμ, hinv⟩, Subtype.ext hmap⟩⟩

/-- The bijection `mapEtaEquiv` is the push-forward `η_*`. -/
@[simp] theorem coe_mapEtaEquiv_apply
    (μ : {μ : Measure (ℤ → ι) // IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ}) :
    (mapEtaEquiv ι μ : Measure (ℕ → ι)) = (μ : Measure (ℤ → ι)).map eta := rfl

/-- The inverse of `mapEtaEquiv` is a right inverse of `η_*`: `η_*((η_*)^{-1}μ^+) = μ^+`. -/
@[simp] theorem map_eta_mapEtaEquiv_symm
    (ν : {ν : Measure (ℕ → ι) // IsProbabilityMeasure ν ∧ MeasurePreserving shiftPlus ν ν}) :
    ((mapEtaEquiv ι).symm ν : Measure (ℤ → ι)).map eta = ν := by
  rw [← coe_mapEtaEquiv_apply, Equiv.apply_symm_apply]

/-- `η_*μ` is ergodic if and only if `μ` is ergodic (tex lines 767 and 768), for the bijection
`mapEtaEquiv`. -/
theorem ergodic_mapEtaEquiv_iff
    (μ : {μ : Measure (ℤ → ι) // IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ}) :
    Ergodic shiftPlus (mapEtaEquiv ι μ : Measure (ℕ → ι)) ↔
      Ergodic (shift 1) (μ : Measure (ℤ → ι)) := by
  have := μ.2.1
  exact ergodic_map_eta_iff μ.2.2

/-- The measure `(η_*)^{-1}μ^+` is ergodic if and only if `μ^+` is ergodic (tex lines 767 to
850). -/
theorem ergodic_mapEtaEquiv_symm_iff
    (ν : {ν : Measure (ℕ → ι) // IsProbabilityMeasure ν ∧ MeasurePreserving shiftPlus ν ν}) :
    Ergodic (shift 1) ((mapEtaEquiv ι).symm ν : Measure (ℤ → ι)) ↔
      Ergodic shiftPlus (ν : Measure (ℕ → ι)) := by
  rw [← ergodic_mapEtaEquiv_iff, Equiv.apply_symm_apply]

end Extension

end BoxLike
