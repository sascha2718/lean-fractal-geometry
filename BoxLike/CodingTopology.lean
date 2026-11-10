module

/-
Topological and measure-theoretic claims about the coding maps that the article states without
a label: the natural projection `η : Σ → Σ^+` of `sec:two_sided_shift_space` (tex lines 727 to
853), the codings `τ`, `ω` of `sec:subshift` as homeomorphisms onto their images (tex lines 851
to 939), and the grouping map `β` of `sec:normalisation` as a homeomorphism that conjugates
`σ²` to the shift (tex lines 2196 and 2197).

The alphabet `ι` of the codings carries the discrete topology. The statements about `η` hold
for an arbitrary measurable alphabet `α`, with the product `σ`-algebra on `ℤ → α` and `ℕ → α`;
for a countable discrete alphabet this is the Borel `σ`-algebra (`borelSpace_twoSided`,
`borelSpace_oneSided`), so the measures are the Borel measures of the article.

* `continuous_unCode`, `isClosedEmbedding_tau`, `isClosedEmbedding_omega`, `isClosed_range_tau`,
  `isClosed_range_omega`, `isClosed_subshift`: `τ` and `ω` are closed embeddings, and `Σ_Z`,
  `τ(Σ)` and `ω(Σ)` are closed.
* `tauHomeomorph`, `omegaHomeomorph`: the homeomorphisms `Σ ≃ τ(Σ)` and `Σ ≃ ω(Σ)`, with
  inverses `\overline{τ}` and `\overline{ω}`, which are `unCode`.
* `ungroup`, `groupHomeomorph`, `groupHomeomorph_shift_two`: `β` is a homeomorphism with
  `β ∘ σ² = σ^(2) ∘ β`.
* `eta`, `shiftPlus`, `eta_shift`, `continuous_eta`, `measurable_eta`, `eta_surjective`: the
  natural projection `η`, the one-sided shift `σ^+` and `η ∘ σ = σ^+ ∘ η`.
* `embed`, `eta_embed`, `isClosedEmbedding_embed`, `embed_comp_shiftPlus_ne`: the embedding
  `e : Σ^+ → Σ`, which is not a conjugacy when `N ≥ 2`.
* `measurePreserving_shiftPlus_map_eta`: `η_*μ` is `σ^+`-invariant when `μ` is `σ`-invariant.
* `etaFrom`, `futureSets`, `isSetAlgebra_futureSets`, `generateFrom_futureSets`,
  `measure_preimage_etaFrom`: the algebra of the sets that depend on the coordinates `k ≥ -m`
  for some `m`; it generates the product `σ`-algebra, and an invariant measure `μ` is
  determined on it by `η_*μ`.
* `map_eta_injective`: `η_*` is injective on the finite invariant measures.
* `exists_preimage_eta_ae_eq`: a `σ`-invariant set is `η^{-1}(B)` up to a null set.
* `ergodic_map_eta_iff`: `η_*μ` is ergodic if and only if `μ` is.
-/
public import BoxLike.Attractor
public import BoxLike.Entropy
public import BoxLike.Grouping
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set
open scoped symmDiff

/-! ### The codings `τ` and `ω` are homeomorphisms onto their images -/

section Coding

variable {ι : Type*} [TopologicalSpace ι]

/-- The common inverse `\overline{τ}`, `\overline{ω}` of the codings is continuous: it leaves the
symbols `i ≤ N` unchanged and sends each symbol `i > N` to `i - N` (tex lines 856 to 858). -/
theorem continuous_unCode : Continuous (unCode : (ℤ → ι × ZMod 2) → ℤ → ι) :=
  continuous_pi fun n => continuous_fst.comp (continuous_apply n)

variable [DiscreteTopology ι] (o : ι → ZMod 2)

/-- The coding `τ` is a homeomorphism onto its image, and the image is closed (tex lines 856
to 939). -/
theorem isClosedEmbedding_tau : IsClosedEmbedding (tau o) :=
  Function.LeftInverse.isClosedEmbedding (f := unCode) unCode_tau continuous_unCode
    (System.continuous_tau o)

/-- The coding `ω` is a homeomorphism onto its image, and the image is closed (tex lines 856
to 939). -/
theorem isClosedEmbedding_omega : IsClosedEmbedding (omega o) :=
  Function.LeftInverse.isClosedEmbedding (f := unCode) unCode_omega continuous_unCode
    (System.continuous_omega o)

/-- The set `τ(Σ) = ⋃_{i ≤ N} [i]` of tex line 853 is closed. -/
theorem isClosed_range_tau : IsClosed (Set.range (tau o)) :=
  (isClosedEmbedding_tau o).isClosed_range

/-- The set `ω(Σ) = ⋃_{i > N} [i]` of tex line 853 is closed. -/
theorem isClosed_range_omega : IsClosed (Set.range (omega o)) :=
  (isClosedEmbedding_omega o).isClosed_range

/-- The sub-shift `Σ_Z = τ(Σ) ∪ ω(Σ)` of `eq:tau_omega_partition` is closed. -/
theorem isClosed_subshift : IsClosed (subshift o) := by
  rw [← range_tau_union_range_omega]
  exact (isClosed_range_tau o).union (isClosed_range_omega o)

/-- The homeomorphism `τ : Σ → τ(Σ)` of tex lines 856 to 858; its inverse is
`\overline{τ} = unCode`. -/
def tauHomeomorph : (ℤ → ι) ≃ₜ Set.range (tau o) where
  toFun x := ⟨tau o x, Set.mem_range_self x⟩
  invFun y := unCode y.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨_, x, rfl⟩
    rfl
  continuous_toFun := (System.continuous_tau o).subtype_mk _
  continuous_invFun := continuous_unCode.comp continuous_subtype_val

/-- The homeomorphism `ω : Σ → ω(Σ)` of tex lines 856 to 858; its inverse is
`\overline{ω} = unCode`. -/
def omegaHomeomorph : (ℤ → ι) ≃ₜ Set.range (omega o) where
  toFun x := ⟨omega o x, Set.mem_range_self x⟩
  invFun y := unCode y.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨_, x, rfl⟩
    rfl
  continuous_toFun := (System.continuous_omega o).subtype_mk _
  continuous_invFun := continuous_unCode.comp continuous_subtype_val

variable {o}

/-- The homeomorphism `tauHomeomorph` is the coding `τ`. -/
@[simp] theorem coe_tauHomeomorph (x : ℤ → ι) : (tauHomeomorph o x : ℤ → ι × ZMod 2) = tau o x :=
  rfl

/-- The inverse of `tauHomeomorph` is `\overline{τ} = unCode`. -/
@[simp] theorem tauHomeomorph_symm_apply (y : Set.range (tau o)) :
    (tauHomeomorph o).symm y = unCode y.1 := rfl

/-- The homeomorphism `omegaHomeomorph` is the coding `ω`. -/
@[simp] theorem coe_omegaHomeomorph (x : ℤ → ι) :
    (omegaHomeomorph o x : ℤ → ι × ZMod 2) = omega o x := rfl

/-- The inverse of `omegaHomeomorph` is `\overline{ω} = unCode`. -/
@[simp] theorem omegaHomeomorph_symm_apply (y : Set.range (omega o)) :
    (omegaHomeomorph o).symm y = unCode y.1 := rfl

end Coding

/-! ### The product `σ`-algebra is the Borel `σ`-algebra -/

section Borel

variable (ι : Type*) [TopologicalSpace ι] [DiscreteTopology ι] [Countable ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

/-- For a countable discrete alphabet the product `σ`-algebra of `Σ` is the Borel `σ`-algebra of
the product topology, so the measures on `Σ` are the Borel measures of tex line 745. -/
theorem borelSpace_twoSided : BorelSpace (ℤ → ι) := inferInstance

/-- For a countable discrete alphabet the product `σ`-algebra of `Σ^+` is the Borel `σ`-algebra
of the product topology. -/
theorem borelSpace_oneSided : BorelSpace (ℕ → ι) := inferInstance

end Borel

/-! ### The grouping map `β` is a homeomorphism -/

section Group

variable {α : Type*}

/-- The inverse of the grouping map `β` of `sec:normalisation`: the symbol at time `k` is the
first or the second entry of the pair at time `⌊k / 2⌋`, according to the parity of `k`. -/
def ungroup (y : ℤ → α × α) : ℤ → α := fun k => if k % 2 = 0 then (y (k / 2)).1 else (y (k / 2)).2

/-- `β^{-1} ∘ β` is the identity. -/
@[simp] theorem ungroup_group (x : ℤ → α) : ungroup (group x) = x := by
  funext k
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · simp only [ungroup, h, ite_true, group_apply]
    congr 1
    omega
  · simp only [ungroup, h, one_ne_zero, ite_false, group_apply]
    congr 1
    omega

/-- `β ∘ β^{-1}` is the identity. -/
@[simp] theorem group_ungroup (y : ℤ → α × α) : group (ungroup y) = y := by
  funext n
  have h0 : (2 * n) % 2 = 0 := by omega
  have h1 : (2 * n + 1) % 2 ≠ 0 := by omega
  have h2 : 2 * n / 2 = n := by omega
  have h3 : (2 * n + 1) / 2 = n := by omega
  simp only [group_apply, ungroup, h0, h1, h2, h3, ite_true, ite_false]

variable [TopologicalSpace α]

/-- The grouping map `β` is continuous. -/
theorem continuous_group : Continuous (group : (ℤ → α) → ℤ → α × α) :=
  continuous_pi fun n => (continuous_apply (2 * n)).prodMk (continuous_apply (2 * n + 1))

/-- The inverse of the grouping map `β` is continuous. -/
theorem continuous_ungroup : Continuous (ungroup : (ℤ → α × α) → ℤ → α) := by
  refine continuous_pi fun k => ?_
  by_cases h : k % 2 = 0
  · simp only [ungroup, h, ite_true]
    exact continuous_fst.comp (continuous_apply _)
  · simp only [ungroup, h, ite_false]
    exact continuous_snd.comp (continuous_apply _)

/-- The grouping map `β` of `sec:normalisation` is a homeomorphism (tex line 2196). -/
def groupHomeomorph : (ℤ → α) ≃ₜ (ℤ → α × α) where
  toFun := group
  invFun := ungroup
  left_inv := ungroup_group
  right_inv := group_ungroup
  continuous_toFun := continuous_group
  continuous_invFun := continuous_ungroup

/-- The homeomorphism `groupHomeomorph` is the grouping map `β`. -/
@[simp] theorem coe_groupHomeomorph :
    (groupHomeomorph : (ℤ → α) → ℤ → α × α) = group := rfl

/-- The inverse of `groupHomeomorph` is `ungroup`. -/
@[simp] theorem coe_groupHomeomorph_symm :
    ((groupHomeomorph (α := α)).symm : (ℤ → α × α) → ℤ → α) = ungroup := rfl

/-- The homeomorphism `β` conjugates `σ²` to the shift `σ^(2)` of the paired alphabet:
`β ∘ σ² = σ^(2) ∘ β` (tex line 2197). -/
theorem groupHomeomorph_shift_two :
    (groupHomeomorph : (ℤ → α) → ℤ → α × α) ∘ shift 2 = shift 1 ∘ groupHomeomorph :=
  funext group_shift_two

end Group

/-! ### The natural projection `η` and the one-sided shift -/

section Eta

variable {α : Type*}

/-- The natural projection `η : Σ → Σ^+`, `η(𝐢) = 𝐢^+`, of tex line 729. -/
def eta (x : ℤ → α) : ℕ → α := fun k => x k

/-- The `k`-th symbol of `η(𝐢)` is `i_k`. -/
@[simp] theorem eta_apply (x : ℤ → α) (k : ℕ) : eta x k = x k := rfl

/-- The left shift `σ^+` of the one-sided full shift `Σ^+` of tex line 718. -/
def shiftPlus (y : ℕ → α) : ℕ → α := fun k => y (k + 1)

/-- The `k`-th symbol of `σ^+(𝐢)` is `i_{k+1}`. -/
@[simp] theorem shiftPlus_apply (y : ℕ → α) (k : ℕ) : shiftPlus y k = y (k + 1) := rfl

/-- The `k`-th symbol of `(σ^+)^j(𝐢)` is `i_{k+j}`. -/
theorem iterate_shiftPlus_apply (j : ℕ) (y : ℕ → α) (k : ℕ) :
    shiftPlus^[j] y k = y (k + j) := by
  induction j generalizing y with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply, ih, shiftPlus_apply, add_assoc]

/-- `η ∘ σ = σ^+ ∘ η` (tex line 730). -/
theorem eta_shift (x : ℤ → α) : eta (shift 1 x) = shiftPlus (eta x) := by
  funext k
  simp [add_comm]

/-- The natural projection `η` is surjective. -/
theorem eta_surjective : Function.Surjective (eta : (ℤ → α) → ℕ → α) := fun y =>
  ⟨fun k => y k.toNat, funext fun k => by simp⟩

/-- The embedding `e : Σ^+ → Σ`, `e(i_0 i_1 ⋯) = ⋯ a a i_0 i_1 ⋯`, of tex line 723, where the
article takes `a = 1`. -/
def embed (a : α) (y : ℕ → α) : ℤ → α := fun k => if 0 ≤ k then y k.toNat else a

/-- The embedding `e` is a section of `η`. -/
@[simp] theorem eta_embed (a : α) (y : ℕ → α) : eta (embed a y) = y := by
  funext k
  simp [embed]

/-- The maps `e ∘ σ^+` and `σ ∘ e` differ at every sequence whose symbol at time `0` is not the
padding symbol. -/
theorem embed_shiftPlus_ne {a : α} {y : ℕ → α} (h : y 0 ≠ a) :
    embed a (shiftPlus y) ≠ shift 1 (embed a y) := fun he =>
  h (by simpa [embed] using (congrFun he (-1)).symm)

/-- The embedding `e` is not a conjugacy, `e ∘ σ^+ ≠ σ ∘ e` (tex line 724), when the alphabet
has a symbol other than the padding symbol, that is, when `N ≥ 2`. -/
theorem embed_comp_shiftPlus_ne {a b : α} (h : b ≠ a) :
    embed a ∘ shiftPlus ≠ shift 1 ∘ embed a := fun he =>
  embed_shiftPlus_ne (y := fun _ => b) h (congrFun he _)

/-- The map `𝐢 ↦ (i_k)_{k ≥ -m}`, which is `η ∘ σ^{-m}`. -/
def etaFrom (m : ℕ) (x : ℤ → α) : ℕ → α := fun k => x (-(m : ℤ) + k)

/-- The map `𝐢 ↦ (i_k)_{k ≥ -m}` is `η ∘ σ^{-m}`. -/
theorem etaFrom_eq (m : ℕ) (x : ℤ → α) : etaFrom m x = eta (shift (-(m : ℤ)) x) := rfl

/-- `η ∘ σ^{-m} ∘ σ^m = η`. -/
theorem etaFrom_shift (m : ℕ) (x : ℤ → α) : etaFrom m (shift m x) = eta x := by
  funext k
  simp [etaFrom]

/-- The coordinates `k ≥ -m` are the coordinates `k ≥ -(m + j)` with the first `j` of them
removed. -/
theorem etaFrom_eq_iterate (m j : ℕ) (x : ℤ → α) :
    etaFrom m x = shiftPlus^[j] (etaFrom (m + j) x) := by
  funext k
  rw [iterate_shiftPlus_apply]
  simp only [etaFrom]
  congr 1
  push_cast
  ring

variable [TopologicalSpace α]

/-- The natural projection `η` is continuous. -/
theorem continuous_eta : Continuous (eta : (ℤ → α) → ℕ → α) :=
  continuous_pi fun k => continuous_apply (k : ℤ)

/-- The one-sided shift `σ^+` is continuous. -/
theorem continuous_shiftPlus : Continuous (shiftPlus : (ℕ → α) → ℕ → α) :=
  continuous_pi fun k => continuous_apply (k + 1)

/-- The embedding `e` is continuous. -/
theorem continuous_embed (a : α) : Continuous (embed a) := by
  refine continuous_pi fun k => ?_
  by_cases h : 0 ≤ k
  · simp only [embed, h, ite_true]
    exact continuous_apply _
  · simp only [embed, h, ite_false]
    exact continuous_const

/-- The embedding `e : Σ^+ → Σ` is injective and continuous, and it is a topological embedding
with closed image (tex lines 724 and 725). -/
theorem isClosedEmbedding_embed [T2Space α] (a : α) : IsClosedEmbedding (embed a) :=
  Function.LeftInverse.isClosedEmbedding (f := eta) (eta_embed a) continuous_eta
    (continuous_embed a)

end Eta

/-! ### Invariant measures on the two-sided and on the one-sided shift -/

section EtaMeasure

variable {α : Type*} [MeasurableSpace α]

/-- The natural projection `η` is measurable. -/
theorem measurable_eta : Measurable (eta : (ℤ → α) → ℕ → α) :=
  Measurable.of_eval fun k => measurable_pi_apply (k : ℤ)

/-- The one-sided shift `σ^+` is measurable. -/
theorem measurable_shiftPlus : Measurable (shiftPlus : (ℕ → α) → ℕ → α) :=
  Measurable.of_eval fun k => measurable_pi_apply (k + 1)

/-- If `μ ∈ ℳ_σ(Σ)`, then `η_*μ ∈ ℳ_σ(Σ^+)` (tex lines 749 to 755). -/
theorem measurePreserving_shiftPlus_map_eta {μ : Measure (ℤ → α)}
    (hμ : MeasurePreserving (shift 1) μ μ) :
    MeasurePreserving shiftPlus (μ.map eta) (μ.map eta) :=
  (measurable_eta.measurePreserving μ).of_semiconj hμ eta_shift measurable_shiftPlus

/-- The map `𝐢 ↦ (i_k)_{k ≥ -m}` is measurable. -/
theorem measurable_etaFrom (m : ℕ) : Measurable (etaFrom m : (ℤ → α) → ℕ → α) :=
  Measurable.of_eval fun k => measurable_pi_apply (-(m : ℤ) + k)

/-- The sets that depend on the coordinates `k ≥ -m` only, for some `m ∈ ℕ`. They contain the
cylinders `[i_k ⋯ i_ℓ]` of tex line 721. -/
def futureSets (α : Type*) [MeasurableSpace α] : Set (Set (ℤ → α)) :=
  {C | ∃ (m : ℕ) (B : Set (ℕ → α)), MeasurableSet B ∧ C = etaFrom m ⁻¹' B}

/-- A set that depends on the coordinates `k ≥ -m` depends on the coordinates `k ≥ -(m + j)`. -/
theorem exists_preimage_etaFrom_add (m j : ℕ) {B : Set (ℕ → α)} (hB : MeasurableSet B) :
    ∃ B' : Set (ℕ → α), MeasurableSet B' ∧ etaFrom m ⁻¹' B = etaFrom (m + j) ⁻¹' B' :=
  ⟨shiftPlus^[j] ⁻¹' B, measurable_shiftPlus.iterate j hB, by
    ext x
    simp only [mem_preimage, etaFrom_eq_iterate m j x]⟩

/-- The sets that depend on the coordinates `k ≥ -m` for some `m` form an algebra of sets. -/
theorem isSetAlgebra_futureSets : IsSetAlgebra (futureSets α) where
  empty_mem := ⟨0, ∅, MeasurableSet.empty, rfl⟩
  compl_mem := by
    rintro _ ⟨m, B, hB, rfl⟩
    exact ⟨m, Bᶜ, hB.compl, rfl⟩
  union_mem := by
    rintro _ _ ⟨m₁, B₁, hB₁, rfl⟩ ⟨m₂, B₂, hB₂, rfl⟩
    obtain ⟨B₁', hB₁', h₁⟩ := exists_preimage_etaFrom_add m₁ m₂ hB₁
    obtain ⟨B₂', hB₂', h₂⟩ := exists_preimage_etaFrom_add m₂ m₁ hB₂
    rw [Nat.add_comm m₂ m₁] at h₂
    exact ⟨m₁ + m₂, B₁' ∪ B₂', hB₁'.union hB₂', by rw [h₁, h₂, preimage_union]⟩

/-- The sets that depend on the coordinates `k ≥ -m` for some `m` generate the product
`σ`-algebra of `Σ`. -/
theorem generateFrom_futureSets :
    MeasurableSpace.generateFrom (futureSets α) = (inferInstance : MeasurableSpace (ℤ → α)) := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) ?_
  · rintro _ ⟨m, B, hB, rfl⟩
    exact measurable_etaFrom m hB
  · refine iSup_le fun k => ?_
    rintro _ ⟨T, hT, rfl⟩
    refine MeasurableSpace.measurableSet_generateFrom
      ⟨k.natAbs, (fun y : ℕ → α => y (k + k.natAbs).toNat) ⁻¹' T, measurable_pi_apply _ hT, ?_⟩
    ext x
    have h : -(k.natAbs : ℤ) + ((k + k.natAbs).toNat : ℤ) = k := by omega
    change x k ∈ T ↔ x (-(k.natAbs : ℤ) + ((k + k.natAbs).toNat : ℤ)) ∈ T
    rw [h]

/-- An invariant measure `μ` is determined on the sets that depend on the coordinates `k ≥ -m`
by `η_*μ`: `μ((η ∘ σ^{-m})^{-1} B) = η_*μ(B)`. -/
theorem measure_preimage_etaFrom {μ : Measure (ℤ → α)} (hμ : MeasurePreserving (shift 1) μ μ)
    (m : ℕ) {B : Set (ℕ → α)} (hB : MeasurableSet B) :
    μ (etaFrom m ⁻¹' B) = μ.map eta B := by
  rw [← (measurePreserving_shift_natCast hμ m).measure_preimage
    (measurable_etaFrom m hB).nullMeasurableSet, Measure.map_apply measurable_eta hB]
  congr 1
  ext x
  simp only [mem_preimage, etaFrom_shift]

/-- The push-forward `η_* : ℳ_σ(Σ) → ℳ_σ(Σ^+)` is injective (tex lines 765 and 766): two finite
invariant measures with the same image under `η` agree on the sets that depend on the
coordinates `k ≥ -m`, and these form a `π`-system that generates the `σ`-algebra. -/
theorem map_eta_injective {μ μ' : Measure (ℤ → α)} [IsFiniteMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) (hμ' : MeasurePreserving (shift 1) μ' μ')
    (h : μ.map eta = μ'.map eta) : μ = μ' := by
  refine ext_of_generate_finite (futureSets α) generateFrom_futureSets.symm
    (fun s hs t ht _ => isSetAlgebra_futureSets.inter_mem hs ht) ?_ ?_
  · rintro _ ⟨m, B, hB, rfl⟩
    rw [measure_preimage_etaFrom hμ m hB, measure_preimage_etaFrom hμ' m hB, h]
  · have h0 := measure_preimage_etaFrom hμ 0 MeasurableSet.univ
    have h0' := measure_preimage_etaFrom hμ' 0 MeasurableSet.univ
    rw [preimage_univ] at h0 h0'
    rw [h0, h0', h]

/-- A `σ`-invariant measurable set is, up to a null set of the finite invariant measure `μ`, the
preimage under `η` of a measurable subset of `Σ^+`. The set is approximated in measure by sets
that depend on the coordinates `k ≥ -m`; by invariance it is approximated by sets `η^{-1}(B_n)`,
and `B = limsup_n B_n` has the required property by the Borel–Cantelli lemma. -/
theorem exists_preimage_eta_ae_eq {μ : Measure (ℤ → α)} [IsFiniteMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) {A : Set (ℤ → α)} (hA : MeasurableSet A)
    (hinv : shift 1 ⁻¹' A = A) :
    ∃ B : Set (ℕ → α), MeasurableSet B ∧ A =ᵐ[μ] eta ⁻¹' B := by
  have hdense := Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite μ
    isSetAlgebra_futureSets generateFrom_futureSets.symm
  have happrox : ∀ n : ℕ, ∃ B : Set (ℕ → α), MeasurableSet B ∧
      μ (A ∆ (eta ⁻¹' B)) < ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
    intro n
    obtain ⟨_, ⟨m, B, hB, rfl⟩, hC⟩ :=
      hdense.approx A hA (measure_ne_top μ A) ((1 / 2 : ℝ) ^ n) (by positivity)
    refine ⟨B, hB, ?_⟩
    have hAm : shift (m : ℤ) ⁻¹' A = A := by
      rw [← iterate_shift_one]
      exact Function.IsFixedPt.preimage_iterate hinv m
    have hpre : shift (m : ℤ) ⁻¹' (A ∆ (etaFrom m ⁻¹' B)) = A ∆ (eta ⁻¹' B) := by
      rw [preimage_symmDiff, hAm]
      congr 1
      ext x
      simp only [mem_preimage, etaFrom_shift]
    rwa [← (measurePreserving_shift_natCast hμ m).measure_preimage
      (hA.symmDiff (measurable_etaFrom m hB)).nullMeasurableSet, hpre] at hC
  choose B hB hBμ using happrox
  refine ⟨limsup B atTop, MeasurableSet.measurableSet_limsup hB, ?_⟩
  have hsub : A ∆ (eta ⁻¹' limsup B atTop) ⊆ limsup (fun n => A ∆ (eta ⁻¹' B n)) atTop := by
    intro x hx
    rw [mem_limsup_iff_frequently_mem]
    rcases hx with ⟨hxA, hxB⟩ | ⟨hxB, hxA⟩
    · rw [mem_preimage, mem_limsup_iff_frequently_mem, not_frequently] at hxB
      exact (hxB.mono fun n hn => Or.inl ⟨hxA, hn⟩).frequently
    · rw [mem_preimage, mem_limsup_iff_frequently_mem] at hxB
      exact hxB.mono fun n hn => Or.inr ⟨hn, hxA⟩
  have hsum : ∑' n, μ (A ∆ (eta ⁻¹' B n)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun n => (hBμ n).le)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) summable_geometric_two]
    exact ENNReal.ofReal_ne_top
  exact measure_symmDiff_eq_zero_iff.1 (measure_mono_null hsub (measure_limsup_atTop_eq_zero hsum))

/-- For a finite `σ`-invariant measure `μ` on `Σ`, the measure `η_*μ` is ergodic if and only if
`μ` is ergodic (tex lines 767 and 768). -/
theorem ergodic_map_eta_iff {μ : Measure (ℤ → α)} [IsFiniteMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) :
    Ergodic shiftPlus (μ.map eta) ↔ Ergodic (shift 1) μ := by
  have hη : MeasurePreserving eta μ (μ.map eta) := measurable_eta.measurePreserving μ
  refine ⟨fun h => ⟨hμ, ⟨fun A hA hinv => ?_⟩⟩, fun h =>
    hη.ergodic_of_ergodic_semiconj h measurable_shiftPlus eta_shift⟩
  obtain ⟨B, hB, hAB⟩ := exists_preimage_eta_ae_eq hμ hA hinv
  have hBinv : shiftPlus ⁻¹' B =ᵐ[μ.map eta] B := by
    rw [← measure_symmDiff_eq_zero_iff, Measure.map_apply measurable_eta
      ((measurable_shiftPlus hB).symmDiff hB), preimage_symmDiff, measure_symmDiff_eq_zero_iff]
    have h1 : shift 1 ⁻¹' A =ᵐ[μ] shift 1 ⁻¹' (eta ⁻¹' B) :=
      hμ.quasiMeasurePreserving.preimage_ae_eq hAB
    rw [hinv] at h1
    have h2 : eta ⁻¹' (shiftPlus ⁻¹' B) = shift 1 ⁻¹' (eta ⁻¹' B) := by
      ext x
      simp only [mem_preimage, eta_shift]
    rw [h2]
    exact h1.symm.trans hAB
  have hconst := h.quasiErgodic.aeconst_set₀ hB.nullMeasurableSet hBinv
  exact ((hη.aeconst_preimage hB.nullMeasurableSet).2 hconst).congr hAB.symm

end EtaMeasure

end BoxLike
