module

/-
The partitions `ξ_0, ξ_1, ξ_2`, `ξ_1^⊥` of `sec:entropies` (tex lines 1775 to 1792) for the
article's choice of `Σ'` and of the Oseledets filtration, and for Feng's choice, compared with
the partitions `System.xi`, `System.xiPerp` of `BoxLike/DimPartitions.lean`, which use the
box-like `Σ'` of `BoxLike/SlowAxis.lean`.

Two kinds of full-measure set occur. The article's `Σ'` (`MatrixTuple.OseledetsSet`) is
saturated with respect to the past, and its atoms agree pointwise with those of `System.xi` at
every point of `Σ'`. Feng's `Σ'` (Duke Math. J. 172 (2023), Section 4, before Lemma 4.1) is an
invariant Borel set of full measure on which his properties (4.1) to (4.4) hold; (4.2) to (4.4)
concern forward time, and the set need not be saturated with respect to the past. Feng's atom
`ξ_i(𝐢) = {𝐣 ∈ Σ' : 𝐣^- = 𝐢^-, π𝐣 - π𝐢 ∈ V_𝐢^i}` is then the box-like atom cut down to Feng's set,
and the two atoms differ in general. The partitions agree modulo null sets: their conditional
measures agree almost everywhere (`condMeas_ae_eq_of_cut`), hence so do the conditional
informations and the pointwise entropies, and the entropies are equal. The forward-time
properties do not enter the atoms, so the comparison holds for every Borel set of full measure
inside which the filtration is given by Feng's (4.6).

* `condMeas_ae_eq_of_cut`: a partition whose atoms are the atoms of a measurable partition cut
  down to a Borel set of full measure has almost everywhere the same conditional measures.
* `IsMeasurablePartition.cut`: such a cut partition is measurable.
* `condInfo_ae_eq_of_condMeas`, `condEntropy_eq_of_condMeas`, `localEntropy_ae_eq_of_condMeas`,
  `infoSum_iff_of_condMeas`: partitions with almost everywhere the same conditional measures
  have the same conditional information, entropy `h_i(μ)`, pointwise entropy `h_i(μ, 𝐢)`, and
  satisfy the information-sum identity of Feng, Lemma 4.6, together.
* `System.xiOn`, `System.xi_eq_xiOn`, `System.xiPerp_eq_xiOn`: the partition of a set `D` by the
  past and a family of sets `W(𝐢)` of differences of `π`, extended by the atom `Σ ∖ D`.
* `System.condMeas_xiOn_ae_eq`, `System.condMeas_xiOn_perp_ae_eq`: the conditional measures for
  every Borel set `D` of full measure agree almost everywhere with those of `System.xi`,
  `System.xiPerp`, whenever `W` is the box-like filtration on `D ∩ Σ'`.
* `System.fengV`, `System.fengV_eq_oseledets_zero`, `System.fengV_eq_oseledets_one`: Feng's
  (4.6) defines the box-like filtration at every point of the box-like `Σ'`.
* `System.fengXi`, `System.condMeas_fengXi_ae_eq`, `System.condEntropy_fengXi_eq`,
  `System.localEntropy_fengXi_ae_eq`, `System.infoSum_fengXi_iff`: Feng's partitions on any
  Borel set of full measure; the information-sum identity of Feng, Lemma 4.6, for Feng's
  partitions is equivalent to the one for `System.xi`, which `FengInfoSum` states.
* `System.oseledetsXi`, `System.oseledetsXiPerp`: the article's partitions for a choice of
  `Σ'`; `System.oseledetsXi_eq`, `System.oseledetsXiPerp_eq`: they agree with `System.xi`,
  `System.xiPerp` at every point of `Σ'`; `System.oseledetsXi_eq_xi`,
  `System.oseledetsXi_oseledetsSet`: they are `System.xi`, `System.xiPerp` for the box-like
  choice.
* `System.isMeasurablePartition_oseledetsXi`, `System.isMeasurablePartition_oseledetsXiPerp`,
  `System.oseledetsXi_succ_subset`, `System.oseledetsXi_two_subset_perp`,
  `System.oseledetsXiPerp_subset_zero`: measurability and the inclusions of tex lines 1794 to
  1875.
* `System.condMeas_oseledetsXi_ae_eq`, `System.condInfo_oseledetsXi_ae_eq`,
  `System.condEntropy_oseledetsXi_eq`, `System.localEntropy_oseledetsXi_ae_eq`,
  `System.condMeas_oseledetsXiPerp_ae_eq`, `System.condEntropy_oseledetsXiPerp_eq`: the
  article's conditional measures and entropies are those of `System.xi`, `System.dimEntropy`,
  `System.dimEntropyAt`, for every choice of `Σ'`.
* `System.oseledets_partitions_xi1`, `System.oseledets_partition_tau_conj`:
  `thm:partitions_xi1` and `thm:partition_tau_conj` for the article's partitions and sets.
-/
public import BoxLike.OseledetsFiltration
public import BoxLike.MeasurablePartitions
public import BoxLike.ConditionalMeasures

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal

/-! ### Partitions cut down to a set of full measure -/

section Cut

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [StandardBorelSpace Ω] in
/-- If the atoms of `ξ'` at the points of a Borel set `D` are the atoms of `ξ` cut down to `D`,
and the atoms of `ξ'` at the other points avoid `D`, then a set of `\widehat{ξ}` cut down to `D`
is a set of `\widehat{ξ'}`. -/
theorem measurableSet_saturated_inter_of_cut {ξ ξ' : Ω → Set Ω} {D : Set Ω}
    (hD : MeasurableSet D) (hin : ∀ x ∈ D, ξ' x = ξ x ∩ D) (hout : ∀ x ∉ D, ξ' x ⊆ Dᶜ)
    {B : Set Ω} (hB : MeasurableSet[saturated ξ] B) : MeasurableSet[saturated ξ'] (B ∩ D) := by
  refine ⟨hB.1.inter hD, fun x y hy => ?_⟩
  by_cases hx : x ∈ D
  · rw [hin x hx] at hy
    simp only [mem_inter_iff, hB.2 x y hy.1, hx, hy.2]
  · have hy' : y ∉ D := hout x hx hy
    simp [hx, hy']

/-- Under the hypotheses of `measurableSet_saturated_inter_of_cut`, for a measurable partition
`ξ` and a set `D` of full measure, every set of `\widehat{ξ'}` agrees modulo `μ` with a set of
`\widehat{ξ}`: the points whose conditional measure gives the set full mass. -/
theorem exists_measurableSet_saturated_ae_eq_of_cut (μ : Measure Ω) [IsFiniteMeasure μ]
    {ξ ξ' : Ω → Set Ω} (hξ : IsMeasurablePartition ξ) {D : Set Ω} (hD : MeasurableSet D)
    (hD0 : μ Dᶜ = 0) (hin : ∀ x ∈ D, ξ' x = ξ x ∩ D) {B : Set Ω}
    (hB : MeasurableSet[saturated ξ'] B) :
    ∃ B', MeasurableSet[saturated ξ] B' ∧ B =ᵐ[μ] B' := by
  have hDae : ∀ᵐ x ∂μ, x ∈ D := ae_iff.2 hD0
  have hDc : ∀ᵐ x ∂μ, condMeas μ ξ x Dᶜ = 0 := by
    have h := setLIntegral_condMeas μ ξ hD.compl (@MeasurableSet.univ _ (saturated ξ))
    rw [Measure.restrict_univ, inter_univ, hD0] at h
    exact (lintegral_eq_zero_iff ((measurable_condMeas μ ξ hD.compl).mono (saturated_le ξ)
      le_rfl)).1 h
  refine ⟨{x | condMeas μ ξ x B = 1},
    measurable_condMeas μ ξ hB.1 (measurableSet_singleton 1), ?_⟩
  filter_upwards [condMeas_atom μ hξ, hDc, hDae] with x h1 h2 h3
  have hfull : condMeas μ ξ x (ξ' x) = 1 := by
    rw [hin x h3]
    refine le_antisymm prob_le_one ?_
    calc (1 : ℝ≥0∞) = condMeas μ ξ x (ξ x) := h1.symm
      _ ≤ condMeas μ ξ x (ξ x ∩ D ∪ Dᶜ) := measure_mono fun y hy => by
          by_cases hyD : y ∈ D
          · exact Or.inl ⟨hy, hyD⟩
          · exact Or.inr hyD
      _ ≤ condMeas μ ξ x (ξ x ∩ D) + condMeas μ ξ x Dᶜ := measure_union_le _ _
      _ = condMeas μ ξ x (ξ x ∩ D) := by rw [h2, add_zero]
  change (x ∈ B) = (condMeas μ ξ x B = 1)
  rw [eq_iff_iff]
  constructor
  · intro hxB
    refine le_antisymm prob_le_one ?_
    rw [← hfull]
    exact measure_mono fun y hy => (hB.2 x y hy).1 hxB
  · intro hB1
    by_contra hxB
    have hc : condMeas μ ξ x Bᶜ = 1 := by
      refine le_antisymm prob_le_one ?_
      rw [← hfull]
      exact measure_mono fun y hy hyB => hxB ((hB.2 x y hy).2 hyB)
    rw [prob_compl_eq_one_iff₀ hB.1.nullMeasurableSet] at hc
    rw [hc] at hB1
    exact zero_ne_one hB1

/-- Comparison of partitions modulo null sets (`sec:entropies`, tex lines 1789 to 1792, and the
header of `BoxLike/LiteratureFeng.lean`): if `ξ` is a measurable partition, `D` is a Borel set
of full measure, the atom `ξ'(x)` is `ξ(x) ∩ D` for `x ∈ D` and avoids `D` for `x ∉ D`, then
`ξ` and `ξ'` have the same conditional measures `μ_x^ξ = μ_x^{ξ'}` for `μ`-almost every `x`.
The atoms themselves need not agree at any point. -/
theorem condMeas_ae_eq_of_cut (μ : Measure Ω) [IsFiniteMeasure μ] {ξ ξ' : Ω → Set Ω}
    (hξ : IsMeasurablePartition ξ) {D : Set Ω} (hD : MeasurableSet D) (hD0 : μ Dᶜ = 0)
    (hin : ∀ x ∈ D, ξ' x = ξ x ∩ D) (hout : ∀ x ∉ D, ξ' x ⊆ Dᶜ) :
    ∀ᵐ x ∂μ, condMeas μ ξ' x = condMeas μ ξ x := by
  classical
  have hDae : ∀ᵐ x ∂μ, x ∈ D := ae_iff.2 hD0
  have hDsat : MeasurableSet[saturated ξ'] D := by
    simpa using measurableSet_saturated_inter_of_cut hD hin hout
      (@MeasurableSet.univ _ (saturated ξ))
  let K : Ω → Measure Ω := fun x => if x ∈ D then condMeas μ ξ x else condMeas μ ξ' x
  have hK : ∀ A, MeasurableSet A → Measurable[saturated ξ'] fun x => K x A := by
    intro A hA
    have e : (fun x => K x A) =
        D.piecewise (fun x => condMeas μ ξ x A) (fun x => condMeas μ ξ' x A) := by
      funext x
      by_cases hx : x ∈ D <;> simp [K, hx]
    rw [e]
    intro U hU
    rw [piecewise_preimage, Set.ite]
    exact (measurableSet_saturated_inter_of_cut hD hin hout
      (measurable_condMeas μ ξ hA hU)).union ((measurable_condMeas μ ξ' hA hU).diff hDsat)
  have hint : ∀ A B, MeasurableSet A → MeasurableSet[saturated ξ'] B →
      ∫⁻ x in B, K x A ∂μ = μ (A ∩ B) := by
    intro A B hA hB
    obtain ⟨B', hB', hBB'⟩ :=
      exists_measurableSet_saturated_ae_eq_of_cut μ hξ hD hD0 hin hB
    calc ∫⁻ x in B, K x A ∂μ = ∫⁻ x in B, condMeas μ ξ x A ∂μ :=
          lintegral_congr_ae (ae_restrict_of_ae (hDae.mono fun x hx => by simp [K, hx]))
      _ = ∫⁻ x in B', condMeas μ ξ x A ∂μ := setLIntegral_congr hBB'
      _ = μ (A ∩ B') := setLIntegral_condMeas μ ξ hA hB'
      _ = μ (A ∩ B) :=
          measure_congr (EventuallyEqSet.inter (EventuallyEq.refl (ae μ) A) hBB'.symm)
  filter_upwards [condMeas_unique μ ξ' K hK hint, hDae] with x hx hxD
  rw [← hx]
  simp [K, hxD]

omit [StandardBorelSpace Ω] in
/-- A partition whose atoms are the atoms of a measurable partition `ξ` cut down to a Borel set
`D`, extended by the atom `Ω ∖ D`, is a measurable partition. -/
theorem IsMeasurablePartition.cut {ξ ξ' : Ω → Set Ω} (hξ : IsMeasurablePartition ξ)
    {D : Set Ω} (hD : MeasurableSet D) (hin : ∀ x ∈ D, ξ' x = ξ x ∩ D)
    (hout : ∀ x ∉ D, ξ' x = Dᶜ) : IsMeasurablePartition ξ' := by
  classical
  obtain ⟨f, hf, hfξ⟩ := hξ
  refine ⟨fun x => if x ∈ D then Real.exp (f x) else 0,
    Measurable.ite hD (Real.measurable_exp.comp hf) measurable_const, fun x y => ?_⟩
  by_cases hx : x ∈ D
  · rw [hin x hx]
    by_cases hy : y ∈ D
    · simp [hx, hy, hfξ x y]
    · simp [hx, hy, (Real.exp_pos _).ne]
  · rw [hout x hx]
    by_cases hy : y ∈ D
    · simp [hx, hy, (Real.exp_pos _).ne']
    · simp [hx, hy]

end Cut

/-! ### Entropies of partitions with the same conditional measures -/

section Entropy

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ : Measure (ℤ → α)} [IsFiniteMeasure μ] {ξ ξ' : (ℤ → α) → Set (ℤ → α)}

/-- Partitions with almost everywhere the same conditional measures have almost everywhere the
same conditional information `I_μ(𝒫 | \widehat{ξ})`. -/
theorem condInfo_ae_eq_of_condMeas (h : ∀ᵐ x ∂μ, condMeas μ ξ' x = condMeas μ ξ x) :
    condInfo μ ξ' =ᵐ[μ] condInfo μ ξ :=
  h.mono fun x hx => by simp only [condInfo, hx]

/-- Partitions with almost everywhere the same conditional measures have the same conditional
entropy `H_μ(𝒫 | \widehat{ξ})`. -/
theorem condEntropy_eq_of_condMeas (h : ∀ᵐ x ∂μ, condMeas μ ξ' x = condMeas μ ξ x) :
    condEntropy μ ξ' = condEntropy μ ξ :=
  integral_congr_ae (condInfo_ae_eq_of_condMeas h)

/-- Partitions with almost everywhere the same conditional measures have almost everywhere the
same pointwise entropy `E_μ(I_μ(𝒫 | \widehat{ξ}) | ℐ)`. -/
theorem localEntropy_ae_eq_of_condMeas (h : ∀ᵐ x ∂μ, condMeas μ ξ' x = condMeas μ ξ x) :
    localEntropy μ ξ' =ᵐ[μ] localEntropy μ ξ :=
  condExp_congr_ae (condInfo_ae_eq_of_condMeas h)

/-- Feng, Lemma 4.6, first identity of (4.16), is the same statement for two partitions with
almost everywhere the same conditional measures, for an invariant measure: the identity
`-log μ_𝐢^ξ(𝒫_0^{n-1}(𝐢)) = ∑_{k<n} I_μ(𝒫 | \widehat{ξ})(σ^k 𝐢)` for all `n` holds almost
everywhere for `ξ'` exactly when it does for `ξ`. -/
theorem infoSum_iff_of_condMeas (hinv : MeasurePreserving (shift 1) μ μ)
    (h : ∀ᵐ x ∂μ, condMeas μ ξ' x = condMeas μ ξ x) :
    (∀ᵐ x ∂μ, ∀ n : ℕ, -Real.log ((condMeas μ ξ' x).real (cylinder (block n x))) =
      ∑ k ∈ Finset.range n, condInfo μ ξ' (shift k x)) ↔
    (∀ᵐ x ∂μ, ∀ n : ℕ, -Real.log ((condMeas μ ξ x).real (cylinder (block n x))) =
      ∑ k ∈ Finset.range n, condInfo μ ξ (shift k x)) := by
  have hk : ∀ᵐ x ∂μ, ∀ k : ℕ, condInfo μ ξ' (shift k x) = condInfo μ ξ (shift k x) :=
    ae_all_iff.2 fun k => (measurePreserving_shift_natCast hinv k).quasiMeasurePreserving.ae
      (condInfo_ae_eq_of_condMeas h)
  have e : ∀ᵐ x ∂μ, ∀ n : ℕ,
      (-Real.log ((condMeas μ ξ' x).real (cylinder (block n x))) =
        ∑ k ∈ Finset.range n, condInfo μ ξ' (shift k x)) ↔
      (-Real.log ((condMeas μ ξ x).real (cylinder (block n x))) =
        ∑ k ∈ Finset.range n, condInfo μ ξ (shift k x)) := by
    filter_upwards [h, hk] with x hx hkx n
    simp only [hx, hkx]
  constructor
  · intro h'
    filter_upwards [h', e] with x hx ex n
    exact (ex n).1 (hx n)
  · intro h'
    filter_upwards [h', e] with x hx ex n
    exact (ex n).2 (hx n)

end Entropy

namespace System

/-! ### Partitions of a subset of `Σ` by the past and a filtration -/

section Partitions

variable {ι : Type*} [MeasurableSpace ι] (S : System ι)

/-- The partition of a set `D ⊆ Σ` into the sets `{𝐣 ∈ D : 𝐣^- = 𝐢^-, π(𝐣) - π(𝐢) ∈ W(𝐢)}`,
extended to `Σ` by the atom `Σ ∖ D`, as the partitions `ξ_i`, `ξ_1^⊥` of `sec:entropies` (tex
lines 1858 to 1867) and Feng's partitions (Section 4, before Lemma 4.2). -/
noncomputable def xiOn (D : Set (ℤ → ι)) (W : (ℤ → ι) → Set (ℝ × ℝ)) :
    (ℤ → ι) → Set (ℤ → ι) :=
  atomsOn D fun x => {y | SamePast y x ∧ S.proj y - S.proj x ∈ W x}

/-- The partitions `ξ_i` of `BoxLike/DimPartitions.lean` are those of the box-like `Σ'` with the
coordinate filtration. -/
theorem xi_eq_xiOn (μ : Measure (ℤ → ι)) (i : ℕ) :
    S.xi μ i = S.xiOn (S.SigmaPrime μ) fun x => S.oseledets μ x i := rfl

/-- The partition `ξ_1^⊥` of `BoxLike/DimPartitions.lean` is that of the box-like `Σ'` with the
coordinate line orthogonal to the slow axis. -/
theorem xiPerp_eq_xiOn (μ : Measure (ℤ → ι)) :
    S.xiPerp μ = S.xiOn (S.SigmaPrime μ) fun x => {v | coord (S.slowAxis μ x) v = 0} := rfl

omit [MeasurableSpace ι] in
/-- At a point of a set `D` saturated with respect to the past the atom of `xiOn D W` is the set
of all sequences with the same past whose difference under `π` lies in `W(𝐢)`. -/
theorem xiOn_of_mem {D : Set (ℤ → ι)} (hD : ∀ x ∈ D, ∀ y, SamePast y x → y ∈ D)
    (W : (ℤ → ι) → Set (ℝ × ℝ)) {x : ℤ → ι} (hx : x ∈ D) :
    S.xiOn D W x = {y | SamePast y x ∧ S.proj y - S.proj x ∈ W x} := by
  rw [xiOn, atomsOn_of_mem hx, inter_eq_left]
  exact fun y hy => hD x hx y hy.1

/-- The atoms of `xiOn D W` are the atoms of `xiOn Σ' W₀` cut down to `D ∩ Σ'` at the points of
`D ∩ Σ'`, whenever `W = W₀` there, and they avoid `D ∩ Σ'` at the other points; here `Σ'` is the
box-like set, which is saturated with respect to the past. -/
theorem xiOn_cut (μ : Measure (ℤ → ι)) {D : Set (ℤ → ι)} {W W₀ : (ℤ → ι) → Set (ℝ × ℝ)}
    (hW : ∀ x ∈ D, x ∈ S.SigmaPrime μ → W x = W₀ x) :
    (∀ x ∈ D ∩ S.SigmaPrime μ,
      S.xiOn D W x = S.xiOn (S.SigmaPrime μ) W₀ x ∩ (D ∩ S.SigmaPrime μ)) ∧
    (∀ x ∉ D ∩ S.SigmaPrime μ, S.xiOn D W x ⊆ (D ∩ S.SigmaPrime μ)ᶜ) := by
  refine ⟨fun x ⟨hxD, hxS⟩ => ?_, fun x hx => ?_⟩
  · rw [xiOn, xiOn, atomsOn_of_mem hxD, atomsOn_of_mem hxS, hW x hxD hxS]
    ext y
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hp, hv⟩, hy⟩
      have hyS := S.mem_SigmaPrime_of_samePast μ hp.symm hxS
      exact ⟨⟨⟨hp, hv⟩, hyS⟩, hy, hyS⟩
    · rintro ⟨⟨⟨hp, hv⟩, -⟩, hy, -⟩
      exact ⟨⟨hp, hv⟩, hy⟩
  · by_cases hxD : x ∈ D
    · have hxS : x ∉ S.SigmaPrime μ := fun h => hx ⟨hxD, h⟩
      rw [xiOn, atomsOn_of_mem hxD]
      rintro y ⟨⟨hp, -⟩, -⟩ ⟨-, hyS⟩
      exact hxS (S.mem_SigmaPrime_of_samePast μ hp hyS)
    · rw [xiOn, atomsOn_of_notMem hxD]
      exact compl_subset_compl.2 inter_subset_left

/-- A Borel set of full measure meets the box-like `Σ'` in a set of full measure. -/
theorem measure_inter_SigmaPrime_compl {μ : Measure (ℤ → ι)} (hSig : μ (S.SigmaPrime μ)ᶜ = 0)
    {D : Set (ℤ → ι)} (hD0 : μ Dᶜ = 0) : μ (D ∩ S.SigmaPrime μ)ᶜ = 0 := by
  rw [compl_inter]
  exact measure_union_null hD0 hSig

end Partitions

section Comparison

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι)

/-- The partitions `ξ_i` of `sec:entropies` modulo null sets: for every Borel set `D` of full
measure and every family `W` that is the coordinate filtration `V_𝐢^i` at the points of
`D ∩ Σ'`, the partition `xiOn D W` has almost everywhere the conditional measures of
`System.xi`. The set `D` need not be saturated with respect to the past, so the atoms may
differ; this covers Feng's set `Σ'` (`fengXi`) as well as the article's (`oseledetsXi`). -/
theorem condMeas_xiOn_ae_eq (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ]
    (hSig : μ (S.SigmaPrime μ)ᶜ = 0) {D : Set (ℤ → ι)} (hD : MeasurableSet D) (hD0 : μ Dᶜ = 0)
    {W : (ℤ → ι) → Set (ℝ × ℝ)} (i : ℕ)
    (hW : ∀ x ∈ D, x ∈ S.SigmaPrime μ → W x = S.oseledets μ x i) :
    ∀ᵐ x ∂μ, condMeas μ (S.xiOn D W) x = condMeas μ (S.xi μ i) x := by
  obtain ⟨hin, hout⟩ := S.xiOn_cut μ hW
  exact condMeas_ae_eq_of_cut μ (S.isMeasurablePartition_xi μ i)
    (hD.inter (S.measurableSet_SigmaPrime μ)) (S.measure_inter_SigmaPrime_compl hSig hD0) hin hout

/-- The partition `ξ_1^⊥` of `sec:entropies` modulo null sets, as `condMeas_xiOn_ae_eq`: for
every Borel set `D` of full measure and every family `W` that is the line orthogonal to `V_𝐢^1`
at the points of `D ∩ Σ'`. -/
theorem condMeas_xiOn_perp_ae_eq (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ]
    (hSig : μ (S.SigmaPrime μ)ᶜ = 0) {D : Set (ℤ → ι)} (hD : MeasurableSet D) (hD0 : μ Dᶜ = 0)
    {W : (ℤ → ι) → Set (ℝ × ℝ)}
    (hW : ∀ x ∈ D, x ∈ S.SigmaPrime μ → W x = {v | coord (S.slowAxis μ x) v = 0}) :
    ∀ᵐ x ∂μ, condMeas μ (S.xiOn D W) x = condMeas μ (S.xiPerp μ) x := by
  obtain ⟨hin, hout⟩ := S.xiOn_cut μ hW
  exact condMeas_ae_eq_of_cut μ (S.isMeasurablePartition_xiPerp μ)
    (hD.inter (S.measurableSet_SigmaPrime μ)) (S.measure_inter_SigmaPrime_compl hSig hD0) hin hout

end Comparison

/-! ### Feng's partitions -/

section Feng

variable {ι : Type*} [MeasurableSpace ι] (S : System ι)

/-- Feng's description (4.6) of the Oseledets filtration (Duke Math. J. 172 (2023), Section 4):
`V_𝐢 = {v : limsup_n n⁻¹ log |A_{i_{-n}} ⋯ A_{i_{-1}} v| ≤ l}`, as a set of differences in
`ℝ × ℝ`. The vector `0` is included explicitly, since `log 0 = 0` in Lean. Feng's exponents
`λ_i(𝐢)` are the constants `λ_i(𝖠, μ)` under his hypothesis (4.7) for an ergodic measure. -/
def fengV (l : ℝ) (x : ℤ → ι) : Set (ℝ × ℝ) :=
  {z | ![z.1, z.2] = 0 ∨ limsup (fun n : ℕ =>
    Real.log (eucNorm (MatrixTuple.word S.mat (pastWord x n) *ᵥ ![z.1, z.2])) / n) atTop ≤ l}

/-- Feng's (4.6) for `i = 0` at the points of the box-like `Σ'`: every vector has backward
`limsup` at most `λ_1(𝖠, μ)`, so `V_𝐢^0 = ℝ²`. -/
theorem fengV_eq_oseledets_zero (μ : Measure (ℤ → ι)) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ)
    {x : ℤ → ι} (hx : x ∈ S.SigmaPrime μ) : S.fengV (S.lyapunov₁ μ) x = S.oseledets μ x 0 := by
  refine eq_univ_of_forall fun z => ?_
  by_cases hz : ![z.1, z.2] = 0
  · exact Or.inl hz
  refine Or.inr ?_
  by_cases hv : ![z.1, z.2] ∈ S.oseledetsSub μ x 1
  · rw [(S.hasEucPastRate_of_mem_oseledetsSub_one μ hlt hx hv hz).limsup_eq]
    exact hlt.le
  · rw [(S.hasEucPastRate_of_notMem_oseledetsSub_one μ hlt hx hv).limsup_eq]

/-- Feng's (4.6) for `i = 1` at the points of the box-like `Σ'`: the vectors with backward
`limsup` at most `λ_2(𝖠, μ)` form the axis `V_𝐢^1`. -/
theorem fengV_eq_oseledets_one (μ : Measure (ℤ → ι)) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ)
    {x : ℤ → ι} (hx : x ∈ S.SigmaPrime μ) : S.fengV (S.lyapunov₂ μ) x = S.oseledets μ x 1 := by
  ext z
  rw [← mem_oseledetsSub_iff]
  constructor
  · rintro (hz | hz)
    · rw [hz]
      exact Submodule.zero_mem _
    · by_contra hv
      rw [(S.hasEucPastRate_of_notMem_oseledetsSub_one μ hlt hx hv).limsup_eq] at hz
      exact hlt.not_ge hz
  · intro hv
    by_cases hz : ![z.1, z.2] = 0
    · exact Or.inl hz
    · exact Or.inr (S.hasEucPastRate_of_mem_oseledetsSub_one μ hlt hx hv hz).limsup_eq.le

/-- Feng's partitions `ξ_0, ξ_1, ξ_2` of his set `D` (Section 4, before Lemma 4.2):
`ξ_0(𝐢) = {𝐣 ∈ D : 𝐣^- = 𝐢^-}` and `ξ_i(𝐢) = {𝐣 ∈ ξ_0(𝐢) : π𝐣 - π𝐢 ∈ V_𝐢^i}`, with `V_𝐢^1` given by
(4.6) and `V_𝐢^2 = {0}`, extended to `Σ` by the atom `Σ ∖ D`. Indices above `2` repeat `ξ_2`.
Feng's set is any Borel set of full measure on which his properties hold; it need not be
saturated with respect to the past. -/
noncomputable def fengXi (μ : Measure (ℤ → ι)) (D : Set (ℤ → ι)) :
    ℕ → (ℤ → ι) → Set (ℤ → ι)
  | 0 => S.xiOn D fun _ => univ
  | 1 => S.xiOn D (S.fengV (S.lyapunov₂ μ))
  | _ => S.xiOn D fun _ => {0}

/-- Feng's filtration agrees with the coordinate filtration at every point of `D ∩ Σ'`. -/
theorem fengXi_eq_xiOn (μ : Measure (ℤ → ι)) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ)
    (D : Set (ℤ → ι)) (i : ℕ) : ∃ W : (ℤ → ι) → Set (ℝ × ℝ), S.fengXi μ D i = S.xiOn D W ∧
      ∀ x ∈ D, x ∈ S.SigmaPrime μ → W x = S.oseledets μ x i := by
  rcases i with _ | _ | i
  · exact ⟨_, rfl, fun x _ _ => rfl⟩
  · exact ⟨_, rfl, fun x _ hx => S.fengV_eq_oseledets_one μ hlt hx⟩
  · exact ⟨_, rfl, fun x _ _ => rfl⟩

variable [Fintype ι] [MeasurableSingletonClass ι]

/-- Feng's partitions and the box-like partitions agree modulo null sets, `sec:entropies` and
the header of `BoxLike/LiteratureFeng.lean`: for every Borel set `D` of full measure the
conditional measures of `fengXi μ D i` and of `System.xi μ i` agree almost everywhere, although
the atoms differ when `D` is not saturated with respect to the past. -/
theorem condMeas_fengXi_ae_eq (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ]
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) (hSig : μ (S.SigmaPrime μ)ᶜ = 0) {D : Set (ℤ → ι)}
    (hD : MeasurableSet D) (hD0 : μ Dᶜ = 0) (i : ℕ) :
    ∀ᵐ x ∂μ, condMeas μ (S.fengXi μ D i) x = condMeas μ (S.xi μ i) x := by
  obtain ⟨W, e, hW⟩ := S.fengXi_eq_xiOn μ hlt D i
  rw [e]
  exact S.condMeas_xiOn_ae_eq μ hSig hD hD0 i hW

/-- Feng's entropies are the entropies `h_i(μ)` of `System.dimEntropy`, for every Borel set of
full measure. -/
theorem condEntropy_fengXi_eq (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ]
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) (hSig : μ (S.SigmaPrime μ)ᶜ = 0) {D : Set (ℤ → ι)}
    (hD : MeasurableSet D) (hD0 : μ Dᶜ = 0) (i : ℕ) :
    condEntropy μ (S.fengXi μ D i) = S.dimEntropy μ i :=
  condEntropy_eq_of_condMeas (S.condMeas_fengXi_ae_eq μ hlt hSig hD hD0 i)

/-- Feng's pointwise entropies are almost everywhere the pointwise entropies `h_i(μ, 𝐢)` of
`System.dimEntropyAt`, for every Borel set of full measure. -/
theorem localEntropy_fengXi_ae_eq (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ]
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) (hSig : μ (S.SigmaPrime μ)ᶜ = 0) {D : Set (ℤ → ι)}
    (hD : MeasurableSet D) (hD0 : μ Dᶜ = 0) (i : ℕ) :
    localEntropy μ (S.fengXi μ D i) =ᵐ[μ] S.dimEntropyAt μ i :=
  localEntropy_ae_eq_of_condMeas (S.condMeas_fengXi_ae_eq μ hlt hSig hD hD0 i)

/-- Feng, Lemma 4.6, first identity of (4.16), for Feng's partitions on any Borel set of full
measure is equivalent to the same identity for `System.xi`, the form in which `FengInfoSum`
states it. This is the reduction "Feng's `Σ'` inside the box-like `Σ'`, partitions modulo null
sets" of the header of `BoxLike/LiteratureFeng.lean`. -/
theorem infoSum_fengXi_iff (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ)
    (hSig : μ (S.SigmaPrime μ)ᶜ = 0) {D : Set (ℤ → ι)} (hD : MeasurableSet D)
    (hD0 : μ Dᶜ = 0) (i : ℕ) :
    (∀ᵐ x ∂μ, ∀ n : ℕ, -Real.log ((condMeas μ (S.fengXi μ D i) x).real (cylinder (block n x))) =
      ∑ k ∈ Finset.range n, condInfo μ (S.fengXi μ D i) (shift k x)) ↔
    (∀ᵐ x ∂μ, ∀ n : ℕ, -Real.log ((condMeas μ (S.xi μ i) x).real (cylinder (block n x))) =
      ∑ k ∈ Finset.range n, condInfo μ (S.xi μ i) (shift k x)) :=
  infoSum_iff_of_condMeas hinv (S.condMeas_fengXi_ae_eq μ hlt hSig hD hD0 i)

end Feng

/-! ### The article's partitions -/

section Article

variable {ι : Type*} [MeasurableSpace ι] (S : System ι) {μ : Measure (ℤ → ι)}

/-- The partitions `ξ_i(𝐢) = {𝐣 ∈ Σ' : 𝐣^- = 𝐢^-, π(𝐣) - π(𝐢) ∈ V_𝐢^i}` of `sec:entropies` (tex
lines 1858 to 1863) for a choice `O` of `Σ'` and of the Oseledets filtration, extended to `Σ` by
the atom `Σ ∖ Σ'`; the indices of the article are `i ∈ {0, 1, 2}`. -/
noncomputable def oseledetsXi (O : MatrixTuple.OseledetsSet S.mat μ) (i : ℕ) :
    (ℤ → ι) → Set (ℤ → ι) :=
  S.xiOn O.carrier fun x => {z | ![z.1, z.2] ∈ O.V x i}

/-- The partition `ξ_1^⊥(𝐢) = {𝐣 ∈ Σ' : 𝐣^- = 𝐢^-, π(𝐣) - π(𝐢) ⊥ V_𝐢^1}` of `sec:entropies` (tex
lines 1864 to 1867) for a choice `O` of `Σ'`, with the Euclidean inner product, extended to `Σ`
by the atom `Σ ∖ Σ'`. -/
noncomputable def oseledetsXiPerp (O : MatrixTuple.OseledetsSet S.mat μ) :
    (ℤ → ι) → Set (ℤ → ι) :=
  S.xiOn O.carrier fun x => {z | ∀ w ∈ O.V x 1, ![z.1, z.2] ⬝ᵥ w = 0}

/-- The vectors orthogonal to a coordinate axis are those with vanishing coordinate along it. -/
theorem forall_dotProduct_axis_eq_zero_iff (c : ZMod 2) (z : ℝ × ℝ) :
    (∀ w ∈ axis c, ![z.1, z.2] ⬝ᵥ w = 0) ↔ coord c z = 0 := by
  have key : (∀ w ∈ axis c, ![z.1, z.2] ⬝ᵥ w = 0) ↔ ![z.1, z.2] ⬝ᵥ axisVec c = 0 := by
    constructor
    · intro h
      exact h _ (Submodule.mem_span_singleton_self _)
    · intro h w hw
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [dotProduct_smul, h, smul_zero]
  rw [key]
  rcases zmod_two_cases c with rfl | rfl <;> simp [axisVec, dotProduct, Fin.sum_univ_two]

/-- The article's `ξ_i` and `System.xi` have the same atom at every point of `Σ'`, for
`i ∈ {0, 1, 2}`: both sets `Σ'` are saturated with respect to the past and the filtrations
agree there. -/
theorem oseledetsXi_eq (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) {x : ℤ → ι} (hx : x ∈ O.carrier) {i : ℕ}
    (hi : i ≤ 2) : S.oseledetsXi O i x = S.xi μ i x := by
  have hxS := carrier_subset_SigmaPrime O hlt hx
  rw [oseledetsXi, S.xiOn_of_mem O.mem_of_samePast _ hx, xi_eq_xiOn,
    S.xiOn_of_mem (fun x hx y h => S.mem_SigmaPrime_of_samePast μ h.symm hx) _ hxS]
  ext y
  simp only [mem_ofPred_eq, mem_V_iff_mem_oseledets O hlt hx hi]

/-- The article's `ξ_1^⊥` and `System.xiPerp` have the same atom at every point of `Σ'`. -/
theorem oseledetsXiPerp_eq (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) {x : ℤ → ι} (hx : x ∈ O.carrier) :
    S.oseledetsXiPerp O x = S.xiPerp μ x := by
  have hxS := carrier_subset_SigmaPrime O hlt hx
  rw [oseledetsXiPerp, S.xiOn_of_mem O.mem_of_samePast _ hx, xiPerp_eq_xiOn,
    S.xiOn_of_mem (fun x hx y h => S.mem_SigmaPrime_of_samePast μ h.symm hx) _ hxS]
  ext y
  simp only [mem_ofPred_eq, V_one_eq_axis_slowAxis O hlt hx, forall_dotProduct_axis_eq_zero_iff]

/-- Off `Σ'` the article's partitions have the single atom `Σ ∖ Σ'`. -/
theorem oseledetsXi_of_notMem (O : MatrixTuple.OseledetsSet S.mat μ) {x : ℤ → ι}
    (hx : x ∉ O.carrier) (i : ℕ) : S.oseledetsXi O i x = O.carrierᶜ := by
  rw [oseledetsXi, xiOn, atomsOn_of_notMem hx]

/-- Off `Σ'` the article's `ξ_1^⊥` has the single atom `Σ ∖ Σ'`. -/
theorem oseledetsXiPerp_of_notMem (O : MatrixTuple.OseledetsSet S.mat μ) {x : ℤ → ι}
    (hx : x ∉ O.carrier) : S.oseledetsXiPerp O x = O.carrierᶜ := by
  rw [oseledetsXiPerp, xiOn, atomsOn_of_notMem hx]

/-- With the box-like choice of `Σ'` the article's partitions are the partitions `System.xi`
and `System.xiPerp` of `BoxLike/DimPartitions.lean`, everywhere. -/
theorem oseledetsXi_eq_xi (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) (hc : O.carrier = S.SigmaPrime μ) {i : ℕ}
    (hi : i ≤ 2) : S.oseledetsXi O i = S.xi μ i ∧ S.oseledetsXiPerp O = S.xiPerp μ := by
  refine ⟨funext fun x => ?_, funext fun x => ?_⟩
  · by_cases hx : x ∈ O.carrier
    · exact S.oseledetsXi_eq O hlt hx hi
    · rw [S.oseledetsXi_of_notMem O hx, xi, atomsOn_of_notMem (hc ▸ hx), hc]
  · by_cases hx : x ∈ O.carrier
    · exact S.oseledetsXiPerp_eq O hlt hx
    · rw [S.oseledetsXiPerp_of_notMem O hx, xiPerp, atomsOn_of_notMem (hc ▸ hx), hc]

/-- The atoms of the article's `ξ_i` at the points of `Σ'` are the atoms of `System.xi` cut down
to `Σ'`. -/
theorem oseledetsXi_eq_inter (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) {x : ℤ → ι} (hx : x ∈ O.carrier) {i : ℕ}
    (hi : i ≤ 2) : S.oseledetsXi O i x = S.xi μ i x ∩ O.carrier := by
  rw [← S.oseledetsXi_eq O hlt hx hi]
  refine (inter_eq_left.2 ?_).symm
  rw [oseledetsXi, xiOn, atomsOn_of_mem hx]
  exact inter_subset_right

/-- The atoms of the article's `ξ_1^⊥` at the points of `Σ'` are the atoms of `System.xiPerp`
cut down to `Σ'`. -/
theorem oseledetsXiPerp_eq_inter (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) {x : ℤ → ι} (hx : x ∈ O.carrier) :
    S.oseledetsXiPerp O x = S.xiPerp μ x ∩ O.carrier := by
  rw [← S.oseledetsXiPerp_eq O hlt hx]
  refine (inter_eq_left.2 ?_).symm
  rw [oseledetsXiPerp, xiOn, atomsOn_of_mem hx]
  exact inter_subset_right

/-- `ξ_2(𝐢) ⊆ ξ_1(𝐢) ⊆ ξ_0(𝐢)` for the article's partitions (tex line 1794). -/
theorem oseledetsXi_succ_subset (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) {i : ℕ} (hi : i ≤ 1) (x : ℤ → ι) :
    S.oseledetsXi O (i + 1) x ⊆ S.oseledetsXi O i x := by
  by_cases hx : x ∈ O.carrier
  · rw [S.oseledetsXi_eq O hlt hx (by omega), S.oseledetsXi_eq O hlt hx (by omega)]
    exact S.xi_succ_subset μ i x
  · rw [S.oseledetsXi_of_notMem O hx, S.oseledetsXi_of_notMem O hx]

/-- `ξ_2(𝐢) ⊆ ξ_1^⊥(𝐢)` for the article's partitions (tex line 1795). -/
theorem oseledetsXi_two_subset_perp (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) (x : ℤ → ι) :
    S.oseledetsXi O 2 x ⊆ S.oseledetsXiPerp O x := by
  by_cases hx : x ∈ O.carrier
  · rw [S.oseledetsXi_eq O hlt hx le_rfl, S.oseledetsXiPerp_eq O hlt hx]
    exact S.xi_two_subset_xiPerp μ x
  · rw [S.oseledetsXi_of_notMem O hx, S.oseledetsXiPerp_of_notMem O hx]

/-- `ξ_1^⊥(𝐢) ⊆ ξ_0(𝐢)` for the article's partitions (tex line 1795). -/
theorem oseledetsXiPerp_subset_zero (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) (x : ℤ → ι) :
    S.oseledetsXiPerp O x ⊆ S.oseledetsXi O 0 x := by
  by_cases hx : x ∈ O.carrier
  · rw [S.oseledetsXi_eq O hlt hx (by norm_num), S.oseledetsXiPerp_eq O hlt hx]
    exact S.xiPerp_subset_xi_zero μ x
  · rw [S.oseledetsXi_of_notMem O hx, S.oseledetsXiPerp_of_notMem O hx]

/-- `thm:partitions_xi1` for the article's partitions and sets: for `𝐢 ∈ Σ^τ`,
`ξ_1(𝐢) = \overline{τ}(\overline{ξ}_1(τ(𝐢))) ⊆ Σ^τ` and
`ξ_1^⊥(𝐢) = \overline{ω}(\overline{ξ}_1(ω(𝐢))) ⊆ Σ^τ`, and for `𝐢 ∈ Σ^ω` the same with `τ` and
`ω` exchanged. It follows from `System.partitions_xi1` and the pointwise agreement of the
partitions on `Σ'`. -/
theorem oseledets_partitions_xi1 (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) (x : ℤ → ι) :
    (x ∈ O.sigmaTau →
      (S.oseledetsXi O 1 x = unCode '' S.xiBar 1 (tau S.o x) ∧
        S.oseledetsXi O 1 x ⊆ O.sigmaTau) ∧
      (S.oseledetsXiPerp O x = unCode '' S.xiBar 1 (omega S.o x) ∧
        S.oseledetsXiPerp O x ⊆ O.sigmaTau)) ∧
    (x ∈ O.sigmaOmega →
      (S.oseledetsXi O 1 x = unCode '' S.xiBar 1 (omega S.o x) ∧
        S.oseledetsXi O 1 x ⊆ O.sigmaOmega) ∧
      (S.oseledetsXiPerp O x = unCode '' S.xiBar 1 (tau S.o x) ∧
        S.oseledetsXiPerp O x ⊆ O.sigmaOmega)) := by
  have hsub : ∀ x ∈ O.carrier, S.oseledetsXi O 1 x ⊆ O.carrier ∧
      S.oseledetsXiPerp O x ⊆ O.carrier := fun x hx => by
    rw [oseledetsXi, oseledetsXiPerp, xiOn, xiOn, atomsOn_of_mem hx, atomsOn_of_mem hx]
    exact ⟨inter_subset_right, inter_subset_right⟩
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have hxc := hx.1
    rw [sigmaTau_eq_inter O hlt] at hx ⊢
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ :=
      And.intro (S.xi_one_of_mem_SigmaTau μ hx.2) (S.xiPerp_of_mem_SigmaTau μ hx.2)
    rw [S.oseledetsXi_eq O hlt hxc (by norm_num), S.oseledetsXiPerp_eq O hlt hxc]
    refine ⟨⟨h1, subset_inter ?_ h2⟩, h3, subset_inter ?_ h4⟩
    · rw [← S.oseledetsXi_eq O hlt hxc (by norm_num)]; exact (hsub x hxc).1
    · rw [← S.oseledetsXiPerp_eq O hlt hxc]; exact (hsub x hxc).2
  · have hxc := hx.1
    rw [sigmaOmega_eq_inter O hlt] at hx ⊢
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ :=
      And.intro (S.xi_one_of_mem_SigmaOmega μ hlt hx.2) (S.xiPerp_of_mem_SigmaOmega μ hlt hx.2)
    rw [S.oseledetsXi_eq O hlt hxc (by norm_num), S.oseledetsXiPerp_eq O hlt hxc]
    refine ⟨⟨h1, subset_inter ?_ h2⟩, h3, subset_inter ?_ h4⟩
    · rw [← S.oseledetsXi_eq O hlt hxc (by norm_num)]; exact (hsub x hxc).1
    · rw [← S.oseledetsXiPerp_eq O hlt hxc]; exact (hsub x hxc).2

/-- `thm:partition_tau_conj` for the article's partitions and sets: for `𝐢 ∈ Σ^τ`,
`(ξ_1 ∨ 𝒫_0^{n-1})(𝐢) = \overline{τ}((\overline{ξ}_1 ∨ \overline{𝒫}_0^{n-1})(τ(𝐢)))`, and the same
with `ω` for `𝐢 ∈ Σ^ω`. -/
theorem oseledets_partition_tau_conj (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) (x : ℤ → ι) (n : ℕ) :
    (x ∈ O.sigmaTau → S.oseledetsXi O 1 x ∩ cylinder (block n x) =
      unCode '' (S.xiBar 1 (tau S.o x) ∩ cylinder (block n (tau S.o x)))) ∧
    (x ∈ O.sigmaOmega → S.oseledetsXi O 1 x ∩ cylinder (block n x) =
      unCode '' (S.xiBar 1 (omega S.o x) ∩ cylinder (block n (omega S.o x)))) := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have hτ : x ∈ S.SigmaTau μ := by rw [sigmaTau_eq_inter O hlt] at hx; exact hx.2
    rw [S.oseledetsXi_eq O hlt hx.1 (by norm_num), S.image_unCode_xiBar_inter_cylinder_tau,
      (S.xi_one_of_mem_SigmaTau μ hτ).1]
  · have hω : x ∈ S.SigmaOmega μ := by rw [sigmaOmega_eq_inter O hlt] at hx; exact hx.2
    rw [S.oseledetsXi_eq O hlt hx.1 (by norm_num), S.image_unCode_xiBar_inter_cylinder_omega,
      (S.xi_one_of_mem_SigmaOmega μ hlt hω).1]

variable [Fintype ι] [MeasurableSingletonClass ι]

/-- The partitions `System.xi`, `System.xiPerp` of `BoxLike/DimPartitions.lean` are the article's
partitions for the box-like choice `oseledetsSet` of `Σ'`. -/
theorem oseledetsXi_oseledetsSet [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) {i : ℕ} (hi : i ≤ 2) :
    S.oseledetsXi (S.oseledetsSet μ hinv herg hlt) i = S.xi μ i ∧
      S.oseledetsXiPerp (S.oseledetsSet μ hinv herg hlt) = S.xiPerp μ :=
  S.oseledetsXi_eq_xi _ hlt rfl hi

/-- The article's partitions `ξ_i` are measurable partitions (tex lines 1789 to 1790; Feng,
Lemma 4.2). -/
theorem isMeasurablePartition_oseledetsXi (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) {i : ℕ} (hi : i ≤ 2) :
    IsMeasurablePartition (S.oseledetsXi O i) :=
  (S.isMeasurablePartition_xi μ i).cut O.measurableSet_carrier
    (fun _ hx => S.oseledetsXi_eq_inter O hlt hx hi) fun _ hx => S.oseledetsXi_of_notMem O hx i

/-- The article's partition `ξ_1^⊥` is a measurable partition (tex lines 1789 to 1790). -/
theorem isMeasurablePartition_oseledetsXiPerp (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) : IsMeasurablePartition (S.oseledetsXiPerp O) :=
  (S.isMeasurablePartition_xiPerp μ).cut O.measurableSet_carrier
    (fun _ hx => S.oseledetsXiPerp_eq_inter O hlt hx) fun _ hx => S.oseledetsXiPerp_of_notMem O hx

/-- The article's partitions `ξ_i` and `System.xi` have almost everywhere the same conditional
measures, for every choice of `Σ'`. -/
theorem condMeas_oseledetsXi_ae_eq [IsFiniteMeasure μ] (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) {i : ℕ} (hi : i ≤ 2) :
    ∀ᵐ x ∂μ, condMeas μ (S.oseledetsXi O i) x = condMeas μ (S.xi μ i) x :=
  S.condMeas_xiOn_ae_eq μ (measure_SigmaPrime_compl_of_oseledetsSet O hlt)
    O.measurableSet_carrier O.measure_compl i fun x hx _ => by
      ext z
      exact mem_V_iff_mem_oseledets O hlt hx hi z

/-- The article's `ξ_1^⊥` and `System.xiPerp` have almost everywhere the same conditional
measures, for every choice of `Σ'`. -/
theorem condMeas_oseledetsXiPerp_ae_eq [IsFiniteMeasure μ]
    (O : MatrixTuple.OseledetsSet S.mat μ) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) :
    ∀ᵐ x ∂μ, condMeas μ (S.oseledetsXiPerp O) x = condMeas μ (S.xiPerp μ) x :=
  S.condMeas_xiOn_perp_ae_eq μ (measure_SigmaPrime_compl_of_oseledetsSet O hlt)
    O.measurableSet_carrier O.measure_compl fun x hx _ => by
      ext z
      simp only [mem_ofPred_eq, V_one_eq_axis_slowAxis O hlt hx,
        forall_dotProduct_axis_eq_zero_iff]

/-- The article's `i`-dimensional entropy `h_i(μ) = H_μ(𝒫 | \widehat{ξ}_i)` (tex lines 1812 to
1897) for every choice of `Σ'` is `System.dimEntropy μ i`. -/
theorem condEntropy_oseledetsXi_eq [IsFiniteMeasure μ] (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) {i : ℕ} (hi : i ≤ 2) :
    condEntropy μ (S.oseledetsXi O i) = S.dimEntropy μ i :=
  condEntropy_eq_of_condMeas (S.condMeas_oseledetsXi_ae_eq O hlt hi)

/-- The article's pointwise entropy `h_i(μ, 𝐢)` (tex lines 1805 to 1811) for every choice of
`Σ'` is almost everywhere `System.dimEntropyAt μ i`. -/
theorem localEntropy_oseledetsXi_ae_eq [IsFiniteMeasure μ]
    (O : MatrixTuple.OseledetsSet S.mat μ) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) {i : ℕ}
    (hi : i ≤ 2) : localEntropy μ (S.oseledetsXi O i) =ᵐ[μ] S.dimEntropyAt μ i :=
  localEntropy_ae_eq_of_condMeas (S.condMeas_oseledetsXi_ae_eq O hlt hi)

/-- The conditional information `I_μ(𝒫 | \widehat{ξ}_i)` of the article's partitions is almost
everywhere that of `System.xi`. -/
theorem condInfo_oseledetsXi_ae_eq [IsFiniteMeasure μ] (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) {i : ℕ} (hi : i ≤ 2) :
    condInfo μ (S.oseledetsXi O i) =ᵐ[μ] condInfo μ (S.xi μ i) :=
  condInfo_ae_eq_of_condMeas (S.condMeas_oseledetsXi_ae_eq O hlt hi)

/-- The entropy `H_μ(𝒫 | \widehat{ξ_1^⊥})` of the article's `ξ_1^⊥` for every choice of `Σ'` is
that of `System.xiPerp`. -/
theorem condEntropy_oseledetsXiPerp_eq [IsFiniteMeasure μ]
    (O : MatrixTuple.OseledetsSet S.mat μ) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) :
    condEntropy μ (S.oseledetsXiPerp O) = condEntropy μ (S.xiPerp μ) :=
  condEntropy_eq_of_condMeas (S.condMeas_oseledetsXiPerp_ae_eq O hlt)

end Article

end System

end BoxLike
