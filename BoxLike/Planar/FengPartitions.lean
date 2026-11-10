module

/-
Other representations of the partitions `ξ_i` of `sec:entropies` for a planar self-affine system,
compared with `PlanarSystem.xi` modulo null sets (tex lines 1775 to 1792). The library's `Σ'` is
the set of all regular points (`BoxLike/Planar/Oseledets.lean`). Feng's partitions (Duke Math. J.
172 (2023), Section 4, before Lemma 4.2) live on an invariant Borel set of full measure, his
`Σ'`, which need not be saturated with respect to the past, with the subspaces given by his
(4.6), `V_𝐢^i = {v : limsup_n n⁻¹ log |A_{i_{-n}} ⋯ A_{i_{-1}} v| ≤ λ_{i+1}}`. The article's
partitions live on a choice of `Σ'` in the sense of `MatrixTuple.OseledetsSet`. In both cases the
atoms at the points of the smaller set are the library's atoms cut down to it, so the
conditional measures agree almost everywhere (`condMeas_ae_eq_of_cut` of
`BoxLike/OseledetsBridge.lean`), and with them the conditional informations, the pointwise
entropies, the entropies and the information-sum identity of Feng, Lemma 4.6, (4.16). This is the
reduction from Feng's source statements used in `BoxLike/LiteraturePlanarFeng.lean`.

* `MatrixTuple.fengV`, `MatrixTuple.fengV_eq_filtration`: Feng's (4.6) gives the library's
  filtration at every regular point.
* `PlanarSystem.fengXi`, `PlanarSystem.condMeas_fengXi_ae_eq`,
  `PlanarSystem.isMeasurablePartition_fengXi`, `PlanarSystem.condEntropy_fengXi_eq`,
  `PlanarSystem.localEntropy_fengXi_ae_eq`, `PlanarSystem.infoSum_fengXi_iff`: Feng's partitions
  on a Borel set of full measure inside `Σ'`.
* `PlanarSystem.oseledetsXi`, `PlanarSystem.condMeas_oseledetsXi_ae_eq`,
  `PlanarSystem.isMeasurablePartition_oseledetsXi`, `PlanarSystem.condEntropy_oseledetsXi_eq`,
  `PlanarSystem.localEntropy_oseledetsXi_ae_eq`, `PlanarSystem.infoSum_oseledetsXi_iff`: the
  article's partitions for a choice of `Σ'`.
-/
public import BoxLike.Planar.FengEntropy
public import BoxLike.Planar.OseledetsChoice
public import BoxLike.OseledetsBridge

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set Matrix

universe u

namespace MatrixTuple

variable {ι : Type*} (A : ι → Matrix (Fin 2) (Fin 2) ℝ)

/-- Feng's subspaces (4.6) (Duke Math. J. 172 (2023), Section 4):
`V_𝐢^i = {v : limsup_n n⁻¹ log |A_{i_{-n}} ⋯ A_{i_{-1}} v| ≤ λ_{i+1}}` for `i ∈ {0, 1}`, and
`V_𝐢^2 = {0}`. The zero vector, whose logarithm is `-∞` in the source, is included explicitly.
Indices above `2` repeat `{0}`. -/
noncomputable def fengV (l₁ l₂ : ℝ) (x : ℤ → ι) : ℕ → Set (Fin 2 → ℝ)
  | 0 => {v | v = 0 ∨ limsup (fun n : ℕ => Real.log ‖pastProd A x n *ᵥ v‖ / n) atTop ≤ l₁}
  | 1 => {v | v = 0 ∨ limsup (fun n : ℕ => Real.log ‖pastProd A x n *ᵥ v‖ / n) atTop ≤ l₂}
  | _ => {0}

variable {A}

/-- At a regular point Feng's (4.6) gives the filtration `filtration` of the library: the backward
rates exist, so the upper limits are the rates `λ_1` and `λ_2`. -/
theorem fengV_eq_filtration {l₁ l₂ : ℝ} (hlt : l₂ < l₁) {x : ℤ → ι}
    (hx : x ∈ regularSet A l₁ l₂) (i : ℕ) : fengV A l₁ l₂ x i = filtration A l₂ x i := by
  obtain ⟨u, hu⟩ := hx
  rcases i with _ | _ | i
  · ext v
    simp only [fengV, mem_ofPred_eq, filtration_zero, mem_univ, iff_true]
    by_cases hv0 : v = 0
    · exact Or.inl hv0
    refine Or.inr ?_
    by_cases hv : v ∈ Submodule.span ℝ {u}
    · rw [((hu.2 v).1 hv hv0).limsup_eq]
      exact hlt.le
    · rw [((hu.2 v).2 hv).limsup_eq]
  · rw [filtration_one, slowLine_eq_span hlt hu]
    ext v
    simp only [fengV, mem_ofPred_eq, SetLike.mem_coe]
    constructor
    · rintro (rfl | h)
      · exact Submodule.zero_mem _
      · by_contra hv
        rw [((hu.2 v).2 hv).limsup_eq] at h
        linarith
    · intro hv
      by_cases hv0 : v = 0
      · exact Or.inl hv0
      · exact Or.inr (((hu.2 v).1 hv hv0).limsup_eq.le)
  · rfl

end MatrixTuple

namespace PlanarSystem

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (P : PlanarSystem ι)

/-! ### Feng's partitions -/

/-- Feng's partitions `ξ_i(𝐢) = {𝐣 ∈ D : 𝐣^- = 𝐢^-, π𝐣 - π𝐢 ∈ V_𝐢^i}` of a set `D` (his `Σ'`),
with `V_𝐢^i` by (4.6), extended to `Σ` by the atom `Σ ∖ D`. -/
noncomputable def fengXi (μ : Measure (ℤ → ι)) (D : Set (ℤ → ι)) (i : ℕ) :
    (ℤ → ι) → Set (ℤ → ι) :=
  atomsOn D fun x => {y | SamePast y x ∧
    toVec (P.proj y - P.proj x) ∈ MatrixTuple.fengV P.mat (P.lyapunov₁ μ) (P.lyapunov₂ μ) x i}

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- At the points of a set `D ⊆ Σ'`, Feng's atoms are the library's atoms cut down to `D`. -/
theorem fengXi_eq_inter (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    {D : Set (ℤ → ι)} (hDsub : D ⊆ P.SigmaPrime μ) (i : ℕ) {x : ℤ → ι} (hx : x ∈ D) :
    P.fengXi μ D i x = P.xi μ i x ∩ D := by
  rw [fengXi, atomsOn_of_mem hx, xi, atomsOn_of_mem (hDsub hx),
    MatrixTuple.fengV_eq_filtration hlt (hDsub hx), inter_assoc, inter_eq_right.2 hDsub]
  rfl

/-- Feng's partitions on a Borel set `D ⊆ Σ'` of full measure have almost everywhere the
conditional measures of the library's partitions `ξ_i`. -/
theorem condMeas_fengXi_ae_eq (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ]
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) {D : Set (ℤ → ι)} (hD : MeasurableSet D)
    (hDsub : D ⊆ P.SigmaPrime μ) (hfull : μ Dᶜ = 0) (i : ℕ) :
    ∀ᵐ x ∂μ, condMeas μ (P.fengXi μ D i) x = condMeas μ (P.xi μ i) x :=
  condMeas_ae_eq_of_cut μ (P.isMeasurablePartition_xi μ hlt i) hD hfull
    (fun x hx => P.fengXi_eq_inter μ hlt hDsub i hx)
    (fun x hx => by rw [fengXi, atomsOn_of_notMem hx])

/-- Feng's partitions on a Borel set `D ⊆ Σ'` are measurable partitions (Feng, Lemma 4.2). -/
theorem isMeasurablePartition_fengXi (μ : Measure (ℤ → ι))
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) {D : Set (ℤ → ι)} (hD : MeasurableSet D)
    (hDsub : D ⊆ P.SigmaPrime μ) (i : ℕ) : IsMeasurablePartition (P.fengXi μ D i) :=
  (P.isMeasurablePartition_xi μ hlt i).cut hD (fun x hx => P.fengXi_eq_inter μ hlt hDsub i hx)
    (fun x hx => by rw [fengXi, atomsOn_of_notMem hx])

/-- Feng's entropies `h_i = H_μ(𝒫 | \widehat{ξ}_i)` of (1.5) for partitions on a Borel set
`D ⊆ Σ'` of full measure are the library's `h_i(μ)`. -/
theorem condEntropy_fengXi_eq (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ]
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) {D : Set (ℤ → ι)} (hD : MeasurableSet D)
    (hDsub : D ⊆ P.SigmaPrime μ) (hfull : μ Dᶜ = 0) (i : ℕ) :
    condEntropy μ (P.fengXi μ D i) = P.dimEntropy μ i :=
  condEntropy_eq_of_condMeas (P.condMeas_fengXi_ae_eq μ hlt hD hDsub hfull i)

/-- Feng's pointwise entropies `h_i(𝐢)` of (4.15) for partitions on a Borel set `D ⊆ Σ'` of full
measure are almost everywhere the library's `h_i(μ, 𝐢)`. -/
theorem localEntropy_fengXi_ae_eq (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ]
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) {D : Set (ℤ → ι)} (hD : MeasurableSet D)
    (hDsub : D ⊆ P.SigmaPrime μ) (hfull : μ Dᶜ = 0) (i : ℕ) :
    localEntropy μ (P.fengXi μ D i) =ᵐ[μ] P.dimEntropyAt μ i :=
  localEntropy_ae_eq_of_condMeas (P.condMeas_fengXi_ae_eq μ hlt hD hDsub hfull i)

/-- The first identity of Feng, Lemma 4.6, (4.16), for Feng's partitions on a Borel set
`D ⊆ Σ'` of full measure is equivalent to the identity `PlanarSystem.InfoSum` for the library's
partitions, which `PlanarFengInfoSum` states. -/
theorem infoSum_fengXi_iff (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    {D : Set (ℤ → ι)} (hD : MeasurableSet D) (hDsub : D ⊆ P.SigmaPrime μ) (hfull : μ Dᶜ = 0)
    (i : ℕ) :
    (∀ᵐ x ∂μ, ∀ n : ℕ, -Real.log ((condMeas μ (P.fengXi μ D i) x).real (cylinder (block n x))) =
      ∑ k ∈ Finset.range n, condInfo μ (P.fengXi μ D i) (shift k x)) ↔ P.InfoSum μ i :=
  infoSum_iff_of_condMeas hinv (P.condMeas_fengXi_ae_eq μ hlt hD hDsub hfull i)

/-! ### The article's partitions for a choice of `Σ'` -/

/-- The article's partitions `ξ_i(𝐢) = {𝐣 ∈ Σ' : 𝐣^- = 𝐢^-, π(𝐣) - π(𝐢) ∈ V_𝐢^i}` (`sec:entropies`,
tex lines 1779 to 1784) for a choice of `Σ'` and of the Oseledets filtration, extended to `Σ` by
the atom `Σ ∖ Σ'`. -/
noncomputable def oseledetsXi {μ : Measure (ℤ → ι)} (O : MatrixTuple.OseledetsSet P.mat μ)
    (i : ℕ) : (ℤ → ι) → Set (ℤ → ι) :=
  atomsOn O.carrier fun x => {y | SamePast y x ∧ toVec (P.proj y - P.proj x) ∈ O.V x i}

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- At the points of a choice of `Σ'`, the article's atoms are the library's atoms cut down to
it, for `i ∈ {0, 1, 2}`. -/
theorem oseledetsXi_eq_inter {μ : Measure (ℤ → ι)} (O : MatrixTuple.OseledetsSet P.mat μ)
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) {i : ℕ} (hi : i ≤ 2) {x : ℤ → ι}
    (hx : x ∈ O.carrier) : P.oseledetsXi O i x = P.xi μ i x ∩ O.carrier := by
  have hsub : O.carrier ⊆ P.SigmaPrime μ := O.carrier_subset_regularSet P.det_ne_zero hlt
  have hV : (O.V x i : Set (Fin 2 → ℝ)) = P.oseledets μ x i := by
    rcases i with _ | _ | i
    · rw [O.V_zero_eq_top hx]
      rfl
    · exact O.coe_V_one hlt hx
    · obtain rfl : i = 0 := by omega
      rw [O.V_two_eq_bot hx]
      ext v
      simp [oseledets]
  rw [oseledetsXi, atomsOn_of_mem hx, xi, atomsOn_of_mem (hsub hx), inter_assoc,
    inter_eq_right.2 hsub, ← hV]
  rfl

/-- The article's partitions for a choice of `Σ'` have almost everywhere the conditional
measures of the library's partitions, for `i ∈ {0, 1, 2}`. -/
theorem condMeas_oseledetsXi_ae_eq {μ : Measure (ℤ → ι)} [IsFiniteMeasure μ]
    (O : MatrixTuple.OseledetsSet P.mat μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) {i : ℕ}
    (hi : i ≤ 2) : ∀ᵐ x ∂μ, condMeas μ (P.oseledetsXi O i) x = condMeas μ (P.xi μ i) x :=
  condMeas_ae_eq_of_cut μ (P.isMeasurablePartition_xi μ hlt i) O.measurableSet_carrier
    O.measure_compl (fun x hx => P.oseledetsXi_eq_inter O hlt hi hx)
    (fun x hx => by rw [oseledetsXi, atomsOn_of_notMem hx])

/-- The article's partitions for a choice of `Σ'` are measurable partitions (Feng, Lemma 4.2),
for `i ∈ {0, 1, 2}`. -/
theorem isMeasurablePartition_oseledetsXi {μ : Measure (ℤ → ι)}
    (O : MatrixTuple.OseledetsSet P.mat μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) {i : ℕ}
    (hi : i ≤ 2) : IsMeasurablePartition (P.oseledetsXi O i) :=
  (P.isMeasurablePartition_xi μ hlt i).cut O.measurableSet_carrier
    (fun x hx => P.oseledetsXi_eq_inter O hlt hi hx)
    (fun x hx => by rw [oseledetsXi, atomsOn_of_notMem hx])

/-- The article's entropies `h_i(μ) = H_μ(𝒫 | \widehat{ξ}_i)` for a choice of `Σ'` are the
library's, for `i ∈ {0, 1, 2}`. -/
theorem condEntropy_oseledetsXi_eq {μ : Measure (ℤ → ι)} [IsFiniteMeasure μ]
    (O : MatrixTuple.OseledetsSet P.mat μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) {i : ℕ}
    (hi : i ≤ 2) : condEntropy μ (P.oseledetsXi O i) = P.dimEntropy μ i :=
  condEntropy_eq_of_condMeas (P.condMeas_oseledetsXi_ae_eq O hlt hi)

/-- The article's pointwise entropies `h_i(μ, 𝐢)` for a choice of `Σ'` are almost everywhere the
library's, for `i ∈ {0, 1, 2}`. -/
theorem localEntropy_oseledetsXi_ae_eq {μ : Measure (ℤ → ι)} [IsFiniteMeasure μ]
    (O : MatrixTuple.OseledetsSet P.mat μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) {i : ℕ}
    (hi : i ≤ 2) : localEntropy μ (P.oseledetsXi O i) =ᵐ[μ] P.dimEntropyAt μ i :=
  localEntropy_ae_eq_of_condMeas (P.condMeas_oseledetsXi_ae_eq O hlt hi)

/-- The first identity of Feng, Lemma 4.6, (4.16), for the article's partitions of a choice of
`Σ'` is equivalent to the identity `PlanarSystem.InfoSum` for the library's partitions, for
`i ∈ {0, 1, 2}`. -/
theorem infoSum_oseledetsXi_iff {μ : Measure (ℤ → ι)} [IsFiniteMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (O : MatrixTuple.OseledetsSet P.mat μ)
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) {i : ℕ} (hi : i ≤ 2) :
    (∀ᵐ x ∂μ, ∀ n : ℕ, -Real.log ((condMeas μ (P.oseledetsXi O i) x).real
      (cylinder (block n x))) = ∑ k ∈ Finset.range n, condInfo μ (P.oseledetsXi O i) (shift k x)) ↔
      P.InfoSum μ i :=
  infoSum_iff_of_condMeas hinv (P.condMeas_oseledetsXi_ae_eq O hlt hi)

end PlanarSystem

end BoxLike
