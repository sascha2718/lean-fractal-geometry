module

/-
Conditional information and conditional entropy of a countable partition given an arbitrary
sub-`σ`-algebra, at the generality of `sec:conditional` (tex lines 1641 to 1669), together with
the remaining unnumbered claims of that span on conditional measures (tex lines 1671 to 1692).
The library's `condInfo` and `condEntropy` of `BoxLike/Conditional.lean` treat the canonical
partition `𝒫 = {[i]}` given `\widehat{ξ}`; they are the specialisation of the objects here.

The conditional expectation `E_μ(f | 𝒜)` is Mathlib's `μ[f | 𝒜]`, the `𝒜`-measurable function
unique up to `μ`-null sets with `∫_A f dμ = ∫_A E_μ(f | 𝒜) dμ` for `A ∈ 𝒜`
(`eq:conditional_expectation_def`). The conditional information is real-valued: where
`E_μ(1_A | 𝒜) = 0` Lean gives `-log 0 = 0` and the article `+∞`, on a `μ`-null set of points of
`A`. The conditional entropy is an extended non-negative real, so that a countable partition of
infinite entropy has the value `∞`.

* `IsCountablePartition`: a countable family of pairwise disjoint Borel sets covering the space.
* `condInfoPart`, `condInfoPart_eq_of_mem`: `I_μ(𝒬 | 𝒜) = -∑_{A ∈ 𝒬} 1_A log E_μ(1_A | 𝒜)`, which
  at a point of `A ∈ 𝒬` is `-log E_μ(1_A | 𝒜)`.
* `condEntropyPart`: `H_μ(𝒬 | 𝒜) = ∫ I_μ(𝒬 | 𝒜) dμ`.
* `trivialSigma`, `condExp_trivialSigma`: the trivial `σ`-algebra
  `𝒩 = {A ∈ ℬ : μ(A) ∈ {0, 1}}` and `E_μ(f | 𝒩) = ∫ f dμ`.
* `condInfoPart_trivialSigma`, `condEntropyPart_trivialSigma`:
  `I_μ(𝒬 | 𝒩) = -∑_{A ∈ 𝒬} 1_A log μ(A)` and `H_μ(𝒬 | 𝒩) = -∑_{A ∈ 𝒬} μ(A) log μ(A)`, the
  Shannon entropy `H_μ(𝒬)`.
* `integral_condMeas_ae_eq_condExp`: `∫ f dμ_x^ξ = E_μ(f | \widehat{ξ})(x)` for `f ∈ L¹(μ)` and
  `μ`-almost every `x` (tex lines 1681 to 1685).
* `twoSetPartition`, `condMeas_twoSetPartition_eq_cond`: the normalised restriction `μ_Ξ` agrees
  with the conditional measure for the partition `{Ξ, Ξ^c}` at `μ`-almost every point of `Ξ`
  (tex lines 1688 to 1692).
* `blockPartition`, `isCountablePartition_blockPartition`,
  `blockEntropy_eq_toReal_condEntropyPart`: the block entropy `H_μ(𝒫_0^{n-1})` of the library is
  the Shannon entropy of the countable partition into cylinders of length `n`.
* `canonicalPartition`, `isCountablePartition_canonicalPartition`,
  `condInfo_ae_eq_condInfoPart`, `condEntropy_eq_toReal_condEntropyPart`: the library's
  `condInfo` and `condEntropy` are `I_μ(𝒫 | \widehat{ξ})` and `H_μ(𝒫 | \widehat{ξ})` for the
  canonical partition `𝒫`.
-/
public import BoxLike.ConditionalMeasures
public import BoxLike.ConditionalLemmas
public import BoxLike.Entropy
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

@[expose] public section

namespace BoxLike

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-! ### Countable partitions, conditional information and conditional entropy -/

section General

variable {Ω : Type*}

section Partition

variable [MeasurableSpace Ω]

/-- A countable Borel partition `𝒬` of `Ω` (`sec:conditional`, tex line 1652): a countable family
of pairwise disjoint Borel sets whose union is `Ω`. -/
structure IsCountablePartition (Q : Set (Set Ω)) : Prop where
  countable : Q.Countable
  measurableSet : ∀ A ∈ Q, MeasurableSet A
  pairwiseDisjoint : Q.PairwiseDisjoint id
  sUnion_eq : ⋃₀ Q = univ

/-- Every point lies in an element of a partition. -/
theorem IsCountablePartition.exists_mem {Q : Set (Set Ω)} (hQ : IsCountablePartition Q)
    (x : Ω) : ∃ A ∈ Q, x ∈ A := by
  have hx : x ∈ ⋃₀ Q := hQ.sUnion_eq ▸ mem_univ x
  exact hx

/-- The element of a partition containing a point is unique. -/
theorem IsCountablePartition.eq_of_mem {Q : Set (Set Ω)} (hQ : IsCountablePartition Q)
    {A B : Set Ω} (hA : A ∈ Q) (hB : B ∈ Q) {x : Ω} (hxA : x ∈ A) (hxB : x ∈ B) : A = B := by
  by_contra hne
  exact Set.disjoint_left.1 (hQ.pairwiseDisjoint hA hB hne) hxA hxB

/-- A sum over a partition of functions supported on the atoms is the value at the atom of the
point. -/
theorem IsCountablePartition.tsum_indicator_eq {Q : Set (Set Ω)} (hQ : IsCountablePartition Q)
    (g : Set Ω → Ω → ℝ) {A : Set Ω} (hA : A ∈ Q) {x : Ω} (hx : x ∈ A) :
    ∑' B : Q, (B : Set Ω).indicator (g B) x = g A x := by
  rw [tsum_eq_single (⟨A, hA⟩ : Q)]
  · rw [indicator_of_mem hx]
  · intro B hB
    refine indicator_of_notMem (fun hxB => hB ?_) _
    exact Subtype.ext (hQ.eq_of_mem B.2 hA hxB hx)

end Partition

section Information

variable (𝒜 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]

/-- The conditional probability `E_μ(1_A | 𝒜)` of a set `A` given a sub-`σ`-algebra `𝒜`. -/
noncomputable def condProbFn (μ : Measure Ω) (A : Set Ω) : Ω → ℝ :=
  μ[A.indicator (fun _ => (1 : ℝ)) | 𝒜]

/-- The conditional information `I_μ(𝒬 | 𝒜) = -∑_{A ∈ 𝒬} 1_A log E_μ(1_A | 𝒜)` of a countable
partition `𝒬` given a sub-`σ`-algebra `𝒜` (`sec:conditional`, tex lines 1652 to 1657). -/
noncomputable def condInfoPart (μ : Measure Ω) (Q : Set (Set Ω)) (x : Ω) : ℝ :=
  -∑' A : Q, (A : Set Ω).indicator (fun y => Real.log (condProbFn 𝒜 μ A y)) x

/-- The conditional entropy `H_μ(𝒬 | 𝒜) = ∫ I_μ(𝒬 | 𝒜) dμ` (`sec:conditional`, tex lines 1658 to
1739), with values in `[0, ∞]`. -/
noncomputable def condEntropyPart (μ : Measure Ω) (Q : Set (Set Ω)) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (condInfoPart 𝒜 μ Q x) ∂μ

/-- At a point of the atom `A ∈ 𝒬` the conditional information is `-log E_μ(1_A | 𝒜)`. -/
theorem condInfoPart_eq_of_mem (μ : Measure Ω) {Q : Set (Set Ω)}
    (hQ : IsCountablePartition Q) {A : Set Ω} (hA : A ∈ Q) {x : Ω} (hx : x ∈ A) :
    condInfoPart 𝒜 μ Q x = -Real.log (condProbFn 𝒜 μ A x) := by
  rw [condInfoPart, hQ.tsum_indicator_eq (fun B y => Real.log (condProbFn 𝒜 μ B y)) hA hx]

end Information

/-! ### The trivial `σ`-algebra -/

variable [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The trivial `σ`-algebra `𝒩 = {A ∈ ℬ : μ(A) ∈ {0, 1}}` of tex line 1651. -/
@[implicit_reducible]
def trivialSigma : MeasurableSpace Ω where
  MeasurableSet' A := MeasurableSet A ∧ (μ A = 0 ∨ μ A = 1)
  measurableSet_empty := ⟨MeasurableSet.empty, Or.inl measure_empty⟩
  measurableSet_compl A hA := by
    refine ⟨hA.1.compl, ?_⟩
    rcases hA.2 with h | h
    · right
      rw [prob_compl_eq_one_sub hA.1, h, tsub_zero]
    · left
      rw [prob_compl_eq_one_sub hA.1, h, tsub_self]
  measurableSet_iUnion f hf := by
    refine ⟨MeasurableSet.iUnion fun n => (hf n).1, ?_⟩
    by_cases h : ∃ n, μ (f n) = 1
    · obtain ⟨n, hn⟩ := h
      right
      refine le_antisymm prob_le_one ?_
      rw [← hn]
      exact measure_mono (subset_iUnion f n)
    · push Not at h
      left
      exact measure_iUnion_null fun n => ((hf n).2.resolve_right (h n))

/-- The trivial `σ`-algebra is a sub-`σ`-algebra of the Borel `σ`-algebra. -/
theorem trivialSigma_le : trivialSigma μ ≤ mΩ := fun _ hA => hA.1

/-- Tex line 1727: `E_μ(f | 𝒩) = ∫ f dμ` for the trivial `σ`-algebra `𝒩`, `μ`-almost everywhere. -/
theorem condExp_trivialSigma {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[f | trivialSigma μ] =ᵐ[μ] fun _ => ∫ x, f x ∂μ := by
  refine (ae_eq_condExp_of_forall_setIntegral_eq (trivialSigma_le μ) hf
    (fun s _ _ => integrableOn_const) (fun s hs _ => ?_)
    stronglyMeasurable_const.aestronglyMeasurable).symm
  rw [setIntegral_const, smul_eq_mul]
  rcases hs.2 with h | h
  · rw [Measure.restrict_eq_zero.2 h, integral_zero_measure, measureReal_def, h,
      ENNReal.toReal_zero, zero_mul]
  · have hcompl : μ sᶜ = 0 := by
      rw [prob_compl_eq_one_sub hs.1, h, tsub_self]
    have hrestr : μ.restrict s = μ :=
      Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.1 hcompl |>.mono
        fun x hx => by simpa using hx)
    rw [hrestr, measureReal_def, h, ENNReal.toReal_one, one_mul]

/-- `E_μ(1_A | 𝒩) = μ(A)`, `μ`-almost everywhere. -/
theorem condExp_indicator_trivialSigma {A : Set Ω} (hA : MeasurableSet A) :
    condProbFn (trivialSigma μ) μ A =ᵐ[μ] fun _ => μ.real A := by
  refine (condExp_trivialSigma μ ((integrable_const (1 : ℝ)).indicator hA)).trans ?_
  refine Filter.Eventually.of_forall fun _ => ?_
  rw [integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one]

/-- Tex lines 1740 and 1741: `I_μ(𝒬 | 𝒩) = -∑_{A ∈ 𝒬} 1_A log μ(A)`, `μ`-almost everywhere. -/
theorem condInfoPart_trivialSigma {Q : Set (Set Ω)} (hQ : IsCountablePartition Q) :
    condInfoPart (trivialSigma μ) μ Q =ᵐ[μ]
      fun x => -∑' A : Q, (A : Set Ω).indicator (fun _ => Real.log (μ.real A)) x := by
  have : Countable Q := hQ.countable.to_subtype
  have hall : ∀ᵐ x ∂μ, ∀ A : Q, condProbFn (trivialSigma μ) μ A x = μ.real A :=
    ae_all_iff.2 fun A => condExp_indicator_trivialSigma μ (hQ.measurableSet A A.2)
  filter_upwards [hall] with x hx
  obtain ⟨A, hA, hxA⟩ := hQ.exists_mem x
  rw [condInfoPart_eq_of_mem _ μ hQ hA hxA,
    hQ.tsum_indicator_eq (fun B _ => Real.log (μ.real B)) hA hxA, hx ⟨A, hA⟩]

/-- Tex lines 1742 to 1746: `H_μ(𝒬 | 𝒩) = -∑_{A ∈ 𝒬} μ(A) log μ(A)`, the Shannon entropy
`H_μ(𝒬)` of `μ` with respect to `𝒬`, with values in `[0, ∞]`. -/
theorem condEntropyPart_trivialSigma {Q : Set (Set Ω)} (hQ : IsCountablePartition Q) :
    condEntropyPart (trivialSigma μ) μ Q =
      ∑' A : Q, ENNReal.ofReal (Real.negMulLog (μ.real A)) := by
  have : Countable Q := hQ.countable.to_subtype
  rw [condEntropyPart, lintegral_congr_ae ((condInfoPart_trivialSigma μ hQ).mono fun x hx => by
    rw [hx])]
  have hU : (⋃ A : Q, (A : Set Ω)) = univ := by
    rw [← sUnion_eq_iUnion, hQ.sUnion_eq]
  rw [← setLIntegral_univ, ← hU, lintegral_iUnion (s := fun A : Q => (A : Set Ω))
    (fun A => hQ.measurableSet A A.2)
    (fun A B hAB => hQ.pairwiseDisjoint A.2 B.2 (fun h => hAB (Subtype.ext h)))]
  refine tsum_congr fun A => ?_
  have hcongr : ∀ x ∈ (A : Set Ω),
      ENNReal.ofReal (-∑' B : Q, (B : Set Ω).indicator (fun _ => Real.log (μ.real B)) x) =
        ENNReal.ofReal (-Real.log (μ.real A)) := fun x hx => by
    rw [hQ.tsum_indicator_eq (fun B _ => Real.log (μ.real B)) A.2 hx]
  have hlog : 0 ≤ -Real.log (μ.real (A : Set Ω)) :=
    neg_nonneg.2 (Real.log_nonpos measureReal_nonneg measureReal_le_one)
  rw [setLIntegral_congr_fun (hQ.measurableSet A A.2) hcongr, setLIntegral_const,
    ← ofReal_measureReal, ← ENNReal.ofReal_mul hlog, Real.negMulLog]
  congr 1
  ring

end General

/-! ### Conditional measures and conditional expectations -/

section ConditionalMeasures

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- Tex lines 1758 to 1762: `∫ f dμ_x^ξ = E_μ(f | \widehat{ξ})(x)` for every `f ∈ L¹(μ)` and
`μ`-almost every `x`. -/
theorem integral_condMeas_ae_eq_condExp (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Set Ω)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    (fun x => ∫ y, f y ∂condMeas μ ξ x) =ᵐ[μ] μ[f | saturated ξ] :=
  (condExp_ae_eq_integral_condExpKernel (saturated_le ξ) hf).symm

/-- `μ_x^ξ(A) = E_μ(1_A | \widehat{ξ})(x)` for every Borel `A` and `μ`-almost every `x`. -/
theorem condMeas_real_ae_eq_condExp (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Set Ω)
    {A : Set Ω} (hA : MeasurableSet A) :
    (fun x => (condMeas μ ξ x).real A) =ᵐ[μ] condProbFn (saturated ξ) μ A :=
  condExpKernel_ae_eq_condExp (saturated_le ξ) hA

omit [StandardBorelSpace Ω] in
open Classical in
/-- The partition `{Ξ, Ξ^c}` of tex line 1692, as an atom map. -/
noncomputable def twoSetPartition (Ξ : Set Ω) (x : Ω) : Set Ω := if x ∈ Ξ then Ξ else Ξᶜ

omit [StandardBorelSpace Ω] in
/-- A set of the `σ`-algebra of `{Ξ, Ξ^c}` contains two points together when both lie in `Ξ` or
both lie outside `Ξ`. -/
theorem saturated_twoSetPartition {Ξ B : Set Ω}
    (hB : MeasurableSet[saturated (twoSetPartition Ξ)] B) {x y : Ω} (hxy : (x ∈ Ξ ↔ y ∈ Ξ)) :
    (x ∈ B ↔ y ∈ B) := by
  refine hB.2 x y ?_
  unfold twoSetPartition
  by_cases hx : x ∈ Ξ
  · rw [ite_eq_left hx]
    exact hxy.1 hx
  · rw [ite_eq_right hx]
    exact fun hy => hx (hxy.2 hy)

/-- Tex lines 1765 to 1770: for a Borel set `Ξ`, the normalised restriction
`μ_Ξ(A) = μ(A ∩ Ξ)/μ(Ξ)` agrees with the conditional measure of `μ` for the partition `{Ξ, Ξ^c}`
at `μ`-almost every point of `Ξ`. The article assumes `μ(Ξ) > 0`, under which `μ_Ξ` is defined;
the almost-everywhere statement holds without it, since it is empty when `μ(Ξ) = 0`. -/
theorem condMeas_twoSetPartition_eq_cond (μ : Measure Ω) [IsProbabilityMeasure μ] {Ξ : Set Ω}
    (hΞ : MeasurableSet Ξ) :
    ∀ᵐ x ∂μ, x ∈ Ξ → condMeas μ (twoSetPartition Ξ) x = μ[|Ξ] := by
  classical
  set K : Ω → Measure Ω := fun x => if x ∈ Ξ then μ[|Ξ] else μ[|Ξᶜ]
  have hΞsat : MeasurableSet[saturated (twoSetPartition Ξ)] Ξ := by
    refine ⟨hΞ, fun x y hy => ?_⟩
    unfold twoSetPartition at hy
    by_cases hx : x ∈ Ξ
    · rw [ite_eq_left hx] at hy
      exact ⟨fun _ => hy, fun _ => hx⟩
    · rw [ite_eq_right hx] at hy
      exact ⟨fun h => absurd h hx, fun h => absurd h hy⟩
  have hK : ∀ A, MeasurableSet A →
      Measurable[saturated (twoSetPartition Ξ)] fun x => K x A := by
    intro A _
    have : (fun x => K x A) = fun x => if x ∈ Ξ then μ[|Ξ] A else μ[|Ξᶜ] A := by
      funext x
      simp only [K]
      split_ifs <;> rfl
    rw [this]
    exact Measurable.ite hΞsat measurable_const measurable_const
  have hint : ∀ A B, MeasurableSet A → MeasurableSet[saturated (twoSetPartition Ξ)] B →
      ∫⁻ x in B, K x A ∂μ = μ (A ∩ B) := by
    intro A B hA hB
    have hBm : MeasurableSet B := hB.1
    have hsplit : ∫⁻ x in B, K x A ∂μ =
        μ (B ∩ Ξ) * μ[A|Ξ] + μ (B ∩ Ξᶜ) * μ[A|Ξᶜ] := by
      rw [← lintegral_indicator hBm, ← lintegral_add_compl _ hΞ]
      have h1 : ∫⁻ x in Ξ, B.indicator (fun x => K x A) x ∂μ =
          ∫⁻ x in Ξ, B.indicator (fun _ => μ[A|Ξ]) x ∂μ := by
        refine setLIntegral_congr_fun hΞ fun x hx => ?_
        by_cases hxB : x ∈ B <;> simp [K, hx, hxB]
      have h2 : ∫⁻ x in Ξᶜ, B.indicator (fun x => K x A) x ∂μ =
          ∫⁻ x in Ξᶜ, B.indicator (fun _ => μ[A|Ξᶜ]) x ∂μ := by
        refine setLIntegral_congr_fun hΞ.compl fun x hx => ?_
        have hx' : x ∉ Ξ := hx
        by_cases hxB : x ∈ B <;> simp [K, hx', hxB]
      rw [h1, h2, lintegral_indicator_const hBm, lintegral_indicator_const hBm,
        Measure.restrict_apply hBm, Measure.restrict_apply hBm, mul_comm, mul_comm (μ[A|Ξᶜ])]
    rw [hsplit]
    have hcase : ∀ T, (T = Ξ ∨ T = Ξᶜ) → (B ∩ T = ∅ ∨ T ⊆ B) := by
      intro T hT
      by_cases hne : (B ∩ T).Nonempty
      · right
        obtain ⟨x, hxB, hxT⟩ := hne
        intro y hyT
        have hxy : x ∈ Ξ ↔ y ∈ Ξ := by
          rcases hT with rfl | rfl
          · exact ⟨fun _ => hyT, fun _ => hxT⟩
          · exact ⟨fun h => absurd h hxT, fun h => absurd h hyT⟩
        exact (saturated_twoSetPartition hB hxy).1 hxB
      · left
        exact not_nonempty_iff_eq_empty.1 hne
    have hpart : ∀ T : Set Ω, MeasurableSet T → (B ∩ T = ∅ ∨ T ⊆ B) →
        μ (B ∩ T) * μ[A|T] = μ (A ∩ B ∩ T) := by
      intro T hT hc
      rcases hc with hBT | hTB
      · rw [hBT, measure_empty, zero_mul, inter_assoc, hBT, inter_empty, measure_empty]
      · have hAB : A ∩ B ∩ T = T ∩ A := by
          ext y
          simp only [mem_inter_iff]
          exact ⟨fun h => ⟨h.2, h.1.1⟩, fun h => ⟨⟨h.2, hTB h.1⟩, h.1⟩⟩
        rw [inter_eq_right.2 hTB, cond_apply hT, ← mul_assoc, hAB]
        by_cases h0 : μ T = 0
        · rw [h0, measure_mono_null inter_subset_left h0, mul_zero]
        · rw [ENNReal.mul_inv_cancel h0 (measure_ne_top _ _), one_mul]
    rw [hpart Ξ hΞ (hcase _ (Or.inl rfl)), hpart Ξᶜ hΞ.compl (hcase _ (Or.inr rfl)), ← sdiff_eq,
      measure_inter_add_sdiff _ hΞ]
  have h := condMeas_unique μ (twoSetPartition Ξ) K hK hint
  filter_upwards [h] with x hx hxΞ
  rw [← hx]
  simp [K, hxΞ]

end ConditionalMeasures

/-! ### The canonical partition -/

section Canonical

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The canonical partition `𝒫 = {[i]}` of `Σ` into the cylinders of length one. -/
def canonicalPartition (α : Type*) : Set (Set (ℤ → α)) := range fun a : α => {y | y 0 = a}

/-- The canonical partition is a countable Borel partition. -/
theorem isCountablePartition_canonicalPartition :
    IsCountablePartition (canonicalPartition α) where
  countable := countable_range _
  measurableSet := by
    rintro _ ⟨a, rfl⟩
    exact show MeasurableSet ((fun y : ℤ → α => y 0) ⁻¹' {a}) from
      measurable_pi_apply (0 : ℤ) (measurableSet_singleton a)
  pairwiseDisjoint := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
    refine Set.disjoint_left.2 fun x (hx : x 0 = a) (hy : x 0 = b) => hab ?_
    rw [← hx, ← hy]
  sUnion_eq := by
    refine eq_univ_of_forall fun x => ⟨{y | y 0 = x 0}, ⟨x 0, rfl⟩, rfl⟩

/-- The library's `condInfo μ ξ` is the conditional information `I_μ(𝒫 | \widehat{ξ})` of the
canonical partition, `μ`-almost everywhere. -/
theorem condInfo_ae_eq_condInfoPart (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (ξ : (ℤ → α) → Set (ℤ → α)) :
    condInfo μ ξ =ᵐ[μ] condInfoPart (saturated ξ) μ (canonicalPartition α) := by
  have hall : ∀ᵐ x ∂μ, ∀ a : α,
      (condMeas μ ξ x).real {y | y 0 = a} = condProbFn (saturated ξ) μ {y | y 0 = a} x :=
    ae_all_iff.2 fun a => condMeas_real_ae_eq_condExp μ ξ
      (show MeasurableSet ((fun y : ℤ → α => y 0) ⁻¹' {a}) from
        measurable_pi_apply (0 : ℤ) (measurableSet_singleton a))
  filter_upwards [hall] with x hx
  rw [condInfoPart_eq_of_mem _ μ isCountablePartition_canonicalPartition ⟨x 0, rfl⟩
    (show x 0 = x 0 from rfl), condInfo, hx (x 0)]

/-- The library's `condEntropy μ ξ` is the conditional entropy `H_μ(𝒫 | \widehat{ξ})` of the
canonical partition, which is finite. -/
theorem condEntropy_eq_toReal_condEntropyPart (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ]
    (ξ : (ℤ → α) → Set (ℤ → α)) :
    condEntropy μ ξ = (condEntropyPart (saturated ξ) μ (canonicalPartition α)).toReal := by
  rw [condEntropy, integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (condInfo_nonneg μ ξ))
    (integrable_condInfo μ ξ).aestronglyMeasurable, condEntropyPart]
  congr 1
  exact lintegral_congr_ae ((condInfo_ae_eq_condInfoPart μ ξ).mono fun x hx =>
    congrArg ENNReal.ofReal hx)

/-- The partition `𝒫_0^{n-1}` of `Σ` into the cylinders of length `n` (tex lines 1801 to
1884). -/
def blockPartition (α : Type*) (n : ℕ) : Set (Set (ℤ → α)) :=
  range (BoxLike.cylinder (n := n) (α := α))

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Distinct words of the same length have distinct cylinders. -/
theorem cylinder_injective (n : ℕ) :
    Function.Injective (BoxLike.cylinder : (Fin n → α) → Set (ℤ → α)) := by
  intro w w' h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  · set x : ℤ → α := fun k => if hk : 0 ≤ k ∧ k < n then w ⟨k.toNat, by omega⟩ else w ⟨0, hn⟩
    have hx : x ∈ BoxLike.cylinder w := fun k => by
      have hk : 0 ≤ (k : ℤ) ∧ (k : ℤ) < n := ⟨by positivity, by exact_mod_cast k.2⟩
      simp only [x, dite_eq_left hk]
      congr 1
    have hx' : x ∈ BoxLike.cylinder w' := h ▸ hx
    funext k
    exact (hx k).symm.trans (hx' k)

/-- The cylinders of length `n` form a countable Borel partition. -/
theorem isCountablePartition_blockPartition (n : ℕ) :
    IsCountablePartition (blockPartition α n) where
  countable := countable_range _
  measurableSet := by
    rintro _ ⟨w, rfl⟩
    exact BoxLike.measurableSet_cylinder w
  pairwiseDisjoint := by
    rintro _ ⟨w, rfl⟩ _ ⟨w', rfl⟩ hww'
    refine Set.disjoint_left.2 fun x hx hx' => hww' ?_
    have : w = w' := funext fun k => (hx k).symm.trans (hx' k)
    rw [this]
  sUnion_eq := eq_univ_of_forall fun x =>
    ⟨BoxLike.cylinder (block n x), ⟨block n x, rfl⟩, fun _ => rfl⟩

/-- The library's block entropy is the Shannon entropy `H_μ(𝒫_0^{n-1}) = H_μ(𝒫_0^{n-1} | 𝒩)` of
the partition into cylinders of length `n`, the conditional entropy given the trivial
`σ`-algebra (tex lines 1663 to 1669 and 1880 to 1884). -/
theorem blockEntropy_eq_toReal_condEntropyPart (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ]
    (n : ℕ) :
    blockEntropy μ n = (condEntropyPart (trivialSigma μ) μ (blockPartition α n)).toReal := by
  rw [condEntropyPart_trivialSigma μ (isCountablePartition_blockPartition n), blockPartition,
    tsum_range (fun A : Set (ℤ → α) => ENNReal.ofReal (Real.negMulLog (μ.real A)))
      (cylinder_injective n), tsum_fintype, ENNReal.toReal_sum fun _ _ => ENNReal.ofReal_ne_top,
    blockEntropy]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [ENNReal.toReal_ofReal (Real.negMulLog_nonneg measureReal_nonneg measureReal_le_one)]

end Canonical

end BoxLike
