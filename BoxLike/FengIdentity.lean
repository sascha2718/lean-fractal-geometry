module

/-
Feng's information-sum identity, D.-J. Feng, *Dimension of invariant measures for affine iterated
function systems*, Duke Math. J. 172 (2023), arXiv:1901.01691v2, Lemma 4.6, first identity of
(4.16), proved for the planar partitions `ξ_i` of `sec:entropies` (tex lines 1775 to 1792). The
proof is Feng's, with `n = 1` in his Lemmas 4.4 and 4.5: Lemma 4.4(1), the invariance property
`ξ(𝐢) ∩ [i_0] = σ^{-1}(ξ(σ 𝐢))`; Lemma 4.5(1), the transport
`μ_𝐢^{σ^{-1}ξ}(A) = μ_{σ 𝐢}^ξ(σ A)`; Lemma 4.5(2), the chain rule
`μ_𝐢^{σ^{-1}ξ}(A) = μ_𝐢^ξ(A ∩ [i_0]) / μ_𝐢^ξ([i_0])`, proved through his (4.14); and the induction
(4.18). Feng writes the induction with the chain rule for conditional information (his Lemma
2.1(ii), (iii)); here it is the product formula of Lemma 4.5(3), of which (4.18) is the logarithm.

The general part works on the full shift over a finite alphabet, for an invariant probability
measure `μ` and a measurable partition `ξ` of a Borel set `D` of full measure with the invariance
property `σ^{-1}(ξ(σ 𝐢)) = ξ(𝐢) ∩ [i_0]` for `𝐢 ∈ D`. Write `ζ = ξ ∨ 𝒫` for the partition with
atoms `ξ(𝐢) ∩ [i_0]` and `η = σ^{-1}ξ` for the partition with atoms `σ^{-1}(ξ(σ 𝐢))`. Neither
ergodicity nor Feng's constant-multiplicity assumption (4.7) is used.

1. `condMeas_refineZero`, Feng's Lemma 4.5(2) for `ζ`: `μ_𝐢^ζ = (μ_𝐢^ξ)_{[i_0]}`, the conditional
   measure of `μ_𝐢^ξ` on the cylinder `[i_0]`, for `μ`-almost every `𝐢`. By Blackwell's theorem
   (`saturated_eq_comap`) every set of `\widehat{ζ}` meets each cylinder `[a]` in a set of
   `\widehat{ξ}`, which gives Feng's computation (4.14); uniqueness of the disintegration
   concludes.
2. `condMeas_pullShift`, Feng's Lemma 4.5(1): `μ_𝐢^η = (σ^{-1})_* μ_{σ 𝐢}^ξ` for an invariant
   measure.
3. `condMeas_pullShift_ae_eq_refineZero`: Feng's consequence `ξ ∨ 𝒫 = σ^{-1}ξ` of Lemma 4.4(1).
   The partitions here are partitions of the whole shift with the extra atom `Σ ∖ D`, so the atoms
   of `η` and `ζ` agree on `D` only, and their conditional measures agree almost everywhere.
4. `condMeas_cylinder_succ`, `condMeas_cylinder_eq_prod`: Feng's Lemma 4.5(3),
   `μ_𝐢^ξ([i_0 ⋯ i_n]) = μ_𝐢^ξ([i_0]) μ_{σ 𝐢}^ξ([i_1 ⋯ i_n])`, and by induction
   `μ_𝐢^ξ(𝒫_0^{n-1}(𝐢)) = ∏_{k<n} μ_{σ^k 𝐢}^ξ([i_k])`.
5. `infoSum_of_pullShift`: taking logarithms, with `μ_{σ^k 𝐢}^ξ([i_k]) > 0` (Feng, Lemma 2.2),
   gives (4.18), which is the first identity of (4.16).

For the box-like partitions `ξ_i` of `Σ'` the invariance property is the relation
`π(𝐣) - π(𝐢) = A_{i_0}(π(σ 𝐣) - π(σ 𝐢))` for `j_0 = i_0` together with
`A_{i_0} V_{σ 𝐢}^i = V_𝐢^i`, which in the box-like case says that the slow axis of `σ 𝐢` is the slow
axis of `𝐢` moved by the orientation of `A_{i_0}`.

* `refineZero`, `pullShift`: the partitions `ξ ∨ 𝒫` and `σ^{-1}ξ`.
* `isMeasurablePartition_refineZero`, `exists_saturated_inter_zeroCyl`: `ξ ∨ 𝒫` is measurable,
  and its sets meet each cylinder `[a]` in a set of `\widehat{ξ}`.
* `condMeas_refineZero`, `condMeas_pullShift`, `condMeas_pullShift_ae_eq_refineZero`: the three
  identities of conditional measures above.
* `cylinder_block_succ`, `condMeas_zeroCyl_pos`: `[i_0 ⋯ i_n] = [i_0] ∩ σ^{-1}[i_1 ⋯ i_n]` and
  Feng's Lemma 2.2 for `𝒫`.
* `condMeas_cylinder_succ`, `condMeas_cylinder_eq_prod`, `infoSum_of_pullShift`: the general
  identity.
* `samePast_shift_one_iff`, `System.slowAxis_shift_one`, `System.proj_sub_mem_oseledets_iff`,
  `System.pullShift_xi`: the invariance property of the box-like `ξ_i`.
* `System.infoSum_xi`: the identity for the box-like `ξ_i`, every invariant `μ` with
  `λ_2 < λ_1` and `μ(Σ') = 1`, and every `i`.
* `fengInfoSum_holds`: the predicate `FengInfoSum` of `BoxLike/LiteratureFeng.lean` holds.
-/
public import BoxLike.FengEntropy
public import BoxLike.OseledetsBridge
public import BoxLike.ConditionalLemmas
public import BoxLike.Attractor
public import BoxLike.SigmaMeasure
public import Mathlib.Probability.ConditionalProbability

@[expose] public section

namespace BoxLike

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

universe u

/-! ### The partitions `ξ ∨ 𝒫` and `σ^{-1}ξ` -/

section General

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

omit [Fintype α] in
/-- The cylinder `[a] = {𝐢 : i_0 = a}` of the canonical partition `𝒫` of `sec:entropies` is
Borel. -/
theorem measurableSet_zeroCyl (a : α) : MeasurableSet {y : ℤ → α | y 0 = a} :=
  show MeasurableSet ((fun y : ℤ → α => y 0) ⁻¹' {a}) from
    measurable_pi_apply (0 : ℤ) (measurableSet_singleton a)

/-- The join `ξ ∨ 𝒫` of a partition with the canonical partition `𝒫 = {[a]}` of `sec:entropies`:
the atom of `𝐢` is `ξ(𝐢) ∩ [i_0]` (Feng, Lemma 4.4(1), the partition `ξ_i ∨ 𝒫_0^{n-1}` for
`n = 1`). -/
def refineZero (ξ : (ℤ → α) → Set (ℤ → α)) (x : ℤ → α) : Set (ℤ → α) :=
  ξ x ∩ {y | y 0 = x 0}

/-- The partition `σ^{-1}ξ`: the atom of `𝐢` is `σ^{-1}(ξ(σ 𝐢))` (Feng, Lemma 4.4(1), `n = 1`). -/
def pullShift (ξ : (ℤ → α) → Set (ℤ → α)) (x : ℤ → α) : Set (ℤ → α) :=
  shift 1 ⁻¹' ξ (shift 1 x)

/-- The join `ξ ∨ 𝒫` of a measurable partition with `𝒫` is a measurable partition: its atoms are
the fibres of `𝐢 ↦ (f(𝐢), i_0)` for the Borel map `f` inducing `ξ`. -/
theorem isMeasurablePartition_refineZero {ξ : (ℤ → α) → Set (ℤ → α)}
    (hξ : IsMeasurablePartition ξ) : IsMeasurablePartition (refineZero ξ) := by
  obtain ⟨f, hf, hfξ⟩ := hξ
  have he := MeasureTheory.measurableEmbedding_embeddingReal (ℝ × α)
  refine ⟨fun x => MeasureTheory.embeddingReal (ℝ × α) (f x, x 0),
    he.measurable.comp (hf.prodMk (measurable_pi_apply 0)), fun x y => ?_⟩
  simp only [refineZero, mem_inter_iff, mem_ofPred_eq, he.injective.eq_iff, Prod.mk.injEq, hfξ]

/-- A set of `\widehat{ξ ∨ 𝒫}` meets every cylinder `[a]` in a set of `\widehat{ξ}`. This is
Blackwell's theorem `saturated_eq_comap` for the Borel map `𝐢 ↦ (f(𝐢), i_0)` inducing `ξ ∨ 𝒫`:
the set is the preimage of a Borel set `U ⊆ ℝ × α`, and its trace on `[a]` is the trace of
`f^{-1}(U_a)`, `U_a` the section of `U` at `a`. -/
theorem exists_saturated_inter_zeroCyl {ξ : (ℤ → α) → Set (ℤ → α)} {f : (ℤ → α) → ℝ}
    (hf : Measurable f) (hfξ : ∀ x y, y ∈ ξ x ↔ f y = f x) {B : Set (ℤ → α)}
    (hB : MeasurableSet[saturated (refineZero ξ)] B) (a : α) :
    ∃ B', MeasurableSet[saturated ξ] B' ∧ B ∩ {y | y 0 = a} = B' ∩ {y | y 0 = a} := by
  have hG : Measurable fun x : ℤ → α => (f x, x 0) := hf.prodMk (measurable_pi_apply 0)
  have hGξ : ∀ x y, y ∈ refineZero ξ x ↔ (f y, y 0) = (f x, x 0) := fun x y => by
    simp only [refineZero, mem_inter_iff, mem_ofPred_eq, Prod.mk.injEq, hfξ]
  rw [saturated_eq_comap hG hGξ] at hB
  obtain ⟨U, hU, rfl⟩ := hB
  refine ⟨f ⁻¹' ((fun r => (r, a)) ⁻¹' U),
    ⟨hf (measurable_prodMk_right hU), fun x y hxy => ?_⟩, ?_⟩
  · simp only [mem_preimage, (hfξ x y).1 hxy]
  · ext x
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, rfl⟩
    · rintro ⟨h, rfl⟩
      exact ⟨h, rfl⟩

/-- Feng, Lemma 4.5(2), with `n = 1`, for the partition `ξ ∨ 𝒫`: its conditional measures are
the conditional measures of `ξ` conditioned on the cylinder `[i_0]`,
`μ_𝐢^{ξ ∨ 𝒫}(A) = μ_𝐢^ξ(A ∩ [i_0]) / μ_𝐢^ξ([i_0])`, for `μ`-almost every `𝐢`. The family on the
right is `\widehat{ξ ∨ 𝒫}`-measurable; its integral over a set `B` of `\widehat{ξ ∨ 𝒫}` splits over
the cylinders `[a]`, on each of which `B` is a set `B'_a` of `\widehat{ξ}`
(`exists_saturated_inter_zeroCyl`), and the pull-out property of `μ^ξ` on `B'_a` gives
`μ(A ∩ B)`. Uniqueness of the disintegration, `condMeas_unique`, concludes. -/
theorem condMeas_refineZero (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ]
    {ξ : (ℤ → α) → Set (ℤ → α)} (hξ : IsMeasurablePartition ξ) :
    ∀ᵐ x ∂μ, condMeas μ (refineZero ξ) x = (condMeas μ ξ x)[|{y | y 0 = x 0}] := by
  classical
  obtain ⟨f, hf, hfξ⟩ := hξ
  set C : α → Set (ℤ → α) := fun a => {y | y 0 = a} with hC
  have hCm : ∀ a, MeasurableSet (C a) := measurableSet_zeroCyl
  have hle : saturated ξ ≤ saturated (refineZero ξ) :=
    saturated_mono fun x => inter_subset_left
  have hCsat : ∀ a, MeasurableSet[saturated (refineZero ξ)] (C a) := fun a =>
    ⟨hCm a, fun x y hxy => by
      simp only [hC, mem_ofPred_eq, show y 0 = x 0 from hxy.2]⟩
  set F : Set (ℤ → α) → α → (ℤ → α) → ℝ≥0∞ := fun A a x =>
    (condMeas μ ξ x (C a))⁻¹ * condMeas μ ξ x (C a ∩ A) with hF
  have hFm : ∀ A, MeasurableSet A → ∀ a, Measurable[saturated ξ] (F A a) := fun A hA a =>
    (measurable_condMeas μ ξ (hCm a)).inv.mul (measurable_condMeas μ ξ ((hCm a).inter hA))
  have hKF : ∀ A x, (condMeas μ ξ x)[|C (x 0)] A = F A (x 0) x := fun A x => by
    rw [cond_apply (hCm _)]
  have hpt : ∀ p q : ℝ≥0∞, q ≤ p → p ≠ ∞ → p⁻¹ * q * p = q := by
    intro p q hqp hp
    rcases eq_or_ne p 0 with rfl | h0
    · simp [nonpos_iff_eq_zero.1 hqp]
    · rw [mul_comm p⁻¹ q, mul_assoc, ENNReal.inv_mul_cancel h0 hp, mul_one]
  have hdisj : ∀ B : Set (ℤ → α), Pairwise (Function.onFun Disjoint fun a => B ∩ C a) :=
    fun B a b hab => Set.disjoint_left.2 fun x hx hy => hab (hx.2.symm.trans hy.2)
  have hcover : ∀ B : Set (ℤ → α), B = ⋃ a, B ∩ C a := fun B => by
    ext x
    simp only [mem_iUnion, mem_inter_iff, hC, mem_ofPred_eq]
    exact ⟨fun h => ⟨x 0, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  refine (condMeas_unique μ (refineZero ξ) (fun x => (condMeas μ ξ x)[|C (x 0)]) ?_ ?_).mono
    fun x hx => hx.symm
  · intro A hA
    have e : (fun x => (condMeas μ ξ x)[|C (x 0)] A) =
        fun x => ∑ a, (C a).indicator (F A a) x := by
      funext x
      rw [hKF, Finset.sum_eq_single (x 0)]
      · rw [indicator_of_mem (show x ∈ C (x 0) from rfl)]
      · intro a _ ha
        exact indicator_of_notMem (show x ∉ C a from fun h => ha h.symm) _
      · simp
    rw [e]
    exact Finset.measurable_sum _ fun a _ => ((hFm A hA a).mono hle le_rfl).indicator (hCsat a)
  · intro A B hA hB
    have hBm : MeasurableSet B := hB.1
    have key : ∀ a, ∫⁻ x in B ∩ C a, (condMeas μ ξ x)[|C (x 0)] A ∂μ = μ (A ∩ (B ∩ C a)) := by
      intro a
      obtain ⟨B', hB', hBB'⟩ := exists_saturated_inter_zeroCyl hf hfξ hB a
      calc ∫⁻ x in B ∩ C a, (condMeas μ ξ x)[|C (x 0)] A ∂μ
          = ∫⁻ x in C a ∩ B', F A a x ∂μ := by
            rw [hBB', inter_comm]
            refine setLIntegral_congr_fun ((hCm a).inter hB'.1) fun x hx => ?_
            rw [hKF, show x 0 = a from hx.1]
        _ = ∫⁻ x in B', F A a x * condMeas μ ξ x (C a) ∂μ :=
            (setLIntegral_mul_condMeas μ ξ (hFm A hA a) (hCm a) hB').symm
        _ = ∫⁻ x in B', condMeas μ ξ x (C a ∩ A) ∂μ :=
            lintegral_congr fun x => hpt _ _ (measure_mono inter_subset_left) (measure_ne_top _ _)
        _ = μ ((C a ∩ A) ∩ B') := setLIntegral_condMeas μ ξ ((hCm a).inter hA) hB'
        _ = μ (A ∩ (B ∩ C a)) := by
            rw [hBB']
            congr 1
            ext x
            simp only [mem_inter_iff]
            tauto
    calc ∫⁻ x in B, (condMeas μ ξ x)[|C (x 0)] A ∂μ
        = ∑' a, ∫⁻ x in B ∩ C a, (condMeas μ ξ x)[|C (x 0)] A ∂μ := by
          conv_lhs => rw [hcover B]
          exact lintegral_iUnion (fun a => hBm.inter (hCm a)) (hdisj B) _
      _ = ∑ a, μ (A ∩ (B ∩ C a)) := by
          rw [tsum_fintype]
          exact Finset.sum_congr rfl fun a _ => key a
      _ = μ (A ∩ B) := by
          have e : A ∩ B = ⋃ a, A ∩ (B ∩ C a) := by
            conv_lhs => rw [hcover B]
            rw [inter_iUnion]
          rw [e, measure_iUnion (fun a b hab => (hdisj B hab).mono inter_subset_right
            inter_subset_right) (fun a => hA.inter (hBm.inter (hCm a))), tsum_fintype]

/-- The transport of conditional measures under the shift, Feng, Lemma 4.5(1), with `n = 1`: for
an invariant measure `μ`, the conditional measures of `σ^{-1}ξ` are
`μ_𝐢^{σ^{-1}ξ} = (σ^{-1})_* μ_{σ 𝐢}^ξ`, that is `μ_𝐢^{σ^{-1}ξ}(σ^{-1}A) = μ_{σ 𝐢}^ξ(A)`, for
`μ`-almost every `𝐢`. The shift maps `\widehat{σ^{-1}ξ}` to `\widehat{ξ}`, and the defining
identity of the right-hand side follows from the invariance of `μ`. -/
theorem condMeas_pullShift {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (ξ : (ℤ → α) → Set (ℤ → α)) :
    ∀ᵐ x ∂μ, condMeas μ (pullShift ξ) x = (condMeas μ ξ (shift 1 x)).map (shift (-1)) := by
  have hback : ∀ x : ℤ → α, shift (-1) (shift 1 x) = x := fun x => by
    rw [shift_shift]; simp
  have hfwd : ∀ x : ℤ → α, shift 1 (shift (-1) x) = x := fun x => by
    rw [shift_shift]; simp
  have hσ : @Measurable _ _ (saturated (pullShift ξ)) (saturated ξ) (shift 1) := by
    intro B hB
    exact ⟨measurable_shift 1 hB.1, fun x y hxy => hB.2 _ _ hxy⟩
  refine (condMeas_unique μ (pullShift ξ) _ ?_ ?_).mono fun x hx => hx.symm
  · intro A hA
    simp_rw [Measure.map_apply (measurable_shift (-1)) hA]
    exact (measurable_condMeas μ ξ (measurable_shift (-1) hA)).comp hσ
  · intro A B hA hB
    have hA' : MeasurableSet (shift (-1) ⁻¹' A) := measurable_shift (-1) hA
    have hB' : MeasurableSet[saturated ξ] (shift (-1) ⁻¹' B) := by
      refine ⟨measurable_shift (-1) hB.1, fun z w hzw => ?_⟩
      have h : shift (-1) w ∈ pullShift ξ (shift (-1) z) := by
        simp only [pullShift, mem_preimage, hfwd]
        exact hzw
      exact hB.2 _ _ h
    have hBB : shift 1 ⁻¹' (shift (-1) ⁻¹' B) = B := by
      ext x
      simp [hback]
    have hAA : shift 1 ⁻¹' (shift (-1) ⁻¹' A) = A := by
      ext x
      simp [hback]
    calc ∫⁻ x in B, (condMeas μ ξ (shift 1 x)).map (shift (-1)) A ∂μ
        = ∫⁻ x in shift 1 ⁻¹' (shift (-1) ⁻¹' B),
            condMeas μ ξ (shift 1 x) (shift (-1) ⁻¹' A) ∂μ := by
          rw [hBB]
          simp_rw [Measure.map_apply (measurable_shift (-1)) hA]
      _ = ∫⁻ z in shift (-1) ⁻¹' B, condMeas μ ξ z (shift (-1) ⁻¹' A) ∂μ :=
          hinv.setLIntegral_comp_preimage hB'.1
            ((measurable_condMeas μ ξ hA').mono (saturated_le ξ) le_rfl)
      _ = μ (shift (-1) ⁻¹' A ∩ shift (-1) ⁻¹' B) := setLIntegral_condMeas μ ξ hA' hB'
      _ = μ (shift 1 ⁻¹' (shift (-1) ⁻¹' A ∩ shift (-1) ⁻¹' B)) :=
          (hinv.measure_preimage (hA'.inter hB'.1).nullMeasurableSet).symm
      _ = μ (A ∩ B) := by rw [preimage_inter, hAA, hBB]

/-- Feng's `ξ ∨ 𝒫 = σ^{-1}ξ`, the consequence of Lemma 4.4(1): the invariance property
`σ^{-1}(ξ(σ 𝐢)) = ξ(𝐢) ∩ [i_0]` on a Borel set `D` of full measure makes the partitions
`σ^{-1}ξ` and `ξ ∨ 𝒫` agree modulo `μ`: their conditional measures agree
almost everywhere (`condMeas_ae_eq_of_cut`). The hypothesis `hout` says that the atoms of
`σ^{-1}ξ` at the points outside `D` avoid `D`. -/
theorem condMeas_pullShift_ae_eq_refineZero (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ]
    {ξ : (ℤ → α) → Set (ℤ → α)} (hξ : IsMeasurablePartition ξ) {D : Set (ℤ → α)}
    (hD : MeasurableSet D) (hD0 : μ Dᶜ = 0) (hin : ∀ x ∈ D, pullShift ξ x = refineZero ξ x)
    (hsub : ∀ x ∈ D, ξ x ⊆ D) (hout : ∀ x ∉ D, pullShift ξ x ⊆ Dᶜ) :
    ∀ᵐ x ∂μ, condMeas μ (pullShift ξ) x = condMeas μ (refineZero ξ) x :=
  condMeas_ae_eq_of_cut μ (isMeasurablePartition_refineZero hξ) hD hD0
    (fun x hx => by
      rw [hin x hx]
      exact (inter_eq_left.2 (show refineZero ξ x ⊆ D from
        inter_subset_left.trans (hsub x hx))).symm) hout

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The cylinder of `n + 1` symbols splits as `[i_0 ⋯ i_n] = [i_0] ∩ σ^{-1}[i_1 ⋯ i_n]`. -/
theorem cylinder_block_succ (n : ℕ) (x : ℤ → α) :
    cylinder (block (n + 1) x) =
      {y | y 0 = x 0} ∩ shift 1 ⁻¹' cylinder (block n (shift 1 x)) := by
  ext y
  simp only [mem_cylinder, block_apply, mem_inter_iff, mem_ofPred_eq, mem_preimage, shift_apply]
  constructor
  · intro h
    refine ⟨by simpa using h 0, fun k => ?_⟩
    have := h k.succ
    simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one] at this
    rwa [add_comm (1 : ℤ)]
  · rintro ⟨h0, h⟩ k
    refine Fin.cases ?_ (fun k => ?_) k
    · simpa using h0
    · have := h k
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
      rwa [add_comm (1 : ℤ)] at this

/-- Feng, Lemma 2.2, for the canonical partition `𝒫`: `μ_𝐢^ξ([i_0]) > 0` for `μ`-almost every
`𝐢`. -/
theorem condMeas_zeroCyl_pos (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (ξ : (ℤ → α) → Set (ℤ → α)) : ∀ᵐ x ∂μ, 0 < condMeas μ ξ x {y | y 0 = x 0} := by
  have h : ∀ᵐ x ∂μ, ∀ a : α, x ∈ {y : ℤ → α | y 0 = a} → 0 < condMeas μ ξ x {y | y 0 = a} :=
    ae_all_iff.2 fun a => condMeas_pos_of_mem μ ξ (measurableSet_zeroCyl a)
  filter_upwards [h] with x hx using hx (x 0) rfl

variable {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ] {ξ : (ℤ → α) → Set (ℤ → α)}
  {D : Set (ℤ → α)}

/-- Feng, Lemma 4.5(3), with `n = 1`: under the invariance property,
`μ_𝐢^ξ([i_0 ⋯ i_n]) = μ_𝐢^ξ([i_0]) μ_{σ 𝐢}^ξ([i_1 ⋯ i_n])` for every `n` and `μ`-almost every `𝐢`.
By `cylinder_block_succ` and Lemma 4.4(1) (`condMeas_refineZero`), the left-hand side is
`μ_𝐢^ξ([i_0]) μ_𝐢^{ξ ∨ 𝒫}(σ^{-1}[i_1 ⋯ i_n])`; the conditional measures of `ξ ∨ 𝒫` are those of
`σ^{-1}ξ` (`condMeas_pullShift_ae_eq_refineZero`), which are transported from those of `ξ` at
`σ 𝐢` (`condMeas_pullShift`). -/
theorem condMeas_cylinder_succ (hinv : MeasurePreserving (shift 1) μ μ)
    (hξ : IsMeasurablePartition ξ) (hD : MeasurableSet D) (hD0 : μ Dᶜ = 0)
    (hin : ∀ x ∈ D, pullShift ξ x = refineZero ξ x) (hsub : ∀ x ∈ D, ξ x ⊆ D)
    (hout : ∀ x ∉ D, pullShift ξ x ⊆ Dᶜ) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, condMeas μ ξ x (cylinder (block (n + 1) x)) =
      condMeas μ ξ x {y | y 0 = x 0} *
        condMeas μ ξ (shift 1 x) (cylinder (block n (shift 1 x))) := by
  filter_upwards [condMeas_pullShift hinv ξ,
    condMeas_pullShift_ae_eq_refineZero μ hξ hD hD0 hin hsub hout, condMeas_refineZero μ hξ,
    condMeas_zeroCyl_pos μ ξ] with x hT hE hC hpos n
  have hfwd : ∀ z : ℤ → α, shift 1 (shift (-1) z) = z := fun z => by
    rw [shift_shift]; simp
  set Cn := cylinder (block n (shift 1 x)) with hCn
  have hmeas : MeasurableSet (shift 1 ⁻¹' Cn) := measurable_shift 1 (measurableSet_cylinder _)
  have hpre : shift (-1) ⁻¹' (shift 1 ⁻¹' Cn) = Cn := by
    ext z
    simp [hfwd]
  rw [cylinder_block_succ]
  calc condMeas μ ξ x ({y | y 0 = x 0} ∩ shift 1 ⁻¹' Cn)
      = condMeas μ ξ x {y | y 0 = x 0} *
          (condMeas μ ξ x)[|{y | y 0 = x 0}] (shift 1 ⁻¹' Cn) := by
        rw [cond_apply (measurableSet_zeroCyl _), ← mul_assoc,
          ENNReal.mul_inv_cancel hpos.ne' (measure_ne_top _ _), one_mul]
    _ = condMeas μ ξ x {y | y 0 = x 0} * condMeas μ (pullShift ξ) x (shift 1 ⁻¹' Cn) := by
        rw [← hC, ← hE]
    _ = condMeas μ ξ x {y | y 0 = x 0} * condMeas μ ξ (shift 1 x) Cn := by
        rw [hT, Measure.map_apply (measurable_shift (-1)) hmeas, hpre]

/-- The product formula behind Feng's (4.18):
`μ_𝐢^ξ(𝒫_0^{n-1}(𝐢)) = ∏_{k<n} μ_{σ^k 𝐢}^ξ([i_k])` for every `n` and `μ`-almost every `𝐢`, by
induction on `n` from `condMeas_cylinder_succ`, which holds along the whole forward orbit of
almost every point since `μ` is invariant. -/
theorem condMeas_cylinder_eq_prod (hinv : MeasurePreserving (shift 1) μ μ)
    (hξ : IsMeasurablePartition ξ) (hD : MeasurableSet D) (hD0 : μ Dᶜ = 0)
    (hin : ∀ x ∈ D, pullShift ξ x = refineZero ξ x) (hsub : ∀ x ∈ D, ξ x ⊆ D)
    (hout : ∀ x ∉ D, pullShift ξ x ⊆ Dᶜ) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, condMeas μ ξ x (cylinder (block n x)) =
      ∏ k ∈ Finset.range n, condMeas μ ξ (shift k x) {y | y 0 = shift k x 0} := by
  have hstep := condMeas_cylinder_succ hinv hξ hD hD0 hin hsub hout
  have hall : ∀ᵐ x ∂μ, ∀ k : ℕ, ∀ n : ℕ,
      condMeas μ ξ (shift k x) (cylinder (block (n + 1) (shift k x))) =
        condMeas μ ξ (shift k x) {y | y 0 = shift k x 0} *
          condMeas μ ξ (shift 1 (shift k x)) (cylinder (block n (shift 1 (shift k x)))) :=
    ae_all_iff.2 fun k => (measurePreserving_shift_natCast hinv k).quasiMeasurePreserving.ae hstep
  have hsk : ∀ (k : ℕ) (z : ℤ → α), shift (k : ℤ) (shift 1 z) = shift ((k + 1 : ℕ) : ℤ) z :=
    fun k z => by
      rw [shift_shift]
      congr 1
      push_cast
      ring
  filter_upwards [hall] with x hx n
  induction n generalizing x with
  | zero =>
    have : cylinder (block 0 x) = univ := by
      ext y
      simp [mem_cylinder]
    simp [this]
  | succ n ih =>
    have h1 : ∀ k : ℕ, ∀ m : ℕ,
        condMeas μ ξ (shift k (shift 1 x)) (cylinder (block (m + 1) (shift k (shift 1 x)))) =
          condMeas μ ξ (shift k (shift 1 x)) {y | y 0 = shift k (shift 1 x) 0} *
            condMeas μ ξ (shift 1 (shift k (shift 1 x)))
              (cylinder (block m (shift 1 (shift k (shift 1 x))))) := fun k => by
      rw [hsk]
      exact hx (k + 1)
    have h0 := hx 0 n
    simp only [Nat.cast_zero, shift_zero] at h0
    rw [h0, ih (shift 1 x) h1, Finset.prod_range_succ', mul_comm]
    simp only [hsk, Nat.cast_zero, shift_zero]

/-- Feng, Lemma 4.6, first identity of (4.16), for a measurable partition `ξ` of a Borel set `D`
of full measure with the invariance property `σ^{-1}(ξ(σ 𝐢)) = ξ(𝐢) ∩ [i_0]` for `𝐢 ∈ D`, and an
invariant probability measure `μ`:
`-log μ_𝐢^ξ(𝒫_0^{n-1}(𝐢)) = ∑_{k<n} I_μ(𝒫 | \widehat{ξ})(σ^k 𝐢)` for all `n`, for `μ`-almost every
`𝐢`; this is Feng's (4.18). Ergodicity is not needed. The logarithm of the product formula
`condMeas_cylinder_eq_prod` is the sum of the logarithms, all factors being positive almost
everywhere along the orbit (`condMeas_zeroCyl_pos`). -/
theorem infoSum_of_pullShift (hinv : MeasurePreserving (shift 1) μ μ)
    (hξ : IsMeasurablePartition ξ) (hD : MeasurableSet D) (hD0 : μ Dᶜ = 0)
    (hin : ∀ x ∈ D, pullShift ξ x = refineZero ξ x) (hsub : ∀ x ∈ D, ξ x ⊆ D)
    (hout : ∀ x ∉ D, pullShift ξ x ⊆ Dᶜ) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, -Real.log ((condMeas μ ξ x).real (cylinder (block n x))) =
      ∑ k ∈ Finset.range n, condInfo μ ξ (shift k x) := by
  have hpos : ∀ᵐ x ∂μ, ∀ k : ℕ, 0 < condMeas μ ξ (shift k x) {y | y 0 = shift k x 0} :=
    ae_all_iff.2 fun k => (measurePreserving_shift_natCast hinv k).quasiMeasurePreserving.ae
      (condMeas_zeroCyl_pos μ ξ)
  filter_upwards [condMeas_cylinder_eq_prod hinv hξ hD hD0 hin hsub hout, hpos] with x hx hp n
  rw [measureReal_def, hx n, ENNReal.toReal_prod,
    Real.log_prod fun k _ => (ENNReal.toReal_pos (hp k).ne' (measure_ne_top _ _)).ne',
    ← Finset.sum_neg_distrib]
  rfl

end General

/-! ### The box-like partitions `ξ_i` -/

/-- `(σ 𝐣)^- = (σ 𝐢)^-` exactly when `𝐣^- = 𝐢^-` and `j_0 = i_0`: the past of `σ 𝐢` is the past
of `𝐢` followed by `i_0`. -/
theorem samePast_shift_one_iff {β : Type*} {x y : ℤ → β} :
    SamePast (shift 1 y) (shift 1 x) ↔ SamePast y x ∧ y 0 = x 0 := by
  constructor
  · intro h
    refine ⟨fun n hn => ?_, ?_⟩
    · have := h (n - 1) (by omega)
      rwa [shift_apply, shift_apply, add_sub_cancel] at this
    · have := h (-1) (by norm_num)
      simpa using this
  · rintro ⟨h, h0⟩ n hn
    simp only [shift_apply]
    rcases lt_or_eq_of_le (show 1 + n ≤ 0 by omega) with h' | h'
    · exact h _ h'
    · rw [h']
      exact h0

namespace System

section BoxLikePartitions

variable {ι : Type u} [MeasurableSpace ι] (S : System ι)

/-- For `𝐢 ∈ Σ'` and `λ_2 < λ_1`, the slow axis of `σ 𝐢` is the slow axis of `𝐢` moved by the
orientation of `A_{i_0}`: `A_{i_0} V_{σ 𝐢}^1 = V_𝐢^1`, which is (V1) of `sec:lyapunov_exponents`
at `σ 𝐢` in the box-like case. It is `eq:sigma_tau_omega_positive_eq_measure1`
(`shift_mem_SigmaTau_iff`) together with `Σ^τ ∩ Σ^ω = ∅`. -/
theorem slowAxis_shift_one (μ : Measure (ℤ → ι)) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ)
    {x : ℤ → ι} (hx : x ∈ S.SigmaPrime μ) :
    S.slowAxis μ (shift 1 x) = S.slowAxis μ x + S.o (x 0) := by
  obtain ⟨h1, -⟩ := S.shift_mem_SigmaTau_iff μ x
  have hdis := S.disjoint_SigmaTau_SigmaOmega μ hlt
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have h01 : (1 : ZMod 2) ≠ 0 := by decide
  unfold slowAxis
  by_cases hτ : x ∈ S.SigmaTau μ
  · have hω : x ∉ S.SigmaOmega μ := Set.disjoint_left.1 hdis hτ
    rcases zmod_two_cases (S.o (x 0)) with h | h
    · have : shift 1 x ∈ S.SigmaTau μ := h1.2 (Or.inl ⟨h, hτ⟩)
      simp [this, hτ, h]
    · have : shift 1 x ∉ S.SigmaTau μ := fun h' => by
        rcases h1.1 h' with ⟨h'', -⟩ | ⟨-, h''⟩
        · rw [h] at h''
          exact h01 h''
        · exact hω h''
      simp [this, hτ, h, h11]
  · have hω : x ∈ S.SigmaOmega μ := hx.resolve_left hτ
    rcases zmod_two_cases (S.o (x 0)) with h | h
    · have : shift 1 x ∉ S.SigmaTau μ := fun h' => by
        rcases h1.1 h' with ⟨-, h''⟩ | ⟨h'', -⟩
        · exact hτ h''
        · rw [h] at h''
          exact h01 h''.symm
      simp [this, hτ, h]
    · have : shift 1 x ∈ S.SigmaTau μ := h1.2 (Or.inr ⟨h, hω⟩)
      simp [this, hτ, h]

omit [MeasurableSpace ι] in
/-- The coordinates of the difference of two images under `φ_j`:
`proj_c(φ_j(z) - φ_j(z')) = g'_{(j, c)} proj_{c + o(j)}(z - z')`, from `eq:phi_def_by_g`. -/
theorem coord_phi_sub_phi (c : ZMod 2) (j : ι) (z z' : ℝ × ℝ) :
    coord c (S.phi j z - S.phi j z') = S.ratio (j, c) * coord (c + S.o j) (z - z') := by
  rw [coord_sub, coord_phi, coord_phi, coord_sub]
  simp only [g]
  ring

/-- The invariance of the filtration used by the partitions `ξ_i` (`sec:entropies`, tex lines
1860 to 1862; Feng, (4.11) in the proof of Lemma 4.4, with `n = 1`): for `𝐢 ∈ Σ'`, `λ_2 < λ_1`
and `j_0 = i_0`,
`π(σ 𝐣) - π(σ 𝐢) ∈ V_{σ 𝐢}^i` exactly when `π(𝐣) - π(𝐢) ∈ V_𝐢^i`. The difference
`π(𝐣) - π(𝐢)` is `A_{i_0}(π(σ 𝐣) - π(σ 𝐢))`, and `A_{i_0}` maps `V_{σ 𝐢}^i` onto `V_𝐢^i`. -/
theorem proj_sub_mem_oseledets_iff [Finite ι] (μ : Measure (ℤ → ι))
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) {x y : ℤ → ι} (hx : x ∈ S.SigmaPrime μ)
    (h0 : y 0 = x 0) (i : ℕ) :
    S.proj (shift 1 y) - S.proj (shift 1 x) ∈ S.oseledets μ (shift 1 x) i ↔
      S.proj y - S.proj x ∈ S.oseledets μ x i := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  have e : S.proj y - S.proj x =
      S.phi (x 0) (S.proj (shift 1 y)) - S.phi (x 0) (S.proj (shift 1 x)) := by
    rw [hS.proj_eq y, hS.proj_eq x, h0]
  rw [e]
  rcases i with _ | _ | i
  · simp [oseledets]
  · simp only [oseledets, mem_ofPred_eq, coord_phi_sub_phi, S.slowAxis_shift_one μ hlt hx,
      mul_eq_zero, S.ratio_ne_zero, false_or]
    rw [show S.slowAxis μ x + S.o (x 0) + 1 = S.slowAxis μ x + 1 + S.o (x 0) by ring]
  · simp only [oseledets, mem_singleton_iff, sub_eq_zero]
    exact (S.injective_phi (x 0)).eq_iff.symm

/-- The atoms of `ξ_i` at points of `Σ'` lie in `Σ'`. -/
theorem xi_subset_SigmaPrime (μ : Measure (ℤ → ι)) (i : ℕ) {x : ℤ → ι}
    (hx : x ∈ S.SigmaPrime μ) : S.xi μ i x ⊆ S.SigmaPrime μ := by
  rw [xi, atomsOn_of_mem hx]
  exact inter_subset_right

/-- The invariance property of the box-like partitions `ξ_i`, Feng, Lemma 4.4(1), with `n = 1`,
for the article's `Σ'`: `σ^{-1}(ξ_i(σ 𝐢)) = ξ_i(𝐢) ∩ [i_0]` for `𝐢 ∈ Σ'` and `λ_2 < λ_1`, for
every `i`. The set `Σ'` is shift-invariant (`shift_mem_SigmaPrime_iff`), the past of `σ 𝐣` is
the past of `𝐣` followed by `j_0` (`samePast_shift_one_iff`), and the filtration is invariant
(`proj_sub_mem_oseledets_iff`). -/
theorem pullShift_xi [Finite ι] (μ : Measure (ℤ → ι)) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ)
    (i : ℕ) {x : ℤ → ι} (hx : x ∈ S.SigmaPrime μ) :
    pullShift (S.xi μ i) x = refineZero (S.xi μ i) x := by
  have hσx : shift 1 x ∈ S.SigmaPrime μ := (S.shift_mem_SigmaPrime_iff μ x).2 hx
  ext y
  simp only [pullShift, refineZero, xi, mem_preimage, atomsOn_of_mem hσx, atomsOn_of_mem hx,
    mem_inter_iff, mem_ofPred_eq, samePast_shift_one_iff, S.shift_mem_SigmaPrime_iff]
  constructor
  · rintro ⟨⟨⟨hp, h0⟩, hv⟩, hy⟩
    exact ⟨⟨⟨hp, (S.proj_sub_mem_oseledets_iff μ hlt hx h0 i).1 hv⟩, hy⟩, h0⟩
  · rintro ⟨⟨⟨hp, hv⟩, hy⟩, h0⟩
    exact ⟨⟨⟨hp, h0⟩, (S.proj_sub_mem_oseledets_iff μ hlt hx h0 i).2 hv⟩, hy⟩

/-- Outside `Σ'` the atoms of `σ^{-1}ξ_i` avoid `Σ'`: they are `σ^{-1}(Σ ∖ Σ') = Σ ∖ Σ'`. -/
theorem pullShift_xi_subset_of_notMem (μ : Measure (ℤ → ι)) (i : ℕ) {x : ℤ → ι}
    (hx : x ∉ S.SigmaPrime μ) : pullShift (S.xi μ i) x ⊆ (S.SigmaPrime μ)ᶜ := by
  have hσx : shift 1 x ∉ S.SigmaPrime μ := fun h => hx ((S.shift_mem_SigmaPrime_iff μ x).1 h)
  intro y hy
  simp only [pullShift, xi, mem_preimage, atomsOn_of_notMem hσx, mem_compl_iff] at hy ⊢
  exact fun h => hy ((S.shift_mem_SigmaPrime_iff μ y).2 h)

/-- Feng, Lemma 4.6, first identity of (4.16), for the box-like partitions `ξ_i`, proved: for
every invariant probability measure `μ` with `λ_2(𝖠, μ) < λ_1(𝖠, μ)` and `μ(Σ') = 1`, and every
`i`, `-log μ_𝐢^{ξ_i}(𝒫_0^{n-1}(𝐢)) = ∑_{k<n} I_μ(𝒫 | \widehat{ξ}_i)(σ^k 𝐢)` for all `n`, for
`μ`-almost every `𝐢`. Ergodicity enters only through `μ(Σ') = 1`. This is the identity behind
`thm:feng_entropy_as_limit` and the one cited in the proof of `thm:feng_entropy_zero` (tex lines
2014 to 2019). -/
theorem infoSum_xi [Fintype ι] [MeasurableSingletonClass ι] (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) (hfull : μ (S.SigmaPrime μ)ᶜ = 0) (i : ℕ) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, -Real.log ((condMeas μ (S.xi μ i) x).real (cylinder (block n x))) =
      ∑ k ∈ Finset.range n, condInfo μ (S.xi μ i) (shift k x) :=
  infoSum_of_pullShift hinv (S.isMeasurablePartition_xi μ i) (S.measurableSet_SigmaPrime μ)
    hfull (fun _ hx => S.pullShift_xi μ hlt i hx) (fun _ hx => S.xi_subset_SigmaPrime μ i hx)
    (fun _ hx => S.pullShift_xi_subset_of_notMem μ i hx)

end BoxLikePartitions

end System

/-- The literature predicate `FengInfoSum` of `BoxLike/LiteratureFeng.lean`, Feng, Lemma 4.6,
first identity of (4.16), for the planar box-like partitions, holds, for every `i : ℕ`: it is
`System.infoSum_xi` with `μ(Σ') = 1` from `System.measure_SigmaPrime_compl`. It is the input of
`thm:feng_entropy_as_limit` and `thm:feng_entropy_zero`, planar part. -/
theorem fengInfoSum_holds : FengInfoSum.{u} := by
  intro ι _ _ _ S μ _ hinv herg hlt i
  exact S.infoSum_xi μ hinv hlt (S.measure_SigmaPrime_compl μ hinv herg) i

end BoxLike
