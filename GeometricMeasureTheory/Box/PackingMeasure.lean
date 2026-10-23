/-
# Section 4.3: Packing premeasure and packing measure

Packings by closed balls of varying radii, the packing premeasure, the packing measure, and packing
dimension. A packing of `E` is a family of pairwise disjoint closed balls with centres in `E` and
radii at most the cutoff, indexed by a subset of `ℕ`, so finite packings and the empty packing are
allowed.

| Notes | Lean declaration | Location |
|---|---|---|
| Definition 4.10 (packing premeasure and measure) | `packingDelta`, `packingPremeasure`, `packingMeasure` | here |
| Packings | `IsPacking`, `packingSum_le_packingDelta`, `packingDelta_le` | here |
| The comparison lemmas | `packingDelta_anti`, `packingDelta_mono`, `packingDelta_union_le` | here |
| Premeasure and measure | `packingPremeasure_mono`, `packingMeasure_le_packingPremeasure` | here |
| Separated families as packings | `finset_sum_le_packingDelta`, `encard_mul_le_packingDelta` | here |
| Example 4.11 (the premeasure is not countably subadditive) | `packing_premeasure_countable` | here |
| Additivity of the premeasure on separated sets | `packingPremeasure_union_of_separated` | here |
| Proposition 4.12 (the packing measure is a metric outer measure) | `packing_outer_measure` | here |
| Critical exponents for the packing measure | `packingMeasure_eq_zero_of_lt` | here |
| Definition 4.13 (packing dimension) | `packingDim`, `packingDim_eq_iSup` | here |
| Monotonicity and countable stability | `packingDim_mono`, `packingDim_iUnion` | here |
-/
import GeometricMeasureTheory.Box.BoxDimension

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

variable {X : Type*} [MetricSpace X]

/-! ## Definition 4.10 (`def:packing-measure`) -/

/-- The supremum of `∑ (2 rᵢ)^s` over packings of `E` by disjoint closed balls with centres in `E`
and radii at most `δ`. The index set `I ⊆ ℕ` may be finite or empty. -/
def packingDelta (s δ : ℝ) (E : Set X) : ℝ≥0∞ :=
  ⨆ (I : Set ℕ) (x : ℕ → X) (r : ℕ → ℝ) (_ : ∀ i ∈ I, x i ∈ E) (_ : ∀ i ∈ I, 0 < r i)
    (_ : ∀ i ∈ I, r i ≤ δ)
    (_ : I.Pairwise (Function.onFun Disjoint fun i => closedBall (x i) (r i))),
    ∑' i : I, ENNReal.ofReal ((2 * r i) ^ s)

/-- Definition 4.10 (`def:packing-measure`): the packing premeasure, the limit of the
`δ`-packing sums as `δ → 0`. -/
def packingPremeasure (s : ℝ) (E : Set X) : ℝ≥0∞ :=
  ⨅ (δ : ℝ) (_ : 0 < δ), packingDelta s δ E

/-- Definition 4.10 (`def:packing-measure`): the packing measure, the infimum of the sums of
premeasures over countable covers. -/
def packingMeasure (s : ℝ) (E : Set X) : ℝ≥0∞ :=
  ⨅ (A : ℕ → Set X) (_ : E ⊆ ⋃ i, A i), ∑' i, packingPremeasure s (A i)

/-- A `δ`-packing of `E`: pairwise disjoint closed balls of positive radius at most `δ`, with
centres in `E`, indexed by a subset `I` of `ℕ`. -/
structure IsPacking (δ : ℝ) (E : Set X) (I : Set ℕ) (x : ℕ → X) (r : ℕ → ℝ) : Prop where
  /-- The centres lie in `E`. -/
  centre_mem : ∀ i ∈ I, x i ∈ E
  /-- The radii are positive. -/
  radius_pos : ∀ i ∈ I, 0 < r i
  /-- The radii are at most the cutoff `δ`. -/
  radius_le : ∀ i ∈ I, r i ≤ δ
  /-- The closed balls are pairwise disjoint. -/
  disjoint : I.Pairwise (Function.onFun Disjoint fun i => closedBall (x i) (r i))

/-- The empty family is a packing. -/
theorem isPacking_empty (δ : ℝ) (E : Set X) (x : ℕ → X) (r : ℕ → ℝ) :
    IsPacking δ E ∅ x r :=
  ⟨fun i hi => absurd hi (Set.notMem_empty i), fun i hi => absurd hi (Set.notMem_empty i),
    fun i hi => absurd hi (Set.notMem_empty i), Set.pairwise_empty _⟩

/-- The weight of a `δ`-packing of `E` is at most `𝓟^s_δ(E)`. -/
theorem packingSum_le_packingDelta {s δ : ℝ} {E : Set X} {I : Set ℕ} {x : ℕ → X} {r : ℕ → ℝ}
    (h : IsPacking δ E I x r) :
    ∑' i : I, ENNReal.ofReal ((2 * r i) ^ s) ≤ packingDelta s δ E :=
  le_iSup_of_le I <| le_iSup_of_le x <| le_iSup_of_le r <| le_iSup_of_le h.centre_mem <|
    le_iSup_of_le h.radius_pos <| le_iSup_of_le h.radius_le <| le_iSup_of_le h.disjoint le_rfl

/-- A bound valid for every `δ`-packing of `E` bounds `𝓟^s_δ(E)`. -/
theorem packingDelta_le {s δ : ℝ} {E : Set X} {c : ℝ≥0∞}
    (h : ∀ I x r, IsPacking δ E I x r → ∑' i : I, ENNReal.ofReal ((2 * r i) ^ s) ≤ c) :
    packingDelta s δ E ≤ c :=
  iSup_le fun I => iSup_le fun x => iSup_le fun r => iSup_le fun h₁ => iSup_le fun h₂ =>
    iSup_le fun h₃ => iSup_le fun h₄ => h I x r ⟨h₁, h₂, h₃, h₄⟩

/-- `𝓟^s_δ(E)` as a supremum over the packings of `E`. -/
theorem packingDelta_eq_iSup (s δ : ℝ) (E : Set X) :
    packingDelta s δ E =
      ⨆ p : {p : Set ℕ × (ℕ → X) × (ℕ → ℝ) // IsPacking δ E p.1 p.2.1 p.2.2},
        ∑' i : p.1.1, ENNReal.ofReal ((2 * p.1.2.2 i) ^ s) :=
  le_antisymm (packingDelta_le fun I x r h => le_iSup_of_le ⟨(I, x, r), h⟩ le_rfl)
    (iSup_le fun p => packingSum_le_packingDelta p.2)

/-- On an empty space there is nothing to pack. -/
theorem packingDelta_of_isEmpty [IsEmpty X] (s δ : ℝ) (E : Set X) : packingDelta s δ E = 0 :=
  le_antisymm (packingDelta_le fun _ x _ _ => (IsEmpty.false (x 0)).elim) zero_le

/-- Every non-empty space carries the empty packing. -/
theorem nonempty_packing [Nonempty X] (δ : ℝ) (E : Set X) :
    Nonempty {p : Set ℕ × (ℕ → X) × (ℕ → ℝ) // IsPacking δ E p.1 p.2.1 p.2.2} :=
  ⟨⟨(∅, fun _ => Classical.arbitrary X, fun _ => 1),
    isPacking_empty δ E _ _⟩⟩

theorem packingDelta_anti (s : ℝ) (E : Set X) {δ δ' : ℝ} (h : δ' ≤ δ) :
    packingDelta s δ' E ≤ packingDelta s δ E :=
  packingDelta_le fun _ _ _ hp => packingSum_le_packingDelta
    ⟨hp.centre_mem, hp.radius_pos, fun i hi => (hp.radius_le i hi).trans h, hp.disjoint⟩

/-- `𝓟^s_δ` is monotone in the set. -/
theorem packingDelta_mono (s δ : ℝ) {E F : Set X} (h : E ⊆ F) :
    packingDelta s δ E ≤ packingDelta s δ F :=
  packingDelta_le fun _ _ _ hp => packingSum_le_packingDelta
    ⟨fun i hi => h (hp.centre_mem i hi), hp.radius_pos, hp.radius_le, hp.disjoint⟩

@[simp]
theorem packingDelta_empty (s δ : ℝ) : packingDelta s δ (∅ : Set X) = 0 := by
  refine le_antisymm (packingDelta_le fun I x r hp => ?_) zero_le
  have hI : I = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun i hi => Set.notMem_empty (x i) (hp.centre_mem i hi)
  subst hI
  haveI : IsEmpty (↥(∅ : Set ℕ)) := Set.isEmpty_coe_sort.2 rfl
  simp

/-- Splitting a packing of `A ∪ B` by its centres: `𝓟^s_δ` is subadditive on pairs. -/
theorem packingDelta_union_le (s δ : ℝ) (A B : Set X) :
    packingDelta s δ (A ∪ B) ≤ packingDelta s δ A + packingDelta s δ B := by
  classical
  refine packingDelta_le fun I x r hp => ?_
  have hpA : IsPacking δ A {i ∈ I | x i ∈ A} x r :=
    ⟨fun _ hi => hi.2, fun i hi => hp.radius_pos i hi.1, fun i hi => hp.radius_le i hi.1,
      hp.disjoint.mono fun _ hi => hi.1⟩
  have hpB : IsPacking δ B {i ∈ I | x i ∉ A} x r :=
    ⟨fun i hi => (hp.centre_mem i hi.1).resolve_left hi.2, fun i hi => hp.radius_pos i hi.1,
      fun i hi => hp.radius_le i hi.1, hp.disjoint.mono fun _ hi => hi.1⟩
  refine le_trans (le_of_eq ?_)
    (add_le_add (packingSum_le_packingDelta (s := s) hpA)
      (packingSum_le_packingDelta (s := s) hpB))
  rw [tsum_subtype I fun n => ENNReal.ofReal ((2 * r n) ^ s),
    tsum_subtype {i ∈ I | x i ∈ A} fun n => ENNReal.ofReal ((2 * r n) ^ s),
    tsum_subtype {i ∈ I | x i ∉ A} fun n => ENNReal.ofReal ((2 * r n) ^ s), ← ENNReal.tsum_add]
  refine tsum_congr fun n => ?_
  by_cases hn : n ∈ I
  · by_cases hA : x n ∈ A
    · have h₁ : n ∈ {i ∈ I | x i ∈ A} := ⟨hn, hA⟩
      have h₂ : n ∉ {i ∈ I | x i ∉ A} := by simp [hA]
      rw [Set.indicator_of_mem hn, Set.indicator_of_mem h₁, Set.indicator_of_notMem h₂, add_zero]
    · have h₁ : n ∉ {i ∈ I | x i ∈ A} := by simp [hA]
      have h₂ : n ∈ {i ∈ I | x i ∉ A} := ⟨hn, hA⟩
      rw [Set.indicator_of_mem hn, Set.indicator_of_notMem h₁, Set.indicator_of_mem h₂, zero_add]
  · have h₁ : n ∉ {i ∈ I | x i ∈ A} := by simp [hn]
    have h₂ : n ∉ {i ∈ I | x i ∉ A} := by simp [hn]
    rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem h₁, Set.indicator_of_notMem h₂,
      add_zero]

/-! ### Separated families as packings -/

/-- A finite `2δ`-separated subset of `E` is the set of centres of a `δ`-packing of `E`, so its
weight bounds `𝓟^s_δ(E)`. This is the bound used for the box dimension in Lemma 4.15. -/
theorem finset_sum_le_packingDelta {s δ : ℝ} (hδ : 0 < δ) {E : Set X} {C : Finset X}
    (hCE : ↑C ⊆ E) (hsep : ∀ y ∈ C, ∀ z ∈ C, y ≠ z → 2 * δ < dist y z) :
    ∑ _y ∈ C, ENNReal.ofReal ((2 * δ) ^ s) ≤ packingDelta s δ E := by
  classical
  rcases C.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
  · simp
  -- enumerate the centres
  set g : ℕ → X := fun i => if h : i < C.card then ((C.equivFin.symm ⟨i, h⟩ : {z // z ∈ C}) : X)
    else y₀ with hg
  have hgC : ∀ i, i < C.card → g i ∈ C := by
    intro i hi
    simp only [hg, dif_pos hi]
    exact (C.equivFin.symm ⟨i, hi⟩).2
  have hginj : ∀ i, i < C.card → ∀ j, j < C.card → i ≠ j → g i ≠ g j := by
    intro i hi j hj hij hgij
    refine hij ?_
    have hval : (C.equivFin.symm ⟨i, hi⟩ : {z // z ∈ C}) = C.equivFin.symm ⟨j, hj⟩ := by
      refine Subtype.ext ?_
      simpa only [hg, dif_pos hi, dif_pos hj] using hgij
    have := C.equivFin.symm.injective hval
    simpa using this
  have hmem : ∀ i : ℕ, i ∈ (↑(Finset.range C.card) : Set ℕ) ↔ i < C.card := by simp
  have hpack : IsPacking δ E (↑(Finset.range C.card)) g (fun _ => δ) := by
    refine ⟨fun i hi => hCE (hgC i ((hmem i).1 hi)), fun _ _ => hδ, fun _ _ => le_rfl, ?_⟩
    intro i hi j hj hij
    refine Metric.closedBall_disjoint_closedBall ?_
    have := hsep (g i) (hgC i ((hmem i).1 hi)) (g j) (hgC j ((hmem j).1 hj))
      (hginj i ((hmem i).1 hi) j ((hmem j).1 hj) hij)
    linarith
  refine le_trans (le_of_eq ?_) (packingSum_le_packingDelta (s := s) hpack)
  rw [Finset.tsum_subtype' (Finset.range C.card) fun _ => ENNReal.ofReal ((2 * δ) ^ s)]
  simp

/-- The bound of `finset_sum_le_packingDelta` for an arbitrary `2δ`-separated subset, in the form
used by packing numbers. -/
theorem encard_mul_le_packingDelta {s δ : ℝ} (hδ : 0 < δ) {E C : Set X} (hCE : C ⊆ E)
    (hsep : ∀ y ∈ C, ∀ z ∈ C, y ≠ z → 2 * δ < dist y z) :
    C.encard * ENNReal.ofReal ((2 * δ) ^ s) ≤ packingDelta s δ E := by
  have hfin : ∀ D : Finset X, ↑D ⊆ C →
      (D.card : ℝ≥0∞) * ENNReal.ofReal ((2 * δ) ^ s) ≤ packingDelta s δ E := by
    intro D hD
    have h := finset_sum_le_packingDelta (s := s) hδ (hD.trans hCE)
      fun y hy z hz hyz => hsep y (hD hy) z (hD hz) hyz
    simpa [Finset.sum_const, nsmul_eq_mul] using h
  rcases C.finite_or_infinite with h | h
  · obtain ⟨D, rfl⟩ := h.exists_finset_coe
    rw [Set.encard_coe_eq_coe_finsetCard]
    exact hfin D subset_rfl
  · rw [h.encard_eq]
    calc (⊤ : ℝ≥0∞) * ENNReal.ofReal ((2 * δ) ^ s)
        = (⨆ n : ℕ, (n : ℝ≥0∞)) * ENNReal.ofReal ((2 * δ) ^ s) := by rw [ENNReal.iSup_natCast]
      _ = ⨆ n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal ((2 * δ) ^ s) := ENNReal.iSup_mul _ _
      _ ≤ packingDelta s δ E := by
          refine iSup_le fun n => ?_
          obtain ⟨D, hDC, hDn⟩ := h.exists_subset_card_eq n
          exact hDn ▸ hfin D hDC

/-- A packing of a singleton has at most one ball, of weight at most `(2δ)^s`. -/
theorem packingDelta_singleton_le {s δ : ℝ} (hs : 0 ≤ s) (x : X) :
    packingDelta s δ ({x} : Set X) ≤ ENNReal.ofReal ((2 * δ) ^ s) := by
  refine packingDelta_le fun I y r hp => ?_
  have hsub : ∀ i ∈ I, ∀ j ∈ I, i = j := by
    intro i hi j hj
    by_contra hij
    have hd := hp.disjoint hi hj hij
    have hxi : x ∈ closedBall (y i) (r i) := by
      rw [Set.mem_singleton_iff.1 (hp.centre_mem i hi)]
      exact mem_closedBall_self (hp.radius_pos i hi).le
    have hxj : x ∈ closedBall (y j) (r j) := by
      rw [Set.mem_singleton_iff.1 (hp.centre_mem j hj)]
      exact mem_closedBall_self (hp.radius_pos j hj).le
    exact absurd hxj (Set.disjoint_left.1 hd hxi)
  rcases Set.eq_empty_or_nonempty I with rfl | ⟨i₀, hi₀⟩
  · haveI : IsEmpty (↥(∅ : Set ℕ)) := Set.isEmpty_coe_sort.2 rfl
    simp
  · have hI : I = {i₀} := Set.eq_singleton_iff_unique_mem.2 ⟨hi₀, fun j hj => hsub j hj i₀ hi₀⟩
    subst hI
    rw [tsum_singleton i₀ fun i => ENNReal.ofReal ((2 * r i) ^ s)]
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ?_ ?_ hs)
    · linarith [hp.radius_pos i₀ hi₀]
    · linarith [hp.radius_le i₀ hi₀]

/-- A singleton has `𝓟^s_δ({x}) = (2δ)^s`: the best packing is the single ball of radius `δ`. At
`s = 0` this is one, as in the notes. -/
theorem packingDelta_singleton {s δ : ℝ} (hs : 0 ≤ s) (hδ : 0 < δ) (x : X) :
    packingDelta s δ ({x} : Set X) = ENNReal.ofReal ((2 * δ) ^ s) := by
  refine le_antisymm (packingDelta_singleton_le hs x) ?_
  have hpack : IsPacking δ ({x} : Set X) {0} (fun _ => x) (fun _ => δ) :=
    ⟨fun _ _ => rfl, fun _ _ => hδ, fun _ _ => le_rfl, Set.pairwise_singleton _ _⟩
  calc ENNReal.ofReal ((2 * δ) ^ s)
      = ∑' _i : ({0} : Set ℕ), ENNReal.ofReal ((2 * δ) ^ s) :=
        (tsum_singleton 0 fun _ => ENNReal.ofReal ((2 * δ) ^ s)).symm
    _ ≤ packingDelta s δ ({x} : Set X) := packingSum_le_packingDelta hpack

/-! ### The premeasure -/

/-- The packing premeasure is at most every `δ`-packing supremum. -/
theorem packingPremeasure_le_packingDelta (s : ℝ) {δ : ℝ} (hδ : 0 < δ) (E : Set X) :
    packingPremeasure s E ≤ packingDelta s δ E :=
  iInf₂_le δ hδ

/-- The packing premeasure as an infimum over positive cutoffs. -/
theorem packingPremeasure_eq_iInf_subtype (s : ℝ) (E : Set X) :
    packingPremeasure s E = ⨅ p : {δ : ℝ // 0 < δ}, packingDelta s p E :=
  iInf_subtype'

/-- The packing premeasure is monotone. -/
theorem packingPremeasure_mono (s : ℝ) {E F : Set X} (h : E ⊆ F) :
    packingPremeasure s E ≤ packingPremeasure s F :=
  iInf₂_mono fun δ _ => packingDelta_mono s δ h

@[simp]
theorem packingPremeasure_empty (s : ℝ) : packingPremeasure s (∅ : Set X) = 0 :=
  le_antisymm ((packingPremeasure_le_packingDelta s one_pos _).trans_eq
    (packingDelta_empty s 1)) zero_le

/-- The packing premeasure is subadditive on pairs. -/
theorem packingPremeasure_union_le (s : ℝ) (A B : Set X) :
    packingPremeasure s (A ∪ B) ≤ packingPremeasure s A + packingPremeasure s B := by
  have key : packingPremeasure s A + packingPremeasure s B
      = ⨅ p : {δ : ℝ // 0 < δ}, (packingDelta s p A + packingDelta s p B) := by
    rw [packingPremeasure_eq_iInf_subtype, packingPremeasure_eq_iInf_subtype]
    refine ENNReal.iInf_add_iInf fun p q => ⟨⟨min p q, lt_min p.2 q.2⟩, ?_⟩
    exact add_le_add (packingDelta_anti s A (min_le_left _ _))
      (packingDelta_anti s B (min_le_right _ _))
  rw [key]
  exact le_iInf fun p =>
    (packingPremeasure_le_packingDelta s p.2 _).trans (packingDelta_union_le s p A B)

/-- Every singleton has packing premeasure zero at a positive exponent. -/
theorem packingPremeasure_singleton {s : ℝ} (hs : 0 < s) (x : X) :
    packingPremeasure s ({x} : Set X) = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
  rw [zero_add]
  have hε0 : (0 : ℝ) < (ε : ℝ) := NNReal.coe_pos.2 hε
  have hδ0 : 0 < (ε : ℝ) ^ (1 / s) / 2 := by
    have := Real.rpow_pos_of_pos hε0 (1 / s)
    linarith
  calc packingPremeasure s ({x} : Set X)
      ≤ packingDelta s ((ε : ℝ) ^ (1 / s) / 2) {x} := packingPremeasure_le_packingDelta s hδ0 _
    _ ≤ ENNReal.ofReal ((2 * ((ε : ℝ) ^ (1 / s) / 2)) ^ s) :=
        packingDelta_singleton_le hs.le x
    _ = ENNReal.ofReal (ε : ℝ) := by
        congr 1
        rw [show 2 * ((ε : ℝ) ^ (1 / s) / 2) = (ε : ℝ) ^ (1 / s) by ring, ← Real.rpow_mul hε0.le,
          one_div, inv_mul_cancel₀ hs.ne', Real.rpow_one]
    _ = (ε : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal

/-! ### The measure -/

/-- The packing measure is the outer measure generated by the packing premeasure. -/
theorem packingMeasure_eq_ofFunction (s : ℝ) (E : Set X) :
    packingMeasure s E =
      OuterMeasure.ofFunction (packingPremeasure (X := X) s) (packingPremeasure_empty s) E :=
  (OuterMeasure.ofFunction_apply _ _ E).symm

/-- The packing measure satisfies Definition 1.1. -/
theorem isOuterMeasure_packingMeasure (s : ℝ) : IsOuterMeasure (packingMeasure (X := X) s) := by
  have h := isOuterMeasure_outerMeasure
    (OuterMeasure.ofFunction (packingPremeasure (X := X) s) (packingPremeasure_empty s))
  rwa [show ⇑(OuterMeasure.ofFunction (packingPremeasure (X := X) s) (packingPremeasure_empty s))
    = packingMeasure (X := X) s from funext fun E => (packingMeasure_eq_ofFunction s E).symm] at h

/-- The packing measure is monotone. -/
theorem packingMeasure_mono (s : ℝ) {E F : Set X} (h : E ⊆ F) :
    packingMeasure s E ≤ packingMeasure s F :=
  (isOuterMeasure_packingMeasure s).mono h

/-- The packing measure is subadditive on pairs. -/
theorem packingMeasure_union_le (s : ℝ) (A B : Set X) :
    packingMeasure s (A ∪ B) ≤ packingMeasure s A + packingMeasure s B := by
  simp only [packingMeasure_eq_ofFunction]
  exact measure_union_le A B

theorem packingMeasure_le_packingPremeasure (s : ℝ) (E : Set X) :
    packingMeasure s E ≤ packingPremeasure s E := by
  classical
  refine iInf_le_of_le (fun i => if i = 0 then E else ∅) <|
    iInf_le_of_le (subset_iUnion_of_subset 0 (by simp)) ?_
  rw [tsum_eq_single 0 fun i hi => by simp [hi]]
  simp

/-! ## Example 4.11 (`ex:packing-premeasure-countable`) -/

/-- A divergent series of nonnegative reals has infinite sum in `ℝ≥0∞`. -/
private theorem tsum_ofReal_eq_top {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i) (h : ¬Summable f) :
    ∑' i, ENNReal.ofReal (f i) = ⊤ := by
  refine ENNReal.tsum_coe_eq_top_iff_not_summable_coe.2 ?_
  have hcoe : (fun i => (((f i).toNNReal : ℝ≥0) : ℝ)) = f :=
    funext fun i => Real.coe_toNNReal _ (hf i)
  rw [hcoe]
  exact h

/-- The harmonic series with a positive factor diverges. -/
private theorem not_summable_const_mul_inv_succ {c : ℝ} (hc : 0 < c) :
    ¬Summable fun j : ℕ => c * ((j : ℝ) + 1)⁻¹ := by
  intro h
  have hc' : c ≠ 0 := hc.ne'
  have h₁ : Summable fun j : ℕ => 1 / ((j + 1 : ℕ) : ℝ) := by
    refine (h.mul_left c⁻¹).congr fun j => ?_
    push_cast
    field_simp
  exact Real.not_summable_one_div_natCast
    ((summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).1 h₁)

/-- For `0 < s < 1` the rationals in `[0, 1]` carry packings of infinite weight at every cutoff:
in blocks of length proportional to `(j + 1)^{-1/s}` one ball each has total weight a multiple of
the harmonic series. -/
private theorem packingDelta_rat_eq_top {s : ℝ} (hs₀ : 0 < s) (hs : s < 1) {δ : ℝ} (hδ : 0 < δ) :
    packingDelta s δ (Set.range ((↑) : ℚ → ℝ) ∩ Icc 0 1) = ⊤ := by
  have hp1 : 1 < 1 / s := (one_lt_div hs₀).2 hs
  -- the summable comparison sequence and its sum
  have hsum : Summable fun j : ℕ => ((j : ℝ) + 1) ^ (-(1 / s)) := by
    have h := (Real.summable_nat_rpow_inv (p := 1 / s)).2 hp1
    refine ((summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ (1 / s))⁻¹) 1).2 h).congr
      fun j => ?_
    rw [Real.rpow_neg (by positivity)]
    push_cast
    rfl
  have hS1 : (1 : ℝ) ≤ ∑' j : ℕ, ((j : ℝ) + 1) ^ (-(1 / s)) := by
    have h := hsum.le_tsum 0 fun j _ => Real.rpow_nonneg (by positivity) _
    simpa using h
  have hS0 : (0 : ℝ) < ∑' j : ℕ, ((j : ℝ) + 1) ^ (-(1 / s)) := lt_of_lt_of_le one_pos hS1
  -- the scale of the construction
  obtain ⟨a, ha0, haδ, haS⟩ :
      ∃ a : ℝ, 0 < a ∧ a ≤ δ ∧ a * ∑' j : ℕ, ((j : ℝ) + 1) ^ (-(1 / s)) ≤ 1 := by
    refine ⟨min δ (∑' j : ℕ, ((j : ℝ) + 1) ^ (-(1 / s)))⁻¹, lt_min hδ (by positivity),
      min_le_left _ _, ?_⟩
    calc min δ (∑' j : ℕ, ((j : ℝ) + 1) ^ (-(1 / s)))⁻¹ *
          ∑' j : ℕ, ((j : ℝ) + 1) ^ (-(1 / s))
        ≤ (∑' j : ℕ, ((j : ℝ) + 1) ^ (-(1 / s)))⁻¹ * ∑' j : ℕ, ((j : ℝ) + 1) ^ (-(1 / s)) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hS0.le
      _ = 1 := inv_mul_cancel₀ hS0.ne'
  -- the block lengths and their partial sums
  set b : ℕ → ℝ := fun j => a * ((j : ℝ) + 1) ^ (-(1 / s)) with hbdef
  have hb0 : ∀ j, 0 < b j := fun j => mul_pos ha0 (Real.rpow_pos_of_pos (by positivity) _)
  have hba : ∀ j, b j ≤ a := fun j => by
    simp only [hbdef]
    calc a * ((j : ℝ) + 1) ^ (-(1 / s)) ≤ a * 1 :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos
            (by simp) (neg_nonpos.2 (by positivity))) ha0.le
      _ = a := mul_one a
  have hbsum : Summable b := by
    simp only [hbdef]
    exact hsum.mul_left a
  have hbtsum : ∑' j, b j = a * ∑' j : ℕ, ((j : ℝ) + 1) ^ (-(1 / s)) := by
    simp only [hbdef]
    exact tsum_mul_left
  set A : ℕ → ℝ := fun j => ∑ i ∈ Finset.range j, b i with hAdef
  have hA0 : ∀ j, 0 ≤ A j := fun j => Finset.sum_nonneg fun i _ => (hb0 i).le
  have hAsucc : ∀ j, A (j + 1) = A j + b j := fun j => by
    simp only [hAdef]
    exact Finset.sum_range_succ b j
  have hAmono : Monotone A := monotone_nat_of_le_succ fun j => by
    rw [hAsucc]; linarith [(hb0 j).le]
  have hAle : ∀ j, A j + b j ≤ 1 := fun j => by
    rw [← hAsucc]
    calc A (j + 1) = ∑ i ∈ Finset.range (j + 1), b i := by simp only [hAdef]
      _ ≤ ∑' i, b i := hbsum.sum_le_tsum _ fun i _ => (hb0 i).le
      _ = a * ∑' j : ℕ, ((j : ℝ) + 1) ^ (-(1 / s)) := hbtsum
      _ ≤ 1 := haS
  -- a rational centre in the middle third of each block
  have hex : ∀ j : ℕ, ∃ q : ℚ, A j + b j / 3 < (q : ℝ) ∧ (q : ℝ) < A j + 2 * b j / 3 :=
    fun j => exists_rat_btwn (by linarith [hb0 j])
  choose q hq₁ hq₂ using hex
  have hball : ∀ j, closedBall ((q j : ℝ)) (b j / 4) ⊆ Ioo (A j) (A (j + 1)) := by
    intro j z hz
    rw [Real.closedBall_eq_Icc, Set.mem_Icc] at hz
    rw [Set.mem_Ioo, hAsucc]
    exact ⟨by linarith [hq₁ j, hz.1, hb0 j], by linarith [hq₂ j, hz.2, hb0 j]⟩
  have hpack : IsPacking δ (Set.range ((↑) : ℚ → ℝ) ∩ Icc 0 1) Set.univ
      (fun j => (q j : ℝ)) (fun j => b j / 4) := by
    refine ⟨fun j _ => ⟨⟨q j, rfl⟩, Set.mem_Icc.2 ⟨?_, ?_⟩⟩, fun j _ => by linarith [hb0 j],
      fun j _ => ?_, ?_⟩
    · linarith [hq₁ j, hA0 j, hb0 j]
    · linarith [hq₂ j, hAle j, hb0 j]
    · linarith [hba j, hb0 j]
    · have key : ∀ m n : ℕ, m < n →
          Disjoint (closedBall ((q m : ℝ)) (b m / 4)) (closedBall ((q n : ℝ)) (b n / 4)) := by
        intro m n hmn
        refine Set.disjoint_left.2 fun z hzm hzn => ?_
        have h₁ := hball m hzm
        have h₂ := hball n hzn
        rw [Set.mem_Ioo] at h₁ h₂
        have h₃ : A (m + 1) ≤ A n := hAmono hmn
        linarith [h₁.2, h₂.1]
      intro m _ n _ hmn
      rcases lt_or_gt_of_ne hmn with h | h
      exacts [key m n h, (key n m h).symm]
  -- the weight of the packing is a multiple of the harmonic series
  have hterm : ∀ j : ℕ, (2 * (b j / 4)) ^ s = (a / 2) ^ s * ((j : ℝ) + 1)⁻¹ := by
    intro j
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have h2r : 2 * (b j / 4) = a / 2 * ((j : ℝ) + 1) ^ (-(1 / s)) := by
      simp only [hbdef]; ring
    rw [h2r, Real.mul_rpow (by linarith) (Real.rpow_nonneg hj.le _), ← Real.rpow_mul hj.le,
      show -(1 / s) * s = -(1 : ℝ) by field_simp, Real.rpow_neg hj.le, Real.rpow_one]
  have hsum_top : ∑' j : ℕ, ENNReal.ofReal ((2 * (b j / 4)) ^ s) = ⊤ := by
    simp_rw [hterm]
    exact tsum_ofReal_eq_top
      (fun j => mul_nonneg (Real.rpow_nonneg (by linarith) s) (by positivity))
      (not_summable_const_mul_inv_succ (Real.rpow_pos_of_pos (by linarith) s))
  refine top_le_iff.1 ?_
  calc (⊤ : ℝ≥0∞) = ∑' j : ℕ, ENNReal.ofReal ((2 * (b j / 4)) ^ s) := hsum_top.symm
    _ = ∑' j : (Set.univ : Set ℕ), ENNReal.ofReal ((2 * (b j / 4)) ^ s) :=
        (tsum_univ fun j => ENNReal.ofReal ((2 * (b j / 4)) ^ s)).symm
    _ ≤ packingDelta s δ (Set.range ((↑) : ℚ → ℝ) ∩ Icc 0 1) := packingSum_le_packingDelta hpack

/-- Example 4.11 (`ex:packing-premeasure-countable`): for `0 < s < 1` the rationals in `[0, 1]`
have infinite packing premeasure, although every singleton has premeasure zero. -/
theorem packing_premeasure_countable {s : ℝ} (hs₀ : 0 < s) (hs : s < 1) :
    packingPremeasure s (Set.range ((↑) : ℚ → ℝ) ∩ Icc 0 1) = ⊤ ∧
      ∀ x : ℝ, packingPremeasure s {x} = 0 :=
  ⟨le_antisymm le_top (le_iInf₂ fun _ hδ => (packingDelta_rat_eq_top hs₀ hs hδ).ge),
    fun x => packingPremeasure_singleton hs₀ x⟩

/-! ## Proposition 4.12 (`thm:packing-outer-measure`) -/

/-- Positively separated sets are at a positive distance from each other. -/
private theorem exists_dist_of_separated {A B : Set X} (h : Metric.AreSeparated A B) :
    ∃ c : ℝ, 0 < c ∧ ∀ a ∈ A, ∀ b ∈ B, c ≤ dist a b := by
  obtain ⟨r, hr0, hr⟩ := h
  refine ⟨(min r 1).toReal, ?_, fun a ha b hb => ?_⟩
  · rw [ENNReal.toReal_pos_iff]
    exact ⟨lt_min (pos_iff_ne_zero.2 hr0) one_pos,
      lt_of_le_of_lt (min_le_right _ _) ENNReal.one_lt_top⟩
  · rw [dist_edist]
    exact ENNReal.toReal_mono (edist_ne_top a b) ((min_le_left _ _).trans (hr a ha b hb))

/-- Two packings merge into one along the even and the odd indices. -/
private theorem isPacking_merge {δ : ℝ} {A B : Set X} {I J : Set ℕ} {x y : ℕ → X} {r u : ℕ → ℝ}
    (hp : IsPacking δ A I x r) (hq : IsPacking δ B J y u)
    (hcross : ∀ i ∈ I, ∀ j ∈ J, Disjoint (closedBall (x i) (r i)) (closedBall (y j) (u j))) :
    IsPacking δ (A ∪ B) {n | if n % 2 = 0 then n / 2 ∈ I else n / 2 ∈ J}
      (fun n => if n % 2 = 0 then x (n / 2) else y (n / 2))
      (fun n => if n % 2 = 0 then r (n / 2) else u (n / 2)) := by
  refine ⟨fun n hn => ?_, fun n hn => ?_, fun n hn => ?_, fun m hm n hn hmn => ?_⟩
  · simp only [Set.mem_setOf_eq] at hn
    by_cases h : n % 2 = 0
    · rw [if_pos h] at hn ⊢
      exact Or.inl (hp.centre_mem _ hn)
    · rw [if_neg h] at hn ⊢
      exact Or.inr (hq.centre_mem _ hn)
  · simp only [Set.mem_setOf_eq] at hn
    by_cases h : n % 2 = 0
    · rw [if_pos h] at hn ⊢
      exact hp.radius_pos _ hn
    · rw [if_neg h] at hn ⊢
      exact hq.radius_pos _ hn
  · simp only [Set.mem_setOf_eq] at hn
    by_cases h : n % 2 = 0
    · rw [if_pos h] at hn ⊢
      exact hp.radius_le _ hn
    · rw [if_neg h] at hn ⊢
      exact hq.radius_le _ hn
  · simp only [Set.mem_setOf_eq] at hm hn
    simp only [Function.onFun]
    by_cases hm2 : m % 2 = 0 <;> by_cases hn2 : n % 2 = 0 <;>
      simp only [hm2, hn2, if_true, if_false] at hm hn ⊢
    · exact hp.disjoint hm hn (by omega)
    · exact hcross _ hm _ hn
    · exact (hcross _ hn _ hm).symm
    · exact hq.disjoint hm hn (by omega)

/-- The weight of a merged packing is the sum of the two weights. -/
private theorem tsum_merge (s : ℝ) (I J : Set ℕ) (r u : ℕ → ℝ) :
    ∑' n : {n | if n % 2 = 0 then n / 2 ∈ I else n / 2 ∈ J},
        ENNReal.ofReal
          ((2 * if (n : ℕ) % 2 = 0 then r ((n : ℕ) / 2) else u ((n : ℕ) / 2)) ^ s) =
      (∑' i : I, ENNReal.ofReal ((2 * r i) ^ s)) + ∑' j : J, ENNReal.ofReal ((2 * u j) ^ s) := by
  rw [tsum_subtype {n | if n % 2 = 0 then n / 2 ∈ I else n / 2 ∈ J}
      (fun n => ENNReal.ofReal ((2 * if n % 2 = 0 then r (n / 2) else u (n / 2)) ^ s)),
    tsum_subtype I (fun n => ENNReal.ofReal ((2 * r n) ^ s)),
    tsum_subtype J (fun n => ENNReal.ofReal ((2 * u n) ^ s)),
    ← tsum_even_add_odd ENNReal.summable ENNReal.summable]
  congr 1
  · refine tsum_congr fun k => ?_
    have h₁ : 2 * k % 2 = 0 := by omega
    have h₂ : 2 * k / 2 = k := by omega
    by_cases hk : k ∈ I
    · rw [Set.indicator_of_mem (by simp [Set.mem_setOf_eq, h₁, h₂, hk]),
        Set.indicator_of_mem hk, h₁, h₂, if_pos rfl]
    · rw [Set.indicator_of_notMem (by simp [Set.mem_setOf_eq, h₁, h₂, hk]),
        Set.indicator_of_notMem hk]
  · refine tsum_congr fun k => ?_
    have h₁ : ¬(2 * k + 1) % 2 = 0 := by omega
    have h₂ : (2 * k + 1) / 2 = k := by omega
    by_cases hk : k ∈ J
    · rw [Set.indicator_of_mem (by simp [Set.mem_setOf_eq, h₂, hk]),
        Set.indicator_of_mem hk, if_neg h₁, h₂]
    · rw [Set.indicator_of_notMem (by simp [Set.mem_setOf_eq, h₂, hk]),
        Set.indicator_of_notMem hk]

/-- Packings of two sets that are further apart than twice the cutoff merge into a packing of
the union. -/
theorem packingDelta_add_le_of_dist {s δ c : ℝ} {A B : Set X}
    (hsep : ∀ a ∈ A, ∀ b ∈ B, c ≤ dist a b) (hδ : 2 * δ < c) :
    packingDelta s δ A + packingDelta s δ B ≤ packingDelta s δ (A ∪ B) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · haveI := hX
    simp [packingDelta_of_isEmpty]
  haveI := nonempty_packing (X := X) δ A
  haveI := nonempty_packing (X := X) δ B
  rw [packingDelta_eq_iSup s δ A, packingDelta_eq_iSup s δ B]
  refine ENNReal.iSup_add_iSup_le fun p q => ?_
  -- balls centred in `A` and balls centred in `B` are disjoint at this cutoff
  have hcross : ∀ i ∈ p.1.1, ∀ j ∈ q.1.1,
      Disjoint (closedBall (p.1.2.1 i) (p.1.2.2 i)) (closedBall (q.1.2.1 j) (q.1.2.2 j)) := by
    intro i hi j hj
    refine Metric.closedBall_disjoint_closedBall ?_
    have h₂ := hsep _ (p.2.centre_mem i hi) _ (q.2.centre_mem j hj)
    have h₃ := p.2.radius_le i hi
    have h₄ := q.2.radius_le j hj
    linarith
  rw [← tsum_merge s p.1.1 q.1.1 p.1.2.2 q.1.2.2]
  exact packingSum_le_packingDelta (isPacking_merge p.2 q.2 hcross)

/-- The packing premeasure is superadditive on positively separated sets. -/
theorem packingPremeasure_add_le_of_separated (s : ℝ) {A B : Set X}
    (h : Metric.AreSeparated A B) :
    packingPremeasure s A + packingPremeasure s B ≤ packingPremeasure s (A ∪ B) := by
  obtain ⟨c, hc, hsep⟩ := exists_dist_of_separated h
  refine le_iInf₂ fun δ hδ => ?_
  have hδ'0 : 0 < min δ (c / 4) := lt_min hδ (by linarith)
  have hδ'c : 2 * min δ (c / 4) < c := by
    have := min_le_right δ (c / 4)
    linarith
  calc packingPremeasure s A + packingPremeasure s B
      ≤ packingDelta s (min δ (c / 4)) A + packingDelta s (min δ (c / 4)) B :=
        add_le_add (packingPremeasure_le_packingDelta s hδ'0 A)
          (packingPremeasure_le_packingDelta s hδ'0 B)
    _ ≤ packingDelta s (min δ (c / 4)) (A ∪ B) := packingDelta_add_le_of_dist hsep hδ'c
    _ ≤ packingDelta s δ (A ∪ B) := packingDelta_anti s _ (min_le_left _ _)

/-- The premeasure identity of Proposition 4.12: the packing premeasure is additive on positively
separated sets. -/
theorem packingPremeasure_union_of_separated (s : ℝ) {A B : Set X}
    (h : Metric.AreSeparated A B) :
    packingPremeasure s (A ∪ B) = packingPremeasure s A + packingPremeasure s B :=
  le_antisymm (packingPremeasure_union_le s A B) (packingPremeasure_add_le_of_separated s h)

/-- Proposition 4.12 (`thm:packing-outer-measure`): the packing measure is a metric outer measure,
so every Borel set is measurable for it. -/
theorem packing_outer_measure (s : ℝ) :
    IsOuterMeasure (packingMeasure (X := X) s) ∧
      ∀ A B : Set X, Metric.AreSeparated A B →
        packingMeasure s (A ∪ B) = packingMeasure s A + packingMeasure s B := by
  refine ⟨isOuterMeasure_packingMeasure s, fun A B hAB =>
    le_antisymm (packingMeasure_union_le s A B) ?_⟩
  refine le_iInf₂ fun U hU => ?_
  have hA : packingMeasure s A ≤ ∑' i, packingPremeasure s (U i ∩ A) :=
    iInf₂_le_of_le (fun i => U i ∩ A) (fun z hz => by
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hU (Or.inl hz))
      exact mem_iUnion.2 ⟨i, hi, hz⟩) le_rfl
  have hB : packingMeasure s B ≤ ∑' i, packingPremeasure s (U i ∩ B) :=
    iInf₂_le_of_le (fun i => U i ∩ B) (fun z hz => by
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hU (Or.inr hz))
      exact mem_iUnion.2 ⟨i, hi, hz⟩) le_rfl
  calc packingMeasure s A + packingMeasure s B
      ≤ (∑' i, packingPremeasure s (U i ∩ A)) + ∑' i, packingPremeasure s (U i ∩ B) :=
        add_le_add hA hB
    _ = ∑' i, (packingPremeasure s (U i ∩ A) + packingPremeasure s (U i ∩ B)) :=
        ENNReal.tsum_add.symm
    _ ≤ ∑' i, packingPremeasure s (U i) := ENNReal.tsum_le_tsum fun i =>
        (packingPremeasure_add_le_of_separated s
          (hAB.mono inter_subset_right inter_subset_right)).trans
          (packingPremeasure_mono s (by
            rw [← inter_union_distrib_left]
            exact inter_subset_left))

/-- The packing measure bundled as an outer measure. -/
def packingMeasureOuter (s : ℝ) : OuterMeasure X :=
  (packing_outer_measure (X := X) s).1.toOuterMeasure

@[simp]
theorem coe_packingMeasureOuter (s : ℝ) :
    ⇑(packingMeasureOuter (X := X) s) = packingMeasure s :=
  rfl

/-- Borel sets are measurable for the packing measure. -/
theorem borel_le_packingMeasure_caratheodory (s : ℝ) :
    borel X ≤ (packingMeasureOuter (X := X) s).caratheodory :=
  (metric_criterion _).2 fun A B hAB => (packing_outer_measure s).2 A B hAB

/-! ## Critical exponents -/

/-- Raising the exponent costs a factor `(2δ)^{t-s}` at the cutoff `δ`. -/
theorem packingDelta_le_mul {s t δ : ℝ} (hst : s < t) (E : Set X) :
    packingDelta t δ E ≤ ENNReal.ofReal ((2 * δ) ^ (t - s)) * packingDelta s δ E := by
  refine packingDelta_le fun I x r hp => ?_
  have hterm : ∀ i : I, ENNReal.ofReal ((2 * r i) ^ t)
      ≤ ENNReal.ofReal ((2 * δ) ^ (t - s)) * ENNReal.ofReal ((2 * r i) ^ s) := by
    rintro ⟨i, hi⟩
    have hr : 0 < 2 * r i := by linarith [hp.radius_pos i hi]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith [hp.radius_le i hi]) _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (2 * r i) ^ t = (2 * r i) ^ (t - s) * (2 * r i) ^ s := by
          rw [← Real.rpow_add hr, show t - s + s = t by ring]
      _ ≤ (2 * δ) ^ (t - s) * (2 * r i) ^ s :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow hr.le (by linarith [hp.radius_le i hi]) (by linarith))
            (Real.rpow_nonneg hr.le s)
  calc ∑' i : I, ENNReal.ofReal ((2 * r i) ^ t)
      ≤ ∑' i : I, ENNReal.ofReal ((2 * δ) ^ (t - s)) * ENNReal.ofReal ((2 * r i) ^ s) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal ((2 * δ) ^ (t - s)) * ∑' i : I, ENNReal.ofReal ((2 * r i) ^ s) :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal ((2 * δ) ^ (t - s)) * packingDelta s δ E :=
        mul_le_mul' le_rfl (packingSum_le_packingDelta hp)

/-- A finite `s`-premeasure forces the `t`-premeasure to vanish for `t > s`. -/
theorem packingPremeasure_eq_zero_of_lt {s t : ℝ} (hst : s < t) {E : Set X}
    (h : packingPremeasure s E ≠ ⊤) : packingPremeasure t E = 0 := by
  have hts : 0 < t - s := sub_pos.2 hst
  obtain ⟨δ₀, hδ₀, hM⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧ packingDelta s δ₀ E ≠ ⊤ := by
    obtain ⟨δ₀, hδ₀⟩ := iInf_lt_iff.1 (lt_top_iff_ne_top.2 h)
    obtain ⟨h₁, h₂⟩ := iInf_lt_iff.1 hδ₀
    exact ⟨δ₀, h₁, h₂.ne⟩
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
  rw [zero_add]
  have hMR : (0 : ℝ) ≤ (packingDelta s δ₀ E).toReal := ENNReal.toReal_nonneg
  have hy0 : 0 < (ε : ℝ) / ((packingDelta s δ₀ E).toReal + 1) :=
    div_pos (NNReal.coe_pos.2 hε) (by linarith)
  set y : ℝ := (ε : ℝ) / ((packingDelta s δ₀ E).toReal + 1) with hydef
  have hδ0 : 0 < min δ₀ (y ^ (1 / (t - s)) / 2) :=
    lt_min hδ₀ (by positivity)
  have h2δ : (2 * min δ₀ (y ^ (1 / (t - s)) / 2)) ^ (t - s) ≤ y := by
    have h₁ : 2 * min δ₀ (y ^ (1 / (t - s)) / 2) ≤ y ^ (1 / (t - s)) := by
      have := min_le_right δ₀ (y ^ (1 / (t - s)) / 2)
      linarith
    calc (2 * min δ₀ (y ^ (1 / (t - s)) / 2)) ^ (t - s) ≤ (y ^ (1 / (t - s))) ^ (t - s) :=
          Real.rpow_le_rpow (by linarith) h₁ hts.le
      _ = y := by
          rw [← Real.rpow_mul hy0.le, one_div, inv_mul_cancel₀ hts.ne', Real.rpow_one]
  calc packingPremeasure t E
      ≤ packingDelta t (min δ₀ (y ^ (1 / (t - s)) / 2)) E :=
        packingPremeasure_le_packingDelta t hδ0 E
    _ ≤ ENNReal.ofReal ((2 * min δ₀ (y ^ (1 / (t - s)) / 2)) ^ (t - s)) *
          packingDelta s (min δ₀ (y ^ (1 / (t - s)) / 2)) E := packingDelta_le_mul hst E
    _ ≤ ENNReal.ofReal y * packingDelta s δ₀ E :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal h2δ) (packingDelta_anti s E (min_le_left _ _))
    _ = ENNReal.ofReal y * ENNReal.ofReal (packingDelta s δ₀ E).toReal := by
        rw [ENNReal.ofReal_toReal hM]
    _ = ENNReal.ofReal (y * (packingDelta s δ₀ E).toReal) := (ENNReal.ofReal_mul hy0.le).symm
    _ ≤ ENNReal.ofReal (ε : ℝ) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hydef, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith [NNReal.coe_pos.2 hε]
    _ = (ε : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal

/-- The critical exponent property of the packing measure. -/
theorem packingMeasure_eq_zero_of_lt {s t : ℝ} (hst : s < t) {E : Set X}
    (h : packingMeasure s E ≠ ⊤) : packingMeasure t E = 0 := by
  obtain ⟨U, hU, hsum⟩ :
      ∃ U : ℕ → Set X, E ⊆ ⋃ i, U i ∧ ∑' i, packingPremeasure s (U i) ≠ ⊤ := by
    obtain ⟨U, hU⟩ := iInf_lt_iff.1 (lt_top_iff_ne_top.2 h)
    obtain ⟨h₁, h₂⟩ := iInf_lt_iff.1 hU
    exact ⟨U, h₁, h₂.ne⟩
  refine le_antisymm ((iInf₂_le_of_le U hU le_rfl).trans ?_) zero_le
  exact le_of_eq (ENNReal.tsum_eq_zero.2 fun i =>
    packingPremeasure_eq_zero_of_lt hst (ENNReal.ne_top_of_tsum_ne_top hsum i))

/-! ## Definition 4.13 (`def:packing-dimension`) -/

/-- Definition 4.13 (`def:packing-dimension`): the packing dimension. -/
def packingDim (E : Set X) : ℝ≥0∞ :=
  ⨅ (s : ℝ≥0) (_ : packingMeasure (s : ℝ) E = 0), (s : ℝ≥0∞)

/-- A vanishing packing measure bounds the packing dimension. -/
theorem packingDim_le_of_packingMeasure_eq_zero {E : Set X} {d : ℝ≥0}
    (h : packingMeasure (d : ℝ) E = 0) : packingDim E ≤ d :=
  iInf₂_le d h

/-- Above the packing dimension the packing measure vanishes. -/
theorem packingMeasure_eq_zero_of_packingDim_lt {E : Set X} {d : ℝ≥0}
    (h : packingDim E < d) : packingMeasure (d : ℝ) E = 0 := by
  obtain ⟨c, hc⟩ := iInf_lt_iff.1 h
  obtain ⟨hc0, hcd⟩ := iInf_lt_iff.1 hc
  exact packingMeasure_eq_zero_of_lt (by exact_mod_cast hcd)
    (ne_of_eq_of_ne hc0 ENNReal.zero_ne_top)

/-- Definition 4.13 (`def:packing-dimension`): the packing dimension as a supremum. -/
theorem packingDim_eq_iSup (E : Set X) :
    packingDim E = ⨆ (s : ℝ≥0) (_ : packingMeasure (s : ℝ) E = ⊤), (s : ℝ≥0∞) := by
  refine le_antisymm ?_ (iSup₂_le fun d hd => le_iInf₂ fun c hc => ?_)
  · by_contra hcon
    obtain ⟨d, hd₁, hd₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (not_le.1 hcon)
    have hdtop : packingMeasure (d : ℝ) E ≠ ⊤ := fun hd =>
      absurd (le_iSup₂ (f := fun (s : ℝ≥0) (_ : packingMeasure (s : ℝ) E = ⊤) =>
        (s : ℝ≥0∞)) d hd) hd₁.not_ge
    obtain ⟨d', hd'₁, hd'₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hd₂
    have h0 : packingMeasure (d' : ℝ) E = 0 :=
      packingMeasure_eq_zero_of_lt (by exact_mod_cast hd'₁) hdtop
    exact absurd (packingDim_le_of_packingMeasure_eq_zero h0) hd'₂.not_ge
  · by_contra hcon
    have h0 : packingMeasure (d : ℝ) E = 0 :=
      packingMeasure_eq_zero_of_lt (by exact_mod_cast not_le.1 hcon)
        (ne_of_eq_of_ne hc ENNReal.zero_ne_top)
    exact absurd (hd.symm.trans h0) ENNReal.top_ne_zero

theorem packingDim_mono {E F : Set X} (h : E ⊆ F) : packingDim E ≤ packingDim F := by
  refine le_iInf₂ fun d hd => packingDim_le_of_packingMeasure_eq_zero (le_antisymm ?_ zero_le)
  exact le_of_le_of_eq (packingMeasure_mono (d : ℝ) h) hd

/-- Packing dimension is countably stable. -/
theorem packingDim_iUnion (E : ℕ → Set X) :
    packingDim (⋃ i, E i) = ⨆ i, packingDim (E i) := by
  refine le_antisymm ?_ (iSup_le fun i => packingDim_mono (subset_iUnion E i))
  by_contra hcon
  obtain ⟨d, hd₁, hd₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (not_le.1 hcon)
  have h0 : ∀ i, packingMeasure (d : ℝ) (E i) = 0 := fun i =>
    packingMeasure_eq_zero_of_packingDim_lt ((le_iSup (fun i => packingDim (E i)) i).trans_lt hd₁)
  have hzero : packingMeasure (d : ℝ) (⋃ i, E i) = 0 := by
    refine le_antisymm (((isOuterMeasure_packingMeasure (d : ℝ)).iUnion_le E).trans ?_) zero_le
    simp [h0]
  exact absurd (hd₂.trans_le (packingDim_le_of_packingMeasure_eq_zero hzero)) (lt_irrefl _)

/-- Countable sets have packing measure zero at every positive exponent. -/
theorem packingMeasure_countable {s : ℝ} (hs : 0 < s) {E : Set X} (hE : E.Countable) :
    packingMeasure s E = 0 := by
  rcases E.eq_empty_or_nonempty with rfl | hne
  · exact le_antisymm ((packingMeasure_le_packingPremeasure s ∅).trans_eq
      (packingPremeasure_empty s)) zero_le
  obtain ⟨f, rfl⟩ := hE.exists_eq_range hne
  refine le_antisymm ((iInf₂_le_of_le (fun i => {f i}) ?_ le_rfl).trans ?_) zero_le
  · exact range_subset_iff.2 fun i => mem_iUnion.2 ⟨i, rfl⟩
  · simp [packingPremeasure_singleton hs]

/-- Countable sets have packing dimension zero. -/
theorem packingDim_countable {E : Set X} (hE : E.Countable) : packingDim E = 0 := by
  refine le_antisymm ?_ zero_le
  by_contra hcon
  obtain ⟨d, hd₁, hd₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (not_le.1 hcon)
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd₁
  exact absurd (hd₂.trans_le
    (packingDim_le_of_packingMeasure_eq_zero (packingMeasure_countable hd0 hE))) (lt_irrefl _)

end GeometricMeasureTheory
