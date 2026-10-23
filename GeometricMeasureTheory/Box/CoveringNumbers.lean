/-
# Section 4.1: Covering and packing numbers

Section 4 of the notes, *Box-counting and packing dimensions*, counts covering and packing balls at
one scale. Mathlib already carries both counts: `Metric.externalCoveringNumber r E` is the notes'
`N_r(E)`, the least number of balls of radius `r` with ambient centres covering `E`, and
`Metric.packingNumber r E` is the notes' `M_r(E)`, the largest cardinality of an `r`-separated
subset of `E`. Mathlib's covers use closed balls and its separated sets use strict inequality;
these conventions change the counts only by a change of radius, which Proposition 4.4 shows does
not affect the dimensions.

| Notes | Lean declaration | Location |
|---|---|---|
| Definition 4.1 (covering and packing numbers) | `Metric.externalCoveringNumber`, `Metric.packingNumber`, `Metric.coveringNumber` | `Mathlib/Topology/MetricSpace/CoveringNumbers.lean` |
| Centres in the set cost a factor of two | `Metric.coveringNumber_two_mul_le_externalCoveringNumber` | `Mathlib/Topology/MetricSpace/CoveringNumbers.lean` |
| Lemma 4.2 (covering against packing) | `covering_packing_numbers` | here |
| Finiteness for totally bounded sets | `externalCoveringNumber_ne_top`, `packingNumber_ne_top` | here |
| A minimising finite cover | `exists_isCover_encard_eq` | here |
| Non-empty sets need at least one ball | `one_le_externalCoveringNumber` | here |
| Separated sets bound the count from below | `encard_le_externalCoveringNumber` | here |
| Subadditivity in the set | `externalCoveringNumber_union_le` | here |
| Passing to the closure | `externalCoveringNumber_closure_le` | here |
| Lipschitz images | `externalCoveringNumber_image_le` | here |
-/
import GeometricMeasureTheory.Hausdorff.Basic

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

variable {X : Type*} [PseudoMetricSpace X]

/-! ## Definition 4.1 (`def:covering-packing-numbers`)

The covering number counts closed balls with ambient centres, and the packing number counts
`r`-separated subsets. -/

example (r : ℝ≥0) (E : Set X) :
    Metric.externalCoveringNumber r E = ⨅ (C : Set X) (_ : Metric.IsCover r E C), C.encard :=
  rfl

example (r : ℝ≥0) (E : Set X) :
    Metric.packingNumber r E =
      ⨆ (C : Set X) (_ : C ⊆ E) (_ : Metric.IsSeparated r C), C.encard :=
  rfl

/-! Requiring the centres to lie in `E` increases the count by at most a change of radius, which is
`Metric.coveringNumber_two_mul_le_externalCoveringNumber`. -/

example (r : ℝ≥0) (E : Set X) :
    Metric.coveringNumber (2 * r) E ≤ Metric.externalCoveringNumber r E :=
  Metric.coveringNumber_two_mul_le_externalCoveringNumber r E

/-! ## Lemma 4.2 (`thm:covering-packing-numbers`) -/

/-- Lemma 4.2 (`thm:covering-packing-numbers`): `N_{2r}(E) ≤ M_r(E) ≤ N_{r/2}(E)`. -/
theorem covering_packing_numbers (r : ℝ≥0) (E : Set X) :
    Metric.externalCoveringNumber (2 * r) E ≤ Metric.packingNumber r E ∧
      Metric.packingNumber r E ≤ Metric.externalCoveringNumber (r / 2) E := by
  constructor
  · calc Metric.externalCoveringNumber (2 * r) E
        ≤ Metric.externalCoveringNumber r E := by
          refine Metric.externalCoveringNumber_anti ?_
          nlinarith [r.coe_nonneg, NNReal.coe_le_coe (r₁ := r) (r₂ := 2 * r)]
      _ ≤ Metric.coveringNumber r E := Metric.externalCoveringNumber_le_coveringNumber r E
      _ ≤ Metric.packingNumber r E := Metric.coveringNumber_le_packingNumber r E
  · calc Metric.packingNumber r E = Metric.packingNumber (2 * (r / 2)) E := by
          rw [mul_div_cancel₀ _ (two_ne_zero)]
      _ ≤ Metric.externalCoveringNumber (r / 2) E :=
          Metric.packingNumber_two_mul_le_externalCoveringNumber (r / 2) E

/-- A totally bounded set has finite covering numbers at every positive radius. -/
theorem externalCoveringNumber_ne_top {E : Set X} (hE : TotallyBounded E) {r : ℝ≥0}
    (hr : 0 < r) : Metric.externalCoveringNumber r E ≠ ⊤ := by
  obtain ⟨N, -, hN, hcov⟩ := Metric.exists_finite_isCover_of_totallyBounded hr.ne' hE
  exact (hcov.externalCoveringNumber_le_encard.trans_lt hN.encard_lt_top).ne

/-- A totally bounded set has finite packing numbers at every positive radius. -/
theorem packingNumber_ne_top {E : Set X} (hE : TotallyBounded E) {r : ℝ≥0} (hr : 0 < r) :
    Metric.packingNumber r E ≠ ⊤ :=
  ((covering_packing_numbers r E).2.trans_lt
    (lt_top_iff_ne_top.2 (externalCoveringNumber_ne_top hE (by positivity)))).ne

/-! ## A minimising cover

The infimum defining the external covering number is attained whenever it is finite, since `ℕ∞` is
well ordered. -/

/-- A finite `r`-cover of `E` whose cardinality is the external covering number, when the latter is
finite. -/
theorem exists_isCover_encard_eq {r : ℝ≥0} {E : Set X}
    (h : Metric.externalCoveringNumber r E ≠ ⊤) :
    ∃ C : Set X, C.Finite ∧ Metric.IsCover r E C ∧
      C.encard = Metric.externalCoveringNumber r E := by
  simp only [Metric.externalCoveringNumber, ne_eq, iInf_eq_top, Set.encard_eq_top_iff, not_forall,
    Set.not_infinite] at h
  obtain ⟨C', hC'_cover, hC'_fin⟩ := h
  have : Nonempty { s : Set X // Metric.IsCover r E s } := ⟨C', hC'_cover⟩
  obtain ⟨C, hC⟩ :=
    ENat.exists_eq_iInf fun C : { s : Set X // Metric.IsCover r E s } => (C : Set X).encard
  refine ⟨C, ?_, C.2, ?_⟩
  · refine Set.encard_lt_top_iff.mp ?_
    simp only [hC, iInf_lt_top, Set.encard_lt_top_iff, Subtype.exists, exists_prop]
    exact ⟨C', hC'_cover, hC'_fin⟩
  · rw [hC, Metric.externalCoveringNumber]
    simp_rw [iInf_subtype]

/-! ## Elementary properties of the counting functions -/

/-- A non-empty set needs at least one ball. -/
theorem one_le_externalCoveringNumber {E : Set X} (hE : E.Nonempty) (r : ℝ≥0) :
    1 ≤ Metric.externalCoveringNumber r E :=
  Order.one_le_iff_pos.2 (Metric.externalCoveringNumber_pos_iff.2 hE)

/-- A `2r`-separated subset of `E` has at most `N_r(E)` points: a ball of radius `r` contains at
most one of them. -/
theorem encard_le_externalCoveringNumber {r : ℝ≥0} {S E : Set X} (hSE : S ⊆ E)
    (hS : Metric.IsSeparated (2 * r : ℝ≥0) S) :
    S.encard ≤ Metric.externalCoveringNumber r E :=
  (hS.encard_le_packingNumber hSE).trans
    (Metric.packingNumber_two_mul_le_externalCoveringNumber r E)

/-- The covering number is subadditive in the set. -/
theorem externalCoveringNumber_union_le (r : ℝ≥0) (E F : Set X) :
    Metric.externalCoveringNumber r (E ∪ F) ≤
      Metric.externalCoveringNumber r E + Metric.externalCoveringNumber r F := by
  rcases eq_or_ne (Metric.externalCoveringNumber r E) ⊤ with hE | hE
  · simp [hE]
  rcases eq_or_ne (Metric.externalCoveringNumber r F) ⊤ with hF | hF
  · simp [hF]
  obtain ⟨C, -, hC, hCcard⟩ := exists_isCover_encard_eq hE
  obtain ⟨D, -, hD, hDcard⟩ := exists_isCover_encard_eq hF
  have hcov : Metric.IsCover r (E ∪ F) (C ∪ D) := by
    rintro x (hx | hx)
    · obtain ⟨c, hcC, hxc⟩ := hC hx
      exact ⟨c, Or.inl hcC, hxc⟩
    · obtain ⟨d, hdD, hxd⟩ := hD hx
      exact ⟨d, Or.inr hdD, hxd⟩
  calc Metric.externalCoveringNumber r (E ∪ F) ≤ (C ∪ D).encard :=
        hcov.externalCoveringNumber_le_encard
    _ ≤ C.encard + D.encard := Set.encard_union_le C D
    _ = _ := by rw [hCcard, hDcard]

/-- An `r`-cover of `E` is an `s`-cover of the closure of `E` for every `s > r`. -/
theorem isCover_closure_of_lt {r s : ℝ≥0} {E C : Set X} (hC : Metric.IsCover r E C) (hrs : r < s) :
    Metric.IsCover s (closure E) C := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ :=
    EMetric.mem_closure_iff.1 hx ((s - r : ℝ≥0) : ℝ≥0∞) (by
      simpa using tsub_pos_of_lt hrs)
  obtain ⟨c, hcC, hyc⟩ := hC hy
  replace hyc : edist y c ≤ (r : ℝ≥0∞) := hyc
  refine ⟨c, hcC, show edist x c ≤ (s : ℝ≥0∞) from ?_⟩
  calc edist x c ≤ edist x y + edist y c := edist_triangle _ _ _
    _ ≤ ((s - r : ℝ≥0) : ℝ≥0∞) + (r : ℝ≥0∞) := add_le_add hxy.le hyc
    _ = (s : ℝ≥0∞) := by
        rw [← ENNReal.coe_add, tsub_add_cancel_of_le hrs.le]

/-- Taking the closure costs only an arbitrarily small enlargement of the radius. -/
theorem externalCoveringNumber_closure_le {r s : ℝ≥0} (hrs : r < s) (E : Set X) :
    Metric.externalCoveringNumber s (closure E) ≤ Metric.externalCoveringNumber r E :=
  le_iInf₂ fun _ hC => (isCover_closure_of_lt hC hrs).externalCoveringNumber_le_encard

/-- An `L`-Lipschitz image needs at most `N_r(E)` balls of radius `2Lr`: the factor of two moves the
centres of a minimising cover into `E`, where the Lipschitz bound applies. -/
theorem externalCoveringNumber_image_le {Y : Type*} [PseudoMetricSpace Y] {f : X → Y} {L : ℝ≥0}
    {E : Set X} (hf : LipschitzOnWith L f E) (r : ℝ≥0) :
    Metric.externalCoveringNumber (2 * L * r) (f '' E) ≤ Metric.externalCoveringNumber r E := by
  refine le_trans ?_ (Metric.coveringNumber_two_mul_le_externalCoveringNumber r E)
  simp only [Metric.coveringNumber, le_iInf_iff]
  intro C hCE hC
  refine le_trans (Metric.IsCover.externalCoveringNumber_le_encard ?_) (Set.encard_image_le f C)
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨c, hcC, hxc⟩ := hC hx
  replace hxc : edist x c ≤ ((2 * r : ℝ≥0) : ℝ≥0∞) := hxc
  refine ⟨f c, ⟨c, hcC, rfl⟩,
    show edist (f x) (f c) ≤ ((2 * L * r : ℝ≥0) : ℝ≥0∞) from ?_⟩
  calc edist (f x) (f c) ≤ (L : ℝ≥0∞) * edist x c := hf hx (hCE hcC)
    _ ≤ (L : ℝ≥0∞) * ((2 * r : ℝ≥0) : ℝ≥0∞) := by gcongr
    _ = ((2 * L * r : ℝ≥0) : ℝ≥0∞) := by push_cast; ring

end GeometricMeasureTheory
