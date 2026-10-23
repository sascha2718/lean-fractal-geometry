/-
# Section 4.4: The modified box characterisation

Packing dimension equals the modified upper box dimension, the infimum over countable bounded
covers of the supremum of the upper box dimensions of the pieces.

The section `Packings` collects what is needed beyond the interface of Section 4.3: the scale
hidden in a finite premeasure, a criterion for a vanishing premeasure, the covers behind a small
packing measure, and the exponents behind the packing dimension.

| Notes | Lean declaration | Location |
|---|---|---|
| Definition 4.14 (modified upper box dimension) | `modifiedUpperBoxDim` | here |
| Lemma 4.15 (premeasure against box dimension) | `packing_premeasure_box` | here |
| Theorem 4.16 (packing dimension is the modified box dimension) | `packing_modified_box` | here |
| Packing dimension under Lipschitz maps | `packingDim_image_le` | here |
| The comparison inequalities after Theorem 4.16 | `packingDim_le_upperBoxDim`, `dimH_le_packingDim` | here |
| Proposition 4.17 (local box dimension) | `local_box_packing` | here |
-/
import GeometricMeasureTheory.Box.PackingMeasure

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

variable {X : Type*} [MetricSpace X]

/-! ## Definition 4.14 (`def:modified-box`) -/

/-- Definition 4.14 (`def:modified-box`): the modified upper box dimension. -/
def modifiedUpperBoxDim (E : Set X) : ℝ≥0∞ :=
  ⨅ (A : ℕ → Set X) (_ : E ⊆ ⋃ i, A i) (_ : ∀ i, Bornology.IsBounded (A i)), ⨆ i, upperBoxDim (A i)

/-! ## Packings

These four lemmas are the only places where the definitions of `packingPremeasure`,
`packingMeasure` and `packingDim` are unfolded; the packing sums themselves are used only through
the interface of Section 4.3. -/

/-- A finite premeasure comes with a scale whose packing sums are already finite. -/
private lemma exists_packingDelta_ne_top {E : Set X} {s : ℝ} (h : packingPremeasure s E ≠ ⊤) :
    ∃ δ : ℝ, 0 < δ ∧ packingDelta s δ E ≠ ⊤ := by
  have hlt : packingPremeasure s E < ⊤ := lt_top_iff_ne_top.2 h
  rw [packingPremeasure] at hlt
  simp only [iInf_lt_iff] at hlt
  obtain ⟨δ, hδ, hδ'⟩ := hlt
  exact ⟨δ, hδ, hδ'.ne⟩

/-- The packing premeasure vanishes as soon as the packing sums are eventually small. -/
private lemma packingPremeasure_eq_zero_of_forall {E : Set X} {s : ℝ}
    (h : ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ packingDelta s δ E ≤ ε) :
    packingPremeasure s E = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) (by simp)
  obtain ⟨δ, hδ, hδ'⟩ := h ε hε
  rw [zero_add]
  exact (packingPremeasure_le_packingDelta s hδ E).trans hδ'

/-- A bound valid at every exponent with vanishing packing measure bounds the packing dimension
from below. -/
private lemma le_packingDim_of_forall {E : Set X} {x : ℝ≥0∞}
    (h : ∀ u : ℝ≥0, packingMeasure (u : ℝ) E = 0 → x ≤ (u : ℝ≥0∞)) : x ≤ packingDim E :=
  le_iInf fun u => le_iInf fun hu => h u hu

/-- A packing measure below `c` comes with a countable cover whose premeasures sum to less
than `c`. -/
private lemma exists_cover_of_packingMeasure_lt {E : Set X} {s : ℝ} {c : ℝ≥0∞}
    (h : packingMeasure s E < c) :
    ∃ A : ℕ → Set X, E ⊆ ⋃ i, A i ∧ ∑' i, packingPremeasure s (A i) < c := by
  rw [packingMeasure] at h
  simp only [iInf_lt_iff] at h
  obtain ⟨A, hcov, hsum⟩ := h
  exact ⟨A, hcov, hsum⟩

/-! ## Auxiliary lemmas -/

/-- A countable bounded cover bounds the modified upper box dimension from above. -/
private lemma modifiedUpperBoxDim_le {E : Set X} {x : ℝ≥0∞} (A : ℕ → Set X)
    (hcov : E ⊆ ⋃ i, A i) (hb : ∀ i, Bornology.IsBounded (A i)) (h : ⨆ i, upperBoxDim (A i) ≤ x) :
    modifiedUpperBoxDim E ≤ x :=
  le_trans (iInf_le_of_le A (iInf_le_of_le hcov (iInf_le_of_le hb le_rfl))) h

/-- A bound valid for every countable bounded cover bounds the modified upper box dimension from
below. -/
private lemma le_modifiedUpperBoxDim {E : Set X} {x : ℝ≥0∞}
    (h : ∀ A : ℕ → Set X, E ⊆ ⋃ i, A i → (∀ i, Bornology.IsBounded (A i)) →
      x ≤ ⨆ i, upperBoxDim (A i)) : x ≤ modifiedUpperBoxDim E :=
  le_iInf fun A => le_iInf fun hcov => le_iInf fun hb => h A hcov hb

/-- A sum of terms bounded by `c` over a set is at most the cardinality of the set times `c`. -/
private lemma tsum_le_encard_mul {ι : Type*} (T : Set ι) (f : ι → ℝ≥0∞) (c : ℝ≥0∞)
    (hf : ∀ i ∈ T, f i ≤ c) : ∑' i : T, f i ≤ (T.encard : ℝ≥0∞) * c := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun t => ?_
  have hcard : ((t.card : ℕ∞) : ℝ≥0∞) ≤ (T.encard : ℝ≥0∞) := by
    refine ENat.toENNReal_mono ?_
    have h1 : ((t : Set T).image Subtype.val).encard = (t.card : ℕ∞) := by
      rw [Set.InjOn.encard_image (Subtype.val_injective.injOn), Set.encard_coe_eq_coe_finsetCard]
    rw [← h1]
    exact Set.encard_le_encard (by rintro _ ⟨y, -, rfl⟩; exact y.2)
  calc ∑ i ∈ t, f (i : ι) ≤ ∑ _i ∈ t, c := Finset.sum_le_sum fun i _ => hf i i.2
    _ = ((t.card : ℕ∞) : ℝ≥0∞) * c := by
        rw [Finset.sum_const, nsmul_eq_mul]; norm_cast
    _ ≤ (T.encard : ℝ≥0∞) * c := by gcongr

/-- A bound on the cardinality of every separated subset bounds the packing number. -/
private lemma toENNReal_packingNumber_le {E : Set X} {ε : ℝ≥0} {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (h : ∀ C, C ⊆ E → Metric.IsSeparated (ε : ℝ≥0∞) C → (C.encard : ℝ≥0∞) ≤ K) :
    (Metric.packingNumber ε E : ℝ≥0∞) ≤ K := by
  have hfloor : ∀ C, C ⊆ E → Metric.IsSeparated (ε : ℝ≥0∞) C →
      C.encard ≤ ((⌊K.toReal⌋₊ : ℕ) : ℕ∞) := by
    intro C hCE hCsep
    have hle := h C hCE hCsep
    have hfin : C.Finite := by
      rw [← Set.encard_ne_top_iff]
      intro htop
      rw [htop] at hle
      simp only [ENat.toENNReal_top, top_le_iff] at hle
      exact hK hle
    rw [hfin.encard_eq_coe_toFinset_card] at hle ⊢
    rw [ENat.toENNReal_coe] at hle
    have hreal : ((hfin.toFinset.card : ℕ) : ℝ) ≤ K.toReal := by
      have h2 := ENNReal.toReal_mono hK hle
      rwa [ENNReal.toReal_natCast] at h2
    exact_mod_cast Nat.le_floor hreal
  calc (Metric.packingNumber ε E : ℝ≥0∞) ≤ (((⌊K.toReal⌋₊ : ℕ) : ℕ∞) : ℝ≥0∞) := by
        refine ENat.toENNReal_mono ?_
        simp only [Metric.packingNumber]
        exact iSup_le fun C => iSup_le fun hCE => iSup_le fun hCsep => hfloor C hCE hCsep
    _ = ENNReal.ofReal ((⌊K.toReal⌋₊ : ℕ) : ℝ) := by
        rw [ENat.toENNReal_coe, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal K.toReal := ENNReal.ofReal_le_ofReal (Nat.floor_le ENNReal.toReal_nonneg)
    _ = K := ENNReal.ofReal_toReal hK

/-- The dyadic estimate behind the second part of Lemma 4.15: splitting a packing with radii at
most `2 ^ (-K)` into the classes `2 ^ (-k-1) < rᵢ ≤ 2 ^ (-k)`, each class is `2 ^ (-k-1)`-separated
and therefore small, and the sums over the classes form a convergent geometric series. -/
private lemma tsum_le_geometric_of_count {E : Set X} {s t : ℝ} (hs : 0 < s) (_hts : t < s)
    {r₀ : ℝ} (hcount : ∀ r : ℝ, 0 < r → r < r₀ →
      (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞) ≤ ENNReal.ofReal (r ^ (-t)))
    {K : ℕ} (hK : (1 / 2 : ℝ) ^ (K + 2) < r₀)
    {ι : Type*} (x : ι → X) (r : ι → ℝ) (hx : ∀ i, x i ∈ E) (hr0 : ∀ i, 0 < r i)
    (hrδ : ∀ i, r i ≤ (1 / 2 : ℝ) ^ K)
    (hdisj : Pairwise (Function.onFun Disjoint fun i => closedBall (x i) (r i))) :
    ∑' i, ENNReal.ofReal ((2 * r i) ^ s) ≤
      ENNReal.ofReal (2 ^ (2 * t + s)) * (1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ (s - t)))⁻¹ *
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (s - t)) ^ K := by
  have hθ0 : (0 : ℝ) < (1 / 2 : ℝ) ^ (s - t) := Real.rpow_pos_of_pos (by norm_num) _
  have hex : ∀ i, ∃ n : ℕ, (1 / 2 : ℝ) ^ (n + K + 1) < r i := by
    intro i
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (hr0 i) (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨n, lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hn⟩
  obtain ⟨j, hjlt, hjle⟩ : ∃ j : ι → ℕ, (∀ i, (1 / 2 : ℝ) ^ (j i + K + 1) < r i) ∧
      (∀ i, r i ≤ (1 / 2 : ℝ) ^ (j i + K)) := by
    refine ⟨fun i => Nat.find (hex i), fun i => Nat.find_spec (hex i), fun i => ?_⟩
    show r i ≤ (1 / 2 : ℝ) ^ (Nat.find (hex i) + K)
    rcases Nat.eq_zero_or_pos (Nat.find (hex i)) with h0 | hpos
    · rw [h0, Nat.zero_add]
      exact hrδ i
    · have hmin := Nat.find_min (hex i) (m := Nat.find (hex i) - 1) (by omega)
      rw [not_lt] at hmin
      have heq : Nat.find (hex i) - 1 + K + 1 = Nat.find (hex i) + K := by omega
      rwa [heq] at hmin
  rw [← ENNReal.tsum_fiberwise (fun i => ENNReal.ofReal ((2 * r i) ^ s)) j]
  have hinner : ∀ m : ℕ, ∑' (i : j ⁻¹' {m}), ENNReal.ofReal ((2 * r (i : ι)) ^ s) ≤
      ENNReal.ofReal (2 ^ (2 * t + s)) * ENNReal.ofReal ((1 / 2 : ℝ) ^ (s - t)) ^ (m + K) := by
    intro m
    have hR0 : (0 : ℝ) < (1 / 2 : ℝ) ^ (m + K) := by positivity
    have hρ0 : (0 : ℝ) < (1 / 2 : ℝ) ^ (m + K + 1) := by positivity
    have hterm : ∀ i ∈ j ⁻¹' {m}, ENNReal.ofReal ((2 * r i) ^ s) ≤
        ENNReal.ofReal ((2 * (1 / 2 : ℝ) ^ (m + K)) ^ s) := by
      intro i hi
      have hri : r i ≤ (1 / 2 : ℝ) ^ (m + K) := by
        have h := hjle i
        rwa [show j i = m from hi] at h
      have h0 : (0 : ℝ) ≤ 2 * r i := by linarith [hr0 i]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow h0 (by linarith) hs.le)
    have hsep : Metric.IsSeparated ((((1 / 2 : ℝ) ^ (m + K + 1)).toNNReal : ℝ≥0) : ℝ≥0∞)
        (x '' (j ⁻¹' {m})) := by
      rintro y ⟨i, hi, rfl⟩ z ⟨i', hi', rfl⟩ hne
      have hii' : i ≠ i' := fun hEq => hne (by rw [hEq])
      have h1 : x i ∉ closedBall (x i') (r i') := fun hmem =>
        Set.disjoint_left.1 (hdisj hii') (mem_closedBall_self (hr0 i).le) hmem
      rw [mem_closedBall, not_le] at h1
      have h2 : (1 / 2 : ℝ) ^ (m + K + 1) < r i' := by
        have h := hjlt i'
        rwa [show j i' = m from hi'] at h
      rw [show (((((1 / 2 : ℝ) ^ (m + K + 1)).toNNReal : ℝ≥0)) : ℝ≥0∞) =
          ENNReal.ofReal ((1 / 2 : ℝ) ^ (m + K + 1)) from rfl, edist_dist,
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg hρ0.le]
      linarith
    have hinj : Set.InjOn x (j ⁻¹' {m}) := by
      intro i hi i' hi' hEq
      by_contra hne
      exact Set.disjoint_left.1 (hdisj hne) (mem_closedBall_self (hr0 i).le)
        (hEq ▸ mem_closedBall_self (hr0 i').le)
    have hcard : (((j ⁻¹' {m} : Set ι).encard : ℕ∞) : ℝ≥0∞) ≤
        ENNReal.ofReal (((1 / 2 : ℝ) ^ (m + K + 1) / 2) ^ (-t)) := by
      calc (((j ⁻¹' {m} : Set ι).encard : ℕ∞) : ℝ≥0∞)
          = ((x '' (j ⁻¹' {m})).encard : ℝ≥0∞) := by rw [hinj.encard_image]
        _ ≤ (Metric.packingNumber ((1 / 2 : ℝ) ^ (m + K + 1)).toNNReal E : ℝ≥0∞) :=
            ENat.toENNReal_mono (Metric.IsSeparated.encard_le_packingNumber
              (by rintro _ ⟨i, -, rfl⟩; exact hx i) hsep)
        _ ≤ (Metric.externalCoveringNumber
              (((1 / 2 : ℝ) ^ (m + K + 1)).toNNReal / 2) E : ℝ≥0∞) :=
            ENat.toENNReal_mono (covering_packing_numbers _ _).2
        _ = (Metric.externalCoveringNumber
              (((1 / 2 : ℝ) ^ (m + K + 1) / 2 : ℝ)).toNNReal E : ℝ≥0∞) := by
            rw [Real.toNNReal_div hρ0.le]
            norm_num
        _ ≤ ENNReal.ofReal (((1 / 2 : ℝ) ^ (m + K + 1) / 2) ^ (-t)) := by
            refine hcount _ (by positivity) ?_
            calc (1 / 2 : ℝ) ^ (m + K + 1) / 2 = (1 / 2 : ℝ) ^ (m + K + 2) := by
                  rw [pow_succ]; ring
              _ ≤ (1 / 2 : ℝ) ^ (K + 2) :=
                  pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
              _ < r₀ := hK
    have hreal : ((1 / 2 : ℝ) ^ (m + K + 1) / 2) ^ (-t) * (2 * (1 / 2 : ℝ) ^ (m + K)) ^ s =
        2 ^ (2 * t + s) * ((1 / 2 : ℝ) ^ (s - t)) ^ (m + K) := by
      have hρR : (1 / 2 : ℝ) ^ (m + K + 1) / 2 = (1 / 2 : ℝ) ^ (m + K) / 4 := by
        rw [pow_succ]; ring
      have e1 : ((1 / 2 : ℝ) ^ (m + K) / 4) ^ (-t) = ((1 / 2 : ℝ) ^ (m + K)) ^ (-t) * 4 ^ t := by
        rw [Real.div_rpow hR0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
        have h4 : (0 : ℝ) < (4 : ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) t
        field_simp
      have e2 : (2 * (1 / 2 : ℝ) ^ (m + K)) ^ s = 2 ^ s * ((1 / 2 : ℝ) ^ (m + K)) ^ s :=
        Real.mul_rpow (by norm_num) hR0.le
      have e3 : ((1 / 2 : ℝ) ^ (m + K)) ^ (-t) * ((1 / 2 : ℝ) ^ (m + K)) ^ s =
          ((1 / 2 : ℝ) ^ (m + K)) ^ (s - t) := by
        rw [← Real.rpow_add hR0]
        congr 1
        ring
      have e4 : (4 : ℝ) ^ t = 2 ^ (2 * t) := by
        rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      have e5 : ((1 / 2 : ℝ) ^ (m + K)) ^ (s - t) = ((1 / 2 : ℝ) ^ (s - t)) ^ (m + K) := by
        rw [← Real.rpow_natCast ((1 / 2 : ℝ) ^ (s - t)) (m + K),
          ← Real.rpow_natCast (1 / 2 : ℝ) (m + K), ← Real.rpow_mul (by norm_num),
          ← Real.rpow_mul (by norm_num), mul_comm]
      calc ((1 / 2 : ℝ) ^ (m + K + 1) / 2) ^ (-t) * (2 * (1 / 2 : ℝ) ^ (m + K)) ^ s
          = (((1 / 2 : ℝ) ^ (m + K)) ^ (-t) * 4 ^ t) *
              (2 ^ s * ((1 / 2 : ℝ) ^ (m + K)) ^ s) := by rw [hρR, e1, e2]
        _ = (4 ^ t * 2 ^ s) *
              (((1 / 2 : ℝ) ^ (m + K)) ^ (-t) * ((1 / 2 : ℝ) ^ (m + K)) ^ s) := by ring
        _ = (2 ^ (2 * t) * 2 ^ s) * ((1 / 2 : ℝ) ^ (m + K)) ^ (s - t) := by rw [e3, e4]
        _ = 2 ^ (2 * t + s) * ((1 / 2 : ℝ) ^ (m + K)) ^ (s - t) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        _ = 2 ^ (2 * t + s) * ((1 / 2 : ℝ) ^ (s - t)) ^ (m + K) := by rw [e5]
    calc ∑' (i : j ⁻¹' {m}), ENNReal.ofReal ((2 * r (i : ι)) ^ s)
        ≤ ((j ⁻¹' {m} : Set ι).encard : ℝ≥0∞) *
            ENNReal.ofReal ((2 * (1 / 2 : ℝ) ^ (m + K)) ^ s) :=
          tsum_le_encard_mul _ _ _ hterm
      _ ≤ ENNReal.ofReal (((1 / 2 : ℝ) ^ (m + K + 1) / 2) ^ (-t)) *
            ENNReal.ofReal ((2 * (1 / 2 : ℝ) ^ (m + K)) ^ s) := by gcongr
      _ = ENNReal.ofReal (((1 / 2 : ℝ) ^ (m + K + 1) / 2) ^ (-t) *
            (2 * (1 / 2 : ℝ) ^ (m + K)) ^ s) :=
          (ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)).symm
      _ = ENNReal.ofReal (2 ^ (2 * t + s) * ((1 / 2 : ℝ) ^ (s - t)) ^ (m + K)) := by rw [hreal]
      _ = ENNReal.ofReal (2 ^ (2 * t + s)) * ENNReal.ofReal ((1 / 2 : ℝ) ^ (s - t)) ^ (m + K) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _), ENNReal.ofReal_pow hθ0.le]
  calc ∑' (m : ℕ), ∑' (i : j ⁻¹' {m}), ENNReal.ofReal ((2 * r (i : ι)) ^ s)
      ≤ ∑' (m : ℕ), ENNReal.ofReal (2 ^ (2 * t + s)) *
          ENNReal.ofReal ((1 / 2 : ℝ) ^ (s - t)) ^ (m + K) := ENNReal.tsum_le_tsum hinner
    _ = (ENNReal.ofReal (2 ^ (2 * t + s)) * ENNReal.ofReal ((1 / 2 : ℝ) ^ (s - t)) ^ K) *
          ∑' (m : ℕ), ENNReal.ofReal ((1 / 2 : ℝ) ^ (s - t)) ^ m := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun m => by rw [pow_add]; ring
    _ = ENNReal.ofReal (2 ^ (2 * t + s)) * (1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ (s - t)))⁻¹ *
          ENNReal.ofReal ((1 / 2 : ℝ) ^ (s - t)) ^ K := by
        rw [ENNReal.tsum_geometric]
        ring

/-! ## Lemma 4.15 (`thm:packing-premeasure-box`) -/

/-- Lemma 4.15 (`thm:packing-premeasure-box`): a finite packing premeasure bounds the upper box
dimension, and an exponent above the upper box dimension has vanishing premeasure. -/
theorem packing_premeasure_box {E : Set X} {s : ℝ} (hs : 0 < s) :
    (packingPremeasure s E ≠ ⊤ → upperBoxDim E ≤ ENNReal.ofReal s) ∧
      (upperBoxDim E < ENNReal.ofReal s → packingPremeasure s E = 0) := by
  have hofReal : ENNReal.ofReal s = ((s.toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
  have hscoe : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs.le
  refine ⟨fun hfin => ?_, fun hlt => ?_⟩
  · -- Finite packing sums at one scale bound the separated sets at every smaller scale.
    obtain ⟨δ₀, hδ₀, hM⟩ := exists_packingDelta_ne_top hfin
    set M : ℝ≥0∞ := packingDelta s δ₀ E with hMdef
    set C₀ : ℝ≥0 := M.toNNReal * ((4 : ℝ) ^ s).toNNReal + 1 with hC₀def
    have hC₀coe : ((C₀ : ℝ≥0) : ℝ≥0∞) = M * ENNReal.ofReal (4 ^ s) + 1 := by
      rw [hC₀def]
      push_cast
      rw [ENNReal.coe_toNNReal hM]
      rfl
    rw [hofReal]
    refine upperBoxDim_le_of_forall (C := C₀) (by positivity) ?_
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨Set.Ioo (0 : ℝ) (min 1 δ₀),
      mem_nhdsGT_iff_exists_Ioo_subset.2 ⟨min 1 δ₀, by simp [hδ₀], subset_rfl⟩, ?_⟩
    rintro r ⟨hr0, hrlt⟩
    have hr1 : r < 1 := lt_of_lt_of_le hrlt (min_le_left _ _)
    have hrδ₀ : r < δ₀ := lt_of_lt_of_le hrlt (min_le_right _ _)
    rw [hscoe]
    have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (r ^ (-s)) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal
        (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr0 hr1.le (by linarith))
    have hhalf : (2 : ℝ≥0) * (r / 2).toNNReal = r.toNNReal := by
      rw [show (2 : ℝ≥0) = (2 : ℝ).toNNReal by simp, ← Real.toNNReal_mul (by norm_num),
        show (2 : ℝ) * (r / 2) = r by ring]
    have hcp : (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞) ≤
        (Metric.packingNumber (r / 2).toNNReal E : ℝ≥0∞) := by
      refine ENat.toENNReal_mono ?_
      rw [← hhalf]
      exact (covering_packing_numbers (r / 2).toNNReal E).1
    refine hcp.trans (toENNReal_packingNumber_le
      (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) ?_)
    intro C hCE hCsep
    have hsepd : ∀ y ∈ C, ∀ z ∈ C, y ≠ z → 2 * (r / 8) < dist y z := by
      intro y hy z hz hyz
      have h := hCsep hy hz hyz
      rw [show ((((r / 2).toNNReal : ℝ≥0)) : ℝ≥0∞) = ENNReal.ofReal (r / 2) from rfl, edist_dist,
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)] at h
      linarith
    have hbound : (C.encard : ℝ≥0∞) * ENNReal.ofReal ((r / 4) ^ s) ≤ M := by
      have h := encard_mul_le_packingDelta (s := s) (by linarith : (0 : ℝ) < r / 8) hCE hsepd
      rw [show 2 * (r / 8) = r / 4 by ring] at h
      exact h.trans (packingDelta_anti s E (by linarith : r / 8 ≤ δ₀))
    set b : ℝ≥0∞ := ENNReal.ofReal ((r / 4) ^ s) with hbdef
    have hb0 : b ≠ 0 := by
      rw [hbdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact Real.rpow_pos_of_pos (by linarith) s
    have hbtop : b ≠ ⊤ := ENNReal.ofReal_ne_top
    have hbinv : b⁻¹ = ENNReal.ofReal (4 ^ s) * ENNReal.ofReal (r ^ (-s)) := by
      rw [hbdef, ← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos (by linarith) s),
        ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) s).le]
      congr 1
      have h4 : (0 : ℝ) < (4 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
      have hrs : (0 : ℝ) < r ^ s := Real.rpow_pos_of_pos hr0 s
      rw [Real.div_rpow hr0.le (by norm_num), Real.rpow_neg hr0.le]
      field_simp
    calc (C.encard : ℝ≥0∞) ≤ M / b :=
          (ENNReal.le_div_iff_mul_le (Or.inl hb0) (Or.inl hbtop)).2 hbound
      _ = M * ENNReal.ofReal (4 ^ s) * ENNReal.ofReal (r ^ (-s)) := by
          rw [div_eq_mul_inv, hbinv, mul_assoc]
      _ ≤ (M * ENNReal.ofReal (4 ^ s) + 1) * ENNReal.ofReal (r ^ (-s)) := by
          gcongr
          exact le_self_add
      _ = (C₀ : ℝ≥0∞) * ENNReal.ofReal (r ^ (-s)) := by rw [hC₀coe]
  · -- An exponent above the upper box dimension: the dyadic classes of a packing.
    obtain ⟨t, ht, hts⟩ : ∃ t : ℝ≥0, UpperBoxDimLE E (t : ℝ) ∧ (t : ℝ) < s := by
      simp only [upperBoxDim, iInf_lt_iff] at hlt
      obtain ⟨t, ht, htlt⟩ := hlt
      refine ⟨t, ht, ?_⟩
      rwa [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff hs] at htlt
    obtain ⟨r₀, hr₀, hcount⟩ : ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
        (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞) ≤
          ENNReal.ofReal (r ^ (-(t : ℝ))) := by
      obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ht
      exact ⟨u, hu, fun r hr0 hru => hsub ⟨hr0, hru⟩⟩
    have hθ0 : (0 : ℝ) < (1 / 2 : ℝ) ^ (s - (t : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have hθ1 : (1 / 2 : ℝ) ^ (s - (t : ℝ)) < 1 :=
      Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
    have hAtop : ENNReal.ofReal (2 ^ (2 * (t : ℝ) + s)) *
        (1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ (s - (t : ℝ))))⁻¹ ≠ ⊤ := by
      refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
      rw [ne_eq, ENNReal.inv_eq_top]
      refine ne_of_gt (tsub_pos_of_lt ?_)
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hθ0.le).2 hθ1
    refine packingPremeasure_eq_zero_of_forall fun ε hε => ?_
    set A : ℝ≥0∞ := ENNReal.ofReal (2 ^ (2 * (t : ℝ) + s)) *
      (1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ (s - (t : ℝ))))⁻¹ with hAdef
    have hA0 : (0 : ℝ) ≤ A.toReal := ENNReal.toReal_nonneg
    have hεpos : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    obtain ⟨n₁, hn₁⟩ := exists_pow_lt_of_lt_one hr₀ (by norm_num : (1 / 2 : ℝ) < 1)
    obtain ⟨n₂, hn₂⟩ := exists_pow_lt_of_lt_one
      (show (0 : ℝ) < (ε : ℝ) / (A.toReal + 1) by positivity) hθ1
    refine ⟨(1 / 2 : ℝ) ^ max n₁ n₂, by positivity, ?_⟩
    have hKr₀ : (1 / 2 : ℝ) ^ (max n₁ n₂ + 2) < r₀ :=
      lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hn₁
    have hmain : packingDelta s ((1 / 2 : ℝ) ^ max n₁ n₂) E ≤
        A * ENNReal.ofReal ((1 / 2 : ℝ) ^ (s - (t : ℝ))) ^ max n₁ n₂ := by
      refine packingDelta_le fun I x r hp => ?_
      rw [hAdef]
      refine tsum_le_geometric_of_count hs hts hcount hKr₀ (ι := ↥I) (fun i => x i)
        (fun i => r i) (fun i => hp.centre_mem i i.2) (fun i => hp.radius_pos i i.2)
        (fun i => hp.radius_le i i.2) fun i j hij => ?_
      exact hp.disjoint i.2 j.2 fun h => hij (Subtype.ext h)
    refine hmain.trans ?_
    have hθK : ((1 / 2 : ℝ) ^ (s - (t : ℝ))) ^ max n₁ n₂ ≤ (ε : ℝ) / (A.toReal + 1) :=
      le_of_lt (lt_of_le_of_lt
        (pow_le_pow_of_le_one hθ0.le hθ1.le (le_max_right n₁ n₂)) hn₂)
    have hreal : A.toReal * ((1 / 2 : ℝ) ^ (s - (t : ℝ))) ^ max n₁ n₂ ≤ (ε : ℝ) := by
      have h1 : A.toReal * ((1 / 2 : ℝ) ^ (s - (t : ℝ))) ^ max n₁ n₂ ≤
          A.toReal * ((ε : ℝ) / (A.toReal + 1)) := mul_le_mul_of_nonneg_left hθK hA0
      have h2 : A.toReal * ((ε : ℝ) / (A.toReal + 1)) ≤ (ε : ℝ) := by
        rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
        nlinarith
      linarith
    calc A * ENNReal.ofReal ((1 / 2 : ℝ) ^ (s - (t : ℝ))) ^ max n₁ n₂
        = A * ENNReal.ofReal (((1 / 2 : ℝ) ^ (s - (t : ℝ))) ^ max n₁ n₂) := by
          rw [ENNReal.ofReal_pow hθ0.le]
      _ = ENNReal.ofReal A.toReal *
            ENNReal.ofReal (((1 / 2 : ℝ) ^ (s - (t : ℝ))) ^ max n₁ n₂) := by
          rw [ENNReal.ofReal_toReal hAtop]
      _ = ENNReal.ofReal (A.toReal * ((1 / 2 : ℝ) ^ (s - (t : ℝ))) ^ max n₁ n₂) :=
          (ENNReal.ofReal_mul hA0).symm
      _ ≤ ENNReal.ofReal (ε : ℝ) := ENNReal.ofReal_le_ofReal hreal
      _ = (ε : ℝ≥0∞) := by simp

/-! ## Theorem 4.16 (`thm:packing-modified-box`) -/

/-- Packing dimension is at most the upper box dimension. -/
theorem packingDim_le_upperBoxDim {E : Set X} : packingDim E ≤ upperBoxDim E := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hfin => ?_
  set u : ℝ≥0 := (upperBoxDim E).toNNReal + ε with hudef
  have hueq : ((u : ℝ≥0) : ℝ≥0∞) = upperBoxDim E + (ε : ℝ≥0∞) := by
    rw [hudef]
    push_cast
    rw [ENNReal.coe_toNNReal hfin.ne]
  have hu0 : (0 : ℝ) < (u : ℝ) := by
    have : (0 : ℝ≥0) < u := lt_of_lt_of_le hε le_add_self
    exact_mod_cast this
  have hboxlt : upperBoxDim E < ENNReal.ofReal (u : ℝ) := by
    rw [ENNReal.ofReal_coe_nnreal, hueq]
    exact ENNReal.lt_add_right hfin.ne (by exact_mod_cast hε.ne')
  have hzero : packingMeasure (u : ℝ) E = 0 :=
    le_antisymm ((packingMeasure_le_packingPremeasure _ _).trans_eq
      ((packing_premeasure_box hu0).2 hboxlt)) (by simp)
  rw [← hueq]
  exact packingDim_le_of_packingMeasure_eq_zero hzero

/-- Theorem 4.16 (`thm:packing-modified-box`): packing dimension equals the modified upper box
dimension. -/
theorem packing_modified_box (E : Set X) : packingDim E = modifiedUpperBoxDim E := by
  refine le_antisymm (le_modifiedUpperBoxDim fun A hcov hb => ?_) ?_
  · calc packingDim E ≤ packingDim (⋃ i, A i) := packingDim_mono hcov
      _ = ⨆ i, packingDim (A i) := packingDim_iUnion A
      _ ≤ ⨆ i, upperBoxDim (A i) := iSup_mono fun i => packingDim_le_upperBoxDim
  rcases E.eq_empty_or_nonempty with rfl | hE
  · rw [packingDim_countable Set.countable_empty]
    exact modifiedUpperBoxDim_le (fun _ => (∅ : Set X)) (by simp)
      (fun _ => Bornology.isBounded_empty) (by simp)
  obtain ⟨c₀, hc₀⟩ := hE
  have key : ∀ v : ℝ≥0, 0 < v → packingMeasure (v : ℝ) E = 0 →
      modifiedUpperBoxDim E ≤ (v : ℝ≥0∞) := by
    intro v hv hmeas
    have hv0 : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
    obtain ⟨A, hcov, hsum⟩ := exists_cover_of_packingMeasure_lt (c := 1)
      (by rw [hmeas]; norm_num)
    refine modifiedUpperBoxDim_le
      (fun k => A k.unpair.1 ∩ ball c₀ ((k.unpair.2 : ℝ) + 1)) ?_ ?_ ?_
    · intro z hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov hz)
      refine Set.mem_iUnion.2 ⟨Nat.pair i ⌈dist z c₀⌉₊, ?_⟩
      rw [Nat.unpair_pair]
      exact ⟨hi, by simpa using lt_of_le_of_lt (Nat.le_ceil (dist z c₀)) (by linarith)⟩
    · exact fun k => Metric.isBounded_ball.subset Set.inter_subset_right
    · refine iSup_le fun k => ?_
      have hfin : packingPremeasure (v : ℝ)
          (A k.unpair.1 ∩ ball c₀ ((k.unpair.2 : ℝ) + 1)) ≠ ⊤ := by
        refine ne_top_of_le_ne_top ?_ (packingPremeasure_mono _ Set.inter_subset_left)
        exact ne_top_of_lt (lt_of_le_of_lt
          (ENNReal.le_tsum (f := fun i => packingPremeasure (v : ℝ) (A i)) k.unpair.1) hsum)
      have hle := (packing_premeasure_box hv0).1 hfin
      rwa [ENNReal.ofReal_coe_nnreal] at hle
  refine le_packingDim_of_forall fun u hu => ?_
  rcases eq_zero_or_pos u with h0 | hu0
  · subst h0
    simp only [NNReal.coe_zero] at hu
    rw [ENNReal.coe_zero]
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    rw [zero_add]
    refine key ε hε (packingMeasure_eq_zero_of_lt (s := (0 : ℝ)) ?_ ?_)
    · exact_mod_cast hε
    · rw [hu]
      simp
  · exact key u hu0 hu

/-- Hausdorff dimension is at most packing dimension. -/
theorem dimH_le_packingDim (E : Set X) : dimH E ≤ packingDim E := by
  rw [packing_modified_box]
  refine le_modifiedUpperBoxDim fun A hcov hb => ?_
  calc dimH E ≤ dimH (⋃ i, A i) := dimH_mono hcov
    _ = ⨆ i, dimH (A i) := dimH_iUnion A
    _ ≤ ⨆ i, upperBoxDim (A i) :=
        iSup_mono fun i => (hausdorff_lower_box (A i)).trans (lowerBoxDim_le_upperBoxDim (A i))

/-- Packing dimension does not increase under a Lipschitz map. -/
theorem packingDim_image_le {Y : Type*} [MetricSpace Y] {f : X → Y} {L : ℝ≥0} {E : Set X}
    (hf : LipschitzOnWith L f E) : packingDim (f '' E) ≤ packingDim E := by
  rw [packing_modified_box, packing_modified_box]
  refine le_modifiedUpperBoxDim fun A hcov hb => ?_
  refine modifiedUpperBoxDim_le (fun i => f '' (A i ∩ E)) ?_ ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov hz)
    exact Set.mem_iUnion.2 ⟨i, ⟨z, ⟨hi, hz⟩, rfl⟩⟩
  · intro i
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 (hb i)
    refine Metric.isBounded_iff.2 ⟨L * C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    calc dist (f z) (f w) ≤ L * dist z w := hf.dist_le_mul z hz.2 w hw.2
      _ ≤ L * C := by
          have hzw : dist z w ≤ C := hC hz.1 hw.1
          gcongr
  · exact iSup_mono fun i => (upperBoxDim_image_le (hf.mono Set.inter_subset_right)).trans
      (upperBoxDim_mono Set.inter_subset_left)

/-! ## Proposition 4.17 (`thm:local-box-packing`) -/

/-- Proposition 4.17 (`thm:local-box-packing`): if every relatively open piece of a compact set has
the full upper box dimension, then its packing and upper box dimensions agree. -/
theorem local_box_packing {E : Set X} (hE : IsCompact E) (hne : E.Nonempty)
    (h : ∀ U : Set X, IsOpen U → (E ∩ U).Nonempty → upperBoxDim (E ∩ U) = upperBoxDim E) :
    packingDim E = upperBoxDim E := by
  refine le_antisymm packingDim_le_upperBoxDim ?_
  rw [packing_modified_box]
  refine le_modifiedUpperBoxDim fun A hcov hb => ?_
  haveI : Nonempty ↥E := hne.to_subtype
  haveI : CompleteSpace ↥E := hE.isComplete.completeSpace_coe
  have hclosed : ∀ i, IsClosed ((Subtype.val : ↥E → X) ⁻¹' closure (A i)) :=
    fun i => isClosed_closure.preimage continuous_subtype_val
  have hunion : (⋃ i, (Subtype.val : ↥E → X) ⁻¹' closure (A i)) = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov z.2)
    exact Set.mem_iUnion.2 ⟨i, subset_closure hi⟩
  obtain ⟨i, p, hp⟩ := nonempty_interior_of_iUnion_of_closed hclosed hunion
  obtain ⟨U, hUopen, hUeq⟩ := isOpen_induced_iff.1
    (isOpen_interior (s := (Subtype.val : ↥E → X) ⁻¹' closure (A i)))
  have hpU : (p : X) ∈ U := by
    have : p ∈ (Subtype.val : ↥E → X) ⁻¹' U := by rw [hUeq]; exact hp
    exact this
  have hUne : (E ∩ U).Nonempty := ⟨(p : X), p.2, hpU⟩
  have hsub : E ∩ U ⊆ closure (A i) := by
    rintro z ⟨hzE, hzU⟩
    have hz : (⟨z, hzE⟩ : ↥E) ∈ (Subtype.val : ↥E → X) ⁻¹' U := hzU
    rw [hUeq] at hz
    have hz2 : (⟨z, hzE⟩ : ↥E) ∈ (Subtype.val : ↥E → X) ⁻¹' closure (A i) := interior_subset hz
    exact hz2
  calc upperBoxDim E = upperBoxDim (E ∩ U) := (h U hUopen hUne).symm
    _ ≤ upperBoxDim (closure (A i)) := upperBoxDim_mono hsub
    _ = upperBoxDim (A i) := upperBoxDim_closure (A i)
    _ ≤ ⨆ j, upperBoxDim (A j) := le_iSup (fun j => upperBoxDim (A j)) i

end GeometricMeasureTheory
