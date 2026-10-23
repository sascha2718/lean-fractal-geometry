import Mathlib
import FractalGeometry.Entropy.Lq.Basic
import FractalGeometry.Entropy.Lq.Limit
import FractalGeometry.Entropy.Lq.Prop413
import FractalGeometry.Entropy.Lq.Prop68
import FractalGeometry.Entropy.Lq.Statements

open MeasureTheory Filter Topology Set

namespace FractalGeometry

namespace Lq

theorem eq_atomicMeasure {ν : Measure ℝ} [IsFiniteMeasure ν] {Y : Finset ℝ}
    (hY : ν (↑Y)ᶜ = 0) : ν = atomicMeasure Y (fun y => ν.real {y}) id := by
  classical
  ext E hE
  have h1 : ν E = ν (E ∩ ↑Y) := by
    refine le_antisymm ?_ (measure_mono Set.inter_subset_left)
    calc ν E ≤ ν (E ∩ ↑Y) + ν (E \ ↑Y) := by
          rw [← measure_union (Set.disjoint_sdiff_inter.symm) (hE.diff (Finset.measurableSet _))]
          · exact measure_mono (by rw [Set.inter_union_sdiff])
      _ = ν (E ∩ ↑Y) := by
          rw [measure_mono_null (show E \ ↑Y ⊆ (↑Y)ᶜ from fun x hx => hx.2) hY, add_zero]
  have h2 : E ∩ ↑Y = ↑(Y.filter (· ∈ E)) := by ext x; simp [and_comm]
  rw [h1, h2, ← sum_measure_singleton]
  unfold atomicMeasure
  rw [Measure.finsetSum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hE, smul_eq_mul]
  by_cases hy : y ∈ E <;> simp [hy, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top ν _)]

theorem measureReal_atomicMeasure_conv_dyadicIco {ι : Type*} (s : Finset ι) {w : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (k : ι → ℤ) (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) (j : ℤ) :
    ((atomicMeasure s w fun i => (k i : ℝ) / 2 ^ n).conv μ).real (dyadicIco n j) =
      ∑ i ∈ s, w i * μ.real (dyadicIco n (j - k i)) := by
  rw [measureReal_atomicMeasure_conv s hw _ μ (measurableSet_dyadicIco n j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  ext x
  simp only [Set.mem_preimage, mem_dyadicIco_iff]
  rw [add_mul, div_mul_cancel₀ _ (by positivity), add_comm, Int.floor_add_intCast]
  omega

theorem lqSum_map_dyadic (ξ : Measure ℝ) [IsFiniteMeasure ξ] (q : ℝ) (m c : ℕ) {β : ℝ} {b : ℤ}
    (hb : β * 2 ^ (m + c) = b) :
    lqSum (ξ.map fun x => x / 2 ^ c + β) q (m + c) = lqSum ξ q m := by
  have hg : Measurable fun x : ℝ => x / 2 ^ c + β := by fun_prop
  have hpre : ∀ j : ℤ, (fun x : ℝ => x / 2 ^ c + β) ⁻¹' dyadicIco (m + c) j =
      dyadicIco m (j - b) := by
    intro j
    ext x
    simp only [Set.mem_preimage, mem_dyadicIco_iff]
    have e : x / 2 ^ c * 2 ^ (m + c) = x * 2 ^ m := by rw [pow_add]; field_simp
    rw [add_mul, e, hb, Int.floor_add_intCast]
    omega
  unfold lqSum
  simp_rw [measureReal_def, Measure.map_apply hg (measurableSet_dyadicIco _ _), hpre]
  exact (Equiv.subRight b).tsum_eq fun k => (ξ (dyadicIco m k)).toReal ^ q

variable {κ : Type*} [Fintype κ]

theorem lqSum_atomicMeasure_conv_map_dyadic {ι : Type*} (s : Finset ι) {w : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (y : ι → ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] (q : ℝ)
    (m c : ℕ) {β : ℝ} {b : ℤ} (hb : β * 2 ^ (m + c) = b) :
    lqSum ((atomicMeasure s w y).conv μ) q m =
      lqSum ((atomicMeasure s w fun i => y i / 2 ^ c).conv
        (μ.map fun x => x / 2 ^ c + β)) q (m + c) := by
  have hg : Measurable fun x : ℝ => x / 2 ^ c + β := by fun_prop
  have hpre : ∀ (z : ℝ) (j : ℤ), (fun x : ℝ => x / 2 ^ c + β) ⁻¹'
      ((fun x => z / 2 ^ c + x) ⁻¹' dyadicIco (m + c) (j + b)) =
      (fun x => z + x) ⁻¹' dyadicIco m j := by
    intro z j
    ext x
    simp only [Set.mem_preimage, mem_dyadicIco_iff]
    have e : (z / 2 ^ c + (x / 2 ^ c + β)) * 2 ^ (m + c) = (z + x) * 2 ^ m + b := by
      rw [← hb, pow_add]; field_simp; ring
    rw [e, Int.floor_add_intCast]
    omega
  have hcell : ∀ j : ℤ, ((atomicMeasure s w y).conv μ).real (dyadicIco m j) =
      ((atomicMeasure s w fun i => y i / 2 ^ c).conv
        (μ.map fun x => x / 2 ^ c + β)).real (dyadicIco (m + c) (j + b)) := by
    intro j
    rw [measureReal_atomicMeasure_conv s hw y μ (measurableSet_dyadicIco _ _),
      measureReal_atomicMeasure_conv s hw _ _ (measurableSet_dyadicIco _ _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_measureReal_apply hg ((measurableSet_dyadicIco _ _).preimage (by fun_prop)), hpre]
  unfold lqSum
  simp_rw [hcell]
  exact ((Equiv.addRight b).tsum_eq fun k => ((atomicMeasure s w fun i => y i / 2 ^ c).conv
    (μ.map fun x => x / 2 ^ c + β)).real (dyadicIco (m + c) k) ^ q)

theorem lqSum_atomicMeasure_div {ι : Type*} (s : Finset ι) {w : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (y : ι → ℝ) {q : ℝ} (hq : 0 < q) (m c : ℕ) :
    lqSum (atomicMeasure s w fun i => y i / 2 ^ c) q (m + c) = lqSum (atomicMeasure s w y) q m := by
  unfold atomicMeasure
  rw [lqSum_sum_dirac s w hw _ hq, lqSum_sum_dirac s w hw _ hq]
  have e : ∀ i, y i / 2 ^ c * 2 ^ (m + c) = y i * 2 ^ m := fun i => by rw [pow_add]; field_simp
  simp_rw [e]

theorem lqSum_atomicMeasure_floor {ι : Type*} (s : Finset ι) {w : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (y : ι → ℝ) {q : ℝ} (hq : 0 < q) (n : ℕ) :
    lqSum (atomicMeasure s w fun i => (⌊y i * 2 ^ n⌋ : ℝ) / 2 ^ n) q n =
      lqSum (atomicMeasure s w y) q n := by
  unfold atomicMeasure
  rw [lqSum_sum_dirac s w hw _ hq, lqSum_sum_dirac s w hw _ hq]
  have e : ∀ i, (⌊y i * 2 ^ n⌋ : ℝ) / 2 ^ n * 2 ^ n = ⌊y i * 2 ^ n⌋ := fun i => by
    field_simp
  simp_rw [e, Int.floor_intCast]

theorem add_rpow_le_two_rpow {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 1 ≤ q) :
    (a + b) ^ q ≤ 2 ^ (q - 1) * (a ^ q + b ^ q) := by
  have := Real.rpow_sum_le_const_mul_sum_rpow (Finset.univ : Finset (Fin 2)) ![a, b] hq
  simpa [Fin.sum_univ_two, abs_of_nonneg ha, abs_of_nonneg hb] using this

theorem lqSum_atomicMeasure_conv_le_floor {ι : Type*} (s : Finset ι) {w : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (y : ι → ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] {q : ℝ}
    (hq : 1 ≤ q) (n : ℕ) :
    lqSum ((atomicMeasure s w y).conv μ) q n ≤
      2 ^ q * lqSum ((atomicMeasure s w fun i => (⌊y i * 2 ^ n⌋ : ℝ) / 2 ^ n).conv μ) q n := by
  set y' : ι → ℝ := fun i => (⌊y i * 2 ^ n⌋ : ℝ) / 2 ^ n
  set ν' := (atomicMeasure s w y').conv μ
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hcell : ∀ j : ℤ, ((atomicMeasure s w y).conv μ).real (dyadicIco n j) ≤
      ν'.real (dyadicIco n j) + ν'.real (dyadicIco n (j - 1)) := by
    intro j
    simp only [ν']
    rw [measureReal_atomicMeasure_conv s hw y μ (measurableSet_dyadicIco _ _),
      measureReal_atomicMeasure_conv s hw y' μ (measurableSet_dyadicIco _ _),
      measureReal_atomicMeasure_conv s hw y' μ (measurableSet_dyadicIco _ _),
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (hw i hi)
    refine (measureReal_mono (s₂ := (fun x => y' i + x) ⁻¹' dyadicIco n j ∪
      (fun x => y' i + x) ⁻¹' dyadicIco n (j - 1)) ?_ (measure_ne_top _ _)).trans
      (measureReal_union_le _ _)
    intro x hx
    simp only [Set.mem_preimage, mem_dyadicIco_iff, Set.mem_union] at hx ⊢
    have h1 := Int.floor_le (y i * 2 ^ n)
    have h2 := Int.lt_floor_add_one (y i * 2 ^ n)
    have e : (y' i + x) * 2 ^ n = ⌊y i * 2 ^ n⌋ + x * 2 ^ n := by
      simp only [y']; field_simp
    have e2 : (y i + x) * 2 ^ n = y i * 2 ^ n + x * 2 ^ n := by ring
    rw [e]
    rw [e2] at hx
    have hx1 := Int.floor_le (y i * 2 ^ n + x * 2 ^ n)
    have hx2 := Int.lt_floor_add_one (y i * 2 ^ n + x * 2 ^ n)
    rw [hx] at hx1 hx2
    rw [Int.floor_intCast_add]
    have hlo : (j : ℝ) - 1 - ⌊y i * 2 ^ n⌋ ≤ x * 2 ^ n := by linarith
    have hhi : x * 2 ^ n < (j : ℝ) + 1 - ⌊y i * 2 ^ n⌋ := by linarith
    have hf1 : j - 1 - ⌊y i * 2 ^ n⌋ ≤ ⌊x * 2 ^ n⌋ := by
      rw [Int.le_floor]; push_cast; exact hlo
    have hf2 : ⌊x * 2 ^ n⌋ < j + 1 - ⌊y i * 2 ^ n⌋ := by
      rw [Int.floor_lt]; push_cast; exact hhi
    omega
  unfold lqSum
  refine Real.tsum_le_of_sum_le (fun k => Real.rpow_nonneg measureReal_nonneg _) fun F => ?_
  calc ∑ j ∈ F, ((atomicMeasure s w y).conv μ).real (dyadicIco n j) ^ q
      ≤ ∑ j ∈ F, 2 ^ (q - 1) * (ν'.real (dyadicIco n j) ^ q +
          ν'.real (dyadicIco n (j - 1)) ^ q) :=
        Finset.sum_le_sum fun j _ => (Real.rpow_le_rpow measureReal_nonneg (hcell j)
          (by linarith)).trans (add_rpow_le_two_rpow measureReal_nonneg measureReal_nonneg hq)
    _ = 2 ^ (q - 1) * (∑ j ∈ F, ν'.real (dyadicIco n j) ^ q +
          ∑ j ∈ F.image (· - 1), ν'.real (dyadicIco n j) ^ q) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_image (fun a _ b _ h => by
          simpa using h)]
    _ ≤ 2 ^ (q - 1) * (lqSum ν' q n + lqSum ν' q n) := by
        gcongr <;> exact sum_le_lqSum ν' hq n _
    _ = 2 ^ q * lqSum ν' q n := by
        rw [← two_mul, ← mul_assoc, ← Real.rpow_add_one (by norm_num)]
        ring_nf

noncomputable def gridMeasure {ι : Type*} (s : Finset ι) (w : ι → ℝ) (k : ι → ℤ) (o : ℤ)
    (k' : ℤ) : ℝ :=
  open Classical in ∑ i ∈ s with k i - o = k', w i

theorem isDyadicMeasure_gridMeasure {ι : Type*} (s : Finset ι) {w : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1) (k : ι → ℤ) {o : ℤ} {n : ℕ}
    (hk : ∀ i ∈ s, o ≤ k i ∧ k i < o + 2 ^ n) : IsDyadicMeasure n (gridMeasure s w k o) := by
  classical
  refine ⟨fun k' => Finset.sum_nonneg fun i hi => hw i (Finset.mem_filter.mp hi).1, ?_, ?_⟩
  · intro k' hk'
    obtain ⟨i, hi, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk'
    obtain ⟨hi', rfl⟩ := Finset.mem_filter.mp hi
    have := hk i hi'
    constructor <;> omega
  · unfold gridMeasure
    rw [Finset.sum_fiberwise_of_maps_to (g := fun i => k i - o) (fun i hi => by
      have := hk i hi
      rw [Finset.mem_Ico]; constructor <;> omega), hw1]

theorem discLq_gridMeasure {ι : Type*} (s : Finset ι) {w : ι → ℝ} (hw : ∀ i ∈ s, 0 ≤ w i)
    (k : ι → ℤ) {o : ℤ} {n : ℕ} (hk : ∀ i ∈ s, o ≤ k i ∧ k i < o + 2 ^ n) {q : ℝ}
    (hq : 0 < q) :
    discLq n q (gridMeasure s w k o) =
      lqSum (atomicMeasure s w fun i => (k i : ℝ) / 2 ^ n) q n := by
  classical
  unfold atomicMeasure
  rw [lqSum_sum_dirac s w hw _ hq]
  have e : ∀ i, (k i : ℝ) / 2 ^ n * 2 ^ n = k i := fun i => by field_simp
  simp_rw [e, Int.floor_intCast]
  unfold discLq gridMeasure
  rw [← Finset.sum_subset (s₁ := (s.image k).image (· - o))]
  · rw [Finset.sum_image (fun a _ b _ h => by simpa using h)]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 2
    ext i
    simp only [Finset.mem_filter]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
  · intro c hc
    simp only [Finset.mem_image] at hc
    obtain ⟨_, ⟨i, hi, rfl⟩, rfl⟩ := hc
    have := hk i hi
    rw [Finset.mem_Ico]; constructor <;> omega
  · intro c _ hc
    have : (s.filter fun i => k i - o = c) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hi hic
      exact hc (Finset.mem_image.mpr ⟨k i, Finset.mem_image_of_mem k hi, hic⟩)
    rw [this, Finset.sum_empty, Real.zero_rpow hq.ne']

theorem lqSum_conv_eq_discLq_circConv {ι : Type*} (s : Finset ι) {w : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (k : ι → ℤ) {o : ℤ} {n : ℕ} (hn : 2 ≤ n)
    (hk : ∀ i ∈ s, o ≤ k i ∧ k i < o + 2 ^ (n - 2)) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ (Set.Icc (3 / 8) (5 / 8))ᶜ = 0) {q : ℝ} (hq : 0 < q) :
    lqSum ((atomicMeasure s w fun i => (k i : ℝ) / 2 ^ n).conv μ) q n =
      discLq n q (circConv n (gridMeasure s w k o) (discretize μ n)) := by
  classical
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hpow : (2 : ℤ) ^ n = 4 * 2 ^ (n - 2) := by
    rw [show n = (n - 2) + 2 by omega, pow_add]; norm_num; ring
  have hpowR : (2 : ℝ) ^ n = 4 * 2 ^ (n - 2) := by exact_mod_cast hpow

  have hzero : ∀ l : ℤ, (l < 2 ^ (n - 2) ∨ 3 * 2 ^ (n - 2) ≤ l) → μ.real (dyadicIco n l) = 0 := by
    intro l hl
    rw [measureReal_def, ENNReal.toReal_eq_zero_iff]
    left
    refine measure_mono_null (show dyadicIco n l ⊆ (Set.Icc (3 / 8) (5 / 8))ᶜ from
      fun x hx hx' => ?_) hμ
    rw [mem_dyadicIco_iff] at hx
    have h1 := Int.floor_le (x * 2 ^ n)
    have h2 := Int.lt_floor_add_one (x * 2 ^ n)
    rw [hx] at h1 h2
    obtain ⟨hx1, hx2⟩ := hx'
    rcases hl with hl | hl
    · have : (l : ℝ) + 1 ≤ 2 ^ (n - 2) := by exact_mod_cast hl
      nlinarith
    · have : 3 * (2 : ℝ) ^ (n - 2) ≤ l := by exact_mod_cast hl
      nlinarith
  set F : ℤ → ℝ := fun j' => ∑ i ∈ s, w i * μ.real (dyadicIco n (j' + o - k i))
  have hcellF : ∀ j : ℤ, ((atomicMeasure s w fun i => (k i : ℝ) / 2 ^ n).conv μ).real
      (dyadicIco n j) = F (j - o) := by
    intro j
    rw [measureReal_atomicMeasure_conv_dyadicIco s hw k μ n j]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 3; ring
  have hFzero : ∀ j' : ℤ, j' ∉ Finset.Ico (0 : ℤ) (2 ^ n) → F j' = 0 := by
    intro j' hj'
    rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hj'
    refine Finset.sum_eq_zero fun i hi => ?_
    have := hk i hi
    rw [hzero _ (by rcases hj' with h | h <;> [left; right] <;> omega), mul_zero]
  have hFcirc : ∀ j' ∈ Finset.Ico (0 : ℤ) (2 ^ n),
      F j' = circConv n (gridMeasure s w k o) (discretize μ n) j' := by
    intro j' hj'
    have hj'' := Finset.mem_Ico.mp hj'
    unfold circConv
    simp only [hj''.1, hj''.2, and_self, ↓reduceIte]
    unfold gridMeasure
    simp_rw [Finset.sum_mul]
    have hfib : ∀ x ∈ Finset.Ico (0 : ℤ) (2 ^ n), ∑ i ∈ s with k i - o = x,
        w i * discretize μ n ((j' - x) % 2 ^ n) =
        ∑ i ∈ s with k i - o = x, w i * discretize μ n ((j' - (k i - o)) % 2 ^ n) :=
      fun x _ => Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
    rw [Finset.sum_congr rfl hfib, Finset.sum_fiberwise_of_maps_to (g := fun i => k i - o)
      (fun i hi => by
        have := hk i hi
        rw [Finset.mem_Ico]; constructor <;> omega)
      (fun i => w i * discretize μ n ((j' - (k i - o)) % 2 ^ n))]
    refine Finset.sum_congr rfl fun i hi => ?_
    congr 1
    have := hk i hi
    unfold discretize
    by_cases hl : 0 ≤ j' - (k i - o)
    · have hmod : (j' - (k i - o)) % 2 ^ n = j' - (k i - o) :=
        Int.emod_eq_of_lt hl (by omega)
      have hlt : j' - (k i - o) < 2 ^ n := by omega
      rw [hmod]
      simp only [hl, hlt, and_self, ↓reduceIte]
      congr 2; ring
    · push Not at hl
      have h1 : 0 ≤ j' - (k i - o) + 2 ^ n := by omega
      have h2 : j' - (k i - o) + 2 ^ n < 2 ^ n := by omega
      have hmod : (j' - (k i - o)) % 2 ^ n = j' - (k i - o) + 2 ^ n := by
        rw [Int.emod_eq_add_self_emod]; exact Int.emod_eq_of_lt h1 h2
      rw [hmod]
      simp only [h1, h2, and_self, ↓reduceIte]
      rw [hzero _ (by left; omega), hzero _ (by right; omega)]
  unfold lqSum
  simp_rw [hcellF]
  have hre := (Equiv.subRight o).tsum_eq (fun j' => F j' ^ q)
  simp only [Equiv.subRight_apply] at hre
  rw [hre]
  rw [tsum_eq_sum (s := Finset.Ico (0 : ℤ) (2 ^ n)) fun j' hj' => by
    rw [hFzero j' hj', Real.zero_rpow hq.ne']]
  unfold discLq
  exact Finset.sum_congr rfl fun j' hj' => by rw [hFcirc j' hj']

theorem lqSum_atomicMeasure_smul {ι : Type*} (s : Finset ι) {w : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (y : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) (q : ℝ) (n : ℕ) :
    lqSum (atomicMeasure s (fun i => c * w i) y) q n = c ^ q * lqSum (atomicMeasure s w y) q n := by
  classical
  unfold lqSum
  rw [← tsum_mul_left]
  congr 1
  funext j
  rw [measureReal_atomicMeasure s (fun i hi => mul_nonneg hc (hw i hi)) y
    (measurableSet_dyadicIco _ _), measureReal_atomicMeasure s hw y (measurableSet_dyadicIco _ _),
    ← Finset.mul_sum, Real.mul_rpow hc (Finset.sum_nonneg fun i hi => hw i
      (Finset.mem_filter.mp hi).1)]

theorem lqSum_atomicMeasure_smul_conv {ι : Type*} (s : Finset ι) {w : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (y : ι → ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] {c : ℝ}
    (hc : 0 ≤ c) (q : ℝ) (n : ℕ) :
    lqSum ((atomicMeasure s (fun i => c * w i) y).conv μ) q n =
      c ^ q * lqSum ((atomicMeasure s w y).conv μ) q n := by
  unfold lqSum
  rw [← tsum_mul_left]
  congr 1
  funext j
  rw [measureReal_atomicMeasure_conv s (fun i hi => mul_nonneg hc (hw i hi)) y μ
    (measurableSet_dyadicIco _ _), measureReal_atomicMeasure_conv s hw y μ
    (measurableSet_dyadicIco _ _)]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, Real.mul_rpow hc (Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi)
    measureReal_nonneg)]

theorem lqSum_conv_le_of_blocks {ι : Type*} (s : Finset ι) {w : ι → ℝ} (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw1 : ∑ i ∈ s, w i = 1) (k : ι → ℤ) {n : ℕ} (hn : 2 ≤ n) {a L : ℝ} (hL : 0 ≤ L)
    (hk : ∀ i ∈ s, a ≤ (k i : ℝ) / 2 ^ n ∧ (k i : ℝ) / 2 ^ n ≤ a + L)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Icc (3 / 8) (5 / 8))ᶜ = 0) {q : ℝ}
    (hq : 1 < q) {θ B : ℝ} (hθ : 0 < θ)
    (hbig : ∀ ζ : ℤ → ℝ, IsDyadicMeasure n ζ →
      discLq n q ζ ≤ θ ^ (-q) * lqSum (atomicMeasure s w fun i => (k i : ℝ) / 2 ^ n) q n →
      discLq n q (circConv n ζ (discretize μ n)) ≤ B)
    (hsmall : θ ^ q * (4 ^ q * lqSum μ q n) ≤ B) :
    lqSum ((atomicMeasure s w fun i => (k i : ℝ) / 2 ^ n).conv μ) q n ≤ (4 * L + 2) ^ q * B := by
  classical
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hn2 : (0 : ℝ) < 2 ^ (n - 2) := by positivity
  have hpowR : (2 : ℝ) ^ n = 4 * 2 ^ (n - 2) := by
    rw [show n = (n - 2) + 2 by omega, pow_add]; norm_num; ring
  have hB0 : 0 ≤ B := le_trans (by
    have := lqSum_nonneg μ q n
    positivity) hsmall
  set β : ι → ℤ := fun i => ⌊(k i : ℝ) / 2 ^ (n - 2)⌋
  set Bl := s.image β

  have hkβ : ∀ i, β i * 2 ^ (n - 2) ≤ k i ∧ k i < β i * 2 ^ (n - 2) + 2 ^ (n - 2) := by
    intro i
    have h1 := Int.floor_le ((k i : ℝ) / 2 ^ (n - 2))
    have h2 := Int.lt_floor_add_one ((k i : ℝ) / 2 ^ (n - 2))
    rw [le_div_iff₀ hn2] at h1
    rw [div_lt_iff₀ hn2] at h2
    have h1' : ((β i * 2 ^ (n - 2) : ℤ) : ℝ) ≤ (k i : ℝ) := by push_cast; exact h1
    have h2' : (k i : ℝ) < ((β i * 2 ^ (n - 2) + 2 ^ (n - 2) : ℤ) : ℝ) := by
      push_cast; simp only [β]; linarith
    exact ⟨Int.cast_le.mp h1', Int.cast_lt.mp h2'⟩

  have hcard : (Bl.card : ℝ) ≤ 4 * L + 2 := by
    have hsub : Bl ⊆ Finset.Icc ⌊4 * a⌋ ⌊4 * a + 4 * L⌋ := by
      intro b hb
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
      have e : (k i : ℝ) / 2 ^ (n - 2) = 4 * ((k i : ℝ) / 2 ^ n) := by rw [hpowR]; field_simp
      simp only [β, e, Finset.mem_Icc]
      obtain ⟨hk1, hk2⟩ := hk i hi
      exact ⟨Int.floor_le_floor (by linarith), Int.floor_le_floor (by linarith)⟩
    have hc := Finset.card_le_card hsub
    rw [Int.card_Icc] at hc
    have h1 := Int.floor_le (4 * a + 4 * L)
    have h2 := Int.lt_floor_add_one (4 * a)
    have hle : ⌊4 * a⌋ ≤ ⌊4 * a + 4 * L⌋ + 1 := by
      have := Int.floor_le_floor (show 4 * a ≤ 4 * a + 4 * L by linarith); omega
    have h3 : ((⌊4 * a + 4 * L⌋ + 1 - ⌊4 * a⌋).toNat : ℝ) =
        ((⌊4 * a + 4 * L⌋ + 1 - ⌊4 * a⌋ : ℤ) : ℝ) := by
      rw [show ((⌊4 * a + 4 * L⌋ + 1 - ⌊4 * a⌋).toNat : ℝ) =
        (((⌊4 * a + 4 * L⌋ + 1 - ⌊4 * a⌋).toNat : ℤ) : ℝ) by norm_cast,
        Int.toNat_of_nonneg (by omega)]
    calc (Bl.card : ℝ) ≤ ((⌊4 * a + 4 * L⌋ + 1 - ⌊4 * a⌋).toNat : ℝ) := by exact_mod_cast hc
      _ = ((⌊4 * a + 4 * L⌋ + 1 - ⌊4 * a⌋ : ℤ) : ℝ) := h3
      _ ≤ 4 * L + 2 := by push_cast; linarith

  set y : ι → ℝ := fun i => (k i : ℝ) / 2 ^ n
  set piece : ℤ → Measure ℝ := fun b => atomicMeasure (s.filter fun i => β i = b) w y
  have hsplit : ∀ E, MeasurableSet E → ((atomicMeasure s w y).conv μ).real E =
      ∑ b ∈ Bl, ((piece b).conv μ).real E := by
    intro E hE
    rw [measureReal_atomicMeasure_conv s hw y μ hE, ← Finset.sum_fiberwise_of_maps_to
      (g := β) (fun i hi => Finset.mem_image_of_mem β hi)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [measureReal_atomicMeasure_conv _ (fun i hi => hw i (Finset.mem_filter.mp hi).1) y μ hE]
  have hpiece : ∀ b ∈ Bl, lqSum ((piece b).conv μ) q n ≤ B := by
    intro b hb
    set sb := s.filter fun i => β i = b
    have hwb : ∀ i ∈ sb, 0 ≤ w i := fun i hi => hw i (Finset.mem_filter.mp hi).1
    set W := ∑ i ∈ sb, w i
    have hW0 : 0 ≤ W := Finset.sum_nonneg hwb
    have hW1 : W ≤ 1 := by
      rw [← hw1]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i hi _ =>
        hw i hi
    rcases hW0.lt_or_eq with hWpos | hWzero
    ·
      set w' : ι → ℝ := fun i => w i / W
      have hw' : ∀ i ∈ sb, 0 ≤ w' i := fun i hi => div_nonneg (hwb i hi) hW0
      have hw'1 : ∑ i ∈ sb, w' i = 1 := by
        simp only [w']; rw [← Finset.sum_div, div_self hWpos.ne']
      have hweq : (fun i => W * w' i) = w := funext fun i => by
        simp only [w']; field_simp
      have hpc : piece b = atomicMeasure sb (fun i => W * w' i) y := by
        rw [hweq]
      have hconv : lqSum ((piece b).conv μ) q n =
          W ^ q * lqSum ((atomicMeasure sb w' y).conv μ) q n := by
        rw [hpc, lqSum_atomicMeasure_smul_conv sb hw' y μ hW0 q n]
      rw [hconv]
      by_cases hθW : θ ≤ W
      ·
        set o := b * 2 ^ (n - 2)
        have hko : ∀ i ∈ sb, o ≤ k i ∧ k i < o + 2 ^ (n - 2) := by
          intro i hi
          have := hkβ i
          rw [(Finset.mem_filter.mp hi).2] at this
          exact this
        have hko' : ∀ i ∈ sb, o ≤ k i ∧ k i < o + 2 ^ n := by
          intro i hi
          have := hko i hi
          have : (2 : ℤ) ^ (n - 2) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
          constructor <;> omega
        have hid := lqSum_conv_eq_discLq_circConv sb hw' k hn hko μ hμ (by linarith : (0 : ℝ) < q)
        rw [hid]
        have hdisc := discLq_gridMeasure sb hw' k hko' (by linarith : (0 : ℝ) < q)
        have hζ := isDyadicMeasure_gridMeasure sb hw' hw'1 k hko'
        have hcond : discLq n q (gridMeasure sb w' k o) ≤
            θ ^ (-q) * lqSum (atomicMeasure s w y) q n := by
          rw [hdisc]
          have hmono : lqSum (atomicMeasure sb (fun i => W * w' i) y) q n ≤
              lqSum (atomicMeasure s w y) q n := by
            rw [← hpc]
            refine lqSum_mono (fun E hE => ?_) hq.le n
            simp only [piece]
            rw [measureReal_atomicMeasure _ (fun i hi => hw i (Finset.mem_filter.mp hi).1) y hE,
              measureReal_atomicMeasure s hw y hE]
            refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) fun i hi _ =>
              hw i (Finset.mem_filter.mp hi).1
            simp only [Finset.mem_filter] at hi ⊢
            exact ⟨hi.1.1, hi.2⟩
          rw [lqSum_atomicMeasure_smul sb hw' y hW0 q n] at hmono
          have hWq : 0 < W ^ q := Real.rpow_pos_of_pos hWpos q
          have h1 : lqSum (atomicMeasure sb w' y) q n ≤
              W ^ (-q) * lqSum (atomicMeasure s w y) q n := by
            rw [Real.rpow_neg hW0, ← div_eq_inv_mul, le_div_iff₀ hWq]
            linarith [mul_comm (W ^ q) (lqSum (atomicMeasure sb w' y) q n)]
          refine h1.trans (mul_le_mul_of_nonneg_right ?_ (lqSum_nonneg _ _ _))
          exact Real.rpow_le_rpow_of_nonpos hθ hθW (by linarith)
        have hle := hbig _ hζ hcond
        calc W ^ q * discLq n q (circConv n (gridMeasure sb w' k o) (discretize μ n))
            ≤ W ^ q * B := mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hW0 _)
          _ ≤ B := mul_le_of_le_one_left hB0 (Real.rpow_le_one hW0 hW1 (by linarith))
      ·
        push Not at hθW
        have hY := lqSum_atomicMeasure_conv_le sb hw' hw'1 y μ hq.le n
        calc W ^ q * lqSum ((atomicMeasure sb w' y).conv μ) q n
            ≤ θ ^ q * (4 ^ q * lqSum μ q n) :=
              mul_le_mul (Real.rpow_le_rpow hW0 hθW.le (by linarith)) hY
                (lqSum_nonneg _ _ _) (by positivity)
          _ ≤ B := hsmall
    ·
      have hw0 : ∀ i ∈ sb, w i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hwb).mp hWzero.symm
      have hz : ∀ j : ℤ, ((piece b).conv μ).real (dyadicIco n j) = 0 := by
        intro j
        simp only [piece]
        rw [measureReal_atomicMeasure_conv _ hwb y μ (measurableSet_dyadicIco _ _)]
        exact Finset.sum_eq_zero fun i hi => by rw [hw0 i hi, zero_mul]
      unfold lqSum
      simp_rw [hz, Real.zero_rpow (by linarith : q ≠ 0), tsum_zero]
      exact hB0

  have hcard0 : (0 : ℝ) ≤ Bl.card := Nat.cast_nonneg _
  have hhol : lqSum ((atomicMeasure s w y).conv μ) q n ≤
      (Bl.card : ℝ) ^ (q - 1) * ∑ b ∈ Bl, lqSum ((piece b).conv μ) q n := by
    unfold lqSum
    rw [← Summable.tsum_finsetSum fun b _ => summable_lq _ hq.le n, ← tsum_mul_left]
    refine (summable_lq _ hq.le n).tsum_le_tsum (fun j => ?_)
      ((summable_sum fun b _ => summable_lq _ hq.le n).mul_left _)
    rw [hsplit _ (measurableSet_dyadicIco _ _)]
    have := Real.rpow_sum_le_const_mul_sum_rpow Bl (fun b => ((piece b).conv μ).real
      (dyadicIco n j)) hq.le
    simpa only [abs_of_nonneg measureReal_nonneg] using this
  calc lqSum ((atomicMeasure s w y).conv μ) q n
      ≤ (Bl.card : ℝ) ^ (q - 1) * ∑ b ∈ Bl, lqSum ((piece b).conv μ) q n := hhol
    _ ≤ (Bl.card : ℝ) ^ (q - 1) * ∑ _b ∈ Bl, B :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpiece) (by positivity)
    _ = (Bl.card : ℝ) ^ q * B := by
        rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, rpow_sub_one_mul_self hcard0 hq.le]
    _ ≤ (4 * L + 2) ^ q * B :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hcard0 hcard (by linarith)) hB0

theorem IsSelfSimilar.map_affine {r t p : κ → ℝ} {μ : Measure ℝ} (h : IsSelfSimilar r t p μ)
    (a b : ℝ) :
    IsSelfSimilar r (fun j => a * t j + (1 - r j) * b) p (μ.map fun x => a * x + b) := by
  have := h.isProbabilityMeasure
  have hg : Measurable fun x : ℝ => a * x + b := by fun_prop
  refine ⟨h.ratio_ne_zero, h.abs_ratio_lt_one, h.weight_pos, h.weight_sum, inferInstance, ?_⟩
  have hcomm : ∀ j, ((μ.map fun x => a * x + b).map fun x => r j * x + (a * t j + (1 - r j) * b)) =
      (μ.map fun x => r j * x + t j).map fun x => a * x + b := by
    intro j
    rw [Measure.map_map (by fun_prop) hg, Measure.map_map hg (by fun_prop)]
    congr 1
    funext x
    simp only [Function.comp_apply]
    ring
  simp_rw [hcomm]
  conv_lhs => rw [h.stationary]
  rw [← Measure.mapₗ_apply_of_measurable hg, map_sum]
  simp only [Measure.mapₗ_apply_of_measurable hg, Measure.map_smul _ hg.aemeasurable]

theorem IsSelfSimilar.lqSpectrum_map_dyadic {r t p : κ → ℝ} {μ : Measure ℝ}
    (h : IsSelfSimilar r t p μ) {c : ℕ} (hc : 1 ≤ c) {q : ℝ} (hq : 1 < q) :
    lqSpectrum (μ.map fun x => x / 2 ^ c + 1 / 2) q = lqSpectrum μ q := by
  have := h.isProbabilityMeasure
  have hfun : (fun x : ℝ => x / 2 ^ c + 1 / 2) = fun x => (2 ^ c)⁻¹ * x + 1 / 2 := by
    funext x; ring
  have h' := h.map_affine ((2 ^ c)⁻¹) (1 / 2)
  rw [← hfun] at h'
  have hlim' := (tendsto_lqExponent h' hq).comp (tendsto_add_atTop_nat c)
  have hlim := tendsto_lqExponent h hq
  have hratio : Tendsto (fun n : ℕ => (n : ℝ) / (n + c)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => 1 - (c : ℝ) / (n + c)) atTop (𝓝 (1 - 0)) := by
      refine tendsto_const_nhds.sub ?_
      exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _
        tendsto_natCast_atTop_atTop)
    rw [sub_zero] at h1
    refine h1.congr' (eventually_ge_atTop 1 |>.mono fun n hn => ?_)
    have : (0 : ℝ) < n + c := by positivity
    field_simp
    ring
  have hprod := hratio.mul hlim
  rw [one_mul] at hprod
  refine tendsto_nhds_unique hlim' (hprod.congr' ?_)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : (1 / 2 : ℝ) * 2 ^ (n + c) = ((2 ^ (n + c - 1) : ℤ) : ℝ) := by
    have hk : n + c = (n + c - 1) + 1 := by omega
    conv_lhs => rw [hk, pow_succ]
    push_cast
    ring
  simp only [Function.comp_apply, lqExponent]
  rw [lqSum_map_dyadic μ q n c hb]
  push_cast
  field_simp

theorem lqSum_le_two_rpow_mul (ν : Measure ℝ) [IsFiniteMeasure ν] {q : ℝ} (hq : 1 ≤ q)
    {n n' : ℕ} (hn : n' ≤ n) :
    lqSum ν q n' ≤ (2 : ℝ) ^ (((n - n' : ℕ) : ℝ) * (q - 1)) * lqSum ν q n := by
  classical
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_sub_cancel_left]
  set ch : ℤ → Finset ℤ := fun k => Finset.Ico (k * 2 ^ d) ((k + 1) * 2 ^ d)
  have hch : ∀ k, (ch k).card = 2 ^ d := fun k => by
    simp only [ch, Int.card_Ico]
    rw [show (k + 1) * 2 ^ d - k * 2 ^ d = (2 : ℤ) ^ d by ring]
    exact_mod_cast Int.toNat_natCast (2 ^ d)
  have hcell : ∀ k, ν.real (dyadicIco n' k) = ∑ j ∈ ch k, ν.real (dyadicIco (n' + d) j) := by
    intro k
    rw [← measureReal_biUnion_finset (fun i _ j _ hij => pairwise_disjoint_dyadicIco _ hij)
      (fun j _ => measurableSet_dyadicIco _ _)]
    congr 1
    ext x
    simp only [Set.mem_iUnion, mem_dyadicIco_iff, ch, Finset.mem_Ico, exists_prop]
    have e : ⌊x * 2 ^ n'⌋ = ⌊x * 2 ^ (n' + d)⌋ / (2 ^ d : ℕ) := by
      rw [← Int.floor_div_natCast]
      congr 1
      push_cast
      rw [pow_add]
      field_simp
    rw [e]
    have h2 : (0 : ℤ) < (2 ^ d : ℕ) := by positivity
    set z := ⌊x * 2 ^ (n' + d)⌋
    have hiff : z / ((2 ^ d : ℕ) : ℤ) = k ↔ k * 2 ^ d ≤ z ∧ z < (k + 1) * 2 ^ d := by
      have e2 : ((2 ^ d : ℕ) : ℤ) = 2 ^ d := by push_cast; rfl
      rw [e2]
      have hp : (0 : ℤ) < 2 ^ d := by positivity
      constructor
      · rintro rfl
        exact ⟨Int.ediv_mul_le _ hp.ne', Int.lt_ediv_add_one_mul_self _ hp⟩
      · rintro ⟨h1, h3⟩
        have h4 : k ≤ z / 2 ^ d := (Int.le_ediv_iff_mul_le hp).mpr h1
        have h5 : z / 2 ^ d < k + 1 := (Int.ediv_lt_iff_lt_mul hp).mpr h3
        omega
    rw [hiff]
    constructor
    · intro h; exact ⟨z, h, rfl⟩
    · rintro ⟨j, hj, rfl⟩; exact hj
  have hsub : ∀ F : Finset ℤ, ∑ k ∈ F, ν.real (dyadicIco n' k) ^ q ≤
      (2 : ℝ) ^ ((d : ℝ) * (q - 1)) * lqSum ν q (n' + d) := by
    intro F
    have hdisj : (↑F : Set ℤ).PairwiseDisjoint ch := by
      intro k _ l _ hkl
      rw [Function.onFun, Finset.disjoint_left]
      intro j hj hj'
      simp only [ch, Finset.mem_Ico] at hj hj'
      apply hkl
      have hp : (0 : ℤ) < 2 ^ d := by positivity
      have h1 : k ≤ j / 2 ^ d := (Int.le_ediv_iff_mul_le hp).mpr hj.1
      have h2 : j / 2 ^ d < k + 1 := (Int.ediv_lt_iff_lt_mul hp).mpr hj.2
      have h3 : l ≤ j / 2 ^ d := (Int.le_ediv_iff_mul_le hp).mpr hj'.1
      have h4 : j / 2 ^ d < l + 1 := (Int.ediv_lt_iff_lt_mul hp).mpr hj'.2
      omega
    calc ∑ k ∈ F, ν.real (dyadicIco n' k) ^ q
        ≤ ∑ k ∈ F, (2 : ℝ) ^ ((d : ℝ) * (q - 1)) *
            ∑ j ∈ ch k, ν.real (dyadicIco (n' + d) j) ^ q := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [hcell k]
          have := Real.rpow_sum_le_const_mul_sum_rpow (ch k)
            (fun j => ν.real (dyadicIco (n' + d) j)) hq
          simp only [abs_of_nonneg measureReal_nonneg, hch k] at this
          rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
            at this
          exact this
      _ = (2 : ℝ) ^ ((d : ℝ) * (q - 1)) *
            ∑ j ∈ F.biUnion ch, ν.real (dyadicIco (n' + d) j) ^ q := by
          rw [← Finset.mul_sum, Finset.sum_biUnion hdisj]
      _ ≤ (2 : ℝ) ^ ((d : ℝ) * (q - 1)) * lqSum ν q (n' + d) :=
          mul_le_mul_of_nonneg_left (sum_le_lqSum ν hq _ _) (by positivity)
  unfold lqSum at hsub ⊢
  exact Real.tsum_le_of_sum_le (fun k => Real.rpow_nonneg measureReal_nonneg _) hsub

set_option maxHeartbeats 2000000 in

theorem flattening_of_theorem51 {r t p : κ → ℝ} {μ : Measure ℝ} (h : IsSelfSimilar r t p μ)
    {q : ℝ} (hq : 1 < q) (hd : DifferentiableAt ℝ (lqSpectrum μ) q)
    (hτ : lqSpectrum μ q < q - 1)
    (h51 : ∀ (t' : κ → ℝ) (μ' : Measure ℝ), IsSelfSimilar r t' p μ' →
      μ' (Set.Icc (3 / 8) (5 / 8))ᶜ = 0 → DifferentiableAt ℝ (lqSpectrum μ') q →
      lqSpectrum μ' q < q - 1 → Theorem51 μ' q) :
    Flattening μ q := by
  classical
  obtain ⟨L₀, hL₀0, hL₀⟩ := h.exists_support
  have := h.isProbabilityMeasure

  obtain ⟨c₁, hc₁⟩ := pow_unbounded_of_one_lt (8 * L₀) (by norm_num : (1 : ℝ) < 2)
  set c := c₁ + 1 with hcdef
  have hc1 : 1 ≤ c := by omega
  have hc : 8 * L₀ < 2 ^ c := lt_of_lt_of_le hc₁ (pow_le_pow_right₀ (by norm_num) (by omega))
  set g : ℝ → ℝ := fun x => x / 2 ^ c + 1 / 2 with hgdef
  have hgfun : g = fun x => (2 ^ c)⁻¹ * x + 1 / 2 := by funext x; simp only [g]; ring
  set μ' := μ.map g with hμ'def
  have h' : IsSelfSimilar r (fun j => (2 ^ c)⁻¹ * t j + (1 - r j) * (1 / 2)) p μ' := by
    have := h.map_affine ((2 ^ c)⁻¹) (1 / 2)
    rwa [← hgfun] at this
  have := h'.isProbabilityMeasure
  have hg : Measurable g := by fun_prop
  have h2c : (0 : ℝ) < 2 ^ c := by positivity
  have hμ'38 : μ' (Set.Icc (3 / 8) (5 / 8))ᶜ = 0 := by
    rw [hμ'def, Measure.map_apply hg measurableSet_Icc.compl]
    refine measure_mono_null (show g ⁻¹' (Set.Icc (3 / 8) (5 / 8))ᶜ ⊆ (Set.Icc (-L₀) L₀)ᶜ from
      fun x hx hxL => hx ?_) hL₀
    obtain ⟨hx1, hx2⟩ := hxL
    have hL8 : L₀ / 2 ^ c ≤ 1 / 8 := by rw [div_le_iff₀ h2c]; linarith
    have h3 : -L₀ / 2 ^ c ≤ x / 2 ^ c := div_le_div_of_nonneg_right hx1 h2c.le
    have h4 : x / 2 ^ c ≤ L₀ / 2 ^ c := div_le_div_of_nonneg_right hx2 h2c.le
    simp only [Set.mem_Icc, g]
    rw [neg_div] at h3
    constructor <;> linarith
  have hμ'11 : μ' (Set.Icc (-1) 1)ᶜ = 0 :=
    measure_mono_null (Set.compl_subset_compl.mpr fun x hx =>
      ⟨by linarith [hx.1], by linarith [hx.2]⟩) hμ'38
  have hτeq : ∀ q', 1 < q' → lqSpectrum μ' q' = lqSpectrum μ q' := fun q' hq' =>
    h.lqSpectrum_map_dyadic hc1 hq'
  have hd' : DifferentiableAt ℝ (lqSpectrum μ') q := by
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hq] with x hx using hτeq x hx
  have hτ' : lqSpectrum μ' q < q - 1 := by rw [hτeq q hq]; exact hτ
  have h51' := h51 _ μ' h' hμ'38 hd' hτ'
  intro σ hσ
  set σ₂ := σ / 2 with hσ₂def
  have hσ₂ : 0 < σ₂ := by positivity
  obtain ⟨εc, hεc, D, hD, hev⟩ := h51' (σ₂ / 4) (by positivity)
  set τ := lqSpectrum μ q
  have hτ0 : 0 ≤ τ := lqSpectrum_nonneg hL₀0 hL₀ hq.le
  have hq1 : 0 < q - 1 := by linarith
  set η := min εc (σ₂ * (q - 1) / 4)
  have hη : 0 < η := lt_min hεc (by positivity)
  refine ⟨η / 4, by positivity, fun L hL => ?_⟩
  set K : ℝ := 2 ^ q * (4 * L + 6) ^ q * 4 ^ q
  have hD0 : 0 < D := by omega
  have htD : Tendsto (fun ℓ : ℕ => ℓ * D) atTop atTop :=
    tendsto_atTop_mono (fun ℓ => Nat.le_mul_of_pos_right ℓ hD0) tendsto_id
  have ev2 := htD.eventually (eventually_lqSum_le (L := 1) zero_le_one
    hμ'11 hq.le (show τ - σ₂ * (q - 1) / 4 < lqSpectrum μ' q by
      rw [hτeq q hq]; have : 0 < σ₂ * (q - 1) / 4 := by positivity
      linarith))
  have ev3 := ((tendsto_sub_atTop_nat c).comp htD).eventually
    (eventually_le_two_rpow K (show 0 < η / 2 by positivity))

  have core : ∀ᶠ ℓ : ℕ in atTop, ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
      (∃ Y : Finset ℝ, ν (↑Y)ᶜ = 0) → (∃ a : ℝ, ν (Set.Icc a (a + L))ᶜ = 0) →
      lqSum ν q (ℓ * D - c) ≤ (2 : ℝ) ^ (-(σ₂ * (q - 1) * (ℓ * D - c : ℕ))) →
      lqSum (ν.conv μ) q (ℓ * D - c) ≤ (2 : ℝ) ^ (-((τ + η / 2) * (ℓ * D - c : ℕ))) := by
    filter_upwards [hev, ev2, ev3, eventually_ge_atTop (3 * c + 2)]
      with ℓ h1 h2 h3 hℓ ν _ ⟨Y, hY⟩ ⟨a, ha⟩ hν'
    change K ≤ (2 : ℝ) ^ (η / 2 * ((ℓ * D - c : ℕ) : ℝ)) at h3
    obtain ⟨m, hmdef⟩ : ∃ m, m = ℓ * D - c := ⟨_, rfl⟩
    have hℓD : ℓ * 3 ≤ ℓ * D := Nat.mul_le_mul_left ℓ hD
    have hnm : ℓ * D = m + c := by omega
    have hm : 3 * c + 2 ≤ m := by omega
    rw [← hmdef] at hν' h3 ⊢
    rw [hnm] at h1 h2
    set n := m + c with hndef
    have hn2 : 2 ≤ n := by omega
    have hn4 : 4 * c ≤ n := by omega
    have hm' : (m : ℝ) = n - c := by simp only [n]; push_cast; ring

    set Y' := Y.filter fun y => y ∈ Set.Icc a (a + L)
    have hY' : ν (↑Y')ᶜ = 0 := by
      refine measure_mono_null (fun x hx => ?_) (measure_union_null hY ha)
      simp only [Y', Finset.coe_filter, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and] at hx
      by_cases hxY : x ∈ Y
      · exact Or.inr (hx hxY)
      · exact Or.inl hxY
    set w : ℝ → ℝ := fun y => ν.real {y}
    have hw : ∀ y ∈ Y', 0 ≤ w y := fun y _ => measureReal_nonneg
    have hνeq : ν = atomicMeasure Y' w id := eq_atomicMeasure hY'
    have hw1 : ∑ y ∈ Y', w y = 1 := by
      have := atomicMeasure_univ Y' hw id
      rw [← hνeq] at this
      rw [← this, probReal_univ]
    have hY'a : ∀ y ∈ Y', a ≤ y ∧ y ≤ a + L := fun y hy => (Finset.mem_filter.mp hy).2

    have hb : (1 / 2 : ℝ) * 2 ^ (m + c) = ((2 ^ (m + c - 1) : ℤ) : ℝ) := by
      have hk : m + c = (m + c - 1) + 1 := by omega
      conv_lhs => rw [hk, pow_succ]
      push_cast
      ring
    have hS2 : lqSum (ν.conv μ) q m = lqSum ((atomicMeasure Y' w fun y => id y / 2 ^ c).conv μ')
        q n := by
      rw [hνeq]
      exact lqSum_atomicMeasure_conv_map_dyadic Y' hw id μ q m c hb

    set kk : ℝ → ℤ := fun y => ⌊id y / 2 ^ c * 2 ^ n⌋
    have hS4 := lqSum_atomicMeasure_conv_le_floor Y' hw (fun y => id y / 2 ^ c) μ' hq.le n

    have hlqν₂ : lqSum (atomicMeasure Y' w fun y => (kk y : ℝ) / 2 ^ n) q n = lqSum ν q m := by
      rw [lqSum_atomicMeasure_floor Y' hw (fun y => id y / 2 ^ c) (by linarith) n,
        lqSum_atomicMeasure_div Y' hw id (by linarith) m c, ← hνeq]

    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    have hkk : ∀ y ∈ Y', a / 2 ^ c - 1 / 2 ^ n ≤ (kk y : ℝ) / 2 ^ n ∧
        (kk y : ℝ) / 2 ^ n ≤ a / 2 ^ c - 1 / 2 ^ n + (L / 2 ^ c + 1 / 2 ^ n) := by
      intro y hy
      obtain ⟨hy1, hy2⟩ := hY'a y hy
      have f1 := Int.floor_le (id y / 2 ^ c * 2 ^ n)
      have f2 := Int.lt_floor_add_one (id y / 2 ^ c * 2 ^ n)
      simp only [id] at f1 f2
      have e1 : (kk y : ℝ) / 2 ^ n ≤ y / 2 ^ c := by
        rw [div_le_iff₀ h2n]; exact f1
      have e2 : y / 2 ^ c - 1 / 2 ^ n < (kk y : ℝ) / 2 ^ n := by
        have h6 : (y / 2 ^ c * 2 ^ n - 1) / 2 ^ n < (kk y : ℝ) / 2 ^ n :=
          div_lt_div_of_pos_right (by simp only [kk, id]; linarith) h2n
        have e : (y / 2 ^ c * 2 ^ n - 1) / 2 ^ n = y / 2 ^ c - 1 / 2 ^ n := by field_simp
        rwa [e] at h6
      have e3 : a / 2 ^ c ≤ y / 2 ^ c := div_le_div_of_nonneg_right hy1 h2c.le
      have e4 : y / 2 ^ c ≤ (a + L) / 2 ^ c := div_le_div_of_nonneg_right hy2 h2c.le
      rw [add_div] at e4
      constructor <;> linarith
    have hLc : L / 2 ^ c + 1 / 2 ^ n ≤ L + 1 := by
      have : L / 2 ^ c ≤ L := div_le_self hL.le (one_le_pow₀ (by norm_num))
      have : 1 / (2 : ℝ) ^ n ≤ 1 := by rw [div_le_one h2n]; exact one_le_pow₀ (by norm_num)
      linarith

    set θ : ℝ := (2 : ℝ) ^ (-(σ₂ * (q - 1) * n / (2 * q)))
    have hθ : 0 < θ := by positivity
    set B : ℝ := 4 ^ q * (2 : ℝ) ^ (-((τ + η) * n))
    have hθq : θ ^ q = (2 : ℝ) ^ (-(σ₂ * (q - 1) * n / 2)) := by
      rw [← Real.rpow_mul (by norm_num)]; congr 1; field_simp
    have hθnq : θ ^ (-q) = (2 : ℝ) ^ (σ₂ * (q - 1) * n / 2) := by
      rw [← Real.rpow_mul (by norm_num)]; congr 1; field_simp
    have hbig : ∀ ζ : ℤ → ℝ, IsDyadicMeasure n ζ →
        discLq n q ζ ≤ θ ^ (-q) * lqSum (atomicMeasure Y' w fun y => (kk y : ℝ) / 2 ^ n) q n →
        discLq n q (circConv n ζ (discretize μ' n)) ≤ B := by
      intro ζ hζ hζq
      have hdisc0 : 0 ≤ discLq n q ζ :=
        Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hζ.nonneg j) _
      have hcond : discLq n q ζ ^ (1 / (q - 1)) ≤ (2 : ℝ) ^ (-(σ₂ / 4 * n)) := by
        rw [hlqν₂, hθnq] at hζq
        have h5 : discLq n q ζ ≤ (2 : ℝ) ^ (σ₂ * (q - 1) * n / 2 + -(σ₂ * (q - 1) * m)) := by
          rw [Real.rpow_add (by norm_num)]
          exact hζq.trans (mul_le_mul_of_nonneg_left hν' (by positivity))
        refine (Real.rpow_le_rpow hdisc0 h5 (by positivity)).trans ?_
        rw [← Real.rpow_mul (by norm_num)]
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        rw [hm']
        have hn4' : (4 : ℝ) * c ≤ n := by exact_mod_cast hn4
        have e : (σ₂ * (q - 1) * n / 2 + -(σ₂ * (q - 1) * (n - c))) * (1 / (q - 1)) =
            σ₂ * c - σ₂ * n / 2 := by field_simp; ring
        rw [e]
        nlinarith
      have h51n := h1 ζ hζ hcond
      rw [hτeq q hq] at h51n
      refine h51n.trans ?_
      calc (2 : ℝ) ^ (-((τ + εc) * n)) ≤ 1 * (2 : ℝ) ^ (-((τ + η) * n)) := by
            rw [one_mul]
            refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
            have := min_le_left εc (σ₂ * (q - 1) / 4)
            have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
            nlinarith
        _ ≤ B := mul_le_mul_of_nonneg_right (Real.one_le_rpow (by norm_num) (by linarith))
            (by positivity)
    have hsmall : θ ^ q * (4 ^ q * lqSum μ' q n) ≤ B := by
      rw [hθq]
      have h2' : lqSum μ' q n ≤ (2 : ℝ) ^ (-((τ - σ₂ * (q - 1) / 4) * n)) := h2
      calc (2 : ℝ) ^ (-(σ₂ * (q - 1) * n / 2)) * (4 ^ q * lqSum μ' q n)
          ≤ (2 : ℝ) ^ (-(σ₂ * (q - 1) * n / 2)) * (4 ^ q *
              (2 : ℝ) ^ (-((τ - σ₂ * (q - 1) / 4) * n))) := by gcongr
        _ = 4 ^ q * (2 : ℝ) ^ (-((τ + σ₂ * (q - 1) / 4) * n)) := by
            rw [mul_left_comm, two_rpow_mul_two_rpow]; congr 2; ring
        _ ≤ B := by
            show _ ≤ 4 ^ q * (2 : ℝ) ^ (-((τ + η) * n))
            refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
              (by positivity)
            have := min_le_right εc (σ₂ * (q - 1) / 4)
            have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
            nlinarith
    have hblocks := lqSum_conv_le_of_blocks Y' hw hw1 kk hn2 (a := a / 2 ^ c - 1 / 2 ^ n)
      (L := L / 2 ^ c + 1 / 2 ^ n) (by positivity) hkk μ' hμ'38 hq hθ hbig hsmall

    have hB0 : 0 ≤ B := by positivity
    calc lqSum (ν.conv μ) q m
        = lqSum ((atomicMeasure Y' w fun y => id y / 2 ^ c).conv μ') q n := hS2
      _ ≤ 2 ^ q * lqSum ((atomicMeasure Y' w fun y => (kk y : ℝ) / 2 ^ n).conv μ') q n := hS4
      _ ≤ 2 ^ q * ((4 * (L / 2 ^ c + 1 / 2 ^ n) + 2) ^ q * B) :=
          mul_le_mul_of_nonneg_left hblocks (by positivity)
      _ ≤ 2 ^ q * ((4 * L + 6) ^ q * B) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity)
            (by linarith [hLc]) (by linarith)) hB0) (by positivity)
      _ = K * (2 : ℝ) ^ (-((τ + η) * n)) := by simp only [K, B]; ring
      _ ≤ (2 : ℝ) ^ (η / 2 * m) * (2 : ℝ) ^ (-((τ + η) * m)) := by
          refine mul_le_mul h3 (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) (by positivity)
            (by positivity)
          have : (m : ℝ) ≤ n := by simp only [n]; push_cast; linarith
          nlinarith
      _ = (2 : ℝ) ^ (-((τ + η / 2) * m)) := by rw [two_rpow_mul_two_rpow]; congr 1; ring

  obtain ⟨ℓ₀, hℓ₀⟩ := eventually_atTop.mp core
  have hσr := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * D / σ)
  have hηr := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
    (4 * (τ + η / 2) * D / η)
  filter_upwards [hσr, hηr, eventually_ge_atTop (ℓ₀ * D)] with m hmσ hmη hmℓ ν _ hY ha hν
  set ℓ := (m + c) / D
  have hlo : ℓ * D ≤ m + c := Nat.div_mul_le_self _ _
  have hhi : m + c < ℓ * D + D := Nat.lt_div_mul_add hD0
  have hℓ : ℓ₀ ≤ ℓ := (Nat.le_div_iff_mul_le hD0).mpr (by omega)
  set m' := ℓ * D - c
  have hm'm : m' ≤ m := by omega
  have hmm' : m < m' + D := by omega
  have hmD : ((m - m' : ℕ) : ℝ) ≤ D := by exact_mod_cast (show m - m' ≤ D by omega)
  have hmr : (m : ℝ) < m' + D := by exact_mod_cast hmm'
  have hm'r : (m' : ℝ) ≤ m := by exact_mod_cast hm'm
  have hνm : lqSum ν q m ≤ (2 : ℝ) ^ (-(σ * (q - 1) * m)) := by
    have h0 : 0 ≤ lqSum ν q m := lqSum_nonneg _ _ _
    have := Real.rpow_le_rpow (Real.rpow_nonneg h0 _) hν hq1.le
    rwa [← Real.rpow_mul h0, one_div, inv_mul_cancel₀ hq1.ne', Real.rpow_one,
      ← Real.rpow_mul (by norm_num), show -(σ * m) * (q - 1) = -(σ * (q - 1) * m) by ring] at this
  have hνm' : lqSum ν q m' ≤ (2 : ℝ) ^ (-(σ₂ * (q - 1) * m')) := by
    calc lqSum ν q m' ≤ (2 : ℝ) ^ (((m - m' : ℕ) : ℝ) * (q - 1)) * lqSum ν q m :=
          lqSum_le_two_rpow_mul ν hq.le hm'm
      _ ≤ (2 : ℝ) ^ ((D : ℝ) * (q - 1)) * (2 : ℝ) ^ (-(σ * (q - 1) * m)) :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (mul_le_mul_of_nonneg_right hmD hq1.le)) hνm (lqSum_nonneg _ _ _) (by positivity)
      _ = (2 : ℝ) ^ ((q - 1) * (D - σ * m)) := by rw [two_rpow_mul_two_rpow]; congr 1; ring
      _ ≤ (2 : ℝ) ^ (-(σ₂ * (q - 1) * m')) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          have h2D : 2 * (D : ℝ) ≤ σ * m := by
            rw [div_le_iff₀ hσ] at hmσ; linarith
          have hA : (D : ℝ) - σ * m + σ₂ * m' ≤ 0 := by
            have : σ * (m' : ℝ) ≤ σ * m := mul_le_mul_of_nonneg_left hm'r hσ.le
            simp only [σ₂]; linarith
          nlinarith
  have := hℓ₀ ℓ hℓ ν hY ha hνm'
  have : IsFiniteMeasure (ν.conv μ) := by unfold Measure.conv; infer_instance
  calc lqSum (ν.conv μ) q m ≤ lqSum (ν.conv μ) q m' := lqSum_le_of_le _ hq.le hm'm
    _ ≤ (2 : ℝ) ^ (-((τ + η / 2) * m')) := by assumption
    _ ≤ (2 : ℝ) ^ (-((τ + η / 4) * m)) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have h4 : (τ + η / 2) * D ≤ η / 4 * m := by
          rw [div_le_iff₀ hη] at hmη; linarith
        have h5 : (τ + η / 2) * (m - D) ≤ (τ + η / 2) * m' :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        nlinarith

end Lq

end FractalGeometry
