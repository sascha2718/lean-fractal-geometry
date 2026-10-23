import Mathlib
import FractalGeometry.Entropy.Lq.Basic
import FractalGeometry.Entropy.Lq.Limit
import FractalGeometry.Entropy.Lq.Prop413
import FractalGeometry.Entropy.Lq.Section4
import FractalGeometry.Entropy.Lq.Statement
import FractalGeometry.Pressure.Rectangular.LyapunovStatement
import FractalGeometry.SelfSimilar.SimilarityWords

open MeasureTheory Filter Topology Set

namespace FractalGeometry

namespace Lq

def Flattening (μ : Measure ℝ) (q : ℝ) : Prop :=
  ∀ σ : ℝ, 0 < σ → ∃ ε : ℝ, 0 < ε ∧ ∀ L : ℝ, 0 < L → ∀ᶠ m : ℕ in atTop,
    ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν], (∃ Y : Finset ℝ, ν (↑Y)ᶜ = 0) →
      (∃ a : ℝ, ν (Set.Icc a (a + L))ᶜ = 0) →
      lqSum ν q m ^ (1 / (q - 1)) ≤ (2 : ℝ) ^ (-(σ * m)) →
      lqSum (ν.conv μ) q m ≤ (2 : ℝ) ^ (-((lqSpectrum μ q + ε) * m))

variable {κ : Type*} [Fintype κ]

def Proposition68 (r t p : κ → ℝ) (μ : Measure ℝ) : Prop :=
  ∀ q : ℝ, 1 < q → DifferentiableAt ℝ (lqSpectrum μ) q → lqSpectrum μ q < q - 1 →
    ∀ R : ℕ, 1 ≤ R →
      Tendsto (fun m : ℕ => Real.logb 2 (lqSum (stoppedMeasure r t p m) q (R * m)) / m) atTop
        (𝓝 (-lqSpectrum μ q))

theorem eventually_rpow_lt_two_rpow {B e σ : ℝ} (hB : 1 ≤ B) (hσ : 0 < σ) :
    ∀ᶠ m : ℕ in atTop, (B * m) ^ e < (2 : ℝ) ^ (σ * m) := by
  set k := ⌈e⌉₊
  have hr : (1 : ℝ) < 2 ^ σ := Real.one_lt_rpow (by norm_num) hσ
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt k hr
  have hBk : (0 : ℝ) < 1 / B ^ k := by positivity
  filter_upwards [hlim.eventually (gt_mem_nhds hBk), eventually_ge_atTop 1] with m hm hm1
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hBm : 1 ≤ B * m := one_le_mul_of_one_le_of_one_le hB hm'
  have hpow : (0 : ℝ) < (2 ^ σ) ^ m := by positivity
  rw [div_lt_iff₀ hpow] at hm
  calc (B * m) ^ e ≤ (B * m) ^ (k : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hBm (Nat.le_ceil e)
    _ = B ^ k * (m : ℝ) ^ k := by rw [Real.rpow_natCast, mul_pow]
    _ < B ^ k * (1 / B ^ k * (2 ^ σ) ^ m) :=
        mul_lt_mul_of_pos_left hm (by positivity)
    _ = (2 : ℝ) ^ (σ * m) := by
        rw [← mul_assoc, mul_one_div_cancel (by positivity), one_mul, ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num)]

theorem sum_omega_wordWeight {r p : κ → ℝ} (hr1 : ∀ j, |r j| < 1) (hp1 : ∑ j, p j = 1)
    {m : ℕ} (hm : 1 ≤ m) : ∑ u ∈ omega r m, wordWeight p u = 1 := by
  have h := sum_omega_eq hr1 (wordWeight p) (fun v => by
    simp_rw [wordWeight_append, ← Finset.mul_sum]
    simp [wordWeight, hp1]) hm
  simpa using h

theorem lqSum_stoppedMeasure_pos {r t p : κ → ℝ} (hr1 : ∀ j, |r j| < 1) (hp : ∀ j, 0 < p j)
    (hp1 : ∑ j, p j = 1) {m : ℕ} (hm : 1 ≤ m) {q : ℝ} (hq : 0 < q) (n : ℕ) :
    0 < lqSum (stoppedMeasure r t p m) q n := by
  classical
  unfold stoppedMeasure
  rw [lqSum_sum_dirac _ _ (fun u _ => (wordWeight_pos hp u).le) _ hq]
  have hne : (omega r m).Nonempty := by
    refine Finset.nonempty_of_sum_ne_zero (f := wordWeight p) ?_
    rw [sum_omega_wordWeight hr1 hp1 hm]
    norm_num
  refine Finset.sum_pos (fun k hk => Real.rpow_pos_of_pos ?_ _) (hne.image _)
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hk
  exact Finset.sum_pos (fun w _ => wordWeight_pos hp w) ⟨v, Finset.mem_filter.mpr ⟨hv, rfl⟩⟩

theorem sum_preimage_Ico_le (ν : Measure ℝ) [IsFiniteMeasure ν] {lam t₀ a h : ℝ}
    (hlam : lam ≠ 0) (hh0 : 0 < h) {n : ℕ} {C q : ℝ} (hq : 1 ≤ q)
    (hC : h / |lam| * 2 ^ n + (h / |lam| * 2 ^ n)⁻¹ + 2 ≤ C) (D' : Finset ℤ) {B : ℝ}
    (hB : ∀ Q : Finset ℤ, (Q.card : ℝ) ≤ C * D'.card →
      ∑ k ∈ Q, ν.real (dyadicIco n k) ^ q ≤ B) :
    ∑ i ∈ D', ν.real ((fun x => lam * x + t₀) ⁻¹' Set.Ico (a + i * h) (a + (i + 1) * h)) ^ q ≤
      C ^ q * B := by
  set ℓ := h / |lam|
  have habs : 0 < |lam| := abs_pos.mpr hlam
  have hℓ0 : 0 < ℓ := by positivity
  set y : ℤ → ℝ := fun j => (a + j * h - t₀) / lam + min 0 (h / lam)
  have hS : ∀ j ∈ D', (fun x => lam * x + t₀) ⁻¹' Set.Ico (a + j * h) (a + (j + 1) * h) ⊆
      Set.Icc (y j) (y j + ℓ) := by
    intro j _ x hx
    simp only [Set.mem_preimage, Set.mem_Ico] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [show a + ((j : ℝ) + 1) * h = a + j * h + h by ring] at hx2
    simp only [y, ℓ, Set.mem_Icc]
    rcases lt_or_gt_of_ne hlam with hneg | hpos
    · have hm0 : min 0 (h / lam) = h / lam := min_eq_right (div_nonpos_of_nonneg_of_nonpos
        hh0.le hneg.le)
      rw [hm0, abs_of_neg hneg]
      constructor
      · rw [← add_div, div_le_iff_of_neg hneg]; linarith
      · have e3 : (a + j * h - t₀) / lam + h / lam + h / -lam = (a + j * h - t₀) / lam := by
          rw [div_neg]; ring
        rw [e3, le_div_iff_of_neg hneg]; linarith
    · have hm0 : min 0 (h / lam) = 0 := min_eq_left (div_nonneg hh0.le hpos.le)
      rw [hm0, abs_of_pos hpos, add_zero]
      constructor
      · rw [div_le_iff₀ hpos]; linarith
      · rw [← add_div, le_div_iff₀ hpos]; linarith
  have hsep : ∀ i ∈ D', ∀ j ∈ D', i ≠ j → ℓ ≤ |y i - y j| := by
    intro i _ j _ hij
    have e : y i - y j = ((i : ℝ) - j) * h / lam := by simp only [y]; field_simp; ring
    rw [e, abs_div, abs_mul, abs_of_pos hh0]
    have hij' : (1 : ℝ) ≤ |(i : ℝ) - j| := by
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hlt
        rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
      · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast hgt
        rw [abs_of_pos (by linarith)]; linarith
    simp only [ℓ]
    rw [div_le_div_iff_of_pos_right habs]
    nlinarith
  obtain ⟨Q, hQ, hsum⟩ := sum_rpow_le_of_separated' ν D'
    (fun j => (fun x => lam * x + t₀) ⁻¹' Set.Ico (a + j * h) (a + (j + 1) * h)) y (m := n) hq
    hℓ0 hS hsep
  have hC0 : 0 ≤ ℓ * 2 ^ n + (ℓ * 2 ^ n)⁻¹ + 2 := by positivity
  have hB0 : 0 ≤ ∑ k ∈ Q, ν.real (dyadicIco n k) ^ q :=
    Finset.sum_nonneg fun k _ => Real.rpow_nonneg measureReal_nonneg _
  refine hsum.trans (mul_le_mul (Real.rpow_le_rpow hC0 hC (by linarith))
    (hB Q (hQ.trans (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _)))) hB0
    (Real.rpow_nonneg (hC0.trans hC) _))

theorem dyadicIco_eq_Ico (n : ℕ) (i : ℤ) :
    dyadicIco n i = Set.Ico (0 + (i : ℝ) * (1 / 2 ^ n)) (0 + ((i : ℝ) + 1) * (1 / 2 ^ n)) := by
  simp only [dyadicIco, zero_add]
  congr 1 <;> ring

noncomputable def atomicMeasure {ι : Type*} (s : Finset ι) (w y : ι → ℝ) : Measure ℝ :=
  ∑ i ∈ s, ENNReal.ofReal (w i) • Measure.dirac (y i)

instance isFiniteMeasure_sum_dirac {ι : Type*} (s : Finset ι) (w y : ι → ℝ) :
    IsFiniteMeasure (∑ i ∈ s, ENNReal.ofReal (w i) • Measure.dirac (y i)) :=
  ⟨by
    rw [Measure.finsetSum_apply]
    exact ENNReal.sum_lt_top.mpr fun i _ => by simp⟩

instance {ι : Type*} (s : Finset ι) (w y : ι → ℝ) : IsFiniteMeasure (atomicMeasure s w y) := by
  unfold atomicMeasure; infer_instance

theorem measureReal_atomicMeasure {ι : Type*} (s : Finset ι) {w : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (y : ι → ℝ) {E : Set ℝ} (hE : MeasurableSet E)
    [DecidablePred (· ∈ E)] :
    (atomicMeasure s w y).real E = ∑ i ∈ s with y i ∈ E, w i :=
  measureReal_sum_dirac s w hw y hE

theorem atomicMeasure_univ {ι : Type*} (s : Finset ι) {w : ι → ℝ} (hw : ∀ i ∈ s, 0 ≤ w i)
    (y : ι → ℝ) : (atomicMeasure s w y).real Set.univ = ∑ i ∈ s, w i := by
  classical
  rw [measureReal_atomicMeasure s hw y MeasurableSet.univ]
  simp

theorem measureReal_atomicMeasure_conv {ι : Type*} (s : Finset ι) {w : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (y : ι → ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] {E : Set ℝ}
    (hE : MeasurableSet E) :
    ((atomicMeasure s w y).conv μ).real E = ∑ i ∈ s, w i * μ.real ((fun x => y i + x) ⁻¹' E) := by
  classical
  have hconv : (atomicMeasure s w y).conv μ =
      ∑ i ∈ s, ENNReal.ofReal (w i) • μ.map (fun x => y i + x) := by
    unfold atomicMeasure
    induction s using Finset.induction_on with
    | empty => simp [Measure.zero_conv]
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, Measure.add_conv,
        Measure.conv_smul_left, Measure.dirac_conv,
        ih fun i hi => hw i (Finset.mem_insert_of_mem hi)]
  rw [hconv, measureReal_def, Measure.finsetSum_apply, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Measure.smul_apply, Measure.map_apply (by fun_prop) hE, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (hw i hi)]
    rfl
  · intro i _
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

instance {ι : Type*} (s : Finset ι) (w y : ι → ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IsFiniteMeasure ((atomicMeasure s w y).conv μ) := by
  unfold Measure.conv; infer_instance

theorem lqSum_atomicMeasure_conv_le {ι : Type*} (s : Finset ι) {w : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1) (y : ι → ℝ) (μ : Measure ℝ)
    [IsFiniteMeasure μ] {q : ℝ} (hq : 1 ≤ q) (n : ℕ) :
    lqSum ((atomicMeasure s w y).conv μ) q n ≤ 4 ^ q * lqSum μ q n := by
  unfold lqSum
  refine Real.tsum_le_of_sum_le (fun k => Real.rpow_nonneg measureReal_nonneg _) fun F => ?_
  have hJ : ∀ k, ((atomicMeasure s w y).conv μ).real (dyadicIco n k) ^ q ≤
      ∑ i ∈ s, w i * μ.real ((fun x => y i + x) ⁻¹' dyadicIco n k) ^ q := by
    intro k
    rw [measureReal_atomicMeasure_conv s hw y μ (measurableSet_dyadicIco n k)]
    exact Real.rpow_arith_mean_le_arith_mean_rpow s w _ hw hw1
      (fun i _ => measureReal_nonneg) hq
  have hi : ∀ i ∈ s, ∑ k ∈ F, μ.real ((fun x => y i + x) ⁻¹' dyadicIco n k) ^ q ≤
      4 ^ q * lqSum μ q n := by
    intro i _
    have e : ∀ k, (fun x => y i + x) ⁻¹' dyadicIco n k =
        (fun x => 1 * x + y i) ⁻¹' Set.Ico (0 + k * (1 / 2 ^ n)) (0 + (k + 1) * (1 / 2 ^ n)) := by
      intro k
      rw [← dyadicIco_eq_Ico]
      ext x; simp [add_comm]
    simp_rw [e]
    refine sum_preimage_Ico_le μ one_ne_zero (by positivity) hq ?_ F
      fun Q _ => sum_le_lqSum μ hq n Q
    rw [abs_one, div_one, one_div, inv_mul_cancel₀ (by positivity), inv_one]
    norm_num
  calc ∑ k ∈ F, ((atomicMeasure s w y).conv μ).real (dyadicIco n k) ^ q
      ≤ ∑ k ∈ F, ∑ i ∈ s, w i * μ.real ((fun x => y i + x) ⁻¹' dyadicIco n k) ^ q :=
        Finset.sum_le_sum fun k _ => hJ k
    _ = ∑ i ∈ s, w i * ∑ k ∈ F, μ.real ((fun x => y i + x) ⁻¹' dyadicIco n k) ^ q := by
        rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ s, w i * (4 ^ q * lqSum μ q n) :=
        Finset.sum_le_sum fun i hi' => mul_le_mul_of_nonneg_left (hi i hi') (hw i hi')
    _ = 4 ^ q * lqSum μ q n := by rw [← Finset.sum_mul, hw1, one_mul]

theorem lqSum_mono {ν ν' : Measure ℝ} [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (h : ∀ E, MeasurableSet E → ν.real E ≤ ν'.real E) {q : ℝ} (hq : 1 ≤ q) (n : ℕ) :
    lqSum ν q n ≤ lqSum ν' q n :=
  (summable_lq ν hq n).tsum_le_tsum (fun k => Real.rpow_le_rpow measureReal_nonneg
    (h _ (measurableSet_dyadicIco n k)) (by linarith)) (summable_lq ν' hq n)

theorem sum_rpow_le_rpow_sum {ι : Type*} (s : Finset ι) {a : ι → ℝ} (ha : ∀ i ∈ s, 0 ≤ a i)
    {q : ℝ} (hq : 1 ≤ q) : ∑ i ∈ s, a i ^ q ≤ (∑ i ∈ s, a i) ^ q := by
  set S := ∑ i ∈ s, a i
  have hS : 0 ≤ S := Finset.sum_nonneg ha
  calc ∑ i ∈ s, a i ^ q ≤ ∑ i ∈ s, a i * S ^ (q - 1) := Finset.sum_le_sum fun i hi => by
        rw [← rpow_sub_one_mul_self (ha i hi) hq, mul_comm]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (ha i hi)
          (Finset.single_le_sum ha hi) (by linarith)) (ha i hi)
    _ = S ^ (q - 1) * S := by rw [← Finset.sum_mul, mul_comm]
    _ = S ^ q := rpow_sub_one_mul_self hS hq

theorem sum_lqSum_le {ι : Type*} (s : Finset ι) (ν : ι → Measure ℝ)
    [∀ i, IsFiniteMeasure (ν i)] {q : ℝ} (hq : 1 ≤ q) (n : ℕ) :
    ∑ i ∈ s, lqSum (ν i) q n ≤ lqSum (∑ i ∈ s, ν i) q n := by
  unfold lqSum
  rw [← Summable.tsum_finsetSum fun i _ => summable_lq (ν i) hq n]
  refine (summable_sum fun i _ => summable_lq (ν i) hq n).tsum_le_tsum (fun k => ?_)
    (summable_lq _ hq n)
  have e : (∑ i ∈ s, ν i).real (dyadicIco n k) = ∑ i ∈ s, (ν i).real (dyadicIco n k) := by
    rw [measureReal_def, Measure.finsetSum_apply, ENNReal.toReal_sum fun i _ => measure_ne_top _ _]
    rfl
  rw [e]
  exact sum_rpow_le_rpow_sum s (fun i _ => measureReal_nonneg) hq

theorem lqSum_le_of_le (ν : Measure ℝ) [IsFiniteMeasure ν] {q : ℝ} (hq : 1 ≤ q) {n n' : ℕ}
    (hn : n ≤ n') : lqSum ν q n' ≤ lqSum ν q n := by
  classical
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  set g : ℤ → ℤ := fun k => k / (2 ^ d : ℕ)
  have hsub : ∀ k, dyadicIco (n + d) k ⊆ dyadicIco n (g k) := by
    intro k x hx
    rw [mem_dyadicIco_iff] at hx ⊢
    simp only [g]
    rw [← hx, ← Int.floor_div_natCast]
    congr 1
    push_cast
    rw [pow_add]
    field_simp
  refine Real.tsum_le_of_sum_le (fun k => Real.rpow_nonneg measureReal_nonneg _) fun F => ?_
  calc ∑ k ∈ F, ν.real (dyadicIco (n + d) k) ^ q
      = ∑ c ∈ F.image g, ∑ k ∈ F with g k = c, ν.real (dyadicIco (n + d) k) ^ q :=
        (Finset.sum_fiberwise_of_maps_to (fun k hk => Finset.mem_image_of_mem g hk) _).symm
    _ ≤ ∑ c ∈ F.image g, (∑ k ∈ F with g k = c, ν.real (dyadicIco (n + d) k)) ^ q :=
        Finset.sum_le_sum fun c _ => sum_rpow_le_rpow_sum _ (fun k _ => measureReal_nonneg) hq
    _ ≤ ∑ c ∈ F.image g, ν.real (dyadicIco n c) ^ q := by
        refine Finset.sum_le_sum fun c _ => Real.rpow_le_rpow
          (Finset.sum_nonneg fun k _ => measureReal_nonneg) ?_ (by linarith)
        rw [← measureReal_biUnion_finset (fun k _ l _ hkl => pairwise_disjoint_dyadicIco _ hkl)
          (fun k _ => measurableSet_dyadicIco _ _)]
        refine measureReal_mono (Set.iUnion₂_subset fun k hk => ?_) (measure_ne_top _ _)
        have := (Finset.mem_filter.mp hk).2
        rw [← this]
        exact hsub k
    _ ≤ lqSum ν q n := sum_le_lqSum ν hq n _

variable {r t p : κ → ℝ} {μ : Measure ℝ}

noncomputable def omegaRC (r t : κ → ℝ) (m : ℕ) (lam : ℝ) (k : ℤ) : Finset (List κ) :=
  open Classical in (omega r m).filter fun u => wordRatio r u = lam ∧ cell r t m u = k

noncomputable def massRC (r t p : κ → ℝ) (m : ℕ) (lam : ℝ) (k : ℤ) : ℝ :=
  ∑ u ∈ omegaRC r t m lam k, wordWeight p u

noncomputable def rhoRC (r t p : κ → ℝ) (m : ℕ) (lam : ℝ) (k : ℤ) : Measure ℝ :=
  atomicMeasure (omegaRC r t m lam k) (fun u => wordWeight p u / massRC r t p m lam k)
    (fun u => simWord r t u 0 / lam)

noncomputable def etaRC (r t p : κ → ℝ) (m : ℕ) (lam : ℝ) (k : ℤ) : Measure ℝ :=
  atomicMeasure (omegaRC r t m lam k) (wordWeight p) (fun u => simWord r t u 0)

instance (r t p : κ → ℝ) (m : ℕ) (lam : ℝ) (k : ℤ) : IsFiniteMeasure (etaRC r t p m lam k) := by
  unfold etaRC; infer_instance

instance (r t p : κ → ℝ) (m : ℕ) (lam : ℝ) (k : ℤ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IsFiniteMeasure ((rhoRC r t p m lam k).conv μ) := by
  unfold rhoRC; infer_instance

omit [Fintype κ] in

theorem massRC_nonneg (hp : ∀ j, 0 < p j) (m : ℕ) (lam : ℝ) (k : ℤ) :
    0 ≤ massRC r t p m lam k :=
  Finset.sum_nonneg fun u _ => (wordWeight_pos hp u).le

omit [Fintype κ] in

theorem massRC_pos (hp : ∀ j, 0 < p j) {m : ℕ} {lam : ℝ} {k : ℤ}
    (hne : (omegaRC r t m lam k).Nonempty) : 0 < massRC r t p m lam k :=
  Finset.sum_pos (fun u _ => wordWeight_pos hp u) hne

omit [Fintype κ] in

theorem rhoRC_isProbabilityMeasure (hp : ∀ j, 0 < p j) {m : ℕ} {lam : ℝ} {k : ℤ}
    (hne : (omegaRC r t m lam k).Nonempty) : IsProbabilityMeasure (rhoRC r t p m lam k) := by
  have hP := massRC_pos (r := r) (t := t) hp hne
  constructor
  have h := atomicMeasure_univ (omegaRC r t m lam k)
    (w := fun u => wordWeight p u / massRC r t p m lam k)
    (fun u _ => div_nonneg (wordWeight_pos hp u).le hP.le) (fun u => simWord r t u 0 / lam)
  rw [← Finset.sum_div, show (∑ i ∈ omegaRC r t m lam k, wordWeight p i) =
    massRC r t p m lam k from rfl, div_self hP.ne'] at h
  unfold rhoRC
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  change ENNReal.ofReal ((atomicMeasure _ _ _).real _) = 1
  rw [h, ENNReal.ofReal_one]

omit [Fintype κ] in

theorem massRC_mul_rhoRC_conv (hp : ∀ j, 0 < p j) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (m : ℕ) {lam : ℝ} (hlam : lam ≠ 0) (k : ℤ) {E : Set ℝ} (hE : MeasurableSet E) :
    massRC r t p m lam k * ((rhoRC r t p m lam k).conv μ).real ((fun x => lam * x) ⁻¹' E) =
      ∑ u ∈ omegaRC r t m lam k, wordWeight p u * μ.real (simWord r t u ⁻¹' E) := by
  classical
  rcases (omegaRC r t m lam k).eq_empty_or_nonempty with he | hne
  · simp [massRC, he]
  have hP := massRC_pos (r := r) (t := t) hp hne
  unfold rhoRC
  rw [measureReal_atomicMeasure_conv _ (fun u _ => div_nonneg (wordWeight_pos hp u).le hP.le) _ μ
    (hE.preimage (by fun_prop)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hlu : wordRatio r u = lam := (Finset.mem_filter.mp hu).2.1
  have hset : (fun x => simWord r t u 0 / lam + x) ⁻¹' ((fun x => lam * x) ⁻¹' E) =
      simWord r t u ⁻¹' E := by
    ext x
    simp only [Set.mem_preimage]
    rw [simWord_apply r t u x]
    change _ ↔ wordRatio r u * x + simWord r t u 0 ∈ E
    rw [hlu, mul_add, mul_div_cancel₀ _ hlam, add_comm]
  rw [hset]
  field_simp

theorem IsSelfSimilar.measureReal_eq_sum_RC (h : IsSelfSimilar r t p μ) {m : ℕ} (hm : 1 ≤ m)
    {E : Set ℝ} (hE : MeasurableSet E) :
    μ.real E = ∑ lam ∈ ratioSet r m, ∑ k ∈ (omega r m).image (cell r t m),
      ∑ u ∈ omegaRC r t m lam k, wordWeight p u * μ.real (simWord r t u ⁻¹' E) := by
  classical
  rw [h.measureReal_eq_sum hm hE]
  have hR : ratioSet r m = (omega r m).image (wordRatio r) := by unfold ratioSet; congr
  rw [hR, ← Finset.sum_fiberwise_of_maps_to (g := wordRatio r)
    (fun u hu => Finset.mem_image_of_mem _ hu)]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [← Finset.sum_fiberwise_of_maps_to (g := cell r t m) (t := (omega r m).image (cell r t m))
    (fun u hu => Finset.mem_image_of_mem _ (Finset.mem_filter.mp hu).1)]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold omegaRC
  rw [Finset.filter_filter]

theorem abs_lt_of_mem_ratioSet {r : κ → ℝ} (hr1 : ∀ j, |r j| < 1) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hρ : ∀ j, ρ₀ ≤ |r j|) {m : ℕ} {lam : ℝ} (hlam : lam ∈ ratioSet r m) :
    ρ₀ * (2 : ℝ) ^ (-(m : ℝ)) < |lam| ∧ |lam| ≤ (2 : ℝ) ^ (-(m : ℝ)) := by
  classical
  have hR : ratioSet r m = (omega r m).image (wordRatio r) := by unfold ratioSet; congr
  rw [hR, Finset.mem_image] at hlam
  obtain ⟨u, hu, rfl⟩ := hlam
  have hst := (mem_omega hr1).mp hu
  exact ⟨lt_abs_wordRatio_of_stopping hρ₀ hρ hst, hst.2.1⟩

theorem IsSelfSimilar.exists_lqSum_le_sum_rho (h : IsSelfSimilar r t p μ) {L : ℝ}
    (hL : μ (Set.Icc (-L) L)ᶜ = 0) {q : ℝ} (hq : 1 ≤ q) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 1 ≤ m → ∀ n : ℕ,
      lqSum μ q (m + n) ≤ K * ((ratioSet r m).card : ℝ) ^ (q - 1) *
        ∑ lam ∈ ratioSet r m, ∑ k ∈ (omega r m).image (cell r t m),
          massRC r t p m lam k ^ q * lqSum ((rhoRC r t p m lam k).conv μ) q n := by
  classical
  have := h.isProbabilityMeasure
  obtain ⟨ρ₀, hρ₀, hρ⟩ := exists_ratio_lower h.ratio_ne_zero
  set N : ℕ := 2 * ⌈L⌉₊ + 3
  set C₁ : ℝ := 1 / ρ₀ + 3
  refine ⟨(N : ℝ) ^ (q - 1) * C₁ ^ q, by positivity, fun m hm n => ?_⟩
  set Λ := ratioSet r m
  set img := (omega r m).image (cell r t m)
  set J : ℤ → Set ℝ := fun i => dyadicIco (m + n) i
  set Y : ℝ → ℤ → ℤ → ℝ := fun lam k i =>
    ∑ u ∈ omegaRC r t m lam k, wordWeight p u * μ.real (simWord r t u ⁻¹' J i)
  set X : ℝ → ℤ → ℤ → ℝ := fun lam k i =>
    ((rhoRC r t p m lam k).conv μ).real ((fun x => lam * x) ⁻¹' J i)
  have hY0 : ∀ lam k i, 0 ≤ Y lam k i := fun lam k i => Finset.sum_nonneg fun u _ =>
    mul_nonneg (wordWeight_pos h.weight_pos u).le measureReal_nonneg
  have hΛ0 : ∀ lam ∈ Λ, lam ≠ 0 := fun lam hlam => by
    have := (abs_lt_of_mem_ratioSet h.abs_ratio_lt_one hρ₀ hρ hlam).1
    exact abs_pos.mp (lt_of_le_of_lt (by positivity) this)
  have hYX : ∀ lam ∈ Λ, ∀ k i, Y lam k i = massRC r t p m lam k * X lam k i := fun lam hlam k i =>
    (massRC_mul_rhoRC_conv h.weight_pos μ m (hΛ0 lam hlam) k (measurableSet_dyadicIco _ _)).symm

  have hG : ∀ lam i, ((img.filter fun k => Y lam k i ≠ 0).card : ℝ) ≤ N := by
    intro lam i
    set c := ⌊(i : ℝ) / 2 ^ n⌋
    have hsub : (img.filter fun k => Y lam k i ≠ 0) ⊆
        Finset.Icc (c - ⌈L⌉₊ - 1) (c + ⌈L⌉₊ + 1) := by
      intro k hk
      obtain ⟨-, hyk⟩ := Finset.mem_filter.mp hk
      obtain ⟨u, hu, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hyk
      obtain ⟨hu', -, rfl⟩ := Finset.mem_filter.mp hu
      have hxu : μ.real (simWord r t u ⁻¹' J i) ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
      have hex : ∃ z ∈ Set.Icc (-L) L, simWord r t u z ∈ dyadicIco (m + n) i := by
        by_contra hno
        push Not at hno
        apply hxu
        rw [measureReal_def, ENNReal.toReal_eq_zero_iff]
        left
        exact measure_mono_null (fun z hz hzK => hno z hzK hz) hL
      obtain ⟨z, hz, hzi⟩ := hex
      rw [Finset.mem_Icc]
      exact cell_near h hu' hz hzi
    calc ((img.filter fun k => Y lam k i ≠ 0).card : ℝ)
        ≤ (Finset.Icc (c - ⌈L⌉₊ - 1) (c + ⌈L⌉₊ + 1)).card := by
          exact_mod_cast Finset.card_le_card hsub
      _ = N := by
          have : (Finset.Icc (c - ⌈L⌉₊ - 1) (c + ⌈L⌉₊ + 1)).card = N := by
            simp only [Int.card_Icc, N]; omega
          rw [this]

  have hscale : ∀ lam ∈ Λ, ∀ k, ∑ i ∈ dyadicCover L (m + n), X lam k i ^ q ≤
      C₁ ^ q * lqSum ((rhoRC r t p m lam k).conv μ) q n := by
    intro lam hlam k
    obtain ⟨hlo, hhi⟩ := abs_lt_of_mem_ratioSet h.abs_ratio_lt_one hρ₀ hρ hlam
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast] at hlo hhi
    have hl0 : 0 < |lam| := lt_of_le_of_lt (by positivity) hlo
    have e : ∀ i, (fun x => lam * x) ⁻¹' J i = (fun x => lam * x + 0) ⁻¹'
        Set.Ico (0 + (i : ℝ) * (1 / 2 ^ (m + n))) (0 + ((i : ℝ) + 1) * (1 / 2 ^ (m + n))) := by
      intro i; simp only [J, add_zero, ← dyadicIco_eq_Ico]
    simp only [X]
    simp_rw [e]
    refine sum_preimage_Ico_le _ (hΛ0 lam hlam) (by positivity) hq ?_ _
      fun Q _ => sum_le_lqSum _ hq n Q
    have e2 : 1 / 2 ^ (m + n) / |lam| * 2 ^ n = (2 ^ m)⁻¹ / |lam| := by
      rw [pow_add]; field_simp
    rw [e2]
    have h1 : (2 ^ m : ℝ)⁻¹ / |lam| ≤ 1 / ρ₀ := by
      rw [div_le_div_iff₀ hl0 hρ₀, one_mul]
      have := mul_lt_mul_of_pos_right hlo (show (0 : ℝ) < 2 ^ m by positivity)
      rw [mul_assoc, inv_mul_cancel₀ (by positivity), mul_one] at this
      rw [← div_eq_inv_mul, div_le_iff₀ (by positivity)] at *
      nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) m]
    have h2 : ((2 ^ m : ℝ)⁻¹ / |lam|)⁻¹ ≤ 1 := by
      rw [inv_div, div_le_one (by positivity)]
      calc |lam| ≤ (2 ^ m)⁻¹ := hhi
        _ = (2 ^ m : ℝ)⁻¹ := rfl
    simp only [C₁]
    linarith
  rw [lqSum_eq_sum_dyadicCover hL (by linarith : (0 : ℝ) < q) (m + n)]
  have hstep : ∀ i, μ.real (J i) ^ q ≤ (Λ.card : ℝ) ^ (q - 1) * ((N : ℝ) ^ (q - 1) *
      ∑ lam ∈ Λ, ∑ k ∈ img, massRC r t p m lam k ^ q * X lam k i ^ q) := by
    intro i
    rw [h.measureReal_eq_sum_RC hm (measurableSet_dyadicIco _ _)]
    change (∑ lam ∈ Λ, ∑ k ∈ img, Y lam k i) ^ q ≤ _
    have h1 := Real.rpow_sum_le_const_mul_sum_rpow Λ (fun lam => ∑ k ∈ img, Y lam k i) hq
    simp only [abs_of_nonneg (Finset.sum_nonneg fun k _ => hY0 _ k i)] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun lam hlam => ?_
    rw [← Finset.sum_filter_ne_zero]
    have h2 := Real.rpow_sum_le_const_mul_sum_rpow (img.filter fun k => Y lam k i ≠ 0)
      (fun k => Y lam k i) hq
    simp only [abs_of_nonneg (hY0 _ _ i)] at h2
    refine h2.trans (mul_le_mul (Real.rpow_le_rpow (Nat.cast_nonneg _) (hG lam i)
      (by linarith)) ?_ (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (hY0 _ k i) _)
      (by positivity))
    calc ∑ k ∈ img.filter (fun k => Y lam k i ≠ 0), Y lam k i ^ q
        ≤ ∑ k ∈ img, Y lam k i ^ q :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun k _ _ =>
            Real.rpow_nonneg (hY0 _ k i) _
      _ = ∑ k ∈ img, massRC r t p m lam k ^ q * X lam k i ^ q :=
          Finset.sum_congr rfl fun k _ => by
            rw [hYX lam hlam k i, Real.mul_rpow (massRC_nonneg h.weight_pos m lam k)
              measureReal_nonneg]
  calc ∑ i ∈ dyadicCover L (m + n), μ.real (dyadicIco (m + n) i) ^ q
      ≤ ∑ i ∈ dyadicCover L (m + n), (Λ.card : ℝ) ^ (q - 1) * ((N : ℝ) ^ (q - 1) *
          ∑ lam ∈ Λ, ∑ k ∈ img, massRC r t p m lam k ^ q * X lam k i ^ q) :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = (Λ.card : ℝ) ^ (q - 1) * ((N : ℝ) ^ (q - 1) * ∑ lam ∈ Λ, ∑ k ∈ img,
          massRC r t p m lam k ^ q * ∑ i ∈ dyadicCover L (m + n), X lam k i ^ q) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        congr 2
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun lam _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
    _ ≤ (Λ.card : ℝ) ^ (q - 1) * ((N : ℝ) ^ (q - 1) * ∑ lam ∈ Λ, ∑ k ∈ img,
          massRC r t p m lam k ^ q * (C₁ ^ q * lqSum ((rhoRC r t p m lam k).conv μ) q n)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Finset.sum_le_sum
          fun lam hlam => Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
            (hscale lam hlam k) (Real.rpow_nonneg (massRC_nonneg h.weight_pos m lam k) _))
          (by positivity)) (by positivity)
    _ = (N : ℝ) ^ (q - 1) * C₁ ^ q * (Λ.card : ℝ) ^ (q - 1) * ∑ lam ∈ Λ, ∑ k ∈ img,
          massRC r t p m lam k ^ q * lqSum ((rhoRC r t p m lam k).conv μ) q n := by
        simp_rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun lam _ => Finset.sum_congr rfl fun k _ => by ring

theorem IsSelfSimilar.exists_sum_rho_le_lqSum (h : IsSelfSimilar r t p μ) {q : ℝ} (hq : 1 ≤ q) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 1 ≤ m → ∀ n : ℕ, ∀ lam ∈ ratioSet r m,
      ∀ S ⊆ (omega r m).image (cell r t m),
      ∑ k ∈ S, massRC r t p m lam k ^ q * lqSum (rhoRC r t p m lam k) q n ≤
        K * lqSum (stoppedMeasure r t p m) q (m + n) := by
  classical
  obtain ⟨ρ₀, hρ₀, hρ⟩ := exists_ratio_lower h.ratio_ne_zero
  set C₃ : ℝ := 1 / ρ₀ + 3
  refine ⟨C₃ ^ q, by positivity, fun m hm n lam hlam S hS => ?_⟩
  obtain ⟨hlo, hhi⟩ := abs_lt_of_mem_ratioSet h.abs_ratio_lt_one hρ₀ hρ hlam
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast] at hlo hhi
  have hl0 : 0 < |lam| := lt_of_le_of_lt (by positivity) hlo
  have hlam0 : lam ≠ 0 := abs_pos.mp hl0

  have hpiece : ∀ k, massRC r t p m lam k ^ q * lqSum (rhoRC r t p m lam k) q n ≤
      C₃ ^ q * lqSum (etaRC r t p m lam k) q (m + n) := by
    intro k
    have hP0 : 0 ≤ massRC r t p m lam k := massRC_nonneg h.weight_pos m lam k
    have hmass : ∀ E, MeasurableSet E → massRC r t p m lam k * (rhoRC r t p m lam k).real E =
        (etaRC r t p m lam k).real ((fun x => lam⁻¹ * x + 0) ⁻¹' E) := by
      intro E hE
      rcases (omegaRC r t m lam k).eq_empty_or_nonempty with he | hne
      · simp [rhoRC, etaRC, atomicMeasure, he]
      have hP := massRC_pos (r := r) (t := t) h.weight_pos hne
      unfold rhoRC etaRC
      rw [measureReal_atomicMeasure _ (fun u _ => div_nonneg (wordWeight_pos h.weight_pos u).le
        hP.le) _ hE, measureReal_atomicMeasure _ (fun u _ => (wordWeight_pos h.weight_pos u).le)
        _ (hE.preimage (by fun_prop)), Finset.mul_sum]
      refine Finset.sum_congr ?_ fun u _ => by field_simp
      ext u
      simp only [Finset.mem_filter, Set.mem_preimage, add_zero]
      rw [div_eq_inv_mul]
    unfold lqSum
    rw [← tsum_mul_left]
    refine Real.tsum_le_of_sum_le (fun c => mul_nonneg (by positivity)
      (Real.rpow_nonneg measureReal_nonneg _)) fun F => ?_
    have e : ∀ c ∈ F, massRC r t p m lam k ^ q * (rhoRC r t p m lam k).real (dyadicIco n c) ^ q =
        (etaRC r t p m lam k).real ((fun x => lam⁻¹ * x + 0) ⁻¹'
          Set.Ico (0 + (c : ℝ) * (1 / 2 ^ n)) (0 + ((c : ℝ) + 1) * (1 / 2 ^ n))) ^ q := by
      intro c _
      rw [← Real.mul_rpow hP0 measureReal_nonneg, hmass _ (measurableSet_dyadicIco n c),
        dyadicIco_eq_Ico]
    rw [Finset.sum_congr rfl e]
    refine sum_preimage_Ico_le _ (inv_ne_zero hlam0) (by positivity) hq ?_ F
      fun Q _ => sum_le_lqSum _ hq (m + n) Q
    have e2 : 1 / 2 ^ n / |lam⁻¹| * 2 ^ (m + n) = |lam| * 2 ^ m := by
      rw [abs_inv, pow_add]; field_simp
    rw [e2]
    have h1 : |lam| * 2 ^ m ≤ 1 := by
      calc |lam| * 2 ^ m ≤ (2 ^ m)⁻¹ * 2 ^ m :=
            mul_le_mul_of_nonneg_right hhi (by positivity)
        _ = 1 := inv_mul_cancel₀ (by positivity)
    have h2 : (|lam| * 2 ^ m)⁻¹ ≤ 1 / ρ₀ := by
      rw [one_div]
      refine inv_anti₀ hρ₀ ?_
      have := mul_lt_mul_of_pos_right hlo (show (0 : ℝ) < 2 ^ m by positivity)
      rw [mul_assoc, inv_mul_cancel₀ (by positivity), mul_one] at this
      exact this.le
    simp only [C₃]
    linarith

  have hdisj : (↑S : Set ℤ).PairwiseDisjoint fun k => omegaRC r t m lam k := by
    intro k _ k' _ hkk'
    rw [Function.onFun, Finset.disjoint_left]
    intro u hu hu'
    exact hkk' ((Finset.mem_filter.mp hu).2.2.symm.trans (Finset.mem_filter.mp hu').2.2)
  have hle : ∀ E, MeasurableSet E → (∑ k ∈ S, etaRC r t p m lam k).real E ≤
      (stoppedMeasure r t p m).real E := by
    intro E hE
    rw [measureReal_def, Measure.finsetSum_apply, ENNReal.toReal_sum fun k _ => measure_ne_top _ _]
    change ∑ k ∈ S, (etaRC r t p m lam k).real E ≤ _
    unfold etaRC
    simp_rw [measureReal_atomicMeasure _ (fun u _ => (wordWeight_pos h.weight_pos u).le) _ hE]
    unfold stoppedMeasure
    rw [measureReal_sum_dirac _ _ (fun u _ => (wordWeight_pos h.weight_pos u).le) _ hE]
    rw [← Finset.sum_biUnion (by
      intro k hk k' hk' hkk'
      exact Finset.disjoint_filter_filter (hdisj hk hk' hkk'))]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun u _ _ =>
      (wordWeight_pos h.weight_pos u).le
    intro u hu
    simp only [Finset.mem_biUnion, Finset.mem_filter] at hu ⊢
    obtain ⟨k, -, hu, hE'⟩ := hu
    exact ⟨(Finset.mem_filter.mp hu).1, hE'⟩
  calc ∑ k ∈ S, massRC r t p m lam k ^ q * lqSum (rhoRC r t p m lam k) q n
      ≤ ∑ k ∈ S, C₃ ^ q * lqSum (etaRC r t p m lam k) q (m + n) :=
        Finset.sum_le_sum fun k _ => hpiece k
    _ = C₃ ^ q * ∑ k ∈ S, lqSum (etaRC r t p m lam k) q (m + n) := (Finset.mul_sum _ _ _).symm
    _ ≤ C₃ ^ q * lqSum (∑ k ∈ S, etaRC r t p m lam k) q (m + n) :=
        mul_le_mul_of_nonneg_left (sum_lqSum_le S _ hq _) (by positivity)
    _ ≤ C₃ ^ q * lqSum (stoppedMeasure r t p m) q (m + n) := by
        have : IsFiniteMeasure (stoppedMeasure r t p m) := by
          unfold stoppedMeasure; infer_instance
        exact mul_le_mul_of_nonneg_left (lqSum_mono hle hq _) (by positivity)

omit [Fintype κ] in

theorem atomicMeasure_compl_eq_zero {ι : Type*} (s : Finset ι) (w y : ι → ℝ) {E : Set ℝ}
    (hE : MeasurableSet E) (h : ∀ i ∈ s, y i ∈ E) : atomicMeasure s w y Eᶜ = 0 := by
  unfold atomicMeasure
  rw [Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hE.compl, smul_eq_mul]
  simp [h i hi]

omit [Fintype κ] in

theorem rhoRC_compl_eq_zero {m : ℕ} {lam : ℝ} (hlam : lam ≠ 0) (k : ℤ) :
    ∃ a : ℝ, rhoRC r t p m lam k (Set.Icc a (a + 1 / (2 ^ m * |lam|)))ᶜ = 0 := by
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hl0 : 0 < |lam| := abs_pos.mpr hlam
  refine ⟨min ((k : ℝ) / 2 ^ m / lam) (((k : ℝ) + 1) / 2 ^ m / lam), ?_⟩
  refine atomicMeasure_compl_eq_zero _ _ _ measurableSet_Icc fun u hu => ?_
  have hk := mem_dyadicIco_iff.mpr (Finset.mem_filter.mp hu).2.2
  simp only [dyadicIco, Set.mem_Ico] at hk
  have e : ((k : ℝ) + 1) / 2 ^ m / lam - (k : ℝ) / 2 ^ m / lam = 1 / (2 ^ m * lam) := by
    field_simp; ring
  rcases lt_or_gt_of_ne hlam with hneg | hpos
  · have h1 : ((k : ℝ) + 1) / 2 ^ m / lam < simWord r t u 0 / lam :=
      (div_lt_div_right_of_neg hneg).mpr hk.2
    have h2 : simWord r t u 0 / lam ≤ (k : ℝ) / 2 ^ m / lam :=
      div_le_div_of_nonpos_of_le hneg.le hk.1
    rw [min_eq_right (by linarith), abs_of_neg hneg]
    constructor
    · linarith
    · have : 1 / (2 ^ m * -lam) = -(1 / (2 ^ m * lam)) := by
        rw [mul_neg, div_neg]
      rw [this]; linarith
  · have h1 : (k : ℝ) / 2 ^ m / lam ≤ simWord r t u 0 / lam :=
      div_le_div_of_nonneg_right hk.1 hpos.le
    have h2 : simWord r t u 0 / lam < ((k : ℝ) + 1) / 2 ^ m / lam :=
      div_lt_div_of_pos_right hk.2 hpos
    rw [min_eq_left (by linarith), abs_of_pos hpos]
    constructor
    · linarith
    · linarith

theorem two_rpow_mul_two_rpow (a b : ℝ) : (2 : ℝ) ^ a * (2 : ℝ) ^ b = (2 : ℝ) ^ (a + b) :=
  (Real.rpow_add (by norm_num) a b).symm

omit [Fintype κ] in

theorem massRC_le_cellWeight (hp : ∀ j, 0 < p j) (m : ℕ) (lam : ℝ) (k : ℤ) :
    massRC r t p m lam k ≤ cellWeight r t p m k := by
  classical
  unfold massRC cellWeight omegaRC
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun u hu => ?_) fun u _ _ =>
    (wordWeight_pos hp u).le
  simp only [Finset.mem_filter] at hu ⊢
  exact ⟨hu.1, hu.2.2⟩

theorem nonempty_ratioSet {r : κ → ℝ} (hr1 : ∀ j, |r j| < 1) {p : κ → ℝ}
    (hp1 : ∑ j, p j = 1) {m : ℕ} (hm : 1 ≤ m) : (ratioSet r m).Nonempty := by
  classical
  have hne : (omega r m).Nonempty := by
    refine Finset.nonempty_of_sum_ne_zero (f := wordWeight p) ?_
    rw [sum_omega_wordWeight hr1 hp1 hm]
    norm_num
  unfold ratioSet
  convert hne.image (wordRatio r)

set_option maxHeartbeats 1000000 in

theorem IsSelfSimilar.eventually_le_lqSum_stoppedMeasure (h : IsSelfSimilar r t p μ) {q : ℝ}
    (hq : 1 < q) (hflat : Flattening μ q) {R₀ : ℕ} (hR₀ : 1 ≤ R₀) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ m : ℕ in atTop, (2 : ℝ) ^ (-((lqSpectrum μ q + 3 * σ) * m)) ≤
      lqSum (stoppedMeasure r t p m) q (m + R₀ * m) := by
  classical
  obtain ⟨L, hL0, hL⟩ := h.exists_support
  have := h.isProbabilityMeasure
  have hne : Nonempty κ := by
    by_contra hk
    rw [not_nonempty_iff] at hk
    have := h.weight_sum
    simp at this
  set τ := lqSpectrum μ q
  have hR₀' : (1 : ℝ) ≤ R₀ := by exact_mod_cast hR₀
  obtain ⟨ρ₀, hρ₀, hρ⟩ := exists_ratio_lower h.ratio_ne_zero
  set σf := σ / (R₀ * (q - 1))
  have hσf : 0 < σf := div_pos hσ (mul_pos (by linarith) (by linarith))
  obtain ⟨ε, hε, hfl⟩ := hflat σf hσf
  have hfl' := hfl (1 / ρ₀) (by positivity)
  set δ := min (ε * R₀ / (2 * (R₀ + 2))) (σ / (2 * R₀ + 1))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  obtain ⟨K, hK, hdec⟩ := h.exists_lqSum_le_sum_rho hL hq.le
  obtain ⟨K', hK', hlow⟩ := h.exists_sum_rho_le_lqSum hq.le
  obtain ⟨C₂, hC₂, h65⟩ := exists_lqSum_stoppedMeasure_le h hL hq.le
  obtain ⟨A, hA⟩ := card_ratioSet_le h.abs_ratio_lt_one
  set B : ℝ := 2 * A + 1
  have hB : 1 ≤ B := by have : (0 : ℝ) ≤ A := Nat.cast_nonneg A; simp only [B]; linarith
  set e := (Fintype.card κ : ℝ) * q

  have hRm : Tendsto (fun m : ℕ => R₀ * m) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun m hm => le_trans hm (Nat.le_mul_of_pos_left m hR₀)⟩
  have hNm : Tendsto (fun m : ℕ => m + R₀ * m) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun m hm => le_trans hm (Nat.le_add_right m _)⟩

  have ev1 : ∀ᶠ m : ℕ in atTop,
      (2 : ℝ) ^ (-((τ + δ) * ((m + R₀ * m : ℕ) : ℝ))) ≤ lqSum μ q (m + R₀ * m) := by
    have h1 := (tendsto_lqExponent h hq).eventually (gt_mem_nhds (show τ < τ + δ by linarith))
    filter_upwards [hNm.eventually h1, hNm.eventually (eventually_ge_atTop 1)] with m hm hm1
    have hN : (0 : ℝ) < ((m + R₀ * m : ℕ) : ℝ) := by exact_mod_cast hm1
    simp only [lqExponent] at hm
    rw [div_lt_iff₀ hN] at hm
    rw [← Real.le_logb_iff_rpow_le (by norm_num) (lqSum_pos hL0 hL hq.le _)]
    linarith
  have ev2 : ∀ᶠ m : ℕ in atTop,
      lqSum μ q (R₀ * m) ≤ (2 : ℝ) ^ (-((τ - δ) * ((R₀ * m : ℕ) : ℝ))) :=
    hRm.eventually (eventually_lqSum_le hL0 hL hq.le (show τ - δ < τ by linarith))
  have ev3 : ∀ᶠ m : ℕ in atTop, lqSum μ q m ≤ (2 : ℝ) ^ (-((τ - δ) * m)) :=
    eventually_lqSum_le hL0 hL hq.le (show τ - δ < τ by linarith)
  have ev4 := hRm.eventually hfl'
  have ev5 := eventually_rpow_lt_two_rpow (B := B) (e := e) hB
    (show 0 < ε * R₀ / 4 by positivity)
  have ev6 := eventually_le_two_rpow (2 * K * C₂) (show 0 < ε * R₀ / 4 by positivity)
  have ev7 := eventually_rpow_lt_two_rpow (B := B) (e := e) hB (show 0 < σ / 2 by positivity)
  have ev8 := eventually_le_two_rpow (2 * K * 4 ^ q * K') (show 0 < σ / 2 by positivity)
  filter_upwards [ev1, ev2, ev3, ev4, ev5, ev6, ev7, ev8, eventually_ge_atTop 1]
    with m h1 h2 h3 h4 h5 h6 h7 h8 hm
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcN : ((m + R₀ * m : ℕ) : ℝ) = m + R₀ * m := by push_cast; ring
  have hcn : ((R₀ * m : ℕ) : ℝ) = R₀ * m := by push_cast; ring
  rw [hcN] at h1
  rw [hcn] at h2 h4
  set n₀ := R₀ * m
  set Λ := ratioSet r m
  set img := (omega r m).image (cell r t m)
  set P : ℝ → ℤ → ℝ := fun lam k => massRC r t p m lam k
  have hP0 : ∀ lam k, 0 ≤ P lam k := fun lam k => massRC_nonneg h.weight_pos m lam k
  set V : ℝ → ℝ := fun lam => ∑ k ∈ img, P lam k ^ q * lqSum ((rhoRC r t p m lam k).conv μ) q n₀
  have hΛne : Λ.Nonempty := nonempty_ratioSet h.abs_ratio_lt_one h.weight_sum hm
  obtain ⟨lam, hlam, hmax⟩ := Λ.exists_max_image V hΛne
  obtain ⟨hlo, hhi⟩ := abs_lt_of_mem_ratioSet h.abs_ratio_lt_one hρ₀ hρ hlam
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast] at hlo hhi
  have hl0 : 0 < |lam| := lt_of_le_of_lt (by positivity) hlo
  have hlam0 : lam ≠ 0 := abs_pos.mp hl0
  set Λc : ℝ := (Λ.card : ℝ) with hΛc
  have hΛc0 : 0 < Λc := by rw [hΛc]; exact_mod_cast hΛne.card_pos

  have h63 : Λc ^ q ≤ (B * m) ^ e := by
    have i1 : Λc ≤ ((A * (m + 1) + 1 : ℕ) : ℝ) ^ Fintype.card κ := by
      rw [hΛc]; exact_mod_cast hA m
    have i2 : ((A * (m + 1) + 1 : ℕ) : ℝ) ≤ B * m := by
      push_cast
      have : (0 : ℝ) ≤ A := Nat.cast_nonneg A
      simp only [B]; nlinarith
    calc Λc ^ q ≤ (((A * (m + 1) + 1 : ℕ) : ℝ) ^ Fintype.card κ) ^ q :=
          Real.rpow_le_rpow hΛc0.le i1 (by linarith)
      _ ≤ ((B * m) ^ Fintype.card κ) ^ q :=
          Real.rpow_le_rpow (by positivity) (pow_le_pow_left₀ (Nat.cast_nonneg _) i2 _)
            (by linarith)
      _ = (B * m) ^ e := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]

  have hdec' : lqSum μ q (m + n₀) ≤ K * Λc ^ q * V lam := by
    refine (hdec m hm n₀).trans ?_
    have hsum : ∑ l ∈ Λ, V l ≤ Λc * V lam := by
      have := Finset.sum_le_card_nsmul Λ V (V lam) hmax
      rwa [nsmul_eq_mul] at this
    calc K * Λc ^ (q - 1) * ∑ l ∈ Λ, V l ≤ K * Λc ^ (q - 1) * (Λc * V lam) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = K * (Λc ^ (q - 1) * Λc) * V lam := by ring
      _ = K * Λc ^ q * V lam := by rw [rpow_sub_one_mul_self hΛc0.le hq.le]

  set S := img.filter fun k => (2 : ℝ) ^ (-(σ * m)) < lqSum (rhoRC r t p m lam k) q n₀
  set W := ∑ k ∈ img, P lam k ^ q
  set Z := ∑ k ∈ S, P lam k ^ q
  have hpiece_small : ∀ k ∈ img.filter (fun k => ¬ (2 : ℝ) ^ (-(σ * m)) <
      lqSum (rhoRC r t p m lam k) q n₀),
      P lam k ^ q * lqSum ((rhoRC r t p m lam k).conv μ) q n₀ ≤
        P lam k ^ q * (2 : ℝ) ^ (-((τ + ε) * (R₀ * m))) := by
    intro k hk
    have hk2 := not_lt.mp (Finset.mem_filter.mp hk).2
    rcases (omegaRC r t m lam k).eq_empty_or_nonempty with he | hne'
    · have : P lam k = 0 := by simp [P, massRC, he]
      rw [this, Real.zero_rpow (by linarith), zero_mul, zero_mul]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (hP0 _ _) _)
    have := rhoRC_isProbabilityMeasure (r := r) (t := t) h.weight_pos hne'
    obtain ⟨a, ha⟩ := rhoRC_compl_eq_zero (r := r) (t := t) (p := p) (m := m) hlam0 k
    refine h4 _ ⟨(omegaRC r t m lam k).image fun u => simWord r t u 0 / lam,
      atomicMeasure_compl_eq_zero _ _ _ (Finset.measurableSet _) fun u hu =>
        Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hu)⟩ ⟨a, measure_mono_null ?_ ha⟩ ?_
    · refine Set.compl_subset_compl.mpr (Set.Icc_subset_Icc le_rfl ?_)
      have : 1 / (2 ^ m * |lam|) ≤ 1 / ρ₀ := by
        rw [div_le_div_iff₀ (by positivity) hρ₀, one_mul, one_mul]
        have := mul_lt_mul_of_pos_left hlo (show (0 : ℝ) < 2 ^ m by positivity)
        rw [← mul_assoc, mul_comm ((2 : ℝ) ^ m) ρ₀, mul_assoc, mul_inv_cancel₀ (by positivity),
          mul_one] at this
        exact this.le
      linarith
    · calc lqSum (rhoRC r t p m lam k) q n₀ ^ (1 / (q - 1))
          ≤ ((2 : ℝ) ^ (-(σ * m))) ^ (1 / (q - 1)) :=
            Real.rpow_le_rpow (lqSum_nonneg _ _ _) hk2 (by have : 0 < q - 1 := by linarith
                                                           positivity)
        _ = (2 : ℝ) ^ (-(σf * (R₀ * m))) := by
            rw [← Real.rpow_mul (by norm_num)]
            congr 1
            simp only [σf]
            field_simp
  have hpiece_big : ∀ k ∈ S, P lam k ^ q * lqSum ((rhoRC r t p m lam k).conv μ) q n₀ ≤
      P lam k ^ q * (4 ^ q * lqSum μ q n₀) := by
    intro k hk
    have hk2 := (Finset.mem_filter.mp hk).2
    rcases (omegaRC r t m lam k).eq_empty_or_nonempty with he | hne'
    · exfalso
      have : lqSum (rhoRC r t p m lam k) q n₀ = 0 := by
        simp [rhoRC, atomicMeasure, he, lqSum, Real.zero_rpow (show q ≠ 0 by linarith)]
      rw [this] at hk2
      exact absurd hk2 (not_lt.mpr (by positivity))
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (hP0 _ _) _)
    have hP := massRC_pos (r := r) (t := t) (lam := lam) (k := k) h.weight_pos hne'
    unfold rhoRC
    refine lqSum_atomicMeasure_conv_le _ (fun u _ => div_nonneg (wordWeight_pos h.weight_pos u).le
      hP.le) ?_ _ μ hq.le n₀
    rw [← Finset.sum_div]
    exact div_self hP.ne'
  have hV : V lam ≤ (2 : ℝ) ^ (-((τ + ε) * (R₀ * m))) * W + 4 ^ q * lqSum μ q n₀ * Z := by
    simp only [V]
    rw [← Finset.sum_filter_add_sum_filter_not img
      (fun k => (2 : ℝ) ^ (-(σ * m)) < lqSum (rhoRC r t p m lam k) q n₀)]
    have hW : ∑ k ∈ img.filter (fun k => ¬ (2 : ℝ) ^ (-(σ * m)) <
        lqSum (rhoRC r t p m lam k) q n₀), P lam k ^ q ≤ W :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun k _ _ =>
        Real.rpow_nonneg (hP0 _ _) _
    calc ∑ k ∈ S, P lam k ^ q * lqSum ((rhoRC r t p m lam k).conv μ) q n₀ +
          ∑ k ∈ img.filter (fun k => ¬ (2 : ℝ) ^ (-(σ * m)) <
            lqSum (rhoRC r t p m lam k) q n₀),
            P lam k ^ q * lqSum ((rhoRC r t p m lam k).conv μ) q n₀
        ≤ ∑ k ∈ S, P lam k ^ q * (4 ^ q * lqSum μ q n₀) +
          ∑ k ∈ img.filter (fun k => ¬ (2 : ℝ) ^ (-(σ * m)) <
            lqSum (rhoRC r t p m lam k) q n₀),
            P lam k ^ q * (2 : ℝ) ^ (-((τ + ε) * (R₀ * m))) :=
          add_le_add (Finset.sum_le_sum hpiece_big) (Finset.sum_le_sum hpiece_small)
      _ = 4 ^ q * lqSum μ q n₀ * Z + (2 : ℝ) ^ (-((τ + ε) * (R₀ * m))) *
          ∑ k ∈ img.filter (fun k => ¬ (2 : ℝ) ^ (-(σ * m)) <
            lqSum (rhoRC r t p m lam k) q n₀), P lam k ^ q := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]; ring
      _ ≤ 4 ^ q * lqSum μ q n₀ * Z + (2 : ℝ) ^ (-((τ + ε) * (R₀ * m))) * W := by
          gcongr
      _ = _ := by ring

  have hW : W ≤ C₂ * lqSum μ q m := by
    refine le_trans ?_ (h65 m hm)
    rw [lqSum_stoppedMeasure_eq h.weight_pos (by linarith) m]
    exact Finset.sum_le_sum fun k _ => Real.rpow_le_rpow (hP0 _ _)
      (massRC_le_cellWeight h.weight_pos m lam k) (by linarith)

  have hZ : (2 : ℝ) ^ (-(σ * m)) * Z ≤ K' * lqSum (stoppedMeasure r t p m) q (m + n₀) := by
    refine le_trans ?_ (hlow m hm n₀ lam hlam S (Finset.filter_subset _ _))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hk).2.le
      (Real.rpow_nonneg (hP0 _ _) _)

  set s := lqSum (stoppedMeasure r t p m) q (m + n₀)
  set y2 := lqSum μ q n₀
  set y3 := lqSum μ q m
  have hy2 : 0 ≤ y2 := lqSum_nonneg _ _ _
  have hy3 : 0 ≤ y3 := lqSum_nonneg _ _ _
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun k _ => Real.rpow_nonneg (hP0 _ _) _
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun k _ => Real.rpow_nonneg (hP0 _ _) _
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hpoly0 : 0 ≤ (B * m) ^ e := by positivity
  have hδ1 : δ * (R₀ + 2) ≤ ε * R₀ / 2 := by
    have := min_le_left (ε * R₀ / (2 * (R₀ + 2))) (σ / (2 * R₀ + 1))
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hδ2 : δ * (2 * R₀ + 1) ≤ σ := by
    have := min_le_right (ε * R₀ / (2 * (R₀ + 2))) (σ / (2 * R₀ + 1))
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  set E1 := (2 : ℝ) ^ (-((τ + δ) * (m + R₀ * m)))

  have hA1 : K * Λc ^ q * ((2 : ℝ) ^ (-((τ + ε) * (R₀ * m))) * W) ≤ (1 / 2) * E1 := by
    calc K * Λc ^ q * ((2 : ℝ) ^ (-((τ + ε) * (R₀ * m))) * W)
        ≤ K * (B * m) ^ e * ((2 : ℝ) ^ (-((τ + ε) * (R₀ * m))) *
            (C₂ * (2 : ℝ) ^ (-((τ - δ) * m)))) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h63 hK.le)
            (mul_le_mul_of_nonneg_left (hW.trans (mul_le_mul_of_nonneg_left h3 hC₂.le))
              (by positivity)) (by positivity) (by positivity)
      _ = (1 / 2) * ((2 * K * C₂) * (B * m) ^ e) *
            ((2 : ℝ) ^ (-((τ + ε) * (R₀ * m))) * (2 : ℝ) ^ (-((τ - δ) * m))) := by ring
      _ ≤ (1 / 2) * ((2 : ℝ) ^ (ε * R₀ / 4 * m) * (2 : ℝ) ^ (ε * R₀ / 4 * m)) *
            ((2 : ℝ) ^ (-((τ + ε) * (R₀ * m))) * (2 : ℝ) ^ (-((τ - δ) * m))) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_mul h6 h5.le hpoly0 (by positivity)) (by norm_num)) (by positivity)
      _ = (1 / 2) * (2 : ℝ) ^ (ε * R₀ / 4 * m + ε * R₀ / 4 * m +
            (-((τ + ε) * (R₀ * m)) + -((τ - δ) * m))) := by
          simp only [two_rpow_mul_two_rpow, mul_assoc]
      _ ≤ (1 / 2) * E1 := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
            (by norm_num)
          nlinarith [mul_le_mul_of_nonneg_right hδ1 hm0]

  have hB1 : (1 / 2) * E1 ≤ K * (B * m) ^ e * 4 ^ q * (2 : ℝ) ^ (-((τ - δ) * (R₀ * m))) * Z := by
    have hchain : E1 ≤ K * Λc ^ q * ((2 : ℝ) ^ (-((τ + ε) * (R₀ * m))) * W) +
        K * Λc ^ q * (4 ^ q * y2 * Z) := by
      rw [← mul_add]
      exact h1.trans (hdec'.trans (mul_le_mul_of_nonneg_left hV (by positivity)))
    have h4' : K * Λc ^ q * (4 ^ q * y2 * Z) ≤
        K * (B * m) ^ e * 4 ^ q * (2 : ℝ) ^ (-((τ - δ) * (R₀ * m))) * Z := by
      calc K * Λc ^ q * (4 ^ q * y2 * Z) ≤ K * (B * m) ^ e * (4 ^ q *
            (2 : ℝ) ^ (-((τ - δ) * (R₀ * m))) * Z) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h63 hK.le) (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h2 (by positivity)) hZ0) (by positivity)
              (by positivity)
        _ = _ := by ring
    linarith

  have hC1 : Z ≤ K' * s * (2 : ℝ) ^ (σ * m) := by
    have e1 : (2 : ℝ) ^ (σ * m) * (2 : ℝ) ^ (-(σ * m)) = 1 := by
      rw [← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero]
    calc Z = (2 : ℝ) ^ (σ * m) * ((2 : ℝ) ^ (-(σ * m)) * Z) := by
          rw [← mul_assoc, e1, one_mul]
      _ ≤ (2 : ℝ) ^ (σ * m) * (K' * s) := mul_le_mul_of_nonneg_left hZ (by positivity)
      _ = K' * s * (2 : ℝ) ^ (σ * m) := by ring
  have hE1 : E1 ≤ (2 : ℝ) ^ (2 * σ * m + -((τ - δ) * (R₀ * m))) * s := by
    have hs0 : 0 ≤ s := lqSum_nonneg _ _ _
    calc E1 = 2 * ((1 / 2) * E1) := by ring
      _ ≤ 2 * (K * (B * m) ^ e * 4 ^ q * (2 : ℝ) ^ (-((τ - δ) * (R₀ * m))) *
            (K' * s * (2 : ℝ) ^ (σ * m))) :=
          mul_le_mul_of_nonneg_left (hB1.trans (mul_le_mul_of_nonneg_left hC1 (by positivity)))
            (by norm_num)
      _ = ((2 * K * 4 ^ q * K') * (B * m) ^ e) *
            ((2 : ℝ) ^ (σ * m) * (2 : ℝ) ^ (-((τ - δ) * (R₀ * m)))) * s := by ring
      _ ≤ ((2 : ℝ) ^ (σ / 2 * m) * (2 : ℝ) ^ (σ / 2 * m)) *
            ((2 : ℝ) ^ (σ * m) * (2 : ℝ) ^ (-((τ - δ) * (R₀ * m)))) * s := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul h8 h7.le hpoly0 (by positivity)) (by positivity)) hs0
      _ = (2 : ℝ) ^ (2 * σ * m + -((τ - δ) * (R₀ * m))) * s := by
          simp only [two_rpow_mul_two_rpow]
          congr 2
          ring

  have e2 : (2 : ℝ) ^ (-((τ + δ) * (m + R₀ * m)) - (2 * σ * m + -((τ - δ) * (R₀ * m)))) *
      (2 : ℝ) ^ (2 * σ * m + -((τ - δ) * (R₀ * m))) = E1 := by
    show _ = (2 : ℝ) ^ (-((τ + δ) * (m + R₀ * m)))
    rw [two_rpow_mul_two_rpow]
    congr 1
    ring
  calc (2 : ℝ) ^ (-((τ + 3 * σ) * m))
      ≤ (2 : ℝ) ^ (-((τ + δ) * (m + R₀ * m)) - (2 * σ * m + -((τ - δ) * (R₀ * m)))) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        nlinarith [mul_le_mul_of_nonneg_right hδ2 hm0]
    _ ≤ s := by
        rw [← mul_le_mul_iff_left₀ (show (0 : ℝ) < (2 : ℝ) ^ (2 * σ * m +
          -((τ - δ) * (R₀ * m))) by positivity), e2]
        linarith [mul_comm s ((2 : ℝ) ^ (2 * σ * m + -((τ - δ) * (R₀ * m))))]

instance (r t p : κ → ℝ) (m : ℕ) : IsFiniteMeasure (stoppedMeasure r t p m) := by
  unfold stoppedMeasure; infer_instance

theorem proposition68_of_flattening (h : IsSelfSimilar r t p μ)
    (hflat : ∀ q, 1 < q → DifferentiableAt ℝ (lqSpectrum μ) q → lqSpectrum μ q < q - 1 →
      Flattening μ q) :
    Proposition68 r t p μ := by
  intro q hq hd hτq R hR
  obtain ⟨L, hL0, hL⟩ := h.exists_support
  have := h.isProbabilityMeasure
  obtain ⟨C₂, hC₂, h65⟩ := exists_lqSum_stoppedMeasure_le h hL hq.le
  set τ := lqSpectrum μ q
  rw [tendsto_order]
  constructor
  · intro a ha
    set σ := (-τ - a) / 4
    have hσ : 0 < σ := by simp only [σ]; linarith
    filter_upwards [h.eventually_le_lqSum_stoppedMeasure hq (hflat q hq hd hτq) hR hσ,
      eventually_ge_atTop 1] with m hm hm1
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm1
    have hS := lqSum_stoppedMeasure_pos (t := t) h.abs_ratio_lt_one h.weight_pos h.weight_sum
      hm1 (by linarith : (0 : ℝ) < q) (R * m)
    have h1 : lqSum (stoppedMeasure r t p m) q (m + R * m) ≤
        lqSum (stoppedMeasure r t p m) q (R * m) := lqSum_le_of_le _ hq.le (by omega)
    have h2 := (Real.le_logb_iff_rpow_le (b := 2) (by norm_num) hS).mpr (hm.trans h1)
    rw [lt_div_iff₀ hm']
    have ha' : a = -τ - 4 * σ := by simp only [σ]; ring
    have hτ' : lqSpectrum μ q = τ := rfl
    rw [hτ'] at h2
    rw [ha']
    nlinarith [mul_pos hσ hm']
  · intro a ha
    set σ := (a + τ) / 4
    have hσ : 0 < σ := by simp only [σ]; linarith
    filter_upwards [eventually_lqSum_le hL0 hL hq.le (show τ - σ < τ by linarith),
      eventually_le_two_rpow C₂ hσ, eventually_ge_atTop 1] with m hm hC hm1
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm1
    have hS := lqSum_stoppedMeasure_pos (t := t) h.abs_ratio_lt_one h.weight_pos h.weight_sum
      hm1 (by linarith : (0 : ℝ) < q) (R * m)
    have h1 : lqSum (stoppedMeasure r t p m) q (R * m) ≤ (2 : ℝ) ^ (-((τ - 2 * σ) * m)) := by
      calc lqSum (stoppedMeasure r t p m) q (R * m) ≤ lqSum (stoppedMeasure r t p m) q m :=
            lqSum_le_of_le _ hq.le (Nat.le_mul_of_pos_left m hR)
        _ ≤ C₂ * lqSum μ q m := h65 m hm1
        _ ≤ (2 : ℝ) ^ (σ * m) * (2 : ℝ) ^ (-((τ - σ) * m)) :=
            mul_le_mul hC hm (lqSum_nonneg _ _ _) (by positivity)
        _ = (2 : ℝ) ^ (-((τ - 2 * σ) * m)) := by
            rw [two_rpow_mul_two_rpow]; congr 1; ring
    have h2 := (Real.logb_le_iff_le_rpow (b := 2) (by norm_num) hS).mpr h1
    rw [div_lt_iff₀ hm']
    have ha' : a = -τ + 4 * σ := by simp only [σ]; ring
    rw [ha']
    nlinarith [mul_pos hσ hm']

end Lq

end FractalGeometry
