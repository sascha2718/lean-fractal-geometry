import Mathlib
import FractalGeometry.Entropy.Lq.Basic
import FractalGeometry.Entropy.Lq.Section4
import FractalGeometry.Entropy.Lq.Statement
import FractalGeometry.Pressure.Rectangular.LyapunovStatement
import FractalGeometry.SelfSimilar.SimilarityWords

open MeasureTheory Filter Topology Set

namespace FractalGeometry

namespace Lq

def subIco (a : ℝ) (n j : ℕ) : Set ℝ := Set.Ico (a + j / 2 ^ n) (a + (j + 1) / 2 ^ n)

def doubleIco (a : ℝ) (s : ℕ) : Set ℝ := Set.Ico (a - 1 / 2 ^ (s + 1)) (a + 3 / 2 ^ (s + 1))

def Proposition413 (μ : Measure ℝ) (q : ℝ) : Prop :=
  (∀ κ : ℝ, 0 < κ → ∃ η : ℝ, 0 < η ∧ ∀ᶠ m : ℕ in atTop, ∀ (s : ℕ) (a : ℝ) (D' : Finset ℕ),
      (∀ j ∈ D', j < 2 ^ m) → (D'.card : ℝ) ≤ (2 : ℝ) ^ ((legendre μ q - κ) * m) →
      ∑ j ∈ D', μ.real (subIco a (s + m) j) ^ q ≤
        (2 : ℝ) ^ (-((lqSpectrum μ q + η) * m)) * μ.real (doubleIco a s) ^ q) ∧
  (∀ δ : ℝ, 0 < δ → ∀ᶠ m : ℕ in atTop, ∀ (s : ℕ) (a : ℝ),
      ∑ j ∈ Finset.range (2 ^ m), μ.real (subIco a (s + m) j) ^ q ≤
        (2 : ℝ) ^ (-((lqSpectrum μ q - δ) * m)) * μ.real (doubleIco a s) ^ q)

theorem rpow_sum_mul_le {ι : Type*} (s : Finset ι) (w x : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hx : ∀ i ∈ s, 0 ≤ x i) {q : ℝ} (hq : 1 ≤ q) :
    (∑ i ∈ s, w i * x i) ^ q ≤ (∑ i ∈ s, w i) ^ (q - 1) * ∑ i ∈ s, w i * x i ^ q := by
  set W := ∑ i ∈ s, w i
  have hW : 0 ≤ W := Finset.sum_nonneg hw
  rcases hW.lt_or_eq with hW | hW
  · have h := Real.rpow_arith_mean_le_arith_mean_rpow s (fun i => w i / W) x
      (fun i hi => div_nonneg (hw i hi) hW.le) (by rw [← Finset.sum_div, div_self hW.ne'])
      hx hq
    simp only [div_mul_eq_mul_div, ← Finset.sum_div] at h
    rw [Real.div_rpow (Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (hx i hi)) hW.le,
      div_le_div_iff₀ (Real.rpow_pos_of_pos hW _) hW] at h
    have e : W ^ q = W ^ (q - 1) * W := by
      rw [← Real.rpow_add_one hW.ne']; ring_nf
    rw [e] at h
    nlinarith [Real.rpow_pos_of_pos hW (q - 1)]
  · have hw0 : ∀ i ∈ s, w i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hw).mp hW.symm
    have h1 : ∑ i ∈ s, w i * x i = 0 := Finset.sum_eq_zero fun i hi => by rw [hw0 i hi, zero_mul]
    have h2 : ∑ i ∈ s, w i * x i ^ q = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hw0 i hi, zero_mul]
    rw [h1, h2, Real.zero_rpow (by linarith), mul_zero]

theorem rpow_sub_one_mul_self {P q : ℝ} (hP : 0 ≤ P) (hq : 1 ≤ q) : P ^ (q - 1) * P = P ^ q := by
  rcases hP.lt_or_eq with hP | rfl
  · rw [← Real.rpow_add_one hP.ne']; ring_nf
  · rw [mul_zero, Real.zero_rpow (by linarith)]

variable {κ : Type*} [Fintype κ] {r t p : κ → ℝ} {μ : Measure ℝ}

theorem exists_ratio_lower {r : κ → ℝ} (hr : ∀ j, r j ≠ 0) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ j, ρ₀ ≤ |r j| := by
  cases isEmpty_or_nonempty κ with
  | inl h => exact ⟨1, one_pos, fun j => (IsEmpty.false j).elim⟩
  | inr h =>
    obtain ⟨j₀, -, hj₀⟩ := Finset.exists_min_image Finset.univ (fun j => |r j|)
      Finset.univ_nonempty
    exact ⟨|r j₀|, abs_pos.mpr (hr j₀), fun j => hj₀ j (Finset.mem_univ j)⟩

omit [Fintype κ] in

theorem lt_abs_wordRatio_of_stopping {r : κ → ℝ} {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hρ : ∀ j, ρ₀ ≤ |r j|) {n : ℕ} {u : List κ} (hu : ShmerkinStopping r n u) :
    ρ₀ * (2 : ℝ) ^ (-(n : ℝ)) < |wordRatio r u| := by
  have h := List.dropLast_append_getLast hu.1
  have h2 : (2 : ℝ) ^ (-(n : ℝ)) < |wordRatio r u.dropLast| := hu.2.2
  rw [← h, wordRatio_append, abs_mul]
  simp only [wordRatio, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  change ρ₀ * (2 : ℝ) ^ (-(n : ℝ)) < |wordRatio r u.dropLast| * |r (u.getLast hu.1)|
  calc ρ₀ * (2 : ℝ) ^ (-(n : ℝ)) < ρ₀ * |wordRatio r u.dropLast| :=
        mul_lt_mul_of_pos_left h2 hρ₀
    _ = |wordRatio r u.dropLast| * ρ₀ := mul_comm _ _
    _ ≤ |wordRatio r u.dropLast| * |r (u.getLast hu.1)| :=
        mul_le_mul_of_nonneg_left (hρ _) (abs_nonneg _)

theorem IsSelfSimilar.measureReal_eq_sum (h : IsSelfSimilar r t p μ) {n : ℕ} (hn : 1 ≤ n)
    {E : Set ℝ} (hE : MeasurableSet E) :
    μ.real E = ∑ u ∈ omega r n, wordWeight p u * μ.real (simWord r t u ⁻¹' E) := by
  have := h.isProbabilityMeasure
  conv_lhs => rw [h.eq_sum_omega hn]
  rw [measureReal_def, Measure.finsetSum_apply, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [Measure.smul_apply, Measure.map_apply (measurable_simWord r t u) hE, smul_eq_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (wordWeight_pos h.weight_pos u).le]
    rfl
  · intro u _
    rw [Measure.smul_apply, Measure.map_apply (measurable_simWord r t u) hE, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

omit [Fintype κ] in

theorem sum_preimage_subIco_le (ν : Measure ℝ) [IsFiniteMeasure ν] {lam t₀ : ℝ} (hlam : lam ≠ 0)
    {s m : ℕ} {C q : ℝ} (hq : 1 ≤ q) (hlo : 1 / 2 ^ m ≤ (1 / 2 ^ (s + m)) / |lam|)
    (hhi : (1 / 2 ^ (s + m)) / |lam| * 2 ^ m + 2 ≤ C) (a : ℝ) (D' : Finset ℕ) {B : ℝ}
    (hB : ∀ Q : Finset ℤ, (Q.card : ℝ) ≤ C * D'.card →
      ∑ k ∈ Q, ν.real (dyadicIco m k) ^ q ≤ B) :
    ∑ j ∈ D', ν.real ((fun x => lam * x + t₀) ⁻¹' subIco a (s + m) j) ^ q ≤ C ^ q * B := by
  set h := 1 / (2 : ℝ) ^ (s + m) with hh
  have hh0 : 0 < h := by positivity
  set ℓ := h / |lam|
  have habs : 0 < |lam| := abs_pos.mpr hlam
  set y : ℕ → ℝ := fun j => (a + j * h - t₀) / lam + min 0 (h / lam)
  have hS : ∀ j ∈ D', (fun x => lam * x + t₀) ⁻¹' subIco a (s + m) j ⊆
      Set.Icc (y j) (y j + ℓ) := by
    intro j _ x hx
    simp only [Set.mem_preimage, subIco, Set.mem_Ico] at hx
    have e1 : a + (j : ℝ) / 2 ^ (s + m) = a + j * h := by rw [hh]; ring
    have e2 : a + ((j : ℝ) + 1) / 2 ^ (s + m) = a + j * h + h := by rw [hh]; ring
    rw [e1, e2] at hx
    obtain ⟨hx1, hx2⟩ := hx
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
  obtain ⟨Q, hQ, hsum⟩ := sum_rpow_le_of_separated ν D'
    (fun j => (fun x => lam * x + t₀) ⁻¹' subIco a (s + m) j) y hq hlo hS hsep
  have hC0 : 0 ≤ ℓ * 2 ^ m + 2 := by positivity
  have hB0 : 0 ≤ ∑ k ∈ Q, ν.real (dyadicIco m k) ^ q :=
    Finset.sum_nonneg fun k _ => Real.rpow_nonneg measureReal_nonneg _
  calc ∑ j ∈ D', ν.real ((fun x => lam * x + t₀) ⁻¹' subIco a (s + m) j) ^ q
      ≤ (ℓ * 2 ^ m + 2) ^ q * ∑ k ∈ Q, ν.real (dyadicIco m k) ^ q := hsum
    _ ≤ C ^ q * B := by
        refine mul_le_mul (Real.rpow_le_rpow hC0 hhi (by linarith))
          (hB Q (hQ.trans (mul_le_mul_of_nonneg_right hhi (Nat.cast_nonneg _)))) hB0
          (Real.rpow_nonneg (hC0.trans hhi) _)

omit [Fintype κ] in

theorem sum_preimage_dyadicIco_le (ν : Measure ℝ) [IsFiniteMeasure ν] {lam t₀ : ℝ}
    (hlam : lam ≠ 0) {s m : ℕ} {C q : ℝ} (hq : 1 ≤ q)
    (hlo : 1 / 2 ^ m ≤ (1 / 2 ^ (s + m)) / |lam|)
    (hhi : (1 / 2 ^ (s + m)) / |lam| * 2 ^ m + 2 ≤ C) (D' : Finset ℤ) {B : ℝ}
    (hB : ∀ Q : Finset ℤ, (Q.card : ℝ) ≤ C * D'.card →
      ∑ k ∈ Q, ν.real (dyadicIco m k) ^ q ≤ B) :
    ∑ i ∈ D', ν.real ((fun x => lam * x + t₀) ⁻¹' dyadicIco (s + m) i) ^ q ≤ C ^ q * B := by
  set h := 1 / (2 : ℝ) ^ (s + m) with hh
  have hh0 : 0 < h := by positivity
  set ℓ := h / |lam|
  have habs : 0 < |lam| := abs_pos.mpr hlam
  set y : ℤ → ℝ := fun j => (j * h - t₀) / lam + min 0 (h / lam)
  have hS : ∀ j ∈ D', (fun x => lam * x + t₀) ⁻¹' dyadicIco (s + m) j ⊆
      Set.Icc (y j) (y j + ℓ) := by
    intro j _ x hx
    simp only [Set.mem_preimage, dyadicIco, Set.mem_Ico] at hx
    have e1 : (j : ℝ) / 2 ^ (s + m) = j * h := by rw [hh]; ring
    have e2 : ((j : ℝ) + 1) / 2 ^ (s + m) = j * h + h := by rw [hh]; ring
    rw [e1, e2] at hx
    obtain ⟨hx1, hx2⟩ := hx
    simp only [y, ℓ, Set.mem_Icc]
    rcases lt_or_gt_of_ne hlam with hneg | hpos
    · have hm0 : min 0 (h / lam) = h / lam := min_eq_right (div_nonpos_of_nonneg_of_nonpos
        hh0.le hneg.le)
      rw [hm0, abs_of_neg hneg]
      constructor
      · rw [← add_div, div_le_iff_of_neg hneg]; linarith
      · have e3 : (j * h - t₀) / lam + h / lam + h / -lam = (j * h - t₀) / lam := by
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
  obtain ⟨Q, hQ, hsum⟩ := sum_rpow_le_of_separated ν D'
    (fun j => (fun x => lam * x + t₀) ⁻¹' dyadicIco (s + m) j) y hq hlo hS hsep
  have hC0 : 0 ≤ ℓ * 2 ^ m + 2 := by positivity
  have hB0 : 0 ≤ ∑ k ∈ Q, ν.real (dyadicIco m k) ^ q :=
    Finset.sum_nonneg fun k _ => Real.rpow_nonneg measureReal_nonneg _
  calc ∑ j ∈ D', ν.real ((fun x => lam * x + t₀) ⁻¹' dyadicIco (s + m) j) ^ q
      ≤ (ℓ * 2 ^ m + 2) ^ q * ∑ k ∈ Q, ν.real (dyadicIco m k) ^ q := hsum
    _ ≤ C ^ q * B := by
        refine mul_le_mul (Real.rpow_le_rpow hC0 hhi (by linarith))
          (hB Q (hQ.trans (mul_le_mul_of_nonneg_right hhi (Nat.cast_nonneg _)))) hB0
          (Real.rpow_nonneg (hC0.trans hhi) _)

theorem IsSelfSimilar.exists_local_bound (h : IsSelfSimilar r t p μ) {L : ℝ}
    (hL : μ (Set.Icc (-L) L)ᶜ = 0) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ q : ℝ, 1 ≤ q → ∀ (s m : ℕ) (a : ℝ) (D' : Finset ℕ),
      (∀ j ∈ D', j < 2 ^ m) → ∀ B : ℝ,
      (∀ Q : Finset ℤ, (Q.card : ℝ) ≤ C₀ * D'.card →
        ∑ k ∈ Q, μ.real (dyadicIco m k) ^ q ≤ B) →
      ∑ j ∈ D', μ.real (subIco a (s + m) j) ^ q ≤ C₀ ^ q * B * μ.real (doubleIco a s) ^ q := by
  classical
  have := h.isProbabilityMeasure
  obtain ⟨ρ₀, hρ₀, hρ⟩ := exists_ratio_lower h.ratio_ne_zero
  obtain ⟨c₁, hc₁⟩ := pow_unbounded_of_one_lt (4 * L) (by norm_num : (1 : ℝ) < 2)
  set c := c₁ + 1
  have hc : 4 * L < 2 ^ c := lt_of_lt_of_le hc₁ (pow_le_pow_right₀ (by norm_num) (by omega))
  have hC1 : (1 : ℝ) ≤ 2 ^ c / ρ₀ + 2 := by
    have : 0 ≤ (2 : ℝ) ^ c / ρ₀ := by positivity
    linarith
  refine ⟨2 ^ c / ρ₀ + 2, hC1, ?_⟩
  intro q hq s m a D' hD' B hB
  set n := s + c
  have hn : 1 ≤ n := by omega
  set K := Set.Icc (-L) L
  set I := Set.Ico a (a + 1 / 2 ^ s)
  set U := (omega r n).filter fun u => ∃ x ∈ K, simWord r t u x ∈ I
  have hB0 : 0 ≤ B := le_trans (by simp)
    (hB ∅ (by simp only [Finset.card_empty, Nat.cast_zero]; positivity))
  have hsub : ∀ j ∈ D', subIco a (s + m) j ⊆ I := by
    intro j hj x hx
    simp only [subIco, Set.mem_Ico] at hx
    simp only [I, Set.mem_Ico]
    have hj' : (j : ℝ) + 1 ≤ 2 ^ m := by exact_mod_cast hD' j hj
    have e : ((j : ℝ) + 1) / 2 ^ (s + m) ≤ 1 / 2 ^ s := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), pow_add]; nlinarith [pow_pos
        (by norm_num : (0 : ℝ) < 2) s]
    exact ⟨le_trans (le_add_of_nonneg_right (by positivity)) hx.1, by linarith [hx.2]⟩

  have hA : ∀ E ⊆ I, MeasurableSet E →
      μ.real E = ∑ u ∈ U, wordWeight p u * μ.real (simWord r t u ⁻¹' E) := by
    intro E hEI hE
    rw [h.measureReal_eq_sum hn hE, ← Finset.sum_filter_add_sum_filter_not (omega r n)
      (fun u => ∃ x ∈ K, simWord r t u x ∈ I)]
    rw [Finset.sum_eq_zero (s := (omega r n).filter fun u => ¬ ∃ x ∈ K, simWord r t u x ∈ I),
      add_zero]
    intro u hu
    simp only [Finset.mem_filter, not_exists, not_and] at hu
    have h0 : μ.real (simWord r t u ⁻¹' E) = 0 := by
      rw [measureReal_def, ENNReal.toReal_eq_zero_iff]
      left
      refine measure_mono_null (fun x hx hxK => hu.2 x hxK (hEI hx)) hL
    rw [h0, mul_zero]

  set P := ∑ u ∈ U, wordWeight p u
  have hP : P ≤ μ.real (doubleIco a s) := by
    rw [h.measureReal_eq_sum (E := doubleIco a s) hn measurableSet_Ico]
    calc P = ∑ u ∈ U, wordWeight p u * 1 := by simp [P]
      _ ≤ ∑ u ∈ U, wordWeight p u * μ.real (simWord r t u ⁻¹' doubleIco a s) := by
          refine Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left ?_
            (wordWeight_pos h.weight_pos u).le
          obtain ⟨hu, x, hxK, hxI⟩ := Finset.mem_filter.mp hu
          have hst := (mem_omega h.abs_ratio_lt_one).mp hu
          have hlam : |wordRatio r u| ≤ (2 : ℝ) ^ (-(n : ℝ)) := hst.2.1
          have hK : K ⊆ simWord r t u ⁻¹' doubleIco a s := by
            intro y hy
            simp only [Set.mem_preimage, doubleIco, Set.mem_Ico]
            simp only [I, Set.mem_Ico] at hxI
            have hd : |simWord r t u y - simWord r t u x| ≤ 2 * L * (2 : ℝ) ^ (-(n : ℝ)) := by
              rw [simWord_apply, simWord_apply r t u x, add_sub_add_right_eq_sub, ← mul_sub,
                abs_mul]
              have hxy : |y - x| ≤ 2 * L := by
                rw [abs_le]; constructor <;> linarith [hy.1, hy.2, hxK.1, hxK.2]
              calc |(u.map r).prod| * |y - x| ≤ (2 : ℝ) ^ (-(n : ℝ)) * (2 * L) :=
                    mul_le_mul hlam hxy (abs_nonneg _) (by positivity)
                _ = 2 * L * (2 : ℝ) ^ (-(n : ℝ)) := by ring
            have hsmall : 2 * L * (2 : ℝ) ^ (-(n : ℝ)) < 1 / 2 ^ (s + 1) := by
              rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
              simp only [n, pow_add, pow_one]
              rw [← div_eq_mul_inv, div_lt_div_iff₀ (by positivity) (by positivity)]
              nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) s]
            have e : (1 : ℝ) / 2 ^ s = 2 / 2 ^ (s + 1) := by rw [pow_succ]; field_simp
            rw [abs_le] at hd
            constructor
            · linarith [hd.1]
            · have : (3 : ℝ) / 2 ^ (s + 1) = 1 / 2 ^ s + 1 / 2 ^ (s + 1) := by
                rw [e]; ring
              linarith [hd.2]
          have hμK : μ.real K = 1 := by
            rw [measureReal_def, prob_compl_eq_zero_iff (measurableSet_Icc) |>.mp hL]
            simp
          calc (1 : ℝ) = μ.real K := hμK.symm
            _ ≤ _ := measureReal_mono hK (measure_ne_top _ _)
      _ ≤ ∑ u ∈ omega r n, wordWeight p u * μ.real (simWord r t u ⁻¹' doubleIco a s) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun u _ _ =>
            mul_nonneg (wordWeight_pos h.weight_pos u).le measureReal_nonneg
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun u _ => (wordWeight_pos h.weight_pos u).le

  have hE : ∀ u ∈ U, ∑ j ∈ D', μ.real (simWord r t u ⁻¹' subIco a (s + m) j) ^ q ≤
      (2 ^ c / ρ₀ + 2) ^ q * B := by
    intro u hu
    have hst := (mem_omega h.abs_ratio_lt_one).mp (Finset.mem_filter.mp hu).1
    have hlam : |wordRatio r u| ≤ (2 : ℝ) ^ (-(n : ℝ)) := hst.2.1
    have hlam' := lt_abs_wordRatio_of_stopping hρ₀ hρ hst
    have hlam0 : 0 < |wordRatio r u| := lt_of_le_of_lt (by positivity) hlam'
    rw [simWord_eq_affine]
    have e2 : (2 : ℝ) ^ (-(n : ℝ)) = 1 / 2 ^ s * (1 / 2 ^ c) := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]; simp only [n, pow_add]; field_simp
    have hlamle : |wordRatio r u| ≤ 1 / 2 ^ s := by
      rw [e2] at hlam
      calc _ ≤ 1 / 2 ^ s * (1 / 2 ^ c) := hlam
        _ ≤ 1 / 2 ^ s * 1 := mul_le_mul_of_nonneg_left
            (by rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)) (by positivity)
        _ = 1 / 2 ^ s := mul_one _
    have hlamgt : ρ₀ < |wordRatio r u| * (2 ^ s * 2 ^ c) := by
      rw [e2] at hlam'
      have h3 : ρ₀ * (1 / 2 ^ s * (1 / 2 ^ c)) * (2 ^ s * 2 ^ c) = ρ₀ := by field_simp
      have := mul_lt_mul_of_pos_right hlam' (show (0 : ℝ) < 2 ^ s * 2 ^ c by positivity)
      linarith
    refine sum_preimage_subIco_le μ (abs_pos.mp hlam0) hq ?_ ?_ a D' hB
    · rw [le_div_iff₀ hlam0, pow_add]
      calc 1 / 2 ^ m * |wordRatio r u| ≤ 1 / 2 ^ m * (1 / 2 ^ s) :=
            mul_le_mul_of_nonneg_left hlamle (by positivity)
        _ = 1 / (2 ^ s * 2 ^ m) := by field_simp
    · have e3 : 1 / 2 ^ (s + m) / |wordRatio r u| * 2 ^ m = (1 / 2 ^ s) / |wordRatio r u| := by
        rw [pow_add]; field_simp
      rw [e3]
      have : (1 / 2 ^ s) / |wordRatio r u| ≤ 2 ^ c / ρ₀ := by
        rw [div_le_div_iff₀ hlam0 hρ₀, one_div, inv_mul_le_iff₀ (by positivity)]
        linarith [show |wordRatio r u| * (2 ^ s * 2 ^ c) = 2 ^ s * (2 ^ c * |wordRatio r u|) by
          ring]
      linarith

  have hx0 : ∀ u j, 0 ≤ μ.real (simWord r t u ⁻¹' subIco a (s + m) j) :=
    fun _ _ => measureReal_nonneg
  calc ∑ j ∈ D', μ.real (subIco a (s + m) j) ^ q
      = ∑ j ∈ D', (∑ u ∈ U, wordWeight p u * μ.real (simWord r t u ⁻¹' subIco a (s + m) j)) ^ q :=
        Finset.sum_congr rfl fun j hj => by rw [hA _ (hsub j hj) measurableSet_Ico]
    _ ≤ ∑ j ∈ D', P ^ (q - 1) *
          ∑ u ∈ U, wordWeight p u * μ.real (simWord r t u ⁻¹' subIco a (s + m) j) ^ q :=
        Finset.sum_le_sum fun j _ => rpow_sum_mul_le U _ _
          (fun u _ => (wordWeight_pos h.weight_pos u).le) (fun u _ => hx0 u j) hq
    _ = P ^ (q - 1) * ∑ u ∈ U, wordWeight p u *
          ∑ j ∈ D', μ.real (simWord r t u ⁻¹' subIco a (s + m) j) ^ q := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [Finset.mul_sum]
    _ ≤ P ^ (q - 1) * ∑ u ∈ U, wordWeight p u * ((2 ^ c / ρ₀ + 2) ^ q * B) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u hu =>
          mul_le_mul_of_nonneg_left (hE u hu) (wordWeight_pos h.weight_pos u).le)
          (Real.rpow_nonneg hP0 _)
    _ = (P ^ (q - 1) * P) * ((2 ^ c / ρ₀ + 2) ^ q * B) := by
        rw [← Finset.sum_mul]; ring
    _ = (2 ^ c / ρ₀ + 2) ^ q * B * P ^ q := by
        rw [rpow_sub_one_mul_self hP0 hq]; ring
    _ ≤ (2 ^ c / ρ₀ + 2) ^ q * B * μ.real (doubleIco a s) ^ q :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hP0 hP (by linarith))
          (mul_nonneg (Real.rpow_nonneg (by linarith) _) hB0)

omit [Fintype κ] in

theorem eventually_le_two_rpow (C : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ m : ℕ in atTop, C ≤ (2 : ℝ) ^ (b * m) := by
  have h1 : (1 : ℝ) < 2 ^ b := Real.one_lt_rpow (by norm_num) hb
  filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt h1).eventually_ge_atTop C] with m hm
  rwa [Real.rpow_mul (by norm_num), Real.rpow_natCast]

theorem proposition413 (h : IsSelfSimilar r t p μ) {q : ℝ} (hq : 1 < q)
    (hd : DifferentiableAt ℝ (lqSpectrum μ) q) : Proposition413 μ q := by
  obtain ⟨L, hL0, hL⟩ := h.exists_support
  have := h.isProbabilityMeasure
  obtain ⟨C₀, hC₀, hloc⟩ := h.exists_local_bound hL
  have hC₀q : 0 < C₀ ^ q := Real.rpow_pos_of_pos (by linarith) _
  set τ := lqSpectrum μ q
  constructor
  · intro κ' hκ
    obtain ⟨ε, hε, h412⟩ := lemma_4_12 hL0 hL hq hd (show 0 < κ' / 2 by positivity)
    refine ⟨ε / 2, by positivity, ?_⟩
    filter_upwards [h412, eventually_le_two_rpow C₀ (show 0 < κ' / 2 by positivity),
      eventually_le_two_rpow (C₀ ^ q) (show 0 < ε / 2 by positivity)]
      with m hm hm1 hm2 s a D' hD' hcard
    have hloc' := hloc q hq.le s m a D' hD' ((2 : ℝ) ^ (-((τ + ε) * m))) fun Q hQ => by
      refine hm Q (hQ.trans ?_)
      calc C₀ * D'.card ≤ (2 : ℝ) ^ (κ' / 2 * m) * (2 : ℝ) ^ ((legendre μ q - κ') * m) :=
            mul_le_mul hm1 hcard (Nat.cast_nonneg _) (by positivity)
        _ = (2 : ℝ) ^ ((legendre μ q - κ' / 2) * m) := by
            rw [← Real.rpow_add (by norm_num)]; ring_nf
    refine hloc'.trans ?_
    rw [mul_assoc]
    calc C₀ ^ q * ((2 : ℝ) ^ (-((τ + ε) * m)) * μ.real (doubleIco a s) ^ q)
        ≤ (2 : ℝ) ^ (ε / 2 * m) * ((2 : ℝ) ^ (-((τ + ε) * m)) * μ.real (doubleIco a s) ^ q) :=
          mul_le_mul_of_nonneg_right hm2 (by positivity)
      _ = (2 : ℝ) ^ (-((τ + ε / 2) * m)) * μ.real (doubleIco a s) ^ q := by
          rw [← mul_assoc, ← Real.rpow_add (by norm_num)]; ring_nf
  · intro δ hδ
    filter_upwards [eventually_lqSum_le hL0 hL hq.le (show τ - δ / 2 < τ by linarith),
      eventually_le_two_rpow (C₀ ^ q) (show 0 < δ / 2 by positivity)] with m hm hm2 s a
    have hloc' := hloc q hq.le s m a (Finset.range (2 ^ m))
      (fun j hj => Finset.mem_range.mp hj) (lqSum μ q m) fun Q _ => sum_le_lqSum μ hq.le m Q
    refine hloc'.trans ?_
    calc C₀ ^ q * lqSum μ q m * μ.real (doubleIco a s) ^ q
        ≤ (2 : ℝ) ^ (δ / 2 * m) * (2 : ℝ) ^ (-((τ - δ / 2) * m)) *
            μ.real (doubleIco a s) ^ q :=
          mul_le_mul_of_nonneg_right (mul_le_mul hm2 hm (lqSum_nonneg _ _ _) (by positivity))
            (Real.rpow_nonneg measureReal_nonneg _)
      _ = (2 : ℝ) ^ (-((τ - δ) * m)) * μ.real (doubleIco a s) ^ q := by
          rw [← Real.rpow_add (by norm_num)]; ring_nf

end Lq

end FractalGeometry
