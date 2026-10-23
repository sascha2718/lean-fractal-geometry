import Mathlib
import FractalGeometry.Entropy.Lq.Basic
import FractalGeometry.Entropy.Lq.Prop413
import FractalGeometry.Entropy.Lq.Section4
import FractalGeometry.Entropy.Lq.Statement
import FractalGeometry.Pressure.Rectangular.LyapunovStatement
import FractalGeometry.SelfSimilar.SimilarityWords

open MeasureTheory Filter Topology Set

namespace FractalGeometry

namespace Lq

variable {κ : Type*} [Fintype κ] {r t p : κ → ℝ} {μ : Measure ℝ}

noncomputable def cell (r t : κ → ℝ) (m : ℕ) (u : List κ) : ℤ := ⌊simWord r t u 0 * 2 ^ m⌋

noncomputable def cellWeight (r t p : κ → ℝ) (m : ℕ) (k : ℤ) : ℝ :=
  open Classical in ∑ u ∈ (omega r m).filter (fun u => cell r t m u = k), wordWeight p u

omit [Fintype κ] in

theorem cellWeight_nonneg (hp : ∀ j, 0 < p j) (m : ℕ) (k : ℤ) : 0 ≤ cellWeight r t p m k :=
  Finset.sum_nonneg fun u _ => (wordWeight_pos hp u).le

omit [Fintype κ] in

theorem lqSum_stoppedMeasure_eq (hp : ∀ j, 0 < p j) {q : ℝ} (hq : 0 < q) (m : ℕ) :
    lqSum (stoppedMeasure r t p m) q m =
      ∑ k ∈ (omega r m).image (cell r t m), cellWeight r t p m k ^ q := by
  classical
  unfold stoppedMeasure
  rw [lqSum_sum_dirac _ _ (fun u _ => (wordWeight_pos hp u).le) _ hq]
  rfl

theorem measureReal_Icc_eq_one [IsProbabilityMeasure μ] {L : ℝ}
    (hL : μ (Set.Icc (-L) L)ᶜ = 0) : μ.real (Set.Icc (-L) L) = 1 := by
  rw [measureReal_def, prob_compl_eq_zero_iff measurableSet_Icc |>.mp hL]
  simp

theorem abs_simWord_sub_le (h : IsSelfSimilar r t p μ) {m : ℕ} {u : List κ}
    (hu : u ∈ omega r m) {L x : ℝ} (hx : x ∈ Set.Icc (-L) L) :
    |simWord r t u x - simWord r t u 0| ≤ L / 2 ^ m := by
  have hst := (mem_omega h.abs_ratio_lt_one).mp hu
  have hlam : |wordRatio r u| ≤ (2 : ℝ) ^ (-(m : ℝ)) := hst.2.1
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast] at hlam
  rw [simWord_apply, add_sub_cancel_right, abs_mul]
  have hx' : |x| ≤ L := abs_le.mpr hx
  calc |(u.map r).prod| * |x| ≤ (2 ^ m)⁻¹ * L :=
        mul_le_mul hlam hx' (abs_nonneg _) (by positivity)
    _ = L / 2 ^ m := by ring

theorem exists_lqSum_stoppedMeasure_le (h : IsSelfSimilar r t p μ) {L : ℝ}
    (hL : μ (Set.Icc (-L) L)ᶜ = 0) {q : ℝ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      lqSum (stoppedMeasure r t p m) q m ≤ C * lqSum μ q m := by
  classical
  have := h.isProbabilityMeasure
  set N : ℕ := 2 * ⌈L⌉₊ + 3
  refine ⟨(N : ℝ) ^ q, by positivity, fun m hm => ?_⟩
  rw [lqSum_stoppedMeasure_eq h.weight_pos (by linarith)]
  set img := (omega r m).image (cell r t m)
  set S : ℤ → Set ℝ := fun k => Set.Icc ((k - L) / 2 ^ m) ((k + 1 + L) / 2 ^ m)
  have h2m : (0 : ℝ) < 2 ^ m := by positivity

  have hcell : ∀ k, cellWeight r t p m k ≤ μ.real (S k) := by
    intro k
    rw [h.measureReal_eq_sum hm measurableSet_Icc]
    unfold cellWeight
    calc ∑ u ∈ (omega r m).filter (fun u => cell r t m u = k), wordWeight p u
        = ∑ u ∈ (omega r m).filter (fun u => cell r t m u = k), wordWeight p u * 1 := by simp
      _ ≤ ∑ u ∈ (omega r m).filter (fun u => cell r t m u = k),
            wordWeight p u * μ.real (simWord r t u ⁻¹' S k) := by
          refine Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left ?_
            (wordWeight_pos h.weight_pos u).le
          obtain ⟨hu, hk⟩ := Finset.mem_filter.mp hu
          rw [← measureReal_Icc_eq_one hL]
          refine measureReal_mono (fun x hx => ?_) (measure_ne_top _ _)
          have hd := abs_simWord_sub_le h hu hx
          have hk' := mem_dyadicIco_iff.mpr hk
          simp only [dyadicIco, Set.mem_Ico] at hk'
          rw [abs_le] at hd
          simp only [Set.mem_preimage, S, Set.mem_Icc]
          constructor
          · rw [sub_div]; linarith [hd.1, hk'.1]
          · rw [add_div]; linarith [hd.2, hk'.2]
      _ ≤ ∑ u ∈ omega r m, wordWeight p u * μ.real (simWord r t u ⁻¹' S k) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun u _ _ =>
            mul_nonneg (wordWeight_pos h.weight_pos u).le measureReal_nonneg

  set c : ℤ → Finset ℤ := fun k => Finset.Icc (k - ⌈L⌉₊ - 1) (k + ⌈L⌉₊ + 1)
  have hcard : ∀ k, (c k).card ≤ N := fun k => by
    simp only [c, Int.card_Icc, N]; omega
  have h41 := lemma_4_1 μ img (img.biUnion c) S (dyadicIco m) N hq c
    (fun k hk => Finset.subset_biUnion_of_mem c hk)
    (fun k _ x hx => by
      simp only [Set.mem_iUnion]
      refine ⟨⌊x * 2 ^ m⌋, ?_, mem_dyadicIco_iff.mpr rfl⟩
      simp only [S, Set.mem_Icc] at hx
      simp only [c, Finset.mem_Icc]
      have hL' : L ≤ ⌈L⌉₊ := Nat.le_ceil L
      constructor
      · have : (k : ℝ) - ⌈L⌉₊ - 1 ≤ x * 2 ^ m := by
          rw [div_le_iff₀ h2m] at hx; linarith [hx.1]
        have := Int.floor_le_floor this
        rw [show (k : ℝ) - ⌈L⌉₊ - 1 = ((k - ⌈L⌉₊ - 1 : ℤ) : ℝ) by push_cast; ring,
          Int.floor_intCast] at this
        exact this
      · have : x * 2 ^ m ≤ (k : ℝ) + ⌈L⌉₊ + 1 := by
          rw [le_div_iff₀ h2m] at hx; linarith [hx.2]
        have := Int.floor_le_floor this
        rw [show (k : ℝ) + ⌈L⌉₊ + 1 = ((k + ⌈L⌉₊ + 1 : ℤ) : ℝ) by push_cast; ring,
          Int.floor_intCast] at this
        exact this)
    (fun k _ => hcard k)
    (fun j _ => by
      calc (img.filter fun k => j ∈ c k).card
          ≤ (Finset.Icc (j - ⌈L⌉₊ - 1) (j + ⌈L⌉₊ + 1)).card := by
            refine Finset.card_le_card fun k hk => ?_
            simp only [Finset.mem_filter, c, Finset.mem_Icc] at hk
            simp only [Finset.mem_Icc]
            omega
        _ ≤ N := hcard j)
  calc ∑ k ∈ img, cellWeight r t p m k ^ q ≤ ∑ k ∈ img, μ.real (S k) ^ q :=
        Finset.sum_le_sum fun k _ => Real.rpow_le_rpow (cellWeight_nonneg h.weight_pos m k)
          (hcell k) (by linarith)
    _ ≤ (N : ℝ) ^ q * ∑ j ∈ img.biUnion c, μ.real (dyadicIco m j) ^ q := h41
    _ ≤ (N : ℝ) ^ q * lqSum μ q m :=
        mul_le_mul_of_nonneg_left (sum_le_lqSum μ hq m _) (by positivity)

theorem cell_near (h : IsSelfSimilar r t p μ) {L : ℝ} {m n : ℕ} {u : List κ}
    (hu : u ∈ omega r m) {x : ℝ} (hx : x ∈ Set.Icc (-L) L) {i : ℤ}
    (hxi : simWord r t u x ∈ dyadicIco (m + n) i) :
    ⌊(i : ℝ) / 2 ^ n⌋ - ⌈L⌉₊ - 1 ≤ cell r t m u ∧ cell r t m u ≤ ⌊(i : ℝ) / 2 ^ n⌋ + ⌈L⌉₊ + 1 := by
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hd := abs_simWord_sub_le h hu hx
  rw [abs_le] at hd
  have hk := mem_dyadicIco_iff.mpr (rfl : cell r t m u = cell r t m u)
  simp only [dyadicIco, Set.mem_Ico, cell] at hk
  rw [div_le_iff₀ h2m, lt_div_iff₀ h2m] at hk
  simp only [dyadicIco, Set.mem_Ico] at hxi
  rw [div_le_iff₀ (by positivity), lt_div_iff₀ (by positivity), pow_add] at hxi
  set c := ⌊(i : ℝ) / 2 ^ n⌋
  have hc1 := Int.floor_le ((i : ℝ) / 2 ^ n)
  have hc2 := Int.lt_floor_add_one ((i : ℝ) / 2 ^ n)
  rw [le_div_iff₀ h2n] at hc1
  rw [div_lt_iff₀ h2n] at hc2
  have hL' : L ≤ ⌈L⌉₊ := Nat.le_ceil L
  have hdm1 : (simWord r t u x - L / 2 ^ m) * 2 ^ m = simWord r t u x * 2 ^ m - L := by
    field_simp
  have hdm2 : (simWord r t u x + L / 2 ^ m) * 2 ^ m = simWord r t u x * 2 ^ m + L := by
    field_simp
  have ht1 : simWord r t u x * 2 ^ m - L ≤ simWord r t u 0 * 2 ^ m := by
    rw [← hdm1]; exact mul_le_mul_of_nonneg_right (by linarith [hd.2]) h2m.le
  have ht2 : simWord r t u 0 * 2 ^ m ≤ simWord r t u x * 2 ^ m + L := by
    rw [← hdm2]; exact mul_le_mul_of_nonneg_right (by linarith [hd.1]) h2m.le

  have hfx1 : (c : ℝ) ≤ simWord r t u x * 2 ^ m := by
    have : (c : ℝ) * 2 ^ n ≤ simWord r t u x * 2 ^ m * 2 ^ n := by nlinarith
    exact le_of_mul_le_mul_right this h2n
  have hfx2 : simWord r t u x * 2 ^ m < c + 2 := by
    have h1 : (i : ℝ) + 1 ≤ ((c : ℝ) + 1) * 2 ^ n + 1 := by linarith
    have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have : simWord r t u x * 2 ^ m * 2 ^ n < ((c : ℝ) + 2) * 2 ^ n := by nlinarith
    exact lt_of_mul_lt_mul_right this h2n.le
  constructor
  · have : ((c - ⌈L⌉₊ - 1 : ℤ) : ℝ) < ((cell r t m u + 1 : ℤ) : ℝ) := by
      simp only [cell]; push_cast; linarith
    have := Int.cast_lt.mp this
    omega
  · have : (cell r t m u : ℝ) < ((c + ⌈L⌉₊ + 2 : ℤ) : ℝ) := by
      simp only [cell]; push_cast; linarith
    have := Int.cast_lt.mp this
    omega

theorem exists_lqSum_add_le (h : IsSelfSimilar r t p μ) {L : ℝ}
    (hL : μ (Set.Icc (-L) L)ᶜ = 0) {q : ℝ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n : ℕ, 1 ≤ m →
      lqSum μ q (m + n) ≤ C * lqSum (stoppedMeasure r t p m) q m * lqSum μ q n := by
  classical
  have := h.isProbabilityMeasure
  obtain ⟨ρ₀, hρ₀, hρ⟩ := exists_ratio_lower h.ratio_ne_zero
  set N : ℕ := 2 * ⌈L⌉₊ + 3
  set C₁ : ℝ := 1 / ρ₀ + 2
  have hC₁ : 0 < C₁ := by positivity
  refine ⟨(N : ℝ) ^ (q - 1) * C₁ ^ q, by positivity, fun m n hm => ?_⟩
  set img := (omega r m).image (cell r t m)
  set x : List κ → ℤ → ℝ := fun u i => μ.real (simWord r t u ⁻¹' dyadicIco (m + n) i)
  set y : ℤ → ℤ → ℝ := fun k i =>
    ∑ u ∈ (omega r m).filter (fun u => cell r t m u = k), wordWeight p u * x u i
  have hx0 : ∀ u i, 0 ≤ x u i := fun _ _ => measureReal_nonneg
  have hy0 : ∀ k i, 0 ≤ y k i := fun k i => Finset.sum_nonneg fun u _ =>
    mul_nonneg (wordWeight_pos h.weight_pos u).le (hx0 u i)
  have hμJ : ∀ i, μ.real (dyadicIco (m + n) i) = ∑ k ∈ img, y k i := by
    intro i
    rw [h.measureReal_eq_sum hm (measurableSet_dyadicIco _ _)]
    exact (Finset.sum_fiberwise_of_maps_to (fun u hu => Finset.mem_image_of_mem _ hu) _).symm

  have hG : ∀ i, ((img.filter fun k => y k i ≠ 0).card : ℝ) ≤ N := by
    intro i
    set c := ⌊(i : ℝ) / 2 ^ n⌋
    have hsub : (img.filter fun k => y k i ≠ 0) ⊆ Finset.Icc (c - ⌈L⌉₊ - 1) (c + ⌈L⌉₊ + 1) := by
      intro k hk
      obtain ⟨-, hyk⟩ := Finset.mem_filter.mp hk
      obtain ⟨u, hu, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hyk
      obtain ⟨hu', rfl⟩ := Finset.mem_filter.mp hu
      have hxu : x u i ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
      have hex : ∃ z ∈ Set.Icc (-L) L, simWord r t u z ∈ dyadicIco (m + n) i := by
        by_contra hno
        push Not at hno
        apply hxu
        simp only [x]
        rw [measureReal_def, ENNReal.toReal_eq_zero_iff]
        left
        exact measure_mono_null (fun z hz hzK => hno z hzK hz) hL
      obtain ⟨z, hz, hzi⟩ := hex
      rw [Finset.mem_Icc]
      exact cell_near h hu' hz hzi
    calc ((img.filter fun k => y k i ≠ 0).card : ℝ)
        ≤ (Finset.Icc (c - ⌈L⌉₊ - 1) (c + ⌈L⌉₊ + 1)).card := by
          exact_mod_cast Finset.card_le_card hsub
      _ = N := by
          have : (Finset.Icc (c - ⌈L⌉₊ - 1) (c + ⌈L⌉₊ + 1)).card = N := by
            simp only [Int.card_Icc, N]; omega
          rw [this]

  have hE : ∀ u ∈ omega r m, ∑ i ∈ dyadicCover L (m + n), x u i ^ q ≤ C₁ ^ q * lqSum μ q n := by
    intro u hu
    have hst := (mem_omega h.abs_ratio_lt_one).mp hu
    have hlam : |wordRatio r u| ≤ (2 : ℝ) ^ (-(m : ℝ)) := hst.2.1
    have hlam' := lt_abs_wordRatio_of_stopping hρ₀ hρ hst
    have hlam0 : 0 < |wordRatio r u| := lt_of_le_of_lt (by positivity) hlam'
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast] at hlam hlam'
    simp only [x]
    rw [simWord_eq_affine]
    refine sum_preimage_dyadicIco_le μ (abs_pos.mp hlam0) hq ?_ ?_ _
      fun Q _ => sum_le_lqSum μ hq n Q
    · rw [le_div_iff₀ hlam0, pow_add]
      calc 1 / 2 ^ n * |wordRatio r u| ≤ 1 / 2 ^ n * (2 ^ m)⁻¹ :=
            mul_le_mul_of_nonneg_left hlam (by positivity)
        _ = 1 / (2 ^ m * 2 ^ n) := by field_simp
    · have e3 : 1 / 2 ^ (m + n) / |wordRatio r u| * 2 ^ n = (1 / 2 ^ m) / |wordRatio r u| := by
        rw [pow_add]; field_simp
      rw [e3]
      have : (1 / 2 ^ m) / |wordRatio r u| ≤ 1 / ρ₀ := by
        rw [div_le_div_iff₀ hlam0 hρ₀, one_mul, one_div, ← div_eq_inv_mul,
          div_le_iff₀ (by positivity)]
        have := mul_lt_mul_of_pos_right hlam' (show (0 : ℝ) < 2 ^ m by positivity)
        rw [mul_assoc, inv_mul_cancel₀ (by positivity), mul_one] at this
        linarith
      simp only [C₁]
      linarith

  set P : ℤ → ℝ := cellWeight r t p m
  have hP0 : ∀ k, 0 ≤ P k := cellWeight_nonneg h.weight_pos m
  have hstep : ∀ i, μ.real (dyadicIco (m + n) i) ^ q ≤ (N : ℝ) ^ (q - 1) *
      ∑ k ∈ img, P k ^ (q - 1) *
        ∑ u ∈ (omega r m).filter (fun u => cell r t m u = k), wordWeight p u * x u i ^ q := by
    intro i
    rw [hμJ i, ← Finset.sum_filter_ne_zero]
    have h1 := Real.rpow_sum_le_const_mul_sum_rpow (img.filter fun k => y k i ≠ 0)
      (fun k => y k i) hq
    simp only [abs_of_nonneg (hy0 _ _)] at h1
    refine h1.trans ?_
    refine mul_le_mul (Real.rpow_le_rpow (Nat.cast_nonneg _) (hG i) (by linarith)) ?_
      (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (hy0 k i) _) (by positivity)
    calc ∑ k ∈ img.filter (fun k => y k i ≠ 0), y k i ^ q ≤ ∑ k ∈ img, y k i ^ q :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun k _ _ =>
            Real.rpow_nonneg (hy0 k i) _
      _ ≤ _ := Finset.sum_le_sum fun k _ => rpow_sum_mul_le _ _ _
          (fun u _ => (wordWeight_pos h.weight_pos u).le) (fun u _ => hx0 u i) hq
  rw [lqSum_eq_sum_dyadicCover hL (by linarith : (0 : ℝ) < q) (m + n),
    lqSum_stoppedMeasure_eq h.weight_pos (by linarith) m]
  calc ∑ i ∈ dyadicCover L (m + n), μ.real (dyadicIco (m + n) i) ^ q
      ≤ ∑ i ∈ dyadicCover L (m + n), (N : ℝ) ^ (q - 1) * ∑ k ∈ img, P k ^ (q - 1) *
          ∑ u ∈ (omega r m).filter (fun u => cell r t m u = k), wordWeight p u * x u i ^ q :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = (N : ℝ) ^ (q - 1) * ∑ k ∈ img, P k ^ (q - 1) *
          ∑ u ∈ (omega r m).filter (fun u => cell r t m u = k), wordWeight p u *
            ∑ i ∈ dyadicCover L (m + n), x u i ^ q := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]
    _ ≤ (N : ℝ) ^ (q - 1) * ∑ k ∈ img, P k ^ (q - 1) *
          ∑ u ∈ (omega r m).filter (fun u => cell r t m u = k), wordWeight p u *
            (C₁ ^ q * lqSum μ q n) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u hu =>
            mul_le_mul_of_nonneg_left (hE u (Finset.mem_filter.mp hu).1)
              (wordWeight_pos h.weight_pos u).le) (Real.rpow_nonneg (hP0 k) _))
          (by positivity)
    _ = (N : ℝ) ^ (q - 1) * C₁ ^ q * (∑ k ∈ img, P k ^ (q - 1) * P k) * lqSum μ q n := by
        have hk : ∀ k, ∑ u ∈ (omega r m).filter (fun u => cell r t m u = k),
            wordWeight p u * (C₁ ^ q * lqSum μ q n) = P k * (C₁ ^ q * lqSum μ q n) := fun k => by
          rw [← Finset.sum_mul]; rfl
        simp_rw [hk]
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = (N : ℝ) ^ (q - 1) * C₁ ^ q * (∑ k ∈ img, P k ^ q) * lqSum μ q n := by
        simp_rw [rpow_sub_one_mul_self (hP0 _) hq]

theorem tendsto_lqExponent (h : IsSelfSimilar r t p μ) {q : ℝ} (hq : 1 < q) :
    Tendsto (lqExponent μ q) atTop (𝓝 (lqSpectrum μ q)) := by
  obtain ⟨L, hL0, hL⟩ := h.exists_support
  have := h.isProbabilityMeasure
  obtain ⟨C₂, hC₂, h65⟩ := exists_lqSum_stoppedMeasure_le h hL hq.le
  obtain ⟨C₃, hC₃, hsub⟩ := exists_lqSum_add_le h hL hq.le
  set S := lqSum μ q
  have hS0 : ∀ n, 0 < S n := lqSum_pos hL0 hL hq.le
  set C := max (C₃ * C₂) (1 / S 0)
  have hC : 0 < C := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hCS0 : 1 ≤ C * S 0 := by
    have := mul_le_mul_of_nonneg_right (le_max_right (C₃ * C₂) (1 / S 0)) (hS0 0).le
    rw [one_div_mul_cancel (hS0 0).ne'] at this
    exact this
  have hsm : ∀ m n, S (m + n) ≤ C * S m * S n := by
    intro m n
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [zero_add]
      calc S n = 1 * S n := (one_mul _).symm
        _ ≤ C * S 0 * S n := mul_le_mul_of_nonneg_right hCS0 (hS0 n).le
    · calc S (m + n) ≤ C₃ * lqSum (stoppedMeasure r t p m) q m * S n := hsub m n hm
        _ ≤ C₃ * (C₂ * S m) * S n :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h65 m hm) hC₃.le) (hS0 n).le
        _ = C₃ * C₂ * S m * S n := by ring
        _ ≤ C * S m * S n :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
              (hS0 m).le) (hS0 n).le
  set u : ℕ → ℝ := fun n => Real.logb 2 (C * S n)
  have hadd : Subadditive u := by
    intro m n
    simp only [u]
    rw [← Real.logb_mul (by have := hS0 m; positivity) (by have := hS0 n; positivity)]
    refine Real.logb_le_logb_of_le (by norm_num) (by have := hS0 (m + n); positivity) ?_
    calc C * S (m + n) ≤ C * (C * S m * S n) := mul_le_mul_of_nonneg_left (hsm m n) hC.le
      _ = C * S m * (C * S n) := by ring

  set A := |Real.logb 2 C| + (q - 1) * (|Real.logb 2 (2 * L + 2)| + 1)
  have hbdd : BddBelow (Set.range fun n => u n / n) := by
    refine ⟨-A, ?_⟩
    rintro _ ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [CharP.cast_eq_zero, div_zero, neg_nonpos]
      positivity
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hge := lqSum_ge hL0 hL hq.le n
    have hlog : (1 - q) * (Real.logb 2 (2 * L + 2) + n) ≤ Real.logb 2 (S n) := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (hS0 n)]
      convert hge using 1
      rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_add (by norm_num),
        Real.rpow_logb (by norm_num) (by norm_num) (by linarith), Real.rpow_natCast]
    simp only [u]
    rw [Real.logb_mul hC.ne' (hS0 n).ne', le_div_iff₀ (by linarith)]
    have h1 : -|Real.logb 2 C| ≤ Real.logb 2 C := neg_abs_le _
    have h2 : -|Real.logb 2 (2 * L + 2)| ≤ Real.logb 2 (2 * L + 2) := neg_abs_le _
    have h3 : 0 ≤ |Real.logb 2 C| := abs_nonneg _
    have h4 : 0 ≤ |Real.logb 2 (2 * L + 2)| := abs_nonneg _
    have hq1 : 0 ≤ q - 1 := by linarith
    have e1 : (q - 1) * Real.logb 2 (2 * L + 2) ≤ (q - 1) * |Real.logb 2 (2 * L + 2)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hq1
    have e2 : |Real.logb 2 C| * 1 ≤ |Real.logb 2 C| * n := mul_le_mul_of_nonneg_left hn' h3
    have e3 : (q - 1) * |Real.logb 2 (2 * L + 2)| * 1 ≤ (q - 1) * |Real.logb 2 (2 * L + 2)| * n :=
      mul_le_mul_of_nonneg_left hn' (mul_nonneg hq1 h4)
    simp only [A]
    nlinarith
  have hlim := hadd.tendsto_lim hbdd
  have hexp : Tendsto (lqExponent μ q) atTop (𝓝 (-hadd.lim)) := by
    have h2 : Tendsto (fun n : ℕ => -(u n / n) + Real.logb 2 C / n) atTop
        (𝓝 (-hadd.lim + 0)) :=
      hlim.neg.add (tendsto_const_div_atTop_nhds_zero_nat _)
    rw [add_zero] at h2
    refine h2.congr' (Eventually.of_forall fun n => ?_)
    simp only [u, lqExponent]
    rw [Real.logb_mul hC.ne' (hS0 n).ne']
    ring
  rwa [lqSpectrum_eq, hexp.liminf_eq]

end Lq

end FractalGeometry
