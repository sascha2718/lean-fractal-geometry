import Mathlib
import FractalGeometry.Entropy.Lq.Inverse.Basic
import FractalGeometry.Entropy.Lq.Statements
import FractalGeometry.Entropy.Lq.Theorem51

open Filter Topology

open scoped Pointwise

namespace FractalGeometry

namespace Lq

namespace Inverse

theorem lemma_3_6 (D ℓ : ℕ) {A : Finset ℤ} (hA : InUnit (ℓ * D) A) :
    ∃ A' ⊆ A, ∃ R : ℕ → ℕ, IsUniform D ℓ A' R ∧ A.card ≤ (2 * (D + 1)) ^ ℓ * A'.card := by
  classical
  induction ℓ generalizing A with
  | zero =>
    exact ⟨A, subset_rfl, fun _ => 0, fun s hs => absurd hs (Nat.not_lt_zero _), by simp⟩
  | succ ℓ ih =>
    set P := A.image (· / 2 ^ D) with hP

    set F : ℤ → Finset ℤ := fun p => A.filter fun y => y / 2 ^ D = p with hF
    set cls : ℤ → ℕ := fun p => Nat.log 2 (F p).card with hcls
    have hFcard : ∀ p ∈ P, 1 ≤ (F p).card ∧ (F p).card ≤ 2 ^ D := by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩, card_fiber_le D A x⟩
    have hcls : ∀ p ∈ P, cls p ∈ Finset.range (D + 1) := by
      intro p hp
      rw [Finset.mem_range, Nat.lt_succ_iff]
      calc cls p ≤ Nat.log 2 (2 ^ D) := Nat.log_mono_right (hFcard p hp).2
        _ = D := Nat.log_pow (by norm_num) D
    set W : ℕ → ℕ := fun j => ∑ p ∈ P.filter (fun p => cls p = j), (F p).card with hW
    have hsumW : ∑ j ∈ Finset.range (D + 1), W j = A.card := by
      rw [Finset.sum_fiberwise_of_maps_to hcls]
      exact (Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image_of_mem _ hx)).symm
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image (Finset.range (D + 1)) W
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos D)⟩
    have hAW : A.card ≤ (D + 1) * W j := by
      rw [← hsumW]
      calc ∑ j' ∈ Finset.range (D + 1), W j' ≤ (Finset.range (D + 1)).card • W j :=
            Finset.sum_le_card_nsmul _ _ _ hj
        _ = (D + 1) * W j := by rw [Finset.card_range, smul_eq_mul]
    set Pj := P.filter (fun p => cls p = j) with hPj
    have hPjF : ∀ p ∈ Pj, 2 ^ j ≤ (F p).card ∧ (F p).card < 2 * 2 ^ j := by
      intro p hp
      obtain ⟨hpP, hpj⟩ := Finset.mem_filter.mp hp
      have hne : (F p).card ≠ 0 := by have := (hFcard p hpP).1; omega
      refine ⟨?_, ?_⟩
      · rw [← hpj]; exact Nat.pow_log_le_self 2 hne
      · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (F p).card
        rw [← hpj, pow_succ] at *
        linarith
    choose! G hGF hGcard using fun p hp => Finset.exists_subset_card_eq (hPjF p hp).1
    have hWj : W j ≤ 2 * 2 ^ j * Pj.card := by
      calc W j = ∑ p ∈ Pj, (F p).card := rfl
        _ ≤ ∑ _p ∈ Pj, 2 * 2 ^ j := Finset.sum_le_sum fun p hp => (hPjF p hp).2.le
        _ = 2 * 2 ^ j * Pj.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

    have hPjunit : InUnit (ℓ * D) Pj := fun p hp =>
      inUnit_image_prefix hA p (Finset.mem_filter.mp hp).1
    obtain ⟨P', hP'Pj, R, hP'R, hPjcard⟩ := ih hPjunit
    set A' := P'.biUnion G with hA'
    have hGfib : ∀ p ∈ P', ∀ y ∈ G p, y ∈ A ∧ y / 2 ^ D = p := fun p hp y hy =>
      Finset.mem_filter.mp (hGF p (hP'Pj hp) hy)
    have hmemA' : ∀ y, y ∈ A' ↔ y / 2 ^ D ∈ P' ∧ y ∈ G (y / 2 ^ D) := by
      intro y
      rw [Finset.mem_biUnion]
      constructor
      · rintro ⟨p, hp, hy⟩
        have := (hGfib p hp y hy).2
        rw [this]
        exact ⟨hp, hy⟩
      · rintro ⟨hp, hy⟩
        exact ⟨_, hp, hy⟩
    have hA'A : A' ⊆ A := by
      intro y hy
      obtain ⟨hp, hyG⟩ := (hmemA' y).mp hy
      exact (hGfib _ hp y hyG).1
    have himg : A'.image (· / 2 ^ D) = P' := by
      ext p
      rw [Finset.mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ((hmemA' y).mp hy).1
      · intro hp
        have hpos : 0 < (G p).card := by rw [hGcard p (hP'Pj hp)]; positivity
        obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
        have hyp := (hGfib p hp y hy).2
        refine ⟨y, (hmemA' y).mpr ⟨by rw [hyp]; exact hp, by rw [hyp]; exact hy⟩, hyp⟩
    have hfib : ∀ x ∈ A', (A'.filter fun y => y / 2 ^ D = x / 2 ^ D) = G (x / 2 ^ D) := by
      intro x hx
      obtain ⟨hxP, -⟩ := (hmemA' x).mp hx
      ext y
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨hy, hyx⟩
        have := ((hmemA' y).mp hy).2
        rwa [hyx] at this
      · intro hy
        have hyx := (hGfib _ hxP y hy).2
        exact ⟨(hmemA' y).mpr ⟨by rw [hyx]; exact hxP, by rw [hyx]; exact hy⟩, hyx⟩
    have hA'card : A'.card = 2 ^ j * P'.card := by
      rw [card_eq_mul_card_image (D := D) (r := 2 ^ j) fun x hx => by
        rw [hfib x hx, hGcard _ (hP'Pj ((hmemA' x).mp hx).1)], himg]
    refine ⟨A', hA'A, Function.update R ℓ (2 ^ j), ?_, ?_⟩
    · refine isUniform_succ_iff.mpr ⟨?_, fun x hx => ?_⟩
      · rw [himg]
        intro s hs p hp
        rw [Function.update_of_ne (Nat.ne_of_lt hs)]
        exact hP'R s hs p hp
      · rw [hfib x hx, hGcard _ (hP'Pj ((hmemA' x).mp hx).1), Function.update_self]
    · calc A.card ≤ (D + 1) * W j := hAW
        _ ≤ (D + 1) * (2 * 2 ^ j * Pj.card) := Nat.mul_le_mul_left _ hWj
        _ ≤ (D + 1) * (2 * 2 ^ j * ((2 * (D + 1)) ^ ℓ * P'.card)) := by gcongr
        _ = (2 * (D + 1)) ^ (ℓ + 1) * A'.card := by rw [hA'card, pow_succ]; ring

theorem lemma_3_7 {D ℓ : ℕ} {A : Finset ℤ} (hA : InUnit (ℓ * D) A) (hne : A.Nonempty)
    {R : ℕ → ℕ} (hR : IsUniform D ℓ A R) (S : Finset ℕ) :
    ∃ A' ⊆ A, A'.Nonempty ∧ IsUniform D ℓ A' (fun s => if s ∈ S then 1 else R s) := by
  classical
  induction ℓ generalizing A with
  | zero => exact ⟨A, subset_rfl, hne, fun s hs => absurd hs (Nat.not_lt_zero _)⟩
  | succ ℓ ih =>
    obtain ⟨hRP, hRfib⟩ := isUniform_succ_iff.mp hR
    obtain ⟨P', hP'P, hP'ne, hP'R⟩ := ih (inUnit_image_prefix hA) (hne.image _) hRP
    have hpre : ∀ p ∈ P', (A.filter fun y => y / 2 ^ D = p).Nonempty := by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hP'P hp)
      exact ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
    by_cases hℓ : ℓ ∈ S
    ·
      choose! g hg using hpre
      have hgA : ∀ p ∈ P', g p ∈ A ∧ g p / 2 ^ D = p := fun p hp => Finset.mem_filter.mp (hg p hp)
      refine ⟨P'.image g, fun y hy => ?_, hP'ne.image _, ?_⟩
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
        exact (hgA p hp).1
      have himg : (P'.image g).image (· / 2 ^ D) = P' := by
        rw [Finset.image_image]
        conv_rhs => rw [← Finset.image_id (s := P')]
        exact Finset.image_congr fun p hp => (hgA p hp).2
      refine isUniform_succ_iff.mpr ⟨by rw [himg]; exact hP'R, fun x hx => ?_⟩
      rw [ite_eq_of_pos hℓ, Finset.card_eq_one]
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      refine ⟨g p, ?_⟩
      ext y
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨p', hp', rfl⟩, h⟩
        rw [(hgA p' hp').2, (hgA p hp).2] at h
        rw [h]
      · rintro rfl
        exact ⟨⟨p, hp, rfl⟩, rfl⟩
    ·
      refine ⟨A.filter fun y => y / 2 ^ D ∈ P', Finset.filter_subset _ _, ?_, ?_⟩
      · obtain ⟨p, hp⟩ := hP'ne
        obtain ⟨x, hx⟩ := hpre p hp
        obtain ⟨hxA, hxp⟩ := Finset.mem_filter.mp hx
        exact ⟨x, Finset.mem_filter.mpr ⟨hxA, by rw [hxp]; exact hp⟩⟩
      have himg : (A.filter fun y => y / 2 ^ D ∈ P').image (· / 2 ^ D) = P' := by
        ext p
        rw [Finset.mem_image]
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact (Finset.mem_filter.mp hy).2
        · intro hp
          obtain ⟨x, hx⟩ := hpre p hp
          obtain ⟨hxA, hxp⟩ := Finset.mem_filter.mp hx
          exact ⟨x, Finset.mem_filter.mpr ⟨hxA, by rw [hxp]; exact hp⟩, hxp⟩
      refine isUniform_succ_iff.mpr ⟨by rw [himg]; exact hP'R, fun x hx => ?_⟩
      obtain ⟨hxA, hxP'⟩ := Finset.mem_filter.mp hx
      rw [ite_eq_of_neg hℓ, ← hRfib x hxA, Finset.filter_filter]
      refine congrArg Finset.card (Finset.filter_congr fun y _ => ⟨fun h => h.2, fun h => ?_⟩)
      exact ⟨by rw [h]; exact hxP', h⟩

theorem inMiddleHalf_add_of_dvd {n : ℕ} {x t : ℤ} (h : (2 : ℤ) ^ n ∣ t) :
    InMiddleHalf n (x + t) ↔ InMiddleHalf n x := by
  unfold InMiddleHalf
  obtain ⟨c, rfl⟩ := h
  rw [show x + 2 ^ n * c = x + c * 2 ^ n by ring, Int.add_mul_emod_self_right]

theorem inMiddleHalf_emod {n m : ℕ} (hnm : n ≤ m) (x : ℤ) :
    InMiddleHalf n (x % 2 ^ m) ↔ InMiddleHalf n x := by
  unfold InMiddleHalf
  rw [Int.emod_emod_of_dvd x (pow_dvd_pow 2 hnm)]

theorem exists_shift_inMiddleHalf {n : ℕ} (hn : 2 ≤ n) (x : ℤ) :
    ∃ t ∈ ({-(2 ^ (n - 2)), 0, 2 ^ (n - 2)} : Finset ℤ), InMiddleHalf n (x + t) := by
  have hN : (2 : ℤ) ^ n = 4 * 2 ^ (n - 2) := by
    rw [show n = n - 2 + 2 by omega, pow_add]
    norm_num [mul_comm]
  generalize hQ : (2 : ℤ) ^ (n - 2) = Q at hN ⊢
  have hQ0 : 0 < Q := by rw [← hQ]; positivity
  generalize hp : x % 2 ^ n = p
  have hp0 : 0 ≤ p := by rw [← hp]; exact Int.emod_nonneg _ (by positivity)
  have hp1 : p < 4 * Q := by rw [← hp, ← hN]; exact Int.emod_lt_of_pos _ (by positivity)
  have key : ∀ t, 0 ≤ p + t → p + t < 4 * Q → (x + t) % 2 ^ n = p + t := by
    intro t h0 h1
    have e : x + t = (p + t) + 2 ^ n * (x / 2 ^ n) := by
      have := Int.mul_ediv_add_emod x (2 ^ n)
      rw [hp] at this
      linarith
    rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt h0 (by rw [hN]; exact h1)]
  unfold InMiddleHalf
  by_cases h1 : 4 * p < 4 * Q
  · refine ⟨Q, by simp, ?_⟩
    rw [key Q (by linarith) (by linarith), hN]
    constructor <;> linarith
  · by_cases h2 : 4 * p ≤ 3 * (4 * Q)
    · refine ⟨0, by simp, ?_⟩
      rw [add_zero, hp, hN]
      exact ⟨by linarith, h2⟩
    · refine ⟨-Q, by simp, ?_⟩
      rw [key (-Q) (by linarith) (by linarith), hN]
      constructor <;> linarith

theorem lemma_3_8_aux {D : ℕ} (hD : 2 ≤ D) (ℓ : ℕ) (A : Finset ℤ) :
    ∀ k ≤ ℓ, ∃ a : ℤ, ∃ A' ⊆ A, A.card ≤ 3 ^ k * A'.card ∧
      ∀ y ∈ A', ∀ s, ℓ - k ≤ s → s < ℓ → InMiddleHalf (ℓ * D - s * D) (y + a) := by
  classical
  intro k
  induction k with
  | zero => exact fun _ => ⟨0, A, subset_rfl, by simp, fun y _ s hs1 hs2 => by omega⟩
  | succ k ih =>
    intro hk
    obtain ⟨a, A', hA'A, hcard, hmid⟩ := ih (by omega)
    set s₀ := ℓ - (k + 1) with hs₀
    set n := ℓ * D - s₀ * D with hn
    have hs₀D : s₀ * D + (k + 1) * D = ℓ * D := by
      rw [← add_mul, hs₀, Nat.sub_add_cancel hk]
    have hkD : D ≤ (k + 1) * D := Nat.le_mul_of_pos_left D (Nat.succ_pos k)
    have hn2 : 2 ≤ n := by omega
    set T : Finset ℤ := {-(2 ^ (n - 2)), 0, 2 ^ (n - 2)} with hT
    set good : ℤ → Finset ℤ := fun t => A'.filter fun y => InMiddleHalf n (y + a + t) with hgood
    have hcover : A'.card ≤ ∑ t ∈ T, (good t).card := by
      calc A'.card ≤ (T.biUnion good).card := Finset.card_le_card fun y hy => by
            obtain ⟨t, ht, hyt⟩ := exists_shift_inMiddleHalf hn2 (y + a)
            exact Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_filter.mpr ⟨hy, hyt⟩⟩
        _ ≤ ∑ t ∈ T, (good t).card := Finset.card_biUnion_le
    obtain ⟨t, htT, ht⟩ := Finset.exists_max_image T (fun t => (good t).card) ⟨0, by simp [hT]⟩
    have h3 : A'.card ≤ 3 * (good t).card := by
      calc A'.card ≤ ∑ t' ∈ T, (good t').card := hcover
        _ ≤ T.card • (good t).card := Finset.sum_le_card_nsmul _ _ _ ht
        _ ≤ 3 * (good t).card := by
            rw [smul_eq_mul]; exact Nat.mul_le_mul_right _ Finset.card_le_three
    refine ⟨a + t, good t, (Finset.filter_subset _ _).trans hA'A, ?_, ?_⟩
    · calc A.card ≤ 3 ^ k * A'.card := hcard
        _ ≤ 3 ^ k * (3 * (good t).card) := Nat.mul_le_mul_left _ h3
        _ = 3 ^ (k + 1) * (good t).card := by ring
    · intro y hy s hs1 hs2
      obtain ⟨hyA', hyt⟩ := Finset.mem_filter.mp hy
      rw [← add_assoc]
      rcases eq_or_lt_of_le hs1 with h | h
      · rw [← h]; exact hyt
      · have hs' : ℓ - k ≤ s := by omega
        have hsD : s₀ * D + D ≤ s * D := by
          have := Nat.mul_le_mul_right D (show s₀ + 1 ≤ s by omega)
          rwa [add_mul, one_mul] at this
        have hsl : s * D ≤ ℓ * D := Nat.mul_le_mul_right D hs2.le
        have hle : ℓ * D - s * D ≤ n - 2 := by omega
        have hdvd : (2 : ℤ) ^ (ℓ * D - s * D) ∣ t := by
          have hQ : (2 : ℤ) ^ (ℓ * D - s * D) ∣ 2 ^ (n - 2) := pow_dvd_pow 2 hle
          rw [hT] at htT
          simp only [Finset.mem_insert, Finset.mem_singleton] at htT
          rcases htT with rfl | rfl | rfl
          · exact (dvd_neg).mpr hQ
          · exact dvd_zero _
          · exact hQ
        rw [inMiddleHalf_add_of_dvd hdvd]
        exact hmid y hyA' s hs' hs2

theorem lemma_3_8 {D : ℕ} (hD : 2 ≤ D) (ℓ : ℕ) (A : Finset ℤ) :
    ∃ a : ℤ, ∃ A' ⊆ A, A.card ≤ 3 ^ ℓ * A'.card ∧
      ∀ y ∈ A', ∀ s < ℓ, InMiddleHalf (ℓ * D - s * D) ((y + a) % 2 ^ (ℓ * D)) := by
  obtain ⟨a, A', hA'A, hcard, hmid⟩ := lemma_3_8_aux hD ℓ A ℓ le_rfl
  refine ⟨a, A', hA'A, hcard, fun y hy s hs => ?_⟩
  rw [inMiddleHalf_emod (Nat.sub_le _ _)]
  exact hmid y hy s (by omega) hs

def Separated (I J : Finset ℤ) : Prop :=
  ∀ i₁ ∈ I, ∀ j₁ ∈ J, ∀ i₂ ∈ I, ∀ j₂ ∈ J, (i₁ ≠ i₂ ∨ j₁ ≠ j₂) → 2 ≤ |(i₁ + j₁) - (i₂ + j₂)|

theorem Separated.symm {I J : Finset ℤ} (h : Separated I J) : Separated J I := by
  intro j₁ hj₁ i₁ hi₁ j₂ hj₂ i₂ hi₂ hne
  have := h i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hne.symm
  rwa [add_comm j₁, add_comm j₂]

theorem Separated.card_add {I J : Finset ℤ} (h : Separated I J) :
    (I + J).card = I.card * J.card := by
  rw [Finset.card_add_iff]
  rintro ⟨i₁, j₁⟩ h₁ ⟨i₂, j₂⟩ h₂ heq
  simp only [Set.mem_prod, Finset.mem_coe] at h₁ h₂
  simp only at heq
  by_contra hne
  have hne' : i₁ ≠ i₂ ∨ j₁ ≠ j₂ := by
    by_contra h'
    push Not at h'
    exact hne (by rw [h'.1, h'.2])
  have := h i₁ h₁.1 j₁ h₁.2 i₂ h₂.1 j₂ h₂.2 hne'
  rw [heq, sub_self, abs_zero] at this
  norm_num at this

theorem two_le_abs_of_cells {N Δ r : ℤ} (hN : 0 < N) (hΔ : 2 ≤ |Δ|) (hr : |r| ≤ 2 * N - 2) :
    2 ≤ |N * Δ + r| := by
  have hr2 := le_abs_self r
  rcases le_abs'.mp hΔ with h | h
  · have : N * Δ ≤ -(2 * N) := by nlinarith
    have hr' := neg_abs_le r
    rw [abs_of_neg (by linarith)]
    linarith [le_abs_self r]
  · have : 2 * N ≤ N * Δ := by nlinarith
    have hr' := neg_abs_le r
    rw [abs_of_pos (by linarith)]
    linarith

theorem separated_extend {D r : ℕ} {A H I₀ J₀ : Finset ℤ}
    (hI₀ : I₀ ⊆ A.image (· / 2 ^ D)) (hJ₀ : J₀ ⊆ H.image (· / 2 ^ D)) (hsep : Separated I₀ J₀)
    (hAfib : ∀ x ∈ A, (A.filter fun y => y / 2 ^ D = x / 2 ^ D).card = r)
    (hHfib : ∀ x ∈ H, (H.filter fun y => y / 2 ^ D = x / 2 ^ D).card = 1) :
    ∃ I ⊆ A, ∃ J ⊆ H, Separated I J ∧ r * (I₀.card * J₀.card) ≤ 2 * (I.card * J.card) := by
  classical
  set J := H.filter fun y => y / 2 ^ D ∈ J₀ with hJ
  set A₀ := A.filter fun y => y / 2 ^ D ∈ I₀ with hA₀

  have hrestr : ∀ (B C : Finset ℤ) (k : ℕ), C ⊆ B.image (· / 2 ^ D) →
      (∀ x ∈ B, (B.filter fun y => y / 2 ^ D = x / 2 ^ D).card = k) →
      (B.filter fun y => y / 2 ^ D ∈ C).card = k * C.card := by
    intro B C k hC hB
    have himg : (B.filter fun y => y / 2 ^ D ∈ C).image (· / 2 ^ D) = C := by
      ext p
      rw [Finset.mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (Finset.mem_filter.mp hy).2
      · intro hp
        obtain ⟨x, hx, hxp⟩ := Finset.mem_image.mp (hC hp)
        exact ⟨x, Finset.mem_filter.mpr ⟨hx, by rw [hxp]; exact hp⟩, hxp⟩
    have := card_eq_mul_card_image (D := D) (r := k) (A := B.filter fun y => y / 2 ^ D ∈ C)
      fun x hx => by
        obtain ⟨hxB, hxC⟩ := Finset.mem_filter.mp hx
        rw [← hB x hxB, Finset.filter_filter]
        refine congrArg Finset.card (Finset.filter_congr fun y _ => ⟨fun h => h.2, fun h => ?_⟩)
        exact ⟨by rw [h]; exact hxC, h⟩
    rw [himg] at this
    exact this
  have hJcard : J.card = J₀.card := by rw [hrestr H J₀ 1 hJ₀ hHfib, one_mul]
  have hA₀card : A₀.card = r * I₀.card := hrestr A I₀ r hI₀ hAfib

  have hpar : (A₀.filter fun y => y % 2 = 0).card + (A₀.filter fun y => ¬ y % 2 = 0).card =
      A₀.card := Finset.card_filter_add_card_filter_not _
  obtain ⟨π, hπ⟩ : ∃ π : Prop, ∃ _ : DecidablePred (fun y : ℤ => (y % 2 = 0) = π), True :=
    ⟨True, inferInstance, trivial⟩
  clear hπ π

  have key : ∀ (P : ℤ → Prop) [DecidablePred P], (∀ y₁ ∈ A₀, ∀ y₂ ∈ A₀, P y₁ → P y₂ →
      y₁ % 2 = y₂ % 2) → A₀.card ≤ 2 * (A₀.filter P).card →
      ∃ I ⊆ A, ∃ J ⊆ H, Separated I J ∧ r * (I₀.card * J₀.card) ≤ 2 * (I.card * J.card) := by
    intro P _ hP hcard
    refine ⟨A₀.filter P, (Finset.filter_subset _ _).trans (Finset.filter_subset _ _), J,
      Finset.filter_subset _ _, ?_, ?_⟩
    · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hne
      obtain ⟨hi₁A₀, hi₁P⟩ := Finset.mem_filter.mp hi₁
      obtain ⟨hi₂A₀, hi₂P⟩ := Finset.mem_filter.mp hi₂
      obtain ⟨hi₁A, hp₁⟩ := Finset.mem_filter.mp hi₁A₀
      obtain ⟨hi₂A, hp₂⟩ := Finset.mem_filter.mp hi₂A₀
      obtain ⟨hj₁H, hq₁⟩ := Finset.mem_filter.mp hj₁
      obtain ⟨hj₂H, hq₂⟩ := Finset.mem_filter.mp hj₂
      by_cases hcell : i₁ / 2 ^ D = i₂ / 2 ^ D ∧ j₁ / 2 ^ D = j₂ / 2 ^ D
      ·
        have hj : j₁ = j₂ := by
          have h1 := hHfib j₁ hj₁H
          exact Finset.card_le_one.mp h1.le j₁ (Finset.mem_filter.mpr ⟨hj₁H, rfl⟩) j₂
            (Finset.mem_filter.mpr ⟨hj₂H, hcell.2.symm⟩)
        have hi : i₁ ≠ i₂ := hne.resolve_right (by rw [hj]; exact fun h => h rfl)
        have hpar' := hP i₁ hi₁A₀ i₂ hi₂A₀ hi₁P hi₂P
        rw [hj, show i₁ + j₂ - (i₂ + j₂) = i₁ - i₂ by ring]
        rcases lt_or_gt_of_ne hi with h | h
        · rw [abs_of_neg (by linarith)]; omega
        · rw [abs_of_pos (by linarith)]; omega
      ·
        have hne' : i₁ / 2 ^ D ≠ i₂ / 2 ^ D ∨ j₁ / 2 ^ D ≠ j₂ / 2 ^ D := by
          by_contra h'
          push Not at h'
          exact hcell h'
        have hΔ := hsep _ hp₁ _ hq₁ _ hp₂ _ hq₂ hne'
        have hN : (0 : ℤ) < 2 ^ D := by positivity
        have e : ∀ y : ℤ, y = 2 ^ D * (y / 2 ^ D) + y % 2 ^ D := fun y =>
          (Int.mul_ediv_add_emod y (2 ^ D)).symm
        have hb : ∀ y : ℤ, 0 ≤ y % 2 ^ D ∧ y % 2 ^ D < 2 ^ D := fun y =>
          ⟨Int.emod_nonneg _ hN.ne', Int.emod_lt_of_pos _ hN⟩
        have hsum : i₁ + j₁ - (i₂ + j₂) = 2 ^ D * ((i₁ / 2 ^ D + j₁ / 2 ^ D) -
            (i₂ / 2 ^ D + j₂ / 2 ^ D)) + (i₁ % 2 ^ D + j₁ % 2 ^ D - i₂ % 2 ^ D - j₂ % 2 ^ D) := by
          conv_lhs => rw [e i₁, e j₁, e i₂, e j₂]
          ring
        rw [hsum]
        refine two_le_abs_of_cells hN hΔ ?_
        rw [abs_le]
        obtain ⟨a1, a2⟩ := hb i₁
        obtain ⟨b1, b2⟩ := hb j₁
        obtain ⟨c1, c2⟩ := hb i₂
        obtain ⟨d1, d2⟩ := hb j₂
        constructor <;> linarith
    · calc r * (I₀.card * J₀.card) = A₀.card * J.card := by rw [hA₀card, hJcard]; ring
        _ ≤ 2 * (A₀.filter P).card * J.card := Nat.mul_le_mul_right _ hcard
        _ = 2 * ((A₀.filter P).card * J.card) := by ring
  by_cases h0 : (A₀.filter fun y => ¬ y % 2 = 0).card ≤ (A₀.filter fun y => y % 2 = 0).card
  · exact key (fun y => y % 2 = 0) (fun y₁ _ y₂ _ h₁ h₂ => by rw [h₁, h₂]) (by omega)
  · exact key (fun y => ¬ y % 2 = 0) (fun y₁ _ y₂ _ h₁ h₂ => by omega) (by omega)

theorem exists_separated {D : ℕ} : ∀ ℓ : ℕ, ∀ {A H : Finset ℤ}, InUnit (ℓ * D) A →
    InUnit (ℓ * D) H → ∀ {R R' : ℕ → ℕ}, IsUniform D ℓ H R → IsUniform D ℓ A R' →
    (∀ s < ℓ, R s = 1 ∨ R' s = 1) →
    ∃ I ⊆ A, ∃ J ⊆ H, Separated I J ∧ A.card * H.card ≤ 2 ^ ℓ * (I.card * J.card)
  | 0, A, H, hA, hH, _, _, _, _, _ => by
    refine ⟨A, subset_rfl, H, subset_rfl, fun i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hne => ?_, by simp⟩
    exfalso
    have h1 := hA i₁ hi₁
    have h2 := hA i₂ hi₂
    have h3 := hH j₁ hj₁
    have h4 := hH j₂ hj₂
    simp only [zero_mul, pow_zero] at h1 h2 h3 h4
    rcases hne with h | h <;> omega
  | ℓ + 1, A, H, hA, hH, R, R', hHR, hAR, hRR => by
    classical
    obtain ⟨hHP, hHfib⟩ := isUniform_succ_iff.mp hHR
    obtain ⟨hAP, hAfib⟩ := isUniform_succ_iff.mp hAR
    obtain ⟨I₀, hI₀, J₀, hJ₀, hsep, hcard⟩ := exists_separated ℓ (inUnit_image_prefix hA)
      (inUnit_image_prefix hH) hHP hAP (fun s hs => hRR s (by omega))
    have hAc := card_eq_mul_card_image hAfib
    have hHc := card_eq_mul_card_image hHfib
    rcases hRR ℓ (by omega) with h | h
    · rw [h] at hHfib hHc
      obtain ⟨I, hI, J, hJ, hsep', hcard'⟩ := separated_extend hI₀ hJ₀ hsep hAfib hHfib
      refine ⟨I, hI, J, hJ, hsep', ?_⟩
      calc A.card * H.card = R' ℓ * ((A.image (· / 2 ^ D)).card *
            (H.image (· / 2 ^ D)).card) := by rw [hAc, hHc]; ring
        _ ≤ R' ℓ * (2 ^ ℓ * (I₀.card * J₀.card)) := Nat.mul_le_mul_left _ hcard
        _ = 2 ^ ℓ * (R' ℓ * (I₀.card * J₀.card)) := by ring
        _ ≤ 2 ^ ℓ * (2 * (I.card * J.card)) := Nat.mul_le_mul_left _ hcard'
        _ = 2 ^ (ℓ + 1) * (I.card * J.card) := by ring
    · rw [h] at hAfib hAc
      obtain ⟨J, hJ, I, hI, hsep', hcard'⟩ := separated_extend hJ₀ hI₀ hsep.symm hHfib hAfib
      refine ⟨I, hI, J, hJ, hsep'.symm, ?_⟩
      calc A.card * H.card = R ℓ * ((H.image (· / 2 ^ D)).card *
            (A.image (· / 2 ^ D)).card) := by rw [hAc, hHc]; ring
        _ ≤ R ℓ * (2 ^ ℓ * (J₀.card * I₀.card)) := by
            rw [mul_comm (H.image _).card, mul_comm J₀.card]
            exact Nat.mul_le_mul_left _ hcard
        _ = 2 ^ ℓ * (R ℓ * (J₀.card * I₀.card)) := by ring
        _ ≤ 2 ^ ℓ * (2 * (J.card * I.card)) := Nat.mul_le_mul_left _ hcard'
        _ = 2 ^ (ℓ + 1) * (I.card * J.card) := by ring

theorem lemma_3_9 {D ℓ : ℕ} {A H : Finset ℤ} (hA : InUnit (ℓ * D) A) (hH : InUnit (ℓ * D) H)
    (hAne : A.Nonempty) {R R' : ℕ → ℕ} (hHR : IsUniform D ℓ H R) (hAR : IsUniform D ℓ A R') :
    H.card * ∏ s ∈ (Finset.range ℓ).filter (fun s => R s = 1), R' s ≤ 2 ^ ℓ * (A + H).card := by
  classical
  set S := (Finset.range ℓ).filter (fun s => ¬ R s = 1) with hS
  obtain ⟨A', hA'A, hA'ne, hA'R⟩ := lemma_3_7 hA hAne hAR S
  have hA' : InUnit (ℓ * D) A' := fun x hx => hA x (hA'A hx)
  obtain ⟨I, hIA', J, hJH, hsep, hcard⟩ := exists_separated ℓ hA' hH hHR hA'R fun s hs => by
    by_cases h : R s = 1
    · exact Or.inl h
    · exact Or.inr (ite_eq_of_pos (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hs, h⟩))
  have hA'card : A'.card = ∏ s ∈ (Finset.range ℓ).filter (fun s => R s = 1), R' s := by
    rw [hA'R.card_eq hA' hA'ne, ← Finset.prod_filter_mul_prod_filter_not (Finset.range ℓ)
      (fun s => R s = 1)]
    have h1 : ∏ s ∈ (Finset.range ℓ).filter (fun s => R s = 1),
        (if s ∈ S then 1 else R' s) = ∏ s ∈ (Finset.range ℓ).filter (fun s => R s = 1), R' s :=
      Finset.prod_congr rfl fun s hs => ite_eq_of_neg fun h => by
        rw [hS, Finset.mem_filter] at h
        exact h.2 (Finset.mem_filter.mp hs).2
    have h2 : ∏ s ∈ (Finset.range ℓ).filter (fun s => ¬ R s = 1),
        (if s ∈ S then 1 else R' s) = 1 :=
      Finset.prod_eq_one fun s hs => ite_eq_of_pos hs
    rw [h1, h2, mul_one]
  calc H.card * ∏ s ∈ (Finset.range ℓ).filter (fun s => R s = 1), R' s
      = A'.card * H.card := by rw [hA'card, mul_comm]
    _ ≤ 2 ^ ℓ * (I.card * J.card) := hcard
    _ = 2 ^ ℓ * (I + J).card := by rw [hsep.card_add]
    _ ≤ 2 ^ ℓ * (A + H).card := Nat.mul_le_mul_left _
        (Finset.card_le_card (Finset.add_subset_add (hIA'.trans hA'A) hJH))

end Inverse

end Lq

end FractalGeometry
