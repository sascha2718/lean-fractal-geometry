import Mathlib
import FractalGeometry.Entropy.Lq.Bourgain.Tree
import FractalGeometry.Entropy.Lq.Statements

open Finset

namespace FractalGeometry

namespace Lq

namespace Bourgain

theorem unif_step {L S s₀ : ℕ} (hs₀ : s₀ < S) {A' : Finset ℤ} (hne : A'.Nonempty)
    {R : ℕ → ℕ} (h : IsUnifFrom L S (s₀ + 1) A' R) :
    ∃ A'' ⊆ A', A''.Nonempty ∧ ∃ R' : ℕ → ℕ, IsUnifFrom L S s₀ A'' R' ∧
      A'.card ≤ 2 * (L + 1) * A''.card := by
  classical
  set M := S * L with hM
  set l := s₀ * L with hl
  set l' := (s₀ + 1) * L with hl'
  have hle : l ≤ l' := Nat.mul_le_mul_right _ (Nat.le_succ s₀)
  have hleM : l' ≤ M := Nat.mul_le_mul_right _ hs₀
  have hLd : l' - l = L := by rw [hl', hl, Nat.succ_mul]; omega
  set F := ∏ s' ∈ Ico (s₀ + 1) S, R s' with hF
  have hFcell : ∀ y ∈ A', (cellOf M l' A' (pre M l' y)).card = F := fun y hy =>
    h.cell_card' le_rfl hs₀ hy

  set ch : ℤ → ℕ := fun c => (kids M l l' A' c).card with hch
  set bk : ℤ → ℕ := fun c => Nat.log 2 (ch c) with hbk
  set C := A'.image (pre M l) with hC
  have hkidF : ∀ c c', c' ∈ kids M l l' A' c → (cellOf M l' A' c').card = F := by
    intro c c' hc'
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hc'
    exact hFcell y (mem_cellOf.mp hy).1
  have hmass : ∀ c, (cellOf M l A' c).card = ch c * F := by
    intro c
    rw [card_cellOf_eq_sum hle hleM, sum_congr rfl (hkidF c), sum_const, smul_eq_mul]
  have hchpos : ∀ c ∈ C, 0 < ch c := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hc
    exact card_pos.mpr ⟨pre M l' y, mem_image.mpr ⟨y, mem_cellOf.mpr ⟨hy, rfl⟩, rfl⟩⟩
  have hbkL : ∀ c ∈ C, bk c < L + 1 := by
    intro c hc
    have h1 : ch c ≤ 2 ^ L := by
      have := card_kids_le hle hleM A' c
      rwa [hLd] at this
    have h2 : bk c ≤ L := by
      calc bk c = Nat.log 2 (ch c) := rfl
        _ ≤ Nat.log 2 (2 ^ L) := Nat.log_mono_right h1
        _ = L := Nat.log_pow (by norm_num) L
    omega

  have hsplit : A'.card = ∑ b ∈ range (L + 1), ∑ c ∈ C with bk c = b, (cellOf M l A' c).card := by
    rw [sum_fiberwise_of_maps_to (fun c hc => mem_range.mpr (hbkL c hc))]
    unfold cellOf
    exact card_eq_sum_card_fiberwise (fun y hy => mem_image_of_mem _ hy)
  obtain ⟨b, -, hb⟩ : ∃ b ∈ range (L + 1),
      A'.card ≤ (L + 1) * ∑ c ∈ C with bk c = b, (cellOf M l A' c).card := by
    apply exists_le_of_sum_le nonempty_range_add_one
    rw [sum_const, card_range, smul_eq_mul, ← mul_sum, ← hsplit]

  have hKex : ∀ c, ∃ K ⊆ kids M l l' A' c, bk c = b → c ∈ C → K.card = 2 ^ b := by
    intro c
    by_cases hc : bk c = b ∧ c ∈ C
    · have h2b : 2 ^ b ≤ ch c := by
        rw [← hc.1]
        exact Nat.pow_log_le_self 2 (hchpos c hc.2).ne'
      obtain ⟨K, hK, hKc⟩ := exists_subset_card_eq h2b
      exact ⟨K, hK, fun _ _ => hKc⟩
    · exact ⟨∅, empty_subset _, fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose Keep hKeep hKeepc using hKex
  set A'' := A'.filter fun y => bk (pre M l y) = b ∧ pre M l' y ∈ Keep (pre M l y) with hA''
  have hsub : A'' ⊆ A' := filter_subset _ _

  have hkeepmem : ∀ c, bk c = b → ∀ c' ∈ Keep c, ∀ y ∈ A', pre M l' y = c' → y ∈ A'' := by
    intro c hc c' hc' y hy hyc'
    have hdiv : pre M l y = c := by
      rw [← pre_pre hle hleM y, hyc']
      exact pre_of_mem_kids hle hleM (hKeep c hc')
    refine mem_filter.mpr ⟨hy, ?_, ?_⟩
    · rw [hdiv]; exact hc
    · rw [hdiv, hyc']; exact hc'

  have hcell'' : ∀ c, bk c = b → ∀ c' ∈ Keep c, cellOf M l' A'' c' = cellOf M l' A' c' := by
    intro c hc c' hc'
    ext y
    simp only [mem_cellOf]
    constructor
    · rintro ⟨hy, hyc⟩; exact ⟨hsub hy, hyc⟩
    · rintro ⟨hy, hyc⟩; exact ⟨hkeepmem c hc c' hc' y hy hyc, hyc⟩

  have hkids'' : ∀ c ∈ C, bk c = b → kids M l l' A'' c = Keep c := by
    intro c hcC hc
    ext c'
    constructor
    · intro hc'
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hc'
      obtain ⟨hyA, hyc⟩ := mem_cellOf.mp hy
      have := (mem_filter.mp hyA).2.2
      rwa [hyc] at this
    · intro hc'
      obtain ⟨y, hy, rfl⟩ := mem_image.mp (hKeep c hc')
      obtain ⟨hyA, hyc⟩ := mem_cellOf.mp hy
      exact mem_image.mpr ⟨y, mem_cellOf.mpr ⟨hkeepmem c hc _ hc' y hyA rfl, hyc⟩, rfl⟩
  have hmass'' : ∀ c ∈ C, bk c = b → (cellOf M l A'' c).card = 2 ^ b * F := by
    intro c hcC hc
    rw [card_cellOf_eq_sum hle hleM, hkids'' c hcC hc]
    rw [sum_congr rfl fun c' hc' => (hcell'' c hc c' hc').symm ▸ hkidF c c' (hKeep c hc'),
      sum_const, smul_eq_mul, hKeepc c hc hcC]
  have hcard'' : A''.card = ∑ c ∈ C with bk c = b, 2 ^ b * F := by
    rw [card_eq_sum_card_fiberwise (f := pre M l) (t := C.filter fun c => bk c = b)]
    · refine sum_congr rfl fun c hc => ?_
      obtain ⟨hcC, hcb⟩ := mem_filter.mp hc
      rw [← hmass'' c hcC hcb]
      rfl
    · intro y hy
      have hy' := mem_filter.mp hy
      exact mem_filter.mpr ⟨mem_image_of_mem _ hy'.1, hy'.2.1⟩

  have hsize : A'.card ≤ 2 * (L + 1) * A''.card := by
    have h1 : ∑ c ∈ C with bk c = b, (cellOf M l A' c).card ≤
        2 * ∑ c ∈ C with bk c = b, 2 ^ b * F := by
      rw [mul_sum]
      refine sum_le_sum fun c hc => ?_
      rw [hmass c]
      have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (ch c)
      have hbc : bk c = b := (mem_filter.mp hc).2
      rw [show Nat.log 2 (ch c) = b from hbc, pow_succ] at hlt
      nlinarith
    rw [hcard'']
    calc A'.card ≤ (L + 1) * ∑ c ∈ C with bk c = b, (cellOf M l A' c).card := hb
      _ ≤ (L + 1) * (2 * ∑ c ∈ C with bk c = b, 2 ^ b * F) := Nat.mul_le_mul_left _ h1
      _ = _ := by ring
  have hne'' : A''.Nonempty := by
    rw [← card_pos]
    have := card_pos.mpr hne
    by_contra h0
    rw [Nat.eq_zero_of_not_pos h0, mul_zero] at hsize
    omega
  refine ⟨A'', hsub, hne'', fun s => if s = s₀ then 2 ^ b else R s, ?_, hsize⟩
  intro s hs₁ hs x hx
  obtain ⟨hxA, hxb, hxK⟩ := mem_filter.mp hx
  rcases Nat.eq_or_lt_of_le hs₁ with rfl | hlt
  · simp only [↓reduceIte]
    rw [branching_eq_card_kids,
      hkids'' _ (mem_image_of_mem _ hxA) hxb, hKeepc _ hxb (mem_image_of_mem _ hxA)]
  · simp only [show s ≠ s₀ by omega, ↓reduceIte]
    rw [← h s hlt hs x hxA]
    have hsl : (s * L) ≥ l' := Nat.mul_le_mul_right _ hlt
    have hsM : s * L ≤ M := Nat.mul_le_mul_right _ hs.le
    unfold branching
    congr 2
    ext y
    simp only [mem_filter]
    constructor
    · rintro ⟨hy, hyx⟩; exact ⟨hsub hy, hyx⟩
    · rintro ⟨hy, hyx⟩
      refine ⟨?_, hyx⟩
      have hyx' : pre M l' y = pre M l' x := pre_eq_of_pre_eq hsl hsM hyx
      have hyx'' : pre M l y = pre M l x := pre_eq_of_pre_eq hle hleM hyx'
      refine mem_filter.mpr ⟨hy, ?_, ?_⟩
      · rw [hyx'']; exact hxb
      · rw [hyx', hyx'']; exact hxK

theorem exists_unif_subset (L S : ℕ) {A : Finset ℤ} (hne : A.Nonempty) :
    ∃ A₀ ⊆ A, A₀.Nonempty ∧ ∃ R : ℕ → ℕ, IsUnif L S A₀ R ∧
      A.card ≤ (2 * (L + 1)) ^ S * A₀.card := by
  have key : ∀ k ≤ S, ∃ A' ⊆ A, A'.Nonempty ∧ ∃ R : ℕ → ℕ, IsUnifFrom L S (S - k) A' R ∧
      A.card ≤ (2 * (L + 1)) ^ k * A'.card := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨A, Subset.rfl, hne, fun _ => 0, fun s hs hs' => by omega, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨A', hA', hne', R, hR, hcard⟩ := ih (by omega)
      have hs : S - (k + 1) < S := by omega
      have hR' : IsUnifFrom L S (S - (k + 1) + 1) A' R := by
        rwa [show S - (k + 1) + 1 = S - k by omega]
      obtain ⟨A'', hA'', hne'', R', hR'', hcard'⟩ := unif_step hs hne' hR'
      refine ⟨A'', hA''.trans hA', hne'', R', hR'', ?_⟩
      calc A.card ≤ (2 * (L + 1)) ^ k * A'.card := hcard
        _ ≤ (2 * (L + 1)) ^ k * (2 * (L + 1) * A''.card) := Nat.mul_le_mul_left _ hcard'
        _ = _ := by ring
  obtain ⟨A₀, hA₀, hne₀, R, hR, hcard⟩ := key S le_rfl
  refine ⟨A₀, hA₀, hne₀, R, fun s hs => ?_, hcard⟩
  exact hR s (by omega) hs

end Bourgain

end Lq

end FractalGeometry
