import Mathlib
import FractalGeometry.Entropy.Lq.Statements

open Finset

namespace FractalGeometry

namespace Lq

namespace Bourgain

def InUnit (M : ℕ) (A : Finset ℤ) : Prop := ∀ x ∈ A, 0 ≤ x ∧ x < 2 ^ M

def IsUnif (L S : ℕ) (A : Finset ℤ) (R : ℕ → ℕ) : Prop :=
  ∀ s < S, ∀ x ∈ A, branching (S * L) (s * L) ((s + 1) * L) A x = R s

def pre (M l : ℕ) (x : ℤ) : ℤ := x / 2 ^ (M - l)

def cellOf (M l : ℕ) (A : Finset ℤ) (c : ℤ) : Finset ℤ := A.filter fun y => pre M l y = c

def kids (M l l' : ℕ) (A : Finset ℤ) (c : ℤ) : Finset ℤ := (cellOf M l A c).image (pre M l')

theorem branching_eq_card_kids (M l l' : ℕ) (A : Finset ℤ) (x : ℤ) :
    branching M l l' A x = (kids M l l' A (pre M l x)).card := rfl

theorem pre_pre {M l l' : ℕ} (h : l ≤ l') (h' : l' ≤ M) (x : ℤ) :
    pre M l' x / 2 ^ (l' - l) = pre M l x := by
  unfold pre
  rw [Int.ediv_ediv_of_nonneg (by positivity), ← pow_add]
  congr 2
  omega

theorem pre_self (M : ℕ) (x : ℤ) : pre M M x = x := by simp [pre]

theorem pre_zero {M : ℕ} {x : ℤ} (hx : 0 ≤ x ∧ x < 2 ^ M) : pre M 0 x = 0 := by
  unfold pre
  rw [Nat.sub_zero]
  exact Int.ediv_eq_zero_of_lt hx.1 hx.2

theorem pre_eq_of_pre_eq {M l l' : ℕ} (h : l ≤ l') (h' : l' ≤ M) {x y : ℤ}
    (hxy : pre M l' y = pre M l' x) : pre M l y = pre M l x := by
  rw [← pre_pre h h' x, ← pre_pre h h' y, hxy]

theorem mem_cellOf {M l : ℕ} {A : Finset ℤ} {c y : ℤ} :
    y ∈ cellOf M l A c ↔ y ∈ A ∧ pre M l y = c := mem_filter

theorem card_cellOf_eq_sum {M l l' : ℕ} (h : l ≤ l') (h' : l' ≤ M) (A : Finset ℤ) (c : ℤ) :
    (cellOf M l A c).card = ∑ c' ∈ kids M l l' A c, (cellOf M l' A c').card := by
  unfold kids
  rw [card_eq_sum_card_image (pre M l') (cellOf M l A c)]
  refine sum_congr rfl fun c' hc' => ?_
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hc'
  rw [mem_cellOf] at hy
  congr 1
  ext z
  simp only [mem_filter, mem_cellOf]
  constructor
  · rintro ⟨⟨hz, -⟩, hzy⟩
    exact ⟨hz, hzy⟩
  · rintro ⟨hz, hzy⟩
    exact ⟨⟨hz, by rw [pre_eq_of_pre_eq h h' hzy, hy.2]⟩, hzy⟩

def IsUnifFrom (L S s₁ : ℕ) (A : Finset ℤ) (R : ℕ → ℕ) : Prop :=
  ∀ s, s₁ ≤ s → s < S → ∀ x ∈ A, branching (S * L) (s * L) ((s + 1) * L) A x = R s

theorem IsUnif.unifFrom {L S : ℕ} {A : Finset ℤ} {R : ℕ → ℕ} (h : IsUnif L S A R) :
    IsUnifFrom L S 0 A R := fun s _ hs => h s hs

theorem IsUnifFrom.cell_card {L S s₁ : ℕ} {A : Finset ℤ} {R : ℕ → ℕ}
    (h : IsUnifFrom L S s₁ A R) :
    ∀ k, k ≤ S - s₁ → ∀ x ∈ A,
      (cellOf (S * L) ((S - k) * L) A (pre (S * L) ((S - k) * L) x)).card =
        ∏ s' ∈ Ico (S - k) S, R s' := by
  intro k
  induction k with
  | zero =>
    intro _ x hx
    simp only [Nat.sub_zero, Ico_self, prod_empty]
    rw [card_eq_one]
    refine ⟨x, ?_⟩
    ext y
    simp only [mem_cellOf, pre_self, mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl
      exact ⟨hx, rfl⟩
  | succ k ih =>
    intro hk x hx
    set s := S - (k + 1) with hs
    have hsS : s < S := by omega
    have hs1 : S - k = s + 1 := by omega
    have hle : s * L ≤ (s + 1) * L := Nat.mul_le_mul_right _ (Nat.le_succ s)
    have hleM : (s + 1) * L ≤ S * L := Nat.mul_le_mul_right _ hsS
    rw [card_cellOf_eq_sum hle hleM]
    have hkid : ∀ c' ∈ kids (S * L) (s * L) ((s + 1) * L) A (pre (S * L) (s * L) x),
        (cellOf (S * L) ((s + 1) * L) A c').card = ∏ s' ∈ Ico (s + 1) S, R s' := by
      intro c' hc'
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hc'
      have hyA := (mem_cellOf.mp hy).1
      have := ih (by omega) y hyA
      rwa [hs1] at this
    rw [sum_congr rfl hkid, sum_const, smul_eq_mul]
    have hb : (kids (S * L) (s * L) ((s + 1) * L) A (pre (S * L) (s * L) x)).card = R s :=
      h s (by omega) hsS x hx
    rw [hb, ← prod_eq_prod_Ico_succ_bot hsS]

theorem IsUnifFrom.cell_card' {L S s₁ : ℕ} {A : Finset ℤ} {R : ℕ → ℕ}
    (h : IsUnifFrom L S s₁ A R) {s : ℕ} (hs₁ : s₁ ≤ s) (hs : s ≤ S) {x : ℤ} (hx : x ∈ A) :
    (cellOf (S * L) (s * L) A (pre (S * L) (s * L) x)).card = ∏ s' ∈ Ico s S, R s' := by
  have := h.cell_card (S - s) (by omega) x hx
  rwa [Nat.sub_sub_self hs] at this

theorem IsUnif.cell_card' {L S : ℕ} {A : Finset ℤ} {R : ℕ → ℕ} (h : IsUnif L S A R) {s : ℕ}
    (hs : s ≤ S) {x : ℤ} (hx : x ∈ A) :
    (cellOf (S * L) (s * L) A (pre (S * L) (s * L) x)).card = ∏ s' ∈ Ico s S, R s' :=
  h.unifFrom.cell_card' (Nat.zero_le s) hs hx

theorem IsUnif.card_eq {L S : ℕ} {A : Finset ℤ} {R : ℕ → ℕ} (h : IsUnif L S A R)
    (hA : InUnit (S * L) A) (hne : A.Nonempty) : A.card = ∏ s ∈ range S, R s := by
  obtain ⟨x, hx⟩ := hne
  have := h.cell_card' (Nat.zero_le S) hx
  rw [zero_mul, ← range_eq_Ico] at this
  rw [← this]
  congr 1
  ext y
  simp only [mem_cellOf, iff_self_and]
  intro hy
  rw [pre_zero (hA y hy), pre_zero (hA x hx)]

theorem pre_of_mem_kids {M l l' : ℕ} (h : l ≤ l') (h' : l' ≤ M) {A : Finset ℤ} {c c' : ℤ}
    (hc' : c' ∈ kids M l l' A c) : c' / 2 ^ (l' - l) = c := by
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hc'
  rw [pre_pre h h', (mem_cellOf.mp hy).2]

theorem card_kids_le {M l l' : ℕ} (h : l ≤ l') (h' : l' ≤ M) (A : Finset ℤ) (c : ℤ) :
    (kids M l l' A c).card ≤ 2 ^ (l' - l) := by
  have hsub : kids M l l' A c ⊆ (Ico (0 : ℤ) (2 ^ (l' - l))).image
      (fun j => c * 2 ^ (l' - l) + j) := by
    intro c' hc'
    have hq := pre_of_mem_kids h h' hc'
    have hpos : (0 : ℤ) < 2 ^ (l' - l) := by positivity
    refine mem_image.mpr ⟨c' % 2 ^ (l' - l), mem_Ico.mpr ⟨Int.emod_nonneg _ hpos.ne',
      Int.emod_lt_of_pos _ hpos⟩, ?_⟩
    rw [← hq]
    linarith [Int.mul_ediv_add_emod c' (2 ^ (l' - l))]
  calc (kids M l l' A c).card ≤ _ := card_le_card hsub
    _ ≤ (Ico (0 : ℤ) (2 ^ (l' - l))).card := card_image_le
    _ = 2 ^ (l' - l) := by
      rw [Int.card_Ico, sub_zero, Int.toNat_pow_of_nonneg (by norm_num)]
      rfl

theorem IsUnif.bounds {L S : ℕ} {A : Finset ℤ} {R : ℕ → ℕ} (h : IsUnif L S A R)
    (hne : A.Nonempty) : ∀ s < S, 1 ≤ R s ∧ R s ≤ 2 ^ L := by
  intro s hs
  obtain ⟨x, hx⟩ := hne
  rw [← h s hs x hx, branching_eq_card_kids]
  have hle : s * L ≤ (s + 1) * L := Nat.mul_le_mul_right _ (Nat.le_succ s)
  have hleM : (s + 1) * L ≤ S * L := Nat.mul_le_mul_right _ hs
  refine ⟨card_pos.mpr ⟨pre (S * L) ((s + 1) * L) x, mem_image.mpr ⟨x, mem_cellOf.mpr ⟨hx, rfl⟩,
    rfl⟩⟩, ?_⟩
  have := card_kids_le hle hleM A (pre (S * L) (s * L) x)
  rwa [show (s + 1) * L - s * L = L by rw [Nat.succ_mul]; omega] at this

end Bourgain

end Lq

end FractalGeometry
