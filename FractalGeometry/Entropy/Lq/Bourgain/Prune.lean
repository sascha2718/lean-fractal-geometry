import Mathlib
import FractalGeometry.Entropy.Lq.Bourgain.Tree
import FractalGeometry.Entropy.Lq.Statements

open Finset

namespace FractalGeometry

namespace Lq

namespace Bourgain

def prunedSet (T S : ℕ) (A : Finset ℤ) (Keep : ℕ → ℤ → Finset ℤ) : Finset ℤ :=
  A.filter fun y => ∀ s < S, pre (S * T) ((s + 1) * T) y ∈ Keep s (pre (S * T) (s * T) y)

theorem kids_eq_image {M l l'' l' : ℕ} (h' : l'' ≤ l') (hM : l' ≤ M)
    (X : Finset ℤ) (c : ℤ) :
    kids M l l'' X c = (kids M l l' X c).image fun c' => c' / 2 ^ (l' - l'') := by
  unfold kids
  rw [image_image]
  refine image_congr fun y _ => ?_
  exact (pre_pre h' hM y).symm

section Selection

variable {T S : ℕ} {A : Finset ℤ} {Keep : ℕ → ℤ → Finset ℤ}

theorem exists_follow
    (hK : ∀ s < S, ∀ c, Keep s c ⊆ kids (S * T) (s * T) ((s + 1) * T) A c)
    (hKne : ∀ s < S, ∀ c ∈ A.image (pre (S * T) (s * T)), (Keep s c).Nonempty) :
    ∀ k ≤ S, ∀ c ∈ A.image (pre (S * T) ((S - k) * T)), ∃ y ∈ A,
      pre (S * T) ((S - k) * T) y = c ∧
      ∀ s', S - k ≤ s' → s' < S →
        pre (S * T) ((s' + 1) * T) y ∈ Keep s' (pre (S * T) (s' * T) y) := by
  intro k
  induction k with
  | zero =>
    intro _ c hc
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hc
    exact ⟨y, hy, rfl, fun s' h1 h2 => by omega⟩
  | succ k ih =>
    intro hk c hc
    set s := S - (k + 1) with hs
    have hsS : s < S := by omega
    have hs1 : S - k = s + 1 := by omega
    obtain ⟨c', hc'⟩ := hKne s hsS c hc
    have hc'kid := hK s hsS c hc'
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hc'kid
    obtain ⟨hzA, hzc⟩ := mem_cellOf.mp hz
    obtain ⟨y, hyA, hyz, hyfol⟩ := ih (by omega) (pre (S * T) ((s + 1) * T) z)
      (by rw [hs1]; exact mem_image_of_mem _ hzA)
    rw [hs1] at hyz hyfol
    have hle : s * T ≤ (s + 1) * T := Nat.mul_le_mul_right _ (Nat.le_succ s)
    have hleM : (s + 1) * T ≤ S * T := Nat.mul_le_mul_right _ hsS
    have hyc : pre (S * T) (s * T) y = c := by
      rw [← hzc]; exact pre_eq_of_pre_eq hle hleM hyz
    refine ⟨y, hyA, hyc, fun s' h1 h2 => ?_⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · rw [hyc, hyz]; exact hc'
    · exact hyfol s' (by omega) h2

theorem prunedSet_subset : prunedSet T S A Keep ⊆ A := filter_subset _ _

theorem kids_prunedSet
    (hK : ∀ s < S, ∀ c, Keep s c ⊆ kids (S * T) (s * T) ((s + 1) * T) A c)
    (hKne : ∀ s < S, ∀ c ∈ A.image (pre (S * T) (s * T)), (Keep s c).Nonempty)
    {s : ℕ} (hs : s < S) {x : ℤ} (hx : x ∈ prunedSet T S A Keep) :
    kids (S * T) (s * T) ((s + 1) * T) (prunedSet T S A Keep) (pre (S * T) (s * T) x) =
      Keep s (pre (S * T) (s * T) x) := by
  have hle : s * T ≤ (s + 1) * T := Nat.mul_le_mul_right _ (Nat.le_succ s)
  have hleM : (s + 1) * T ≤ S * T := Nat.mul_le_mul_right _ hs
  obtain ⟨hxA, hxfol⟩ := mem_filter.mp hx
  ext c'
  constructor
  · intro hc'
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hc'
    obtain ⟨hyH, hyc⟩ := mem_cellOf.mp hy
    have := (mem_filter.mp hyH).2 s hs
    rwa [hyc] at this
  · intro hc'
    obtain ⟨z, hz, rfl⟩ := mem_image.mp (hK s hs _ hc')
    obtain ⟨hzA, hzc⟩ := mem_cellOf.mp hz
    obtain ⟨y, hyA, hyz, hyfol⟩ := exists_follow hK hKne (S - (s + 1)) (by omega)
      (pre (S * T) ((s + 1) * T) z)
      (by rw [show S - (S - (s + 1)) = s + 1 by omega]; exact mem_image_of_mem _ hzA)
    rw [show S - (S - (s + 1)) = s + 1 by omega] at hyz hyfol
    have hyc : pre (S * T) (s * T) y = pre (S * T) (s * T) x := by
      rw [← hzc]; exact pre_eq_of_pre_eq hle hleM hyz
    refine mem_image.mpr ⟨y, mem_cellOf.mpr ⟨mem_filter.mpr ⟨hyA, fun s' hs' => ?_⟩, hyc⟩, hyz⟩
    rcases lt_trichotomy s' s with hlt | rfl | hgt
    ·
      have h1 : (s' + 1) * T ≤ s * T := Nat.mul_le_mul_right _ hlt
      have h2 : s * T ≤ S * T := Nat.mul_le_mul_right _ hs.le
      have h3 : s' * T ≤ (s' + 1) * T := Nat.mul_le_mul_right _ (Nat.le_succ s')
      rw [pre_eq_of_pre_eq h1 h2 hyc, pre_eq_of_pre_eq (h3.trans h1) h2 hyc]
      exact hxfol s' hs'
    · rw [hyc, hyz]; exact hc'
    · exact hyfol s' (by omega) hs'

theorem prunedSet_nonempty
    (hK : ∀ s < S, ∀ c, Keep s c ⊆ kids (S * T) (s * T) ((s + 1) * T) A c)
    (hKne : ∀ s < S, ∀ c ∈ A.image (pre (S * T) (s * T)), (Keep s c).Nonempty)
    (hne : A.Nonempty) : (prunedSet T S A Keep).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hyA, -, hyfol⟩ := exists_follow hK hKne S le_rfl _
    (mem_image_of_mem _ hx)
  exact ⟨y, mem_filter.mpr ⟨hyA, fun s hs => hyfol s (by omega) hs⟩⟩

end Selection

theorem card_le_two_mul_card_image_half (K : Finset ℤ) :
    K.card ≤ 2 * (K.image fun c => c / 2).card := by
  classical
  apply card_le_mul_card_image
  intro q _
  have hsub : K.filter (fun c => c / 2 = q) ⊆ {2 * q, 2 * q + 1} := by
    intro c hc
    have hq := (mem_filter.mp hc).2
    have h1 := Int.emod_nonneg c (by norm_num : (2 : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos c (by norm_num : (0 : ℤ) < 2)
    have h3 := Int.mul_ediv_add_emod c 2
    rw [hq] at h3
    simp only [mem_insert, mem_singleton]
    omega
  exact (card_le_card hsub).trans (card_insert_le _ _)

theorem exists_pruned {T S : ℕ} (hT : 1 ≤ T) {A : Finset ℤ} {R : ℕ → ℕ}
    (h : IsUnif T S A R) (hA : InUnit (S * T) A) (hne : A.Nonempty) (C : Finset ℕ) :
    ∃ H' ⊆ A, H'.card = ∏ s ∈ range S, (if s ∈ C then 1 else (R s + 1) / 2) ∧
      (∀ s < S, s ∈ C → ∀ x ∈ H', branching (S * T) (s * T) ((s + 1) * T) H' x = 1) ∧
      (∀ s < S, s ∉ C → ∀ x ∈ H',
        branching (S * T) (s * T) ((s + 1) * T - 1) H' x = (R s + 1) / 2 ∧
        branching (S * T) ((s + 1) * T - 1) ((s + 1) * T) H' x = 1) := by
  classical
  set M := S * T

  have hsel : ∀ s c, ∃ K ⊆ kids M (s * T) ((s + 1) * T) A c,
      Set.InjOn (fun c' => c' / 2) (K : Set ℤ) ∧
      (s < S → c ∈ A.image (pre M (s * T)) →
        K.card = if s ∈ C then 1 else (R s + 1) / 2) := by
    intro s c
    by_cases hc : s < S ∧ c ∈ A.image (pre M (s * T))
    · obtain ⟨hs, hcA⟩ := hc
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hcA
      have hR : (kids M (s * T) ((s + 1) * T) A (pre M (s * T) x)).card = R s := h s hs x hx
      set Kd := kids M (s * T) ((s + 1) * T) A (pre M (s * T) x)
      set P := Kd.image fun c' => c' / 2
      have hP : (R s + 1) / 2 ≤ P.card := by
        have h2 : Kd.card ≤ 2 * P.card := card_le_two_mul_card_image_half Kd
        rw [hR] at h2
        omega
      have hchild : ∀ q ∈ P, ∃ c' ∈ Kd, c' / 2 = q := fun q hq => by
        obtain ⟨c', hc', rfl⟩ := mem_image.mp hq
        exact ⟨c', hc', rfl⟩
      choose! child hchildK hchildq using hchild
      have hcount : (if s ∈ C then 1 else (R s + 1) / 2) ≤ P.card := by
        split_ifs
        · have hpos : 0 < Kd.card := by
            rw [hR]; exact (h.bounds hne s hs).1
          obtain ⟨c', hc'⟩ := card_pos.mp hpos
          exact card_pos.mpr ⟨_, mem_image_of_mem _ hc'⟩
        · exact hP
      obtain ⟨P', hP', hP'card⟩ := exists_subset_card_eq hcount
      have hinj : Set.InjOn child (P' : Set ℤ) := fun q₁ h₁ q₂ h₂ he => by
        rw [← hchildq q₁ (hP' h₁), ← hchildq q₂ (hP' h₂), he]
      refine ⟨P'.image child, fun c' hc' => ?_, ?_, fun _ _ => ?_⟩
      · obtain ⟨q, hq, rfl⟩ := mem_image.mp hc'
        exact hchildK q (hP' hq)
      · intro a ha b hb hab
        obtain ⟨q₁, h₁, rfl⟩ := mem_image.mp ha
        obtain ⟨q₂, h₂, rfl⟩ := mem_image.mp hb
        simp only at hab
        rw [hchildq q₁ (hP' h₁), hchildq q₂ (hP' h₂)] at hab
        rw [hab]
      · rw [card_image_of_injOn hinj, hP'card]
    · exact ⟨∅, empty_subset _, by simp, fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose Keep hKsub hKinj hKcard using hsel
  have hK : ∀ s < S, ∀ c, Keep s c ⊆ kids M (s * T) ((s + 1) * T) A c := fun s _ c => hKsub s c
  have hKne : ∀ s < S, ∀ c ∈ A.image (pre M (s * T)), (Keep s c).Nonempty := by
    intro s hs c hc
    rw [← card_pos, hKcard s c hs hc]
    split_ifs
    · norm_num
    · obtain ⟨x, hx, rfl⟩ := mem_image.mp hc
      have := (h.bounds hne s hs).1
      omega
  set H' := prunedSet T S A Keep
  have hkids : ∀ s < S, ∀ x ∈ H',
      kids M (s * T) ((s + 1) * T) H' (pre M (s * T) x) = Keep s (pre M (s * T) x) :=
    fun s hs x hx => kids_prunedSet hK hKne hs hx
  have hcardK : ∀ s < S, ∀ x ∈ H',
      (Keep s (pre M (s * T) x)).card = if s ∈ C then 1 else (R s + 1) / 2 :=
    fun s hs x hx => hKcard s _ hs (mem_image_of_mem _ (prunedSet_subset hx))
  have hunif : IsUnif T S H' fun s => if s ∈ C then 1 else (R s + 1) / 2 := by
    intro s hs x hx
    rw [branching_eq_card_kids, hkids s hs x hx, hcardK s hs x hx]
  have hne' : H'.Nonempty := prunedSet_nonempty hK hKne hne
  have hA' : InUnit (S * T) H' := fun x hx => hA x (prunedSet_subset hx)
  refine ⟨H', prunedSet_subset, hunif.card_eq hA' hne', fun s hs hsC x hx => ?_,
    fun s hs hsC x hx => ?_⟩
  · have := hunif s hs x hx
    simpa [hsC] using this
  · have hle : s * T ≤ (s + 1) * T - 1 := by
      rw [Nat.succ_mul]; omega
    have hle' : (s + 1) * T - 1 ≤ (s + 1) * T := Nat.sub_le _ _
    have hleM : (s + 1) * T ≤ M := Nat.mul_le_mul_right _ hs
    have hd : (s + 1) * T - ((s + 1) * T - 1) = 1 := by
      have : 1 ≤ (s + 1) * T := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    constructor
    · rw [branching_eq_card_kids, kids_eq_image hle' hleM, hkids s hs x hx, hd, pow_one,
        card_image_of_injOn (hKinj s _), hcardK s hs x hx,
        ite_eq_right_iff.mpr (fun h => absurd h hsC)]
    · rw [branching_eq_card_kids, card_eq_one]
      refine ⟨pre M ((s + 1) * T) x, ?_⟩
      ext c'
      simp only [mem_singleton]
      constructor
      · intro hc'
        obtain ⟨y, hy, rfl⟩ := mem_image.mp hc'
        obtain ⟨hyH, hyx⟩ := mem_cellOf.mp hy
        have hys : pre M (s * T) y = pre M (s * T) x := pre_eq_of_pre_eq hle (hle'.trans hleM) hyx
        have hyK := (mem_filter.mp hyH).2 s hs
        have hxK := (mem_filter.mp hx).2 s hs
        rw [hys] at hyK
        apply hKinj s _ hyK hxK
        have e1 := pre_pre hle' hleM y
        have e2 := pre_pre hle' hleM x
        rw [hd, pow_one] at e1 e2
        simp only
        rw [e1, e2, hyx]
      · rintro rfl
        exact mem_image.mpr ⟨x, mem_cellOf.mpr ⟨hx, rfl⟩, rfl⟩

end Bourgain

end Lq

end FractalGeometry
