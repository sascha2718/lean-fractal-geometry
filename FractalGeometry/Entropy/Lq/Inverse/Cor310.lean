import Mathlib
import FractalGeometry.Entropy.Lq.Bourgain.Main
import FractalGeometry.Entropy.Lq.Inverse.Basic
import FractalGeometry.Entropy.Lq.Inverse.Trees
import FractalGeometry.Entropy.Lq.Statements
import FractalGeometry.Entropy.Lq.Theorem51

open Filter Topology

open scoped Pointwise

namespace FractalGeometry

namespace Lq

namespace Inverse

theorem branching_mono {M a b n n' : ℕ} {A A' : Finset ℤ} (hA : A' ⊆ A) (hna : n ≤ a)
    (hab : a ≤ b) (hbn : b ≤ n') (hn' : n' ≤ M) (x : ℤ) :
    branching M a b A' x ≤ branching M n n' A x := by
  classical
  unfold branching
  refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (f := (· / 2 ^ (n' - b))))
  intro c hc
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨hyA, hyx⟩ := Finset.mem_filter.mp hy
  refine Finset.mem_image.mpr ⟨y / 2 ^ (M - n'), Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr
    ⟨hA hyA, ?_⟩, rfl⟩, ediv_two_pow_ediv hbn hn' y⟩
  rw [← ediv_two_pow_ediv hna (le_trans hab (le_trans hbn hn')) y,
    ← ediv_two_pow_ediv hna (le_trans hab (le_trans hbn hn')) x, hyx]

theorem branching_scale {m k n n' : ℕ} (hn : n ≤ n') (hn' : n' ≤ m) (A : Finset ℤ) (x : ℤ) :
    branching (m + k) n n' (A.image (· * 2 ^ k)) (x * 2 ^ k) = branching m n n' A x := by
  classical
  unfold branching
  have e : ∀ z : ℤ, ∀ j ≤ m, z * 2 ^ k / 2 ^ (m + k - j) = z / 2 ^ (m - j) := by
    intro z j hj
    rw [show m + k - j = (m - j) + k by omega, pow_add, mul_comm z, mul_comm ((2 : ℤ) ^ (m - j))]
    exact Int.mul_ediv_mul_of_pos _ _ (by positivity)
  have hnm : n ≤ m := le_trans hn hn'
  congr 1
  ext c
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨y, ⟨⟨z, hz, rfl⟩, hzx⟩, rfl⟩
    refine ⟨z, ⟨hz, ?_⟩, (e z n' hn').symm⟩
    rw [e z n hnm, e x n hnm] at hzx
    exact hzx
  · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
    exact ⟨z * 2 ^ k, ⟨⟨z, hz, rfl⟩, by rw [e z n hnm, e x n hnm]; exact hzx⟩, e z n' hn'⟩

theorem card_cellsAt_mul {M a b : ℕ} (hab : a ≤ b) (hb : b ≤ M) {G : Finset ℤ} {c : ℕ}
    (h : ∀ x ∈ G, branching M a b G x = c) :
    (cellsAt M b G).card = c * (cellsAt M a G).card := by
  classical
  set g : ℤ → ℤ := fun z => z / 2 ^ (b - a)
  have hg : ∀ x : ℤ, g (x / 2 ^ (M - b)) = x / 2 ^ (M - a) := fun x => ediv_two_pow_ediv hab hb x
  have hmaps : ∀ z ∈ cellsAt M b G, g z ∈ cellsAt M a G := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    rw [hg]
    exact Finset.mem_image_of_mem _ hx
  rw [Finset.card_eq_sum_card_fiberwise hmaps, mul_comm]
  refine Finset.sum_const_nat fun z hz => ?_
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  rw [← h x hx]
  unfold branching
  congr 1
  ext z'
  simp only [cellsAt, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hyz⟩
    rw [hg] at hyz
    exact ⟨y, ⟨hy, hyz⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hyz⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, by rw [hg]; exact hyz⟩

theorem card_cellsAt_zero {M : ℕ} {G : Finset ℤ} (hG : InUnit M G) (hne : G.Nonempty) :
    (cellsAt M 0 G).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨0, ?_⟩
  ext c
  simp only [cellsAt, Finset.mem_image, Finset.mem_singleton, Nat.sub_zero]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Int.ediv_eq_zero_of_lt (hG x hx).1 (hG x hx).2
  · rintro rfl
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hx, Int.ediv_eq_zero_of_lt (hG x hx).1 (hG x hx).2⟩

theorem cellsAt_self (M : ℕ) (G : Finset ℤ) : cellsAt M M G = G := by
  unfold cellsAt
  rw [Nat.sub_self, pow_zero]
  simp

theorem card_eq_prod_of_blocks {T m₁ : ℕ} {G : Finset ℤ} (hG : InUnit (m₁ * T) G)
    (hne : G.Nonempty) {S : Finset ℕ} (hS : S ⊆ Finset.range m₁) {R n : ℕ → ℕ}
    (h2 : ∀ s < m₁, s ∉ S → ∀ x ∈ G, branching (m₁ * T) (s * T) ((s + 1) * T) G x = 1)
    (h3 : ∀ s ∈ S, s * T ≤ n s ∧ n s < (s + 1) * T ∧
      ∀ x ∈ G, branching (m₁ * T) (s * T) (n s) G x = R s ∧
        branching (m₁ * T) (n s) ((s + 1) * T) G x = 1) :
    G.card = ∏ s ∈ S, R s := by
  classical
  have key : ∀ s ≤ m₁, (cellsAt (m₁ * T) (s * T) G).card =
      ∏ s' ∈ S.filter (· < s), R s' := by
    intro s
    induction s with
    | zero =>
      intro _
      rw [zero_mul, card_cellsAt_zero hG hne]
      simp
    | succ s ih =>
      intro hs
      have hsT : (s + 1) * T ≤ m₁ * T := Nat.mul_le_mul_right T hs
      have hsT' : s * T ≤ (s + 1) * T := Nat.mul_le_mul_right T (Nat.le_succ s)
      have hfilt : S.filter (· < s + 1) =
          if s ∈ S then insert s (S.filter (· < s)) else S.filter (· < s) := by
        ext t
        split_ifs with h
        · simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨ht, hts⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hts with h' | h'
            · exact Or.inr ⟨ht, h'⟩
            · exact Or.inl h'
          · rintro (rfl | ⟨ht, hts⟩)
            · exact ⟨h, Nat.lt_succ_self _⟩
            · exact ⟨ht, Nat.lt_succ_of_lt hts⟩
        · simp only [Finset.mem_filter]
          constructor
          · rintro ⟨ht, hts⟩
            refine ⟨ht, ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hts with h' | h'
            · exact h'
            · exact absurd (h' ▸ ht) h
          · rintro ⟨ht, hts⟩
            exact ⟨ht, Nat.lt_succ_of_lt hts⟩
      rw [hfilt]
      split_ifs with h
      · obtain ⟨hn1, hn2, hbr⟩ := h3 s h
        rw [Finset.prod_insert (by simp), ← ih (by omega)]
        rw [card_cellsAt_mul hn2.le hsT fun x hx => (hbr x hx).2, one_mul,
          card_cellsAt_mul hn1 (le_trans hn2.le hsT) fun x hx => (hbr x hx).1]
      · rw [← ih (by omega), card_cellsAt_mul hsT' hsT (h2 s (by omega) h), one_mul]
  have := key m₁ le_rfl
  rw [cellsAt_self] at this
  rw [this]
  congr 1
  ext t
  simp only [Finset.mem_filter]
  exact ⟨fun h => h.1, fun h => ⟨h, Finset.mem_range.mp (hS h)⟩⟩

theorem two_pow_card_block_le {D s ns L : ℕ} {Rs : ℝ} (hD : 1 ≤ D) (hns1 : s * D ^ 2 ≤ ns)
    (hns2 : ns < (s + 1) * D ^ 2)
    (hR : (2 : ℝ) ^ ((1 - 1 / (D : ℝ)) * ((ns : ℝ) - s * ((D ^ 2 : ℕ) : ℝ))) < Rs) :
    (2 : ℝ) ^ (D * ((Finset.range L).filter fun u => u / D = s ∧ u * D < ns).card) ≤
      2 ^ (2 * D) * Rs := by
  classical
  set r := ns - s * D ^ 2 with hr
  have hrD : r < D ^ 2 := by
    have : (s + 1) * D ^ 2 = s * D ^ 2 + D ^ 2 := by ring
    omega
  set w := (r + D - 1) / D with hw
  have hD0 : 0 < D := hD
  set U := (Finset.range L).filter fun u => u / D = s ∧ u * D < ns with hU
  have hUw : U.card ≤ w := by
    have hsub : U ⊆ Finset.Ico (s * D) (s * D + w) := by
      intro u hu
      obtain ⟨-, hus, huD⟩ := Finset.mem_filter.mp hu
      have h1 : s * D ≤ u := by rw [← hus]; exact Nat.div_mul_le_self u D
      obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le h1
      refine Finset.mem_Ico.mpr ⟨h1, ?_⟩
      have h2 : v * D < r := by
        have : (s * D + v) * D = s * D ^ 2 + v * D := by ring
        omega
      have h3 : v + 1 ≤ w := by
        rw [hw, Nat.le_div_iff_mul_le hD0, add_mul, one_mul]
        omega
      omega
    calc U.card ≤ (Finset.Ico (s * D) (s * D + w)).card := Finset.card_le_card hsub
      _ = w := by rw [Nat.card_Ico, Nat.add_sub_cancel_left]
  have hDw : D * U.card ≤ r + D := by
    have : w * D ≤ r + D - 1 := Nat.div_mul_le_self _ _
    have : D * U.card ≤ D * w := Nat.mul_le_mul_left D hUw
    rw [mul_comm D w] at this
    omega
  have hRs : (2 : ℝ) ^ r ≤ 2 ^ D * Rs := by
    have hrR : ((ns : ℝ) - s * ((D ^ 2 : ℕ) : ℝ)) = (r : ℝ) := by
      rw [hr, Nat.cast_sub hns1]; push_cast; ring
    rw [hrR] at hR
    have hDR : (0 : ℝ) < D := by exact_mod_cast hD0
    have e : (2 : ℝ) ^ r = (2 : ℝ) ^ ((1 - 1 / (D : ℝ)) * r) * (2 : ℝ) ^ ((r : ℝ) / D) := by
      rw [← Real.rpow_add two_pos, ← Real.rpow_natCast]
      congr 1
      field_simp
      ring
    have h2 : (2 : ℝ) ^ ((r : ℝ) / D) ≤ 2 ^ D := by
      rw [← Real.rpow_natCast]
      refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
      rw [div_le_iff₀ hDR]
      have : (r : ℝ) ≤ (D : ℝ) ^ 2 := by exact_mod_cast hrD.le
      nlinarith
    rw [e, mul_comm (2 ^ D : ℝ)]
    exact mul_le_mul hR.le h2 (by positivity) (le_trans (by positivity) hR.le)
  calc (2 : ℝ) ^ (D * U.card) ≤ 2 ^ (r + D) := pow_le_pow_right₀ one_le_two hDw
    _ = 2 ^ r * 2 ^ D := pow_add _ _ _
    _ ≤ 2 ^ D * Rs * 2 ^ D := mul_le_mul_of_nonneg_right hRs (by positivity)
    _ = 2 ^ (2 * D) * Rs := by rw [two_mul, pow_add]; ring

theorem uniform_of_blocks {D m₁ : ℕ} (hD : 1 ≤ D) {η γ : ℝ} (hη : 0 < η) (hγ : 0 < γ)
    (h2D : 2 * ((D : ℝ) + 1) ≤ (2 : ℝ) ^ (γ * D)) {G : Finset ℤ} (hG : InUnit (m₁ * D ^ 2) G)
    (hne : G.Nonempty) {S : Finset ℕ} (hS : S ⊆ Finset.range m₁) {R n : ℕ → ℕ}
    (h2 : ∀ s < m₁, s ∉ S → ∀ x ∈ G,
      branching (m₁ * D ^ 2) (s * D ^ 2) ((s + 1) * D ^ 2) G x = 1)
    (h3 : ∀ s ∈ S, s * D ^ 2 ≤ n s ∧ n s < (s + 1) * D ^ 2 ∧
      (∀ x ∈ G, branching (m₁ * D ^ 2) (s * D ^ 2) (n s) G x = R s ∧
        branching (m₁ * D ^ 2) (n s) ((s + 1) * D ^ 2) G x = 1) ∧
      (2 : ℝ) ^ ((1 - 1 / (D : ℝ)) * ((n s : ℝ) - s * ((D ^ 2 : ℕ) : ℝ))) < R s) :
    ∃ G₁ ⊆ G, G₁.Nonempty ∧ ∃ R₁ : ℕ → ℕ, IsUniform D (m₁ * D) G₁ R₁ ∧
      (∀ u < m₁ * D, R₁ u = 1 ∨ (2 : ℝ) ^ ((1 - η) * D) ≤ R₁ u) ∧
      (G.card : ℝ) ≤ (2 : ℝ) ^ ((γ + (2 / D + γ) / η) * ((m₁ * D ^ 2 : ℕ) : ℝ)) * G₁.card := by
  classical
  have hD0 : 0 < D := hD
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD0
  have hM : m₁ * D * D = m₁ * D ^ 2 := by ring
  have hG' : InUnit (m₁ * D * D) G := by rw [hM]; exact hG
  obtain ⟨G'', hG''G, Rh, hG''R, hGcard⟩ := lemma_3_6 D (m₁ * D) hG'
  have hG''ne : G''.Nonempty := by
    rw [← Finset.card_pos]
    exact Nat.pos_of_mul_pos_left (lt_of_lt_of_le hne.card_pos hGcard)
  have hG'' : InUnit (m₁ * D * D) G'' := fun x hx => hG' x (hG''G hx)
  have hGprod : G.card = ∏ s ∈ S, R s :=
    card_eq_prod_of_blocks hG hne hS h2 fun s hs => ⟨(h3 s hs).1, (h3 s hs).2.1, (h3 s hs).2.2.1⟩

  set U := (Finset.range (m₁ * D)).filter fun u => u / D ∈ S ∧ u * D < n (u / D) with hU
  have hRone : ∀ u < m₁ * D, u ∉ U → Rh u = 1 := by
    intro u hu huU
    obtain ⟨x, hx⟩ := hG''ne
    have h1 := hG''R u hu x hx
    rw [hM] at h1
    set s := u / D with hs
    have hsm : s < m₁ := (Nat.div_lt_iff_lt_mul hD0).mpr hu
    have hsu : s * D ≤ u := Nat.div_mul_le_self u D
    have hus : u < s * D + D := Nat.lt_div_mul_add hD0
    have e1 : s * D ^ 2 ≤ u * D := by
      rw [pow_two, ← mul_assoc]; exact Nat.mul_le_mul_right D hsu
    have e2 : (u + 1) * D ≤ (s + 1) * D ^ 2 := by
      rw [pow_two, ← mul_assoc]; exact Nat.mul_le_mul_right D (by rw [add_mul, one_mul]; omega)
    have e3 : (s + 1) * D ^ 2 ≤ m₁ * D ^ 2 := Nat.mul_le_mul_right _ hsm
    have e4 : u * D ≤ (u + 1) * D := Nat.mul_le_mul_right D (Nat.le_succ u)
    refine le_antisymm ?_ (by rw [← h1]; exact branching_pos hx)
    rw [← h1]
    by_cases hsS : s ∈ S
    · have hns : n s ≤ u * D := by
        by_contra h
        exact huU (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hu, hsS, not_le.mp h⟩)
      exact le_trans (branching_mono hG''G hns e4 e2 e3 x)
        (le_of_eq ((h3 s hsS).2.2.1 x (hG''G hx)).2)
    · exact le_trans (branching_mono hG''G e1 e4 e2 e3 x) (le_of_eq (h2 s hsm hsS x (hG''G hx)))

  have hUbound : (2 : ℝ) ^ (D * U.card) ≤ (2 : ℝ) ^ (2 * D * m₁) * G.card := by
    have hmaps : ∀ u ∈ U, u / D ∈ S := fun u hu => (Finset.mem_filter.mp hu).2.1
    have hUcard := Finset.card_eq_sum_card_fiberwise hmaps
    have hfib : ∀ s ∈ S, U.filter (fun u => u / D = s) =
        (Finset.range (m₁ * D)).filter fun u => u / D = s ∧ u * D < n s := by
      intro s hs
      ext u
      simp only [hU, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hu, -, hun⟩, rfl⟩; exact ⟨hu, rfl, hun⟩
      · rintro ⟨hu, rfl, hun⟩; exact ⟨⟨hu, hs, hun⟩, rfl⟩
    rw [hUcard, Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum, hGprod, Nat.cast_prod]
    calc ∏ s ∈ S, (2 : ℝ) ^ (D * (U.filter fun u => u / D = s).card)
        ≤ ∏ s ∈ S, ((2 : ℝ) ^ (2 * D) * R s) := by
          refine Finset.prod_le_prod₀ (fun s _ => by positivity) fun s hs => ?_
          rw [hfib s hs]
          exact two_pow_card_block_le hD (h3 s hs).1 (h3 s hs).2.1 (h3 s hs).2.2.2
      _ = (2 : ℝ) ^ (2 * D * S.card) * ∏ s ∈ S, (R s : ℝ) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul, mul_comm (2 * D)]
      _ ≤ (2 : ℝ) ^ (2 * D * m₁) * ∏ s ∈ S, (R s : ℝ) := by
          refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two ?_)
            (Finset.prod_nonneg fun s _ => Nat.cast_nonneg _)
          have := Finset.card_le_card hS
          rw [Finset.card_range] at this
          exact Nat.mul_le_mul_left _ this

  set U' := (Finset.range (m₁ * D)).filter fun u => 1 < Rh u ∧ (Rh u : ℝ) < 2 ^ ((1 - η) * D)
    with hU'
  have hU'U : U' ⊆ U := by
    intro u hu
    obtain ⟨hur, h1, -⟩ := Finset.mem_filter.mp hu
    by_contra h
    have := hRone u (Finset.mem_range.mp hur) h
    omega
  have hUsub : U ⊆ Finset.range (m₁ * D) := Finset.filter_subset _ _
  have hRh1 := hG''R.one_le hG''ne
  have hRh2 := hG''R.le_two_pow hG''ne

  have hG''U : (G''.card : ℝ) * (2 : ℝ) ^ (η * D * U'.card) ≤ (2 : ℝ) ^ (D * U.card) := by
    have hprod : G''.card = (∏ u ∈ U \ U', Rh u) * ∏ u ∈ U', Rh u := by
      rw [hG''R.card_eq hG'' hG''ne, Finset.prod_sdiff hU'U]
      exact (Finset.prod_subset hUsub fun u hu huU => hRone u (Finset.mem_range.mp hu) huU).symm
    have h1 : ((∏ u ∈ U \ U', Rh u : ℕ) : ℝ) ≤ (2 : ℝ) ^ (D * (U \ U').card) := by
      rw [pow_mul]
      exact prod_le_pow_card_real fun u hu => by
        exact_mod_cast hRh2 u (Finset.mem_range.mp (hUsub (Finset.mem_sdiff.mp hu).1))
    have h2 : ((∏ u ∈ U', Rh u : ℕ) : ℝ) ≤ ((2 : ℝ) ^ ((1 - η) * D)) ^ U'.card :=
      prod_le_pow_card_real fun u hu => (Finset.mem_filter.mp hu).2.2.le
    have hcard := Finset.card_sdiff_add_card_eq_card hU'U
    rw [hprod, Nat.cast_mul]
    calc ((∏ u ∈ U \ U', Rh u : ℕ) : ℝ) * ((∏ u ∈ U', Rh u : ℕ) : ℝ) *
          (2 : ℝ) ^ (η * D * U'.card)
        ≤ (2 : ℝ) ^ (D * (U \ U').card) * ((2 : ℝ) ^ ((1 - η) * D)) ^ U'.card *
          (2 : ℝ) ^ (η * D * U'.card) := by
          gcongr
      _ = (2 : ℝ) ^ (D * U.card) := by
          rw [two_rpow_pow, ← Real.rpow_natCast, ← Real.rpow_add two_pos,
            ← Real.rpow_add two_pos, ← Real.rpow_natCast, ← hcard]
          congr 1
          push_cast
          ring

  have hU'bound : η * D * U'.card ≤ 2 * D * m₁ + γ * ((m₁ * D ^ 2 : ℕ) : ℝ) := by
    have hG''pos : (0 : ℝ) < G''.card := by exact_mod_cast hG''ne.card_pos
    have h6 : ((2 * (D + 1) : ℕ) : ℝ) ^ (m₁ * D) ≤ (2 : ℝ) ^ (γ * ((m₁ * D ^ 2 : ℕ) : ℝ)) := by
      calc ((2 * (D + 1) : ℕ) : ℝ) ^ (m₁ * D) ≤ ((2 : ℝ) ^ (γ * D)) ^ (m₁ * D) := by
            gcongr; push_cast; linarith
        _ = (2 : ℝ) ^ (γ * ((m₁ * D ^ 2 : ℕ) : ℝ)) := by
            rw [two_rpow_pow]; push_cast; ring_nf
    have hGG'' : (G.card : ℝ) ≤ ((2 * (D + 1) : ℕ) : ℝ) ^ (m₁ * D) * G''.card := by
      exact_mod_cast hGcard
    have key : (G''.card : ℝ) * (2 : ℝ) ^ (η * D * U'.card) ≤
        (G''.card : ℝ) * (2 : ℝ) ^ ((2 * D * m₁ : ℕ) + γ * ((m₁ * D ^ 2 : ℕ) : ℝ)) := by
      calc (G''.card : ℝ) * (2 : ℝ) ^ (η * D * U'.card) ≤ (2 : ℝ) ^ (D * U.card) := hG''U
        _ ≤ (2 : ℝ) ^ (2 * D * m₁) * G.card := hUbound
        _ ≤ (2 : ℝ) ^ (2 * D * m₁) * (((2 * (D + 1) : ℕ) : ℝ) ^ (m₁ * D) * G''.card) :=
            mul_le_mul_of_nonneg_left hGG'' (by positivity)
        _ ≤ (2 : ℝ) ^ (2 * D * m₁) * ((2 : ℝ) ^ (γ * ((m₁ * D ^ 2 : ℕ) : ℝ)) * G''.card) := by
            gcongr
        _ = (G''.card : ℝ) * (2 : ℝ) ^ ((2 * D * m₁ : ℕ) + γ * ((m₁ * D ^ 2 : ℕ) : ℝ)) := by
            rw [Real.rpow_add two_pos, Real.rpow_natCast]; ring
    have := le_of_mul_le_mul_left key hG''pos
    rw [Real.rpow_le_rpow_left_iff one_lt_two] at this
    push_cast at this ⊢
    linarith

  obtain ⟨G₁, hG₁G'', hG₁ne, hG₁R⟩ := lemma_3_7 hG'' hG''ne hG''R U'
  have hG₁ : InUnit (m₁ * D * D) G₁ := fun x hx => hG'' x (hG₁G'' hx)
  refine ⟨G₁, hG₁G''.trans hG''G, hG₁ne, _, hG₁R, fun u hu => ?_, ?_⟩
  · by_cases huU' : u ∈ U'
    · left; exact ite_eq_of_pos huU'
    · rw [ite_eq_of_neg huU']
      by_cases h1 : Rh u = 1
      · left; exact h1
      · right
        by_contra h2
        push Not at h2
        have := hRh1 u hu
        exact huU' (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hu, by omega, h2⟩)
  ·
    have h1 := prod_eq_prod_ite_mul (m₁ * D) U' Rh
    rw [← hG''R.card_eq hG'' hG''ne, ← hG₁R.card_eq hG₁ hG₁ne] at h1
    have hU'r : (Finset.range (m₁ * D)).filter (· ∈ U') = U' := by
      rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]
    rw [hU'r] at h1
    have h2 : ((∏ u ∈ U', Rh u : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((D : ℝ) * U'.card) := by
      calc ((∏ u ∈ U', Rh u : ℕ) : ℝ) ≤ ((2 : ℝ) ^ (D : ℝ)) ^ U'.card :=
            prod_le_pow_card_real fun u hu => by
              rw [Real.rpow_natCast]
              exact_mod_cast hRh2 u (Finset.mem_range.mp (Finset.mem_filter.mp hu).1)
        _ = (2 : ℝ) ^ ((D : ℝ) * U'.card) := two_rpow_pow _ _
    have hG''G₁ : (G''.card : ℝ) ≤ G₁.card * (2 : ℝ) ^ ((D : ℝ) * U'.card) := by
      rw [h1, Nat.cast_mul]
      exact mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
    have hGG'' : (G.card : ℝ) ≤ (2 : ℝ) ^ (γ * ((m₁ * D ^ 2 : ℕ) : ℝ)) * G''.card := by
      have : (G.card : ℝ) ≤ ((2 * (D + 1) : ℕ) : ℝ) ^ (m₁ * D) * G''.card := by
        exact_mod_cast hGcard
      refine le_trans this (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
      calc ((2 * (D + 1) : ℕ) : ℝ) ^ (m₁ * D) ≤ ((2 : ℝ) ^ (γ * D)) ^ (m₁ * D) := by
            gcongr; push_cast; linarith
        _ = (2 : ℝ) ^ (γ * ((m₁ * D ^ 2 : ℕ) : ℝ)) := by
            rw [two_rpow_pow]; push_cast; ring_nf
    have hDU' : (D : ℝ) * U'.card ≤ (2 / D + γ) / η * ((m₁ * D ^ 2 : ℕ) : ℝ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hη]
      have e : (2 / (D : ℝ) + γ) * ((m₁ * D ^ 2 : ℕ) : ℝ) =
          2 * D * m₁ + γ * ((m₁ * D ^ 2 : ℕ) : ℝ) := by
        push_cast; field_simp
      rw [e]; nlinarith
    calc (G.card : ℝ) ≤ (2 : ℝ) ^ (γ * ((m₁ * D ^ 2 : ℕ) : ℝ)) * G''.card := hGG''
      _ ≤ (2 : ℝ) ^ (γ * ((m₁ * D ^ 2 : ℕ) : ℝ)) * (G₁.card * (2 : ℝ) ^ ((D : ℝ) * U'.card)) :=
          mul_le_mul_of_nonneg_left hG''G₁ (by positivity)
      _ ≤ (2 : ℝ) ^ (γ * ((m₁ * D ^ 2 : ℕ) : ℝ)) * (G₁.card *
            (2 : ℝ) ^ ((2 / D + γ) / η * ((m₁ * D ^ 2 : ℕ) : ℝ))) := by
          gcongr; exact one_le_two
      _ = (2 : ℝ) ^ ((γ + (2 / D + γ) / η) * ((m₁ * D ^ 2 : ℕ) : ℝ)) * G₁.card := by
          rw [add_mul, Real.rpow_add two_pos]; ring

theorem eventually_logb_div_sqrt_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ D : ℕ in atTop,
      2 * Real.logb 2 ((D ^ 2 : ℕ) : ℝ) / Real.sqrt ((D ^ 2 : ℕ) : ℝ) ≤ c := by
  have h := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    tendsto_natCast_atTop_atTop).const_mul (4 / Real.log 2)
  rw [mul_zero] at h
  filter_upwards [h.eventually (gt_mem_nhds hc), eventually_ge_atTop 1] with D hD hD1
  simp only [Function.comp, pow_one, one_mul, add_zero] at hD
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD1
  have e : 2 * Real.logb 2 ((D ^ 2 : ℕ) : ℝ) / Real.sqrt ((D ^ 2 : ℕ) : ℝ) =
      4 / Real.log 2 * (Real.log D / D) := by
    push_cast
    rw [Real.sqrt_sq hDR.le, Real.logb_pow, Real.logb]
    field_simp
    ring
  rw [e]
  exact hD.le

theorem corollary_3_10 (h31 : Bourgain.Theorem31Weak) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∀ᶠ D : ℕ in atTop, ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ ℓ : ℕ in atTop, ∀ H : Finset ℤ,
      InUnit (ℓ * D) H → H.Nonempty →
      ((H + H).card : ℝ) ≤ (2 : ℝ) ^ (σ * (ℓ * D : ℕ)) * H.card →
      ∃ H' ⊆ H, H'.Nonempty ∧ ∃ R : ℕ → ℕ, IsUniform D ℓ H' R ∧
        (∀ s < ℓ, R s = 1 ∨ (2 : ℝ) ^ ((1 - η) * D) ≤ R s) ∧
        (2 : ℝ) ^ (-(η * (ℓ * D : ℕ))) * H.card ≤ H'.card := by
  classical
  set γ : ℝ := η ^ 2 / 16 with hγ
  have hγ0 : 0 < γ := by positivity
  have hsq : Tendsto (fun D : ℕ => D ^ 2) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun D hD => le_trans hD (Nat.le_self_pow two_ne_zero D)⟩
  filter_upwards [hsq.eventually h31, eventually_linear_le_two_rpow 2 hγ0,
    eventually_logb_div_sqrt_le (by positivity : (0 : ℝ) < η / 8),
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (32 / η ^ 2)),
    eventually_ge_atTop 1] with D h31D h2D hlogD hDη hD1
  obtain ⟨σ, hσ, h31D⟩ := h31D
  refine ⟨σ, hσ, ?_⟩
  have hD0 : 0 < D := hD1
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD0
  have hm₁ : Tendsto (fun ℓ : ℕ => ℓ / D + 1) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b * D, fun ℓ hℓ => by
      have := (Nat.le_div_iff_mul_le hD0).mpr hℓ; omega⟩
  filter_upwards [hm₁.eventually h31D, eventually_ge_atTop D] with ℓ h31ℓ hℓD
  intro H hH hHne hdbl
  obtain ⟨m₁, hm₁def⟩ : ∃ m₁, m₁ = ℓ / D + 1 := ⟨_, rfl⟩
  rw [← hm₁def] at h31ℓ
  have hℓ1 : ℓ < m₁ * D := by
    rw [hm₁def, add_mul, one_mul]; exact Nat.lt_div_mul_add hD0
  have hℓ2 : m₁ * D ≤ ℓ + D := by
    rw [hm₁def, add_mul, one_mul]; have := Nat.div_mul_le_self ℓ D; omega
  have hlM : ℓ * D ≤ m₁ * D ^ 2 := by
    rw [pow_two, ← mul_assoc]; exact Nat.mul_le_mul_right D hℓ1.le
  obtain ⟨k, hMk⟩ : ∃ k, m₁ * D ^ 2 = ℓ * D + k := ⟨m₁ * D ^ 2 - ℓ * D, by omega⟩
  have hM2 : ((m₁ * D ^ 2 : ℕ) : ℝ) ≤ 2 * ((ℓ * D : ℕ) : ℝ) := by
    have : m₁ * D ^ 2 ≤ 2 * (ℓ * D) := by
      rw [pow_two, ← mul_assoc]
      calc m₁ * D * D ≤ (ℓ + D) * D := Nat.mul_le_mul_right D hℓ2
        _ ≤ 2 * (ℓ * D) := by nlinarith
    exact_mod_cast this

  set Hs := H.image (· * (2 : ℤ) ^ k) with hHs
  have hinj : Set.InjOn (· * (2 : ℤ) ^ k) (H : Set ℤ) := fun a _ b _ h =>
    mul_right_cancel₀ (by positivity) h
  have hHscard : Hs.card = H.card := Finset.card_image_of_injOn hinj
  have hHsunit : InUnit (m₁ * D ^ 2) Hs := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have := hH x hx
    rw [hMk, pow_add]
    exact ⟨mul_nonneg this.1 (by positivity), mul_lt_mul_of_pos_right this.2 (by positivity)⟩
  have hsumimg : Hs + Hs = (H + H).image (· * (2 : ℤ) ^ k) := by
    ext z
    simp only [Finset.mem_add, Finset.mem_image, hHs]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨x + y, ⟨x, hx, y, hy, rfl⟩, by ring⟩
    · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, by ring⟩
  have hHsdbl : ((Hs + Hs).card : ℝ) ≤ (2 : ℝ) ^ (σ * ((m₁ * D ^ 2 : ℕ) : ℝ)) * Hs.card := by
    have hcard2 : (Hs + Hs).card = (H + H).card := by
      rw [hsumimg]
      exact Finset.card_image_of_injective _ fun a b h => mul_right_cancel₀
        (by positivity : (2 : ℤ) ^ k ≠ 0) h
    rw [hcard2, hHscard]
    refine le_trans hdbl (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le one_le_two
      ?_) (Nat.cast_nonneg _))
    have : ((ℓ * D : ℕ) : ℝ) ≤ ((m₁ * D ^ 2 : ℕ) : ℝ) := by exact_mod_cast hlM
    exact mul_le_mul_of_nonneg_left this hσ.le

  obtain ⟨G, hGHs, S, hS, R, n, hGsize, hG2, hG3⟩ := h31ℓ Hs hHsunit hHsdbl
  have hG : InUnit (m₁ * D ^ 2) G := fun x hx => hHsunit x (hGHs hx)
  have hHpos : (0 : ℝ) < H.card := by exact_mod_cast hHne.card_pos
  have hGne : G.Nonempty := by
    rw [← Finset.card_pos]
    have hHs0 : (0 : ℝ) < Hs.card := by rw [hHscard]; exact hHpos
    have : (0 : ℝ) < G.card := lt_of_lt_of_le (mul_pos (by positivity) hHs0) hGsize
    exact_mod_cast this
  have hsqrt : Real.sqrt ((D ^ 2 : ℕ) : ℝ) = D := by
    push_cast; exact Real.sqrt_sq hDR.le
  obtain ⟨G₁, hG₁G, hG₁ne, R₁, hG₁R, hdich, hGG₁⟩ := uniform_of_blocks hD1 hη hγ0 h2D hG hGne hS
    hG2 fun s hs => by
      obtain ⟨h1, h2, h3, h4, -⟩ := hG3 s hs
      exact ⟨h1, h2, h3, by rw [hsqrt] at h4; exact h4⟩

  set H₁ := H.filter fun x => x * (2 : ℤ) ^ k ∈ G₁ with hH₁
  have hH₁img : H₁.image (· * (2 : ℤ) ^ k) = G₁ := by
    ext y
    rw [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (Finset.mem_filter.mp hx).2
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hGHs (hG₁G hy))
      exact ⟨x, Finset.mem_filter.mpr ⟨hx, hy⟩, rfl⟩
  have hH₁card : H₁.card = G₁.card := by
    rw [← hH₁img]
    exact (Finset.card_image_of_injOn fun a ha b hb h => hinj (Finset.mem_filter.mp ha).1
      (Finset.mem_filter.mp hb).1 h).symm
  refine ⟨H₁, Finset.filter_subset _ _, ?_, R₁, ?_, fun s hs => hdich s (by omega), ?_⟩
  · rw [← Finset.card_pos, hH₁card]; exact hG₁ne.card_pos
  · intro s hs x hx
    have hsD : (s + 1) * D ≤ ℓ * D := Nat.mul_le_mul_right D hs
    have hsD' : s * D ≤ (s + 1) * D := Nat.mul_le_mul_right D (Nat.le_succ s)
    rw [← branching_scale (k := k) hsD' hsD, hH₁img, ← hMk,
      show m₁ * D ^ 2 = m₁ * D * D by ring]
    exact hG₁R s (by omega) _ ((Finset.mem_filter.mp hx).2)
  ·
    have hX : 2 * Real.logb 2 ((D ^ 2 : ℕ) : ℝ) / Real.sqrt ((D ^ 2 : ℕ) : ℝ) +
        (γ + (2 / D + γ) / η) ≤ η / 2 := by
      have h2D' : 2 / (D : ℝ) ≤ η ^ 2 / 16 := by
        rw [div_le_iff₀ hDR]
        rw [div_le_iff₀ (by positivity)] at hDη
        nlinarith
      have h3 : (2 / (D : ℝ) + γ) / η ≤ η / 8 := by
        rw [div_le_iff₀ hη, hγ]; nlinarith
      have h4 : γ ≤ η / 16 := by rw [hγ]; nlinarith
      linarith
    set X := 2 * Real.logb 2 ((D ^ 2 : ℕ) : ℝ) / Real.sqrt ((D ^ 2 : ℕ) : ℝ) with hXdef
    have hX0 : 0 ≤ X := by
      rw [hXdef]
      have : 0 ≤ Real.logb 2 ((D ^ 2 : ℕ) : ℝ) := Real.logb_nonneg one_lt_two (by
        have : (1 : ℝ) ≤ ((D ^ 2 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow _ _ hD0
        exact this)
      positivity
    have hHG : (H.card : ℝ) ≤ (2 : ℝ) ^ (X * ((m₁ * D ^ 2 : ℕ) : ℝ)) * G.card := by
      have h1 := mul_le_mul_of_nonneg_left hGsize (by positivity :
        (0 : ℝ) ≤ (2 : ℝ) ^ (X * ((m₁ * D ^ 2 : ℕ) : ℝ)))
      rw [← mul_assoc, ← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero, one_mul,
        hHscard] at h1
      exact h1
    have hHH₁ : (H.card : ℝ) ≤ (2 : ℝ) ^ ((X + (γ + (2 / D + γ) / η)) *
        ((m₁ * D ^ 2 : ℕ) : ℝ)) * H₁.card := by
      rw [hH₁card, add_mul, Real.rpow_add two_pos, mul_assoc]
      exact le_trans hHG (mul_le_mul_of_nonneg_left hGG₁ (by positivity))
    have hexp : (X + (γ + (2 / D + γ) / η)) * ((m₁ * D ^ 2 : ℕ) : ℝ) ≤ η * ((ℓ * D : ℕ) : ℝ) := by
      have hpos : 0 ≤ X + (γ + (2 / D + γ) / η) := by positivity
      calc (X + (γ + (2 / D + γ) / η)) * ((m₁ * D ^ 2 : ℕ) : ℝ)
          ≤ η / 2 * (2 * ((ℓ * D : ℕ) : ℝ)) := mul_le_mul hX hM2 (Nat.cast_nonneg _) (by positivity)
        _ = η * ((ℓ * D : ℕ) : ℝ) := by ring
    calc (2 : ℝ) ^ (-(η * ((ℓ * D : ℕ) : ℝ))) * H.card
        ≤ (2 : ℝ) ^ (-(η * ((ℓ * D : ℕ) : ℝ))) * ((2 : ℝ) ^ ((X + (γ + (2 / D + γ) / η)) *
          ((m₁ * D ^ 2 : ℕ) : ℝ)) * H₁.card) := mul_le_mul_of_nonneg_left hHH₁ (by positivity)
      _ ≤ (2 : ℝ) ^ (-(η * ((ℓ * D : ℕ) : ℝ))) * ((2 : ℝ) ^ (η * ((ℓ * D : ℕ) : ℝ)) * H₁.card) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le one_le_two hexp) (Nat.cast_nonneg _)) (by positivity)
      _ = H₁.card := by
          rw [← mul_assoc, ← Real.rpow_add two_pos, neg_add_cancel, Real.rpow_zero, one_mul]

end Inverse

end Lq

end FractalGeometry
