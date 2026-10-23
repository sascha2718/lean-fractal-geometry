import Mathlib
import FractalGeometry.Entropy.Lq.BSG.Basic
import FractalGeometry.Entropy.Lq.BSG.Graph

open Finset

open scoped Pointwise

namespace FractalGeometry.Lq.BSG

noncomputable def thr (ε : ℝ) (j : ℕ) : ℝ := 2 * (ε / 4) ^ (2 ^ j)

lemma thr_zero (ε : ℝ) : thr ε 0 = ε / 2 := by
  simp only [thr, pow_zero, pow_one]; ring

lemma thr_succ (ε : ℝ) (j : ℕ) : thr ε (j + 1) = thr ε j ^ 2 / 2 := by
  simp only [thr, pow_succ, pow_mul]; ring

lemma thr_pos {ε : ℝ} (hε : 0 < ε) (j : ℕ) : 0 < thr ε j := by
  unfold thr; positivity

lemma thr_anti {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {i j : ℕ} (hij : i ≤ j) :
    thr ε j ≤ thr ε i := by
  unfold thr
  have h := pow_le_pow_of_le_one (a := ε / 4) (by positivity) (by linarith)
    (Nat.pow_le_pow_right (n := 2) (by norm_num) hij)
  linarith

noncomputable def lev (ε : ℝ) (J : ℕ) : ℝ := (ε / 4) ^ (2 ^ J)

noncomputable def gam (ε : ℝ) (J m : ℕ) : ℝ := lev ε J / (m + 1)

noncomputable def kay (ε M : ℝ) (J m : ℕ) : ℝ := 2 ^ 33 * M ^ 6 / gam ε J m ^ 12

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

structure IsChain (A B : Finset G) (ε : ℝ) (m : ℕ) (C : ℕ → Finset G) (n : ℕ) : Prop where
  zero : C 0 = B
  nonempty : ∀ j ≤ n, (C j).Nonempty
  sym : ∀ j < n, ∀ x ∈ C (j + 1), thr ε j * #A ≤ rep A x
  reg : ∀ j < n, ∀ x ∈ C (j + 1),
    thr ε j / (2 * (m + 1)) * #(C j) ^ 2 ≤ #(C (j + 1)) * rep (C j) x

lemma level_pairs {A B : Finset G} (hA : A.Nonempty) {ε : ℝ} (hε : 0 < ε)
    (hE : ε * #A * #B ^ 2 ≤ addEnergy A B) {m : ℕ} {C : ℕ → Finset G} {n : ℕ}
    (hC : IsChain A B ε m C n) :
    thr ε n * #(C n) ^ 2 ≤ #{p ∈ C n ×ˢ C n | thr ε n * #A ≤ rep A (p.1 - p.2)} := by
  cases n with
  | zero =>
    rw [hC.zero, thr_zero]
    exact energy_pairs A B hA hε.le hE
  | succ k =>
    rw [thr_succ]
    exact sym_pairs A (C (k + 1)) hA (thr_pos hε k).le (hC.sym k (Nat.lt_succ_self k))

lemma exists_chain {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty) {ε : ℝ} (hε : 0 < ε)
    (hE : ε * #A * #B ^ 2 ≤ addEnergy A B) {m : ℕ} (hN : ∀ S : Finset G, #S ≤ 2 ^ m) :
    ∀ n, ∃ C : ℕ → Finset G, IsChain A B ε m C n := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun _ => B, rfl, fun j hj => ?_, fun j hj => (Nat.not_lt_zero _ hj).elim,
      fun j hj => (Nat.not_lt_zero _ hj).elim⟩
    exact hB
  | succ n ih =>
    obtain ⟨C, hC⟩ := ih
    obtain ⟨V, hVne, hVsym, hVreg⟩ := regularize A (C n) m (hN _) (thr_pos hε n)
      (hC.nonempty n le_rfl) (level_pairs hA hε hE hC)
    classical
    refine ⟨fun j => if j = n + 1 then V else C j, ?_, ?_, ?_, ?_⟩
    · rw [ite_eq_right (by omega)]; exact hC.zero
    · intro j hj
      by_cases h : j = n + 1
      · rw [ite_eq_left h]; exact hVne
      · rw [ite_eq_right h]; exact hC.nonempty j (by omega)
    · intro j hj x hx
      by_cases h : j = n
      · subst h
        rw [ite_eq_left rfl] at hx
        exact hVsym x hx
      · rw [ite_eq_right (by omega)] at hx
        exact hC.sym j (by omega) x hx
    · intro j hj x hx
      by_cases h : j = n
      · subst h
        rw [ite_eq_left rfl] at hx ⊢
        rw [ite_eq_right (by omega)]
        exact hVreg x hx
      · rw [ite_eq_right (by omega)] at hx ⊢
        rw [ite_eq_right (by omega)]
        exact hC.reg j (by omega) x hx

lemma exists_small_ratio {α : Type*} (C : ℕ → Finset α) {J : ℕ} (hJ : 1 ≤ J)
    (hne : (C 1).Nonempty) {M N : ℝ}
    (hM : 0 < M) (hMJ : N ≤ M ^ J) (hN : (#(C (J + 1)) : ℝ) ≤ N) :
    ∃ j, 1 ≤ j ∧ j ≤ J ∧ (#(C (j + 1)) : ℝ) ≤ M * #(C j) := by
  by_contra! h
  have key : ∀ k, k ≤ J → M ^ k * #(C 1) ≤ #(C (k + 1)) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := h (k + 1) (by omega) hk
      calc M ^ (k + 1) * #(C 1) = M * (M ^ k * #(C 1)) := by ring
        _ ≤ M * #(C (k + 1)) := by gcongr
        _ ≤ _ := h2.le
  obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
  have h1 := key J' (by omega)
  have h2 := h (J' + 1) (by omega) le_rfl
  have h3 : (1 : ℝ) ≤ #(C 1) := by exact_mod_cast hne.card_pos
  have h4 : M ^ (J' + 1) * #(C 1) < #(C (J' + 1 + 1)) := by
    calc M ^ (J' + 1) * #(C 1) = M * (M ^ J' * #(C 1)) := by ring
      _ ≤ M * #(C (J' + 1)) := by gcongr
      _ < _ := h2
  have h5 : M ^ (J' + 1) ≤ M ^ (J' + 1) * #(C 1) := by
    have : 0 < M ^ (J' + 1) := by positivity
    nlinarith
  linarith

lemma backprop {A B : Finset G} {ε : ℝ} {m n : ℕ} {C : ℕ → Finset G}
    (hC : IsChain A B ε m C n) (S : Finset G) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : ∀ l < n, γ ≤ thr ε l / (2 * (m + 1))) :
    ∀ j ≤ n, ∀ β : ℝ, 0 ≤ β → ∀ x : G, β * #(C j) ≤ #{u ∈ C j | u - x ∈ S} →
      ∃ y : G, β * γ ^ j * #B ≤ #{b ∈ B | b - y ∈ S} := by
  intro j
  induction j with
  | zero =>
    intro _ β _ x hx
    rw [hC.zero] at hx
    exact ⟨x, by simpa using hx⟩
  | succ k ih =>
    intro hk β hβ x hx
    have hreg : ∀ z ∈ C (k + 1), γ * #(C k) ^ 2 ≤ #(C (k + 1)) * rep (C k) z := by
      intro z hz
      calc γ * #(C k) ^ 2 ≤ thr ε k / (2 * (m + 1)) * #(C k) ^ 2 := by
            gcongr; exact hγ k (by omega)
        _ ≤ _ := hC.reg k (by omega) z hz
    obtain ⟨y, hy⟩ := backprop_step (C k) (C (k + 1)) S hγ0 (hC.nonempty (k + 1) hk) hreg x hx
    obtain ⟨y', hy'⟩ := ih (by omega) (β * γ) (by positivity) y hy
    exact ⟨y', by rw [pow_succ]; linarith [show β * γ ^ k * γ = β * γ * γ ^ k by ring]⟩

lemma card_nsmul_sub_nsmul_le {H : Finset G} (hH : H.Nonempty) {K : ℝ}
    (hK : (#(H - H) : ℝ) ≤ K * #H) (n : ℕ) :
    (#(n • H - n • H) : ℝ) ≤ K ^ (2 * n) * #H := by
  have h := pluennecke_ruzsa_inequality_nsmul_sub_nsmul_sub hH H n n
  have hH0 : (0 : ℝ) < #H := by exact_mod_cast hH.card_pos
  have h' : (#(n • H - n • H) : ℝ) ≤ ((#(H - H) : ℝ) / #H) ^ (n + n) * #H := by
    have h2 := (NNRat.cast_le (K := ℝ)).2 h
    push_cast at h2
    exact h2
  have hK' : (#(H - H) : ℝ) / #H ≤ K := by rwa [div_le_iff₀ hH0]
  calc (#(n • H - n • H) : ℝ) ≤ ((#(H - H) : ℝ) / #H) ^ (n + n) * #H := h'
    _ ≤ K ^ (n + n) * #H := by gcongr
    _ = K ^ (2 * n) * #H := by rw [two_mul]

theorem core (A B : Finset G) (hA : A.Nonempty) (hB : B.Nonempty) (m : ℕ)
    (hN : ∀ S : Finset G, #S ≤ 2 ^ m) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hE : ε * #A * #B ^ 2 ≤ addEnergy A B) {J : ℕ} (hJ : 1 ≤ J) {M : ℝ} (hM : 1 ≤ M)
    (hMJ : (2 : ℝ) ^ m ≤ M ^ J) :
    ∃ H X : Finset G, #(H + H) ≤ 4 * kay ε M J m ^ 8 * #H ∧
      lev ε J * #A ≤ #(A ∩ (X + H)) ∧
      #X * #H ≤ 2 * kay ε M J m ^ 4 / lev ε J * #A ∧
      gam ε J m ^ (J + 1) / 6 * #B ≤ #(B ∩ H) := by
  classical

  obtain ⟨C, hC⟩ := exists_chain hA hB hε hE hN (J + 1)
  have hM0 : 0 < M := by linarith
  obtain ⟨j, hj1, hjJ, hratio⟩ := exists_small_ratio C hJ (hC.nonempty 1 (by omega)) hM0 hMJ
    (by exact_mod_cast hN (C (J + 1)))
  have hlev : 0 < lev ε J := by unfold lev; positivity
  have hγpos : 0 < gam ε J m := by unfold gam; positivity
  have hthrJ : thr ε J = 2 * lev ε J := rfl
  have hγle : ∀ l ≤ J, gam ε J m ≤ thr ε l / (2 * (m + 1)) := by
    intro l hl
    have h := thr_anti hε hε1 hl
    rw [hthrJ] at h
    unfold gam
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hγ1 : gam ε J m ≤ 1 := by
    unfold gam lev
    rw [div_le_one (by positivity)]
    have : (ε / 4) ^ 2 ^ J ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
    have : (0 : ℝ) ≤ m := by positivity
    linarith
  set γ := gam ε J m with hγdef
  set U := C j with hU
  set V := C (j + 1) with hV
  have hUne : U.Nonempty := hC.nonempty j (by omega)

  have hpairs : γ * #U ^ 2 ≤ #{p ∈ U ×ˢ U | p.1 - p.2 ∈ V} := by
    rw [card_pairs_sub_mem]
    push_cast
    have hVne : V.Nonempty := hC.nonempty (j + 1) (by omega)
    have hV0 : (0 : ℝ) < #V := by exact_mod_cast hVne.card_pos
    have hx : ∀ x ∈ V, γ * #U ^ 2 / #V ≤ (rep U x : ℝ) := by
      intro x hx
      rw [div_le_iff₀ hV0, mul_comm (rep U x : ℝ)]
      calc γ * #U ^ 2 ≤ thr ε j / (2 * (m + 1)) * #U ^ 2 := by
            gcongr; exact hγle j hjJ
        _ ≤ _ := hC.reg j (by omega) x hx
    calc γ * #U ^ 2 = #V * (γ * #U ^ 2 / #V) := by field_simp
      _ = ∑ x ∈ V, γ * #U ^ 2 / #V := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum hx

  obtain ⟨H0, hH0U, hH0card, hH0diff⟩ := diff_bsg U V hγpos hγ1 hUne hpairs hratio
  have hK : (#(H0 - H0) : ℝ) ≤ kay ε M J m * #H0 := hH0diff
  have hKpos : 0 < kay ε M J m := by unfold kay; positivity
  have hH0ne : H0.Nonempty := by
    rw [← card_pos]
    have : (0 : ℝ) < #H0 := lt_of_lt_of_le (by positivity) hH0card
    exact_mod_cast this
  obtain ⟨h0, hh0⟩ := hH0ne
  set S := 2 • H0 - 2 • H0 with hS
  have hSsub : H0 - H0 ⊆ S := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sub.1 hz
    rw [hS, two_nsmul]
    exact mem_sub.2 ⟨a + h0, add_mem_add ha hh0, b + h0, add_mem_add hb hh0, by abel⟩
  have hScard : (#S : ℝ) ≤ kay ε M J m ^ 4 * #H0 := card_nsmul_sub_nsmul_le ⟨h0, hh0⟩ hK 2
  have hSS : (#(S + S) : ℝ) ≤ kay ε M J m ^ 8 * #H0 := by
    have : S + S = 4 • H0 - 4 • H0 := by
      rw [hS, sub_add_sub_comm, ← add_nsmul]
    rw [this]
    exact card_nsmul_sub_nsmul_le ⟨h0, hh0⟩ hK 4
  have hH0S : (#H0 : ℝ) ≤ #S := by
    have : #H0 ≤ #S := card_le_card_of_injOn (fun h => h - h0)
      (fun h hh => hSsub (sub_mem_sub hh hh0)) (fun a _ b _ hab => sub_left_injective hab)
    exact_mod_cast this

  have hstart : γ / 6 * #U ≤ #{u ∈ U | u - h0 ∈ S} := by
    refine hH0card.trans ?_
    exact_mod_cast card_le_card (fun h hh => mem_filter.2 ⟨hH0U hh, hSsub (sub_mem_sub hh hh0)⟩)
  obtain ⟨x0, hx0⟩ := backprop hC S hγpos.le (fun l hl => hγle l (by omega)) j (by omega)
    (γ / 6) (by positivity) h0 hstart

  have hrepH0 : ∀ h ∈ H0, thr ε J * #A ≤ rep A h := by
    intro h hh
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact (mul_le_mul_of_nonneg_right (thr_anti hε hε1 (by omega)) (by positivity)).trans
      (hC.sym j' (by omega) h (hH0U hh))
  obtain ⟨A0, Λ, hA0A, hA0card, hA0cov, hΛ⟩ := cover A H0 ⟨h0, hh0⟩ (thr_pos hε J) hrepH0

  set T : Finset G := {0, x0} with hT
  have hT0 : (0 : G) ∈ T := by simp [hT]
  have hTcard : (#T : ℝ) ≤ 2 := by
    have : #T ≤ 2 := card_le_two
    exact_mod_cast this
  have hSST : (#S : ℝ) ≤ #(S + T) := by exact_mod_cast card_le_card (subset_add_left S hT0)
  have hSTle : (#(S + T) : ℝ) ≤ 2 * #S := by
    have : (#(S + T) : ℝ) ≤ #S * #T := by exact_mod_cast card_add_le
    calc (#(S + T) : ℝ) ≤ #S * #T := this
      _ ≤ #S * 2 := by gcongr
      _ = 2 * #S := by ring
  refine ⟨S + T, Λ, ?_, ?_, ?_, ?_⟩
  ·
    have h1 : (S + T) + (S + T) = (S + S) + (T + T) := add_add_add_comm _ _ _ _
    have h2 : (#((S + S) + (T + T)) : ℝ) ≤ #(S + S) * (#T * #T) := by
      have : #((S + S) + (T + T)) ≤ #(S + S) * (#T * #T) :=
        card_add_le.trans (Nat.mul_le_mul_left _ card_add_le)
      exact_mod_cast this
    rw [h1]
    calc (#((S + S) + (T + T)) : ℝ) ≤ #(S + S) * (#T * #T) := h2
      _ ≤ #(S + S) * 4 := by
        have hTT : (#T : ℝ) * #T ≤ 4 := by
          calc (#T : ℝ) * #T ≤ 2 * 2 := mul_le_mul hTcard hTcard (by positivity) (by norm_num)
            _ = 4 := by norm_num
        gcongr
      _ ≤ kay ε M J m ^ 8 * #H0 * 4 := by gcongr
      _ ≤ kay ε M J m ^ 8 * #(S + T) * 4 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hH0S.trans hSST) (by positivity))
          (by norm_num)
      _ = _ := by ring
  ·
    have hsub : A0 ⊆ A ∩ (Λ + (S + T)) := by
      intro a ha
      refine mem_inter.2 ⟨hA0A ha, ?_⟩
      exact add_subset_add_left ((hSsub).trans (subset_add_left S hT0)) (hA0cov ha)
    calc lev ε J * #A = thr ε J / 2 * #A := by rw [hthrJ]; ring
      _ ≤ #A0 := hA0card
      _ ≤ _ := by exact_mod_cast card_le_card hsub
  ·
    have hthr : 0 < thr ε J := thr_pos hε J
    have h1 : (#Λ : ℝ) * #H0 ≤ #A / lev ε J := by
      rw [le_div_iff₀ hlev]
      have : (#Λ : ℝ) * #H0 * thr ε J ≤ 2 * #A := hΛ
      rw [hthrJ] at this
      linarith
    calc (#Λ : ℝ) * #(S + T) ≤ #Λ * (2 * (kay ε M J m ^ 4 * #H0)) := by
          gcongr; linarith
      _ = 2 * kay ε M J m ^ 4 * (#Λ * #H0) := by ring
      _ ≤ 2 * kay ε M J m ^ 4 * (#A / lev ε J) := by gcongr
      _ = _ := by ring
  ·
    have hsub : {b ∈ B | b - x0 ∈ S} ⊆ B ∩ (S + T) := by
      intro b hb
      obtain ⟨hbB, hbS⟩ := mem_filter.1 hb
      refine mem_inter.2 ⟨hbB, mem_add.2 ⟨b - x0, hbS, x0, by simp [hT], by abel⟩⟩
    have hpow : γ ^ (J + 1) ≤ γ * γ ^ j := by
      calc γ ^ (J + 1) = γ * γ ^ J := by ring
        _ ≤ γ * γ ^ j := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hγpos.le hγ1 hjJ)
            hγpos.le
    calc γ ^ (J + 1) / 6 * #B ≤ γ / 6 * γ ^ j * #B := by
          gcongr
          linarith
      _ ≤ #{b ∈ B | b - x0 ∈ S} := hx0
      _ ≤ _ := by exact_mod_cast card_le_card hsub

end FractalGeometry.Lq.BSG
