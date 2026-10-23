import Mathlib
import FractalGeometry.Entropy.Lq.Bourgain.Measure
import FractalGeometry.Entropy.Lq.Bourgain.Prune
import FractalGeometry.Entropy.Lq.Bourgain.Tree
import FractalGeometry.Entropy.Lq.Bourgain.Unif
import FractalGeometry.Entropy.Lq.Statements

open Filter Topology Finset

open scoped Pointwise

namespace FractalGeometry

namespace Lq

namespace Bourgain

def T31Concl (T m₁ : ℕ) (H : Finset ℤ) : Prop :=
  ∃ H' ⊆ H, ∃ S ⊆ Finset.range m₁, ∃ R n : ℕ → ℕ,
    (2 : ℝ) ^ (-(2 * Real.logb 2 T / Real.sqrt T * (m₁ * T : ℕ))) * H.card ≤ H'.card ∧
    (∀ s < m₁, s ∉ S → ∀ x ∈ H', branching (m₁ * T) (s * T) ((s + 1) * T) H' x = 1) ∧
    (∀ s ∈ S, s * T ≤ n s ∧ n s < (s + 1) * T ∧
      (∀ x ∈ H', branching (m₁ * T) (s * T) (n s) H' x = R s ∧
        branching (m₁ * T) (n s) ((s + 1) * T) H' x = 1) ∧
      (2 : ℝ) ^ ((1 - 1 / Real.sqrt T) * ((n s : ℝ) - s * T)) < R s ∧
      (R s : ℝ) ≤ (2 : ℝ) ^ ((n s : ℝ) - s * T))

def Theorem31Weak : Prop :=
  ∀ᶠ T : ℕ in atTop, ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ m₁ : ℕ in atTop, ∀ H : Finset ℤ,
    (∀ x ∈ H, 0 ≤ x ∧ x < 2 ^ (m₁ * T)) →
    ((H + H).card : ℝ) ≤ (2 : ℝ) ^ (ε * (m₁ * T : ℕ)) * H.card →
    T31Concl T m₁ H

theorem card_nsmul_le {H : Finset ℤ} (hH : H.Nonempty) (n : ℕ) :
    ((n • H).card : ℝ) ≤ (((H + H).card : ℝ) / H.card) ^ n * H.card := by
  have h := Finset.pluennecke_ruzsa_inequality_nsmul_add hH H n
  have h' := (NNRat.cast_le (K := ℝ)).mpr h
  push_cast at h'
  exact h'

theorem arith_main {r : ℝ} (hr : 32 ≤ r) :
    Real.log (2 * r ^ 2 + 2) + Real.log 2 +
      ((103 / 100) * Real.log 2 + Real.log (2 * r ^ 2 + 2)) /
        ((r ^ 2 - 1) / (r ^ 2 * r) - 2 * (1 / (100 * r ^ 2))) ≤
      2 * r * Real.log (r ^ 2) := by
  set T := r ^ 2 with hT
  have hr0 : 0 < r := by linarith
  have hT1024 : 1024 ≤ T := by nlinarith
  have hT0 : 0 < T := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)

  have hl1 : Real.log (2 * T + 2) ≤ 2 * Real.log 2 + Real.log T := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [← h4, ← Real.log_mul (by norm_num) hT0.ne']
    exact Real.log_le_log (by linarith) (by linarith)

  have hl2 : 10 * Real.log 2 ≤ Real.log T := by
    have : Real.log (2 ^ 10) = 10 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [← this]
    exact Real.log_le_log (by norm_num) (by linarith)
  have hlogT : 0 < Real.log T := by linarith

  have hgap : 99 / 100 / r ≤ (T - 1) / (T * r) - 2 * (1 / (100 * T)) := by
    have e : (T - 1) / (T * r) - 2 * (1 / (100 * T)) = ((T - 1) - r / 50) / (T * r) := by
      field_simp
      ring
    rw [e, div_le_div_iff₀ hr0 (by positivity)]
    nlinarith
  have hgap0 : 0 < 99 / 100 / r := by positivity
  set X := (103 / 100) * Real.log 2 + Real.log (2 * T + 2) with hX
  have hX0 : 0 ≤ X := by
    have : 0 ≤ Real.log (2 * T + 2) := Real.log_nonneg (by linarith)
    positivity
  have hdiv : X / ((T - 1) / (T * r) - 2 * (1 / (100 * T))) ≤ X / (99 / 100 / r) :=
    div_le_div_of_nonneg_left hX0 hgap0 hgap
  have hdiv' : X / (99 / 100 / r) = X * r * (100 / 99) := by field_simp
  rw [hdiv'] at hdiv
  have hXle : X ≤ (131 / 100) * Real.log T := by rw [hX]; linarith
  have hfin : X * r * (100 / 99) ≤ (131 / 100) * Real.log T * r * (100 / 99) := by
    have := mul_le_mul_of_nonneg_right hXle hr0.le
    nlinarith
  have hrl : 32 * Real.log T ≤ r * Real.log T := mul_le_mul_of_nonneg_right hr hlogT.le
  nlinarith

theorem log_prod_nat (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ i ∈ s, 0 < f i) :
    Real.log (∏ i ∈ s, f i : ℕ) = ∑ i ∈ s, Real.log (f i) := by
  push_cast
  exact Real.log_prod fun i hi => by exact_mod_cast (hf i hi).ne'

set_option maxHeartbeats 1000000 in

theorem t31Concl_of_counting {T : ℕ} (hT : 2 ^ 10 ≤ T) {δ ε : ℝ} (hδ : δ = 1 / (100 * T))
    {n : ℕ} (hn : 0 < n) (hε : ε = 1 / (100 * n * T)) (m₁ : ℕ) (H : Finset ℤ)
    (hH : InUnit (m₁ * T) H) (hne : H.Nonempty)
    (hdoub : ((H + H).card : ℝ) ≤ (2 : ℝ) ^ (ε * (m₁ * T : ℕ)) * H.card)
    (hcore : ∀ (A : Finset ℤ) (R : ℕ → ℕ), A.Nonempty → InUnit (m₁ * T) A →
      IsUnif T m₁ A R →
      (T : ℝ) * (1 - δ) ^ 2 * ((range m₁).filter (fun s => 3 ≤ R s)).card *
        Real.log 2 ≤ Real.log (n • A).card) :
    T31Concl T m₁ H := by
  classical
  have hT1 : 1 ≤ T := le_trans Nat.one_le_two_pow hT
  have hTR : (1024 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  set r := Real.sqrt T with hr_def
  have hrT : r ^ 2 = T := Real.sq_sqrt hT0.le
  have hr32 : 32 ≤ r := by
    rw [show (32 : ℝ) = Real.sqrt 1024 by
      rw [show (1024 : ℝ) = 32 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hTR
  have hr0 : 0 < r := by linarith
  set η : ℝ := ((T : ℝ) - 1) / (T * r) with hη
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)

  obtain ⟨A₀, hA₀H, hA₀ne, R, hunif, hcardH⟩ := exists_unif_subset T m₁ hne
  have hA₀ : InUnit (m₁ * T) A₀ := fun x hx => hH x (hA₀H hx)
  have hbd := hunif.bounds hA₀ne

  set good : ℕ → Prop := fun s => 3 ≤ R s ∧ (2 : ℝ) ^ ((1 - η) * T) < R s with hgood
  set G := (range m₁).filter good with hG
  set C := (range m₁).filter fun s => ¬ good s with hC
  set S1 := (range m₁).filter fun s => 3 ≤ R s with hS1
  set B := S1.filter fun s => ¬ (2 : ℝ) ^ ((1 - η) * T) < R s with hB
  set Sm := (range m₁).filter fun s => ¬ 3 ≤ R s with hSm

  obtain ⟨H', hH'A₀, hH'card, hcoll, hhalf⟩ := exists_pruned hT1 hunif hA₀ hA₀ne C
  have hC_iff : ∀ s < m₁, s ∉ C ↔ s ∈ G := by
    intro s hs
    simp only [hC, hG, mem_filter, mem_range, hs, true_and, not_not]
  refine ⟨H', hH'A₀.trans hA₀H, G, filter_subset _ _, fun s => (R s + 1) / 2,
    fun s => (s + 1) * T - 1, ?_, ?_, ?_⟩
  ·
    have hHpos : (0 : ℝ) < H.card := by exact_mod_cast card_pos.mpr hne
    have hRpos : ∀ s ∈ range m₁, 0 < R s := fun s hs => (hbd s (mem_range.mp hs)).1

    have hK1 := hcore A₀ R hA₀ne hA₀ hunif

    have hS1G : S1.filter (fun s => (2 : ℝ) ^ ((1 - η) * T) < R s) = G := by
      rw [hS1, filter_filter]
    have hS1card : S1.card = B.card + G.card := by
      rw [← hS1G, add_comm]
      exact (card_filter_add_card_filter_not _).symm
    have hcount : Sm.card + B.card + G.card = m₁ := by
      rw [add_assoc, ← hS1card, add_comm]
      have := card_filter_add_card_filter_not (s := range m₁) (fun s => 3 ≤ R s)
      rwa [card_range] at this

    have hK2 : Real.log (n • A₀).card ≤ (m₁ / 100) * Real.log 2 + Real.log H.card := by
      have hnA : (0 : ℝ) < (n • A₀).card := by exact_mod_cast card_pos.mpr (hA₀ne.nsmul)
      have h1 : ((n • A₀).card : ℝ) ≤ (n • H).card := by
        exact_mod_cast card_le_card (nsmul_subset_nsmul_left hA₀H)
      have h2 := card_nsmul_le hne n
      have hD : ((H + H).card : ℝ) / H.card ≤ (2 : ℝ) ^ (ε * (m₁ * T : ℕ)) := by
        rw [div_le_iff₀ hHpos]; exact hdoub
      have h3 : (((H + H).card : ℝ) / H.card) ^ n ≤ ((2 : ℝ) ^ (ε * (m₁ * T : ℕ))) ^ n :=
        pow_le_pow_left₀ (by positivity) hD n
      have h4 : ((n • A₀).card : ℝ) ≤ ((2 : ℝ) ^ (ε * (m₁ * T : ℕ))) ^ n * H.card := by
        calc ((n • A₀).card : ℝ) ≤ (n • H).card := h1
          _ ≤ _ := h2
          _ ≤ _ := mul_le_mul_of_nonneg_right h3 hHpos.le
      have h5 := Real.log_le_log hnA h4
      rw [Real.log_mul (by positivity) hHpos.ne', Real.log_pow, Real.log_rpow (by norm_num)] at h5
      have hnε : (n : ℝ) * (ε * (m₁ * T : ℕ)) = m₁ / 100 := by
        rw [hε]
        have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        push_cast
        field_simp
      calc Real.log (n • A₀).card ≤ _ := h5
        _ = _ := by rw [← mul_assoc, hnε]

    have hK3 : Real.log H.card ≤ m₁ * Real.log (2 * T + 2) + Real.log A₀.card := by
      have hA₀pos : (0 : ℝ) < A₀.card := by exact_mod_cast card_pos.mpr hA₀ne
      have h : (H.card : ℝ) ≤ (2 * T + 2) ^ m₁ * A₀.card := by
        have := (Nat.cast_le (α := ℝ)).mpr hcardH
        push_cast at this
        rwa [show (2 : ℝ) * (T + 1) = 2 * T + 2 by ring] at this
      have := Real.log_le_log hHpos h
      rwa [Real.log_mul (by positivity) hA₀pos.ne', Real.log_pow] at this

    have hK4 : Real.log A₀.card = ∑ s ∈ range m₁, Real.log (R s) := by
      rw [hunif.card_eq hA₀ hA₀ne, log_prod_nat _ _ hRpos]
    have hsplit1 := sum_filter_add_sum_filter_not (range m₁) (fun s => 3 ≤ R s)
      (fun s => Real.log (R s))
    have hsplit2 := sum_filter_add_sum_filter_not S1 (fun s => (2 : ℝ) ^ ((1 - η) * T) < R s)
      (fun s => Real.log (R s))
    rw [hS1G] at hsplit2

    have hlogR : ∀ s ∈ range m₁, Real.log (R s) ≤ T * Real.log 2 := by
      intro s hs
      have h : (R s : ℝ) ≤ 2 ^ T := by exact_mod_cast (hbd s (mem_range.mp hs)).2
      have := Real.log_le_log (by exact_mod_cast hRpos s hs) h
      rwa [Real.log_pow] at this
    have hbSm : ∑ s ∈ Sm, Real.log (R s) ≤ Sm.card * Real.log 2 := by
      rw [← nsmul_eq_mul]
      apply sum_le_card_nsmul
      intro s hs
      obtain ⟨hs1, hs2⟩ := mem_filter.mp hs
      have h : (R s : ℝ) ≤ 2 := by exact_mod_cast (show R s ≤ 2 by omega)
      exact Real.log_le_log (by exact_mod_cast hRpos s hs1) h
    have hbB : ∑ s ∈ B, Real.log (R s) ≤ B.card * ((1 - η) * T * Real.log 2) := by
      rw [← nsmul_eq_mul]
      apply sum_le_card_nsmul
      intro s hs
      obtain ⟨hs1, hs2⟩ := mem_filter.mp hs
      have hs0 := (mem_filter.mp hs1).1
      push Not at hs2
      have := Real.log_le_log (by exact_mod_cast hRpos s hs0) hs2
      rwa [Real.log_rpow (by norm_num)] at this
    have hbBT : ∑ s ∈ B, Real.log (R s) ≤ B.card * (T * Real.log 2) := by
      rw [← nsmul_eq_mul]
      exact sum_le_card_nsmul _ _ _ fun s hs => hlogR s (mem_filter.mp (mem_filter.mp hs).1).1
    have hbG : ∑ s ∈ G, Real.log (R s) ≤ G.card * (T * Real.log 2) := by
      rw [← nsmul_eq_mul]
      exact sum_le_card_nsmul _ _ _ fun s hs => hlogR s (mem_filter.mp hs).1

    have hK5 : ∑ s ∈ G, Real.log (R s) - G.card * Real.log 2 ≤ Real.log H'.card := by
      have hfpos : ∀ s ∈ range m₁, 0 < (if s ∈ C then 1 else (R s + 1) / 2) := by
        intro s hs
        split_ifs
        · norm_num
        · have := hRpos s hs; omega
      rw [hH'card, log_prod_nat _ _ hfpos]
      have hsp := sum_filter_add_sum_filter_not (range m₁) (fun s => s ∈ C)
        (fun s => Real.log ((if s ∈ C then 1 else (R s + 1) / 2 : ℕ) : ℝ))
      have hC0 : ∑ s ∈ (range m₁).filter (fun s => s ∈ C),
          Real.log ((if s ∈ C then 1 else (R s + 1) / 2 : ℕ) : ℝ) = 0 := by
        refine sum_eq_zero fun s hs => ?_
        simp [(mem_filter.mp hs).2]
      have hGeq : (range m₁).filter (fun s => s ∉ C) = G := by
        ext s
        simp only [mem_filter, mem_range]
        constructor
        · rintro ⟨hs, hsC⟩; exact (hC_iff s hs).mp hsC
        · intro hsG
          have hs := mem_range.mp (mem_filter.mp hsG).1
          exact ⟨hs, (hC_iff s hs).mpr hsG⟩
      rw [← hsp, hC0, zero_add, hGeq, ← nsmul_eq_mul, ← sum_const, ← sum_sub_distrib]
      apply sum_le_sum
      intro s hsG
      have hsC : s ∉ C := (hC_iff s (mem_range.mp (mem_filter.mp hsG).1)).mpr hsG
      simp only [hsC, ↓reduceIte]
      rw [← Real.log_div (by exact_mod_cast (hRpos s (mem_filter.mp hsG).1).ne')
        (by norm_num)]
      apply Real.log_le_log (by have := hRpos s (mem_filter.mp hsG).1; positivity)
      have h : R s ≤ 2 * ((R s + 1) / 2) := by omega
      have h' : (R s : ℝ) ≤ 2 * (((R s + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h
      linarith

    set xS : ℝ := (Sm.card : ℝ)
    set xB : ℝ := (B.card : ℝ)
    set xG : ℝ := (G.card : ℝ)
    have hcountR : xS + xB + xG = m₁ := by
      simp only [xS, xB, xG]; exact_mod_cast hcount
    have hxS : 0 ≤ xS := Nat.cast_nonneg _
    have hxB : 0 ≤ xB := Nat.cast_nonneg _
    have hxG : 0 ≤ xG := Nat.cast_nonneg _
    have hδ' : (1 - δ) ^ 2 ≥ 1 - 2 * δ := by nlinarith [sq_nonneg δ]
    have hδT : T * δ = 1 / 100 := by rw [hδ]; field_simp
    rw [hS1card] at hK1
    push_cast at hK1

    have hgap : 0 < η - 2 * δ := by
      rw [hη, hδ]
      have e : ((T : ℝ) - 1) / (T * r) - 2 * (1 / (100 * T)) = ((T - 1) - r / 50) / (T * r) := by
        field_simp
        ring
      rw [e]
      apply div_pos _ (by positivity)
      nlinarith
    have E1 : (T : ℝ) * (1 - δ) ^ 2 * (xB + xG) * Real.log 2 ≤
        m₁ / 100 * Real.log 2 + m₁ * Real.log (2 * T + 2) + xS * Real.log 2 +
          xB * ((1 - η) * T * Real.log 2) + xG * (T * Real.log 2) := by
      linarith
    have E2 : (T : ℝ) * (1 - 2 * δ) * (xB + xG) * Real.log 2 ≤
        T * (1 - δ) ^ 2 * (xB + xG) * Real.log 2 := by
      apply mul_le_mul_of_nonneg_right _ hlog2.le
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hδ' hT0.le
    have F1 : (xS + xG / 50 - m₁) * Real.log 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hlog2.le
    have G1 : 0 ≤ (m₁ : ℝ) * Real.log 2 := mul_nonneg (Nat.cast_nonneg _) hlog2.le
    have Z1 : 2 * xG * Real.log 2 * (T * δ - 1 / 100) = 0 := by rw [hδT]; ring
    have hid : xB * T * Real.log 2 * (η - 2 * δ) -
        m₁ * ((103 / 100) * Real.log 2 + Real.log (2 * T + 2)) =
        ((T : ℝ) * (1 - 2 * δ) * (xB + xG) * Real.log 2 -
          (m₁ / 100 * Real.log 2 + m₁ * Real.log (2 * T + 2) + xS * Real.log 2 +
            xB * ((1 - η) * T * Real.log 2) + xG * (T * Real.log 2))) +
        (xS + xG / 50 - m₁) * Real.log 2 + 2 * xG * Real.log 2 * (T * δ - 1 / 100) -
          2 / 100 * (m₁ * Real.log 2) := by ring
    have hbad : xB * T * Real.log 2 ≤
        m₁ * ((103 / 100) * Real.log 2 + Real.log (2 * T + 2)) / (η - 2 * δ) := by
      rw [le_div_iff₀ hgap]
      linarith only [hid, E1, E2, F1, G1, Z1]

    have hfinal : Real.log H.card - Real.log H'.card ≤ m₁ * (2 * r * Real.log T) := by
      have H1 : xS * Real.log 2 + xG * Real.log 2 ≤ m₁ * Real.log 2 := by
        have h : xS + xG ≤ m₁ := by linarith
        have := mul_le_mul_of_nonneg_right h hlog2.le
        linarith [add_mul xS xG (Real.log 2)]
      have H2 : ∑ s ∈ B, Real.log (R s) ≤ xB * T * Real.log 2 := by
        have := hbBT
        linarith [mul_assoc xB (T : ℝ) (Real.log 2)]
      have hlogs : Real.log H.card - Real.log H'.card ≤
          m₁ * Real.log (2 * T + 2) + m₁ * Real.log 2 + xB * T * Real.log 2 := by
        linarith only [hK3, hK4, hsplit1, hsplit2, hK5, hbSm, H2, H1]
      have harith := arith_main hr32
      rw [hrT] at harith
      have hηδ : ((T : ℝ) - 1) / (T * r) - 2 * (1 / (100 * T)) = η - 2 * δ := by rw [hη, hδ]
      rw [hηδ] at harith
      have hm : (0 : ℝ) ≤ m₁ := Nat.cast_nonneg _
      have H3 := mul_le_mul_of_nonneg_left harith hm
      rw [mul_add, mul_add] at H3
      have hYeq : (m₁ : ℝ) * ((103 / 100) * Real.log 2 + Real.log (2 * T + 2)) / (η - 2 * δ) =
          m₁ * (((103 / 100) * Real.log 2 + Real.log (2 * T + 2)) / (η - 2 * δ)) := by ring
      linarith only [hlogs, hbad, H3, hYeq]
    have hpos' : (0 : ℝ) < (2 : ℝ) ^ (-(2 * Real.logb 2 T / Real.sqrt T * (m₁ * T : ℕ))) *
        H.card := mul_pos (Real.rpow_pos_of_pos two_pos _) hHpos
    have hH'pos : (0 : ℝ) < H'.card := by
      rw [hH'card]
      exact_mod_cast prod_pos fun s hs => by
        split_ifs
        · norm_num
        · have := hRpos s hs; omega
    rw [← Real.log_le_log_iff hpos' hH'pos, Real.log_mul (by positivity) hHpos.ne',
      Real.log_rpow (by norm_num)]
    have hlb : Real.logb 2 T * Real.log 2 = Real.log T := by
      rw [Real.logb, div_mul_cancel₀ _ hlog2.ne']
    have hTr : (T : ℝ) / r = r := by
      rw [← hrT]; field_simp
    have heq : 2 * Real.logb 2 T / Real.sqrt T * ((m₁ * T : ℕ) : ℝ) * Real.log 2 =
        m₁ * (2 * r * Real.log T) := by
      rw [← hr_def, ← hlb]
      push_cast
      rw [← hTr]
      field_simp
      rw [hrT]
    linarith only [heq, hfinal]
  · intro s hs hsG x hx
    exact hcoll s hs (by_contra fun h => hsG ((hC_iff s hs).mp h)) x hx
  · intro s hsG
    have hs' : s < m₁ := mem_range.mp (mem_filter.mp hsG).1
    have hgs : good s := (mem_filter.mp hsG).2
    have hsC : s ∉ C := (hC_iff s hs').mpr hsG
    have hsT : 1 ≤ (s + 1) * T := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have h1 : s * T ≤ (s + 1) * T - 1 := by rw [Nat.succ_mul]; omega
    have h2 : (s + 1) * T - 1 < (s + 1) * T := by omega
    have hcast : (((s + 1) * T - 1 : ℕ) : ℝ) - s * T = T - 1 := by
      rw [Nat.cast_sub hsT]; push_cast; ring
    refine ⟨h1, h2, fun x hx => hhalf s hs' hsC x hx, ?_, ?_⟩
    · rw [hcast]
      have hexp : (1 - 1 / Real.sqrt T) * ((T : ℝ) - 1) = (1 - η) * T - 1 := by
        rw [← hr_def, hη]
        field_simp
        nlinarith [hrT]
      rw [hexp, Real.rpow_sub (by norm_num), Real.rpow_one]
      have hhalf' : (R s : ℝ) / 2 ≤ (((R s + 1) / 2 : ℕ) : ℝ) := by
        have h : R s ≤ 2 * ((R s + 1) / 2) := by omega
        have h' : (R s : ℝ) ≤ 2 * (((R s + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h
        linarith
      have := hgs.2
      calc (2 : ℝ) ^ ((1 - η) * T) / 2 < R s / 2 := by linarith
        _ ≤ _ := hhalf'
    · rw [hcast]
      have hle : (R s + 1) / 2 ≤ 2 ^ (T - 1) := by
        have hR := (hbd s hs').2
        have h2T : 2 ^ T = 2 * 2 ^ (T - 1) := by
          rw [← pow_succ']; congr 1; omega
        omega
      calc (((R s + 1) / 2 : ℕ) : ℝ) ≤ ((2 ^ (T - 1) : ℕ) : ℝ) := by exact_mod_cast hle
        _ = (2 : ℝ) ^ ((T : ℝ) - 1) := by
          rw [show ((T : ℝ) - 1) = ((T - 1 : ℕ) : ℝ) by rw [Nat.cast_sub hT1]; simp,
            Real.rpow_natCast]
          push_cast
          rfl

theorem theorem31Weak : Theorem31Weak := by
  filter_upwards [eventually_ge_atTop (2 ^ 10)] with T hT
  have hT1 : 1 ≤ T := le_trans Nat.one_le_two_pow hT
  set δ : ℝ := 1 / (100 * T) with hδ
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT1
  have hδpos : 0 < δ := by positivity
  have hδ1 : δ < 1 := by
    rw [hδ, div_lt_one (by positivity)]
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT1
    linarith
  obtain ⟨n, hn, hcore⟩ := dichotomy_core hT1 hδpos hδ1
  refine ⟨1 / (100 * n * T), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 0] with m₁ _
  intro H hH hdoub
  rcases H.eq_empty_or_nonempty with rfl | hne
  · refine ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, fun _ => 0, fun _ => 0, ?_, ?_,
      ?_⟩
    · simp
    · intro s _ _ x hx
      simp at hx
    · intro s hs
      simp at hs
  exact t31Concl_of_counting hT hδ hn rfl m₁ H hH hne hdoub (hcore m₁)

end Bourgain

end Lq

end FractalGeometry
