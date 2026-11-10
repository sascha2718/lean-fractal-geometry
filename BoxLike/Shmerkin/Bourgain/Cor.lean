module

public import BoxLike.Shmerkin.Bourgain.Main
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Shmerkin, Corollary 3.10: a weak form

Corollary 3.10 of Shmerkin (arXiv:1609.07802v3), the form of Theorem 3.1 that the proof of
Theorem 2.1 uses, with the doubling exponent `2^{-2D²-1}` replaced by some `σ(D) > 0`
(`Corollary310Weak`). It is Theorem 1.5 of Shmerkin, arXiv:2308.09846, in dimension one, and is
proved directly from Hochman's saturation theorem (`dichotomy_core`), Lemma 3.6
(`exists_unif_subset`) and Lemma 3.7 (`exists_collapsed`), with the rates `log R_s ≥ (1 - η) D`
and `|H'| ≥ 2^{-η m} |H|` for every `η ∈ (0, 1]`.
-/

open Filter Topology Finset
open scoped Pointwise

namespace BoxLike
namespace Shmerkin
namespace Bourgain

/-- **Corollary 3.10 of Shmerkin, weak form.** For `η ∈ (0, 1]` and large `D` there is `σ > 0`
such that every nonempty `2^{-ℓD}`-set `H` with `|H + H| ≤ 2^{σ ℓ D} |H|` contains a nonempty
`(D, ℓ, R)`-uniform subset `H'` with `R_s = 1` or `R_s ≥ 2^{(1-η) D}` for every block and
`|H'| ≥ 2^{-η ℓ D} |H|`. -/
def Corollary310Weak : Prop :=
  ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ᶠ D : ℕ in atTop, ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ ℓ : ℕ in atTop,
    ∀ H : Finset ℤ, InUnit (ℓ * D) H → H.Nonempty →
      ((H + H).card : ℝ) ≤ (2 : ℝ) ^ (σ * (ℓ * D : ℕ)) * H.card →
      ∃ H' ⊆ H, H'.Nonempty ∧ ∃ R : ℕ → ℕ, IsUnif D ℓ H' R ∧
        (∀ s < ℓ, R s = 1 ∨ (2 : ℝ) ^ ((1 - η) * D) ≤ R s) ∧
        (2 : ℝ) ^ (-(η * (ℓ * D : ℕ))) * H.card ≤ H'.card

/-- The numerical inequality of the counting step for Corollary 3.10, with
`δ = 1/(100 D)` and `D ≥ 400 / η⁴`. -/
theorem arith_cor {η D : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hD : 400 / η ^ 4 ≤ D) :
    Real.log (2 * D + 2) + Real.log 2 +
      ((103 / 100) * Real.log 2 + Real.log (2 * D + 2)) / (η - 2 * (1 / (100 * D))) ≤
      η * D * Real.log 2 := by
  have hη4 : 0 < η ^ 4 := by positivity
  have hη4le : η ^ 4 ≤ 1 := pow_le_one₀ hη.le hη1
  have hD400 : 400 ≤ D := le_trans (by rw [le_div_iff₀ hη4]; nlinarith) hD
  have hD0 : 0 < D := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hlog2'' : 1 / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  -- `u = √D ≥ 20 / η²`
  set u := Real.sqrt D with hu
  have hu2 : u ^ 2 = D := Real.sq_sqrt hD0.le
  have hu0 : 0 ≤ u := Real.sqrt_nonneg D
  have hu20 : 20 / η ^ 2 ≤ u := by
    rw [hu, show (20 : ℝ) / η ^ 2 = Real.sqrt ((20 / η ^ 2) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    rw [div_pow]
    linarith [show (20 : ℝ) ^ 2 / (η ^ 2) ^ 2 = 400 / η ^ 4 by ring]
  have hupos : 0 < u := lt_of_lt_of_le (by positivity) hu20
  -- `log D ≤ 2 u`
  have hlogD : Real.log D ≤ 2 * u := by
    rw [← hu2, Real.log_pow]
    have := Real.log_le_sub_one_of_pos hupos
    push_cast
    linarith
  have hlogD0 : 0 ≤ Real.log D := Real.log_nonneg (by linarith)
  -- `log (2D + 2) ≤ 2 log 2 + log D`
  have hl1 : Real.log (2 * D + 2) ≤ 2 * Real.log 2 + Real.log D := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [← h4, ← Real.log_mul (by norm_num) hD0.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  -- the gap `η - 2δ ≥ η / 2`
  have hgap : η / 2 ≤ η - 2 * (1 / (100 * D)) := by
    have : 2 * (1 / (100 * D)) ≤ η / 2 := by
      rw [show 2 * (1 / (100 * D)) = 1 / (50 * D) by ring, div_le_div_iff₀ (by positivity)
        (by norm_num)]
      have : 1 ≤ η * D := by
        have h1 : 400 ≤ η ^ 4 * D := by rw [div_le_iff₀ hη4] at hD; linarith
        have h2 : η ^ 4 ≤ η := by
          calc η ^ 4 = η * η ^ 3 := by ring
            _ ≤ η * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hη.le hη1) hη.le
            _ = η := mul_one η
        nlinarith [mul_le_mul_of_nonneg_right h2 hD0.le]
      nlinarith
    linarith
  have hX0 : 0 ≤ (103 / 100) * Real.log 2 + Real.log (2 * D + 2) := by
    have : 0 ≤ Real.log (2 * D + 2) := Real.log_nonneg (by linarith)
    positivity
  have hdiv : ((103 / 100) * Real.log 2 + Real.log (2 * D + 2)) / (η - 2 * (1 / (100 * D))) ≤
      ((103 / 100) * Real.log 2 + Real.log (2 * D + 2)) / (η / 2) :=
    div_le_div_of_nonneg_left hX0 (by positivity) hgap
  have hdiv' : ((103 / 100) * Real.log 2 + Real.log (2 * D + 2)) / (η / 2) =
      2 / η * ((103 / 100) * Real.log 2 + Real.log (2 * D + 2)) := by field_simp
  rw [hdiv'] at hdiv
  -- the main estimate
  have hY : (103 / 100) * Real.log 2 + Real.log (2 * D + 2) ≤ 4 + 2 * u := by linarith
  have hinv : 1 ≤ 1 / η := by rw [le_div_iff₀ hη]; linarith
  have hA : 2 / η * ((103 / 100) * Real.log 2 + Real.log (2 * D + 2)) ≤ 2 / η * (4 + 2 * u) :=
    mul_le_mul_of_nonneg_left hY (by positivity)
  have hB : Real.log (2 * D + 2) + Real.log 2 ≤ 1 / η * (4 + 2 * u) := by
    have : Real.log (2 * D + 2) + Real.log 2 ≤ 4 + 2 * u := by linarith
    nlinarith
  -- `3/η (4 + 2u) ≤ η u² log 2`
  have hfin : 3 / η * (4 + 2 * u) ≤ η * u ^ 2 * Real.log 2 := by
    have h1 : 20 ≤ η ^ 2 * u := by rw [div_le_iff₀ (by positivity)] at hu20; linarith
    have h2 : 1 ≤ u := by nlinarith [pow_le_one₀ hη.le hη1 (n := 2)]
    rw [div_mul_eq_mul_div, div_le_iff₀ hη]
    nlinarith [mul_le_mul_of_nonneg_left h1 hupos.le, mul_le_mul_of_nonneg_right hlog2''.le
      (by positivity : (0 : ℝ) ≤ η ^ 2 * u ^ 2)]
  have hDu : η * D * Real.log 2 = η * u ^ 2 * Real.log 2 := by rw [hu2]
  have : 2 / η * (4 + 2 * u) + 1 / η * (4 + 2 * u) = 3 / η * (4 + 2 * u) := by ring
  linarith

set_option maxHeartbeats 1000000 in
/-- **The counting step for Corollary 3.10.** -/
theorem cor310_of_counting {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {D : ℕ}
    (hD : 400 / η ^ 4 ≤ D) {δ σ : ℝ} (hδ : δ = 1 / (100 * D))
    {n : ℕ} (hn : 0 < n) (hσ : σ = 1 / (100 * n * D)) (ℓ : ℕ) (H : Finset ℤ)
    (hH : InUnit (ℓ * D) H) (hne : H.Nonempty)
    (hdoub : ((H + H).card : ℝ) ≤ (2 : ℝ) ^ (σ * (ℓ * D : ℕ)) * H.card)
    (hcore : ∀ (A : Finset ℤ) (R : ℕ → ℕ), A.Nonempty → InUnit (ℓ * D) A →
      IsUnif D ℓ A R →
      (D : ℝ) * (1 - δ) ^ 2 * ((range ℓ).filter (fun s => 3 ≤ R s)).card *
        Real.log 2 ≤ Real.log (n • A).card) :
    ∃ H' ⊆ H, H'.Nonempty ∧ ∃ R : ℕ → ℕ, IsUnif D ℓ H' R ∧
      (∀ s < ℓ, R s = 1 ∨ (2 : ℝ) ^ ((1 - η) * D) ≤ R s) ∧
      (2 : ℝ) ^ (-(η * (ℓ * D : ℕ))) * H.card ≤ H'.card := by
  classical
  have hη4 : 0 < η ^ 4 := by positivity
  have hD400 : (400 : ℝ) ≤ D := le_trans (by
    rw [le_div_iff₀ hη4]; nlinarith [pow_le_one₀ hη.le hη1 (n := 4)]) hD
  have hD0 : (0 : ℝ) < D := by linarith
  have hD1 : 1 ≤ D := by exact_mod_cast (show (1 : ℝ) ≤ D by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the uniform subset
  obtain ⟨A₀, hA₀H, hA₀ne, R, hunif, hcardH⟩ := exists_unif_subset D ℓ hne
  have hA₀ : InUnit (ℓ * D) A₀ := fun x hx => hH x (hA₀H hx)
  have hbd := hunif.bounds hA₀ne
  -- the classes of blocks
  set good : ℕ → Prop := fun s => 3 ≤ R s ∧ (2 : ℝ) ^ ((1 - η) * D) ≤ R s with hgood
  set G := (range ℓ).filter good with hG
  set C := (range ℓ).filter fun s => ¬ good s with hC
  set S1 := (range ℓ).filter fun s => 3 ≤ R s with hS1
  set B := S1.filter fun s => ¬ (2 : ℝ) ^ ((1 - η) * D) ≤ R s with hB
  set Sm := (range ℓ).filter fun s => ¬ 3 ≤ R s with hSm
  -- the collapsed set
  obtain ⟨H', hH'A₀, hH'ne, hH'unif⟩ := exists_collapsed hunif hA₀ne C
  have hC_iff : ∀ s < ℓ, s ∉ C ↔ s ∈ G := by
    intro s hs
    simp only [hC, hG, mem_filter, mem_range, hs, true_and, not_not]
  refine ⟨H', hH'A₀.trans hA₀H, hH'ne, _, hH'unif, fun s hs => ?_, ?_⟩
  · by_cases hsC : s ∈ C
    · left; simp [hsC]
    · right
      simp only [hsC, ↓reduceIte]
      exact ((mem_filter.mp ((hC_iff s hs).mp hsC)).2).2
  -- the size of `H'`
  have hHpos : (0 : ℝ) < H.card := by exact_mod_cast card_pos.mpr hne
  have hRpos : ∀ s ∈ range ℓ, 0 < R s := fun s hs => (hbd s (mem_range.mp hs)).1
  have hK1 := hcore A₀ R hA₀ne hA₀ hunif
  have hS1G : S1.filter (fun s => (2 : ℝ) ^ ((1 - η) * D) ≤ R s) = G := by
    rw [hS1, filter_filter]
  have hS1card : S1.card = B.card + G.card := by
    rw [← hS1G, add_comm]
    exact (card_filter_add_card_filter_not _).symm
  have hcount : Sm.card + B.card + G.card = ℓ := by
    rw [add_assoc, ← hS1card, add_comm]
    have := card_filter_add_card_filter_not (s := range ℓ) (fun s => 3 ≤ R s)
    rwa [card_range] at this
  -- Plünnecke–Ruzsa
  have hK2 : Real.log (n • A₀).card ≤ (ℓ / 100) * Real.log 2 + Real.log H.card := by
    have hnA : (0 : ℝ) < (n • A₀).card := by exact_mod_cast card_pos.mpr (hA₀ne.nsmul)
    have h1 : ((n • A₀).card : ℝ) ≤ (n • H).card := by
      exact_mod_cast card_le_card (nsmul_subset_nsmul_left hA₀H)
    have h2 := card_nsmul_le hne n
    have hDd : ((H + H).card : ℝ) / H.card ≤ (2 : ℝ) ^ (σ * (ℓ * D : ℕ)) := by
      rw [div_le_iff₀ hHpos]; exact hdoub
    have h3 : (((H + H).card : ℝ) / H.card) ^ n ≤ ((2 : ℝ) ^ (σ * (ℓ * D : ℕ))) ^ n :=
      pow_le_pow_left₀ (by positivity) hDd n
    have h4 : ((n • A₀).card : ℝ) ≤ ((2 : ℝ) ^ (σ * (ℓ * D : ℕ))) ^ n * H.card := by
      calc ((n • A₀).card : ℝ) ≤ (n • H).card := h1
        _ ≤ _ := h2
        _ ≤ _ := mul_le_mul_of_nonneg_right h3 hHpos.le
    have h5 := Real.log_le_log hnA h4
    rw [Real.log_mul (by positivity) hHpos.ne', Real.log_pow, Real.log_rpow (by norm_num)] at h5
    have hnσ : (n : ℝ) * (σ * (ℓ * D : ℕ)) = ℓ / 100 := by
      rw [hσ]
      have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      push_cast
      field_simp
    calc Real.log (n • A₀).card ≤ _ := h5
      _ = _ := by rw [← mul_assoc, hnσ]
  -- the uniformisation loss
  have hK3 : Real.log H.card ≤ ℓ * Real.log (2 * D + 2) + Real.log A₀.card := by
    have hA₀pos : (0 : ℝ) < A₀.card := by exact_mod_cast card_pos.mpr hA₀ne
    have h : (H.card : ℝ) ≤ (2 * D + 2) ^ ℓ * A₀.card := by
      have := (Nat.cast_le (α := ℝ)).mpr hcardH
      push_cast at this
      rwa [show (2 : ℝ) * (D + 1) = 2 * D + 2 by ring] at this
    have := Real.log_le_log hHpos h
    rwa [Real.log_mul (by positivity) hA₀pos.ne', Real.log_pow] at this
  have hK4 : Real.log A₀.card = ∑ s ∈ range ℓ, Real.log (R s) := by
    rw [hunif.card_eq hA₀ hA₀ne, log_prod_nat _ _ hRpos]
  have hsplit1 := sum_filter_add_sum_filter_not (range ℓ) (fun s => 3 ≤ R s)
    (fun s => Real.log (R s))
  have hsplit2 := sum_filter_add_sum_filter_not S1 (fun s => (2 : ℝ) ^ ((1 - η) * D) ≤ R s)
    (fun s => Real.log (R s))
  rw [hS1G] at hsplit2
  have hlogR : ∀ s ∈ range ℓ, Real.log (R s) ≤ D * Real.log 2 := by
    intro s hs
    have h : (R s : ℝ) ≤ 2 ^ D := by exact_mod_cast (hbd s (mem_range.mp hs)).2
    have := Real.log_le_log (by exact_mod_cast hRpos s hs) h
    rwa [Real.log_pow] at this
  have hbSm : ∑ s ∈ Sm, Real.log (R s) ≤ Sm.card * Real.log 2 := by
    rw [← nsmul_eq_mul]
    apply sum_le_card_nsmul
    intro s hs
    obtain ⟨hs1, hs2⟩ := mem_filter.mp hs
    have h : (R s : ℝ) ≤ 2 := by exact_mod_cast (show R s ≤ 2 by omega)
    exact Real.log_le_log (by exact_mod_cast hRpos s hs1) h
  have hbB : ∑ s ∈ B, Real.log (R s) ≤ B.card * ((1 - η) * D * Real.log 2) := by
    rw [← nsmul_eq_mul]
    apply sum_le_card_nsmul
    intro s hs
    obtain ⟨hs1, hs2⟩ := mem_filter.mp hs
    have hs0 := (mem_filter.mp hs1).1
    push Not at hs2
    have := Real.log_le_log (by exact_mod_cast hRpos s hs0) hs2.le
    rwa [Real.log_rpow (by norm_num)] at this
  have hbBT : ∑ s ∈ B, Real.log (R s) ≤ B.card * (D * Real.log 2) := by
    rw [← nsmul_eq_mul]
    exact sum_le_card_nsmul _ _ _ fun s hs => hlogR s (mem_filter.mp (mem_filter.mp hs).1).1
  have hbG : ∑ s ∈ G, Real.log (R s) ≤ G.card * (D * Real.log 2) := by
    rw [← nsmul_eq_mul]
    exact sum_le_card_nsmul _ _ _ fun s hs => hlogR s (mem_filter.mp hs).1
  -- the logarithm of `|H'|`
  have hK5 : ∑ s ∈ G, Real.log (R s) ≤ Real.log H'.card := by
    have hfpos : ∀ s ∈ range ℓ, 0 < (if s ∈ C then 1 else R s) := by
      intro s hs
      split_ifs
      · norm_num
      · exact hRpos s hs
    have hH'A : InUnit (ℓ * D) H' := fun x hx => hA₀ x (hH'A₀ hx)
    rw [hH'unif.card_eq hH'A hH'ne, log_prod_nat _ _ hfpos]
    have hsp := sum_filter_add_sum_filter_not (range ℓ) (fun s => s ∈ C)
      (fun s => Real.log ((if s ∈ C then 1 else R s : ℕ) : ℝ))
    have hC0 : ∑ s ∈ (range ℓ).filter (fun s => s ∈ C),
        Real.log ((if s ∈ C then 1 else R s : ℕ) : ℝ) = 0 := by
      refine sum_eq_zero fun s hs => ?_
      simp [(mem_filter.mp hs).2]
    have hGeq : (range ℓ).filter (fun s => s ∉ C) = G := by
      ext s
      simp only [mem_filter, mem_range]
      constructor
      · rintro ⟨hs, hsC⟩; exact (hC_iff s hs).mp hsC
      · intro hsG
        have hs := mem_range.mp (mem_filter.mp hsG).1
        exact ⟨hs, (hC_iff s hs).mpr hsG⟩
    rw [← hsp, hC0, zero_add, hGeq]
    apply le_of_eq
    refine sum_congr rfl fun s hsG => ?_
    have hsC : s ∉ C := (hC_iff s (mem_range.mp (mem_filter.mp hsG).1)).mpr hsG
    simp only [hsC, ↓reduceIte]
  -- the counting
  set xS : ℝ := (Sm.card : ℝ)
  set xB : ℝ := (B.card : ℝ)
  set xG : ℝ := (G.card : ℝ)
  have hcountR : xS + xB + xG = ℓ := by
    simp only [xS, xB, xG]; exact_mod_cast hcount
  have hxS : 0 ≤ xS := Nat.cast_nonneg _
  have hxB : 0 ≤ xB := Nat.cast_nonneg _
  have hxG : 0 ≤ xG := Nat.cast_nonneg _
  have hδ' : (1 - δ) ^ 2 ≥ 1 - 2 * δ := by nlinarith [sq_nonneg δ]
  have hδD : D * δ = 1 / 100 := by rw [hδ]; field_simp
  rw [hS1card] at hK1
  push_cast at hK1
  have hgap : 0 < η - 2 * δ := by
    have h1 : 2 * δ = 1 / (50 * D) := by rw [hδ]; ring
    have h2 : 1 / (50 * (D : ℝ)) < η := by
      rw [div_lt_iff₀ (by positivity)]
      have : 1 ≤ η * D := by
        have h3 : 400 ≤ η ^ 4 * D := by rw [div_le_iff₀ hη4] at hD; linarith
        have h4 : η ^ 4 ≤ η := by
          calc η ^ 4 = η * η ^ 3 := by ring
            _ ≤ η * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hη.le hη1) hη.le
            _ = η := mul_one η
        nlinarith [mul_le_mul_of_nonneg_right h4 hD0.le]
      nlinarith
    linarith
  have E1 : (D : ℝ) * (1 - δ) ^ 2 * (xB + xG) * Real.log 2 ≤
      ℓ / 100 * Real.log 2 + ℓ * Real.log (2 * D + 2) + xS * Real.log 2 +
        xB * ((1 - η) * D * Real.log 2) + xG * (D * Real.log 2) := by
    linarith
  have E2 : (D : ℝ) * (1 - 2 * δ) * (xB + xG) * Real.log 2 ≤
      D * (1 - δ) ^ 2 * (xB + xG) * Real.log 2 := by
    apply mul_le_mul_of_nonneg_right _ hlog2.le
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hδ' hD0.le
  have F1 : (xS + xG / 50 - ℓ) * Real.log 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hlog2.le
  have G1 : 0 ≤ (ℓ : ℝ) * Real.log 2 := mul_nonneg (Nat.cast_nonneg _) hlog2.le
  have Z1 : 2 * xG * Real.log 2 * (D * δ - 1 / 100) = 0 := by rw [hδD]; ring
  have hid : xB * D * Real.log 2 * (η - 2 * δ) -
      ℓ * ((103 / 100) * Real.log 2 + Real.log (2 * D + 2)) =
      ((D : ℝ) * (1 - 2 * δ) * (xB + xG) * Real.log 2 -
        (ℓ / 100 * Real.log 2 + ℓ * Real.log (2 * D + 2) + xS * Real.log 2 +
          xB * ((1 - η) * D * Real.log 2) + xG * (D * Real.log 2))) +
      (xS + xG / 50 - ℓ) * Real.log 2 + 2 * xG * Real.log 2 * (D * δ - 1 / 100) -
        2 / 100 * (ℓ * Real.log 2) := by ring
  have hbad : xB * D * Real.log 2 ≤
      ℓ * ((103 / 100) * Real.log 2 + Real.log (2 * D + 2)) / (η - 2 * δ) := by
    rw [le_div_iff₀ hgap]
    linarith only [hid, E1, E2, F1, G1, Z1]
  have hfinal : Real.log H.card - Real.log H'.card ≤ ℓ * (η * D * Real.log 2) := by
    have H1 : xS * Real.log 2 ≤ ℓ * Real.log 2 := by
      have h : xS ≤ ℓ := by linarith
      exact mul_le_mul_of_nonneg_right h hlog2.le
    have H2 : ∑ s ∈ B, Real.log (R s) ≤ xB * D * Real.log 2 := by
      have := hbBT
      linarith [mul_assoc xB (D : ℝ) (Real.log 2)]
    have hlogs : Real.log H.card - Real.log H'.card ≤
        ℓ * Real.log (2 * D + 2) + ℓ * Real.log 2 + xB * D * Real.log 2 := by
      linarith only [hK3, hK4, hsplit1, hsplit2, hK5, hbSm, H2, H1]
    have harith := arith_cor hη hη1 hD
    rw [← hδ] at harith
    have hm : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
    have H3 := mul_le_mul_of_nonneg_left harith hm
    rw [mul_add, mul_add] at H3
    have hYeq : (ℓ : ℝ) * ((103 / 100) * Real.log 2 + Real.log (2 * D + 2)) / (η - 2 * δ) =
        ℓ * (((103 / 100) * Real.log 2 + Real.log (2 * D + 2)) / (η - 2 * δ)) := by ring
    linarith only [hlogs, hbad, H3, hYeq]
  have hpos' : (0 : ℝ) < (2 : ℝ) ^ (-(η * (ℓ * D : ℕ))) * H.card :=
    mul_pos (Real.rpow_pos_of_pos two_pos _) hHpos
  have hH'pos : (0 : ℝ) < H'.card := by exact_mod_cast card_pos.mpr hH'ne
  rw [← Real.log_le_log_iff hpos' hH'pos, Real.log_mul (by positivity) hHpos.ne',
    Real.log_rpow (by norm_num)]
  have heq : η * ((ℓ * D : ℕ) : ℝ) * Real.log 2 = ℓ * (η * D * Real.log 2) := by
    push_cast; ring
  linarith only [heq, hfinal]

/-- **Corollary 3.10 of Shmerkin, weak form.** -/
theorem corollary310Weak : Corollary310Weak := by
  intro η hη hη1
  filter_upwards [eventually_ge_atTop ⌈400 / η ^ 4⌉₊] with D hD
  have hD' : 400 / η ^ 4 ≤ (D : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hD)
  have hη4 : 0 < η ^ 4 := by positivity
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le (by positivity) hD'
  have hD1 : 1 ≤ D := by exact_mod_cast hDpos
  set δ : ℝ := 1 / (100 * D) with hδ
  have hδpos : 0 < δ := by positivity
  have hδ1 : δ < 1 := by
    rw [hδ, div_lt_one (by positivity)]
    have : (1 : ℝ) ≤ D := by exact_mod_cast hD1
    linarith
  obtain ⟨n, hn, hcore⟩ := dichotomy_core hD1 hδpos hδ1
  refine ⟨1 / (100 * n * D), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 0] with ℓ _
  intro H hH hne hdoub
  exact cor310_of_counting hη hη1 hD' hδ hn rfl ℓ H hH hne hdoub (hcore ℓ)

end Bourgain
end Shmerkin
end BoxLike
