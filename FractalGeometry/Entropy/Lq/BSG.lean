import Mathlib
import FractalGeometry.Entropy.Lq.BSG.Core
import FractalGeometry.Entropy.Lq.Statements

open Finset Filter

open scoped Pointwise

namespace FractalGeometry.Lq

namespace BSG

lemma eventually_poly_le_exp {c : ℝ} (hc : 0 < c) (D : ℝ) (k : ℕ) :
    ∀ᶠ m : ℕ in atTop, D * ((m : ℝ) + 1) ^ k ≤ (2 : ℝ) ^ (c * m) := by
  have hr : 1 < (2 : ℝ) ^ c := Real.one_lt_rpow (by norm_num) hc
  have ht := tendsto_pow_const_div_const_pow_of_one_lt k hr
  set D' : ℝ := max D 1 * 2 ^ k with hD'
  have hD'pos : 0 < D' := by positivity
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / D' by positivity))
  filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1
  have h1 : ((m : ℝ) + 1) ^ k ≤ 2 ^ k * (m : ℝ) ^ k := by
    rw [← mul_pow]
    gcongr
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    linarith
  have h2 : (2 : ℝ) ^ (c * m) = ((2 : ℝ) ^ c) ^ m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [h2]
  have hrm : 0 < ((2 : ℝ) ^ c) ^ m := by positivity
  rw [div_lt_div_iff₀ hrm hD'pos, one_mul] at hm
  calc D * ((m : ℝ) + 1) ^ k ≤ max D 1 * ((m : ℝ) + 1) ^ k := by
        gcongr; exact le_max_left _ _
    _ ≤ max D 1 * (2 ^ k * (m : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left h1 (by have := le_max_right D 1; linarith)
    _ = D' * (m : ℝ) ^ k := by ring
    _ ≤ _ := by linarith

set_option exponentiation.threshold 512 in

lemma bounds_of {M γ L a : ℝ} (J : ℕ) (hM : 1 ≤ M) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hγL : γ ≤ L)
    (ha : 1 ≤ a) (hMa : M ^ 48 ≤ a) (hPa : 2 ^ 300 * γ⁻¹ ^ (J + 100) ≤ a ^ 2) :
    4 * (2 ^ 33 * M ^ 6 / γ ^ 12) ^ 8 ≤ a ^ 3 ∧ (a ^ 3)⁻¹ ≤ L ∧
      2 * (2 ^ 33 * M ^ 6 / γ ^ 12) ^ 4 / L ≤ a ^ 3 ∧ (a ^ 3)⁻¹ ≤ γ ^ (J + 1) / 6 := by
  set P := γ⁻¹ with hP
  have hP1 : 1 ≤ P := one_le_inv_iff₀.2 ⟨hγ, hγ1⟩
  have hPpos : 0 < P := by positivity
  have hγP : γ = P⁻¹ := by rw [hP, inv_inv]
  have hL : 0 < L := lt_of_lt_of_le hγ hγL
  have hPow : ∀ n ≤ J + 100, P ^ n ≤ P ^ (J + 100) := fun n hn => pow_le_pow_right₀ hP1 hn
  have hM48 : 1 ≤ M ^ 48 := one_le_pow₀ hM
  have ha2 : a ^ 2 ≤ a ^ 3 := pow_le_pow_right₀ ha (by norm_num)
  have hmain : 2 ^ 300 * M ^ 48 * P ^ (J + 100) ≤ a ^ 3 := by
    calc 2 ^ 300 * M ^ 48 * P ^ (J + 100) = M ^ 48 * (2 ^ 300 * P ^ (J + 100)) := by ring
      _ ≤ a * a ^ 2 := by gcongr
      _ = a ^ 3 := by ring
  have hkay : 2 ^ 33 * M ^ 6 / γ ^ 12 = 2 ^ 33 * M ^ 6 * P ^ 12 := by
    rw [hγP, inv_pow, div_inv_eq_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hkay]
    calc 4 * (2 ^ 33 * M ^ 6 * P ^ 12) ^ 8 = 2 ^ 266 * M ^ 48 * P ^ 96 := by ring
      _ ≤ 2 ^ 300 * M ^ 48 * P ^ 96 := by gcongr <;> norm_num
      _ ≤ 2 ^ 300 * M ^ 48 * P ^ (J + 100) :=
          mul_le_mul_of_nonneg_left (hPow 96 (by omega)) (by positivity)
      _ ≤ _ := hmain
  · rw [inv_le_comm₀ (by positivity) hL]
    calc L⁻¹ ≤ γ⁻¹ := inv_anti₀ hγ hγL
      _ = P := rfl
      _ ≤ P ^ (J + 100) := by simpa using hPow 1 (by omega)
      _ ≤ 2 ^ 300 * P ^ (J + 100) := le_mul_of_one_le_left (by positivity) (by norm_num)
      _ ≤ a ^ 3 := hPa.trans ha2
  · rw [hkay]
    have hLinv : L⁻¹ ≤ P := inv_anti₀ hγ hγL
    calc 2 * (2 ^ 33 * M ^ 6 * P ^ 12) ^ 4 / L = 2 ^ 133 * M ^ 24 * P ^ 48 * L⁻¹ := by ring
      _ ≤ 2 ^ 133 * M ^ 24 * P ^ 48 * P := by gcongr
      _ = 2 ^ 133 * M ^ 24 * P ^ 49 := by ring
      _ ≤ 2 ^ 300 * M ^ 24 * P ^ 49 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
            (by positivity)
      _ ≤ 2 ^ 300 * M ^ 48 * P ^ 49 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hM (by norm_num)) (by positivity)) (by positivity)
      _ ≤ 2 ^ 300 * M ^ 48 * P ^ (J + 100) :=
          mul_le_mul_of_nonneg_left (hPow 49 (by omega)) (by positivity)
      _ ≤ _ := hmain
  · rw [hγP, inv_pow, inv_le_comm₀ (by positivity) (by positivity)]
    calc ((P ^ (J + 1))⁻¹ / 6)⁻¹ = 6 * P ^ (J + 1) := by rw [inv_div, div_inv_eq_mul]
      _ ≤ 2 ^ 300 * P ^ (J + 1) := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ ≤ 2 ^ 300 * P ^ (J + 100) :=
          mul_le_mul_of_nonneg_left (hPow (J + 1) (by omega)) (by positivity)
      _ ≤ a ^ 3 := hPa.trans ha2

set_option exponentiation.threshold 512 in

lemma eventually_bounds {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ m : ℕ in atTop,
      ((2 : ℝ) ^ ((m : ℝ) / ⌈144 / κ⌉₊)) ^ 48 ≤ (2 : ℝ) ^ (κ * m / 3) ∧
      2 ^ 300 * (gam ((2 : ℝ) ^ (-(κ / (3 * 2 ^ ⌈144 / κ⌉₊ * (⌈144 / κ⌉₊ + 100)) * m)))
        ⌈144 / κ⌉₊ m)⁻¹ ^ (⌈144 / κ⌉₊ + 100) ≤ ((2 : ℝ) ^ (κ * m / 3)) ^ 2 := by
  set J := ⌈144 / κ⌉₊ with hJ
  set τ := κ / (3 * 2 ^ J * (J + 100)) with hτ
  have hJpos : (0 : ℝ) < J := Nat.cast_pos.2 (Nat.ceil_pos.2 (by positivity))
  have hJge : 144 / κ ≤ J := Nat.le_ceil _
  set n : ℕ := 2 ^ J * (J + 100) with hn
  set D : ℝ := 2 ^ 300 * 4 ^ n with hD
  filter_upwards [eventually_poly_le_exp (c := κ / 3) (by positivity) D (J + 100)] with m hm
  have hm0 : (0 : ℝ) ≤ m := by positivity
  constructor
  · rw [← Real.rpow_mul_natCast (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h48 : 48 / (J : ℝ) ≤ κ / 3 := by
      rw [div_le_iff₀ hJpos]
      rw [div_le_iff₀ hκ] at hJge
      linarith
    calc (m : ℝ) / J * (48 : ℕ) = m * (48 / J) := by push_cast; ring
      _ ≤ m * (κ / 3) := by gcongr
      _ = κ * m / 3 := by ring
  · have hεinv : ((2 : ℝ) ^ (-(τ * m)))⁻¹ = 2 ^ (τ * m) := by
      rw [Real.rpow_neg (by norm_num), inv_inv]
    have hgam : (gam ((2 : ℝ) ^ (-(τ * m))) J m)⁻¹ = (m + 1) * (4 * 2 ^ (τ * m)) ^ 2 ^ J := by
      unfold gam lev
      rw [inv_div, div_eq_mul_inv, ← inv_pow, inv_div, div_eq_mul_inv 4, hεinv]
    have h2 : ((2 : ℝ) ^ (τ * m)) ^ n = (2 : ℝ) ^ (κ * m / 3) := by
      rw [← Real.rpow_mul_natCast (by norm_num)]
      congr 1
      rw [hn, hτ]
      push_cast
      field_simp
    have hm' : D * ((m : ℝ) + 1) ^ (J + 100) ≤ (2 : ℝ) ^ (κ * m / 3) := by
      have : κ / 3 * (m : ℝ) = κ * m / 3 := by ring
      rw [this] at hm
      exact hm
    rw [hgam, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← hn, h2]
    calc (2 : ℝ) ^ 300 * ((↑m + 1) ^ (J + 100) * (4 ^ n * 2 ^ (κ * ↑m / 3))) =
        (D * ((m : ℝ) + 1) ^ (J + 100)) * 2 ^ (κ * ↑m / 3) := by rw [hD]; ring
      _ ≤ 2 ^ (κ * ↑m / 3) * 2 ^ (κ * ↑m / 3) := by gcongr
      _ = _ := by ring

end BSG

theorem theorem32 : Theorem32 := by
  intro κ hκ
  set J : ℕ := ⌈144 / κ⌉₊ with hJdef
  set τ : ℝ := κ / (3 * 2 ^ J * (J + 100)) with hτdef
  have hJ : 1 ≤ J := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  refine ⟨τ, by positivity, ?_⟩
  filter_upwards [BSG.eventually_bounds hκ] with m hm
  obtain ⟨hMa, hPa⟩ := hm
  intro A B hE
  set a : ℝ := (2 : ℝ) ^ (κ * m / 3) with ha
  have ha1 : 1 ≤ a := Real.one_le_rpow (by norm_num) (by positivity)
  have ha3 : (2 : ℝ) ^ (κ * m) = a ^ 3 := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1; push_cast; ring
  have ha3' : (2 : ℝ) ^ (-(κ * m)) = (a ^ 3)⁻¹ := by
    rw [Real.rpow_neg (by norm_num), ha3]
  have ha6' : (2 : ℝ) ^ (-(2 * κ * m)) = ((a ^ 3)⁻¹) ^ 2 := by
    rw [← ha3', ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1; push_cast; ring
  have hκm : (1 : ℝ) ≤ 2 ^ (κ * m) := Real.one_le_rpow (by norm_num) (by positivity)
  have hκm' : (2 : ℝ) ^ (-(κ * m)) ≤ 1 := by
    rw [ha3']; exact inv_le_one_of_one_le₀ (one_le_pow₀ ha1)
  have hN : ∀ S : Finset (ZMod (2 ^ m)), #S ≤ 2 ^ m := fun S => by
    simpa [ZMod.card] using card_le_univ S
  rcases A.eq_empty_or_nonempty with rfl | hA
  · refine ⟨univ, ∅, ?_, by simp, by simp, ?_⟩
    · have : #(univ + univ : Finset (ZMod (2 ^ m))) ≤ #(univ : Finset (ZMod (2 ^ m))) :=
        card_le_univ _
      calc (#(univ + univ : Finset (ZMod (2 ^ m))) : ℝ) ≤ #(univ : Finset (ZMod (2 ^ m))) := by
            exact_mod_cast this
        _ ≤ _ := le_mul_of_one_le_left (by positivity) hκm
    · rw [inter_univ]
      exact mul_le_of_le_one_left (by positivity) hκm'
  rcases B.eq_empty_or_nonempty with rfl | hB
  · refine ⟨0, A, ?_, ?_, ?_, by simp⟩
    · rw [add_zero, card_zero]; simpa using hκm
    · rw [add_zero, inter_self]
      exact mul_le_of_le_one_left (by positivity) hκm'
    · rw [card_zero, Nat.cast_one, mul_one]
      gcongr
      · exact one_le_two
      · linarith

  set ε : ℝ := (2 : ℝ) ^ (-(τ * m)) with hεdef
  set M : ℝ := (2 : ℝ) ^ ((m : ℝ) / J) with hMdef
  have hε : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by
    have : 0 ≤ τ * m := by positivity
    linarith)
  have hM : 1 ≤ M := Real.one_le_rpow (by norm_num) (by positivity)
  have hMJ : (2 : ℝ) ^ m ≤ M ^ J := by
    have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast (by omega : J ≠ 0)
    have : ((2 : ℝ) ^ ((m : ℝ) / J)) ^ J = (2 : ℝ) ^ (m : ℝ) := by
      rw [← Real.rpow_mul_natCast (by norm_num)]
      congr 1
      field_simp
    rw [hMdef, this, Real.rpow_natCast]
  obtain ⟨H, X, h1, h2, h3, h4⟩ := BSG.core A B hA hB m hN hε hε1 hE hJ hM hMJ
  have hγ : 0 < BSG.gam ε J m := by unfold BSG.gam BSG.lev; positivity
  have hγ1 : BSG.gam ε J m ≤ 1 := by
    unfold BSG.gam BSG.lev
    rw [div_le_one (by positivity)]
    have : (ε / 4) ^ 2 ^ J ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
    have : (0 : ℝ) ≤ m := by positivity
    linarith
  have hγL : BSG.gam ε J m ≤ BSG.lev ε J := by
    unfold BSG.gam
    rw [div_le_iff₀ (by positivity)]
    have : 0 < BSG.lev ε J := by unfold BSG.lev; positivity
    have : (0 : ℝ) ≤ m := by positivity
    nlinarith
  obtain ⟨b1, b2, b3, b4⟩ := BSG.bounds_of J hM hγ hγ1 hγL ha1 hMa hPa
  refine ⟨H, X, ?_, ?_, ?_, ?_⟩
  · rw [ha3]
    calc (#(H + H) : ℝ) ≤ 4 * BSG.kay ε M J m ^ 8 * #H := h1
      _ ≤ a ^ 3 * #H := by gcongr; exact b1
  · rw [ha3']
    calc (a ^ 3)⁻¹ * #A ≤ BSG.lev ε J * #A := by gcongr
      _ ≤ _ := h2
  · rw [ha3', ha6']
    have : (#X : ℝ) * #H ≤ a ^ 3 * #A := by
      calc (#X : ℝ) * #H ≤ 2 * BSG.kay ε M J m ^ 4 / BSG.lev ε J * #A := h3
        _ ≤ a ^ 3 * #A := by gcongr; exact b3
    have hpos : 0 < (a ^ 3)⁻¹ := by positivity
    calc ((a ^ 3)⁻¹) ^ 2 * #X * #H = ((a ^ 3)⁻¹) ^ 2 * (#X * #H) := by ring
      _ ≤ ((a ^ 3)⁻¹) ^ 2 * (a ^ 3 * #A) := by gcongr
      _ = (a ^ 3)⁻¹ * #A := by field_simp
  · rw [ha3']
    calc (a ^ 3)⁻¹ * #B ≤ BSG.gam ε J m ^ (J + 1) / 6 * #B := by gcongr
      _ ≤ _ := h4

end FractalGeometry.Lq
