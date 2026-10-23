import Mathlib
import FractalGeometry.Entropy.Lq.Bourgain.Main
import FractalGeometry.Entropy.Lq.Inverse.Analytic
import FractalGeometry.Entropy.Lq.Inverse.Basic
import FractalGeometry.Entropy.Lq.Inverse.Cor310
import FractalGeometry.Entropy.Lq.Inverse.Trees
import FractalGeometry.Entropy.Lq.Statements
import FractalGeometry.Entropy.Lq.Theorem51

open Filter Topology

open scoped Pointwise

namespace FractalGeometry

namespace Lq

namespace Inverse

theorem translate_mem (m : ℕ) (y a : ℤ) : 0 ≤ (y + a) % 2 ^ m ∧ (y + a) % 2 ^ m < 2 ^ m :=
  ⟨Int.emod_nonneg _ (by positivity), Int.emod_lt_of_pos _ (by positivity)⟩

theorem inUnit_image_translate (m : ℕ) (a : ℤ) (A : Finset ℤ) :
    InUnit m (A.image fun y => (y + a) % 2 ^ m) := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
  exact translate_mem m y a

theorem card_image_translate {m : ℕ} {A : Finset ℤ} (hA : InUnit m A) (a : ℤ) :
    (A.image fun y => (y + a) % 2 ^ m).card = A.card := by
  refine Finset.card_image_of_injOn fun y₁ h₁ y₂ h₂ h => ?_
  have h₁' := hA y₁ h₁
  have h₂' := hA y₂ h₂
  have h3 : y₁ % 2 ^ m = y₂ % 2 ^ m := Int.ModEq.add_right_cancel' a h
  rwa [Int.emod_eq_of_lt h₁'.1 h₁'.2, Int.emod_eq_of_lt h₂'.1 h₂'.2] at h3

theorem circTranslate_translate {m : ℕ} (a : ℤ) (μ : ℤ → ℝ) {y : ℤ} (hy : 0 ≤ y ∧ y < 2 ^ m) :
    circTranslate m a μ ((y + a) % 2 ^ m) = μ y := by
  unfold circTranslate
  rw [ite_eq_of_pos (translate_mem m y a)]
  congr 1
  rw [Int.sub_emod, Int.emod_emod_of_dvd _ (dvd_refl _), ← Int.sub_emod, add_sub_cancel_right]
  exact Int.emod_eq_of_lt hy.1 hy.2

theorem cast_translate (m : ℕ) (y a : ℤ) :
    (((y + a) % 2 ^ m : ℤ) : ZMod (2 ^ m)) = (y : ZMod (2 ^ m)) + (a : ZMod (2 ^ m)) := by
  have := ZMod.intCast_mod (y + a) (2 ^ m)
  push_cast at this
  exact this

theorem card_filter_cast {m : ℕ} {A : Finset ℤ} (hA : InUnit m A) (Z : Finset (ZMod (2 ^ m))) :
    (A.filter fun x : ℤ => (x : ZMod (2 ^ m)) ∈ Z).card =
      (A.image (Int.cast : ℤ → ZMod (2 ^ m)) ∩ Z).card := by
  classical
  rw [← card_image_cast (A := A.filter fun x : ℤ => (x : ZMod (2 ^ m)) ∈ Z)
    (fun x hx => hA x (Finset.mem_filter.mp hx).1)]
  congr 1
  ext w
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨x, ⟨hx, hxZ⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, hxZ⟩
  · rintro ⟨⟨x, hx, rfl⟩, hxZ⟩
    exact ⟨x, ⟨hx, hxZ⟩, rfl⟩

theorem sum_rpow_ge_of_flat {A A₁ : Finset ℤ} {μ μ' : ℤ → ℝ} {q : ℝ} (hq : 0 ≤ q)
    (hpos : ∀ x ∈ A₁, 0 < μ x) (hflat : ∀ x ∈ A₁, ∀ y ∈ A₁, μ y ≤ 2 * μ x)
    (hσ : ∀ x ∈ A, ∃ y ∈ A₁, μ' x = μ y) :
    (2 : ℝ) ^ (-q) * A.card * ∑ y ∈ A₁, μ y ^ q ≤ A₁.card * ∑ x ∈ A, μ' x ^ q := by
  have key : ∀ x ∈ A, (2 : ℝ) ^ (-q) * ∑ y ∈ A₁, μ y ^ q ≤ A₁.card * μ' x ^ q := by
    intro x hx
    obtain ⟨y₀, hy₀, hxy⟩ := hσ x hx
    rw [hxy]
    have h1 : ∀ y ∈ A₁, μ y ^ q ≤ (2 : ℝ) ^ q * μ y₀ ^ q := by
      intro y hy
      rw [← Real.mul_rpow (by norm_num) (hpos y₀ hy₀).le]
      exact Real.rpow_le_rpow (hpos y hy).le (hflat y₀ hy₀ y hy) hq
    calc (2 : ℝ) ^ (-q) * ∑ y ∈ A₁, μ y ^ q
        ≤ (2 : ℝ) ^ (-q) * ∑ y ∈ A₁, (2 : ℝ) ^ q * μ y₀ ^ q := by
          gcongr with y hy; exact h1 y hy
      _ = A₁.card * μ y₀ ^ q := by
          rw [Finset.sum_const, nsmul_eq_mul, show (2 : ℝ) ^ (-q) * (A₁.card * ((2 : ℝ) ^ q *
            μ y₀ ^ q)) = A₁.card * ((2 : ℝ) ^ (-q) * 2 ^ q) * μ y₀ ^ q by ring,
            ← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero, mul_one]
  calc (2 : ℝ) ^ (-q) * A.card * ∑ y ∈ A₁, μ y ^ q
      = ∑ x ∈ A, (2 : ℝ) ^ (-q) * ∑ y ∈ A₁, μ y ^ q := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ x ∈ A, (A₁.card : ℝ) * μ' x ^ q := Finset.sum_le_sum key
    _ = A₁.card * ∑ x ∈ A, μ' x ^ q := by rw [Finset.mul_sum]

theorem numeric_scales {c δ₁ m D s s' X0 : ℝ} (hδ₁ : 0 < δ₁) (hc : c = δ₁ ^ 2 / 64)
    (hδ₁1 : δ₁ ≤ 1) (hX0 : X0 ≤ 6 * c * m) (hD : 0 ≤ D) (hs' : 0 ≤ s') (hSm : D * s ≤ m)
    (hexp : (1 - c) * D * (s + s') ≤ X0 + (D * s + (1 - δ₁) * D * s')) :
    D * s' ≤ δ₁ * m / 4 := by
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have h1 : (δ₁ - c) * (D * s') ≤ 7 * c * m := by
    have : c * (D * s) ≤ c * m := mul_le_mul_of_nonneg_left hSm hc0
    nlinarith
  have hcδ : c ≤ δ₁ / 64 := by
    have : δ₁ ^ 2 ≤ δ₁ := by nlinarith
    rw [hc]; linarith
  have hY : 0 ≤ D * s' := mul_nonneg hD hs'
  have h2 : δ₁ * ((63 / 64) * (D * s')) ≤ δ₁ * (7 * δ₁ * m / 64) := by
    rw [hc] at h1; nlinarith
  have h3 := le_of_mul_le_mul_left h2 hδ₁
  nlinarith

theorem lq_A_numeric {q c δ₁ ε κ m P T nA nA₁ S₁ : ℝ} (hq : 1 ≤ q) (hc : c ≤ δ₁ / 64)
    (hε : ε ≤ c / 4) (hκ : κ ≤ c) (hmc : 1 ≤ c * m) (hm : 0 ≤ m) (hP : 0 ≤ P) (hnA : 0 < nA)
    (h1 : (2 : ℝ) ^ (-q) * nA * S₁ ≤ nA₁ * T) (h2 : (2 : ℝ) ^ (-(2 * ε * q * m)) * P ≤ S₁)
    (h3 : nA₁ ≤ (2 : ℝ) ^ (κ * m) * ((2 : ℝ) ^ (c * m) * nA)) (hT : 0 ≤ T) :
    (2 : ℝ) ^ (-(q * δ₁ * m)) * P ≤ T := by
  have hc0 : 0 ≤ c := by
    by_contra h
    push Not at h
    nlinarith
  have e1 : nA * ((2 : ℝ) ^ (-q) * (2 : ℝ) ^ (-(2 * ε * q * m)) * P) ≤
      nA * ((2 : ℝ) ^ (κ * m) * (2 : ℝ) ^ (c * m) * T) := by
    have : (2 : ℝ) ^ (-q) * nA * ((2 : ℝ) ^ (-(2 * ε * q * m)) * P) ≤
        (2 : ℝ) ^ (-q) * nA * S₁ := mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : nA₁ * T ≤ (2 : ℝ) ^ (κ * m) * ((2 : ℝ) ^ (c * m) * nA) * T :=
      mul_le_mul_of_nonneg_right h3 hT
    nlinarith
  have e2 := le_of_mul_le_mul_left e1 hnA
  have e3 : (2 : ℝ) ^ (-(q * δ₁ * m)) ≤
      (2 : ℝ) ^ (-(κ * m)) * (2 : ℝ) ^ (-(c * m)) * ((2 : ℝ) ^ (-q) *
        (2 : ℝ) ^ (-(2 * ε * q * m))) := by
    simp only [← Real.rpow_add two_pos]
    apply Real.rpow_le_rpow_of_exponent_le one_le_two
    have : κ * m ≤ c * m := mul_le_mul_of_nonneg_right hκ hm
    have : ε * m ≤ c / 4 * m := mul_le_mul_of_nonneg_right hε hm
    have : q * (c * m) ≤ q * (δ₁ / 64 * m) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hc hm) (by linarith)
    have : c * m ≤ q * (c * m) := le_mul_of_one_le_left (by nlinarith) hq
    have : 2 * ε * q * m = 2 * q * (ε * m) := by ring
    have : 2 * q * (ε * m) ≤ 2 * q * (c / 4 * m) := mul_le_mul_of_nonneg_left
      (by assumption) (by linarith)
    nlinarith
  calc (2 : ℝ) ^ (-(q * δ₁ * m)) * P
      ≤ (2 : ℝ) ^ (-(κ * m)) * (2 : ℝ) ^ (-(c * m)) * ((2 : ℝ) ^ (-q) *
        (2 : ℝ) ^ (-(2 * ε * q * m))) * P := mul_le_mul_of_nonneg_right e3 hP
    _ = (2 : ℝ) ^ (-(κ * m)) * (2 : ℝ) ^ (-(c * m)) * ((2 : ℝ) ^ (-q) *
        (2 : ℝ) ^ (-(2 * ε * q * m)) * P) := by ring
    _ ≤ (2 : ℝ) ^ (-(κ * m)) * (2 : ℝ) ^ (-(c * m)) *
        ((2 : ℝ) ^ (κ * m) * (2 : ℝ) ^ (c * m) * T) :=
        mul_le_mul_of_nonneg_left e2 (by positivity)
    _ = ((2 : ℝ) ^ (-(κ * m)) * (2 : ℝ) ^ (κ * m)) * ((2 : ℝ) ^ (-(c * m)) *
        (2 : ℝ) ^ (c * m)) * T := by ring
    _ = T := by
        rw [← Real.rpow_add two_pos, ← Real.rpow_add two_pos, neg_add_cancel, neg_add_cancel,
          Real.rpow_zero, one_mul, one_mul]

theorem mass_B_numeric {c δ₁ ε κ m ℓ Ds T nB nB₁ S₁ : ℝ} (hc : c ≤ δ₁ / 64) (hε : ε ≤ c / 4)
    (hκ : κ ≤ c) (hmc : 1 ≤ c * m) (hℓ : ℓ ≤ c * m) (hDs : Ds ≤ δ₁ * m / 4) (hm : 0 ≤ m)
    (hnB : 0 < nB) (h1 : (2 : ℝ) ^ (-1 : ℝ) * nB * S₁ ≤ nB₁ * T)
    (h2 : (2 : ℝ) ^ (-(2 * ε * m)) ≤ S₁)
    (h3 : nB₁ ≤ (2 : ℝ) ^ (κ * m) * ((2 : ℝ) ^ (c * m) *
      ((2 : ℝ) ^ (ℓ + 1 + κ * m + c * m) * (2 : ℝ) ^ Ds * nB))) (hT : 0 ≤ T) :
    (2 : ℝ) ^ (-(δ₁ * m)) ≤ T := by
  set E := κ * m + c * m + (ℓ + 1 + κ * m + c * m) + Ds with hE
  have h3' : nB₁ ≤ (2 : ℝ) ^ E * nB := by
    rw [hE]; simp only [Real.rpow_add two_pos] at h3 ⊢; linarith
  have e1 : nB * ((2 : ℝ) ^ (-1 : ℝ) * (2 : ℝ) ^ (-(2 * ε * m))) ≤ nB * ((2 : ℝ) ^ E * T) := by
    have : (2 : ℝ) ^ (-1 : ℝ) * nB * (2 : ℝ) ^ (-(2 * ε * m)) ≤ (2 : ℝ) ^ (-1 : ℝ) * nB * S₁ :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : nB₁ * T ≤ (2 : ℝ) ^ E * nB * T := mul_le_mul_of_nonneg_right h3' hT
    nlinarith
  have e2 := le_of_mul_le_mul_left e1 hnB
  have e3 : (2 : ℝ) ^ (-(δ₁ * m)) ≤ (2 : ℝ) ^ (-E) * ((2 : ℝ) ^ (-1 : ℝ) *
      (2 : ℝ) ^ (-(2 * ε * m))) := by
    simp only [← Real.rpow_add two_pos]
    apply Real.rpow_le_rpow_of_exponent_le one_le_two
    have : κ * m ≤ c * m := mul_le_mul_of_nonneg_right hκ hm
    have : ε * m ≤ c / 4 * m := mul_le_mul_of_nonneg_right hε hm
    have : c * m ≤ δ₁ / 64 * m := mul_le_mul_of_nonneg_right hc hm
    rw [hE]; nlinarith
  calc (2 : ℝ) ^ (-(δ₁ * m)) ≤ (2 : ℝ) ^ (-E) * ((2 : ℝ) ^ (-1 : ℝ) *
      (2 : ℝ) ^ (-(2 * ε * m))) := e3
    _ ≤ (2 : ℝ) ^ (-E) * ((2 : ℝ) ^ E * T) := mul_le_mul_of_nonneg_left e2 (by positivity)
    _ = T := by rw [← mul_assoc, ← Real.rpow_add two_pos, neg_add_cancel, Real.rpow_zero, one_mul]

theorem isDyadicMeasure_circTranslate {m : ℕ} {μ : ℤ → ℝ} (hμ : IsDyadicMeasure m μ) (a : ℤ) :
    IsDyadicMeasure m (circTranslate m a μ) := by
  refine ⟨fun k => ?_, fun k hk => ?_, ?_⟩
  · unfold circTranslate; split_ifs
    · exact hμ.nonneg _
    · exact le_rfl
  · unfold circTranslate at hk; split_ifs at hk with h
    · exact h
    · exact absurd rfl hk
  · have h := discLq_circTranslate m 1 a μ
    unfold discLq at h
    simp only [Real.rpow_one] at h
    rw [h, hμ.sum_eq_one]

theorem discLq_le_one {m : ℕ} {μ : ℤ → ℝ} (hμ : IsDyadicMeasure m μ) {q : ℝ} (hq : 1 ≤ q) :
    discLq m q μ ≤ 1 := by
  unfold discLq
  calc ∑ k ∈ Finset.Ico (0 : ℤ) (2 ^ m), μ k ^ q ≤ ∑ k ∈ Finset.Ico (0 : ℤ) (2 ^ m), μ k := by
        refine Finset.sum_le_sum fun k hk => ?_
        have h0 := hμ.nonneg k
        have h1 : μ k ≤ 1 := by
          calc μ k ≤ ∑ j ∈ Finset.Ico (0 : ℤ) (2 ^ m), μ j :=
                Finset.single_le_sum (fun j _ => hμ.nonneg j) hk
            _ = 1 := hμ.sum_eq_one
        calc μ k ^ q ≤ μ k ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge' h0 h1 zero_le_one hq
          _ = μ k := Real.rpow_one _
    _ = 1 := hμ.sum_eq_one

theorem sum_le_one_of_inUnit {m : ℕ} {μ : ℤ → ℝ} (hμ : IsDyadicMeasure m μ) {A : Finset ℤ}
    (hA : InUnit m A) : ∑ x ∈ A, μ x ≤ 1 := by
  rw [← hμ.sum_eq_one]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => Finset.mem_Ico.mpr (hA x hx))
    (fun x _ _ => hμ.nonneg x)

theorem logb_card_le_of_flat {q a P : ℝ} (hq : 1 < q) {A : Finset ℤ} {μ : ℤ → ℝ}
    (hne : A.Nonempty) (hpos : ∀ x ∈ A, 0 < μ x) (hflat : ∀ x ∈ A, ∀ y ∈ A, μ y ≤ 2 * μ x)
    (hsum : ∑ x ∈ A, μ x ≤ 1) (hP : 0 < P) (h : (2 : ℝ) ^ (-a) * P ≤ ∑ x ∈ A, μ x ^ q) :
    (q - 1) * Real.logb 2 A.card ≤ q + a - Real.logb 2 P := by
  obtain ⟨y₀, hy₀, hmax⟩ := A.exists_max_image μ hne
  set M := μ y₀ with hM
  have hM0 : 0 < M := hpos y₀ hy₀
  have hA0 : (0 : ℝ) < A.card := by exact_mod_cast hne.card_pos
  have h1 : ∑ x ∈ A, μ x ^ q ≤ A.card * M ^ q := by
    calc ∑ x ∈ A, μ x ^ q ≤ ∑ _x ∈ A, M ^ q := Finset.sum_le_sum fun x hx =>
          Real.rpow_le_rpow (hpos x hx).le (hmax x hx) (by linarith)
      _ = A.card * M ^ q := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : A.card * M ≤ 2 := by
    have : ∑ _x ∈ A, M ≤ ∑ x ∈ A, 2 * μ x := Finset.sum_le_sum fun x hx => hflat x hx y₀ hy₀
    rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at this
    linarith
  have hM2 : M ≤ 2 / A.card := by rw [le_div_iff₀ hA0]; linarith
  have h3 : (2 : ℝ) ^ (-a) * P ≤ A.card * (2 / A.card) ^ q :=
    le_trans h (le_trans h1 (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hM0.le hM2 (by linarith)) hA0.le))
  have h4 := Real.logb_le_logb_of_le one_lt_two (by positivity) h3
  rw [Real.logb_mul (by positivity) hP.ne', Real.logb_rpow two_pos (by norm_num),
    Real.logb_mul hA0.ne' (by positivity), Real.logb_rpow_eq_mul_logb_of_pos (by positivity),
    Real.logb_div (by norm_num) hA0.ne', Real.logb_self_eq_one one_lt_two] at h4
  nlinarith

theorem logb_lq_ge_of_flat {q : ℝ} (hq : 0 ≤ q) {B : Finset ℤ} {ν : ℤ → ℝ} (hne : B.Nonempty)
    (hpos : ∀ y ∈ B, 0 < ν y) (hflat : ∀ x ∈ B, ∀ y ∈ B, ν y ≤ 2 * ν x) :
    (1 - q) * Real.logb 2 B.card + q * (Real.logb 2 (∑ y ∈ B, ν y) - 1) ≤
      Real.logb 2 (∑ y ∈ B, ν y ^ q) := by
  have hB0 : (0 : ℝ) < B.card := by exact_mod_cast hne.card_pos
  have hS0 : 0 < ∑ y ∈ B, ν y := Finset.sum_pos hpos hne
  set t := (∑ y ∈ B, ν y) / (2 * B.card) with ht
  have ht0 : 0 < t := by positivity
  have hty : ∀ y ∈ B, t ≤ ν y := by
    intro y hy
    rw [ht, div_le_iff₀ (by positivity)]
    have : ∑ x ∈ B, ν x ≤ ∑ _x ∈ B, 2 * ν y := Finset.sum_le_sum fun x hx => hflat y hy x hx
    rw [Finset.sum_const, nsmul_eq_mul] at this
    linarith
  have h1 : B.card * t ^ q ≤ ∑ y ∈ B, ν y ^ q := by
    calc B.card * t ^ q = ∑ _y ∈ B, t ^ q := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ y ∈ B, ν y ^ q := Finset.sum_le_sum fun y hy =>
          Real.rpow_le_rpow ht0.le (hty y hy) hq
  have h2 := Real.logb_le_logb_of_le one_lt_two (by positivity) h1
  rw [Real.logb_mul hB0.ne' (by positivity), Real.logb_rpow_eq_mul_logb_of_pos ht0, ht,
    Real.logb_div hS0.ne' (by positivity), Real.logb_mul (by norm_num) hB0.ne',
    Real.logb_self_eq_one one_lt_two] at h2
  linarith

theorem lq_root {q δ m P T : ℝ} (hq : 0 < q) (hP : 0 ≤ P)
    (h : (2 : ℝ) ^ (-(q * δ * m)) * P ≤ T) : (2 : ℝ) ^ (-(δ * m)) * P ^ (1 / q) ≤ T ^ (1 / q) := by
  have h1 : ((2 : ℝ) ^ (-(q * δ * m)) * P) ^ (1 / q) ≤ T ^ (1 / q) :=
    Real.rpow_le_rpow (by positivity) h (by positivity)
  rwa [Real.mul_rpow (by positivity) hP, ← Real.rpow_mul (by norm_num),
    show -(q * δ * m) * (1 / q) = -(δ * m) by field_simp] at h1

theorem flat_restrict_bound {a b c n n' S T P : ℝ} (hn' : 0 < n')
    (h : (2 : ℝ) ^ (-a) * n' * S ≤ n * T) (hS : (2 : ℝ) ^ (-b) * P ≤ S)
    (hn : n ≤ n' * (2 : ℝ) ^ c) (hT : 0 ≤ T) : (2 : ℝ) ^ (-(a + b + c)) * P ≤ T := by
  have e1 : n' * ((2 : ℝ) ^ (-a) * (2 : ℝ) ^ (-b) * P) ≤ n' * ((2 : ℝ) ^ c * T) := by
    have h1 : (2 : ℝ) ^ (-a) * n' * ((2 : ℝ) ^ (-b) * P) ≤ (2 : ℝ) ^ (-a) * n' * S :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    have h2 : n * T ≤ n' * (2 : ℝ) ^ c * T := mul_le_mul_of_nonneg_right hn hT
    nlinarith
  have e2 := le_of_mul_le_mul_left e1 hn'
  calc (2 : ℝ) ^ (-(a + b + c)) * P = (2 : ℝ) ^ (-c) * ((2 : ℝ) ^ (-a) * (2 : ℝ) ^ (-b) * P) := by
        rw [show -(a + b + c) = -c + (-a + -b) by ring, Real.rpow_add two_pos,
          Real.rpow_add two_pos]; ring
    _ ≤ (2 : ℝ) ^ (-c) * ((2 : ℝ) ^ c * T) := mul_le_mul_of_nonneg_left e2 (by positivity)
    _ = T := by rw [← mul_assoc, ← Real.rpow_add two_pos, neg_add_cancel, Real.rpow_zero, one_mul]

theorem vi_constants {q q' δ δ₁ m D x : ℝ} (hq : 1 ≤ q) (hq' : 0 < q') (hδ : 0 < δ)
    (hδ₁ : 0 < δ₁) (hm : 0 ≤ m) (hδ₁δ : δ₁ * (2 * (q' + 1) * (q' + q + 1)) ≤ δ)
    (hm1 : q + q' + D ≤ q * δ * m / 2) (hm2 : 1 + q' + D ≤ δ * m / 2)
    (hm3 : q' * (2 + q' + D) ≤ δ * m / 2) (hx : x ≤ q' * (1 + δ₁ * m) + D) :
    q + q * δ₁ * m + x ≤ q * δ * m ∧ 1 + δ₁ * m + x ≤ δ * m ∧
      q' * (1 + (1 + δ₁ * m + x)) ≤ δ * m := by
  have hm' : 0 ≤ δ₁ * m := mul_nonneg hδ₁.le hm
  have k1 : (q' + q) * δ₁ ≤ q * δ / 2 := by
    have : (q' + q) * 2 ≤ 2 * (q' + 1) * (q' + q + 1) := by nlinarith
    have : 2 * ((q' + q) * δ₁) ≤ δ := by nlinarith
    nlinarith
  have k2 : (1 + q') * δ₁ ≤ δ / 2 := by
    have : (1 + q') * 2 ≤ 2 * (q' + 1) * (q' + q + 1) := by nlinarith
    nlinarith
  have k3 : q' * (1 + q') * δ₁ ≤ δ / 2 := by
    have : q' * (1 + q') * 2 ≤ 2 * (q' + 1) * (q' + q + 1) := by nlinarith
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have : (q' + q) * δ₁ * m ≤ q * δ / 2 * m := mul_le_mul_of_nonneg_right k1 hm
    nlinarith
  · have : (1 + q') * δ₁ * m ≤ δ / 2 * m := mul_le_mul_of_nonneg_right k2 hm
    nlinarith
  · have : q' * (1 + q') * δ₁ * m ≤ δ / 2 * m := mul_le_mul_of_nonneg_right k3 hm
    have : q' * x ≤ q' * (q' * (1 + δ₁ * m) + D) := mul_le_mul_of_nonneg_left hx hq'.le
    nlinarith

structure CoreConclusion (q δ : ℝ) (ℓ D : ℕ) (μ ν : ℤ → ℝ) (A B : Finset ℤ)
    (R' R'' : ℕ → ℕ) : Prop where
  unit_A : InUnit (ℓ * D) A
  unit_B : InUnit (ℓ * D) B
  ne_A : A.Nonempty
  ne_B : B.Nonempty
  pos_A : ∀ x ∈ A, 0 < μ x
  pos_B : ∀ y ∈ B, 0 < ν y
  lq_A : (2 : ℝ) ^ (-(q * δ * (ℓ * D : ℕ))) * discLq (ℓ * D) q μ ≤ ∑ x ∈ A, μ x ^ q
  flat_A : ∀ x ∈ A, ∀ y ∈ A, μ y ≤ 2 * μ x
  regular_A : IsUniform D ℓ A R'
  middle_A : ∀ x ∈ A, ∀ s < ℓ, InMiddleHalf (ℓ * D - s * D) x
  mass_B : (2 : ℝ) ^ (-(δ * (ℓ * D : ℕ))) ≤ ∑ y ∈ B, ν y
  flat_B : ∀ x ∈ B, ∀ y ∈ B, ν y ≤ 2 * ν x
  regular_B : IsUniform D ℓ B R''
  middle_B : ∀ y ∈ B, ∀ s < ℓ, InMiddleHalf (ℓ * D - s * D) y
  dichotomy : ∀ s < ℓ, R'' s = 1 ∨ (2 : ℝ) ^ ((1 - δ) * D) ≤ R' s

set_option maxHeartbeats 2000000 in

theorem inverseConclusion_of_core {q δ : ℝ} (hq : 1 < q) (hδ : 0 < δ) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ 1 ∧ ∀ D : ℕ, 1 ≤ D → ∀ᶠ ℓ : ℕ in atTop,
      ∀ μ ν : ℤ → ℝ, IsDyadicMeasure (ℓ * D) μ → IsDyadicMeasure (ℓ * D) ν →
      ∀ A B : Finset ℤ, ∀ R' R'' : ℕ → ℕ, CoreConclusion q δ₁ ℓ D μ ν A B R' R'' →
      ∃ A' B' : Finset ℤ, ∃ R'₂ R''₂ : ℕ → ℕ, InverseConclusion q δ ℓ D μ ν A' B' R'₂ R''₂ := by
  classical
  have hq1 : 0 < q - 1 := by linarith
  set q' := q / (q - 1) with hq'
  have hq'0 : 0 < q' := by positivity
  set δ₁ := min 1 (δ / (2 * (q' + 1) * (q' + q + 1))) with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min one_pos (by positivity)
  have hδ₁1 : δ₁ ≤ 1 := min_le_left _ _
  have hδ₁δ : δ₁ * (2 * (q' + 1) * (q' + q + 1)) ≤ δ := by
    have := min_le_right 1 (δ / (2 * (q' + 1) * (q' + q + 1)))
    rwa [le_div_iff₀ (by positivity)] at this
  have hδ₁δ' : δ₁ ≤ δ := by
    have : 1 ≤ 2 * (q' + 1) * (q' + q + 1) := by nlinarith
    nlinarith
  refine ⟨δ₁, hδ₁0, hδ₁1, fun D hD => ?_⟩
  have hT : Tendsto (fun ℓ : ℕ => ((ℓ * D : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_mul_right_atTop hD)
  filter_upwards [hT.eventually (eventually_ge_atTop (2 * (q + q' + D) / (q * δ))),
    hT.eventually (eventually_ge_atTop (2 * (1 + q' + D) / δ)),
    hT.eventually (eventually_ge_atTop (2 * (q' * (2 + q' + D)) / δ))] with ℓ hm1 hm2 hm3
  intro μ ν hμ hν A B R' R'' hc
  set m := ℓ * D with hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hm1' : q + q' + D ≤ q * δ * m / 2 := by
    rw [div_le_iff₀ (by positivity)] at hm1; linarith
  have hm2' : 1 + q' + D ≤ δ * m / 2 := by rw [div_le_iff₀ hδ] at hm2; linarith
  have hm3' : q' * (2 + q' + D) ≤ δ * m / 2 := by rw [div_le_iff₀ hδ] at hm3; linarith

  set P := discLq m q μ with hPdef
  have hP0 : 0 < P := discLq_pos hμ q
  have hP1 : P ≤ 1 := discLq_le_one hμ hq.le
  set L := Real.logb 2 (P ^ (-(1 / (q - 1)))) with hLdef
  have hL : L = -(1 / (q - 1)) * Real.logb 2 P := Real.logb_rpow_eq_mul_logb_of_pos hP0
  have hlogP : Real.logb 2 P ≤ 0 := Real.logb_nonpos one_lt_two hP0.le hP1
  have hL0 : 0 ≤ L := by
    rw [hL]; have : 0 < 1 / (q - 1) := by positivity
    nlinarith

  set e := q' * (1 + δ₁ * m) with he
  have he0 : 0 ≤ e := by positivity
  have hlogA : Real.logb 2 A.card ≤ e + L := by
    have h := logb_card_le_of_flat (a := q * δ₁ * m) hq hc.ne_A hc.pos_A hc.flat_A
      (sum_le_one_of_inUnit hμ hc.unit_A) hP0 hc.lq_A
    have e1 : (q - 1) * (e + L) = q + q * δ₁ * m - Real.logb 2 P := by
      rw [hL, he, hq']; field_simp; ring
    rw [← e1] at h
    exact le_of_mul_le_mul_left h hq1

  set S := fullScales δ ℓ D R' with hSdef
  have hSsub : S ⊆ Finset.range ℓ := Finset.filter_subset _ _
  have hR'1 := hc.regular_A.one_le hc.ne_A
  have hR'2 := hc.regular_A.le_two_pow hc.ne_A
  have hSA : (1 - δ) * D * S.card ≤ Real.logb 2 A.card := by
    have h1 : ∏ s ∈ S, R' s ≤ A.card := by
      rw [hc.regular_A.card_eq hc.unit_A hc.ne_A]
      exact Finset.prod_le_prod_of_subset_of_one_le hSsub fun s hs _ =>
        hR'1 s (Finset.mem_range.mp hs)
    have h2 := pow_card_le_prod_real (T := S) (f := R') (a := (2 : ℝ) ^ ((1 - δ) * D))
      (by positivity) fun s hs => (Finset.mem_filter.mp hs).2
    have h3 : ((2 : ℝ) ^ ((1 - δ) * D)) ^ S.card ≤ A.card :=
      le_trans h2 (by exact_mod_cast h1)
    rw [two_rpow_pow] at h3
    have h4 := Real.logb_le_logb_of_le one_lt_two (by positivity) h3
    rwa [Real.logb_rpow two_pos (by norm_num)] at h4
  have hSm : (D : ℝ) * S.card ≤ m := by
    have h1 : S.card ≤ ℓ := by
      simpa using Finset.card_le_card hSsub
    have h2 : (S.card : ℝ) ≤ ℓ := by exact_mod_cast h1
    calc (D : ℝ) * S.card ≤ D * ℓ := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = m := by rw [hm]; push_cast; ring

  set E := (D : ℝ) * S.card - L - δ * m with hE
  have hEe : E ≤ e := by
    have : δ * (D * S.card) ≤ δ * m := mul_le_mul_of_nonneg_left hSm hδ.le
    rw [hE]; nlinarith
  set k := ⌈E / D⌉₊ with hk
  have hkS : k ≤ S.card := by
    rw [hk, Nat.ceil_le, div_le_iff₀ (by positivity)]
    have : 0 ≤ δ * m := by positivity
    rw [hE]; nlinarith
  obtain ⟨K, hKS, hKcard⟩ := Finset.exists_subset_card_eq hkS
  have hDk1 : E ≤ D * k := by
    have := Nat.le_ceil (E / D)
    rw [← hk, div_le_iff₀ (by positivity)] at this
    linarith
  have hDk2 : (D : ℝ) * k ≤ e + D := by
    by_cases hE0 : E ≤ 0
    · have : k = 0 := by rw [hk]; exact Nat.ceil_eq_zero.mpr (div_nonpos_of_nonpos_of_nonneg hE0
        (by positivity))
      rw [this]; push_cast; linarith
    · have h1 := Nat.ceil_lt_add_one (div_nonneg (le_of_not_ge hE0) (by positivity : (0 : ℝ) ≤ D))
      rw [← hk] at h1
      have h2 : (D : ℝ) * k < E + D := by
        have := mul_lt_mul_of_pos_left h1 (by positivity : (0 : ℝ) < D)
        rw [mul_add, mul_div_cancel₀ _ (by positivity), mul_one] at this
        exact this
      linarith
  have hKδ : K.Nonempty → δ < 1 := by
    intro hK
    have hk1 : 1 ≤ k := by rw [← hKcard]; exact hK.card_pos
    have hE0 : 0 < E := by
      by_contra h
      push Not at h
      have : k = 0 := by rw [hk]; exact Nat.ceil_eq_zero.mpr (div_nonpos_of_nonpos_of_nonneg h
        (by positivity))
      omega
    by_contra h
    push Not at h
    have : δ * m ≥ m := le_mul_of_one_le_left hm0 h
    rw [hE] at hE0
    linarith

  obtain ⟨A', hA'A, hA'ne, hA'R⟩ := lemma_3_7 hc.unit_A hc.ne_A hc.regular_A K
  obtain ⟨B', hB'B, hB'ne, hB'R⟩ := lemma_3_7 hc.unit_B hc.ne_B hc.regular_B K
  have hA' : InUnit m A' := fun x hx => hc.unit_A x (hA'A hx)
  have hB' : InUnit m B' := fun x hx => hc.unit_B x (hB'B hx)
  have hKr : (Finset.range ℓ).filter (· ∈ K) = K := by
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hKS.trans hSsub)]
  have hcollapse : ∀ (C C' : Finset ℤ) (Rc : ℕ → ℕ), InUnit m C → C.Nonempty →
      IsUniform D ℓ C Rc → InUnit m C' → C'.Nonempty →
      IsUniform D ℓ C' (fun s => if s ∈ K then 1 else Rc s) →
      (C.card : ℝ) ≤ C'.card * (2 : ℝ) ^ ((D : ℝ) * k) := by
    intro C C' Rc hC hCne hCR hC' hC'ne hC'R
    have h1 := prod_eq_prod_ite_mul ℓ K Rc
    rw [← hCR.card_eq hC hCne, ← hC'R.card_eq hC' hC'ne, hKr] at h1
    have h2 := prod_le_pow_card_real (T := K) (f := Rc) (a := (2 : ℝ) ^ (D : ℝ)) fun s hs => by
      rw [Real.rpow_natCast]
      have := (hCR.le_two_pow hCne) s (Finset.mem_range.mp (hSsub (hKS hs)))
      exact_mod_cast this
    rw [two_rpow_pow, hKcard] at h2
    rw [h1, Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
  have hAA' := hcollapse A A' R' hc.unit_A hc.ne_A hc.regular_A hA' hA'ne hA'R
  have hBB' := hcollapse B B' R'' hc.unit_B hc.ne_B hc.regular_B hB' hB'ne hB'R
  have hA'0 : (0 : ℝ) < A'.card := by exact_mod_cast hA'ne.card_pos
  have hB'0 : (0 : ℝ) < B'.card := by exact_mod_cast hB'ne.card_pos
  obtain ⟨X1, X2, X3⟩ := vi_constants hq.le hq'0 hδ hδ₁0 hm0 hδ₁δ hm1' hm2' hm3' hDk2

  have hlqA' : (2 : ℝ) ^ (-(q * δ * m)) * P ≤ ∑ x ∈ A', μ x ^ q := by
    have h1 := sum_rpow_ge_of_flat (A := A') (μ' := μ) (by linarith : (0 : ℝ) ≤ q) hc.pos_A
      hc.flat_A fun x hx => ⟨x, hA'A hx, rfl⟩
    have h2 := flat_restrict_bound hA'0 h1 hc.lq_A hAA'
      (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (hμ.nonneg x) q)
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hP0.le) h2
    exact Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
  have hmassB' : (2 : ℝ) ^ (-(1 + δ₁ * m + D * k)) ≤ ∑ y ∈ B', ν y := by
    have h1 := sum_rpow_ge_of_flat (A := B') (μ' := ν) (by norm_num : (0 : ℝ) ≤ 1) hc.pos_B
      hc.flat_B fun x hx => ⟨x, hB'B hx, rfl⟩
    simp only [Real.rpow_one] at h1
    have h2 := flat_restrict_bound (P := 1) hB'0 h1 (by rw [mul_one]; exact hc.mass_B) hBB'
      (Finset.sum_nonneg fun x _ => hν.nonneg x)
    rwa [mul_one] at h2

  set R'₂ : ℕ → ℕ := fun s => if s ∈ K then 1 else R' s with hR'₂
  set R''₂ : ℕ → ℕ := fun s => if s ∈ K then 1 else R'' s with hR''₂
  set S₂ := fullScales δ ℓ D R'₂ with hS₂
  have hS₂sub : S₂ ⊆ S \ K := by
    intro s hs
    obtain ⟨hsl, hs2⟩ := Finset.mem_filter.mp hs
    have hsK : s ∉ K := by
      intro hsK
      have hδ1 := hKδ ⟨s, hsK⟩
      have h1 : (1 : ℝ) < (2 : ℝ) ^ ((1 - δ) * D) :=
        Real.one_lt_rpow one_lt_two (mul_pos (by linarith) (by positivity))
      have h2 : ((R'₂ s : ℕ) : ℝ) = 1 := by rw [hR'₂]; simp [hsK]
      rw [h2] at hs2
      linarith
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hsl, ?_⟩, hsK⟩
    have h2 : R'₂ s = R' s := by rw [hR'₂]; simp [hsK]
    rw [← h2]; exact hs2
  have hS₂card : (S₂.card : ℝ) + k ≤ S.card := by
    have h1 := Finset.card_le_card hS₂sub
    have h2 := Finset.card_sdiff_add_card_eq_card hKS
    rw [hKcard] at h2
    have : S₂.card + k ≤ S.card := by omega
    exact_mod_cast this

  have hright : (D : ℝ) * S₂.card ≤ L + δ * m := by
    have : (D : ℝ) * (S₂.card + k) ≤ D * S.card := mul_le_mul_of_nonneg_left hS₂card
      (by positivity)
    rw [hE] at hDk1
    nlinarith
  have hN'' : Real.logb 2 B'.card ≤ D * S₂.card := by
    set N := (Finset.range ℓ).filter (fun s => R''₂ s ≠ 1) with hN
    have hNS : N ⊆ S₂ := by
      intro s hs
      obtain ⟨hsl, hs1⟩ := Finset.mem_filter.mp hs
      have hsK : s ∉ K := fun hsK => hs1 (by rw [hR''₂]; simp [hsK])
      have h1 : R''₂ s = R'' s := by rw [hR''₂]; simp [hsK]
      have h2 : R'₂ s = R' s := by rw [hR'₂]; simp [hsK]
      rcases hc.dichotomy s (Finset.mem_range.mp hsl) with h | h
      · exact absurd (h1.trans h) hs1
      · refine Finset.mem_filter.mpr ⟨hsl, ?_⟩
        rw [h2]
        exact le_trans (Real.rpow_le_rpow_of_exponent_le one_le_two
          (mul_le_mul_of_nonneg_right (by linarith) (by positivity))) h
    have hcard : B'.card = ∏ s ∈ N, R''₂ s := by
      rw [hB'R.card_eq hB' hB'ne, hN, Finset.prod_filter_ne_one]
    have h1 := prod_le_pow_card_real (T := N) (f := R''₂) (a := (2 : ℝ) ^ (D : ℝ)) fun s hs => by
      rw [Real.rpow_natCast]
      have := (hB'R.le_two_pow hB'ne) s (Finset.mem_range.mp (Finset.mem_filter.mp hs).1)
      exact_mod_cast this
    rw [two_rpow_pow, ← hcard] at h1
    have h2 := Real.logb_le_logb_of_le one_lt_two hB'0 h1
    rw [Real.logb_rpow two_pos (by norm_num)] at h2
    have h3 : (N.card : ℝ) ≤ S₂.card := by exact_mod_cast Finset.card_le_card hNS
    have h4 : (D : ℝ) * N.card ≤ D * S₂.card := mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  have hleft : Real.logb 2 (discLq m q ν ^ (-(1 / (q - 1)))) - δ * m ≤ D * S₂.card := by
    have hPν : 0 < discLq m q ν := discLq_pos hν q
    have hsub : ∑ y ∈ B', ν y ^ q ≤ discLq m q ν :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => Finset.mem_Ico.mpr (hB' x hx))
        (fun x _ _ => Real.rpow_nonneg (hν.nonneg x) q)
    have hS0 : 0 < ∑ y ∈ B', ν y := Finset.sum_pos (fun y hy => hc.pos_B y (hB'B hy)) hB'ne
    have h1 := logb_lq_ge_of_flat (by linarith : (0 : ℝ) ≤ q) hB'ne
      (fun y hy => hc.pos_B y (hB'B hy)) (fun x hx y hy => hc.flat_B x (hB'B hx) y (hB'B hy))
    have h2 : Real.logb 2 (∑ y ∈ B', ν y ^ q) ≤ Real.logb 2 (discLq m q ν) :=
      Real.logb_le_logb_of_le one_lt_two (Finset.sum_pos (fun y hy =>
        Real.rpow_pos_of_pos (hc.pos_B y (hB'B hy)) q) hB'ne) hsub
    have h3 : -(1 + δ₁ * m + D * k) ≤ Real.logb 2 (∑ y ∈ B', ν y) := by
      have := Real.logb_le_logb_of_le one_lt_two (by positivity) hmassB'
      rwa [Real.logb_rpow two_pos (by norm_num)] at this
    rw [Real.logb_rpow_eq_mul_logb_of_pos hPν]
    have e1 : -(1 / (q - 1)) * Real.logb 2 (discLq m q ν) ≤
        Real.logb 2 B'.card - q' * (Real.logb 2 (∑ y ∈ B', ν y) - 1) := by
      have h4 : (q - 1) * (-(1 / (q - 1)) * Real.logb 2 (discLq m q ν)) ≤
          (q - 1) * (Real.logb 2 B'.card - q' * (Real.logb 2 (∑ y ∈ B', ν y) - 1)) := by
        have e2 : (q - 1) * (-(1 / (q - 1)) * Real.logb 2 (discLq m q ν)) =
            -Real.logb 2 (discLq m q ν) := by field_simp
        have e3 : (q - 1) * (Real.logb 2 B'.card - q' * (Real.logb 2 (∑ y ∈ B', ν y) - 1)) =
            (q - 1) * Real.logb 2 B'.card - q * (Real.logb 2 (∑ y ∈ B', ν y) - 1) := by
          rw [hq']; field_simp
        rw [e2, e3]
        linarith
      exact le_of_mul_le_mul_left h4 hq1
    have e4 : q' * (Real.logb 2 (∑ y ∈ B', ν y) - 1) ≥ -(q' * (1 + (1 + δ₁ * m + D * k))) := by
      nlinarith
    linarith
  refine ⟨A', B', R'₂, R''₂, ?_⟩
  exact {
    pos_A := fun x hx => hc.pos_A x (hA'A hx)
    pos_B := fun y hy => hc.pos_B y (hB'B hy)
    lq_A := lq_root (by linarith) hP0.le hlqA'
    flat_A := fun x hx y hy => hc.flat_A x (hA'A hx) y (hA'A hy)
    regular_A := hA'R
    middle_A := fun x hx s hs => hc.middle_A x (hA'A hx) s hs
    mass_B := le_trans (Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)) hmassB'
    flat_B := fun x hx y hy => hc.flat_B x (hB'B hx) y (hB'B hy)
    regular_B := hB'R
    middle_B := fun y hy s hs => hc.middle_B y (hB'B hy) s hs
    dichotomy := fun s hs => by
      by_cases hsK : s ∈ K
      · left; simp [hR''₂, hsK]
      · rcases hc.dichotomy s hs with h | h
        · left; simp [hR''₂, hsK, h]
        · right
          have h2 : R'₂ s = R' s := by rw [hR'₂]; simp [hsK]
          rw [h2]
          exact le_trans (Real.rpow_le_rpow_of_exponent_le one_le_two
            (mul_le_mul_of_nonneg_right (by linarith) (by positivity))) h
    count_le := hleft
    le_count := hright }

set_option maxHeartbeats 4000000 in

theorem core_of_theorem31Weak_theorem32 (h31 : Bourgain.Theorem31Weak) (h32 : Theorem32) {q δ₁ : ℝ}
    (hq : 1 < q) (hδ₁ : 0 < δ₁) (hδ₁1 : δ₁ ≤ 1) (D₀ : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ D : ℕ, D₀ ≤ D ∧ 1 ≤ D ∧ ∀ᶠ ℓ : ℕ in atTop, ∀ μ ν : ℤ → ℝ,
      IsDyadicMeasure (ℓ * D) μ → IsDyadicMeasure (ℓ * D) ν →
      (2 : ℝ) ^ (-(ε * (ℓ * D : ℕ))) * discLq (ℓ * D) q μ ^ (1 / q) ≤
        discLq (ℓ * D) q (circConv (ℓ * D) μ ν) ^ (1 / q) →
      ∃ a b : ℤ, ∃ A B : Finset ℤ, ∃ R' R'' : ℕ → ℕ,
        CoreConclusion q δ₁ ℓ D (circTranslate (ℓ * D) a μ) (circTranslate (ℓ * D) b ν)
          A B R' R'' := by
  classical
  set c : ℝ := δ₁ ^ 2 / 64 with hc
  have hc0 : 0 < c := by positivity
  have hcδ : c ≤ δ₁ / 64 := by
    have : δ₁ ^ 2 ≤ δ₁ := by nlinarith
    rw [hc]; linarith
  have hc1 : c ≤ 1 := by linarith

  obtain ⟨D, hcor, h6D, hDc, hD2, hD₀D⟩ := ((corollary_3_10 h31 hc0 hc1).and
    ((eventually_linear_le_two_rpow 6 hc0).and
    ((tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (1 / c))).and
    ((eventually_ge_atTop 2).and (eventually_ge_atTop D₀))))).exists
  obtain ⟨σ, hσ, hcor⟩ := hcor
  have hD1 : 1 ≤ D := by omega
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD1
  have hcD : 1 ≤ c * D := by rw [div_le_iff₀ hc0] at hDc; linarith
  set κ : ℝ := min (σ / 2) c with hκ
  have hκ0 : 0 < κ := lt_min (by positivity) hc0
  have hκc : κ ≤ c := min_le_right _ _
  have hκT : 2 * κ ≤ σ := by
    have : κ ≤ σ / 2 := min_le_left _ _
    linarith
  obtain ⟨τ, hτ, h32'⟩ := h32 κ hκ0
  set Q := max q (q / (q - 1)) with hQ
  have hQ1 : 1 < Q := lt_of_lt_of_le hq (le_max_left _ _)
  set ε : ℝ := min (τ / (2 * Q)) (c / 4) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hεc : ε ≤ c / 4 := min_le_right _ _
  have hετ : Q * (2 * ε) ≤ τ := by
    have : ε ≤ τ / (2 * Q) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  refine ⟨ε, hε0, D, hD₀D, hD1, ?_⟩
  have hT := tendsto_mul_right_atTop hD1
  filter_upwards [hcor, hT.eventually h32', hT.eventually (lemma_3_3 hε0 hq),
    hT.eventually (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (1 / κ)))]
    with ℓ hcorℓ h32ℓ h33ℓ hκℓ
  intro μ ν hμ hν hconv
  set m := ℓ * D with hm
  have hmR : (m : ℝ) = ℓ * D := by rw [hm]; push_cast; ring
  have hmκ : 1 ≤ κ * m := by rw [div_le_iff₀ hκ0] at hκℓ; linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmc : 1 ≤ c * m := le_trans hmκ (by gcongr)
  have hℓc : (ℓ : ℝ) ≤ c * m := by
    rw [hmR]
    have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
    nlinarith
  have h6ℓ : ((6 * (D + 1) : ℕ) : ℝ) ^ ℓ ≤ (2 : ℝ) ^ (c * m) := by
    calc ((6 * (D + 1) : ℕ) : ℝ) ^ ℓ ≤ ((2 : ℝ) ^ (c * D)) ^ ℓ := by
          gcongr; push_cast; linarith
      _ = (2 : ℝ) ^ (c * m) := by
          rw [← Real.rpow_mul_natCast (by norm_num), hmR]; ring_nf

  obtain ⟨A₁, B₁, hA₁, hB₁, hA₁ne, hB₁ne, hA₁pos, hB₁pos, hA₁flat, hB₁flat, hconv1, hA₁q,
    hB₁mass⟩ := h33ℓ μ ν hμ hν hconv

  have hE := lemma_3_4 (κ := 2 * ε) hq (by positivity) hA₁ hB₁ hconv1
  set Ab := A₁.image (Int.cast : ℤ → ZMod (2 ^ m)) with hAb
  set Bb := B₁.image (Int.cast : ℤ → ZMod (2 ^ m)) with hBb
  have hAbc : Ab.card = A₁.card := card_image_cast hA₁
  have hBbc : Bb.card = B₁.card := card_image_cast hB₁
  have hE' : (2 : ℝ) ^ (-(τ * m)) * Ab.card * (Bb.card : ℝ) ^ 2 ≤ Finset.addEnergy Ab Bb := by
    refine le_trans ?_ hE
    rw [hAbc, hBbc]
    gcongr
    exact one_le_two
  obtain ⟨H, X, hHH, hA₁XH, hXH, hB₁H⟩ := h32ℓ Ab Bb hE'
  rw [hAbc] at hA₁XH hXH
  rw [hBbc] at hB₁H

  set Ht := lift H with hHtdef
  have hHt : InUnit m Ht := inUnit_lift H
  have hHtcard : Ht.card = H.card := card_lift H
  have hHtimg : Ht.image (Int.cast : ℤ → ZMod (2 ^ m)) = H := image_cast_lift H
  have hB₁card : (0 : ℝ) < B₁.card := by exact_mod_cast hB₁ne.card_pos
  have hA₁card : (0 : ℝ) < A₁.card := by exact_mod_cast hA₁ne.card_pos
  have hHne : H.Nonempty := by
    have h1 : (0 : ℝ) < (Bb ∩ H).card := lt_of_lt_of_le (by positivity) hB₁H
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (by exact_mod_cast h1)
    exact ⟨w, (Finset.mem_inter.mp hw).2⟩
  have hHtne : Ht.Nonempty := by
    rw [← Finset.card_pos, hHtcard]; exact hHne.card_pos
  have hHtdbl : ((Ht + Ht).card : ℝ) ≤ (2 : ℝ) ^ (σ * m) * Ht.card := by
    have h1 : (Ht + Ht).card ≤ 2 * (H + H).card := by
      have := card_add_le_two_mul hHt hHt; rwa [hHtimg] at this
    calc ((Ht + Ht).card : ℝ) ≤ 2 * (H + H).card := by exact_mod_cast h1
      _ ≤ 2 * ((2 : ℝ) ^ (κ * m) * H.card) := by gcongr
      _ = (2 : ℝ) ^ (1 + κ * m) * Ht.card := by
          rw [Real.rpow_add two_pos, Real.rpow_one, hHtcard]; ring
      _ ≤ (2 : ℝ) ^ (σ * m) * Ht.card := by
          gcongr
          · exact one_le_two
          · have := mul_le_mul_of_nonneg_right hκT hm0
            linarith
  obtain ⟨H', hH'Ht, hH'ne, R, hH'R, hRdich, hH'card⟩ := hcorℓ Ht hHt hHtne hHtdbl
  have hH' : InUnit m H' := fun x hx => hHt x (hH'Ht hx)
  have hH'H : ∀ h ∈ H', (h : ZMod (2 ^ m)) ∈ H := fun h hh => by
    rw [← hHtimg]; exact Finset.mem_image_of_mem _ (hH'Ht hh)

  set A₁' := A₁.filter (fun x : ℤ => (x : ZMod (2 ^ m)) ∈ X + H) with hA₁'def
  have hA₁'card : A₁'.card = (Ab ∩ (X + H)).card := card_filter_cast hA₁ _
  obtain ⟨a, A₂, hA₂A₁', hA₂card, hA₂mid⟩ := lemma_3_8 hD2 ℓ A₁'
  have hA₂ : InUnit m A₂ := fun x hx => hA₁ x (Finset.mem_filter.mp (hA₂A₁' hx)).1
  set A₃ := A₂.image (fun y => (y + a) % 2 ^ m) with hA₃def
  have hA₃ : InUnit m A₃ := inUnit_image_translate m a A₂
  have hA₃card : A₃.card = A₂.card := card_image_translate hA₂ a
  obtain ⟨A, hAA₃, R', hAR', hAcard⟩ := lemma_3_6 D ℓ hA₃
  have hA : InUnit m A := fun x hx => hA₃ x (hAA₃ hx)
  have hA₁'pos : (0 : ℝ) < A₁'.card := by
    rw [hA₁'card]; exact lt_of_lt_of_le (by positivity) hA₁XH
  have hAne : A.Nonempty := by
    rw [← Finset.card_pos]
    have h1 : 0 < A₁'.card := by exact_mod_cast hA₁'pos
    have h2 : 0 < A₂.card := Nat.pos_of_mul_pos_left (lt_of_lt_of_le h1 hA₂card)
    have h3 : 0 < A₃.card := by omega
    exact Nat.pos_of_mul_pos_left (lt_of_lt_of_le h3 hAcard)

  set B₁' := B₁.filter (fun y : ℤ => (y : ZMod (2 ^ m)) ∈ H) with hB₁'def
  have hB₁'card : B₁'.card = (Bb ∩ H).card := card_filter_cast hB₁ _
  obtain ⟨b, B₂', hB₂'B₁', hB₂'card, hB₂'mid⟩ := lemma_3_8 hD2 ℓ B₁'
  have hB₂' : InUnit m B₂' := fun x hx => hB₁ x (Finset.mem_filter.mp (hB₂'B₁' hx)).1
  set B₃ := B₂'.image (fun y => (y + b) % 2 ^ m) with hB₃def
  have hB₃ : InUnit m B₃ := inUnit_image_translate m b B₂'
  have hB₃card : B₃.card = B₂'.card := card_image_translate hB₂' b
  obtain ⟨B₂, hB₂B₃, Rt, hB₂R, hB₂card⟩ := lemma_3_6 D ℓ hB₃
  have hB₂ : InUnit m B₂ := fun x hx => hB₃ x (hB₂B₃ hx)
  have hB₁'pos : (0 : ℝ) < B₁'.card := by
    rw [hB₁'card]; exact lt_of_lt_of_le (by positivity) hB₁H
  have hB₂ne : B₂.Nonempty := by
    rw [← Finset.card_pos]
    have h1 : 0 < B₁'.card := by exact_mod_cast hB₁'pos
    have h2 : 0 < B₂'.card := Nat.pos_of_mul_pos_left (lt_of_lt_of_le h1 hB₂'card)
    have h3 : 0 < B₃.card := by omega
    exact Nat.pos_of_mul_pos_left (lt_of_lt_of_le h3 hB₂card)

  have hAH'sub : A.image (Int.cast : ℤ → ZMod (2 ^ m)) + H'.image Int.cast ⊆
      (X + (H + H)).image (· + (a : ZMod (2 ^ m))) := by
    intro z hz
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hAA₃ hx)
    obtain ⟨ξ, hξ, η₁, hη₁, hξη⟩ := Finset.mem_add.mp (Finset.mem_filter.mp (hA₂A₁' hy)).2
    refine Finset.mem_image.mpr ⟨ξ + (η₁ + h), Finset.add_mem_add hξ
      (Finset.add_mem_add hη₁ (hH'H h hh)), ?_⟩
    rw [cast_translate, ← hξη]; ring
  have hAH' : (A + H').card ≤ 2 * (X.card * (H + H).card) :=
    calc (A + H').card ≤ 2 * (A.image (Int.cast : ℤ → ZMod (2 ^ m)) + H'.image Int.cast).card :=
          card_add_le_two_mul hA hH'
      _ ≤ 2 * ((X + (H + H)).image (· + (a : ZMod (2 ^ m)))).card :=
          Nat.mul_le_mul_left 2 (Finset.card_le_card hAH'sub)
      _ ≤ 2 * (X + (H + H)).card := Nat.mul_le_mul_left 2 Finset.card_image_le
      _ ≤ 2 * (X.card * (H + H).card) := Nat.mul_le_mul_left 2 Finset.card_add_le

  have hBH'sub : B₂.image (Int.cast : ℤ → ZMod (2 ^ m)) + H'.image Int.cast ⊆
      (H + H).image (· + (b : ZMod (2 ^ m))) := by
    intro z hz
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hB₂B₃ hx)
    refine Finset.mem_image.mpr ⟨(y : ZMod (2 ^ m)) + h, Finset.add_mem_add
      (Finset.mem_filter.mp (hB₂'B₁' hy)).2 (hH'H h hh), ?_⟩
    rw [cast_translate]; ring
  have hBH' : (B₂ + H').card ≤ 2 * (H + H).card :=
    calc (B₂ + H').card ≤ 2 * (B₂.image (Int.cast : ℤ → ZMod (2 ^ m)) + H'.image Int.cast).card :=
          card_add_le_two_mul hB₂ hH'
      _ ≤ 2 * ((H + H).image (· + (b : ZMod (2 ^ m)))).card :=
          Nat.mul_le_mul_left 2 (Finset.card_le_card hBH'sub)
      _ ≤ 2 * (H + H).card := Nat.mul_le_mul_left 2 Finset.card_image_le

  have h39A := lemma_3_9 hA hH' hAne hH'R hAR'
  have h39B := lemma_3_9 hB₂ hH' hB₂ne hH'R hB₂R
  set S₀ := (Finset.range ℓ).filter (fun s => R s = 1) with hS₀
  set S₁ := (Finset.range ℓ).filter (fun s => ¬ R s = 1) with hS₁
  have hAprod : A.card = (∏ s ∈ S₀, R' s) * ∏ s ∈ S₁, R' s := by
    rw [hAR'.card_eq hA hAne, Finset.prod_filter_mul_prod_filter_not]
  have hH'prod : H'.card = ∏ s ∈ S₁, R s := by
    rw [hH'R.card_eq hH' hH'ne, ← Finset.prod_filter_mul_prod_filter_not (Finset.range ℓ)
      (fun s => R s = 1), Finset.prod_eq_one (fun s hs => (Finset.mem_filter.mp hs).2), one_mul]
  have hR'1 := hAR'.one_le hAne
  have hR'2 := hAR'.le_two_pow hAne
  have hRt1 := hB₂R.one_le hB₂ne
  have hRt2 := hB₂R.le_two_pow hB₂ne
  have hPA0 : (0 : ℝ) < ((∏ s ∈ S₀, R' s : ℕ) : ℝ) := by
    have : 0 < ∏ s ∈ S₀, R' s := Finset.prod_pos fun s hs =>
      hR'1 s (Finset.mem_range.mp (Finset.mem_filter.mp hs).1)
    exact_mod_cast this

  have hXH' : (X.card : ℝ) * H.card ≤ (2 : ℝ) ^ (κ * m) * A₁.card := by
    have h1 : (2 : ℝ) ^ (2 * κ * m) * ((2 : ℝ) ^ (-(2 * κ * m)) * X.card * H.card) ≤
        (2 : ℝ) ^ (2 * κ * m) * ((2 : ℝ) ^ (-(κ * m)) * A₁.card) := by gcongr
    rw [← mul_assoc, ← mul_assoc, ← Real.rpow_add two_pos, ← mul_assoc,
      ← Real.rpow_add two_pos] at h1
    rw [show 2 * κ * m + -(2 * κ * m) = 0 by ring, show 2 * κ * m + -(κ * m) = κ * m by ring,
      Real.rpow_zero, one_mul] at h1
    exact h1
  have hA₁A₁' : (A₁.card : ℝ) ≤ (2 : ℝ) ^ (κ * m) * A₁'.card := by
    have h1 : (2 : ℝ) ^ (κ * m) * ((2 : ℝ) ^ (-(κ * m)) * A₁.card) ≤
        (2 : ℝ) ^ (κ * m) * A₁'.card := by rw [hA₁'card]; gcongr
    rwa [← mul_assoc, ← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero, one_mul] at h1
  have hA₁'A : (A₁'.card : ℝ) ≤ (2 : ℝ) ^ (c * m) * A.card := by
    have h1 : A₁'.card ≤ (6 * (D + 1)) ^ ℓ * A.card := by
      calc A₁'.card ≤ 3 ^ ℓ * A₂.card := hA₂card
        _ = 3 ^ ℓ * A₃.card := by rw [hA₃card]
        _ ≤ 3 ^ ℓ * ((2 * (D + 1)) ^ ℓ * A.card) := Nat.mul_le_mul_left _ hAcard
        _ = (6 * (D + 1)) ^ ℓ * A.card := by rw [← mul_assoc, ← mul_pow]; ring_nf
    calc (A₁'.card : ℝ) ≤ ((6 * (D + 1) : ℕ) : ℝ) ^ ℓ * A.card := by exact_mod_cast h1
      _ ≤ (2 : ℝ) ^ (c * m) * A.card := by gcongr
  have hB₁B₁' : (B₁.card : ℝ) ≤ (2 : ℝ) ^ (κ * m) * B₁'.card := by
    have h1 : (2 : ℝ) ^ (κ * m) * ((2 : ℝ) ^ (-(κ * m)) * B₁.card) ≤
        (2 : ℝ) ^ (κ * m) * B₁'.card := by rw [hB₁'card]; gcongr
    rwa [← mul_assoc, ← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero, one_mul] at h1
  have hB₁'B₂ : (B₁'.card : ℝ) ≤ (2 : ℝ) ^ (c * m) * B₂.card := by
    have h1 : B₁'.card ≤ (6 * (D + 1)) ^ ℓ * B₂.card := by
      calc B₁'.card ≤ 3 ^ ℓ * B₂'.card := hB₂'card
        _ = 3 ^ ℓ * B₃.card := by rw [hB₃card]
        _ ≤ 3 ^ ℓ * ((2 * (D + 1)) ^ ℓ * B₂.card) := Nat.mul_le_mul_left _ hB₂card
        _ = (6 * (D + 1)) ^ ℓ * B₂.card := by rw [← mul_assoc, ← mul_pow]; ring_nf
    calc (B₁'.card : ℝ) ≤ ((6 * (D + 1) : ℕ) : ℝ) ^ ℓ * B₂.card := by exact_mod_cast h1
      _ ≤ (2 : ℝ) ^ (c * m) * B₂.card := by gcongr
  have hHH' : (H.card : ℝ) ≤ (2 : ℝ) ^ (c * m) * H'.card := by
    have h1 : (2 : ℝ) ^ (c * m) * ((2 : ℝ) ^ (-(c * m)) * Ht.card) ≤
        (2 : ℝ) ^ (c * m) * H'.card := by gcongr
    rwa [← mul_assoc, ← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero, one_mul,
      hHtcard] at h1
  have hHH2 : ((H + H).card : ℝ) ≤ (2 : ℝ) ^ (κ * m) * H.card := hHH

  set S := S₁.filter (fun s => (2 : ℝ) ^ ((1 - δ₁) * D) ≤ R' s) with hSdef
  set S' := S₁.filter (fun s => ¬ (2 : ℝ) ^ ((1 - δ₁) * D) ≤ R' s) with hS'def
  have hS₁card : S.card + S'.card = S₁.card := Finset.card_filter_add_card_filter_not _
  have hS₁ℓ : S₁.card ≤ ℓ := by
    calc S₁.card ≤ (Finset.range ℓ).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = ℓ := Finset.card_range ℓ
  set X0 : ℝ := ℓ + 1 + 3 * (κ * m) + c * m with hX0
  have hX0e : (2 : ℝ) ^ X0 = 2 ^ ℓ * 2 * (2 : ℝ) ^ (κ * m) * (2 : ℝ) ^ (κ * m) *
      (2 : ℝ) ^ (κ * m) * (2 : ℝ) ^ (c * m) := by
    rw [hX0, show (ℓ : ℝ) + 1 + 3 * (κ * m) + c * m =
      ℓ + 1 + κ * m + κ * m + κ * m + c * m by ring]
    simp only [Real.rpow_add two_pos, Real.rpow_one, Real.rpow_natCast]
  have hAprodR : (A.card : ℝ) = (∏ s ∈ S₀, (R' s : ℝ)) * ∏ s ∈ S₁, (R' s : ℝ) := by
    rw [hAprod]; push_cast; ring
  have hPA0' : (0 : ℝ) < ∏ s ∈ S₀, (R' s : ℝ) := by rw [← Nat.cast_prod]; exact hPA0
  have hH'PA1 : (H'.card : ℝ) ≤ (2 : ℝ) ^ X0 * ∏ s ∈ S₁, (R' s : ℝ) := by
    have h1 : ((H'.card * ∏ s ∈ S₀, R' s : ℕ) : ℝ) ≤ ((2 ^ ℓ * (A + H').card : ℕ) : ℝ) := by
      exact_mod_cast h39A
    have h2 : ((A + H').card : ℝ) ≤ 2 * (X.card * (H + H).card) := by exact_mod_cast hAH'
    push_cast at h1
    have key : (H'.card : ℝ) * ∏ s ∈ S₀, (R' s : ℝ) ≤
        ((2 : ℝ) ^ X0 * ∏ s ∈ S₁, (R' s : ℝ)) * ∏ s ∈ S₀, (R' s : ℝ) := by
      calc (H'.card : ℝ) * ∏ s ∈ S₀, (R' s : ℝ) ≤ 2 ^ ℓ * (A + H').card := h1
        _ ≤ 2 ^ ℓ * (2 * (X.card * ((2 : ℝ) ^ (κ * m) * H.card))) := by
            gcongr; exact le_trans h2 (by gcongr)
        _ = 2 ^ ℓ * 2 * (2 : ℝ) ^ (κ * m) * (X.card * H.card) := by ring
        _ ≤ 2 ^ ℓ * 2 * (2 : ℝ) ^ (κ * m) * ((2 : ℝ) ^ (κ * m) * A₁.card) := by gcongr
        _ ≤ 2 ^ ℓ * 2 * (2 : ℝ) ^ (κ * m) * ((2 : ℝ) ^ (κ * m) *
              ((2 : ℝ) ^ (κ * m) * A₁'.card)) := by gcongr
        _ ≤ 2 ^ ℓ * 2 * (2 : ℝ) ^ (κ * m) * ((2 : ℝ) ^ (κ * m) *
              ((2 : ℝ) ^ (κ * m) * ((2 : ℝ) ^ (c * m) * A.card))) := by gcongr
        _ = (2 : ℝ) ^ X0 * A.card := by rw [hX0e]; ring
        _ = ((2 : ℝ) ^ X0 * ∏ s ∈ S₁, (R' s : ℝ)) * ∏ s ∈ S₀, (R' s : ℝ) := by
            rw [hAprodR]; ring
    exact le_of_mul_le_mul_right key hPA0'
  have hH'low : ((2 : ℝ) ^ ((1 - c) * D)) ^ S₁.card ≤ (H'.card : ℝ) := by
    rw [hH'prod]
    refine pow_card_le_prod_real (by positivity) fun s hs => ?_
    obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp hs
    exact (hRdich s (Finset.mem_range.mp hs1)).resolve_left hs2
  have hPA1up : ∏ s ∈ S₁, (R' s : ℝ) ≤
      ((2 : ℝ) ^ (D : ℝ)) ^ S.card * ((2 : ℝ) ^ ((1 - δ₁) * D)) ^ S'.card := by
    rw [← Finset.prod_filter_mul_prod_filter_not S₁
      (fun s => (2 : ℝ) ^ ((1 - δ₁) * D) ≤ R' s)]
    have e1 := prod_le_pow_card_real (T := S) (f := R') (a := (2 : ℝ) ^ (D : ℝ)) fun s hs => by
      rw [Real.rpow_natCast]
      exact_mod_cast hR'2 s (Finset.mem_range.mp (Finset.mem_filter.mp
        (Finset.mem_filter.mp hs).1).1)
    have e2 := prod_le_pow_card_real (T := S') (f := R') (a := (2 : ℝ) ^ ((1 - δ₁) * D))
      fun s hs => (not_le.mp (Finset.mem_filter.mp hs).2).le
    rw [Nat.cast_prod] at e1 e2
    exact mul_le_mul e1 e2 (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _) (by positivity)
  have hSc : (S₁.card : ℝ) = S.card + S'.card := by exact_mod_cast hS₁card.symm
  have hexp : (1 - c) * D * (S.card + S'.card) ≤
      X0 + (D * S.card + (1 - δ₁) * D * S'.card) := by
    have h := le_trans hH'low (le_trans hH'PA1 (mul_le_mul_of_nonneg_left hPA1up
      (by positivity)))
    rw [two_rpow_pow, two_rpow_pow, two_rpow_pow, ← Real.rpow_add two_pos,
      ← Real.rpow_add two_pos, Real.rpow_le_rpow_left_iff one_lt_two, hSc] at h
    exact h
  have hSm : (D : ℝ) * S.card ≤ m := by
    have h1 : S.card ≤ ℓ := le_trans (by omega) hS₁ℓ
    have h2 : (S.card : ℝ) ≤ ℓ := by exact_mod_cast h1
    calc (D : ℝ) * S.card ≤ D * ℓ := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg D)
      _ = m := by rw [hmR]; ring
  have hX0b : X0 ≤ 6 * c * m := by
    have : κ * m ≤ c * m := mul_le_mul_of_nonneg_right hκc hm0
    rw [hX0]; linarith only [this, hℓc, hmc]
  have hS'bound : (D : ℝ) * S'.card ≤ δ₁ * m / 4 :=
    numeric_scales hδ₁ hc hδ₁1 hX0b (Nat.cast_nonneg D) (Nat.cast_nonneg _) hSm hexp

  obtain ⟨B, hBB₂, hBne, hBR⟩ := lemma_3_7 hB₂ hB₂ne hB₂R (S₀ ∪ S')
  have hB : InUnit m B := fun x hx => hB₂ x (hBB₂ hx)
  have hPB0 : ∏ s ∈ S₀, (Rt s : ℝ) ≤ (2 : ℝ) ^ ((ℓ : ℝ) + 1 + κ * m + c * m) := by
    have h1 : ((H'.card * ∏ s ∈ S₀, Rt s : ℕ) : ℝ) ≤ ((2 ^ ℓ * (B₂ + H').card : ℕ) : ℝ) := by
      exact_mod_cast h39B
    have h2 : ((B₂ + H').card : ℝ) ≤ 2 * (H + H).card := by exact_mod_cast hBH'
    push_cast at h1
    have hH'pos : (0 : ℝ) < H'.card := by exact_mod_cast hH'ne.card_pos
    have h3 : ((H + H).card : ℝ) ≤ (2 : ℝ) ^ (κ * m) * ((2 : ℝ) ^ (c * m) * H'.card) :=
      le_trans hHH2 (mul_le_mul_of_nonneg_left hHH' (by positivity))
    have h4 : ((B₂ + H').card : ℝ) ≤ 2 * ((2 : ℝ) ^ (κ * m) * ((2 : ℝ) ^ (c * m) * H'.card)) :=
      le_trans h2 (by linarith only [h3])
    have key : (∏ s ∈ S₀, (Rt s : ℝ)) * H'.card ≤
        (2 : ℝ) ^ ((ℓ : ℝ) + 1 + κ * m + c * m) * H'.card := by
      calc (∏ s ∈ S₀, (Rt s : ℝ)) * H'.card = H'.card * ∏ s ∈ S₀, (Rt s : ℝ) := by ring
        _ ≤ 2 ^ ℓ * (B₂ + H').card := h1
        _ ≤ 2 ^ ℓ * (2 * ((2 : ℝ) ^ (κ * m) * ((2 : ℝ) ^ (c * m) * H'.card))) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = (2 : ℝ) ^ ((ℓ : ℝ) + 1 + κ * m + c * m) * H'.card := by
            simp only [Real.rpow_add two_pos, Real.rpow_one, Real.rpow_natCast]; ring
    exact le_of_mul_le_mul_right key hH'pos
  have hB₂B : (B₂.card : ℝ) ≤
      (2 : ℝ) ^ ((ℓ : ℝ) + 1 + κ * m + c * m) * (2 : ℝ) ^ ((D : ℝ) * S'.card) * B.card := by
    have h1 := prod_eq_prod_ite_mul ℓ (S₀ ∪ S') Rt
    rw [← hB₂R.card_eq hB₂ hB₂ne, ← hBR.card_eq hB hBne] at h1
    have hsub : S₀ ∪ S' ⊆ Finset.range ℓ := Finset.union_subset (Finset.filter_subset _ _)
      ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
    have hK : (Finset.range ℓ).filter (· ∈ S₀ ∪ S') = S₀ ∪ S' := by
      rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub]
    have hdisj : Disjoint S₀ S' := by
      rw [Finset.disjoint_left]
      intro s hs hs'
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hs').1).2 (Finset.mem_filter.mp hs).2
    rw [hK, Finset.prod_union hdisj] at h1
    have hS'R := prod_le_pow_card_real (T := S') (f := Rt) (a := (2 : ℝ) ^ (D : ℝ))
      fun s hs => by
        rw [Real.rpow_natCast]
        exact_mod_cast hRt2 s (Finset.mem_range.mp (Finset.mem_filter.mp
          (Finset.mem_filter.mp hs).1).1)
    rw [two_rpow_pow, Nat.cast_prod] at hS'R
    have h1' : (B₂.card : ℝ) = B.card * ((∏ s ∈ S₀, (Rt s : ℝ)) * ∏ s ∈ S', (Rt s : ℝ)) := by
      rw [h1]; push_cast; ring
    rw [h1', mul_comm (D : ℝ)]
    have h5 : (∏ s ∈ S₀, (Rt s : ℝ)) * ∏ s ∈ S', (Rt s : ℝ) ≤
        (2 : ℝ) ^ ((ℓ : ℝ) + 1 + κ * m + c * m) * (2 : ℝ) ^ ((S'.card : ℝ) * D) := by
      rw [mul_comm (S'.card : ℝ)]
      exact mul_le_mul hPB0 hS'R (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)
        (by positivity)
    calc (B.card : ℝ) * ((∏ s ∈ S₀, (Rt s : ℝ)) * ∏ s ∈ S', (Rt s : ℝ))
        ≤ B.card * ((2 : ℝ) ^ ((ℓ : ℝ) + 1 + κ * m + c * m) *
          (2 : ℝ) ^ ((S'.card : ℝ) * D)) := mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg _)
      _ = _ := by ring

  have hσA : ∀ x ∈ A, ∃ y ∈ A₁, circTranslate m a μ x = μ y := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hAA₃ hx)
    exact ⟨y, (Finset.mem_filter.mp (hA₂A₁' hy)).1, circTranslate_translate a μ (hA₂ y hy)⟩
  have hσB : ∀ x ∈ B, ∃ y ∈ B₁, circTranslate m b ν x = ν y := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hB₂B₃ (hBB₂ hx))
    exact ⟨y, (Finset.mem_filter.mp (hB₂'B₁' hy)).1, circTranslate_translate b ν (hB₂' y hy)⟩
  have hAcardpos : (0 : ℝ) < A.card := by exact_mod_cast hAne.card_pos
  have hBcardpos : (0 : ℝ) < B.card := by exact_mod_cast hBne.card_pos
  have hlqA : (2 : ℝ) ^ (-(q * δ₁ * m)) * discLq m q (circTranslate m a μ) ≤
      ∑ x ∈ A, circTranslate m a μ x ^ q := by
    rw [discLq_circTranslate]
    have h1 := sum_rpow_ge_of_flat (by linarith : (0 : ℝ) ≤ q) hA₁pos hA₁flat hσA
    have h3 : (A₁.card : ℝ) ≤ (2 : ℝ) ^ (κ * m) * ((2 : ℝ) ^ (c * m) * A.card) :=
      le_trans hA₁A₁' (mul_le_mul_of_nonneg_left hA₁'A (by positivity))
    have hP : 0 ≤ discLq m q μ := (discLq_pos hμ q).le
    have hT : 0 ≤ ∑ x ∈ A, circTranslate m a μ x ^ q :=
      Finset.sum_nonneg fun x _ =>
        Real.rpow_nonneg ((isDyadicMeasure_circTranslate hμ a).nonneg x) q
    exact lq_A_numeric hq.le hcδ hεc hκc hmc hm0 hP hAcardpos h1 hA₁q h3 hT
  have hmassB : (2 : ℝ) ^ (-(δ₁ * m)) ≤ ∑ y ∈ B, circTranslate m b ν y := by
    have h1 := sum_rpow_ge_of_flat (by norm_num : (0 : ℝ) ≤ 1) hB₁pos hB₁flat hσB
    simp only [Real.rpow_one] at h1
    have h3 : (B₁.card : ℝ) ≤ (2 : ℝ) ^ (κ * m) * ((2 : ℝ) ^ (c * m) *
        ((2 : ℝ) ^ ((ℓ : ℝ) + 1 + κ * m + c * m) * (2 : ℝ) ^ ((D : ℝ) * S'.card) * B.card)) :=
      le_trans hB₁B₁' (mul_le_mul_of_nonneg_left (le_trans hB₁'B₂
        (mul_le_mul_of_nonneg_left hB₂B (by positivity))) (by positivity))
    have hT : 0 ≤ ∑ y ∈ B, circTranslate m b ν y :=
      Finset.sum_nonneg fun y _ => (isDyadicMeasure_circTranslate hν b).nonneg _
    exact mass_B_numeric hcδ hεc hκc hmc hℓc hS'bound hm0 hBcardpos h1 hB₁mass h3 hT
  refine ⟨a, b, A, B, R', fun s => if s ∈ S₀ ∪ S' then 1 else Rt s, ?_⟩
  exact {
    unit_A := hA
    unit_B := hB
    ne_A := hAne
    ne_B := hBne
    pos_A := fun x hx => by
      obtain ⟨y, hy, h⟩ := hσA x hx
      rw [h]; exact hA₁pos y hy
    pos_B := fun x hx => by
      obtain ⟨y, hy, h⟩ := hσB x hx
      rw [h]; exact hB₁pos y hy
    lq_A := hlqA
    flat_A := fun x hx y hy => by
      obtain ⟨x', hx', h1⟩ := hσA x hx
      obtain ⟨y', hy', h2⟩ := hσA y hy
      rw [h1, h2]; exact hA₁flat x' hx' y' hy'
    regular_A := hAR'
    middle_A := fun x hx s hs => by
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hAA₃ hx)
      exact hA₂mid y hy s hs
    mass_B := hmassB
    flat_B := fun x hx y hy => by
      obtain ⟨x', hx', h1⟩ := hσB x hx
      obtain ⟨y', hy', h2⟩ := hσB y hy
      rw [h1, h2]; exact hB₁flat x' hx' y' hy'
    regular_B := hBR
    middle_B := fun x hx s hs => by
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hB₂B₃ (hBB₂ hx))
      exact hB₂'mid y hy s hs
    dichotomy := fun s hs => by
      by_cases hK : s ∈ S₀ ∪ S'
      · left; exact ite_eq_of_pos hK
      · right
        have hs0 : ¬ R s = 1 := fun h => hK (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hs, h⟩))
        have hs1 : s ∈ S₁ := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hs, hs0⟩
        by_contra h
        exact hK (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs1, h⟩)) }

end Inverse

open Inverse in

theorem inverseTheorem_of_theorem31Weak_theorem32 (h31 : Bourgain.Theorem31Weak)
    (h32 : Theorem32) : InverseTheorem := by
  intro q hq δ hδ D₀ hD₀
  obtain ⟨δ₁, hδ₁, hδ₁1, hpost⟩ := inverseConclusion_of_core hq hδ
  obtain ⟨ε, hε, D, hD₀D, hD1, hcore⟩ := core_of_theorem31Weak_theorem32 h31 h32 hq hδ₁ hδ₁1 D₀
  refine ⟨ε, hε, D, hD₀D, ?_⟩
  filter_upwards [hcore, hpost D hD1] with ℓ hℓ hℓ' μ ν hμ hν hconv
  obtain ⟨a, b, A, B, R', R'', hc⟩ := hℓ μ ν hμ hν hconv
  obtain ⟨A', B', R'₂, R''₂, h⟩ := hℓ' _ _ (isDyadicMeasure_circTranslate hμ a)
    (isDyadicMeasure_circTranslate hν b) A B R' R'' hc
  exact ⟨a, b, A', B', R'₂, R''₂, h⟩

theorem inverseTheorem_of_theorem32 (h32 : Theorem32) : InverseTheorem :=
  inverseTheorem_of_theorem31Weak_theorem32 Bourgain.theorem31Weak h32

end Lq

end FractalGeometry
