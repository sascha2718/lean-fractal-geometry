import Mathlib
import FractalGeometry.Entropy.Lq.Basic

open MeasureTheory Filter Topology Set

open scoped Pointwise

namespace FractalGeometry

namespace Lq

structure IsDyadicMeasure (m : ℕ) (μ : ℤ → ℝ) : Prop where
  nonneg : ∀ k, 0 ≤ μ k
  support : ∀ k, μ k ≠ 0 → 0 ≤ k ∧ k < 2 ^ m
  sum_eq_one : ∑ k ∈ Finset.Ico (0 : ℤ) (2 ^ m), μ k = 1

noncomputable def discLq (m : ℕ) (q : ℝ) (μ : ℤ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Ico (0 : ℤ) (2 ^ m), μ k ^ q

noncomputable def circConv (m : ℕ) (μ ν : ℤ → ℝ) (k : ℤ) : ℝ :=
  if 0 ≤ k ∧ k < 2 ^ m then ∑ i ∈ Finset.Ico (0 : ℤ) (2 ^ m), μ i * ν ((k - i) % 2 ^ m) else 0

noncomputable def circTranslate (m : ℕ) (a : ℤ) (μ : ℤ → ℝ) (k : ℤ) : ℝ :=
  if 0 ≤ k ∧ k < 2 ^ m then μ ((k - a) % 2 ^ m) else 0

def branching (m n n' : ℕ) (A : Finset ℤ) (x : ℤ) : ℕ :=
  ((A.filter fun y => y / 2 ^ (m - n) = x / 2 ^ (m - n)).image fun y => y / 2 ^ (m - n')).card

def InMiddleHalf (n : ℕ) (x : ℤ) : Prop :=
  2 ^ n ≤ 4 * (x % 2 ^ n) ∧ 4 * (x % 2 ^ n) ≤ 3 * 2 ^ n

noncomputable def fullScales (δ : ℝ) (ℓ D : ℕ) (R' : ℕ → ℕ) : Finset ℕ :=
  open Classical in (Finset.range ℓ).filter fun s => (2 : ℝ) ^ ((1 - δ) * D) ≤ R' s

structure InverseConclusion (q δ : ℝ) (ℓ D : ℕ) (μ ν : ℤ → ℝ) (A B : Finset ℤ)
    (R' R'' : ℕ → ℕ) : Prop where
  pos_A : ∀ x ∈ A, 0 < μ x
  pos_B : ∀ y ∈ B, 0 < ν y

  lq_A : (2 : ℝ) ^ (-(δ * (ℓ * D : ℕ))) * discLq (ℓ * D) q μ ^ (1 / q) ≤
    (∑ x ∈ A, μ x ^ q) ^ (1 / q)

  flat_A : ∀ x ∈ A, ∀ y ∈ A, μ y ≤ 2 * μ x

  regular_A : ∀ s < ℓ, ∀ x ∈ A, branching (ℓ * D) (s * D) ((s + 1) * D) A x = R' s

  middle_A : ∀ x ∈ A, ∀ s < ℓ, InMiddleHalf (ℓ * D - s * D) x

  mass_B : (2 : ℝ) ^ (-(δ * (ℓ * D : ℕ))) ≤ ∑ y ∈ B, ν y

  flat_B : ∀ x ∈ B, ∀ y ∈ B, ν y ≤ 2 * ν x

  regular_B : ∀ s < ℓ, ∀ y ∈ B, branching (ℓ * D) (s * D) ((s + 1) * D) B y = R'' s

  middle_B : ∀ y ∈ B, ∀ s < ℓ, InMiddleHalf (ℓ * D - s * D) y

  dichotomy : ∀ s < ℓ, R'' s = 1 ∨ (2 : ℝ) ^ ((1 - δ) * D) ≤ R' s

  count_le : Real.logb 2 (discLq (ℓ * D) q ν ^ (-(1 / (q - 1)))) - δ * (ℓ * D : ℕ) ≤
    D * (fullScales δ ℓ D R').card

  le_count : (D : ℝ) * (fullScales δ ℓ D R').card ≤
    Real.logb 2 (discLq (ℓ * D) q μ ^ (-(1 / (q - 1)))) + δ * (ℓ * D : ℕ)

def InverseTheorem : Prop :=
  ∀ q : ℝ, 1 < q → ∀ δ : ℝ, 0 < δ → ∀ D₀ : ℕ, 1 ≤ D₀ →
    ∃ ε : ℝ, 0 < ε ∧ ∃ D : ℕ, D₀ ≤ D ∧ ∀ᶠ ℓ : ℕ in atTop, ∀ μ ν : ℤ → ℝ,
      IsDyadicMeasure (ℓ * D) μ → IsDyadicMeasure (ℓ * D) ν →
      (2 : ℝ) ^ (-(ε * (ℓ * D : ℕ))) * discLq (ℓ * D) q μ ^ (1 / q) ≤
        discLq (ℓ * D) q (circConv (ℓ * D) μ ν) ^ (1 / q) →
      ∃ a b : ℤ, ∃ A B : Finset ℤ, ∃ R' R'' : ℕ → ℕ,
        InverseConclusion q δ ℓ D (circTranslate (ℓ * D) a μ) (circTranslate (ℓ * D) b ν)
          A B R' R''

def Theorem32 : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ m : ℕ in atTop, ∀ A B : Finset (ZMod (2 ^ m)),
    (2 : ℝ) ^ (-(τ * m)) * A.card * B.card ^ 2 ≤ Finset.addEnergy A B →
    ∃ H X : Finset (ZMod (2 ^ m)),
      ((H + H).card : ℝ) ≤ (2 : ℝ) ^ (κ * m) * H.card ∧
      (2 : ℝ) ^ (-(κ * m)) * A.card ≤ (A ∩ (X + H)).card ∧
      (2 : ℝ) ^ (-(2 * κ * m)) * X.card * H.card ≤ (2 : ℝ) ^ (-(κ * m)) * A.card ∧
      (2 : ℝ) ^ (-(κ * m)) * B.card ≤ (B ∩ H).card

noncomputable def discretize (μ : Measure ℝ) (m : ℕ) (k : ℤ) : ℝ :=
  if 0 ≤ k ∧ k < 2 ^ m then μ.real (dyadicIco m k) else 0

def Theorem51 (μ : Measure ℝ) (q : ℝ) : Prop :=
  ∀ σ : ℝ, 0 < σ → ∃ ε : ℝ, 0 < ε ∧ ∃ D : ℕ, 3 ≤ D ∧ ∀ᶠ ℓ : ℕ in atTop, ∀ ν : ℤ → ℝ,
    IsDyadicMeasure (ℓ * D) ν →
    discLq (ℓ * D) q ν ^ (1 / (q - 1)) ≤ (2 : ℝ) ^ (-(σ * (ℓ * D : ℕ))) →
    discLq (ℓ * D) q (circConv (ℓ * D) ν (discretize μ (ℓ * D))) ≤
      (2 : ℝ) ^ (-((lqSpectrum μ q + ε) * (ℓ * D : ℕ)))

end Lq

end FractalGeometry
