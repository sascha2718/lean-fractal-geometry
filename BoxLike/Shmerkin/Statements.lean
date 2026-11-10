module

public import BoxLike.Shmerkin.Prop68
public import Mathlib.Combinatorics.Additive.Energy

@[expose] public section

/-!
# Shmerkin, Theorems 2.1, 3.1, 3.2 and 5.1: statements

* `InverseTheorem`: Theorem 2.1, the inverse theorem for `L^q` norms of convolutions, for
  `2^{-m}`-measures on the circle, in integer coordinates.
* `Theorem31`, `Theorem32`: Bourgain's structure theorem for sets of small exponential doubling
  and the asymmetric Balog–Szemerédi–Gowers theorem, the two results the source cites.
* `Theorem51`: Theorem 5.1 for a single measure carried by `[0, 1)`.
-/

open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace BoxLike
namespace Shmerkin

/-! ### Theorem 2.1 -/

/-- A `2^{-m}`-measure (Shmerkin, Section 2): a probability measure on `2^{-m} ℤ ∩ [0, 1)`, written
as the weights `μ k` of the atoms `k 2^{-m}`, `0 ≤ k < 2^m`. -/
structure IsDyadicMeasure (m : ℕ) (μ : ℤ → ℝ) : Prop where
  nonneg : ∀ k, 0 ≤ μ k
  support : ∀ k, μ k ≠ 0 → 0 ≤ k ∧ k < 2 ^ m
  sum_eq_one : ∑ k ∈ Finset.Ico (0 : ℤ) (2 ^ m), μ k = 1

/-- `‖μ‖_q^q = ∑_y μ(y)^q` for a `2^{-m}`-measure `μ`. -/
noncomputable def discLq (m : ℕ) (q : ℝ) (μ : ℤ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Ico (0 : ℤ) (2 ^ m), μ k ^ q

/-- The convolution `μ ∗ ν` on the circle `ℝ/ℤ` of two `2^{-m}`-measures. -/
noncomputable def circConv (m : ℕ) (μ ν : ℤ → ℝ) (k : ℤ) : ℝ :=
  if 0 ≤ k ∧ k < 2 ^ m then ∑ i ∈ Finset.Ico (0 : ℤ) (2 ^ m), μ i * ν ((k - i) % 2 ^ m) else 0

/-- The translate of a `2^{-m}`-measure by `a 2^{-m}` on the circle. -/
noncomputable def circTranslate (m : ℕ) (a : ℤ) (μ : ℤ → ℝ) (k : ℤ) : ℝ :=
  if 0 ≤ k ∧ k < 2 ^ m then μ ((k - a) % 2 ^ m) else 0

/-- `N_{n'}(A ∩ D_n(x))` for a `2^{-m}`-set `A`, in integer coordinates: the number of
`2^{-n'}`-intervals that meet `A` inside the `2^{-n}`-interval containing `x 2^{-m}`. -/
def branching (m n n' : ℕ) (A : Finset ℤ) (x : ℤ) : ℕ :=
  ((A.filter fun y => y / 2 ^ (m - n) = x / 2 ^ (m - n)).image fun y => y / 2 ^ (m - n')).card

/-- `x 2^{-m} ∈ ½ D_{m - n}(x 2^{-m})`: the point lies in the closed middle half of its dyadic
interval of length `2^{n - m}`. -/
def InMiddleHalf (n : ℕ) (x : ℤ) : Prop :=
  2 ^ n ≤ 4 * (x % 2 ^ n) ∧ 4 * (x % 2 ^ n) ≤ 3 * 2 ^ n

/-- The set `S` of Theorem 2.1 (vi): the scales `s ∈ [ℓ]` with `R'_s ≥ 2^{(1 - δ) D}`. -/
noncomputable def fullScales (δ : ℝ) (ℓ D : ℕ) (R' : ℕ → ℕ) : Finset ℕ :=
  open Classical in (Finset.range ℓ).filter fun s => (2 : ℝ) ^ ((1 - δ) * D) ≤ R' s

/-- The conclusions (A-i) to (vi) of Theorem 2.1, for the translated measures `μ, ν`, the sets
`A ⊆ supp μ`, `B ⊆ supp ν` and the branching numbers `R'_s`, `R''_s`, with `m = ℓ D`. -/
structure InverseConclusion (q δ : ℝ) (ℓ D : ℕ) (μ ν : ℤ → ℝ) (A B : Finset ℤ)
    (R' R'' : ℕ → ℕ) : Prop where
  pos_A : ∀ x ∈ A, 0 < μ x
  pos_B : ∀ y ∈ B, 0 < ν y
  /-- (A-i) -/
  lq_A : (2 : ℝ) ^ (-(δ * (ℓ * D : ℕ))) * discLq (ℓ * D) q μ ^ (1 / q) ≤
    (∑ x ∈ A, μ x ^ q) ^ (1 / q)
  /-- (A-ii) -/
  flat_A : ∀ x ∈ A, ∀ y ∈ A, μ y ≤ 2 * μ x
  /-- (A-iii) -/
  regular_A : ∀ s < ℓ, ∀ x ∈ A, branching (ℓ * D) (s * D) ((s + 1) * D) A x = R' s
  /-- (A-iv) -/
  middle_A : ∀ x ∈ A, ∀ s < ℓ, InMiddleHalf (ℓ * D - s * D) x
  /-- (B-i) -/
  mass_B : (2 : ℝ) ^ (-(δ * (ℓ * D : ℕ))) ≤ ∑ y ∈ B, ν y
  /-- (B-ii) -/
  flat_B : ∀ x ∈ B, ∀ y ∈ B, ν y ≤ 2 * ν x
  /-- (B-iii) -/
  regular_B : ∀ s < ℓ, ∀ y ∈ B, branching (ℓ * D) (s * D) ((s + 1) * D) B y = R'' s
  /-- (B-iv) -/
  middle_B : ∀ y ∈ B, ∀ s < ℓ, InMiddleHalf (ℓ * D - s * D) y
  /-- (v) -/
  dichotomy : ∀ s < ℓ, R'' s = 1 ∨ (2 : ℝ) ^ ((1 - δ) * D) ≤ R' s
  /-- (vi), with `‖ν‖_q^{-q'} = (‖ν‖_q^q)^{-1/(q-1)}` -/
  count_le : Real.logb 2 (discLq (ℓ * D) q ν ^ (-(1 / (q - 1)))) - δ * (ℓ * D : ℕ) ≤
    D * (fullScales δ ℓ D R').card
  /-- (vi) -/
  le_count : (D : ℝ) * (fullScales δ ℓ D R').card ≤
    Real.logb 2 (discLq (ℓ * D) q μ ^ (-(1 / (q - 1)))) + δ * (ℓ * D : ℕ)

/-- Theorem 2.1 of Shmerkin, the inverse theorem for `L^q` norms of convolutions: given
`q ∈ (1, ∞)`, `δ > 0` and `D₀ ∈ ℕ` there are `ε > 0` and `D ≥ D₀` such that for all large `ℓ`,
with `m = ℓ D`, any `2^{-m}`-measures with `‖μ ∗ ν‖_q ≥ 2^{-ε m} ‖μ‖_q` (convolution on the
circle) have, after translation by multiples of `2^{-m}`, sets `A ⊆ supp μ`, `B ⊆ supp ν` with
(A-i) to (vi). The middle-half condition (A-iv), (B-iv) is read with the closed middle half. -/
def InverseTheorem : Prop :=
  ∀ q : ℝ, 1 < q → ∀ δ : ℝ, 0 < δ → ∀ D₀ : ℕ, 1 ≤ D₀ →
    ∃ ε : ℝ, 0 < ε ∧ ∃ D : ℕ, D₀ ≤ D ∧ ∀ᶠ ℓ : ℕ in atTop, ∀ μ ν : ℤ → ℝ,
      IsDyadicMeasure (ℓ * D) μ → IsDyadicMeasure (ℓ * D) ν →
      (2 : ℝ) ^ (-(ε * (ℓ * D : ℕ))) * discLq (ℓ * D) q μ ^ (1 / q) ≤
        discLq (ℓ * D) q (circConv (ℓ * D) μ ν) ^ (1 / q) →
      ∃ a b : ℤ, ∃ A B : Finset ℤ, ∃ R' R'' : ℕ → ℕ,
        InverseConclusion q δ ℓ D (circTranslate (ℓ * D) a μ) (circTranslate (ℓ * D) b ν)
          A B R' R''

/-! ### Theorems 3.1 and 3.2 -/

/-- Theorem 3.1 of Shmerkin (Bourgain's structure theorem for sets of small exponential doubling,
"emerges from the constructions in Sections 2 and 3" of J. Bourgain, J. Anal. Math. 112 (2010)):
given a large `T ∈ ℕ`, for all large `m₁`, with `m = m₁ T`, every `2^{-m}`-set `H ⊆ [0, 1)` with
`|H + H| ≤ 2^{2^{-2T-1} m} |H|` contains `H'` with `|H'| ≥ 2^{-(2 log T/√T) m} |H|`, a set
`S ⊆ [m₁]` and integers `R_s`, `n_s ∈ [sT, (s+1)T)` (`s ∈ S`) such that `H'` has no branching
between the levels `sT` and `(s+1)T` for `s ∉ S`, uniform branching `R_s` between `sT` and `n_s`
and none between `n_s` and `(s+1)T` for `s ∈ S`, and `2^{(1 - T^{-1/2})(n_s - sT)} < R_s ≤
2^{n_s - sT}`. Sets are written in integer coordinates `x ↦ x 2^{-m}`; logarithms are to base `2`.
-/
def Theorem31 : Prop :=
  ∀ᶠ T : ℕ in atTop, ∀ᶠ m₁ : ℕ in atTop, ∀ H : Finset ℤ,
    (∀ x ∈ H, 0 ≤ x ∧ x < 2 ^ (m₁ * T)) →
    ((H + H).card : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (-(2 * (T : ℝ) + 1)) * (m₁ * T : ℕ)) * H.card →
    ∃ H' ⊆ H, ∃ S ⊆ Finset.range m₁, ∃ R n : ℕ → ℕ,
      (2 : ℝ) ^ (-(2 * Real.logb 2 T / Real.sqrt T * (m₁ * T : ℕ))) * H.card ≤ H'.card ∧
      (∀ s < m₁, s ∉ S → ∀ x ∈ H', branching (m₁ * T) (s * T) ((s + 1) * T) H' x = 1) ∧
      (∀ s ∈ S, s * T ≤ n s ∧ n s < (s + 1) * T ∧
        (∀ x ∈ H', branching (m₁ * T) (s * T) (n s) H' x = R s ∧
          branching (m₁ * T) (n s) ((s + 1) * T) H' x = 1) ∧
        (2 : ℝ) ^ ((1 - 1 / Real.sqrt T) * ((n s : ℝ) - s * T)) < R s ∧
        (R s : ℝ) ≤ (2 : ℝ) ^ ((n s : ℝ) - s * T))

/-- Theorem 3.2 of Shmerkin, the asymmetric Balog–Szemerédi–Gowers theorem (T. Tao and V. Vu,
*Additive combinatorics*, Theorem 2.35), for `2^{-m}`-sets of the circle `ℝ/ℤ`, written as subsets
of `ZMod (2^m)`: given `κ > 0` there is `τ > 0` such that for large `m`, if
`E(A, B) ≥ 2^{-τ m} |A| |B|^2`, there are an `(m, κ)`-small doubling set `H` and a set `X` with
`|A ∩ (X + H)| ≥ 2^{-κ m} |A| ≥ 2^{-2κ m} |X| |H|` and `|B ∩ H| ≥ 2^{-κ m} |B|`. -/
def Theorem32 : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ m : ℕ in atTop, ∀ A B : Finset (ZMod (2 ^ m)),
    (2 : ℝ) ^ (-(τ * m)) * A.card * B.card ^ 2 ≤ Finset.addEnergy A B →
    ∃ H X : Finset (ZMod (2 ^ m)),
      ((H + H).card : ℝ) ≤ (2 : ℝ) ^ (κ * m) * H.card ∧
      (2 : ℝ) ^ (-(κ * m)) * A.card ≤ (A ∩ (X + H)).card ∧
      (2 : ℝ) ^ (-(2 * κ * m)) * X.card * H.card ≤ (2 : ℝ) ^ (-(κ * m)) * A.card ∧
      (2 : ℝ) ^ (-(κ * m)) * B.card ≤ (B ∩ H).card

/-! ### Theorem 5.1 -/

/-- `μ^{(m)}` as a `2^{-m}`-measure: the masses `μ(D_m(k))`, `0 ≤ k < 2^m`. It is a
`2^{-m}`-measure when `μ` is a probability measure carried by `[0, 1)`. -/
noncomputable def discretize (μ : Measure ℝ) (m : ℕ) (k : ℤ) : ℝ :=
  if 0 ≤ k ∧ k < 2 ^ m then μ.real (dyadicIco m k) else 0

/-- Theorem 5.1 of Shmerkin for a single measure `μ` carried by `[0, 1)`, with `τ = τ(μ, ·)` in
place of `T` (Section 6.4): given `σ > 0` there are `ε > 0` and `D ≥ 3` such that for large `ℓ`,
with `m = ℓ D`, every `2^{-m}`-measure `ν` with `‖ν‖_q^{q'} ≤ 2^{-σ m}` has
`‖ν ∗ μ^{(m)}‖_q^q ≤ 2^{-(τ(q) + ε) m}` (convolution on the circle). The source proves the bound
for `m = ℓ D` and passes to every large `m` by applying the argument to `⌊m/D⌋ D`; that step is
made on the line, in `flattening_of_theorem51`. -/
def Theorem51 (μ : Measure ℝ) (q : ℝ) : Prop :=
  ∀ σ : ℝ, 0 < σ → ∃ ε : ℝ, 0 < ε ∧ ∃ D : ℕ, 3 ≤ D ∧ ∀ᶠ ℓ : ℕ in atTop, ∀ ν : ℤ → ℝ,
    IsDyadicMeasure (ℓ * D) ν →
    discLq (ℓ * D) q ν ^ (1 / (q - 1)) ≤ (2 : ℝ) ^ (-(σ * (ℓ * D : ℕ))) →
    discLq (ℓ * D) q (circConv (ℓ * D) ν (discretize μ (ℓ * D))) ≤
      (2 : ℝ) ^ (-((lqSpectrum μ q + ε) * (ℓ * D : ℕ)))

end Shmerkin
end BoxLike
