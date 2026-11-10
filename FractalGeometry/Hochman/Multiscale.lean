import FractalGeometry.Hochman.Entropy

/-!
# Global entropy from local entropy

Hochman's Lemma 3.4 (Hochman, *On self-similar sets with overlaps and inverse theorems for
entropy*, Ann. of Math. 180 (2014), Section 3.2) in the shared vocabulary
`FractalGeometry.SelfConformal`, with the levels shifted by `i`: for a probability measure `θ` of
bounded support and `m, n ≥ 1`,
`|H(θ, 𝒟_{i+n})/n - 𝔼_{i ≤ j < i+n}(H(θ_{x,j}, 𝒟_{j+m})/m)| ≤ (H(θ, 𝒟_i) + m)/n`.

## Main declarations

* `sum_integral_component_eq`: the sum of the average component entropies over `n` consecutive
  levels, as a sum of `m` entropy differences.
* `abs_dyadicEntropy_div_sub_avg_le`: Lemma 3.4.
-/

namespace FractalGeometry.Hochman

open MeasureTheory Set FractalGeometry.SelfConformal

/-- `∑_{p<n} ∫ H(θ_{x,i+p}, 𝒟_{i+p+m}) dθ(x) = ∑_{s<m} (H(θ, 𝒟_{i+n+s}) - H(θ, 𝒟_{i+s}))`, by the
chain rule and telescoping. -/
theorem sum_integral_component_eq (θ : Measure ℝ) [IsProbabilityMeasure θ] {a b : ℝ}
    (hab : θ (Icc a b)ᶜ = 0) (i n m : ℕ) :
    ∑ p ∈ Finset.range n, ∫ x, dyadicEntropy (component θ (i + p) x) (i + p + m) ∂θ =
      ∑ s ∈ Finset.range m, (dyadicEntropy θ (i + (n + s)) - dyadicEntropy θ (i + s)) := by
  have h := ExactOverlaps.Entropy.sum_window_differences (fun t => dyadicEntropy θ (i + t)) n m
  rw [← h]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← dyadicEntropy_add_sub_eq_integral θ hab (i + p) m, add_assoc]

/-- Hochman's Lemma 3.4 with the levels shifted by `i`: the normalised entropy
`H(θ, 𝒟_{i+n})/n` differs from the average over the levels `i ≤ j < i + n` of the normalised
component entropies `𝔼(H(θ_{x,j}, 𝒟_{j+m})/m)` by at most `(H(θ, 𝒟_i) + m)/n`. -/
theorem abs_dyadicEntropy_div_sub_avg_le (θ : Measure ℝ) [IsProbabilityMeasure θ] {a b : ℝ}
    (hab : θ (Icc a b)ᶜ = 0) (i : ℕ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    |dyadicEntropy θ (i + n) / n -
        (∑ p ∈ Finset.range n, ∫ x, dyadicEntropy (component θ (i + p) x) (i + p + m) / m ∂θ) /
          n| ≤
      (dyadicEntropy θ i + m) / n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  set A : ℕ → ℝ := fun t => dyadicEntropy θ (i + t)
  have hA0 : 0 ≤ A 0 := dyadicEntropy_nonneg θ prob_le_one _
  have hsum : ∑ p ∈ Finset.range n,
      ∫ x, dyadicEntropy (component θ (i + p) x) (i + p + m) / m ∂θ =
        (∑ s ∈ Finset.range m, (A (n + s) - A s)) / m := by
    simp_rw [integral_div]
    rw [← Finset.sum_div, sum_integral_component_eq θ hab i n m]
  -- each window differs from `A n` by an amount in `[-(A 0 + m), m]`
  have hlow : ∀ s ∈ Finset.range m, A n - (A 0 + m) ≤ A (n + s) - A s := by
    intro s hs
    have hs' : (s : ℝ) ≤ m := by exact_mod_cast (Finset.mem_range.1 hs).le
    have h1 : A n ≤ A (n + s) := by
      simp only [A, ← add_assoc]
      exact dyadicEntropy_le_add θ hab (i + n) s
    have h2 : A s - A 0 ≤ s := by
      simpa [A] using dyadicEntropy_add_sub_le θ hab i s
    linarith
  have hup : ∀ s ∈ Finset.range m, A (n + s) - A s ≤ A n + m := by
    intro s hs
    have hs' : (s : ℝ) ≤ m := by exact_mod_cast (Finset.mem_range.1 hs).le
    have h1 : A (n + s) - A n ≤ s := by
      simp only [A, ← add_assoc]
      exact dyadicEntropy_add_sub_le θ hab (i + n) s
    have h2 : A 0 ≤ A s := by
      simpa [A] using dyadicEntropy_le_add θ hab i s
    linarith
  have hS1 := Finset.sum_le_sum hlow
  have hS2 := Finset.sum_le_sum hup
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hS1 hS2
  set S := ∑ s ∈ Finset.range m, (A (n + s) - A s)
  have hkey : |(m : ℝ) * A n - S| ≤ m * (A 0 + m) := by
    rw [abs_le]
    constructor <;> nlinarith
  have heq : A n / n - S / m / n = ((m : ℝ) * A n - S) / (m * n) := by
    field_simp
  rw [hsum, show dyadicEntropy θ (i + n) = A n from rfl, show dyadicEntropy θ i = A 0 by simp [A],
    heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < m * n),
    div_le_div_iff₀ (by positivity) hn']
  have := mul_le_mul_of_nonneg_right hkey hn'.le
  nlinarith

end FractalGeometry.Hochman
