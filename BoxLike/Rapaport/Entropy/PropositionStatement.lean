module

/-
The statement of Proposition 1.7 of Rapaport (arXiv:2309.03985, lines 1075 to 1188 of his tex)
for `d = 2`, as the `Prop` `Prop17 χ`, so that the entropy increase theorem (his Theorem 1.4) can
be proved against it while its proof is written in `Rapaport/Entropy/Proposition.lean`.

* `Prop17 χ`: for every `0 < ε < 1` there is `δ > 0` such that for parameters
  `ε⁻¹ ≪ m₂ ≪ k₂ ≪ m₁ ≪ k₁ ≪ n` and every `θ` carried by a ball of radius `ε⁻¹` with
  `H(θ, ℰ_n) / n > ε`, for some `j ∈ {1, 2}` more than `δ n` levels `q ∈ [1, n]` satisfy
  `H(θ^{∗k_j}, ℰ_{q+m_j} ∣ ℰ_q ∨ π_{j'}⁻¹ ℰ_{q+m_j}) / m_j > χ_j - ε`.
-/
public import BoxLike.Rapaport.Defs

@[expose] public section

namespace BoxLike.Rapaport

open MeasureTheory

open Classical in
/-- Proposition 1.7 of the source for `d = 2` (lines 1075 to 1188): the conclusion lists the
levels `q = i + 1`, `i < n`, at which the slices of `θ^{∗k_j}` in direction `j` have almost full
conditional entropy; the sets `Q₁`, `Q₂` are the filtered ranges, and one of them has more than
`δ n` elements. The nested quantifiers encode `ε⁻¹ ≪ m₂ ≪ k₂ ≪ m₁ ≪ k₁ ≪ n`. -/
def Prop17 (χ : Exps) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ : ℝ, 0 < δ ∧
    ∃ M₂ : ℕ, ∀ m₂ : ℕ, M₂ ≤ m₂ → ∃ K₂ : ℕ, ∀ k₂ : ℕ, K₂ ≤ k₂ →
    ∃ M₁ : ℕ, ∀ m₁ : ℕ, M₁ ≤ m₁ → ∃ K₁ : ℕ, ∀ k₁ : ℕ, K₁ ≤ k₁ →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ (θ : Measure (ℝ × ℝ)) [IsProbabilityMeasure θ] (c : ℝ × ℝ), InBall θ c ε⁻¹ →
    ε < ent θ (χ.E n) / n →
    δ * n < (((Finset.range n).filter fun i =>
        χ.χ₁ - ε < cent (convPow θ k₁) (χ.E ((i + 1 + m₁ : ℕ) : ℤ))
          (fun z => (χ.E ((i + 1 : ℕ) : ℤ) z, χ.E₂ ((i + 1 + m₁ : ℕ) : ℤ) z)) / m₁).card : ℝ) ∨
    δ * n < (((Finset.range n).filter fun i =>
        χ.χ₂ - ε < cent (convPow θ k₂) (χ.E ((i + 1 + m₂ : ℕ) : ℤ))
          (fun z => (χ.E ((i + 1 : ℕ) : ℤ) z, χ.E₁ ((i + 1 + m₂ : ℕ) : ℤ) z)) / m₂).card : ℝ)

end BoxLike.Rapaport
