module

/-
Grouping a Bernoulli measure in pairs, `sec:normalisation` (tex lines 2248 to 2249): the image
`β_*μ` of a Bernoulli measure `μ` with the weights `(p_i)` under the grouping map `β` of
`thm:two-block-normalisation` is the Bernoulli measure on the paired alphabet with the weights
`p_{(i,j)} = p_i p_j`. Hence, if `μ^(2) = β_*μ` is not Bernoulli, neither is `μ`.

* `flatFin`, `flatFin_pair`: a word of length `n` over the paired alphabet as the word of length
  `2n` over the original alphabet, indexed through `Fin n × Fin 2 ≃ Fin (n * 2)`.
* `preimage_group_shift_cylinder`: `β⁻¹(σ^{-k}[w]) = σ^{-2k}[w']` for the underlying word `w'`.
* `IsBernoulli.map_group`: grouping a Bernoulli measure in pairs gives a Bernoulli measure.
* `not_isBernoulli_of_map_group`: if `μ^(2)` is not Bernoulli, then `μ` is not Bernoulli.
-/
public import BoxLike.GibbsProperties
public import BoxLike.Grouping

@[expose] public section

namespace BoxLike

open MeasureTheory

section Flat

variable {α : Type*} {n : ℕ}

/-- The word `i_0 i_1 ⋯ i_{2n-1}` of length `2n` underlying a word `(i_0, i_1) ⋯` of length `n`
over the paired alphabet: the letter at the position `b + 2a` is the `b`-th entry of the `a`-th
pair. -/
def flatFin (w : Fin n → α × α) : Fin (n * 2) → α := fun j =>
  if (finProdFinEquiv.symm j).2 = 0 then (w (finProdFinEquiv.symm j).1).1
  else (w (finProdFinEquiv.symm j).1).2

/-- The two letters of the `a`-th pair sit at the positions `2a` and `2a + 1`. -/
theorem flatFin_pair (w : Fin n → α × α) (a : Fin n) (b : Fin 2) :
    flatFin w (finProdFinEquiv (a, b)) = if b = 0 then (w a).1 else (w a).2 := by
  simp [flatFin]

/-- The position of `(a, b)` in the underlying word is `b + 2a`. -/
theorem coe_finProdFinEquiv_two (a : Fin n) (b : Fin 2) :
    ((finProdFinEquiv (a, b) : Fin (n * 2)) : ℕ) = b + 2 * a := rfl

/-- `β⁻¹(σ^{-k}[w]) = σ^{-2k}[w']`: the pairs at the positions `k, …, k + n - 1` of `β(𝐢)` are
the letters at the positions `2k, …, 2k + 2n - 1` of `𝐢`. -/
theorem preimage_group_shift_cylinder (k : ℤ) (w : Fin n → α × α) :
    group ⁻¹' (shift k ⁻¹' cylinder w) = shift (2 * k) ⁻¹' cylinder (flatFin w) := by
  ext x
  simp only [Set.mem_preimage, mem_cylinder, shift_apply, group_apply]
  constructor
  · intro h j
    obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective j
    rw [flatFin_pair, coe_finProdFinEquiv_two]
    have ha := h a
    rw [Prod.ext_iff] at ha
    fin_cases b
    · simp only [Fin.isValue, Fin.zero_eta, ↓reduceIte]
      rw [← ha.1]
      congr 1
      push_cast
      ring
    · simp only [Fin.isValue, Fin.mk_one, one_ne_zero, ↓reduceIte]
      rw [← ha.2]
      congr 1
      push_cast
      ring
  · intro h a
    have h0 := h (finProdFinEquiv (a, 0))
    have h1 := h (finProdFinEquiv (a, 1))
    rw [flatFin_pair, coe_finProdFinEquiv_two] at h0 h1
    simp only [Fin.isValue, ↓reduceIte, Fin.val_zero, Fin.val_one, one_ne_zero] at h0 h1
    refine Prod.ext ?_ ?_
    · dsimp only
      rw [← h0]
      congr 1
      push_cast
      ring
    · dsimp only
      rw [← h1]
      congr 1
      push_cast
      ring

end Flat

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ : Measure (ℤ → α)}

/-- Grouping a Bernoulli measure in pairs gives a Bernoulli measure (tex lines 2248 to 2249):
if `μ` is Bernoulli with the weights `(p_i)`, then `μ^(2) = β_*μ` is Bernoulli with the weights
`p_{(i,j)} = p_i p_j` on the paired alphabet. -/
theorem IsBernoulli.map_group (h : IsBernoulli μ) : IsBernoulli (μ.map group) := by
  obtain ⟨p, hp0, hp1, hp⟩ := h
  refine ⟨fun q => p q.1 * p q.2, fun q => mul_nonneg (hp0 _) (hp0 _), ?_, ?_⟩
  · rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hp1, mul_one]
  · intro k n hn w
    rw [map_measureReal_apply measurable_group
        ((measurable_shift k) (measurableSet_cylinder w)),
      preimage_group_shift_cylinder, hp (2 * k) (n * 2) (by omega)]
    rw [← Fintype.prod_equiv finProdFinEquiv (fun q => p (flatFin w (finProdFinEquiv q)))
        (fun j => p (flatFin w j)) fun _ => rfl, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Fin.prod_univ_two, flatFin_pair, flatFin_pair]
    simp

/-- The step of `sec:normalisation` (tex lines 2248 to 2249): if `μ^(2) = β_*μ` is not a
Bernoulli measure, then neither is `μ`. -/
theorem not_isBernoulli_of_map_group (h : ¬ IsBernoulli (μ.map group)) : ¬ IsBernoulli μ :=
  fun hμ => h hμ.map_group

end BoxLike
