module

/-
The theorem of Furstenberg and Kesten for the backward products of an invertible planar tuple,
the first half of Oseledets' multiplicative ergodic theorem cited in `sec:lyapunov_exponents`
(Oseledec 1968, tex line 1508). For an ergodic `μ ∈ M_σ(Σ)` and `M_n(𝐢) = A_{i_{-n}} ⋯ A_{i_{-1}}`,
`n⁻¹ log α_1(M_n(𝐢)) → λ_1(𝖠, μ)` and `n⁻¹ log α_2(M_n(𝐢)) → λ_2(𝖠, μ)` for `μ`-almost every
`𝐢`, where the exponents are the limits of `n⁻¹ ∫ log α_i(A_{i_0} ⋯ A_{i_{n-1}}) dμ` of tex lines
1572 to 1581. Both follow from Kingman's theorem (`BoxLike/Kingman.lean`) over the inverse shift
`σ⁻¹`, which is ergodic: `log α_1` is sub-additive and `-log α_2` is sub-additive on words, and
the integrals of a function of `M_n(𝐢)` and of `A_{i_0} ⋯ A_{i_{n-1}}` agree by invariance.

* `pastWord_add`, `MatrixTuple.pastProd_add`, `MatrixTuple.pastProd_succ`,
  `MatrixTuple.pastProd_zero`: the cocycle identities `M_{m+n}(𝐢) = M_n(σ^{-m} 𝐢) M_m(𝐢)`,
  `M_{n+1}(𝐢) = A_{i_{-n-1}} M_n(𝐢)` and `M_0(𝐢) = 1`.
* `measurable_comp_pastWord`, `tendsto_pastWord_of_subadditive`: the backward form of Kingman's
  theorem on `Σ` for a sub-additive function of words.
* `MatrixTuple.tendsto_log_norm_pastProd`, `MatrixTuple.tendsto_log_alpha₂_pastProd`: the
  theorem of Furstenberg and Kesten for `α_1` and `α_2`.
-/
public import BoxLike.Kingman
public import BoxLike.SigmaMeasure
public import BoxLike.Planar.Oseledets
public import BoxLike.Planar.Lyapunov

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set Matrix
open scoped Matrix.Norms.L2Operator

/-- `i_{-m-n} ⋯ i_{-1}` is `i_{-m-n} ⋯ i_{-m-1}`, the past word of length `n` of `σ^{-m} 𝐢`,
followed by `i_{-m} ⋯ i_{-1}`. -/
theorem pastWord_add {α : Type*} (x : ℤ → α) (m n : ℕ) :
    pastWord x (m + n) = pastWord (shift (-(m : ℤ)) x) n ++ pastWord x m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, pastWord_succ, ih, pastWord_succ, List.cons_append, shift_apply]
    congr 2
    push_cast
    ring

section Backward

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- A function of the past word `i_{-n} ⋯ i_{-1}` is measurable. -/
theorem measurable_comp_pastWord (G : List α → ℝ) (n : ℕ) :
    Measurable fun x : ℤ → α => G (pastWord x n) := by
  simp only [pastWord_eq_futureWord]
  exact (measurable_comp_futureWord G n).comp (measurable_shift _)

/-- The backward form of Kingman's theorem on `Σ`: if `G` is sub-additive on words,
`G(𝐢𝐣) ≤ G(𝐢) + G(𝐣)`, `μ` is ergodic and `n⁻¹ ∫ G(i_0 ⋯ i_{n-1}) dμ → L`, then
`n⁻¹ G(i_{-n} ⋯ i_{-1}) → L` for `μ`-almost every `𝐢`. The functions
`f_n(𝐢) = G(i_{-n} ⋯ i_{-1})` form a sub-additive cocycle over `σ⁻¹`, and
`∫ f_n dμ = ∫ G(i_0 ⋯ i_{n-1}) dμ` by invariance. -/
theorem tendsto_pastWord_of_subadditive {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) {G : List α → ℝ} (hsub : ∀ w w', G (w ++ w') ≤ G w + G w')
    {L : ℝ} (hL : Tendsto (fun n : ℕ => (∫ x, G (futureWord x n) ∂μ) / n) atTop (𝓝 L)) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => G (pastWord x n) / n) atTop (𝓝 L) := by
  have hμ := herg.toMeasurePreserving
  have hcoc : IsSubadditiveCocycle (shift (-1)) fun n x => G (pastWord x n) := by
    intro m n x
    dsimp only
    rw [iterate_shift_neg_one, pastWord_add, add_comm (G (pastWord x m))]
    exact hsub _ _
  have hint : ∀ n, Integrable (fun x : ℤ → α => G (pastWord x n)) μ := fun n => by
    simp only [pastWord_eq_futureWord]
    exact (measurePreserving_shift_neg_natCast hμ n).integrable_comp_of_integrable
      (integrable_comp_futureWord G n)
  have hI : ∀ n : ℕ, ∫ x, G (pastWord x n) ∂μ = ∫ x, G (futureWord x n) ∂μ := fun n => by
    simp only [pastWord_eq_futureWord]
    exact integral_comp_shift_neg hμ n (measurable_comp_futureWord G n)
  exact kingman_ergodic_of_tendsto (ergodic_shift_neg_one herg) hcoc
    (fun n => measurable_comp_pastWord G n) hint (hL.congr fun n => by rw [hI])

end Backward

namespace MatrixTuple

variable {ι : Type*} {A : ι → Matrix (Fin 2) (Fin 2) ℝ}

/-- The cocycle identity `M_{m+n}(𝐢) = M_n(σ^{-m} 𝐢) M_m(𝐢)` of the backward products. -/
theorem pastProd_add (x : ℤ → ι) (m n : ℕ) :
    pastProd A x (m + n) = pastProd A (shift (-(m : ℤ)) x) n * pastProd A x m := by
  rw [pastProd, pastWord_add, word_append, pastProd, pastProd]

/-- `M_{n+1}(𝐢) = A_{i_{-n-1}} M_n(𝐢)`: the backward products grow on the left. -/
theorem pastProd_succ (x : ℤ → ι) (n : ℕ) :
    pastProd A x (n + 1) = A (x (-((n : ℤ) + 1))) * pastProd A x n := by
  rw [pastProd, pastWord_succ, pastProd]
  simp [word]

/-- `M_0(𝐢)` is the identity. -/
@[simp] theorem pastProd_zero (x : ℤ → ι) : pastProd A x 0 = 1 := rfl

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]

/-- The theorem of Furstenberg and Kesten for `α_1`, the first half of Oseledets' theorem in
`sec:lyapunov_exponents` (tex line 1508): for an invertible tuple and an ergodic `μ`,
`n⁻¹ log ‖A_{i_{-n}} ⋯ A_{i_{-1}}‖ → λ_1(𝖠, μ)` for `μ`-almost every `𝐢`. -/
theorem tendsto_log_norm_pastProd (hA : ∀ i, (A i).det ≠ 0) (herg : Ergodic (shift 1) μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => Real.log ‖pastProd A x n‖ / n) atTop
      (𝓝 (lyapunov₁ A μ)) :=
  tendsto_pastWord_of_subadditive herg (G := fun w => Real.log ‖word A w‖)
    (log_norm_word_append_le hA) (tendsto_lyapunov₁_of_det_ne_zero hA herg.toMeasurePreserving)

/-- The theorem of Furstenberg and Kesten for `α_2 = |det| / α_1`, the first half of Oseledets'
theorem in `sec:lyapunov_exponents` (tex line 1508): for an invertible tuple and an ergodic `μ`,
`n⁻¹ log α_2(A_{i_{-n}} ⋯ A_{i_{-1}}) → λ_2(𝖠, μ)` for `μ`-almost every `𝐢`. The function
`-log α_2` is sub-additive on words. -/
theorem tendsto_log_alpha₂_pastProd (hA : ∀ i, (A i).det ≠ 0) (herg : Ergodic (shift 1) μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ =>
      Real.log (|(pastProd A x n).det| / ‖pastProd A x n‖) / n) atTop (𝓝 (lyapunov₂ A μ)) := by
  have hL := (tendsto_lyapunov₂_of_det_ne_zero hA herg.toMeasurePreserving).neg
  have h := tendsto_pastWord_of_subadditive herg
    (G := fun w => -Real.log (|(word A w).det| / ‖word A w‖))
    (fun w w' => by linarith [le_log_abs_det_div_norm_word_append hA w w'])
    (L := -lyapunov₂ A μ) (hL.congr fun n => by rw [integral_neg, neg_div])
  filter_upwards [h] with x hx
  have hx' := hx.neg
  rw [neg_neg] at hx'
  refine hx'.congr fun n => ?_
  simp only [pastProd, neg_div, neg_neg]

end MatrixTuple

end BoxLike
