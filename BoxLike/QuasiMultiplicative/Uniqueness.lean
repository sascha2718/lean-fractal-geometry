module

/-
The uniqueness part of Feng–Käenmäki, Proposition 1.2 (Discrete Contin. Dyn. Syst. 30 (2011)),
which the article quotes as `thm:irred_eq_state` (tex lines 2113 to 2127), on the two-sided
shift `Σ = ℤ → ι` with the potential `‖·‖^q`, `q ≥ 0`: every invariant `q`-equilibrium state
equals every ergodic probability measure with the Gibbs property.

For an invariant `q`-equilibrium state `μ` and `n ≥ 1`, the entropy and the Lyapunov exponent
are at most their averages at level `n`: `h(μ) ≤ H_μ(𝒫_0^{n-1}) / n` and
`λ_1(𝖠, μ) ≤ n⁻¹ ∑_{|w| = n} μ([w]) log ‖A_w‖`, by Fekete's lemma. With
`P(q) = q λ_1(𝖠, μ) + h(μ)` this gives
`n P(q) ≤ H_μ(𝒫_0^{n-1}) + q ∑_{|w| = n} μ([w]) log ‖A_w‖`. The Gibbs bound
`‖A_w‖^q ≤ C e^{n P(q)} ν([w])` turns this into
`D_n(μ ‖ ν) = ∑_{|w| = n} μ([w]) log(μ([w]) / ν([w])) ≤ log C`. Bounded relative entropy gives
`μ ≪ ν` (`absolutelyContinuous_of_blockRelEntropy_le`), and an invariant probability measure
absolutely continuous with respect to an ergodic one equals it. The argument is the one of
`BoxLike/EquilibriumGibbs.lean` for the singular value potential.

* `MatrixTuple.lyapunov₁_le_div`: `λ_1(𝖠, μ) ≤ n⁻¹ ∫ log ‖A_{𝐢|_n}‖ dμ(𝐢)` for `n ≥ 1`.
* `MatrixTuple.IsNormEquilibrium.le_blockEntropy_add`: the block inequality
  `n P(q) ≤ H_μ(𝒫_0^{n-1}) + q ∑_{|w| = n} μ([w]) log ‖A_w‖` of an equilibrium state.
* `MatrixTuple.IsNormEquilibrium.blockRelEntropy_le`: `D_n(μ ‖ ν) ≤ log C` for a measure `ν`
  with the Gibbs property with constant `C`.
* `MatrixTuple.IsNormEquilibrium.absolutelyContinuous_of_hasNormGibbs`,
  `MatrixTuple.IsNormEquilibrium.eq_of_hasNormGibbs`: an invariant `q`-equilibrium state is
  absolutely continuous with respect to every invariant probability measure with the Gibbs
  property, and equals every ergodic one.
-/
public import BoxLike.BernoulliEntropy
public import BoxLike.InvariantMeasures
public import BoxLike.Support.RelativeEntropy
public import BoxLike.TupleEquilibriumNorm

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace MatrixTuple

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {A : ι → Matrix (Fin 2) (Fin 2) ℝ} {q : ℝ}

/-- `λ_1(𝖠, μ) ≤ n⁻¹ ∫ log ‖A_{𝐢|_n}‖ dμ(𝐢)` for an invariant probability measure and every
`n ≥ 1`, in the proof of `thm:irred_eq_state` (Feng–Käenmäki, Proposition 1.2): by Fekete's
lemma the limit defining `λ_1` is the infimum of these averages, since
`log ‖A_𝐢 A_𝐣‖ ≤ log ‖A_𝐢‖ + log ‖A_𝐣‖` and `log ‖A_𝐢‖ ≥ |𝐢| log δ`. -/
theorem lyapunov₁_le_div (hA : ∀ i, (A i).det ≠ 0) {μ : Measure (ℤ → ι)}
    [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ) {n : ℕ} (hn : n ≠ 0) :
    lyapunov₁ A μ ≤ (∫ x, Real.log ‖word A (futureWord x n)‖ ∂μ) / n := by
  have hsub := subadditive_integral_futureWord hμ (G := fun w => Real.log ‖word A w‖)
    fun w w' => by
      rw [← Real.log_mul (norm_word_pos hA w).ne' (norm_word_pos hA w').ne', word_append]
      exact Real.log_le_log (by rw [← word_append]; exact norm_word_pos hA _)
        (Matrix.l2_opNorm_mul _ _)
  have hbdd : BddBelow (Set.range fun n : ℕ =>
      (∫ x, Real.log ‖word A (futureWord x n)‖ ∂μ) / n) := by
    refine ⟨min 0 (Real.log (normLowerBound A)), ?_⟩
    rintro _ ⟨m, rfl⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · exact (min_le_right _ _).trans (le_integral_futureWord_div (le_log_norm_word hA) hm)
  rw [tendsto_nhds_unique (tendsto_lyapunov₁ hA hμ) (hsub.tendsto_lim hbdd)]
  exact hsub.lim_le_div hbdd hn

/-- The block inequality of an invariant `q`-equilibrium state of `‖·‖^q`, `q ≥ 0`, in the proof
of `thm:irred_eq_state` (Feng–Käenmäki, Proposition 1.2): for every `n ≥ 1`,
`n P(q) ≤ H_μ(𝒫_0^{n-1}) + q ∑_{|w| = n} μ([w]) log ‖A_w‖`. The entropy and the Lyapunov
exponent are at most their averages at level `n` (`entropy_le_blockEntropy_div`,
`lyapunov₁_le_div`). -/
theorem IsNormEquilibrium.le_blockEntropy_add (hA : ∀ i, (A i).det ≠ 0) (hq : 0 ≤ q)
    {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ)
    (heq : IsNormEquilibrium A q μ) {n : ℕ} (hn : 0 < n) :
    n * normPressure A q ≤ blockEntropy μ n +
      q * ∑ w : Fin n → ι, μ.real (cylinder w) * Real.log ‖word A (List.ofFn w)‖ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := entropy_le_blockEntropy_div hμ hn.ne'
  have h2 := lyapunov₁_le_div hA hμ hn.ne'
  rw [integral_comp_futureWord_eq_sum μ fun w => Real.log ‖word A w‖] at h2
  rw [le_div_iff₀ hn'] at h1 h2
  have hP : normPressure A q = q * lyapunov₁ A μ + entropy μ := heq
  rw [hP]
  nlinarith [mul_le_mul_of_nonneg_left h2 hq]

/-- The relative entropy bound in the proof of `thm:irred_eq_state` (Feng–Käenmäki,
Proposition 1.2): an invariant `q`-equilibrium state `μ` of `‖·‖^q`, `q ≥ 0`, and a measure `ν`
with `C⁻¹ e^{-n P(q)} ‖A_w‖^q ≤ ν([w])` for all words of length `n ≥ 1` satisfy
`D_n(μ ‖ ν) ≤ log C` for every `n ≥ 1`. By `IsNormEquilibrium.le_blockEntropy_add`,
`n P(q) ≤ H_μ(𝒫_0^{n-1}) + q ∑_{|w| = n} μ([w]) log ‖A_w‖`, and the Gibbs bound gives
`q log ‖A_w‖ ≤ log C + n P(q) + log ν([w])`. -/
theorem IsNormEquilibrium.blockRelEntropy_le (hA : ∀ i, (A i).det ≠ 0) (hq : 0 ≤ q)
    {μ ν : Measure (ℤ → ι)} [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ)
    (heq : IsNormEquilibrium A q μ) {C : ℝ} (hC : 0 < C)
    (hlow : ∀ n : ℕ, 0 < n → ∀ w : Fin n → ι,
      C⁻¹ * (Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn w)‖ ^ q) ≤
        ν.real (cylinder w))
    {n : ℕ} (hn : 0 < n) : blockRelEntropy μ ν n ≤ Real.log C := by
  have hpos : ∀ w : Fin n → ι, 0 < ν.real (cylinder w) := fun w => by
    have := norm_word_pos hA (List.ofFn w)
    exact lt_of_lt_of_le (by positivity) (hlow n hn w)
  have hblock := heq.le_blockEntropy_add hA hq hμ hn
  have hlog : ∀ w : Fin n → ι, q * Real.log ‖word A (List.ofFn w)‖ ≤
      Real.log C + n * normPressure A q + Real.log (ν.real (cylinder w)) := by
    intro w
    have hw := norm_word_pos hA (List.ofFn w)
    have hl := hlow n hn w
    have hφ : ‖word A (List.ofFn w)‖ ^ q ≤
        C * ν.real (cylinder w) * Real.exp (n * normPressure A q) := by
      rw [inv_mul_le_iff₀ hC] at hl
      calc ‖word A (List.ofFn w)‖ ^ q
          = Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn w)‖ ^ q *
              Real.exp (n * normPressure A q) := by
            rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
              mul_one]
        _ ≤ C * ν.real (cylinder w) * Real.exp (n * normPressure A q) :=
            mul_le_mul_of_nonneg_right hl (Real.exp_pos _).le
    have h := Real.log_le_log (Real.rpow_pos_of_pos hw q) hφ
    rwa [Real.log_rpow hw, Real.log_mul (mul_pos hC (hpos w)).ne' (Real.exp_pos _).ne',
      Real.log_exp, Real.log_mul hC.ne' (hpos w).ne', add_right_comm] at h
  have hsum : q * ∑ w : Fin n → ι, μ.real (cylinder w) * Real.log ‖word A (List.ofFn w)‖
      ≤ Real.log C + n * normPressure A q +
        ∑ w : Fin n → ι, μ.real (cylinder w) * Real.log (ν.real (cylinder w)) := by
    calc q * ∑ w : Fin n → ι, μ.real (cylinder w) * Real.log ‖word A (List.ofFn w)‖
        = ∑ w : Fin n → ι, μ.real (cylinder w) * (q * Real.log ‖word A (List.ofFn w)‖) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun w _ => by ring
      _ ≤ ∑ w : Fin n → ι, μ.real (cylinder w) *
            (Real.log C + n * normPressure A q + Real.log (ν.real (cylinder w))) :=
          Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hlog w) measureReal_nonneg
      _ = (∑ w : Fin n → ι, μ.real (cylinder w)) * (Real.log C + n * normPressure A q) +
            ∑ w : Fin n → ι, μ.real (cylinder w) * Real.log (ν.real (cylinder w)) := by
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun w _ => by ring
      _ = _ := by rw [sum_measureReal_cylinder μ n, one_mul]
  rw [blockRelEntropy_eq n fun w => (hpos w).ne']
  linarith

/-- An invariant `q`-equilibrium state of `‖·‖^q`, `q ≥ 0`, is absolutely continuous with respect
to every invariant probability measure with the Gibbs property, in the proof of
`thm:irred_eq_state` (Feng–Käenmäki, Proposition 1.2): the relative entropy of the cylinder
partitions is bounded (`IsNormEquilibrium.blockRelEntropy_le`). -/
theorem IsNormEquilibrium.absolutelyContinuous_of_hasNormGibbs (hA : ∀ i, (A i).det ≠ 0)
    (hq : 0 ≤ q) {μ ν : Measure (ℤ → ι)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MeasurePreserving (shift 1) μ μ) (hν : MeasurePreserving (shift 1) ν ν)
    (heq : IsNormEquilibrium A q μ) (hg : HasNormGibbs A q ν) : μ ≪ ν := by
  obtain ⟨C, hC, hG⟩ := hg
  have hlow : ∀ n : ℕ, 0 < n → ∀ w : Fin n → ι,
      C⁻¹ * (Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn w)‖ ^ q) ≤
        ν.real (cylinder w) := fun n hn w => (hG n hn w).1
  refine absolutelyContinuous_of_blockRelEntropy_le hμ hν (fun n hn w => ?_)
    fun n hn => heq.blockRelEntropy_le hA hq hμ hC hlow hn
  have := norm_word_pos hA (List.ofFn w)
  exact lt_of_lt_of_le (by positivity) (hlow n hn w)

/-- The uniqueness in Feng–Käenmäki, Proposition 1.2 (Discrete Contin. Dyn. Syst. 30 (2011)),
quoted as `thm:irred_eq_state` (tex lines 2113 to 2127), on the two-sided shift: for a tuple of
invertible planar matrices and `q ≥ 0`, an invariant `q`-equilibrium state of `‖·‖^q` equals
every ergodic probability measure with the Gibbs property of `‖·‖^q`. It is absolutely
continuous with respect to it (`IsNormEquilibrium.absolutelyContinuous_of_hasNormGibbs`). -/
theorem IsNormEquilibrium.eq_of_hasNormGibbs (hA : ∀ i, (A i).det ≠ 0) (hq : 0 ≤ q)
    {μ ν : Measure (ℤ → ι)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MeasurePreserving (shift 1) μ μ) (hν : Ergodic (shift 1) ν)
    (heq : IsNormEquilibrium A q μ) (hg : HasNormGibbs A q ν) : μ = ν :=
  hν.eq_of_absolutelyContinuous hμ
    (heq.absolutelyContinuous_of_hasNormGibbs hA hq hμ hν.toMeasurePreserving hg)

end MatrixTuple

end BoxLike
