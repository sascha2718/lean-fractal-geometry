module

/-
The measure of `Σ'`, `Σ^τ` and `Σ^ω`: the assertion `μ(Σ') = 1` of `sec:lyapunov_exponents` (tex
lines 1598 to 1600), the almost sure limit `eq:lyapunov_exponent_gsystem`, and
`thm:sigma_tau_omega_positive_eq_measure` of `sec:normalisation`.

The backward growth rate of `eq:lyapunov_exponent_gsystem` along `𝐣 ∈ Σ_Z` is a Birkhoff average
of `𝐣 ↦ log |g'_{j_{-1}}|` under the inverse shift `σ⁻¹`. For an ergodic measure on `Σ_Z` this
gives `eq:lyapunov_exponent_gsystem`. For an ergodic measure `μ` on `Σ` the average
`(τ_*μ + ω_*μ) / 2` is an invariant measure on `Σ_Z`, so the two backward rates `r_1(𝐢)` along
`τ(𝐢)` and `r_2(𝐢)` along `ω(𝐢)` exist for `μ`-almost every `𝐢`. The shift keeps or exchanges the
two rates, so `max{r_1, r_2}` and `min{r_1, r_2}` are invariant, hence constant, and the
constants are `λ_1(𝖠, μ)` and `λ_2(𝖠, μ)` by dominated convergence, since
`max{|g'_{τ(𝐢)}|, |g'_{ω(𝐢)}|} = α_1(A_𝐢)` and `min{|g'_{τ(𝐢)}|, |g'_{ω(𝐢)}|} = α_2(A_𝐢)`. No
Oseledets theorem is used.

* `shiftEquiv`, `ergodic_shift_neg_one`, `measurePreserving_shift_neg_natCast`,
  `integral_comp_shift_neg`: the inverse shift `σ⁻¹` preserves an invariant measure and is
  ergodic for an ergodic measure.
* `System.log_abs_gDeriv_pastWord`, `System.hasBackRate_iff_birkhoffAverage`: the backward rate
  as a Birkhoff average under `σ⁻¹`.
* `System.lyapunov_exponent_gsystem`: `eq:lyapunov_exponent_gsystem`.
* `shift_one_tau`, `shift_one_omega`, `measurePreserving_shift_avgMeasure_coding`: the lift
  `(τ_*μ + ω_*μ) / 2` of an invariant measure is invariant, from
  `thm:tau_omega_sigma_commutative`.
* `System.norm_matWord_pastWord`, `System.abs_det_div_norm_matWord_pastWord`: the singular values
  of `A_{i_{-n}} ⋯ A_{i_{-1}}` through `thm:matrix_products_g_derivatives`.
* `tendsto_integral_futureWord_div_of_ae_pastWord`: an almost sure backward limit of a function
  of words is the limit of the forward averages of its integrals.
* `System.exists_backRate`, `System.max_min_backRate_shift`: the two backward rates exist almost
  everywhere, and the shift keeps or exchanges them.
* `System.measure_SigmaPrime_compl`: `μ(Σ') = 1`.
* `System.irreducible_of_proximal`: a proximal box-like tuple with rotations is irreducible.
* `System.HasGibbsBounds.measure_cylinder_pos`, `System.measure_cylinder_le_two_mul`: full
  support, and `μ([i]) ≤ 2 μ(Σ^τ)`, `μ([i]) ≤ 2 μ(Σ^ω)` for an anti-diagonal `A_i`.
* `System.sigma_tau_omega_positive`: `thm:sigma_tau_omega_positive_eq_measure`.
-/
public import BoxLike.Birkhoff
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.General
public import BoxLike.PartitionIdentities
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator

universe u

/-! ### The inverse shift -/

/-- The iterates of `σ⁻¹` are the maps `shift (-n)`. -/
theorem iterate_shift_neg_one {α : Type*} (n : ℕ) :
    (shift (-1) : (ℤ → α) → ℤ → α)^[n] = shift (-(n : ℤ)) := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    funext x
    rw [Function.iterate_succ_apply', ih, shift_shift]
    congr 1
    push_cast
    ring

section InverseShift

variable {α : Type*} [MeasurableSpace α]

/-- The left shift `σ` of `sec:two_sided_shift_space` as a measurable equivalence; its inverse is
`σ⁻¹ = shift (-1)`. -/
def shiftEquiv : (ℤ → α) ≃ᵐ (ℤ → α) where
  toFun := shift 1
  invFun := shift (-1)
  left_inv x := by rw [shift_shift]; simp
  right_inv x := by rw [shift_shift]; simp
  measurable_toFun := measurable_shift 1
  measurable_invFun := measurable_shift (-1)

/-- The inverse shift `σ⁻¹` is ergodic for an ergodic measure, as used for
`eq:lyapunov_exponent_gsystem`. -/
theorem ergodic_shift_neg_one {μ : Measure (ℤ → α)} (h : Ergodic (shift 1) μ) :
    Ergodic (shift (-1)) μ :=
  Ergodic.symm (e := shiftEquiv) h

/-- The inverse shift `σ⁻¹` preserves every `σ`-invariant measure. -/
theorem measurePreserving_shift_neg_one {μ : Measure (ℤ → α)}
    (h : MeasurePreserving (shift 1) μ μ) : MeasurePreserving (shift (-1)) μ μ :=
  MeasurePreserving.symm shiftEquiv h

/-- An invariant measure is invariant under every `σ^{-n}`, `n ∈ ℕ`. -/
theorem measurePreserving_shift_neg_natCast {μ : Measure (ℤ → α)}
    (h : MeasurePreserving (shift 1) μ μ) (n : ℕ) :
    MeasurePreserving (shift (-(n : ℤ))) μ μ := by
  rw [← iterate_shift_neg_one]
  exact (measurePreserving_shift_neg_one h).iterate n

/-- The integral of an invariant measure does not change under `σ^{-n}`, `n ∈ ℕ`. -/
theorem integral_comp_shift_neg {μ : Measure (ℤ → α)} (hμ : MeasurePreserving (shift 1) μ μ)
    (n : ℕ) {F : (ℤ → α) → ℝ} (hF : Measurable F) :
    ∫ x, F (shift (-(n : ℤ)) x) ∂μ = ∫ x, F x ∂μ := by
  have h := measurePreserving_shift_neg_natCast hμ n
  rw [← integral_map h.measurable.aemeasurable hF.aestronglyMeasurable, h.map_eq]

end InverseShift

namespace System

/-! ### The backward rate as a Birkhoff average -/

section BackRate

variable {ι : Type u} (S : System ι)

/-- `log |g'_{j_{-n} ⋯ j_{-1}}| = ∑_{k<n} log |g'_{j_{-k-1}}|` is the Birkhoff sum of
`𝐣 ↦ log |g'_{j_{-1}}|` under the inverse shift, as in `eq:lyapunov_exponent_gsystem`. -/
theorem log_abs_gDeriv_pastWord (y : ℤ → ι × ZMod 2) (n : ℕ) :
    Real.log |S.gDeriv (pastWord y n)| =
      birkhoffSum (shift (-1)) (fun z : ℤ → ι × ZMod 2 => Real.log |S.ratio (z (-1))|) n y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [birkhoffSum_succ_apply, ← ih, pastWord_succ, gDeriv_cons, abs_mul,
      Real.log_mul (abs_ne_zero.2 (S.ratio_ne_zero _)) (abs_ne_zero.2 (S.gDeriv_ne_zero _)),
      iterate_shift_neg_one, shift_apply, add_comm]
    congr 5
    ring

/-- The backward growth rate of `eq:lyapunov_exponent_gsystem` exists and equals `l` exactly when
the Birkhoff averages of `𝐣 ↦ log |g'_{j_{-1}}|` under the inverse shift converge to `l`. -/
theorem hasBackRate_iff_birkhoffAverage (y : ℤ → ι × ZMod 2) (l : ℝ) :
    S.HasBackRate y l ↔ Tendsto (fun n : ℕ => birkhoffAverage ℝ (shift (-1))
      (fun z : ℤ → ι × ZMod 2 => Real.log |S.ratio (z (-1))|) n y) atTop (𝓝 l) := by
  unfold HasBackRate
  refine tendsto_congr fun n => ?_
  rw [birkhoffAverage, ← log_abs_gDeriv_pastWord, smul_eq_mul, div_eq_inv_mul]

end BackRate

section Gsystem

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι)

/-- The function `𝐣 ↦ log |g'_{j_{-1}}|` is integrable for every finite measure. -/
theorem integrable_log_abs_ratio_neg_one (ν : Measure (ℤ → ι × ZMod 2)) [IsFiniteMeasure ν] :
    Integrable (fun z : ℤ → ι × ZMod 2 => Real.log |S.ratio (z (-1))|) ν :=
  (Integrable.of_finite (f := fun p : ι × ZMod 2 => Real.log |S.ratio p|)).comp_measurable
    (measurable_pi_apply (-1))

/-- `eq:lyapunov_exponent_gsystem`: for an ergodic invariant `ν` on `Σ_Z`,
`\overline{λ}(𝖠, ν) = lim_n n⁻¹ log |g'_{i_{-n} ⋯ i_{-1}}(0)|` for `ν`-almost every `𝐢`. Here
`\overline{λ}(𝖠, ν)` is `S.lyapBar ν = ∫ log |g'_{j_0}| dν`, which is the limit of
`sec:lyapunov_exponents` by `System.lyapBarLim_eq`.
Depends on: `birkhoff_ergodic` for `σ⁻¹`. -/
theorem lyapunov_exponent_gsystem (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν]
    (herg : Ergodic (shift 1) ν) : ∀ᵐ y ∂ν, S.HasBackRate y (S.lyapBar ν) := by
  have hval : ∫ z, Real.log |S.ratio (z (-1))| ∂ν = S.lyapBar ν := by
    have h := integral_comp_shift_neg herg.toMeasurePreserving 1
      (F := fun y : ℤ → ι × ZMod 2 => Real.log |S.ratio (y 0)|)
      ((Measurable.of_discrete (f := fun p : ι × ZMod 2 => Real.log |S.ratio p|)).comp
        (measurable_pi_apply 0))
    simpa [lyapBar] using h
  filter_upwards [birkhoff_ergodic (ergodic_shift_neg_one herg)
    (S.integrable_log_abs_ratio_neg_one ν)] with y hy
  rw [hasBackRate_iff_birkhoffAverage, ← hval]
  exact hy

end Gsystem

end System

/-! ### The invariant lift of a measure on `Σ` to `Σ_Z` -/

section Lift

variable {ι : Type u}

/-- `thm:tau_omega_sigma_commutative` for `n = 1` and `τ`: `σ(τ(𝐢)) = τ(σ(𝐢))` when `A_{i_0}` is
diagonal and `σ(τ(𝐢)) = ω(σ(𝐢))` when it is anti-diagonal. -/
theorem shift_one_tau (o : ι → ZMod 2) (x : ℤ → ι) :
    shift 1 (tau o x) = if o (x 0) = 0 then tau o (shift 1 x) else omega o (shift 1 x) := by
  have he : eps o x 1 = o (x 0) := by
    have h := eps_add_one o x 0
    rwa [zero_add, eps_zero, zero_add] at h
  rcases zmod_two_cases (o (x 0)) with h | h
  · rw [ite_eq_left h, tau_shift_of_eps_eq_zero (he.trans h)]
  · rw [ite_eq_right (by rw [h]; decide), omega_shift_of_eps_eq_one (he.trans h)]

/-- `thm:tau_omega_sigma_commutative` for `n = 1` and `ω`: `σ(ω(𝐢)) = ω(σ(𝐢))` when `A_{i_0}` is
diagonal and `σ(ω(𝐢)) = τ(σ(𝐢))` when it is anti-diagonal. -/
theorem shift_one_omega (o : ι → ZMod 2) (x : ℤ → ι) :
    shift 1 (omega o x) = if o (x 0) = 0 then omega o (shift 1 x) else tau o (shift 1 x) := by
  have he : eps o x 1 = o (x 0) := by
    have h := eps_add_one o x 0
    rwa [zero_add, eps_zero, zero_add] at h
  rcases zmod_two_cases (o (x 0)) with h | h
  · rw [ite_eq_left h, omega_shift_of_eps_eq_zero (he.trans h)]
  · rw [ite_eq_right (by rw [h]; decide), tau_shift_of_eps_eq_one (he.trans h)]

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The lift `(τ_*μ + ω_*μ) / 2` of an invariant measure `μ` on `Σ` is an invariant measure on
`Σ_Z`: by `thm:tau_omega_sigma_commutative` the shift maps the two sheets `τ(Σ)`, `ω(Σ)` to
themselves over a diagonal first symbol and exchanges them over an anti-diagonal one. -/
theorem measurePreserving_shift_avgMeasure_coding (o : ι → ZMod 2) {μ : Measure (ℤ → ι)}
    (hinv : MeasurePreserving (shift 1) μ μ) :
    MeasurePreserving (shift 1) (avgMeasure (μ.map (tau o)) (μ.map (omega o)))
      (avgMeasure (μ.map (tau o)) (μ.map (omega o))) := by
  refine ⟨measurable_shift 1, ?_⟩
  have hτ := measurable_tau o
  have hω := measurable_omega o
  have hσ : Measurable (shift 1 : (ℤ → ι × ZMod 2) → ℤ → ι × ZMod 2) := measurable_shift 1
  have hA : MeasurableSet {x : ℤ → ι | o (x 0) = 0} :=
    ((Measurable.of_discrete (f := o)).comp (measurable_pi_apply 0))
      (measurableSet_singleton (0 : ZMod 2))
  have key : (μ.map (tau o)).map (shift 1) + (μ.map (omega o)).map (shift 1) =
      μ.map (tau o) + μ.map (omega o) := by
    ext B hB
    have hP : MeasurableSet (tau o ⁻¹' B) := hτ hB
    have hQ : MeasurableSet (omega o ⁻¹' B) := hω hB
    have e1 : tau o ⁻¹' (shift 1 ⁻¹' B) ∩ {x | o (x 0) = 0} =
        shift 1 ⁻¹' (tau o ⁻¹' B) ∩ {x | o (x 0) = 0} := by
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
      refine and_congr_left fun h => ?_
      rw [shift_one_tau, ite_eq_left h]
    have e2 : tau o ⁻¹' (shift 1 ⁻¹' B) \ {x | o (x 0) = 0} =
        shift 1 ⁻¹' (omega o ⁻¹' B) \ {x | o (x 0) = 0} := by
      ext x
      simp only [Set.mem_sdiff, mem_preimage, mem_ofPred_eq]
      refine and_congr_left fun h => ?_
      rw [shift_one_tau, ite_eq_right h]
    have e3 : omega o ⁻¹' (shift 1 ⁻¹' B) ∩ {x | o (x 0) = 0} =
        shift 1 ⁻¹' (omega o ⁻¹' B) ∩ {x | o (x 0) = 0} := by
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
      refine and_congr_left fun h => ?_
      rw [shift_one_omega, ite_eq_left h]
    have e4 : omega o ⁻¹' (shift 1 ⁻¹' B) \ {x | o (x 0) = 0} =
        shift 1 ⁻¹' (tau o ⁻¹' B) \ {x | o (x 0) = 0} := by
      ext x
      simp only [Set.mem_sdiff, mem_preimage, mem_ofPred_eq]
      refine and_congr_left fun h => ?_
      rw [shift_one_omega, ite_eq_right h]
    rw [Measure.add_apply, Measure.add_apply, Measure.map_apply hσ hB, Measure.map_apply hσ hB,
      Measure.map_apply hτ (hσ hB), Measure.map_apply hω (hσ hB), Measure.map_apply hτ hB,
      Measure.map_apply hω hB, ← hinv.measure_preimage hP.nullMeasurableSet,
      ← hinv.measure_preimage hQ.nullMeasurableSet,
      ← measure_inter_add_sdiff (tau o ⁻¹' (shift 1 ⁻¹' B)) hA,
      ← measure_inter_add_sdiff (omega o ⁻¹' (shift 1 ⁻¹' B)) hA,
      ← measure_inter_add_sdiff (shift 1 ⁻¹' (tau o ⁻¹' B)) hA,
      ← measure_inter_add_sdiff (shift 1 ⁻¹' (omega o ⁻¹' B)) hA, e1, e2, e3, e4]
    abel
  rw [avgMeasure, Measure.map_smul _ hσ.aemeasurable, Measure.map_add _ _ hσ, key]

/-- A property that holds almost everywhere for the average `(μ_1 + μ_2) / 2` of
`eq:average_gibbs` holds almost everywhere for `μ_1` and for `μ_2`. -/
theorem ae_of_ae_avgMeasure {Ω : Type*} [MeasurableSpace Ω] {m₁ m₂ : Measure Ω} {p : Ω → Prop}
    (h : ∀ᵐ y ∂avgMeasure m₁ m₂, p y) : (∀ᵐ y ∂m₁, p y) ∧ ∀ᵐ y ∂m₂, p y := by
  rw [ae_iff] at h ⊢
  rw [ae_iff]
  simpa [avgMeasure, ENNReal.smul_def] using h

end Lift

/-! ### Backward limits and forward averages -/

section Dominated

variable {α : Type*} [MeasurableSpace α] [Finite α] [MeasurableSingletonClass α]

/-- If a function `G` of words grows at most linearly and `n⁻¹ G(i_{-n} ⋯ i_{-1})` converges to
the constant `c` for `μ`-almost every `𝐢`, then the forward averages `n⁻¹ ∫ G(𝐢|_n) dμ(𝐢)` of an
invariant probability measure converge to `c`: the word `i_{-n} ⋯ i_{-1}` is the prefix of
`σ^{-n}(𝐢)`, and the convergence is dominated. -/
theorem tendsto_integral_futureWord_div_of_ae_pastWord {μ : Measure (ℤ → α)}
    [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ) {G : List α → ℝ} {C c : ℝ}
    (hG : ∀ w, |G w| ≤ C * w.length)
    (h : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => G (pastWord x n) / n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (∫ x, G (futureWord x n) ∂μ) / n) atTop (𝓝 c) := by
  have hmeas : ∀ n : ℕ, Measurable fun x : ℤ → α => G (pastWord x n) := fun n => by
    simp only [pastWord_eq_futureWord]
    exact (measurable_comp_futureWord G n).comp (measurable_shift _)
  have key : ∀ n : ℕ, (∫ x, G (futureWord x n) ∂μ) / n = ∫ x, G (pastWord x n) / n ∂μ :=
    fun n => by
      rw [integral_div, ← integral_comp_shift_neg hμ n (measurable_comp_futureWord G n)]
      simp only [pastWord_eq_futureWord]
  have hlim := tendsto_integral_of_dominated_convergence (fun _ => |C|)
    (F := fun (n : ℕ) (x : ℤ → α) => G (pastWord x n) / n) (f := fun _ => c)
    (fun n => ((hmeas n).div_const _).aestronglyMeasurable) (integrable_const _)
    (fun n => Eventually.of_forall fun x => ?_) h
  · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hlim
    exact hlim.congr fun n => (key n).symm
  · rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [div_le_iff₀ (Nat.cast_pos.2 hn)]
      calc |G (pastWord x n)| ≤ C * n := by simpa using hG (pastWord x n)
        _ ≤ |C| * n := mul_le_mul_of_nonneg_right (le_abs_self C) (Nat.cast_nonneg n)

end Dominated

/-- The logarithm commutes with the maximum of two positive numbers. -/
theorem log_max_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (max a b) = max (Real.log a) (Real.log b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (Real.log_le_log ha h)]
  · rw [max_eq_left h, max_eq_left (Real.log_le_log hb h)]

/-- The logarithm commutes with the minimum of two positive numbers. -/
theorem log_min_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (min a b) = min (Real.log a) (Real.log b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (Real.log_le_log ha h)]
  · rw [min_eq_right h, min_eq_right (Real.log_le_log hb h)]

namespace System

/-! ### The singular values along the past -/

section PastWord

variable {ι : Type u} (S : System ι)

/-- `α_1(A_{i_{-n}} ⋯ A_{i_{-1}})` is the larger of the moduli `|g'|` along `τ(𝐢)` and `ω(𝐢)`, by
`thm:matrix_products_g_derivatives`. -/
theorem norm_matWord_pastWord (x : ℤ → ι) (n : ℕ) :
    ‖S.matWord (pastWord x n)‖ =
      max |S.gDeriv (pastWord (tau S.o x) n)| |S.gDeriv (pastWord (omega S.o x) n)| := by
  rw [norm_matWord, ← S.codeWord_pastWord_tau, ← S.codeWord_pastWord_omega]
  rcases zmod_two_cases (eps S.o x (-(n : ℤ))) with h | h
  · rw [h, zero_add]
  · rw [h, show (1 : ZMod 2) + 1 = 0 by decide, max_comm]

/-- `α_2(A_{i_{-n}} ⋯ A_{i_{-1}})` is the smaller of the moduli `|g'|` along `τ(𝐢)` and `ω(𝐢)`,
by `thm:matrix_products_g_derivatives`. -/
theorem abs_det_div_norm_matWord_pastWord (x : ℤ → ι) (n : ℕ) :
    |(S.matWord (pastWord x n)).det| / ‖S.matWord (pastWord x n)‖ =
      min |S.gDeriv (pastWord (tau S.o x) n)| |S.gDeriv (pastWord (omega S.o x) n)| := by
  rw [abs_det_div_norm_matWord, ← S.codeWord_pastWord_tau, ← S.codeWord_pastWord_omega]
  rcases zmod_two_cases (eps S.o x (-(n : ℤ))) with h | h
  · rw [h, zero_add]
  · rw [h, show (1 : ZMod 2) + 1 = 0 by decide, min_comm]

/-- If the backward rates along `τ(𝐢)` and `ω(𝐢)` are `a` and `b`, then
`n⁻¹ log α_1(A_{i_{-n}} ⋯ A_{i_{-1}})` converges to `max{a, b}`. -/
theorem tendsto_log_norm_matWord_pastWord {x : ℤ → ι} {a b : ℝ}
    (ha : S.HasBackRate (tau S.o x) a) (hb : S.HasBackRate (omega S.o x) b) :
    Tendsto (fun n : ℕ => Real.log ‖S.matWord (pastWord x n)‖ / n) atTop (𝓝 (max a b)) := by
  refine (Filter.Tendsto.max ha hb).congr fun n => ?_
  rw [norm_matWord_pastWord, log_max_of_pos (abs_pos.2 (S.gDeriv_ne_zero _))
    (abs_pos.2 (S.gDeriv_ne_zero _)), max_div_div_right (Nat.cast_nonneg n)]

/-- If the backward rates along `τ(𝐢)` and `ω(𝐢)` are `a` and `b`, then
`n⁻¹ log α_2(A_{i_{-n}} ⋯ A_{i_{-1}})` converges to `min{a, b}`. -/
theorem tendsto_log_abs_det_div_norm_matWord_pastWord {x : ℤ → ι} {a b : ℝ}
    (ha : S.HasBackRate (tau S.o x) a) (hb : S.HasBackRate (omega S.o x) b) :
    Tendsto (fun n : ℕ => Real.log (|(S.matWord (pastWord x n)).det| /
      ‖S.matWord (pastWord x n)‖) / n) atTop (𝓝 (min a b)) := by
  refine (Filter.Tendsto.min ha hb).congr fun n => ?_
  rw [abs_det_div_norm_matWord_pastWord, log_min_of_pos (abs_pos.2 (S.gDeriv_ne_zero _))
    (abs_pos.2 (S.gDeriv_ne_zero _)), min_div_div_right (Nat.cast_nonneg n)]

/-- The shift keeps the two backward rates along `τ(𝐢)` and `ω(𝐢)` or exchanges them
(`sec:lyapunov_exponents`, tex lines 1521 to 1522), so their maximum and their minimum are
invariant. -/
theorem max_min_backRate_shift {x : ℤ → ι} {a b a' b' : ℝ}
    (ha : S.HasBackRate (tau S.o x) a) (hb : S.HasBackRate (omega S.o x) b)
    (ha' : S.HasBackRate (tau S.o (shift 1 x)) a')
    (hb' : S.HasBackRate (omega S.o (shift 1 x)) b') :
    max a' b' = max a b ∧ min a' b' = min a b := by
  rcases zmod_two_cases (S.o (x 0)) with h | h
  · have e1 : tau S.o (shift 1 x) = shift 1 (tau S.o x) := by rw [shift_one_tau, ite_eq_left h]
    have e2 : omega S.o (shift 1 x) = shift 1 (omega S.o x) := by
      rw [shift_one_omega, ite_eq_left h]
    rw [e1, hasBackRate_shift_one] at ha'
    rw [e2, hasBackRate_shift_one] at hb'
    rw [tendsto_nhds_unique ha' ha, tendsto_nhds_unique hb' hb]
    exact ⟨rfl, rfl⟩
  · have h' : ¬ S.o (x 0) = 0 := by rw [h]; decide
    have e1 : tau S.o (shift 1 x) = shift 1 (omega S.o x) := by
      rw [shift_one_omega, ite_eq_right h']
    have e2 : omega S.o (shift 1 x) = shift 1 (tau S.o x) := by rw [shift_one_tau, ite_eq_right h']
    rw [e1, hasBackRate_shift_one] at ha'
    rw [e2, hasBackRate_shift_one] at hb'
    rw [tendsto_nhds_unique ha' hb, tendsto_nhds_unique hb' ha]
    exact ⟨max_comm _ _, min_comm _ _⟩

/-- The functions `log α_1(A_𝐢)` and `log α_2(A_𝐢)` of the word `𝐢` grow at most linearly. -/
theorem exists_abs_log_singularValue_le [Finite ι] [Nonempty ι] :
    ∃ C : ℝ, (∀ w : List ι, |Real.log ‖S.matWord w‖| ≤ C * w.length) ∧
      ∀ w : List ι, |Real.log (|(S.matWord w).det| / ‖S.matWord w‖)| ≤ C * w.length := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  obtain ⟨δ, hδ⟩ := S.exists_ratioLowerBound
  have hlow : ∀ w : List ι, -((|Real.log δ| + |Real.log r|) * w.length) ≤
      Real.log δ * w.length := fun w => by
    have h := mul_le_mul_of_nonneg_right (neg_abs_le (Real.log δ)) (Nat.cast_nonneg w.length)
    have h' := mul_nonneg (abs_nonneg (Real.log r)) (Nat.cast_nonneg (α := ℝ) w.length)
    linarith
  have hupp : ∀ w : List ι, Real.log r * w.length ≤
      (|Real.log δ| + |Real.log r|) * w.length := fun w => by
    have h := mul_le_mul_of_nonneg_right (le_abs_self (Real.log r)) (Nat.cast_nonneg w.length)
    have h' := mul_nonneg (abs_nonneg (Real.log δ)) (Nat.cast_nonneg (α := ℝ) w.length)
    linarith
  refine ⟨|Real.log δ| + |Real.log r|, fun w => abs_le.2 ⟨?_, ?_⟩, fun w => abs_le.2 ⟨?_, ?_⟩⟩
  · exact (hlow w).trans (hδ.le_log_norm_matWord w)
  · exact (hS.log_norm_matWord_le w).trans (hupp w)
  · exact (hlow w).trans (hδ.le_log_abs_det_div_norm_matWord w)
  · exact ((S.log_abs_det_div_norm_matWord_le w).trans (hS.log_norm_matWord_le w)).trans (hupp w)

end PastWord

/-! ### `μ(Σ') = 1` -/

section SigmaPrime

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι)

/-- For an invariant probability measure `μ` on `Σ` the backward rates of
`eq:lyapunov_exponent_gsystem` along `τ(𝐢)` and `ω(𝐢)` exist for `μ`-almost every `𝐢`, and they
are the values at `τ(𝐢)` and `ω(𝐢)` of one Borel function on `Σ_Z`: Birkhoff's theorem for
`σ⁻¹` and the invariant lift `(τ_*μ + ω_*μ) / 2`. -/
theorem exists_backRate (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) :
    ∃ r : (ℤ → ι × ZMod 2) → ℝ, Measurable r ∧
      (∀ᵐ x ∂μ, S.HasBackRate (tau S.o x) (r (tau S.o x))) ∧
      ∀ᵐ x ∂μ, S.HasBackRate (omega S.o x) (r (omega S.o x)) := by
  obtain ⟨ν, hν⟩ : ∃ ν, ν = avgMeasure (μ.map (tau S.o)) (μ.map (omega S.o)) := ⟨_, rfl⟩
  have : IsProbabilityMeasure ν := hν ▸ isProbabilityMeasure_avgMeasure _ _
  have hνinv : MeasurePreserving (shift 1) ν ν :=
    hν ▸ measurePreserving_shift_avgMeasure_coding S.o hinv
  have hrate : ∀ᵐ y ∂ν, S.HasBackRate y ((ν[fun z : ℤ → ι × ZMod 2 =>
      Real.log |S.ratio (z (-1))| | MeasurableSpace.invariants (shift (-1))]) y) := by
    filter_upwards [birkhoff_ae (measurePreserving_shift_neg_one hνinv)
      (S.integrable_log_abs_ratio_neg_one ν)] with y hy
    exact (S.hasBackRate_iff_birkhoffAverage y _).2 hy
  rw [hν] at hrate
  obtain ⟨h1, h2⟩ := ae_of_ae_avgMeasure hrate
  exact ⟨_, (stronglyMeasurable_condExp.measurable).mono
    (MeasurableSpace.invariants_le (shift (-1))) le_rfl,
    ae_of_ae_map (measurable_tau S.o).aemeasurable h1,
    ae_of_ae_map (measurable_omega S.o).aemeasurable h2⟩

/-- `sec:lyapunov_exponents`, tex line 1522: `μ(Σ') = 1` for an ergodic `μ`. The article
obtains it from Oseledets' theorem. In the box-like case `birkhoff_ae` suffices: the two backward
rates are Birkhoff averages of `log |g'_{j_{-1}}|` under `σ⁻¹` along `τ(𝐢)` and `ω(𝐢)`, for the
invariant lift `(τ_*μ + ω_*μ) / 2`; their maximum and their minimum are `σ`-invariant, hence
constant, and equal `λ_1` and `λ_2` by dominated convergence.
Depends on: `thm:tau_omega_sigma_commutative`, `thm:matrix_products_g_derivatives`,
`birkhoff_ae`. -/
theorem measure_SigmaPrime_compl (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ) :
    μ (S.SigmaPrime μ)ᶜ = 0 := by
  have : Nonempty ι := nonempty_of_measure μ
  obtain ⟨r, hrm, hτ, hω⟩ := S.exists_backRate μ hinv
  -- Their maximum and their minimum are invariant, hence constant.
  have hshift : ∀ᵐ x ∂μ,
      max (r (tau S.o (shift 1 x))) (r (omega S.o (shift 1 x))) =
        max (r (tau S.o x)) (r (omega S.o x)) ∧
      min (r (tau S.o (shift 1 x))) (r (omega S.o (shift 1 x))) =
        min (r (tau S.o x)) (r (omega S.o x)) := by
    filter_upwards [hτ, hω, hinv.quasiMeasurePreserving.ae hτ,
      hinv.quasiMeasurePreserving.ae hω] with x ha hb ha' hb'
    exact S.max_min_backRate_shift ha hb ha' hb'
  have hrτ : Measurable fun x => r (tau S.o x) := hrm.comp (measurable_tau S.o)
  have hrω : Measurable fun x => r (omega S.o x) := hrm.comp (measurable_omega S.o)
  obtain ⟨cmax, hcmax⟩ := herg.ae_eq_const_of_ae_eq_comp₀
    (g := fun x => max (r (tau S.o x)) (r (omega S.o x))) (hrτ.max hrω).nullMeasurable
    (hshift.mono fun x hx => hx.1)
  obtain ⟨cmin, hcmin⟩ := herg.ae_eq_const_of_ae_eq_comp₀
    (g := fun x => min (r (tau S.o x)) (r (omega S.o x))) (hrτ.min hrω).nullMeasurable
    (hshift.mono fun x hx => hx.2)
  -- The constants are the Lyapunov exponents.
  obtain ⟨C, hC₁, hC₂⟩ := S.exists_abs_log_singularValue_le
  have hmax : cmax = S.lyapunov₁ μ := by
    refine tendsto_nhds_unique ?_ (S.tendsto_lyapunov₁ hinv)
    refine tendsto_integral_futureWord_div_of_ae_pastWord hinv hC₁ ?_
    filter_upwards [hτ, hω, hcmax] with x ha hb hc
    rw [← show max (r (tau S.o x)) (r (omega S.o x)) = cmax from hc]
    exact S.tendsto_log_norm_matWord_pastWord ha hb
  have hmin : cmin = S.lyapunov₂ μ := by
    refine tendsto_nhds_unique ?_ (S.tendsto_lyapunov₂ hinv)
    refine tendsto_integral_futureWord_div_of_ae_pastWord hinv hC₂ ?_
    filter_upwards [hτ, hω, hcmin] with x ha hb hc
    rw [← show min (r (tau S.o x)) (r (omega S.o x)) = cmin from hc]
    exact S.tendsto_log_abs_det_div_norm_matWord_pastWord ha hb
  -- Hence the two rates are the two exponents, in one of the two orders.
  change ∀ᵐ x ∂μ, x ∈ S.SigmaPrime μ
  filter_upwards [hτ, hω, hcmax, hcmin] with x ha hb hc hc'
  have e1 : max (r (tau S.o x)) (r (omega S.o x)) = S.lyapunov₁ μ := hc.trans hmax
  have e2 : min (r (tau S.o x)) (r (omega S.o x)) = S.lyapunov₂ μ := hc'.trans hmin
  rcases le_total (r (omega S.o x)) (r (tau S.o x)) with h | h
  · rw [max_eq_left h] at e1
    rw [min_eq_right h] at e2
    exact Or.inl ⟨e1 ▸ ha, e2 ▸ hb⟩
  · rw [max_eq_right h] at e1
    rw [min_eq_left h] at e2
    exact Or.inr ⟨e2 ▸ ha, e1 ▸ hb⟩

end SigmaPrime

/-! ### `μ(Σ^τ) > 0` and `μ(Σ^ω) > 0` -/

section Irreducible

variable {ι : Type u} (S : System ι)

/-- A proximal box-like tuple with rotations is irreducible: by `thm:box_like_proximal` the tuple
`𝖠` or `𝖠²` contains a proximal diagonal generator, and a common invariant line of `𝖠` is one of
`𝖠²`. This is the hypothesis of `thm:irred_eq_state`. -/
theorem irreducible_of_proximal (hrot : S.WithRotations) (hprox : S.Proximal) :
    S.Irreducible := by
  rcases hprox.hasProximalDiagonal_or_sq with h | h
  · exact irreducible_of_hasProximalDiagonal hrot h
  · rintro ⟨v, hv, hline⟩
    refine irreducible_of_hasProximalDiagonal (S.sq_withRotations hrot) h ⟨v, hv, fun p => ?_⟩
    obtain ⟨c₁, h₁⟩ := hline p.1
    obtain ⟨c₂, h₂⟩ := hline p.2
    exact ⟨c₂ * c₁, by rw [sq_mat, ← Matrix.mulVec_mulVec, h₂, Matrix.mulVec_smul, h₁, smul_smul]⟩

end Irreducible

section Positive

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {s : ℝ}

omit [MeasurableSingletonClass ι] in
/-- A measure with the Gibbs bounds of `thm:irred_eq_state` charges the cylinder `[i]` of every
symbol: it is fully supported. -/
theorem HasGibbsBounds.measure_cylinder_pos {S : System ι} {μ : Measure (ℤ → ι)}
    (h : S.HasGibbsBounds s μ) (i : ι) : 0 < μ (cylinder fun _ : Fin 1 => i) := by
  obtain ⟨C, hC, hb⟩ := h
  have hpos : 0 < μ.real (cylinder fun _ : Fin 1 => i) :=
    lt_of_lt_of_le (mul_pos (inv_pos.2 (lt_of_lt_of_le one_pos hC))
      (mul_pos (Real.exp_pos _) (S.svf_matWord_pos s _))) (hb 1 one_pos fun _ => i).1
  rw [measureReal_def] at hpos
  exact (ENNReal.toReal_pos_iff.1 hpos).1

/-- The integrated form of the counting inequality in the proof of
`thm:sigma_tau_omega_positive_eq_measure`: if `A_{i_0}` is anti-diagonal and `𝐢 ∈ Σ'`, then
`𝐢 ∈ Σ^τ` or `σ(𝐢) ∈ Σ^τ` by `eq:sigma_tau_omega_positive_eq_measure1`, and the same holds for
`Σ^ω`. Hence `μ([i]) ≤ 2 μ(Σ^τ)` and `μ([i]) ≤ 2 μ(Σ^ω)` for an invariant measure with
`μ(Σ') = 1` and an anti-diagonal generator `A_i`. -/
theorem measure_cylinder_le_two_mul (μ : Measure (ℤ → ι))
    (hinv : MeasurePreserving (shift 1) μ μ) (hfull : μ (S.SigmaPrime μ)ᶜ = 0) {i : ι}
    (hi : S.o i = 1) :
    μ (cylinder fun _ : Fin 1 => i) ≤ 2 * μ (S.SigmaTau μ) ∧
      μ (cylinder fun _ : Fin 1 => i) ≤ 2 * μ (S.SigmaOmega μ) := by
  have h0 : ∀ x ∈ cylinder fun _ : Fin 1 => i, S.o (x 0) = 1 := fun x hx => by
    have h := hx 0
    simp only [Fin.val_zero, Nat.cast_zero] at h
    rw [h, hi]
  have h01 : (1 : ZMod 2) ≠ 0 := by decide
  have hτ : (cylinder fun _ : Fin 1 => i) ∩ S.SigmaPrime μ ⊆
      S.SigmaTau μ ∪ shift 1 ⁻¹' S.SigmaTau μ := by
    rintro x ⟨hx, hx' | hx'⟩
    · exact Or.inl hx'
    · exact Or.inr ((S.shift_mem_SigmaTau_iff μ x).1.2 (Or.inr ⟨h0 x hx, hx'⟩))
  have hω : (cylinder fun _ : Fin 1 => i) ∩ S.SigmaPrime μ ⊆
      S.SigmaOmega μ ∪ shift 1 ⁻¹' S.SigmaOmega μ := by
    rintro x ⟨hx, hx' | hx'⟩
    · exact Or.inr ((S.shift_mem_SigmaTau_iff μ x).2.2 (Or.inr ⟨h0 x hx, hx'⟩))
    · exact Or.inl hx'
  have key : ∀ E : Set (ℤ → ι), MeasurableSet E →
      (cylinder fun _ : Fin 1 => i) ∩ S.SigmaPrime μ ⊆ E ∪ shift 1 ⁻¹' E →
      μ (cylinder fun _ : Fin 1 => i) ≤ 2 * μ E := fun E hE hsub =>
    calc μ (cylinder fun _ : Fin 1 => i)
        = μ ((cylinder fun _ : Fin 1 => i) ∩ S.SigmaPrime μ) := (measure_inter_conull hfull).symm
      _ ≤ μ (E ∪ shift 1 ⁻¹' E) := measure_mono hsub
      _ ≤ μ E + μ (shift 1 ⁻¹' E) := measure_union_le _ _
      _ = 2 * μ E := by rw [hinv.measure_preimage hE.nullMeasurableSet, two_mul]
  exact ⟨key _ (S.measurableSet_SigmaTau μ) hτ, key _ (S.measurableSet_SigmaOmega μ) hω⟩

/-- `thm:sigma_tau_omega_positive_eq_measure`: `μ(Σ^τ) > 0` and `μ(Σ^ω) > 0` for the
ergodic `s`-equilibrium state, `0 < s < 2`, of a box-like tuple with rotations; proximality is
not used. The ergodicity `herg` comes from `thm:irred_eq_state`. The counting inequality of the
article is integrated against the invariant measure, which gives `μ([i]) ≤ 2 μ(Σ^τ)` and
`μ([i]) ≤ 2 μ(Σ^ω)` for an anti-diagonal `A_i`; Birkhoff's theorem and `eq:simple_lyapunov` are
not used.
Depends on: `shift_mem_SigmaTau_iff`, `measure_SigmaPrime_compl`, `thm:irred_eq_state` (full
support, from the Gibbs bounds of `EquilibriumGibbsStatement`, which the library proves). -/
theorem sigma_tau_omega_positive (hfk : EquilibriumGibbsStatement.{u}) (hrot : S.WithRotations)
    (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (heq : S.IsEquilibriumState s μ) : 0 < μ (S.SigmaTau μ) ∧ 0 < μ (S.SigmaOmega μ) := by
  obtain ⟨i, hi⟩ := hrot.2
  have hpos := (hfk S hrot hs0 hs2 μ hinv heq).measure_cylinder_pos i
  obtain ⟨hτ, hω⟩ := S.measure_cylinder_le_two_mul μ hinv (S.measure_SigmaPrime_compl μ hinv herg)
    hi
  refine ⟨pos_of_ne_zero fun h => ?_, pos_of_ne_zero fun h => ?_⟩
  · rw [h, mul_zero] at hτ
    exact hpos.not_ge hτ
  · rw [h, mul_zero] at hω
    exact hpos.not_ge hω

end Positive

end System

end BoxLike
