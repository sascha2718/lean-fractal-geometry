module

/-
Invariant measures of the iterated function system `Φ`, for the case `s ≥ 2` of
`thm:main_extended` in `sec:dimension_result_proof` (tex lines 3404 to 3407): Hutchinson's
uniqueness of the invariant probability measure, and the invariance of the projection `π_*μ` of
a Bernoulli measure `μ` in the sense of `sec:normalisation` (tex lines 2236 to 2241 and 2376 to
2382).

The plane `ℝ × ℝ` carries the sup metric and the Borel `σ`-algebra, the alphabet `ι` carries a
measurable structure with measurable singletons, and the sequence spaces `ℤ → ι` and `ℕ → ι`
carry the product `σ`-algebra.

* `System.testOp`, `System.IsInvariantMeasure.integral_iterate_testOp`: the operator
  `T f = ∑_i p_i f ∘ φ_i` on bounded continuous functions, and `∫ f dν = ∫ T^n f dν` for an
  invariant measure `ν`.
* `System.Bounds.abs_sub_iterate_testOp_le`: on a set `K` with `φ_i(K) ⊆ K` the oscillation of
  `T^n f` at scale `t` is that of `f` at scale `r^n t`.
* `System.Bounds.mapsTo_closedBall`, `exists_measure_compl_closedBall_lt`: large closed balls
  are mapped into themselves by every `φ_i`, and carry almost all the mass of a finite measure.
* `System.IsInvariantMeasure.sum_eq_one`: the weights of an invariant probability measure sum
  to one.
* `System.IsInvariantMeasure.unique`: Hutchinson's theorem, uniqueness part.
* `futureSeq`, `extendFuture`, `futureCylinder`, `isPiSystem_futureCylinders`,
  `generateFrom_futureCylinders`: the future `𝐢^+` of a sequence, and the one-sided cylinders
  as a `π`-system generating the product `σ`-algebra of `ℕ → α`.
* `measure_cylinder_inter_shift_preimage`: under a Bernoulli measure the symbol `i_0` is
  independent of the future of `σ 𝐢`.
* `System.isInvariantMeasure_map_proj`: the projection of a Bernoulli measure is invariant.
* `System.map_proj_eq_of_isInvariantMeasure`: the projection of a Bernoulli measure is the only
  invariant probability measure with the weights of its symbols.
-/
public import BoxLike.Attractor
public import BoxLike.Entropy
public import BoxLike.Measurable
public import BoxLike.SelfAffineMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Metric
open scoped ENNReal BoundedContinuousFunction

/-! ### Probability weights and tails of finite measures -/

/-- Weights `p_i ∈ [0, ∞]` with `∑_i p_i = 1` are finite. -/
theorem weight_ne_top {ι : Type*} [Fintype ι] {p : ι → ℝ≥0∞} (hp : ∑ i, p i = 1) (i : ι) :
    p i ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (hp ▸ Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i))

/-- Weights `p_i ∈ [0, ∞]` with `∑_i p_i = 1` form a real probability vector. -/
theorem sum_toReal_weight {ι : Type*} [Fintype ι] {p : ι → ℝ≥0∞} (hp : ∑ i, p i = 1) :
    ∑ i, (p i).toReal = 1 := by
  rw [← ENNReal.toReal_sum fun i _ => weight_ne_top hp i, hp, ENNReal.toReal_one]

/-- A finite Borel measure on a metric space gives mass less than `η` to the complement of a
closed ball of radius at least `R₀`, for every `η > 0`. -/
theorem exists_measure_compl_closedBall_lt {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] (x : X) {η : ℝ≥0∞} (hη : 0 < η)
    (R₀ : ℝ) : ∃ R, R₀ ≤ R ∧ ν (closedBall x R)ᶜ < η := by
  have hanti : Antitone fun n : ℕ => (closedBall x (n : ℝ))ᶜ := fun m n hmn =>
    Set.compl_subset_compl.2 (closedBall_subset_closedBall (Nat.cast_le.2 hmn))
  have hempty : ⋂ n : ℕ, (closedBall x (n : ℝ))ᶜ = ∅ := by
    ext z
    simp only [Set.mem_iInter, Set.mem_compl_iff, mem_closedBall, not_le, Set.mem_empty_iff_false,
      iff_false, not_forall, not_lt]
    exact exists_nat_ge _
  have h := tendsto_measure_iInter_atTop (μ := ν)
    (fun n => (measurableSet_closedBall.compl).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hempty, measure_empty] at h
  obtain ⟨n, hn, hn'⟩ := ((h.eventually (gt_mem_nhds hη)).and
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop R₀)).exists
  exact ⟨n, hn', hn⟩

namespace System

/-! ### The operator on test functions -/

section Unique

variable {ι : Type*} [Fintype ι] (S : System ι)

/-- The operator `T f = ∑_i p_i f ∘ φ_i` on bounded continuous test functions. It is the adjoint
of `ν ↦ ∑_i p_i (φ_i)_*ν`, the operator of the invariance equation in the proof of
`thm:main_extended` (tex lines 3399 to 3403). -/
noncomputable def testOp (p : ι → ℝ≥0∞) (f : (ℝ × ℝ) →ᵇ ℝ) : (ℝ × ℝ) →ᵇ ℝ :=
  ∑ i, (p i).toReal • f.compContinuous ⟨S.phi i, S.continuous_phi i⟩

/-- The value of `T f` at a point: `T f(z) = ∑_i p_i f(φ_i(z))`. -/
theorem testOp_apply (p : ι → ℝ≥0∞) (f : (ℝ × ℝ) →ᵇ ℝ) (z : ℝ × ℝ) :
    S.testOp p f z = ∑ i, (p i).toReal * f (S.phi i z) := by
  simp [testOp]

/-- For probability weights the operator `T` does not increase the sup norm. -/
theorem norm_testOp_le {p : ι → ℝ≥0∞} (hp : ∑ i, p i = 1) (f : (ℝ × ℝ) →ᵇ ℝ) :
    ‖S.testOp p f‖ ≤ ‖f‖ := by
  calc ‖S.testOp p f‖
      ≤ ∑ i, ‖(p i).toReal • f.compContinuous ⟨S.phi i, S.continuous_phi i⟩‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i, (p i).toReal * ‖f‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        exact mul_le_mul_of_nonneg_left (f.norm_compContinuous_le _) ENNReal.toReal_nonneg
    _ = ‖f‖ := by rw [← Finset.sum_mul, sum_toReal_weight hp, one_mul]

/-- For probability weights the iterates `T^n` do not increase the sup norm. -/
theorem norm_iterate_testOp_le {p : ι → ℝ≥0∞} (hp : ∑ i, p i = 1) (f : (ℝ × ℝ) →ᵇ ℝ)
    (n : ℕ) : ‖(S.testOp p)^[n] f‖ ≤ ‖f‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (S.norm_testOp_le hp _).trans ih

variable {S}

/-- The weights of an invariant probability measure sum to one: evaluate the invariance equation
of the proof of `thm:main_extended` (tex lines 3399 to 3403) on the whole plane. -/
theorem IsInvariantMeasure.sum_eq_one {p : ι → ℝ≥0∞} {ν : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure ν] (h : S.IsInvariantMeasure p ν) : ∑ i, p i = 1 := by
  have hmi : ∀ i, Measurable (S.phi i) := fun i => (S.continuous_phi i).measurable
  have h1 := congrArg (fun m : Measure (ℝ × ℝ) => m Set.univ) h
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (hmi _) MeasurableSet.univ, Set.preimage_univ, measure_univ, mul_one] at h1
  exact h1.symm

/-- The invariance equation integrated against a bounded continuous function:
`∫ f dν = ∫ T f dν`. -/
theorem IsInvariantMeasure.integral_testOp {p : ι → ℝ≥0∞} (hp : ∑ i, p i = 1)
    {ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure ν] (h : S.IsInvariantMeasure p ν)
    (f : (ℝ × ℝ) →ᵇ ℝ) : ∫ z, f z ∂ν = ∫ z, S.testOp p f z ∂ν := by
  have hmi : ∀ i, Measurable (S.phi i) := fun i => (S.continuous_phi i).measurable
  have hint : ∀ i ∈ (Finset.univ : Finset ι),
      Integrable (fun z => f z) (p i • ν.map (S.phi i)) := fun i _ =>
    (f.integrable _).smul_measure (weight_ne_top hp i)
  have hgi : ∀ i ∈ (Finset.univ : Finset ι),
      Integrable (fun z => (p i).toReal * f (S.phi i z)) ν := fun i _ =>
    ((f.compContinuous ⟨S.phi i, S.continuous_phi i⟩).integrable ν).const_mul _
  have hterm : ∀ i : ι, ∫ z, f z ∂(p i • ν.map (S.phi i))
      = ∫ z, (p i).toReal * f (S.phi i z) ∂ν := fun i => by
    rw [integral_smul_measure, smul_eq_mul,
      integral_map (hmi i).aemeasurable f.continuous.aestronglyMeasurable, ← integral_const_mul]
  unfold IsInvariantMeasure at h
  conv_lhs => rw [h]
  rw [integral_finsetSum_measure hint]
  simp only [hterm]
  rw [← integral_finsetSum _ hgi]
  exact integral_congr_ae (Eventually.of_forall fun z => (S.testOp_apply p f z).symm)

/-- The invariance equation iterated `n` times: `∫ f dν = ∫ T^n f dν`. -/
theorem IsInvariantMeasure.integral_iterate_testOp {p : ι → ℝ≥0∞} (hp : ∑ i, p i = 1)
    {ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure ν] (h : S.IsInvariantMeasure p ν)
    (f : (ℝ × ℝ) →ᵇ ℝ) (n : ℕ) : ∫ z, f z ∂ν = ∫ z, (S.testOp p)^[n] f z ∂ν := by
  induction n with
  | zero => simp
  | succ n ih => rw [ih, Function.iterate_succ_apply', h.integral_testOp hp]

/-- On a set `K` with `φ_i(K) ⊆ K` for all `i`, the oscillation of `T^n f` at scale `t` is at
most the oscillation of `f` at scale `r^n t`, where `r` is the common contraction ratio. -/
theorem Bounds.abs_sub_iterate_testOp_le {r M : ℝ} (hS : S.Bounds r M) {p : ι → ℝ≥0∞}
    (hp : ∑ i, p i = 1) (f : (ℝ × ℝ) →ᵇ ℝ) {K : Set (ℝ × ℝ)}
    (hK : ∀ i, Set.MapsTo (S.phi i) K K) {ε δ : ℝ}
    (hf : ∀ a ∈ K, ∀ b ∈ K, dist a b ≤ δ → |f a - f b| ≤ ε) (n : ℕ) :
    ∀ x ∈ K, ∀ y ∈ K, dist x y * r ^ n ≤ δ →
      |(S.testOp p)^[n] f x - (S.testOp p)^[n] f y| ≤ ε := by
  induction n with
  | zero =>
    intro x hx y hy hxy
    simpa using hf x hx y hy (by simpa using hxy)
  | succ n ih =>
    intro x hx y hy hxy
    have hkey : ∀ i,
        |(S.testOp p)^[n] f (S.phi i x) - (S.testOp p)^[n] f (S.phi i y)| ≤ ε := by
      intro i
      refine ih _ (hK i hx) _ (hK i hy) ?_
      calc dist (S.phi i x) (S.phi i y) * r ^ n ≤ r * dist x y * r ^ n :=
            mul_le_mul_of_nonneg_right (hS.dist_phi_le i x y) (pow_nonneg hS.r_nonneg n)
        _ = dist x y * r ^ (n + 1) := by ring
        _ ≤ δ := hxy
    rw [Function.iterate_succ_apply', testOp_apply, testOp_apply, ← Finset.sum_sub_distrib]
    calc |∑ i, ((p i).toReal * (S.testOp p)^[n] f (S.phi i x)
            - (p i).toReal * (S.testOp p)^[n] f (S.phi i y))|
        ≤ ∑ i, |(p i).toReal * (S.testOp p)^[n] f (S.phi i x)
            - (p i).toReal * (S.testOp p)^[n] f (S.phi i y)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (p i).toReal * ε := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← mul_sub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
          exact mul_le_mul_of_nonneg_left (hkey i) ENNReal.toReal_nonneg
      _ = ε := by rw [← Finset.sum_mul, sum_toReal_weight hp, one_mul]

omit [Fintype ι] in
/-- Every `φ_i` maps the closed ball of radius `R` about the origin into itself as soon as
`r R + M ≤ R`; this is the large ball of the proof of `thm:main_extended` (tex lines 3385 to
3558). -/
theorem Bounds.mapsTo_closedBall {r M : ℝ} (hS : S.Bounds r M) {R : ℝ} (hR : r * R + M ≤ R)
    (i : ι) : Set.MapsTo (S.phi i) (closedBall 0 R) (closedBall 0 R) := by
  intro z hz
  rw [mem_closedBall] at hz ⊢
  have h0 : dist (S.phi i 0) 0 ≤ M := by
    rw [Prod.dist_eq]
    refine max_le ?_ ?_
    · simpa [phi, coord, trans, Real.dist_eq] using hS.abs_trans_le (i, 0)
    · simpa [phi, coord, trans, Real.dist_eq] using hS.abs_trans_le (i, 1)
  calc dist (S.phi i z) 0 ≤ dist (S.phi i z) (S.phi i 0) + dist (S.phi i 0) 0 :=
        dist_triangle _ _ _
    _ ≤ r * dist z 0 + M := add_le_add (hS.dist_phi_le i z 0) h0
    _ ≤ r * R + M := by gcongr; exact hS.r_nonneg
    _ ≤ R := hR

/-! ### Hutchinson's uniqueness -/

/-- Hutchinson's theorem, uniqueness part: two invariant probability measures with the same
probability weights coincide. This is the uniqueness cited in the proof of `thm:main_extended`
(tex lines 3406 to 3407). No assumption on the supports is made: for a bounded continuous `f`
the function `T^n f` is within `ε` of a constant on a large closed ball `K` with `φ_i(K) ⊆ K`,
and the complement of `K` carries little mass. -/
theorem IsInvariantMeasure.unique {p : ι → ℝ≥0∞} (hp : ∑ i, p i = 1) {ν ν' : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'] (h : S.IsInvariantMeasure p ν)
    (h' : S.IsInvariantMeasure p ν') : ν = ν' := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have habs : ∀ ε > 0, |∫ z, f z ∂ν - ∫ z, f z ∂ν'| ≤ 4 * ε := by
    intro ε hε
    have hC : 0 < 2 * ‖f‖ + 1 := by positivity
    set η : ℝ := ε / (2 * ‖f‖ + 1) with hη_def
    have hη : 0 < η := div_pos hε hC
    have hCη : 2 * ‖f‖ * η ≤ ε := by
      rw [hη_def, ← mul_div_assoc, div_le_iff₀ hC]
      nlinarith [norm_nonneg f]
    obtain ⟨R, hR₀, hR⟩ := exists_measure_compl_closedBall_lt (ν + ν') (0 : ℝ × ℝ)
      (ENNReal.ofReal_pos.2 hη) (max (M / (1 - r)) 1)
    have hRpos : 0 < R := zero_lt_one.trans_le ((le_max_right _ _).trans hR₀)
    have hRM : r * R + M ≤ R := by
      have := (div_le_iff₀ (sub_pos.2 hS.r_lt_one)).1 ((le_max_left _ _).trans hR₀)
      linarith
    set K : Set (ℝ × ℝ) := closedBall 0 R with hK_def
    have hKmeas : MeasurableSet K := measurableSet_closedBall
    have hKinv : ∀ i, Set.MapsTo (S.phi i) K K := fun i => hS.mapsTo_closedBall hRM i
    obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff_le.1
      ((isCompact_closedBall (0 : ℝ × ℝ) R).uniformContinuousOn_of_continuous
        f.continuous.continuousOn) ε hε
    have hf : ∀ a ∈ K, ∀ b ∈ K, dist a b ≤ δ → |f a - f b| ≤ ε := fun a ha b hb hab => by
      have := hδ a ha b hb hab
      rwa [Real.dist_eq] at this
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hδ0 hRpos) hS.r_lt_one
    set g : (ℝ × ℝ) →ᵇ ℝ := (S.testOp p)^[n] f with hg
    have hgK : ∀ z ∈ K, |g z - g 0| ≤ ε := fun z hz => by
      refine hS.abs_sub_iterate_testOp_le hp f hKinv hf n z hz 0
        (mem_closedBall_self hRpos.le) ?_
      have h1 : dist z 0 ≤ R := mem_closedBall.1 hz
      have h2 : R * r ^ n ≤ δ := by
        have := (lt_div_iff₀ hRpos).1 hn
        linarith
      exact (mul_le_mul_of_nonneg_right h1 (pow_nonneg hS.r_nonneg n)).trans h2
    have hgall : ∀ z, |g z - g 0| ≤ 2 * ‖f‖ := fun z => by
      have h1 := g.dist_le_two_norm z 0
      rw [Real.dist_eq] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left (S.norm_iterate_testOp_le hp f n) zero_le_two)
    have key : ∀ (m : Measure (ℝ × ℝ)) [IsProbabilityMeasure m], S.IsInvariantMeasure p m →
        m.real Kᶜ ≤ η → |∫ z, f z ∂m - g 0| ≤ 2 * ε := by
      intro m _ hm hmK
      rw [hm.integral_iterate_testOp hp f n, ← hg]
      have hgint : Integrable (fun z => g z) m := g.integrable m
      have h3 : ∫ z, (g z - g 0) ∂m = (∫ z, g z ∂m) - g 0 := by
        rw [integral_sub hgint (integrable_const _)]
        simp
      have hind : Integrable (fun z => 2 * ‖f‖ * Kᶜ.indicator (1 : ℝ × ℝ → ℝ) z) m :=
        ((integrable_const (1 : ℝ)).indicator hKmeas.compl).const_mul _
      have hbound : ∀ z, ‖g z - g 0‖ ≤ ε + 2 * ‖f‖ * Kᶜ.indicator (1 : ℝ × ℝ → ℝ) z := by
        intro z
        rw [Real.norm_eq_abs]
        by_cases hz : z ∈ K
        · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.2 hz), mul_zero, add_zero]
          exact hgK z hz
        · rw [Set.indicator_of_mem (Set.mem_compl hz), Pi.one_apply, mul_one]
          linarith [hgall z]
      calc |(∫ z, g z ∂m) - g 0| = ‖∫ z, (g z - g 0) ∂m‖ := by rw [h3, Real.norm_eq_abs]
        _ ≤ ∫ z, ‖g z - g 0‖ ∂m := norm_integral_le_integral_norm _
        _ ≤ ∫ z, (ε + 2 * ‖f‖ * Kᶜ.indicator (1 : ℝ × ℝ → ℝ) z) ∂m :=
            integral_mono (hgint.sub (integrable_const _)).norm
              ((integrable_const _).add hind) hbound
        _ = ε + 2 * ‖f‖ * m.real Kᶜ := by
            rw [integral_add (integrable_const _) hind, integral_const, integral_const_mul,
              integral_indicator_one hKmeas.compl]
            simp
        _ ≤ 2 * ε := by
            have := mul_le_mul_of_nonneg_left hmK (by positivity : 0 ≤ 2 * ‖f‖)
            linarith
    have hν : ν.real Kᶜ ≤ η := ENNReal.toReal_le_of_le_ofReal hη.le
      ((Measure.le_add_right le_rfl _).trans hR.le)
    have hν' : ν'.real Kᶜ ≤ η := ENNReal.toReal_le_of_le_ofReal hη.le
      ((Measure.le_add_left le_rfl _).trans hR.le)
    have h1 := abs_le.1 (key ν h hν)
    have h2 := abs_le.1 (key ν' h' hν')
    rw [abs_le]
    constructor <;> linarith
  have hle : |∫ z, f z ∂ν - ∫ z, f z ∂ν'| ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := habs (ε / 4) (by linarith)
    linarith
  exact sub_eq_zero.1 (abs_eq_zero.1 (le_antisymm hle (abs_nonneg _)))

end Unique

end System

/-! ### The future of a sequence and one-sided cylinders -/

section Future

variable {α : Type*}

/-- The future `𝐢^+ = (i_0, i_1, …)` of a two-sided sequence (`sec:two_sided_shift_space`), as a
sequence indexed by `ℕ`. -/
def futureSeq (x : ℤ → α) : ℕ → α := fun n => x n

/-- A two-sided sequence with the given future; its past is constant. -/
def extendFuture (y : ℕ → α) : ℤ → α := fun k => y k.toNat

/-- The sequence `extendFuture (futureSeq x)` has the future of `x`. -/
theorem extendFuture_futureSeq (x : ℤ → α) (k : ℕ) : extendFuture (futureSeq x) k = x k := by
  simp [extendFuture, futureSeq]

/-- The one-sided cylinder `{y : y_0 ⋯ y_{n-1} = w}` in `ℕ → α`. -/
def futureCylinder {n : ℕ} (w : Fin n → α) : Set (ℕ → α) := {y | ∀ k : Fin n, y k = w k}

/-- The cylinder `[w]` of `sec:two_sided_shift_space` is the set of sequences whose future lies
in the one-sided cylinder of `w`. -/
theorem preimage_futureCylinder {n : ℕ} (w : Fin n → α) :
    futureSeq ⁻¹' futureCylinder w = cylinder w := rfl

/-- The family of all one-sided cylinders. -/
def futureCylinders (α : Type*) : Set (Set (ℕ → α)) :=
  {s | ∃ (n : ℕ) (w : Fin n → α), s = futureCylinder w}

/-- Two one-sided cylinders that meet are nested, so the one-sided cylinders form a
`π`-system. -/
theorem isPiSystem_futureCylinders : IsPiSystem (futureCylinders α) := by
  rintro _ ⟨m, w, rfl⟩ _ ⟨n, w', rfl⟩ ⟨y, hy, hy'⟩
  rcases le_total m n with hmn | hmn
  · refine ⟨n, w', Set.inter_eq_right.2 fun z hz k => ?_⟩
    rw [← hy k]
    exact (hz ⟨k, k.2.trans_le hmn⟩).trans (hy' ⟨k, k.2.trans_le hmn⟩).symm
  · refine ⟨m, w, Set.inter_eq_left.2 fun z hz k => ?_⟩
    rw [← hy' k]
    exact (hz ⟨k, k.2.trans_le hmn⟩).trans (hy ⟨k, k.2.trans_le hmn⟩).symm

variable [MeasurableSpace α]

/-- The future `𝐢 ↦ 𝐢^+` is a measurable map. -/
theorem measurable_futureSeq : Measurable (futureSeq : (ℤ → α) → ℕ → α) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- The extension of a one-sided sequence to a two-sided one is a measurable map. -/
theorem measurable_extendFuture : Measurable (extendFuture : (ℕ → α) → ℤ → α) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

variable [MeasurableSingletonClass α]

/-- One-sided cylinders are measurable. -/
theorem measurableSet_futureCylinder {n : ℕ} (w : Fin n → α) :
    MeasurableSet (futureCylinder w) := by
  have : futureCylinder w = ⋂ k : Fin n, (fun y : ℕ → α => y k) ⁻¹' {w k} := by
    ext y
    simp [futureCylinder]
  rw [this]
  exact MeasurableSet.iInter fun k => measurable_pi_apply _ (measurableSet_singleton _)

/-- Over a countable alphabet the one-sided cylinders generate the product `σ`-algebra of
`ℕ → α`: the set `{y : y_k ∈ A}` is the countable union of the cylinders of the words
`w_0 ⋯ w_k` with `w_k ∈ A`. -/
theorem generateFrom_futureCylinders [Countable α] :
    (inferInstance : MeasurableSpace (ℕ → α)) =
      MeasurableSpace.generateFrom (futureCylinders α) := by
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
  · refine iSup_le fun k => ?_
    rintro _ ⟨A, -, rfl⟩
    have : (fun y : ℕ → α => y k) ⁻¹' A =
        ⋃ w : {w : Fin (k + 1) → α // w (Fin.last k) ∈ A}, futureCylinder w.1 := by
      ext y
      simp only [Set.mem_preimage, Set.mem_iUnion, futureCylinder, Set.mem_ofPred_eq]
      constructor
      · intro hy
        exact ⟨⟨fun j => y j, by simpa using hy⟩, fun _ => rfl⟩
      · rintro ⟨⟨w, hw⟩, hy⟩
        have := hy (Fin.last k)
        simp only [Fin.val_last] at this
        rwa [this]
    rw [this]
    exact MeasurableSet.iUnion fun w =>
      MeasurableSpace.measurableSet_generateFrom ⟨_, _, rfl⟩
  · rintro _ ⟨n, w, rfl⟩
    exact measurableSet_futureCylinder w

end Future

/-! ### Independence of the first symbol and the shifted future -/

section Bernoulli

variable {ι : Type*} [MeasurableSpace ι]

/-- For a Bernoulli measure in the sense of `sec:normalisation` (tex lines 2236 to 2241),
`μ[i w] = μ[i] μ[w]`. -/
theorem measureReal_cylinder_cons {μ : Measure (ℤ → ι)}
    (hprod : ∀ (n : ℕ) (w : Fin n → ι), μ.real (cylinder w) = ∏ k, μ.real (cylinder ![w k]))
    (i : ι) {n : ℕ} (w : Fin n → ι) :
    μ.real (cylinder (Fin.append ![i] w)) = μ.real (cylinder ![i]) * μ.real (cylinder w) := by
  rw [hprod (1 + n) (Fin.append ![i] w), Fin.prod_univ_add, hprod n w]
  simp

variable [Fintype ι] [MeasurableSingletonClass ι]

/-- Under a Bernoulli measure in the sense of `sec:normalisation` (tex lines 2236 to 2241) the
symbol `i_0` is independent of the future of `σ 𝐢`: `μ([i] ∩ σ^{-1} E) = μ[i] μ(E)` for every
set `E` determined by the future `𝐢^+`. Both sides are finite measures of `E` that agree on the
one-sided cylinders. -/
theorem measure_cylinder_inter_shift_preimage {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]
    (hprod : ∀ (n : ℕ) (w : Fin n → ι), μ.real (cylinder w) = ∏ k, μ.real (cylinder ![w k]))
    (i : ι) {D : Set (ℕ → ι)} (hD : MeasurableSet D) :
    μ (cylinder ![i] ∩ shift 1 ⁻¹' (futureSeq ⁻¹' D)) =
      μ (cylinder ![i]) * μ (futureSeq ⁻¹' D) := by
  have hm : Measurable fun x : ℤ → ι => futureSeq (shift 1 x) :=
    measurable_futureSeq.comp (measurable_shift 1)
  have key : (μ.restrict (cylinder ![i])).map (fun x => futureSeq (shift 1 x)) =
      μ (cylinder ![i]) • μ.map futureSeq := by
    refine ext_of_generate_finite _ generateFrom_futureCylinders isPiSystem_futureCylinders ?_ ?_
    · rintro _ ⟨n, w, rfl⟩
      rw [Measure.map_apply hm (measurableSet_futureCylinder w),
        Measure.restrict_apply (hm (measurableSet_futureCylinder w)), Measure.smul_apply,
        Measure.map_apply measurable_futureSeq (measurableSet_futureCylinder w), smul_eq_mul,
        preimage_futureCylinder]
      have e : (fun x : ℤ → ι => futureSeq (shift 1 x)) ⁻¹' futureCylinder w ∩ cylinder ![i] =
          cylinder (Fin.append ![i] w) := by
        rw [cylinder_append, Set.inter_comm, Nat.cast_one]
        rfl
      rw [e, ← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
        (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)), ENNReal.toReal_mul]
      exact measureReal_cylinder_cons hprod i w
    · rw [Measure.map_apply hm MeasurableSet.univ, Measure.smul_apply,
        Measure.map_apply measurable_futureSeq MeasurableSet.univ]
      simp
  have := congrArg (fun m : Measure (ℕ → ι) => m D) key
  simp only [Measure.map_apply hm hD, Measure.restrict_apply (hm hD), Measure.smul_apply,
    Measure.map_apply measurable_futureSeq hD, smul_eq_mul] at this
  rw [Set.inter_comm]
  exact this

end Bernoulli

/-! ### The projection of a Bernoulli measure -/

namespace System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)

set_option linter.unusedVariables false in
/-- The projection of a Bernoulli measure is invariant with the weights of its symbols, as in
the proof of `thm:main_extended` (tex lines 3404 to 3405). The measure is Bernoulli in the sense
of `sec:normalisation` (tex lines 2236 to 2241), with `p_i = μ[i]`. The proof splits `Σ` into
the cylinders `[i]`, on which `π = φ_i ∘ π ∘ σ`, and uses that `π ∘ σ` is a function of the
future of `σ 𝐢`, which is independent of `i_0`. The hypothesis `hinv` is not used: the product
formula for the cylinders at time `0` determines the law of the future `𝐢^+`. -/
theorem isInvariantMeasure_map_proj {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ)
    (hprod : ∀ (n : ℕ) (w : Fin n → ι), μ.real (cylinder w) = ∏ k, μ.real (cylinder ![w k])) :
    S.IsInvariantMeasure (fun i => μ (cylinder ![i])) (μ.map S.proj) := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  have hproj : Measurable S.proj := hS.measurable_proj
  have hphi : ∀ i, Measurable (S.phi i) := fun i => (S.continuous_phi i).measurable
  have hfac : ∀ C : Set (ℝ × ℝ),
      S.proj ⁻¹' C = futureSeq ⁻¹' ((fun y => S.proj (extendFuture y)) ⁻¹' C) := by
    intro C
    ext x
    simp only [Set.mem_preimage]
    rw [S.proj_congr fun k => (extendFuture_futureSeq x k)]
  unfold IsInvariantMeasure
  refine Measure.ext fun B hB => ?_
  have hdecomp : S.proj ⁻¹' B =
      ⋃ i, cylinder ![i] ∩ shift 1 ⁻¹' (S.proj ⁻¹' (S.phi i ⁻¹' B)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, mem_cylinder]
    constructor
    · intro hx
      refine ⟨x 0, by simp, ?_⟩
      rwa [← hS.proj_eq]
    · rintro ⟨i, hi, hx⟩
      have h0 : x 0 = i := by simpa using hi 0
      rw [hS.proj_eq, h0]
      exact hx
  have hdisj : Pairwise (Function.onFun Disjoint fun i =>
      cylinder ![i] ∩ shift 1 ⁻¹' (S.proj ⁻¹' (S.phi i ⁻¹' B))) := by
    intro i j hij
    refine Set.disjoint_left.2 fun x hx hx' => hij ?_
    have h1 := hx.1 0
    have h2 := hx'.1 0
    simp only [Matrix.cons_val_fin_one] at h1 h2
    rw [← h1, ← h2]
  have hmeas : ∀ i, MeasurableSet
      (cylinder ![i] ∩ shift 1 ⁻¹' (S.proj ⁻¹' (S.phi i ⁻¹' B))) := fun i =>
    (measurableSet_cylinder _).inter (measurable_shift 1 (hproj (hphi i hB)))
  rw [Measure.map_apply hproj hB, Measure.finsetSum_apply, hdecomp, measure_iUnion hdisj hmeas,
    tsum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (hphi i) hB,
    Measure.map_apply hproj (hphi i hB), hfac (S.phi i ⁻¹' B)]
  exact measure_cylinder_inter_shift_preimage hprod i
    ((hproj.comp measurable_extendFuture) (hphi i hB))

/-- The step `π_*μ = ν` of the proof of `thm:main_extended` (tex lines 3404 to 3407): the
projection of a Bernoulli measure `μ` is the only invariant probability measure with the weights
`p_i = μ[i]`. -/
theorem map_proj_eq_of_isInvariantMeasure {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ)
    (hprod : ∀ (n : ℕ) (w : Fin n → ι), μ.real (cylinder w) = ∏ k, μ.real (cylinder ![w k]))
    {ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure ν]
    (hν : S.IsInvariantMeasure (fun i => μ (cylinder ![i])) ν) : μ.map S.proj = ν :=
  IsInvariantMeasure.unique hν.sum_eq_one (S.isInvariantMeasure_map_proj hinv hprod) hν

end System

end BoxLike
