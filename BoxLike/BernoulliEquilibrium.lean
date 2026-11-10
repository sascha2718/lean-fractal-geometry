module

/-
Bernoulli measures and `thm:bernoulli_equilibrium` in `sec:normalisation`. A Bernoulli measure on `ℤ → ι` is the product of copies of a
probability measure `p` on the alphabet; it is invariant and ergodic. For `s ≥ 2` the potential
`φ^s = |det|^{s/2}` is multiplicative, and the `s`-equilibrium state exists, is unique, and is the
Bernoulli measure with the weights `p_i = |det A_i|^{s/2} / ∑_j |det A_j|^{s/2}`.

* `bernoulli`, `measurePreserving_shift_bernoulli`: the Bernoulli measure and its invariance
  under every `σ^m`.
* `bernoulli_inter_preimage_shift`, `ergodic_shift_bernoulli`: a set depending on finitely many
  coordinates is independent of its far translates, and the Bernoulli measure is ergodic.
* `bernoulli_cylinder`, `measureReal_bernoulli_cylinder`: the measure `∏_j p_{w_j}` of the
  cylinder `{x : x_k ⋯ x_{k+n-1} = w}` at every position `k ∈ ℤ`.
* `measure_ext_of_cylinder`, `eq_bernoulli_of_cylinder`, `eq_bernoulli_of_measureReal_cylinder`:
  a finite measure on `ℤ → ι` is determined by its values on the cylinders at all positions, and
  a measure with the cylinder measures `∏_j p_{w_j}` is the Bernoulli measure.
* `blockEntropy_add_of_mul`, `blockEntropy_bernoulli`, `entropy_bernoulli`: the entropy of the
  Bernoulli measure is `∑_i -p_i log p_i`.
* `weightMeasure`, `measureReal_weightMeasure_singleton`, `isProbabilityMeasure_weightMeasure`,
  `eq_bernoulli_weightMeasure_of_measureReal_cylinder`: a probability vector as a measure on the
  alphabet, and the definition of a Bernoulli measure of tex lines 2236 to 2241 in terms of a
  probability vector.
* `System.detWeight`, `System.detWeightMeasure`, `System.measureReal_detWeightMeasure_singleton`:
  the probability vector `p_i = |det A_i|^{s/2} / ∑_j |det A_j|^{s/2}` as a measure on `ι`.
* `System.isEquilibriumState_bernoulli`: the Bernoulli measure with these weights is an
  `s`-equilibrium state for `s ≥ 2`.
* `System.IsEquilibriumState.eq_bernoulli`, `System.IsEquilibriumState.ergodic_of_two_le`: every
  invariant `s`-equilibrium state with `s ≥ 2` is this Bernoulli measure, and it is ergodic.
* `System.existsUnique_isEquilibriumState_of_two_le`: existence and uniqueness of the
  `s`-equilibrium state for `s ≥ 2`.
-/
public import BoxLike.BernoulliEntropy
public import BoxLike.PressureLarge
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ProductMeasure

@[expose] public section

namespace BoxLike

open Filter Topology MeasureTheory ProbabilityTheory
open scoped symmDiff

/-! ### Bernoulli measures -/

section Bernoulli

variable {ι : Type*} [MeasurableSpace ι]

/-- The Bernoulli measure on `Σ = ℤ → ι` with the one-symbol distribution `p`, tex lines 2236 to
2360: the product of copies of `p` over `ℤ`. It is used for a probability measure `p`. -/
noncomputable def bernoulli (p : Measure ι) : Measure (ℤ → ι) :=
  Measure.infinitePi fun _ : ℤ => p

/-- The Bernoulli measure is a probability measure. -/
instance isProbabilityMeasure_bernoulli (p : Measure ι) [IsProbabilityMeasure p] :
    IsProbabilityMeasure (bernoulli p) := by
  unfold bernoulli
  infer_instance

/-- The Bernoulli measure is invariant under every `σ^m`, `m ∈ ℤ`; it belongs to `𝓜_σ(Σ)`, tex
line 2361. -/
theorem measurePreserving_shift_bernoulli (p : Measure ι) [IsProbabilityMeasure p] (m : ℤ) :
    MeasurePreserving (shift m) (bernoulli p) (bernoulli p) := by
  refine ⟨measurable_shift m, ?_⟩
  have h := Measure.infinitePi_map_piCongrLeft (fun _ : ℤ => p) (Equiv.addLeft (-m))
  have e : ⇑(MeasurableEquiv.piCongrLeft (fun _ : ℤ => ι) (Equiv.addLeft (-m))) = shift m := by
    funext x k
    rw [MeasurableEquiv.coe_piCongrLeft]
    simpa using Equiv.piCongrLeft_apply_apply (fun _ : ℤ => ι) (Equiv.addLeft (-m)) x (m + k)
  rw [e] at h
  exact h

/-! ### Ergodicity -/

/-- Under the Bernoulli measure a set `B` depending on the coordinates in a finite set `I ⊆ ℤ`
is independent of `σ^{-m} B` when `m + I` is disjoint from `I`. -/
theorem bernoulli_inter_preimage_shift (p : Measure ι) [IsProbabilityMeasure p] {I : Finset ℤ}
    {S : Set (∀ _ : I, ι)} (hS : MeasurableSet S) {m : ℤ} (hm : ∀ i ∈ I, m + i ∉ I) :
    bernoulli p (I.restrict ⁻¹' S ∩ shift m ⁻¹' (I.restrict ⁻¹' S)) =
      bernoulli p (I.restrict ⁻¹' S) * bernoulli p (I.restrict ⁻¹' S) := by
  let T : Finset ℤ := I.map (addLeftEmbedding m)
  have hT : ∀ i : I, m + (i : ℤ) ∈ T := fun i => Finset.mem_map.2 ⟨i, i.2, rfl⟩
  let r : (∀ _ : T, ι) → ∀ _ : I, ι := fun y i => y ⟨m + i, hT i⟩
  have hr : Measurable r := Measurable.of_eval fun i => measurable_pi_apply _
  have hpre : shift m ⁻¹' (I.restrict ⁻¹' S) = T.restrict ⁻¹' (r ⁻¹' S) := rfl
  have hdisj : Disjoint I T := by
    rw [Finset.disjoint_left]
    intro i hi hiT
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hiT
    exact hm j hj hi
  have hind : iIndepFun (fun (i : ℤ) (x : ℤ → ι) => x i) (bernoulli p) :=
    iIndepFun_infinitePi (P := fun _ : ℤ => p) (X := fun _ => id) fun _ => measurable_id
  have h := (hind.indepFun_finset I T hdisj fun i => measurable_pi_apply i
    ).measure_inter_preimage_eq_mul S (r ⁻¹' S) hS (hr hS)
  have hmp := (measurePreserving_shift_bernoulli p m).measure_preimage
    (Finset.measurable_restrict I hS).nullMeasurableSet
  rw [hpre] at hmp ⊢
  exact h.trans (congrArg _ hmp)

/-- A Bernoulli measure is ergodic, tex line 2242; see Walters, An Introduction to Ergodic Theory,
Section 1.5. An invariant set `A` is approximated by a set `B` depending on finitely many
coordinates, the far translate `σ^{-m} B` approximates `σ^{-m} A = A` equally well and is
independent of `B`, so `μ(A) = μ(A)²`. -/
theorem ergodic_shift_bernoulli (p : Measure ι) [IsProbabilityMeasure p] :
    Ergodic (shift 1) (bernoulli p) := by
  refine ⟨measurePreserving_shift_bernoulli p 1, ⟨fun A hA hinv => ?_⟩⟩
  have hinvm : ∀ m : ℕ, shift (m : ℤ) ⁻¹' A = A := fun m => by
    have h := Function.IsFixedPt.preimage_iterate (f := shift 1) hinv m
    rwa [iterate_shift_one] at h
  have key : ∀ ε : ℝ, 0 < ε →
      |(bernoulli p).real A - (bernoulli p).real A * (bernoulli p).real A| ≤ 4 * ε := by
    intro ε hε
    obtain ⟨B, hB, hBA⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      (μ := bernoulli p) isSetRing_measurableCylinders
      ⟨{Set.univ}, Set.countable_singleton _,
        by simpa using univ_mem_measurableCylinders fun _ : ℤ => ι, by simp⟩
      generateFrom_measurableCylinders.symm hA (ENNReal.ofReal_pos.2 hε)
    obtain ⟨I, S, hS, hBeq⟩ := (mem_measurableCylinders B).1 hB
    have hBm : MeasurableSet B := .of_mem_measurableCylinders hB
    have hm : ∀ i ∈ I, ((2 * I.sup Int.natAbs + 1 : ℕ) : ℤ) + i ∉ I := by
      intro i hi hmi
      have h1 := Finset.le_sup (f := Int.natAbs) hi
      have h2 := Finset.le_sup (f := Int.natAbs) hmi
      omega
    generalize 2 * I.sup Int.natAbs + 1 = m at hm
    have hmp := measurePreserving_shift_bernoulli p m
    have hB'm : MeasurableSet (shift (m : ℤ) ⁻¹' B) := hmp.measurable hBm
    have hd : (bernoulli p).real (B ∆ A) < ε := ENNReal.toReal_lt_of_lt_ofReal hBA
    have hd' : (bernoulli p).real ((shift (m : ℤ) ⁻¹' B) ∆ A) = (bernoulli p).real (B ∆ A) := by
      conv_lhs => rw [← hinvm m, ← Set.preimage_symmDiff]
      exact hmp.measureReal_preimage (hBm.symmDiff hA).nullMeasurableSet
    have h1 := abs_measureReal_sub_le_measureReal_symmDiff (μ := bernoulli p)
      hBm.nullMeasurableSet hA.nullMeasurableSet
    have h2 := abs_measureReal_sub_le_measureReal_symmDiff (μ := bernoulli p)
      (hBm.inter hB'm).nullMeasurableSet hA.nullMeasurableSet
    have hsub : (B ∩ shift (m : ℤ) ⁻¹' B) ∆ A ⊆ B ∆ A ∪ (shift (m : ℤ) ⁻¹' B) ∆ A := by
      intro x
      simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_union]
      tauto
    have h3 := (measureReal_mono hsub).trans (measureReal_union_le _ _)
    have h4 : (bernoulli p).real (B ∩ shift (m : ℤ) ⁻¹' B) =
        (bernoulli p).real B * (bernoulli p).real B := by
      subst hBeq
      rw [measureReal_def, measureReal_def, ← ENNReal.toReal_mul]
      exact congrArg ENNReal.toReal (bernoulli_inter_preimage_shift p hS hm)
    rw [h4] at h2
    rw [hd'] at h3
    have ha0 : 0 ≤ (bernoulli p).real A := measureReal_nonneg
    have ha1 : (bernoulli p).real A ≤ 1 := measureReal_le_one
    have hb0 : 0 ≤ (bernoulli p).real B := measureReal_nonneg
    have hb1 : (bernoulli p).real B ≤ 1 := measureReal_le_one
    generalize (bernoulli p).real A = a at *
    generalize (bernoulli p).real B = b at *
    generalize (bernoulli p).real (B ∆ A) = d at *
    have h5 : |b * b - a * a| ≤ 2 * d := by
      have e : b * b - a * a = (b + a) * (b - a) := by ring
      rw [e, abs_mul]
      exact mul_le_mul (abs_le.2 ⟨by linarith, by linarith⟩) h1 (abs_nonneg _) (by norm_num)
    rw [abs_le] at h2 h5 ⊢
    constructor <;> linarith
  have h0 : (bernoulli p).real A - (bernoulli p).real A * (bernoulli p).real A = 0 :=
    abs_eq_zero.1 <| le_antisymm (le_of_forall_pos_le_add fun ε hε => by
      have := key (ε / 4) (by positivity)
      linarith) (abs_nonneg _)
  rw [eventuallyEmptyOrUniv_iff', ae_eq_empty, ae_eq_univ, prob_compl_eq_zero_iff hA]
  have h01 : (bernoulli p).real A = 0 ∨ (bernoulli p).real A = 1 := by
    have : (bernoulli p).real A * (1 - (bernoulli p).real A) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases h01 with h | h
  · exact Or.inl ((measureReal_eq_zero_iff (by finiteness)).1 h)
  · refine Or.inr ?_
    rw [measureReal_def] at h
    exact (ENNReal.toReal_eq_one_iff _).1 h

/-! ### Cylinders -/

variable [MeasurableSingletonClass ι]

/-- The defining property of the Bernoulli measure, tex lines 2236 to 2241: the cylinder
`[i_k ⋯ i_ℓ] = {x : x_k ⋯ x_{k+n-1} = w}` at the position `k ∈ ℤ`, which is `σ^{-k}[w]`, has
measure `p_{w_0} ⋯ p_{w_{n-1}}`. -/
theorem bernoulli_cylinder (p : Measure ι) [IsProbabilityMeasure p] (k : ℤ) {n : ℕ}
    (w : Fin n → ι) : bernoulli p {x | ∀ j : Fin n, x (k + j) = w j} = ∏ j, p {w j} := by
  have hinj : Function.Injective fun j : Fin n => k + (j : ℤ) := fun i j h =>
    Fin.ext (by simpa using h)
  let t : ℤ → Set ι := Function.extend (fun j : Fin n => k + (j : ℤ)) (fun j => {w j})
    fun _ => Set.univ
  have ht : ∀ j : Fin n, t (k + j) = {w j} := fun j => hinj.extend_apply _ _ j
  have hset : {x : ℤ → ι | ∀ j : Fin n, x (k + j) = w j} =
      Set.pi (Finset.univ.map ⟨_, hinj⟩ : Finset ℤ) t := by
    ext x
    simp [ht]
  rw [hset, bernoulli, Measure.infinitePi_pi, Finset.prod_map]
  · simp [ht]
  · intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 hi
    simp [ht]

/-- The cylinder `[w]` has the real Bernoulli measure `∏_j p_{w_j}`. -/
theorem measureReal_bernoulli_cylinder (p : Measure ι) [IsProbabilityMeasure p] {n : ℕ}
    (w : Fin n → ι) : (bernoulli p).real (cylinder w) = ∏ j, p.real {w j} := by
  have h := bernoulli_cylinder p 0 w
  simp only [zero_add] at h
  rw [measureReal_def, cylinder, h, ENNReal.toReal_prod]
  rfl

variable [Fintype ι]

/-- A finite measure on `ℤ → ι` is determined by its values on the cylinders
`{x : x_k ⋯ x_{k+n-1} = w}`, `k ∈ ℤ`: every set depending on finitely many coordinates is a
finite disjoint union of such cylinders. -/
theorem measure_ext_of_cylinder {μ ν : Measure (ℤ → ι)} [IsFiniteMeasure μ]
    (h : ∀ (k : ℤ) (n : ℕ) (w : Fin n → ι),
      μ {x | ∀ j : Fin n, x (k + j) = w j} = ν {x | ∀ j : Fin n, x (k + j) = w j}) :
    μ = ν := by
  have hP : IsProjectiveLimit μ fun I : Finset ℤ => μ.map I.restrict := fun I => rfl
  refine hP.unique fun I => (Measure.ext_of_singleton fun f => ?_).symm
  rw [Measure.map_apply (Finset.measurable_restrict I) (measurableSet_singleton f),
    Measure.map_apply (Finset.measurable_restrict I) (measurableSet_singleton f)]
  obtain ⟨k, n, hkn⟩ : ∃ (k : ℤ) (n : ℕ), ∀ i ∈ I, ∃ j : Fin n, k + j = i := by
    refine ⟨-(I.sup Int.natAbs : ℕ), 2 * I.sup Int.natAbs + 1, fun i hi => ?_⟩
    have hle := Finset.le_sup (f := Int.natAbs) hi
    refine ⟨⟨(i + (I.sup Int.natAbs : ℕ)).toNat, by omega⟩, ?_⟩
    simp only
    omega
  have hg : ∀ w : Fin n → ι, MeasurableSet {x : ℤ → ι | ∀ j : Fin n, x (k + j) = w j} :=
    fun w => (measurable_shift k) (measurableSet_cylinder w)
  have hpre : ∀ w : Fin n → ι, (fun (x : ℤ → ι) (j : Fin n) => x (k + j)) ⁻¹' {w} =
      {x | ∀ j : Fin n, x (k + j) = w j} := fun w => by
    ext x
    simp [funext_iff]
  have key : ∀ ρ : Measure (ℤ → ι), ρ (I.restrict ⁻¹' {f}) =
      ∑ w : Fin n → ι, ρ ({x | ∀ j : Fin n, x (k + j) = w j} ∩ I.restrict ⁻¹' {f}) := by
    intro ρ
    have hsum := sum_measure_preimage_singleton (μ := ρ.restrict (I.restrict ⁻¹' {f}))
      Finset.univ (f := fun (x : ℤ → ι) (j : Fin n) => x (k + j))
      fun w _ => by rw [hpre]; exact hg w
    rw [Finset.coe_univ, Set.preimage_univ, Measure.restrict_apply_univ] at hsum
    rw [← hsum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hpre, Measure.restrict_apply (hg w)]
  rw [key μ, key ν]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hne :
      ({x : ℤ → ι | ∀ j : Fin n, x (k + j) = w j} ∩ I.restrict ⁻¹' {f}).Nonempty
  · obtain ⟨x, hxw, hxf⟩ := hne
    have hsub : {x : ℤ → ι | ∀ j : Fin n, x (k + j) = w j} ⊆
        (I.restrict ⁻¹' {f} : Set (ℤ → ι)) := by
      intro y hy
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hxf ⊢
      rw [← hxf]
      funext i
      obtain ⟨j, hj⟩ := hkn i i.2
      rw [Finset.restrict, Finset.restrict, ← hj, hy j, hxw j]
    rw [Set.inter_eq_left.2 hsub]
    exact h k n w
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, measure_empty, measure_empty]

/-- A measure whose cylinders at every position have the measure `p_{w_0} ⋯ p_{w_{n-1}}` of tex
lines 2355 to 2360 is the Bernoulli measure with the one-symbol distribution `p`. The empty word
gives `μ(Σ) = 1`. -/
theorem eq_bernoulli_of_cylinder (p : Measure ι) [IsProbabilityMeasure p] {μ : Measure (ℤ → ι)}
    (h : ∀ (k : ℤ) (n : ℕ) (w : Fin n → ι),
      μ {x | ∀ j : Fin n, x (k + j) = w j} = ∏ j, p {w j}) :
    μ = bernoulli p := by
  have : IsFiniteMeasure μ := ⟨by
    have h0 := h 0 0 Fin.elim0
    simp only [IsEmpty.forall_iff, Set.ofPred_true, Finset.univ_eq_empty,
      Finset.prod_empty] at h0
    rw [h0]
    exact ENNReal.one_lt_top⟩
  exact measure_ext_of_cylinder fun k n w => by rw [h k n w, bernoulli_cylinder]

/-- The real form of `eq_bernoulli_of_cylinder`. -/
theorem eq_bernoulli_of_measureReal_cylinder (p : Measure ι) [IsProbabilityMeasure p]
    {μ : Measure (ℤ → ι)} [IsFiniteMeasure μ]
    (h : ∀ (k : ℤ) (n : ℕ) (w : Fin n → ι),
      μ.real {x | ∀ j : Fin n, x (k + j) = w j} = ∏ j, p.real {w j}) :
    μ = bernoulli p := by
  refine eq_bernoulli_of_cylinder p fun k n w => ?_
  rw [← ofReal_measureReal, h k n w, ENNReal.ofReal_prod_of_nonneg fun _ _ => measureReal_nonneg]
  exact Finset.prod_congr rfl fun j _ => ofReal_measureReal

/-! ### The entropy of a Bernoulli measure -/

/-- If `μ[w w'] = μ[w] μ[w']` for all words of lengths `m` and `n`, then
`H_μ(𝒫_0^{m+n-1}) = H_μ(𝒫_0^{m-1}) + H_μ(𝒫_0^{n-1})`. -/
theorem blockEntropy_add_of_mul (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] {m n : ℕ}
    (h : ∀ (w : Fin m → ι) (w' : Fin n → ι),
      μ.real (cylinder (Fin.append w w')) = μ.real (cylinder w) * μ.real (cylinder w')) :
    blockEntropy μ (m + n) = blockEntropy μ m + blockEntropy μ n := by
  rw [blockEntropy_add_eq_sum]
  simp only [h, Real.negMulLog_mul, Finset.sum_add_distrib]
  rw [← Finset.sum_mul_sum, Finset.sum_comm, ← Finset.sum_mul_sum, sum_measureReal_cylinder,
    sum_measureReal_cylinder, one_mul, one_mul, blockEntropy, blockEntropy]

/-- `H_μ(𝒫_0^{n-1}) = n ∑_i -p_i log p_i` for the Bernoulli measure `μ` with weights `p`. -/
theorem blockEntropy_bernoulli (p : Measure ι) [IsProbabilityMeasure p] (n : ℕ) :
    blockEntropy (bernoulli p) n = n * ∑ i, Real.negMulLog (p.real {i}) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [blockEntropy_add_of_mul (bernoulli p) fun w w' => ?_, ih, blockEntropy_one]
    · simp only [measureReal_bernoulli_cylinder, Fin.prod_univ_one, Matrix.cons_val_zero]
      push_cast
      ring
    · simp only [measureReal_bernoulli_cylinder]
      rw [Fin.prod_univ_add]
      simp

/-- The entropy of the Bernoulli measure with weights `p` is the entropy `∑_i -p_i log p_i` of
the one-symbol distribution, the equality case of tex lines 2268 and 2269. -/
theorem entropy_bernoulli (p : Measure ι) [IsProbabilityMeasure p] :
    entropy (bernoulli p) = ∑ i, Real.negMulLog (p.real {i}) := by
  refine Tendsto.limUnder_eq (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [blockEntropy_bernoulli, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 hn)]

/-! ### Probability vectors -/

/-- The measure `∑_i p_i δ_i` on the alphabet with the weights `p_i`. It is used for a probability
vector `(p_1, …, p_N)`, tex line 2237. -/
noncomputable def weightMeasure (p : ι → ℝ) : Measure ι :=
  ∑ i, ENNReal.ofReal (p i) • Measure.dirac i

/-- The measure `∑_i p_i δ_i` gives the symbol `i` the mass `p_i`. -/
theorem weightMeasure_singleton (p : ι → ℝ) (i : ι) :
    weightMeasure p {i} = ENNReal.ofReal (p i) := by
  classical
  simp [weightMeasure, Set.indicator_apply, eq_comm]

/-- The measure `∑_i p_i δ_i` gives the symbol `i` the mass `p_i`, in real form. -/
theorem measureReal_weightMeasure_singleton {p : ι → ℝ} {i : ι} (hp : 0 ≤ p i) :
    (weightMeasure p).real {i} = p i := by
  rw [measureReal_def, weightMeasure_singleton, ENNReal.toReal_ofReal hp]

omit [MeasurableSingletonClass ι] in
/-- The measure `∑_i p_i δ_i` of a probability vector is a probability measure. -/
theorem isProbabilityMeasure_weightMeasure {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) : IsProbabilityMeasure (weightMeasure p) := by
  constructor
  have h : ∑ i, ENNReal.ofReal (p i) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hp i, hsum, ENNReal.ofReal_one]
  simpa [weightMeasure] using h

/-- The definition of a Bernoulli measure of tex lines 2236 to 2241 determines the measure: a
probability measure `μ` with `μ([i_k ⋯ i_ℓ]) = p_{i_k} ⋯ p_{i_ℓ}` for a probability vector `p`
and every cylinder `[i_k ⋯ i_ℓ] = σ^{-k}[w]` is the product measure with the one-symbol
distribution `∑_i p_i δ_i`. -/
theorem eq_bernoulli_weightMeasure_of_measureReal_cylinder {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]
    (h : ∀ (k : ℤ) (n : ℕ), 0 < n → ∀ w : Fin n → ι,
      μ.real (shift k ⁻¹' cylinder w) = ∏ j, p (w j)) :
    μ = bernoulli (weightMeasure p) := by
  have := isProbabilityMeasure_weightMeasure hp hsum
  refine eq_bernoulli_of_measureReal_cylinder _ fun k n w => ?_
  simp only [measureReal_weightMeasure_singleton (hp _)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact h k n hn w

end Bernoulli

/-! ### The equilibrium state for `s ≥ 2` -/

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι) (s : ℝ)

omit [Fintype ι] in
/-- `|det A_i|^t > 0`. -/
theorem rpow_abs_det_mat_pos (t : ℝ) (i : ι) : 0 < |(S.mat i).det| ^ t := by
  refine Real.rpow_pos_of_pos ?_ t
  rw [mat, abs_det_boxMat]
  exact mul_pos (abs_pos.2 (S.a_ne_zero i)) (abs_pos.2 (S.b_ne_zero i))

/-- The weights `p_i = |det A_i|^{s/2} / ∑_j |det A_j|^{s/2}` of tex line 2261. -/
noncomputable def detWeight (i : ι) : ℝ :=
  |(S.mat i).det| ^ (s / 2) / ∑ j, |(S.mat j).det| ^ (s / 2)

/-- The weights `p_i` are positive. -/
theorem detWeight_pos (i : ι) : 0 < S.detWeight s i :=
  div_pos (S.rpow_abs_det_mat_pos _ i)
    (Finset.sum_pos (fun j _ => S.rpow_abs_det_mat_pos _ j) ⟨i, Finset.mem_univ i⟩)

/-- The weights `p_i` form a probability vector. -/
theorem sum_detWeight [Nonempty ι] : ∑ i, S.detWeight s i = 1 := by
  simp only [detWeight]
  rw [← Finset.sum_div]
  exact div_self (Finset.sum_pos (fun j _ => S.rpow_abs_det_mat_pos _ j)
    Finset.univ_nonempty).ne'

variable [MeasurableSpace ι]

/-- The probability vector `(p_i)` of tex line 2261 as the measure `∑_i p_i δ_i` on the
alphabet. -/
noncomputable def detWeightMeasure : Measure ι := weightMeasure (S.detWeight s)

/-- The measure `∑_i p_i δ_i` is a probability measure on a non-empty alphabet. -/
instance isProbabilityMeasure_detWeightMeasure [Nonempty ι] :
    IsProbabilityMeasure (S.detWeightMeasure s) :=
  isProbabilityMeasure_weightMeasure (fun i => (S.detWeight_pos s i).le) (S.sum_detWeight s)

variable [MeasurableSingletonClass ι]

/-- The measure `∑_i p_i δ_i` gives the symbol `i` the mass
`p_i = |det A_i|^{s/2} / ∑_j |det A_j|^{s/2}`. -/
theorem measureReal_detWeightMeasure_singleton (i : ι) :
    (S.detWeightMeasure s).real {i} = S.detWeight s i :=
  measureReal_weightMeasure_singleton (S.detWeight_pos s i).le

variable {s}

/-- For `s ≥ 2` the Bernoulli measure with the weights
`p_i = |det A_i|^{s/2} / ∑_j |det A_j|^{s/2}` is an `s`-equilibrium state, tex lines 2258 to
2381: its entropy is `∑_i -p_i log p_i`, its energy is `∑_i p_i log |det A_i|^{s/2}`, and the
sum is `log ∑_i |det A_i|^{s/2} = P(𝖠, s)`. -/
theorem isEquilibriumState_bernoulli [Nonempty ι] (hs : 2 ≤ s) :
    S.IsEquilibriumState s (bernoulli (S.detWeightMeasure s)) := by
  have hinv := measurePreserving_shift_bernoulli (S.detWeightMeasure s) 1
  refine IsEquilibriumState.of_pressure_eq hinv (by linarith) ?_
  have hcyl : ∀ i, (bernoulli (S.detWeightMeasure s)).real (cylinder ![i]) = S.detWeight s i :=
    fun i => by
      rw [measureReal_bernoulli_cylinder, Fin.prod_univ_one, Matrix.cons_val_zero,
        measureReal_detWeightMeasure_singleton]
  have hdefect := sum_gibbs_defect (p := S.detWeight s) (q := fun i => |(S.mat i).det| ^ (s / 2))
    (S.sum_detWeight s) (S.rpow_abs_det_mat_pos _)
  have hzero : ∀ i, |(S.mat i).det| ^ (s / 2) / ∑ j, |(S.mat j).det| ^ (s / 2)
      - S.detWeight s i - (Real.negMulLog (S.detWeight s i) + S.detWeight s i
        * Real.log (|(S.mat i).det| ^ (s / 2) / ∑ j, |(S.mat j).det| ^ (s / 2))) = 0 :=
    fun i => by
      rw [← detWeight, Real.negMulLog]
      ring
  rw [Finset.sum_congr rfl fun i _ => hzero i, Finset.sum_const_zero] at hdefect
  have hlog : ∀ i, Real.log (|(S.mat i).det| ^ (s / 2)) = s / 2 * Real.log |(S.mat i).det| :=
    fun i => Real.log_rpow (by simpa using S.rpow_abs_det_mat_pos 1 i) _
  rw [S.pressure_of_two_le hs, energy_of_two_le hs, S.lyapunov₁_add_lyapunov₂ hinv,
    entropy_bernoulli, Finset.mul_sum]
  simp only [hcyl, measureReal_detWeightMeasure_singleton]
  simp only [hlog] at hdefect
  have e : ∀ i, s / 2 * (S.detWeight s i * Real.log |(S.mat i).det|) =
      S.detWeight s i * (s / 2 * Real.log |(S.mat i).det|) := fun i => by ring
  simp only [e]
  linarith

variable {S}

/-- For `s ≥ 2` every invariant `s`-equilibrium state is the Bernoulli measure with the weights
`p_i = |det A_i|^{s/2} / ∑_j |det A_j|^{s/2}`, tex lines 2267 to 2275: the entropy is at most the
entropy of the one-symbol distribution, with equality only for a Bernoulli measure, and the
variational expression of this distribution is maximised only by `(p_i)`. -/
theorem IsEquilibriumState.eq_bernoulli {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]
    (heq : S.IsEquilibriumState s μ) (hinv : MeasurePreserving (shift 1) μ μ) (hs : 2 ≤ s) :
    μ = bernoulli (S.detWeightMeasure s) := by
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
  have hq := S.rpow_abs_det_mat_pos (s / 2)
  have hE := heq.log_sum_eq hinv hs
  have hrw : s / 2 * ∑ i, μ.real (cylinder ![i]) * Real.log |(S.mat i).det| =
      ∑ i, μ.real (cylinder ![i]) * Real.log (|(S.mat i).det| ^ (s / 2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.log_rpow (by simpa using S.rpow_abs_det_mat_pos 1 i)]
    ring
  rw [hrw] at hE
  have hG := blockEntropy_one_add_sum_le μ (fun i => |(S.mat i).det| ^ (s / 2)) hq
  have hH := entropy_le_blockEntropy_one hinv
  have hent : entropy μ = blockEntropy μ 1 := by linarith
  have hGeq : blockEntropy μ 1
      + ∑ i, μ.real (cylinder ![i]) * Real.log (|(S.mat i).det| ^ (s / 2)) =
      Real.log (∑ i, |(S.mat i).det| ^ (s / 2)) := by linarith
  refine eq_bernoulli_of_measureReal_cylinder _ fun k n w => ?_
  rw [measureReal_preimage_shift_cylinder_eq_prod_of_entropy_eq hinv hent k w]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [measureReal_cylinder_eq_of_blockEntropy_one_add_sum_eq μ _ hq hGeq,
    measureReal_detWeightMeasure_singleton, detWeight]

/-- For `s ≥ 2` every invariant `s`-equilibrium state is ergodic: it is a Bernoulli measure. -/
theorem IsEquilibriumState.ergodic_of_two_le {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]
    (heq : S.IsEquilibriumState s μ) (hinv : MeasurePreserving (shift 1) μ μ) (hs : 2 ≤ s) :
    Ergodic (shift 1) μ := by
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
  rw [heq.eq_bernoulli hinv hs]
  exact ergodic_shift_bernoulli _

variable (S)

/-- For `s ≥ 2` there is exactly one invariant probability measure that is an
`s`-equilibrium state, tex lines 2258 to 2275. -/
theorem existsUnique_isEquilibriumState_of_two_le [Nonempty ι] (hs : 2 ≤ s) :
    ∃! μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
      S.IsEquilibriumState s μ :=
  ⟨bernoulli (S.detWeightMeasure s),
    ⟨inferInstance, measurePreserving_shift_bernoulli _ 1, S.isEquilibriumState_bernoulli hs⟩,
    fun _ ⟨hprob, hinv, heq⟩ => haveI := hprob; heq.eq_bernoulli hinv hs⟩

end System

end BoxLike
