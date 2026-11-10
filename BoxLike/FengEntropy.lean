module

/-
The pointwise entropies of `sec:entropies` as limits along cylinders and the criterion for their
vanishing: `thm:feng_entropy_as_limit` and `thm:feng_entropy_zero`. Both are derived from the
first identity of Feng, Lemma 4.6, (4.16), which is the hypothesis `FengInfoSum` for the planar
partitions `ξ_i` and `FengInfoSumBar` for the partitions `\overline{ξ}_i` of the projective
system.

The general part works on the full shift over a finite alphabet, for an invariant probability
measure `μ` and a map `ξ` whose conditional measures satisfy the identity
`-log μ_x^ξ([x|_n]) = ∑_{k<n} I_μ(𝒫 | \widehat{ξ})(σ^k x)` almost everywhere. Division by `n` and
Birkhoff's theorem give the limit. If the pointwise entropy `H = E_μ(I | ℐ)` vanishes on an
invariant set `E`, then `∫_E I dμ = ∫_E H dμ = 0`, so `I(σ^k x) = 0` for every `k` and almost
every `x ∈ E`, and the identity gives `μ_x^ξ([x|_n]) = 1` for every `n`. A conditional measure
carried by an atom with fixed past is then the Dirac mass at `x`.

For the planar partitions the atoms have fixed past on `Σ'`. The set `Σ'` is invariant, so an
ergodic measure gives it mass `0` or `1`. If `μ(Σ') = 0` the partition is trivial modulo `μ`,
the conditional measures are `μ` itself, and an invariant measure giving mass one to all
cylinders `[x|_n]` of one point is the Dirac mass at a constant sequence. By
`sec:lyapunov_exponents`, tex line 1522 (`System.measure_SigmaPrime_compl`), the case
`μ(Σ') = 0` does not occur; treating it keeps this module independent of that result.

* `condMeas_pos_of_mem`, `condMeas_cylinder_pos`: `μ_x^ξ(A) > 0` for almost every `x ∈ A`.
* `condMeas_eq_one_of_atom_subset`, `condMeas_atomsOn_of_measure_eq_zero`: the conditional
  measures of a measurable partition are carried by every set containing the atom, and the
  conditional measures of a partition of a null set `D` are `μ`.
* `birkhoffAverage_shift_one`: Birkhoff averages along the shift.
* `tendsto_neg_log_condMeas_cylinder`: the general form of `thm:feng_entropy_as_limit`.
* `condInfo_shift_eq_zero_of_localEntropy_eq_zero`,
  `condMeas_cylinder_eq_one_of_localEntropy_eq_zero`: the vanishing step of
  `thm:feng_entropy_zero`.
* `eq_dirac_of_cylinder_of_samePast`: a probability measure carried by all cylinders `[x|_n]`
  and by the points with the past of `x` is `δ_x`.
* `localEntropy_eq_zero_iff_condMeas_eq_dirac`: the general form of `thm:feng_entropy_zero`.
* `measure_singleton_const_of_cylinder`: an invariant probability measure that gives mass one
  to every cylinder `[x|_n]` is the Dirac mass at a constant sequence.
* `System.condMeas_xi_samePast`, `System.condMeas_xiBar_samePast`: the conditional measures of
  `ξ_i` that give mass one to all cylinders `[x|_n]`, and the conditional measures of
  `\overline{ξ}_i`, are carried by the points with the past of `x`.
* `System.feng_entropy_as_limit`, `System.feng_entropy_as_limit_bar`:
  `thm:feng_entropy_as_limit`.
* `System.feng_entropy_zero`, `System.feng_entropy_zero_bar`: `thm:feng_entropy_zero`.
-/
public import BoxLike.Birkhoff
public import BoxLike.ConditionalMeasures
public import BoxLike.LiteratureFeng
public import BoxLike.MeasurablePartitions
public import BoxLike.PartitionIdentities
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set

universe u

/-! ### Conditional measures on a standard Borel space -/

section StandardBorel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- Feng, Lemma 2.2, in the form used for `thm:feng_entropy_zero`: for a Borel set `A`,
`μ_x^ξ(A) > 0` for `μ`-almost every `x ∈ A`. The set `B = {x : μ_x^ξ(A) = 0}` lies in
`\widehat{ξ}`, and `μ(A ∩ B) = ∫_B μ_x^ξ(A) dμ(x) = 0`. -/
theorem condMeas_pos_of_mem (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Set Ω) {A : Set Ω}
    (hA : MeasurableSet A) : ∀ᵐ x ∂μ, x ∈ A → 0 < condMeas μ ξ x A := by
  have hB : MeasurableSet[saturated ξ] {x | condMeas μ ξ x A = 0} :=
    measurable_condMeas μ ξ hA (measurableSet_singleton 0)
  have h0 : μ (A ∩ {x | condMeas μ ξ x A = 0}) = 0 := by
    rw [← setLIntegral_condMeas μ ξ hA hB,
      setLIntegral_congr_fun (saturated_le ξ _ hB) (fun x hx => hx)]
    simp
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with x hx hxA
  exact pos_iff_ne_zero.2 fun h => hx ⟨hxA, h⟩

/-- "The conditional measure is supported on an atom with fixed past" (proof of
`thm:feng_entropy_zero`), in general form: for a measurable partition `ξ`, the conditional
measure `μ_x^ξ` gives mass one to every set `R(x)` containing the atom `ξ(x)`, for `μ`-almost
every `x`. This is `condMeas_atom`. -/
theorem condMeas_eq_one_of_atom_subset (μ : Measure Ω) [IsFiniteMeasure μ] {ξ : Ω → Set Ω}
    (hξ : IsMeasurablePartition ξ) {R : Ω → Set Ω} (hsub : ∀ᵐ x ∂μ, ξ x ⊆ R x) :
    ∀ᵐ x ∂μ, condMeas μ ξ x (R x) = 1 := by
  filter_upwards [condMeas_atom μ hξ, hsub] with x hx hxR
  exact le_antisymm prob_le_one (hx.symm.le.trans (measure_mono hxR))

/-- If `μ(D) = 0`, the partition `atomsOn D η` of `sec:entropies` is trivial modulo `μ`: every
set of its `σ`-algebra contains `Ω ∖ D` or lies in `D`, so it has measure `1` or `0`, and the
conditional measures are `μ` itself, by `condMeas_unique`. -/
theorem condMeas_atomsOn_of_measure_eq_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    {D : Set Ω} (hD : μ D = 0) (η : Ω → Set Ω) :
    ∀ᵐ x ∂μ, condMeas μ (atomsOn D η) x = μ := by
  have h := condMeas_unique μ (atomsOn D η) (fun _ => μ) (fun A _ => measurable_const)
    fun A B _ hB => by
      rw [setLIntegral_const]
      by_cases hBD : B ⊆ D
      · rw [measure_mono_null hBD hD, measure_mono_null (inter_subset_right.trans hBD) hD,
          mul_zero]
      · obtain ⟨x₀, hx₀B, hx₀D⟩ := not_subset.1 hBD
        have hsub : Bᶜ ⊆ D := by
          intro y hyB
          by_contra hyD
          refine hyB ((hB.2 x₀ y ?_).1 hx₀B)
          rw [atomsOn_of_notMem hx₀D]
          exact hyD
        have hBc : μ Bᶜ = 0 := measure_mono_null hsub hD
        rw [measure_inter_conull hBc,
          (prob_compl_eq_zero_iff (saturated_le _ _ hB)).1 hBc, mul_one]
  filter_upwards [h] with x hx using hx.symm

end StandardBorel

/-! ### The general statements on the full shift -/

/-- The Birkhoff average of `f` along the shift `σ` is `n⁻¹ ∑_{k<n} f(σ^k x)`, the form in
which the averages occur in `thm:feng_entropy_as_limit`. -/
theorem birkhoffAverage_shift_one {α : Type*} (f : (ℤ → α) → ℝ) (n : ℕ) (x : ℤ → α) :
    birkhoffAverage ℝ (shift 1) f n x = (∑ k ∈ Finset.range n, f (shift k x)) / n := by
  rw [birkhoffAverage, birkhoffSum, smul_eq_mul, div_eq_inv_mul]
  simp only [iterate_shift_one]

section Dirac

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The last step of the proof of `thm:feng_entropy_zero`: "the conditional measure is supported
on an atom with fixed past, intersecting these cylinders gives `ν({x}) = 1`". A probability
measure on the two-sided shift that gives mass one to every cylinder `[x|_n]` and to the set of
points with the past of `x` is the Dirac mass at `x`. -/
theorem eq_dirac_of_cylinder_of_samePast {ν : Measure (ℤ → α)} [IsProbabilityMeasure ν]
    {x : ℤ → α} (hcyl : ∀ n : ℕ, ν (cylinder (block n x)) = 1)
    (hpast : ν {y | SamePast y x} = 1) : ν = Measure.dirac x := by
  have hpm : MeasurableSet {y : ℤ → α | SamePast y x} := by
    have : {y : ℤ → α | SamePast y x} = past ⁻¹' {past x} := by
      ext y
      exact past_eq_iff.symm
    rw [this]
    exact measurable_past (measurableSet_singleton _)
  have hsub : ({x} : Set (ℤ → α))ᶜ ⊆
      {y | SamePast y x}ᶜ ∪ ⋃ n : ℕ, (cylinder (block n x))ᶜ := by
    intro y hy
    by_contra hcon
    simp only [mem_union, mem_compl_iff, mem_iUnion, not_or, not_not, not_exists] at hcon
    refine hy (funext fun k => ?_)
    rcases lt_or_ge k 0 with hk | hk
    · exact hcon.1 k hk
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
      exact hcon.2 (m + 1) ⟨m, Nat.lt_succ_self m⟩
  have hnull : ν ({x} : Set (ℤ → α))ᶜ = 0 := by
    refine measure_mono_null hsub (measure_union_null ?_ (measure_iUnion_null fun n => ?_))
    · exact (prob_compl_eq_zero_iff hpm).2 hpast
    · exact (prob_compl_eq_zero_iff (measurableSet_cylinder _)).2 (hcyl n)
  have hae : ∀ᵐ y ∂ν, y ∈ ({x} : Set (ℤ → α)) := measure_eq_zero_iff_ae_notMem.1 hnull |>.mono
    fun y hy => not_not.1 hy
  have h1 : ν {x} = 1 := (prob_compl_eq_zero_iff (measurableSet_singleton x)).1 hnull
  rw [← Measure.restrict_eq_self_of_ae_mem hae, Measure.restrict_singleton, h1, one_smul]

/-- An invariant probability measure that gives mass one to every cylinder `[x|_n]` of one point
`x` is the Dirac mass at the constant sequence `x_0`. The sets `{z : z_0 = x_k}`, `k ≥ 0`, have
measure one by invariance, so they meet and `x_k = x_0`; by invariance again every set
`{z : z_j = x_0}`, `j ∈ ℤ`, has measure one. This covers the partition of `sec:entropies` that is
trivial modulo `μ`. -/
theorem measure_singleton_const_of_cylinder {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) {x : ℤ → α}
    (hcyl : ∀ n : ℕ, μ (cylinder (block n x)) = 1) : μ {fun _ => x 0} = 1 := by
  have hCm : ∀ (b : α) (j : ℤ), MeasurableSet {z : ℤ → α | z j = b} := fun b j =>
    show MeasurableSet ((fun z : ℤ → α => z j) ⁻¹' {b}) from
      measurable_pi_apply j (measurableSet_singleton b)
  have hshift : ∀ (b : α) (m : ℕ) (j : ℤ),
      μ {z : ℤ → α | z (m + j) = b} = μ {z : ℤ → α | z j = b} := fun b m j =>
    (measurePreserving_shift_natCast hinv m).measure_preimage (hCm b j).nullMeasurableSet
  have h1 : ∀ k : ℕ, μ {z : ℤ → α | z k = x k} = 1 := fun k =>
    le_antisymm prob_le_one ((hcyl (k + 1)).symm.le.trans
      (measure_mono fun z hz => hz ⟨k, Nat.lt_succ_self k⟩))
  have h2 : ∀ k : ℕ, μ {z : ℤ → α | z 0 = x k} = 1 := fun k => by
    rw [← hshift (x k) k 0, add_zero]
    exact h1 k
  have hG : μ (⋂ k : ℕ, {z : ℤ → α | z 0 = x k})ᶜ = 0 := by
    rw [compl_iInter]
    exact measure_iUnion_null fun k => (prob_compl_eq_zero_iff (hCm _ _)).2 (h2 k)
  obtain ⟨z₀, hz₀⟩ : (⋂ k : ℕ, {z : ℤ → α | z 0 = x k}).Nonempty := by
    apply nonempty_of_measure_ne_zero (μ := μ)
    rw [(prob_compl_eq_zero_iff (MeasurableSet.iInter fun k => hCm _ _)).1 hG]
    exact one_ne_zero
  have h3 : ∀ k : ℕ, x k = x 0 := fun k => by
    have hk : z₀ 0 = x k := mem_iInter.1 hz₀ k
    have h0 : z₀ 0 = x ((0 : ℕ) : ℤ) := mem_iInter.1 hz₀ 0
    rw [← hk, h0, Nat.cast_zero]
  have h0 : μ {z : ℤ → α | z 0 = x 0} = 1 := by
    have := h2 0
    rwa [Nat.cast_zero] at this
  have h4 : ∀ j : ℤ, μ {z : ℤ → α | z j = x 0} = 1 := by
    intro j
    rcases le_total 0 j with hj | hj
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hj
      have h := hshift (x 0) m 0
      rw [add_zero] at h
      rw [h, h0]
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 hj)
      have h := hshift (x 0) m j
      rw [show (m : ℤ) + j = 0 by omega] at h
      rw [← h, h0]
  have hsub : ({fun _ => x 0} : Set (ℤ → α))ᶜ ⊆ ⋃ j : ℤ, {z : ℤ → α | z j = x 0}ᶜ := by
    intro z hz
    by_contra hcon
    simp only [mem_iUnion, mem_compl_iff, mem_ofPred_eq, not_exists, not_not] at hcon
    exact hz (funext hcon)
  have hnull : μ ({fun _ => x 0} : Set (ℤ → α))ᶜ = 0 :=
    measure_mono_null hsub
      (measure_iUnion_null fun j => (prob_compl_eq_zero_iff (hCm _ _)).2 (h4 j))
  exact (prob_compl_eq_zero_iff (measurableSet_singleton _)).1 hnull

end Dirac

section General

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- `μ_x^ξ([x|_n]) > 0` for every `n` and `μ`-almost every `x` (Feng, Lemma 2.2). Hence the
logarithms in `thm:feng_entropy_as_limit` are logarithms of positive numbers. -/
theorem condMeas_cylinder_pos (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (ξ : (ℤ → α) → Set (ℤ → α)) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, 0 < condMeas μ ξ x (cylinder (block n x)) := by
  have h : ∀ᵐ x ∂μ, ∀ n : ℕ, ∀ w : Fin n → α,
      x ∈ cylinder w → 0 < condMeas μ ξ x (cylinder w) :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun w => condMeas_pos_of_mem μ ξ (measurableSet_cylinder w)
  filter_upwards [h] with x hx n
  exact hx n (block n x) fun _ => rfl

/-- The general form of `thm:feng_entropy_as_limit`: if the conditional measures of `ξ` satisfy
the first identity of Feng, Lemma 4.6, (4.16), then
`-n⁻¹ log μ_x^ξ([x|_n]) → E_μ(I_μ(𝒫 | \widehat{ξ}) | ℐ)(x)` for `μ`-almost every `x`. This is
Birkhoff's theorem `birkhoff_ae` for the integrable function `I_μ(𝒫 | \widehat{ξ})`. -/
theorem tendsto_neg_log_condMeas_cylinder {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) {ξ : (ℤ → α) → Set (ℤ → α)}
    (hsum : ∀ᵐ x ∂μ, ∀ n : ℕ, -Real.log ((condMeas μ ξ x).real (cylinder (block n x))) =
      ∑ k ∈ Finset.range n, condInfo μ ξ (shift k x)) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => -Real.log ((condMeas μ ξ x).real (cylinder (block n x))) / n)
      atTop (𝓝 (localEntropy μ ξ x)) := by
  filter_upwards [birkhoff_ae hinv (integrable_condInfo μ ξ), hsum] with x hx hs
  have hx' : Tendsto (fun n : ℕ => birkhoffAverage ℝ (shift 1) (condInfo μ ξ) n x) atTop
      (𝓝 (localEntropy μ ξ x)) := hx
  simp only [birkhoffAverage_shift_one] at hx'
  simpa only [hs] using hx'

/-- The vanishing step of `thm:feng_entropy_zero`: with `f = I_μ(𝒫 | \widehat{ξ})` and
`H = E_μ(f | ℐ)`, the set `E = {H = 0}` is invariant and `∫_E f dμ = ∫_E H dμ = 0`, so
`f(σ^k x) = 0` for every `k ≥ 0` and `μ`-almost every `x ∈ E`. -/
theorem condInfo_shift_eq_zero_of_localEntropy_eq_zero {μ : Measure (ℤ → α)}
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (ξ : (ℤ → α) → Set (ℤ → α)) :
    ∀ᵐ x ∂μ, localEntropy μ ξ x = 0 → ∀ k : ℕ, condInfo μ ξ (shift k x) = 0 := by
  have hle := MeasurableSpace.invariants_le (shift 1 : (ℤ → α) → ℤ → α)
  have hHm : Measurable[MeasurableSpace.invariants (shift 1 : (ℤ → α) → ℤ → α)]
      (localEntropy μ ξ) := stronglyMeasurable_condExp.measurable
  have hHinv : ∀ (k : ℕ) (x : ℤ → α), localEntropy μ ξ (shift k x) = localEntropy μ ξ x := by
    intro k x
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← ih, Nat.cast_succ, ← shift_shift]
      exact congrFun (MeasurableSpace.comp_eq_of_measurable_invariants hHm) (shift k x)
  have hE : MeasurableSet[MeasurableSpace.invariants (shift 1 : (ℤ → α) → ℤ → α)]
      (localEntropy μ ξ ⁻¹' {0}) := hHm (measurableSet_singleton 0)
  have hint : ∫ x in localEntropy μ ξ ⁻¹' {0}, condInfo μ ξ x ∂μ = 0 := by
    rw [← setIntegral_condExp hle (integrable_condInfo μ ξ) hE]
    exact setIntegral_eq_zero_of_forall_eq_zero fun x hx => hx
  have h0 : ∀ᵐ x ∂μ, localEntropy μ ξ x = 0 → condInfo μ ξ x = 0 :=
    (ae_restrict_iff' (hle _ hE)).1
      ((setIntegral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (condInfo_nonneg μ ξ))
        (integrable_condInfo μ ξ).integrableOn).1 hint)
  have h1 : ∀ᵐ x ∂μ, ∀ k : ℕ, localEntropy μ ξ (shift k x) = 0 →
      condInfo μ ξ (shift k x) = 0 :=
    ae_all_iff.2 fun k => (measurePreserving_shift_natCast hinv k).quasiMeasurePreserving.ae h0
  filter_upwards [h1] with x hx hH k
  exact hx k ((hHinv k x).trans hH)

/-- The vanishing step of `thm:feng_entropy_zero`, continued: where the pointwise entropy
vanishes, the first identity of Feng, Lemma 4.6, (4.16), gives `μ_x^ξ([x|_n]) = 1` for every
`n`. The positivity `condMeas_cylinder_pos` excludes the value `0`, at which Lean's logarithm
vanishes as well. -/
theorem condMeas_cylinder_eq_one_of_localEntropy_eq_zero {μ : Measure (ℤ → α)}
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    {ξ : (ℤ → α) → Set (ℤ → α)}
    (hsum : ∀ᵐ x ∂μ, ∀ n : ℕ, -Real.log ((condMeas μ ξ x).real (cylinder (block n x))) =
      ∑ k ∈ Finset.range n, condInfo μ ξ (shift k x)) :
    ∀ᵐ x ∂μ, localEntropy μ ξ x = 0 → ∀ n : ℕ, condMeas μ ξ x (cylinder (block n x)) = 1 := by
  filter_upwards [hsum, condInfo_shift_eq_zero_of_localEntropy_eq_zero hinv ξ,
    condMeas_cylinder_pos μ ξ] with x hs hf hpos hH n
  have hlog : Real.log ((condMeas μ ξ x).real (cylinder (block n x))) = 0 := by
    have h := hs n
    rw [Finset.sum_eq_zero fun k _ => hf hH k, neg_eq_zero] at h
    exact h
  have hpos' : 0 < (condMeas μ ξ x).real (cylinder (block n x)) :=
    ENNReal.toReal_pos (hpos n).ne' (measure_ne_top _ _)
  have h1 : (condMeas μ ξ x).real (cylinder (block n x)) = 1 :=
    Real.eq_one_of_pos_of_log_eq_zero hpos' hlog
  rwa [measureReal_def, ENNReal.toReal_eq_one_iff] at h1

/-- The general form of `thm:feng_entropy_zero`: if the conditional measures of `ξ` satisfy the
first identity of Feng, Lemma 4.6, (4.16), and a conditional measure that gives mass one to all
cylinders `[x|_n]` is carried by the points with the past of `x`, then
`E_μ(I_μ(𝒫 | \widehat{ξ}) | ℐ)(x) = 0 ↔ μ_x^ξ = δ_x` for `μ`-almost every `x`. Ergodicity is not
assumed. For the converse, a Dirac conditional measure gives the limit zero in
`tendsto_neg_log_condMeas_cylinder`. -/
theorem localEntropy_eq_zero_iff_condMeas_eq_dirac {μ : Measure (ℤ → α)}
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    {ξ : (ℤ → α) → Set (ℤ → α)}
    (hsum : ∀ᵐ x ∂μ, ∀ n : ℕ, -Real.log ((condMeas μ ξ x).real (cylinder (block n x))) =
      ∑ k ∈ Finset.range n, condInfo μ ξ (shift k x))
    (hpast : ∀ᵐ x ∂μ, (∀ n : ℕ, condMeas μ ξ x (cylinder (block n x)) = 1) →
      condMeas μ ξ x {y | SamePast y x} = 1) :
    ∀ᵐ x ∂μ, localEntropy μ ξ x = 0 ↔ condMeas μ ξ x = Measure.dirac x := by
  filter_upwards [tendsto_neg_log_condMeas_cylinder hinv hsum,
    condMeas_cylinder_eq_one_of_localEntropy_eq_zero hinv hsum, hpast] with x hlim hcyl hp
  constructor
  · intro hH
    exact eq_dirac_of_cylinder_of_samePast (hcyl hH) (hp (hcyl hH))
  · intro hd
    have hone : ∀ n : ℕ, (condMeas μ ξ x).real (cylinder (block n x)) = 1 := fun n => by
      rw [hd, measureReal_def,
        Measure.dirac_apply_of_mem (show x ∈ cylinder (block n x) from fun _ => rfl),
        ENNReal.toReal_one]
    simp only [hone, Real.log_one, neg_zero, zero_div] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds

end General

/-! ### `thm:feng_entropy_as_limit` and `thm:feng_entropy_zero` -/

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι)

/-- The conditional measures of the planar partitions are carried by the points with the past of
`𝐢`, in the form `localEntropy_eq_zero_iff_condMeas_eq_dirac` needs: if `μ_𝐢^{ξ_i}` gives mass
one to every cylinder `[𝐢|_n]`, then it gives mass one to `{𝐣 : 𝐣^- = 𝐢^-}`, for `μ`-almost every
`𝐢`. The set `Σ'` is invariant, so `μ(Σ') ∈ {0, 1}` for ergodic `μ`. If `μ(Σ') = 1`, the atoms
`ξ_i(𝐢)` have fixed past and `condMeas_atom` applies. If `μ(Σ') = 0`, the conditional measures
are `μ`, and `μ` is the Dirac mass at a constant sequence as soon as it gives mass one to all
cylinders of one point. -/
theorem condMeas_xi_samePast (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ) (i : ℕ) :
    ∀ᵐ x ∂μ, (∀ n : ℕ, condMeas μ (S.xi μ i) x (cylinder (block n x)) = 1) →
      condMeas μ (S.xi μ i) x {y | SamePast y x} = 1 := by
  have hpre : shift 1 ⁻¹' S.SigmaPrime μ = S.SigmaPrime μ := by
    ext x
    exact S.shift_mem_SigmaPrime_iff μ x
  rcases herg.toPreErgodic.measure_self_or_compl_eq_zero (S.measurableSet_SigmaPrime μ) hpre
    with h | h
  · have hc : ∀ᵐ x ∂μ, condMeas μ (S.xi μ i) x = μ := condMeas_atomsOn_of_measure_eq_zero μ h _
    by_cases hex : ∃ x₀ : ℤ → ι, ∀ n : ℕ, μ (cylinder (block n x₀)) = 1
    · obtain ⟨x₀, hx₀⟩ := hex
      have h1 := measure_singleton_const_of_cylinder hinv hx₀
      have hae : ∀ᵐ x ∂μ, x ∈ ({fun _ => x₀ 0} : Set (ℤ → ι)) :=
        (measure_eq_zero_iff_ae_notMem.1
          ((prob_compl_eq_zero_iff (measurableSet_singleton _)).2 h1)).mono
          fun x hx => not_not.1 hx
      filter_upwards [hc, hae] with x hx hxc _
      rw [hx]
      refine le_antisymm prob_le_one (h1.symm.le.trans (measure_mono ?_))
      rw [mem_singleton_iff] at hxc
      rw [hxc]
      exact singleton_subset_iff.2 (SamePast.refl _)
    · filter_upwards [hc] with x hx hcyl
      exact absurd ⟨x, fun n => hx ▸ hcyl n⟩ hex
  · have hsub : ∀ᵐ x ∂μ, S.xi μ i x ⊆ {y | SamePast y x} := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h] with x hx
      rw [xi, atomsOn_of_mem (not_not.1 hx)]
      exact fun y hy => hy.1.1
    exact (condMeas_eq_one_of_atom_subset μ (S.isMeasurablePartition_xi μ i) hsub).mono
      fun x hx _ => hx

/-- "The conditional measure is supported on an atom with fixed past" (proof of
`thm:feng_entropy_zero`) for the projective system: for a measure `ν` carried by `Σ_Z`,
`ν_𝐢^{\overline{ξ}_i}` gives mass one to `{𝐣 : 𝐣^- = 𝐢^-}` for `ν`-almost every `𝐢`. -/
theorem condMeas_xiBar_samePast (ν : Measure (ℤ → ι × ZMod 2)) [IsFiniteMeasure ν]
    (hsupp : ν (subshift S.o)ᶜ = 0) (i : ℕ) :
    ∀ᵐ y ∂ν, condMeas ν (S.xiBar i) y {z | SamePast z y} = 1 := by
  refine condMeas_eq_one_of_atom_subset ν (S.isMeasurablePartition_xiBar i) ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hsupp] with y hy
  rcases i with _ | i
  · simp only [xiBar, atomsOn_of_mem (not_not.1 hy)]
    exact fun z hz => hz.1
  · simp only [xiBar, atomsOn_of_mem (not_not.1 hy)]
    exact fun z hz => hz.1.1

/-- `thm:feng_entropy_as_limit`, first part; Feng, Lemma 4.6, second identity of
(4.16): for ergodic `μ` with `λ_2 < λ_1` and `i ∈ {0, 1, 2}`,
`h_i(μ, 𝐢) = -lim_n n⁻¹ log μ_𝐢^{ξ_i}(𝒫_0^{n-1}(𝐢))` for `μ`-almost every `𝐢`. The article states
it for a planar self-affine set; here the system is box-like and `Σ'`, `V_𝐢^1` have their
box-like form. It follows from the first identity `FengInfoSum` of (4.16) and Birkhoff's
theorem `birkhoff_ae`. -/
theorem feng_entropy_as_limit (hfi : FengInfoSum.{u}) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) (i : ℕ) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => -Real.log ((condMeas μ (S.xi μ i) x).real (cylinder (block n x))) / n)
      atTop (𝓝 (S.dimEntropyAt μ i x)) :=
  tendsto_neg_log_condMeas_cylinder hinv (hfi S μ hinv herg hlt i)

/-- `thm:feng_entropy_as_limit`, second part; Feng, Lemma 4.6, for the projective
system: for every invariant `ν` on `Σ_Z` and `i ∈ {0, 1}`,
`\overline{h}_i(ν, 𝐢) = -lim_n n⁻¹ log ν_𝐢^{\overline{ξ}_i}(\overline{𝒫}_0^{n-1}(𝐢))` for
`ν`-almost every `𝐢`. Ergodicity is not assumed. It follows from `FengInfoSumBar` and
`birkhoff_ae`. -/
theorem feng_entropy_as_limit_bar (hfib : FengInfoSumBar.{u}) (hrot : S.WithRotations)
    (hprox : S.Proximal) (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν]
    (hinv : MeasurePreserving (shift 1) ν ν) (hsupp : ν (subshift S.o)ᶜ = 0) (i : ℕ) :
    ∀ᵐ y ∂ν, Tendsto
      (fun n : ℕ => -Real.log ((condMeas ν (S.xiBar i) y).real (cylinder (block n y))) / n)
      atTop (𝓝 (S.dimEntropyBarAt ν i y)) :=
  tendsto_neg_log_condMeas_cylinder hinv (hfib S hrot hprox ν hinv hsupp i)

/-- `thm:feng_entropy_zero`, planar part: for ergodic `μ` with `λ_2 < λ_1` and
`i ∈ {0, 1, 2}`, `h_i(μ, 𝐢) = 0 ↔ μ_𝐢^{ξ_i} = δ_𝐢` for `μ`-almost every `𝐢`.
Depends on: `FengInfoSum`, `thm:feng_entropy_as_limit`, `condMeas_atom`. -/
theorem feng_entropy_zero (hfi : FengInfoSum.{u}) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) (i : ℕ) :
    ∀ᵐ x ∂μ, S.dimEntropyAt μ i x = 0 ↔ condMeas μ (S.xi μ i) x = Measure.dirac x :=
  localEntropy_eq_zero_iff_condMeas_eq_dirac hinv (hfi S μ hinv herg hlt i)
    (S.condMeas_xi_samePast μ hinv herg i)

/-- `thm:feng_entropy_zero`, scalar part: for every invariant `ν` on `Σ_Z`, ergodic or
not, and `i ∈ {0, 1}`, `\overline{h}_i(ν, 𝐢) = 0 ↔ ν_𝐢^{\overline{ξ}_i} = δ_𝐢` for `ν`-almost
every `𝐢`.
Depends on: `FengInfoSumBar`, `thm:feng_entropy_as_limit`, `condMeas_atom`. -/
theorem feng_entropy_zero_bar (hfib : FengInfoSumBar.{u}) (hrot : S.WithRotations)
    (hprox : S.Proximal) (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν]
    (hinv : MeasurePreserving (shift 1) ν ν) (hsupp : ν (subshift S.o)ᶜ = 0) (i : ℕ) :
    ∀ᵐ y ∂ν, S.dimEntropyBarAt ν i y = 0 ↔
      condMeas ν (S.xiBar i) y = Measure.dirac y :=
  localEntropy_eq_zero_iff_condMeas_eq_dirac hinv (hfib S hrot hprox ν hinv hsupp i)
    ((S.condMeas_xiBar_samePast ν hsupp i).mono fun _ hy _ => hy)

end System

end BoxLike
