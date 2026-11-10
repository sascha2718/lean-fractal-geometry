module

/-
`thm:irred_eq_state` for `s ≥ 2` and an arbitrary tuple `𝖠 = (A_1, …, A_N)` of invertible
planar matrices, by the determinant calculation of `thm:bernoulli_equilibrium` (tex lines 2257
to 2395). For `s ≥ 2` the singular value function `φ^s(A) = |det A|^{s/2}` is multiplicative,
the pressure is `log ∑_i |det A_i|^{s/2}`, and the unique `s`-equilibrium state is the Bernoulli
measure with the weights `p_i = |det A_i|^{s/2} / ∑_j |det A_j|^{s/2}`; it is ergodic and has
the Gibbs bounds with the constant `C = 1`. Irreducibility is not needed.

* `MatrixTuple.svfSum_of_two_le`, `MatrixTuple.pressure_of_two_le`: `P(𝖠, s) = log ∑_i
  |det A_i|^{s/2}`.
* `MatrixTuple.energyLim_of_two_le`: `Λ(𝖠, μ, s) = (s/2) ∑_i μ([i]) log |det A_i|` for an
  invariant `μ`.
* `MatrixTuple.detWeight`, `MatrixTuple.detWeightMeasure`: the weights `p_i` and the measure
  `∑_i p_i δ_i`.
* `MatrixTuple.isEquilibriumState_bernoulli`, `MatrixTuple.IsEquilibriumState.eq_bernoulli`:
  the Bernoulli measure is an `s`-equilibrium state, and every invariant `s`-equilibrium state
  is this Bernoulli measure.
* `MatrixTuple.hasGibbsBounds_bernoulli`: `μ([𝐢]) = exp(-|𝐢| P(𝖠, s)) φ^s(A_𝐢)`.
* `MatrixTuple.irred_eq_state_of_two_le`: existence, uniqueness, ergodicity and the Gibbs
  bounds for `s ≥ 2`.
* `System.detWeightMeasure_eq_tuple`, `System.hasGibbsBounds_bernoulli`: the specialisation to
  box-like systems.
-/
public import BoxLike.BernoulliEquilibrium
public import BoxLike.TupleEquilibrium

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

namespace MatrixTuple

variable {ι : Type*} [Fintype ι] (A : ι → Matrix (Fin 2) (Fin 2) ℝ) {s : ℝ}

/-! ### The pressure for `s ≥ 2` -/

/-- For `s ≥ 2` the sums `∑_{|𝐢| = n} φ^s(A_𝐢)` are multiplicative in `n`. -/
theorem svfSum_add_of_two_le (hs : 2 ≤ s) (m n : ℕ) :
    svfSum A s (m + n) = svfSum A s m * svfSum A s n := by
  rw [svfSum, sum_ofFn_add m n fun w => svf s (word A w), svfSum, svfSum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => ?_
  rw [word_append, svf_mul_of_two_le hs]

/-- The sum over the words of length one is `∑_i |det A_i|^{s/2}` for `s ≥ 2`. -/
theorem svfSum_one_of_two_le (hs : 2 ≤ s) : svfSum A s 1 = ∑ i, |(A i).det| ^ (s / 2) := by
  rw [svfSum]
  refine (Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι).symm _ _ fun i => ?_).symm
  rw [svf_of_two_le hs]
  simp [word]

/-- `∑_{|𝐢| = n} φ^s(A_𝐢) = (∑_i |det A_i|^{s/2})^n` for `s ≥ 2`. -/
theorem svfSum_of_two_le (hs : 2 ≤ s) (n : ℕ) :
    svfSum A s n = (∑ i, |(A i).det| ^ (s / 2)) ^ n := by
  induction n with
  | zero => simp [svfSum, svf_of_two_le hs]
  | succ n ih => rw [svfSum_add_of_two_le A hs, ih, svfSum_one_of_two_le A hs, pow_succ]

/-- For `s ≥ 2` the pressure is `log ∑_i |det A_i|^{s/2}`, tex line 2258. -/
theorem pressure_of_two_le (hs : 2 ≤ s) :
    pressure A s = Real.log (∑ i, |(A i).det| ^ (s / 2)) := by
  have h : (fun n : ℕ => Real.log (svfSum A s n) / n) '' Set.Ici 1 =
      {Real.log (∑ i, |(A i).det| ^ (s / 2))} := by
    ext t
    simp only [Set.mem_image, Set.mem_Ici, Set.mem_singleton_iff]
    constructor
    · rintro ⟨n, hn, rfl⟩
      rw [svfSum_of_two_le A hs, Real.log_pow,
        mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 hn))]
    · rintro rfl
      exact ⟨1, le_rfl, by rw [svfSum_of_two_le A hs]; simp⟩
  rw [pressure, h, csInf_singleton]

/-! ### The energy for `s ≥ 2` -/

variable {A}

omit [Fintype ι] in
/-- `log |det A_{𝐢|_n}| = ∑_{k<n} log |det A_{i_k}|`. -/
theorem log_abs_det_word_futureWord (hA : ∀ i, (A i).det ≠ 0) (x : ℤ → ι) (n : ℕ) :
    Real.log |(word A (futureWord x n)).det| =
      ∑ k ∈ Finset.range n, Real.log |(A (x k)).det| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [futureWord_succ, log_abs_det_word_append hA, ih, Finset.sum_range_succ]
    simp [word]

variable [MeasurableSpace ι] [MeasurableSingletonClass ι] {μ : Measure (ℤ → ι)}
  [IsProbabilityMeasure μ]

/-- For an invariant measure every coordinate has the same distribution:
`∫ log |det A_{i_k}| dμ(𝐢) = ∑_i μ([i]) log |det A_i|`. -/
theorem integral_log_abs_det_apply (hμ : MeasurePreserving (shift 1) μ μ) (k : ℕ) :
    ∫ x, Real.log |(A (x k)).det| ∂μ = ∑ i, μ.real (cylinder ![i]) * Real.log |(A i).det| := by
  have h := integral_comp_shift hμ k (F := fun x => Real.log |(A (x 0)).det|)
    ((Measurable.of_discrete (f := fun i : ι => Real.log |(A i).det|)).comp
      (measurable_pi_apply 0))
  simp only [shift_apply, add_zero] at h
  rw [h, integral_comp_apply_zero μ fun i => Real.log |(A i).det|]

/-- `Λ(𝖠, μ, s) = (s/2) ∑_i μ([i]) log |det A_i|` for `s ≥ 2` and an invariant measure `μ`: the
potential `log φ^s(A_𝐢) = (s/2) log |det A_𝐢|` is additive. -/
theorem energyLim_of_two_le (hA : ∀ i, (A i).det ≠ 0) (hμ : MeasurePreserving (shift 1) μ μ)
    (hs : 2 ≤ s) :
    energyLim A s μ = s / 2 * ∑ i, μ.real (cylinder ![i]) * Real.log |(A i).det| := by
  refine Tendsto.limUnder_eq (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hint : ∀ k : ℕ, Integrable (fun x : ℤ → ι => Real.log |(A (x k)).det|) μ :=
    fun k =>
      (Integrable.of_finite (f := fun i : ι => Real.log |(A i).det|)).comp_measurable
        (measurable_pi_apply (k : ℤ))
  have e : ∀ x : ℤ → ι, Real.log (svf s (word A (futureWord x n))) =
      s / 2 * ∑ k ∈ Finset.range n, Real.log |(A (x k)).det| := fun x => by
    rw [svf_of_two_le hs, Real.log_rpow (abs_det_word_pos hA _),
      log_abs_det_word_futureWord hA]
  simp only [e]
  rw [integral_const_mul, integral_finsetSum _ fun k _ => hint k,
    Finset.sum_congr rfl fun k _ => integral_log_abs_det_apply hμ k, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_left_comm, mul_div_cancel_left₀ _
      (Nat.cast_ne_zero.2 hn)]

/-- The equilibrium equation for `s ≥ 2`:
`log ∑_i |det A_i|^{s/2} = h_0(μ) + (s/2) ∑_i μ([i]) log |det A_i|`. -/
theorem IsEquilibriumState.log_sum_eq (hA : ∀ i, (A i).det ≠ 0)
    (heq : IsEquilibriumState A s μ) (hμ : MeasurePreserving (shift 1) μ μ) (hs : 2 ≤ s) :
    Real.log (∑ i, |(A i).det| ^ (s / 2)) =
      entropy μ + s / 2 * ∑ i, μ.real (cylinder ![i]) * Real.log |(A i).det| := by
  rw [← pressure_of_two_le A hs, ← energyLim_of_two_le hA hμ hs]
  exact heq

end MatrixTuple

/-! ### The Bernoulli equilibrium state -/

namespace MatrixTuple

variable {ι : Type*} [Fintype ι] (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ)

/-- The weights `p_i = |det A_i|^{s/2} / ∑_j |det A_j|^{s/2}` of tex line 2261. -/
noncomputable def detWeight (i : ι) : ℝ :=
  |(A i).det| ^ (s / 2) / ∑ j, |(A j).det| ^ (s / 2)

variable {A}

omit [Fintype ι] in
/-- `|det A_i|^t > 0`. -/
theorem rpow_abs_det_pos (hA : ∀ i, (A i).det ≠ 0) (t : ℝ) (i : ι) : 0 < |(A i).det| ^ t :=
  Real.rpow_pos_of_pos (abs_pos.2 (hA i)) t

/-- The weights `p_i` are positive. -/
theorem detWeight_pos (hA : ∀ i, (A i).det ≠ 0) (i : ι) : 0 < detWeight A s i :=
  div_pos (rpow_abs_det_pos hA _ i)
    (Finset.sum_pos (fun j _ => rpow_abs_det_pos hA _ j) ⟨i, Finset.mem_univ i⟩)

/-- The weights `p_i` form a probability vector. -/
theorem sum_detWeight [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) : ∑ i, detWeight A s i = 1 := by
  simp only [detWeight]
  rw [← Finset.sum_div]
  exact div_self (Finset.sum_pos (fun j _ => rpow_abs_det_pos hA _ j) Finset.univ_nonempty).ne'

variable (A) [MeasurableSpace ι]

/-- The probability vector `(p_i)` as the measure `∑_i p_i δ_i` on the alphabet. -/
noncomputable def detWeightMeasure : Measure ι := weightMeasure (detWeight A s)

variable {A}

/-- The measure `∑_i p_i δ_i` is a probability measure on a non-empty alphabet. -/
theorem isProbabilityMeasure_detWeightMeasure [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) :
    IsProbabilityMeasure (detWeightMeasure A s) :=
  isProbabilityMeasure_weightMeasure (fun i => (detWeight_pos s hA i).le) (sum_detWeight s hA)

variable [MeasurableSingletonClass ι]

/-- The measure `∑_i p_i δ_i` gives the symbol `i` the mass `p_i`. -/
theorem measureReal_detWeightMeasure_singleton (hA : ∀ i, (A i).det ≠ 0) (i : ι) :
    (detWeightMeasure A s).real {i} = detWeight A s i :=
  measureReal_weightMeasure_singleton (detWeight_pos s hA i).le

variable {s}

/-- For `s ≥ 2` the Bernoulli measure with the weights `p_i` is an `s`-equilibrium state, tex
lines 2385 to 2394: its entropy is `∑_i -p_i log p_i`, its energy `∑_i p_i log |det A_i|^{s/2}`,
and the sum is `log ∑_i |det A_i|^{s/2} = P(𝖠, s)`. -/
theorem isEquilibriumState_bernoulli [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) (hs : 2 ≤ s) :
    IsEquilibriumState A s (bernoulli (detWeightMeasure A s)) := by
  have := isProbabilityMeasure_detWeightMeasure s hA
  have hinv := measurePreserving_shift_bernoulli (detWeightMeasure A s) 1
  have hcyl : ∀ i, (bernoulli (detWeightMeasure A s)).real (cylinder ![i]) = detWeight A s i :=
    fun i => by
      rw [measureReal_bernoulli_cylinder, Fin.prod_univ_one, Matrix.cons_val_zero,
        measureReal_detWeightMeasure_singleton s hA]
  have hdefect := sum_gibbs_defect (p := detWeight A s) (q := fun i => |(A i).det| ^ (s / 2))
    (sum_detWeight s hA) (rpow_abs_det_pos hA _)
  have hzero : ∀ i, |(A i).det| ^ (s / 2) / ∑ j, |(A j).det| ^ (s / 2)
      - detWeight A s i - (Real.negMulLog (detWeight A s i) + detWeight A s i
        * Real.log (|(A i).det| ^ (s / 2) / ∑ j, |(A j).det| ^ (s / 2))) = 0 :=
    fun i => by
      rw [← detWeight, Real.negMulLog]
      ring
  rw [Finset.sum_congr rfl fun i _ => hzero i, Finset.sum_const_zero] at hdefect
  have hlog : ∀ i, Real.log (|(A i).det| ^ (s / 2)) = s / 2 * Real.log |(A i).det| :=
    fun i => Real.log_rpow (abs_pos.2 (hA i)) _
  show pressure A s = entropy _ + energyLim A s _
  rw [pressure_of_two_le A hs, energyLim_of_two_le hA hinv hs, entropy_bernoulli,
    Finset.mul_sum]
  simp only [hcyl, measureReal_detWeightMeasure_singleton s hA]
  simp only [hlog] at hdefect
  have e : ∀ i, s / 2 * (detWeight A s i * Real.log |(A i).det|) =
      detWeight A s i * (s / 2 * Real.log |(A i).det|) := fun i => by ring
  simp only [e]
  linarith

/-- For `s ≥ 2` every invariant `s`-equilibrium state is the Bernoulli measure with the weights
`p_i`, tex lines 2267 to 2275: the entropy is at most the entropy of the one-symbol
distribution, with equality only for a Bernoulli measure, and Gibbs' inequality is an equality
only for `(p_i)`. -/
theorem IsEquilibriumState.eq_bernoulli (hA : ∀ i, (A i).det ≠ 0) {μ : Measure (ℤ → ι)}
    [IsProbabilityMeasure μ] (heq : IsEquilibriumState A s μ)
    (hinv : MeasurePreserving (shift 1) μ μ) (hs : 2 ≤ s) :
    μ = bernoulli (detWeightMeasure A s) := by
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
  have := isProbabilityMeasure_detWeightMeasure s hA
  have hq := rpow_abs_det_pos hA (s / 2)
  have hE := heq.log_sum_eq hA hinv hs
  have hrw : s / 2 * ∑ i, μ.real (cylinder ![i]) * Real.log |(A i).det| =
      ∑ i, μ.real (cylinder ![i]) * Real.log (|(A i).det| ^ (s / 2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.log_rpow (abs_pos.2 (hA i))]
    ring
  rw [hrw] at hE
  have hG := blockEntropy_one_add_sum_le μ (fun i => |(A i).det| ^ (s / 2)) hq
  have hH := entropy_le_blockEntropy_one hinv
  have hent : entropy μ = blockEntropy μ 1 := by linarith
  have hGeq : blockEntropy μ 1
      + ∑ i, μ.real (cylinder ![i]) * Real.log (|(A i).det| ^ (s / 2)) =
      Real.log (∑ i, |(A i).det| ^ (s / 2)) := by linarith
  refine eq_bernoulli_of_measureReal_cylinder _ fun k n w => ?_
  rw [measureReal_preimage_shift_cylinder_eq_prod_of_entropy_eq hinv hent k w]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [measureReal_cylinder_eq_of_blockEntropy_one_add_sum_eq μ _ hq hGeq,
    measureReal_detWeightMeasure_singleton s hA, detWeight]

/-- The Gibbs bounds of `thm:irred_eq_state` for `s ≥ 2`, with the constant `C = 1`:
`μ([𝐢]) = ∏_j p_{i_j} = exp(-|𝐢| P(𝖠, s)) φ^s(A_𝐢)`, since
`φ^s(A_𝐢) = ∏_j |det A_{i_j}|^{s/2}`. -/
theorem hasGibbsBounds_bernoulli [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) (hs : 2 ≤ s) :
    HasGibbsBounds A s (bernoulli (detWeightMeasure A s)) := by
  have := isProbabilityMeasure_detWeightMeasure s hA
  have hZ : 0 < ∑ j, |(A j).det| ^ (s / 2) :=
    Finset.sum_pos (fun j _ => rpow_abs_det_pos hA _ j) Finset.univ_nonempty
  have hsvf : ∀ (n : ℕ) (w : Fin n → ι),
      svf s (word A (List.ofFn w)) = ∏ j, |(A (w j)).det| ^ (s / 2) := by
    intro n w
    induction n with
    | zero => simp [svf_of_two_le hs]
    | succ n ih =>
      rw [List.ofFn_succ, word_cons, svf_mul_of_two_le hs, ih, Fin.prod_univ_succ,
        svf_of_two_le hs]
  have key : ∀ (n : ℕ) (w : Fin n → ι), (bernoulli (detWeightMeasure A s)).real (cylinder w) =
      Real.exp (-(n * pressure A s)) * svf s (word A (List.ofFn w)) := by
    intro n w
    rw [measureReal_bernoulli_cylinder, pressure_of_two_le A hs, hsvf, neg_mul_eq_mul_neg,
      ← Real.log_inv, ← Real.log_rpow (inv_pos.2 hZ), Real.exp_log (Real.rpow_pos_of_pos
        (inv_pos.2 hZ) _), Real.rpow_natCast, Finset.prod_congr rfl fun j _ =>
        measureReal_detWeightMeasure_singleton s hA (w j)]
    simp only [detWeight, div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    ring
  refine ⟨1, le_rfl, fun n _ w => ?_⟩
  rw [key, inv_one, one_mul]
  exact ⟨le_rfl, le_rfl⟩

/-- `thm:irred_eq_state` for `s ≥ 2` and every tuple of invertible planar matrices, with no
irreducibility hypothesis and no literature input: the Bernoulli measure with the weights
`p_i = |det A_i|^{s/2} / ∑_j |det A_j|^{s/2}` is an `s`-equilibrium state, every invariant
`s`-equilibrium state equals it, it is ergodic, and it has the Gibbs bounds. -/
theorem irred_eq_state_of_two_le [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) (hs : 2 ≤ s) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
      IsEquilibriumState A s μ ∧
      (∀ ν : Measure (ℤ → ι), IsProbabilityMeasure ν → MeasurePreserving (shift 1) ν ν →
        IsEquilibriumState A s ν → ν = μ) ∧
      Ergodic (shift 1) μ ∧ HasGibbsBounds A s μ := by
  have := isProbabilityMeasure_detWeightMeasure s hA
  exact ⟨bernoulli (detWeightMeasure A s), inferInstance,
    measurePreserving_shift_bernoulli _ 1, isEquilibriumState_bernoulli hA hs,
    fun ν hν hinv heq => haveI := hν; heq.eq_bernoulli hA hinv hs,
    ergodic_shift_bernoulli _, hasGibbsBounds_bernoulli hA hs⟩

end MatrixTuple

namespace System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] (S : System ι) (s : ℝ)

/-- The Bernoulli equilibrium state of a box-like system for `s ≥ 2` is that of the tuple
`S.mat`. -/
theorem detWeightMeasure_eq_tuple :
    S.detWeightMeasure s = MatrixTuple.detWeightMeasure S.mat s := rfl

variable [MeasurableSingletonClass ι] [Nonempty ι] {s}

/-- The Gibbs bounds of `thm:irred_eq_state` for `s ≥ 2` and a box-like system, with the
constant `C = 1`. -/
theorem hasGibbsBounds_bernoulli (hs : 2 ≤ s) :
    S.HasGibbsBounds s (bernoulli (S.detWeightMeasure s)) :=
  MatrixTuple.hasGibbsBounds_bernoulli S.det_mat_ne_zero hs

end System

end BoxLike
