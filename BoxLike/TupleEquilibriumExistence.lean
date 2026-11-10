module

/-
The existence part of `thm:irred_eq_state` for an arbitrary tuple `𝖠 = (A_1, …, A_N)` of
invertible planar matrices and every `s ≥ 0`, with no irreducibility hypothesis (tex lines 2105
to 2218; Käenmäki, Ann. Acad. Sci. Fenn. Math. 29 (2004), Theorem 2.6, and, for sub-additive
potentials, Cao–Feng–Huang, Discrete Contin. Dyn. Syst. 20 (2008), Theorem 1.1). The proof is
Misiurewicz's construction of `BoxLike/EquilibriumExistence.lean` for the tuple: the weights
`φ^s(A_𝐢) / ∑_{|𝐣| = n} φ^s(A_𝐣)` on the words of length `n` give a Bernoulli measure on the
blocks of length `n`, its image under the concatenation of blocks is invariant under `σ^n`, and
the average of its first `n` translates is invariant under `σ`. Along a weak-star limit of these
measures the block averages of the entropy and of the energy are at least `P(𝖠, s)`, and their
limits are `h_0(μ)` and `Λ(𝖠, μ, s)`.

* `MatrixTuple.blockEnergy`, `MatrixTuple.blockEnergy_add_le`: the energy at level `n` and its
  sub-additivity in the length, with the second term taken for a translate.
* `MatrixTuple.exists_blockBound`: `|H_μ(𝒫_0^{l-1}) + ∫ log φ^s(A_{𝐢|_l}) dμ| ≤ l C` for every
  probability measure.
* `MatrixTuple.blockWeight`, `MatrixTuple.blockMeasure`, `MatrixTuple.avgBlockMeasure`: the
  weights, the image of the Bernoulli measure with these weights under the concatenation, and
  the average of its translates, which is invariant.
* `MatrixTuple.blockSum`, `MatrixTuple.log_svfSum_le_avgBlockMeasure`: the Misiurewicz estimate
  `m log ∑_{|𝐢| = n} φ^s(A_𝐢) ≤ n (H + energy at level m) + 5 m² C`.
* `MatrixTuple.exists_invariant_pressure_le`: an invariant probability measure with
  `P(𝖠, s) ≤ h_0(μ) + Λ(𝖠, μ, s)`.
* `MatrixTuple.exists_isEquilibriumState`: an `s`-equilibrium state exists for every `s ≥ 0`.
* `System.exists_isEquilibriumState_eq_tuple`: the specialisation to box-like systems.
-/
public import BoxLike.EquilibriumExistence
public import BoxLike.TupleEquilibrium

@[expose] public section

namespace BoxLike

open Filter MeasureTheory Topology
open scoped ENNReal Matrix.Norms.L2Operator

namespace MatrixTuple

variable {ι : Type*} [Fintype ι] {A : ι → Matrix (Fin 2) (Fin 2) ℝ} {s : ℝ}

variable (A s) in
/-- `∑_{|𝐢| = 0} φ^s(A_𝐢) = 1`: the empty word is the only word of length zero. -/
theorem svfSum_zero : svfSum A s 0 = 1 := by
  rw [svfSum, Fintype.sum_unique, List.ofFn_zero, word_nil, svf_one]

/-- `log ∑_{|𝐢| = l} φ^s(A_𝐢) ≤ l log ∑_i φ^s(A_i)`, by sub-multiplicativity. -/
theorem log_svfSum_le [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) (hs : 0 ≤ s) (l : ℕ) :
    Real.log (svfSum A s l) ≤ l * Real.log (svfSum A s 1) := by
  induction l with
  | zero => simp [svfSum_zero]
  | succ l ih =>
    have h1 := svfSum_pos hA s l
    have h2 := svfSum_pos hA s 1
    have h := Real.log_le_log (svfSum_pos hA s (l + 1)) (svfSum_add_le A hs l 1)
    rw [Real.log_mul h1.ne' h2.ne'] at h
    push_cast
    linarith

/-! ### The energy at level `n` -/

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

variable (A) in
/-- The energy at level `n`: the integral `∫ log φ^s(A_{𝐢|_n}) dμ(𝐢)` of `eq:energy_def`
before the passage to the limit, written as a sum over the cylinders of length `n`. -/
noncomputable def blockEnergy (s : ℝ) (μ : Measure (ℤ → ι)) (n : ℕ) : ℝ :=
  ∑ w : Fin n → ι, μ.real (cylinder w) * Real.log (svf s (word A (List.ofFn w)))

/-- The energy at level `n` is the integral `∫ log φ^s(A_{𝐢|_n}) dμ(𝐢)`. -/
theorem blockEnergy_eq_integral (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] (n : ℕ) :
    blockEnergy A s μ n = ∫ x, Real.log (svf s (word A (futureWord x n))) ∂μ :=
  (integral_comp_futureWord_eq_sum μ (fun w => Real.log (svf s (word A w))) n).symm

/-- The energies at level `n` are sub-additive in the length, by sub-multiplicativity of `φ^s`,
provided the second term is taken for the translate `(σ^m)_*μ`. -/
theorem blockEnergy_add_le (hA : ∀ i, (A i).det ≠ 0) (hs : 0 ≤ s) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (m n : ℕ) :
    blockEnergy A s μ (m + n)
      ≤ blockEnergy A s μ m + blockEnergy A s (μ.map (shift (m : ℤ))) n := by
  have e1 : ∑ w : Fin m → ι, ∑ w' : Fin n → ι, μ.real (cylinder (Fin.append w w'))
        * Real.log (svf s (word A (List.ofFn w)))
      = blockEnergy A s μ m :=
    Finset.sum_congr rfl fun w _ => by
      rw [← Finset.sum_mul, sum_measureReal_cylinder_append_right]
  have e2 : ∑ w : Fin m → ι, ∑ w' : Fin n → ι, μ.real (cylinder (Fin.append w w'))
        * Real.log (svf s (word A (List.ofFn w')))
      = blockEnergy A s (μ.map (shift (m : ℤ))) n := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun w' _ => by
      rw [← Finset.sum_mul, sum_measureReal_cylinder_append_left']
  calc blockEnergy A s μ (m + n)
      = ∑ w : Fin m → ι, ∑ w' : Fin n → ι, μ.real (cylinder (Fin.append w w'))
          * Real.log (svf s (word A (List.ofFn (Fin.append w w')))) := sum_fin_append _
    _ ≤ ∑ w : Fin m → ι, ∑ w' : Fin n → ι, (μ.real (cylinder (Fin.append w w'))
          * Real.log (svf s (word A (List.ofFn w)))
          + μ.real (cylinder (Fin.append w w'))
            * Real.log (svf s (word A (List.ofFn w')))) :=
        Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun w' _ => by
          rw [← mul_add]
          refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
          rw [List.ofFn_fin_append]
          exact log_svf_word_append_le hA hs _ _
    _ = blockEnergy A s μ m + blockEnergy A s (μ.map (shift (m : ℤ))) n := by
        simp only [Finset.sum_add_distrib]
        rw [e1, e2]

/-- Gibbs' inequality at level `n`: `H_μ(𝒫_0^{n-1}) + ∫ log φ^s(A_{𝐢|_n}) dμ(𝐢)` is at most
`log ∑_{|𝐢| = n} φ^s(A_𝐢)`. -/
theorem blockEntropy_add_blockEnergy_le (hA : ∀ i, (A i).det ≠ 0) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (n : ℕ) :
    blockEntropy μ n + blockEnergy A s μ n ≤ Real.log (svfSum A s n) := by
  rw [blockEnergy_eq_integral μ n, add_comm]
  exact integral_log_svf_add_blockEntropy_le hA n s

/-- The energy at level `n` is at least `n c` for the constant `c` of
`exists_le_log_svf_word`. -/
theorem le_blockEnergy {c : ℝ} (hc : ∀ w : List ι, c * w.length ≤ Real.log (svf s (word A w)))
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (n : ℕ) : n * c ≤ blockEnergy A s μ n := by
  have key : ∀ w : Fin n → ι, (n : ℝ) * c ≤ Real.log (svf s (word A (List.ofFn w))) := by
    intro w
    have h := hc (List.ofFn w)
    rw [List.length_ofFn] at h
    linarith
  calc (n : ℝ) * c
      = ∑ w : Fin n → ι, μ.real (cylinder w) * ((n : ℝ) * c) := by
        rw [← Finset.sum_mul, sum_measureReal_cylinder, one_mul]
    _ ≤ blockEnergy A s μ n :=
        Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (key w) measureReal_nonneg

/-- The sum of the block entropy and the block energy at level `l` is bounded by `l C` for every
probability measure, with a constant `C` depending only on the tuple and on `s`. -/
theorem exists_blockBound [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ μ : Measure (ℤ → ι), IsProbabilityMeasure μ → ∀ l : ℕ,
      |blockEntropy μ l + blockEnergy A s μ l| ≤ l * C := by
  obtain ⟨c, hc⟩ := exists_le_log_svf_word hA hs
  refine ⟨|Real.log (svfSum A s 1)| + |c|, by positivity, fun μ hμ l => ?_⟩
  have := hμ
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hC1 : Real.log (svfSum A s 1) ≤ |Real.log (svfSum A s 1)| + |c| :=
    (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
  have hC2 : -(|Real.log (svfSum A s 1)| + |c|) ≤ c := by
    have := neg_abs_le c
    have := abs_nonneg (Real.log (svfSum A s 1))
    linarith
  have hup : blockEntropy μ l + blockEnergy A s μ l
      ≤ l * (|Real.log (svfSum A s 1)| + |c|) := by
    have h1 := blockEntropy_add_blockEnergy_le (s := s) hA μ l
    have h2 := log_svfSum_le hA hs l
    have h3 := mul_le_mul_of_nonneg_left hC1 hl
    linarith
  have hlow : -(l * (|Real.log (svfSum A s 1)| + |c|))
      ≤ blockEntropy μ l + blockEnergy A s μ l := by
    have h1 := blockEntropy_nonneg μ l
    have h2 := le_blockEnergy hc μ l
    have h3 := mul_le_mul_of_nonneg_left hC2 hl
    rw [mul_neg] at h3
    linarith
  rw [abs_le]
  exact ⟨hlow, hup⟩

/-! ### The measures of Misiurewicz's construction -/

section Construction

variable [Nonempty ι] (n : ℕ)

variable (A s) in
/-- The weights `p_𝐢 = φ^s(A_𝐢) / ∑_{|𝐣| = n} φ^s(A_𝐣)` on the words of length `n`. -/
noncomputable def blockWeight (w : Fin n → ι) : ℝ :=
  svf s (word A (List.ofFn w)) / svfSum A s n

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The weights of the words of length `n` are positive. -/
theorem blockWeight_pos (hA : ∀ i, (A i).det ≠ 0) (w : Fin n → ι) : 0 < blockWeight A s n w :=
  div_pos (svf_word_pos hA s _) (svfSum_pos hA s n)

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The weights of the words of length `n` form a probability vector. -/
theorem sum_blockWeight (hA : ∀ i, (A i).det ≠ 0) : ∑ w : Fin n → ι, blockWeight A s n w = 1 := by
  simp only [blockWeight]
  rw [← Finset.sum_div, ← svfSum]
  exact div_self (svfSum_pos hA s n).ne'

omit [MeasurableSingletonClass ι] in
/-- The weights of the words of length `n` as a probability measure on the blocks. -/
theorem isProbabilityMeasure_blockWeightMeasure (hA : ∀ i, (A i).det ≠ 0) :
    IsProbabilityMeasure (weightMeasure (blockWeight A s n)) :=
  isProbabilityMeasure_weightMeasure (fun w => (blockWeight_pos n hA w).le) (sum_blockWeight n hA)

variable (A s) in
/-- The image under the concatenation of blocks of the Bernoulli measure with the weights
`p_𝐢`. It is invariant under `σ^n`, but not under `σ`. -/
noncomputable def blockMeasure [NeZero n] : Measure (ℤ → ι) :=
  (bernoulli (weightMeasure (blockWeight A s n))).map (concat n)

omit [MeasurableSingletonClass ι] in
/-- The block measure is a probability measure. -/
theorem isProbabilityMeasure_blockMeasure [NeZero n] (hA : ∀ i, (A i).det ≠ 0) :
    IsProbabilityMeasure (blockMeasure A s n) := by
  have := isProbabilityMeasure_blockWeightMeasure (s := s) n hA
  rw [blockMeasure]
  infer_instance

/-- The cylinder `[𝐢]` of a word of length `n` has the weight `p_𝐢` for the block measure. -/
theorem measureReal_blockMeasure_cylinder [NeZero n] (hA : ∀ i, (A i).det ≠ 0)
    (w : Fin n → ι) : (blockMeasure A s n).real (cylinder w) = blockWeight A s n w := by
  have := isProbabilityMeasure_blockWeightMeasure (s := s) n hA
  rw [blockMeasure, map_measureReal_apply (measurable_concat n) (measurableSet_cylinder w),
    preimage_concat_cylinder, measureReal_bernoulli_cylinder, Fin.prod_univ_one,
    Matrix.cons_val_zero, measureReal_weightMeasure_singleton (blockWeight_pos n hA w).le]

omit [MeasurableSingletonClass ι] in
/-- The block measure is invariant under `σ^n`. -/
theorem map_shift_blockMeasure [NeZero n] (hA : ∀ i, (A i).det ≠ 0) :
    (blockMeasure A s n).map (shift (n : ℤ)) = blockMeasure A s n := by
  have := isProbabilityMeasure_blockWeightMeasure (s := s) n hA
  have hcomp : (shift (n : ℤ)) ∘ (concat n : (ℤ → (Fin n → ι)) → ℤ → ι) = concat n ∘ shift 1 :=
    funext fun y => (concat_shift n y).symm
  rw [blockMeasure, Measure.map_map (measurable_shift (n : ℤ)) (measurable_concat n), hcomp,
    ← Measure.map_map (measurable_concat n) (measurable_shift 1),
    (measurePreserving_shift_bernoulli _ 1).map_eq]

/-- Gibbs' inequality is an equality for the weights `p_𝐢`: the block entropy and the block
energy of the block measure at level `n` add up to `log ∑_{|𝐢| = n} φ^s(A_𝐢)`. -/
theorem blockEntropy_add_blockEnergy_blockMeasure [NeZero n] (hA : ∀ i, (A i).det ≠ 0) :
    blockEntropy (blockMeasure A s n) n + blockEnergy A s (blockMeasure A s n) n
      = Real.log (svfSum A s n) := by
  have hdefect := sum_gibbs_defect (p := blockWeight A s n)
    (q := fun w : Fin n → ι => svf s (word A (List.ofFn w))) (sum_blockWeight n hA)
    (fun _ => svf_word_pos hA s _)
  have hZ : ∑ w : Fin n → ι, svf s (word A (List.ofFn w)) = svfSum A s n := rfl
  rw [hZ] at hdefect
  have hzero : ∀ w : Fin n → ι, svf s (word A (List.ofFn w)) / svfSum A s n
      - blockWeight A s n w - (Real.negMulLog (blockWeight A s n w) + blockWeight A s n w
        * Real.log (svf s (word A (List.ofFn w)) / svfSum A s n)) = 0 := by
    intro w
    rw [← blockWeight, Real.negMulLog]
    ring
  rw [Finset.sum_congr rfl fun w _ => hzero w, Finset.sum_const_zero] at hdefect
  rw [blockEntropy, blockEnergy]
  simp only [measureReal_blockMeasure_cylinder n hA]
  linarith

variable (A s) in
/-- The average `n⁻¹ ∑_{k < n} (σ^k)_*μ` of the first `n` translates of the block measure. -/
noncomputable def avgBlockMeasure [NeZero n] : Measure (ℤ → ι) :=
  (n : ℝ≥0∞)⁻¹ • ∑ j ∈ Finset.range n, (blockMeasure A s n).map (shift (j : ℤ))

omit [MeasurableSingletonClass ι] [Nonempty ι] in
/-- The measure of a set for the average of the translates, in `ℝ≥0∞`. -/
theorem avgBlockMeasure_apply [NeZero n] (B : Set (ℤ → ι)) :
    avgBlockMeasure A s n B
      = (n : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range n, ((blockMeasure A s n).map (shift (j : ℤ))) B := by
  rw [avgBlockMeasure, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]

omit [MeasurableSingletonClass ι] in
/-- The average of the translates of the block measure is a probability measure. -/
theorem isProbabilityMeasure_avgBlockMeasure [NeZero n] (hA : ∀ i, (A i).det ≠ 0) :
    IsProbabilityMeasure (avgBlockMeasure A s n) := by
  have := isProbabilityMeasure_blockMeasure (s := s) n hA
  constructor
  rw [avgBlockMeasure_apply n]
  have hone : ∀ j ∈ Finset.range n,
      ((blockMeasure A s n).map (shift (j : ℤ))) Set.univ = 1 := fun j _ => measure_univ
  rw [Finset.sum_congr rfl hone, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 (NeZero.ne n)) (ENNReal.natCast_ne_top n)]

omit [MeasurableSingletonClass ι] in
/-- The measure of a set for the average of the translates. -/
theorem measureReal_avgBlockMeasure [NeZero n] (hA : ∀ i, (A i).det ≠ 0) (B : Set (ℤ → ι)) :
    (avgBlockMeasure A s n).real B
      = (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, ((blockMeasure A s n).map (shift (j : ℤ))).real B := by
  have := isProbabilityMeasure_blockMeasure (s := s) n hA
  have hfin : ∀ j ∈ Finset.range n, ((blockMeasure A s n).map (shift (j : ℤ))) B ≠ ⊤ :=
    fun j _ => measure_ne_top _ _
  rw [measureReal_def, avgBlockMeasure_apply n, ENNReal.toReal_mul,
    ENNReal.toReal_sum hfin, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rfl

omit [MeasurableSingletonClass ι] in
/-- The sum of the measures of a set over the translates. -/
theorem sum_measureReal_map_shift [NeZero n] (hA : ∀ i, (A i).det ≠ 0) (B : Set (ℤ → ι)) :
    ∑ j ∈ Finset.range n, ((blockMeasure A s n).map (shift (j : ℤ))).real B
      = n * (avgBlockMeasure A s n).real B := by
  rw [measureReal_avgBlockMeasure n hA B, ← mul_assoc,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 (NeZero.ne n)), one_mul]

omit [MeasurableSingletonClass ι] in
/-- The average of the translates of the block measure is invariant under `σ`. -/
theorem measurePreserving_shift_avgBlockMeasure [NeZero n] (hA : ∀ i, (A i).det ≠ 0) :
    MeasurePreserving (shift 1) (avgBlockMeasure A s n) (avgBlockMeasure A s n) := by
  have := isProbabilityMeasure_avgBlockMeasure (s := s) n hA
  have hcast : ∀ j : ℕ, ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := fun j => by push_cast; ring
  have hf : ∀ (j : ℕ) (B : Set (ℤ → ι)), MeasurableSet B →
      ((blockMeasure A s n).map (shift ((j + 1 : ℕ) : ℤ))).real B
        = ((blockMeasure A s n).map (shift (j : ℤ))).real (shift 1 ⁻¹' B) := by
    intro j B hB
    rw [map_measureReal_apply (measurable_shift _) hB,
      map_measureReal_apply (measurable_shift _) (measurable_shift 1 hB)]
    congr 1
    ext x
    simp only [Set.mem_preimage, shift_shift, hcast]
  have hzero : ∀ B : Set (ℤ → ι),
      ((blockMeasure A s n).map (shift ((0 : ℕ) : ℤ))).real B = (blockMeasure A s n).real B := by
    intro B
    have h0 : (shift ((0 : ℕ) : ℤ) : (ℤ → ι) → ℤ → ι) = id := by
      funext x k
      simp
    rw [h0, Measure.map_id]
  have hnn : ∀ B : Set (ℤ → ι),
      ((blockMeasure A s n).map (shift ((n : ℕ) : ℤ))).real B = (blockMeasure A s n).real B := by
    intro B
    rw [map_shift_blockMeasure n hA]
  refine ⟨measurable_shift 1, Measure.ext fun B hB => ?_⟩
  rw [Measure.map_apply (measurable_shift 1) hB,
    ← ofReal_measureReal (measure_ne_top (avgBlockMeasure A s n) (shift 1 ⁻¹' B)),
    ← ofReal_measureReal (measure_ne_top (avgBlockMeasure A s n) B)]
  congr 1
  rw [measureReal_avgBlockMeasure n hA, measureReal_avgBlockMeasure n hA]
  congr 1
  rw [Finset.sum_congr rfl fun j _ => (hf j B hB).symm]
  exact sum_range_shift_eq
    (f := fun j : ℕ => ((blockMeasure A s n).map (shift (j : ℤ))).real B)
    (by rw [hzero, hnn])

end Construction

/-! ### The Misiurewicz estimate -/

variable (A s) in
/-- The sum of the block entropy and the block energy at level `l` for the translate
`(σ^j)_*μ`. -/
noncomputable def blockSum (μ : Measure (ℤ → ι)) (j l : ℕ) : ℝ :=
  blockEntropy (μ.map (shift (j : ℤ))) l + blockEnergy A s (μ.map (shift (j : ℤ))) l

omit [MeasurableSingletonClass ι] in
/-- At `j = 0` the block sum is that of the measure itself. -/
theorem blockSum_zero_left (μ : Measure (ℤ → ι)) (l : ℕ) :
    blockSum A s μ 0 l = blockEntropy μ l + blockEnergy A s μ l := by
  have h0 : (shift ((0 : ℕ) : ℤ) : (ℤ → ι) → ℤ → ι) = id := by
    funext x k
    simp
  rw [blockSum, h0, Measure.map_id]

/-- The block sums are sub-additive in the length: the second term is the block sum of the
translate by `l₁`. -/
theorem blockSum_add_le (hA : ∀ i, (A i).det ≠ 0) (hs : 0 ≤ s) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (j l₁ l₂ : ℕ) :
    blockSum A s μ j (l₁ + l₂) ≤ blockSum A s μ j l₁ + blockSum A s μ (j + l₁) l₂ := by
  have hmap : (μ.map (shift (j : ℤ))).map (shift (l₁ : ℤ))
      = μ.map (shift ((j + l₁ : ℕ) : ℤ)) := by
    rw [Measure.map_map (measurable_shift _) (measurable_shift _)]
    congr 1
    funext x
    rw [Function.comp_apply, shift_shift]
    push_cast
    ring_nf
  have h1 := blockEntropy_add_le' (μ.map (shift (j : ℤ))) l₁ l₂
  have h2 := blockEnergy_add_le hA hs (μ.map (shift (j : ℤ))) l₁ l₂
  rw [hmap] at h1 h2
  unfold blockSum
  linarith

omit [MeasurableSingletonClass ι] in
/-- The block sums of the translates are bounded by `l C`. -/
theorem abs_blockSum_le {C : ℝ}
    (hCb : ∀ μ : Measure (ℤ → ι), IsProbabilityMeasure μ → ∀ l : ℕ,
      |blockEntropy μ l + blockEnergy A s μ l| ≤ l * C)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (j l : ℕ) : |blockSum A s μ j l| ≤ l * C :=
  hCb _ inferInstance l

/-- Iterating the sub-additivity of the block sums along the blocks of length `m`. -/
theorem blockSum_chain_le (hA : ∀ i, (A i).det ≠ 0) (hs : 0 ≤ s) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (m : ℕ) :
    ∀ (a j z : ℕ), blockSum A s μ j (a * m + z)
      ≤ (∑ r ∈ Finset.range a, blockSum A s μ (j + r * m) m) + blockSum A s μ (j + a * m) z := by
  intro a
  induction a with
  | zero => intro j z; simp
  | succ a ih =>
    intro j z
    have h1 := blockSum_add_le hA hs μ j m (a * m + z)
    have h2 := ih (j + m) z
    have hsum : ∑ r ∈ Finset.range a, blockSum A s μ (j + m + r * m) m
        = ∑ r ∈ Finset.range a, blockSum A s μ (j + (r + 1) * m) m :=
      Finset.sum_congr rfl fun r _ => by
        have hr : j + m + r * m = j + (r + 1) * m := by ring
        rw [hr]
    have hidx : j + m + a * m = j + (a + 1) * m := by ring
    rw [hsum, hidx] at h2
    have h3 : ∑ r ∈ Finset.range (a + 1), blockSum A s μ (j + r * m) m
        = (∑ r ∈ Finset.range a, blockSum A s μ (j + (r + 1) * m) m)
          + blockSum A s μ (j + 0 * m) m :=
      Finset.sum_range_succ' (fun r => blockSum A s μ (j + r * m) m) a
    simp only [Nat.zero_mul, Nat.add_zero] at h3
    have he : (a + 1) * m + z = m + (a * m + z) := by ring
    rw [he, h3]
    linarith

variable [Nonempty ι]

omit [MeasurableSingletonClass ι] in
/-- The block sums of the translates of the block measure add up to at most `n` times the block
sum of the average of the translates: the energy is affine in the measure and the entropy is
concave. -/
theorem sum_blockSum_le (hA : ∀ i, (A i).det ≠ 0) {n : ℕ} [NeZero n] (m : ℕ) :
    ∑ j ∈ Finset.range n, blockSum A s (blockMeasure A s n) j m
      ≤ n * (blockEntropy (avgBlockMeasure A s n) m
        + blockEnergy A s (avgBlockMeasure A s n) m) := by
  have hn0 : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  have hn0' : (0 : ℝ) < n := lt_of_le_of_ne (Nat.cast_nonneg n) (Ne.symm hn0)
  have hcyl : ∀ w : Fin m → ι,
      ∑ j ∈ Finset.range n, ((blockMeasure A s n).map (shift (j : ℤ))).real (cylinder w)
        = n * (avgBlockMeasure A s n).real (cylinder w) :=
    fun w => sum_measureReal_map_shift n hA _
  have henergy : ∑ j ∈ Finset.range n,
      blockEnergy A s ((blockMeasure A s n).map (shift (j : ℤ))) m
      = n * blockEnergy A s (avgBlockMeasure A s n) m := by
    simp only [blockEnergy]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.sum_mul, hcyl w, mul_assoc]
  have hentropy : ∑ j ∈ Finset.range n,
      blockEntropy ((blockMeasure A s n).map (shift (j : ℤ))) m
      ≤ n * blockEntropy (avgBlockMeasure A s n) m := by
    simp only [blockEntropy]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    have hw0 : ∀ j ∈ Finset.range n, (0 : ℝ) ≤ (n : ℝ)⁻¹ := fun _ _ => by positivity
    have hw1 : ∑ _j ∈ Finset.range n, (n : ℝ)⁻¹ = 1 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_inv_cancel₀ hn0]
    have hmem : ∀ j ∈ Finset.range n,
        ((blockMeasure A s n).map (shift (j : ℤ))).real (cylinder w) ∈ Set.Ici (0 : ℝ) :=
      fun _ _ => measureReal_nonneg
    have h := Real.concaveOn_negMulLog.le_map_sum hw0 hw1 hmem
    simp only [smul_eq_mul] at h
    have hrhs : ∑ j ∈ Finset.range n,
        (n : ℝ)⁻¹ * ((blockMeasure A s n).map (shift (j : ℤ))).real (cylinder w)
          = (avgBlockMeasure A s n).real (cylinder w) := by
      rw [← Finset.mul_sum, hcyl w, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
    have hlhs : ∑ j ∈ Finset.range n,
        (n : ℝ)⁻¹ * Real.negMulLog (((blockMeasure A s n).map (shift (j : ℤ))).real (cylinder w))
          = (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n,
            Real.negMulLog (((blockMeasure A s n).map (shift (j : ℤ))).real (cylinder w)) :=
      (Finset.mul_sum _ _ _).symm
    rw [hlhs, hrhs] at h
    rw [inv_mul_le_iff₀ hn0'] at h
    exact h
  simp only [blockSum]
  rw [Finset.sum_add_distrib, henergy, mul_add]
  linarith

/-- The Misiurewicz estimate: for `1 ≤ m ≤ n` the average `μ` of the translates of the block
measure of length `n` satisfies
`m log ∑_{|𝐢| = n} φ^s(A_𝐢) ≤ n (H_μ(𝒫_0^{m-1}) + ∫ log φ^s(A_{𝐢|_m}) dμ) + 5 m² C`. -/
theorem log_svfSum_le_avgBlockMeasure (hA : ∀ i, (A i).det ≠ 0) (hs : 0 ≤ s) {C : ℝ}
    (hC : 0 ≤ C)
    (hCb : ∀ μ : Measure (ℤ → ι), IsProbabilityMeasure μ → ∀ l : ℕ,
      |blockEntropy μ l + blockEnergy A s μ l| ≤ l * C)
    {n m : ℕ} [NeZero n] (hm : 0 < m) (hmn : m ≤ n) :
    m * Real.log (svfSum A s n)
      ≤ n * (blockEntropy (avgBlockMeasure A s n) m + blockEnergy A s (avgBlockMeasure A s n) m)
        + 5 * m ^ 2 * C := by
  have := isProbabilityMeasure_blockMeasure (s := s) n hA
  obtain ⟨a, ha⟩ : ∃ a, n / m = a + 1 := ⟨n / m - 1, by
    have h1 : 1 ≤ n / m := (Nat.one_le_div_iff hm).2 hmn
    omega⟩
  have hsplit : a * m + m + n % m = n := by
    have h := Nat.div_add_mod n m
    rw [ha, Nat.mul_succ, Nat.mul_comm] at h
    omega
  have hmodlt : n % m < m := Nat.mod_lt _ hm
  have hmC : 0 ≤ (m : ℝ) * C := mul_nonneg (Nat.cast_nonneg m) hC
  have hlogZ : blockEntropy (blockMeasure A s n) n + blockEnergy A s (blockMeasure A s n) n
      = Real.log (svfSum A s n) := blockEntropy_add_blockEnergy_blockMeasure n hA
  have key : ∀ k ∈ Finset.range m, Real.log (svfSum A s n)
      ≤ (∑ r ∈ Finset.range a, blockSum A s (blockMeasure A s n) (k + r * m) m)
        + 3 * ((m : ℝ) * C) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hz : k + (a * m + (n - (k + a * m))) = n := by omega
    have h1 := blockSum_add_le hA hs (blockMeasure A s n) 0 k (a * m + (n - (k + a * m)))
    rw [hz, Nat.zero_add] at h1
    have h2 := blockSum_chain_le hA hs (blockMeasure A s n) m a k (n - (k + a * m))
    have h3 := (abs_le.1 (abs_blockSum_le hCb (blockMeasure A s n) 0 k)).2
    have h4 := (abs_le.1 (abs_blockSum_le hCb (blockMeasure A s n) (k + a * m)
      (n - (k + a * m)))).2
    have h5 : (k : ℝ) * C ≤ (m : ℝ) * C :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hk.le) hC
    have h6 : ((n - (k + a * m) : ℕ) : ℝ) * C ≤ 2 * ((m : ℝ) * C) := by
      have hle : (n - (k + a * m) : ℕ) ≤ 2 * m := by omega
      have : ((n - (k + a * m) : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hle
      calc ((n - (k + a * m) : ℕ) : ℝ) * C ≤ (2 * (m : ℝ)) * C :=
            mul_le_mul_of_nonneg_right this hC
        _ = 2 * ((m : ℝ) * C) := by ring
    rw [blockSum_zero_left (blockMeasure A s n) n, hlogZ] at h1
    linarith
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hreindex : ∑ k ∈ Finset.range m,
      ∑ r ∈ Finset.range a, blockSum A s (blockMeasure A s n) (k + r * m) m
      = ∑ j ∈ Finset.range (a * m), blockSum A s (blockMeasure A s n) j m := by
    rw [sum_range_mul_eq]
    exact Finset.sum_comm
  rw [hreindex] at hsum
  have hd : a * m + (n - a * m) = n := by omega
  have hsplit2 : ∑ j ∈ Finset.range n, blockSum A s (blockMeasure A s n) j m
      = (∑ j ∈ Finset.range (a * m), blockSum A s (blockMeasure A s n) j m)
        + ∑ i ∈ Finset.range (n - a * m), blockSum A s (blockMeasure A s n) (a * m + i) m := by
    have h := Finset.sum_range_add (fun j => blockSum A s (blockMeasure A s n) j m)
      (a * m) (n - a * m)
    rw [hd] at h
    exact h
  have hlow : ∀ i ∈ Finset.range (n - a * m),
      -((m : ℝ) * C) ≤ blockSum A s (blockMeasure A s n) (a * m + i) m := fun i _ =>
    (abs_le.1 (abs_blockSum_le hCb (blockMeasure A s n) (a * m + i) m)).1
  have hcard := Finset.card_nsmul_le_sum (Finset.range (n - a * m))
    (fun i => blockSum A s (blockMeasure A s n) (a * m + i) m) (-((m : ℝ) * C)) hlow
  rw [Finset.card_range, nsmul_eq_mul] at hcard
  have htail : -(2 * (m : ℝ) * ((m : ℝ) * C))
      ≤ ∑ i ∈ Finset.range (n - a * m), blockSum A s (blockMeasure A s n) (a * m + i) m := by
    refine le_trans ?_ hcard
    have hle : (n - a * m : ℕ) ≤ 2 * m := by omega
    have h' : ((n - a * m : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hle
    nlinarith
  have havg : ∑ j ∈ Finset.range n, blockSum A s (blockMeasure A s n) j m
      ≤ n * (blockEntropy (avgBlockMeasure A s n) m
        + blockEnergy A s (avgBlockMeasure A s n) m) := sum_blockSum_le hA m
  have hsq : (m : ℝ) * (3 * ((m : ℝ) * C)) + 2 * (m : ℝ) * ((m : ℝ) * C)
      = 5 * (m : ℝ) ^ 2 * C := by ring
  have step1 : ∑ j ∈ Finset.range (a * m), blockSum A s (blockMeasure A s n) j m
      ≤ (∑ j ∈ Finset.range n, blockSum A s (blockMeasure A s n) j m)
        + 2 * (m : ℝ) * ((m : ℝ) * C) := by
    linarith [hsplit2, htail]
  linarith [hsum, step1, havg, hsq]

/-! ### The limit measure -/

/-- **The existence half of the variational principle** for a tuple of invertible matrices:
there is a `σ`-invariant probability measure with `P(𝖠, s) ≤ h_0(μ) + Λ(𝖠, μ, s)`, for every
`s ≥ 0`. The measure is a weak-star limit of the averages `avgBlockMeasure`. -/
theorem exists_invariant_pressure_le (hA : ∀ i, (A i).det ≠ 0) (hs : 0 ≤ s) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
      pressure A s ≤ entropy μ + energyLim A s μ := by
  obtain ⟨C, hC, hCb⟩ := exists_blockBound hA hs
  set μs : ℕ → Measure (ℤ → ι) := fun n => avgBlockMeasure A s (n + 1) with hμs
  have hprob : ∀ n, IsProbabilityMeasure (μs n) := fun n =>
    isProbabilityMeasure_avgBlockMeasure (n + 1) hA
  have hinvs : ∀ n, MeasurePreserving (shift 1) (μs n) (μs n) := fun n =>
    measurePreserving_shift_avgBlockMeasure (n + 1) hA
  let : TopologicalSpace ι := ⊥
  have : DiscreteTopology ι := ⟨rfl⟩
  have : BorelSpace ι := ⟨le_antisymm
    (fun t _ => MeasurableSpace.measurableSet_generateFrom (isOpen_discrete t))
    (MeasurableSpace.generateFrom_le fun u _ => (Set.toFinite u).measurableSet)⟩
  set U : Ultrafilter ℕ := Ultrafilter.of atTop with hU
  set P : ℕ → ProbabilityMeasure (ℤ → ι) := fun n => ⟨μs n, hprob n⟩ with hP
  obtain ⟨Q, -, hQ⟩ := isCompact_univ.ultrafilter_le_nhds (U.map P) (by simp)
  have hten : Tendsto P (U : Filter ℕ) (𝓝 Q) := by
    rw [Tendsto, ← Ultrafilter.coe_map]
    exact hQ
  have hUle : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have hcoe : ∀ (R : ProbabilityMeasure (ℤ → ι)) (B : Set (ℤ → ι)),
      ((R B : NNReal) : ℝ) = (R : Measure (ℤ → ι)).real B := fun R B => by
    rw [measureReal_def, ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_toReal]
  have hconv : ∀ B : Set (ℤ → ι), IsClopen B →
      Tendsto (fun n => (μs n).real B) (U : Filter ℕ)
        (𝓝 ((Q : Measure (ℤ → ι)).real B)) := by
    intro B hB
    have h := (NNReal.continuous_coe.tendsto _).comp
      (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hten hB)
    rw [Function.comp_def, hcoe Q] at h
    exact h.congr fun n => hcoe (P n) B
  -- the limit measure is invariant
  have hQshift : ∀ (k : ℤ) (m : ℕ) (w : Fin m → ι),
      (Q : Measure (ℤ → ι)).real (shift k ⁻¹' cylinder w)
        = (Q : Measure (ℤ → ι)).real (cylinder w) := by
    intro k m w
    refine tendsto_nhds_unique (hconv _ (isClopen_preimage_shift_cylinder k w)) ?_
    exact (hconv _ (isClopen_cylinder w)).congr fun n =>
      haveI := hprob n
      (measureReal_preimage_shift (hinvs n) k (measurableSet_cylinder w)).symm
  have hinvQ : MeasurePreserving (shift 1) (Q : Measure (ℤ → ι)) (Q : Measure (ℤ → ι)) := by
    refine ⟨measurable_shift 1, measure_ext_of_cylinder fun k m w => ?_⟩
    have hset : ∀ j : ℤ, {x : ℤ → ι | ∀ i : Fin m, x (j + i) = w i} = shift j ⁻¹' cylinder w :=
      fun j => rfl
    have hpre : shift (1 : ℤ) ⁻¹' (shift k ⁻¹' cylinder w) = shift (1 + k) ⁻¹' cylinder w := by
      ext x
      simp [shift_shift]
    rw [hset k, Measure.map_apply (measurable_shift 1)
      (measurable_shift k (measurableSet_cylinder w)), hpre,
      ← ofReal_measureReal (measure_ne_top (Q : Measure (ℤ → ι)) _),
      ← ofReal_measureReal (measure_ne_top (Q : Measure (ℤ → ι)) _), hQshift, hQshift]
  refine ⟨(Q : Measure (ℤ → ι)), inferInstance, hinvQ, ?_⟩
  -- the block estimate passes to the limit
  have hblock : ∀ m : ℕ, 0 < m →
      (m : ℝ) * pressure A s ≤ blockEntropy (Q : Measure (ℤ → ι)) m
        + blockEnergy A s (Q : Measure (ℤ → ι)) m := by
    intro m hm
    have hcyl : ∀ w : Fin m → ι, Tendsto (fun n => (μs n).real (cylinder w)) (U : Filter ℕ)
        (𝓝 ((Q : Measure (ℤ → ι)).real (cylinder w))) := fun w => hconv _ (isClopen_cylinder w)
    have hB1 : Tendsto (fun n => blockEntropy (μs n) m) (U : Filter ℕ)
        (𝓝 (blockEntropy (Q : Measure (ℤ → ι)) m)) :=
      tendsto_finsetSum _ fun w _ => (Real.continuous_negMulLog.tendsto _).comp (hcyl w)
    have hB2 : Tendsto (fun n => blockEnergy A s (μs n) m) (U : Filter ℕ)
        (𝓝 (blockEnergy A s (Q : Measure (ℤ → ι)) m)) :=
      tendsto_finsetSum _ fun w _ => (hcyl w).mul_const _
    have hB := hB1.add hB2
    have herr : Tendsto (fun n : ℕ => (5 * (m : ℝ) ^ 2 * C) * (1 / ((n : ℝ) + 1)))
        (U : Filter ℕ) (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => (5 * (m : ℝ) ^ 2 * C) * (1 / ((n : ℝ) + 1))) atTop
          (𝓝 ((5 * (m : ℝ) ^ 2 * C) * 0)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _
      rw [mul_zero] at h0
      exact h0.mono_left hUle
    have hlim := hB.add herr
    rw [add_zero] at hlim
    refine ge_of_tendsto hlim ?_
    filter_upwards [hUle (eventually_ge_atTop m)] with n hn
    have hmn : m ≤ n + 1 := le_trans hn (Nat.le_succ n)
    have hkey := log_svfSum_le_avgBlockMeasure hA hs hC hCb (n := n + 1) (m := m) hm hmn
    have hpre := pressure_le_log_svfSum_div hA hs (n := n + 1) (Nat.succ_le_succ (Nat.zero_le n))
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn1' : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hn1', le_div_iff₀ hn1, mul_comm] at hpre
    rw [hn1'] at hkey
    have hmnn : (m : ℝ) * (((n : ℝ) + 1) * pressure A s)
        ≤ (m : ℝ) * Real.log (svfSum A s (n + 1)) :=
      mul_le_mul_of_nonneg_left hpre (Nat.cast_nonneg m)
    have hfinal : ((n : ℝ) + 1) * ((m : ℝ) * pressure A s)
        ≤ ((n : ℝ) + 1) * (blockEntropy (μs n) m + blockEnergy A s (μs n) m
          + (5 * (m : ℝ) ^ 2 * C) * (1 / ((n : ℝ) + 1))) := by
      have hdiv : ((n : ℝ) + 1) * ((5 * (m : ℝ) ^ 2 * C) * (1 / ((n : ℝ) + 1)))
          = 5 * (m : ℝ) ^ 2 * C := by
        field_simp
      rw [mul_add, hdiv]
      nlinarith
    exact le_of_mul_le_mul_left hfinal hn1
  have hlim := (tendsto_entropy hinvQ).add (tendsto_energyLim hA hinvQ hs)
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have h := hblock m hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [← blockEnergy_eq_integral (Q : Measure (ℤ → ι)) m, ← add_div, le_div_iff₀ hm', mul_comm]
  exact h

/-- **Existence of an `s`-equilibrium state** for every tuple of invertible planar matrices and
every `s ≥ 0`, the existence part of `thm:irred_eq_state` with no irreducibility hypothesis:
the measure of `exists_invariant_pressure_le` satisfies `eq:eq_state_def`, since
`eq:variational` gives the reverse inequality. -/
theorem exists_isEquilibriumState (hA : ∀ i, (A i).det ≠ 0) (hs : 0 ≤ s) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
      IsEquilibriumState A s μ := by
  obtain ⟨μ, hprob, hinv, h⟩ := exists_invariant_pressure_le hA hs
  have := hprob
  exact ⟨μ, hprob, hinv, le_antisymm h (entropy_add_energyLim_le_pressure hA hinv hs)⟩

end MatrixTuple

namespace System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [Nonempty ι]
  (S : System ι) {s : ℝ}

/-- `MatrixTuple.exists_isEquilibriumState` for a box-like system recovers
`System.exists_isEquilibriumState`. -/
theorem exists_isEquilibriumState_eq_tuple (hs : 0 ≤ s) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
      S.IsEquilibriumState s μ :=
  MatrixTuple.exists_isEquilibriumState S.det_mat_ne_zero hs

end System

end BoxLike
