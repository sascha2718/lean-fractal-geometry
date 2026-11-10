module

/-
The existence of an `s`-equilibrium state, the half of the sub-additive variational principle
that `thm:irred_eq_state` needs (tex lines 2097 to 2106; Käenmäki, Ann. Acad. Sci. Fenn. Math.
29 (2004), Theorem 2.6, and, for sub-additive potentials, Cao–Feng–Huang, Discrete Contin. Dyn.
Syst. 20 (2008), Theorem 1.1). The construction is the one of Misiurewicz: the weights
`φ^s(A_𝐢)/∑_{|𝐣| = n} φ^s(A_𝐣)` on the words of length `n` give a Bernoulli measure on the
alphabet of blocks of length `n`, its image under the concatenation of blocks is invariant under
`σ^n`, and the average of its first `n` translates is invariant under `σ`. Along a limit of these
measures the block averages of the entropy and of the energy are at least `P(𝖠, s)`, and their
limits are `h_0(μ)` and `Λ(𝖠, μ, s)`.

* `System.blockEnergy`: the energy `∫ log φ^s(A_{𝐢|_n}) dμ(𝐢)` at level `n`, as a sum over the
  cylinders.
* `blockEntropy_add_le'`, `System.blockEnergy_add_le`: sub-additivity in the length, with the
  second term taken for the translate `(σ^m)_*μ`; neither needs invariance.
* `System.exists_blockBound`: `|H_μ(𝒫_0^{l-1}) + ∫ log φ^s(A_{𝐢|_l}) dμ| ≤ l C` for every
  probability measure.
* `concat`, `concat_shift`, `preimage_concat_cylinder`: the concatenation of blocks of length
  `n`, which conjugates `σ` to `σ^n`.
* `System.blockWeight`, `System.blockMeasure`, `System.avgBlockMeasure`: the weights
  `p_𝐢 = φ^s(A_𝐢)/∑_{|𝐣| = n} φ^s(A_𝐣)`, the image of the Bernoulli measure with these weights
  under the concatenation, and the average of its translates.
* `isClopen_cylinder`, `isClopen_preimage_shift_cylinder`: the cylinders and their translates are
  clopen for the product topology of the discrete alphabet.
* `System.blockSum`, `System.blockSum_chain_le`: the sum of the block entropy and the block energy
  for a translate, and its sub-additivity along the blocks of length `m`.
* `System.log_svfSum_le_avgBlockMeasure`: the Misiurewicz estimate
  `m log ∑_{|𝐢| = n} φ^s(A_𝐢) ≤ n (H + energy at level m) + 5 m² C`.
* `System.exists_invariant_pressure_le`, `System.exists_invariant_le_entropy_add_energy`: an
  invariant probability measure with `P(𝖠, s) ≤ h_0(μ) + Λ(𝖠, μ, s)`.
* `System.exists_isEquilibriumState`: an `s`-equilibrium state exists for every `s ≥ 0`.
-/
public import BoxLike.BernoulliEquilibrium
public import BoxLike.CodingTopology
public import BoxLike.Variational
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov

@[expose] public section

namespace BoxLike

open Filter MeasureTheory Topology
open scoped ENNReal Matrix.Norms.L2Operator

/-! ### The singular value function of the empty word -/

/-- `φ^s(I) = 1`. -/
theorem svf_one (s : ℝ) : svf s (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  have h1 : (1 : Matrix (Fin 2) (Fin 2) ℝ) = boxMat 0 1 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hn : ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ = 1 := by
    rw [h1, norm_boxMat]
    norm_num
  unfold svf
  rw [hn, Matrix.det_one]
  split_ifs <;> simp

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι) {s δ : ℝ}

omit [Fintype ι] in
/-- `φ^s(A_∅) = 1`. -/
theorem svf_matWord_nil : svf s (S.matWord ([] : List ι)) = 1 := by
  rw [matWord_nil, svf_one]

/-- `∑_{|𝐢| = 0} φ^s(A_𝐢) = 1`: the empty word is the only word of length zero. -/
theorem svfSum_zero : S.svfSum s 0 = 1 := by
  rw [svfSum, Fintype.sum_unique, List.ofFn_zero, svf_matWord_nil]

/-- `log ∑_{|𝐢| = l} φ^s(A_𝐢) ≤ l log ∑_i φ^s(A_i)`, by sub-multiplicativity. -/
theorem log_svfSum_le [Nonempty ι] (hδ : S.RatioLowerBound δ) (hs : 0 ≤ s) (l : ℕ) :
    Real.log (S.svfSum s l) ≤ l * Real.log (S.svfSum s 1) := by
  induction l with
  | zero => simp [S.svfSum_zero]
  | succ l ih =>
    have h1 := hδ.svfSum_pos hs l
    have h2 := hδ.svfSum_pos hs 1
    have h := Real.log_le_log (hδ.svfSum_pos hs (l + 1)) (S.svfSum_add_le hs l 1)
    rw [Real.log_mul h1.ne' h2.ne'] at h
    push_cast
    linarith

end System

/-! ### The concatenation of blocks -/

section Concat

variable {α : Type*}

/-- The concatenation of blocks of length `n`: the blocks of the sequence `y` written side by
side, `(concat n y)_k = y_{⌊k/n⌋, k mod n}`. It inverts the recoding of `Σ` by the blocks of
length `n`, of which `group` of `sec:normalisation` is the case `n = 2`. -/
def concat (n : ℕ) [NeZero n] (y : ℤ → (Fin n → α)) : ℤ → α :=
  fun k => y (k / n) ⟨(k % n).toNat % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩

/-- `concat n ∘ σ = σ^n ∘ concat n`: the concatenation conjugates the shift of the blocks to the
`n`-th iterate of the shift. -/
theorem concat_shift (n : ℕ) [NeZero n] (y : ℤ → (Fin n → α)) :
    concat n (shift 1 y) = shift (n : ℤ) (concat n y) := by
  have hn : (n : ℤ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  funext k
  have hsplit : (n : ℤ) + k = k + 1 * (n : ℤ) := by ring
  have hdiv : ((n : ℤ) + k) / (n : ℤ) = 1 + k / (n : ℤ) := by
    rw [hsplit, Int.add_mul_ediv_right _ _ hn, add_comm]
  have hmod : ((n : ℤ) + k) % (n : ℤ) = k % (n : ℤ) := by
    rw [hsplit, Int.add_mul_emod_self_right]
  simp only [concat, shift_apply]
  rw [hdiv]
  congr 1
  refine Fin.ext ?_
  show (k % (n : ℤ)).toNat % n = (((n : ℤ) + k) % (n : ℤ)).toNat % n
  rw [hmod]

/-- Inside the block at time `0` the concatenation reads off that block. -/
theorem concat_coe (n : ℕ) [NeZero n] (y : ℤ → (Fin n → α)) (k : Fin n) :
    concat n y (k : ℤ) = y 0 k := by
  have h0 : (0 : ℤ) ≤ ((k : ℕ) : ℤ) := Int.natCast_nonneg _
  have h1 : ((k : ℕ) : ℤ) < (n : ℤ) := by exact_mod_cast k.2
  have hdiv : ((k : ℕ) : ℤ) / (n : ℤ) = 0 := Int.ediv_eq_zero_of_lt h0 h1
  have hidx : (((k : ℕ) : ℤ) % (n : ℤ)).toNat % n = (k : ℕ) := by
    rw [Int.emod_eq_of_lt h0 h1, Int.toNat_natCast, Nat.mod_eq_of_lt k.2]
  simp only [concat]
  rw [hdiv]
  congr 1
  exact Fin.ext hidx

/-- The preimage under the concatenation of a cylinder of length `n` is the cylinder of the
single block. -/
theorem preimage_concat_cylinder (n : ℕ) [NeZero n] (w : Fin n → α) :
    concat n ⁻¹' cylinder w = cylinder ![w] := by
  ext y
  simp only [Set.mem_preimage, mem_cylinder, concat_coe]
  constructor
  · intro h j
    rw [Subsingleton.elim j 0]
    exact funext h
  · intro h _
    exact congrFun (h 0) _

variable [MeasurableSpace α]

/-- The concatenation of blocks is measurable. -/
theorem measurable_concat (n : ℕ) [NeZero n] :
    Measurable (concat n : (ℤ → (Fin n → α)) → ℤ → α) :=
  Measurable.of_eval fun _ => (measurable_pi_apply _).comp (measurable_pi_apply _)

end Concat

/-! ### Clopen cylinders -/

section Clopen

variable {α : Type*} [TopologicalSpace α] [DiscreteTopology α] {m : ℕ}

/-- The cylinders are clopen for the product topology of a discrete alphabet. -/
theorem isClopen_cylinder (w : Fin m → α) : IsClopen (cylinder w : Set (ℤ → α)) := by
  have hc : Continuous (block m : (ℤ → α) → Fin m → α) := continuous_pi fun _ => continuous_apply _
  rw [cylinder_eq_preimage]
  exact ⟨(isClosed_discrete _).preimage hc, (isOpen_discrete _).preimage hc⟩

/-- The translates of the cylinders are clopen. -/
theorem isClopen_preimage_shift_cylinder (k : ℤ) (w : Fin m → α) :
    IsClopen (shift k ⁻¹' cylinder w : Set (ℤ → α)) :=
  (isClopen_cylinder w).preimage (continuous_pi fun _ => continuous_apply _)

end Clopen

/-! ### Block entropies and energies of the translates -/

section Shifted

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] {m n : ℕ}

/-- Summing `μ([w w'])` over the words `w` of length `m` gives the measure of `[w']` for the
translate `(σ^m)_*μ`. -/
theorem sum_measureReal_cylinder_append_left' (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (w' : Fin n → α) :
    ∑ w : Fin m → α, μ.real (cylinder (Fin.append w w'))
      = (μ.map (shift (m : ℤ))).real (cylinder w') := by
  have h := sum_measureReal_inter_preimage_singleton μ (f := block m)
    (fun c => measurable_block m (measurableSet_singleton c)) (shift (m : ℤ) ⁻¹' cylinder w')
  rw [map_measureReal_apply (measurable_shift (m : ℤ)) (measurableSet_cylinder w'), ← h]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [cylinder_append, cylinder_eq_preimage w, Set.inter_comm]

/-- The block entropies are sub-additive in the length without any invariance, provided the
second term is taken for the translate `(σ^m)_*μ`. -/
theorem blockEntropy_add_le' (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ] (m n : ℕ) :
    blockEntropy μ (m + n) ≤ blockEntropy μ m + blockEntropy (μ.map (shift (m : ℤ))) n := by
  rw [blockEntropy_add_eq_sum]
  exact sum_negMulLog_le_add (fun _ _ => measureReal_nonneg)
    (sum_measureReal_cylinder_append_right μ) (sum_measureReal_cylinder_append_left' μ)
    (sum_measureReal_cylinder μ m)

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- A sum over the words of length `m + n` as an iterated sum over the two halves. -/
theorem sum_fin_append {M : Type*} [AddCommMonoid M] (G : (Fin (m + n) → α) → M) :
    ∑ v : Fin (m + n) → α, G v = ∑ w : Fin m → α, ∑ w' : Fin n → α, G (Fin.append w w') :=
  calc ∑ v : Fin (m + n) → α, G v
      = ∑ p : (Fin m → α) × (Fin n → α), G (Fin.append p.1 p.2) :=
        (Fintype.sum_equiv (Fin.appendEquiv m n) _ _ fun _ => rfl).symm
    _ = ∑ w : Fin m → α, ∑ w' : Fin n → α, G (Fin.append w w') := Fintype.sum_prod_type _

/-- A sum over `a m` terms as a double sum over the blocks of length `m`. -/
theorem sum_range_mul_eq {f : ℕ → ℝ} (a m : ℕ) :
    ∑ j ∈ Finset.range (a * m), f j
      = ∑ r ∈ Finset.range a, ∑ k ∈ Finset.range m, f (k + r * m) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ, ← ih, show (a + 1) * m = a * m + m from by ring,
      Finset.sum_range_add]
    exact congrArg _ (Finset.sum_congr rfl fun k _ => by rw [add_comm])

/-- A telescoping sum: `∑_{j < n} f(j+1) = ∑_{j < n} f(j)` when `f 0 = f n`. -/
theorem sum_range_shift_eq {f : ℕ → ℝ} {N : ℕ} (h : f 0 = f N) :
    ∑ j ∈ Finset.range N, f (j + 1) = ∑ j ∈ Finset.range N, f j := by
  have h1 := Finset.sum_range_succ' f N
  have h2 := Finset.sum_range_succ f N
  rw [h2] at h1
  linarith

end Shifted

namespace System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
  {s δ : ℝ}

/-- The energy at level `n`: the integral `∫ log φ^s(A_{𝐢|_n}) dμ(𝐢)` of `eq:energy_def` before
the passage to the limit, written as a sum over the cylinders of length `n`. -/
noncomputable def blockEnergy (s : ℝ) (μ : Measure (ℤ → ι)) (n : ℕ) : ℝ :=
  ∑ w : Fin n → ι, μ.real (cylinder w) * Real.log (svf s (S.matWord (List.ofFn w)))

/-- The energy at level `n` is the integral `∫ log φ^s(A_{𝐢|_n}) dμ(𝐢)`. -/
theorem blockEnergy_eq_integral (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] (n : ℕ) :
    S.blockEnergy s μ n = ∫ x, Real.log (svf s (S.matWord (futureWord x n))) ∂μ :=
  (integral_comp_futureWord_eq_sum μ (fun w => Real.log (svf s (S.matWord w))) n).symm

/-- The energies at level `n` are sub-additive in the length, by sub-multiplicativity of `φ^s`,
provided the second term is taken for the translate `(σ^m)_*μ`. -/
theorem blockEnergy_add_le (hs : 0 ≤ s) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (m n : ℕ) :
    S.blockEnergy s μ (m + n)
      ≤ S.blockEnergy s μ m + S.blockEnergy s (μ.map (shift (m : ℤ))) n := by
  have e1 : ∑ w : Fin m → ι, ∑ w' : Fin n → ι, μ.real (cylinder (Fin.append w w'))
        * Real.log (svf s (S.matWord (List.ofFn w)))
      = S.blockEnergy s μ m :=
    Finset.sum_congr rfl fun w _ => by
      rw [← Finset.sum_mul, sum_measureReal_cylinder_append_right]
  have e2 : ∑ w : Fin m → ι, ∑ w' : Fin n → ι, μ.real (cylinder (Fin.append w w'))
        * Real.log (svf s (S.matWord (List.ofFn w')))
      = S.blockEnergy s (μ.map (shift (m : ℤ))) n := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun w' _ => by
      rw [← Finset.sum_mul, sum_measureReal_cylinder_append_left']
  calc S.blockEnergy s μ (m + n)
      = ∑ w : Fin m → ι, ∑ w' : Fin n → ι, μ.real (cylinder (Fin.append w w'))
          * Real.log (svf s (S.matWord (List.ofFn (Fin.append w w')))) := sum_fin_append _
    _ ≤ ∑ w : Fin m → ι, ∑ w' : Fin n → ι, (μ.real (cylinder (Fin.append w w'))
          * Real.log (svf s (S.matWord (List.ofFn w)))
          + μ.real (cylinder (Fin.append w w'))
            * Real.log (svf s (S.matWord (List.ofFn w')))) :=
        Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun w' _ => by
          rw [← mul_add]
          refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
          rw [List.ofFn_fin_append]
          exact S.log_svf_matWord_append_le hs _ _
    _ = S.blockEnergy s μ m + S.blockEnergy s (μ.map (shift (m : ℤ))) n := by
        simp only [Finset.sum_add_distrib]
        rw [e1, e2]

/-- Gibbs' inequality at level `n`: `H_μ(𝒫_0^{n-1}) + ∫ log φ^s(A_{𝐢|_n}) dμ(𝐢)` is at most
`log ∑_{|𝐢| = n} φ^s(A_𝐢)`. -/
theorem blockEntropy_add_blockEnergy_le (hs : 0 ≤ s) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (n : ℕ) :
    blockEntropy μ n + S.blockEnergy s μ n ≤ Real.log (S.svfSum s n) := by
  rw [S.blockEnergy_eq_integral μ n, add_comm]
  exact S.integral_log_svf_add_blockEntropy_le n hs

/-- The energy at level `n` is at least `n s log δ` when every `|a_i|` and `|b_i|` is at least
`δ`. -/
theorem le_blockEnergy (hδ : S.RatioLowerBound δ) (hs : 0 ≤ s) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (n : ℕ) : n * (s * Real.log δ) ≤ S.blockEnergy s μ n := by
  have key : ∀ w : Fin n → ι,
      (n : ℝ) * (s * Real.log δ) ≤ Real.log (svf s (S.matWord (List.ofFn w))) := by
    intro w
    have h := hδ.le_log_svf_matWord hs (List.ofFn w)
    rw [List.length_ofFn] at h
    linarith
  calc (n : ℝ) * (s * Real.log δ)
      = ∑ w : Fin n → ι, μ.real (cylinder w) * ((n : ℝ) * (s * Real.log δ)) := by
        rw [← Finset.sum_mul, sum_measureReal_cylinder, one_mul]
    _ ≤ S.blockEnergy s μ n :=
        Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (key w) measureReal_nonneg

/-- The sum of the block entropy and the block energy at level `l` is bounded by `l C` for every
probability measure, with a constant `C` depending only on the system and on `s`. -/
theorem exists_blockBound [Nonempty ι] (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ μ : Measure (ℤ → ι), IsProbabilityMeasure μ → ∀ l : ℕ,
      |blockEntropy μ l + S.blockEnergy s μ l| ≤ l * C := by
  obtain ⟨δ, hδ⟩ := S.exists_ratioLowerBound
  refine ⟨|Real.log (S.svfSum s 1)| + |s * Real.log δ|, by positivity, fun μ hμ l => ?_⟩
  have := hμ
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hC1 : Real.log (S.svfSum s 1) ≤ |Real.log (S.svfSum s 1)| + |s * Real.log δ| :=
    (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
  have hC2 : -(|Real.log (S.svfSum s 1)| + |s * Real.log δ|) ≤ s * Real.log δ := by
    have := neg_abs_le (s * Real.log δ)
    have := abs_nonneg (Real.log (S.svfSum s 1))
    linarith
  have hup : blockEntropy μ l + S.blockEnergy s μ l
      ≤ l * (|Real.log (S.svfSum s 1)| + |s * Real.log δ|) := by
    have h1 := S.blockEntropy_add_blockEnergy_le hs μ l
    have h2 := S.log_svfSum_le hδ hs l
    have h3 := mul_le_mul_of_nonneg_left hC1 hl
    linarith
  have hlow : -(l * (|Real.log (S.svfSum s 1)| + |s * Real.log δ|))
      ≤ blockEntropy μ l + S.blockEnergy s μ l := by
    have h1 := blockEntropy_nonneg μ l
    have h2 := S.le_blockEnergy hδ hs μ l
    have h3 := mul_le_mul_of_nonneg_left hC2 hl
    rw [mul_neg] at h3
    linarith
  rw [abs_le]
  exact ⟨hlow, hup⟩

end System

/-! ### The measures of Misiurewicz's construction -/

namespace System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [Nonempty ι]
  (S : System ι) (s : ℝ) (n : ℕ)

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- `∑_{|𝐢| = n} φ^s(A_𝐢) > 0`: every term is positive. -/
theorem svfSum_pos_of_nonempty : 0 < S.svfSum s n :=
  Finset.sum_pos (fun _ _ => S.svf_matWord_pos s _) Finset.univ_nonempty

/-- The weights `p_𝐢 = φ^s(A_𝐢) / ∑_{|𝐣| = n} φ^s(A_𝐣)` on the words of length `n`. -/
noncomputable def blockWeight (w : Fin n → ι) : ℝ :=
  svf s (S.matWord (List.ofFn w)) / S.svfSum s n

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The weights of the words of length `n` are positive. -/
theorem blockWeight_pos (w : Fin n → ι) : 0 < S.blockWeight s n w :=
  div_pos (S.svf_matWord_pos s _) (S.svfSum_pos_of_nonempty s n)

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The weights of the words of length `n` form a probability vector. -/
theorem sum_blockWeight : ∑ w : Fin n → ι, S.blockWeight s n w = 1 := by
  simp only [blockWeight]
  rw [← Finset.sum_div, ← svfSum]
  exact div_self (S.svfSum_pos_of_nonempty s n).ne'

omit [MeasurableSingletonClass ι] in
/-- The weights of the words of length `n` as a probability measure on the alphabet of the
blocks of length `n`. -/
theorem isProbabilityMeasure_blockWeightMeasure :
    IsProbabilityMeasure (weightMeasure (S.blockWeight s n)) :=
  isProbabilityMeasure_weightMeasure (fun w => (S.blockWeight_pos s n w).le)
    (S.sum_blockWeight s n)

/-- The image under the concatenation of blocks of the Bernoulli measure with the weights
`p_𝐢 = φ^s(A_𝐢) / ∑_{|𝐣| = n} φ^s(A_𝐣)`. It is invariant under `σ^n`, but not under `σ`. -/
noncomputable def blockMeasure [NeZero n] : Measure (ℤ → ι) :=
  (bernoulli (weightMeasure (S.blockWeight s n))).map (concat n)

/-- The block measure is a probability measure. -/
instance isProbabilityMeasure_blockMeasure [NeZero n] :
    IsProbabilityMeasure (S.blockMeasure s n) := by
  have := S.isProbabilityMeasure_blockWeightMeasure s n
  rw [blockMeasure]
  infer_instance

/-- Every translate of the block measure is a probability measure. -/
instance isProbabilityMeasure_map_shift_blockMeasure [NeZero n] (j : ℤ) :
    IsProbabilityMeasure ((S.blockMeasure s n).map (shift j)) :=
  inferInstance

/-- The cylinder `[𝐢]` of a word of length `n` has the weight `p_𝐢` for the block measure. -/
theorem measureReal_blockMeasure_cylinder [NeZero n] (w : Fin n → ι) :
    (S.blockMeasure s n).real (cylinder w) = S.blockWeight s n w := by
  have := S.isProbabilityMeasure_blockWeightMeasure s n
  rw [blockMeasure, map_measureReal_apply (measurable_concat n) (measurableSet_cylinder w),
    preimage_concat_cylinder, measureReal_bernoulli_cylinder, Fin.prod_univ_one,
    Matrix.cons_val_zero, measureReal_weightMeasure_singleton (S.blockWeight_pos s n w).le]

omit [MeasurableSingletonClass ι] in
/-- The block measure is invariant under `σ^n`. -/
theorem map_shift_blockMeasure [NeZero n] :
    (S.blockMeasure s n).map (shift (n : ℤ)) = S.blockMeasure s n := by
  have := S.isProbabilityMeasure_blockWeightMeasure s n
  have hcomp : (shift (n : ℤ)) ∘ (concat n : (ℤ → (Fin n → ι)) → ℤ → ι) = concat n ∘ shift 1 :=
    funext fun y => (concat_shift n y).symm
  rw [blockMeasure, Measure.map_map (measurable_shift (n : ℤ)) (measurable_concat n), hcomp,
    ← Measure.map_map (measurable_concat n) (measurable_shift 1),
    (measurePreserving_shift_bernoulli _ 1).map_eq]

/-- Gibbs' inequality is an equality for the weights `p_𝐢 = φ^s(A_𝐢)/∑_{|𝐣| = n} φ^s(A_𝐣)`:
the block entropy and the block energy of the block measure at level `n` add up to
`log ∑_{|𝐢| = n} φ^s(A_𝐢)`. -/
theorem blockEntropy_add_blockEnergy_blockMeasure [NeZero n] :
    blockEntropy (S.blockMeasure s n) n + S.blockEnergy s (S.blockMeasure s n) n
      = Real.log (S.svfSum s n) := by
  have hdefect := sum_gibbs_defect (p := S.blockWeight s n)
    (q := fun w : Fin n → ι => svf s (S.matWord (List.ofFn w))) (S.sum_blockWeight s n)
    (fun _ => S.svf_matWord_pos s _)
  have hZ : ∑ w : Fin n → ι, svf s (S.matWord (List.ofFn w)) = S.svfSum s n := rfl
  rw [hZ] at hdefect
  have hzero : ∀ w : Fin n → ι, svf s (S.matWord (List.ofFn w)) / S.svfSum s n
      - S.blockWeight s n w - (Real.negMulLog (S.blockWeight s n w) + S.blockWeight s n w
        * Real.log (svf s (S.matWord (List.ofFn w)) / S.svfSum s n)) = 0 := by
    intro w
    rw [← blockWeight, Real.negMulLog]
    ring
  rw [Finset.sum_congr rfl fun w _ => hzero w, Finset.sum_const_zero] at hdefect
  rw [blockEntropy, blockEnergy]
  simp only [S.measureReal_blockMeasure_cylinder]
  linarith

/-- The average `n⁻¹ ∑_{k < n} (σ^k)_*μ` of the first `n` translates of the block measure. -/
noncomputable def avgBlockMeasure [NeZero n] : Measure (ℤ → ι) :=
  (n : ℝ≥0∞)⁻¹ • ∑ j ∈ Finset.range n, (S.blockMeasure s n).map (shift (j : ℤ))

omit [MeasurableSingletonClass ι] [Nonempty ι] in
/-- The measure of a set for the average of the translates, in `ℝ≥0∞`. -/
theorem avgBlockMeasure_apply [NeZero n] (A : Set (ℤ → ι)) :
    S.avgBlockMeasure s n A
      = (n : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range n, ((S.blockMeasure s n).map (shift (j : ℤ))) A := by
  rw [avgBlockMeasure, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]

/-- The average of the translates of the block measure is a probability measure. -/
instance isProbabilityMeasure_avgBlockMeasure [NeZero n] :
    IsProbabilityMeasure (S.avgBlockMeasure s n) := by
  constructor
  rw [S.avgBlockMeasure_apply s n]
  have hone : ∀ j ∈ Finset.range n,
      ((S.blockMeasure s n).map (shift (j : ℤ))) Set.univ = 1 := fun j _ => measure_univ
  rw [Finset.sum_congr rfl hone, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 (NeZero.ne n)) (ENNReal.natCast_ne_top n)]

omit [MeasurableSingletonClass ι] in
/-- The measure of a set for the average of the translates. -/
theorem measureReal_avgBlockMeasure [NeZero n] (A : Set (ℤ → ι)) :
    (S.avgBlockMeasure s n).real A
      = (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, ((S.blockMeasure s n).map (shift (j : ℤ))).real A := by
  rw [measureReal_def, S.avgBlockMeasure_apply s n, ENNReal.toReal_mul,
    ENNReal.toReal_sum fun j _ => measure_ne_top _ _, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rfl

omit [MeasurableSingletonClass ι] in
/-- The sum of the measures of a set over the translates. -/
theorem sum_measureReal_map_shift [NeZero n] (A : Set (ℤ → ι)) :
    ∑ j ∈ Finset.range n, ((S.blockMeasure s n).map (shift (j : ℤ))).real A
      = n * (S.avgBlockMeasure s n).real A := by
  rw [S.measureReal_avgBlockMeasure s n A, ← mul_assoc,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 (NeZero.ne n)), one_mul]

omit [MeasurableSingletonClass ι] in
/-- The average of the translates of the block measure is invariant under `σ`. -/
theorem measurePreserving_shift_avgBlockMeasure [NeZero n] :
    MeasurePreserving (shift 1) (S.avgBlockMeasure s n) (S.avgBlockMeasure s n) := by
  have hcast : ∀ j : ℕ, ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := fun j => by push_cast; ring
  have hf : ∀ (j : ℕ) (A : Set (ℤ → ι)), MeasurableSet A →
      ((S.blockMeasure s n).map (shift ((j + 1 : ℕ) : ℤ))).real A
        = ((S.blockMeasure s n).map (shift (j : ℤ))).real (shift 1 ⁻¹' A) := by
    intro j A hA
    rw [map_measureReal_apply (measurable_shift _) hA,
      map_measureReal_apply (measurable_shift _) (measurable_shift 1 hA)]
    congr 1
    ext x
    simp only [Set.mem_preimage, shift_shift, hcast]
  have hzero : ∀ A : Set (ℤ → ι),
      ((S.blockMeasure s n).map (shift ((0 : ℕ) : ℤ))).real A = (S.blockMeasure s n).real A := by
    intro A
    have h0 : (shift ((0 : ℕ) : ℤ) : (ℤ → ι) → ℤ → ι) = id := by
      funext x k
      simp
    rw [h0, Measure.map_id]
  have hnn : ∀ A : Set (ℤ → ι),
      ((S.blockMeasure s n).map (shift ((n : ℕ) : ℤ))).real A = (S.blockMeasure s n).real A := by
    intro A
    rw [S.map_shift_blockMeasure s n]
  refine ⟨measurable_shift 1, Measure.ext fun A hA => ?_⟩
  rw [Measure.map_apply (measurable_shift 1) hA,
    ← ofReal_measureReal (measure_ne_top (S.avgBlockMeasure s n) (shift 1 ⁻¹' A)),
    ← ofReal_measureReal (measure_ne_top (S.avgBlockMeasure s n) A)]
  congr 1
  rw [S.measureReal_avgBlockMeasure s n, S.measureReal_avgBlockMeasure s n]
  congr 1
  rw [Finset.sum_congr rfl fun j _ => (hf j A hA).symm]
  exact sum_range_shift_eq
    (f := fun j : ℕ => ((S.blockMeasure s n).map (shift (j : ℤ))).real A)
    (by rw [hzero, hnn])

end System


/-! ### The Misiurewicz estimate -/

namespace System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) (s : ℝ)

/-- The sum of the block entropy and the block energy at level `l` for the translate
`(σ^j)_*μ`. -/
noncomputable def blockSum (μ : Measure (ℤ → ι)) (j l : ℕ) : ℝ :=
  blockEntropy (μ.map (shift (j : ℤ))) l + S.blockEnergy s (μ.map (shift (j : ℤ))) l

variable {s}

omit [MeasurableSingletonClass ι] in
/-- At `j = 0` the block sum is that of the measure itself. -/
theorem blockSum_zero_left (μ : Measure (ℤ → ι)) (l : ℕ) :
    S.blockSum s μ 0 l = blockEntropy μ l + S.blockEnergy s μ l := by
  have h0 : (shift ((0 : ℕ) : ℤ) : (ℤ → ι) → ℤ → ι) = id := by
    funext x k
    simp
  rw [blockSum, h0, Measure.map_id]

/-- The block sums are sub-additive in the length: the second term is the block sum of the
translate by `l₁`. -/
theorem blockSum_add_le (hs : 0 ≤ s) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (j l₁ l₂ : ℕ) :
    S.blockSum s μ j (l₁ + l₂) ≤ S.blockSum s μ j l₁ + S.blockSum s μ (j + l₁) l₂ := by
  have hmap : (μ.map (shift (j : ℤ))).map (shift (l₁ : ℤ))
      = μ.map (shift ((j + l₁ : ℕ) : ℤ)) := by
    rw [Measure.map_map (measurable_shift _) (measurable_shift _)]
    congr 1
    funext x
    rw [Function.comp_apply, shift_shift]
    push_cast
    ring_nf
  have h1 := blockEntropy_add_le' (μ.map (shift (j : ℤ))) l₁ l₂
  have h2 := S.blockEnergy_add_le hs (μ.map (shift (j : ℤ))) l₁ l₂
  rw [hmap] at h1 h2
  unfold blockSum
  linarith

omit [MeasurableSingletonClass ι] in
/-- The block sums of the translates are bounded by `l C`. -/
theorem abs_blockSum_le {C : ℝ}
    (hCb : ∀ μ : Measure (ℤ → ι), IsProbabilityMeasure μ → ∀ l : ℕ,
      |blockEntropy μ l + S.blockEnergy s μ l| ≤ l * C)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (j l : ℕ) : |S.blockSum s μ j l| ≤ l * C :=
  hCb _ inferInstance l

/-- Iterating the sub-additivity of the block sums along the blocks of length `m`. -/
theorem blockSum_chain_le (hs : 0 ≤ s) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (m : ℕ) :
    ∀ (a j z : ℕ), S.blockSum s μ j (a * m + z)
      ≤ (∑ r ∈ Finset.range a, S.blockSum s μ (j + r * m) m) + S.blockSum s μ (j + a * m) z := by
  intro a
  induction a with
  | zero => intro j z; simp
  | succ a ih =>
    intro j z
    have h1 := S.blockSum_add_le hs μ j m (a * m + z)
    have h2 := ih (j + m) z
    have hsum : ∑ r ∈ Finset.range a, S.blockSum s μ (j + m + r * m) m
        = ∑ r ∈ Finset.range a, S.blockSum s μ (j + (r + 1) * m) m :=
      Finset.sum_congr rfl fun r _ => by
        have hr : j + m + r * m = j + (r + 1) * m := by ring
        rw [hr]
    have hidx : j + m + a * m = j + (a + 1) * m := by ring
    rw [hsum, hidx] at h2
    have h3 : ∑ r ∈ Finset.range (a + 1), S.blockSum s μ (j + r * m) m
        = (∑ r ∈ Finset.range a, S.blockSum s μ (j + (r + 1) * m) m)
          + S.blockSum s μ (j + 0 * m) m :=
      Finset.sum_range_succ' (fun r => S.blockSum s μ (j + r * m) m) a
    simp only [Nat.zero_mul, Nat.add_zero] at h3
    have he : (a + 1) * m + z = m + (a * m + z) := by ring
    rw [he, h3]
    linarith

variable [Nonempty ι]

omit [MeasurableSingletonClass ι] in
/-- The block sums of the translates of the block measure add up to at most `n` times the block
sum of the average of the translates: the energy is affine in the measure and the entropy is
concave. -/
theorem sum_blockSum_le {n : ℕ} [NeZero n] (m : ℕ) :
    ∑ j ∈ Finset.range n, S.blockSum s (S.blockMeasure s n) j m
      ≤ n * (blockEntropy (S.avgBlockMeasure s n) m
        + S.blockEnergy s (S.avgBlockMeasure s n) m) := by
  have hn0 : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  have hn0' : (0 : ℝ) < n := lt_of_le_of_ne (Nat.cast_nonneg n) (Ne.symm hn0)
  have hcyl : ∀ w : Fin m → ι,
      ∑ j ∈ Finset.range n, ((S.blockMeasure s n).map (shift (j : ℤ))).real (cylinder w)
        = n * (S.avgBlockMeasure s n).real (cylinder w) :=
    fun w => S.sum_measureReal_map_shift s n _
  have henergy : ∑ j ∈ Finset.range n, S.blockEnergy s ((S.blockMeasure s n).map (shift (j : ℤ))) m
      = n * S.blockEnergy s (S.avgBlockMeasure s n) m := by
    simp only [blockEnergy]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.sum_mul, hcyl w, mul_assoc]
  have hentropy : ∑ j ∈ Finset.range n, blockEntropy ((S.blockMeasure s n).map (shift (j : ℤ))) m
      ≤ n * blockEntropy (S.avgBlockMeasure s n) m := by
    simp only [blockEntropy]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    have hw0 : ∀ j ∈ Finset.range n, (0 : ℝ) ≤ (n : ℝ)⁻¹ := fun _ _ => by positivity
    have hw1 : ∑ _j ∈ Finset.range n, (n : ℝ)⁻¹ = 1 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_inv_cancel₀ hn0]
    have hmem : ∀ j ∈ Finset.range n,
        ((S.blockMeasure s n).map (shift (j : ℤ))).real (cylinder w) ∈ Set.Ici (0 : ℝ) :=
      fun _ _ => measureReal_nonneg
    have h := Real.concaveOn_negMulLog.le_map_sum hw0 hw1 hmem
    simp only [smul_eq_mul] at h
    have hrhs : ∑ j ∈ Finset.range n,
        (n : ℝ)⁻¹ * ((S.blockMeasure s n).map (shift (j : ℤ))).real (cylinder w)
          = (S.avgBlockMeasure s n).real (cylinder w) := by
      rw [← Finset.mul_sum, hcyl w, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
    have hlhs : ∑ j ∈ Finset.range n,
        (n : ℝ)⁻¹ * Real.negMulLog (((S.blockMeasure s n).map (shift (j : ℤ))).real (cylinder w))
          = (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n,
            Real.negMulLog (((S.blockMeasure s n).map (shift (j : ℤ))).real (cylinder w)) :=
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
theorem log_svfSum_le_avgBlockMeasure (hs : 0 ≤ s) {C : ℝ} (hC : 0 ≤ C)
    (hCb : ∀ μ : Measure (ℤ → ι), IsProbabilityMeasure μ → ∀ l : ℕ,
      |blockEntropy μ l + S.blockEnergy s μ l| ≤ l * C)
    {n m : ℕ} [NeZero n] (hm : 0 < m) (hmn : m ≤ n) :
    m * Real.log (S.svfSum s n)
      ≤ n * (blockEntropy (S.avgBlockMeasure s n) m + S.blockEnergy s (S.avgBlockMeasure s n) m)
        + 5 * m ^ 2 * C := by
  obtain ⟨a, ha⟩ : ∃ a, n / m = a + 1 := ⟨n / m - 1, by
    have h1 : 1 ≤ n / m := (Nat.one_le_div_iff hm).2 hmn
    omega⟩
  have hsplit : a * m + m + n % m = n := by
    have h := Nat.div_add_mod n m
    rw [ha, Nat.mul_succ, Nat.mul_comm] at h
    omega
  have hmodlt : n % m < m := Nat.mod_lt _ hm
  have hmC : 0 ≤ (m : ℝ) * C := mul_nonneg (Nat.cast_nonneg m) hC
  have hlogZ : blockEntropy (S.blockMeasure s n) n + S.blockEnergy s (S.blockMeasure s n) n
      = Real.log (S.svfSum s n) := S.blockEntropy_add_blockEnergy_blockMeasure s n
  have key : ∀ k ∈ Finset.range m, Real.log (S.svfSum s n)
      ≤ (∑ r ∈ Finset.range a, S.blockSum s (S.blockMeasure s n) (k + r * m) m)
        + 3 * ((m : ℝ) * C) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hz : k + (a * m + (n - (k + a * m))) = n := by omega
    have h1 := S.blockSum_add_le hs (S.blockMeasure s n) 0 k (a * m + (n - (k + a * m)))
    rw [hz, Nat.zero_add] at h1
    have h2 := S.blockSum_chain_le hs (S.blockMeasure s n) m a k (n - (k + a * m))
    have h3 := (abs_le.1 (S.abs_blockSum_le hCb (S.blockMeasure s n) 0 k)).2
    have h4 := (abs_le.1 (S.abs_blockSum_le hCb (S.blockMeasure s n) (k + a * m)
      (n - (k + a * m)))).2
    have h5 : (k : ℝ) * C ≤ (m : ℝ) * C :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hk.le) hC
    have h6 : ((n - (k + a * m) : ℕ) : ℝ) * C ≤ 2 * ((m : ℝ) * C) := by
      have hle : (n - (k + a * m) : ℕ) ≤ 2 * m := by omega
      have : ((n - (k + a * m) : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hle
      calc ((n - (k + a * m) : ℕ) : ℝ) * C ≤ (2 * (m : ℝ)) * C :=
            mul_le_mul_of_nonneg_right this hC
        _ = 2 * ((m : ℝ) * C) := by ring
    rw [S.blockSum_zero_left (S.blockMeasure s n) n, hlogZ] at h1
    linarith
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hreindex : ∑ k ∈ Finset.range m,
      ∑ r ∈ Finset.range a, S.blockSum s (S.blockMeasure s n) (k + r * m) m
      = ∑ j ∈ Finset.range (a * m), S.blockSum s (S.blockMeasure s n) j m := by
    rw [sum_range_mul_eq]
    exact Finset.sum_comm
  rw [hreindex] at hsum
  have hd : a * m + (n - a * m) = n := by omega
  have hsplit2 : ∑ j ∈ Finset.range n, S.blockSum s (S.blockMeasure s n) j m
      = (∑ j ∈ Finset.range (a * m), S.blockSum s (S.blockMeasure s n) j m)
        + ∑ i ∈ Finset.range (n - a * m), S.blockSum s (S.blockMeasure s n) (a * m + i) m := by
    have h := Finset.sum_range_add (fun j => S.blockSum s (S.blockMeasure s n) j m)
      (a * m) (n - a * m)
    rw [hd] at h
    exact h
  have hlow : ∀ i ∈ Finset.range (n - a * m),
      -((m : ℝ) * C) ≤ S.blockSum s (S.blockMeasure s n) (a * m + i) m := fun i _ =>
    (abs_le.1 (S.abs_blockSum_le hCb (S.blockMeasure s n) (a * m + i) m)).1
  have hcard := Finset.card_nsmul_le_sum (Finset.range (n - a * m))
    (fun i => S.blockSum s (S.blockMeasure s n) (a * m + i) m) (-((m : ℝ) * C)) hlow
  rw [Finset.card_range, nsmul_eq_mul] at hcard
  have htail : -(2 * (m : ℝ) * ((m : ℝ) * C))
      ≤ ∑ i ∈ Finset.range (n - a * m), S.blockSum s (S.blockMeasure s n) (a * m + i) m := by
    refine le_trans ?_ hcard
    have hle : (n - a * m : ℕ) ≤ 2 * m := by omega
    have h' : ((n - a * m : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hle
    nlinarith
  have havg : ∑ j ∈ Finset.range n, S.blockSum s (S.blockMeasure s n) j m
      ≤ n * (blockEntropy (S.avgBlockMeasure s n) m
        + S.blockEnergy s (S.avgBlockMeasure s n) m) := S.sum_blockSum_le m
  have hsq : (m : ℝ) * (3 * ((m : ℝ) * C)) + 2 * (m : ℝ) * ((m : ℝ) * C)
      = 5 * (m : ℝ) ^ 2 * C := by ring
  have step1 : ∑ j ∈ Finset.range (a * m), S.blockSum s (S.blockMeasure s n) j m
      ≤ (∑ j ∈ Finset.range n, S.blockSum s (S.blockMeasure s n) j m)
        + 2 * (m : ℝ) * ((m : ℝ) * C) := by
    linarith [hsplit2, htail]
  linarith [hsum, step1, havg, hsq]

/-! ### The limit measure -/

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The pressure is at most `log ∑_{|𝐢| = n} φ^s(A_𝐢) / n` for every `n ≥ 1`, since it is the
infimum of these quotients. -/
theorem pressure_le_log_svfSum_div (hδ : S.RatioLowerBound δ) (hs : 0 ≤ s) {n : ℕ}
    (hn : 1 ≤ n) : S.pressure s ≤ Real.log (S.svfSum s n) / n :=
  csInf_le (BddBelow.mono (Set.image_subset_range _ _) (hδ.bddBelow hs)) ⟨n, hn, rfl⟩

/-- **The existence half of the variational principle.** There is a `σ`-invariant probability
measure with `P(𝖠, s) ≤ h_0(μ) + Λ(𝖠, μ, s)`, for every `s ≥ 0`. The measure is a limit of the
averages `avgBlockMeasure` of Misiurewicz's construction. -/
theorem exists_invariant_pressure_le (hs : 0 ≤ s) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
      S.pressure s ≤ entropy μ + S.energyLim s μ := by
  obtain ⟨C, hC, hCb⟩ := S.exists_blockBound hs
  obtain ⟨δ, hδ⟩ := S.exists_ratioLowerBound
  set μs : ℕ → Measure (ℤ → ι) := fun n => S.avgBlockMeasure s (n + 1) with hμs
  have hprob : ∀ n, IsProbabilityMeasure (μs n) := fun n => inferInstance
  have hinvs : ∀ n, MeasurePreserving (shift 1) (μs n) (μs n) := fun n =>
    S.measurePreserving_shift_avgBlockMeasure s (n + 1)
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
  have hcoe : ∀ (R : ProbabilityMeasure (ℤ → ι)) (A : Set (ℤ → ι)),
      ((R A : NNReal) : ℝ) = (R : Measure (ℤ → ι)).real A := fun R A => by
    rw [measureReal_def, ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_toReal]
  have hconv : ∀ A : Set (ℤ → ι), IsClopen A →
      Tendsto (fun n => (μs n).real A) (U : Filter ℕ)
        (𝓝 ((Q : Measure (ℤ → ι)).real A)) := by
    intro A hA
    have h := (NNReal.continuous_coe.tendsto _).comp
      (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hten hA)
    rw [Function.comp_def, hcoe Q] at h
    exact h.congr fun n => hcoe (P n) A
  -- the limit measure is invariant
  have hQshift : ∀ (k : ℤ) (m : ℕ) (w : Fin m → ι),
      (Q : Measure (ℤ → ι)).real (shift k ⁻¹' cylinder w)
        = (Q : Measure (ℤ → ι)).real (cylinder w) := by
    intro k m w
    refine tendsto_nhds_unique (hconv _ (isClopen_preimage_shift_cylinder k w)) ?_
    exact (hconv _ (isClopen_cylinder w)).congr fun n =>
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
      (m : ℝ) * S.pressure s ≤ blockEntropy (Q : Measure (ℤ → ι)) m
        + S.blockEnergy s (Q : Measure (ℤ → ι)) m := by
    intro m hm
    have hcyl : ∀ w : Fin m → ι, Tendsto (fun n => (μs n).real (cylinder w)) (U : Filter ℕ)
        (𝓝 ((Q : Measure (ℤ → ι)).real (cylinder w))) := fun w => hconv _ (isClopen_cylinder w)
    have hB1 : Tendsto (fun n => blockEntropy (μs n) m) (U : Filter ℕ)
        (𝓝 (blockEntropy (Q : Measure (ℤ → ι)) m)) :=
      tendsto_finsetSum _ fun w _ => (Real.continuous_negMulLog.tendsto _).comp (hcyl w)
    have hB2 : Tendsto (fun n => S.blockEnergy s (μs n) m) (U : Filter ℕ)
        (𝓝 (S.blockEnergy s (Q : Measure (ℤ → ι)) m)) :=
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
    have hkey := S.log_svfSum_le_avgBlockMeasure hs hC hCb (n := n + 1) (m := m) hm hmn
    have hpre := S.pressure_le_log_svfSum_div hδ hs (n := n + 1) (Nat.succ_le_succ (Nat.zero_le n))
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn1' : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hn1', le_div_iff₀ hn1, mul_comm] at hpre
    rw [hn1'] at hkey
    have hmnn : (m : ℝ) * (((n : ℝ) + 1) * S.pressure s)
        ≤ (m : ℝ) * Real.log (S.svfSum s (n + 1)) :=
      mul_le_mul_of_nonneg_left hpre (Nat.cast_nonneg m)
    have hfinal : ((n : ℝ) + 1) * ((m : ℝ) * S.pressure s)
        ≤ ((n : ℝ) + 1) * (blockEntropy (μs n) m + S.blockEnergy s (μs n) m
          + (5 * (m : ℝ) ^ 2 * C) * (1 / ((n : ℝ) + 1))) := by
      have hdiv : ((n : ℝ) + 1) * ((5 * (m : ℝ) ^ 2 * C) * (1 / ((n : ℝ) + 1)))
          = 5 * (m : ℝ) ^ 2 * C := by
        field_simp
      rw [mul_add, hdiv]
      nlinarith
    exact le_of_mul_le_mul_left hfinal hn1
  have hlim := (tendsto_entropy hinvQ).add (S.tendsto_energyLim hinvQ hs)
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have h := hblock m hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [← S.blockEnergy_eq_integral (Q : Measure (ℤ → ι)) m, ← add_div, le_div_iff₀ hm', mul_comm]
  exact h

/-- The form of `exists_invariant_pressure_le` with an error `ε`. -/
theorem exists_invariant_le_entropy_add_energy (hs : 0 ≤ s) {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
      S.pressure s - ε ≤ entropy μ + S.energyLim s μ := by
  obtain ⟨μ, hprob, hinv, h⟩ := S.exists_invariant_pressure_le hs
  exact ⟨μ, hprob, hinv, by linarith⟩

/-- **Existence of an `s`-equilibrium state**, the existence part of `thm:irred_eq_state` (tex
lines 2209 to 2218), for every `s ≥ 0` and with no irreducibility hypothesis: the measure of
`exists_invariant_pressure_le` satisfies `eq:eq_state_def`, since the variational inequality
`eq:variational` gives the reverse inequality. -/
theorem exists_isEquilibriumState (hs : 0 ≤ s) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
      S.IsEquilibriumState s μ := by
  obtain ⟨μ, hprob, hinv, h⟩ := S.exists_invariant_pressure_le hs
  have := hprob
  exact ⟨μ, hprob, hinv, le_antisymm h (S.entropy_add_energyLim_le_pressure hinv hs)⟩

end System

end BoxLike

