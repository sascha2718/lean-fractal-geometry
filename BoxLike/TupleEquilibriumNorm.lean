module

/-
The norm potential of Feng–Käenmäki and the reductions of `thm:irred_eq_state` to it (tex
lines 2235 to 2239). Feng–Käenmäki, *Equilibrium states of the pressure function for products
of matrices*, Discrete Contin. Dyn. Syst. 30 (2011), work on the one-sided full shift
`Σ^+ = ℕ → ι` with the potential `𝐢 ↦ ‖A_𝐢‖^q`, `q > 0`: the pressure is
`P(q) = lim_n n⁻¹ log ∑_{|𝐢| = n} ‖A_𝐢‖^q` (their (1.1)), the Lyapunov exponent of an
invariant measure is `M_*(ν) = lim_n n⁻¹ ∑_{|𝐢| = n} ν([𝐢]) log ‖A_𝐢‖` (their (1.2)), a
`q`-equilibrium state is an invariant `ν` with `P(q) = q M_*(ν) + h(ν)` (their (1.4)), and the
Gibbs property is their (1.6). This module defines these objects and proves the reductions the
article makes: from the one-sided to the two-sided shift, `φ^s = ‖·‖^s` for `0 < s ≤ 1`, and
`φ^s(A_𝐢) = ‖A'_𝐢‖^{2-s}` for `1 < s < 2` with the rescaled tuple
`A'_i = |det A_i|^{(s-1)/(2-s)} A_i`, which is invertible and irreducible when `𝖠` is.

* `blockEntropyPlus`, `entropyPlus`: the entropy of a measure on `Σ^+`, as the entropy rate of
  the generating partition into the cylinders `futureCylinder`.
* `MatrixTuple.normSum`, `MatrixTuple.normPressure`, `MatrixTuple.normLyapPlus`,
  `MatrixTuple.IsNormEquilibriumPlus`, `MatrixTuple.HasNormGibbsPlus`: (1.1), (1.2), (1.4) and
  (1.6) of Feng–Käenmäki on `Σ^+`.
* `MatrixTuple.IsNormEquilibrium`, `MatrixTuple.HasNormGibbs`: the same on the two-sided shift
  `Σ`, with `M_*` the exponent `λ_1`.
* `MatrixTuple.isNormEquilibriumPlus_map_eta_iff`, `MatrixTuple.hasNormGibbsPlus_map_eta_iff`:
  the two-sided-shift reduction: `μ ∈ ℳ_σ(Σ)` is a `q`-equilibrium state, or has the Gibbs
  property, exactly when `η_*μ ∈ ℳ_σ(Σ^+)` does.
* `MatrixTuple.tendsto_lyapunov₁`: the limit defining `λ_1(𝖠, μ)` exists.
* `MatrixTuple.tendsto_normPressure`, `tendsto_entropyPlus`, `MatrixTuple.tendsto_normLyapPlus`:
  the limits (1.1), (1.2) and `h(ν)` of Feng–Käenmäki exist, so that their objects are the
  limits and not junk values.
* `MatrixTuple.exists_one_le_bounds`: Gibbs bounds with a constant `C > 0` hold with a constant
  `C ≥ 1`.
* `MatrixTuple.isEquilibriumState_iff_isNormEquilibrium`,
  `MatrixTuple.hasGibbsBounds_iff_hasNormGibbs`: the case `0 < s ≤ 1`, with `q = s`.
* `MatrixTuple.rescale`, `MatrixTuple.det_rescale_ne_zero`, `MatrixTuple.tupleIrreducible_rescale`,
  `MatrixTuple.norm_word_rescale_rpow`: the rescaled tuple and `‖A'_𝐢‖^{2-s} = φ^s(A_𝐢)`.
* `MatrixTuple.isEquilibriumState_iff_rescale`, `MatrixTuple.hasGibbsBounds_iff_rescale`: the
  case `1 < s < 2`, with `q = 2 - s` for the rescaled tuple.
-/
public import BoxLike.Classification
public import BoxLike.InvariantMeasure
public import BoxLike.NaturalExtension
public import BoxLike.TupleEquilibrium

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

/-! ### Entropy on the one-sided shift -/

section OneSided

variable {α : Type*} [Fintype α] [MeasurableSpace α]

/-- The entropy `H_ν(𝒫_0^{n-1})` of the partition of `Σ^+` into the cylinders of length `n`. -/
noncomputable def blockEntropyPlus (ν : Measure (ℕ → α)) (n : ℕ) : ℝ :=
  ∑ w : Fin n → α, Real.negMulLog (ν.real (futureCylinder w))

/-- The entropy `h(ν) = lim_n H_ν(𝒫_0^{n-1}) / n` of a measure on `Σ^+`: the entropy of the
generating partition into the cylinders `[i]`, which is the measure-theoretic entropy of `ν` by
the Kolmogorov–Sinai theorem. -/
noncomputable def entropyPlus (ν : Measure (ℕ → α)) : ℝ :=
  limUnder atTop fun n : ℕ => blockEntropyPlus ν n / n

variable [MeasurableSingletonClass α]

omit [Fintype α] in
/-- The cylinder of `Σ^+` has under `η_*μ` the mass of the cylinder of `Σ` under `μ`. -/
theorem measureReal_map_eta_futureCylinder (μ : Measure (ℤ → α)) {n : ℕ} (w : Fin n → α) :
    (μ.map eta).real (futureCylinder w) = μ.real (cylinder w) := by
  rw [map_measureReal_apply measurable_eta (measurableSet_futureCylinder w)]
  rfl

/-- The block entropies of `η_*μ` are those of `μ`. -/
theorem blockEntropyPlus_map_eta (μ : Measure (ℤ → α)) (n : ℕ) :
    blockEntropyPlus (μ.map eta) n = blockEntropy μ n := by
  simp only [blockEntropyPlus, blockEntropy, measureReal_map_eta_futureCylinder]

/-- `h(η_*μ) = h(μ)`. -/
theorem entropyPlus_map_eta (μ : Measure (ℤ → α)) : entropyPlus (μ.map eta) = entropy μ := by
  simp only [entropyPlus, entropy, blockEntropyPlus_map_eta]

end OneSided

namespace MatrixTuple

variable {ι : Type*} (A : ι → Matrix (Fin 2) (Fin 2) ℝ)

/-! ### The norm potential -/

section Defs

variable [Fintype ι]

/-- The sum `∑_{|𝐢| = n} ‖A_𝐢‖^q`. -/
noncomputable def normSum (q : ℝ) (n : ℕ) : ℝ := ∑ w : Fin n → ι, ‖word A (List.ofFn w)‖ ^ q

/-- The pressure `P(q) = lim_n n⁻¹ log ∑_{|𝐢| = n} ‖A_𝐢‖^q` of the potential `‖·‖^q`,
Feng–Käenmäki (1.1). -/
noncomputable def normPressure (q : ℝ) : ℝ :=
  limUnder atTop fun n : ℕ => Real.log (normSum A q n) / n

variable [MeasurableSpace ι]

/-- The Lyapunov exponent `M_*(ν) = lim_n n⁻¹ ∑_{|𝐢| = n} ν([𝐢]) log ‖A_𝐢‖` of a measure on the
one-sided shift `Σ^+`, Feng–Käenmäki (1.2). -/
noncomputable def normLyapPlus (ν : Measure (ℕ → ι)) : ℝ :=
  limUnder atTop fun n : ℕ =>
    (∑ w : Fin n → ι, ν.real (futureCylinder w) * Real.log ‖word A (List.ofFn w)‖) / n

/-- `ν` is a `q`-equilibrium state of the pressure `P` on `Σ^+`, Feng–Käenmäki (1.4):
`P(q) = q M_*(ν) + h(ν)`. -/
def IsNormEquilibriumPlus (q : ℝ) (ν : Measure (ℕ → ι)) : Prop :=
  normPressure A q = q * normLyapPlus A ν + entropyPlus ν

/-- The Gibbs property (1.6) of Feng–Käenmäki on `Σ^+`: there is `C > 0` with
`C⁻¹ exp(-n P(q)) ‖A_𝐢‖^q ≤ ν([𝐢]) ≤ C exp(-n P(q)) ‖A_𝐢‖^q` for all words of length
`n ≥ 1`. -/
def HasNormGibbsPlus (q : ℝ) (ν : Measure (ℕ → ι)) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ w : Fin n → ι,
    C⁻¹ * (Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn w)‖ ^ q) ≤
        ν.real (futureCylinder w) ∧
      ν.real (futureCylinder w) ≤
        C * (Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn w)‖ ^ q)

/-- `μ` is a `q`-equilibrium state of the potential `‖·‖^q` on the two-sided shift `Σ`:
`P(q) = q λ_1(𝖠, μ) + h(μ)`. -/
def IsNormEquilibrium (q : ℝ) (μ : Measure (ℤ → ι)) : Prop :=
  normPressure A q = q * lyapunov₁ A μ + entropy μ

/-- The Gibbs property of the potential `‖·‖^q` on the two-sided shift `Σ`. -/
def HasNormGibbs (q : ℝ) (μ : Measure (ℤ → ι)) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ w : Fin n → ι,
    C⁻¹ * (Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn w)‖ ^ q) ≤
        μ.real (cylinder w) ∧
      μ.real (cylinder w) ≤
        C * (Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn w)‖ ^ q)

end Defs

/-! ### The two-sided-shift reduction -/

section TwoSided

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] {A}

/-- `M_*(η_*μ) = λ_1(𝖠, μ)`: the integral defining `λ_1` is the sum over the cylinders. -/
theorem normLyapPlus_map_eta (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] :
    normLyapPlus A (μ.map eta) = lyapunov₁ A μ := by
  simp only [normLyapPlus, lyapunov₁, measureReal_map_eta_futureCylinder,
    integral_comp_futureWord_eq_sum μ fun w => Real.log ‖word A w‖]

/-- The two-sided-shift reduction for the equilibrium states: `μ` is a `q`-equilibrium state
on `Σ` exactly when `η_*μ` is one on `Σ^+`. -/
theorem isNormEquilibriumPlus_map_eta_iff {q : ℝ} (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] :
    IsNormEquilibriumPlus A q (μ.map eta) ↔ IsNormEquilibrium A q μ := by
  rw [IsNormEquilibriumPlus, IsNormEquilibrium, normLyapPlus_map_eta, entropyPlus_map_eta]

/-- The two-sided-shift reduction for the Gibbs property: the cylinders of `Σ^+` under `η_*μ`
have the masses of the cylinders of `Σ` under `μ`. -/
theorem hasNormGibbsPlus_map_eta_iff {q : ℝ} (μ : Measure (ℤ → ι)) :
    HasNormGibbsPlus A q (μ.map eta) ↔ HasNormGibbs A q μ := by
  simp only [HasNormGibbsPlus, HasNormGibbs, measureReal_map_eta_futureCylinder]

end TwoSided

/-! ### The Lyapunov exponent `λ_1` of a tuple -/

variable {A}

/-- The limit defining `λ_1(𝖠, μ)` exists for an invariant measure, by Fekete's lemma:
`log ‖A_𝐢 A_𝐣‖ ≤ log ‖A_𝐢‖ + log ‖A_𝐣‖` and `log ‖A_𝐢‖ ≥ |𝐢| log δ`. -/
theorem tendsto_lyapunov₁ [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (hA : ∀ i, (A i).det ≠ 0) {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) :
    Tendsto (fun n : ℕ => (∫ x, Real.log ‖word A (futureWord x n)‖ ∂μ) / n) atTop
      (𝓝 (lyapunov₁ A μ)) := by
  have hsub : ∀ w w' : List ι,
      Real.log ‖word A (w ++ w')‖ ≤ Real.log ‖word A w‖ + Real.log ‖word A w'‖ := by
    intro w w'
    rw [← Real.log_mul (norm_word_pos hA w).ne' (norm_word_pos hA w').ne', word_append]
    exact Real.log_le_log (by rw [← word_append]; exact norm_word_pos hA _)
      (Matrix.l2_opNorm_mul _ _)
  obtain ⟨L, hL⟩ := exists_tendsto_integral_futureWord_div hμ
    (G := fun w => Real.log ‖word A w‖) hsub (le_log_norm_word hA)
  rw [lyapunov₁, hL.limUnder_eq]
  exact hL

/-! ### The limits of Feng–Käenmäki exist -/

/-- The limit `P(q)` of Feng–Käenmäki (1.1) exists for a tuple of invertible matrices and
`q ≥ 0`, by Fekete's lemma, so that `normPressure` is that limit. -/
theorem tendsto_normPressure [Fintype ι] [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) {q : ℝ}
    (hq : 0 ≤ q) :
    Tendsto (fun n : ℕ => Real.log (normSum A q n) / n) atTop (𝓝 (normPressure A q)) := by
  have hpos : ∀ n, 0 < normSum A q n := fun n =>
    Finset.sum_pos (fun _ _ => Real.rpow_pos_of_pos (norm_word_pos hA _) _) Finset.univ_nonempty
  have hsub : Subadditive fun n => Real.log (normSum A q n) := by
    intro m n
    rw [← Real.log_mul (hpos m).ne' (hpos n).ne']
    refine Real.log_le_log (hpos _) ?_
    rw [normSum, sum_ofFn_add m n fun w => ‖word A w‖ ^ q, normSum, normSum,
      Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun h _ => ?_
    rw [word_append, ← Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    exact Real.rpow_le_rpow (norm_nonneg _) (Matrix.l2_opNorm_mul _ _) hq
  have hbdd : BddBelow (Set.range fun n : ℕ => Real.log (normSum A q n) / n) := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    refine ⟨min 0 (q * Real.log (normLowerBound A)), ?_⟩
    rintro _ ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      refine (min_le_right _ _).trans ?_
      rw [le_div_iff₀ hn']
      have hw := le_log_norm_word hA (List.ofFn fun _ : Fin n => i)
      rw [List.length_ofFn] at hw
      have hle : ‖word A (List.ofFn fun _ : Fin n => i)‖ ^ q ≤ normSum A q n :=
        Finset.single_le_sum (f := fun w : Fin n → ι => ‖word A (List.ofFn w)‖ ^ q)
          (fun w _ => (Real.rpow_pos_of_pos (norm_word_pos hA _) _).le) (Finset.mem_univ _)
      have h := Real.log_le_log (Real.rpow_pos_of_pos (norm_word_pos hA _) _) hle
      rw [Real.log_rpow (norm_word_pos hA _)] at h
      nlinarith [mul_le_mul_of_nonneg_left hw hq]
  have h := hsub.tendsto_lim hbdd
  rw [normPressure, h.limUnder_eq]
  exact h

/-- The limit `h(ν)` exists for an invariant probability measure on `Σ^+`: `ν = η_*μ` for an
invariant `μ` on `Σ`, and the block entropies agree. -/
theorem _root_.BoxLike.tendsto_entropyPlus {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {ν : Measure (ℕ → α)} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving shiftPlus ν ν) :
    Tendsto (fun n : ℕ => blockEntropyPlus ν n / n) atTop (𝓝 (entropyPlus ν)) := by
  obtain ⟨μ, hμ, hinv, rfl⟩ := exists_map_eta_eq hν
  simp only [blockEntropyPlus_map_eta, entropyPlus_map_eta]
  exact tendsto_entropy hinv

/-- The limit `M_*(ν)` of Feng–Käenmäki (1.2) exists for an invariant probability measure on
`Σ^+`. -/
theorem tendsto_normLyapPlus [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (hA : ∀ i, (A i).det ≠ 0) {ν : Measure (ℕ → ι)} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving shiftPlus ν ν) :
    Tendsto (fun n : ℕ =>
      (∑ w : Fin n → ι, ν.real (futureCylinder w) * Real.log ‖word A (List.ofFn w)‖) / n)
      atTop (𝓝 (normLyapPlus A ν)) := by
  obtain ⟨μ, hμ, hinv, rfl⟩ := exists_map_eta_eq hν
  simp only [measureReal_map_eta_futureCylinder, normLyapPlus_map_eta,
    ← integral_comp_futureWord_eq_sum μ fun w => Real.log ‖word A w‖]
  exact tendsto_lyapunov₁ hA hinv

/-! ### Gibbs constants -/

/-- Bounds `C⁻¹ x ≤ y ≤ C x` with `C > 0` and `x ≥ 0` hold with the constant
`max C C⁻¹ ≥ 1`. -/
theorem exists_one_le_bounds {β : Type*} {x y : β → ℝ} (hx : ∀ b, 0 ≤ x b) {C : ℝ}
    (hC : 0 < C) (h : ∀ b, C⁻¹ * x b ≤ y b ∧ y b ≤ C * x b) :
    ∃ C' : ℝ, 1 ≤ C' ∧ ∀ b, C'⁻¹ * x b ≤ y b ∧ y b ≤ C' * x b := by
  refine ⟨max C C⁻¹, ?_, fun b => ⟨?_, ?_⟩⟩
  · rcases le_total 1 C with h1 | h1
    · exact h1.trans (le_max_left _ _)
    · exact (one_le_inv₀ hC).2 h1 |>.trans (le_max_right _ _)
  · refine le_trans (mul_le_mul_of_nonneg_right ?_ (hx b)) (h b).1
    exact inv_anti₀ hC (le_max_left _ _)
  · exact (h b).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hx b))

/-! ### The case `0 < s ≤ 1` -/

section SmallExponent

variable [Fintype ι] {s : ℝ}

/-- For `s ≤ 1` the singular value function is `‖·‖^s`. -/
theorem normSum_eq_svfSum (hs1 : s ≤ 1) (n : ℕ) : normSum A s n = svfSum A s n := by
  simp only [normSum, svfSum, svf, ite_eq_left hs1]

/-- For `0 ≤ s ≤ 1` the pressure of `‖·‖^s` is the singular value pressure. -/
theorem normPressure_eq_pressure [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : normPressure A s = pressure A s := by
  simp only [normPressure, normSum_eq_svfSum hs1]
  exact (tendsto_pressure hA hs0).limUnder_eq

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- For `0 ≤ s ≤ 1` the `s`-energy is `s λ_1(𝖠, μ)`. -/
theorem energyLim_eq_mul_lyapunov₁ (hA : ∀ i, (A i).det ≠ 0) {μ : Measure (ℤ → ι)}
    [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ) (hs1 : s ≤ 1) :
    energyLim A s μ = s * lyapunov₁ A μ := by
  refine Tendsto.limUnder_eq (((tendsto_lyapunov₁ hA hμ).const_mul s).congr fun n => ?_)
  have e : ∀ x : ℤ → ι, Real.log (svf s (word A (futureWord x n))) =
      s * Real.log ‖word A (futureWord x n)‖ := fun x => by
    rw [svf, ite_eq_left hs1, Real.log_rpow (norm_word_pos hA _)]
  simp only [e, integral_const_mul, mul_div_assoc]

/-- The case `0 < s ≤ 1` of the reduction: the `s`-equilibrium states of `φ^s` are the
`s`-equilibrium states of `‖·‖^s`. -/
theorem isEquilibriumState_iff_isNormEquilibrium [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0)
    {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : IsEquilibriumState A s μ ↔ IsNormEquilibrium A s μ := by
  rw [IsEquilibriumState, IsNormEquilibrium, normPressure_eq_pressure hA hs0 hs1,
    energyLim_eq_mul_lyapunov₁ hA hμ hs1, add_comm (entropy μ)]

omit [MeasurableSingletonClass ι] in
/-- The case `0 < s ≤ 1` of the reduction for the Gibbs bounds. -/
theorem hasGibbsBounds_iff_hasNormGibbs [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0)
    {μ : Measure (ℤ → ι)} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    HasGibbsBounds A s μ ↔ HasNormGibbs A s μ := by
  have e : ∀ (n : ℕ) (w : Fin n → ι),
      Real.exp (-(n * pressure A s)) * svf s (word A (List.ofFn w)) =
        Real.exp (-(n * normPressure A s)) * ‖word A (List.ofFn w)‖ ^ s := fun n w => by
    rw [normPressure_eq_pressure hA hs0 hs1, svf, ite_eq_left hs1]
  simp only [HasGibbsBounds, HasNormGibbs, e]
  constructor
  · rintro ⟨C, hC, h⟩
    exact ⟨C, by linarith, h⟩
  · rintro ⟨C, hC, h⟩
    obtain ⟨C', hC', h'⟩ := exists_one_le_bounds
      (x := fun p : (Σ n : ℕ, {_h : 0 < n // True} × (Fin n → ι)) =>
        Real.exp (-(p.1 * normPressure A s)) * ‖word A (List.ofFn p.2.2)‖ ^ s)
      (y := fun p => μ.real (cylinder p.2.2))
      (fun p => by positivity) hC fun p => h p.1 p.2.1.1 p.2.2
    exact ⟨C', hC', fun n hn w => h' ⟨n, ⟨hn, trivial⟩, w⟩⟩

end SmallExponent

/-! ### The rescaled tuple for `1 < s < 2` -/

variable (A) in
/-- The rescaled tuple `A'_i = |det A_i|^{(s-1)/(2-s)} A_i` of tex lines 2124 to 2127. -/
noncomputable def rescale (s : ℝ) (i : ι) : Matrix (Fin 2) (Fin 2) ℝ :=
  |(A i).det| ^ ((s - 1) / (2 - s)) • A i

/-- `A'_𝐢 = |det A_𝐢|^{(s-1)/(2-s)} A_𝐢`. -/
theorem word_rescale (s : ℝ) (w : List ι) :
    word (rescale A s) w = |(word A w).det| ^ ((s - 1) / (2 - s)) • word A w := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [word_cons, word_cons, ih, rescale, smul_mul_smul_comm, Matrix.det_mul, abs_mul,
      Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]

/-- The rescaled tuple is invertible. -/
theorem det_rescale_ne_zero (hA : ∀ i, (A i).det ≠ 0) (s : ℝ) (i : ι) :
    (rescale A s i).det ≠ 0 := by
  rw [rescale, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (Real.rpow_pos_of_pos (abs_pos.2 (hA i)) _).ne') (hA i)

/-- The rescaled tuple is irreducible when `𝖠` is: `A'_i` is a positive multiple of `A_i`. -/
theorem tupleIrreducible_rescale (hA : ∀ i, (A i).det ≠ 0) (s : ℝ) (h : TupleIrreducible A) :
    TupleIrreducible (rescale A s) := by
  rintro ⟨v, hv, hline⟩
  refine h ⟨v, hv, fun i => ?_⟩
  obtain ⟨c, hc⟩ := hline i
  have hpos : 0 < |(A i).det| ^ ((s - 1) / (2 - s)) := Real.rpow_pos_of_pos (abs_pos.2 (hA i)) _
  refine ⟨c / |(A i).det| ^ ((s - 1) / (2 - s)), ?_⟩
  rw [rescale, Matrix.smul_mulVec] at hc
  rw [div_eq_inv_mul, mul_smul, ← hc, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]

/-- `‖A'_𝐢‖^{2-s} = φ^s(A_𝐢)` for `1 < s < 2`, tex lines 2125 to 2126: the norm of the rescaled
product is `|det A_𝐢|^{(s-1)/(2-s)} ‖A_𝐢‖`, and `φ^s(A) = ‖A‖^{2-s} |det A|^{s-1}`. -/
theorem norm_word_rescale_rpow {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2) (w : List ι) :
    ‖word (rescale A s) w‖ ^ (2 - s) = svf s (word A w) := by
  have h2 : 0 < 2 - s := by linarith
  rw [word_rescale, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
    Real.mul_rpow (Real.rpow_nonneg (abs_nonneg _) _) (norm_nonneg _),
    ← Real.rpow_mul (abs_nonneg _), div_mul_cancel₀ _ h2.ne', svf, ite_eq_right (by linarith),
    ite_eq_left hs2.le, mul_comm]

section Rescaled

variable [Fintype ι] {s : ℝ}

/-- `∑_{|𝐢| = n} ‖A'_𝐢‖^{2-s} = ∑_{|𝐢| = n} φ^s(A_𝐢)` for `1 < s < 2`. -/
theorem normSum_rescale (hs1 : 1 < s) (hs2 : s < 2) (n : ℕ) :
    normSum (rescale A s) (2 - s) n = svfSum A s n := by
  simp only [normSum, svfSum, norm_word_rescale_rpow hs1 hs2]

/-- The pressure of `‖·‖^{2-s}` for the rescaled tuple is `P(𝖠, s)`, for `1 < s < 2`. -/
theorem normPressure_rescale [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) (hs1 : 1 < s)
    (hs2 : s < 2) : normPressure (rescale A s) (2 - s) = pressure A s := by
  simp only [normPressure, normSum_rescale hs1 hs2]
  exact (tendsto_pressure hA (by linarith)).limUnder_eq

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- `Λ(𝖠, μ, s) = (2 - s) λ_1(𝖠', μ)` for `1 < s < 2` and an invariant measure `μ`. -/
theorem energyLim_eq_rescale (hA : ∀ i, (A i).det ≠ 0) {μ : Measure (ℤ → ι)}
    [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ) (hs1 : 1 < s)
    (hs2 : s < 2) : energyLim A s μ = (2 - s) * lyapunov₁ (rescale A s) μ := by
  refine Tendsto.limUnder_eq
    (((tendsto_lyapunov₁ (det_rescale_ne_zero hA s) hμ).const_mul (2 - s)).congr fun n => ?_)
  have e : ∀ x : ℤ → ι, Real.log (svf s (word A (futureWord x n))) =
      (2 - s) * Real.log ‖word (rescale A s) (futureWord x n)‖ := fun x => by
    rw [← norm_word_rescale_rpow hs1 hs2,
      Real.log_rpow (norm_word_pos (det_rescale_ne_zero hA s) _)]
  simp only [e, integral_const_mul, mul_div_assoc]

/-- The case `1 < s < 2` of the reduction: the `s`-equilibrium states of `φ^s` for `𝖠` are the
`(2 - s)`-equilibrium states of `‖·‖^{2-s}` for the rescaled tuple. -/
theorem isEquilibriumState_iff_rescale [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0)
    {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ)
    (hs1 : 1 < s) (hs2 : s < 2) :
    IsEquilibriumState A s μ ↔ IsNormEquilibrium (rescale A s) (2 - s) μ := by
  rw [IsEquilibriumState, IsNormEquilibrium, normPressure_rescale hA hs1 hs2,
    energyLim_eq_rescale hA hμ hs1 hs2, add_comm (entropy μ)]

omit [MeasurableSingletonClass ι] in
/-- The case `1 < s < 2` of the reduction for the Gibbs bounds. -/
theorem hasGibbsBounds_iff_rescale [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0)
    {μ : Measure (ℤ → ι)} (hs1 : 1 < s) (hs2 : s < 2) :
    HasGibbsBounds A s μ ↔ HasNormGibbs (rescale A s) (2 - s) μ := by
  have e : ∀ (n : ℕ) (w : Fin n → ι),
      Real.exp (-(n * pressure A s)) * svf s (word A (List.ofFn w)) =
        Real.exp (-(n * normPressure (rescale A s) (2 - s))) *
          ‖word (rescale A s) (List.ofFn w)‖ ^ (2 - s) := fun n w => by
    rw [normPressure_rescale hA hs1 hs2, norm_word_rescale_rpow hs1 hs2]
  simp only [HasGibbsBounds, HasNormGibbs, e]
  constructor
  · rintro ⟨C, hC, h⟩
    exact ⟨C, by linarith, h⟩
  · rintro ⟨C, hC, h⟩
    obtain ⟨C', hC', h'⟩ := exists_one_le_bounds
      (x := fun p : (Σ n : ℕ, {_h : 0 < n // True} × (Fin n → ι)) =>
        Real.exp (-(p.1 * normPressure (rescale A s) (2 - s))) *
          ‖word (rescale A s) (List.ofFn p.2.2)‖ ^ (2 - s))
      (y := fun p => μ.real (cylinder p.2.2))
      (fun p => by positivity) hC fun p => h p.1 p.2.1.1 p.2.2
    exact ⟨C', hC', fun n hn w => h' ⟨n, ⟨hn, trivial⟩, w⟩⟩

end Rescaled

end MatrixTuple

end BoxLike
