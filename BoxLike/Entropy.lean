module

/-
The block entropies `H_μ(𝒫_0^{n-1})` of the canonical partition `𝒫` of `sec:entropies` and the
Kolmogorov–Sinai entropy `lim_n H_μ(𝒫_0^{n-1}) / n` used in `sec:entropy_eq_state`, for a
probability measure `μ` on the two-sided full shift `ℤ → α` over a finite alphabet `α` with
measurable singletons, where `ℤ → α` carries the product `σ`-algebra.

The atoms of `𝒫_0^{n-1}` are the cylinders `[w]`, `w : Fin n → α`, so the entropy of the
partition is the finite sum `∑_w -μ[w] log μ[w]`.

* `cylinder`, `block`, `cylinder_eq_preimage`, `measurableSet_cylinder`: the cylinder `[w]` is
  the fibre over `w` of the measurable map `x ↦ x_0 ⋯ x_{n-1}`.
* `cylinder_append`: `[w w'] = [w] ∩ σ^{-m}[w']`.
* `measurable_shift`, `iterate_shift_one`, `measurePreserving_shift_natCast`: every `σ^m` is
  measurable, and `σ^m`, `m ∈ ℕ`, preserves a `σ`-invariant measure.
* `sum_measureReal_inter_preimage_singleton`, `sum_measureReal_cylinder`: a finite measurable
  partition splits the measure of every set, and the cylinders of length `n` partition the
  space.
* `blockEntropy`, `entropy`: the entropy `H_μ(𝒫_0^{n-1})` and the Kolmogorov–Sinai entropy.
* `blockEntropy_nonneg`, `blockEntropy_zero`, `blockEntropy_le`: `0 ≤ H_μ(𝒫_0^{n-1}) ≤ n log #α`.
* `sum_negMulLog_le_add`, `blockEntropy_add_le`: the entropy of a joint distribution is at most
  the sum of the entropies of its marginals, so `n ↦ H_μ(𝒫_0^{n-1})` is sub-additive for an
  invariant measure.
* `tendsto_entropy`, `entropy_nonneg`, `entropy_le`: the limit defining the entropy exists by
  Fekete's lemma and lies in `[0, log #α]`.
* `entropy_eq_of_blockEntropy_close`: measures whose block entropies differ by a bounded amount
  have the same entropy.
-/
public import BoxLike.Orientation
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Subadditive
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

namespace BoxLike

open Filter Topology MeasureTheory

/-- Sub-additivity of the Shannon entropy: the entropy of a probability vector `p` on a product
is at most the sum of the entropies of its two marginals `p₁` and `p₂`. -/
theorem sum_negMulLog_le_add {A B : Type*} [Fintype A] [Fintype B] {p : A → B → ℝ}
    {p₁ : A → ℝ} {p₂ : B → ℝ} (hp : ∀ a b, 0 ≤ p a b) (h₁ : ∀ a, ∑ b, p a b = p₁ a)
    (h₂ : ∀ b, ∑ a, p a b = p₂ b) (hsum : ∑ a, p₁ a = 1) :
    ∑ a, ∑ b, Real.negMulLog (p a b)
      ≤ ∑ a, Real.negMulLog (p₁ a) + ∑ b, Real.negMulLog (p₂ b) := by
  have key : ∀ a b, Real.negMulLog (p a b)
      ≤ -(p a b * Real.log (p₁ a)) - p a b * Real.log (p₂ b) + (p₁ a * p₂ b - p a b) := by
    intro a b
    have h1 : p a b ≤ p₁ a := h₁ a ▸
      Finset.single_le_sum (f := fun b => p a b) (fun b _ => hp a b) (Finset.mem_univ b)
    have h2 : p a b ≤ p₂ b := h₂ b ▸
      Finset.single_le_sum (f := fun a => p a b) (fun a _ => hp a b) (Finset.mem_univ a)
    rcases (hp a b).eq_or_lt with h | h
    · rw [← h] at h1 h2
      rw [← h]
      simpa using mul_nonneg h1 h2
    · have h1' : 0 < p₁ a := h.trans_le h1
      have h2' : 0 < p₂ b := h.trans_le h2
      have hlog := Real.log_le_sub_one_of_pos (div_pos (mul_pos h1' h2') h)
      rw [Real.log_div (mul_pos h1' h2').ne' h.ne', Real.log_mul h1'.ne' h2'.ne'] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog h.le
      have e : p a b * (p₁ a * p₂ b / p a b - 1) = p₁ a * p₂ b - p a b := by
        field_simp
      rw [e] at hmul
      rw [Real.negMulLog]
      linarith
  have e0 : ∑ a, ∑ b, p a b = 1 := by simp_rw [h₁]; exact hsum
  have e1 : ∑ a, ∑ b, p a b * Real.log (p₁ a) = ∑ a, p₁ a * Real.log (p₁ a) :=
    Finset.sum_congr rfl fun a _ => by rw [← Finset.sum_mul, h₁]
  have e2 : ∑ a, ∑ b, p a b * Real.log (p₂ b) = ∑ b, p₂ b * Real.log (p₂ b) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => by rw [← Finset.sum_mul, h₂]
  have hsum' : ∑ b, p₂ b = 1 := by
    rw [← e0, Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => (h₂ b).symm
  have e3 : ∑ a, ∑ b, p₁ a * p₂ b = 1 := by
    rw [← Finset.sum_mul_sum, hsum, hsum', mul_one]
  calc ∑ a, ∑ b, Real.negMulLog (p a b)
      ≤ ∑ a, ∑ b, (-(p a b * Real.log (p₁ a)) - p a b * Real.log (p₂ b)
          + (p₁ a * p₂ b - p a b)) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => key a b
    _ = ∑ a, Real.negMulLog (p₁ a) + ∑ b, Real.negMulLog (p₂ b) := by
        simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, e0, e1, e2, e3]
        ring

section Cylinder

variable {α : Type*} {m n : ℕ}

/-- The cylinder `[w] = {x : x_0 ⋯ x_{n-1} = w}` of `sec:two_sided_shift_space`. -/
def cylinder {α : Type*} {n : ℕ} (w : Fin n → α) : Set (ℤ → α) :=
  {x | ∀ k : Fin n, x (k : ℤ) = w k}

/-- Membership in the cylinder `[w]`, unfolded. -/
theorem mem_cylinder {w : Fin n → α} {x : ℤ → α} :
    x ∈ cylinder w ↔ ∀ k : Fin n, x (k : ℤ) = w k := Iff.rfl

/-- The block `x_0 ⋯ x_{n-1}` of a point `x`. -/
def block (n : ℕ) (x : ℤ → α) : Fin n → α := fun k => x k

/-- The `k`-th symbol of the block `x_0 ⋯ x_{n-1}` is `x_k`. -/
@[simp] theorem block_apply (x : ℤ → α) (k : Fin n) : block n x k = x k := rfl

/-- The cylinder `[w]` is the set of points whose block of length `n` is `w`. -/
theorem cylinder_eq_preimage (w : Fin n → α) : cylinder w = block n ⁻¹' {w} := by
  ext x
  simp [cylinder, funext_iff]

/-- The cylinder of a concatenation: `[w w'] = [w] ∩ σ^{-m}[w']` for `|w| = m`. -/
theorem cylinder_append (w : Fin m → α) (w' : Fin n → α) :
    cylinder (Fin.append w w') = cylinder w ∩ shift m ⁻¹' cylinder w' := by
  ext x
  simp only [cylinder, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, shift_apply]
  constructor
  · intro h
    refine ⟨fun k => ?_, fun k => ?_⟩
    · simpa using h (Fin.castAdd n k)
    · simpa using h (Fin.natAdd m k)
  · rintro ⟨h1, h2⟩ k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simpa using h1 i
    · simpa using h2 i

/-- The iterates of the left shift `σ = shift 1` are the maps `shift m`. -/
theorem iterate_shift_one (m : ℕ) : (shift 1 : (ℤ → α) → ℤ → α)^[m] = shift m := by
  induction m with
  | zero => funext x; simp
  | succ m ih =>
    funext x
    rw [Function.iterate_succ_apply, ih, shift_shift, Nat.cast_succ, add_comm]

end Cylinder

section Measurable

variable {α : Type*} [MeasurableSpace α] {n : ℕ}

/-- Every iterate `σ^n`, `n ∈ ℤ`, of the shift is measurable. -/
theorem measurable_shift (n : ℤ) : Measurable (shift n : (ℤ → α) → ℤ → α) :=
  Measurable.of_eval fun k => measurable_pi_apply (n + k)

/-- The map `x ↦ x_0 ⋯ x_{n-1}` is measurable. -/
theorem measurable_block (n : ℕ) : Measurable (block n : (ℤ → α) → Fin n → α) :=
  Measurable.of_eval fun k => measurable_pi_apply (k : ℤ)

/-- Cylinders are measurable. -/
theorem measurableSet_cylinder [MeasurableSingletonClass α] (w : Fin n → α) :
    MeasurableSet (cylinder w) := by
  rw [cylinder_eq_preimage]
  exact measurable_block n (measurableSet_singleton w)

/-- An invariant measure is invariant under every `σ^m`, `m ∈ ℕ`. -/
theorem measurePreserving_shift_natCast {μ : Measure (ℤ → α)}
    (hμ : MeasurePreserving (shift 1) μ μ) (m : ℕ) : MeasurePreserving (shift (m : ℤ)) μ μ := by
  rw [← iterate_shift_one]
  exact hμ.iterate m

/-- A finite measurable partition, given as the fibres of a map into a finite type, splits the
measure of every set. -/
theorem sum_measureReal_inter_preimage_singleton {X γ : Type*} [MeasurableSpace X] [Fintype γ]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → γ} (hf : ∀ c, MeasurableSet (f ⁻¹' {c}))
    (S : Set X) : ∑ c, μ.real (S ∩ f ⁻¹' {c}) = μ.real S := by
  have h := sum_measureReal_preimage_singleton (μ := μ.restrict S) Finset.univ (f := f)
    fun c _ => hf c
  simpa [measureReal_restrict_apply (hf _), Set.inter_comm] using h

end Measurable

section Entropy

variable {α : Type*} [Fintype α] [MeasurableSpace α]

/-- The entropy `H_μ(𝒫_0^{n-1})` of the partition into cylinders of length `n`. -/
noncomputable def blockEntropy (μ : Measure (ℤ → α)) (n : ℕ) : ℝ :=
  ∑ w : Fin n → α, Real.negMulLog (μ.real (cylinder w))

/-- The Kolmogorov–Sinai entropy `h(μ) = lim_n H_μ(𝒫_0^{n-1}) / n`. -/
noncomputable def entropy (μ : Measure (ℤ → α)) : ℝ :=
  limUnder atTop fun n : ℕ => blockEntropy μ n / n

/-- The entropy of the partition into cylinders of length `n` is non-negative. -/
theorem blockEntropy_nonneg (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ] (n : ℕ) :
    0 ≤ blockEntropy μ n :=
  Finset.sum_nonneg fun _ _ => Real.negMulLog_nonneg measureReal_nonneg measureReal_le_one

/-- Two measures whose block entropies stay within bounded distance have the same entropy. -/
theorem entropy_eq_of_blockEntropy_close {β : Type*} [Fintype β] [MeasurableSpace β]
    {μ : Measure (ℤ → α)} {ν : Measure (ℤ → β)} {C : ℝ}
    (hμ : Tendsto (fun n : ℕ => blockEntropy μ n / n) atTop (𝓝 (entropy μ)))
    (h : ∀ n, |blockEntropy ν n - blockEntropy μ n| ≤ C) : entropy ν = entropy μ := by
  have hdiff : Tendsto (fun n : ℕ => blockEntropy ν n / n - blockEntropy μ n / n) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (tendsto_const_div_atTop_nhds_zero_nat C)
    rw [← sub_div, Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (h n) (Nat.cast_nonneg n)
  have hν := hdiff.add hμ
  simp only [sub_add_cancel, zero_add] at hν
  exact hν.limUnder_eq

variable [MeasurableSingletonClass α]

/-- The cylinders of length `n` partition the space. -/
theorem sum_measureReal_cylinder (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ] (n : ℕ) :
    ∑ w : Fin n → α, μ.real (cylinder w) = 1 := by
  have h := sum_measureReal_inter_preimage_singleton μ (f := block n)
    (fun c => measurable_block n (measurableSet_singleton c)) Set.univ
  simpa [cylinder_eq_preimage] using h

/-- The partition into cylinders of length `0` is trivial. -/
@[simp] theorem blockEntropy_zero (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ] :
    blockEntropy μ 0 = 0 := by
  have h := sum_measureReal_cylinder μ 0
  rw [Fintype.sum_unique] at h
  rw [blockEntropy, Fintype.sum_unique, h, Real.negMulLog_one]

/-- The block entropy is at most the logarithm of the number of blocks, by Jensen's
inequality for the concave function `negMulLog`. -/
theorem blockEntropy_le (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ] (n : ℕ) :
    blockEntropy μ n ≤ n * Real.log (Fintype.card α) := by
  have hsum := sum_measureReal_cylinder μ n
  have hN : 0 < (Fintype.card (Fin n → α) : ℝ) := by
    rw [Nat.cast_pos, Fintype.card_pos_iff]
    by_contra hne
    rw [not_nonempty_iff] at hne
    simp at hsum
  have hJ := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
    (w := fun _ : Fin n → α => (Fintype.card (Fin n → α) : ℝ)⁻¹)
    (p := fun w => μ.real (cylinder w)) (fun _ _ => (inv_pos.2 hN).le)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hN.ne'])
    (fun _ _ => measureReal_nonneg)
  simp only [smul_eq_mul, ← Finset.mul_sum, hsum, mul_one, Real.negMulLog, Real.log_inv,
    neg_mul_neg] at hJ
  have h := le_of_mul_le_mul_left hJ (inv_pos.2 hN)
  rwa [Fintype.card_pi_const, Nat.cast_pow, Real.log_pow] at h

/-- The block entropies of an invariant measure are sub-additive. -/
theorem blockEntropy_add_le {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) (m n : ℕ) :
    blockEntropy μ (m + n) ≤ blockEntropy μ m + blockEntropy μ n := by
  have h1 : ∀ w : Fin m → α,
      ∑ w' : Fin n → α, μ.real (cylinder (Fin.append w w')) = μ.real (cylinder w) := by
    intro w
    have h := sum_measureReal_inter_preimage_singleton μ (f := fun x => block n (shift m x))
      (fun c => (measurable_block n).comp (measurable_shift m) (measurableSet_singleton c))
      (cylinder w)
    rw [← h]
    refine Finset.sum_congr rfl fun w' _ => ?_
    rw [cylinder_append, cylinder_eq_preimage w']
    rfl
  have h2 : ∀ w' : Fin n → α,
      ∑ w : Fin m → α, μ.real (cylinder (Fin.append w w')) = μ.real (cylinder w') := by
    intro w'
    have h := sum_measureReal_inter_preimage_singleton μ (f := block m)
      (fun c => measurable_block m (measurableSet_singleton c)) (shift m ⁻¹' cylinder w')
    rw [(measurePreserving_shift_natCast hμ m).measureReal_preimage
      (measurableSet_cylinder w').nullMeasurableSet] at h
    rw [← h]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [cylinder_append, cylinder_eq_preimage w, Set.inter_comm]
  have key := sum_negMulLog_le_add
    (p := fun (w : Fin m → α) (w' : Fin n → α) => μ.real (cylinder (Fin.append w w')))
    (fun _ _ => measureReal_nonneg) h1 h2 (sum_measureReal_cylinder μ m)
  calc blockEntropy μ (m + n)
      = ∑ p : (Fin m → α) × (Fin n → α),
          Real.negMulLog (μ.real (cylinder (Fin.append p.1 p.2))) :=
        (Fintype.sum_equiv (Fin.appendEquiv m n) _ _ fun p => rfl).symm
    _ = ∑ w : Fin m → α, ∑ w' : Fin n → α,
          Real.negMulLog (μ.real (cylinder (Fin.append w w'))) := Fintype.sum_prod_type _
    _ ≤ blockEntropy μ m + blockEntropy μ n := key

/-- The limit defining the Kolmogorov–Sinai entropy of an invariant measure exists, by Fekete's
lemma. -/
theorem tendsto_entropy {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) :
    Tendsto (fun n : ℕ => blockEntropy μ n / n) atTop (𝓝 (entropy μ)) := by
  have hsub : Subadditive (blockEntropy μ) := fun m n => blockEntropy_add_le hμ m n
  have hbdd : BddBelow (Set.range fun n : ℕ => blockEntropy μ n / n) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact div_nonneg (blockEntropy_nonneg μ n) (Nat.cast_nonneg n)⟩
  have h := hsub.tendsto_lim hbdd
  rw [entropy, h.limUnder_eq]
  exact h

/-- The Kolmogorov–Sinai entropy of an invariant measure is non-negative. -/
theorem entropy_nonneg {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) : 0 ≤ entropy μ :=
  ge_of_tendsto' (tendsto_entropy hμ) fun n =>
    div_nonneg (blockEntropy_nonneg μ n) (Nat.cast_nonneg n)

/-- The entropy of an invariant measure is at most the logarithm of the size of the alphabet. -/
theorem entropy_le {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) : entropy μ ≤ Real.log (Fintype.card α) :=
  le_of_tendsto' (tendsto_entropy hμ) fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using Real.log_natCast_nonneg _
    · rw [div_le_iff₀ (Nat.cast_pos.2 hn), mul_comm]
      exact blockEntropy_le μ n

end Entropy

end BoxLike
