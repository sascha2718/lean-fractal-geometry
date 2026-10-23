module

public import Mathlib
public import FractalGeometry.Symbolic.Shift

@[expose] public section

namespace FractalGeometry


open Filter Topology MeasureTheory

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

def cylinder {α : Type*} {n : ℕ} (w : Fin n → α) : Set (ℤ → α) :=
  {x | ∀ k : Fin n, x (k : ℤ) = w k}

def block (n : ℕ) (x : ℤ → α) : Fin n → α := fun k => x k

@[simp] theorem block_apply (n : ℕ) (x : ℤ → α) (k : Fin n) :
    block n x k = x k := rfl

theorem cylinder_eq_preimage (w : Fin n → α) : cylinder w = block n ⁻¹' {w} := by
  ext x
  simp [cylinder, funext_iff]

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

theorem iterate_shift_one (m : ℕ) : (shift 1 : (ℤ → α) → ℤ → α)^[m] = shift m := by
  induction m with
  | zero => funext x; simp
  | succ m ih =>
    funext x
    rw [Function.iterate_succ_apply, ih, shift_shift, Nat.cast_succ, add_comm]

end Cylinder

section Measurable

variable {α : Type*} [MeasurableSpace α] {n : ℕ}

theorem measurable_shift (n : ℤ) : Measurable (shift n : (ℤ → α) → ℤ → α) :=
  Measurable.of_eval fun k => measurable_pi_apply (n + k)

theorem measurable_block (n : ℕ) : Measurable (block n : (ℤ → α) → Fin n → α) :=
  Measurable.of_eval fun k => measurable_pi_apply (k : ℤ)

theorem measurableSet_cylinder [MeasurableSingletonClass α] (w : Fin n → α) :
    MeasurableSet (cylinder w) := by
  rw [cylinder_eq_preimage]
  exact measurable_block n (measurableSet_singleton w)

theorem measurePreserving_shift_natCast {μ : Measure (ℤ → α)}
    (hμ : MeasurePreserving (shift 1) μ μ) (m : ℕ) : MeasurePreserving (shift (m : ℤ)) μ μ := by
  rw [← iterate_shift_one]
  exact hμ.iterate m

theorem sum_measureReal_inter_preimage_singleton {X γ : Type*} [MeasurableSpace X] [Fintype γ]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → γ} (hf : ∀ c, MeasurableSet (f ⁻¹' {c}))
    (S : Set X) : ∑ c, μ.real (S ∩ f ⁻¹' {c}) = μ.real S := by
  have h := sum_measureReal_preimage_singleton (μ := μ.restrict S) Finset.univ (f := f)
    fun c _ => hf c
  simpa [measureReal_restrict_apply (hf _), Set.inter_comm] using h

end Measurable

section Entropy

variable {α : Type*} [Fintype α] [MeasurableSpace α]

noncomputable def blockEntropy (μ : Measure (ℤ → α)) (n : ℕ) : ℝ :=
  ∑ w : Fin n → α, Real.negMulLog (μ.real (cylinder w))

noncomputable def entropy (μ : Measure (ℤ → α)) : ℝ :=
  limUnder atTop fun n : ℕ => blockEntropy μ n / n

theorem blockEntropy_nonneg (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ] (n : ℕ) :
    0 ≤ blockEntropy μ n :=
  Finset.sum_nonneg fun _ _ => Real.negMulLog_nonneg measureReal_nonneg measureReal_le_one

variable [MeasurableSingletonClass α]

theorem sum_measureReal_cylinder (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ] (n : ℕ) :
    ∑ w : Fin n → α, μ.real (cylinder w) = 1 := by
  have h := sum_measureReal_inter_preimage_singleton μ (f := block n)
    (fun c => measurable_block n (measurableSet_singleton c)) Set.univ
  simpa [cylinder_eq_preimage] using h

@[simp] theorem blockEntropy_zero (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ] :
    blockEntropy μ 0 = 0 := by
  have h := sum_measureReal_cylinder μ 0
  rw [Fintype.sum_unique] at h
  rw [blockEntropy, Fintype.sum_unique, h, Real.negMulLog_one]

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

theorem tendsto_entropy {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) :
    Tendsto (fun n : ℕ => blockEntropy μ n / n) atTop (𝓝 (entropy μ)) := by
  have hsub : Subadditive (blockEntropy μ) := fun m n => blockEntropy_add_le hμ m n
  have hbdd : BddBelow (Set.range fun n : ℕ => blockEntropy μ n / n) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact div_nonneg (blockEntropy_nonneg μ n) (Nat.cast_nonneg n)⟩
  have h := hsub.tendsto_lim hbdd
  rw [entropy, h.limUnder_eq]
  exact h

end Entropy

end FractalGeometry
