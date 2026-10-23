import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.GibbsEntropy
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open Filter Topology MeasureTheory

theorem eq_of_negMulLog_add_mul_log_eq {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (h : q = 0 → p = 0)
    (he : Real.negMulLog p + p * Real.log q = q - p) : p = q := by
  rcases hp.eq_or_lt with rfl | hp'
  · simpa using he
  · have hq' : 0 < q := hq.lt_of_ne' fun h0 => hp'.ne' (h h0)
    by_contra hne
    have hne' : q / p ≠ 1 := fun h1 => hne ((div_eq_one_iff_eq hp'.ne').1 h1).symm
    have hlog := Real.log_lt_sub_one_of_pos (div_pos hq' hp') hne'
    rw [Real.log_div hq'.ne' hp'.ne'] at hlog
    have hmul := mul_lt_mul_of_pos_left hlog hp'
    have e : p * (q / p - 1) = q - p := by field_simp
    rw [e] at hmul
    rw [Real.negMulLog] at he
    linarith

section Finite

variable {A B : Type*} [Fintype A] [Fintype B]

theorem eq_div_sum_of_sum_negMulLog_add_sum_mul_log_eq {p q : A → ℝ} (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) (hq : ∀ a, 0 < q a)
    (h : ∑ a, Real.negMulLog (p a) + ∑ a, p a * Real.log (q a) = Real.log (∑ a, q a)) (a : A) :
    p a = q a / ∑ b, q b := by
  have hA : Nonempty A := ⟨a⟩
  have hQ : 0 < ∑ a, q a := Finset.sum_pos (fun a _ => hq a) Finset.univ_nonempty
  have hle : ∀ a, Real.negMulLog (p a) + p a * Real.log (q a / ∑ b, q b)
      ≤ q a / ∑ b, q b - p a := fun a =>
    negMulLog_add_mul_log_le (hp a) (div_pos (hq a) hQ).le
      fun h0 => absurd h0 (div_pos (hq a) hQ).ne'
  have h0 := sum_gibbs_defect hsum hq
  rw [h, sub_self, Finset.sum_eq_zero_iff_of_nonneg fun a _ => sub_nonneg.2 (hle a)] at h0
  exact eq_of_negMulLog_add_mul_log_eq (hp a) (div_pos (hq a) hQ).le
    (fun h0 => absurd h0 (div_pos (hq a) hQ).ne') (sub_eq_zero.1 (h0 a (Finset.mem_univ a))).symm

theorem eq_mul_of_sum_negMulLog_eq_add {p : A → B → ℝ} {p₁ : A → ℝ} {p₂ : B → ℝ}
    (hp : ∀ a b, 0 ≤ p a b) (h₁ : ∀ a, ∑ b, p a b = p₁ a) (h₂ : ∀ b, ∑ a, p a b = p₂ b)
    (hsum : ∑ a, p₁ a = 1)
    (h : ∑ a, ∑ b, Real.negMulLog (p a b)
      = ∑ a, Real.negMulLog (p₁ a) + ∑ b, Real.negMulLog (p₂ b)) (a : A) (b : B) :
    p a b = p₁ a * p₂ b := by
  have hle₁ : ∀ a b, p a b ≤ p₁ a := fun a b => h₁ a ▸
    Finset.single_le_sum (f := fun b => p a b) (fun b _ => hp a b) (Finset.mem_univ b)
  have hle₂ : ∀ a b, p a b ≤ p₂ b := fun a b => h₂ b ▸
    Finset.single_le_sum (f := fun a => p a b) (fun a _ => hp a b) (Finset.mem_univ a)
  have hp₁ : ∀ a, 0 ≤ p₁ a := fun a => h₁ a ▸ Finset.sum_nonneg fun b _ => hp a b
  have hp₂ : ∀ b, 0 ≤ p₂ b := fun b => h₂ b ▸ Finset.sum_nonneg fun a _ => hp a b
  have hzero : ∀ a b, p₁ a * p₂ b = 0 → p a b = 0 := by
    intro a b h0
    rcases mul_eq_zero.1 h0 with h0 | h0
    · exact le_antisymm (h0 ▸ hle₁ a b) (hp a b)
    · exact le_antisymm (h0 ▸ hle₂ a b) (hp a b)
  have hlog : ∀ a b, p a b * Real.log (p₁ a * p₂ b)
      = p a b * Real.log (p₁ a) + p a b * Real.log (p₂ b) := by
    intro a b
    by_cases h0 : p₁ a * p₂ b = 0
    · simp [hzero a b h0]
    · rw [Real.log_mul (left_ne_zero_of_mul h0) (right_ne_zero_of_mul h0), mul_add]
  have hle : ∀ a b, Real.negMulLog (p a b) + p a b * Real.log (p₁ a * p₂ b)
      ≤ p₁ a * p₂ b - p a b := fun a b =>
    negMulLog_add_mul_log_le (hp a b) (mul_nonneg (hp₁ a) (hp₂ b)) (hzero a b)
  have e0 : ∑ a, ∑ b, p a b = 1 := by simp_rw [h₁]; exact hsum
  have e1 : ∑ a, ∑ b, p a b * Real.log (p₁ a) = -∑ a, Real.negMulLog (p₁ a) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => by
      rw [← Finset.sum_mul, h₁, Real.negMulLog, neg_mul, neg_neg]
  have e2 : ∑ a, ∑ b, p a b * Real.log (p₂ b) = -∑ b, Real.negMulLog (p₂ b) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => by
      rw [← Finset.sum_mul, h₂, Real.negMulLog, neg_mul, neg_neg]
  have hsum' : ∑ b, p₂ b = 1 := by
    rw [← e0, Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => (h₂ b).symm
  have e3 : ∑ a, ∑ b, p₁ a * p₂ b = 1 := by
    rw [← Finset.sum_mul_sum, hsum, hsum', mul_one]
  have hdefect : ∑ a, ∑ b, (p₁ a * p₂ b - p a b
      - (Real.negMulLog (p a b) + p a b * Real.log (p₁ a * p₂ b))) = 0 := by
    simp only [hlog, Finset.sum_sub_distrib, Finset.sum_add_distrib, e0, e1, e2, e3, h]
    ring
  rw [Finset.sum_eq_zero_iff_of_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => sub_nonneg.2 (hle a b)] at hdefect
  have hab := hdefect a (Finset.mem_univ a)
  rw [Finset.sum_eq_zero_iff_of_nonneg fun b _ => sub_nonneg.2 (hle a b)] at hab
  exact eq_of_negMulLog_add_mul_log_eq (hp a b) (mul_nonneg (hp₁ a) (hp₂ b)) (hzero a b)
    (sub_eq_zero.1 (hab b (Finset.mem_univ b))).symm

end Finite

section Marginals

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] {m n : ℕ}

theorem sum_measureReal_cylinder_append_right (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (w : Fin m → α) :
    ∑ w' : Fin n → α, μ.real (cylinder (Fin.append w w')) = μ.real (cylinder w) := by
  have h := sum_measureReal_inter_preimage_singleton μ (f := fun x => block n (shift m x))
    (fun c => (measurable_block n).comp (measurable_shift m) (measurableSet_singleton c))
    (cylinder w)
  rw [← h]
  refine Finset.sum_congr rfl fun w' _ => ?_
  rw [cylinder_append, cylinder_eq_preimage w']
  rfl

theorem sum_measureReal_cylinder_append_left {μ : Measure (ℤ → α)} [IsFiniteMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) (w' : Fin n → α) :
    ∑ w : Fin m → α, μ.real (cylinder (Fin.append w w')) = μ.real (cylinder w') := by
  have h := sum_measureReal_inter_preimage_singleton μ (f := block m)
    (fun c => measurable_block m (measurableSet_singleton c)) (shift m ⁻¹' cylinder w')
  rw [(measurePreserving_shift_natCast hμ m).measureReal_preimage
    (measurableSet_cylinder w').nullMeasurableSet] at h
  rw [← h]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [cylinder_append, cylinder_eq_preimage w, Set.inter_comm]

omit [MeasurableSingletonClass α] in

theorem blockEntropy_add_eq_sum (μ : Measure (ℤ → α)) (m n : ℕ) :
    blockEntropy μ (m + n) = ∑ w : Fin m → α, ∑ w' : Fin n → α,
      Real.negMulLog (μ.real (cylinder (Fin.append w w'))) :=
  calc blockEntropy μ (m + n)
      = ∑ p : (Fin m → α) × (Fin n → α),
          Real.negMulLog (μ.real (cylinder (Fin.append p.1 p.2))) :=
        (Fintype.sum_equiv (Fin.appendEquiv m n) _ _ fun _ => rfl).symm
    _ = ∑ w : Fin m → α, ∑ w' : Fin n → α,
          Real.negMulLog (μ.real (cylinder (Fin.append w w'))) := Fintype.sum_prod_type _

omit [MeasurableSpace α] [MeasurableSingletonClass α] in

theorem sum_fin_one_fun {M : Type*} [AddCommMonoid M] (F : (Fin 1 → α) → M) :
    ∑ w, F w = ∑ i, F ![i] :=
  Fintype.sum_equiv (Equiv.funUnique (Fin 1) α) _ _ fun w => by
    congr 1
    funext k
    rw [Subsingleton.elim k 0]
    rfl

omit [MeasurableSingletonClass α] in

theorem blockEntropy_one (μ : Measure (ℤ → α)) :
    blockEntropy μ 1 = ∑ i, Real.negMulLog (μ.real (cylinder ![i])) := by
  rw [blockEntropy, sum_fin_one_fun]

theorem sum_measureReal_cylinder_one (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ] :
    ∑ i, μ.real (cylinder ![i]) = 1 := by
  rw [← sum_fin_one_fun fun w => μ.real (cylinder w)]
  exact sum_measureReal_cylinder μ 1

omit [Fintype α] [MeasurableSingletonClass α] in

theorem measureReal_preimage_shift {μ : Measure (ℤ → α)} (hμ : MeasurePreserving (shift 1) μ μ)
    (k : ℤ) {S : Set (ℤ → α)} (hS : MeasurableSet S) : μ.real (shift k ⁻¹' S) = μ.real S := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · exact (measurePreserving_shift_natCast hμ m).measureReal_preimage hS.nullMeasurableSet
  · have h := (measurePreserving_shift_natCast hμ m).measureReal_preimage
      (measurable_shift (-(m : ℤ)) hS).nullMeasurableSet
    rw [← h]
    congr 1
    ext x
    simp [shift_shift]

end Marginals

section Bernoulli

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem entropy_le_blockEntropy_one {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) : entropy μ ≤ blockEntropy μ 1 := by
  simpa using entropy_le_blockEntropy_div hμ one_ne_zero

theorem blockEntropy_le_mul {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) (n : ℕ) :
    blockEntropy μ n ≤ n * blockEntropy μ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := blockEntropy_add_le hμ n 1
    push_cast
    linarith

theorem blockEntropy_eq_mul_of_entropy_eq {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) (h : entropy μ = blockEntropy μ 1) (n : ℕ) :
    blockEntropy μ n = n * blockEntropy μ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · refine le_antisymm (blockEntropy_le_mul hμ n) ?_
    have h' := entropy_le_blockEntropy_div hμ hn.ne'
    rwa [h, le_div_iff₀ (Nat.cast_pos.2 hn), mul_comm] at h'

theorem measureReal_cylinder_append_of_entropy_eq {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) (h : entropy μ = blockEntropy μ 1) {m n : ℕ}
    (w : Fin m → α) (w' : Fin n → α) :
    μ.real (cylinder (Fin.append w w')) = μ.real (cylinder w) * μ.real (cylinder w') := by
  refine eq_mul_of_sum_negMulLog_eq_add
    (p := fun (w : Fin m → α) (w' : Fin n → α) => μ.real (cylinder (Fin.append w w')))
    (fun _ _ => measureReal_nonneg) (sum_measureReal_cylinder_append_right μ)
    (sum_measureReal_cylinder_append_left hμ) (sum_measureReal_cylinder μ m) ?_ w w'
  have e := blockEntropy_eq_mul_of_entropy_eq hμ h
  rw [← blockEntropy_add_eq_sum, ← blockEntropy, ← blockEntropy, e (m + n), e m, e n]
  push_cast
  ring

theorem measureReal_cylinder_eq_prod_of_entropy_eq {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) (h : entropy μ = blockEntropy μ 1) {n : ℕ}
    (w : Fin n → α) : μ.real (cylinder w) = ∏ k, μ.real (cylinder ![w k]) := by
  induction n with
  | zero =>
    have h0 := sum_measureReal_cylinder μ 0
    rw [Fintype.sum_unique] at h0
    rw [Subsingleton.elim w default, h0, Finset.univ_eq_empty, Finset.prod_empty]
  | succ n ih =>
    have e : w = Fin.append (Fin.init w) ![w (Fin.last n)] := by
      rw [Fin.append_right_eq_snoc, Matrix.cons_val_zero, Fin.snoc_init_self]
    have ha := measureReal_cylinder_append_of_entropy_eq hμ h (Fin.init w) ![w (Fin.last n)]
    rw [← e, ih (Fin.init w)] at ha
    rw [ha, Fin.prod_univ_castSucc]
    rfl

theorem measureReal_preimage_shift_cylinder_eq_prod_of_entropy_eq {μ : Measure (ℤ → α)}
    [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ)
    (h : entropy μ = blockEntropy μ 1) (k : ℤ) {n : ℕ} (w : Fin n → α) :
    μ.real {x | ∀ j : Fin n, x (k + j) = w j} = ∏ j, μ.real (cylinder ![w j]) := by
  rw [← measureReal_cylinder_eq_prod_of_entropy_eq hμ h w,
    ← measureReal_preimage_shift hμ k (measurableSet_cylinder w)]
  rfl

theorem blockEntropy_one_add_sum_le (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ] (q : α → ℝ)
    (hq : ∀ i, 0 < q i) :
    blockEntropy μ 1 + ∑ i, μ.real (cylinder ![i]) * Real.log (q i) ≤ Real.log (∑ i, q i) := by
  rw [blockEntropy_one]
  exact sum_negMulLog_add_sum_mul_log_le (fun _ => measureReal_nonneg)
    (sum_measureReal_cylinder_one μ) hq

theorem measureReal_cylinder_eq_of_blockEntropy_one_add_sum_eq (μ : Measure (ℤ → α))
    [IsProbabilityMeasure μ] (q : α → ℝ) (hq : ∀ i, 0 < q i)
    (h : blockEntropy μ 1 + ∑ i, μ.real (cylinder ![i]) * Real.log (q i) = Real.log (∑ i, q i))
    (i : α) : μ.real (cylinder ![i]) = q i / ∑ j, q j := by
  rw [blockEntropy_one] at h
  exact eq_div_sum_of_sum_negMulLog_add_sum_mul_log_eq (p := fun i => μ.real (cylinder ![i]))
    (fun _ => measureReal_nonneg) (sum_measureReal_cylinder_one μ) hq h i

end Bernoulli

end FractalGeometry
