import Mathlib
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.Shift

namespace FractalGeometry

open Filter Topology MeasureTheory

theorem negMulLog_add_mul_log_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (h : q = 0 → p = 0) :
    Real.negMulLog p + p * Real.log q ≤ q - p := by
  rcases hp.eq_or_lt with rfl | hp'
  · simpa using hq
  · have hq' : 0 < q := hq.lt_of_ne' fun h0 => hp'.ne' (h h0)
    have hlog := Real.log_le_sub_one_of_pos (div_pos hq' hp')
    rw [Real.log_div hq'.ne' hp'.ne'] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hp
    have e : p * (q / p - 1) = q - p := by field_simp
    rw [e] at hmul
    rw [Real.negMulLog]
    linarith

section Finite

variable {A B : Type*} [Fintype A] [Fintype B]

theorem sum_gibbs_defect {p q : A → ℝ} (hsum : ∑ a, p a = 1) (hq : ∀ a, 0 < q a) :
    ∑ a, (q a / ∑ b, q b - p a
        - (Real.negMulLog (p a) + p a * Real.log (q a / ∑ b, q b)))
      = Real.log (∑ a, q a) - (∑ a, Real.negMulLog (p a) + ∑ a, p a * Real.log (q a)) := by
  have hA : Nonempty A := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    simp at hsum
  have hQ : 0 < ∑ a, q a := Finset.sum_pos (fun a _ => hq a) Finset.univ_nonempty
  have e : ∑ a, p a * Real.log (q a / ∑ b, q b)
      = ∑ a, p a * Real.log (q a) - Real.log (∑ b, q b) := by
    simp only [Real.log_div (hq _).ne' hQ.ne', mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hsum, one_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, e,
    ← Finset.sum_div, div_self hQ.ne', hsum]
  ring

theorem sum_negMulLog_add_sum_mul_log_le {p q : A → ℝ} (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) (hq : ∀ a, 0 < q a) :
    ∑ a, Real.negMulLog (p a) + ∑ a, p a * Real.log (q a) ≤ Real.log (∑ a, q a) := by
  have hA : Nonempty A := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    simp at hsum
  have hQ : 0 < ∑ a, q a := Finset.sum_pos (fun a _ => hq a) Finset.univ_nonempty
  have h := sum_gibbs_defect hsum hq
  have h0 : 0 ≤ ∑ a, (q a / ∑ b, q b - p a
      - (Real.negMulLog (p a) + p a * Real.log (q a / ∑ b, q b))) :=
    Finset.sum_nonneg fun a _ => sub_nonneg.2 <|
      negMulLog_add_mul_log_le (hp a) (div_pos (hq a) hQ).le
        fun h0 => absurd h0 (div_pos (hq a) hQ).ne'
  linarith

end Finite

section Bernoulli

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem entropy_le_blockEntropy_div {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) {n : ℕ} (hn : n ≠ 0) :
    entropy μ ≤ blockEntropy μ n / n := by
  have hsub : Subadditive (blockEntropy μ) := fun m n => blockEntropy_add_le hμ m n
  have hbdd : BddBelow (Set.range fun n : ℕ => blockEntropy μ n / n) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact div_nonneg (blockEntropy_nonneg μ n) (Nat.cast_nonneg n)⟩
  rw [entropy, (hsub.tendsto_lim hbdd).limUnder_eq]
  exact hsub.lim_le_div hbdd hn

end Bernoulli

end FractalGeometry
