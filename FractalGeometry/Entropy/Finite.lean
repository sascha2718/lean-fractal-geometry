/-
Finite Shannon entropy and aggregation of a probability distribution.
A map whose fibres have at most M elements loses at most log M entropy.
Zero probabilities are allowed. These elementary inequalities are proved
directly from the logarithm bound.
-/
import Mathlib

noncomputable section
open Classical
open scoped BigOperators

namespace FractalGeometry.Entropy

def finiteEntropy {A : Type*} [Fintype A] (p : A → ℝ) : ℝ :=
  ∑ a, Real.negMulLog (p a)

def fibreMass {A B : Type*} [Fintype A] (T : A → B) (p : A → ℝ) (b : B) : ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a ↦ T a = b), p a

private theorem negMulLog_tangent {p q M : ℝ} (hp : 0 ≤ p) (hq : 0 < q)
    (hM : 0 < M) :
    Real.negMulLog p ≤ -p * Real.log q + p * Real.log M + q / M - p := by
  rcases eq_or_lt_of_le hp with hp0 | hp
  · subst p
    simpa using (div_nonneg hq.le hM.le)
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hq (mul_pos hM hp))) hp.le
  rw [Real.log_div (ne_of_gt hq) (ne_of_gt (mul_pos hM hp)),
    Real.log_mul (ne_of_gt hM) (ne_of_gt hp)] at h
  have he : p * (q / (M * p) - 1) = q / M - p := by field_simp
  rw [he] at h
  simp only [Real.negMulLog_def]
  linarith

theorem entropy_sum_le_mass_log_card {A : Type*} (s : Finset A) (p : A → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) {M : ℝ} (hM : 0 < M) (hcard : (s.card : ℝ) ≤ M) :
    ∑ a ∈ s, Real.negMulLog (p a) ≤
      Real.negMulLog (∑ a ∈ s, p a) + (∑ a ∈ s, p a) * Real.log M := by
  let q := ∑ a ∈ s, p a
  have hq : 0 ≤ q := Finset.sum_nonneg hp
  rcases eq_or_lt_of_le hq with hq0 | hq
  · have hz : ∀ a ∈ s, p a = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg hp).mp hq0.symm
    have he : (∑ a ∈ s, Real.negMulLog (p a)) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      simp [hz a ha]
    rw [he]
    change 0 ≤ Real.negMulLog q + q * Real.log M
    rw [← hq0]
    simp
  · have hb := Finset.sum_le_sum fun a ha ↦ negMulLog_tangent (hp a ha) hq hM
    have he : (∑ a ∈ s, (-p a * Real.log q + p a * Real.log M + q / M - p a)) =
        -q * Real.log q + q * Real.log M + (s.card : ℝ) * (q / M) - q := by
      simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul,
        Finset.sum_neg_distrib, q]
    rw [he] at hb
    have hc : (s.card : ℝ) * (q / M) ≤ q := by
      calc
        _ ≤ M * (q / M) := mul_le_mul_of_nonneg_right hcard (div_nonneg hq.le hM.le)
        _ = q := by field_simp
    change _ ≤ Real.negMulLog q + q * Real.log M
    simp only [Real.negMulLog_def] at hb ⊢
    linarith

theorem entropy_loss_le_log_fibre {A B : Type*} [Fintype A] [Fintype B]
    (T : A → B) (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    {M : ℕ} (hM : 0 < M)
    (hcard : ∀ b, (Finset.univ.filter (fun a ↦ T a = b)).card ≤ M) :
    finiteEntropy p - Real.log M ≤ finiteEntropy (fibreMass T p) := by
  have hf (f : A → ℝ) :
      ∑ b, ∑ a ∈ Finset.univ.filter (fun a ↦ T a = b), f a = ∑ a, f a := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun b _ ↦
    entropy_sum_le_mass_log_card (M := (M : ℝ)) (Finset.univ.filter (fun a ↦ T a = b)) p
      (fun a _ ↦ hp a) (by exact_mod_cast hM) (by exact_mod_cast hcard b))
  rw [hf] at hb
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, hf, hsum, one_mul] at hb
  change finiteEntropy p ≤ finiteEntropy (fibreMass T p) + Real.log (M : ℝ) at hb
  linarith

end FractalGeometry.Entropy
