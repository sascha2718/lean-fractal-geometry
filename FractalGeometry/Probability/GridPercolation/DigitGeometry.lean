import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open Finset

noncomputable def digitLeft (Mb : ℕ) (d : ℕ → ℕ) (a : ℕ) : ℝ :=
  ∑ l ∈ Finset.range a, (d l : ℝ) / (Mb : ℝ) ^ (l + 1)

def digitIndex (Mb : ℕ) (d : ℕ → ℕ) (a : ℕ) : ℕ :=
  ∑ l ∈ Finset.range a, d l * Mb ^ (a - 1 - l)

lemma digitLeft_congr (Mb : ℕ) {d e : ℕ → ℕ} (a : ℕ) (h : ∀ l < a, d l = e l) :
    digitLeft Mb d a = digitLeft Mb e a := by
  unfold digitLeft
  exact Finset.sum_congr rfl fun l hl => by rw [h l (Finset.mem_range.mp hl)]

lemma digitLeft_succ_head (Mb : ℕ) (d : ℕ → ℕ) (a : ℕ) :
    digitLeft Mb d (a + 1) =
      ((d 0 : ℝ) + digitLeft Mb (fun l => d (l + 1)) a) / (Mb : ℝ) := by
  unfold digitLeft
  rw [Finset.sum_range_succ', add_div, Finset.sum_div,
    add_comm ((d 0 : ℝ) / (Mb : ℝ))]
  congr 1
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [div_div, ← pow_succ]
  · norm_num

lemma digitLeft_mono (Mb : ℕ) (d : ℕ → ℕ) {k a : ℕ} (h : k ≤ a) :
    digitLeft Mb d k ≤ digitLeft Mb d a := by
  unfold digitLeft
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h) ?_
  exact fun l _ _ => div_nonneg (Nat.cast_nonneg _) (by positivity)

lemma digitLeft_add_inv_le (Mb : ℕ) (hMb : 1 ≤ Mb) (d : ℕ → ℕ) {k a : ℕ} (hka : k ≤ a)
    (hd : ∀ l, k ≤ l → l < a → d l < Mb) :
    digitLeft Mb d a + ((Mb : ℝ) ^ a)⁻¹ ≤ digitLeft Mb d k + ((Mb : ℝ) ^ k)⁻¹ := by
  induction a, hka using Nat.le_induction with
  | base => exact le_rfl
  | succ a hka ih =>
    have hMb0 : (0 : ℝ) < Mb := by exact_mod_cast lt_of_lt_of_le one_pos hMb
    have hda : (d a : ℝ) ≤ (Mb : ℝ) - 1 := by
      have h1 : d a + 1 ≤ Mb := hd a hka (Nat.lt_succ_self a)
      have h2 : ((d a + 1 : ℕ) : ℝ) ≤ (Mb : ℝ) := by exact_mod_cast h1
      push_cast at h2
      linarith
    have hpos : (0 : ℝ) < (Mb : ℝ) ^ (a + 1) := by positivity
    have hstep : digitLeft Mb d (a + 1) + ((Mb : ℝ) ^ (a + 1))⁻¹ ≤
        digitLeft Mb d a + ((Mb : ℝ) ^ a)⁻¹ := by
      have hsum : digitLeft Mb d (a + 1) =
          digitLeft Mb d a + (d a : ℝ) / (Mb : ℝ) ^ (a + 1) := by
        unfold digitLeft
        rw [Finset.sum_range_succ]
      rw [hsum]
      have hkey : (d a : ℝ) / (Mb : ℝ) ^ (a + 1) + ((Mb : ℝ) ^ (a + 1))⁻¹ ≤
          ((Mb : ℝ) ^ a)⁻¹ := by
        have heq : (d a : ℝ) / (Mb : ℝ) ^ (a + 1) + ((Mb : ℝ) ^ (a + 1))⁻¹ =
            ((d a : ℝ) + 1) / (Mb : ℝ) ^ (a + 1) := by
          field_simp
        rw [heq, div_le_iff₀ hpos]
        calc (d a : ℝ) + 1 ≤ (Mb : ℝ) := by linarith
          _ = ((Mb : ℝ) ^ a)⁻¹ * (Mb : ℝ) ^ (a + 1) := by
              rw [pow_succ]
              field_simp
      linarith
    exact hstep.trans (ih fun l hkl hla => hd l hkl (hla.trans (Nat.lt_succ_self a)))

lemma digitLeft_eq_digitIndex_div (Mb : ℕ) (hMb : 1 ≤ Mb) (d : ℕ → ℕ) (a : ℕ) :
    digitLeft Mb d a = (digitIndex Mb d a : ℝ) / (Mb : ℝ) ^ a := by
  have hMb0 : (0 : ℝ) < Mb := by exact_mod_cast lt_of_lt_of_le one_pos hMb
  unfold digitLeft digitIndex
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hla : l < a := Finset.mem_range.mp hl
  have hexp : (a - 1 - l) + (l + 1) = a := by omega
  rw [div_eq_div_iff (by positivity) (by positivity)]
  rw [mul_assoc, ← pow_add, hexp]

end FractalGeometry.Probability.GridPercolation
