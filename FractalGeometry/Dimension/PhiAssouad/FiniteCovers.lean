import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering

namespace FractalGeometry.Dimension.PhiAssouad

open Set

open scoped ENNReal

variable {E : Type*} [PseudoEMetricSpace E]

lemma exists_isCover (r : ℝ) (X : Set E) :
    ∃ C : Set (Set E), X ⊆ ⋃₀ C ∧ ∀ S ∈ C, Metric.ediam S ≤ ENNReal.ofReal r :=
  ⟨(fun x => {x}) '' X, fun x hx => ⟨{x}, ⟨x, hx, rfl⟩, rfl⟩, by
    rintro S ⟨x, -, rfl⟩
    show Metric.ediam {x} ≤ _
    rw [Metric.ediam_singleton]
    exact zero_le⟩

lemma exists_isCover_encard_eq (r : ℝ) (X : Set E) :
    ∃ C : Set (Set E), X ⊆ ⋃₀ C ∧ (∀ S ∈ C, Metric.ediam S ≤ ENNReal.ofReal r) ∧
      C.encard = coverNum r X := by
  set T : Set ℕ∞ := {n | ∃ C : Set (Set E), X ⊆ ⋃₀ C ∧
    (∀ S ∈ C, Metric.ediam S ≤ ENNReal.ofReal r) ∧ C.encard = n} with hT
  have hne : T.Nonempty := by
    obtain ⟨C, hcov, hdiam⟩ := exists_isCover r X
    exact ⟨C.encard, C, hcov, hdiam, rfl⟩
  obtain ⟨C, hcov, hdiam, hC⟩ := csInf_mem hne
  refine ⟨C, hcov, hdiam, ?_⟩
  rw [hC]
  refine le_antisymm ?_ ?_
  · exact le_iInf fun C' => le_iInf fun hcov' => le_iInf fun hdiam' =>
      csInf_le (OrderBot.bddBelow _) ⟨C', hcov', hdiam', rfl⟩
  · rw [← hC]
    exact coverNum_le_of_isCover hcov hdiam

lemma coverNum_union_le (r : ℝ) (X Y : Set E) :
    coverNum r (X ∪ Y) ≤ coverNum r X + coverNum r Y := by
  obtain ⟨CX, hcovX, hdiamX, hCX⟩ := exists_isCover_encard_eq r X
  obtain ⟨CY, hcovY, hdiamY, hCY⟩ := exists_isCover_encard_eq r Y
  have hcov : X ∪ Y ⊆ ⋃₀ (CX ∪ CY) := by
    rw [Set.sUnion_union]
    exact Set.union_subset_union hcovX hcovY
  have hdiam : ∀ S ∈ CX ∪ CY, Metric.ediam S ≤ ENNReal.ofReal r := by
    rintro S (hS | hS)
    · exact hdiamX S hS
    · exact hdiamY S hS
  calc coverNum r (X ∪ Y) ≤ (CX ∪ CY).encard := coverNum_le_of_isCover hcov hdiam
    _ ≤ CX.encard + CY.encard := Set.encard_union_le _ _
    _ = coverNum r X + coverNum r Y := by rw [hCX, hCY]

lemma coverNum_biUnion_le {ι : Type*} (r : ℝ) (s : Finset ι) (f : ι → Set E) :
    coverNum r (⋃ i ∈ s, f i) ≤ ∑ i ∈ s, coverNum r (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Finset.sum_empty]
      have : (∅ : Set E) ⊆ ⋃₀ (∅ : Set (Set E)) := by simp
      have h := coverNum_le_of_isCover (r := r) this (fun S hS => absurd hS (Set.notMem_empty _))
      simpa using h
  | insert a s ha ih =>
      rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
      exact le_trans (coverNum_union_le r _ _) (add_le_add (le_refl _) ih)

lemma toENNReal_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ∞) :
    ((∑ i ∈ s, f i : ℕ∞) : ℝ≥0∞) = ∑ i ∈ s, ((f i : ℕ∞) : ℝ≥0∞) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ENat.toENNReal_add, ih]

end FractalGeometry.Dimension.PhiAssouad
