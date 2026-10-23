import Mathlib

namespace FractalGeometry.Dimension.PhiAssouad

open Set EMetric

open scoped ENNReal

noncomputable def coverNum {E : Type*} [PseudoEMetricSpace E]
    (r : ℝ) (X : Set E) : ℕ∞ :=
  ⨅ (C : Set (Set E)) (_ : X ⊆ ⋃₀ C)
      (_ : ∀ S ∈ C, Metric.ediam S ≤ ENNReal.ofReal r), C.encard

section

variable {E : Type*} [PseudoEMetricSpace E]

lemma coverNum_le_of_isCover {r : ℝ} {X : Set E} {C : Set (Set E)} (hcov : X ⊆ ⋃₀ C)
    (hdiam : ∀ S ∈ C, Metric.ediam S ≤ ENNReal.ofReal r) : coverNum r X ≤ C.encard := by
  refine le_trans (iInf_le _ C) ?_
  exact le_trans (iInf_le _ hcov) (iInf_le _ hdiam)

lemma coverNum_mono {r : ℝ} {X Y : Set E} (h : X ⊆ Y) : coverNum r X ≤ coverNum r Y := by
  refine le_iInf fun C => le_iInf fun hcov => le_iInf fun hdiam => ?_
  exact coverNum_le_of_isCover (h.trans hcov) hdiam

lemma coverNum_anti {r r' : ℝ} {X : Set E} (h : r ≤ r') : coverNum r' X ≤ coverNum r X := by
  refine le_iInf fun C => le_iInf fun hcov => le_iInf fun hdiam => ?_
  exact coverNum_le_of_isCover hcov
    fun S hS => (hdiam S hS).trans (ENNReal.ofReal_le_ofReal h)

end

def AssouadExponents {E : Type*} [PseudoEMetricSpace E] (X : Set E) : Set ℝ :=
  {s | 0 ≤ s ∧ ∃ C : ℝ, 0 < C ∧ ∀ R r : ℝ, 0 < r → r ≤ R → R < 1 → ∀ x ∈ X,
    (coverNum r (X ∩ Metric.eball x (ENNReal.ofReal R)) : ℝ≥0∞)
      ≤ ENNReal.ofReal (C * (R / r) ^ s)}

def PhiAssouadExponents {E : Type*} [PseudoEMetricSpace E]
    (φ : ℝ → ℝ) (X : Set E) : Set ℝ :=
  {s | 0 ≤ s ∧ ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → R < 1 → ∀ x ∈ X,
    (coverNum (R ^ (1 + φ R)) (X ∩ Metric.eball x (ENNReal.ofReal R)) : ℝ≥0∞)
      ≤ ENNReal.ofReal (C * R ^ (-φ R * s))}

noncomputable def dimAphi {E : Type*} [PseudoEMetricSpace E]
    (φ : ℝ → ℝ) (X : Set E) : ℝ :=
  sInf {s | 0 ≤ s ∧ ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → R < 1 → ∀ x ∈ X,
    (coverNum (R ^ (1 + φ R)) (X ∩ Metric.eball x (ENNReal.ofReal R)) : ℝ≥0∞)
      ≤ ENNReal.ofReal (C * R ^ (-φ R * s))}

section

variable {E : Type*} [PseudoEMetricSpace E]

theorem assouadExponents_subset {φ : ℝ → ℝ} (hφ : ∀ R, 0 < R → R < 1 → 0 < φ R)
    (X : Set E) : AssouadExponents X ⊆ PhiAssouadExponents φ X := by
  rintro s ⟨hs0, C, hC, hbound⟩
  refine ⟨hs0, C, hC, fun R hR0 hR1 x hx => ?_⟩
  have hφR := hφ R hR0 hR1
  have hr0 : 0 < R ^ (1 + φ R) := Real.rpow_pos_of_pos hR0 _
  have hrR : R ^ (1 + φ R) ≤ R := by
    calc R ^ (1 + φ R) ≤ R ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hR0 hR1.le (by linarith)
      _ = R := Real.rpow_one R
  have hratio : R / R ^ (1 + φ R) = R ^ (-(φ R)) := by
    rw [div_eq_iff hr0.ne', ← Real.rpow_add hR0,
      show -(φ R) + (1 + φ R) = 1 by ring, Real.rpow_one]
  have hpow : (R / R ^ (1 + φ R)) ^ s = R ^ (-(φ R) * s) := by
    rw [hratio, ← Real.rpow_mul hR0.le]
  rw [← hpow]
  exact hbound R (R ^ (1 + φ R)) hr0 hrR hR1 x hx

end

end FractalGeometry.Dimension.PhiAssouad
