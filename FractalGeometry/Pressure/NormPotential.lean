import Mathlib
import FractalGeometry.LinearCocycles.LowerBounds
import FractalGeometry.LinearCocycles.Lyapunov
import FractalGeometry.LinearCocycles.Products
import FractalGeometry.Symbolic.Concatenation
import FractalGeometry.Symbolic.Cylinders
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.OneSidedShift
import FractalGeometry.Symbolic.SequenceTopology
import FractalGeometry.Symbolic.Shift
import FractalGeometry.Symbolic.WordAverages
import FractalGeometry.Symbolic.WordIntegrals

namespace FractalGeometry

open MeasureTheory Filter Topology

open scoped Matrix.Norms.L2Operator

section OneSided

variable {α : Type*} [Fintype α] [MeasurableSpace α]

noncomputable def blockEntropyPlus (ν : Measure (ℕ → α)) (n : ℕ) : ℝ :=
  ∑ w : Fin n → α, Real.negMulLog (ν.real (futureCylinder w))

noncomputable def entropyPlus (ν : Measure (ℕ → α)) : ℝ :=
  limUnder atTop fun n : ℕ => blockEntropyPlus ν n / n

variable [MeasurableSingletonClass α]

omit [Fintype α] in

theorem measureReal_map_eta_futureCylinder (μ : Measure (ℤ → α)) {n : ℕ} (w : Fin n → α) :
    (μ.map eta).real (futureCylinder w) = μ.real (cylinder w) := by
  rw [map_measureReal_apply measurable_eta (measurableSet_futureCylinder w)]
  rfl

theorem blockEntropyPlus_map_eta (μ : Measure (ℤ → α)) (n : ℕ) :
    blockEntropyPlus (μ.map eta) n = blockEntropy μ n := by
  simp only [blockEntropyPlus, blockEntropy, measureReal_map_eta_futureCylinder]

theorem entropyPlus_map_eta (μ : Measure (ℤ → α)) : entropyPlus (μ.map eta) = entropy μ := by
  simp only [entropyPlus, entropy, blockEntropyPlus_map_eta]

end OneSided

namespace MatrixTuple

variable {ι : Type*} (A : ι → Matrix (Fin 2) (Fin 2) ℝ)

section Defs

variable [Fintype ι]

noncomputable def normSum (q : ℝ) (n : ℕ) : ℝ := ∑ w : Fin n → ι, ‖word A (List.ofFn w)‖ ^ q

noncomputable def normPressure (q : ℝ) : ℝ :=
  limUnder atTop fun n : ℕ => Real.log (normSum A q n) / n

variable [MeasurableSpace ι]

noncomputable def normLyapPlus (ν : Measure (ℕ → ι)) : ℝ :=
  limUnder atTop fun n : ℕ =>
    (∑ w : Fin n → ι, ν.real (futureCylinder w) * Real.log ‖word A (List.ofFn w)‖) / n

def IsNormEquilibriumPlus (q : ℝ) (ν : Measure (ℕ → ι)) : Prop :=
  normPressure A q = q * normLyapPlus A ν + entropyPlus ν

def HasNormGibbsPlus (q : ℝ) (ν : Measure (ℕ → ι)) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ w : Fin n → ι,
    C⁻¹ * (Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn w)‖ ^ q) ≤
        ν.real (futureCylinder w) ∧
      ν.real (futureCylinder w) ≤
        C * (Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn w)‖ ^ q)

def IsNormEquilibrium (q : ℝ) (μ : Measure (ℤ → ι)) : Prop :=
  normPressure A q = q * lyapunov₁ A μ + entropy μ

def HasNormGibbs (q : ℝ) (μ : Measure (ℤ → ι)) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ w : Fin n → ι,
    C⁻¹ * (Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn w)‖ ^ q) ≤
        μ.real (cylinder w) ∧
      μ.real (cylinder w) ≤
        C * (Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn w)‖ ^ q)

end Defs

section TwoSided

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] {A}

theorem normLyapPlus_map_eta (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] :
    normLyapPlus A (μ.map eta) = lyapunov₁ A μ := by
  simp only [normLyapPlus, lyapunov₁, measureReal_map_eta_futureCylinder,
    integral_comp_futureWord_eq_sum μ fun w => Real.log ‖word A w‖]

theorem isNormEquilibriumPlus_map_eta_iff {q : ℝ} (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] :
    IsNormEquilibriumPlus A q (μ.map eta) ↔ IsNormEquilibrium A q μ := by
  rw [IsNormEquilibriumPlus, IsNormEquilibrium, normLyapPlus_map_eta, entropyPlus_map_eta]

theorem hasNormGibbsPlus_map_eta_iff {q : ℝ} (μ : Measure (ℤ → ι)) :
    HasNormGibbsPlus A q (μ.map eta) ↔ HasNormGibbs A q μ := by
  simp only [HasNormGibbsPlus, HasNormGibbs, measureReal_map_eta_futureCylinder]

end TwoSided

variable {A}

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

end MatrixTuple

end FractalGeometry
