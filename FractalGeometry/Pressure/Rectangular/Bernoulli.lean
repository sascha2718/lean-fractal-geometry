import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.LinearCocycles.Monomial
import FractalGeometry.LinearCocycles.MonomialSingularValues
import FractalGeometry.Pressure.Rectangular.Defs
import FractalGeometry.Pressure.Rectangular.DeterminantPotential
import FractalGeometry.Pressure.Rectangular.Matrices
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.Symbolic.BernoulliEntropy
import FractalGeometry.Symbolic.BernoulliMeasure
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open Filter Topology MeasureTheory ProbabilityTheory

open scoped symmDiff


namespace RectangularIFS

variable {ι : Type*} [Fintype ι] (S : RectangularIFS ι) (s : ℝ)

omit [Fintype ι] in

theorem rpow_abs_det_mat_pos (t : ℝ) (i : ι) : 0 < |(S.mat i).det| ^ t := by
  refine Real.rpow_pos_of_pos ?_ t
  rw [mat, abs_det_monomialMatrix]
  exact mul_pos (abs_pos.2 (S.a_ne_zero i)) (abs_pos.2 (S.b_ne_zero i))

noncomputable def detWeight (i : ι) : ℝ :=
  |(S.mat i).det| ^ (s / 2) / ∑ j, |(S.mat j).det| ^ (s / 2)

theorem detWeight_pos (i : ι) : 0 < S.detWeight s i :=
  div_pos (S.rpow_abs_det_mat_pos _ i)
    (Finset.sum_pos (fun j _ => S.rpow_abs_det_mat_pos _ j) ⟨i, Finset.mem_univ i⟩)

theorem sum_detWeight [Nonempty ι] : ∑ i, S.detWeight s i = 1 := by
  simp only [detWeight]
  rw [← Finset.sum_div]
  exact div_self (Finset.sum_pos (fun j _ => S.rpow_abs_det_mat_pos _ j)
    Finset.univ_nonempty).ne'

variable [MeasurableSpace ι]

noncomputable def detWeightMeasure : Measure ι := weightMeasure (S.detWeight s)

instance isProbabilityMeasure_detWeightMeasure [Nonempty ι] :
    IsProbabilityMeasure (S.detWeightMeasure s) :=
  isProbabilityMeasure_weightMeasure (fun i => (S.detWeight_pos s i).le) (S.sum_detWeight s)

variable [MeasurableSingletonClass ι]

theorem measureReal_detWeightMeasure_singleton (i : ι) :
    (S.detWeightMeasure s).real {i} = S.detWeight s i :=
  measureReal_weightMeasure_singleton (S.detWeight_pos s i).le

variable {s}

variable {S}

theorem IsEquilibriumState.eq_bernoulli {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]
    (heq : S.IsEquilibriumState s μ) (hinv : MeasurePreserving (shift 1) μ μ) (hs : 2 ≤ s) :
    μ = bernoulli (S.detWeightMeasure s) := by
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
  have hq := S.rpow_abs_det_mat_pos (s / 2)
  have hE := heq.log_sum_eq hinv hs
  have hrw : s / 2 * ∑ i, μ.real (cylinder ![i]) * Real.log |(S.mat i).det| =
      ∑ i, μ.real (cylinder ![i]) * Real.log (|(S.mat i).det| ^ (s / 2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.log_rpow (by simpa using S.rpow_abs_det_mat_pos 1 i)]
    ring
  rw [hrw] at hE
  have hG := blockEntropy_one_add_sum_le μ (fun i => |(S.mat i).det| ^ (s / 2)) hq
  have hH := entropy_le_blockEntropy_one hinv
  have hent : entropy μ = blockEntropy μ 1 := by linarith
  have hGeq : blockEntropy μ 1
      + ∑ i, μ.real (cylinder ![i]) * Real.log (|(S.mat i).det| ^ (s / 2)) =
      Real.log (∑ i, |(S.mat i).det| ^ (s / 2)) := by linarith
  refine eq_bernoulli_of_measureReal_cylinder _ fun k n w => ?_
  rw [measureReal_preimage_shift_cylinder_eq_prod_of_entropy_eq hinv hent k w]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [measureReal_cylinder_eq_of_blockEntropy_one_add_sum_eq μ _ hq hGeq,
    measureReal_detWeightMeasure_singleton, detWeight]

variable (S)

end RectangularIFS

end FractalGeometry
