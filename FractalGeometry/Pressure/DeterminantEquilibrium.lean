import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.LinearCocycles.LowerBounds
import FractalGeometry.LinearCocycles.Pressure
import FractalGeometry.LinearCocycles.PressureBounds
import FractalGeometry.LinearCocycles.Products
import FractalGeometry.LinearCocycles.SingularValue
import FractalGeometry.Pressure.Rectangular.Bernoulli
import FractalGeometry.Pressure.Rectangular.Defs
import FractalGeometry.Pressure.Rectangular.DeterminantPotential
import FractalGeometry.Pressure.Rectangular.Invertibility
import FractalGeometry.Pressure.Rectangular.Matrices
import FractalGeometry.Pressure.SingularValueStatement
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.Symbolic.Concatenation
import FractalGeometry.Symbolic.Entropy

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology

open scoped Matrix.Norms.L2Operator

namespace MatrixTuple

variable {ι : Type*} [Fintype ι] (A : ι → Matrix (Fin 2) (Fin 2) ℝ) {s : ℝ}

theorem svfSum_add_of_two_le (hs : 2 ≤ s) (m n : ℕ) :
    svfSum A s (m + n) = svfSum A s m * svfSum A s n := by
  rw [svfSum, sum_ofFn_add m n fun w => svf s (word A w), svfSum, svfSum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => ?_
  rw [word_append, svf_mul_of_two_le hs]

theorem svfSum_one_of_two_le (hs : 2 ≤ s) : svfSum A s 1 = ∑ i, |(A i).det| ^ (s / 2) := by
  rw [svfSum]
  refine (Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι).symm _ _ fun i => ?_).symm
  rw [svf_of_two_le hs]
  simp [word]

theorem svfSum_of_two_le (hs : 2 ≤ s) (n : ℕ) :
    svfSum A s n = (∑ i, |(A i).det| ^ (s / 2)) ^ n := by
  induction n with
  | zero => simp [svfSum, svf_of_two_le hs]
  | succ n ih => rw [svfSum_add_of_two_le A hs, ih, svfSum_one_of_two_le A hs, pow_succ]

theorem pressure_of_two_le (hs : 2 ≤ s) :
    pressure A s = Real.log (∑ i, |(A i).det| ^ (s / 2)) := by
  have h : (fun n : ℕ => Real.log (svfSum A s n) / n) '' Set.Ici 1 =
      {Real.log (∑ i, |(A i).det| ^ (s / 2))} := by
    ext t
    simp only [Set.mem_image, Set.mem_Ici, Set.mem_singleton_iff]
    constructor
    · rintro ⟨n, hn, rfl⟩
      rw [svfSum_of_two_le A hs, Real.log_pow,
        mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 hn))]
    · rintro rfl
      exact ⟨1, le_rfl, by rw [svfSum_of_two_le A hs]; simp⟩
  rw [pressure, h, csInf_singleton]

variable {A}

variable [MeasurableSpace ι] [MeasurableSingletonClass ι] {μ : Measure (ℤ → ι)}
  [IsProbabilityMeasure μ]

end MatrixTuple

namespace MatrixTuple

variable {ι : Type*} [Fintype ι] (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ)

noncomputable def detWeight (i : ι) : ℝ :=
  |(A i).det| ^ (s / 2) / ∑ j, |(A j).det| ^ (s / 2)

variable {A}

omit [Fintype ι] in

theorem rpow_abs_det_pos (hA : ∀ i, (A i).det ≠ 0) (t : ℝ) (i : ι) : 0 < |(A i).det| ^ t :=
  Real.rpow_pos_of_pos (abs_pos.2 (hA i)) t

theorem detWeight_pos (hA : ∀ i, (A i).det ≠ 0) (i : ι) : 0 < detWeight A s i :=
  div_pos (rpow_abs_det_pos hA _ i)
    (Finset.sum_pos (fun j _ => rpow_abs_det_pos hA _ j) ⟨i, Finset.mem_univ i⟩)

theorem sum_detWeight [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) : ∑ i, detWeight A s i = 1 := by
  simp only [detWeight]
  rw [← Finset.sum_div]
  exact div_self (Finset.sum_pos (fun j _ => rpow_abs_det_pos hA _ j) Finset.univ_nonempty).ne'

variable (A) [MeasurableSpace ι]

noncomputable def detWeightMeasure : Measure ι := weightMeasure (detWeight A s)

variable {A}

theorem isProbabilityMeasure_detWeightMeasure [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) :
    IsProbabilityMeasure (detWeightMeasure A s) :=
  isProbabilityMeasure_weightMeasure (fun i => (detWeight_pos s hA i).le) (sum_detWeight s hA)

variable [MeasurableSingletonClass ι]

theorem measureReal_detWeightMeasure_singleton (hA : ∀ i, (A i).det ≠ 0) (i : ι) :
    (detWeightMeasure A s).real {i} = detWeight A s i :=
  measureReal_weightMeasure_singleton (detWeight_pos s hA i).le

variable {s}

theorem hasGibbsBounds_bernoulli [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) (hs : 2 ≤ s) :
    HasGibbsBounds A s (bernoulli (detWeightMeasure A s)) := by
  have := isProbabilityMeasure_detWeightMeasure s hA
  have hZ : 0 < ∑ j, |(A j).det| ^ (s / 2) :=
    Finset.sum_pos (fun j _ => rpow_abs_det_pos hA _ j) Finset.univ_nonempty
  have hsvf : ∀ (n : ℕ) (w : Fin n → ι),
      svf s (word A (List.ofFn w)) = ∏ j, |(A (w j)).det| ^ (s / 2) := by
    intro n w
    induction n with
    | zero => simp [svf_of_two_le hs]
    | succ n ih =>
      rw [List.ofFn_succ, word_cons, svf_mul_of_two_le hs, ih, Fin.prod_univ_succ,
        svf_of_two_le hs]
  have key : ∀ (n : ℕ) (w : Fin n → ι), (bernoulli (detWeightMeasure A s)).real (cylinder w) =
      Real.exp (-(n * pressure A s)) * svf s (word A (List.ofFn w)) := by
    intro n w
    rw [measureReal_bernoulli_cylinder, pressure_of_two_le A hs, hsvf, neg_mul_eq_mul_neg,
      ← Real.log_inv, ← Real.log_rpow (inv_pos.2 hZ), Real.exp_log (Real.rpow_pos_of_pos
        (inv_pos.2 hZ) _), Real.rpow_natCast, Finset.prod_congr rfl fun j _ =>
        measureReal_detWeightMeasure_singleton s hA (w j)]
    simp only [detWeight, div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    ring
  refine ⟨1, le_rfl, fun n _ w => ?_⟩
  rw [key, inv_one, one_mul]
  exact ⟨le_rfl, le_rfl⟩

end MatrixTuple

namespace RectangularIFS

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] (S : RectangularIFS ι) (s : ℝ)

variable [MeasurableSingletonClass ι] [Nonempty ι] {s}

theorem hasGibbsBounds_bernoulli (hs : 2 ≤ s) :
    S.HasGibbsBounds s (bernoulli (S.detWeightMeasure s)) :=
  MatrixTuple.hasGibbsBounds_bernoulli S.det_mat_ne_zero hs

end RectangularIFS

end FractalGeometry
