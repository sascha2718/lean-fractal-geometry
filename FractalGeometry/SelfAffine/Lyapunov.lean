import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.LinearCocycles.Lyapunov
import FractalGeometry.LinearCocycles.Products
import FractalGeometry.LinearCocycles.Regularity
import FractalGeometry.SelfAffine.Partitions
import FractalGeometry.SelfAffine.Planar
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.Shift
import FractalGeometry.Symbolic.SuperadditiveWordAverages

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology Matrix

open scoped Matrix.Norms.L2Operator

namespace AffineIFS

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (P : AffineIFS ι) {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]

theorem tendsto_lyapunov₁ (hμ : MeasurePreserving (shift 1) μ μ) :
    Tendsto (fun n : ℕ => (∫ x, Real.log ‖MatrixTuple.word P.mat (futureWord x n)‖ ∂μ) / n)
      atTop (𝓝 (P.lyapunov₁ μ)) :=
  MatrixTuple.tendsto_lyapunov₁_of_det_ne_zero P.det_ne_zero hμ

theorem tendsto_lyapunov₂ (hμ : MeasurePreserving (shift 1) μ μ) :
    Tendsto (fun n : ℕ =>
      (∫ x, Real.log (|(MatrixTuple.word P.mat (futureWord x n)).det| /
        ‖MatrixTuple.word P.mat (futureWord x n)‖) ∂μ) / n) atTop (𝓝 (P.lyapunov₂ μ)) :=
  MatrixTuple.tendsto_lyapunov₂_of_det_ne_zero P.det_ne_zero hμ

theorem lyapunov₁_neg (hμ : MeasurePreserving (shift 1) μ μ) : P.lyapunov₁ μ < 0 := by
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
  obtain ⟨i₁, -, h₁⟩ := Finset.exists_max_image Finset.univ (fun i => ‖P.mat i‖)
    Finset.univ_nonempty
  set r := ‖P.mat i₁‖
  have hr : 0 < r := norm_pos_of_det_ne_zero (P.det_ne_zero i₁)
  have hr1 : r < 1 := P.norm_lt_one i₁
  have hbound : ∀ w : List ι, Real.log ‖MatrixTuple.word P.mat w‖ ≤ Real.log r * w.length := by
    intro w
    have hpos := norm_pos_of_det_ne_zero (MatrixTuple.det_word_ne_zero P.det_ne_zero w)
    calc Real.log ‖MatrixTuple.word P.mat w‖ ≤ Real.log (r ^ w.length) :=
          Real.log_le_log hpos (P.norm_word_le hr.le (fun i => h₁ i (Finset.mem_univ i)) w)
      _ = Real.log r * w.length := by rw [Real.log_pow, mul_comm]
  have hle : P.lyapunov₁ μ ≤ Real.log r :=
    le_of_tendsto (P.tendsto_lyapunov₁ hμ) ((eventually_gt_atTop 0).mono fun n hn =>
      integral_futureWord_div_le (G := fun w => Real.log ‖MatrixTuple.word P.mat w‖) hbound hn)
  exact hle.trans_lt (Real.log_neg hr hr1)

end AffineIFS

end FractalGeometry
