import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.WordAverages

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology

open scoped Matrix.Norms.L2Operator

section futureWord

variable {α : Type*}

variable [MeasurableSpace α]

variable [Finite α] [MeasurableSingletonClass α]

variable {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ] {G H : List α → ℝ} {c : ℝ}

theorem integral_futureWord_div_le (hc : ∀ w, G w ≤ c * w.length) {n : ℕ} (hn : 0 < n) :
    (∫ x, G (futureWord x n) ∂μ) / n ≤ c := by
  rw [div_le_iff₀ (Nat.cast_pos.2 hn)]
  calc ∫ x, G (futureWord x n) ∂μ ≤ ∫ _, c * n ∂μ :=
      integral_mono (integrable_comp_futureWord G n) (integrable_const _) fun x => by
        simpa using hc (futureWord x n)
    _ = c * n := by simp

end futureWord

end FractalGeometry
