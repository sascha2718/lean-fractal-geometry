import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.SelfSimilar.Line.Defs
import FractalGeometry.SelfSimilar.Line.Lyapunov
import FractalGeometry.SelfSimilar.Line.Separation
import FractalGeometry.SelfSimilar.Line.Words
import FractalGeometry.Symbolic.FutureWords

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology

open scoped Matrix.Norms.L2Operator

namespace LineIFS

section Word

variable {ι : Type*} (S : LineIFS ι)

variable {S} {δ r M : ℝ}

variable (S)

theorem log_abs_gDeriv_futureWord (y : ℤ → ι) (n : ℕ) :
    Real.log |S.gDeriv (futureWord y n)| =
      ∑ k ∈ Finset.range n, Real.log |S.ratio (y k)| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [futureWord_succ, gDeriv_append, abs_mul,
      Real.log_mul (abs_ne_zero.2 (S.gDeriv_ne_zero _)) (abs_ne_zero.2 (S.gDeriv_ne_zero _)),
      ih, Finset.sum_range_succ]
    simp

end Word

end LineIFS

end FractalGeometry
