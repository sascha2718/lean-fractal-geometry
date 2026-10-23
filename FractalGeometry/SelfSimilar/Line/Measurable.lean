import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.SelfSimilar.Line.Coding
import FractalGeometry.SelfSimilar.Line.Defs
import FractalGeometry.SelfSimilar.Line.Separation
import FractalGeometry.SelfSimilar.Line.Words
import FractalGeometry.Symbolic.FutureWords

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology

variable {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]

namespace LineIFS

variable {S : LineIFS ι} {r M : ℝ}

theorem measurable_gDeriv_futureWord (S : LineIFS ι) (k : ℕ) :
    Measurable fun y : ℤ → ι => S.gDeriv (futureWord y k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : (fun y : ℤ → ι => S.gDeriv (futureWord y (k + 1))) =
        fun y => S.gDeriv (futureWord y k) * S.ratio (y k) := by
      funext y
      rw [futureWord_succ, gDeriv_append]
      simp
    rw [h]
    exact ih.mul ((Measurable.of_discrete (f := S.ratio)).comp (measurable_pi_apply _))

theorem measurable_codeTerm (S : LineIFS ι) (k : ℕ) :
    Measurable fun y : ℤ → ι => S.codeTerm y k :=
  (S.measurable_gDeriv_futureWord k).mul
    ((Measurable.of_discrete (f := S.trans)).comp (measurable_pi_apply _))

theorem Bounds.measurable_code (hS : S.Bounds r M) : Measurable S.code := by
  refine measurable_of_tendsto_metrizable
    (f := fun n y => ∑ k ∈ Finset.range n, S.codeTerm y k)
    (fun n => Finset.measurable_sum _ fun k _ => S.measurable_codeTerm k) ?_
  exact tendsto_pi_nhds.2 fun y => (hS.summable_codeTerm y).hasSum.tendsto_sum_nat

end LineIFS

end FractalGeometry
