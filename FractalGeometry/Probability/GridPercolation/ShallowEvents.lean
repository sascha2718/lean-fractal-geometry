import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.BlockIndependence
import FractalGeometry.Probability.GridPercolation.Configuration
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.LawInvariance
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.Processes
import FractalGeometry.Probability.GridPercolation.RootIndependence

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory

variable {A : GridLaw} {Ω : Type*}

def shallowExtend (c : ℕ) (v : ShallowCoord A c → Bool) : Configuration A :=
  fun q => if h : q.1.length < c then v (⟨q.1, h⟩, q.2) else false

lemma measurable_shallowExtend (c : ℕ) : Measurable (shallowExtend (A := A) c) := by
  apply Measurable.of_eval
  intro q
  unfold shallowExtend
  split_ifs with h
  · exact measurable_pi_apply _
  · exact measurable_const

lemma shallowExtend_shallowVector (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (c : ℕ) (ω : Ω)
    (q : Word A × (Fin A.M × Fin A.N)) (hq : q.1.length < c) :
    shallowExtend c (shallowVector X c ω) q = config X ω q := by
  simp [shallowExtend, shallowVector, config, hq]

lemma retainedBelowConfig_congr {x y : Configuration A} {c : ℕ}
    (hxy : ∀ q : Word A × (Fin A.M × Fin A.N), q.1.length < c → x q = y q) {root u : Word A}
    (hlen : root.length + u.length ≤ c) :
    retainedBelowConfig x root u ↔ retainedBelowConfig y root u := by
  unfold retainedBelowConfig
  refine forall_congr' fun l => ?_
  rw [hxy _ (by
    simp only [List.length_append, List.length_take]
    have := l.isLt
    omega)]

lemma retainedBelowConfig_shallow_iff (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (c : ℕ)
    (ω : Ω) {root u : Word A} (hlen : root.length + u.length ≤ c) :
    retainedBelowConfig (shallowExtend c (shallowVector X c ω)) root u ↔
      RetainedBelow X ω root u :=
  retainedBelowConfig_congr (fun q hq => shallowExtend_shallowVector X c ω q hq) hlen

end FractalGeometry.Probability.GridPercolation
