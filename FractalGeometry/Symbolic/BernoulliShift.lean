import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.Symbolic.BernoulliMeasure
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open Filter Topology MeasureTheory ProbabilityTheory

open scoped symmDiff

section Bernoulli

variable {ι : Type*} [MeasurableSpace ι]

instance isProbabilityMeasure_bernoulli (p : Measure ι) [IsProbabilityMeasure p] :
    IsProbabilityMeasure (bernoulli p) := by
  unfold bernoulli
  infer_instance

theorem measurePreserving_shift_bernoulli (p : Measure ι) [IsProbabilityMeasure p] (m : ℤ) :
    MeasurePreserving (shift m) (bernoulli p) (bernoulli p) := by
  refine ⟨measurable_shift m, ?_⟩
  have h := Measure.infinitePi_map_piCongrLeft (fun _ : ℤ => p) (Equiv.addLeft (-m))
  have e : ⇑(MeasurableEquiv.piCongrLeft (fun _ : ℤ => ι) (Equiv.addLeft (-m))) = shift m := by
    funext x k
    rw [MeasurableEquiv.coe_piCongrLeft]
    simpa using Equiv.piCongrLeft_apply_apply (fun _ : ℤ => ι) (Equiv.addLeft (-m)) x (m + k)
  rw [e] at h
  exact h

variable [MeasurableSingletonClass ι]

variable [Fintype ι]

end Bernoulli

end FractalGeometry
