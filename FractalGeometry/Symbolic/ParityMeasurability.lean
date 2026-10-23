import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.Symbolic.OrientationCoding
import FractalGeometry.Symbolic.ParityMeasures
import FractalGeometry.Symbolic.ParityRanges
import FractalGeometry.Symbolic.ParityShift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Set

universe u

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem measurableSet_range_tau (o : ι → ZMod 2) : MeasurableSet (range (tau o)) := by
  have h2 : MeasurableSet {y : ℤ → ι × ZMod 2 | (y 0).2 = 0} :=
    (measurable_snd.comp (measurable_pi_apply 0)) (measurableSet_singleton (0 : ZMod 2))
  rw [range_tau]
  exact (measurableSet_subshift o).inter h2

theorem measurableSet_range_omega (o : ι → ZMod 2) : MeasurableSet (range (omega o)) := by
  have h2 : MeasurableSet {y : ℤ → ι × ZMod 2 | (y 0).2 = 1} :=
    (measurable_snd.comp (measurable_pi_apply 0)) (measurableSet_singleton (1 : ZMod 2))
  rw [range_omega]
  exact (measurableSet_subshift o).inter h2

end FractalGeometry
