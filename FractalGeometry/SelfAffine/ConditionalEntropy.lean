import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.SelfAffine.Partitions
import FractalGeometry.SelfAffine.Planar
import FractalGeometry.Symbolic.Conditional
import FractalGeometry.Symbolic.ConditionalInformation
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology Set

universe u

namespace AffineIFS

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (P : AffineIFS ι)

def InfoSum (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] (i : ℕ) : Prop :=
  ∀ᵐ x ∂μ, ∀ n : ℕ, -Real.log ((condMeas μ (P.xi μ i) x).real (cylinder (block n x))) =
    ∑ k ∈ Finset.range n, condInfo μ (P.xi μ i) (shift k x)

theorem feng_entropy_as_limit_of_infoSum (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) {i : ℕ} (hsum : P.InfoSum μ i) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => -Real.log ((condMeas μ (P.xi μ i) x).real (cylinder (block n x))) / n)
      atTop (𝓝 (P.dimEntropyAt μ i x)) :=
  tendsto_neg_log_condMeas_cylinder hinv hsum

end AffineIFS

end FractalGeometry
