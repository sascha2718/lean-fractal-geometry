import FractalGeometry.Probability.GridPercolation.UpperBound
import FractalGeometry.Probability.GridPercolation.BoxCoverRateLimit
import FractalGeometry.Probability.GridPercolation.GrowthOnSurvival
import FractalGeometry.Probability.GridPercolation.ProjectionPositive

/-!
# Box dimension of rectangular fractal percolation

The independent Bernoulli-retention specialisation of the box-dimension formula
in Gatzouras and Lalley (1994), Theorem 4.1 in the authors' March 1993 version.
The statement is the limit of logarithmic covering counts at all small scales.
It holds almost surely on nonextinction when the expected offspring exceeds one.
-/

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory Filter Topology
open FractalGeometry.Dimension.PhiAssouad

variable {A : GridLaw} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

theorem gatzourasLalley_boxCoverRate (hX : IsPercolation P X) (hm : 1 < A.m) :
    ∀ᵐ ω ∂P, ω ∈ survival X →
      Tendsto (boxCoverRate (limitSet X ω)) (𝓝[>] (0 : ℝ)) (𝓝 A.sbox) := by
  have hlower := ae_le_liminf_approximateSquareRate_of_growth hX hm
    (ae_exists_pos_eventually_descendantCount_ge hX hm)
    (forall_exists_measure_prunedColumnCount_ge_of_isPercolation hX hm)
  filter_upwards [hlower, ae_limsup_approximateSquareRate_le hX hm] with ω hlo hup hs
  exact tendsto_boxCoverRate_of_le_liminf_of_limsup_le
    ((mem_survival_iff_limitSet_nonempty X ω).mp hs) hup (hlo hs)

theorem gatzourasLalley_boxDimension (hX : IsPercolation P X) (hm : 1 < A.m) :
    ∀ᵐ ω ∂P, ω ∈ survival X →
      lowerBoxDim (limitSet X ω) = A.sbox ∧ upperBoxDim (limitSet X ω) = A.sbox := by
  filter_upwards [gatzourasLalley_boxCoverRate hX hm] with ω hω hs
  exact ⟨(hω hs).liminf_eq, (hω hs).limsup_eq⟩

end FractalGeometry.Probability.GridPercolation
