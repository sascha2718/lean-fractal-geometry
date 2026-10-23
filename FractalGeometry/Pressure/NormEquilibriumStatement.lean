import Mathlib
import FractalGeometry.LinearCocycles.Classification
import FractalGeometry.Pressure.NormPotential
import FractalGeometry.Symbolic.OneSidedShift

namespace FractalGeometry

open MeasureTheory Filter Topology

open scoped Matrix Matrix.Norms.L2Operator

universe u

def FengKaenmakiNormEquilibrium : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (A : ι → Matrix (Fin 2) (Fin 2) ℝ), (∀ i, (A i).det ≠ 0) → TupleIrreducible A →
    ∀ {q : ℝ}, 0 < q → ∀ (ν : Measure (ℕ → ι)) [IsProbabilityMeasure ν],
    MeasurePreserving shiftPlus ν ν → MatrixTuple.IsNormEquilibriumPlus A q ν →
    MatrixTuple.HasNormGibbsPlus A q ν ∧
      ∀ (ν' : Measure (ℕ → ι)) [IsProbabilityMeasure ν'], MeasurePreserving shiftPlus ν' ν' →
        MatrixTuple.IsNormEquilibriumPlus A q ν' → ν' = ν

end FractalGeometry
