import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Processes

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory

open scoped ENNReal

variable {A : GridLaw} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

def extendColumnWord (A : GridLaw) {ℓ : ℕ} (w : ColumnWord A ℓ) : ℕ → Fin A.M :=
  fun l => if h : l < ℓ then w ⟨l, h⟩ else ⟨0, A.hM_pos⟩

omit [MeasurableSpace Ω] in

lemma columnPrefix_extendColumnWord {ℓ : ℕ} (w : ColumnWord A ℓ) :
    columnPrefix (extendColumnWord A w) ℓ = w := by
  funext l
  simp [columnPrefix, extendColumnWord, l.isLt]

end FractalGeometry.Probability.GridPercolation
