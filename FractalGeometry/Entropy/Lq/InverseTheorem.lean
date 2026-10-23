import Mathlib
import FractalGeometry.Entropy.Lq.BSG
import FractalGeometry.Entropy.Lq.Basic
import FractalGeometry.Entropy.Lq.Flattening
import FractalGeometry.Entropy.Lq.Inverse.Main
import FractalGeometry.Entropy.Lq.Prop413
import FractalGeometry.Entropy.Lq.Prop68
import FractalGeometry.Entropy.Lq.Statements
import FractalGeometry.Entropy.Lq.Theorem51

open MeasureTheory Filter Topology Set

namespace FractalGeometry

namespace Lq

theorem inverseTheorem : InverseTheorem :=
  inverseTheorem_of_theorem32 theorem32

variable {κ : Type*} [Fintype κ]

theorem proposition68 {r t p : κ → ℝ} {μ : Measure ℝ} (h : IsSelfSimilar r t p μ) :
    Proposition68 r t p μ :=
  proposition68_of_flattening h fun _ hq hd hτ =>
    flattening_of_theorem51 h hq hd hτ fun _ _ h' hμ' hd' hτ' =>
      have := h'.isProbabilityMeasure
      theorem51_of_inverseTheorem inverseTheorem hμ' hq hd' hτ' (proposition413 h' hq hd')

end Lq

end FractalGeometry
