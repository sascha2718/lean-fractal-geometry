import Mathlib
import FractalGeometry.Symbolic.Entropy

namespace FractalGeometry

open Filter Topology MeasureTheory

section Cylinder

variable {α : Type*} {m n : ℕ}

theorem mem_cylinder {w : Fin n → α} {x : ℤ → α} :
    x ∈ cylinder w ↔ ∀ k : Fin n, x (k : ℤ) = w k := Iff.rfl

end Cylinder

end FractalGeometry
