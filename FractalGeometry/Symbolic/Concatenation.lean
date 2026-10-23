import Mathlib
import GeometricMeasureTheory.Box.BoxDimension


open GeometricMeasureTheory

namespace FractalGeometry

open Filter Topology

theorem sum_ofFn_add {ι M : Type*} [Fintype ι] [AddCommMonoid M] (k n : ℕ) (G : List ι → M) :
    ∑ f : Fin (k + n) → ι, G (List.ofFn f)
      = ∑ g : Fin k → ι, ∑ h : Fin n → ι, G (List.ofFn g ++ List.ofFn h) :=
  calc ∑ f : Fin (k + n) → ι, G (List.ofFn f)
      = ∑ p : (Fin k → ι) × (Fin n → ι), G (List.ofFn p.1 ++ List.ofFn p.2) :=
        (Fintype.sum_equiv (Fin.appendEquiv k n) _ _ fun x => by simp [Fin.appendEquiv]).symm
    _ = ∑ g : Fin k → ι, ∑ h : Fin n → ι, G (List.ofFn g ++ List.ofFn h) :=
        Fintype.sum_prod_type _

end FractalGeometry
