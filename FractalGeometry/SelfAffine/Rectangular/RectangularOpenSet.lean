import Mathlib
import GeometricMeasureTheory.Box.ModifiedBox
import FractalGeometry.SelfAffine.Rectangular.Attractor
import FractalGeometry.SelfAffine.Rectangular.Coding
import FractalGeometry.SelfAffine.Rectangular.Defs

open GeometricMeasureTheory

namespace FractalGeometry

open Metric

namespace RectangularIFS

variable {ι : Type*} (S : RectangularIFS ι)

def RectangularOpenSet : Prop :=
  ∃ a b c d : ℝ, a < b ∧ c < d ∧
    (∀ i, S.phi i '' (Set.Ioo a b ×ˢ Set.Ioo c d) ⊆ Set.Ioo a b ×ˢ Set.Ioo c d) ∧
    Pairwise fun i j => Disjoint (S.phi i '' (Set.Ioo a b ×ˢ Set.Ioo c d))
      (S.phi j '' (Set.Ioo a b ×ˢ Set.Ioo c d))

theorem attractor_subset_of_invariant [Finite ι] {L : Set (ℝ × ℝ)} (hL : IsCompact L)
    (hLne : L.Nonempty) (hLsub : ∀ i, S.phi i '' L ⊆ L) : S.attractor ⊆ L := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  exact hS.subset_of_invariant S.isCompact_attractor S.attractor_eq_iUnion.subset hL hLne hLsub

end RectangularIFS

end FractalGeometry
