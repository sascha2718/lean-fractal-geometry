module

public import BoxLike.Shmerkin.BSG
public import BoxLike.Shmerkin.Inverse.Main
public import BoxLike.Shmerkin.Flattening
public import BoxLike.Shmerkin.Theorem51

@[expose] public section

/-!
# Shmerkin, Theorem 2.1 and Proposition 6.8: the assembly

The inverse theorem for `L^q` norms of convolutions (Shmerkin, arXiv:1609.07802v3, Theorem 2.1)
from its two ingredients, and Proposition 6.8 from the inverse theorem.

* `inverseTheorem`: Theorem 2.1, from the asymmetric Balog–Szemerédi–Gowers theorem
  (`theorem32`, `BoxLike.Shmerkin.BSG`) and the weak form of Bourgain's structure theorem
  (`Bourgain.theorem31Weak`, `BoxLike.Shmerkin.Bourgain.Main`) through Section 3
  (`inverseTheorem_of_theorem32`, `BoxLike.Shmerkin.Inverse.Main`).
* `proposition68`: Proposition 6.8 for a self-similar measure, through Theorem 5.1 on the circle
  (`theorem51_of_inverseTheorem`), Proposition 4.13 (`proposition413`) and the line form of
  Theorem 5.1 (`flattening_of_theorem51`).
-/

open MeasureTheory Filter Topology Set

namespace BoxLike
namespace Shmerkin

/-- Theorem 2.1 of Shmerkin, the inverse theorem for `L^q` norms of convolutions. -/
theorem inverseTheorem : InverseTheorem :=
  inverseTheorem_of_theorem32 theorem32

variable {κ : Type*} [Fintype κ]

/-- Proposition 6.8 of Shmerkin (Section 6.4) for a self-similar measure. -/
theorem proposition68 {r t p : κ → ℝ} {μ : Measure ℝ} (h : IsSelfSimilar r t p μ) :
    Proposition68 r t p μ :=
  proposition68_of_flattening h fun _ hq hd hτ =>
    flattening_of_theorem51 h hq hd hτ fun _ _ h' hμ' hd' hτ' =>
      have := h'.isProbabilityMeasure
      theorem51_of_inverseTheorem inverseTheorem hμ' hq hd' hτ' (proposition413 h' hq hd')

end Shmerkin
end BoxLike
