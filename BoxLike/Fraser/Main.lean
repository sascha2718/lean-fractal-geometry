module

/-
`thm:fraser` (tex lines 398 to 473), Fraser, "On the packing dimension of box-like self-affine
sets in the plane", Theorem 2.3 (numbering of arXiv:1108.2639v1), as a theorem for every box-like
self-affine set: `\dim_P X = \overline{\dim}_M X ≤ dimmaff(X)`, and under the rectangular open
set condition `\dim_P X = \dim_M X = dimmaff(X)`. No literature premise is used.

* `System.fraserROSC_holds`: the second part, `System.FraserROSC`, from the upper bound
  `System.fraserBound_holds` (`BoxLike/Fraser/UpperBound.lean`) and the lower bound
  `System.dimmaff_le_lowerBoxDim` (`BoxLike/Fraser/LowerCover.lean`).
-/
public import BoxLike.Fraser.Lower
public import BoxLike.Fraser.UpperBound

@[expose] public section

namespace BoxLike

namespace System

universe u

variable {ι : Type u} [Fintype ι] [Nonempty ι] (S : System ι)

/-- `thm:fraser`, second part (tex lines 398 to 473), Fraser, Theorem 2.3: under the rectangular
open set condition the Minkowski dimension of `X` exists and `\dim_P X = \dim_M X = dimmaff(X)`.
The upper bound is `fraserBound_holds` and the lower bound `dimmaff_le_lowerBoxDim`. -/
theorem fraserROSC_holds : S.FraserROSC :=
  S.fraserROSC_of_fraserBound S.fraserBound_holds

end System

end BoxLike
