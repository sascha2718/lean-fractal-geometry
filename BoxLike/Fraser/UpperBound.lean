module

/-
The first part of `thm:fraser` (tex lines 398 to 473), Fraser, "On the packing dimension of
box-like self-affine sets in the plane", Theorem 2.3 (numbering of arXiv:1108.2639v1), as a
theorem for every box-like self-affine set: `\dim_P X = \overline{\dim}_M X ≤ dimmaff(X)`.

The cited statement is the `Prop` `System.FraserBound` of `BoxLike.FraserChain`, and
`System.fraserBound_iff` reduces it to the inequality, which is
`System.upperBoxDim_attractor_le_dimmaff` of `BoxLike.Fraser.Upper`.

* `System.fraserBound_holds`: `System.FraserBound` holds for every box-like system.
-/
public import BoxLike.Fraser.Upper
public import BoxLike.FraserChain

@[expose] public section

namespace BoxLike

namespace System

universe u

variable {ι : Type u} [Fintype ι] [Nonempty ι] (S : System ι)

/-- `thm:fraser`, first part (tex lines 398 to 473), Fraser, Theorem 2.3: for every box-like
self-affine set `\dim_P X = \overline{\dim}_M X ≤ dimmaff(X)`. The equality is
`packingDim_attractor` and the inequality `upperBoxDim_attractor_le_dimmaff`. -/
theorem fraserBound_holds : S.FraserBound :=
  (S.fraserBound_iff).2 S.upperBoxDim_attractor_le_dimmaff

end System

end BoxLike
