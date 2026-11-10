module

/-
The second part of `thm:fraser` (tex lines 398 to 473), Fraser, "On the packing dimension of
box-like self-affine sets in the plane", Theorem 2.3 (numbering of arXiv:1108.2639v1), from the
first part. The cited content of the second part beyond the first is the lower bound
`dimmaff(X) ≤ \underline{\dim}_M X` under the rectangular open set condition
(`System.fraserROSC_of_le`); it is proved in `BoxLike.Fraser.LowerCover` after the proof
"Lower bound (assuming the ROSC)" of Fraser's §5, with his Lemma 5.1 (2) in
`BoxLike.Fraser.LowerStop`.

* `System.dimmaff_le_lowerBoxDim` (in `BoxLike.Fraser.LowerCover`): `dimmaff(X) ≤
  \underline{\dim}_M X` under the rectangular open set condition.
* `System.fraserROSC_of_fraserBound`: `System.FraserBound` implies `System.FraserROSC`.
-/
public import BoxLike.Fraser.LowerCover
public import BoxLike.FraserChain

@[expose] public section

namespace BoxLike

universe u

namespace System

variable {ι : Type u} [Fintype ι] [Nonempty ι] (S : System ι)

/-- `thm:fraser` (tex lines 398 to 473), second part, from the first: if
`\overline{\dim}_M X ≤ dimmaff(X)` for every box-like set, then under the rectangular open set
condition `\dim_P X = \dim_M X = dimmaff(X)`. The lower bound is `dimmaff_le_lowerBoxDim`. -/
theorem fraserROSC_of_fraserBound (hB : S.FraserBound) : S.FraserROSC :=
  S.fraserROSC_of_le hB S.dimmaff_le_lowerBoxDim

end System

end BoxLike
