module

/-
The equality `dimmaff(X) = dimaff(X)` of `sec:intro_fraser` for `dimaff(X) < 2` under the
absence of projective exact overlaps alone, with neither the threshold nor the strong open set
condition of `thm:main2`: the diagonal subsystems in the proof of `thm:main2` show that both
coordinate projections of `X` have dimension `min{1, dimaff(X)}`, so the modified and the
ordinary singular value functions agree at `s = dimaff(X)`.

The modified singular value function `ψ^s(𝐢) = α_1(𝐢)^{s(𝐢)} α_2(𝐢)^{s - s(𝐢)}` of
`BoxLike/ModifiedAffinity.lean` weights the longer side of `A_𝐢([0,1]²)` by the Minkowski
dimension `s(𝐢)` of the projection of `X` onto the axis parallel to it. When both projections
have Minkowski dimension `min{1, s}` and `s ≤ 2`, this is `α_1^{min{1,s}} α_2^{s - min{1,s}}`,
the singular value function `φ^s(A_𝐢)`, which is `α_1^s` for `s ≤ 1` and `α_1 α_2^{s-1}`
for `1 ≤ s ≤ 2`. The modified pressure then agrees with the pressure at `s`; at
`s = dimaff(X)` both vanish, and `dimmaff(X)`, the unique zero of the modified pressure on
`[0, ∞)`, equals `dimaff(X)`. The projection dimensions are those of
`BoxLike/MainTwoProse/ProjectionDimension.lean`.

* `svfExp_eq_min`: the exponent of `α_1` in `φ^s` is `min{1, s}` for `s ≤ 2`.
* `System.modSvf_eq_svf_of_projDim_eq_min`: `ψ^s = φ^s` when `s_1 = s_2 = min{1, s}` and
  `s ≤ 2`.
* `System.modPressure_eq_pressure_of_projDim_eq_min`: the two pressures agree at such `s`.
* `System.dimmaff_eq_dimaff_of_projDim_eq_min`: `dimmaff(X) = dimaff(X)` when
  `s_1 = s_2 = min{1, dimaff(X)}` and `dimaff(X) ≤ 2`.
* `System.dimmaff_eq_dimaff_of_noExactOverlaps`,
  `System.dimmaff_eq_dimaff_of_noExactOverlaps_proved`: `dimmaff(X) = dimaff(X)` for a proximal
  box-like self-affine set with rotations whose projective system has no exact overlaps and
  `dimaff(X) < 2`, with and without the literature hypotheses of the proof of `thm:main2`.
-/
public import BoxLike.MainTwoProse.ProjectionDimension
public import BoxLike.ModifiedAffinity

@[expose] public section

namespace BoxLike

universe u

/-- The exponent `p(s)` of `α_1` in `φ^s(A) = α_1^{p(s)} α_2^{s - p(s)}` is `min{1, s}` for
`s ≤ 2` (`sec:affinity_dim`): `φ^s(A) = α_1^s` for `s ≤ 1` and `α_1 α_2^{s-1}` for
`1 ≤ s ≤ 2`. -/
theorem svfExp_eq_min {s : ℝ} (h2 : s ≤ 2) : svfExp s = min 1 s := by
  unfold svfExp
  split_ifs with h1
  · exact (min_eq_right h1).symm
  · exact (min_eq_left (not_le.1 h1).le).symm

namespace System

variable {ι : Type u} (S : System ι)

/-- `sec:intro_fraser`: the modified singular value function at `s ≤ 2` equals the singular
value function when both coordinate projections of `X` have Minkowski dimension `min{1, s}`:
`ψ^s(𝐢) = α_1(𝐢)^{min{1,s}} α_2(𝐢)^{s - min{1,s}} = φ^s(A_𝐢)`. -/
theorem modSvf_eq_svf_of_projDim_eq_min {s : ℝ} (hs2 : s ≤ 2) (h : ∀ c, S.projDim c = min 1 s)
    (w : List ι) : S.modSvf s w = svf s (S.matWord w) := by
  rw [svf_matWord_eq, modSvf, S.wordDim_eq h, svfExp_eq_min hs2]

variable [Fintype ι] [Nonempty ι]

/-- The modified pressure agrees with the pressure at every `0 ≤ s ≤ 2` at which both
coordinate projections of `X` have Minkowski dimension `min{1, s}` (`sec:intro_fraser`). -/
theorem modPressure_eq_pressure_of_projDim_eq_min {s : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2)
    (h : ∀ c, S.projDim c = min 1 s) : S.modPressure s = S.pressure s :=
  S.modPressure_eq_pressure hs0 fun c => (h c).trans (svfExp_eq_min hs2).symm

/-- `sec:intro_fraser`: if both coordinate projections of `X` have Minkowski dimension
`min{1, dimaff(X)}` and `dimaff(X) ≤ 2`, then `dimmaff(X) = dimaff(X)`: the two pressures agree
at `s = dimaff(X)`, where the pressure vanishes, and `dimmaff(X)` is the unique zero of the
modified pressure on `[0, ∞)`. -/
theorem dimmaff_eq_dimaff_of_projDim_eq_min (h2 : S.dimaff ≤ 2)
    (h : ∀ c, S.projDim c = min 1 S.dimaff) : S.dimmaff = S.dimaff := by
  refine S.dimmaff_eq S.dimaff_nonneg ?_
  rw [S.modPressure_eq_pressure_of_projDim_eq_min S.dimaff_nonneg h2 h, S.pressure_dimaff]

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- `sec:intro_fraser`: for a proximal box-like self-affine set `X` with rotations whose
projective system has no exact overlaps and `dimaff(X) < 2`, `dimmaff(X) = dimaff(X)`, with
neither the threshold nor the strong open set condition of `thm:main2`: both coordinate
projections have Minkowski dimension `min{1, dimaff(X)}` (`projDim_eq_min`), so the modified
and the ordinary singular value functions agree at `s = dimaff(X)`.
Depends on: `ShannonMcMillanBreimanStatement`, `MorrisShmerkinLyapunov`,
`EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, `KittleKoglerDimension`. -/
theorem dimmaff_eq_dimaff_of_noExactOverlaps (hsmb : ShannonMcMillanBreimanStatement.{u})
    (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hkk : KittleKoglerDimension.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal) (hfree : S.NoExactOverlaps)
    (h2 : S.dimaff < 2) : S.dimmaff = S.dimaff :=
  S.dimmaff_eq_dimaff_of_projDim_eq_min h2.le
    (S.projDim_eq_min hsmb hms hfk hfjj hkk hrot hprox hfree h2)

/-- `dimmaff_eq_dimaff_of_noExactOverlaps` with the five statements it depends on discharged by
the library theorems `shannonMcMillanBreiman`, `morrisShmerkinLyapunov_holds`,
`equilibriumGibbs`, `fraserJordanJurgaDecomposition_holds` and `kittleKoglerDimension_holds`:
`dimmaff(X) = dimaff(X)` for a proximal box-like self-affine set with rotations whose
projective system has no exact overlaps and `dimaff(X) < 2` (`sec:intro_fraser`). -/
theorem dimmaff_eq_dimaff_of_noExactOverlaps_proved (hrot : S.WithRotations)
    (hprox : S.Proximal) (hfree : S.NoExactOverlaps) (h2 : S.dimaff < 2) :
    S.dimmaff = S.dimaff :=
  S.dimmaff_eq_dimaff_of_noExactOverlaps shannonMcMillanBreiman morrisShmerkinLyapunov_holds
    equilibriumGibbs fraserJordanJurgaDecomposition_holds kittleKoglerDimension_holds hrot hprox
    hfree h2

end System

end BoxLike
