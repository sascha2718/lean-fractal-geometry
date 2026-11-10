module

/-
The Hausdorff dimension of a box-like self-affine set with rotations:
`sec:dimension_result_proof`, `thm:main_extended` for `0 < s < 2` and the projectively
exponentially separated case of `thm:main2`.

The Ledrappier–Young formula `thm:feng1` is evaluated with the entropies of
`sec:higher_dimensional_entropies`; a tuple without a proximal diagonal generator is reduced to
its second iterate by `thm:two-block-normalisation`. The case `s ≥ 2` of `thm:main_extended` is
not part of this module; `thm:main2` does not use it.

* `System.main_extended_normalised`: `thm:main_extended`, `0 < s < 2`, for a tuple containing
  a proximal diagonal generator.
* `System.main_extended_lt_two'`: `thm:main_extended`, `0 < s < 2`.
* `System.main2_of_bounds`: the exponentially separated case of `thm:main2` from an upper
  and a lower bound for `\dim_H(X)`.
* `System.main_extended_dimaff`, `System.main2`: `thm:main_extended` for `dimaff(X) < 2` and
  the exponentially separated case of `thm:main2`, with `s = dimaff(X)`, Falconer's bound
  `System.dimH_attractor_le` and the lower
  bound `System.le_dimH_attractor`.
-/
public import BoxLike.AffinityMain
public import BoxLike.EquilibriumEntropyLarge
public import BoxLike.EquilibriumEntropySmall
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.FalconerBound
public import BoxLike.SeparationConditions
public import BoxLike.StrongOpenSetEntropy

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {s : ℝ}

/-- `thm:main_extended` for `0 < s < 2` and a tuple containing a proximal diagonal
generator: `dim π_*μ = dimaff(𝖠)`. The parameter `s` is the
affinity dimension through `hP : P(𝖠, s) = 0`. The proof evaluates the formula of `thm:feng1`,
which gives the dimension exactly; Rossi's bound `eq:hausdorff_ergodic_lyapunov` is not used.
Depends on: `MorrisShmerkinLyapunov`, `thm:feng1` (planar, `FengLedrappierYoung`),
`dimEntropy_zero_eq_entropy`, `thm:eq_state_h1_zero`, `thm:eq_state_h2_zero`,
`thm:eq_state_h1_large`, `thm:orto_partition_dirac`, `thm:SOSC_h2_zero`, `eq:main_extended1`,
`eq:main_extended2`, `eq:diml_min2`. -/
theorem main_extended_normalised (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hjr : JordanRapaportDimension.{u}) (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u})
    (hly : FengLedrappierYoung.{u}) (hlyb : FengLedrappierYoungBar.{u})
    (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal)
    (hsep : S.ProjExpSeparation) (hs0 : 0 < s) (hs2 : s < 2) (hP : S.pressure s = 0)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ)
    (hor : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet) : IsExactDim (μ.map S.proj) s := by
  have hl := hms S hrot hdiag hs0 hs2 μ hinv heq
  have hl1 := S.lyapunov₁_neg hinv
  have henergy : entropy μ + energy (S.lyapunov₁ μ) (S.lyapunov₂ μ) s = 0 := by
    rw [← heq.pressure_eq hinv hs0.le, hP]
  have hdim := lyapDim_eq hl.le hl1 henergy
  have hlt2 := entropy_lt_of_lt_two hl.le hl1 hs2 henergy
  have hLY := hly S μ hinv herg hl
  rw [S.dimEntropy_zero_eq_entropy μ hinv herg hl] at hLY
  by_cases h1 : entropy μ ≤ -S.lyapunov₁ μ
  · have hh1 := (S.eq_state_h1_zero hms hfk hfjj hjr hfi hfib hlyb hrot hdiag hsep hs0 hs2 μ hinv
      herg heq h1).1
    have hh2 := S.eq_state_h2_zero hms hfk hfjj hjr hfi hfib hlyb hrot hdiag hsep hs0 hs2 μ hinv
      herg heq h1
    rw [hh1, hh2, ledrappierYoung_small h1, hdim] at hLY
    exact hLY
  · rw [not_le] at h1
    have hh1 := S.eq_state_h1_large hms hfk hfjj hjr hfi hfib hlyb hrot hdiag hsep hs0 hs2 μ hinv
      herg heq h1.le
    have hh2 : S.dimEntropy μ 2 = 0 := by
      by_cases h2 : entropy μ ≤ -S.lyapunov₂ μ
      · exact S.orto_partition_dirac hms hfk hfjj hjr hfi hfib hlyb hrot hdiag hsep hs0 hs2 μ
          hinv herg heq h2
      · exact S.SOSC_h2_zero hms hfk hfi hrot hdiag.proximal (hor.resolve_left h2) hs0 hs2 μ
          hinv herg heq
    rw [hh1, hh2, ledrappierYoung_large hl1 h1 hlt2.le, hdim] at hLY
    exact hLY

/-- The reduction of `thm:main_extended`, `0 < s < 2`, to the normalised case through
`thm:two-block-normalisation`, with the ergodicity hypotheses in the form in which the two cases
of `thm:box_like_proximal` use them. -/
theorem main_extended_lt_two_aux (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hjr : JordanRapaportDimension.{u}) (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u})
    (hly : FengLedrappierYoung.{u}) (hlyb : FengLedrappierYoungBar.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (hs0 : 0 < s) (hs2 : s < 2) (hP : S.pressure s = 0)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : S.HasProximalDiagonal → Ergodic (shift 1) μ)
    (herg2 : S.sq.HasProximalDiagonal → Ergodic (shift 1) (μ.map group))
    (heq : S.IsEquilibriumState s μ)
    (hor : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet) : IsExactDim (μ.map S.proj) s := by
  rcases hprox.hasProximalDiagonal_or_sq with h | h
  · exact S.main_extended_normalised hms hfk hfjj hjr hfi hfib hly hlyb hrot h hsep hs0 hs2 hP μ
      hinv (herg h) heq hor
  · have := nonempty_of_measure μ
    have e2 := S.lyapunov₂_sq_map_group (S.tendsto_lyapunov₂ hinv)
    have hor2 : entropy (μ.map group) ≤ -S.sq.lyapunov₂ (μ.map group) ∨ S.sq.StrongOpenSet := by
      rcases hor with h' | h'
      · left
        rw [entropy_map_group hinv, e2]
        linarith
      · exact Or.inr (StrongOpenSet.sq S h')
    have key := S.sq.main_extended_normalised hms hfk hfjj hjr hfi hfib hly hlyb
      (S.sq_withRotations hrot) h (ProjExpSeparation.sq S hsep) hs0 hs2
      (by rw [S.pressure_sq hs0.le, hP, mul_zero])
      (μ.map group) (measurePreserving_shift_map_group hinv) (herg2 h)
      (heq.map_group hinv hs0.le) hor2
    obtain ⟨r', M', hS'⟩ := S.sq.exists_bounds
    have hcomp : S.sq.proj ∘ group = S.proj := funext fun x => S.proj_sq_group x
    rwa [Measure.map_map hS'.measurable_proj measurable_group, hcomp] at key

/-- `thm:main_extended` for `0 < s < 2`, for every proximal box-like tuple with rotations,
assembled from the normalised case through `thm:two-block-normalisation`. The hypothesis `herg2`
is the ergodicity of `μ^(2) = β_*μ` under the shift of `Σ^(2)`, that is, of `μ` under `σ²`; the
article takes it from `thm:irred_eq_state` for `𝖠²`.
Depends on: `thm:box_like_proximal`, `thm:two-block-normalisation`
(`System.IsEquilibriumState.map_group`, `System.pressure_sq`, `entropy_map_group`,
`System.lyapunov₂_sq_map_group`, `System.ProjExpSeparation.sq`, `System.proj_sq_group`,
`System.StrongOpenSet.sq`). -/
theorem main_extended_lt_two (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hjr : JordanRapaportDimension.{u}) (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u})
    (hly : FengLedrappierYoung.{u}) (hlyb : FengLedrappierYoungBar.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (hs0 : 0 < s) (hs2 : s < 2) (hP : S.pressure s = 0)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (herg2 : Ergodic (shift 1) (μ.map group))
    (heq : S.IsEquilibriumState s μ)
    (hor : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet) : IsExactDim (μ.map S.proj) s :=
  S.main_extended_lt_two_aux hms hfk hfjj hjr hfi hfib hly hlyb hrot hprox hsep hs0 hs2 hP μ hinv
    (fun _ => herg) (fun _ => herg2) heq hor

/-- `thm:main_extended` for `0 < s < 2` with the ergodicity hypotheses discharged: in
each case of `thm:box_like_proximal` the ergodicity needed is that of the equilibrium state of a
tuple containing a proximal diagonal generator, which `ergodic_of_hasProximalDiagonal` derives
from the hypotheses `EquilibriumGibbsStatement` and `FraserJordanJurgaDecomposition`. -/
theorem main_extended_lt_two' (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hjr : JordanRapaportDimension.{u}) (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u})
    (hly : FengLedrappierYoung.{u}) (hlyb : FengLedrappierYoungBar.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (hs0 : 0 < s) (hs2 : s < 2) (hP : S.pressure s = 0)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ)
    (hor : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet) : IsExactDim (μ.map S.proj) s := by
  exact S.main_extended_lt_two_aux hms hfk hfjj hjr hfi hfib hly hlyb hrot hprox hsep hs0 hs2
    hP μ hinv (fun h => S.ergodic_of_hasProximalDiagonal hfk hfjj hrot h hs0 hs2 μ hinv heq)
    (fun h => S.sq.ergodic_of_hasProximalDiagonal hfk hfjj (S.sq_withRotations hrot) h hs0 hs2
      (μ.map group) (measurePreserving_shift_map_group hinv) (heq.map_group hinv hs0.le))
    heq hor

/-- The exponentially separated case of `thm:main2` with the two facts `hupper`, `hlower`:
the ergodicity hypotheses of `main2` are discharged by `main_extended_lt_two'`. -/
theorem main2_of_bounds (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hjr : JordanRapaportDimension.{u}) (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u})
    (hly : FengLedrappierYoung.{u}) (hlyb : FengLedrappierYoungBar.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal) (hsep : S.ProjExpSeparation)
    (hs0 : 0 < s) (hs2 : s < 2) (hP : S.pressure s = 0) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ)
    (hor : s ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet)
    (hupper : dimH S.attractor ≤ ENNReal.ofReal (min 2 s))
    (hlower : ∀ d, IsExactDim (μ.map S.proj) d → ENNReal.ofReal d ≤ dimH S.attractor) :
    dimH S.attractor = ENNReal.ofReal s := by
  have hl := S.simple_lyapunov hms hrot hprox hs0 hs2 μ hinv heq
  have hl1 := S.lyapunov₁_neg hinv
  have henergy : entropy μ + energy (S.lyapunov₁ μ) (S.lyapunov₂ μ) s = 0 := by
    rw [← heq.pressure_eq hinv hs0.le, hP]
  have hor' : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet :=
    hor.imp (entropy_le_iff hl hl1 hs2 henergy).2 id
  have hdim := S.main_extended_lt_two' hms hfk hfjj hjr hfi hfib hly hlyb hrot hprox hsep hs0 hs2
    hP μ hinv heq hor'
  refine le_antisymm ?_ (hlower s hdim)
  rwa [min_eq_right hs2.le] at hupper

/-- `thm:main_extended` for `dimaff(𝖠) < 2`. Let `X` be a proximal box-like self-affine set with
rotations satisfying the projective exponential separation condition and `μ` the
`s`-equilibrium state for `s = dimaff(𝖠) < 2`. If `h_0(μ) ≤ -λ_2(𝖠, μ)` or `X` satisfies the
strong open set condition, then `π_*μ` is exact-dimensional with `dim(π_*μ) = dimaff(𝖠)`. -/
theorem main_extended_dimaff (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hjr : JordanRapaportDimension.{u}) (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u})
    (hly : FengLedrappierYoung.{u}) (hlyb : FengLedrappierYoungBar.{u})
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (h2 : S.dimaff < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    IsExactDim (μ.map S.proj) S.dimaff := by
  have := S.nontrivial_of_withRotations hrot
  exact S.main_extended_lt_two' hms hfk hfjj hjr hfi hfib hly hlyb hrot hprox hsep
    S.dimaff_pos h2 S.pressure_dimaff μ hinv heq hor

/-- The exponentially separated case of `thm:main2`.
Let `X` be a proximal box-like self-affine set with rotations satisfying the
projective exponential separation condition such that `dimaff(X) < 2`, and let `μ` be the
`s`-equilibrium state for `s = dimaff(X)`. If
`dimaff(X) ≤ 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)`, or if `X` satisfies the strong open set condition, then
`\dim_H(X) = dimaff(X)`. The upper bound is Falconer's, `eq:hausdorff_affinity_upper_bound`,
and the lower bound is `dim(π_*μ) ≤ \dim_H(X)`. -/
theorem main2 (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hjr : JordanRapaportDimension.{u}) (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u})
    (hly : FengLedrappierYoung.{u}) (hlyb : FengLedrappierYoungBar.{u})
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (h2 : S.dimaff < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    dimH S.attractor = ENNReal.ofReal S.dimaff := by
  have := S.nontrivial_of_withRotations hrot
  exact S.main2_of_bounds hms hfk hfjj hjr hfi hfib hly hlyb hrot hprox hsep S.dimaff_pos h2
    S.pressure_dimaff μ hinv heq hor S.dimH_attractor_le fun _ hd => S.le_dimH_attractor hd

end System

end BoxLike
