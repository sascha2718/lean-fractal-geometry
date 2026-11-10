module

/-
The affinity dimension in the main results: `sec:affinity_dim`, `thm:main1` and the last step
of the proof of `thm:main2`.

* `System.nontrivial_of_withRotations`: a tuple with rotations has at least two generators.
* `System.lyapDim_le_dimaff`: `\dim_L(𝖠, μ) ≤ dimaff(𝖠)` for every invariant measure, from
  `eq:variational`.
* `System.IsEquilibriumState.lyapDim_eq_dimaff`: `\dim_L(𝖠, μ) = dimaff(𝖠)` for an equilibrium
  state at `s = dimaff(𝖠)`.
* `System.main1_dimaff`: `thm:main1` with `s = dimaff(X) < 2`.
* `System.le_dimH_attractor`: `dim(π_*μ) ≤ \dim_H(X)`, the use of `eq:dimension_measure_def` in
  the proof of `thm:main2`.
-/
public import BoxLike.AffinityDim
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.General
public import BoxLike.MassDistribution
public import BoxLike.Variational

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι)

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- A tuple with rotations has at least two generators. -/
theorem nontrivial_of_withRotations (h : S.WithRotations) : Nontrivial ι := by
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := h
  refine ⟨⟨i, j, fun hij => ?_⟩⟩
  rw [hij, hj] at hi
  exact absurd hi (by decide)

/-- `\dim_L(𝖠, μ) ≤ dimaff(𝖠)` for every invariant probability measure `μ`, from
`eq:variational`. -/
theorem lyapDim_le_dimaff [Nonempty ι] {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) :
    lyapDim (entropy μ) (S.lyapunov₁ μ) (S.lyapunov₂ μ) ≤ S.dimaff :=
  S.le_dimaff_of_pressure_nonneg
    (lyapDim_nonneg (S.lyapunov₂_le_lyapunov₁ hinv) (S.lyapunov₁_neg hinv) (entropy_nonneg hinv))
    (S.pressure_lyapDim_nonneg hinv)

variable {S} in
/-- `\dim_L(𝖠, μ) = dimaff(𝖠)` for an equilibrium state at `s = dimaff(𝖠)`. -/
theorem IsEquilibriumState.lyapDim_eq_dimaff [Nonempty ι] {μ : Measure (ℤ → ι)}
    [IsProbabilityMeasure μ] (heq : S.IsEquilibriumState S.dimaff μ)
    (hinv : MeasurePreserving (shift 1) μ μ) :
    lyapDim (entropy μ) (S.lyapunov₁ μ) (S.lyapunov₂ μ) = S.dimaff :=
  lyapDim_eq (S.lyapunov₂_le_lyapunov₁ hinv) (S.lyapunov₁_neg hinv)
    ((heq.pressure_eq hinv S.dimaff_nonneg).symm.trans S.pressure_dimaff)

/-- The case `0 < s < 2` of `thm:main1`, with the values. Let `X` be a proximal box-like
self-affine set with rotations satisfying the projective exponential separation condition such
that `dimaff(X) < 2`, and let `μ` be the `s`-equilibrium state for `s = dimaff(X)`. Then the
pointwise dimension of each coordinate projection of `μ` is `min{1, -h_0(μ)/λ_1(𝖠, μ)}` or
`min{1, -h_0(μ)/λ_2(𝖠, μ)}` almost everywhere. Both projections fail to be exact-dimensional
precisely when `s < 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)`. At equality and above, both projections are
exact-dimensional of dimension one. -/
theorem main1_dimaff (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hjr : JordanRapaportDimension.{u})
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal) (hsep : S.ProjExpSeparation)
    (h2 : S.dimaff < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ) (c : ZMod 2) :
    HasLocalDimPair (S.marginal c μ) (min 1 (-entropy μ / S.lyapunov₁ μ))
        (min 1 (-entropy μ / S.lyapunov₂ μ)) ∧
      ((¬ ∃ d, IsExactDim (S.marginal c μ) d) ↔
        S.dimaff < 2 - S.lyapunov₁ μ / S.lyapunov₂ μ) ∧
      (2 - S.lyapunov₁ μ / S.lyapunov₂ μ ≤ S.dimaff → IsExactDim (S.marginal c μ) 1) := by
  have := S.nontrivial_of_withRotations hrot
  exact S.main1 hms hfk hfjj hjr hrot hprox hsep S.dimaff_pos h2 S.pressure_dimaff μ hinv heq c

/-- `dim(π_*μ) ≤ \dim_H(X)` for an exact-dimensional projected measure: the use of
`eq:dimension_measure_def` in the proof of `thm:main2`. -/
theorem le_dimH_attractor {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] {d : ℝ}
    (h : IsExactDim (μ.map S.proj) d) : ENNReal.ofReal d ≤ dimH S.attractor := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  exact IsExactDim.le_dimH_of_map hS.measurable_proj h

end System

end BoxLike
