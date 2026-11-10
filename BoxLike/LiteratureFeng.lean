module

/-
The results of D.-J. Feng, *Dimension of invariant measures for affine iterated function
systems*, Duke Math. J. 172 (2023), arXiv:1901.01691v2, cited in `sec:entropies` and
`sec:ledrappier_young_formula`, as `Prop`-valued definitions about the partitions and entropies
of `BoxLike/DimPartitions.lean`. All are proved elsewhere in the library.

Feng's set `Σ'` lies inside the article's box-like `Σ'`, with each partition extended by one
null atom; the conditional measures agree almost everywhere (`System.condMeas_fengXi_ae_eq`), so
the statements for Feng's partitions and for the library's are equivalent.

* `FengInfoSum`, `FengInfoSumBar`: Lemma 4.6, first identity of (4.16) (`fengInfoSum_holds`,
  `fengInfoSumBar_holds`).
* `FengLedrappierYoung`, `FengLedrappierYoungBar`: `thm:feng1`, Theorems 1.2 and 1.3
  (`fengLedrappierYoung_holds`, `fengLedrappierYoungBar_holds`).
-/
public import BoxLike.DimPartitions

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

/-- Feng, Lemma 4.6, first identity of (4.16), for the planar partitions:
`-log μ_𝐢^{ξ_i}(𝒫_0^{n-1}(𝐢)) = ∑_{k<n} I_μ(𝒫 | \widehat{ξ}_i)(σ^k 𝐢)` for all `n`, on one set of
full measure. The proof of `thm:feng_entropy_zero` uses it. Hypotheses as in
`thm:feng_entropy_as_limit`. -/
def FengInfoSum : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ], MeasurePreserving (shift 1) μ μ →
    Ergodic (shift 1) μ → S.lyapunov₂ μ < S.lyapunov₁ μ → ∀ i : ℕ,
    ∀ᵐ x ∂μ, ∀ n : ℕ, -Real.log ((condMeas μ (S.xi μ i) x).real (cylinder (block n x))) =
      ∑ k ∈ Finset.range n, condInfo μ (S.xi μ i) (shift k x)

/-- Feng, Lemma 4.6, first identity of (4.16), for the projective system and an
invariant measure `ν` on `Σ_Z`, ergodic or not; the article checks Feng's constant-multiplicity
hypothesis (4.7) in `sec:entropies`, tex lines 1842 to 1842. Rotations and proximality are
not needed. -/
def FengInfoSumBar : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι),
    S.WithRotations → S.Proximal → ∀ (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν],
    MeasurePreserving (shift 1) ν ν → ν (subshift S.o)ᶜ = 0 → ∀ i : ℕ,
    ∀ᵐ y ∂ν, ∀ n : ℕ, -Real.log ((condMeas ν (S.xiBar i) y).real (cylinder (block n y))) =
      ∑ k ∈ Finset.range n, condInfo ν (S.xiBar i) (shift k y)

/-- `thm:feng1`, first part, `eq:feng1_1`; Feng, Theorems 1.2 and 1.3, for `d = 2`
and simple Lyapunov spectrum: if `μ` is ergodic with `λ_2(𝖠, μ) < λ_1(𝖠, μ)`, then `π_*μ` is
exact-dimensional with
`dim π_*μ = (h_1(μ) - h_0(μ)) / λ_1(𝖠, μ) + (h_2(μ) - h_1(μ)) / λ_2(𝖠, μ)`.
Feng works with closed Euclidean balls; `IsExactDim` on `ℝ × ℝ` uses closed balls of the
supremum norm, which gives the same pointwise dimension. -/
def FengLedrappierYoung : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ], MeasurePreserving (shift 1) μ μ →
    Ergodic (shift 1) μ → S.lyapunov₂ μ < S.lyapunov₁ μ →
    IsExactDim (μ.map S.proj)
      ((S.dimEntropy μ 1 - S.dimEntropy μ 0) / S.lyapunov₁ μ +
        (S.dimEntropy μ 2 - S.dimEntropy μ 1) / S.lyapunov₂ μ)

/-- `thm:feng1`, second part; Feng, Theorems 1.2 and 1.3, for the self-similar system
`Ψ` on `ℝ`: if `ν` is an ergodic invariant measure on `Σ_Z`, then `\overline{π}_*ν` is
exact-dimensional with
`dim \overline{π}_*ν = (\overline{h}_1(ν) - \overline{h}_0(ν)) / \overline{λ}(𝖠, ν)`.
Rotations and proximality are not needed. -/
def FengLedrappierYoungBar : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι),
    S.WithRotations → S.Proximal → ∀ (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν],
    MeasurePreserving (shift 1) ν ν → Ergodic (shift 1) ν → ν (subshift S.o)ᶜ = 0 →
    IsExactDim (ν.map S.projBar)
      ((S.dimEntropyBar ν 1 - S.dimEntropyBar ν 0) / S.lyapBar ν)

end BoxLike
