module

/-
`thm:feng1` of `sec:ledrappier_young_formula` at the article's scope, from the cited theorems of
Feng: the first part for every planar self-affine set from `PlanarFengLedrappierYoung`
(`BoxLike/LiteraturePlanarFeng.lean`), the second part for proximal box-like systems with rotations
from `FengLedrappierYoungBar` (`BoxLike/LiteratureFeng.lean`), which follows from the first part
(`fengLedrappierYoungBar_of_fengLedrappierYoung`, `BoxLike/ProjectiveLineSystem.lean`).

* `PlanarSystem.feng1`: the first part for a planar self-affine set.
* `planar_feng1`: both parts.
-/
public import BoxLike.LiteraturePlanarFeng

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

namespace PlanarSystem

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (P : PlanarSystem ι)

/-- `thm:feng1`, first
part, `eq:feng1_1`, for a planar self-affine set: for ergodic `μ` with
`λ_2(𝖠, μ) < λ_1(𝖠, μ)`, `π_*μ` is exact-dimensional with
`dim π_*μ = (h_1(μ) - h_0(μ)) / λ_1(𝖠, μ) + (h_2(μ) - h_1(μ)) / λ_2(𝖠, μ)`. -/
theorem feng1 (hly : PlanarFengLedrappierYoung.{u}) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    IsExactDim (μ.map P.proj)
      ((P.dimEntropy μ 1 - P.dimEntropy μ 0) / P.lyapunov₁ μ +
        (P.dimEntropy μ 2 - P.dimEntropy μ 1) / P.lyapunov₂ μ) :=
  hly P μ hinv herg hlt

end PlanarSystem

/-- `thm:feng1`, both
parts, at the article's scope. First part: for every planar self-affine set and every ergodic
`μ` with `λ_2 < λ_1`, `π_*μ` is exact-dimensional with
`dim π_*μ = (h_1(μ) - h_0(μ)) / λ_1(𝖠, μ) + (h_2(μ) - h_1(μ)) / λ_2(𝖠, μ)`. Second part: for
every proximal box-like self-affine set with rotations and every ergodic `ν` on `Σ_Z`,
`\overline{π}_*ν` is exact-dimensional with
`dim \overline{π}_*ν = (\overline{h}_1(ν) - \overline{h}_0(ν)) / \overline{λ}(𝖠, ν)`; this is
`FengLedrappierYoungBar`, which follows from `FengLedrappierYoung`
(`fengLedrappierYoungBar_of_fengLedrappierYoung`). -/
theorem planar_feng1 (hly : PlanarFengLedrappierYoung.{u})
    (hlyb : FengLedrappierYoungBar.{u}) :
    (∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (P : PlanarSystem ι) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ],
      MeasurePreserving (shift 1) μ μ → Ergodic (shift 1) μ → P.lyapunov₂ μ < P.lyapunov₁ μ →
      IsExactDim (μ.map P.proj)
        ((P.dimEntropy μ 1 - P.dimEntropy μ 0) / P.lyapunov₁ μ +
          (P.dimEntropy μ 2 - P.dimEntropy μ 1) / P.lyapunov₂ μ)) ∧
    (∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (S : System ι), S.WithRotations → S.Proximal →
      ∀ (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν],
      MeasurePreserving (shift 1) ν ν → Ergodic (shift 1) ν → ν (subshift S.o)ᶜ = 0 →
      IsExactDim (ν.map S.projBar)
        ((S.dimEntropyBar ν 1 - S.dimEntropyBar ν 0) / S.lyapBar ν)) :=
  ⟨fun P μ _ hinv herg hlt => P.feng1 hly μ hinv herg hlt, hlyb⟩

end BoxLike
