module

/-
`thm:feng_entropy_as_limit` and `thm:feng_entropy_zero` at the article's scope: every planar
self-affine set and every ergodic shift-invariant measure with `λ_2(𝖠, μ) < λ_1(𝖠, μ)`, with no
premise. Feng's identity (Lemma 4.6, (4.16)) is proved in `BoxLike/Planar/FengIdentity.lean` for
every planar system with `μ(Σ') = 1`, and `μ(Σ') = 1` is the planar Oseledets theorem of
`BoxLike/Planar/OseledetsTheorem.lean`.

* `feng_entropy_as_limit_general`: both clauses of `thm:feng_entropy_as_limit`.
* `feng_entropy_zero_general`: both clauses of `thm:feng_entropy_zero`.
-/
public import BoxLike.Planar.FengIdentity
public import BoxLike.Planar.OseledetsTheorem

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology

universe u

/-- `thm:feng_entropy_as_limit` for every planar self-affine set. Planar clause: for every
planar system, every ergodic `μ` with `λ_2 < λ_1` and `i ≤ 2`,
`-n⁻¹ log μ_𝐢^{ξ_i}(𝒫_0^{n-1}(𝐢)) → h_i(μ, 𝐢)` almost everywhere. Projective clause: for every
proximal box-like system with rotations and every invariant `ν` carried by `Σ_Z`, ergodic or not,
and `i ≤ 1`, the analogous limit for `\overline{ξ}_i` and `\overline{h}_i(ν, 𝐣)`. -/
theorem feng_entropy_as_limit_general :
    (∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
        (P : PlanarSystem ι) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ],
        Ergodic (shift 1) μ → P.lyapunov₂ μ < P.lyapunov₁ μ → ∀ i ≤ 2,
          ∀ᵐ x ∂μ, Tendsto
            (fun n : ℕ => -Real.log ((condMeas μ (P.xi μ i) x).real (cylinder (block n x))) / n)
            atTop (𝓝 (P.dimEntropyAt μ i x))) ∧
      ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
        (S : System ι), S.WithRotations → S.Proximal →
        ∀ (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν],
          MeasurePreserving (shift 1) ν ν → ν (subshift S.o)ᶜ = 0 → ∀ i ≤ 1,
            ∀ᵐ y ∂ν, Tendsto
              (fun n : ℕ => -Real.log ((condMeas ν (S.xiBar i) y).real (cylinder (block n y))) / n)
              atTop (𝓝 (S.dimEntropyBarAt ν i y)) :=
  ⟨fun P μ _ herg hlt i hi => feng_entropy_as_limit_of_full.1 P μ herg.toMeasurePreserving herg
    hlt (P.measure_SigmaPrime_compl_of_ergodic μ herg hlt) i hi, feng_entropy_as_limit_of_full.2⟩

/-- `thm:feng_entropy_zero` for every planar self-affine set. Planar clause: for every planar
system, every ergodic `μ` with `λ_2 < λ_1` and `i ≤ 2`, `h_i(μ, 𝐢) = 0` exactly when
`μ_𝐢^{ξ_i} = δ_𝐢`, for almost every `𝐢`. Projective clause: the same for `\overline{ξ}_i`,
`i ≤ 1`, and every invariant `ν` carried by `Σ_Z`, ergodic or not. -/
theorem feng_entropy_zero_general :
    (∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
        (P : PlanarSystem ι) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ],
        Ergodic (shift 1) μ → P.lyapunov₂ μ < P.lyapunov₁ μ → ∀ i ≤ 2,
          ∀ᵐ x ∂μ, P.dimEntropyAt μ i x = 0 ↔ condMeas μ (P.xi μ i) x = Measure.dirac x) ∧
      ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
        (S : System ι), S.WithRotations → S.Proximal →
        ∀ (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν],
          MeasurePreserving (shift 1) ν ν → ν (subshift S.o)ᶜ = 0 → ∀ i ≤ 1,
            ∀ᵐ y ∂ν, S.dimEntropyBarAt ν i y = 0 ↔
              condMeas ν (S.xiBar i) y = Measure.dirac y :=
  ⟨fun P μ _ herg hlt i hi => feng_entropy_zero_of_full.1 P μ herg.toMeasurePreserving herg
    hlt (P.measure_SigmaPrime_compl_of_ergodic μ herg hlt) i hi, feng_entropy_zero_of_full.2⟩

end BoxLike
