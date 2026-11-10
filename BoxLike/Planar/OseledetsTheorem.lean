module

/-
Oseledets' multiplicative ergodic theorem for invertible planar matrix cocycles, in the form that
`sec:lyapunov_exponents` cites (Oseledec 1968 and Froyland–Lloyd–Quas, Theorem 4.1, tex lines
1585 to 1607): for an invertible tuple `𝖠` and an ergodic `μ ∈ M_σ(Σ)` with
`λ_2(𝖠, μ) < λ_1(𝖠, μ)`, `μ`-almost every `𝐢` carries a line `V_𝐢^1` such that every non-zero
`v ∈ V_𝐢^1` has `n⁻¹ log |A_{i_{-n}} ⋯ A_{i_{-1}} v| → λ_2(𝖠, μ)` and every `v ∉ V_𝐢^1` has the
rate `λ_1(𝖠, μ)`. In the terms of `BoxLike/Planar/Oseledets.lean`, the set of regular points has
full measure; it is the set `Σ'` of the article, on which (V1) to (V3) and `eq:V_lyapunov`
hold. The proof combines the theorem of Furstenberg and Kesten
(`BoxLike/FurstenbergKesten.lean`, from Kingman's theorem) with the deterministic planar
argument of `BoxLike/Planar/OseledetsTheoremDirection.lean`. No literature premise is used.

The consequences at the general planar scope: a choice of `Σ'` and of the Oseledets filtration
(`MatrixTuple.OseledetsSet`) exists for every invertible planar tuple; for a planar self-affine
system `μ(Σ') = 1`, `thm:feng_entropy_kolmogorov_sinai` holds in the form of the article, and
`h_0(μ) = h(μ)` (tex lines 1901 to 1901).

* `MatrixTuple.ae_mem_regularSet`, `MatrixTuple.measure_regularSet_compl_of_ergodic`: Oseledets'
  theorem in the plane.
* `MatrixTuple.nonempty_oseledetsSet_of_ergodic`, `MatrixTuple.oseledetsSetOfErgodic`: a choice
  of `Σ'` and of the filtration.
* `PlanarSystem.measure_SigmaPrime_compl_of_ergodic`, `PlanarSystem.oseledetsSetOfErgodic`: the
  same for a planar self-affine system.
* `PlanarSystem.feng_entropy_kolmogorov_sinai_general`,
  `PlanarSystem.tendsto_neg_log_cylinder_dimEntropyAt_of_ergodic`:
  `thm:feng_entropy_kolmogorov_sinai` for a planar self-affine set.
* `PlanarSystem.dimEntropy_zero_eq_ksEntropy_of_ergodic`,
  `PlanarSystem.dimEntropy_zero_eq_entropy_of_ergodic`: `h_0(μ) = h(μ)`.
-/
public import BoxLike.FurstenbergKesten
public import BoxLike.Planar.OseledetsTheoremDirection
public import BoxLike.Planar.CylinderEntropy

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set Matrix
open scoped Matrix.Norms.L2Operator

universe u

namespace MatrixTuple

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {A : ι → Matrix (Fin 2) (Fin 2) ℝ} {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]

/-- **Oseledets' theorem for invertible planar cocycles**, in the form of
`sec:lyapunov_exponents` (Oseledec 1968, Froyland–Lloyd–Quas, Theorem 4.1, tex lines 1508 to
1607): for an invertible tuple and an ergodic `μ` with `λ_2(𝖠, μ) < λ_1(𝖠, μ)`, `μ`-almost every
`𝐢` is regular, that is, has a line `V_𝐢^1` with the properties (V2) and (V3). At such a point
the theorem of Furstenberg and Kesten gives the rates of `α_1` and `α_2` of
`A_{i_{-n}} ⋯ A_{i_{-1}}`, and the deterministic theorem `exists_slow_fast_of_tendsto` gives a
vector of rate `λ_2` and one of rate `λ_1`, which suffice by `isRegularWith_of`. -/
theorem ae_mem_regularSet (hA : ∀ i, (A i).det ≠ 0) (herg : Ergodic (shift 1) μ)
    (hlt : lyapunov₂ A μ < lyapunov₁ A μ) :
    ∀ᵐ x ∂μ, x ∈ regularSet A (lyapunov₁ A μ) (lyapunov₂ A μ) := by
  set K : ℝ := ∑ i, (‖A i‖ + ‖(A i)⁻¹‖) with hK_def
  have hKi : ∀ i, ‖A i‖ ≤ K ∧ ‖(A i)⁻¹‖ ≤ K := fun i => by
    have h := Finset.single_le_sum (f := fun j => ‖A j‖ + ‖(A j)⁻¹‖)
      (fun j _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ i)
    exact ⟨by linarith [norm_nonneg (A i)⁻¹], by linarith [norm_nonneg (A i)]⟩
  filter_upwards [tendsto_log_norm_pastProd hA herg, tendsto_log_alpha₂_pastProd hA herg]
    with x h₁ h₂
  obtain ⟨u, w, hu0, hw0, hu, hw⟩ := exists_slow_fast_of_tendsto
    (M := pastProd A x) (B := fun n => A (x (-((n : ℤ) + 1)))) (pastProd_succ x)
    (fun n => det_word_ne_zero hA _) (fun n => hA _) (fun n => (hKi _).1) (fun n => (hKi _).2)
    hlt h₁ h₂
  exact ⟨u, isRegularWith_of hA hlt hu0 hw0 hu hw⟩

/-- Oseledets' theorem for invertible planar cocycles in the form `μ(Σ') = 1`: the set of
regular points has full measure for an ergodic `μ` with `λ_2(𝖠, μ) < λ_1(𝖠, μ)`
(`sec:lyapunov_exponents`, tex lines 1508 to 1530). -/
theorem measure_regularSet_compl_of_ergodic (hA : ∀ i, (A i).det ≠ 0)
    (herg : Ergodic (shift 1) μ) (hlt : lyapunov₂ A μ < lyapunov₁ A μ) :
    μ (regularSet A (lyapunov₁ A μ) (lyapunov₂ A μ))ᶜ = 0 :=
  ae_iff.1 (ae_mem_regularSet hA herg hlt)

/-- A choice of `Σ'` and of the Oseledets filtration in the sense of `OseledetsSet`, the form in
which `sec:lyapunov_exponents` (tex lines 1508 to 1530) takes Oseledets' theorem, exists for every
invertible planar tuple and every ergodic `μ` with `λ_2(𝖠, μ) < λ_1(𝖠, μ)`. -/
theorem nonempty_oseledetsSet_of_ergodic (hA : ∀ i, (A i).det ≠ 0)
    (herg : Ergodic (shift 1) μ) (hlt : lyapunov₂ A μ < lyapunov₁ A μ) :
    Nonempty (OseledetsSet A μ) :=
  (nonempty_oseledetsSet_iff hA hlt).2 (measure_regularSet_compl_of_ergodic hA herg hlt)

variable (A μ) in
/-- The choice of `Σ'` and of the Oseledets filtration given by the regular points and the
filtration `regularV`, for an invertible planar tuple and an ergodic `μ` with
`λ_2(𝖠, μ) < λ_1(𝖠, μ)` (`sec:lyapunov_exponents`, tex lines 1508 to 1530). -/
noncomputable def oseledetsSetOfErgodic (hA : ∀ i, (A i).det ≠ 0)
    (herg : Ergodic (shift 1) μ) (hlt : lyapunov₂ A μ < lyapunov₁ A μ) : OseledetsSet A μ :=
  regularOseledetsSet A μ hA hlt (measure_regularSet_compl_of_ergodic hA herg hlt)

end MatrixTuple

namespace PlanarSystem

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (P : PlanarSystem ι)

/-- `μ(Σ') = 1` for a planar self-affine system and an ergodic `μ` with
`λ_2(𝖠, μ) < λ_1(𝖠, μ)` (`sec:lyapunov_exponents`, tex lines 1508 to 1530), by Oseledets'
theorem `MatrixTuple.measure_regularSet_compl_of_ergodic`. -/
theorem measure_SigmaPrime_compl_of_ergodic (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    μ (P.SigmaPrime μ)ᶜ = 0 :=
  MatrixTuple.measure_regularSet_compl_of_ergodic P.det_ne_zero herg hlt

/-- The choice of `Σ'` and of the Oseledets filtration in the sense of
`MatrixTuple.OseledetsSet` for a planar self-affine system and an ergodic `μ` with
`λ_2(𝖠, μ) < λ_1(𝖠, μ)` (`sec:lyapunov_exponents`, tex lines 1508 to 1530). -/
noncomputable def oseledetsSetOfErgodic (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    MatrixTuple.OseledetsSet P.mat μ :=
  MatrixTuple.oseledetsSetOfErgodic P.mat μ P.det_ne_zero herg hlt

/-- `thm:feng_entropy_kolmogorov_sinai` for a planar self-affine set, in the form of the article:
if `μ ∈ M_σ(Σ)` is ergodic with `λ_2(𝖠, μ) < λ_1(𝖠, μ)`, then
`h_0(μ, 𝐢) = -lim_n n⁻¹ log μ(𝒫_0^{n-1}(𝐢))` for `μ`-almost every `𝐢 ∈ Σ'`, with the
unconditional masses of the cylinders. The choice of `Σ'` is `oseledetsSetOfErgodic`, from
Oseledets' theorem. -/
theorem feng_entropy_kolmogorov_sinai_general (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    ∀ᵐ x ∂μ, x ∈ P.SigmaPrime μ →
      Tendsto (fun n : ℕ => -Real.log (μ.real (cylinder (block n x))) / n) atTop
        (𝓝 (P.dimEntropyAt μ 0 x)) :=
  P.feng_entropy_kolmogorov_sinai_of_oseledetsSet μ (P.oseledetsSetOfErgodic μ herg hlt) herg
    hlt

/-- `thm:feng_entropy_kolmogorov_sinai` for a planar self-affine set on all of `Σ`: the limit
holds for `μ`-almost every `𝐢`, since `μ(Σ') = 1`. -/
theorem tendsto_neg_log_cylinder_dimEntropyAt_of_ergodic (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (herg : Ergodic (shift 1) μ)
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => -Real.log (μ.real (cylinder (block n x))) / n) atTop
      (𝓝 (P.dimEntropyAt μ 0 x)) :=
  P.tendsto_neg_log_cylinder_dimEntropyAt μ herg.toMeasurePreserving hlt
    (P.measure_SigmaPrime_compl_of_ergodic μ herg hlt)

/-- `h_0(μ) = h(μ)` with the Kolmogorov–Sinai entropy of tex lines 1877 to 1884, for a planar
self-affine system and an ergodic `μ` with `λ_2(𝖠, μ) < λ_1(𝖠, μ)` (`sec:entropies`, tex lines
1989 to 1991). -/
theorem dimEntropy_zero_eq_ksEntropy_of_ergodic (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    P.dimEntropy μ 0 = ksEntropy μ (shift 1) :=
  P.dimEntropy_zero_eq_ksEntropy μ herg.toMeasurePreserving hlt
    (P.measure_SigmaPrime_compl_of_ergodic μ herg hlt)

/-- `h_0(μ) = h(μ)` with the entropy rate of the time-zero partition, for a planar self-affine
system and an ergodic `μ` with `λ_2(𝖠, μ) < λ_1(𝖠, μ)` (`sec:entropies`, tex lines 1901 to
1991). -/
theorem dimEntropy_zero_eq_entropy_of_ergodic (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    P.dimEntropy μ 0 = entropy μ :=
  P.dimEntropy_zero_eq_entropy' μ herg.toMeasurePreserving hlt
    (P.measure_SigmaPrime_compl_of_ergodic μ herg hlt)

end PlanarSystem

end BoxLike
