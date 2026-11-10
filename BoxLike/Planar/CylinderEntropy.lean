module

/-
`thm:feng_entropy_kolmogorov_sinai` (Lemma 3.6) for a planar self-affine system: the pointwise
entropy `h_0(μ, 𝐢)` is the almost sure limit of `-n⁻¹ log μ(𝒫_0^{n-1}(𝐢))`, with the
unconditional masses of the cylinders. The partition `ξ_0` of `Σ'` is the partition of `Σ'` by
the past, since `V_𝐢^0 = ℝ²` (`PlanarSystem.xi_zero_eq`), so the Shannon–McMillan–Breiman theorem
of `BoxLike/ShannonMcMillanBreiman.lean` for a Borel set of full measure applies, as in Feng,
Lemma 4.6, (4.17), which the article cites. The one input beyond it is `μ(Σ') = 1`. For a
box-like system it is proved (`System.measure_toPlanar_SigmaPrime_compl`); it follows from any
choice of `Σ'` in the sense of `MatrixTuple.OseledetsSet`; for an arbitrary planar system and an
ergodic `μ` with `λ_2 < λ_1` it is Oseledets' theorem, which the library proves
(`PlanarSystem.measure_SigmaPrime_compl_of_ergodic`). The endpoint at the general scope,
`PlanarSystem.feng_entropy_kolmogorov_sinai_general`, is in `BoxLike/Planar/OseledetsTheorem.lean`.

* `PlanarSystem.xi_zero_eq`: `ξ_0` is the partition of `Σ'` by the past.
* `PlanarSystem.tendsto_neg_log_cylinder_dimEntropyAt`: the limit for every invariant measure
  with `μ(Σ') = 1`.
* `PlanarSystem.feng_entropy_kolmogorov_sinai_of_oseledetsSet`: `thm:feng_entropy_kolmogorov_sinai`
  for a planar system, given a choice of `Σ'`.
* `PlanarSystem.dimEntropy_zero_eq_ksEntropy`: `h_0(μ) = h(μ)` with the Kolmogorov–Sinai entropy
  of tex lines 1877 to 1884, when `μ(Σ') = 1`.
* `System.feng_entropy_kolmogorov_sinai_toPlanar`: `thm:feng_entropy_kolmogorov_sinai` for a
  box-like system through the planar objects, with no hypothesis beyond the article's.
-/
public import BoxLike.Planar.OseledetsChoice
public import BoxLike.CylinderEntropy

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set

universe u

namespace PlanarSystem

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (P : PlanarSystem ι)

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- `ξ_0` is the partition of `Σ'` by the past (`sec:entropies`, tex lines 1779 to 1784), since
`V_𝐢^0 = ℝ²`. -/
theorem xi_zero_eq (μ : Measure (ℤ → ι)) :
    P.xi μ 0 = atomsOn (P.SigmaPrime μ) fun x => {y | SamePast y x} := by
  unfold xi
  congr 1
  funext x
  ext y
  simp [oseledets]

/-- The form of Feng's (4.17) (Duke Math. J. 172 (2023), Lemma 4.6) for a planar self-affine
system: for every invariant probability measure with `λ_2(𝖠, μ) < λ_1(𝖠, μ)` and `μ(Σ') = 1`,
`-n⁻¹ log μ(𝒫_0^{n-1}(𝐢)) → h_0(μ, 𝐢)` for `μ`-almost every `𝐢`. Ergodicity is not used. The
proof is the Shannon–McMillan–Breiman theorem `tendsto_neg_log_cylinder_localEntropy`. -/
theorem tendsto_neg_log_cylinder_dimEntropyAt (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    (hfull : μ (P.SigmaPrime μ)ᶜ = 0) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => -Real.log (μ.real (cylinder (block n x))) / n) atTop
      (𝓝 (P.dimEntropyAt μ 0 x)) := by
  rw [dimEntropyAt, xi_zero_eq]
  exact tendsto_neg_log_cylinder_localEntropy hinv (P.measurableSet_SigmaPrime μ hlt) hfull

/-- `thm:feng_entropy_kolmogorov_sinai` for a planar self-affine set, given a choice of `Σ'` and of
the Oseledets filtration (`MatrixTuple.OseledetsSet`): if `μ` is ergodic with
`λ_2(𝖠, μ) < λ_1(𝖠, μ)`, then `h_0(μ, 𝐢) = -lim_n n⁻¹ log μ(𝒫_0^{n-1}(𝐢))` for `μ`-almost every
`𝐢 ∈ Σ'`. The choice gives `μ(Σ') = 1` (`MatrixTuple.OseledetsSet.measure_regularSet_compl`). -/
theorem feng_entropy_kolmogorov_sinai_of_oseledetsSet (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (O : MatrixTuple.OseledetsSet P.mat μ)
    (herg : Ergodic (shift 1) μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    ∀ᵐ x ∂μ, x ∈ P.SigmaPrime μ →
      Tendsto (fun n : ℕ => -Real.log (μ.real (cylinder (block n x))) / n) atTop
        (𝓝 (P.dimEntropyAt μ 0 x)) :=
  (P.tendsto_neg_log_cylinder_dimEntropyAt μ herg.toMeasurePreserving hlt
    (O.measure_regularSet_compl P.det_ne_zero hlt)).mono fun _ hx _ => hx

/-- `sec:entropies`, tex lines 1901 to 1901: `h_0(μ) = h(μ)` with the Kolmogorov–Sinai entropy
`h(μ)` of tex lines 1877 to 1884 (the supremum over finite Borel partitions), for every invariant
probability measure with `λ_2(𝖠, μ) < λ_1(𝖠, μ)` and `μ(Σ') = 1`, for a planar self-affine
system. -/
theorem dimEntropy_zero_eq_ksEntropy (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    (hfull : μ (P.SigmaPrime μ)ᶜ = 0) : P.dimEntropy μ 0 = ksEntropy μ (shift 1) := by
  rw [ksEntropy_shift_eq_entropy hinv]
  exact P.dimEntropy_zero_eq_entropy' μ hinv hlt hfull

end PlanarSystem

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι)

/-- `thm:feng_entropy_kolmogorov_sinai` for a box-like self-affine set through the planar objects
of `S.toPlanar`: if `μ` is ergodic with `λ_2(𝖠, μ) < λ_1(𝖠, μ)`, then
`h_0(μ, 𝐢) = -lim_n n⁻¹ log μ(𝒫_0^{n-1}(𝐢))` for `μ`-almost every `𝐢 ∈ Σ'`. The set `Σ'` of the
planar system has full measure by `measure_toPlanar_SigmaPrime_compl`, and its `ξ_0` and
`h_0(μ, ·)` are those of `S` (`toPlanar_SigmaPrime`, `toPlanar_dimEntropyAt`). -/
theorem feng_entropy_kolmogorov_sinai_toPlanar (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) :
    ∀ᵐ x ∂μ, x ∈ S.SigmaPrime μ →
      Tendsto (fun n : ℕ => -Real.log (μ.real (cylinder (block n x))) / n) atTop
        (𝓝 (S.dimEntropyAt μ 0 x)) := by
  have h := S.toPlanar.tendsto_neg_log_cylinder_dimEntropyAt μ herg.toMeasurePreserving hlt
    (S.measure_toPlanar_SigmaPrime_compl μ herg.toMeasurePreserving herg hlt)
  rw [S.toPlanar_dimEntropyAt μ hlt] at h
  exact h.mono fun _ hx _ => hx

end System

end BoxLike
