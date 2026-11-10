module

/-
`thm:feng_entropy_kolmogorov_sinai` (Lemma 3.6 of `sec:entropies`): the pointwise entropy
`h_0(μ, 𝐢)` is the almost sure limit of `-n⁻¹ log μ(𝒫_0^{n-1}(𝐢))`, with the unconditional
masses of the cylinders. The article cites Feng, Lemma 4.6, whose assertion (4.17) is this limit,
derived there from the Shannon–McMillan–Breiman theorem. The proof here is the same:
`BoxLike/ShannonMcMillanBreiman.lean` proves that for every invariant probability measure `μ`
and every Borel set `D` of full measure,
`-n⁻¹ log μ([x_0 ⋯ x_{n-1}]) → E_μ(I_μ(𝒫 | \widehat{ξ}) | ℐ)(x)` almost everywhere, where `ξ` is
the partition of `D` by the past. The partition `ξ_0` of `Σ'` is of this form, since
`V_𝐢^0 = ℝ²`, and `Σ'` has full measure for ergodic `μ` (`System.measure_SigmaPrime_compl`).
The scalar partition `\overline{ξ}_0` of `Σ_Z` is of the same form with `D = Σ_Z`.

* `tendsto_neg_log_cylinder_localEntropy_of_atoms`: the statement for every partition whose
  atoms inside a Borel set of full measure are the classes of the past, the form that transfers
  to other representations of `Σ'` and `ξ_0`.
* `System.xi_zero_eq`: `ξ_0` is the partition of `Σ'` by the past.
* `System.tendsto_neg_log_cylinder_dimEntropyAt`: the form of Feng's (4.17) for every invariant
  measure with `μ(Σ') = 1`, without ergodicity or `λ_2 < λ_1`.
* `System.feng_entropy_kolmogorov_sinai'`, `System.feng_entropy_kolmogorov_sinai`:
  `thm:feng_entropy_kolmogorov_sinai`, on all of `Σ` and in the form of the article, for almost
  every `𝐢 ∈ Σ'`.
* `System.dimEntropy_zero_eq_entropy_of_feng_entropy_kolmogorov_sinai`,
  `System.dimEntropy_zero_eq_ksEntropy_of_feng_entropy_kolmogorov_sinai`: "the lemma identifies
  `h_0(μ)` with the Kolmogorov–Sinai entropy `h(μ)`" (tex line 1901), through the lemma and
  the Shannon–McMillan–Breiman theorem, for the entropy rate and for the supremum over finite
  Borel partitions.
* `System.dimEntropy_zero_eq_ksEntropy`, `System.dimEntropyBar_zero_eq_ksEntropy`:
  `h_0(μ) = h(μ)` and `\overline{h}_0(ν) = h(ν)` for every invariant measure (tex lines 1901 to
  1991), with the Kolmogorov–Sinai entropy of tex lines 1877 to 1884.
* `System.feng_entropy_kolmogorov_sinai_bar`: the form of Feng's (4.17) for the projective
  system, for every invariant measure on `Σ_Z`:
  `\overline{h}_0(ν, 𝐢) = -lim n⁻¹ log ν(\overline{𝒫}_0^{n-1}(𝐢))`.
* `System.feng_entropy_kolmogorov_sinai_bar_ergodic`: its ergodic form, with the limit `h(ν)`.
-/
public import BoxLike.KolmogorovSinai
public import BoxLike.PastEntropy
public import BoxLike.ShannonMcMillanBreiman

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set

universe u

/-- `thm:feng_entropy_kolmogorov_sinai` for an arbitrary partition by the past, in the form that
transfers to every representation of `Σ'` and `ξ_0`: if a Borel set `D` has full measure for an
invariant probability measure `μ` on `ℤ → α`, `α` finite, and the atoms of `ξ` are the classes of
the past `𝐢^-` inside `D`, with the single further atom `Ω ∖ D`, then
`-n⁻¹ log μ([x_0 ⋯ x_{n-1}]) → E_μ(I_μ(𝒫 | \widehat{ξ}) | ℐ)(x)` for `μ`-almost every `x`. -/
theorem tendsto_neg_log_cylinder_localEntropy_of_atoms {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {μ : Measure (ℤ → α)}
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ) {D : Set (ℤ → α)}
    (hD : MeasurableSet D) (hfull : μ Dᶜ = 0) {ξ : (ℤ → α) → Set (ℤ → α)}
    (hξD : ∀ x ∈ D, ξ x = {y | SamePast y x} ∩ D) (hξc : ∀ x ∉ D, ξ x = Dᶜ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => -Real.log (μ.real (cylinder (block n x))) / n) atTop
      (𝓝 (localEntropy μ ξ x)) := by
  have e : ξ = atomsOn D fun x => {y | SamePast y x} := by
    funext x
    by_cases hx : x ∈ D
    · rw [atomsOn_of_mem hx, hξD x hx]
    · rw [atomsOn_of_notMem hx, hξc x hx]
  rw [e]
  exact tendsto_neg_log_cylinder_localEntropy hinv hD hfull

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι)

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- The partition `ξ_0` of `sec:entropies` (tex lines 1779 to 1783) is the partition of `Σ'` by
the past `𝐢^-`, extended by the atom `Σ ∖ Σ'`: the condition `π(𝐣) - π(𝐢) ∈ V_𝐢^0 = ℝ²` is
void. -/
theorem xi_zero_eq (μ : Measure (ℤ → ι)) :
    S.xi μ 0 = atomsOn (S.SigmaPrime μ) fun x => {y | SamePast y x} := by
  unfold xi
  congr 1
  funext x
  ext y
  simp [oseledets]

/-- The form of Feng's (4.17) (Feng, Duke Math. J. 172 (2023), Lemma 4.6) for the box-like
system, behind `thm:feng_entropy_kolmogorov_sinai`: for every invariant probability
measure with `μ(Σ') = 1`, `-n⁻¹ log μ(𝒫_0^{n-1}(𝐢)) → h_0(μ, 𝐢)` for `μ`-almost every `𝐢`.
Neither ergodicity nor `λ_2 < λ_1` is used. -/
theorem tendsto_neg_log_cylinder_dimEntropyAt (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (hfull : μ (S.SigmaPrime μ)ᶜ = 0) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => -Real.log (μ.real (cylinder (block n x))) / n) atTop
      (𝓝 (S.dimEntropyAt μ 0 x)) := by
  rw [dimEntropyAt, xi_zero_eq]
  exact tendsto_neg_log_cylinder_localEntropy hinv (S.measurableSet_SigmaPrime μ) hfull

/-- `thm:feng_entropy_kolmogorov_sinai` for the box-like system, on all of `Σ`: if `μ` is ergodic
with `λ_2(𝖠, μ) < λ_1(𝖠, μ)`, then `h_0(μ, 𝐢) = -lim_n n⁻¹ log μ(𝒫_0^{n-1}(𝐢))` for `μ`-almost
every `𝐢`; the limit exists. The proof uses ergodicity for `μ(Σ') = 1`; the hypothesis
`λ_2 < λ_1` of the article, under which `Σ'` and the partitions are defined there, is not used
by the proof. -/
theorem feng_entropy_kolmogorov_sinai' (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (_hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => -Real.log (μ.real (cylinder (block n x))) / n) atTop
      (𝓝 (S.dimEntropyAt μ 0 x)) :=
  S.tendsto_neg_log_cylinder_dimEntropyAt μ herg.toMeasurePreserving
    (S.measure_SigmaPrime_compl μ herg.toMeasurePreserving herg)

/-- `thm:feng_entropy_kolmogorov_sinai`, in the form of the article: if `X` is a box-like
self-affine set and `μ` is an ergodic shift-invariant probability measure with
`λ_2(𝖠, μ) < λ_1(𝖠, μ)`, then `h_0(μ, 𝐢) = -lim_{n → ∞} n⁻¹ log μ(𝒫_0^{n-1}(𝐢))` for
`μ`-almost every `𝐢 ∈ Σ'`, with the unconditional masses `μ(𝒫_0^{n-1}(𝐢)) = μ([i_0 ⋯ i_{n-1}])`
of the cylinders. -/
theorem feng_entropy_kolmogorov_sinai (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) :
    ∀ᵐ x ∂μ, x ∈ S.SigmaPrime μ →
      Tendsto (fun n : ℕ => -Real.log (μ.real (cylinder (block n x))) / n) atTop
        (𝓝 (S.dimEntropyAt μ 0 x)) :=
  (S.feng_entropy_kolmogorov_sinai' μ herg hlt).mono fun _ hx _ => hx

/-- "The lemma identifies `h_0(μ)` with the Kolmogorov–Sinai entropy `h(μ)`" (`sec:entropies`,
tex line 1901): by `thm:feng_entropy_kolmogorov_sinai`, `eq:ergodic_entropy_constant` and the
Shannon–McMillan–Breiman theorem, the almost sure limit of `-n⁻¹ log μ(𝒫_0^{n-1}(𝐢))` is both
`h_0(μ)` and `h(μ)`. The library also proves the identity directly, without the lemma, as
`System.dimEntropy_zero_eq_entropy`. -/
theorem dimEntropy_zero_eq_entropy_of_feng_entropy_kolmogorov_sinai (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (herg : Ergodic (shift 1) μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) : S.dimEntropy μ 0 = entropy μ := by
  obtain ⟨x, hx1, hx2, hx3⟩ := ((S.feng_entropy_kolmogorov_sinai' μ herg hlt).and
    ((localEntropy_ae_eq μ herg (S.xi μ 0)).and
      (tendsto_neg_log_cylinder_entropy herg))).exists
  have hx2' : S.dimEntropyAt μ 0 x = S.dimEntropy μ 0 := hx2
  rw [hx2'] at hx1
  exact tendsto_nhds_unique hx1 hx3

/-- "The lemma identifies `h_0(μ)` with the Kolmogorov–Sinai entropy `h(μ)`" (`sec:entropies`,
tex line 1901), with `h(μ)` the supremum over finite Borel partitions of tex lines 1877 to 1884:
by `thm:feng_entropy_kolmogorov_sinai`, `eq:ergodic_entropy_constant` and the
Shannon–McMillan–Breiman theorem. -/
theorem dimEntropy_zero_eq_ksEntropy_of_feng_entropy_kolmogorov_sinai (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (herg : Ergodic (shift 1) μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) : S.dimEntropy μ 0 = ksEntropy μ (shift 1) := by
  rw [ksEntropy_shift_eq_entropy herg.toMeasurePreserving]
  exact S.dimEntropy_zero_eq_entropy_of_feng_entropy_kolmogorov_sinai μ herg hlt

/-- `sec:entropies`, tex lines 1901 to 1901: `h_0(μ) = h(μ)` with the Kolmogorov–Sinai entropy
`h(μ)` of tex lines 1877 to 1884, for every invariant probability measure with `μ(Σ') = 1`. -/
theorem dimEntropy_zero_eq_ksEntropy (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (hfull : μ (S.SigmaPrime μ)ᶜ = 0) :
    S.dimEntropy μ 0 = ksEntropy μ (shift 1) := by
  rw [ksEntropy_shift_eq_entropy hinv]
  exact S.dimEntropy_zero_eq_entropy' μ hinv hfull

/-- `sec:entropies`, tex lines 1901 to 1901: `\overline{h}_0(ν) = h(ν)` with the
Kolmogorov–Sinai entropy of tex lines 1877 to 1884, for every invariant probability measure on
`{1, …, 2N}^ℤ` giving full measure to `Σ_Z`. -/
theorem dimEntropyBar_zero_eq_ksEntropy (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν]
    (hinv : MeasurePreserving (shift 1) ν ν) (hsupp : ν (subshift S.o)ᶜ = 0) :
    S.dimEntropyBar ν 0 = ksEntropy ν (shift 1) := by
  rw [ksEntropy_shift_eq_entropy hinv]
  exact S.dimEntropyBar_zero_eq_entropy' ν hinv hsupp

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The partition `\overline{ξ}_0` of `sec:entropies` (tex lines 1836 to 1841) is the partition
of `Σ_Z` by the past, extended by the atom `{1, …, 2N}^ℤ ∖ Σ_Z`. -/
theorem xiBar_zero_eq : S.xiBar 0 = atomsOn (subshift S.o) fun y => {z | SamePast z y} := rfl

/-- The form of Feng's (4.17) for the projective system `Ψ` (Feng, Lemma 4.6, for `Ψ`; the scalar
counterpart of `thm:feng_entropy_kolmogorov_sinai` used through `\overline{h}_0(ν) = h(ν)`, tex
lines 1989 to 1991): for every invariant probability measure `ν` on `{1, …, 2N}^ℤ` giving full
measure to `Σ_Z`, `-n⁻¹ log ν(\overline{𝒫}_0^{n-1}(𝐢)) → \overline{h}_0(ν, 𝐢)` for `ν`-almost
every `𝐢`. Neither ergodicity nor the hypotheses on the system are used. -/
theorem feng_entropy_kolmogorov_sinai_bar (ν : Measure (ℤ → ι × ZMod 2))
    [IsProbabilityMeasure ν] (hinv : MeasurePreserving (shift 1) ν ν)
    (hsupp : ν (subshift S.o)ᶜ = 0) :
    ∀ᵐ x ∂ν, Tendsto (fun n : ℕ => -Real.log (ν.real (cylinder (block n x))) / n) atTop
      (𝓝 (S.dimEntropyBarAt ν 0 x)) := by
  rw [dimEntropyBarAt, xiBar_zero_eq]
  exact tendsto_neg_log_cylinder_localEntropy hinv (measurableSet_subshift S.o) hsupp

/-- The ergodic form of `feng_entropy_kolmogorov_sinai_bar`: for an ergodic `ν` on `Σ_Z`,
`\overline{h}_0(ν, 𝐢) = -lim n⁻¹ log ν(\overline{𝒫}_0^{n-1}(𝐢)) = h(ν)` for `ν`-almost every
`𝐢`. -/
theorem feng_entropy_kolmogorov_sinai_bar_ergodic (ν : Measure (ℤ → ι × ZMod 2))
    [IsProbabilityMeasure ν] (herg : Ergodic (shift 1) ν) (hsupp : ν (subshift S.o)ᶜ = 0) :
    ∀ᵐ x ∂ν, S.dimEntropyBarAt ν 0 x = entropy ν ∧
      Tendsto (fun n : ℕ => -Real.log (ν.real (cylinder (block n x))) / n) atTop
        (𝓝 (S.dimEntropyBarAt ν 0 x)) := by
  filter_upwards [S.feng_entropy_kolmogorov_sinai_bar ν herg.toMeasurePreserving hsupp,
    tendsto_neg_log_cylinder_entropy herg] with x hx hx'
  exact ⟨tendsto_nhds_unique hx hx', hx⟩

end System

end BoxLike
