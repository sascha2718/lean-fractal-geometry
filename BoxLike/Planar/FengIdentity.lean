module

/-
Feng's information-sum identity, D.-J. Feng, *Dimension of invariant measures for affine iterated
function systems*, Duke Math. J. 172 (2023), arXiv:1901.01691v2, Lemma 4.6, first identity of
(4.16), proved for the partitions `ξ_i` of a planar self-affine system (`sec:entropies`, tex
lines 1854 to 1871), and with it the planar parts of `thm:feng_entropy_as_limit` and
`thm:feng_entropy_zero` at the article's scope, for every measure giving full mass to `Σ'`.

The identity is the general `infoSum_of_pullShift` of `BoxLike/FengIdentity.lean`, applied with
`D = Σ'`, the set of regular points of `BoxLike/Planar/Oseledets.lean`. The invariance property
`σ^{-1}(ξ_i(σ 𝐢)) = ξ_i(𝐢) ∩ [i_0]` holds at every point of `Σ'`: `Σ'` is shift-invariant, the past
of `σ 𝐣` is the past of `𝐣` followed by `j_0`, `π(𝐣) - π(𝐢) = A_{i_0}(π(σ 𝐣) - π(σ 𝐢))` for
`j_0 = i_0`, and `A_{i_0} V_{σ 𝐢}^i = V_𝐢^i` by the growth characterisation of the filtration
(`MatrixTuple.mem_slowLine_shift_iff`, which is (V1)). The one hypothesis beyond invariance and
`λ_2 < λ_1` is `μ(Σ') = 1`. For an ergodic `μ` it is Oseledets' theorem, proved for box-like
tuples (`System.measure_toPlanar_SigmaPrime_compl`) and for arbitrary invertible tuples
(`PlanarSystem.measure_SigmaPrime_compl_of_ergodic` in `BoxLike/Planar/OseledetsTheorem.lean`,
which combines it with this module in `BoxLike/Planar/FengGeneral.lean`). It cannot be dropped:
if `μ(Σ') = 0` the partitions are
trivial modulo `μ` and the identity says `μ(𝒫_0^{n-1}(𝐢)) = ∏_{k<n} μ([i_k])`, which fails for
every invariant measure that is not Bernoulli.

* `PlanarSystem.mulVec_mem_oseledets_iff`: `A_{i_0} V_{σ 𝐢}^i = V_𝐢^i`.
* `PlanarSystem.pullShift_xi`, `PlanarSystem.xi_subset_SigmaPrime`,
  `PlanarSystem.pullShift_xi_subset_of_notMem`: the invariance property of `ξ_i`.
* `PlanarSystem.infoSum_xi`: the identity `PlanarSystem.InfoSum` for every invariant `μ` with
  `λ_2 < λ_1` and `μ(Σ') = 1`, and every `i`.
* `PlanarSystem.feng_entropy_as_limit_of_full`, `PlanarSystem.feng_entropy_zero_of_full`: the
  planar parts of `thm:feng_entropy_as_limit` and `thm:feng_entropy_zero`, given `μ(Σ') = 1`.
* `feng_entropy_as_limit_of_full`, `feng_entropy_zero_of_full`: both parts of the two lemmas,
  the planar part for every planar system and every ergodic `μ` with `λ_2 < λ_1` and `μ(Σ') = 1`,
  the scalar part for every proximal box-like system with rotations, with no premise.
* `feng_entropy_as_limit_boxLike_holds`, `feng_entropy_zero_boxLike_holds`: both parts of the two
  lemmas for box-like systems, with no premise.
-/
public import BoxLike.FengIdentityBar
public import BoxLike.Planar.FengEntropy

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set Matrix

universe u

namespace PlanarSystem

section Invariance

variable {ι : Type u} [MeasurableSpace ι] (P : PlanarSystem ι)

/-- The invariance of the filtration of `sec:lyapunov_exponents` under the shift:
`w ∈ V_{σ 𝐢}^i` exactly when `A_{i_0} w ∈ V_𝐢^i`, for every `𝐢` and every `i`. For `i = 1` this is
(V1) at `σ 𝐢` in the forward form `MatrixTuple.mem_slowLine_shift_iff`; for `i ≥ 2` it is the
invertibility of `A_{i_0}`. -/
theorem mulVec_mem_oseledets_iff (μ : Measure (ℤ → ι)) (x : ℤ → ι) (i : ℕ) (w : Fin 2 → ℝ) :
    w ∈ P.oseledets μ (shift 1 x) i ↔ P.mat (x 0) *ᵥ w ∈ P.oseledets μ x i := by
  rcases i with _ | _ | i
  · simp [oseledets]
  · simp only [oseledets]
    exact MatrixTuple.mem_slowLine_shift_iff P.det_ne_zero _ x w
  · simp only [oseledets, MatrixTuple.filtration_add_two, mem_singleton_iff]
    constructor
    · rintro rfl
      exact mulVec_zero _
    · intro h
      by_contra hw
      exact mulVec_ne_zero_of_det_ne_zero (P.det_ne_zero (x 0)) hw h

/-- The invariance property of the planar partitions `ξ_i`, Feng, Lemma 4.4(1), with `n = 1`, for
the article's `Σ'`: `σ^{-1}(ξ_i(σ 𝐢)) = ξ_i(𝐢) ∩ [i_0]` for every `𝐢 ∈ Σ'` and every `i`. -/
theorem pullShift_xi [Finite ι] (μ : Measure (ℤ → ι)) (i : ℕ) {x : ℤ → ι}
    (hx : x ∈ P.SigmaPrime μ) : pullShift (P.xi μ i) x = refineZero (P.xi μ i) x := by
  have hσx : shift 1 x ∈ P.SigmaPrime μ := (P.shift_mem_SigmaPrime_iff μ x).2 hx
  ext y
  simp only [pullShift, refineZero, xi, mem_preimage, atomsOn_of_mem hσx, atomsOn_of_mem hx,
    mem_inter_iff, mem_ofPred_eq, samePast_shift_one_iff, P.shift_mem_SigmaPrime_iff]
  constructor
  · rintro ⟨⟨⟨hp, h0⟩, hv⟩, hy⟩
    refine ⟨⟨⟨hp, ?_⟩, hy⟩, h0⟩
    rw [P.proj_sub_proj h0]
    exact (P.mulVec_mem_oseledets_iff μ x i _).1 hv
  · rintro ⟨⟨⟨hp, hv⟩, hy⟩, h0⟩
    refine ⟨⟨⟨hp, h0⟩, ?_⟩, hy⟩
    rw [P.proj_sub_proj h0] at hv
    exact (P.mulVec_mem_oseledets_iff μ x i _).2 hv

/-- The atoms of `ξ_i` at points of `Σ'` lie in `Σ'`. -/
theorem xi_subset_SigmaPrime (μ : Measure (ℤ → ι)) (i : ℕ) {x : ℤ → ι}
    (hx : x ∈ P.SigmaPrime μ) : P.xi μ i x ⊆ P.SigmaPrime μ := by
  rw [xi, atomsOn_of_mem hx]
  exact inter_subset_right

/-- Outside `Σ'` the atoms of `σ^{-1}ξ_i` avoid `Σ'`: they are `σ^{-1}(Σ ∖ Σ') = Σ ∖ Σ'`. -/
theorem pullShift_xi_subset_of_notMem (μ : Measure (ℤ → ι)) (i : ℕ) {x : ℤ → ι}
    (hx : x ∉ P.SigmaPrime μ) : pullShift (P.xi μ i) x ⊆ (P.SigmaPrime μ)ᶜ := by
  have hσx : shift 1 x ∉ P.SigmaPrime μ := fun h => hx ((P.shift_mem_SigmaPrime_iff μ x).1 h)
  intro y hy
  simp only [pullShift, xi, mem_preimage, atomsOn_of_notMem hσx, mem_compl_iff] at hy ⊢
  exact fun h => hy ((P.shift_mem_SigmaPrime_iff μ y).2 h)

end Invariance

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (P : PlanarSystem ι)

/-- Feng, Lemma 4.6, first identity of (4.16), for the partitions `ξ_i` of a planar self-affine
system, proved: for every invariant probability measure `μ` with `λ_2(𝖠, μ) < λ_1(𝖠, μ)` and
`μ(Σ') = 1`, and every `i`, `-log μ_𝐢^{ξ_i}(𝒫_0^{n-1}(𝐢)) = ∑_{k<n} I_μ(𝒫 | \widehat{ξ}_i)(σ^k 𝐢)`
for all `n`, for `μ`-almost every `𝐢`. Ergodicity is not needed. This is the identity behind
`thm:feng_entropy_as_limit` and the one cited in the proof of `thm:feng_entropy_zero` (tex lines
2014 to 2019), at the article's planar scope. -/
theorem infoSum_xi (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    (hfull : μ (P.SigmaPrime μ)ᶜ = 0) (i : ℕ) : P.InfoSum μ i :=
  infoSum_of_pullShift hinv (P.isMeasurablePartition_xi μ hlt i)
    (P.measurableSet_SigmaPrime μ hlt) hfull (fun _ hx => P.pullShift_xi μ i hx)
    (fun _ hx => P.xi_subset_SigmaPrime μ i hx) (fun _ hx => P.pullShift_xi_subset_of_notMem μ i hx)

/-- `thm:feng_entropy_as_limit`, planar part, for a planar self-affine set: for every invariant
`μ` with `λ_2(𝖠, μ) < λ_1(𝖠, μ)` and `μ(Σ') = 1`, and every `i`,
`h_i(μ, 𝐢) = -lim_n n⁻¹ log μ_𝐢^{ξ_i}(𝒫_0^{n-1}(𝐢))` for `μ`-almost every `𝐢`; Feng's identity
`infoSum_xi` and Birkhoff's theorem. -/
theorem feng_entropy_as_limit_of_full (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    (hfull : μ (P.SigmaPrime μ)ᶜ = 0) (i : ℕ) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => -Real.log ((condMeas μ (P.xi μ i) x).real (cylinder (block n x))) / n)
      atTop (𝓝 (P.dimEntropyAt μ i x)) :=
  P.feng_entropy_as_limit_of_infoSum μ hinv (P.infoSum_xi μ hinv hlt hfull i)

/-- `thm:feng_entropy_zero`, planar part, for a planar self-affine set: for every ergodic `μ`
with `λ_2(𝖠, μ) < λ_1(𝖠, μ)` and `μ(Σ') = 1`, and every `i`,
`h_i(μ, 𝐢) = 0 ↔ μ_𝐢^{ξ_i} = δ_𝐢` for `μ`-almost every `𝐢`, by the article's proof
(`PlanarSystem.feng_entropy_zero_of_infoSum`) with Feng's identity `infoSum_xi`. -/
theorem feng_entropy_zero_of_full (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) (hfull : μ (P.SigmaPrime μ)ᶜ = 0) (i : ℕ) :
    ∀ᵐ x ∂μ, P.dimEntropyAt μ i x = 0 ↔ condMeas μ (P.xi μ i) x = Measure.dirac x :=
  P.feng_entropy_zero_of_infoSum μ hinv herg hlt (P.infoSum_xi μ hinv hlt hfull i)

end PlanarSystem

/-- `thm:feng_entropy_as_limit`, both parts, with no literature premise. Planar part: for every
planar self-affine set, every ergodic `μ` with `λ_2 < λ_1` and `μ(Σ') = 1`, and each
`i ∈ {0, 1, 2}`, `h_i(μ, 𝐢) = -lim_n n⁻¹ log μ_𝐢^{ξ_i}(𝒫_0^{n-1}(𝐢))` for `μ`-almost every `𝐢`.
Scalar part: for every proximal box-like self-affine set with rotations, every invariant `ν` on
`Σ_Z`, ergodic or not, and each `i ∈ {0, 1}`,
`\overline{h}_i(ν, 𝐢) = -lim_n n⁻¹ log ν_𝐢^{\overline{ξ}_i}(\overline{𝒫}_0^{n-1}(𝐢))` for
`ν`-almost every `𝐢`. The hypothesis `μ(Σ') = 1` is Oseledets' theorem; for box-like systems it
is `System.measure_toPlanar_SigmaPrime_compl`. -/
theorem feng_entropy_as_limit_of_full :
    (∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (P : PlanarSystem ι) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ],
      MeasurePreserving (shift 1) μ μ → Ergodic (shift 1) μ → P.lyapunov₂ μ < P.lyapunov₁ μ →
      μ (P.SigmaPrime μ)ᶜ = 0 → ∀ i : ℕ, i ≤ 2 → ∀ᵐ x ∂μ, Tendsto
        (fun n : ℕ => -Real.log ((condMeas μ (P.xi μ i) x).real (cylinder (block n x))) / n)
        atTop (𝓝 (P.dimEntropyAt μ i x))) ∧
    (∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (S : System ι), S.WithRotations → S.Proximal →
      ∀ (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν],
      MeasurePreserving (shift 1) ν ν → ν (subshift S.o)ᶜ = 0 →
      ∀ i : ℕ, i ≤ 1 → ∀ᵐ y ∂ν, Tendsto
        (fun n : ℕ => -Real.log ((condMeas ν (S.xiBar i) y).real (cylinder (block n y))) / n)
        atTop (𝓝 (S.dimEntropyBarAt ν i y))) :=
  ⟨fun P μ _ hinv _ hlt hfull i _ => P.feng_entropy_as_limit_of_full μ hinv hlt hfull i,
    fun S hrot hprox ν _ hinv hsupp i _ =>
      S.feng_entropy_as_limit_bar fengInfoSumBar_holds hrot hprox ν hinv hsupp i⟩

/-- `thm:feng_entropy_zero`, both parts, with no literature premise. Planar part: for every
planar self-affine set, every ergodic `μ` with `λ_2 < λ_1` and `μ(Σ') = 1`, and each
`i ∈ {0, 1, 2}`, `h_i(μ, 𝐢) = 0 ↔ μ_𝐢^{ξ_i} = δ_𝐢` for `μ`-almost every `𝐢`. Scalar part: for
every proximal box-like self-affine set with rotations, every invariant `ν` on `Σ_Z`, ergodic or
not, and each `i ∈ {0, 1}`, `\overline{h}_i(ν, 𝐢) = 0 ↔ ν_𝐢^{\overline{ξ}_i} = δ_𝐢` for
`ν`-almost every `𝐢`. The hypothesis `μ(Σ') = 1` is Oseledets' theorem; for box-like systems it
is `System.measure_toPlanar_SigmaPrime_compl`. -/
theorem feng_entropy_zero_of_full :
    (∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (P : PlanarSystem ι) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ],
      MeasurePreserving (shift 1) μ μ → Ergodic (shift 1) μ → P.lyapunov₂ μ < P.lyapunov₁ μ →
      μ (P.SigmaPrime μ)ᶜ = 0 → ∀ i : ℕ, i ≤ 2 → ∀ᵐ x ∂μ,
        P.dimEntropyAt μ i x = 0 ↔ condMeas μ (P.xi μ i) x = Measure.dirac x) ∧
    (∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (S : System ι), S.WithRotations → S.Proximal →
      ∀ (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν],
      MeasurePreserving (shift 1) ν ν → ν (subshift S.o)ᶜ = 0 →
      ∀ i : ℕ, i ≤ 1 → ∀ᵐ y ∂ν,
        S.dimEntropyBarAt ν i y = 0 ↔ condMeas ν (S.xiBar i) y = Measure.dirac y) :=
  ⟨fun P μ _ hinv herg hlt hfull i _ => P.feng_entropy_zero_of_full μ hinv herg hlt hfull i,
    fun S hrot hprox ν _ hinv hsupp i _ =>
      S.feng_entropy_zero_bar fengInfoSumBar_holds hrot hprox ν hinv hsupp i⟩

/-- `thm:feng_entropy_as_limit`, both parts, for box-like systems, with no premise: the statement
`feng_entropy_as_limit_boxLike` with Feng's identities proved (`fengInfoSum_holds`,
`fengInfoSumBar_holds`). -/
theorem feng_entropy_as_limit_boxLike_holds :
    (∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (S : System ι) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ],
      MeasurePreserving (shift 1) μ μ → Ergodic (shift 1) μ → S.lyapunov₂ μ < S.lyapunov₁ μ →
      ∀ i : ℕ, i ≤ 2 → ∀ᵐ x ∂μ, Tendsto
        (fun n : ℕ => -Real.log ((condMeas μ (S.xi μ i) x).real (cylinder (block n x))) / n)
        atTop (𝓝 (S.dimEntropyAt μ i x))) ∧
    (∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (S : System ι), S.WithRotations → S.Proximal →
      ∀ (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν],
      MeasurePreserving (shift 1) ν ν → ν (subshift S.o)ᶜ = 0 →
      ∀ i : ℕ, i ≤ 1 → ∀ᵐ y ∂ν, Tendsto
        (fun n : ℕ => -Real.log ((condMeas ν (S.xiBar i) y).real (cylinder (block n y))) / n)
        atTop (𝓝 (S.dimEntropyBarAt ν i y))) :=
  feng_entropy_as_limit_boxLike fengInfoSum_holds fengInfoSumBar_holds

/-- `thm:feng_entropy_zero`, both parts, for box-like systems, with no premise: the statement
`feng_entropy_zero_boxLike` with Feng's identities proved (`fengInfoSum_holds`,
`fengInfoSumBar_holds`). -/
theorem feng_entropy_zero_boxLike_holds :
    (∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (S : System ι) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ],
      MeasurePreserving (shift 1) μ μ → Ergodic (shift 1) μ → S.lyapunov₂ μ < S.lyapunov₁ μ →
      ∀ i : ℕ, i ≤ 2 → ∀ᵐ x ∂μ,
        S.dimEntropyAt μ i x = 0 ↔ condMeas μ (S.xi μ i) x = Measure.dirac x) ∧
    (∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (S : System ι), S.WithRotations → S.Proximal →
      ∀ (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν],
      MeasurePreserving (shift 1) ν ν → ν (subshift S.o)ᶜ = 0 →
      ∀ i : ℕ, i ≤ 1 → ∀ᵐ y ∂ν,
        S.dimEntropyBarAt ν i y = 0 ↔ condMeas ν (S.xiBar i) y = Measure.dirac y) :=
  feng_entropy_zero_boxLike fengInfoSum_holds fengInfoSumBar_holds

end BoxLike
