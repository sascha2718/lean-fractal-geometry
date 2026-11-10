module

/-
`thm:feng_entropy_as_limit` and `thm:feng_entropy_zero` for a planar self-affine system, with the
partitions `ξ_i` of `BoxLike/Planar/Partitions.lean`. Both lemmas rest on the first identity of
Feng, Lemma 4.6, (4.16):
`-log μ_𝐢^{ξ_i}(𝒫_0^{n-1}(𝐢)) = ∑_{k<n} I_μ(𝒫 | \widehat{ξ}_i)(σ^k 𝐢)` for all `n`, on one set of
full measure. Here it is the hypothesis `PlanarSystem.InfoSum` about the given system and
measure. For box-like systems it follows from `FengInfoSum` through the specialisation
`System.toPlanar_xi` (`System.infoSum_toPlanar`); for every planar system with `μ(Σ') = 1` it is
proved in `BoxLike/Planar/FengIdentity.lean` (`PlanarSystem.infoSum_xi`), and `FengInfoSum`
itself is the theorem `fengInfoSum_holds`.

The proof of the planar part of `thm:feng_entropy_zero` follows the article (tex lines 1918 to
2028): with `f = I_μ(𝒫 | \widehat{ξ}_i)` and `H = E_μ(f | ℐ) = h_i(μ, ·)`, the set `E = {H = 0}`
is invariant and `∫_E f dμ = ∫_E H dμ = 0`, so `f(σ^k 𝐢) = 0` for every `k ≥ 0` and almost every
`𝐢 ∈ E`; the identity gives `μ_𝐢^{ξ_i}(𝒫_0^{n-1}(𝐢)) = 1` for every `n`; the conditional measure
is carried by an atom with fixed past, and intersecting the cylinders gives
`μ_𝐢^{ξ_i}({𝐢}) = 1`. Conversely a Dirac conditional measure gives the limit zero in
`thm:feng_entropy_as_limit`. The scalar part is the box-like statement
`System.feng_entropy_zero_bar`, without ergodicity.

* `PlanarSystem.InfoSum`: the first identity of Feng, Lemma 4.6, (4.16), for `P`, `μ`, `i`.
* `PlanarSystem.condMeas_xi_samePast`: the conditional measures of `ξ_i` that give mass one to
  all cylinders `[𝐢|_n]` are carried by the points with the past of `𝐢`.
* `PlanarSystem.feng_entropy_as_limit_of_infoSum`: `thm:feng_entropy_as_limit`, planar part.
* `PlanarSystem.feng_entropy_zero_of_infoSum`: `thm:feng_entropy_zero`, planar part.
* `System.infoSum_toPlanar`: `FengInfoSum` gives the identity for the planar system of a
  box-like system.
* `System.feng_entropy_as_limit_toPlanar`, `System.feng_entropy_zero_toPlanar`: the box-like
  lemmas as specialisations of the planar ones.
* `feng_entropy_as_limit_boxLike`, `feng_entropy_zero_boxLike`: both parts of
  `thm:feng_entropy_as_limit` and of `thm:feng_entropy_zero` for box-like systems, the planar
  part through the planar objects, from `FengInfoSum` and `FengInfoSumBar`. Both hold
  (`fengInfoSum_holds`, `fengInfoSumBar_holds`), and the unconditional forms are
  `feng_entropy_as_limit_boxLike_holds`, `feng_entropy_zero_boxLike_holds` of
  `BoxLike/Planar/FengIdentity.lean`.
-/
public import BoxLike.Planar.Specialisation
public import BoxLike.FengEntropy

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set

universe u

namespace PlanarSystem

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (P : PlanarSystem ι)

/-- The first identity of Feng, Lemma 4.6, (4.16), for the partition `ξ_i` of the planar system
`P` and the measure `μ`: `-log μ_𝐢^{ξ_i}(𝒫_0^{n-1}(𝐢)) = ∑_{k<n} I_μ(𝒫 | \widehat{ξ}_i)(σ^k 𝐢)`
for all `n`, on one set of full measure. The proof of `thm:feng_entropy_zero` (tex lines 1920 to
2019) uses it. -/
def InfoSum (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] (i : ℕ) : Prop :=
  ∀ᵐ x ∂μ, ∀ n : ℕ, -Real.log ((condMeas μ (P.xi μ i) x).real (cylinder (block n x))) =
    ∑ k ∈ Finset.range n, condInfo μ (P.xi μ i) (shift k x)

/-- "The conditional measure is supported on an atom with fixed past" (proof of
`thm:feng_entropy_zero`, tex lines 1926 to 1928) for a planar system: if `μ_𝐢^{ξ_i}` gives mass
one to every cylinder `[𝐢|_n]`, then it gives mass one to `{𝐣 : 𝐣^- = 𝐢^-}`, for `μ`-almost
every `𝐢`. The set `Σ'` is invariant and Borel, so `μ(Σ') ∈ {0, 1}` for ergodic `μ`. If
`μ(Σ') = 1`, the atoms `ξ_i(𝐢)` have fixed past and `condMeas_atom` applies. If `μ(Σ') = 0`,
the conditional measures are `μ`, and `μ` is the Dirac mass at a constant sequence as soon as it
gives mass one to all cylinders of one point. -/
theorem condMeas_xi_samePast (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) (i : ℕ) :
    ∀ᵐ x ∂μ, (∀ n : ℕ, condMeas μ (P.xi μ i) x (cylinder (block n x)) = 1) →
      condMeas μ (P.xi μ i) x {y | SamePast y x} = 1 := by
  rcases herg.toPreErgodic.measure_self_or_compl_eq_zero (P.measurableSet_SigmaPrime μ hlt)
    (P.preimage_shift_SigmaPrime μ) with h | h
  · have hc : ∀ᵐ x ∂μ, condMeas μ (P.xi μ i) x = μ :=
      condMeas_atomsOn_of_measure_eq_zero μ h _
    by_cases hex : ∃ x₀ : ℤ → ι, ∀ n : ℕ, μ (cylinder (block n x₀)) = 1
    · obtain ⟨x₀, hx₀⟩ := hex
      have h1 := measure_singleton_const_of_cylinder hinv hx₀
      have hae : ∀ᵐ x ∂μ, x ∈ ({fun _ => x₀ 0} : Set (ℤ → ι)) :=
        (measure_eq_zero_iff_ae_notMem.1
          ((prob_compl_eq_zero_iff (measurableSet_singleton _)).2 h1)).mono
          fun x hx => not_not.1 hx
      filter_upwards [hc, hae] with x hx hxc _
      rw [hx]
      refine le_antisymm prob_le_one (h1.symm.le.trans (measure_mono ?_))
      rw [mem_singleton_iff] at hxc
      rw [hxc]
      exact singleton_subset_iff.2 (SamePast.refl _)
    · filter_upwards [hc] with x hx hcyl
      exact absurd ⟨x, fun n => hx ▸ hcyl n⟩ hex
  · have hsub : ∀ᵐ x ∂μ, P.xi μ i x ⊆ {y | SamePast y x} := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h] with x hx
      exact P.xi_subset_samePast μ i (not_not.1 hx)
    exact (condMeas_eq_one_of_atom_subset μ (P.isMeasurablePartition_xi μ hlt i) hsub).mono
      fun x hx _ => hx

/-- `thm:feng_entropy_as_limit`, planar part, for a planar self-affine system and an invariant
measure `μ`: given the first identity of Feng, Lemma 4.6, (4.16), for `ξ_i`,
`h_i(μ, 𝐢) = -lim_n n⁻¹ log μ_𝐢^{ξ_i}(𝒫_0^{n-1}(𝐢))` for `μ`-almost every `𝐢`. This is Birkhoff's
theorem `birkhoff_ae` for the integrable function `I_μ(𝒫 | \widehat{ξ}_i)`. -/
theorem feng_entropy_as_limit_of_infoSum (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) {i : ℕ} (hsum : P.InfoSum μ i) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => -Real.log ((condMeas μ (P.xi μ i) x).real (cylinder (block n x))) / n)
      atTop (𝓝 (P.dimEntropyAt μ i x)) :=
  tendsto_neg_log_condMeas_cylinder hinv hsum

/-- `thm:feng_entropy_zero`, planar part, for a planar self-affine system: for ergodic `μ` with
`λ_2(𝖠, μ) < λ_1(𝖠, μ)`, given the first identity of Feng, Lemma 4.6, (4.16), for `ξ_i`,
`h_i(μ, 𝐢) = 0 ↔ μ_𝐢^{ξ_i} = δ_𝐢` for `μ`-almost every `𝐢`. The proof is the article's
(tex lines 1918 to 1931): `condInfo_shift_eq_zero_of_localEntropy_eq_zero` (the invariant zero
set of `H`, on which `f` vanishes along every forward iterate),
`condMeas_cylinder_eq_one_of_localEntropy_eq_zero` (the finite information-sum identity gives
mass one on all future cylinders), `condMeas_xi_samePast` (fixed past) and
`eq_dirac_of_cylinder_of_samePast` (intersection to a Dirac measure); the converse is the
pointwise limit `feng_entropy_as_limit_of_infoSum`. -/
theorem feng_entropy_zero_of_infoSum (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) {i : ℕ} (hsum : P.InfoSum μ i) :
    ∀ᵐ x ∂μ, P.dimEntropyAt μ i x = 0 ↔ condMeas μ (P.xi μ i) x = Measure.dirac x := by
  filter_upwards [P.feng_entropy_as_limit_of_infoSum μ hinv hsum,
    condMeas_cylinder_eq_one_of_localEntropy_eq_zero hinv hsum,
    P.condMeas_xi_samePast μ hinv herg hlt i] with x hlim hcyl hpast
  constructor
  · intro hH
    exact eq_dirac_of_cylinder_of_samePast (hcyl hH) (hpast (hcyl hH))
  · intro hd
    have hone : ∀ n : ℕ, (condMeas μ (P.xi μ i) x).real (cylinder (block n x)) = 1 := fun n => by
      rw [hd, measureReal_def,
        Measure.dirac_apply_of_mem (show x ∈ cylinder (block n x) from fun _ => rfl),
        ENNReal.toReal_one]
    simp only [hone, Real.log_one, neg_zero, zero_div] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds

end PlanarSystem

/-! ### Box-like systems through the planar objects -/

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι)

/-- The cited identity `FengInfoSum` of Feng, Lemma 4.6, (4.16), for box-like systems is the
identity `PlanarSystem.InfoSum` for the planar system `S.toPlanar`, by `toPlanar_xi`. -/
theorem infoSum_toPlanar (hfi : FengInfoSum.{u}) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) (i : ℕ) : S.toPlanar.InfoSum μ i := by
  rw [PlanarSystem.InfoSum, S.toPlanar_xi μ hlt]
  exact hfi S μ hinv herg hlt i

/-- `thm:feng_entropy_as_limit`, planar part, for a box-like system, as the specialisation of
`PlanarSystem.feng_entropy_as_limit_of_infoSum` to `S.toPlanar`; the partitions and the
pointwise entropies are those of `BoxLike/DimPartitions.lean`. Hypothesis: `FengInfoSum`. -/
theorem feng_entropy_as_limit_toPlanar (hfi : FengInfoSum.{u}) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) (i : ℕ) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => -Real.log ((condMeas μ (S.xi μ i) x).real (cylinder (block n x))) / n)
      atTop (𝓝 (S.dimEntropyAt μ i x)) := by
  have h := S.toPlanar.feng_entropy_as_limit_of_infoSum μ hinv
    (S.infoSum_toPlanar hfi μ hinv herg hlt i)
  rwa [S.toPlanar_dimEntropyAt μ hlt, S.toPlanar_xi μ hlt] at h

/-- `thm:feng_entropy_zero`, planar part, for a box-like system, as the specialisation of
`PlanarSystem.feng_entropy_zero_of_infoSum` to `S.toPlanar`; the partitions and the pointwise
entropies are those of `BoxLike/DimPartitions.lean`. Hypothesis: `FengInfoSum`. -/
theorem feng_entropy_zero_toPlanar (hfi : FengInfoSum.{u}) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) (i : ℕ) :
    ∀ᵐ x ∂μ, S.dimEntropyAt μ i x = 0 ↔ condMeas μ (S.xi μ i) x = Measure.dirac x := by
  have h := S.toPlanar.feng_entropy_zero_of_infoSum μ hinv herg hlt
    (S.infoSum_toPlanar hfi μ hinv herg hlt i)
  rwa [S.toPlanar_dimEntropyAt μ hlt, S.toPlanar_xi μ hlt] at h

end System

/-- `thm:feng_entropy_as_limit`, both parts, for box-like systems, with the planar part proved
through the planar objects of `S.toPlanar`. Planar part: for an ergodic `μ` with `λ_2 < λ_1` and
each `i ∈ {0, 1, 2}`, `h_i(μ, 𝐢) = -lim_n n⁻¹ log μ_𝐢^{ξ_i}(𝒫_0^{n-1}(𝐢))` for `μ`-almost every
`𝐢`. Scalar part: for a proximal box-like system with rotations, every invariant `ν` on `Σ_Z`,
ergodic or not, and each `i ∈ {0, 1}`,
`\overline{h}_i(ν, 𝐢) = -lim_n n⁻¹ log ν_𝐢^{\overline{ξ}_i}(\overline{𝒫}_0^{n-1}(𝐢))` for
`ν`-almost every `𝐢`. Hypotheses: `FengInfoSum`, `FengInfoSumBar`. The general planar scope is
`feng_entropy_as_limit_general` of `BoxLike/Planar/FengGeneral.lean`. -/
theorem feng_entropy_as_limit_boxLike (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u}) :
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
  ⟨fun S μ _ hinv herg hlt i _ => S.feng_entropy_as_limit_toPlanar hfi μ hinv herg hlt i,
    fun S hrot hprox ν _ hinv hsupp i _ =>
      S.feng_entropy_as_limit_bar hfib hrot hprox ν hinv hsupp i⟩

/-- `thm:feng_entropy_zero`, both parts, for box-like systems, with the planar part proved
through the planar objects of `S.toPlanar` along the article's proof. Planar part: for an ergodic
`μ` with `λ_2 < λ_1` and each `i ∈ {0, 1, 2}`, `h_i(μ, 𝐢) = 0 ↔ μ_𝐢^{ξ_i} = δ_𝐢` for `μ`-almost
every `𝐢`. Scalar part: for a proximal box-like system with rotations, every invariant `ν` on
`Σ_Z`, ergodic or not, and each `i ∈ {0, 1}`,
`\overline{h}_i(ν, 𝐢) = 0 ↔ ν_𝐢^{\overline{ξ}_i} = δ_𝐢` for `ν`-almost every `𝐢`. Hypotheses:
`FengInfoSum`, `FengInfoSumBar`. The general planar scope is `feng_entropy_zero_general` of
`BoxLike/Planar/FengGeneral.lean`. -/
theorem feng_entropy_zero_boxLike (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u}) :
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
  ⟨fun S μ _ hinv herg hlt i _ => S.feng_entropy_zero_toPlanar hfi μ hinv herg hlt i,
    fun S hrot hprox ν _ hinv hsupp i _ =>
      S.feng_entropy_zero_bar hfib hrot hprox ν hinv hsupp i⟩

end BoxLike
