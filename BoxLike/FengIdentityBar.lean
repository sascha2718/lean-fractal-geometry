module

/-
Feng's information-sum identity, D.-J. Feng, *Dimension of invariant measures for affine iterated
function systems*, Duke Math. J. 172 (2023), arXiv:1901.01691v2, Lemma 4.6, first identity of
(4.16), proved for the partitions `\overline{ξ}_0`, `\overline{ξ}_1` of `Σ_Z` of `sec:entropies`
(tex lines 1830 to 1842) and every invariant measure carried by `Σ_Z`, ergodic or not. It is the
general identity `infoSum_of_pullShift` of `BoxLike/FengIdentity.lean`, applied with `D = Σ_Z`:
the shift maps the atoms of `\overline{ξ}_i` refined by the time-zero symbol onto atoms of
`\overline{ξ}_i`, since the past of `σ 𝐢` is the past of `𝐢` followed by `i_0`, and
`\overline{π}(𝐢) = g_{i_0}(\overline{π}(σ 𝐢))` with `g_{i_0}` injective. The article checks Feng's
constant-multiplicity hypothesis (4.7) at tex lines 1842 to 1842; the proof here needs no
hypothesis of this kind, and neither rotations nor proximality.

* `shift_one_mem_subshift_iff`: `σ^{-1}(Σ_Z) = Σ_Z`.
* `System.projBar_shift_one_eq_iff`: `\overline{π}(σ 𝐣) = \overline{π}(σ 𝐢)` exactly when
  `\overline{π}(𝐣) = \overline{π}(𝐢)`, for `j_0 = i_0`.
* `System.pullShift_xiBar`, `System.pullShift_xiBar_subset_of_notMem`: the invariance property
  of `\overline{ξ}_i`.
* `System.infoSum_xiBar`: the identity for `\overline{ξ}_i`, every invariant `ν` carried by
  `Σ_Z` and every `i`.
* `fengInfoSumBar_holds`: the predicate `FengInfoSumBar` of `BoxLike/LiteratureFeng.lean` holds.
-/
public import BoxLike.FengIdentity

@[expose] public section

namespace BoxLike

open MeasureTheory Set

universe u

/-- `σ^{-1}(Σ_Z) = Σ_Z`: a sequence lies in `Σ_Z` exactly when its shift does
(`sec:subshift`). -/
theorem shift_one_mem_subshift_iff {ι : Type*} {o : ι → ZMod 2} {y : ℤ → ι × ZMod 2} :
    shift 1 y ∈ subshift o ↔ y ∈ subshift o := by
  constructor
  · intro h
    have := shift_mem_subshift o h (-1)
    rwa [shift_shift, show (1 : ℤ) + -1 = 0 by norm_num, shift_zero] at this
  · intro h
    exact shift_mem_subshift o h 1

namespace System

variable {ι : Type u} (S : System ι)

/-- For `j_0 = i_0`, `\overline{π}(σ 𝐣) = \overline{π}(σ 𝐢)` exactly when
`\overline{π}(𝐣) = \overline{π}(𝐢)`: `\overline{π}(𝐢) = g_{i_0}(\overline{π}(σ 𝐢))`
(`Bounds.projBar_eq`) and `g_{i_0}` is injective, its ratio being non-zero. -/
theorem projBar_shift_one_eq_iff [Finite ι] {y z : ℤ → ι × ZMod 2} (h0 : z 0 = y 0) :
    S.projBar (shift 1 z) = S.projBar (shift 1 y) ↔ S.projBar z = S.projBar y := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  rw [hS.projBar_eq z, hS.projBar_eq y, h0]
  simp only [g, add_left_inj, mul_right_inj' (S.ratio_ne_zero (y 0))]

/-- The invariance property of the partitions `\overline{ξ}_i` of `Σ_Z`, Feng, Lemma 4.4(1), with
`n = 1`, for the projective system `Ψ`:
`σ^{-1}(\overline{ξ}_i(σ 𝐢)) = \overline{ξ}_i(𝐢) ∩ [i_0]` for `𝐢 ∈ Σ_Z` and every `i`. -/
theorem pullShift_xiBar [Finite ι] (i : ℕ) {y : ℤ → ι × ZMod 2} (hy : y ∈ subshift S.o) :
    pullShift (S.xiBar i) y = refineZero (S.xiBar i) y := by
  have hσy : shift 1 y ∈ subshift S.o := shift_one_mem_subshift_iff.2 hy
  ext z
  rcases i with _ | i
  · simp only [pullShift, refineZero, xiBar, mem_preimage, atomsOn_of_mem hσy,
      atomsOn_of_mem hy, mem_inter_iff, mem_ofPred_eq, samePast_shift_one_iff,
      shift_one_mem_subshift_iff]
    tauto
  · simp only [pullShift, refineZero, xiBar, mem_preimage, atomsOn_of_mem hσy,
      atomsOn_of_mem hy, mem_inter_iff, mem_ofPred_eq, samePast_shift_one_iff,
      shift_one_mem_subshift_iff]
    constructor
    · rintro ⟨⟨⟨hp, h0⟩, hπ⟩, hz⟩
      exact ⟨⟨⟨hp, (S.projBar_shift_one_eq_iff h0).1 hπ⟩, hz⟩, h0⟩
    · rintro ⟨⟨⟨hp, hπ⟩, hz⟩, h0⟩
      exact ⟨⟨⟨hp, h0⟩, (S.projBar_shift_one_eq_iff h0).2 hπ⟩, hz⟩

/-- The atoms of `\overline{ξ}_i` at points of `Σ_Z` lie in `Σ_Z`. -/
theorem xiBar_subset_subshift (i : ℕ) {y : ℤ → ι × ZMod 2} (hy : y ∈ subshift S.o) :
    S.xiBar i y ⊆ subshift S.o := by
  rcases i with _ | i <;> simp only [xiBar, atomsOn_of_mem hy] <;> exact inter_subset_right

/-- Outside `Σ_Z` the atoms of `σ^{-1}\overline{ξ}_i` avoid `Σ_Z`. -/
theorem pullShift_xiBar_subset_of_notMem (i : ℕ) {y : ℤ → ι × ZMod 2}
    (hy : y ∉ subshift S.o) : pullShift (S.xiBar i) y ⊆ (subshift S.o)ᶜ := by
  have hσy : shift 1 y ∉ subshift S.o := fun h => hy (shift_one_mem_subshift_iff.1 h)
  intro z hz
  rcases i with _ | i <;>
  · simp only [pullShift, xiBar, mem_preimage, atomsOn_of_notMem hσy, mem_compl_iff] at hz ⊢
    exact fun h => hz (shift_one_mem_subshift_iff.2 h)

/-- Feng, Lemma 4.6, first identity of (4.16), for the partitions `\overline{ξ}_i` of `Σ_Z`,
proved: for every invariant probability measure `ν` on `{1, …, 2N}^ℤ` carried by `Σ_Z`, ergodic
or not, and every `i`, `-log ν_𝐢^{\overline{ξ}_i}(\overline{𝒫}_0^{n-1}(𝐢))` equals
`∑_{k<n} I_ν(\overline{𝒫} | \widehat{\overline{ξ}}_i)(σ^k 𝐢)` for all `n`, for `ν`-almost every
`𝐢`. This is the identity cited in the proof of `thm:feng_entropy_zero` (tex lines 1919 to
2019) and behind `thm:feng_entropy_as_limit`, scalar part. -/
theorem infoSum_xiBar [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν]
    (hinv : MeasurePreserving (shift 1) ν ν) (hsupp : ν (subshift S.o)ᶜ = 0) (i : ℕ) :
    ∀ᵐ y ∂ν, ∀ n : ℕ, -Real.log ((condMeas ν (S.xiBar i) y).real (cylinder (block n y))) =
      ∑ k ∈ Finset.range n, condInfo ν (S.xiBar i) (shift k y) :=
  infoSum_of_pullShift hinv (S.isMeasurablePartition_xiBar i) (measurableSet_subshift S.o)
    hsupp (fun _ hy => S.pullShift_xiBar i hy) (fun _ hy => S.xiBar_subset_subshift i hy)
    (fun _ hy => S.pullShift_xiBar_subset_of_notMem i hy)

end System

/-- The literature predicate `FengInfoSumBar` of `BoxLike/LiteratureFeng.lean`, Feng, Lemma 4.6,
first identity of (4.16), for the projective partitions, holds: it is `System.infoSum_xiBar`; the
hypotheses `S.WithRotations` and `S.Proximal` of the predicate are not used. It is the input of
`thm:feng_entropy_as_limit` and `thm:feng_entropy_zero`, scalar part. -/
theorem fengInfoSumBar_holds : FengInfoSumBar.{u} := by
  intro ι _ _ _ S _ _ ν _ hinv hsupp i
  exact S.infoSum_xiBar ν hinv hsupp i

end BoxLike
