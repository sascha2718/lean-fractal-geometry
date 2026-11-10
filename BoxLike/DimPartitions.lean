module

/-
The partitions and the entropies of a box-like system: the system-specific part of
`sec:entropies`, the average measure of `sec:average_gibbs`, the ergodicity of the equilibrium
state of a tuple containing a proximal diagonal generator, and the first step of the proof of
`thm:main_extended` for `s ≥ 2`. The partitions are atom maps in the sense of
`BoxLike/Conditional.lean`, and `Σ'`, `V_𝐢^i` have the box-like form of `BoxLike/SlowAxis.lean`.

* `System.xi`, `System.xiPerp`: the partitions `ξ_0, ξ_1, ξ_2` and `ξ_1^⊥` of `Σ'`, extended to
  `Σ` by the atom `Σ ∖ Σ'`.
* `System.mem_xi_self`, `System.xi_eq_of_mem`: `ξ_i` is a partition of `Σ`.
* `System.xi_succ_subset`, `System.xi_two_subset_xiPerp`, `System.xiPerp_subset_xi_zero`: the
  inclusions `ξ_2(𝐢) ⊆ ξ_1(𝐢) ⊆ ξ_0(𝐢)` and `ξ_2(𝐢) ⊆ ξ_1^⊥(𝐢) ⊆ ξ_0(𝐢)`.
* `System.xiBar`, `System.xiBar_succ_subset`: the partitions `\overline{ξ}_0`, `\overline{ξ}_1`
  of `Σ_Z`, extended by the atom `{1, …, 2N}^ℤ ∖ Σ_Z`, and
  `\overline{ξ}_1(𝐢) ⊆ \overline{ξ}_0(𝐢)`.
* `System.dimEntropy`, `System.dimEntropyAt`, `System.dimEntropyBar`, `System.dimEntropyBarAt`:
  the entropies `h_i(μ)`, `h_i(μ, 𝐢)`, `\overline{h}_i(ν)`, `\overline{h}_i(ν, 𝐢)`.
* `avgMeasure`, `isProbabilityMeasure_avgMeasure`: the average `\overline{μ} = (μ_1 + μ_2)/2`
  of `eq:average_gibbs`.
* `System.ergodic_of_gibbsDecomposition`, `System.ergodic_of_hasProximalDiagonal`: the
  equilibrium state is ergodic, from `thm:eq_state_is_sum`.
* `neg_lt_entropy_of_two_le`: for `s ≥ 2` the entropy of an equilibrium state exceeds `-λ_2`.
-/
public import BoxLike.Conditional
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.Main
public import BoxLike.SlowAxis

@[expose] public section

namespace BoxLike

open MeasureTheory Set
open scoped NNReal

universe u

namespace System

/-! ### The partitions of `Σ'` -/

section Planar

variable {ι : Type u} [MeasurableSpace ι] (S : System ι)

/-- The partitions `ξ_0, ξ_1, ξ_2` of `Σ'` (`sec:entropies`, tex lines 1779 to 1784):
`ξ_i(𝐢) = {𝐣 ∈ Σ' : 𝐣^- = 𝐢^-, π(𝐣) - π(𝐢) ∈ V_𝐢^i}`, extended to `Σ` by the atom `Σ ∖ Σ'`. -/
noncomputable def xi (μ : Measure (ℤ → ι)) (i : ℕ) : (ℤ → ι) → Set (ℤ → ι) :=
  atomsOn (S.SigmaPrime μ) fun x =>
    {y | SamePast y x ∧ S.proj y - S.proj x ∈ S.oseledets μ x i}

/-- The partition `ξ_1^⊥` of `Σ'` (`sec:entropies`, tex lines 1785 to 1788):
`ξ_1^⊥(𝐢) = {𝐣 ∈ Σ' : 𝐣^- = 𝐢^-, π(𝐣) - π(𝐢) ⊥ V_𝐢^1}`, extended to `Σ` by the atom `Σ ∖ Σ'`.
Orthogonality to the axis `slowAxis` is the vanishing of that coordinate. -/
noncomputable def xiPerp (μ : Measure (ℤ → ι)) : (ℤ → ι) → Set (ℤ → ι) :=
  atomsOn (S.SigmaPrime μ) fun x =>
    {y | SamePast y x ∧ coord (S.slowAxis μ x) (S.proj y - S.proj x) = 0}

/-- Every point lies in its own atom of `ξ_i`. -/
theorem mem_xi_self (μ : Measure (ℤ → ι)) (i : ℕ) (x : ℤ → ι) : x ∈ S.xi μ i x := by
  unfold xi
  by_cases hx : x ∈ S.SigmaPrime μ
  · rw [atomsOn_of_mem hx]
    refine ⟨⟨SamePast.refl x, ?_⟩, hx⟩
    rw [sub_self]
    rcases i with _ | _ | i <;> simp [oseledets, coord]
  · rw [atomsOn_of_notMem hx]
    exact hx

/-- `ξ_i` is a partition: the atom of a point of `ξ_i(𝐢)` is `ξ_i(𝐢)`. This uses that `Σ'` and
the slow axis are saturated with respect to the past. -/
theorem xi_eq_of_mem (μ : Measure (ℤ → ι)) (i : ℕ) {x y : ℤ → ι} (h : y ∈ S.xi μ i x) :
    S.xi μ i y = S.xi μ i x := by
  unfold xi at h ⊢
  by_cases hx : x ∈ S.SigmaPrime μ
  · rw [atomsOn_of_mem hx] at h
    obtain ⟨⟨hp, hv⟩, hy⟩ := h
    rw [atomsOn_of_mem hx, atomsOn_of_mem hy]
    have hax : S.slowAxis μ y = S.slowAxis μ x := S.slowAxis_eq_of_samePast μ hp.symm
    rw [mem_oseledets_iff] at hv
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, mem_oseledets_iff, hax]
    constructor
    · rintro ⟨⟨hzp, hzv⟩, hz⟩
      refine ⟨⟨hzp.trans hp, ?_⟩, hz⟩
      rcases hzv with h0 | ⟨h1, e⟩ | ⟨h2, e⟩
      · exact Or.inl h0
      · rcases hv with h0 | ⟨-, e'⟩ | ⟨h2, -⟩
        · omega
        · exact Or.inr (Or.inl ⟨h1, e.trans e'⟩)
        · omega
      · rcases hv with h0 | ⟨h1, -⟩ | ⟨-, e'⟩
        · omega
        · omega
        · exact Or.inr (Or.inr ⟨h2, e.trans e'⟩)
    · rintro ⟨⟨hzp, hzv⟩, hz⟩
      refine ⟨⟨hzp.trans hp.symm, ?_⟩, hz⟩
      rcases hzv with h0 | ⟨h1, e⟩ | ⟨h2, e⟩
      · exact Or.inl h0
      · rcases hv with h0 | ⟨-, e'⟩ | ⟨h2, -⟩
        · omega
        · exact Or.inr (Or.inl ⟨h1, e.trans e'.symm⟩)
        · omega
      · rcases hv with h0 | ⟨h1, -⟩ | ⟨-, e'⟩
        · omega
        · omega
        · exact Or.inr (Or.inr ⟨h2, e.trans e'.symm⟩)
  · rw [atomsOn_of_notMem hx] at h
    rw [atomsOn_of_notMem hx, atomsOn_of_notMem h]

/-- `ξ_2(𝐢) ⊆ ξ_1(𝐢) ⊆ ξ_0(𝐢)` (`sec:entropies`, tex line 1794). -/
theorem xi_succ_subset (μ : Measure (ℤ → ι)) (i : ℕ) (x : ℤ → ι) :
    S.xi μ (i + 1) x ⊆ S.xi μ i x := by
  unfold xi
  by_cases hx : x ∈ S.SigmaPrime μ
  · rw [atomsOn_of_mem hx, atomsOn_of_mem hx]
    rintro y ⟨⟨hp, hv⟩, hy⟩
    refine ⟨⟨hp, ?_⟩, hy⟩
    rcases i with _ | _ | i
    · trivial
    · simp only [oseledets, mem_singleton_iff] at hv
      simp [oseledets, hv, coord]
    · exact hv
  · rw [atomsOn_of_notMem hx, atomsOn_of_notMem hx]

/-- `ξ_2(𝐢) ⊆ ξ_1^⊥(𝐢)` (`sec:entropies`, tex line 1795). -/
theorem xi_two_subset_xiPerp (μ : Measure (ℤ → ι)) (x : ℤ → ι) :
    S.xi μ 2 x ⊆ S.xiPerp μ x := by
  unfold xi xiPerp
  by_cases hx : x ∈ S.SigmaPrime μ
  · rw [atomsOn_of_mem hx, atomsOn_of_mem hx]
    rintro y ⟨⟨hp, hv⟩, hy⟩
    refine ⟨⟨hp, ?_⟩, hy⟩
    simp only [oseledets, mem_singleton_iff] at hv
    simp [hv, coord]
  · rw [atomsOn_of_notMem hx, atomsOn_of_notMem hx]

/-- `ξ_1^⊥(𝐢) ⊆ ξ_0(𝐢)` (`sec:entropies`, tex line 1795). -/
theorem xiPerp_subset_xi_zero (μ : Measure (ℤ → ι)) (x : ℤ → ι) :
    S.xiPerp μ x ⊆ S.xi μ 0 x := by
  unfold xi xiPerp
  by_cases hx : x ∈ S.SigmaPrime μ
  · rw [atomsOn_of_mem hx, atomsOn_of_mem hx]
    rintro y ⟨⟨hp, -⟩, hy⟩
    exact ⟨⟨hp, trivial⟩, hy⟩
  · rw [atomsOn_of_notMem hx, atomsOn_of_notMem hx]

end Planar

/-! ### The partitions of `Σ_Z` -/

section Projective

variable {ι : Type u} (S : System ι)

/-- The partitions `\overline{ξ}_0`, `\overline{ξ}_1` of `Σ_Z` (`sec:entropies`, tex lines 1836
to 1920), extended to `{1, …, 2N}^ℤ` by the atom `{1, …, 2N}^ℤ ∖ Σ_Z`. They do not depend on a
measure. Indices above `1` repeat `\overline{ξ}_1`. -/
noncomputable def xiBar : ℕ → (ℤ → ι × ZMod 2) → Set (ℤ → ι × ZMod 2)
  | 0 => atomsOn (subshift S.o) fun y => {z | SamePast z y}
  | _ => atomsOn (subshift S.o) fun y => {z | SamePast z y ∧ S.projBar z = S.projBar y}

/-- `\overline{ξ}_1(𝐢) ⊆ \overline{ξ}_0(𝐢)` (`sec:entropies`, tex line 1842). -/
theorem xiBar_succ_subset (i : ℕ) (y : ℤ → ι × ZMod 2) : S.xiBar (i + 1) y ⊆ S.xiBar i y := by
  by_cases hy : y ∈ subshift S.o
  · rcases i with _ | i
    · simp only [xiBar, atomsOn_of_mem hy]
      rintro z ⟨⟨hp, -⟩, hz⟩
      exact ⟨hp, hz⟩
    · simp only [xiBar]
      exact subset_rfl
  · rcases i with _ | i <;> simp only [xiBar, atomsOn_of_notMem hy] <;> exact subset_rfl

end Projective

/-! ### The entropies of `sec:entropies` -/

section Entropies

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι)

/-- The `i`-dimensional entropy `h_i(μ) = H_μ(𝒫 | \widehat{ξ}_i)` (`sec:entropies`, tex lines
1891 to 1897). -/
noncomputable def dimEntropy (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] (i : ℕ) : ℝ :=
  condEntropy μ (S.xi μ i)

/-- The pointwise `i`-dimensional entropy `h_i(μ, 𝐢) = E_μ(I_μ(𝒫 | \widehat{ξ}_i) | ℐ)(𝐢)`
(`sec:entropies`, tex lines 1805 to 1811), determined up to a `μ`-null set. -/
noncomputable def dimEntropyAt (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] (i : ℕ) :
    (ℤ → ι) → ℝ :=
  localEntropy μ (S.xi μ i)

/-- The entropy `\overline{h}_i(ν) = H_ν(\overline{𝒫} | \widehat{\overline{ξ}}_i)`
(`sec:entropies`, tex lines 1848 to 1853). -/
noncomputable def dimEntropyBar (ν : Measure (ℤ → ι × ZMod 2)) [IsFiniteMeasure ν] (i : ℕ) : ℝ :=
  condEntropy ν (S.xiBar i)

/-- The pointwise entropy `\overline{h}_i(ν, 𝐢)` (`sec:entropies`, tex lines 1842 to 1847),
determined up to a `ν`-null set. -/
noncomputable def dimEntropyBarAt (ν : Measure (ℤ → ι × ZMod 2)) [IsFiniteMeasure ν] (i : ℕ) :
    (ℤ → ι × ZMod 2) → ℝ :=
  localEntropy ν (S.xiBar i)

end Entropies

end System

/-! ### The average measure of `sec:average_gibbs` -/

/-- The average `\overline{μ} = (μ_1 + μ_2) / 2` of `eq:average_gibbs`. The scalar lies in
`ℝ≥0`, for which Mathlib has the instance that a multiple of a finite measure is finite. -/
noncomputable def avgMeasure {Ω : Type*} [MeasurableSpace Ω] (μ₁ μ₂ : Measure Ω) : Measure Ω :=
  (2⁻¹ : ℝ≥0) • (μ₁ + μ₂)

/-- The average `\overline{μ}` of `eq:average_gibbs` of two finite measures is finite. -/
instance {Ω : Type*} [MeasurableSpace Ω] (μ₁ μ₂ : Measure Ω) [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] : IsFiniteMeasure (avgMeasure μ₁ μ₂) := by
  unfold avgMeasure
  infer_instance

/-- The average of two probability measures is a probability measure. -/
theorem isProbabilityMeasure_avgMeasure {Ω : Type*} [MeasurableSpace Ω] (μ₁ μ₂ : Measure Ω)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] :
    IsProbabilityMeasure (avgMeasure μ₁ μ₂) := by
  refine ⟨?_⟩
  simp only [avgMeasure, Measure.smul_apply, Measure.add_apply, measure_univ]
  rw [ENNReal.smul_def, smul_eq_mul, one_add_one_eq_two]
  simp [ENNReal.inv_mul_cancel]

/-! ### Ergodicity of the equilibrium state -/

namespace System

section Ergodicity

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {s : ℝ}

variable {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)}

/-- In the normalised case the ergodicity of the equilibrium state follows from
`thm:eq_state_is_sum`: `μ = q_*μ_1` is a factor of the ergodic measure `μ_1`. The hypothesis
`herg` of the statements of `sec:average_gibbs` and `sec:average_gibbs_entropy` is therefore a
consequence of their hypothesis `hdec`. -/
theorem ergodic_of_gibbsDecomposition {μ : Measure (ℤ → ι)}
    (hdec : S.GibbsDecomposition s μ μ₁ μ₂) : Ergodic (shift 1) μ := by
  have hmap : μ₁.map unCode = μ := map_unCode_of_decomposition hdec.supp₁ hdec.eq₁
  have hmp : MeasurePreserving (unCode : (ℤ → ι × ZMod 2) → ℤ → ι) μ₁ μ :=
    ⟨measurable_unCode, hmap⟩
  exact hmp.ergodic_of_ergodic_semiconj hdec.ergodic₁ (measurable_shift 1)
    (fun y => unCode_shift 1 y)

/-- Proved from the Gibbs bounds of `thm:irred_eq_state` for tuples with rotations,
`EquilibriumGibbsStatement`, and the decomposition of `thm:eq_state_is_sum`,
`FraserJordanJurgaDecomposition`, both proved in the library: for a tuple containing a proximal
diagonal generator and `0 < s < 2`, every invariant `s`-equilibrium state is ergodic. -/
theorem ergodic_of_hasProximalDiagonal (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hrot : S.WithRotations)
    (hdiag : S.HasProximalDiagonal) (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) : Ergodic (shift 1) μ := by
  have hgibbs := hfk S hrot hs0 hs2 μ hinv heq
  obtain ⟨μ₁, μ₂, h⟩ := hfjj S hrot hdiag hs0 hs2 μ hinv hgibbs
  exact S.ergodic_of_gibbsDecomposition h

end Ergodicity

end System

/-! ### The case `s ≥ 2` of `thm:main_extended` -/

/-- For `s ≥ 2` the entropy of an equilibrium state exceeds `-λ_2`, so the entropy alternative of
`thm:main_extended` cannot hold (first step of its proof). -/
theorem neg_lt_entropy_of_two_le {h l1 l2 s : ℝ} (hl : l2 ≤ l1) (hl1 : l1 < 0) (hs : 2 ≤ s)
    (heq : h + energy l1 l2 s = 0) : -l2 < h := by
  have hl2 : l2 < 0 := lt_of_le_of_lt hl hl1
  unfold energy at heq
  split_ifs at heq with hs1 hs2
  · linarith
  · have : s = 2 := le_antisymm hs2 hs
    subst this
    nlinarith
  · have := mul_nonneg (show 0 ≤ s / 2 - 1 by linarith)
      (neg_nonneg.2 (show l1 + l2 ≤ 0 by linarith))
    nlinarith

end BoxLike
