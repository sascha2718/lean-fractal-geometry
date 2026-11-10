module

/-
The partitions of `sec:entropies` are measurable partitions (tex lines 1789 to 1790 and 1914 to
1915; Feng, Lemma 4.2): each of `ξ_0, ξ_1, ξ_2`, `ξ_1^⊥`, `\overline{ξ}_0`, `\overline{ξ}_1` is
the partition into the fibres of a Borel map into `ℝ`. The map records the past `𝐢^-` and the
coordinates of `π(𝐢)` or `\overline{π}(𝐢)` that the atom fixes, and sends the complement of `Σ'`
or of `Σ_Z` to one separate value.

* `past`, `past_eq_iff`, `measurable_past`: the past `𝐢^- = (i_{-1}, i_{-2}, …)` as a Borel map
  into `ℕ → ι`, with `𝐢^- = 𝐣^-` the relation `SamePast`.
* `isMeasurablePartition_atomsOn`: a partition of a Borel set `D` into the fibres of a Borel map
  into a standard Borel space, extended by the atom `Ω ∖ D`, is a measurable partition.
* `System.measurable_coord_slowAxis_proj`: the coordinate of `π(𝐢)` along an axis determined by
  the slow axis `V_𝐢^1` is a Borel function of `𝐢`.
* `System.isMeasurablePartition_xi`, `System.isMeasurablePartition_xiPerp`,
  `System.isMeasurablePartition_xiBar`: the partitions of `sec:entropies` are measurable.
-/
public import BoxLike.DimPartitions
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

@[expose] public section

namespace BoxLike

open MeasureTheory Set

/-! ### The past as a Borel map -/

/-- The past `𝐢^- = (i_{-1}, i_{-2}, …)` of a sequence (`sec:two_sided_shift_space`, tex line
809), as a sequence indexed by `ℕ`. -/
def past {α : Type*} (x : ℤ → α) : ℕ → α := fun n => x (Int.negSucc n)

/-- Two sequences have the same past exactly when `𝐢^- = 𝐣^-` in the sense of `SamePast`
(`sec:two_sided_shift_space`, tex line 728). -/
theorem past_eq_iff {α : Type*} {x y : ℤ → α} : past y = past x ↔ SamePast y x := by
  constructor
  · intro h n hn
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = Int.negSucc k := by
      rcases n with n | n
      · exact absurd hn (by simp)
      · exact ⟨n, rfl⟩
    exact congrFun h k
  · intro h
    funext k
    exact h _ (Int.negSucc_lt_zero k)

/-- The past `𝐢 ↦ 𝐢^-` of `sec:two_sided_shift_space` is a Borel map. -/
theorem measurable_past {α : Type*} [MeasurableSpace α] :
    Measurable (past : (ℤ → α) → ℕ → α) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-! ### Fibres of a Borel map on a Borel set -/

/-- A partition of a Borel set `D` into the fibres of a Borel map `G` into a standard Borel
space, extended to `Ω` by the atom `Ω ∖ D`, is a measurable partition in the sense of
`sec:conditional` (tex lines 1671 to 1673). The inducing map into `ℝ` is the exponential of a
measurable embedding of the target of `G` on `D`, and `0` on `Ω ∖ D`. -/
theorem isMeasurablePartition_atomsOn {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [StandardBorelSpace X] {D : Set Ω} (hD : MeasurableSet D) {G : Ω → X} (hG : Measurable G)
    {ξ : Ω → Set Ω} (hξ : ∀ x ∈ D, ∀ y ∈ D, y ∈ ξ x ↔ G y = G x) :
    IsMeasurablePartition (atomsOn D ξ) := by
  classical
  have he := measurableEmbedding_embeddingReal X
  refine ⟨fun x => if x ∈ D then Real.exp (embeddingReal X (G x)) else 0, ?_, fun x y => ?_⟩
  · exact Measurable.ite hD (Real.measurable_exp.comp (he.measurable.comp hG)) measurable_const
  · by_cases hx : x ∈ D
    · rw [atomsOn_of_mem hx]
      by_cases hy : y ∈ D
      · simp only [mem_inter_iff, hy, and_true, ite_eq_left hx, ite_true, Real.exp_eq_exp,
          he.injective.eq_iff]
        exact hξ x hx y hy
      · simp [hx, hy, (Real.exp_pos _).ne]
    · rw [atomsOn_of_notMem hx]
      by_cases hy : y ∈ D
      · simp [hx, hy, (Real.exp_pos _).ne']
      · simp [hx, hy]

namespace System

/-! ### The partitions of `Σ'` -/

section Planar

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι)

/-- The coordinate of `π(𝐢)` along the axis `slowAxis + c` is a Borel function of `𝐢`, since
`Σ^τ` is Borel (`sec:lyapunov_exponents`, tex line 1545) and `π` is Borel. -/
theorem measurable_coord_slowAxis_proj (μ : Measure (ℤ → ι)) (c : ZMod 2) :
    Measurable fun x => coord (S.slowAxis μ x + c) (S.proj x) := by
  classical
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  have h : (fun x => coord (S.slowAxis μ x + c) (S.proj x)) = fun x =>
      if x ∈ S.SigmaTau μ then coord (1 + c) (S.proj x) else coord (0 + c) (S.proj x) := by
    funext x
    by_cases hx : x ∈ S.SigmaTau μ <;> simp [slowAxis, hx]
  have hc : ∀ d : ZMod 2, Measurable fun x => coord d (S.proj x) := fun d => by
    unfold coord
    split_ifs
    · exact measurable_fst.comp hS.measurable_proj
    · exact measurable_snd.comp hS.measurable_proj
  rw [h]
  exact Measurable.ite (S.measurableSet_SigmaTau μ) (hc _) (hc _)

/-- Feng, *Dimension of invariant measures for affine iterated function systems*,
Duke Math. J. 172 (2023), Lemma 4.2, for the planar partitions (`sec:entropies`, tex lines 1789
to 1869): `ξ_0, ξ_1, ξ_2` are measurable partitions, being the fibres of
`𝐢 ↦ (𝐢^-, V_𝐢^i + π(𝐢))`. In the box-like case the proof is elementary once `Σ^τ` and `Σ^ω`
are Borel. -/
theorem isMeasurablePartition_xi (μ : Measure (ℤ → ι)) (i : ℕ) :
    IsMeasurablePartition (S.xi μ i) := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  have hax : ∀ {x y : ℤ → ι}, SamePast y x → S.slowAxis μ y = S.slowAxis μ x :=
    fun h => S.slowAxis_eq_of_samePast μ h.symm
  unfold xi
  rcases i with _ | _ | i
  · refine isMeasurablePartition_atomsOn (S.measurableSet_SigmaPrime μ) measurable_past
      fun x _ y _ => ?_
    simp [mem_oseledets_iff, past_eq_iff]
  · refine isMeasurablePartition_atomsOn (S.measurableSet_SigmaPrime μ)
      (measurable_past.prodMk (S.measurable_coord_slowAxis_proj μ 1)) fun x _ y _ => ?_
    simp only [mem_ofPred_eq, mem_oseledets_iff, Prod.mk.injEq, past_eq_iff]
    constructor
    · rintro ⟨hp, h⟩
      refine ⟨hp, ?_⟩
      rw [hax hp]
      simpa using h
    · rintro ⟨hp, h⟩
      rw [hax hp] at h
      exact ⟨hp, by simpa using h⟩
  · refine isMeasurablePartition_atomsOn (S.measurableSet_SigmaPrime μ)
      (measurable_past.prodMk hS.measurable_proj) fun x _ y _ => ?_
    simp [mem_oseledets_iff, past_eq_iff]

/-- `ξ_1^⊥` is a measurable partition: "the same argument" as Feng, Lemma 4.2
(`sec:entropies`, tex line 1790). -/
theorem isMeasurablePartition_xiPerp (μ : Measure (ℤ → ι)) :
    IsMeasurablePartition (S.xiPerp μ) := by
  have h0 := S.measurable_coord_slowAxis_proj μ 0
  simp only [add_zero] at h0
  unfold xiPerp
  refine isMeasurablePartition_atomsOn (S.measurableSet_SigmaPrime μ)
    (measurable_past.prodMk h0) fun x _ y _ => ?_
  simp only [mem_ofPred_eq, coord_sub, sub_eq_zero, Prod.mk.injEq, past_eq_iff]
  constructor
  · rintro ⟨hp, h⟩
    exact ⟨hp, by rw [S.slowAxis_eq_of_samePast μ hp.symm, h]⟩
  · rintro ⟨hp, h⟩
    rw [S.slowAxis_eq_of_samePast μ hp.symm] at h
    exact ⟨hp, h⟩

end Planar

/-! ### The partitions of `Σ_Z` -/

section Projective

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι)

/-- Feng, Lemma 4.2, for the projective system `Ψ` on `ℝ` (`sec:entropies`, tex lines 1835 to
1920): `\overline{ξ}_0` and `\overline{ξ}_1` are measurable partitions. -/
theorem isMeasurablePartition_xiBar (i : ℕ) : IsMeasurablePartition (S.xiBar i) := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  rcases i with _ | i
  · simp only [xiBar]
    refine isMeasurablePartition_atomsOn (measurableSet_subshift S.o) measurable_past
      fun x _ y _ => ?_
    simp [past_eq_iff]
  · simp only [xiBar]
    refine isMeasurablePartition_atomsOn (measurableSet_subshift S.o)
      (measurable_past.prodMk hS.measurable_projBar) fun x _ y _ => ?_
    simp [past_eq_iff]

end Projective

end System

end BoxLike
