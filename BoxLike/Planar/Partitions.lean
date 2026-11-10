module

/-
The partitions and the entropies of `sec:entropies` for a planar self-affine system: the
partitions `ξ_0, ξ_1, ξ_2` and `ξ_1^⊥` of the set `Σ'` of `sec:lyapunov_exponents`, the
`i`-dimensional entropies `h_i(μ)` and the pointwise entropies `h_i(μ, 𝐢)`, for the objects of
`thm:feng_entropy_as_limit`, `thm:feng_entropy_kolmogorov_sinai`, `thm:feng_entropy_zero` and
`thm:feng1`. `Σ'` is the set of regular points of `BoxLike/Planar/Oseledets.lean` for the
exponents `λ_i(𝖠, μ)`, and `V_𝐢^1` is given by `eq:V_lyapunov`. The partitions are atom maps
in the sense of `BoxLike/Conditional.lean`, extended to `Σ` by the atom `Σ ∖ Σ'`, as for the
box-like partitions of `BoxLike/DimPartitions.lean`.

* `PlanarSystem.lyapunov₁`, `PlanarSystem.lyapunov₂`: the exponents `λ_i(𝖠, μ)` of the tuple.
* `PlanarSystem.SigmaPrime`, `PlanarSystem.oseledets`, `PlanarSystem.slowAngle`: `Σ'`, the
  filtration `V_𝐢^i` and the angle of the slow direction.
* `PlanarSystem.measurableSet_SigmaPrime`, `PlanarSystem.shift_mem_SigmaPrime_iff`,
  `PlanarSystem.mem_SigmaPrime_of_samePast`: `Σ'` is Borel, invariant and saturated with
  respect to the past.
* `PlanarSystem.xi`, `PlanarSystem.xiPerp`: `ξ_i(𝐢) = {𝐣 ∈ Σ' : 𝐣^- = 𝐢^-, π(𝐣) - π(𝐢) ∈ V_𝐢^i}`
  and `ξ_1^⊥(𝐢) = {𝐣 ∈ Σ' : 𝐣^- = 𝐢^-, π(𝐣) - π(𝐢) ⊥ V_𝐢^1}`.
* `PlanarSystem.mem_xi_self`, `PlanarSystem.xi_eq_of_mem`: `ξ_i` is a partition.
* `PlanarSystem.xi_succ_subset`, `PlanarSystem.xi_two_subset_xiPerp`,
  `PlanarSystem.xiPerp_subset_xi_zero`: `ξ_2(𝐢) ⊆ ξ_1(𝐢) ⊆ ξ_0(𝐢)` and
  `ξ_2(𝐢) ⊆ ξ_1^⊥(𝐢) ⊆ ξ_0(𝐢)`.
* `PlanarSystem.isMeasurablePartition_xi`, `PlanarSystem.isMeasurablePartition_xiPerp`: Feng,
  Lemma 4.2, the partitions are measurable.
* `PlanarSystem.dimEntropy`, `PlanarSystem.dimEntropyAt`: `h_i(μ)` and `h_i(μ, 𝐢)`.
* `PlanarSystem.dimEntropy_zero_eq_entropy'`: `h_0(μ) = h(μ)` when `μ(Σ') = 1`.
-/
public import BoxLike.Planar.Oseledets
public import BoxLike.PastEntropy

@[expose] public section

namespace BoxLike

open MeasureTheory Set Matrix
open scoped Real

universe u

namespace PlanarSystem

variable {ι : Type u} (P : PlanarSystem ι)

/-! ### Exponents, `Σ'` and the filtration -/

section Oseledets

variable [MeasurableSpace ι]

/-- The Lyapunov exponent `λ_1(𝖠, μ)` of the linear parts (`sec:lyapunov_exponents`). -/
noncomputable def lyapunov₁ (μ : Measure (ℤ → ι)) : ℝ := MatrixTuple.lyapunov₁ P.mat μ

/-- The Lyapunov exponent `λ_2(𝖠, μ)` of the linear parts (`sec:lyapunov_exponents`). -/
noncomputable def lyapunov₂ (μ : Measure (ℤ → ι)) : ℝ := MatrixTuple.lyapunov₂ P.mat μ

/-- The set `Σ'` of `sec:lyapunov_exponents` (tex lines 1521 to 1523 and 1617 to 1618): the
points at which the Oseledets properties (V1) to (V3) hold for the exponents `λ_1(𝖠, μ)`,
`λ_2(𝖠, μ)`. It is the largest such set; it is Borel, invariant and saturated with respect to
the past (`measurableSet_SigmaPrime`, `shift_mem_SigmaPrime_iff`, `mem_SigmaPrime_of_samePast`).
That `μ(Σ') = 1` for ergodic `μ` with `λ_2 < λ_1` is Oseledets' theorem, proved in
`BoxLike/Planar/OseledetsTheorem.lean` (`measure_SigmaPrime_compl_of_ergodic`). -/
noncomputable def SigmaPrime (μ : Measure (ℤ → ι)) : Set (ℤ → ι) :=
  MatrixTuple.regularSet P.mat (P.lyapunov₁ μ) (P.lyapunov₂ μ)

/-- The Oseledets filtration `ℝ² = V_𝐢^0 ⊋ V_𝐢^1 ⊋ V_𝐢^2 = {0}` of `sec:lyapunov_exponents`,
with `V_𝐢^1` given by `eq:V_lyapunov`. Indices above `2` repeat `{0}`. -/
noncomputable def oseledets (μ : Measure (ℤ → ι)) (x : ℤ → ι) (i : ℕ) : Set (Fin 2 → ℝ) :=
  MatrixTuple.filtration P.mat (P.lyapunov₂ μ) x i

/-- The angle `θ ∈ [0, π)` of the slow direction `(cos θ, sin θ)` spanning `V_𝐢^1` on `Σ'`. -/
noncomputable def slowAngle (μ : Measure (ℤ → ι)) (x : ℤ → ι) : ℝ :=
  MatrixTuple.slowAngle P.mat (P.lyapunov₁ μ) (P.lyapunov₂ μ) x

/-- `Σ'` is saturated with respect to the past (tex lines 1540 to 1541). -/
theorem mem_SigmaPrime_of_samePast (μ : Measure (ℤ → ι)) {x y : ℤ → ι} (h : SamePast x y)
    (hx : x ∈ P.SigmaPrime μ) : y ∈ P.SigmaPrime μ :=
  MatrixTuple.mem_regularSet_of_samePast h hx

/-- `σ(Σ') = Σ'` (tex line 1521). -/
theorem shift_mem_SigmaPrime_iff (μ : Measure (ℤ → ι)) (x : ℤ → ι) :
    shift 1 x ∈ P.SigmaPrime μ ↔ x ∈ P.SigmaPrime μ :=
  MatrixTuple.shift_mem_regularSet_iff P.det_ne_zero _ _ x

/-- `σ^{-1}(Σ') = Σ'`. -/
theorem preimage_shift_SigmaPrime (μ : Measure (ℤ → ι)) :
    shift 1 ⁻¹' P.SigmaPrime μ = P.SigmaPrime μ :=
  MatrixTuple.preimage_shift_regularSet P.det_ne_zero _ _

/-- The filtration depends only on the past. -/
theorem oseledets_congr (μ : Measure (ℤ → ι)) {x y : ℤ → ι} (h : SamePast x y) (i : ℕ) :
    P.oseledets μ x i = P.oseledets μ y i :=
  MatrixTuple.filtration_congr h _ i

/-- On `Σ'`, `V_𝐢^1` is the line spanned by `(cos θ, sin θ)`, `θ` the slow angle, that is the
set of vectors `v` with `cross (cos θ, sin θ) v = 0`. -/
theorem oseledets_one_eq (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    {x : ℤ → ι} (hx : x ∈ P.SigmaPrime μ) :
    P.oseledets μ x 1 = {v | MatrixTuple.cross (MatrixTuple.dirVec (P.slowAngle μ x)) v = 0} :=
  MatrixTuple.slowLine_eq_cross hlt hx

/-- The slow angle depends only on the past. -/
theorem slowAngle_congr (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    {x y : ℤ → ι} (h : SamePast x y) : P.slowAngle μ x = P.slowAngle μ y :=
  MatrixTuple.slowAngle_congr hlt h

/-- On `Σ'`, each `V_𝐢^i` is a linear subspace: it contains `0` and is closed under
subtraction. -/
theorem sub_mem_oseledets (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    {x : ℤ → ι} (hx : x ∈ P.SigmaPrime μ) (i : ℕ) {v w : Fin 2 → ℝ}
    (hv : v ∈ P.oseledets μ x i) (hw : w ∈ P.oseledets μ x i) :
    v - w ∈ P.oseledets μ x i := by
  rcases i with _ | _ | i
  · trivial
  · rw [P.oseledets_one_eq μ hlt hx] at hv hw ⊢
    simp only [mem_ofPred_eq, MatrixTuple.cross, Pi.sub_apply] at hv hw ⊢
    linarith
  · change v = 0 at hv
    change w = 0 at hw
    change v - w = 0
    rw [hv, hw, sub_zero]

end Oseledets

section Measurability

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- `Σ'` is Borel (tex line 1521), when `λ_2(𝖠, μ) < λ_1(𝖠, μ)`. -/
theorem measurableSet_SigmaPrime (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    MeasurableSet (P.SigmaPrime μ) :=
  MatrixTuple.measurableSet_regularSet P.det_ne_zero hlt

/-- The slow angle is a Borel function, when `λ_2(𝖠, μ) < λ_1(𝖠, μ)`. -/
theorem measurable_slowAngle (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    Measurable (P.slowAngle μ) :=
  MatrixTuple.measurable_slowAngle P.det_ne_zero hlt

end Measurability

/-! ### The partitions of `Σ'` -/

section Partitions

variable [MeasurableSpace ι]

/-- The partitions `ξ_0, ξ_1, ξ_2` of `Σ'` (`sec:entropies`, tex lines 1779 to 1784):
`ξ_i(𝐢) = {𝐣 ∈ Σ' : 𝐣^- = 𝐢^-, π(𝐣) - π(𝐢) ∈ V_𝐢^i}`, extended to `Σ` by the atom `Σ ∖ Σ'`.
Indices above `2` repeat `ξ_2`. -/
noncomputable def xi (μ : Measure (ℤ → ι)) (i : ℕ) : (ℤ → ι) → Set (ℤ → ι) :=
  atomsOn (P.SigmaPrime μ) fun x =>
    {y | SamePast y x ∧ toVec (P.proj y - P.proj x) ∈ P.oseledets μ x i}

/-- The partition `ξ_1^⊥` of `Σ'` (`sec:entropies`, tex lines 1785 to 1788):
`ξ_1^⊥(𝐢) = {𝐣 ∈ Σ' : 𝐣^- = 𝐢^-, π(𝐣) - π(𝐢) ⊥ V_𝐢^1}`, extended to `Σ` by the atom
`Σ ∖ Σ'`. Orthogonality is for the Euclidean inner product, the dot product of coordinate
vectors. -/
noncomputable def xiPerp (μ : Measure (ℤ → ι)) : (ℤ → ι) → Set (ℤ → ι) :=
  atomsOn (P.SigmaPrime μ) fun x =>
    {y | SamePast y x ∧ ∀ w ∈ P.oseledets μ x 1, toVec (P.proj y - P.proj x) ⬝ᵥ w = 0}

/-- Every point lies in its own atom of `ξ_i`. -/
theorem mem_xi_self (μ : Measure (ℤ → ι)) (i : ℕ) (x : ℤ → ι) : x ∈ P.xi μ i x := by
  unfold xi
  by_cases hx : x ∈ P.SigmaPrime μ
  · rw [atomsOn_of_mem hx]
    refine ⟨⟨SamePast.refl x, ?_⟩, hx⟩
    rw [sub_self, toVec_zero]
    exact MatrixTuple.zero_mem_filtration _ _ i
  · rw [atomsOn_of_notMem hx]
    exact hx

/-- Every point lies in its own atom of `ξ_1^⊥`. -/
theorem mem_xiPerp_self (μ : Measure (ℤ → ι)) (x : ℤ → ι) : x ∈ P.xiPerp μ x := by
  unfold xiPerp
  by_cases hx : x ∈ P.SigmaPrime μ
  · rw [atomsOn_of_mem hx]
    refine ⟨⟨SamePast.refl x, fun w _ => ?_⟩, hx⟩
    rw [sub_self, toVec_zero, zero_dotProduct]
  · rw [atomsOn_of_notMem hx]
    exact hx

/-- `ξ_i` is a partition: the atom of a point of `ξ_i(𝐢)` is `ξ_i(𝐢)`. This uses that `Σ'` and
`V_𝐢^i` depend only on the past and that `V_𝐢^i` is a linear subspace on `Σ'`. -/
theorem xi_eq_of_mem (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) (i : ℕ)
    {x y : ℤ → ι} (h : y ∈ P.xi μ i x) : P.xi μ i y = P.xi μ i x := by
  unfold xi at h ⊢
  by_cases hx : x ∈ P.SigmaPrime μ
  · rw [atomsOn_of_mem hx] at h
    obtain ⟨⟨hp, hv⟩, hy⟩ := h
    rw [atomsOn_of_mem hx, atomsOn_of_mem hy, P.oseledets_congr μ hp]
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hzp, hzv⟩, hz⟩
      refine ⟨⟨hzp.trans hp, ?_⟩, hz⟩
      have := P.sub_mem_oseledets μ hlt hx i hzv
        (P.sub_mem_oseledets μ hlt hx i (MatrixTuple.zero_mem_filtration _ _ i) hv)
      rwa [zero_sub, sub_neg_eq_add, ← toVec_add, sub_add_sub_cancel] at this
    · rintro ⟨⟨hzp, hzv⟩, hz⟩
      refine ⟨⟨hzp.trans hp.symm, ?_⟩, hz⟩
      have := P.sub_mem_oseledets μ hlt hx i hzv hv
      rwa [← toVec_sub, sub_sub_sub_cancel_right] at this
  · rw [atomsOn_of_notMem hx] at h
    rw [atomsOn_of_notMem hx, atomsOn_of_notMem h]

/-- `ξ_2(𝐢) ⊆ ξ_1(𝐢) ⊆ ξ_0(𝐢)` (`sec:entropies`, tex line 1794). -/
theorem xi_succ_subset (μ : Measure (ℤ → ι)) (i : ℕ) (x : ℤ → ι) :
    P.xi μ (i + 1) x ⊆ P.xi μ i x := by
  unfold xi
  by_cases hx : x ∈ P.SigmaPrime μ
  · rw [atomsOn_of_mem hx, atomsOn_of_mem hx]
    rintro y ⟨⟨hp, hv⟩, hy⟩
    exact ⟨⟨hp, MatrixTuple.filtration_succ_subset _ _ i hv⟩, hy⟩
  · rw [atomsOn_of_notMem hx, atomsOn_of_notMem hx]

/-- `ξ_2(𝐢) ⊆ ξ_1^⊥(𝐢)` (`sec:entropies`, tex line 1795). -/
theorem xi_two_subset_xiPerp (μ : Measure (ℤ → ι)) (x : ℤ → ι) :
    P.xi μ 2 x ⊆ P.xiPerp μ x := by
  unfold xi xiPerp
  by_cases hx : x ∈ P.SigmaPrime μ
  · rw [atomsOn_of_mem hx, atomsOn_of_mem hx]
    rintro y ⟨⟨hp, hv⟩, hy⟩
    refine ⟨⟨hp, fun w _ => ?_⟩, hy⟩
    change toVec (P.proj y - P.proj x) = 0 at hv
    rw [hv, zero_dotProduct]
  · rw [atomsOn_of_notMem hx, atomsOn_of_notMem hx]

/-- `ξ_1^⊥(𝐢) ⊆ ξ_0(𝐢)` (`sec:entropies`, tex line 1795). -/
theorem xiPerp_subset_xi_zero (μ : Measure (ℤ → ι)) (x : ℤ → ι) :
    P.xiPerp μ x ⊆ P.xi μ 0 x := by
  unfold xi xiPerp
  by_cases hx : x ∈ P.SigmaPrime μ
  · rw [atomsOn_of_mem hx, atomsOn_of_mem hx]
    rintro y ⟨⟨hp, -⟩, hy⟩
    exact ⟨⟨hp, trivial⟩, hy⟩
  · rw [atomsOn_of_notMem hx, atomsOn_of_notMem hx]

/-- The atoms of `ξ_i` in `Σ'` have fixed past. -/
theorem xi_subset_samePast (μ : Measure (ℤ → ι)) (i : ℕ) {x : ℤ → ι} (hx : x ∈ P.SigmaPrime μ) :
    P.xi μ i x ⊆ {y | SamePast y x} := by
  rw [xi, atomsOn_of_mem hx]
  exact fun y hy => hy.1.1

end Partitions

/-! ### Measurability of the partitions -/

section MeasurablePartitions

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The linear form `z ↦ cross (cos θ, sin θ) z` vanishing on the slow line, evaluated at the
point `π(𝐢)` with `θ` the slow angle of `𝐢`: a Borel function of `𝐢`. -/
theorem measurable_cross_slowAngle_proj (μ : Measure (ℤ → ι))
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    Measurable fun x =>
      MatrixTuple.cross (MatrixTuple.dirVec (P.slowAngle μ x)) (toVec (P.proj x)) := by
  have h := P.measurable_slowAngle μ hlt
  have hp := P.measurable_proj
  simp only [MatrixTuple.cross, MatrixTuple.dirVec, toVec, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  exact ((Real.measurable_cos.comp h).mul (measurable_snd.comp hp)).sub
    ((Real.measurable_sin.comp h).mul (measurable_fst.comp hp))

/-- The dot product of `π(𝐢)` with the slow direction `(cos θ, sin θ)`: a Borel function of
`𝐢`. -/
theorem measurable_dot_slowAngle_proj (μ : Measure (ℤ → ι))
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    Measurable fun x => toVec (P.proj x) ⬝ᵥ MatrixTuple.dirVec (P.slowAngle μ x) := by
  have h := P.measurable_slowAngle μ hlt
  have hp := P.measurable_proj
  simp only [dotProduct, Fin.sum_univ_two, MatrixTuple.dirVec, toVec, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  exact ((measurable_fst.comp hp).mul (Real.measurable_cos.comp h)).add
    ((measurable_snd.comp hp).mul (Real.measurable_sin.comp h))

/-- Feng, *Dimension of invariant measures for affine iterated function systems*, Duke Math. J.
172 (2023), Lemma 4.2, for a planar self-affine system (`sec:entropies`, tex lines 1789 to 1790):
`ξ_0, ξ_1, ξ_2` are measurable partitions, being the fibres of `𝐢 ↦ 𝐢^-`,
`𝐢 ↦ (𝐢^-, V_𝐢^1 + π(𝐢))` and `𝐢 ↦ (𝐢^-, π(𝐢))` on `Σ'`. The affine line `V_𝐢^1 + π(𝐢)` is
recorded by the slow angle, which depends only on the past, and the value at `π(𝐢)` of the
linear form vanishing on `V_𝐢^1`. -/
theorem isMeasurablePartition_xi (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    (i : ℕ) : IsMeasurablePartition (P.xi μ i) := by
  have hD := P.measurableSet_SigmaPrime μ hlt
  unfold xi
  rcases i with _ | _ | i
  · refine isMeasurablePartition_atomsOn hD measurable_past fun x _ y _ => ?_
    simp [oseledets, past_eq_iff]
  · refine isMeasurablePartition_atomsOn hD
      (measurable_past.prodMk (P.measurable_cross_slowAngle_proj μ hlt)) fun x hx y _ => ?_
    simp only [mem_ofPred_eq, Prod.mk.injEq, past_eq_iff, P.oseledets_one_eq μ hlt hx]
    constructor
    · rintro ⟨hp, h⟩
      refine ⟨hp, ?_⟩
      rw [P.slowAngle_congr μ hlt hp]
      simp only [MatrixTuple.cross, toVec_sub, Pi.sub_apply] at h ⊢
      linarith
    · rintro ⟨hp, h⟩
      refine ⟨hp, ?_⟩
      rw [P.slowAngle_congr μ hlt hp] at h
      simp only [MatrixTuple.cross, toVec_sub, Pi.sub_apply] at h ⊢
      linarith
  · refine isMeasurablePartition_atomsOn hD (measurable_past.prodMk P.measurable_proj)
      fun x _ y _ => ?_
    simp only [mem_ofPred_eq, Prod.mk.injEq, past_eq_iff, oseledets,
      MatrixTuple.filtration_add_two, mem_singleton_iff, toVec_sub, sub_eq_zero]
    exact and_congr_right fun _ => toVec_injective.eq_iff

omit [Fintype ι] [MeasurableSingletonClass ι] in
/-- On `Σ'`, orthogonality to `V_𝐢^1` is orthogonality to the slow direction. -/
theorem forall_dotProduct_oseledets_iff (μ : Measure (ℤ → ι))
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) {x : ℤ → ι} (hx : x ∈ P.SigmaPrime μ)
    (z : Fin 2 → ℝ) :
    (∀ w ∈ P.oseledets μ x 1, z ⬝ᵥ w = 0) ↔
      z ⬝ᵥ MatrixTuple.dirVec (P.slowAngle μ x) = 0 := by
  rw [P.oseledets_one_eq μ hlt hx]
  constructor
  · intro h
    refine h _ ?_
    simp only [mem_ofPred_eq, MatrixTuple.cross]
    ring
  · intro h w hw
    have hu := MatrixTuple.dirVec_ne_zero (P.slowAngle μ x)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1
      ((MatrixTuple.mem_span_iff_cross hu w).2 hw)
    rw [dotProduct_smul, h, smul_zero]

/-- `ξ_1^⊥` is a measurable partition: "the same argument" as Feng, Lemma 4.2 (`sec:entropies`,
tex line 1790), with the dot product with the slow direction in place of the linear form
vanishing on `V_𝐢^1`. -/
theorem isMeasurablePartition_xiPerp (μ : Measure (ℤ → ι))
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) : IsMeasurablePartition (P.xiPerp μ) := by
  unfold xiPerp
  refine isMeasurablePartition_atomsOn (P.measurableSet_SigmaPrime μ hlt)
    (measurable_past.prodMk (P.measurable_dot_slowAngle_proj μ hlt)) fun x hx y _ => ?_
  simp only [mem_ofPred_eq, Prod.mk.injEq, past_eq_iff]
  rw [P.forall_dotProduct_oseledets_iff μ hlt hx]
  simp only [toVec_sub, sub_dotProduct, sub_eq_zero]
  constructor
  · rintro ⟨hp, h⟩
    exact ⟨hp, by rw [P.slowAngle_congr μ hlt hp, h]⟩
  · rintro ⟨hp, h⟩
    rw [P.slowAngle_congr μ hlt hp] at h
    exact ⟨hp, h⟩

end MeasurablePartitions

/-! ### The entropies of `sec:entropies` -/

section Entropies

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The `i`-dimensional entropy `h_i(μ) = H_μ(𝒫 | \widehat{ξ}_i)` (`sec:entropies`, tex lines
1891 to 1897). -/
noncomputable def dimEntropy (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] (i : ℕ) : ℝ :=
  condEntropy μ (P.xi μ i)

/-- The pointwise `i`-dimensional entropy `h_i(μ, 𝐢) = E_μ(I_μ(𝒫 | \widehat{ξ}_i) | ℐ)(𝐢)`
(`sec:entropies`, tex lines 1805 to 1811), determined up to a `μ`-null set. -/
noncomputable def dimEntropyAt (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] (i : ℕ) :
    (ℤ → ι) → ℝ :=
  localEntropy μ (P.xi μ i)

/-- `h_i(μ) = ∫ h_i(μ, 𝐢) dμ(𝐢)` (`sec:entropies`, tex lines 1813 to 1817). -/
theorem integral_dimEntropyAt (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] (i : ℕ) :
    ∫ x, P.dimEntropyAt μ i x ∂μ = P.dimEntropy μ i :=
  integral_localEntropy μ (P.xi μ i)

/-- `sec:entropies`, tex lines 1901 to 1901: `h_0(μ) = h(μ)`, the Kolmogorov–Sinai entropy, for
every invariant measure `μ` with `λ_2 < λ_1` and `μ(Σ') = 1`: the atoms of `ξ_0` in `Σ'` are the
classes of the relation `𝐢^- = 𝐣^-`. -/
theorem dimEntropy_zero_eq_entropy' (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    (hfull : μ (P.SigmaPrime μ)ᶜ = 0) : P.dimEntropy μ 0 = entropy μ := by
  have e : P.xi μ 0 = atomsOn (P.SigmaPrime μ) fun x => {y | SamePast y x} := by
    unfold xi
    congr 1
    funext x
    ext y
    simp [oseledets]
  rw [dimEntropy, e]
  exact condEntropy_atomsOn_samePast hinv (P.measurableSet_SigmaPrime μ hlt) hfull

end Entropies

end PlanarSystem

end BoxLike
