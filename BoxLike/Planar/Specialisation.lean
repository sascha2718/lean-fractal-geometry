module

/-
The box-like objects of the library are the planar objects of a box-like system. For
`S : System ι` the planar system `S.toPlanar` has the linear parts `S.mat`; when
`λ_2(𝖠, μ) < λ_1(𝖠, μ)` its set `Σ'` of regular points is the box-like set
`Σ' = Σ^τ ∪ Σ^ω` of `BoxLike/SlowAxis.lean`, its slow line `V_𝐢^1` is the coordinate axis
`slowAxis`, and its partitions `ξ_i`, `ξ_1^⊥` and entropies `h_i(μ)`, `h_i(μ, 𝐢)` are those of
`BoxLike/DimPartitions.lean`, pointwise. The partitions, the entropies, the exponents and the
projection used by the headline results are therefore the specialisations of the general ones of
`thm:feng_entropy_as_limit`, `thm:feng_entropy_zero` and `thm:feng1` (tex lines 1508 to 1554 and
1853 to 1906). This is the observation of `sec:lyapunov_exponents` that for diagonal and
anti-diagonal matrices `V_𝐢^1` is a coordinate axis (tex lines 1537 to 1539).

* `norm_fin_two`: the supremum norm of a planar vector.
* `System.norm_pastProd_e1`, `System.norm_pastProd_e2`,
  `System.hasPastRate_e1_iff`, `System.hasPastRate_e2_iff`: the growth of the basis vectors is
  the growth of `|g'|` along `τ(𝐢)` and `ω(𝐢)` (`thm:matrix_products_g_derivatives`).
* `MatrixTuple.le_rate_of_le`, `System.le_rate_e1`, `System.le_rate_e2`: a vector with a
  non-zero `j`-th coordinate grows at least as fast as the basis vector `e_j`.
* `System.toPlanar_lyapunov₁`, `System.toPlanar_lyapunov₂`: the exponents.
* `System.isRegularWith_of_mem_SigmaTau`, `System.isRegularWith_of_mem_SigmaOmega`,
  `System.toPlanar_SigmaPrime`: the two descriptions of `Σ'` agree.
* `System.toVec_mem_toPlanar_oseledets_iff`: the filtrations agree on `Σ'`.
* `System.toPlanar_xi`, `System.toPlanar_xiPerp`: the partitions agree.
* `System.toPlanar_dimEntropy`, `System.toPlanar_dimEntropyAt`: the entropies agree.
* `System.toPlanar_slowAngle_of_mem_SigmaTau`, `System.toPlanar_slowAngle_of_mem_SigmaOmega`:
  the slow direction is the `y`-axis on `Σ^τ` and the `x`-axis on `Σ^ω`.
-/
public import BoxLike.Planar.Partitions
public import BoxLike.Classification
public import BoxLike.SigmaMeasure

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set Matrix
open scoped Real

universe u

/-- The supremum norm of a planar vector is the larger modulus of its two coordinates. -/
theorem norm_fin_two (v : Fin 2 → ℝ) : ‖v‖ = max |v 0| |v 1| := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (le_max_of_le_left (abs_nonneg _))).2
    fun j => ?_) (max_le (norm_le_pi_norm v 0) (norm_le_pi_norm v 1))
  fin_cases j
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- A vector with a vanishing coordinate has supremum norm `|v_0| + |v_1|`. -/
theorem norm_fin_two_of_or {v : Fin 2 → ℝ} (h : v 0 = 0 ∨ v 1 = 0) : ‖v‖ = |v 0| + |v 1| := by
  rw [norm_fin_two]
  rcases h with h | h <;> simp [h]

/-- The action of a diagonal matrix. -/
theorem boxMat_zero_mulVec (a b : ℝ) (u : Fin 2 → ℝ) : boxMat 0 a b *ᵥ u = ![a * u 0, b * u 1] := by
  ext j; fin_cases j <;> simp [mulVec, dotProduct, Fin.sum_univ_two]

/-- The action of an anti-diagonal matrix. -/
theorem boxMat_one_mulVec (a b : ℝ) (u : Fin 2 → ℝ) : boxMat 1 a b *ᵥ u = ![a * u 1, b * u 0] := by
  ext j; fin_cases j <;> simp [mulVec, dotProduct, Fin.sum_univ_two]

/-- For a diagonal or anti-diagonal matrix `M`, `|M u| ≥ |u_0| |M e_1|` and
`|M u| ≥ |u_1| |M e_2|`: the images of the basis vectors lie on different axes. -/
theorem le_norm_boxMat_mulVec (c : ZMod 2) (a b : ℝ) (u : Fin 2 → ℝ) :
    |u 0| * ‖boxMat c a b *ᵥ ![1, 0]‖ ≤ ‖boxMat c a b *ᵥ u‖ ∧
      |u 1| * ‖boxMat c a b *ᵥ ![0, 1]‖ ≤ ‖boxMat c a b *ᵥ u‖ := by
  rcases zmod_two_cases c with rfl | rfl
  · simp only [boxMat_zero_mulVec, norm_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero, abs_zero,
      abs_mul]
    rw [max_eq_left (abs_nonneg a), max_eq_right (abs_nonneg b)]
    exact ⟨(le_of_eq (mul_comm _ _)).trans (le_max_left _ _),
      (le_of_eq (mul_comm _ _)).trans (le_max_right _ _)⟩
  · simp only [boxMat_one_mulVec, norm_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero, abs_zero,
      abs_mul]
    rw [max_eq_right (abs_nonneg b), max_eq_left (abs_nonneg a)]
    exact ⟨(le_of_eq (mul_comm _ _)).trans (le_max_right _ _),
      (le_of_eq (mul_comm _ _)).trans (le_max_left _ _)⟩

/-- If `|c| |M_n(𝐢) e| ≤ |M_n(𝐢) u|` for every `n`, with `c ≠ 0` and `e ≠ 0`, then the backward
rate of `e` is at most that of `u`. -/
theorem MatrixTuple.le_rate_of_le {ι : Type*} {A : ι → Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ∀ i, (A i).det ≠ 0) {x : ℤ → ι} {u e : Fin 2 → ℝ} {c l l' : ℝ} (hc : c ≠ 0)
    (he0 : e ≠ 0)
    (hle : ∀ n, |c| * ‖MatrixTuple.pastProd A x n *ᵥ e‖ ≤ ‖MatrixTuple.pastProd A x n *ᵥ u‖)
    (hu : MatrixTuple.HasPastRate A x u l) (he : MatrixTuple.HasPastRate A x e l') :
    l' ≤ l := by
  have hpos : ∀ n, 0 < ‖MatrixTuple.pastProd A x n *ᵥ e‖ := fun n =>
    MatrixTuple.norm_pastProd_mulVec_pos hA x n he0
  have hg : Tendsto (fun n : ℕ =>
      (Real.log |c| + Real.log ‖MatrixTuple.pastProd A x n *ᵥ e‖) / n) atTop (𝓝 l') :=
    tendsto_div_of_abs_sub_le (abs (Real.log |c|)) (Eventually.of_forall fun n => by simp) he
  refine le_of_tendsto_of_tendsto' hg hu fun n => div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n)
  rw [← Real.log_mul (abs_ne_zero.2 hc) (hpos n).ne']
  exact Real.log_le_log (mul_pos (abs_pos.2 hc) (hpos n)) (hle n)

namespace System

variable {ι : Type u} (S : System ι)

/-! ### Backward growth rates of a box-like tuple -/

/-- The backward products of the planar system of `S` are the products `A_{i_{-n}} ⋯ A_{i_{-1}}`
of `S`. -/
theorem pastProd_eq_matWord (x : ℤ → ι) (n : ℕ) :
    MatrixTuple.pastProd S.mat x n = S.matWord (pastWord x n) := rfl

/-- `|A_{i_{-n}} ⋯ A_{i_{-1}} e_1| = |g'_{τ_{-n}(𝐢) ⋯ τ_{-1}(𝐢)}(0)|`
(`thm:matrix_products_g_derivatives`), with the supremum norm. -/
theorem norm_pastProd_e1 (x : ℤ → ι) (n : ℕ) :
    ‖MatrixTuple.pastProd S.mat x n *ᵥ ![1, 0]‖ = |S.gDeriv (pastWord (tau S.o x) n)| := by
  rw [pastProd_eq_matWord, ← abs_matWord_pastWord_e1]
  refine norm_fin_two_of_or ?_
  rw [matWord_mulVec_e1]
  split_ifs <;> simp

/-- `|A_{i_{-n}} ⋯ A_{i_{-1}} e_2| = |g'_{ω_{-n}(𝐢) ⋯ ω_{-1}(𝐢)}(0)|`
(`thm:matrix_products_g_derivatives`), with the supremum norm. -/
theorem norm_pastProd_e2 (x : ℤ → ι) (n : ℕ) :
    ‖MatrixTuple.pastProd S.mat x n *ᵥ ![0, 1]‖ = |S.gDeriv (pastWord (omega S.o x) n)| := by
  rw [pastProd_eq_matWord, ← abs_matWord_pastWord_e2]
  refine norm_fin_two_of_or ?_
  rw [matWord_mulVec_e2]
  split_ifs <;> simp

/-- The backward rate of `e_1` is the backward rate of `|g'|` along `τ(𝐢)`
(`eq:lyapunov_exponent_gsystem`). -/
theorem hasPastRate_e1_iff (x : ℤ → ι) (l : ℝ) :
    MatrixTuple.HasPastRate S.mat x ![1, 0] l ↔ S.HasBackRate (tau S.o x) l := by
  simp only [MatrixTuple.HasPastRate, HasBackRate, norm_pastProd_e1]

/-- The backward rate of `e_2` is the backward rate of `|g'|` along `ω(𝐢)`
(`eq:lyapunov_exponent_gsystem`). -/
theorem hasPastRate_e2_iff (x : ℤ → ι) (l : ℝ) :
    MatrixTuple.HasPastRate S.mat x ![0, 1] l ↔ S.HasBackRate (omega S.o x) l := by
  simp only [MatrixTuple.HasPastRate, HasBackRate, norm_pastProd_e2]

/-- A vector `u` with `u_0 ≠ 0` grows backwards at least as fast as `e_1`. -/
theorem le_rate_e1 {x : ℤ → ι} {u : Fin 2 → ℝ} {l l' : ℝ}
    (hu : MatrixTuple.HasPastRate S.mat x u l) (hj : u 0 ≠ 0)
    (he : MatrixTuple.HasPastRate S.mat x ![1, 0] l') : l' ≤ l := by
  refine MatrixTuple.le_rate_of_le (A := S.mat) S.toPlanar.det_ne_zero hj (by simp)
    (fun n => ?_) hu he
  rw [pastProd_eq_matWord, matWord_eq]
  exact (le_norm_boxMat_mulVec _ _ _ u).1

/-- A vector `u` with `u_1 ≠ 0` grows backwards at least as fast as `e_2`. -/
theorem le_rate_e2 {x : ℤ → ι} {u : Fin 2 → ℝ} {l l' : ℝ}
    (hu : MatrixTuple.HasPastRate S.mat x u l) (hj : u 1 ≠ 0)
    (he : MatrixTuple.HasPastRate S.mat x ![0, 1] l') : l' ≤ l := by
  refine MatrixTuple.le_rate_of_le (A := S.mat) S.toPlanar.det_ne_zero hj (by simp)
    (fun n => ?_) hu he
  rw [pastProd_eq_matWord, matWord_eq]
  exact (le_norm_boxMat_mulVec _ _ _ u).2

/-! ### The exponents and `Σ'` -/

variable [MeasurableSpace ι]

/-- `λ_1(𝖠, μ)` of the planar system of `S` is `λ_1(𝖠, μ)` of `S`. -/
@[simp] theorem toPlanar_lyapunov₁ (μ : Measure (ℤ → ι)) :
    S.toPlanar.lyapunov₁ μ = S.lyapunov₁ μ := rfl

/-- `λ_2(𝖠, μ)` of the planar system of `S` is `λ_2(𝖠, μ)` of `S`. -/
@[simp] theorem toPlanar_lyapunov₂ (μ : Measure (ℤ → ι)) :
    S.toPlanar.lyapunov₂ μ = S.lyapunov₂ μ := rfl

/-- On `Σ^τ` the planar system is regular with slow line the `y`-axis. -/
theorem isRegularWith_of_mem_SigmaTau (μ : Measure (ℤ → ι)) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ)
    {x : ℤ → ι} (hx : x ∈ S.SigmaTau μ) :
    MatrixTuple.IsRegularWith (A := S.mat) (S.lyapunov₁ μ) (S.lyapunov₂ μ) x ![0, 1] :=
  MatrixTuple.isRegularWith_of S.toPlanar.det_ne_zero hlt (by simp) (by simp)
    ((S.hasPastRate_e2_iff x _).2 hx.2) ((S.hasPastRate_e1_iff x _).2 hx.1)

/-- On `Σ^ω` the planar system is regular with slow line the `x`-axis. -/
theorem isRegularWith_of_mem_SigmaOmega (μ : Measure (ℤ → ι))
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) {x : ℤ → ι} (hx : x ∈ S.SigmaOmega μ) :
    MatrixTuple.IsRegularWith (A := S.mat) (S.lyapunov₁ μ) (S.lyapunov₂ μ) x ![1, 0] :=
  MatrixTuple.isRegularWith_of S.toPlanar.det_ne_zero hlt (by simp) (by simp)
    ((S.hasPastRate_e1_iff x _).2 hx.1) ((S.hasPastRate_e2_iff x _).2 hx.2)

/-- `sec:lyapunov_exponents`, tex lines 1537 to 1553: for a box-like system with
`λ_2(𝖠, μ) < λ_1(𝖠, μ)`, the set `Σ'` of the points at which the Oseledets properties hold is
the box-like set `Σ' = Σ^τ ∪ Σ^ω` of sequences for which the two backward coordinate growth
rates are `λ_1(𝖠, μ)` and `λ_2(𝖠, μ)` in either order. -/
theorem toPlanar_SigmaPrime (μ : Measure (ℤ → ι)) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) :
    S.toPlanar.SigmaPrime μ = S.SigmaPrime μ := by
  have hA := S.toPlanar.det_ne_zero
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu0, hu⟩ := hx
    have hrate : ∀ v ∈ Submodule.span ℝ {u}, v ≠ 0 →
        MatrixTuple.HasPastRate S.mat x v (S.lyapunov₂ μ) := fun v hv hv0 => (hu v).1 hv hv0
    have hrate' : ∀ v ∉ Submodule.span ℝ {u},
        MatrixTuple.HasPastRate S.mat x v (S.lyapunov₁ μ) := fun v hv => (hu v).2 hv
    have hu2 : MatrixTuple.HasPastRate S.mat x u (S.lyapunov₂ μ) :=
      hrate u (Submodule.mem_span_singleton_self u) hu0
    -- One basis vector lies on the slow line: otherwise both grow at the rate `λ_1`, and so
    -- does `u`.
    have hcross := MatrixTuple.mem_span_iff_cross hu0
    by_cases h1 : (![0, 1] : Fin 2 → ℝ) ∈ Submodule.span ℝ {u}
    · have h0 : (![1, 0] : Fin 2 → ℝ) ∉ Submodule.span ℝ {u} := by
        intro h0
        rw [hcross] at h0 h1
        apply hu0
        ext j; fin_cases j
        · simpa [MatrixTuple.cross] using h1
        · simpa [MatrixTuple.cross] using h0
      refine Or.inl ⟨(S.hasPastRate_e1_iff x _).1 (hrate' _ h0),
        (S.hasPastRate_e2_iff x _).1 (hrate _ h1 (by simp))⟩
    · by_cases h0 : (![1, 0] : Fin 2 → ℝ) ∈ Submodule.span ℝ {u}
      · exact Or.inr ⟨(S.hasPastRate_e1_iff x _).1 (hrate _ h0 (by simp)),
          (S.hasPastRate_e2_iff x _).1 (hrate' _ h1)⟩
      · exfalso
        by_cases hj : u 0 = 0
        · have hj1 : u 1 ≠ 0 := fun h => hu0 (by ext j; fin_cases j <;> simp [hj, h])
          have := S.le_rate_e2 hu2 hj1 (hrate' _ h1)
          linarith
        · have := S.le_rate_e1 hu2 hj (hrate' _ h0)
          linarith
  · rintro (hx | hx)
    · exact ⟨_, S.isRegularWith_of_mem_SigmaTau μ hlt hx⟩
    · exact ⟨_, S.isRegularWith_of_mem_SigmaOmega μ hlt hx⟩

/-- Oseledets' theorem for a box-like tuple (`sec:lyapunov_exponents`, tex lines 1508 to 1523):
for an ergodic `μ` with `λ_2(𝖠, μ) < λ_1(𝖠, μ)`, the set `Σ'` of the planar system of `S` has full
measure. It is the box-like `μ(Σ') = 1` of `BoxLike/SigmaMeasure.lean`, proved from Birkhoff's
theorem, through `toPlanar_SigmaPrime`. -/
theorem measure_toPlanar_SigmaPrime_compl [Fintype ι] [MeasurableSingletonClass ι]
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) :
    μ (S.toPlanar.SigmaPrime μ)ᶜ = 0 := by
  rw [S.toPlanar_SigmaPrime μ hlt]
  exact S.measure_SigmaPrime_compl μ hinv herg

/-- On `Σ^τ` the slow direction of the planar system of `S` is the `y`-axis: the slow angle is
`π / 2`. -/
theorem toPlanar_slowAngle_of_mem_SigmaTau (μ : Measure (ℤ → ι))
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) {x : ℤ → ι} (hx : x ∈ S.SigmaTau μ) :
    S.toPlanar.slowAngle μ x = π / 2 := by
  have hreg : x ∈ S.toPlanar.SigmaPrime μ := by
    rw [S.toPlanar_SigmaPrime μ hlt]; exact Or.inl hx
  refine MatrixTuple.slowAngle_eq hlt hreg ⟨by positivity, by linarith [Real.pi_pos]⟩ ?_
  have e : MatrixTuple.dirVec (π / 2) = ![0, 1] := by
    ext j; fin_cases j <;> simp [MatrixTuple.dirVec]
  rw [e]
  exact (S.hasPastRate_e2_iff x _).2 hx.2

/-- On `Σ^ω` the slow direction of the planar system of `S` is the `x`-axis: the slow angle is
`0`. -/
theorem toPlanar_slowAngle_of_mem_SigmaOmega (μ : Measure (ℤ → ι))
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) {x : ℤ → ι} (hx : x ∈ S.SigmaOmega μ) :
    S.toPlanar.slowAngle μ x = 0 := by
  have hreg : x ∈ S.toPlanar.SigmaPrime μ := by
    rw [S.toPlanar_SigmaPrime μ hlt]; exact Or.inr hx
  refine MatrixTuple.slowAngle_eq hlt hreg ⟨le_rfl, Real.pi_pos⟩ ?_
  have e : MatrixTuple.dirVec 0 = ![1, 0] := by
    ext j; fin_cases j <;> simp [MatrixTuple.dirVec]
  rw [e]
  exact (S.hasPastRate_e1_iff x _).2 hx.1

/-- On `Σ'`, the filtration of the planar system of `S` is the box-like filtration of
`BoxLike/SlowAxis.lean`: `V_𝐢^1` is the coordinate axis `slowAxis`. -/
theorem toVec_mem_toPlanar_oseledets_iff (μ : Measure (ℤ → ι))
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) {x : ℤ → ι} (hx : x ∈ S.SigmaPrime μ) (i : ℕ)
    (z : ℝ × ℝ) : toVec z ∈ S.toPlanar.oseledets μ x i ↔ z ∈ S.oseledets μ x i := by
  rcases i with _ | _ | i
  · simp [PlanarSystem.oseledets, oseledets]
  · change toVec z ∈ MatrixTuple.slowLine S.mat (S.lyapunov₂ μ) x ↔ _
    rcases hx with hx | hx
    · rw [MatrixTuple.slowLine_eq_span hlt (S.isRegularWith_of_mem_SigmaTau μ hlt hx),
        SetLike.mem_coe, MatrixTuple.mem_span_iff_cross (by simp)]
      simp [oseledets, slowAxis_of_mem_SigmaTau S μ hx, MatrixTuple.cross,
        show (1 : ZMod 2) + 1 = 0 from by decide]
    · rw [MatrixTuple.slowLine_eq_span hlt (S.isRegularWith_of_mem_SigmaOmega μ hlt hx),
        SetLike.mem_coe, MatrixTuple.mem_span_iff_cross (by simp)]
      simp [oseledets, slowAxis_of_mem_SigmaOmega S μ hlt hx, MatrixTuple.cross]
  · change toVec z = 0 ↔ z = 0
    rw [← toVec_zero]
    exact toVec_injective.eq_iff

/-! ### The partitions and the entropies -/

/-- The partitions `ξ_i` of the planar system of `S` are the box-like partitions `ξ_i` of
`BoxLike/DimPartitions.lean`, for every `i`, when `λ_2(𝖠, μ) < λ_1(𝖠, μ)`. -/
theorem toPlanar_xi [Finite ι] (μ : Measure (ℤ → ι)) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ)
    (i : ℕ) : S.toPlanar.xi μ i = S.xi μ i := by
  unfold PlanarSystem.xi xi
  rw [S.toPlanar_SigmaPrime μ hlt, S.toPlanar_proj]
  funext x
  by_cases hx : x ∈ S.SigmaPrime μ
  · rw [atomsOn_of_mem hx, atomsOn_of_mem hx]
    ext y
    simp only [mem_inter_iff, mem_ofPred_eq, S.toVec_mem_toPlanar_oseledets_iff μ hlt hx]
  · rw [atomsOn_of_notMem hx, atomsOn_of_notMem hx]

/-- The partition `ξ_1^⊥` of the planar system of `S` is the box-like partition `ξ_1^⊥`, when
`λ_2(𝖠, μ) < λ_1(𝖠, μ)`: orthogonality to the slow axis is the vanishing of that coordinate. -/
theorem toPlanar_xiPerp [Finite ι] (μ : Measure (ℤ → ι))
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) : S.toPlanar.xiPerp μ = S.xiPerp μ := by
  unfold PlanarSystem.xiPerp xiPerp
  rw [S.toPlanar_SigmaPrime μ hlt, S.toPlanar_proj]
  funext x
  by_cases hx : x ∈ S.SigmaPrime μ
  · rw [atomsOn_of_mem hx, atomsOn_of_mem hx]
    ext y
    simp only [mem_inter_iff, mem_ofPred_eq]
    refine and_congr_left fun _ => and_congr_right fun _ => ?_
    change (∀ w ∈ MatrixTuple.slowLine S.mat (S.lyapunov₂ μ) x, _) ↔ _
    have key : ∀ (u : Fin 2 → ℝ), u ≠ 0 →
        MatrixTuple.slowLine S.mat (S.lyapunov₂ μ) x = (Submodule.span ℝ {u} : Set _) →
        ((∀ w ∈ MatrixTuple.slowLine S.mat (S.lyapunov₂ μ) x,
          toVec (S.proj y - S.proj x) ⬝ᵥ w = 0) ↔ toVec (S.proj y - S.proj x) ⬝ᵥ u = 0) := by
      intro u hu0 hL
      rw [hL]
      constructor
      · exact fun h => h u (Submodule.mem_span_singleton_self u)
      · intro h w hw
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
        rw [dotProduct_smul, h, smul_zero]
    rcases hx with hx | hx
    · rw [key _ (by simp)
        (MatrixTuple.slowLine_eq_span hlt (S.isRegularWith_of_mem_SigmaTau μ hlt hx)),
        slowAxis_of_mem_SigmaTau S μ hx]
      simp [dotProduct, Fin.sum_univ_two, toVec]
    · rw [key _ (by simp)
        (MatrixTuple.slowLine_eq_span hlt (S.isRegularWith_of_mem_SigmaOmega μ hlt hx)),
        slowAxis_of_mem_SigmaOmega S μ hlt hx]
      simp [dotProduct, Fin.sum_univ_two, toVec]
  · rw [atomsOn_of_notMem hx, atomsOn_of_notMem hx]

variable [Fintype ι] [MeasurableSingletonClass ι]

/-- The entropies `h_i(μ)` of the planar system of `S` are the box-like entropies, when
`λ_2(𝖠, μ) < λ_1(𝖠, μ)`. -/
theorem toPlanar_dimEntropy (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ]
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) (i : ℕ) :
    S.toPlanar.dimEntropy μ i = S.dimEntropy μ i := by
  rw [PlanarSystem.dimEntropy, S.toPlanar_xi μ hlt, dimEntropy]

/-- The pointwise entropies `h_i(μ, 𝐢)` of the planar system of `S` are the box-like pointwise
entropies, when `λ_2(𝖠, μ) < λ_1(𝖠, μ)`. -/
theorem toPlanar_dimEntropyAt (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ]
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) (i : ℕ) :
    S.toPlanar.dimEntropyAt μ i = S.dimEntropyAt μ i := by
  rw [PlanarSystem.dimEntropyAt, S.toPlanar_xi μ hlt, dimEntropyAt]

end System

end BoxLike
