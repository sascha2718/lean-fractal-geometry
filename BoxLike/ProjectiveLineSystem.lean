module

/-
The second part of `thm:feng1` (tex lines 2581 to 2594) from its first part. Both parts are
cases of Feng's Theorems 1.2 and 1.3 (Duke Math. J. 172 (2023), arXiv:1901.01691v2): the first
for planar systems, the second for the projective system `Ψ` on `ℝ` of a box-like system. The
second follows from the first applied to the degenerate planar system
`z ↦ diag(g'_j, g'_j / 2) z + (g_j(0), 0)` over the alphabet `{1, …, 2N} = ι × ZMod 2` of `Ψ`.
Its attractor lies on the horizontal axis and its projection is `𝐣 ↦ (\overline{π}(𝐣), 0)`; its
Lyapunov exponents are `\overline{λ}(𝖠, ν)` and `\overline{λ}(𝖠, ν) - log 2` for every
invariant measure `ν`; its slow subspace is vertical at every point of its set `Σ'`, so that
its partitions `ξ_1` and `ξ_2` both fix the past and `\overline{π}`; and its partitions `ξ_i`
agree with the partitions `\overline{ξ}_i` of `Σ_Z` modulo `ν`-null sets when `ν` is carried by
`Σ_Z`. The planar formula then reads
`dim \overline{π}_*ν = (\overline{h}_1(ν) - \overline{h}_0(ν)) / \overline{λ}(𝖠, ν)`. Neither
rotations nor proximality enter.

* `isExactDim_of_map_prodMk_zero`: exactness on the line from exactness of the image under
  `t ↦ (t, 0)`.
* `System.projectiveLineSystem`: the planar system `diag(g'_j, g'_j / 2) z + (g_j(0), 0)`.
* `System.proj_projectiveLineSystem`, `System.map_proj_projectiveLineSystem`: its projection is
  `𝐣 ↦ (\overline{π}(𝐣), 0)`.
* `System.lyapunov₁_projectiveLineSystem`, `System.lyapunov₂_projectiveLineSystem`: its
  exponents `\overline{λ}(𝖠, ν)` and `\overline{λ}(𝖠, ν) - log 2`.
* `System.sigmaOmega_projectiveLineSystem`, `System.slowAxis_projectiveLineSystem`: its set
  `Σ^ω` is empty and its slow axis is vertical on `Σ'`.
* `System.xi_two_projectiveLineSystem`: its partitions `ξ_2 = ξ_1`.
* `System.dimEntropy_projectiveLineSystem`: its entropies are `h_i = \overline{h}_i`.
* `System.isExactDim_map_projBar_of_fengLedrappierYoung`: the scalar formula for every box-like
  system, from `FengLedrappierYoung`.
* `fengLedrappierYoungBar_of_fengLedrappierYoung`: `FengLedrappierYoung` implies
  `FengLedrappierYoungBar`.
-/
public import BoxLike.LiteratureFeng
public import BoxLike.MainTwoProse.ScalarFeng
public import BoxLike.OseledetsBridge

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Metric
open scoped Matrix.Norms.L2Operator

universe u

/-- The converse of `isExactDim_map_prodMk_zero`: a measure on the line whose image under
`t ↦ (t, 0)` is exact-dimensional is exact-dimensional with the same dimension (`thm:feng1`,
second part, from the first). -/
theorem isExactDim_of_map_prodMk_zero {m : Measure ℝ} {d : ℝ}
    (h : IsExactDim (m.map fun t : ℝ => (t, (0 : ℝ))) d) : IsExactDim m d := by
  unfold IsExactDim at h ⊢
  rw [measurableEmbedding_prodMk_zero.ae_map_iff] at h
  filter_upwards [h] with t ht
  unfold HasLocalDim at ht ⊢
  refine ht.congr fun r => ?_
  rw [measureReal_def, measureReal_def,
    Measure.map_apply measurableEmbedding_prodMk_zero.measurable measurableSet_closedBall,
    preimage_prodMk_zero_closedBall]

namespace System

/-! ### The planar system of the projective system -/

section Definition

variable {ι : Type*} (S : System ι)

/-- The planar system `z ↦ diag(g'_j, g'_j / 2) z + (g_j(0), 0)` over the alphabet
`{1, …, 2N} = ι × ZMod 2` of the projective system `Ψ` (`thm:feng1`, second part, from the
first): it carries `Ψ` on the horizontal axis. -/
noncomputable def projectiveLineSystem : System (ι × ZMod 2) where
  o _ := 0
  a := S.ratio
  b p := S.ratio p / 2
  v p := (S.trans p, 0)
  a_ne_zero := S.ratio_ne_zero
  b_ne_zero p := div_ne_zero (S.ratio_ne_zero p) two_ne_zero
  abs_a_lt_one := S.abs_ratio_lt_one
  abs_b_lt_one p := by
    rw [abs_div, abs_two]
    have := S.abs_ratio_lt_one p
    linarith [abs_nonneg (S.ratio p)]

/-- The ratio of the symbol `(j, 0)` of the planar system is `g'_j` (`thm:feng1`). -/
@[simp] theorem ratio_projectiveLineSystem_zero (p : ι × ZMod 2) :
    S.projectiveLineSystem.ratio (p, 0) = S.ratio p := rfl

/-- The ratio of the symbol `(j, 1)` of the planar system is `g'_j / 2` (`thm:feng1`). -/
@[simp] theorem ratio_projectiveLineSystem_one (p : ι × ZMod 2) :
    S.projectiveLineSystem.ratio (p, 1) = S.ratio p / 2 := rfl

/-- The translation of the symbol `(j, 0)` of the planar system is `g_j(0)` (`thm:feng1`). -/
@[simp] theorem trans_projectiveLineSystem_zero (p : ι × ZMod 2) :
    S.projectiveLineSystem.trans (p, 0) = S.trans p := rfl

/-- The translation of the symbol `(j, 1)` of the planar system vanishes (`thm:feng1`). -/
@[simp] theorem trans_projectiveLineSystem_one (p : ι × ZMod 2) :
    S.projectiveLineSystem.trans (p, 1) = 0 := rfl

/-- The planar system has no orientation changes (`thm:feng1`). -/
theorem eps_projectiveLineSystem (y : ℤ → ι × ZMod 2) (m : ℤ) :
    eps S.projectiveLineSystem.o y m = 0 := by
  have h := eq_eps_of_succ S.projectiveLineSystem.o y (S := fun _ => 0) rfl fun m => by
    simp [projectiveLineSystem]
  exact (congrFun h m).symm

/-- `τ(𝐣)` keeps every symbol of the planar system on the horizontal axis (`thm:feng1`). -/
theorem tau_projectiveLineSystem (y : ℤ → ι × ZMod 2) :
    tau S.projectiveLineSystem.o y = fun k => (y k, 0) := by
  funext k
  rw [tau_apply, eps_projectiveLineSystem]

/-- `ω(𝐣)` keeps every symbol of the planar system on the vertical axis (`thm:feng1`). -/
theorem omega_projectiveLineSystem (y : ℤ → ι × ZMod 2) :
    omega S.projectiveLineSystem.o y = fun k => (y k, 1) := by
  funext k
  rw [omega_apply, eps_projectiveLineSystem, zero_add]

/-- Along the horizontal axis the derivative of the planar system is `g'` (`thm:feng1`). -/
theorem gDeriv_projectiveLineSystem_map_zero (u : List (ι × ZMod 2)) :
    S.projectiveLineSystem.gDeriv (u.map fun p => (p, 0)) = S.gDeriv u := by
  induction u with
  | nil => simp
  | cons p u ih =>
    rw [List.map_cons, gDeriv_cons, gDeriv_cons, ih, ratio_projectiveLineSystem_zero]

/-- The product of the matrices of a word of the planar system is `diag(g'_𝐮, g'_𝐮 / 2^n)`
(`thm:feng1`). -/
theorem matWord_projectiveLineSystem (u : List (ι × ZMod 2)) :
    S.projectiveLineSystem.matWord u = boxMat 0 (S.gDeriv u) (S.gDeriv u / 2 ^ u.length) := by
  induction u with
  | nil =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | cons p u ih =>
    rw [matWord_cons, ih, mat, boxMat_mul]
    simp only [projectiveLineSystem, add_zero, ite_true, gDeriv_cons, List.length_cons,
      pow_succ']
    congr 1
    ring

/-- `log α_1(A_𝐮) = log |g'_𝐮|` for the planar system (`thm:feng1`). -/
theorem log_norm_matWord_projectiveLineSystem (u : List (ι × ZMod 2)) :
    Real.log ‖S.projectiveLineSystem.matWord u‖ = Real.log |S.gDeriv u| := by
  rw [S.matWord_projectiveLineSystem, norm_boxMat, abs_div, abs_pow, abs_two,
    max_eq_left (div_le_self (abs_nonneg _) (one_le_pow₀ one_le_two))]

/-- `log α_2(A_𝐮) = log |g'_𝐮| - |𝐮| log 2` for the planar system (`thm:feng1`). -/
theorem log_abs_det_div_norm_matWord_projectiveLineSystem (u : List (ι × ZMod 2)) :
    Real.log (|(S.projectiveLineSystem.matWord u).det| / ‖S.projectiveLineSystem.matWord u‖) =
      Real.log |S.gDeriv u| - u.length * Real.log 2 := by
  have hg : |S.gDeriv u| ≠ 0 := abs_ne_zero.2 (S.gDeriv_ne_zero u)
  rw [S.matWord_projectiveLineSystem, norm_boxMat, abs_det_boxMat, abs_div, abs_pow, abs_two,
    max_eq_left (div_le_self (abs_nonneg _) (one_le_pow₀ one_le_two)),
    mul_div_cancel_left₀ _ hg, Real.log_div hg (pow_ne_zero _ two_ne_zero), Real.log_pow]

/-- The projection of the planar system is `𝐣 ↦ (\overline{π}(𝐣), 0)` (`thm:feng1`). -/
theorem proj_projectiveLineSystem (y : ℤ → ι × ZMod 2) :
    S.projectiveLineSystem.proj y = (S.projBar y, 0) := by
  refine Prod.ext ?_ ?_
  · rw [fst_proj, tau_projectiveLineSystem]
    unfold projBar projBarTerm
    congr 1
    funext k
    have e : futureWord (fun k => (y k, (0 : ZMod 2))) k =
        (futureWord y k).map fun p => (p, 0) := by
      simp [futureWord, List.map_map, Function.comp_def]
    rw [e, gDeriv_projectiveLineSystem_map_zero, trans_projectiveLineSystem_zero]
  · rw [snd_proj, omega_projectiveLineSystem]
    unfold projBar projBarTerm
    simp

/-- The backward derivative of the planar system along `τ(𝐣)` is that of `Ψ` along `𝐣`
(`thm:feng1`). -/
theorem gDeriv_pastWord_tau_projectiveLineSystem (y : ℤ → ι × ZMod 2) (n : ℕ) :
    S.projectiveLineSystem.gDeriv (pastWord (tau S.projectiveLineSystem.o y) n) =
      S.gDeriv (pastWord y n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pastWord_succ, gDeriv_cons, ih, pastWord_succ, gDeriv_cons, tau_projectiveLineSystem,
      ratio_projectiveLineSystem_zero]

/-- The backward derivative of the planar system along `ω(𝐣)` is that of `Ψ` along `𝐣`
divided by `2^n` (`thm:feng1`). -/
theorem gDeriv_pastWord_omega_projectiveLineSystem (y : ℤ → ι × ZMod 2) (n : ℕ) :
    S.projectiveLineSystem.gDeriv (pastWord (omega S.projectiveLineSystem.o y) n) =
      S.gDeriv (pastWord y n) / 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pastWord_succ, gDeriv_cons, ih, pastWord_succ, gDeriv_cons, omega_projectiveLineSystem,
      ratio_projectiveLineSystem_one, pow_succ']
    ring

/-- The backward rate of the planar system along `ω(𝐣)` is its rate along `τ(𝐣)` minus `log 2`
(`thm:feng1`). -/
theorem hasBackRate_omega_projectiveLineSystem {y : ℤ → ι × ZMod 2} {l : ℝ}
    (h : S.projectiveLineSystem.HasBackRate (tau S.projectiveLineSystem.o y) l) :
    S.projectiveLineSystem.HasBackRate (omega S.projectiveLineSystem.o y) (l - Real.log 2) := by
  unfold HasBackRate at h ⊢
  refine (h.sub tendsto_const_nhds).congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hg : |S.gDeriv (pastWord y n)| ≠ 0 := abs_ne_zero.2 (S.gDeriv_ne_zero _)
  rw [gDeriv_pastWord_tau_projectiveLineSystem, gDeriv_pastWord_omega_projectiveLineSystem,
    abs_div, abs_pow, abs_two, Real.log_div hg (pow_ne_zero _ two_ne_zero), Real.log_pow]
  field_simp

end Definition

/-! ### The exponents, the slow axis and the partitions -/

section Measure

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {ν : Measure (ℤ → ι × ZMod 2)} [IsProbabilityMeasure ν]

/-- `λ_1 = \overline{λ}(𝖠, ν)` for the planar system and every invariant probability measure
`ν` (`thm:feng1`). -/
theorem lyapunov₁_projectiveLineSystem (hinv : MeasurePreserving (shift 1) ν ν) :
    S.projectiveLineSystem.lyapunov₁ ν = S.lyapBar ν := by
  refine tendsto_nhds_unique (S.projectiveLineSystem.tendsto_lyapunov₁ hinv)
    (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp only [log_norm_matWord_projectiveLineSystem]
  rw [S.integral_log_abs_gDeriv_futureWord hinv, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 hn)]

/-- `λ_2 = \overline{λ}(𝖠, ν) - log 2` for the planar system and every invariant probability
measure `ν` (`thm:feng1`). -/
theorem lyapunov₂_projectiveLineSystem (hinv : MeasurePreserving (shift 1) ν ν) :
    S.projectiveLineSystem.lyapunov₂ ν = S.lyapBar ν - Real.log 2 := by
  refine tendsto_nhds_unique (S.projectiveLineSystem.tendsto_lyapunov₂ hinv)
    (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp only [log_abs_det_div_norm_matWord_projectiveLineSystem, length_futureWord]
  rw [integral_sub (integrable_comp_futureWord (fun w => Real.log |S.gDeriv w|) n)
    (integrable_const _), integral_const, S.integral_log_abs_gDeriv_futureWord hinv]
  simp only [probReal_univ, one_smul]
  field_simp

/-- `λ_2 < λ_1` for the planar system and every invariant probability measure (`thm:feng1`). -/
theorem lyapunov₂_lt_lyapunov₁_projectiveLineSystem (hinv : MeasurePreserving (shift 1) ν ν) :
    S.projectiveLineSystem.lyapunov₂ ν < S.projectiveLineSystem.lyapunov₁ ν := by
  rw [S.lyapunov₁_projectiveLineSystem hinv, S.lyapunov₂_projectiveLineSystem hinv]
  linarith [Real.log_pos one_lt_two]

/-- The set `Σ^ω` of the planar system is empty: along `ω(𝐣)` the backward rate is the rate
along `τ(𝐣)` minus `log 2`, so the two rates cannot be `λ_2` and `λ_1 = λ_2 + log 2` in this
order (`thm:feng1`). -/
theorem sigmaOmega_projectiveLineSystem (hinv : MeasurePreserving (shift 1) ν ν) :
    S.projectiveLineSystem.SigmaOmega ν = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun y hy => ?_
  have h := tendsto_nhds_unique hy.2 (S.hasBackRate_omega_projectiveLineSystem hy.1)
  rw [S.lyapunov₁_projectiveLineSystem hinv, S.lyapunov₂_projectiveLineSystem hinv] at h
  linarith [Real.log_pos one_lt_two]

/-- The slow axis of the planar system is vertical at every point of its set `Σ'`
(`thm:feng1`). -/
theorem slowAxis_projectiveLineSystem (hinv : MeasurePreserving (shift 1) ν ν)
    {y : ℤ → ι × ZMod 2} (hy : y ∈ S.projectiveLineSystem.SigmaPrime ν) :
    S.projectiveLineSystem.slowAxis ν y = 1 := by
  have hy' : y ∈ S.projectiveLineSystem.SigmaTau ν := by
    rcases hy with hy | hy
    · exact hy
    · rw [S.sigmaOmega_projectiveLineSystem hinv] at hy
      exact hy.elim
  simp [slowAxis, hy']

/-- At a point of `Σ'` of the planar system, a difference of projections lies in `V^i` exactly
when `i = 0` or the projections under `\overline{π}` agree (`thm:feng1`). -/
theorem proj_sub_mem_oseledets_projectiveLineSystem (hinv : MeasurePreserving (shift 1) ν ν)
    {y : ℤ → ι × ZMod 2} (hy : y ∈ S.projectiveLineSystem.SigmaPrime ν)
    (z : ℤ → ι × ZMod 2) (i : ℕ) :
    S.projectiveLineSystem.proj z - S.projectiveLineSystem.proj y ∈
        S.projectiveLineSystem.oseledets ν y i ↔ i = 0 ∨ S.projBar z = S.projBar y := by
  rw [mem_oseledets_iff, S.slowAxis_projectiveLineSystem hinv hy,
    show (1 : ZMod 2) + 1 = 0 from by decide, coord_zero, coord_zero,
    S.proj_projectiveLineSystem, S.proj_projectiveLineSystem, Prod.mk.injEq]
  constructor
  · rintro (h | ⟨-, h⟩ | ⟨-, h, -⟩)
    exacts [Or.inl h, Or.inr h, Or.inr h]
  · rintro (h | h)
    · exact Or.inl h
    · rcases i with _ | _ | i
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, h⟩)
      · exact Or.inr (Or.inr ⟨by omega, h, rfl⟩)

/-- The partitions `ξ_2` and `ξ_1` of the planar system agree, since the vertical coordinate of
its coded points vanishes (`thm:feng1`). -/
theorem xi_two_projectiveLineSystem (hinv : MeasurePreserving (shift 1) ν ν) :
    S.projectiveLineSystem.xi ν 2 = S.projectiveLineSystem.xi ν 1 := by
  funext y
  by_cases hy : y ∈ S.projectiveLineSystem.SigmaPrime ν
  · simp only [xi, atomsOn_of_mem hy]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
      S.proj_sub_mem_oseledets_projectiveLineSystem hinv hy]
    simp
  · simp only [xi, atomsOn_of_notMem hy]

/-- At a point `𝐣` of `Σ' ∩ Σ_Z`, the atom `ξ_i(𝐣)` of the planar system and the atom
`\overline{ξ}_i(𝐣)` of `Σ_Z` have the same intersection with `Σ' ∩ Σ_Z` (`thm:feng1`). -/
theorem xi_inter_projectiveLineSystem (hinv : MeasurePreserving (shift 1) ν ν) (i : ℕ)
    {y : ℤ → ι × ZMod 2}
    (hy : y ∈ S.projectiveLineSystem.SigmaPrime ν ∩ subshift S.o) :
    S.projectiveLineSystem.xi ν i y ∩ (S.projectiveLineSystem.SigmaPrime ν ∩ subshift S.o) =
      S.xiBar i y ∩ (S.projectiveLineSystem.SigmaPrime ν ∩ subshift S.o) := by
  ext z
  rcases i with _ | i
  · simp only [xi, xiBar, atomsOn_of_mem hy.1, atomsOn_of_mem hy.2, Set.mem_inter_iff,
      Set.mem_ofPred_eq, S.proj_sub_mem_oseledets_projectiveLineSystem hinv hy.1]
    tauto
  · simp only [xi, xiBar, atomsOn_of_mem hy.1, atomsOn_of_mem hy.2, Set.mem_inter_iff,
      Set.mem_ofPred_eq, S.proj_sub_mem_oseledets_projectiveLineSystem hinv hy.1]
    simp only [Nat.add_one_ne_zero, false_or]
    tauto

/-- The entropies of the planar system are those of `Ψ`: `h_i(ν) = \overline{h}_i(ν)` for an
ergodic invariant probability measure `ν` carried by `Σ_Z` (`thm:feng1`). The partitions agree
on the set `Σ' ∩ Σ_Z` of full measure, so their conditional measures agree almost everywhere
(`condMeas_ae_eq_of_cut`). -/
theorem dimEntropy_projectiveLineSystem (hinv : MeasurePreserving (shift 1) ν ν)
    (herg : Ergodic (shift 1) ν) (hsupp : ν (subshift S.o)ᶜ = 0) (i : ℕ) :
    S.projectiveLineSystem.dimEntropy ν i = S.dimEntropyBar ν i := by
  set D := S.projectiveLineSystem.SigmaPrime ν ∩ subshift S.o with hD_def
  have hD : MeasurableSet D :=
    (S.projectiveLineSystem.measurableSet_SigmaPrime ν).inter (measurableSet_subshift S.o)
  have hD0 : ν Dᶜ = 0 := by
    rw [hD_def, Set.compl_inter]
    exact measure_union_null (S.projectiveLineSystem.measure_SigmaPrime_compl ν hinv herg) hsupp
  have h₁ := condMeas_ae_eq_of_cut ν (S.isMeasurablePartition_xiBar i) hD hD0
    (ξ' := atomsOn D (S.xiBar i)) (fun y hy => atomsOn_of_mem hy)
    (fun y hy => (atomsOn_of_notMem hy).subset)
  have h₂ := condMeas_ae_eq_of_cut ν (S.projectiveLineSystem.isMeasurablePartition_xi ν i) hD
    hD0 (ξ' := atomsOn D (S.xiBar i))
    (fun y hy => by rw [atomsOn_of_mem hy, S.xi_inter_projectiveLineSystem hinv i hy])
    (fun y hy => (atomsOn_of_notMem hy).subset)
  unfold dimEntropy dimEntropyBar
  rw [← condEntropy_eq_of_condMeas h₂, condEntropy_eq_of_condMeas h₁]

/-- The image of `ν` under the projection of the planar system is the image of
`\overline{π}_*ν` under `t ↦ (t, 0)` (`thm:feng1`). -/
theorem map_proj_projectiveLineSystem (ν : Measure (ℤ → ι × ZMod 2)) :
    ν.map S.projectiveLineSystem.proj =
      (ν.map S.projBar).map fun t : ℝ => (t, (0 : ℝ)) := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  rw [Measure.map_map measurableEmbedding_prodMk_zero.measurable hS.measurable_projBar]
  congr 1
  funext y
  exact S.proj_projectiveLineSystem y

end Measure

end System

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- `thm:feng1`, second part, from its first part, for every box-like system: Feng's Theorems 1.2
and 1.3 for planar systems give the scalar formula
`dim \overline{π}_*ν = (\overline{h}_1(ν) - \overline{h}_0(ν)) / \overline{λ}(𝖠, ν)` for the
projective system `Ψ` and every ergodic invariant probability measure `ν` carried by `Σ_Z`,
through the planar system `projectiveLineSystem`, whose projection of `ν` is `\overline{π}_*ν`
on the horizontal axis and whose partitions `ξ_2` and `ξ_1` agree. Neither rotations nor
proximality are assumed.
Depends on: `FengLedrappierYoung`. -/
theorem isExactDim_map_projBar_of_fengLedrappierYoung (hly : FengLedrappierYoung.{u})
    (S : System ι) (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν]
    (hinv : MeasurePreserving (shift 1) ν ν) (herg : Ergodic (shift 1) ν)
    (hsupp : ν (subshift S.o)ᶜ = 0) :
    IsExactDim (ν.map S.projBar) ((S.dimEntropyBar ν 1 - S.dimEntropyBar ν 0) / S.lyapBar ν) := by
  have h := hly S.projectiveLineSystem ν hinv herg
    (S.lyapunov₂_lt_lyapunov₁_projectiveLineSystem hinv)
  have h2 : S.projectiveLineSystem.dimEntropy ν 2 = S.projectiveLineSystem.dimEntropy ν 1 := by
    unfold dimEntropy
    rw [S.xi_two_projectiveLineSystem hinv]
  rw [h2, sub_self, zero_div, add_zero, S.dimEntropy_projectiveLineSystem hinv herg hsupp,
    S.dimEntropy_projectiveLineSystem hinv herg hsupp, S.lyapunov₁_projectiveLineSystem hinv,
    S.map_proj_projectiveLineSystem] at h
  exact isExactDim_of_map_prodMk_zero h

end System

/-- `thm:feng1`, second part, from its first part: `FengLedrappierYoung` implies
`FengLedrappierYoungBar`, by `System.isExactDim_map_projBar_of_fengLedrappierYoung`. The
hypotheses `S.WithRotations` and `S.Proximal` of `FengLedrappierYoungBar` are not used.
Depends on: `FengLedrappierYoung`. -/
theorem fengLedrappierYoungBar_of_fengLedrappierYoung (hly : FengLedrappierYoung.{u}) :
    FengLedrappierYoungBar.{u} :=
  fun S _ _ ν _ hinv herg hsupp =>
    S.isExactDim_map_projBar_of_fengLedrappierYoung hly ν hinv herg hsupp

end BoxLike
