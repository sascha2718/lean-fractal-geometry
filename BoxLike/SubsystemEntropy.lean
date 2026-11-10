module

/-
The dimension of the Bernoulli measure of a finite homogeneous diagonal subsystem: the second
part of the measure-theoretic argument in the proof of `thm:main2` in
`sec:dimension_result_proof` (tex lines 3522 to 3560). For the subsystem `T` of
`BoxLike/HomogeneousSubsystem.lean`, with the alphabet `Option κ`, the common diagonal linear
part `diag(a, b)`, `|b| < |a|`, and the Bernoulli measure `ν_n` with equal weights on the
symbols `some k`, write `H = log #κ`, `χ_1 = -log |a|` and `χ_2 = -log |b|`.

Kittle–Kogler gives the dimensions `min{1, H / χ_i}` of the two coordinate marginals, which are
self-similar measures without exact overlaps. The scalar Ledrappier–Young formula for the coded
measures `τ_*ν_n` and `ω_*ν_n` turns them into the conditional entropies
`\overline{h}_1(τ_*ν_n) = H - χ_1 min{1, H / χ_1}` and `\overline{h}_1(ω_*ν_n) = H - χ_2
min{1, H / χ_2}`. The planar entropies of `ν_n` are `h_0 = H`, `h_1 = \overline{h}_1(τ_*ν_n)`,
by the transport of the conditional measures along `τ`, and `h_2 = 0`, either because
`H ≤ χ_2` makes `\overline{h}_1(ω_*ν_n)` vanish, or because the coding is unique. The planar
Ledrappier–Young formula then gives the dimension `subsystemDim H χ_1 χ_2` of `π_*ν_n`.

* `subsystemDim`, `subsystemDim_eq_lyapDim`, `subsystemDim_div`, `tendsto_subsystemDim`,
  `subsystemDim_eq_ledrappierYoung`: the dimension formula `d + (H - χ_1 d) / χ_2` with
  `d = min{1, H / χ_1}` of tex lines 3553 to 3555, its agreement with `eq:diml_min2`, its
  homogeneity, its continuity and its evaluation through `eq:feng1_1`.
* `measurableEmbedding_tau`, `measurableEmbedding_omega`, `restrict_map_image_eq`,
  `tau_preimage_cylinder_zero`: the codings are measurable embeddings, and the restriction
  identity that the transport of conditional measures takes.
* `condMeas_eq_zero_of_measure_eq_zero`, `condMeas_optionBernoulli_isSome`,
  `System.samePast_and_proj_eq_of_mem_xi_two`, `System.eq_of_mem_xi_two`: a null set is null
  for almost every conditional measure, so the conditional measures of `ν_n` are carried by
  the sequences over `some κ`, and the atom of `ξ_2` on `Σ'` fixes the past and the planar
  point.
* `System.IsHomogeneousOption.marginal_isExactDim`, `…_zero_isExactDim`, `…_one_isExactDim`:
  the dimension of a coordinate marginal, from `KittleKoglerDimension`.
* `System.IsHomogeneousOption.dimEntropyBar_map_tau`,
  `System.IsHomogeneousOption.dimEntropyBar_map_omega_eq_zero`: the conditional entropies
  `q_{x,n}` and `q_{y,n}` of tex lines 3536 to 3547.
* `System.IsHomogeneousOption.dimEntropy_one_eq`,
  `System.IsHomogeneousOption.condMeas_xiPerp_eq_dirac`: the transport of the conditional
  entropy and of the Dirac conditional measures along the codings.
* `System.IsHomogeneousOption.dimEntropy_eq_zero_of_condMeas_xi_eq_dirac`,
  `System.IsHomogeneousOption.dimEntropy_two_eq_zero_of_le`,
  `System.IsHomogeneousOption.dimEntropy_two_eq_zero_of_unique_coding`: `h_2(ν_n) = 0`.
* `System.IsHomogeneousOption.isExactDim_map_proj`: `dim((π_n)_*ν_n) = subsystemDim H χ_1 χ_2`.
-/
public import BoxLike.AverageEntropy
public import BoxLike.ConditionalLemmas
public import BoxLike.ConditionalTwoWays
public import BoxLike.EquilibriumEntropySmall
public import BoxLike.GibbsOrientation
public import BoxLike.HomogeneousSubsystem
public import BoxLike.Literature
public import BoxLike.LiteratureFeng
public import BoxLike.LyapunovDim
public import BoxLike.PartitionIdentities
public import BoxLike.StrongOpenSetEntropy

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology

universe u

/-! ### The dimension formula of the subsystem -/

/-- The dimension of the subsystem measure `ν_n` of tex lines 3553 to 3555:
`d + (H - χ_1 d) / χ_2` with `d = min{1, H / χ_1}`, for `H = log #W_n`, `χ_1 = -log |a_n|` and
`χ_2 = -log |b_n|`. -/
noncomputable def subsystemDim (H χ₁ χ₂ : ℝ) : ℝ :=
  min 1 (H / χ₁) + (H - χ₁ * min 1 (H / χ₁)) / χ₂

/-- Tex lines 3734 to 3735: the dimension formula of the subsystem agrees with `eq:diml_min2`
for `l₂ < l₁ < 0` and `h ≤ -l₁ - l₂`, that is, in the range `dim_L ≤ 2`. -/
theorem subsystemDim_eq_lyapDim {h l₁ l₂ : ℝ} (hl : l₂ < l₁) (hl₁ : l₁ < 0)
    (hh₂ : h ≤ -l₁ - l₂) : subsystemDim h (-l₁) (-l₂) = lyapDim h l₁ l₂ := by
  have hl₂ : l₂ < 0 := hl.trans hl₁
  have h1 : l₁ ≠ 0 := hl₁.ne
  have h2 : l₂ ≠ 0 := hl₂.ne
  unfold subsystemDim lyapDim
  by_cases hle : h ≤ -l₁
  · rw [min_eq_right ((div_le_one (neg_pos.2 hl₁)).2 hle), ite_eq_left hle]
    field_simp
    ring
  · rw [min_eq_left ((one_le_div (neg_pos.2 hl₁)).2 (not_le.1 hle).le), ite_eq_right hle,
      ite_eq_left hh₂]
    field_simp
    ring

/-- The dimension formula is invariant under dividing all three parameters by the same nonzero
number, as happens with `log #W_n / n`, `log |a_n| / n` and `log |b_n| / n` (tex line 3557). -/
theorem subsystemDim_div (H χ₁ χ₂ : ℝ) {n : ℝ} (hn : n ≠ 0) :
    subsystemDim (H / n) (χ₁ / n) (χ₂ / n) = subsystemDim H χ₁ χ₂ := by
  unfold subsystemDim
  rw [div_div_div_cancel_right₀ hn]
  congr 1
  rw [show H / n - χ₁ / n * min 1 (H / χ₁) = (H - χ₁ * min 1 (H / χ₁)) / n by ring,
    div_div_div_cancel_right₀ hn]

/-- Tex lines 3734 to 3735: the dimension formula is continuous where both exponents are
positive. -/
theorem tendsto_subsystemDim {H χ₁ χ₂ : ℕ → ℝ} {h c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hH : Tendsto H atTop (𝓝 h)) (h₁ : Tendsto χ₁ atTop (𝓝 c₁))
    (h₂ : Tendsto χ₂ atTop (𝓝 c₂)) :
    Tendsto (fun m => subsystemDim (H m) (χ₁ m) (χ₂ m)) atTop (𝓝 (subsystemDim h c₁ c₂)) := by
  unfold subsystemDim
  have hmin : Tendsto (fun m => min 1 (H m / χ₁ m)) atTop (𝓝 (min 1 (h / c₁))) :=
    tendsto_const_nhds.min (hH.div h₁ hc₁.ne')
  exact hmin.add ((hH.sub (h₁.mul hmin)).div h₂ hc₂.ne')

/-- The planar Ledrappier–Young formula `eq:feng1_1` with `h_0 = H`, `h_1 = H - χ_1 d`,
`h_2 = 0`, `λ_1 = -χ_1` and `λ_2 = -χ_2`, where `d = min{1, H / χ_1}`, evaluates to
`subsystemDim H χ_1 χ_2` (tex lines 3551 to 3556). -/
theorem subsystemDim_eq_ledrappierYoung {H l₁ l₂ : ℝ} (h₁ : l₁ ≠ 0) (h₂ : l₂ ≠ 0) :
    subsystemDim H (-l₁) (-l₂) =
      (H - -l₁ * min 1 (H / -l₁) - H) / l₁ + (0 - (H - -l₁ * min 1 (H / -l₁))) / l₂ := by
  unfold subsystemDim
  generalize min 1 (H / -l₁) = d
  field_simp
  ring

/-! ### The codings as measurable embeddings -/

section Coding

variable {ι : Type*}

/-- The cylinder `{𝐣 : j_0 = τ_0(𝐢)}` pulls back under `τ` to `{𝐤 : k_0 = i_0}`, since
`ε_0 = 0`. -/
theorem tau_preimage_cylinder_zero (o : ι → ZMod 2) (x : ℤ → ι) :
    tau o ⁻¹' {y | y 0 = tau o x 0} = {z | z 0 = x 0} := by
  ext z
  simp [tau_apply, eps_zero]

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The coding `τ` is a measurable embedding: it is injective, measurable, and maps Borel sets
to Borel sets (`measurableSet_tau_image`). -/
theorem measurableEmbedding_tau (o : ι → ZMod 2) : MeasurableEmbedding (tau o) :=
  ⟨Function.LeftInverse.injective (unCode_tau (o := o)), measurable_tau o,
    fun _ hs => measurableSet_tau_image o hs⟩

/-- The coding `ω` is a measurable embedding. -/
theorem measurableEmbedding_omega (o : ι → ZMod 2) : MeasurableEmbedding (omega o) :=
  ⟨Function.LeftInverse.injective (unCode_omega (o := o)), measurable_omega o,
    fun _ hs => measurableSet_omega_image o hs⟩

/-- The restriction of `f_*μ` to `f(E)` is `f_*(μ|_E)` for a measurable embedding `f`: the
hypothesis of `condMeas_xiBar_eq_map` with `c = 1`. -/
theorem restrict_map_image_eq {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {f : X → Y} (hf : MeasurableEmbedding f) (E : Set X) :
    (μ.map f).restrict (f '' E) = (1 : ENNReal) • (μ.restrict E).map f := by
  rw [one_smul, hf.restrict_map, hf.injective.preimage_image]

end Coding

/-! ### Null sets under conditional measures and the atoms of `ξ_2` -/

section Conditional

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- A `μ`-null Borel set is null for `μ`-almost every conditional measure: the case `B = Ω`
of the defining identity `setLIntegral_condMeas` of the conditional measures. -/
theorem condMeas_eq_zero_of_measure_eq_zero (μ : Measure Ω) [IsFiniteMeasure μ]
    (ξ : Ω → Set Ω) {A : Set Ω} (hA : MeasurableSet A) (h : μ A = 0) :
    ∀ᵐ x ∂μ, condMeas μ ξ x A = 0 := by
  have hint : ∫⁻ x, condMeas μ ξ x A ∂μ = 0 := by
    have := setLIntegral_condMeas μ ξ hA (@MeasurableSet.univ Ω (saturated ξ))
    rwa [Measure.restrict_univ, Set.inter_univ, h] at this
  exact (lintegral_eq_zero_iff ((measurable_condMeas μ ξ hA).mono (saturated_le ξ) le_rfl)).1 hint

end Conditional

namespace System

variable {ι : Type u} [MeasurableSpace ι] (S : System ι)

/-- The atom of `ξ_2` on `Σ'` (`sec:entropies`, tex lines 1779 to 1783): `𝐣 ∈ ξ_2(𝐢)` fixes
the past and the planar point, since `V_𝐢^2 = {0}`. -/
theorem samePast_and_proj_eq_of_mem_xi_two (μ : Measure (ℤ → ι)) {x y : ℤ → ι}
    (hx : x ∈ S.SigmaPrime μ) (hy : y ∈ S.xi μ 2 x) : SamePast y x ∧ S.proj y = S.proj x := by
  unfold System.xi at hy
  rw [atomsOn_of_mem hx] at hy
  obtain ⟨⟨hp, hv⟩, -⟩ := hy
  rw [S.mem_oseledets_iff] at hv
  refine ⟨hp, ?_⟩
  rcases hv with h0 | ⟨h1, -⟩ | ⟨-, e⟩
  · omega
  · omega
  · exact e

/-- The last step of the proof of `thm:SOSC_h2_zero`, pointwise: `𝐣 ∈ ξ_2(𝐢)` with `𝐢 ∈ Σ'`
and `𝐣^+ = 𝐢^+` forces `𝐣 = 𝐢`, since the atom fixes the past. -/
theorem eq_of_mem_xi_two (μ : Measure (ℤ → ι)) {x y : ℤ → ι} (hx : x ∈ S.SigmaPrime μ)
    (hy : y ∈ S.xi μ 2 x) (hfut : ∀ k : ℕ, y k = x k) : y = x := by
  obtain ⟨hp, -⟩ := S.samePast_and_proj_eq_of_mem_xi_two μ hx hy
  refine funext fun k => ?_
  rcases lt_or_ge k 0 with hk | hk
  · exact hp k hk
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    exact hfut m

end System

section Bernoulli

variable {κ : Type u}

/-- The set of sequences over `some κ` is Borel. -/
theorem measurableSet_isSome : MeasurableSet {y : ℤ → Option κ | ∀ k : ℤ, (y k).isSome} := by
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun k =>
    show MeasurableSet ((fun y : ℤ → Option κ => y k) ⁻¹' {j | j.isSome}) from
      measurable_pi_apply k MeasurableSpace.measurableSet_top

variable [Fintype κ] [Nonempty κ]

/-- For `ν_n`-almost every `𝐢`, the conditional measure of any partition is carried by the
sequences over `some κ`, which have full `ν_n`-measure. -/
theorem condMeas_optionBernoulli_isSome (ξ : (ℤ → Option κ) → Set (ℤ → Option κ)) :
    ∀ᵐ x ∂optionBernoulli κ,
      condMeas (optionBernoulli κ) ξ x {y | ∀ k : ℤ, (y k).isSome} = 1 := by
  have h0 : optionBernoulli κ {y : ℤ → Option κ | ∀ k : ℤ, (y k).isSome}ᶜ = 0 :=
    ae_iff.1 ae_isSome_optionBernoulli
  filter_upwards [condMeas_eq_zero_of_measure_eq_zero (optionBernoulli κ) ξ
    measurableSet_isSome.compl h0] with x hx
  exact (prob_compl_eq_zero_iff measurableSet_isSome).1 hx

end Bernoulli

namespace System.IsHomogeneousOption

variable {κ : Type u} [Fintype κ] [Nonempty κ] {T : System (Option κ)} {a b : ℝ}
  (hT : T.IsHomogeneousOption a b)
include hT

/-! ### The exponents -/

omit [Fintype κ] in
/-- `log |a| < 0`, so that `-log |a_n| > 0` (tex line 3518). -/
theorem log_abs_a_neg : Real.log |a| < 0 :=
  Real.log_neg (abs_pos.2 hT.a_ne_zero) hT.abs_a_lt_one

omit [Fintype κ] in
/-- `log |b| < 0`, so that `-log |b_n| > 0` (tex line 3518). -/
theorem log_abs_b_neg : Real.log |b| < 0 :=
  Real.log_neg (abs_pos.2 hT.b_ne_zero) hT.abs_b_lt_one

/-- `λ_2(𝖠_n, ν_n) < λ_1(𝖠_n, ν_n)` when `|b| < |a|`. -/
theorem lyapunov₂_lt_lyapunov₁ (hab : |b| < |a|) :
    T.lyapunov₂ (optionBernoulli κ) < T.lyapunov₁ (optionBernoulli κ) := by
  rw [hT.lyapunov₁_optionBernoulli hab.le, hT.lyapunov₂_optionBernoulli hab.le]
  exact Real.log_lt_log (abs_pos.2 hT.b_ne_zero) hab

/-! ### The dimensions of the coordinate marginals -/

/-- Tex lines 3703 to 3712: each coordinate marginal of `ν_n` is a self-similar measure with
equal weights on the `#κ` coordinate maps `g_{(some k, c)}` of the subsystem, with the common
ratio `a` for `c = 0` and `b` for `c = 1`; without exact overlaps, that is, when the words in
these maps compose injectively, Kittle–Kogler gives `dim = min{1, log #W_n / (-log |r|)}` for
the ratio `r = a` or `r = b`. -/
theorem marginal_isExactDim (hkk : KittleKoglerDimension.{u}) (c : ZMod 2)
    (hfree : Function.Injective
      (simWord (fun _ : κ => if c = 0 then a else b) (fun k => T.trans (some k, c)))) :
    IsExactDim (T.marginal c (optionBernoulli κ))
      (min 1 (Real.log (Fintype.card κ) / -Real.log |if c = 0 then a else b|)) := by
  have hr0 : (if c = 0 then a else b) ≠ 0 := by
    split_ifs
    exacts [hT.a_ne_zero, hT.b_ne_zero]
  have hr1 : |if c = 0 then a else b| < 1 := by
    split_ifs
    exacts [hT.abs_a_lt_one, hT.abs_b_lt_one]
  have hcard : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.2 Fintype.card_pos
  have hp : ∀ _ : κ, 0 < (1 / Fintype.card κ : ℝ) := fun _ => by positivity
  have hsum : ∑ _ : κ, (1 / Fintype.card κ : ℝ) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have : IsProbabilityMeasure (T.marginal c (optionBernoulli κ)) := by
    unfold System.marginal
    infer_instance
  have hstat := hT.marginal_eq_sum c
  simp only [hT.ratio_some] at hstat
  have key := hkk (fun _ : κ => if c = 0 then a else b) (fun k => T.trans (some k, c))
    (fun _ => 1 / Fintype.card κ) (fun _ => hr0) (fun _ => hr1) hp hsum hfree
    (T.marginal c (optionBernoulli κ)) hstat
  have h1 : ∑ _ : κ, Real.negMulLog (1 / Fintype.card κ : ℝ) = Real.log (Fintype.card κ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.negMulLog, one_div, Real.log_inv]
    field_simp
  have h2 : ∑ _ : κ, (1 / Fintype.card κ : ℝ) * Real.log |if c = 0 then a else b| =
      Real.log |if c = 0 then a else b| := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  simpa only [h1, h2] using key

/-- Tex lines 3707 to 3712 for the horizontal marginal:
`d_{x,n} = min{1, log #W_n / (-log |a_n|)}`. -/
theorem marginal_zero_isExactDim (hkk : KittleKoglerDimension.{u})
    (hfreex : Function.Injective (simWord (fun _ : κ => a) (fun k => T.trans (some k, 0)))) :
    IsExactDim (T.marginal 0 (optionBernoulli κ))
      (min 1 (Real.log (Fintype.card κ) / -Real.log |a|)) := by
  simpa using hT.marginal_isExactDim hkk 0 (by simpa using hfreex)

/-- Tex lines 3707 to 3712 for the vertical marginal:
`d_{y,n} = min{1, log #W_n / (-log |b_n|)}`. -/
theorem marginal_one_isExactDim (hkk : KittleKoglerDimension.{u})
    (hfreey : Function.Injective (simWord (fun _ : κ => b) (fun k => T.trans (some k, 1)))) :
    IsExactDim (T.marginal 1 (optionBernoulli κ))
      (min 1 (Real.log (Fintype.card κ) / -Real.log |b|)) := by
  simpa using hT.marginal_isExactDim hkk 1 (by simpa using hfreey)

/-! ### The scalar Ledrappier–Young formula for the coded measures -/

/-- Tex lines 3714 to 3721: `q_{x,n} = \overline{h}_1(τ_*ν_n) = log #W_n + d_{x,n} log |a_n|` with
`d_{x,n} = min{1, log #W_n / (-log |a_n|)}`, by comparing the scalar Ledrappier–Young formula
`thm:feng1` for `τ_*ν_n`, whose projection is the horizontal marginal
(`eq:commutative_diagram`), with the dimension of Kittle–Kogler, through the uniqueness of the
exact dimension. -/
theorem dimEntropyBar_map_tau (hlyb : FengLedrappierYoungBar.{u}) (hkk : KittleKoglerDimension.{u})
    (hab : |b| < |a|)
    (hfreex : Function.Injective (simWord (fun _ : κ => a) (fun k => T.trans (some k, 0)))) :
    T.dimEntropyBar ((optionBernoulli κ).map (tau T.o)) 1 =
      Real.log (Fintype.card κ) -
        -Real.log |a| * min 1 (Real.log (Fintype.card κ) / -Real.log |a|) := by
  have hsupp := T.map_tau_subshift_compl (optionBernoulli κ)
  have hLY := hlyb T hT.withRotations (hT.proximal hab) _ hT.measurePreserving_shift_map_tau
    hT.ergodic_shift_map_tau hsupp
  rw [T.map_projBar_map_tau, T.dimEntropyBar_zero_eq_entropy' _ hT.measurePreserving_shift_map_tau
    hsupp, T.entropy_map_tau, hT.lyapBar_map_tau] at hLY
  have : IsProbabilityMeasure (T.marginal 0 (optionBernoulli κ)) := by
    unfold System.marginal
    infer_instance
  have heq := IsExactDim.unique (IsProbabilityMeasure.ne_zero _) hLY
    (hT.marginal_zero_isExactDim hkk hfreex)
  rw [div_eq_iff hT.log_abs_a_neg.ne] at heq
  linarith

/-- Tex lines 3714 to 3724: `q_{y,n} = \overline{h}_1(ω_*ν_n) = log #W_n + d_{y,n} log |b_n|` with
`d_{y,n} = min{1, log #W_n / (-log |b_n|)}`, which vanishes when `log #W_n ≤ -log |b_n|`. -/
theorem dimEntropyBar_map_omega_eq_zero (hlyb : FengLedrappierYoungBar.{u})
    (hkk : KittleKoglerDimension.{u}) (hab : |b| < |a|)
    (hfreey : Function.Injective (simWord (fun _ : κ => b) (fun k => T.trans (some k, 1))))
    (hH : Real.log (Fintype.card κ) ≤ -Real.log |b|) :
    T.dimEntropyBar ((optionBernoulli κ).map (omega T.o)) 1 = 0 := by
  have hsupp := T.map_omega_subshift_compl (optionBernoulli κ)
  have hLY := hlyb T hT.withRotations (hT.proximal hab) _ hT.measurePreserving_shift_map_omega
    hT.ergodic_shift_map_omega hsupp
  rw [T.map_projBar_map_omega, T.dimEntropyBar_zero_eq_entropy' _
    hT.measurePreserving_shift_map_omega hsupp, T.entropy_map_omega, hT.lyapBar_map_omega] at hLY
  have : IsProbabilityMeasure (T.marginal 1 (optionBernoulli κ)) := by
    unfold System.marginal
    infer_instance
  have heq := IsExactDim.unique (IsProbabilityMeasure.ne_zero _) hLY
    (hT.marginal_one_isExactDim hkk hfreey)
  have hlb : 0 < -Real.log |b| := neg_pos.2 hT.log_abs_b_neg
  rw [min_eq_right ((div_le_one hlb).2 hH), div_eq_iff hT.log_abs_b_neg.ne, div_neg,
    neg_mul, div_mul_cancel₀ _ hT.log_abs_b_neg.ne] at heq
  linarith

/-! ### The transport along the codings -/

/-- Tex lines 3726 to 3728: `h_1(ν_n) = \overline{h}_1(τ_*ν_n)`. On `Σ^τ`, which carries
`ν_n`, the atom `ξ_1(𝐢)` is `\overline{τ}(\overline{ξ}_1(τ(𝐢)))` (`thm:partitions_xi1`), so the
conditional measures transport along `τ` (`thm:conditional_two_ways`) and the conditional
information agrees pointwise. -/
theorem dimEntropy_one_eq (hab : |b| < |a|) :
    T.dimEntropy (optionBernoulli κ) 1 =
      T.dimEntropyBar ((optionBernoulli κ).map (tau T.o)) 1 := by
  have hemb := measurableEmbedding_tau T.o
  have key := T.condMeas_xiBar_eq_map (optionBernoulli κ) ((optionBernoulli κ).map (tau T.o))
    (Or.inl rfl) (T.measurableSet_SigmaTau (optionBernoulli κ))
    (T.isMeasurablePartition_xi (optionBernoulli κ) 1)
    (fun x hx => (T.xi_one_of_mem_SigmaTau (optionBernoulli κ) hx).2)
    (fun x hx => (T.xi_one_of_mem_SigmaTau (optionBernoulli κ) hx).1) (1 : ENNReal)
    (restrict_map_image_eq (optionBernoulli κ) hemb (T.SigmaTau (optionBernoulli κ)))
  have key' := ae_of_ae_map (measurable_tau T.o).aemeasurable key
  unfold System.dimEntropy System.dimEntropyBar condEntropy
  rw [hemb.integral_map]
  refine integral_congr_ae ?_
  filter_upwards [key', hT.ae_mem_SigmaTau hab.le] with x hx hxE
  have h := hx (Set.mem_image_of_mem _ hxE)
  rw [unCode_tau] at h
  have hmeas : MeasurableSet {y : ℤ → Option κ × ZMod 2 | y 0 = tau T.o x 0} :=
    measurable_pi_apply 0 (measurableSet_singleton _)
  unfold condInfo
  rw [h, measureReal_def, measureReal_def, Measure.map_apply (measurable_tau T.o) hmeas,
    tau_preimage_cylinder_zero]

/-- Tex lines 3722 to 3724, the transport step: if the conditional measures of `\overline{ξ}_1`
under `ω_*ν_n` are Dirac, then so are those of `ξ_1^⊥` under `ν_n`, because on `Σ^τ` the atom
`ξ_1^⊥(𝐢)` is `\overline{ω}(\overline{ξ}_1(ω(𝐢)))` (`thm:partitions_xi1`) and `ω` is
injective. -/
theorem condMeas_xiPerp_eq_dirac (hab : |b| < |a|)
    (h : ∀ᵐ y ∂(optionBernoulli κ).map (omega T.o),
      condMeas ((optionBernoulli κ).map (omega T.o)) (T.xiBar 1) y = Measure.dirac y) :
    ∀ᵐ x ∂optionBernoulli κ,
      condMeas (optionBernoulli κ) (T.xiPerp (optionBernoulli κ)) x = Measure.dirac x := by
  have hemb := measurableEmbedding_omega T.o
  have key := T.condMeas_xiBar_eq_map (optionBernoulli κ) ((optionBernoulli κ).map (omega T.o))
    (Or.inr rfl) (T.measurableSet_SigmaTau (optionBernoulli κ))
    (T.isMeasurablePartition_xiPerp (optionBernoulli κ))
    (fun x hx => (T.xiPerp_of_mem_SigmaTau (optionBernoulli κ) hx).2)
    (fun x hx => (T.xiPerp_of_mem_SigmaTau (optionBernoulli κ) hx).1) (1 : ENNReal)
    (restrict_map_image_eq (optionBernoulli κ) hemb (T.SigmaTau (optionBernoulli κ)))
  have key' := ae_of_ae_map (measurable_omega T.o).aemeasurable key
  have h' := ae_of_ae_map (measurable_omega T.o).aemeasurable h
  filter_upwards [key', h', hT.ae_mem_SigmaTau hab.le] with x hx hx' hxE
  have e := hx (Set.mem_image_of_mem _ hxE)
  rw [unCode_omega, hx'] at e
  exact eq_dirac_of_map_coding (Or.inr rfl) e.symm

/-! ### `h_2(ν_n) = 0` -/

omit hT in
/-- If the conditional measures of `ξ_i` under `ν_n` are Dirac, then `h_i(ν_n) = 0`, directly
from the definition of the conditional information: `-log δ_𝐢([i_0]) = 0`. -/
theorem dimEntropy_eq_zero_of_condMeas_xi_eq_dirac (i : ℕ)
    (h : ∀ᵐ x ∂optionBernoulli κ,
      condMeas (optionBernoulli κ) (T.xi (optionBernoulli κ) i) x = Measure.dirac x) :
    T.dimEntropy (optionBernoulli κ) i = 0 := by
  unfold System.dimEntropy condEntropy
  refine (integral_congr_ae ?_).trans (integral_zero _ _)
  filter_upwards [h] with x hx
  unfold condInfo
  rw [hx, measureReal_def, Measure.dirac_apply_of_mem (show x ∈ {y | y 0 = x 0} from rfl),
    ENNReal.toReal_one, Real.log_one, neg_zero]

/-- Tex lines 3722 to 3724, the case `log #W_n ≤ -log |b_n|`: then `q_{y,n} = 0`, the conditional
measures of `\overline{ξ}_1` under `ω_*ν_n` are Dirac (`thm:feng_entropy_zero`), hence those
of `ξ_1^⊥` under `ν_n`, hence those of the finer partition `ξ_2`
(`thm:finer_partition_dirac_mass`), and `h_2(ν_n) = 0`. -/
theorem dimEntropy_two_eq_zero_of_le (hfib : FengInfoSumBar.{u})
    (hlyb : FengLedrappierYoungBar.{u}) (hkk : KittleKoglerDimension.{u}) (hab : |b| < |a|)
    (hfreey : Function.Injective (simWord (fun _ : κ => b) (fun k => T.trans (some k, 1))))
    (hH : Real.log (Fintype.card κ) ≤ -Real.log |b|) :
    T.dimEntropy (optionBernoulli κ) 2 = 0 := by
  have h0 := hT.dimEntropyBar_map_omega_eq_zero hlyb hkk hab hfreey hH
  have hd := T.condMeas_xiBar_eq_dirac hfib hT.withRotations (hT.proximal hab) _
    hT.ergodic_shift_map_omega (T.map_omega_subshift_compl _) h0
  exact dimEntropy_eq_zero_of_condMeas_xi_eq_dirac 2
    (finer_partition_dirac_mass _ (T.isMeasurablePartition_xiPerp _)
      (T.isMeasurablePartition_xi _ 2) (T.xi_two_subset_xiPerp _)
      (hT.condMeas_xiPerp_eq_dirac hab hd))

/-- Tex lines 3724 to 3725, the case of unique coding: if every `𝐣` over `some κ` with
`π(𝐣) = π(𝐢)` agrees with `𝐢` in forward time, for every `𝐢` over `some κ`, then the
conditional measure of `ξ_2` at almost every `𝐢` is carried by `ξ_2(𝐢) ∩ (some κ)^ℤ = {𝐢}`
(`thm:SOSC_h2_zero`), so it is Dirac, and `h_2(ν_n) = 0`. The sequences using the auxiliary
symbol `none` are not constrained, since they are `ν_n`-null. -/
theorem dimEntropy_two_eq_zero_of_unique_coding (hab : |b| < |a|)
    (hcode : ∀ x : ℤ → Option κ, (∀ k : ℤ, (x k).isSome) →
      ∀ y : ℤ → Option κ, (∀ k : ℤ, (y k).isSome) → T.proj y = T.proj x →
        ∀ k : ℕ, y k = x k) :
    T.dimEntropy (optionBernoulli κ) 2 = 0 := by
  have hsub : ∀ᵐ x ∂optionBernoulli κ,
      T.xi (optionBernoulli κ) 2 x ∩ {y | ∀ k : ℤ, (y k).isSome} ⊆ {x} := by
    filter_upwards [ae_isSome_optionBernoulli, hT.ae_mem_SigmaTau hab.le] with x hx hxE
    rintro y ⟨hy, hy'⟩
    exact T.eq_of_mem_xi_two _ (Or.inl hxE) hy
      (hcode x hx y hy' (T.samePast_and_proj_eq_of_mem_xi_two _ (Or.inl hxE) hy).2)
  have h1 : ∀ᵐ x ∂optionBernoulli κ,
      condMeas (optionBernoulli κ) (T.xi (optionBernoulli κ) 2) x {x} = 1 := by
    filter_upwards [condMeas_atom (optionBernoulli κ)
      (T.isMeasurablePartition_xi (optionBernoulli κ) 2),
      condMeas_optionBernoulli_isSome (T.xi (optionBernoulli κ) 2), hsub] with x hx hx' hxs
    have h2 : condMeas (optionBernoulli κ) (T.xi (optionBernoulli κ) 2) x
        (T.xi (optionBernoulli κ) 2 x ∩ {y | ∀ k : ℤ, (y k).isSome}) = 1 := by
      rw [measure_inter_conull ((prob_compl_eq_zero_iff measurableSet_isSome).2 hx'), hx]
    exact le_antisymm prob_le_one (h2.symm.le.trans (measure_mono hxs))
  exact dimEntropy_eq_zero_of_condMeas_xi_eq_dirac 2
    (h1.mono fun _ hx => eq_dirac_of_measure_singleton hx)

/-! ### The dimension of `ν_n` -/

/-- Tex lines 3728 to 3733:
`dim((π_n)_*ν_n) = d_{x,n} + (log #W_n + d_{x,n} log |a_n|) / (-log |b_n|)`, by the planar
Ledrappier–Young formula `thm:feng1` with the entropies `h_0 = log #W_n`, `h_1 = q_{x,n}` and
`h_2 = 0`, and the exponents `λ_1 = log |a_n|`, `λ_2 = log |b_n|`. The hypothesis `hzero` is the
case distinction of the article: `log #W_n ≤ -log |b_n|`, or unique coding of the subsystem
among the sequences over `some κ`. -/
theorem isExactDim_map_proj (hfib : FengInfoSumBar.{u}) (hly : FengLedrappierYoung.{u})
    (hlyb : FengLedrappierYoungBar.{u}) (hkk : KittleKoglerDimension.{u}) (hab : |b| < |a|)
    (hfreex : Function.Injective (simWord (fun _ : κ => a) (fun k => T.trans (some k, 0))))
    (hfreey : Function.Injective (simWord (fun _ : κ => b) (fun k => T.trans (some k, 1))))
    (hzero : Real.log (Fintype.card κ) ≤ -Real.log |b| ∨
      ∀ x : ℤ → Option κ, (∀ k : ℤ, (x k).isSome) →
        ∀ y : ℤ → Option κ, (∀ k : ℤ, (y k).isSome) → T.proj y = T.proj x →
          ∀ k : ℕ, y k = x k) :
    IsExactDim ((optionBernoulli κ).map T.proj)
      (subsystemDim (Real.log (Fintype.card κ)) (-Real.log |a|) (-Real.log |b|)) := by
  have hLY := hly T (optionBernoulli κ) (measurePreserving_shift_optionBernoulli 1)
    ergodic_shift_optionBernoulli (hT.lyapunov₂_lt_lyapunov₁ hab)
  have h2 : T.dimEntropy (optionBernoulli κ) 2 = 0 := by
    rcases hzero with hH | hcode
    · exact hT.dimEntropy_two_eq_zero_of_le hfib hlyb hkk hab hfreey hH
    · exact hT.dimEntropy_two_eq_zero_of_unique_coding hab hcode
  rw [hT.dimEntropy_zero hab.le, hT.dimEntropy_one_eq hab,
    hT.dimEntropyBar_map_tau hlyb hkk hab hfreex, h2, hT.lyapunov₁_optionBernoulli hab.le,
    hT.lyapunov₂_optionBernoulli hab.le] at hLY
  rw [subsystemDim_eq_ledrappierYoung hT.log_abs_a_neg.ne hT.log_abs_b_neg.ne]
  exact hLY

end System.IsHomogeneousOption

end BoxLike
