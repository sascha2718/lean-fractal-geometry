module

/-
Finite homogeneous diagonal subsystems and their Bernoulli measures: the first part of the
measure-theoretic argument in the proof of `thm:main2` in `sec:dimension_result_proof` (tex
lines 3697 to 3737). The subsystem of the proof has the alphabet `Option κ`: the symbols
`some k` are the words `w ∈ W_n`, all with the common diagonal linear part `diag(a, b)`, and
`none` is one anti-diagonal word of the same length, which carries no mass and only makes the
system box-like with rotations and proximal, as the projective part of `thm:feng1` requires.
The measure `ν_n` of the article is the Bernoulli measure with equal weights on the symbols
`some k`; its coded versions `τ_*ν_n` and `ω_*ν_n` live on `Σ_Z` and project to the two
coordinate marginals.

* `instMeasurableSpaceOption`, `instMeasurableSingletonClassOption`: the discrete `σ`-algebra
  on `Option κ`.
* `optionWeight`, `optionUniform`, `optionBernoulli`: the weights `1/#κ` on `some k` and `0`
  on `none`, and the Bernoulli measure `ν_n` on `ℤ → Option κ`; it is invariant and ergodic,
  almost every sequence has all its symbols in `some κ`, and its entropy is `log #κ`.
* `System.IsHomogeneousOption`: the symbols `some k` have the common diagonal linear part
  `diag(a, b)` and `none` has an anti-diagonal one.
* `System.IsHomogeneousOption.lyapunov₁_optionBernoulli`,
  `System.IsHomogeneousOption.lyapunov₂_optionBernoulli`: the Lyapunov exponents are
  `log |a|` and `log |b|`.
* `System.IsHomogeneousOption.mem_SigmaTau_of_forall_isSome`,
  `System.IsHomogeneousOption.measure_SigmaPrime_compl`: every sequence over `some κ` lies in
  `Σ^τ`, so the slow axis is the vertical axis almost everywhere.
* `System.IsHomogeneousOption.dimEntropy_zero`: `h_0(ν_n) = log #κ`.
* `System.IsHomogeneousOption.measurePreserving_shift_map_tau`, `…_omega`,
  `System.IsHomogeneousOption.ergodic_shift_map_tau`, `…_omega`,
  `System.map_tau_subshift_compl`, `System.map_omega_subshift_compl`,
  `System.entropy_map_tau`, `System.entropy_map_omega`,
  `System.IsHomogeneousOption.lyapBar_map_tau`, `…_omega`,
  `System.map_projBar_map_tau`, `System.map_projBar_map_omega`: the coded measures
  `τ_*ν_n`, `ω_*ν_n` are invariant ergodic measures on `Σ_Z` with entropy `log #κ`, Lyapunov
  exponents `log |a|`, `log |b|`, and projections the two coordinate marginals.
* `System.IsHomogeneousOption.marginal_eq_sum`: each coordinate marginal is the self-similar
  measure of the coordinate maps of the subsystem with equal weights.
* `ergodic_of_ae_semiconj`: ergodicity passes to the image under a measure-preserving map that
  semiconjugates the dynamics almost everywhere.
-/
public import BoxLike.BernoulliEquilibrium
public import BoxLike.DimPartitions
public import BoxLike.EntropyFactor
public import BoxLike.InvariantMeasure
public import BoxLike.Main
public import BoxLike.PastEntropy
public import BoxLike.PressureLarge
public import BoxLike.SlowAxis

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

/-! ### The discrete `σ`-algebra on `Option κ` -/

/-- The discrete `σ`-algebra on the alphabet `Option κ` of the subsystem. -/
instance instMeasurableSpaceOption {κ : Type*} : MeasurableSpace (Option κ) := ⊤

/-- Every singleton of `Option κ` is measurable. -/
instance instMeasurableSingletonClassOption {κ : Type*} :
    MeasurableSingletonClass (Option κ) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-! ### Auxiliary results -/

/-- Every symbol of the prefix `𝐢|_n` of a sequence over `some κ` lies in `some κ`. -/
theorem forall_mem_futureWord_isSome {κ : Type*} {x : ℤ → Option κ}
    (hx : ∀ k : ℤ, (x k).isSome) (n : ℕ) : ∀ j ∈ futureWord x n, j.isSome := by
  intro j hj
  simp only [futureWord, List.mem_map, List.mem_range] at hj
  obtain ⟨k, -, rfl⟩ := hj
  exact hx k

/-- `n⁻¹ log |c^n| → log |c|`. -/
theorem tendsto_log_abs_pow_div (c : ℝ) :
    Tendsto (fun n : ℕ => Real.log |c ^ n| / n) atTop (𝓝 (Real.log |c|)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [abs_pow, Real.log_pow, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 hn)]

/-- Ergodicity passes to the image measure under a measure-preserving map `g` that
semiconjugates the dynamics almost everywhere: if `f` is ergodic for `μ`, `f'` preserves
`ν = g_*μ` and `g ∘ f = f' ∘ g` holds `μ`-almost everywhere, then `f'` is ergodic for `ν`.
An invariant set of `f'` pulls back to an almost invariant set of `f`, which is null or conull
by the quasi-ergodicity of `f`. -/
theorem ergodic_of_ae_semiconj {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → X} {f' : Y → Y} {g : X → Y}
    (hf : Ergodic f μ) (hf' : MeasurePreserving f' ν ν) (hg : MeasurePreserving g μ ν)
    (h : ∀ᵐ x ∂μ, g (f x) = f' (g x)) : Ergodic f' ν := by
  refine ⟨hf', ⟨fun s hs hinv => ?_⟩⟩
  have hae : f ⁻¹' (g ⁻¹' s) =ᵐ[μ] g ⁻¹' s := by
    filter_upwards [h] with x hx
    change (g (f x) ∈ s) = (g x ∈ s)
    rw [hx]
    show (g x ∈ f' ⁻¹' s) = (g x ∈ s)
    rw [hinv]
  rw [eventuallyEmptyOrUniv_iff']
  rcases hf.quasiErgodic.ae_empty_or_univ₀ (hg.measurable hs).nullMeasurableSet hae with
    h0 | h1
  · left
    rw [ae_eq_empty] at h0 ⊢
    rwa [hg.measure_preimage hs.nullMeasurableSet] at h0
  · right
    rw [ae_eq_univ] at h1 ⊢
    rwa [← Set.preimage_compl, hg.measure_preimage hs.compl.nullMeasurableSet] at h1

/-! ### The Bernoulli measure with equal weights on `some κ` -/

section Bernoulli

variable (κ : Type*) [Fintype κ]

/-- The weights `1/#κ` on the symbols `some k` and `0` on `none`. -/
noncomputable def optionWeight : Option κ → ℝ :=
  fun j => if j.isSome then 1 / Fintype.card κ else 0

/-- The probability measure on `Option κ` with the weights `optionWeight`. -/
noncomputable def optionUniform : Measure (Option κ) := weightMeasure (optionWeight κ)

/-- The Bernoulli measure `ν_n` of tex lines 3522 to 3523: equal probabilities on the maps
`φ_w`, `w ∈ W_n`, that is, on the symbols `some k`, and none on `none`. -/
noncomputable def optionBernoulli : Measure (ℤ → Option κ) := bernoulli (optionUniform κ)

variable {κ}

@[simp] theorem optionWeight_some (k : κ) : optionWeight κ (some k) = 1 / Fintype.card κ := rfl

@[simp] theorem optionWeight_none : optionWeight κ none = 0 := rfl

theorem optionWeight_nonneg (j : Option κ) : 0 ≤ optionWeight κ j := by
  unfold optionWeight
  split_ifs <;> positivity

theorem sum_optionWeight [Nonempty κ] : ∑ j, optionWeight κ j = 1 := by
  rw [Fintype.sum_option, optionWeight_none, zero_add]
  simp only [optionWeight_some, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_one_div, div_self (Nat.cast_ne_zero.2 Fintype.card_ne_zero)]

theorem measureReal_optionUniform_singleton (j : Option κ) :
    (optionUniform κ).real {j} = optionWeight κ j :=
  measureReal_weightMeasure_singleton (optionWeight_nonneg j)

instance isProbabilityMeasure_optionUniform [Nonempty κ] :
    IsProbabilityMeasure (optionUniform κ) :=
  isProbabilityMeasure_weightMeasure optionWeight_nonneg sum_optionWeight

instance isProbabilityMeasure_optionBernoulli [Nonempty κ] :
    IsProbabilityMeasure (optionBernoulli κ) :=
  isProbabilityMeasure_bernoulli _

/-- The Bernoulli measure `ν_n` is invariant under every iterate of the shift. -/
theorem measurePreserving_shift_optionBernoulli [Nonempty κ] (m : ℤ) :
    MeasurePreserving (shift m) (optionBernoulli κ) (optionBernoulli κ) :=
  measurePreserving_shift_bernoulli _ m

/-- The Bernoulli measure `ν_n` is ergodic. -/
theorem ergodic_shift_optionBernoulli [Nonempty κ] : Ergodic (shift 1) (optionBernoulli κ) :=
  ergodic_shift_bernoulli _

/-- The cylinder measures of `ν_n` are products of the weights. -/
theorem measureReal_optionBernoulli_cylinder [Nonempty κ] {n : ℕ} (w : Fin n → Option κ) :
    (optionBernoulli κ).real (cylinder w) = ∏ j, optionWeight κ (w j) := by
  rw [optionBernoulli, measureReal_bernoulli_cylinder]
  exact Finset.prod_congr rfl fun j _ => measureReal_optionUniform_singleton (w j)

/-- The cylinder `[j]` of one symbol has the measure `optionWeight κ j`. -/
theorem measureReal_optionBernoulli_cylinder_single [Nonempty κ] (j : Option κ) :
    (optionBernoulli κ).real (cylinder ![j]) = optionWeight κ j := by
  rw [measureReal_optionBernoulli_cylinder, Fin.prod_univ_one, Matrix.cons_val_zero]

/-- The cylinder `[j]` of one symbol has the measure `optionWeight κ j`, in `ℝ≥0∞`. -/
theorem optionBernoulli_cylinder_single [Nonempty κ] (j : Option κ) :
    optionBernoulli κ (cylinder ![j]) = ENNReal.ofReal (optionWeight κ j) := by
  rw [← ofReal_measureReal, measureReal_optionBernoulli_cylinder_single]

/-- The cylinder measures of `ν_n` are products of the one-symbol measures, the form of the
product property that `isInvariantMeasure_map_proj` takes. -/
theorem measureReal_optionBernoulli_cylinder_prod [Nonempty κ] {n : ℕ} (w : Fin n → Option κ) :
    (optionBernoulli κ).real (cylinder w) =
      ∏ k, (optionBernoulli κ).real (cylinder ![w k]) := by
  rw [measureReal_optionBernoulli_cylinder]
  exact Finset.prod_congr rfl fun k _ => (measureReal_optionBernoulli_cylinder_single (w k)).symm

/-- Almost every sequence has all its symbols in `some κ`. -/
theorem ae_isSome_optionBernoulli [Nonempty κ] :
    ∀ᵐ x ∂optionBernoulli κ, ∀ k : ℤ, (x k).isSome := by
  rw [ae_all_iff]
  intro k
  rw [ae_iff]
  have h := bernoulli_cylinder (optionUniform κ) k ![(none : Option κ)]
  rw [Fin.prod_univ_one, Matrix.cons_val_zero, optionUniform, weightMeasure_singleton,
    optionWeight_none, ENNReal.ofReal_zero] at h
  refine measure_mono_null (fun x hx => ?_) h
  rw [Set.mem_ofPred_eq, Option.not_isSome_iff_eq_none] at hx
  intro j
  obtain rfl : j = 0 := Subsingleton.elim j 0
  simpa using hx

/-- The entropy of `ν_n` is `log #W_n` (tex line 3520). -/
theorem entropy_optionBernoulli [Nonempty κ] :
    entropy (optionBernoulli κ) = Real.log (Fintype.card κ) := by
  have hc : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [optionBernoulli, entropy_bernoulli, Fintype.sum_option]
  simp only [measureReal_optionUniform_singleton, optionWeight_none, optionWeight_some,
    Real.negMulLog_zero, zero_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.negMulLog, one_div, Real.log_inv]
  field_simp

/-- A function of the prefix `𝐢|_n` that equals `n c` on the words over `some κ` has the
normalised `ν_n`-integrals converging to `c`: almost every sequence lies over `some κ`. -/
theorem tendsto_integral_futureWord_div [Nonempty κ] {G : List (Option κ) → ℝ} {c : ℝ}
    (hG : ∀ u : List (Option κ), (∀ j ∈ u, j.isSome) → G u = u.length * c) :
    Tendsto (fun n : ℕ => (∫ x, G (futureWord x n) ∂optionBernoulli κ) / n) atTop (𝓝 c) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have h : ∫ x, G (futureWord x n) ∂optionBernoulli κ =
      ∫ _, (n : ℝ) * c ∂optionBernoulli κ := by
    refine integral_congr_ae ?_
    filter_upwards [ae_isSome_optionBernoulli (κ := κ)] with x hx
    rw [hG _ (forall_mem_futureWord_isSome hx n), length_futureWord]
  rw [h, integral_const, probReal_univ, one_smul,
    mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 hn)]

end Bernoulli

namespace System

/-! ### Homogeneous diagonal subsystems -/

variable {κ : Type*} [Fintype κ]

/-- The subsystem of the proof of `thm:main2` (tex lines 3496 to 3502): the symbols `some k`
have the common diagonal linear part `diag(a, b)` and the symbol `none` has an anti-diagonal
linear part. -/
structure IsHomogeneousOption (T : System (Option κ)) (a b : ℝ) : Prop where
  /-- The linear part of `some k` is diagonal. -/
  o_some : ∀ k, T.o (some k) = 0
  /-- The first entry of the linear part of `some k` is `a`. -/
  a_some : ∀ k, T.a (some k) = a
  /-- The second entry of the linear part of `some k` is `b`. -/
  b_some : ∀ k, T.b (some k) = b
  /-- The linear part of `none` is anti-diagonal. -/
  o_none : T.o none = 1

namespace IsHomogeneousOption

variable {T : System (Option κ)} {a b : ℝ} (hT : T.IsHomogeneousOption a b)
include hT

omit [Fintype κ] in
theorem a_ne_zero [Nonempty κ] : a ≠ 0 := by
  obtain ⟨k⟩ : Nonempty κ := inferInstance
  simpa [hT.a_some k] using T.a_ne_zero (some k)

omit [Fintype κ] in
theorem b_ne_zero [Nonempty κ] : b ≠ 0 := by
  obtain ⟨k⟩ : Nonempty κ := inferInstance
  simpa [hT.b_some k] using T.b_ne_zero (some k)

omit [Fintype κ] in
theorem abs_a_lt_one [Nonempty κ] : |a| < 1 := by
  obtain ⟨k⟩ : Nonempty κ := inferInstance
  simpa [hT.a_some k] using T.abs_a_lt_one (some k)

omit [Fintype κ] in
theorem abs_b_lt_one [Nonempty κ] : |b| < 1 := by
  obtain ⟨k⟩ : Nonempty κ := inferInstance
  simpa [hT.b_some k] using T.abs_b_lt_one (some k)

omit [Fintype κ] in
/-- The contraction ratio of the symbol `(some k, c)` of the projective system is `a` on the
first axis and `b` on the second. -/
theorem ratio_some (k : κ) (c : ZMod 2) : T.ratio (some k, c) = if c = 0 then a else b := by
  simp only [ratio, hT.a_some, hT.b_some]

omit [Fintype κ] in
/-- The subsystem is box-like with rotations: `some k` is diagonal and `none` anti-diagonal. -/
theorem withRotations [Nonempty κ] : T.WithRotations :=
  ⟨⟨some (Classical.arbitrary κ), hT.o_some _⟩, ⟨none, hT.o_none⟩⟩

omit [Fintype κ] in
/-- The subsystem is proximal when `|b| < |a|`: the matrix `diag(a, b)` of a symbol `some k`
has the two real eigenvalues `a`, `b` of different absolute values. -/
theorem proximal [Nonempty κ] (hab : |b| < |a|) : T.Proximal :=
  HasProximalDiagonal.proximal ⟨some (Classical.arbitrary κ), hT.o_some _, by
    rw [hT.a_some, hT.b_some]
    exact hab.ne'⟩

omit [Fintype κ] in
/-- The product of the matrices of a word over `some κ` is `diag(a^n, b^n)`. -/
theorem matWord_of_forall_isSome (u : List (Option κ)) (hu : ∀ j ∈ u, j.isSome) :
    T.matWord u = boxMat 0 (a ^ u.length) (b ^ u.length) := by
  induction u with
  | nil =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | cons j u ih =>
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (hu j (by simp))
    rw [matWord_cons, ih fun j' hj' => hu j' (by simp [hj']), mat, hk, hT.o_some, hT.a_some,
      hT.b_some, boxMat_mul, List.length_cons, pow_succ', pow_succ']
    simp

omit [Fintype κ] in
/-- `log α_1(A_𝐮) = |𝐮| log |a|` for a word `𝐮` over `some κ`, when `|b| ≤ |a|`. -/
theorem log_norm_matWord_of_forall_isSome (hab : |b| ≤ |a|) (u : List (Option κ))
    (hu : ∀ j ∈ u, j.isSome) : Real.log ‖T.matWord u‖ = u.length * Real.log |a| := by
  rw [hT.matWord_of_forall_isSome u hu, norm_boxMat, abs_pow, abs_pow,
    max_eq_left (pow_le_pow_left₀ (abs_nonneg b) hab _), Real.log_pow]

omit [Fintype κ] in
/-- `log α_2(A_𝐮) = |𝐮| log |b|` for a word `𝐮` over `some κ`, when `|b| ≤ |a|`. -/
theorem log_abs_det_div_norm_matWord_of_forall_isSome [Nonempty κ] (hab : |b| ≤ |a|)
    (u : List (Option κ)) (hu : ∀ j ∈ u, j.isSome) :
    Real.log (|(T.matWord u).det| / ‖T.matWord u‖) = u.length * Real.log |b| := by
  rw [hT.matWord_of_forall_isSome u hu, norm_boxMat, abs_det_boxMat, abs_pow, abs_pow,
    max_eq_left (pow_le_pow_left₀ (abs_nonneg b) hab _),
    mul_div_cancel_left₀ _ (pow_ne_zero _ (abs_ne_zero.2 hT.a_ne_zero)), Real.log_pow]

/-- `λ_1(𝖠_n, ν_n) = log |a|` for the subsystem: tex lines 3518 to 3520, with
`-log |a_n|`. -/
theorem lyapunov₁_optionBernoulli [Nonempty κ] (hab : |b| ≤ |a|) :
    T.lyapunov₁ (optionBernoulli κ) = Real.log |a| :=
  tendsto_nhds_unique (T.tendsto_lyapunov₁ (measurePreserving_shift_optionBernoulli 1))
    (tendsto_integral_futureWord_div (G := fun w => Real.log ‖T.matWord w‖)
      fun u hu => hT.log_norm_matWord_of_forall_isSome hab u hu)

/-- `λ_2(𝖠_n, ν_n) = log |b|` for the subsystem: tex lines 3518 to 3520, with
`-log |b_n|`. -/
theorem lyapunov₂_optionBernoulli [Nonempty κ] (hab : |b| ≤ |a|) :
    T.lyapunov₂ (optionBernoulli κ) = Real.log |b| :=
  tendsto_nhds_unique (T.tendsto_lyapunov₂ (measurePreserving_shift_optionBernoulli 1))
    (tendsto_integral_futureWord_div
      (G := fun w => Real.log (|(T.matWord w).det| / ‖T.matWord w‖))
      fun u hu => hT.log_abs_det_div_norm_matWord_of_forall_isSome hab u hu)

omit [Fintype κ] in
/-- `ε_m(𝐢) = 0` for every `m ∈ ℤ` when all symbols of `𝐢` lie in `some κ`: every symbol is
diagonal. -/
theorem eps_eq_zero_of_forall_isSome {x : ℤ → Option κ} (hx : ∀ k : ℤ, (x k).isSome)
    (m : ℤ) : eps T.o x m = 0 := by
  have ho : ∀ k, T.o (x k) = 0 := fun k => by
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 (hx k)
    rw [hj, hT.o_some]
  have h := eq_eps_of_succ T.o x (S := fun _ => 0) rfl fun m => by simp [ho]
  exact (congrFun h m).symm

omit [Fintype κ] in
/-- `g'_{τ_{-n}(𝐢) ⋯ τ_{-1}(𝐢)} = a^n` for a sequence `𝐢` over `some κ`. -/
theorem gDeriv_pastWord_tau_of_forall_isSome {x : ℤ → Option κ} (hx : ∀ k : ℤ, (x k).isSome)
    (n : ℕ) : T.gDeriv (pastWord (tau T.o x) n) = a ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (hx (-((n : ℤ) + 1)))
    rw [pastWord_succ, gDeriv_cons, ih, tau_apply, hk, hT.eps_eq_zero_of_forall_isSome hx,
      hT.ratio_some, ite_eq_left rfl, pow_succ']

omit [Fintype κ] in
/-- `g'_{ω_{-n}(𝐢) ⋯ ω_{-1}(𝐢)} = b^n` for a sequence `𝐢` over `some κ`. -/
theorem gDeriv_pastWord_omega_of_forall_isSome {x : ℤ → Option κ}
    (hx : ∀ k : ℤ, (x k).isSome) (n : ℕ) : T.gDeriv (pastWord (omega T.o x) n) = b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (hx (-((n : ℤ) + 1)))
    rw [pastWord_succ, gDeriv_cons, ih, omega_apply, hk, hT.eps_eq_zero_of_forall_isSome hx,
      zero_add, hT.ratio_some, ite_eq_right (by decide), pow_succ']

/-- Every sequence over `some κ` lies in `Σ^τ`: the backward growth rates of `e_1` and `e_2`
are `log |a|` and `log |b|` exactly, so the slow axis `V^1` is the vertical axis (tex lines
3726 to 3727). -/
theorem mem_SigmaTau_of_forall_isSome [Nonempty κ] (hab : |b| ≤ |a|) {x : ℤ → Option κ}
    (hx : ∀ k : ℤ, (x k).isSome) : x ∈ T.SigmaTau (optionBernoulli κ) := by
  simp only [SigmaTau, Set.mem_ofPred_eq, HasBackRate, hT.lyapunov₁_optionBernoulli hab,
    hT.lyapunov₂_optionBernoulli hab, hT.gDeriv_pastWord_tau_of_forall_isSome hx,
    hT.gDeriv_pastWord_omega_of_forall_isSome hx]
  exact ⟨tendsto_log_abs_pow_div a, tendsto_log_abs_pow_div b⟩

/-- Almost every sequence lies in `Σ^τ`. -/
theorem ae_mem_SigmaTau [Nonempty κ] (hab : |b| ≤ |a|) :
    ∀ᵐ x ∂optionBernoulli κ, x ∈ T.SigmaTau (optionBernoulli κ) := by
  filter_upwards [ae_isSome_optionBernoulli (κ := κ)] with x hx
  exact hT.mem_SigmaTau_of_forall_isSome hab hx

/-- `Σ'` has full measure for `ν_n`. -/
theorem measure_SigmaPrime_compl [Nonempty κ] (hab : |b| ≤ |a|) :
    optionBernoulli κ (T.SigmaPrime (optionBernoulli κ))ᶜ = 0 :=
  measure_mono_null (fun _ hx hx' => hx (Or.inl hx')) (ae_iff.1 (hT.ae_mem_SigmaTau hab))

/-- `h_0(ν_n) = log #W_n` (tex line 3520 and 3551). -/
theorem dimEntropy_zero [Nonempty κ] (hab : |b| ≤ |a|) :
    T.dimEntropy (optionBernoulli κ) 0 = Real.log (Fintype.card κ) := by
  rw [T.dimEntropy_zero_eq_entropy' _ (measurePreserving_shift_optionBernoulli 1)
    (hT.measure_SigmaPrime_compl hab), entropy_optionBernoulli]

/-! ### The coded measures `τ_*ν_n` and `ω_*ν_n` on `Σ_Z` -/

/-- `τ ∘ σ = σ ∘ τ` almost everywhere: `ε_1(𝐢) = 0` on the sequences over `some κ`. -/
theorem ae_tau_shift [Nonempty κ] :
    ∀ᵐ x ∂optionBernoulli κ, tau T.o (shift 1 x) = shift 1 (tau T.o x) := by
  filter_upwards [ae_isSome_optionBernoulli (κ := κ)] with x hx
  exact tau_shift_of_eps_eq_zero (hT.eps_eq_zero_of_forall_isSome hx 1)

/-- `ω ∘ σ = σ ∘ ω` almost everywhere. -/
theorem ae_omega_shift [Nonempty κ] :
    ∀ᵐ x ∂optionBernoulli κ, omega T.o (shift 1 x) = shift 1 (omega T.o x) := by
  filter_upwards [ae_isSome_optionBernoulli (κ := κ)] with x hx
  exact omega_shift_of_eps_eq_zero (hT.eps_eq_zero_of_forall_isSome hx 1)

/-- `τ_*ν_n` is shift-invariant: `τ ∘ σ = σ ∘ τ` on the sequences over `some κ`, which have
full measure. -/
theorem measurePreserving_shift_map_tau [Nonempty κ] :
    MeasurePreserving (shift 1) ((optionBernoulli κ).map (tau T.o))
      ((optionBernoulli κ).map (tau T.o)) := by
  refine ⟨measurable_shift 1, ?_⟩
  rw [Measure.map_map (measurable_shift 1) (measurable_tau T.o)]
  have h : (optionBernoulli κ).map (shift 1 ∘ tau T.o) =
      (optionBernoulli κ).map (tau T.o ∘ shift 1) :=
    Measure.map_congr (hT.ae_tau_shift.mono fun _ hx => hx.symm)
  rw [h, ← Measure.map_map (measurable_tau T.o) (measurable_shift 1),
    (measurePreserving_shift_optionBernoulli 1).map_eq]

/-- `ω_*ν_n` is shift-invariant. -/
theorem measurePreserving_shift_map_omega [Nonempty κ] :
    MeasurePreserving (shift 1) ((optionBernoulli κ).map (omega T.o))
      ((optionBernoulli κ).map (omega T.o)) := by
  refine ⟨measurable_shift 1, ?_⟩
  rw [Measure.map_map (measurable_shift 1) (measurable_omega T.o)]
  have h : (optionBernoulli κ).map (shift 1 ∘ omega T.o) =
      (optionBernoulli κ).map (omega T.o ∘ shift 1) :=
    Measure.map_congr (hT.ae_omega_shift.mono fun _ hx => hx.symm)
  rw [h, ← Measure.map_map (measurable_omega T.o) (measurable_shift 1),
    (measurePreserving_shift_optionBernoulli 1).map_eq]

/-- `τ_*ν_n` is ergodic, as the image of the ergodic measure `ν_n` under a map that
semiconjugates the shifts almost everywhere. -/
theorem ergodic_shift_map_tau [Nonempty κ] :
    Ergodic (shift 1) ((optionBernoulli κ).map (tau T.o)) :=
  ergodic_of_ae_semiconj ergodic_shift_optionBernoulli hT.measurePreserving_shift_map_tau
    ⟨measurable_tau T.o, rfl⟩ hT.ae_tau_shift

/-- `ω_*ν_n` is ergodic. -/
theorem ergodic_shift_map_omega [Nonempty κ] :
    Ergodic (shift 1) ((optionBernoulli κ).map (omega T.o)) :=
  ergodic_of_ae_semiconj ergodic_shift_optionBernoulli hT.measurePreserving_shift_map_omega
    ⟨measurable_omega T.o, rfl⟩ hT.ae_omega_shift

/-- `\overline{λ}(𝖠_n, τ_*ν_n) = log |a|`. -/
theorem lyapBar_map_tau [Nonempty κ] :
    T.lyapBar ((optionBernoulli κ).map (tau T.o)) = Real.log |a| := by
  have hmeas : Measurable fun y : ℤ → Option κ × ZMod 2 => Real.log |T.ratio (y 0)| :=
    (Measurable.of_discrete (f := fun p : Option κ × ZMod 2 => Real.log |T.ratio p|)).comp
      (measurable_pi_apply 0)
  rw [lyapBar, integral_map (measurable_tau T.o).aemeasurable hmeas.aestronglyMeasurable]
  simp only [tau_apply, eps_zero]
  rw [integral_comp_apply_zero (optionBernoulli κ) fun j => Real.log |T.ratio (j, 0)|,
    Fintype.sum_option]
  simp only [measureReal_optionBernoulli_cylinder_single, optionWeight_none, zero_mul, zero_add,
    optionWeight_some, hT.ratio_some, ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, mul_one_div_cancel (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_mul]

/-- `\overline{λ}(𝖠_n, ω_*ν_n) = log |b|`. -/
theorem lyapBar_map_omega [Nonempty κ] :
    T.lyapBar ((optionBernoulli κ).map (omega T.o)) = Real.log |b| := by
  have hmeas : Measurable fun y : ℤ → Option κ × ZMod 2 => Real.log |T.ratio (y 0)| :=
    (Measurable.of_discrete (f := fun p : Option κ × ZMod 2 => Real.log |T.ratio p|)).comp
      (measurable_pi_apply 0)
  rw [lyapBar, integral_map (measurable_omega T.o).aemeasurable hmeas.aestronglyMeasurable]
  simp only [omega_apply, eps_zero, zero_add]
  rw [integral_comp_apply_zero (optionBernoulli κ) fun j => Real.log |T.ratio (j, 1)|,
    Fintype.sum_option]
  simp only [measureReal_optionBernoulli_cylinder_single, optionWeight_none, zero_mul, zero_add,
    optionWeight_some, hT.ratio_some, (by decide : (1 : ZMod 2) ≠ 0), ite_false,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, mul_one_div_cancel (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_mul]

/-- Each coordinate marginal of `ν_n` is the self-similar measure of the coordinate maps
`g_{(some k, c)}` of the subsystem with equal weights (tex lines 3523 to 3524): the
stationarity equation of a self-similar measure, from the invariance of the projection of a
Bernoulli measure (`isInvariantMeasure_map_proj`) and `eq:phi_def_by_g`. -/
theorem marginal_eq_sum [Nonempty κ] (c : ZMod 2) :
    T.marginal c (optionBernoulli κ) =
      ∑ k : κ, ENNReal.ofReal (1 / Fintype.card κ) •
        (T.marginal c (optionBernoulli κ)).map
          (fun x => T.ratio (some k, c) * x + T.trans (some k, c)) := by
  obtain ⟨r, M, hS⟩ := T.exists_bounds
  have hc : Measurable (coord c) := by
    unfold coord
    split_ifs
    · exact measurable_fst
    · exact measurable_snd
  have hphi : ∀ i, Measurable (T.phi i) := fun i => (T.continuous_phi i).measurable
  have hg : ∀ k : κ, Measurable fun x : ℝ => T.ratio (some k, c) * x + T.trans (some k, c) :=
    fun k => (measurable_id.const_mul _).add_const _
  have hinv := T.isInvariantMeasure_map_proj (measurePreserving_shift_optionBernoulli 1)
    fun n w => measureReal_optionBernoulli_cylinder_prod w
  unfold IsInvariantMeasure at hinv
  refine Measure.ext fun B hB => ?_
  have key : ∀ k : κ, T.phi (some k) ⁻¹' (coord c ⁻¹' B) =
      coord c ⁻¹' ((fun x => T.ratio (some k, c) * x + T.trans (some k, c)) ⁻¹' B) := by
    intro k
    ext z
    simp only [Set.mem_preimage, coord_phi, hT.o_some, add_zero, g]
  calc T.marginal c (optionBernoulli κ) B
      = (optionBernoulli κ).map T.proj (coord c ⁻¹' B) := by
        rw [marginal, Measure.map_apply hc hB]
    _ = ∑ i, optionBernoulli κ (cylinder ![i]) *
          (optionBernoulli κ).map T.proj (T.phi i ⁻¹' (coord c ⁻¹' B)) := by
        conv_lhs => rw [hinv]
        rw [Measure.finsetSum_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (hphi i) (hc hB)]
    _ = ∑ k : κ, ENNReal.ofReal (1 / Fintype.card κ) *
          (optionBernoulli κ).map T.proj
            (coord c ⁻¹' ((fun x => T.ratio (some k, c) * x + T.trans (some k, c)) ⁻¹' B)) := by
        rw [Fintype.sum_option, optionBernoulli_cylinder_single, optionWeight_none,
          ENNReal.ofReal_zero, zero_mul, zero_add]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [optionBernoulli_cylinder_single, optionWeight_some, key]
    _ = (∑ k : κ, ENNReal.ofReal (1 / Fintype.card κ) •
          (T.marginal c (optionBernoulli κ)).map
            (fun x => T.ratio (some k, c) * x + T.trans (some k, c))) B := by
        rw [Measure.finsetSum_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (hg k) hB, marginal,
          Measure.map_apply hc (hg k hB)]

end IsHomogeneousOption

variable (T : System (Option κ))

/-- `τ_*ν` is carried by `Σ_Z`, for every measure `ν`. -/
theorem map_tau_subshift_compl (ν : Measure (ℤ → Option κ)) :
    ν.map (tau T.o) (subshift T.o)ᶜ = 0 := by
  rw [Measure.map_apply (measurable_tau T.o) (measurableSet_subshift T.o).compl]
  exact measure_mono_null (fun x hx => (hx (tau_mem_subshift x)).elim) measure_empty

/-- `ω_*ν` is carried by `Σ_Z`, for every measure `ν`. -/
theorem map_omega_subshift_compl (ν : Measure (ℤ → Option κ)) :
    ν.map (omega T.o) (subshift T.o)ᶜ = 0 := by
  rw [Measure.map_apply (measurable_omega T.o) (measurableSet_subshift T.o).compl]
  exact measure_mono_null (fun x hx => (hx (omega_mem_subshift x)).elim) measure_empty

/-- `h(τ_*ν_n) = h(ν_n)`, since `\overline{τ} ∘ τ` is the identity. The block entropies of
`τ_*ν_n` and of `ν_n` differ by at most `log 2`, and the limit exists for `ν_n`. -/
theorem entropy_map_tau [Nonempty κ] :
    entropy ((optionBernoulli κ).map (tau T.o)) = Real.log (Fintype.card κ) := by
  have hmap : ((optionBernoulli κ).map (tau T.o)).map unCode = optionBernoulli κ := by
    rw [Measure.map_map measurable_unCode (measurable_tau T.o)]
    exact Measure.map_id
  rw [← entropy_optionBernoulli (κ := κ)]
  refine entropy_eq_of_blockEntropy_close (C := Real.log 2)
    (tendsto_entropy (measurePreserving_shift_optionBernoulli 1)) fun n => ?_
  obtain ⟨h1, h2⟩ := blockEntropy_map_unCode T.o ((optionBernoulli κ).map (tau T.o))
    (T.map_tau_subshift_compl _) n
  rw [hmap] at h1 h2
  rw [abs_le]
  constructor <;> linarith [Real.log_nonneg (one_le_two (α := ℝ))]

/-- `h(ω_*ν_n) = h(ν_n)`. -/
theorem entropy_map_omega [Nonempty κ] :
    entropy ((optionBernoulli κ).map (omega T.o)) = Real.log (Fintype.card κ) := by
  have hmap : ((optionBernoulli κ).map (omega T.o)).map unCode = optionBernoulli κ := by
    rw [Measure.map_map measurable_unCode (measurable_omega T.o)]
    exact Measure.map_id
  rw [← entropy_optionBernoulli (κ := κ)]
  refine entropy_eq_of_blockEntropy_close (C := Real.log 2)
    (tendsto_entropy (measurePreserving_shift_optionBernoulli 1)) fun n => ?_
  obtain ⟨h1, h2⟩ := blockEntropy_map_unCode T.o ((optionBernoulli κ).map (omega T.o))
    (T.map_omega_subshift_compl _) n
  rw [hmap] at h1 h2
  rw [abs_le]
  constructor <;> linarith [Real.log_nonneg (one_le_two (α := ℝ))]

/-- `\overline{π}_*(τ_*ν) = (proj_x)_*(π_*ν)` for every probability measure `ν`:
`eq:commutative_diagram`. -/
theorem map_projBar_map_tau (ν : Measure (ℤ → Option κ)) [IsProbabilityMeasure ν] :
    (ν.map (tau T.o)).map T.projBar = T.marginal 0 ν := by
  obtain ⟨r, M, hS⟩ := T.exists_bounds
  rw [Measure.map_map hS.measurable_projBar (measurable_tau T.o), T.marginal_eq_map hS]
  rfl

/-- `\overline{π}_*(ω_*ν) = (proj_y)_*(π_*ν)` for every probability measure `ν`:
`eq:commutative_diagram`. -/
theorem map_projBar_map_omega (ν : Measure (ℤ → Option κ)) [IsProbabilityMeasure ν] :
    (ν.map (omega T.o)).map T.projBar = T.marginal 1 ν := by
  obtain ⟨r, M, hS⟩ := T.exists_bounds
  rw [Measure.map_map hS.measurable_projBar (measurable_omega T.o), T.marginal_eq_map hS]
  rfl

end System

end BoxLike
