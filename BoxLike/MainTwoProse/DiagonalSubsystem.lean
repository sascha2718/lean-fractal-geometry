module

/-
The finite diagonal subsystems of the proof of `thm:main2` in `sec:dimension_result_proof` and
their Bernoulli measures with equal weights. A subsystem of the proof is genuinely diagonal: all
its maps have the common diagonal linear part `diag(a_n, b_n)`, and the measure `ν_n` assigns
equal probabilities to them. For such a system the Lyapunov exponents of every invariant measure
are `log |a|` and `log |b|`, every sequence lies in `Σ^τ`, the slow subspace `V^1` is the vertical
axis, and the partitions of `sec:entropies` are given by the past and the coordinates of the
coded point. Both coordinate projections of `(π_n)_*ν_n` are self-similar measures with equal
weights, whose dimensions Kittle–Kogler give without exact overlaps.

* `uniformMeasure`, `uniformBernoulli`: the equal weights `1 / #κ` and the Bernoulli measure
  `ν_n`; it is invariant and ergodic, its cylinder measures are products, and its entropy is
  `log #κ = log #W_n`.
* `System.IsHomDiag`: all maps of the system have the linear part `diag(a, b)`.
* `System.IsHomDiag.eps_eq_zero`, `…tau_eq`, `…omega_eq`, `…matWord_eq`: no orientation
  changes, and `A_𝐮 = diag(a^n, b^n)` for a word of length `n`.
* `System.IsHomDiag.lyapunov₁_eq`, `…lyapunov₂_eq`: `λ_1 = log |a|`, `λ_2 = log |b|` for every
  invariant probability measure when `|b| ≤ |a|`.
* `System.IsHomDiag.mem_SigmaTau`, `…sigmaPrime_eq_univ`, `…slowAxis_eq_one`: `V^1` is the
  vertical axis at every sequence.
* `System.IsHomDiag.xi_one_eq`, `…xiPerp_eq`, `…xi_two_eq`: the atoms of `ξ_1`, `ξ_1^⊥`, `ξ_2`
  fix the past and the horizontal coordinate, the vertical coordinate, the planar point.
* `System.IsHomDiag.dimEntropy_zero`: `h_0(ν_n) = log #W_n`.
* `System.IsHomDiag.marginal_eq_sum`, `…marginal_isExactDim`: each coordinate marginal of
  `(π_n)_*ν_n` is the self-similar measure with equal weights, of dimension
  `min{1, log #W_n / (-log |a_n|)}` or `min{1, log #W_n / (-log |b_n|)}`.
-/
public import BoxLike.HomogeneousSubsystem
public import BoxLike.Literature

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

universe u

/-! ### The Bernoulli measure with equal weights -/

section Uniform

variable (κ : Type*) [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- The probability measure on `κ` with the equal weights `1 / #κ`. -/
noncomputable def uniformMeasure : Measure κ := weightMeasure fun _ : κ => 1 / Fintype.card κ

/-- The Bernoulli measure `ν_n` of the proof of `thm:main2`: equal probabilities on the maps
`φ_w`, `w ∈ W_n`, of the subsystem. -/
noncomputable def uniformBernoulli : Measure (ℤ → κ) := bernoulli (uniformMeasure κ)

variable {κ}

omit [MeasurableSpace κ] [MeasurableSingletonClass κ] in
/-- The equal weights sum to one. -/
theorem sum_uniform_weight [Nonempty κ] : ∑ _k : κ, (1 / Fintype.card κ : ℝ) = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div,
    div_self (Nat.cast_ne_zero.2 Fintype.card_ne_zero)]

/-- The equal weights define a probability measure. -/
instance isProbabilityMeasure_uniformMeasure [Nonempty κ] :
    IsProbabilityMeasure (uniformMeasure κ) :=
  isProbabilityMeasure_weightMeasure (fun _ => by positivity) sum_uniform_weight

/-- `ν_n` is a probability measure. -/
instance isProbabilityMeasure_uniformBernoulli [Nonempty κ] :
    IsProbabilityMeasure (uniformBernoulli κ) :=
  isProbabilityMeasure_bernoulli _

/-- Every symbol has the weight `1 / #κ`. -/
theorem measureReal_uniformMeasure_singleton (k : κ) :
    (uniformMeasure κ).real {k} = 1 / Fintype.card κ :=
  measureReal_weightMeasure_singleton (by positivity)

omit [MeasurableSingletonClass κ] in
/-- `ν_n` is invariant under every iterate of the shift. -/
theorem measurePreserving_shift_uniformBernoulli [Nonempty κ] (m : ℤ) :
    MeasurePreserving (shift m) (uniformBernoulli κ) (uniformBernoulli κ) :=
  measurePreserving_shift_bernoulli _ m

omit [MeasurableSingletonClass κ] in
/-- `ν_n` is ergodic. -/
theorem ergodic_shift_uniformBernoulli [Nonempty κ] : Ergodic (shift 1) (uniformBernoulli κ) :=
  ergodic_shift_bernoulli _

/-- The cylinder `[k]` of one symbol has the measure `1 / #κ`. -/
theorem measureReal_uniformBernoulli_cylinder_single [Nonempty κ] (k : κ) :
    (uniformBernoulli κ).real (cylinder ![k]) = 1 / Fintype.card κ := by
  rw [uniformBernoulli, measureReal_bernoulli_cylinder, Fin.prod_univ_one, Matrix.cons_val_zero,
    measureReal_uniformMeasure_singleton]

/-- The cylinder `[k]` of one symbol has the measure `1 / #κ`, in `ℝ≥0∞`. -/
theorem uniformBernoulli_cylinder_single [Nonempty κ] (k : κ) :
    uniformBernoulli κ (cylinder ![k]) = ENNReal.ofReal (1 / Fintype.card κ) := by
  rw [← ofReal_measureReal, measureReal_uniformBernoulli_cylinder_single]

/-- The cylinder measures of `ν_n` are products of the one-symbol measures. -/
theorem measureReal_uniformBernoulli_cylinder_prod [Nonempty κ] {n : ℕ} (w : Fin n → κ) :
    (uniformBernoulli κ).real (cylinder w) =
      ∏ k, (uniformBernoulli κ).real (cylinder ![w k]) := by
  rw [uniformBernoulli, measureReal_bernoulli_cylinder]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [measureReal_uniformMeasure_singleton, ← uniformBernoulli,
    measureReal_uniformBernoulli_cylinder_single]

/-- The entropy of `ν_n` is `log #W_n`. -/
theorem entropy_uniformBernoulli [Nonempty κ] :
    entropy (uniformBernoulli κ) = Real.log (Fintype.card κ) := by
  have hc : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [uniformBernoulli, entropy_bernoulli]
  simp only [measureReal_uniformMeasure_singleton, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [Real.negMulLog, one_div, Real.log_inv]
  field_simp

end Uniform

namespace System

/-! ### Homogeneous diagonal systems -/

variable {κ : Type*}

/-- A homogeneous diagonal system: every map has the diagonal linear part `diag(a, b)`. The
subsystems of the proof of `thm:main2` have this form. -/
structure IsHomDiag (T : System κ) (a b : ℝ) : Prop where
  /-- Every linear part is diagonal. -/
  o_eq : ∀ k, T.o k = 0
  /-- The first diagonal entry of every linear part is `a`. -/
  a_eq : ∀ k, T.a k = a
  /-- The second diagonal entry of every linear part is `b`. -/
  b_eq : ∀ k, T.b k = b

namespace IsHomDiag

variable {T : System κ} {a b : ℝ} (hT : T.IsHomDiag a b)
include hT

/-- `a ≠ 0`. -/
theorem a_ne_zero [Nonempty κ] : a ≠ 0 := by
  obtain ⟨k⟩ : Nonempty κ := inferInstance
  simpa [hT.a_eq k] using T.a_ne_zero k

/-- `b ≠ 0`. -/
theorem b_ne_zero [Nonempty κ] : b ≠ 0 := by
  obtain ⟨k⟩ : Nonempty κ := inferInstance
  simpa [hT.b_eq k] using T.b_ne_zero k

/-- `|a| < 1`. -/
theorem abs_a_lt_one [Nonempty κ] : |a| < 1 := by
  obtain ⟨k⟩ : Nonempty κ := inferInstance
  simpa [hT.a_eq k] using T.abs_a_lt_one k

/-- `|b| < 1`. -/
theorem abs_b_lt_one [Nonempty κ] : |b| < 1 := by
  obtain ⟨k⟩ : Nonempty κ := inferInstance
  simpa [hT.b_eq k] using T.abs_b_lt_one k

/-- `log |a| < 0`, so that `-log |a_n| > 0`. -/
theorem log_abs_a_neg [Nonempty κ] : Real.log |a| < 0 :=
  Real.log_neg (abs_pos.2 hT.a_ne_zero) hT.abs_a_lt_one

/-- `log |b| < 0`, so that `-log |b_n| > 0`. -/
theorem log_abs_b_neg [Nonempty κ] : Real.log |b| < 0 :=
  Real.log_neg (abs_pos.2 hT.b_ne_zero) hT.abs_b_lt_one

/-- The contraction ratio of the symbol `(k, c)` of the projective system is `a` on the first
axis and `b` on the second. -/
theorem ratio_eq (k : κ) (c : ZMod 2) : T.ratio (k, c) = if c = 0 then a else b := by
  simp only [ratio, hT.a_eq, hT.b_eq]

/-- The system is proximal when `|b| < |a|`. -/
theorem proximal [Nonempty κ] (hab : |b| < |a|) : T.Proximal :=
  HasProximalDiagonal.proximal ⟨Classical.arbitrary κ, hT.o_eq _, by
    rw [hT.a_eq, hT.b_eq]
    exact hab.ne'⟩

/-- No orientation changes: `ε_m(𝐢) = 0` for every `𝐢` and every `m ∈ ℤ`. -/
theorem eps_eq_zero (x : ℤ → κ) (m : ℤ) : eps T.o x m = 0 := by
  have h := eq_eps_of_succ T.o x (S := fun _ => 0) rfl fun m => by simp [hT.o_eq]
  exact (congrFun h m).symm

/-- `τ(𝐢)` keeps every symbol on the horizontal axis. -/
theorem tau_eq (x : ℤ → κ) : tau T.o x = fun k => (x k, 0) := by
  funext k
  rw [tau_apply, hT.eps_eq_zero]

/-- `ω(𝐢)` keeps every symbol on the vertical axis. -/
theorem omega_eq (x : ℤ → κ) : omega T.o x = fun k => (x k, 1) := by
  funext k
  rw [omega_apply, hT.eps_eq_zero, zero_add]

/-- Every word has an even number of anti-diagonal generators. -/
theorem oWord_eq_zero (u : List κ) : T.oWord u = 0 := by
  rw [oWord]
  exact List.sum_eq_zero fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact hT.o_eq i

/-- The product of the matrices of a word of length `n` is `diag(a^n, b^n)`. -/
theorem matWord_eq (u : List κ) : T.matWord u = boxMat 0 (a ^ u.length) (b ^ u.length) := by
  induction u with
  | nil =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | cons j u ih =>
    rw [matWord_cons, ih, mat, hT.o_eq, hT.a_eq, hT.b_eq, boxMat_mul, List.length_cons,
      pow_succ', pow_succ']
    simp

/-- `log α_1(A_𝐮) = |𝐮| log |a|` when `|b| ≤ |a|`. -/
theorem log_norm_matWord (hab : |b| ≤ |a|) (u : List κ) :
    Real.log ‖T.matWord u‖ = u.length * Real.log |a| := by
  rw [hT.matWord_eq u, norm_boxMat, abs_pow, abs_pow,
    max_eq_left (pow_le_pow_left₀ (abs_nonneg b) hab _), Real.log_pow]

/-- `log α_2(A_𝐮) = |𝐮| log |b|` when `|b| ≤ |a|`. -/
theorem log_abs_det_div_norm_matWord [Nonempty κ] (hab : |b| ≤ |a|) (u : List κ) :
    Real.log (|(T.matWord u).det| / ‖T.matWord u‖) = u.length * Real.log |b| := by
  rw [hT.matWord_eq u, norm_boxMat, abs_det_boxMat, abs_pow, abs_pow,
    max_eq_left (pow_le_pow_left₀ (abs_nonneg b) hab _),
    mul_div_cancel_left₀ _ (pow_ne_zero _ (abs_ne_zero.2 hT.a_ne_zero)), Real.log_pow]

/-- `g'_{τ_{-n}(𝐢) ⋯ τ_{-1}(𝐢)} = a^n`. -/
theorem gDeriv_pastWord_tau (x : ℤ → κ) (n : ℕ) : T.gDeriv (pastWord (tau T.o x) n) = a ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pastWord_succ, gDeriv_cons, ih, tau_apply, hT.eps_eq_zero, hT.ratio_eq, ite_eq_left rfl,
      pow_succ']

/-- `g'_{ω_{-n}(𝐢) ⋯ ω_{-1}(𝐢)} = b^n`. -/
theorem gDeriv_pastWord_omega (x : ℤ → κ) (n : ℕ) :
    T.gDeriv (pastWord (omega T.o x) n) = b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pastWord_succ, gDeriv_cons, ih, omega_apply, hT.eps_eq_zero, zero_add, hT.ratio_eq,
      ite_eq_right (by decide), pow_succ']

section Measure

variable [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- `λ_1(𝖠, μ) = log |a|` for every invariant probability measure `μ`, when `|b| ≤ |a|`; with
`-log |a_n|` in the proof of `thm:main2`. -/
theorem lyapunov₁_eq (hab : |b| ≤ |a|) {μ : Measure (ℤ → κ)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) : T.lyapunov₁ μ = Real.log |a| := by
  refine tendsto_nhds_unique (T.tendsto_lyapunov₁ hinv) (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ne_atTop 0] with n hn
  have h : ∀ x : ℤ → κ, Real.log ‖T.matWord (futureWord x n)‖ = n * Real.log |a| := fun x => by
    rw [hT.log_norm_matWord hab, length_futureWord]
  simp only [h, integral_const, probReal_univ, one_smul]
  rw [mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 hn)]

/-- `λ_2(𝖠, μ) = log |b|` for every invariant probability measure `μ`, when `|b| ≤ |a|`; with
`-log |b_n|` in the proof of `thm:main2`. -/
theorem lyapunov₂_eq (hab : |b| ≤ |a|) {μ : Measure (ℤ → κ)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) : T.lyapunov₂ μ = Real.log |b| := by
  have : Nonempty κ := nonempty_of_measure μ
  refine tendsto_nhds_unique (T.tendsto_lyapunov₂ hinv) (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ne_atTop 0] with n hn
  have h : ∀ x : ℤ → κ, Real.log (|(T.matWord (futureWord x n)).det| /
      ‖T.matWord (futureWord x n)‖) = n * Real.log |b| := fun x => by
    rw [hT.log_abs_det_div_norm_matWord hab, length_futureWord]
  simp only [h, integral_const, probReal_univ, one_smul]
  rw [mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 hn)]

/-- `λ_2(𝖠, μ) < λ_1(𝖠, μ)` when `|b| < |a|`. -/
theorem lyapunov₂_lt_lyapunov₁ (hab : |b| < |a|) {μ : Measure (ℤ → κ)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) : T.lyapunov₂ μ < T.lyapunov₁ μ := by
  have : Nonempty κ := nonempty_of_measure μ
  rw [hT.lyapunov₁_eq hab.le hinv, hT.lyapunov₂_eq hab.le hinv]
  exact Real.log_lt_log (abs_pos.2 hT.b_ne_zero) hab

/-- Every sequence lies in `Σ^τ`: the backward growth rates of `e_1` and `e_2` are `log |a|` and
`log |b|` exactly, so the one-dimensional Oseledets subspace `V^1` of the diagonal subsystem is
the vertical axis (proof of `thm:main2`). -/
theorem mem_SigmaTau (hab : |b| ≤ |a|) {μ : Measure (ℤ → κ)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (x : ℤ → κ) : x ∈ T.SigmaTau μ := by
  simp only [SigmaTau, Set.mem_ofPred_eq, HasBackRate, hT.lyapunov₁_eq hab hinv,
    hT.lyapunov₂_eq hab hinv, hT.gDeriv_pastWord_tau, hT.gDeriv_pastWord_omega]
  exact ⟨tendsto_log_abs_pow_div a, tendsto_log_abs_pow_div b⟩

/-- `Σ'` is the whole shift space. -/
theorem sigmaPrime_eq_univ (hab : |b| ≤ |a|) {μ : Measure (ℤ → κ)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) : T.SigmaPrime μ = Set.univ :=
  Set.eq_univ_of_forall fun x => Or.inl (hT.mem_SigmaTau hab hinv x)

/-- The slow axis is the vertical axis at every sequence. -/
theorem slowAxis_eq_one (hab : |b| ≤ |a|) {μ : Measure (ℤ → κ)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (x : ℤ → κ) : T.slowAxis μ x = 1 := by
  rw [slowAxis, ite_eq_left (hT.mem_SigmaTau hab hinv x)]

/-- The atom `ξ_1(𝐢)` consists of the sequences with the past of `𝐢` whose coded point has the
horizontal coordinate of `π(𝐢)`, since `V^1` is the vertical axis. -/
theorem xi_one_eq (hab : |b| ≤ |a|) {μ : Measure (ℤ → κ)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (x : ℤ → κ) :
    T.xi μ 1 x = {y | SamePast y x ∧ (T.proj y).1 = (T.proj x).1} := by
  unfold xi
  rw [hT.sigmaPrime_eq_univ hab hinv, atomsOn_of_mem (Set.mem_univ x), Set.inter_univ]
  ext y
  simp only [Set.mem_ofPred_eq, oseledets, hT.slowAxis_eq_one hab hinv,
    show (1 : ZMod 2) + 1 = 0 from by decide, coord_zero, Prod.fst_sub, sub_eq_zero]

/-- The atom `ξ_1^⊥(𝐢)` consists of the sequences with the past of `𝐢` whose coded point has
the vertical coordinate of `π(𝐢)`. -/
theorem xiPerp_eq (hab : |b| ≤ |a|) {μ : Measure (ℤ → κ)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (x : ℤ → κ) :
    T.xiPerp μ x = {y | SamePast y x ∧ (T.proj y).2 = (T.proj x).2} := by
  unfold xiPerp
  rw [hT.sigmaPrime_eq_univ hab hinv, atomsOn_of_mem (Set.mem_univ x), Set.inter_univ]
  ext y
  simp only [Set.mem_ofPred_eq, hT.slowAxis_eq_one hab hinv, coord_one, Prod.snd_sub,
    sub_eq_zero]

/-- The atom `ξ_2(𝐢)` consists of the sequences with the past of `𝐢` whose coded point is
`π(𝐢)`. -/
theorem xi_two_eq (hab : |b| ≤ |a|) {μ : Measure (ℤ → κ)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (x : ℤ → κ) :
    T.xi μ 2 x = {y | SamePast y x ∧ T.proj y = T.proj x} := by
  unfold xi
  rw [hT.sigmaPrime_eq_univ hab hinv, atomsOn_of_mem (Set.mem_univ x), Set.inter_univ]
  ext y
  simp only [Set.mem_ofPred_eq, oseledets, Set.mem_singleton_iff, sub_eq_zero]

/-- `h_0(ν_n) = log #W_n` in the proof of `thm:main2`. -/
theorem dimEntropy_zero [Nonempty κ] (hab : |b| ≤ |a|) :
    T.dimEntropy (uniformBernoulli κ) 0 = Real.log (Fintype.card κ) := by
  rw [T.dimEntropy_zero_eq_entropy' _ (measurePreserving_shift_uniformBernoulli 1)
    (by rw [hT.sigmaPrime_eq_univ hab (measurePreserving_shift_uniformBernoulli 1),
      Set.compl_univ, measure_empty]), entropy_uniformBernoulli]

/-- Each coordinate marginal of `ν_n` is the self-similar measure of the coordinate maps
`g_{(k, c)}` of the subsystem with equal weights (proof of `thm:main2`): the stationarity
equation, from the invariance of the projection of a Bernoulli measure and
`eq:phi_def_by_g`. -/
theorem marginal_eq_sum [Nonempty κ] (c : ZMod 2) :
    T.marginal c (uniformBernoulli κ) =
      ∑ k : κ, ENNReal.ofReal (1 / Fintype.card κ) •
        (T.marginal c (uniformBernoulli κ)).map
          (fun x => T.ratio (k, c) * x + T.trans (k, c)) := by
  have hc : Measurable (coord c) := by
    unfold coord
    split_ifs
    · exact measurable_fst
    · exact measurable_snd
  have hphi : ∀ i, Measurable (T.phi i) := fun i => (T.continuous_phi i).measurable
  have hg : ∀ k : κ, Measurable fun x : ℝ => T.ratio (k, c) * x + T.trans (k, c) :=
    fun k => (measurable_id.const_mul _).add_const _
  have hinv := T.isInvariantMeasure_map_proj (measurePreserving_shift_uniformBernoulli 1)
    fun n w => measureReal_uniformBernoulli_cylinder_prod w
  unfold IsInvariantMeasure at hinv
  refine Measure.ext fun B hB => ?_
  have key : ∀ k : κ, T.phi k ⁻¹' (coord c ⁻¹' B) =
      coord c ⁻¹' ((fun x => T.ratio (k, c) * x + T.trans (k, c)) ⁻¹' B) := by
    intro k
    ext z
    simp only [Set.mem_preimage, coord_phi, hT.o_eq, add_zero, g]
  calc T.marginal c (uniformBernoulli κ) B
      = (uniformBernoulli κ).map T.proj (coord c ⁻¹' B) := by
        rw [marginal, Measure.map_apply hc hB]
    _ = ∑ i, uniformBernoulli κ (cylinder ![i]) *
          (uniformBernoulli κ).map T.proj (T.phi i ⁻¹' (coord c ⁻¹' B)) := by
        conv_lhs => rw [hinv]
        rw [Measure.finsetSum_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (hphi i) (hc hB)]
    _ = ∑ k : κ, ENNReal.ofReal (1 / Fintype.card κ) *
          (uniformBernoulli κ).map T.proj
            (coord c ⁻¹' ((fun x => T.ratio (k, c) * x + T.trans (k, c)) ⁻¹' B)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [uniformBernoulli_cylinder_single, key]
    _ = (∑ k : κ, ENNReal.ofReal (1 / Fintype.card κ) •
          (T.marginal c (uniformBernoulli κ)).map
            (fun x => T.ratio (k, c) * x + T.trans (k, c))) B := by
        rw [Measure.finsetSum_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (hg k) hB, marginal,
          Measure.map_apply hc (hg k hB)]

end Measure

end IsHomDiag

end System

namespace System.IsHomDiag

variable {κ : Type u} [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ] [Nonempty κ]
  {T : System κ} {a b : ℝ} (hT : T.IsHomDiag a b)
include hT

/-- The dimension of a coordinate marginal of `ν_n` (proof of `thm:main2`): the marginal is the
self-similar measure with equal weights on the `#κ` coordinate maps `g_{(k, c)}`, all with the
ratio `a` for `c = 0` and `b` for `c = 1`; without exact overlaps, that is, when the words in
these maps compose injectively, Kittle–Kogler give `dim = min{1, log #W_n / (-log |r|)}` for the
ratio `r = a` or `r = b`.
Depends on: `KittleKoglerDimension`. -/
theorem marginal_isExactDim (hkk : KittleKoglerDimension.{u}) (c : ZMod 2)
    (hfree : Function.Injective
      (simWord (fun _ : κ => if c = 0 then a else b) (fun k => T.trans (k, c)))) :
    IsExactDim (T.marginal c (uniformBernoulli κ))
      (min 1 (Real.log (Fintype.card κ) / -Real.log |if c = 0 then a else b|)) := by
  have hr0 : (if c = 0 then a else b) ≠ 0 := by
    split_ifs
    exacts [hT.a_ne_zero, hT.b_ne_zero]
  have hr1 : |if c = 0 then a else b| < 1 := by
    split_ifs
    exacts [hT.abs_a_lt_one, hT.abs_b_lt_one]
  have hp : ∀ _ : κ, 0 < (1 / Fintype.card κ : ℝ) := fun _ => by
    have : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.2 Fintype.card_pos
    positivity
  have : IsProbabilityMeasure (T.marginal c (uniformBernoulli κ)) := by
    unfold System.marginal
    infer_instance
  have hstat := hT.marginal_eq_sum c
  simp only [hT.ratio_eq] at hstat
  have key := hkk (fun _ : κ => if c = 0 then a else b) (fun k => T.trans (k, c))
    (fun _ => 1 / Fintype.card κ) (fun _ => hr0) (fun _ => hr1) hp sum_uniform_weight hfree
    (T.marginal c (uniformBernoulli κ)) hstat
  have h1 : ∑ _ : κ, Real.negMulLog (1 / Fintype.card κ : ℝ) = Real.log (Fintype.card κ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.negMulLog, one_div, Real.log_inv]
    field_simp
  have h2 : ∑ _ : κ, (1 / Fintype.card κ : ℝ) * Real.log |if c = 0 then a else b| =
      Real.log |if c = 0 then a else b| := by
    rw [← Finset.sum_mul, sum_uniform_weight, one_mul]
  simpa only [h1, h2] using key

end System.IsHomDiag

end BoxLike
