module

/-
The Oseledets filtration of `sec:lyapunov_exponents` (tex lines 1508 to 1553) and
`thm:lyapunov_exponents_via_g_system` in the form of the article. The article takes from
Oseledets' theorem a Borel set `Σ'` with `σ(Σ') = Σ'` and `μ(Σ') = 1`, saturated with respect
to the past, and measurable subspaces `{0} = V_𝐢^2 ⊊ V_𝐢^1 ⊊ V_𝐢^0 = ℝ²` with the properties
(V1) to (V3) at every `𝐢 ∈ Σ'`, and defines `Σ^τ` and `Σ^ω` by the position of `V_𝐢^1`
(`eq:sigma_tau_omega`). Here such a choice is the structure `MatrixTuple.OseledetsSet`, for an
arbitrary planar tuple. For a box-like tuple every choice is identified with the coordinate
filtration on the box-like set `Σ'` of `BoxLike/SlowAxis.lean`, and that set with that
filtration is one choice; this proves the box-like case of Oseledets' theorem without a
literature hypothesis. The rate-defined sets `S.SigmaTau μ`, `S.SigmaOmega μ` are the article's
sets `Σ^τ`, `Σ^ω` for this choice, and agree with them modulo `μ`-null sets for every choice.

* `eucNorm`, `eucNorm_sq`: the Euclidean norm `|v|` of `v ∈ ℝ²`.
* `tendsto_log_sqrt_div`: the growth rate of `√((p α_n)² + (q β_n)²)` is the larger rate.
* `axisVec`, `axis`, `mem_axis_zero_iff`, `mem_axis_one_iff`: the coordinate axes
  `span{(1,0)}` and `span{(0,1)}`.
* `MatrixTuple.HasEucPastRate`: the backward growth rate `lim_n n⁻¹ log |A_{i_{-n}} ⋯ A_{i_{-1}} v|`
  of (V3); `MatrixTuple.hasEucPastRate_shift_neg_one_iff`: its behaviour under `σ^{-1}`.
* `MatrixTuple.OseledetsSet`: a choice of `Σ'` and of the filtration with the properties
  (V1), (V2), (V3), Borel, invariant, of full measure and saturated with respect to the past.
* `MatrixTuple.OseledetsSet.mem_V_zero_iff`, `MatrixTuple.OseledetsSet.mem_V_one_iff`:
  `eq:V_lyapunov`; `MatrixTuple.OseledetsSet.V_one_eq_of_samePast`: `V_𝐢^1` depends only on
  `𝐢^-`; `MatrixTuple.OseledetsSet.V_one_eq`: two choices agree on their common points.
* `MatrixTuple.OseledetsSet.sigmaTau`, `MatrixTuple.OseledetsSet.sigmaOmega`:
  `eq:sigma_tau_omega`, and `MatrixTuple.OseledetsSet.disjoint_sigmaTau_sigmaOmega`.
* `System.eucNorm_matWord_pastWord_e1`, `System.eucNorm_matWord_pastWord_e2`,
  `System.hasEucPastRate_e1_iff`, `System.hasEucPastRate_e2_iff`:
  `thm:matrix_products_g_derivatives` with the Euclidean norm.
* `System.hasEucPastRate_of_snd_eq_zero`, `System.hasEucPastRate_of_fst_eq_zero`,
  `System.hasEucPastRate_of_ne_zero`: the backward rate of every vector of `ℝ²` from the two
  coordinate rates.
* `System.oseledetsSub`, `System.hasEucPastRate_of_mem_oseledetsSub_one`,
  `System.hasEucPastRate_of_notMem_oseledetsSub_one`, `System.mem_oseledetsSub_one_iff`: the
  coordinate filtration on the box-like `Σ'` and its all-vector property (V3).
* `System.map_oseledetsSub`, `System.finrank_oseledetsSub`, `System.measurableSet_oseledetsSub`:
  (V1), (V2) and measurability of the coordinate filtration.
* `System.oseledetsSet`: a choice of `Σ'` for a box-like tuple, with `Σ' = S.SigmaPrime μ`.
* `System.V_one_eq_axis`, `System.carrier_subset_SigmaPrime`, `System.V_eq_oseledetsSub`,
  `System.mem_V_iff_mem_oseledets`: for every choice `V_𝐢^1` is a coordinate axis (tex lines
  1614 to 1616) and the filtration is the coordinate filtration.
* `System.sigmaTau_eq_inter`, `System.sigmaOmega_eq_inter`, `System.sigmaTau_ae_eq`,
  `System.sigmaOmega_ae_eq`, `System.sigmaTau_union_sigmaOmega`, `System.carrier_ae_eq`: the
  article's `Σ'`, `Σ^τ`, `Σ^ω` agree with the box-like sets on `Σ'`, hence modulo `μ`-null sets,
  and `eq:tau_omega_partition2`.
* `System.sigmaTau_oseledetsSet`, `System.sigmaOmega_oseledetsSet`: for the box-like choice the
  article's sets are `S.SigmaTau μ` and `S.SigmaOmega μ`.
* `System.shift_mem_sigmaTau_iff`, `System.measurableSet_sigmaTau`,
  `System.measurableSet_sigmaOmega`, `System.measure_sigmaTau`, `System.measure_sigmaOmega`:
  invariance and measurability of the article's sets.
* `System.lyapunov_exponents_via_g_system_oseledets`,
  `System.lyapunov_exponents_via_g_system_manuscript`: `thm:lyapunov_exponents_via_g_system`
  for every choice of `Σ'`, by the prose proof, with the existence of a choice.
* `System.sigma_tau_omega_positive_oseledets`: `thm:sigma_tau_omega_positive_eq_measure` for the
  article's sets.
-/
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.SigmaMeasure
public import BoxLike.MatrixTuple
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set Matrix Module

/-! ### The Euclidean norm on `ℝ²` -/

/-- The Euclidean norm `|v|` of `v ∈ ℝ²` of `sec:lyapunov_exponents`, the norm of
`EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def eucNorm (v : Fin 2 → ℝ) : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 2))‖

/-- `|v| = √(v_1² + v_2²)`. -/
theorem eucNorm_eq (v : Fin 2 → ℝ) : eucNorm v = √(v 0 ^ 2 + v 1 ^ 2) := by
  rw [eucNorm, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two]

/-- `|v|² = v_1² + v_2²`. -/
theorem eucNorm_sq (v : Fin 2 → ℝ) : eucNorm v ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  rw [eucNorm_eq, Real.sq_sqrt (by positivity)]

/-- The Euclidean norm is non-negative. -/
theorem eucNorm_nonneg (v : Fin 2 → ℝ) : 0 ≤ eucNorm v := norm_nonneg _

/-- A vector with a vanishing coordinate has Euclidean norm the sum of the moduli of its
coordinates; this is the form of `thm:matrix_products_g_derivatives` in `BoxLike/System.lean`. -/
theorem eucNorm_of_coord_eq_zero {v : Fin 2 → ℝ} (h : v 0 = 0 ∨ v 1 = 0) :
    eucNorm v = |v 0| + |v 1| := by
  rcases h with h | h <;> simp [eucNorm_eq, h, Real.sqrt_sq_eq_abs]

/-- A vector of `ℝ²` with a vanishing first coordinate is non-zero exactly when its second
coordinate is non-zero. -/
theorem snd_ne_zero_of_fst_eq_zero {v : Fin 2 → ℝ} (hv : v ≠ 0) (h : v 0 = 0) : v 1 ≠ 0 := by
  intro h1
  apply hv
  funext j
  fin_cases j
  · exact h
  · exact h1

/-- A vector of `ℝ²` with a vanishing second coordinate is non-zero exactly when its first
coordinate is non-zero. -/
theorem fst_ne_zero_of_snd_eq_zero {v : Fin 2 → ℝ} (hv : v ≠ 0) (h : v 1 = 0) : v 0 ≠ 0 := by
  intro h0
  apply hv
  funext j
  fin_cases j
  · exact h0
  · exact h

/-! ### Growth rates -/

/-- A positive constant factor does not change a growth rate `lim_n n⁻¹ log α_n`. -/
theorem tendsto_log_const_mul_div {α : ℕ → ℝ} (hα : ∀ n, 0 < α n) {a p : ℝ} (hp : 0 < p)
    (ha : Tendsto (fun n : ℕ => Real.log (α n) / n) atTop (𝓝 a)) :
    Tendsto (fun n : ℕ => Real.log (p * α n) / n) atTop (𝓝 a) := by
  have h := (tendsto_const_div_atTop_nhds_zero_nat (Real.log p)).add ha
  rw [zero_add] at h
  refine h.congr fun n => ?_
  rw [Real.log_mul hp.ne' (hα n).ne', add_div]

/-- The growth rate of `√((p α_n)² + (q β_n)²)` for `p, q > 0` is the larger of the growth
rates of `α_n` and `β_n`: the root lies between `max{p α_n, q β_n}` and twice that maximum. -/
theorem tendsto_log_sqrt_div {α β : ℕ → ℝ} (hα : ∀ n, 0 < α n) (hβ : ∀ n, 0 < β n)
    {a b p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (ha : Tendsto (fun n : ℕ => Real.log (α n) / n) atTop (𝓝 a))
    (hb : Tendsto (fun n : ℕ => Real.log (β n) / n) atTop (𝓝 b)) :
    Tendsto (fun n : ℕ => Real.log √((p * α n) ^ 2 + (q * β n) ^ 2) / n) atTop
      (𝓝 (max a b)) := by
  have hA : ∀ n, 0 < p * α n := fun n => mul_pos hp (hα n)
  have hB : ∀ n, 0 < q * β n := fun n => mul_pos hq (hβ n)
  have hM : Tendsto (fun n : ℕ => Real.log (max (p * α n) (q * β n)) / n) atTop
      (𝓝 (max a b)) := by
    refine ((tendsto_log_const_mul_div hα hp ha).max
      (tendsto_log_const_mul_div hβ hq hb)).congr fun n => ?_
    rw [log_max_of_pos (hA n) (hB n), max_div_div_right (Nat.cast_nonneg n)]
  have hU : Tendsto (fun n : ℕ => Real.log (2 * max (p * α n) (q * β n)) / n) atTop
      (𝓝 (max a b)) :=
    tendsto_log_const_mul_div (fun n => lt_max_of_lt_left (hA n)) two_pos hM
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hM hU (fun n => ?_) (fun n => ?_)
  · refine div_le_div_of_nonneg_right (Real.log_le_log (lt_max_of_lt_left (hA n)) ?_)
      (Nat.cast_nonneg n)
    rw [max_le_iff]
    constructor
    · exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (q * β n)])
    · exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (p * α n)])
  · refine div_le_div_of_nonneg_right (Real.log_le_log (Real.sqrt_pos.2 (by
      nlinarith [sq_nonneg (q * β n), hA n])) ?_) (Nat.cast_nonneg n)
    rw [Real.sqrt_le_left (mul_nonneg zero_le_two (le_max_of_le_left (hA n).le))]
    have h1 := le_max_left (p * α n) (q * β n)
    have h2 := le_max_right (p * α n) (q * β n)
    nlinarith [hA n, hB n]

/-- Shifting the index by one does not change a growth rate `lim_n n⁻¹ f(n)`. -/
theorem tendsto_succ_div_iff (f : ℕ → ℝ) (l : ℝ) :
    Tendsto (fun n : ℕ => f (n + 1) / n) atTop (𝓝 l) ↔
      Tendsto (fun n : ℕ => f n / n) atTop (𝓝 l) := by
  rw [← tendsto_add_div_succ_iff (fun n => f (n + 1)) 0 l,
    ← tendsto_add_atTop_iff_nat (f := fun n : ℕ => f n / n) 1]
  refine tendsto_congr fun n => ?_
  push_cast
  rw [add_zero]

/-! ### The coordinate axes -/

/-- The unit vector `(1, 0)` for `c = 0` and `(0, 1)` for `c = 1`. -/
def axisVec (c : ZMod 2) : Fin 2 → ℝ := if c = 0 then ![1, 0] else ![0, 1]

/-- The coordinate axis `span{(1, 0)}`, the `x`-axis, for `c = 0` and `span{(0, 1)}`, the
`y`-axis, for `c = 1`, as subspaces of `ℝ²` (`eq:sigma_tau_omega`). -/
noncomputable def axis (c : ZMod 2) : Submodule ℝ (Fin 2 → ℝ) := ℝ ∙ axisVec c

/-- The `x`-axis is the set of vectors with vanishing second coordinate. -/
theorem mem_axis_zero_iff {v : Fin 2 → ℝ} : v ∈ axis 0 ↔ v 1 = 0 := by
  simp only [axis, axisVec, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    simp
  · intro h
    refine ⟨v 0, ?_⟩
    funext j
    fin_cases j <;> simp [h]

/-- The `y`-axis is the set of vectors with vanishing first coordinate. -/
theorem mem_axis_one_iff {v : Fin 2 → ℝ} : v ∈ axis 1 ↔ v 0 = 0 := by
  simp only [axis, axisVec, one_ne_zero, ↓reduceIte, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    simp
  · intro h
    refine ⟨v 1, ?_⟩
    funext j
    fin_cases j <;> simp [h]

/-- The coordinate axes are lines. -/
theorem finrank_axis (c : ZMod 2) : finrank ℝ (axis c) = 1 := by
  refine finrank_span_singleton ?_
  unfold axisVec
  split_ifs
  · intro h
    simpa using congrFun h 0
  · intro h
    simpa using congrFun h 1

/-- The two coordinate axes are different. -/
theorem axis_zero_ne_axis_one : axis 0 ≠ axis 1 := by
  intro h
  have h1 : (![1, 0] : Fin 2 → ℝ) ∈ axis 0 := mem_axis_zero_iff.2 (by simp)
  rw [h, mem_axis_one_iff] at h1
  simp at h1

/-- The unit vector `(1, 0)` lies on the `x`-axis and not on the `y`-axis. -/
theorem e1_mem_axis : (![1, 0] : Fin 2 → ℝ) ∈ axis 0 ∧ (![1, 0] : Fin 2 → ℝ) ∉ axis 1 := by
  rw [mem_axis_zero_iff, mem_axis_one_iff]
  simp

/-- The unit vector `(0, 1)` lies on the `y`-axis and not on the `x`-axis. -/
theorem e2_mem_axis : (![0, 1] : Fin 2 → ℝ) ∈ axis 1 ∧ (![0, 1] : Fin 2 → ℝ) ∉ axis 0 := by
  rw [mem_axis_zero_iff, mem_axis_one_iff]
  simp

/-! ### The Oseledets filtration of a planar tuple -/

namespace MatrixTuple

variable {ι : Type*} (A : ι → Matrix (Fin 2) (Fin 2) ℝ)

/-- The backward growth rate of `v ∈ ℝ²` along `𝐢` of (V3) in `sec:lyapunov_exponents`:
`lim_n n⁻¹ log |A_{i_{-n}} ⋯ A_{i_{-1}} v| = l`, with the Euclidean norm. -/
def HasEucPastRate (x : ℤ → ι) (v : Fin 2 → ℝ) (l : ℝ) : Prop :=
  Tendsto (fun n : ℕ => Real.log (eucNorm (word A (pastWord x n) *ᵥ v)) / n) atTop (𝓝 l)

variable {A}

/-- The backward growth rate is unique. -/
theorem HasEucPastRate.unique {x : ℤ → ι} {v : Fin 2 → ℝ} {l l' : ℝ} (h : HasEucPastRate A x v l)
    (h' : HasEucPastRate A x v l') : l = l' :=
  tendsto_nhds_unique h h'

/-- The backward growth rate depends only on the past `𝐢^-` (tex lines 1523 to 1529). -/
theorem hasEucPastRate_congr {x y : ℤ → ι} (h : SamePast x y) (v : Fin 2 → ℝ) (l : ℝ) :
    HasEucPastRate A x v l ↔ HasEucPastRate A y v l := by
  simp only [HasEucPastRate, pastWord_congr h]

/-- Appending one matrix on the right: the backward rate of `A_{i_{-1}} v` along `σ^{-1}(𝐢)` is
the backward rate of `v` along `𝐢`, as in (V1). -/
theorem hasEucPastRate_shift_neg_one_iff (x : ℤ → ι) (v : Fin 2 → ℝ) (l : ℝ) :
    HasEucPastRate A (shift (-1) x) (A (x (-1)) *ᵥ v) l ↔ HasEucPastRate A x v l := by
  have hw : ∀ n, pastWord x (n + 1) = pastWord (shift (-1) x) n ++ [x (-1)] := fun n => by
    have h := pastWord_shift_one (shift (-1) x) n
    rwa [shift_shift, neg_add_cancel, shift_zero, shift_apply, add_zero] at h
  unfold HasEucPastRate
  rw [← tendsto_succ_div_iff (fun n => Real.log (eucNorm (word A (pastWord x n) *ᵥ v)))]
  refine tendsto_congr fun n => ?_
  rw [hw, word_append, mulVec_mulVec]
  simp [word]

variable (A) [MeasurableSpace ι]

/-- A choice of the set `Σ'` and of the Oseledets filtration of `sec:lyapunov_exponents` (tex
lines 1585 to 1606 and 1617 to 1618) for the tuple `𝖠` and the measure `μ`: a Borel set `Σ'`
with `σ(Σ') = Σ'` and `μ(Σ') = 1`, containing every sequence sharing the past of one of its
elements, and subspaces `V_𝐢^0, V_𝐢^1, V_𝐢^2` of `ℝ²` with, at every `𝐢 ∈ Σ'`,
(V1) `A_{i_{-1}} V_𝐢^i = V_{σ^{-1}(𝐢)}^i`, (V2) `dim V_𝐢^i = 2 - i`, and (V3)
`lim_n n⁻¹ log |A_{i_{-n}} ⋯ A_{i_{-1}} v| = λ_{i+1}(𝖠, μ)` for `i ∈ {0, 1}` and
`v ∈ V_𝐢^i ∖ V_𝐢^{i+1}`. The subspaces are measurable in the sense that the graph
`{(𝐢, v) : v ∈ V_𝐢^i}` is a Borel set. The chain `{0} = V_𝐢^2 ⊊ V_𝐢^1 ⊊ V_𝐢^0 = ℝ²` follows from
(V2) (`V_zero_eq_top`, `V_two_eq_bot`). Indices above `2` are not used. -/
structure OseledetsSet (μ : Measure (ℤ → ι)) where
  /-- The set `Σ'`. -/
  carrier : Set (ℤ → ι)
  /-- The subspaces `V_𝐢^i`, for `i ∈ {0, 1, 2}`. -/
  V : (ℤ → ι) → ℕ → Submodule ℝ (Fin 2 → ℝ)
  /-- `Σ'` is a Borel set. -/
  measurableSet_carrier : MeasurableSet carrier
  /-- `σ(Σ') = Σ'`. -/
  image_shift : shift 1 '' carrier = carrier
  /-- `μ(Σ') = 1`, for the probability measure `μ`. -/
  measure_compl : μ carrierᶜ = 0
  /-- `Σ'` contains every sequence sharing the past of one of its elements (tex lines 1540
  to 1618). -/
  mem_of_samePast : ∀ x ∈ carrier, ∀ y, SamePast y x → y ∈ carrier
  /-- The subspaces are measurable: their graphs are Borel. -/
  measurableSet_V : ∀ i ≤ 2, MeasurableSet {p : (ℤ → ι) × (Fin 2 → ℝ) | p.2 ∈ V p.1 i}
  /-- (V1): `A_{i_{-1}} V_𝐢^i = V_{σ^{-1}(𝐢)}^i`. -/
  map_V : ∀ x ∈ carrier, ∀ i ≤ 2, (V x i).map (A (x (-1))).mulVecLin = V (shift (-1) x) i
  /-- (V2): `dim V_𝐢^i = 2 - i`. -/
  finrank_V : ∀ x ∈ carrier, ∀ i ≤ 2, finrank ℝ (V x i) = 2 - i
  /-- (V3) for `i = 0`: every `v ∈ V_𝐢^0 ∖ V_𝐢^1` grows backwards at the rate `λ_1(𝖠, μ)`. -/
  rate_zero : ∀ x ∈ carrier, ∀ v ∈ V x 0, v ∉ V x 1 → HasEucPastRate A x v (lyapunov₁ A μ)
  /-- (V3) for `i = 1`: every `v ∈ V_𝐢^1 ∖ V_𝐢^2` grows backwards at the rate `λ_2(𝖠, μ)`. -/
  rate_one : ∀ x ∈ carrier, ∀ v ∈ V x 1, v ∉ V x 2 → HasEucPastRate A x v (lyapunov₂ A μ)

namespace OseledetsSet

variable {A} {μ : Measure (ℤ → ι)} (O : OseledetsSet A μ)

/-- `σ(Σ') = Σ'` in the form of membership: `σ(𝐢) ∈ Σ'` exactly when `𝐢 ∈ Σ'`. -/
theorem shift_mem_iff (x : ℤ → ι) : shift 1 x ∈ O.carrier ↔ x ∈ O.carrier := by
  constructor
  · intro h
    rw [← O.image_shift] at h
    obtain ⟨y, hy, hxy⟩ := h
    have : y = x := by
      have := congrArg (shift (-1)) hxy
      rwa [shift_shift, shift_shift, add_neg_cancel, shift_zero, shift_zero] at this
    exact this ▸ hy
  · intro h
    rw [← O.image_shift]
    exact ⟨x, h, rfl⟩

/-- `σ^{-1}(Σ') = Σ'`: `σ^{-1}(𝐢) ∈ Σ'` exactly when `𝐢 ∈ Σ'`. -/
theorem shift_neg_one_mem_iff (x : ℤ → ι) : shift (-1) x ∈ O.carrier ↔ x ∈ O.carrier := by
  rw [← O.shift_mem_iff, shift_shift, neg_add_cancel, shift_zero]

/-- `V_𝐢^0 = ℝ²`, from (V2). -/
theorem V_zero_eq_top {x : ℤ → ι} (hx : x ∈ O.carrier) : O.V x 0 = ⊤ := by
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [O.finrank_V x hx 0 (by norm_num), finrank_fin_fun]

/-- `V_𝐢^2 = {0}`, from (V2). -/
theorem V_two_eq_bot {x : ℤ → ι} (hx : x ∈ O.carrier) : O.V x 2 = ⊥ := by
  rw [← Submodule.finrank_eq_zero, O.finrank_V x hx 2 le_rfl]

/-- `V_𝐢^1` is a line: it contains a non-zero vector. -/
theorem exists_mem_V_one_ne_zero {x : ℤ → ι} (hx : x ∈ O.carrier) :
    ∃ v ∈ O.V x 1, v ≠ 0 := by
  refine Submodule.exists_mem_ne_zero_of_ne_bot fun h => ?_
  have h1 := O.finrank_V x hx 1 (by norm_num)
  rw [h, finrank_bot] at h1
  norm_num at h1

/-- (V3) for `i = 0` with `V_𝐢^0 = ℝ²`: every `v ∉ V_𝐢^1` grows backwards at the rate
`λ_1(𝖠, μ)`. -/
theorem hasEucPastRate_of_notMem {x : ℤ → ι} (hx : x ∈ O.carrier) {v : Fin 2 → ℝ}
    (hv : v ∉ O.V x 1) : HasEucPastRate A x v (lyapunov₁ A μ) :=
  O.rate_zero x hx v (by rw [O.V_zero_eq_top hx]; trivial) hv

/-- (V3) for `i = 1` with `V_𝐢^2 = {0}`: every non-zero `v ∈ V_𝐢^1` grows backwards at the rate
`λ_2(𝖠, μ)`. -/
theorem hasEucPastRate_of_mem {x : ℤ → ι} (hx : x ∈ O.carrier) {v : Fin 2 → ℝ}
    (hv : v ∈ O.V x 1) (hv0 : v ≠ 0) : HasEucPastRate A x v (lyapunov₂ A μ) :=
  O.rate_one x hx v hv (by rw [O.V_two_eq_bot hx, Submodule.mem_bot]; exact hv0)

/-- `eq:V_lyapunov` for `i = 0`: `V_𝐢^0` is `{0}` together with the non-zero vectors whose
backward rate exists and is at most `λ_1(𝖠, μ)`. -/
theorem mem_V_zero_iff (hlt : lyapunov₂ A μ < lyapunov₁ A μ) {x : ℤ → ι} (hx : x ∈ O.carrier)
    (v : Fin 2 → ℝ) :
    v ∈ O.V x 0 ↔ v = 0 ∨ (v ≠ 0 ∧ ∃ l, HasEucPastRate A x v l ∧ l ≤ lyapunov₁ A μ) := by
  rw [O.V_zero_eq_top hx]
  refine ⟨fun _ => ?_, fun _ => trivial⟩
  by_cases hv0 : v = 0
  · exact Or.inl hv0
  refine Or.inr ⟨hv0, ?_⟩
  by_cases hv : v ∈ O.V x 1
  · exact ⟨_, O.hasEucPastRate_of_mem hx hv hv0, hlt.le⟩
  · exact ⟨_, O.hasEucPastRate_of_notMem hx hv, le_rfl⟩

/-- `eq:V_lyapunov` for `i = 1`: `V_𝐢^1` is `{0}` together with the non-zero vectors whose
backward rate exists and is at most `λ_2(𝖠, μ)`. -/
theorem mem_V_one_iff (hlt : lyapunov₂ A μ < lyapunov₁ A μ) {x : ℤ → ι} (hx : x ∈ O.carrier)
    (v : Fin 2 → ℝ) :
    v ∈ O.V x 1 ↔ v = 0 ∨ (v ≠ 0 ∧ ∃ l, HasEucPastRate A x v l ∧ l ≤ lyapunov₂ A μ) := by
  constructor
  · intro hv
    by_cases hv0 : v = 0
    · exact Or.inl hv0
    · exact Or.inr ⟨hv0, _, O.hasEucPastRate_of_mem hx hv hv0, le_rfl⟩
  · rintro (rfl | ⟨-, l, hl, hle⟩)
    · exact (O.V x 1).zero_mem
    · by_contra hv
      have := hl.unique (O.hasEucPastRate_of_notMem hx hv)
      linarith

/-- `V_𝐢^1` depends only on the past `𝐢^-` (tex lines 1523 to 1529), by `eq:V_lyapunov`. -/
theorem V_one_eq_of_samePast (hlt : lyapunov₂ A μ < lyapunov₁ A μ) {x y : ℤ → ι}
    (hx : x ∈ O.carrier) (hy : y ∈ O.carrier) (h : SamePast x y) : O.V x 1 = O.V y 1 := by
  ext v
  simp only [O.mem_V_one_iff hlt hx, O.mem_V_one_iff hlt hy, hasEucPastRate_congr h]

/-- Two choices of `Σ'` and of the filtration give the same subspace `V_𝐢^1` at the points of
both sets, by `eq:V_lyapunov`. -/
theorem V_one_eq (O' : OseledetsSet A μ) (hlt : lyapunov₂ A μ < lyapunov₁ A μ) {x : ℤ → ι}
    (hx : x ∈ O.carrier) (hx' : x ∈ O'.carrier) : O.V x 1 = O'.V x 1 := by
  ext v
  rw [O.mem_V_one_iff hlt hx, O'.mem_V_one_iff hlt hx']

/-- `Σ^τ` of `eq:sigma_tau_omega`: the points of `Σ'` at which `V_𝐢^1` is the `y`-axis. -/
def sigmaTau : Set (ℤ → ι) := {x | x ∈ O.carrier ∧ O.V x 1 = axis 1}

/-- `Σ^ω` of `eq:sigma_tau_omega`: the points of `Σ'` at which `V_𝐢^1` is the `x`-axis. -/
def sigmaOmega : Set (ℤ → ι) := {x | x ∈ O.carrier ∧ O.V x 1 = axis 0}

/-- `eq:tau_omega_partition2`, the disjointness half: `Σ^τ ∩ Σ^ω = ∅`, since the axes differ. -/
theorem disjoint_sigmaTau_sigmaOmega : Disjoint O.sigmaTau O.sigmaOmega := by
  rw [Set.disjoint_left]
  rintro x ⟨-, h1⟩ ⟨-, h0⟩
  exact axis_zero_ne_axis_one (h0.symm.trans h1)

end OseledetsSet

end MatrixTuple

/-! ### Box-like tuples: the backward rate of every vector -/

namespace System

section Rates

variable {ι : Type*} (S : System ι)

/-- For a diagonal or anti-diagonal matrix the images of `(1, 0)` and `(0, 1)` are orthogonal:
`|A v|² = v_1² |A (1,0)|² + v_2² |A (0,1)|²`. -/
theorem eucNorm_boxMat_mulVec_sq (c : ZMod 2) (a b : ℝ) (v : Fin 2 → ℝ) :
    eucNorm (boxMat c a b *ᵥ v) ^ 2 =
      v 0 ^ 2 * eucNorm (boxMat c a b *ᵥ ![1, 0]) ^ 2 +
        v 1 ^ 2 * eucNorm (boxMat c a b *ᵥ ![0, 1]) ^ 2 := by
  rcases zmod_two_cases c with rfl | rfl <;>
    simp [eucNorm_sq, dotProduct, Fin.sum_univ_two] <;> ring

/-- `|A_𝐢 v|² = v_1² |A_𝐢 (1,0)|² + v_2² |A_𝐢 (0,1)|²` for every finite word `𝐢`. -/
theorem eucNorm_matWord_mulVec_sq (w : List ι) (v : Fin 2 → ℝ) :
    eucNorm (S.matWord w *ᵥ v) ^ 2 =
      v 0 ^ 2 * eucNorm (S.matWord w *ᵥ ![1, 0]) ^ 2 +
        v 1 ^ 2 * eucNorm (S.matWord w *ᵥ ![0, 1]) ^ 2 := by
  rw [matWord_eq]
  exact eucNorm_boxMat_mulVec_sq _ _ _ v

/-- `thm:matrix_products_g_derivatives`, first identity, with the Euclidean norm:
`|A_{i_{-n}} ⋯ A_{i_{-1}} (1,0)| = |g'_{τ_{-n}(𝐢) ⋯ τ_{-1}(𝐢)}(0)|`. -/
theorem eucNorm_matWord_pastWord_e1 (x : ℤ → ι) (n : ℕ) :
    eucNorm (S.matWord (pastWord x n) *ᵥ ![1, 0]) = |S.gDeriv (pastWord (tau S.o x) n)| := by
  rw [← abs_matWord_pastWord_e1, eucNorm_of_coord_eq_zero]
  rw [matWord_mulVec_e1]
  split_ifs <;> simp

/-- `thm:matrix_products_g_derivatives`, second identity, with the Euclidean norm:
`|A_{i_{-n}} ⋯ A_{i_{-1}} (0,1)| = |g'_{ω_{-n}(𝐢) ⋯ ω_{-1}(𝐢)}(0)|`. -/
theorem eucNorm_matWord_pastWord_e2 (x : ℤ → ι) (n : ℕ) :
    eucNorm (S.matWord (pastWord x n) *ᵥ ![0, 1]) = |S.gDeriv (pastWord (omega S.o x) n)| := by
  rw [← abs_matWord_pastWord_e2, eucNorm_of_coord_eq_zero]
  rw [matWord_mulVec_e2]
  split_ifs <;> simp

/-- The backward rate of `(1, 0)` is the backward rate of `|g'|` along `τ(𝐢)`
(`thm:matrix_products_g_derivatives`). -/
theorem hasEucPastRate_e1_iff (x : ℤ → ι) (l : ℝ) :
    MatrixTuple.HasEucPastRate S.mat x ![1, 0] l ↔ S.HasBackRate (tau S.o x) l := by
  simp only [MatrixTuple.HasEucPastRate, HasBackRate, ← matWord_eq_word,
    eucNorm_matWord_pastWord_e1]

/-- The backward rate of `(0, 1)` is the backward rate of `|g'|` along `ω(𝐢)`
(`thm:matrix_products_g_derivatives`). -/
theorem hasEucPastRate_e2_iff (x : ℤ → ι) (l : ℝ) :
    MatrixTuple.HasEucPastRate S.mat x ![0, 1] l ↔ S.HasBackRate (omega S.o x) l := by
  simp only [MatrixTuple.HasEucPastRate, HasBackRate, ← matWord_eq_word,
    eucNorm_matWord_pastWord_e2]

/-- `|A_{i_{-n}} ⋯ A_{i_{-1}} v|` in terms of the moduli `|g'|` along `τ(𝐢)` and `ω(𝐢)`. -/
theorem eucNorm_matWord_pastWord (x : ℤ → ι) (n : ℕ) (v : Fin 2 → ℝ) :
    eucNorm (S.matWord (pastWord x n) *ᵥ v) =
      √((|v 0| * |S.gDeriv (pastWord (tau S.o x) n)|) ^ 2 +
        (|v 1| * |S.gDeriv (pastWord (omega S.o x) n)|) ^ 2) := by
  rw [← S.eucNorm_matWord_pastWord_e1, ← S.eucNorm_matWord_pastWord_e2, mul_pow, mul_pow,
    sq_abs, sq_abs, ← eucNorm_matWord_mulVec_sq, Real.sqrt_sq (eucNorm_nonneg _)]

/-- A vector `v = (v_1, 0)` with `v_1 ≠ 0` grows backwards at the rate of `|g'|` along `τ(𝐢)`. -/
theorem hasEucPastRate_of_snd_eq_zero {x : ℤ → ι} {a : ℝ} (ha : S.HasBackRate (tau S.o x) a)
    {v : Fin 2 → ℝ} (h0 : v 0 ≠ 0) (h1 : v 1 = 0) : MatrixTuple.HasEucPastRate S.mat x v a := by
  unfold MatrixTuple.HasEucPastRate
  simp only [← matWord_eq_word, eucNorm_matWord_pastWord, h1, abs_zero, zero_mul,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  refine (tendsto_log_const_mul_div (fun n => abs_pos.2 (S.gDeriv_ne_zero _))
    (abs_pos.2 h0) ha).congr fun n => ?_
  rw [Real.sqrt_sq (mul_nonneg (abs_nonneg _) (abs_nonneg _))]

/-- A vector `v = (0, v_2)` with `v_2 ≠ 0` grows backwards at the rate of `|g'|` along `ω(𝐢)`. -/
theorem hasEucPastRate_of_fst_eq_zero {x : ℤ → ι} {b : ℝ} (hb : S.HasBackRate (omega S.o x) b)
    {v : Fin 2 → ℝ} (h0 : v 0 = 0) (h1 : v 1 ≠ 0) : MatrixTuple.HasEucPastRate S.mat x v b := by
  unfold MatrixTuple.HasEucPastRate
  simp only [← matWord_eq_word, eucNorm_matWord_pastWord, h0, abs_zero, zero_mul,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
  refine (tendsto_log_const_mul_div (fun n => abs_pos.2 (S.gDeriv_ne_zero _))
    (abs_pos.2 h1) hb).congr fun n => ?_
  rw [Real.sqrt_sq (mul_nonneg (abs_nonneg _) (abs_nonneg _))]

/-- A vector with two non-zero coordinates grows backwards at the larger of the rates of `|g'|`
along `τ(𝐢)` and `ω(𝐢)`. -/
theorem hasEucPastRate_of_ne_zero {x : ℤ → ι} {a b : ℝ} (ha : S.HasBackRate (tau S.o x) a)
    (hb : S.HasBackRate (omega S.o x) b) {v : Fin 2 → ℝ} (h0 : v 0 ≠ 0) (h1 : v 1 ≠ 0) :
    MatrixTuple.HasEucPastRate S.mat x v (max a b) := by
  unfold MatrixTuple.HasEucPastRate
  simp only [← matWord_eq_word, eucNorm_matWord_pastWord]
  exact tendsto_log_sqrt_div (fun n => abs_pos.2 (S.gDeriv_ne_zero _))
    (fun n => abs_pos.2 (S.gDeriv_ne_zero _)) (abs_pos.2 h0) (abs_pos.2 h1) ha hb

/-- The generators of a box-like system are invertible. -/
theorem isUnit_det_mat (i : ι) : IsUnit (S.mat i).det := by
  rw [isUnit_iff_ne_zero, ← abs_ne_zero, mat, abs_det_boxMat]
  exact mul_ne_zero (abs_ne_zero.2 (S.a_ne_zero i)) (abs_ne_zero.2 (S.b_ne_zero i))

end Rates

/-! ### The coordinate filtration on the box-like `Σ'` -/

section Filtration

variable {ι : Type*} [MeasurableSpace ι] (S : System ι)

/-- The coordinate filtration `ℝ² = V_𝐢^0 ⊋ V_𝐢^1 ⊋ V_𝐢^2 = {0}` on the box-like `Σ'` of
`BoxLike/SlowAxis.lean`, as subspaces of `ℝ²`: `V_𝐢^1` is the axis `slowAxis`, the `y`-axis on
`Σ^τ` and the `x`-axis elsewhere. Indices above `2` repeat `{0}`. -/
noncomputable def oseledetsSub (μ : Measure (ℤ → ι)) (x : ℤ → ι) :
    ℕ → Submodule ℝ (Fin 2 → ℝ)
  | 0 => ⊤
  | 1 => axis (S.slowAxis μ x)
  | _ => ⊥

/-- The subspaces `oseledetsSub` are the sets `oseledets` of `BoxLike/SlowAxis.lean`, used by the
partitions of `BoxLike/DimPartitions.lean`, under `(a, b) ↦ ![a, b]`. -/
theorem mem_oseledetsSub_iff (μ : Measure (ℤ → ι)) (x : ℤ → ι) (i : ℕ) (z : ℝ × ℝ) :
    ![z.1, z.2] ∈ S.oseledetsSub μ x i ↔ z ∈ S.oseledets μ x i := by
  rcases i with _ | _ | i
  · simp [oseledetsSub, oseledets]
  · rcases zmod_two_cases (S.slowAxis μ x) with h | h
    · simp [oseledetsSub, oseledets, h, mem_axis_zero_iff]
    · simp [oseledetsSub, oseledets, h, mem_axis_one_iff,
        show (1 : ZMod 2) + 1 = 0 by decide]
  · simp only [oseledetsSub, oseledets, Submodule.mem_bot, mem_singleton_iff]
    constructor
    · intro h
      exact Prod.ext (by simpa using congrFun h 0) (by simpa using congrFun h 1)
    · rintro rfl
      funext j
      fin_cases j <;> rfl

/-- `V_𝐢^1` is the `y`-axis on `Σ^τ`. -/
theorem oseledetsSub_one_of_mem_SigmaTau (μ : Measure (ℤ → ι)) {x : ℤ → ι}
    (hx : x ∈ S.SigmaTau μ) : S.oseledetsSub μ x 1 = axis 1 := by
  simp [oseledetsSub, S.slowAxis_of_mem_SigmaTau μ hx]

/-- `V_𝐢^1` is the `x`-axis on `Σ^ω` when `λ_2(𝖠, μ) < λ_1(𝖠, μ)`. -/
theorem oseledetsSub_one_of_mem_SigmaOmega (μ : Measure (ℤ → ι))
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) {x : ℤ → ι} (hx : x ∈ S.SigmaOmega μ) :
    S.oseledetsSub μ x 1 = axis 0 := by
  simp [oseledetsSub, S.slowAxis_of_mem_SigmaOmega μ hlt hx]

/-- (V3) for `i = 1` on the box-like `Σ'`: every non-zero vector of the axis `V_𝐢^1` grows
backwards at the rate `λ_2(𝖠, μ)`. -/
theorem hasEucPastRate_of_mem_oseledetsSub_one (μ : Measure (ℤ → ι))
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) {x : ℤ → ι} (hx : x ∈ S.SigmaPrime μ)
    {v : Fin 2 → ℝ} (hv : v ∈ S.oseledetsSub μ x 1) (hv0 : v ≠ 0) :
    MatrixTuple.HasEucPastRate S.mat x v (S.lyapunov₂ μ) := by
  rcases hx with hx | hx
  · rw [S.oseledetsSub_one_of_mem_SigmaTau μ hx, mem_axis_one_iff] at hv
    exact S.hasEucPastRate_of_fst_eq_zero hx.2 hv (snd_ne_zero_of_fst_eq_zero hv0 hv)
  · rw [S.oseledetsSub_one_of_mem_SigmaOmega μ hlt hx, mem_axis_zero_iff] at hv
    exact S.hasEucPastRate_of_snd_eq_zero hx.1 (fst_ne_zero_of_snd_eq_zero hv0 hv) hv

/-- (V3) for `i = 0` on the box-like `Σ'`: every vector off the axis `V_𝐢^1` grows backwards at
the rate `λ_1(𝖠, μ)`. -/
theorem hasEucPastRate_of_notMem_oseledetsSub_one (μ : Measure (ℤ → ι))
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) {x : ℤ → ι} (hx : x ∈ S.SigmaPrime μ)
    {v : Fin 2 → ℝ} (hv : v ∉ S.oseledetsSub μ x 1) :
    MatrixTuple.HasEucPastRate S.mat x v (S.lyapunov₁ μ) := by
  rcases hx with hx | hx
  · rw [S.oseledetsSub_one_of_mem_SigmaTau μ hx, mem_axis_one_iff] at hv
    by_cases h1 : v 1 = 0
    · exact S.hasEucPastRate_of_snd_eq_zero hx.1 hv h1
    · have h := S.hasEucPastRate_of_ne_zero hx.1 hx.2 hv h1
      rwa [max_eq_left hlt.le] at h
  · rw [S.oseledetsSub_one_of_mem_SigmaOmega μ hlt hx, mem_axis_zero_iff] at hv
    by_cases h0 : v 0 = 0
    · exact S.hasEucPastRate_of_fst_eq_zero hx.2 h0 hv
    · have h := S.hasEucPastRate_of_ne_zero hx.1 hx.2 h0 hv
      rwa [max_eq_right hlt.le] at h

/-- `eq:V_lyapunov` for `i = 1` on the box-like `Σ'`: the axis `V_𝐢^1` is `{0}` together with
the vectors that grow backwards at the rate `λ_2(𝖠, μ)`. -/
theorem mem_oseledetsSub_one_iff (μ : Measure (ℤ → ι))
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) {x : ℤ → ι} (hx : x ∈ S.SigmaPrime μ)
    (v : Fin 2 → ℝ) :
    v ∈ S.oseledetsSub μ x 1 ↔ v = 0 ∨ MatrixTuple.HasEucPastRate S.mat x v (S.lyapunov₂ μ) := by
  constructor
  · intro hv
    by_cases hv0 : v = 0
    · exact Or.inl hv0
    · exact Or.inr (S.hasEucPastRate_of_mem_oseledetsSub_one μ hlt hx hv hv0)
  · rintro (rfl | h)
    · exact Submodule.zero_mem _
    · by_contra hv
      exact hlt.ne (h.unique (S.hasEucPastRate_of_notMem_oseledetsSub_one μ hlt hx hv))

/-- (V1) on the box-like `Σ'`: `A_{i_{-1}} V_𝐢^i = V_{σ^{-1}(𝐢)}^i`. For `i = 1` this follows from
`eq:V_lyapunov` at `𝐢` and at `σ^{-1}(𝐢)`, since the backward rate of `A_{i_{-1}} v` along
`σ^{-1}(𝐢)` is the backward rate of `v` along `𝐢`. -/
theorem map_oseledetsSub (μ : Measure (ℤ → ι)) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ)
    {x : ℤ → ι} (hx : x ∈ S.SigmaPrime μ) (i : ℕ) :
    (S.oseledetsSub μ x i).map (S.mat (x (-1))).mulVecLin = S.oseledetsSub μ (shift (-1) x) i := by
  have hx' : shift (-1) x ∈ S.SigmaPrime μ := by
    rw [← S.shift_mem_SigmaPrime_iff, shift_shift, neg_add_cancel, shift_zero]
    exact hx
  have hinv : S.mat (x (-1)) * (S.mat (x (-1)))⁻¹ = 1 := mul_nonsing_inv _ (S.isUnit_det_mat _)
  rcases i with _ | _ | i
  · simp only [oseledetsSub, Submodule.map_top]
    rw [LinearMap.range_eq_top]
    intro w
    exact ⟨(S.mat (x (-1)))⁻¹ *ᵥ w, by simp [mulVec_mulVec, hinv]⟩
  · ext w
    simp only [Submodule.mem_map, mulVecLin_apply]
    rw [S.mem_oseledetsSub_one_iff μ hlt hx']
    constructor
    · rintro ⟨u, hu, rfl⟩
      rcases (S.mem_oseledetsSub_one_iff μ hlt hx u).1 hu with rfl | h
      · exact Or.inl (mulVec_zero _)
      · exact Or.inr ((MatrixTuple.hasEucPastRate_shift_neg_one_iff x u _).2 h)
    · intro h
      refine ⟨(S.mat (x (-1)))⁻¹ *ᵥ w, ?_, by simp [mulVec_mulVec, hinv]⟩
      rw [S.mem_oseledetsSub_one_iff μ hlt hx]
      rcases h with rfl | h
      · exact Or.inl (mulVec_zero _)
      · refine Or.inr ((MatrixTuple.hasEucPastRate_shift_neg_one_iff x _ _).1 ?_)
        simpa [mulVec_mulVec, hinv] using h
  · simp [oseledetsSub]

/-- (V2) on the box-like `Σ'`: `dim V_𝐢^i = 2 - i` for `i ≤ 2`. -/
theorem finrank_oseledetsSub (μ : Measure (ℤ → ι)) (x : ℤ → ι) {i : ℕ} (hi : i ≤ 2) :
    finrank ℝ (S.oseledetsSub μ x i) = 2 - i :=
  match i, hi with
  | 0, _ => show finrank ℝ (⊤ : Submodule ℝ (Fin 2 → ℝ)) = 2 - 0 by simp
  | 1, _ => show finrank ℝ (axis (S.slowAxis μ x)) = 2 - 1 by rw [finrank_axis]
  | 2, _ => show finrank ℝ (⊥ : Submodule ℝ (Fin 2 → ℝ)) = 2 - 2 by simp
  | _ + 3, h => by omega

/-- `σ(Σ') = Σ'` for the box-like `Σ'` (tex line 1521). -/
theorem image_shift_SigmaPrime (μ : Measure (ℤ → ι)) :
    shift 1 '' S.SigmaPrime μ = S.SigmaPrime μ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (S.shift_mem_SigmaPrime_iff μ x).2 hx
  · intro hy
    refine ⟨shift (-1) y, ?_, by rw [shift_shift, neg_add_cancel, shift_zero]⟩
    rw [← S.shift_mem_SigmaPrime_iff, shift_shift, neg_add_cancel, shift_zero]
    exact hy

end Filtration

section Construction

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι)

/-- The coordinate filtration is measurable: its graphs `{(𝐢, v) : v ∈ V_𝐢^i}` are Borel, since
`Σ^τ` is Borel. -/
theorem measurableSet_oseledetsSub (μ : Measure (ℤ → ι)) (i : ℕ) :
    MeasurableSet {p : (ℤ → ι) × (Fin 2 → ℝ) | p.2 ∈ S.oseledetsSub μ p.1 i} := by
  classical
  let P : Fin 2 → Set ((ℤ → ι) × (Fin 2 → ℝ)) := fun j => {p | p.2 j = 0}
  have hc : ∀ j : Fin 2, MeasurableSet (P j) := fun j =>
    measurableSet_eq_fun ((measurable_pi_apply j).comp measurable_snd) measurable_const
  rcases i with _ | _ | i
  · simp [oseledetsSub]
  · have h : {p : (ℤ → ι) × (Fin 2 → ℝ) | p.2 ∈ S.oseledetsSub μ p.1 1} =
        (Prod.fst ⁻¹' S.SigmaTau μ ∩ P 0) ∪ ((Prod.fst ⁻¹' S.SigmaTau μ)ᶜ ∩ P 1) := by
      ext p
      by_cases hp : p.1 ∈ S.SigmaTau μ <;>
        simp [P, oseledetsSub, slowAxis, hp, mem_axis_zero_iff, mem_axis_one_iff]
    rw [h]
    have hτ : MeasurableSet (Prod.fst ⁻¹' S.SigmaTau μ : Set ((ℤ → ι) × (Fin 2 → ℝ))) :=
      measurable_fst (S.measurableSet_SigmaTau μ)
    exact (hτ.inter (hc 0)).union (hτ.compl.inter (hc 1))
  · have h : {p : (ℤ → ι) × (Fin 2 → ℝ) | p.2 ∈ S.oseledetsSub μ p.1 (i + 2)} =
        P 0 ∩ P 1 := by
      ext p
      simp only [P, oseledetsSub, Submodule.mem_bot, mem_ofPred_eq, mem_inter_iff]
      constructor
      · rintro h
        simp [h]
      · rintro ⟨h0, h1⟩
        funext j
        fin_cases j
        · exact h0
        · exact h1
    rw [h]
    exact (hc 0).inter (hc 1)

/-- Oseledets' theorem for a box-like tuple, `sec:lyapunov_exponents`, proved: for an ergodic
invariant probability measure with `λ_2(𝖠, μ) < λ_1(𝖠, μ)` the box-like set `Σ'` of
`BoxLike/SlowAxis.lean` with the coordinate filtration `oseledetsSub` has every property the
article takes from Oseledets' theorem. No literature hypothesis is used: `μ(Σ') = 1` is
`measure_SigmaPrime_compl`, proved with Birkhoff's theorem, and (V3) is the all-vector
characterisation `hasEucPastRate_of_mem_oseledetsSub_one`,
`hasEucPastRate_of_notMem_oseledetsSub_one`.
Depends on: `thm:matrix_products_g_derivatives`, `measure_SigmaPrime_compl`,
`shift_mem_SigmaPrime_iff`, `mem_SigmaPrime_of_samePast`. -/
noncomputable def oseledetsSet (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) : MatrixTuple.OseledetsSet S.mat μ where
  carrier := S.SigmaPrime μ
  V := S.oseledetsSub μ
  measurableSet_carrier := S.measurableSet_SigmaPrime μ
  image_shift := S.image_shift_SigmaPrime μ
  measure_compl := S.measure_SigmaPrime_compl μ hinv herg
  mem_of_samePast _ hx _ h := S.mem_SigmaPrime_of_samePast μ h.symm hx
  measurableSet_V i _ := S.measurableSet_oseledetsSub μ i
  map_V x hx i _ := S.map_oseledetsSub μ hlt hx i
  finrank_V x _ i hi := S.finrank_oseledetsSub μ x hi
  rate_zero x hx v _ hv := S.hasEucPastRate_of_notMem_oseledetsSub_one μ hlt hx hv
  rate_one x hx v hv hv2 := S.hasEucPastRate_of_mem_oseledetsSub_one μ hlt hx hv (by
    simpa [oseledetsSub] using hv2)

/-- The carrier of `oseledetsSet` is the box-like `Σ'`. -/
@[simp] theorem oseledetsSet_carrier (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) :
    (S.oseledetsSet μ hinv herg hlt).carrier = S.SigmaPrime μ := rfl

/-- The filtration of `oseledetsSet` is the coordinate filtration. -/
@[simp] theorem oseledetsSet_V (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) :
    (S.oseledetsSet μ hinv herg hlt).V = S.oseledetsSub μ := rfl

end Construction

/-! ### Every choice of `Σ'` is the coordinate one -/

section Identification

variable {ι : Type*} [MeasurableSpace ι] {S : System ι} {μ : Measure (ℤ → ι)}

/-- Tex lines 1614 to 1616, proved: for a box-like tuple and every choice of `Σ'` and of the
filtration, `V_𝐢^1` is one of the coordinate axes at every `𝐢 ∈ Σ'`, "by (V3)". If neither
`(1, 0)` nor `(0, 1)` lay on the line `V_𝐢^1`, both would grow at the rate `λ_1(𝖠, μ)`, and so
would every vector, including the non-zero vectors of `V_𝐢^1`. -/
theorem V_one_eq_axis (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) {x : ℤ → ι} (hx : x ∈ O.carrier) :
    O.V x 1 = axis 0 ∨ O.V x 1 = axis 1 := by
  have hle : ∀ c, axisVec c ∈ O.V x 1 → O.V x 1 = axis c := fun c hc => by
    have h : axis c ≤ O.V x 1 := (Submodule.span_singleton_le_iff_mem _ _).2 hc
    exact (Submodule.eq_of_le_of_finrank_eq h
      (by rw [finrank_axis, O.finrank_V x hx 1 (by norm_num)])).symm
  by_cases h1 : (![1, 0] : Fin 2 → ℝ) ∈ O.V x 1
  · exact Or.inl (hle 0 (by simpa [axisVec] using h1))
  by_cases h2 : (![0, 1] : Fin 2 → ℝ) ∈ O.V x 1
  · exact Or.inr (hle 1 (by simpa [axisVec] using h2))
  exfalso
  have ha := (S.hasEucPastRate_e1_iff x _).1 (O.hasEucPastRate_of_notMem hx h1)
  have hb := (S.hasEucPastRate_e2_iff x _).1 (O.hasEucPastRate_of_notMem hx h2)
  obtain ⟨v, hv, hv0⟩ := O.exists_mem_V_one_ne_zero hx
  have hr := O.hasEucPastRate_of_mem hx hv hv0
  have hr' : MatrixTuple.HasEucPastRate S.mat x v (MatrixTuple.lyapunov₁ S.mat μ) := by
    by_cases h0 : v 0 = 0
    · exact S.hasEucPastRate_of_fst_eq_zero hb h0 (snd_ne_zero_of_fst_eq_zero hv0 h0)
    by_cases h1' : v 1 = 0
    · exact S.hasEucPastRate_of_snd_eq_zero ha h0 h1'
    · simpa using S.hasEucPastRate_of_ne_zero ha hb h0 h1'
  exact hlt.ne (hr.unique hr')

/-- At a point of `Σ'` where `V_𝐢^1` is the `y`-axis the two backward coordinate rates are
`λ_1(𝖠, μ)` along `τ(𝐢)` and `λ_2(𝖠, μ)` along `ω(𝐢)`, by (V3). -/
theorem mem_SigmaTau_of_V_one (O : MatrixTuple.OseledetsSet S.mat μ) {x : ℤ → ι}
    (hx : x ∈ O.carrier) (h : O.V x 1 = axis 1) : x ∈ S.SigmaTau μ := by
  refine ⟨(S.hasEucPastRate_e1_iff x _).1 (O.hasEucPastRate_of_notMem hx ?_),
    (S.hasEucPastRate_e2_iff x _).1 (O.hasEucPastRate_of_mem hx ?_ ?_)⟩
  · rw [h]; exact e1_mem_axis.2
  · rw [h]; exact e2_mem_axis.1
  · intro h0; simpa using congrFun h0 1

/-- At a point of `Σ'` where `V_𝐢^1` is the `x`-axis the two backward coordinate rates are
`λ_2(𝖠, μ)` along `τ(𝐢)` and `λ_1(𝖠, μ)` along `ω(𝐢)`, by (V3). -/
theorem mem_SigmaOmega_of_V_one (O : MatrixTuple.OseledetsSet S.mat μ) {x : ℤ → ι}
    (hx : x ∈ O.carrier) (h : O.V x 1 = axis 0) : x ∈ S.SigmaOmega μ := by
  refine ⟨(S.hasEucPastRate_e1_iff x _).1 (O.hasEucPastRate_of_mem hx ?_ ?_),
    (S.hasEucPastRate_e2_iff x _).1 (O.hasEucPastRate_of_notMem hx ?_)⟩
  · rw [h]; exact e1_mem_axis.1
  · intro h0; simpa using congrFun h0 0
  · rw [h]; exact e2_mem_axis.2

/-- Every choice of `Σ'` lies inside the box-like `Σ'` of `BoxLike/SlowAxis.lean`. -/
theorem carrier_subset_SigmaPrime (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) : O.carrier ⊆ S.SigmaPrime μ := fun _ hx =>
  (V_one_eq_axis O hlt hx).elim (fun h => Or.inr (mem_SigmaOmega_of_V_one O hx h))
    (fun h => Or.inl (mem_SigmaTau_of_V_one O hx h))

/-- Every choice of the filtration is the coordinate filtration `oseledetsSub` on its set `Σ'`,
for `i ∈ {0, 1, 2}`. -/
theorem V_eq_oseledetsSub (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) {x : ℤ → ι} (hx : x ∈ O.carrier) {i : ℕ}
    (hi : i ≤ 2) : O.V x i = S.oseledetsSub μ x i := by
  rcases i with _ | _ | _ | i
  · exact O.V_zero_eq_top hx
  · rcases V_one_eq_axis O hlt hx with h | h
    · rw [h, S.oseledetsSub_one_of_mem_SigmaOmega μ hlt (mem_SigmaOmega_of_V_one O hx h)]
    · rw [h, S.oseledetsSub_one_of_mem_SigmaTau μ (mem_SigmaTau_of_V_one O hx h)]
  · exact O.V_two_eq_bot hx
  · omega

/-- The article's `Σ^τ` of `eq:sigma_tau_omega` is `Σ' ∩ S.SigmaTau μ`. -/
theorem sigmaTau_eq_inter (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) : O.sigmaTau = O.carrier ∩ S.SigmaTau μ := by
  ext x
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, mem_SigmaTau_of_V_one O hx h⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, by rw [V_eq_oseledetsSub O hlt hx (by norm_num),
      S.oseledetsSub_one_of_mem_SigmaTau μ h]⟩

/-- The article's `Σ^ω` of `eq:sigma_tau_omega` is `Σ' ∩ S.SigmaOmega μ`. -/
theorem sigmaOmega_eq_inter (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) : O.sigmaOmega = O.carrier ∩ S.SigmaOmega μ := by
  ext x
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, mem_SigmaOmega_of_V_one O hx h⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, by rw [V_eq_oseledetsSub O hlt hx (by norm_num),
      S.oseledetsSub_one_of_mem_SigmaOmega μ hlt h]⟩

/-- `eq:tau_omega_partition2`, the covering half: `Σ' = Σ^τ ∪ Σ^ω`. -/
theorem sigmaTau_union_sigmaOmega (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) : O.sigmaTau ∪ O.sigmaOmega = O.carrier := by
  ext x
  constructor
  · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
  · intro hx
    rcases V_one_eq_axis O hlt hx with h | h
    · exact Or.inr ⟨hx, h⟩
    · exact Or.inl ⟨hx, h⟩

/-- The existence of a choice of `Σ'` gives `μ(Σ') = 1` for the box-like `Σ'`. -/
theorem measure_SigmaPrime_compl_of_oseledetsSet (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) : μ (S.SigmaPrime μ)ᶜ = 0 :=
  measure_mono_null (compl_subset_compl.2 (carrier_subset_SigmaPrime O hlt)) O.measure_compl

/-- The article's `Σ'` and the box-like `Σ'` agree modulo `μ`-null sets. -/
theorem carrier_ae_eq (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) : O.carrier =ᵐ[μ] S.SigmaPrime μ :=
  (ae_eq_univ.2 O.measure_compl).trans
    (ae_eq_univ.2 (measure_SigmaPrime_compl_of_oseledetsSet O hlt)).symm

/-- The article's `Σ^τ` and `S.SigmaTau μ` agree modulo `μ`-null sets. -/
theorem sigmaTau_ae_eq (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) : O.sigmaTau =ᵐ[μ] S.SigmaTau μ := by
  rw [sigmaTau_eq_inter O hlt]
  exact inter_ae_eq_right_of_ae_eq_univ (ae_eq_univ.2 O.measure_compl)

/-- The article's `Σ^ω` and `S.SigmaOmega μ` agree modulo `μ`-null sets. -/
theorem sigmaOmega_ae_eq (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) : O.sigmaOmega =ᵐ[μ] S.SigmaOmega μ := by
  rw [sigmaOmega_eq_inter O hlt]
  exact inter_ae_eq_right_of_ae_eq_univ (ae_eq_univ.2 O.measure_compl)

/-- The membership `V_𝐢^i` of the article's filtration is the membership of the sets `oseledets`
of `BoxLike/SlowAxis.lean`, used by the partitions of `BoxLike/DimPartitions.lean`, at every
point of `Σ'` and for `i ∈ {0, 1, 2}`. -/
theorem mem_V_iff_mem_oseledets (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) {x : ℤ → ι} (hx : x ∈ O.carrier) {i : ℕ}
    (hi : i ≤ 2) (z : ℝ × ℝ) : ![z.1, z.2] ∈ O.V x i ↔ z ∈ S.oseledets μ x i := by
  rw [V_eq_oseledetsSub O hlt hx hi, mem_oseledetsSub_iff]

/-- `V_𝐢^1` is the slow axis `slowAxis` of `BoxLike/SlowAxis.lean` at every point of `Σ'`. -/
theorem V_one_eq_axis_slowAxis (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) {x : ℤ → ι} (hx : x ∈ O.carrier) :
    O.V x 1 = axis (S.slowAxis μ x) :=
  V_eq_oseledetsSub O hlt hx (by norm_num)

/-- The article's `Σ^τ` has the measure of `S.SigmaTau μ`. -/
theorem measure_sigmaTau (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) : μ O.sigmaTau = μ (S.SigmaTau μ) :=
  measure_congr (sigmaTau_ae_eq O hlt)

/-- The article's `Σ^ω` has the measure of `S.SigmaOmega μ`. -/
theorem measure_sigmaOmega (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) : μ O.sigmaOmega = μ (S.SigmaOmega μ) :=
  measure_congr (sigmaOmega_ae_eq O hlt)

/-- The behaviour of the article's `Σ^τ` and `Σ^ω` under the shift
(`eq:sigma_tau_omega_positive_eq_measure1`): appending `A_{i_0}` keeps `V^1` when `A_{i_0}` is
diagonal and exchanges the axes when it is anti-diagonal. -/
theorem shift_mem_sigmaTau_iff (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) (x : ℤ → ι) :
    (shift 1 x ∈ O.sigmaTau ↔
      (S.o (x 0) = 0 ∧ x ∈ O.sigmaTau) ∨ (S.o (x 0) = 1 ∧ x ∈ O.sigmaOmega)) ∧
    (shift 1 x ∈ O.sigmaOmega ↔
      (S.o (x 0) = 0 ∧ x ∈ O.sigmaOmega) ∨ (S.o (x 0) = 1 ∧ x ∈ O.sigmaTau)) := by
  obtain ⟨h1, h2⟩ := S.shift_mem_SigmaTau_iff μ x
  simp only [sigmaTau_eq_inter O hlt, sigmaOmega_eq_inter O hlt, mem_inter_iff, O.shift_mem_iff,
    h1, h2]
  constructor <;> tauto

/-- `thm:lyapunov_exponents_via_g_system`, in the form of the article, proved for every choice
of `Σ'` and of the Oseledets filtration: every `𝐢 ∈ Σ'` lies in `Σ^τ` or in `Σ^ω`, and
`λ_1(𝖠, μ)`, `λ_2(𝖠, μ)` are the backward rates of `|g'|` along `τ(𝐢)`, `ω(𝐢)` on `Σ^τ` and
along `ω(𝐢)`, `τ(𝐢)` on `Σ^ω`. The proof is the prose proof: by
`thm:matrix_products_g_derivatives` (`hasEucPastRate_e1_iff`, `hasEucPastRate_e2_iff`)
`|A_{i_{-n}} ⋯ A_{i_{-1}} (1,0)| = |g'_{τ_{-n}(𝐢) ⋯ τ_{-1}(𝐢)}(0)|` and the same with `(0,1)` and
`ω`; by (V3) the backward rate is `λ_1(𝖠, μ)` off `V_𝐢^1` and `λ_2(𝖠, μ)` on `V_𝐢^1 ∖ {0}`; on
`Σ^τ` the line `V_𝐢^1` is `span{(0,1)}` and on `Σ^ω` it is `span{(1,0)}`. The case distinction
`Σ' = Σ^τ ∪ Σ^ω` is `sigmaTau_union_sigmaOmega`, which uses `λ_2(𝖠, μ) < λ_1(𝖠, μ)`; the
hypotheses proximal, with rotations, invariant and ergodic are those of the article and are not
used by the argument. -/
theorem lyapunov_exponents_via_g_system_oseledets (_hrot : S.WithRotations)
    (_hprox : S.Proximal) [IsProbabilityMeasure μ] (_hinv : MeasurePreserving (shift 1) μ μ)
    (_herg : Ergodic (shift 1) μ) (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ)
    (O : MatrixTuple.OseledetsSet S.mat μ) {x : ℤ → ι} (hx : x ∈ O.carrier) :
    (x ∈ O.sigmaTau ∨ x ∈ O.sigmaOmega) ∧
    (x ∈ O.sigmaTau → S.HasBackRate (tau S.o x) (S.lyapunov₁ μ) ∧
      S.HasBackRate (omega S.o x) (S.lyapunov₂ μ)) ∧
    (x ∈ O.sigmaOmega → S.HasBackRate (omega S.o x) (S.lyapunov₁ μ) ∧
      S.HasBackRate (tau S.o x) (S.lyapunov₂ μ)) := by
  refine ⟨?_, fun ⟨hx', h⟩ => ?_, fun ⟨hx', h⟩ => ?_⟩
  · rw [← sigmaTau_union_sigmaOmega O hlt] at hx
    exact hx
  · -- On `Σ^τ`: `(1, 0) ∉ V_𝐢^1 = span{(0, 1)}` and `(0, 1) ∈ V_𝐢^1 ∖ {0}`.
    have he1 : (![1, 0] : Fin 2 → ℝ) ∉ O.V x 1 := by rw [h]; exact e1_mem_axis.2
    have he2 : (![0, 1] : Fin 2 → ℝ) ∈ O.V x 1 := by rw [h]; exact e2_mem_axis.1
    have he2' : (![0, 1] : Fin 2 → ℝ) ≠ 0 := fun h0 => by simpa using congrFun h0 1
    exact ⟨(S.hasEucPastRate_e1_iff x _).1 (O.hasEucPastRate_of_notMem hx' he1),
      (S.hasEucPastRate_e2_iff x _).1 (O.hasEucPastRate_of_mem hx' he2 he2')⟩
  · -- On `Σ^ω`: `(0, 1) ∉ V_𝐢^1 = span{(1, 0)}` and `(1, 0) ∈ V_𝐢^1 ∖ {0}`.
    have he2 : (![0, 1] : Fin 2 → ℝ) ∉ O.V x 1 := by rw [h]; exact e2_mem_axis.2
    have he1 : (![1, 0] : Fin 2 → ℝ) ∈ O.V x 1 := by rw [h]; exact e1_mem_axis.1
    have he1' : (![1, 0] : Fin 2 → ℝ) ≠ 0 := fun h0 => by simpa using congrFun h0 0
    exact ⟨(S.hasEucPastRate_e2_iff x _).1 (O.hasEucPastRate_of_notMem hx' he2),
      (S.hasEucPastRate_e1_iff x _).1 (O.hasEucPastRate_of_mem hx' he1 he1')⟩

end Identification

section Endpoint

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι)

/-- The article's `Σ^τ` is Borel. -/
theorem measurableSet_sigmaTau {μ : Measure (ℤ → ι)} (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) : MeasurableSet O.sigmaTau := by
  rw [sigmaTau_eq_inter O hlt]
  exact O.measurableSet_carrier.inter (S.measurableSet_SigmaTau μ)

/-- The article's `Σ^ω` is Borel. -/
theorem measurableSet_sigmaOmega {μ : Measure (ℤ → ι)} (O : MatrixTuple.OseledetsSet S.mat μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) : MeasurableSet O.sigmaOmega := by
  rw [sigmaOmega_eq_inter O hlt]
  exact O.measurableSet_carrier.inter (S.measurableSet_SigmaOmega μ)

/-- `thm:lyapunov_exponents_via_g_system` with the choice of `Σ'` of `sec:lyapunov_exponents`,
proved: under the hypotheses of the article a choice of `Σ'` and of the Oseledets filtration
exists (`oseledetsSet`, the box-like case of Oseledets' theorem, proved without a literature
hypothesis), and for every such choice and every `𝐢 ∈ Σ'` the point lies in `Σ^τ` or `Σ^ω` and
the four limits of the lemma hold (`lyapunov_exponents_via_g_system_oseledets`).
Depends on: `thm:matrix_products_g_derivatives`, `measure_SigmaPrime_compl`, `V_one_eq_axis`. -/
theorem lyapunov_exponents_via_g_system_manuscript (hrot : S.WithRotations)
    (hprox : S.Proximal) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) :
    Nonempty (MatrixTuple.OseledetsSet S.mat μ) ∧
    ∀ O : MatrixTuple.OseledetsSet S.mat μ, ∀ x ∈ O.carrier,
      (x ∈ O.sigmaTau ∨ x ∈ O.sigmaOmega) ∧
      (x ∈ O.sigmaTau → S.HasBackRate (tau S.o x) (S.lyapunov₁ μ) ∧
        S.HasBackRate (omega S.o x) (S.lyapunov₂ μ)) ∧
      (x ∈ O.sigmaOmega → S.HasBackRate (omega S.o x) (S.lyapunov₁ μ) ∧
        S.HasBackRate (tau S.o x) (S.lyapunov₂ μ)) :=
  ⟨⟨S.oseledetsSet μ hinv herg hlt⟩, fun O _ hx =>
    lyapunov_exponents_via_g_system_oseledets hrot hprox hinv herg hlt O hx⟩

/-- The box-like choice `oseledetsSet` of `Σ'` has the article's `Σ^τ` equal to the set
`S.SigmaTau μ` of `BoxLike/SlowAxis.lean`. -/
theorem sigmaTau_oseledetsSet (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) :
    (S.oseledetsSet μ hinv herg hlt).sigmaTau = S.SigmaTau μ := by
  rw [sigmaTau_eq_inter _ hlt, oseledetsSet_carrier, inter_eq_right]
  exact subset_union_left

/-- The box-like choice `oseledetsSet` of `Σ'` has the article's `Σ^ω` equal to the set
`S.SigmaOmega μ` of `BoxLike/SlowAxis.lean`. -/
theorem sigmaOmega_oseledetsSet (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) :
    (S.oseledetsSet μ hinv herg hlt).sigmaOmega = S.SigmaOmega μ := by
  rw [sigmaOmega_eq_inter _ hlt, oseledetsSet_carrier, inter_eq_right]
  exact subset_union_right

end Endpoint

section Positive

universe u

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι)

/-- `thm:sigma_tau_omega_positive_eq_measure` for the article's `Σ^τ` and `Σ^ω` and every choice
of `Σ'`: `μ(Σ^τ) > 0` and `μ(Σ^ω) > 0`, transferred from `System.sigma_tau_omega_positive`
through `measure_sigmaTau`, `measure_sigmaOmega`. The hypothesis `hlt` is the simple Lyapunov
spectrum `eq:simple_lyapunov` under which the article chooses `Σ'`. -/
theorem sigma_tau_omega_positive_oseledets (hfk : EquilibriumGibbsStatement.{u})
    (hrot : S.WithRotations) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ)
    (hlt : S.lyapunov₂ μ < S.lyapunov₁ μ) (O : MatrixTuple.OseledetsSet S.mat μ) :
    0 < μ O.sigmaTau ∧ 0 < μ O.sigmaOmega := by
  rw [measure_sigmaTau O hlt, measure_sigmaOmega O hlt]
  exact S.sigma_tau_omega_positive hfk hrot hs0 hs2 μ hinv herg heq

end Positive

end System

end BoxLike
