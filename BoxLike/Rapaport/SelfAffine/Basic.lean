module

/-
Basic theory of the homogeneous diagonal planar systems `HomSystem` (`Rapaport/Defs.lean`) for
the proof of Rapaport's theorem (arXiv:2309.03985): the notation of Sections 2.2, 2.3 and 6.2 of
the source for the maps `φ_i(z) = A z + v_i`, `A = diag(r₁, r₂)`, the decomposition
`μ = ∑_{u ∈ Λ^n} p_u φ_u μ` (line 1632), and the separation step of lines 1900 to 1908.

* Linear parts: `Apow_zero`, `Apow_succ`, `Apow_succ'`, `Apow_add`, `A_eq_Apow_one`,
  `Apow_add_apply`, `Apow_sub_apply`, `ApowL` with `coe_ApowL` and `ApowL_apply`,
  `continuous_Apow`, `measurable_Apow`, `measurable_A`, `abs_r₁_pow` and `abs_r₂_pow`
  (`|r_j^n| = e^{-χ_j n}`), `abs_fst_Apow`, `abs_snd_Apow`, `norm_Apow_le`.
* Words: `φWord_zero`, `φWord_succ`, `φWord_cons`, `φWord_eq` (`φ_u z = A^n z + φ_u(0)`),
  `point_zero`, `point_succ`, `point_cons`, `point_snoc`, the radius `R₀` and `norm_point_le`.
* Weights: `weight_cons`, `weight_snoc`, `weight_pos`, `weight_le_one`, `sum_weight`,
  `sum_negMulLog_weight` (`-∑_u p_u log p_u = n H(p)`), and the splittings `sum_words_succ`,
  `sum_words_snoc` of sums over words.
* The laws `ν_n`: `isProbabilityMeasure_ν`, `ν_apply`, `ν_real_apply`, `ν_zero`, `ν_one`,
  `ν_succ_eq_sum`, `ν_succ_eq_conv` (`ν_{n+1} = ν_n ∗ (A^n)_* ν_1`), `inBall_ν`, `bddSupp_ν`.
* The self-affine measure: `map_φ_eq_conv`, `eq_sum_map_φWord`, `eq_sum_map_add_point`,
  `eq_ν_conv_map_Apow` (`μ = ν_n ∗ (A^n)_* μ`), `InBall.map_Apow`, `InBall.ae_abs_sub_Apow_le`.
* Entropy: `ent_sum_dirac_of_injective`, `ent_sum_dirac_of_injOn`, `ent_ν_of_injective`, and
  `XSep.exists_ent_ν_E_eq`: under exponential separation there is `M₀` such that for every
  `M ≥ M₀`, `H(ν_n, ℰ_{Mn}) = n H(p)` for infinitely many `n`.
* Auxiliary: finite sums of Dirac masses (`sum_dirac_apply`, `sum_dirac_real_apply`,
  `ae_sum_dirac`, `map_sum_dirac`) and convolution with finite sums (`finset_sum_conv`,
  `conv_finset_sum`).
-/
public import BoxLike.Rapaport.Defs

@[expose] public section

namespace BoxLike.Rapaport.HomSystem

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal MeasureTheory

variable {ι : Type*} [Fintype ι] (S : HomSystem ι)

/-! ### Linear parts -/

/-- `A z = (r₁ z.1, r₂ z.2)`: the common linear part of the maps of line 142 of the source. -/
theorem A_apply (z : ℝ × ℝ) : S.A z = (S.r₁ * z.1, S.r₂ * z.2) := rfl

/-- `A^n z = (r₁^n z.1, r₂^n z.2)`: the linear part `diag(r_{u,1}, r_{u,2})` of `φ_u` for a word
`u` of length `n` (line 1200 of the source). -/
theorem Apow_apply (n : ℕ) (z : ℝ × ℝ) : S.Apow n z = (S.r₁ ^ n * z.1, S.r₂ ^ n * z.2) := rfl

/-- `A^0` is the identity, the linear part of `φ_∅` (line 1201 of the source). -/
theorem Apow_zero : S.Apow 0 = id := by
  funext z; simp [Apow, diagMap]

/-- `A^{n+1} = A ∘ A^n`: `r_{iu,j} = r_{i,j} r_{u,j}` (line 1200 of the source). -/
theorem Apow_succ (n : ℕ) : S.Apow (n + 1) = S.A ∘ S.Apow n := by
  funext z; simp only [Apow, A, diagMap, Function.comp_apply, pow_succ]; ext <;> ring

/-- `A^{n+1} = A^n ∘ A`: `r_{ui,j} = r_{u,j} r_{i,j}` (line 1200 of the source). -/
theorem Apow_succ' (n : ℕ) : S.Apow (n + 1) = S.Apow n ∘ S.A := by
  funext z; simp only [Apow, A, diagMap, Function.comp_apply, pow_succ]; ext <;> ring

/-- `A^{m+n} = A^m ∘ A^n`: the linear part of a concatenation `uv` (line 1208 of the source). -/
theorem Apow_add (m n : ℕ) : S.Apow (m + n) = S.Apow m ∘ S.Apow n := by
  funext z; simp only [Apow, diagMap, Function.comp_apply, pow_add]; ext <;> ring

/-- `A = A^1`: the linear part of a single map. -/
theorem A_eq_Apow_one : S.A = S.Apow 1 := by
  funext z; simp [Apow, A]

/-- `A^n` is additive, being linear. -/
theorem Apow_add_apply (n : ℕ) (z w : ℝ × ℝ) : S.Apow n (z + w) = S.Apow n z + S.Apow n w := by
  simp only [Apow, diagMap, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, mul_add]

/-- `A^n` commutes with subtraction, being linear. -/
theorem Apow_sub_apply (n : ℕ) (z w : ℝ × ℝ) : S.Apow n (z - w) = S.Apow n z - S.Apow n w := by
  simp only [Apow, diagMap, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk, mul_sub]

/-- `A^n 0 = 0`, being linear. -/
theorem Apow_apply_zero (n : ℕ) : S.Apow n 0 = 0 := by
  simp [Apow, diagMap]

/-- `A` is additive, being linear. -/
theorem A_add_apply (z w : ℝ × ℝ) : S.A (z + w) = S.A z + S.A w := by
  rw [A_eq_Apow_one, Apow_add_apply]

/-- `A 0 = 0`, being linear. -/
theorem A_apply_zero : S.A 0 = 0 := by
  rw [A_eq_Apow_one, Apow_apply_zero]

/-- `A^n` as a continuous linear map of the plane, the linear part `A_{φ_u}` of Section 6.2 of
the source (line 1573) for words of length `n`. -/
noncomputable def ApowL (n : ℕ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (S.r₁ ^ n • ContinuousLinearMap.id ℝ ℝ).prodMap (S.r₂ ^ n • ContinuousLinearMap.id ℝ ℝ)

/-- The continuous linear map `ApowL n` is the map `A^n`. -/
theorem coe_ApowL (n : ℕ) : ⇑(S.ApowL n) = S.Apow n := by
  funext z; ext <;> simp [ApowL, Apow, diagMap]

/-- The continuous linear map `ApowL n` is the map `A^n`, pointwise. -/
theorem ApowL_apply (n : ℕ) (z : ℝ × ℝ) : S.ApowL n z = S.Apow n z := by
  rw [coe_ApowL]

/-- `A^n` is continuous, being linear. -/
theorem continuous_Apow (n : ℕ) : Continuous (S.Apow n) := by
  rw [← coe_ApowL]; exact (S.ApowL n).continuous

/-- `A^n` is measurable, being continuous. -/
theorem measurable_Apow (n : ℕ) : Measurable (S.Apow n) := (S.continuous_Apow n).measurable

/-- `A` is continuous, being linear. -/
theorem continuous_A : Continuous S.A := by
  rw [A_eq_Apow_one]; exact S.continuous_Apow 1

/-- `A` is measurable, being continuous. -/
theorem measurable_A : Measurable S.A := S.continuous_A.measurable

/-- The map `φ_i` of line 142 of the source is continuous. -/
theorem continuous_φ (i : ι) : Continuous (S.φ i) := S.continuous_A.add continuous_const

/-- The map `φ_i` of line 142 of the source is measurable. -/
theorem measurable_φ (i : ι) : Measurable (S.φ i) := (S.continuous_φ i).measurable

/-- `|r₁^n| = e^{-χ₁ n}`: the first coordinate of `diag(|r_{u,1}|, |r_{u,2}|) = A_χ^{-t_u}` with
`t_u = n` for a homogeneous system (line 1206 of the source). -/
theorem abs_r₁_pow (n : ℕ) : |S.r₁ ^ n| = Real.exp (-S.χ₁ * n) := by
  rw [χ₁, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log S.abs_r₁_pos, abs_pow]

/-- `|r₂^n| = e^{-χ₂ n}`: the second coordinate of `diag(|r_{u,1}|, |r_{u,2}|) = A_χ^{-t_u}` with
`t_u = n` for a homogeneous system (line 1206 of the source). -/
theorem abs_r₂_pow (n : ℕ) : |S.r₂ ^ n| = Real.exp (-S.χ₂ * n) := by
  rw [χ₂, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log S.abs_r₂_pos, abs_pow]

/-- The horizontal contraction of `A^n`: `|(A^n z).1| = |r₁|^n |z.1|`, by `A^n = diag(r₁^n, r₂^n)`
(line 1200 of the source). -/
theorem abs_fst_Apow (n : ℕ) (z : ℝ × ℝ) : |(S.Apow n z).1| = |S.r₁| ^ n * |z.1| := by
  simp [Apow, diagMap, abs_mul, abs_pow]

/-- The vertical contraction of `A^n`: `|(A^n z).2| = |r₂|^n |z.2|`, by `A^n = diag(r₁^n, r₂^n)`
(line 1200 of the source). -/
theorem abs_snd_Apow (n : ℕ) (z : ℝ × ℝ) : |(S.Apow n z).2| = |S.r₂| ^ n * |z.2| := by
  simp [Apow, diagMap, abs_mul, abs_pow]

/-- `‖A^n z‖ ≤ |r₁|^n ‖z‖` in the supremum norm, since `|r₂| < |r₁|`: the operator norm of the
linear part is `e^{-χ₁ n}` (line 1206 of the source). -/
theorem norm_Apow_le (n : ℕ) (z : ℝ × ℝ) : ‖S.Apow n z‖ ≤ |S.r₁| ^ n * ‖z‖ := by
  have h₂ : |S.r₂| ^ n ≤ |S.r₁| ^ n := pow_le_pow_left₀ (abs_nonneg _) S.abs_r₂_lt.le n
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_fst_Apow, abs_snd_Apow]
  refine max_le ?_ ?_
  · exact mul_le_mul_of_nonneg_left (by simpa using norm_fst_le z) (by positivity)
  · exact (mul_le_mul_of_nonneg_right h₂ (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (by simpa using norm_snd_le z) (by positivity))

/-- `‖A z‖ ≤ |r₁| ‖z‖`, the case `n = 1` of `norm_Apow_le`. -/
theorem norm_A_le (z : ℝ × ℝ) : ‖S.A z‖ ≤ |S.r₁| * ‖z‖ := by
  simpa [← A_eq_Apow_one] using S.norm_Apow_le 1 z

/-! ### Words and the points `φ_u(0)` -/

/-- The empty word gives the identity `φ_∅ = id` (Section 2.3 of the source, line 615). -/
theorem φWord_zero (u : Fin 0 → ι) : S.φWord 0 u = id := rfl

/-- `φ_u = φ_{u 0} ∘ φ_{tail u}`, the composition `φ_{i_1} ∘ ⋯ ∘ φ_{i_n}` of Section 2.3 of the
source (line 613). -/
theorem φWord_succ {n : ℕ} (u : Fin (n + 1) → ι) :
    S.φWord (n + 1) u = S.φ (u 0) ∘ S.φWord n (Fin.tail u) := rfl

/-- `φ_{iu} = φ_i ∘ φ_u` (Section 2.3 of the source, line 613). -/
theorem φWord_cons {n : ℕ} (i : ι) (u : Fin n → ι) :
    S.φWord (n + 1) (Fin.cons i u) = S.φ i ∘ S.φWord n u := by
  rw [φWord_succ, Fin.cons_zero, Fin.tail_cons]

/-- The empty word gives the point `φ_∅(0) = 0`. -/
theorem point_zero (u : Fin 0 → ι) : S.point u = 0 := rfl

/-- `φ_u(0) = A φ_{tail u}(0) + v_{u 0}`, the point `ev_0(φ_u)` of line 1572 of the source. -/
theorem point_succ {n : ℕ} (u : Fin (n + 1) → ι) :
    S.point u = S.A (S.point (Fin.tail u)) + S.v (u 0) := rfl

/-- `φ_{iu}(0) = A φ_u(0) + v_i`, the point `ev_0(φ_{iu})` of line 1572 of the source. -/
theorem point_cons {n : ℕ} (i : ι) (u : Fin n → ι) :
    S.point (Fin.cons i u : Fin (n + 1) → ι) = S.A (S.point u) + S.v i := by
  rw [point_succ, Fin.cons_zero, Fin.tail_cons]

/-- `φ_u(z) = A^n z + φ_u(0)`: `ψ(x) = A_ψ x + ev_0(ψ)` (line 1574 of the source) for `ψ = φ_u`,
whose linear part is `A^n`. -/
theorem φWord_eq {n : ℕ} (u : Fin n → ι) (z : ℝ × ℝ) : S.φWord n u z = S.Apow n z + S.point u := by
  induction n with
  | zero => simp [φWord_zero, point_zero, Apow_zero]
  | succ n ih =>
    rw [φWord_succ, Function.comp_apply, ih, point_succ, φ, Apow_succ, Function.comp_apply,
      A_add_apply]
    abel

/-- The composition `φ_u` is continuous, being affine (line 1574 of the source). -/
theorem continuous_φWord {n : ℕ} (u : Fin n → ι) : Continuous (S.φWord n u) := by
  have : S.φWord n u = fun z => S.Apow n z + S.point u := funext (S.φWord_eq u)
  rw [this]; exact (S.continuous_Apow n).add continuous_const

/-- The composition `φ_u` is measurable, being affine (line 1574 of the source). -/
theorem measurable_φWord {n : ℕ} (u : Fin n → ι) : Measurable (S.φWord n u) :=
  (S.continuous_φWord u).measurable

/-- `φ_{ui}(0) = φ_u(0) + A^n v_i` for a word `u` of length `n`: `ev_0(φ_u ∘ φ_i) = φ_u(v_i)`
(line 1574 of the source). -/
theorem point_snoc {n : ℕ} (u : Fin n → ι) (i : ι) :
    S.point (Fin.snoc u i : Fin (n + 1) → ι) = S.point u + S.Apow n (S.v i) := by
  induction n with
  | zero =>
    rw [point_succ, Fin.snoc_zero, point_zero, point_zero, A_apply_zero, Apow_zero]
    simp
  | succ n ih =>
    obtain ⟨a, q, rfl⟩ : ∃ a q, u = Fin.cons a q := ⟨u 0, Fin.tail u, (Fin.cons_self_tail u).symm⟩
    rw [← Fin.cons_snoc_eq_snoc_cons, point_cons, ih, A_add_apply, point_cons, Apow_succ,
      Function.comp_apply]
    abel

/-- The radius `R₀ = (∑_i ‖v_i‖) / (1 - |r₁|)` of a ball about `0` containing every point
`φ_u(0)`, so that `ν^{(n)}` has compact support uniformly in `n` (line 1582 of the source). -/
noncomputable def R₀ : ℝ := (∑ i, ‖S.v i‖) / (1 - |S.r₁|)

/-- The radius `R₀` is nonnegative. -/
theorem R₀_nonneg : 0 ≤ S.R₀ :=
  div_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) (sub_nonneg.2 S.abs_r₁_lt_one.le)

/-- `|r₁| R₀ + ∑_i ‖v_i‖ = R₀`, the fixed point equation of the radius `R₀`. -/
theorem abs_r₁_mul_R₀_add : |S.r₁| * S.R₀ + ∑ i, ‖S.v i‖ = S.R₀ := by
  have h : (1 - |S.r₁|) ≠ 0 := (sub_pos.2 S.abs_r₁_lt_one).ne'
  rw [R₀]; field_simp; ring

/-- `‖φ_u(0)‖ ≤ R₀`: all points `ev_0(φ_u)` lie in the ball of radius `R₀` about `0`, so that
`ev_0 ν^{(n)}` is compactly supported uniformly in `n` (line 1582 of the source). -/
theorem norm_point_le {n : ℕ} (u : Fin n → ι) : ‖S.point u‖ ≤ S.R₀ := by
  induction n with
  | zero => rw [point_zero, norm_zero]; exact S.R₀_nonneg
  | succ n ih =>
    rw [point_succ]
    calc ‖S.A (S.point (Fin.tail u)) + S.v (u 0)‖
        ≤ ‖S.A (S.point (Fin.tail u))‖ + ‖S.v (u 0)‖ := norm_add_le _ _
      _ ≤ |S.r₁| * S.R₀ + ∑ i, ‖S.v i‖ := by
        gcongr
        · exact (S.norm_A_le _).trans (mul_le_mul_of_nonneg_left (ih _) (abs_nonneg _))
        · exact Finset.single_le_sum (f := fun i => ‖S.v i‖) (fun _ _ => norm_nonneg _)
            (Finset.mem_univ _)
      _ = S.R₀ := S.abs_r₁_mul_R₀_add

/-! ### Weights -/

/-- `p_{iu} = p_i p_u` for the weight `p_u = p_{i_1} ⋯ p_{i_n}` of Section 2.3 of the source
(line 613). -/
theorem weight_cons {n : ℕ} (i : ι) (u : Fin n → ι) :
    S.weight (Fin.cons i u : Fin (n + 1) → ι) = S.p i * S.weight u := by
  simp [weight, Fin.prod_univ_succ]

/-- `p_u = p_{u 0} p_{tail u}` (Section 2.3 of the source, line 613). -/
theorem weight_succ {n : ℕ} (u : Fin (n + 1) → ι) :
    S.weight u = S.p (u 0) * S.weight (Fin.tail u) := by
  conv_lhs => rw [← Fin.cons_self_tail u]
  rw [weight_cons]

/-- `p_{ui} = p_u p_i` (Section 2.3 of the source, line 613). -/
theorem weight_snoc {n : ℕ} (u : Fin n → ι) (i : ι) :
    S.weight (Fin.snoc u i : Fin (n + 1) → ι) = S.weight u * S.p i := by
  simp [weight, Fin.prod_univ_castSucc]

/-- The empty word has weight `p_∅ = 1` (Section 2.3 of the source, line 615). -/
theorem weight_zero (u : Fin 0 → ι) : S.weight u = 1 := by
  simp [weight]

/-- `p_u > 0`, since all weights `p_i` are positive. -/
theorem weight_pos {n : ℕ} (u : Fin n → ι) : 0 < S.weight u :=
  Finset.prod_pos fun k _ => S.p_pos (u k)

/-- `p_u ≥ 0`, since all weights `p_i` are positive. -/
theorem weight_nonneg {n : ℕ} (u : Fin n → ι) : 0 ≤ S.weight u := (S.weight_pos u).le

/-- A sum over words `u ∈ Λ^{n+1}`, split by the first letter: `u = iw`. -/
theorem sum_words_succ {M : Type*} [AddCommMonoid M] {n : ℕ} (f : (Fin (n + 1) → ι) → M) :
    ∑ u, f u = ∑ i, ∑ u : Fin n → ι, f (Fin.cons i u) := by
  rw [← (Fin.consEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type]
  rfl

/-- A sum over words `u ∈ Λ^{n+1}`, split by the last letter: `u = wi`. -/
theorem sum_words_snoc {M : Type*} [AddCommMonoid M] {n : ℕ} (f : (Fin (n + 1) → ι) → M) :
    ∑ u, f u = ∑ u : Fin n → ι, ∑ i, f (Fin.snoc u i) := by
  rw [← (Fin.snocEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- `∑_{u ∈ Λ^n} p_u = 1`: `ν^{(n)}` of line 1582 of the source is a probability measure. -/
theorem sum_weight (n : ℕ) : ∑ u : Fin n → ι, S.weight u = 1 := by
  induction n with
  | zero => simp [weight]
  | succ n ih =>
    simp_rw [sum_words_succ, weight_cons, ← Finset.mul_sum, ih, mul_one, S.p_sum]

/-- `p_u ≤ 1`, since `∑_{u ∈ Λ^n} p_u = 1`. -/
theorem weight_le_one {n : ℕ} (u : Fin n → ι) : S.weight u ≤ 1 := by
  rw [← S.sum_weight n]
  exact Finset.single_le_sum (fun v _ => S.weight_nonneg v) (Finset.mem_univ u)

/-- `-∑_{u ∈ Λ^n} p_u log p_u = n H(p)`: the entropy of the Bernoulli law `p^{×n}` on words of
length `n`, the value `n H(p)` of lines 1902 to 1906 of the source. -/
theorem sum_negMulLog_weight (n : ℕ) :
    ∑ u : Fin n → ι, Real.negMulLog (S.weight u) = n * S.H := by
  induction n with
  | zero => simp [weight]
  | succ n ih =>
    simp_rw [sum_words_succ, weight_cons, Real.negMulLog_mul, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, S.sum_weight, ih, one_mul, ← Finset.sum_mul, S.p_sum,
      H]
    push_cast; ring

/-! ### Finite sums of Dirac masses -/

section Dirac

variable {X κ : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [Fintype κ]

open scoped Classical in
/-- The mass of a set under the finite law `∑_u w_u δ_{x_u}`, as for `ν^{(n)}` (line 1582 of
the source). -/
theorem sum_dirac_apply (w : κ → ℝ) (x : κ → X) (s : Set X) :
    (∑ u, ENNReal.ofReal (w u) • Measure.dirac (x u)) s =
      ∑ u, if x u ∈ s then ENNReal.ofReal (w u) else 0 := by
  classical
  rw [Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  by_cases h : x u ∈ s <;> simp [h]

open scoped Classical in
/-- The real mass of a set under the finite law `∑_u w_u δ_{x_u}`, `w ≥ 0`, as for `ν^{(n)}`
(line 1582 of the source). -/
theorem sum_dirac_real_apply (w : κ → ℝ) (hw : ∀ u, 0 ≤ w u) (x : κ → X) (s : Set X) :
    (∑ u, ENNReal.ofReal (w u) • Measure.dirac (x u)).real s =
      ∑ u, if x u ∈ s then w u else 0 := by
  classical
  rw [Measure.real, sum_dirac_apply, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h : x u ∈ s <;> simp [h, hw u]
  · intro u _
    by_cases h : x u ∈ s <;> simp [h]

/-- A property of every atom holds almost everywhere for a finite sum of Dirac masses, as for
the support of `ν^{(n)}` (line 1582 of the source). -/
theorem ae_sum_dirac (c : κ → ℝ≥0∞) (x : κ → X) {P : X → Prop} (h : ∀ u, P (x u)) :
    ∀ᵐ z ∂(∑ u, c u • Measure.dirac (x u)), P z := by
  rw [ae_iff, Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply, Set.indicator_of_notMem (by simpa using h u),
    smul_zero]

omit [MeasurableSingletonClass X] in
/-- The image of a finite sum of Dirac masses under a measurable map, as for the push-forward
`ev_0 ν^{(n)}` (lines 1571 and 1582 of the source). -/
theorem map_sum_dirac {Y : Type*} [MeasurableSpace Y] (c : κ → ℝ≥0∞) (x : κ → X) {f : X → Y}
    (hf : Measurable f) :
    (∑ u, c u • Measure.dirac (x u)).map f = ∑ u, c u • Measure.dirac (f (x u)) := by
  rw [Measure.map_finset_sum' hf.aemeasurable]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Measure.map_smul _ hf.aemeasurable, Measure.map_dirac' hf]

end Dirac

/-! ### Convolution with finite sums -/

/-- A finite sum of s-finite measures is s-finite, as needed for the convolutions of line 1632
of the source. -/
theorem sFinite_finset_sum {α X : Type*} [MeasurableSpace X] (s : Finset α)
    (μ : α → Measure X) [∀ a, SFinite (μ a)] : SFinite (∑ a ∈ s, μ a) := by
  rw [← Measure.sum_coe_finset]; infer_instance

/-- Convolution distributes over finite sums in the first argument, as in the passage from
`μ = ∑_u p_u φ_u μ` to the convolution form of line 1632 of the source. -/
theorem finset_sum_conv {α : Type*} (s : Finset α) (μ : α → Measure (ℝ × ℝ))
    [∀ a, SFinite (μ a)] (ρ : Measure (ℝ × ℝ)) [SFinite ρ] :
    (∑ a ∈ s, μ a) ∗ ρ = ∑ a ∈ s, μ a ∗ ρ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have := sFinite_finset_sum s μ
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.add_conv, ih]

/-- Convolution distributes over finite sums in the second argument, as in the passage from
`μ = ∑_u p_u φ_u μ` to the convolution form of line 1632 of the source. -/
theorem conv_finset_sum {α : Type*} (s : Finset α) (μ : α → Measure (ℝ × ℝ))
    [∀ a, SFinite (μ a)] (ρ : Measure (ℝ × ℝ)) [SFinite ρ] :
    ρ ∗ (∑ a ∈ s, μ a) = ∑ a ∈ s, ρ ∗ μ a := by
  have := sFinite_finset_sum s μ
  rw [Measure.conv_comm, finset_sum_conv]
  exact Finset.sum_congr rfl fun a _ => Measure.conv_comm _ _

/-! ### The discrete laws `ν_n` -/

open scoped Classical in
/-- `ν_n(s) = ∑_{φ_u(0) ∈ s} p_u` for the law `ν_n = ev_0 ν^{(n)}` of line 1582 of the source. -/
theorem ν_apply (n : ℕ) (s : Set (ℝ × ℝ)) :
    S.ν n s = ∑ u : Fin n → ι, if S.point u ∈ s then ENNReal.ofReal (S.weight u) else 0 :=
  sum_dirac_apply _ _ s

open scoped Classical in
/-- `ν_n(s) = ∑_{φ_u(0) ∈ s} p_u` in `ℝ`, for the law `ν_n = ev_0 ν^{(n)}` of line 1582 of the
source. -/
theorem ν_real_apply (n : ℕ) (s : Set (ℝ × ℝ)) :
    (S.ν n).real s = ∑ u : Fin n → ι, if S.point u ∈ s then S.weight u else 0 :=
  sum_dirac_real_apply _ (fun u => S.weight_nonneg u) _ s

/-- `ν_n = ev_0 ν^{(n)}` is a probability measure (line 1582 of the source), since
`∑_u p_u = 1`. -/
instance isProbabilityMeasure_ν (n : ℕ) : IsProbabilityMeasure (S.ν n) := by
  constructor
  rw [ν_apply]
  simp only [Set.mem_univ, ite_true]
  rw [← ENNReal.ofReal_sum_of_nonneg fun u _ => S.weight_nonneg u, S.sum_weight,
    ENNReal.ofReal_one]

/-- `ν_0 = δ_0`: the empty word gives `φ_∅ = id` (line 615 of the source). -/
theorem ν_zero : S.ν 0 = Measure.dirac 0 := by
  simp [ν, weight_zero, point_zero]

/-- The image of `ν_n = ev_0 ν^{(n)}` (line 1582 of the source) under a measurable map `f` is
`∑_u p_u δ_{f(φ_u(0))}`. -/
theorem map_ν (n : ℕ) {f : ℝ × ℝ → ℝ × ℝ} (hf : Measurable f) :
    (S.ν n).map f = ∑ u : Fin n → ι, ENNReal.ofReal (S.weight u) • Measure.dirac (f (S.point u)) :=
  map_sum_dirac _ _ hf

/-- `ν_{n+1} = ∑_i p_i (φ_i)_* ν_n`: splitting off the first letter in `ν^{(n+1)}` (line 1582 of
the source). -/
theorem ν_succ_eq_sum (n : ℕ) :
    S.ν (n + 1) = ∑ i, ENNReal.ofReal (S.p i) • (S.ν n).map (S.φ i) := by
  simp_rw [S.map_ν n (S.measurable_φ _), Finset.smul_sum, smul_smul,
    ← ENNReal.ofReal_mul (S.p_pos _).le]
  rw [ν, sum_words_succ]
  simp_rw [weight_cons, point_cons, φ]

/-- `ν_1 = ∑_i p_i δ_{v_i}`, the law `ev_0 ν^{(1)}` of line 1582 of the source. -/
theorem ν_one : S.ν 1 = ∑ i, ENNReal.ofReal (S.p i) • Measure.dirac (S.v i) := by
  rw [ν_succ_eq_sum, ν_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.map_dirac' (S.measurable_φ i), φ, A_apply_zero, zero_add]

/-- `ν_{n+1} = ν_n ∗ (A^n)_* ν_1`: appending a last letter in `ν^{(n+1)}` (line 1582 of the
source). -/
theorem ν_succ_eq_conv (n : ℕ) : S.ν (n + 1) = S.ν n ∗ (S.ν 1).map (S.Apow n) := by
  rw [ν_one, map_sum_dirac _ _ (S.measurable_Apow n), conv_finset_sum]
  simp_rw [Measure.conv_smul_right, Measure.conv_dirac]
  simp_rw [S.map_ν n (measurable_add_const _), Finset.smul_sum, smul_smul,
    ← ENNReal.ofReal_mul (S.p_pos _).le]
  rw [Finset.sum_comm, ν, sum_words_snoc]
  simp_rw [weight_snoc, point_snoc, mul_comm (S.p _)]

/-- `ν_n` is carried by the ball of radius `R₀` about `0`: `ν^{(n)} ∈ ℳ_c(Aff(d))` (line 1582 of
the source), uniformly in `n`. -/
theorem inBall_ν (n : ℕ) : InBall (S.ν n) 0 S.R₀ :=
  ae_sum_dirac _ _ fun u => by simpa using S.norm_point_le u

/-- `ν_n` has bounded support: `ν^{(n)} ∈ ℳ_c(Aff(d))` (line 1582 of the source). -/
theorem bddSupp_ν (n : ℕ) : BddSupp (S.ν n) := ⟨0, S.R₀, S.inBall_ν n⟩

/-! ### The self-affine measure -/

section Invariant

variable {μ : Measure (ℝ × ℝ)}

/-- `(φ_i)_* μ = δ_{v_i} ∗ A_* μ`: `ψ μ = δ_{ev_0(ψ)} ∗ A_ψ μ` for `ψ(x) = A_ψ x + ev_0(ψ)`
(lines 1574 and 1632 of the source). -/
theorem map_φ_eq_conv [SFinite μ] (i : ι) :
    μ.map (S.φ i) = Measure.dirac (S.v i) ∗ μ.map S.A := by
  rw [Measure.dirac_conv, Measure.map_map (measurable_const_add _) S.measurable_A]
  congr 1
  funext z
  simp [φ, add_comm]

/-- `(φ_u)_* μ = (· + φ_u(0))_* (A^n)_* μ`: `φ_u μ = δ_{ev_0(φ_u)} ∗ A_{φ_u} μ` (lines 1574 and
1632 of the source). -/
theorem map_φWord_eq [SFinite μ] {n : ℕ} (u : Fin n → ι) :
    μ.map (S.φWord n u) = (μ.map (S.Apow n)).map (· + S.point u) := by
  rw [Measure.map_map (measurable_add_const _) (S.measurable_Apow n)]
  congr 1
  funext z
  simp [φWord_eq]

/-- Iterating the invariance: `μ = ∑_{u ∈ Λ^n} p_u φ_u μ` (line 1632 of the source). -/
theorem eq_sum_map_φWord (hμ : S.IsInvariant μ) (n : ℕ) :
    μ = ∑ u : Fin n → ι, ENNReal.ofReal (S.weight u) • μ.map (S.φWord n u) := by
  induction n with
  | zero => simp [weight_zero, φWord_zero]
  | succ n ih =>
    calc μ = ∑ i, ENNReal.ofReal (S.p i) • μ.map (S.φ i) := hμ
      _ = ∑ i, ENNReal.ofReal (S.p i) •
            (∑ u : Fin n → ι, ENNReal.ofReal (S.weight u) • μ.map (S.φWord n u)).map (S.φ i) := by
          rw [← ih]
      _ = _ := by
          rw [sum_words_succ]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Measure.map_finset_sum' (S.measurable_φ i).aemeasurable, Finset.smul_sum]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Measure.map_smul _ (S.measurable_φ i).aemeasurable,
            Measure.map_map (S.measurable_φ i) (S.measurable_φWord u), smul_smul,
            ← ENNReal.ofReal_mul (S.p_pos i).le, weight_cons, φWord_cons]

/-- `μ = ∑_{u ∈ Λ^n} p_u (· + φ_u(0))_* (A^n)_* μ`, the decomposition of line 1632 of the source
with `φ_u μ = δ_{ev_0(φ_u)} ∗ A^n μ`. -/
theorem eq_sum_map_add_point [SFinite μ] (hμ : S.IsInvariant μ) (n : ℕ) :
    μ = ∑ u : Fin n → ι,
      ENNReal.ofReal (S.weight u) • (μ.map (S.Apow n)).map (· + S.point u) := by
  conv_lhs => rw [S.eq_sum_map_φWord hμ n]
  simp_rw [S.map_φWord_eq]

/-- `μ = ν_n ∗ (A^n)_* μ`: Rapaport's `μ = ∑_{u ∈ Λ^n} p_u φ_u μ` written as a convolution
`μ = ∫ ev_0 ν ∗ A_φ μ dν^{(n)}` (lines 1632 to 1635 of the source) for a homogeneous system,
where `A_{φ_u} = A^n` for all `u`. -/
theorem eq_ν_conv_map_Apow [SFinite μ] (hμ : S.IsInvariant μ) (n : ℕ) :
    μ = S.ν n ∗ μ.map (S.Apow n) := by
  rw [ν, finset_sum_conv]
  simp_rw [Measure.conv_smul_left, Measure.dirac_conv]
  conv_lhs => rw [S.eq_sum_map_add_point hμ n]
  simp_rw [add_comm _ (S.point _)]

end Invariant

/-- The image of a measure carried by the ball `B(c, R)` under `A^n` is carried by the ball
`B(A^n c, R |r₁|^n)`; the support bound for `A_φ μ` behind lines 1636 to 1638 of the source. -/
theorem _root_.BoxLike.Rapaport.InBall.map_Apow {μ : Measure (ℝ × ℝ)} {c : ℝ × ℝ} {R : ℝ}
    (h : InBall μ c R) (n : ℕ) : InBall (μ.map (S.Apow n)) (S.Apow n c) (R * |S.r₁| ^ n) := by
  unfold InBall at h ⊢
  rw [ae_map_iff (S.measurable_Apow n).aemeasurable
    (measurableSet_le (by fun_prop) measurable_const)]
  filter_upwards [h] with z hz
  rw [← Apow_sub_apply, mul_comm]
  exact (S.norm_Apow_le n _).trans (mul_le_mul_of_nonneg_left hz (by positivity))

/-- Coordinatewise support bound for `(A^n)_* μ` when `μ` is carried by `B(c, R)`: horizontal
radius `R |r₁|^n = R e^{-χ₁ n}` and vertical radius `R |r₂|^n = R e^{-χ₂ n}`, so that `A^n μ`
meets `O(1)` cells of `ℰ_n` (lines 1636 to 1638 of the source). -/
theorem _root_.BoxLike.Rapaport.InBall.ae_abs_sub_Apow_le {μ : Measure (ℝ × ℝ)} {c : ℝ × ℝ}
    {R : ℝ} (h : InBall μ c R) (n : ℕ) :
    ∀ᵐ z ∂(μ.map (S.Apow n)), |z.1 - (S.Apow n c).1| ≤ R * |S.r₁| ^ n ∧
      |z.2 - (S.Apow n c).2| ≤ R * |S.r₂| ^ n := by
  unfold InBall at h
  have hs : MeasurableSet {z : ℝ × ℝ | |z.1 - (S.Apow n c).1| ≤ R * |S.r₁| ^ n ∧
      |z.2 - (S.Apow n c).2| ≤ R * |S.r₂| ^ n} := by
    rw [Set.ofPred_and]
    exact (measurableSet_le (by fun_prop) measurable_const).inter
      (measurableSet_le (by fun_prop) measurable_const)
  rw [ae_map_iff (S.measurable_Apow n).aemeasurable hs]
  filter_upwards [h] with z hz
  have h₁ : |(z - c).1| ≤ R := by simpa using (norm_fst_le (z - c)).trans hz
  have h₂ : |(z - c).2| ≤ R := by simpa using (norm_snd_le (z - c)).trans hz
  rw [← Prod.fst_sub, ← Prod.snd_sub, ← Apow_sub_apply, abs_fst_Apow, abs_snd_Apow, mul_comm R,
    mul_comm R]
  exact ⟨mul_le_mul_of_nonneg_left h₁ (by positivity),
    mul_le_mul_of_nonneg_left h₂ (by positivity)⟩

/-! ### Entropy of `ν_n` under exponential separation -/

open ExactOverlaps.Entropy

/-- The entropy of a finite law `∑_u w_u δ_{x_u}`, `w ≥ 0`, for a labelling `f` that separates
the atoms (`f ∘ x` injective) is `-∑_u w_u log w_u`: the label law is the law `w` itself, the
step `H(ν^{(n)}, ev_0^{-1} ℰ_{Mn}) = H(p^{×n})` of lines 1902 to 1906 of the source. -/
theorem ent_sum_dirac_of_injective {X κ L : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [Fintype κ] (w : κ → ℝ) (hw : ∀ u, 0 ≤ w u) (x : κ → X)
    (f : X → L) (hf : Function.Injective (f ∘ x)) :
    ent (∑ u, ENNReal.ofReal (w u) • Measure.dirac (x u)) f = ∑ u, Real.negMulLog (w u) := by
  classical
  have hθ : ∀ b, (∑ u, ENNReal.ofReal (w u) • Measure.dirac (x u)).real (f ⁻¹' {b}) =
      ∑ u, if f (x u) = b then w u else 0 := by
    intro b
    rw [sum_dirac_real_apply w hw x]
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
  unfold ent
  rw [tsum_eq_sum (s := Finset.univ.image (f ∘ x))]
  · rw [Finset.sum_image fun u _ v _ h => hf h]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hθ, Finset.sum_eq_single u]
    · simp
    · intro v _ hv
      have : f (x v) ≠ f (x u) := fun h => hv (hf h)
      simp [this]
    · simp
  · intro b hb
    rw [hθ, Finset.sum_eq_zero, Real.negMulLog_zero]
    intro u _
    have : f (x u) ≠ b := fun h => hb (Finset.mem_image.2 ⟨u, Finset.mem_univ _, h⟩)
    simp [this]

/-- The entropy of a finite law `∑_u w_u δ_{x_u}`, `w ≥ 0`, for a labelling `f` that separates
the atoms of positive weight (`f ∘ x` injective on `{u : w_u ≠ 0}`) is `-∑_u w_u log w_u`, as in
lines 1902 to 1906 of the source. -/
theorem ent_sum_dirac_of_injOn {X κ L : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [Fintype κ] (w : κ → ℝ) (hw : ∀ u, 0 ≤ w u) (x : κ → X)
    (f : X → L) (hf : Set.InjOn (f ∘ x) {u | w u ≠ 0}) :
    ent (∑ u, ENNReal.ofReal (w u) • Measure.dirac (x u)) f = ∑ u, Real.negMulLog (w u) := by
  classical
  have hμ : ∑ u, ENNReal.ofReal (w u) • Measure.dirac (x u) =
      ∑ u : {u // w u ≠ 0}, ENNReal.ofReal (w u) • Measure.dirac (x u) := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun u => w u ≠ 0),
      Fintype.sum_eq_zero (fun u : {u // ¬w u ≠ 0} => ENNReal.ofReal (w u) • Measure.dirac (x u))
        fun u => by simp [not_not.1 u.2], add_zero]
  have hH : ∑ u, Real.negMulLog (w u) = ∑ u : {u // w u ≠ 0}, Real.negMulLog (w u) := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun u => w u ≠ 0),
      Fintype.sum_eq_zero (fun u : {u // ¬w u ≠ 0} => Real.negMulLog (w u))
        fun u => by simp [not_not.1 u.2], add_zero]
  rw [hμ, hH]
  exact ent_sum_dirac_of_injective (fun u : {u // w u ≠ 0} => w u) (fun u => hw u)
    (fun u => x u) f fun a b h => Subtype.ext (hf a.2 b.2 h)

/-- If a labelling `f` separates the points `φ_u(0)`, `u ∈ Λ^n`, then `H(ν_n, f) = n H(p)`
(lines 1902 to 1906 of the source). -/
theorem ent_ν_of_injective {L : Type*} (n : ℕ) (f : ℝ × ℝ → L)
    (hf : Function.Injective (f ∘ S.point (n := n))) : ent (S.ν n) f = n * S.H := by
  rw [ν, ent_sum_dirac_of_injective _ (fun u => S.weight_nonneg u) _ _ hf, sum_negMulLog_weight]

/-- The mesh of the dyadic level `lvl χ n` is at most `2 e^{-χ n}`, the cells of `ℰ_n`
(Section 2.5 of the source, lines 737 to 775) having side `e^{-χ_j n}` up to a factor `2`. -/
private theorem two_zpow_neg_lvl_le (χ : ℝ) (n : ℤ) :
    (2 : ℝ) ^ (-lvl χ n) ≤ 2 * Real.exp (-χ * n) := by
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hfl : χ * n / Real.log 2 - 1 < (lvl χ n : ℝ) := Int.sub_one_lt_floor _
  rw [← Real.rpow_intCast, Real.rpow_def_of_pos two_pos]
  calc Real.exp (Real.log 2 * ((-lvl χ n : ℤ) : ℝ))
      ≤ Real.exp (Real.log 2 * (1 - χ * n / Real.log 2)) := by
        refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hl.le)
        push_cast; linarith
    _ = 2 * Real.exp (-χ * n) := by
        rw [mul_sub, mul_one, mul_div_cancel₀ _ hl.ne', sub_eq_add_neg, Real.exp_add,
          Real.exp_log two_pos, neg_mul]

/-- Two reals with the same dyadic label at level `i` are within `2^{-i}` of each other: the
cells of `𝒟_i` have diameter `2^{-i}` (Section 2.5 of the source). -/
private theorem abs_sub_lt_of_dyadicQuantize_eq {i : ℤ} {x y : ℝ}
    (h : dyadicQuantize i x = dyadicQuantize i y) : |x - y| < (2 : ℝ) ^ (-i) := by
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor h
  have h2 : (0 : ℝ) < 2 ^ i := zpow_pos two_pos i
  rw [← mul_sub, abs_mul, abs_of_pos h2] at h1
  rw [zpow_neg, ← one_div, lt_div_iff₀ h2, mul_comm]
  exact h1

/-- Exponential separation gives full entropy of `ν_n` at the level `ℰ_{Mn}` (lines 1900 to
1908 of the source): there is `M₀ ≥ 1` such that for every `M ≥ M₀`,
`H(ν_n, ℰ_{Mn}) = n H(p)` for infinitely many `n`. Rapaport's `M > 1` is any `M ≥ M₀`; for
a homogeneous system the partition `ℒ_{Aff(d)}` by linear parts is trivial on `supp ν^{(n)}`. -/
theorem XSep.exists_ent_ν_E_eq {S : HomSystem ι} (h : S.XSep) :
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ M, M₀ ≤ M →
      ∃ᶠ n : ℕ in atTop, ent (S.ν n) (S.exps.E (M * n)) = n * S.H := by
  obtain ⟨c, hc, hfreq⟩ := h
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt ((Real.log 2 - Real.log c) / S.χ₁)
  refine ⟨M₀ + 1, Nat.succ_pos _, fun M hM => ?_⟩
  have hM' : Real.log 2 - Real.log c < M * S.χ₁ := by
    have h1 : ((M₀ : ℝ) + 1) ≤ M := by exact_mod_cast hM
    have h2 := (div_lt_iff₀ S.χ₁_pos).1 hM₀
    nlinarith [S.χ₁_pos]
  refine (hfreq.and_eventually (eventually_ge_atTop 1)).mono fun n ⟨hsep, hn⟩ => ?_
  refine S.ent_ν_of_injective n _ fun u u' huu' => ?_
  by_contra hne
  have h1 := hsep u u' hne
  have h2 : dyadicQuantize (lvl S.χ₁ (M * n)) (S.point u).1 =
      dyadicQuantize (lvl S.χ₁ (M * n)) (S.point u').1 := congrArg Prod.fst huu'
  have h3 := abs_sub_lt_of_dyadicQuantize_eq h2
  have h4 := two_zpow_neg_lvl_le S.χ₁ (M * n)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : 2 * Real.exp (-S.χ₁ * ((M * n : ℤ) : ℝ)) ≤ c ^ n := by
    rw [← Real.exp_log hc, ← Real.exp_nat_mul, ← Real.exp_log (two_pos : (0 : ℝ) < 2),
      ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    push_cast
    have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
    nlinarith
  linarith

end BoxLike.Rapaport.HomSystem
