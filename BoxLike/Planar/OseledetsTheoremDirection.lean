module

/-
The deterministic core of Oseledets' multiplicative ergodic theorem in the plane, the classical
two-dimensional argument behind the filtration of `sec:lyapunov_exponents` (tex lines 1508 to
1607). Let `M_{n+1} = B_n M_n` be invertible planar matrices with `‖B_n‖, ‖B_n⁻¹‖ ≤ K`, and
suppose that `n⁻¹ log α_1(M_n) → l_1` and `n⁻¹ log α_2(M_n) → l_2 < l_1`. Then some non-zero
vector `u` has `n⁻¹ log |M_n u| → l_2` and some non-zero `w` has `n⁻¹ log |M_n w| → l_1`.

Proof. For every invertible `M` the unit vector `s` perpendicular to the longer row of `M` has
`|M s| ≤ 2 α_2(M)`; for such `s` and every `x`, `|det M| |s ∧ x| = |M s ∧ M x|` gives
`|s ∧ x| ≤ 4 |M x| / α_1(M)`. Applied to `M_n`, the slow vectors `s_n, s_{n+1}` of `M_n, M_{n+1}`
satisfy `|s_n ∧ s_{n+1}| ≤ C α_2(M_n) / α_1(M_n)`, which decays exponentially at the rate
`l_2 - l_1 < 0`. With the signs chosen so that consecutive inner products are non-negative, the
unit vectors `s_n` form a Cauchy sequence; its limit `u` satisfies
`|u - s_n| ≤ C' e^{n (l_2 - l_1 + δ)}`, so `|M_n u| ≤ |M_n s_n| + 2 α_1(M_n) |u - s_n|` grows at the
rate `l_2`, while `|M_n u| ≥ |det M_n| |u| / (4 α_1(M_n))` gives the lower bound. The vector `w`
perpendicular to `u` has `|s_n ∧ w| → 1`, hence `|M_n w| ≥ α_1(M_n) / 8` eventually. Vectors carry
the supremum norm and matrices the `ℓ²` operator norm, as in `BoxLike/Planar/Oseledets.lean`.

* `MatrixTuple.perp`, `MatrixTuple.dot`, `MatrixTuple.cross_mulVec`,
  `MatrixTuple.abs_cross_le`, `MatrixTuple.norm_perp`, `MatrixTuple.cross_perp`,
  `MatrixTuple.perp_ne_zero`: the plane, `M u ∧ M v = det M (u ∧ v)` and `v ∧ J v = |v|_2²`.
* `MatrixTuple.norm_le_eucNorm`, `MatrixTuple.eucNorm_smul`, `MatrixTuple.eucNorm_neg`,
  `MatrixTuple.continuous_eucNorm`: the Euclidean norm.
* `MatrixTuple.sq_add_le_of_abs_le`, `MatrixTuple.norm_le_two_mul_of_abs_le`,
  `MatrixTuple.abs_det_mul_norm_le`: `α_1(M) ≤ 2 m` for entries bounded by `m`, and
  `|det M| |v| ≤ 4 α_1(M) |M v|`.
* `MatrixTuple.exists_slow_vector`, `MatrixTuple.abs_cross_le_of_slow`,
  `MatrixTuple.abs_cross_slow_succ_le`: the slow vector of a matrix, the angle bound, and the
  angle between the slow vectors of `M` and `B M`.
* `MatrixTuple.alignSeq`, `MatrixTuple.norm_sub_le_two_abs_cross`: the choice of signs, and
  `|a - b| ≤ 2 |a ∧ b|` for unit vectors with `a · b ≥ 0`.
* `MatrixTuple.eventually_le_exp_of_tendsto`, `MatrixTuple.eventually_exp_le_of_tendsto`,
  `MatrixTuple.tendsto_log_div_of_bounds`: growth rates through exponential bounds.
* `MatrixTuple.exists_slow_fast_of_tendsto`: the deterministic planar Oseledets theorem.
-/
public import BoxLike.Planar.OseledetsChoice
public import BoxLike.Planar.Lyapunov

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set Matrix
open scoped Matrix.Norms.L2Operator

namespace MatrixTuple

/-! ### Vectors and matrices in the plane -/

/-- The vector `J v = (-v_1, v_0)`, the vector `v` turned by a right angle. -/
def perp (v : Fin 2 → ℝ) : Fin 2 → ℝ := ![-v 1, v 0]

/-- The Euclidean inner product `u · v = u_0 v_0 + u_1 v_1`. -/
def dot (u v : Fin 2 → ℝ) : ℝ := u 0 * v 0 + u 1 * v 1

/-- `M u ∧ M v = det M (u ∧ v)` for the determinant `cross` of two planar vectors. -/
theorem cross_mulVec (M : Matrix (Fin 2) (Fin 2) ℝ) (u v : Fin 2 → ℝ) :
    cross (M *ᵥ u) (M *ᵥ v) = M.det * cross u v := by
  simp only [cross, mulVec, dotProduct, Fin.sum_univ_two, det_fin_two]
  ring

/-- `|u ∧ v| ≤ 2 |u| |v|` with the supremum norm. -/
theorem abs_cross_le (u v : Fin 2 → ℝ) : |cross u v| ≤ 2 * ‖u‖ * ‖v‖ := by
  have hu0 : |u 0| ≤ ‖u‖ := norm_le_pi_norm u 0
  have hu1 : |u 1| ≤ ‖u‖ := norm_le_pi_norm u 1
  have hv0 : |v 0| ≤ ‖v‖ := norm_le_pi_norm v 0
  have hv1 : |v 1| ≤ ‖v‖ := norm_le_pi_norm v 1
  calc |cross u v| ≤ |u 0| * |v 1| + |u 1| * |v 0| := by
        rw [cross, ← abs_mul, ← abs_mul]
        exact abs_sub _ _
    _ ≤ ‖u‖ * ‖v‖ + ‖u‖ * ‖v‖ := by gcongr
    _ = 2 * ‖u‖ * ‖v‖ := by ring

/-- The vector `J v` has the norm of `v`. -/
theorem norm_perp (v : Fin 2 → ℝ) : ‖perp v‖ = ‖v‖ := by
  rw [norm_fin_two, norm_fin_two]
  simp [perp, max_comm]

/-- `v ∧ J v = |v|_2²`. -/
theorem cross_perp (v : Fin 2 → ℝ) : cross v (perp v) = v 0 ^ 2 + v 1 ^ 2 := by
  simp only [cross, perp, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The vector `J v` vanishes only for `v = 0`. -/
theorem perp_ne_zero {v : Fin 2 → ℝ} (hv : v ≠ 0) : perp v ≠ 0 := by
  intro h
  apply hv
  have h0 : -v 1 = 0 := congrFun h 0
  have h1 : v 0 = 0 := congrFun h 1
  ext j; fin_cases j
  · exact h1
  · simpa using h0

/-- The supremum norm is at most the Euclidean norm. -/
theorem norm_le_eucNorm (v : Fin 2 → ℝ) : ‖v‖ ≤ eucNorm v := by
  rw [norm_fin_two, eucNorm_eq]
  refine max_le ?_ ?_
  · rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (v 1)])
  · rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (v 0)])

/-- The Euclidean norm is homogeneous. -/
theorem eucNorm_smul (c : ℝ) (v : Fin 2 → ℝ) : eucNorm (c • v) = |c| * eucNorm v := by
  rw [eucNorm, eucNorm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

/-- The Euclidean norm of `-v` is that of `v`. -/
theorem eucNorm_neg (v : Fin 2 → ℝ) : eucNorm (-v) = eucNorm v := by
  rw [show -v = (-1 : ℝ) • v by simp, eucNorm_smul]
  simp

/-- The Euclidean norm is continuous. -/
theorem continuous_eucNorm : Continuous eucNorm :=
  continuous_norm.comp (PiLp.continuous_toLp 2 _)

/-- `(a u + b v)² ≤ 2 m² (u² + v²)` for `|a|, |b| ≤ m`. -/
theorem sq_add_le_of_abs_le {a b m : ℝ} (ha : |a| ≤ m) (hb : |b| ≤ m) (u v : ℝ) :
    (a * u + b * v) ^ 2 ≤ 2 * m ^ 2 * (u ^ 2 + v ^ 2) := by
  have ha2 : a ^ 2 ≤ m ^ 2 := by
    rw [← sq_abs a]
    exact pow_le_pow_left₀ (abs_nonneg a) ha 2
  have hb2 : b ^ 2 ≤ m ^ 2 := by
    rw [← sq_abs b]
    exact pow_le_pow_left₀ (abs_nonneg b) hb 2
  nlinarith [sq_nonneg (a * v - b * u), sq_nonneg u, sq_nonneg v]

/-- The `ℓ²` operator norm is at most twice a bound of the entries: `α_1(M) ≤ 2 m`. -/
theorem norm_le_two_mul_of_abs_le (M : Matrix (Fin 2) (Fin 2) ℝ) {m : ℝ}
    (hm : ∀ i j, |M i j| ≤ m) : ‖M‖ ≤ 2 * m := by
  have hm0 : 0 ≤ m := (abs_nonneg _).trans (hm 0 0)
  rw [← l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, Fin.sum_univ_two, ofLp_toEuclideanCLM]
  simp only [mulVec, dotProduct, Fin.sum_univ_two]
  have h0 := sq_add_le_of_abs_le (hm 0 0) (hm 0 1) (x.ofLp 0) (x.ofLp 1)
  have h1 := sq_add_le_of_abs_le (hm 1 0) (hm 1 1) (x.ofLp 0) (x.ofLp 1)
  nlinarith

/-- `|det M| |v| ≤ 4 α_1(M) |M v|`: no vector is contracted by more than `α_2(M)`, up to the
constant of the supremum norm. -/
theorem abs_det_mul_norm_le (M : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) :
    |M.det| * ‖v‖ ≤ 4 * ‖M‖ * ‖M *ᵥ v‖ := by
  have h1 : |M.det| * (v 0 ^ 2 + v 1 ^ 2) ≤ 2 * ‖M *ᵥ v‖ * ‖M *ᵥ perp v‖ := by
    have h := abs_cross_le (M *ᵥ v) (M *ᵥ perp v)
    rwa [cross_mulVec, cross_perp, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ v 0 ^ 2 + v 1 ^ 2)] at h
  have h2 : ‖M *ᵥ perp v‖ ≤ 2 * ‖M‖ * ‖v‖ := by
    have h := norm_mulVec_le M (perp v)
    rwa [norm_perp] at h
  have h3 : ‖v‖ ^ 2 ≤ v 0 ^ 2 + v 1 ^ 2 := by
    rw [norm_fin_two]
    rcases max_choice |v 0| |v 1| with h | h <;> rw [h, sq_abs] <;> nlinarith [sq_nonneg (v 0),
      sq_nonneg (v 1)]
  rcases eq_or_lt_of_le (norm_nonneg v) with h | h
  · rw [← h, mul_zero]
    positivity
  · refine le_of_mul_le_mul_right ?_ h
    have hd := abs_nonneg M.det
    have hMv := norm_nonneg (M *ᵥ v)
    calc |M.det| * ‖v‖ * ‖v‖ = |M.det| * ‖v‖ ^ 2 := by ring
      _ ≤ |M.det| * (v 0 ^ 2 + v 1 ^ 2) := by gcongr
      _ ≤ 2 * ‖M *ᵥ v‖ * ‖M *ᵥ perp v‖ := h1
      _ ≤ 2 * ‖M *ᵥ v‖ * (2 * ‖M‖ * ‖v‖) := by gcongr
      _ = 4 * ‖M‖ * ‖M *ᵥ v‖ * ‖v‖ := by ring

/-- The slow vector of an invertible matrix: the Euclidean unit vector `s` perpendicular to the
longer row of `M` has `|M s| ≤ 2 |det M| / α_1(M) = 2 α_2(M)`. -/
theorem exists_slow_vector (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det ≠ 0) :
    ∃ s : Fin 2 → ℝ, eucNorm s = 1 ∧ ‖M *ᵥ s‖ ≤ 2 * |M.det| / ‖M‖ := by
  set r0 := max |M 0 0| |M 0 1| with hr0
  set r1 := max |M 1 0| |M 1 1| with hr1
  obtain ⟨s₀, hs₀M, hs₀n⟩ : ∃ s₀ : Fin 2 → ℝ, ‖M *ᵥ s₀‖ = |M.det| ∧ ‖s₀‖ = max r0 r1 := by
    rcases le_total r1 r0 with h | h
    · refine ⟨![-M 0 1, M 0 0], ?_, ?_⟩
      · rw [norm_fin_two]
        simp only [mulVec, dotProduct, Fin.sum_univ_two, det_fin_two, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        rw [show M 0 0 * -M 0 1 + M 0 1 * M 0 0 = 0 by ring, abs_zero,
          max_eq_right (abs_nonneg _)]
        congr 1
        ring
      · rw [norm_fin_two, max_eq_left h, hr0]
        simp [max_comm]
    · refine ⟨![-M 1 1, M 1 0], ?_, ?_⟩
      · rw [norm_fin_two]
        simp only [mulVec, dotProduct, Fin.sum_univ_two, det_fin_two, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        rw [show M 1 0 * -M 1 1 + M 1 1 * M 1 0 = 0 by ring, abs_zero,
          max_eq_left (abs_nonneg _), show M 0 0 * -M 1 1 + M 0 1 * M 1 0 =
            -(M 0 0 * M 1 1 - M 0 1 * M 1 0) by ring, abs_neg]
      · rw [norm_fin_two, max_eq_right h, hr1]
        simp [max_comm]
  have hm : ∀ i j, |M i j| ≤ max r0 r1 := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  have hnorm := norm_le_two_mul_of_abs_le M hm
  have hMpos : 0 < ‖M‖ := norm_pos_of_det_ne_zero hM
  have he : ‖s₀‖ ≤ eucNorm s₀ := norm_le_eucNorm s₀
  have hepos : 0 < eucNorm s₀ := by linarith
  refine ⟨(eucNorm s₀)⁻¹ • s₀, ?_, ?_⟩
  · rw [eucNorm_smul, abs_inv, abs_of_pos hepos, inv_mul_cancel₀ hepos.ne']
  · rw [mulVec_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hepos, hs₀M,
      inv_mul_eq_div, div_le_div_iff₀ hepos hMpos]
    nlinarith [abs_nonneg M.det]

/-- The angle bound: if `|M s| ≤ C |det M| / α_1(M)`, then `|s ∧ x| ≤ 2 C |M x| / α_1(M)` for
every `x`, since `|det M| |s ∧ x| = |M s ∧ M x| ≤ 2 |M s| |M x|`. -/
theorem abs_cross_le_of_slow {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.det ≠ 0) {s : Fin 2 → ℝ}
    {C : ℝ} (hs : ‖M *ᵥ s‖ ≤ C * |M.det| / ‖M‖) (x : Fin 2 → ℝ) :
    |cross s x| ≤ 2 * C * ‖M *ᵥ x‖ / ‖M‖ := by
  have h := abs_cross_le (M *ᵥ s) (M *ᵥ x)
  rw [cross_mulVec, abs_mul] at h
  have hd : 0 < |M.det| := abs_pos.2 hM
  have hMpos : 0 < ‖M‖ := norm_pos_of_det_ne_zero hM
  have hMx := norm_nonneg (M *ᵥ x)
  have h2 : |M.det| * |cross s x| * ‖M‖ ≤ |M.det| * (2 * C * ‖M *ᵥ x‖) := by
    have h3 : |M.det| * |cross s x| ≤ 2 * (C * |M.det| / ‖M‖) * ‖M *ᵥ x‖ :=
      h.trans (by gcongr)
    have h4 : 2 * (C * |M.det| / ‖M‖) * ‖M *ᵥ x‖ * ‖M‖ = |M.det| * (2 * C * ‖M *ᵥ x‖) := by
      field_simp
    calc |M.det| * |cross s x| * ‖M‖ ≤ 2 * (C * |M.det| / ‖M‖) * ‖M *ᵥ x‖ * ‖M‖ := by
          gcongr
      _ = _ := h4
  rw [le_div_iff₀ hMpos]
  rw [mul_assoc] at h2
  exact le_of_mul_le_mul_left h2 hd

/-! ### The choice of signs -/

/-- The sequence `±s_n` with the signs chosen inductively so that consecutive inner products are
non-negative. -/
noncomputable def alignSeq (s : ℕ → Fin 2 → ℝ) : ℕ → Fin 2 → ℝ
  | 0 => s 0
  | n + 1 => if 0 ≤ dot (alignSeq s n) (s (n + 1)) then s (n + 1) else -s (n + 1)

/-- Every term of `alignSeq s` is `s_n` or `-s_n`. -/
theorem alignSeq_eq_or (s : ℕ → Fin 2 → ℝ) : ∀ n, alignSeq s n = s n ∨ alignSeq s n = -s n
  | 0 => Or.inl rfl
  | n + 1 => by
    show (if 0 ≤ dot (alignSeq s n) (s (n + 1)) then s (n + 1) else -s (n + 1)) = s (n + 1) ∨
      (if 0 ≤ dot (alignSeq s n) (s (n + 1)) then s (n + 1) else -s (n + 1)) = -s (n + 1)
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- Consecutive terms of `alignSeq s` have a non-negative inner product. -/
theorem dot_alignSeq_nonneg (s : ℕ → Fin 2 → ℝ) (n : ℕ) :
    0 ≤ dot (alignSeq s n) (alignSeq s (n + 1)) := by
  show 0 ≤ dot (alignSeq s n)
    (if 0 ≤ dot (alignSeq s n) (s (n + 1)) then s (n + 1) else -s (n + 1))
  split_ifs with h
  · exact h
  · simp only [dot, Pi.neg_apply] at h ⊢
    linarith

/-- `|a - b| ≤ 2 |a ∧ b|` for Euclidean unit vectors with `a · b ≥ 0`: by Lagrange's identity
`(a · b)² + (a ∧ b)² = 1`, so `|a - b|_2² = 2 - 2 a · b ≤ 2 (a ∧ b)²`. -/
theorem norm_sub_le_two_abs_cross {a b : Fin 2 → ℝ} (ha : eucNorm a = 1) (hb : eucNorm b = 1)
    (hab : 0 ≤ dot a b) : ‖a - b‖ ≤ 2 * |cross a b| := by
  have ha2 : a 0 ^ 2 + a 1 ^ 2 = 1 := by rw [← eucNorm_sq, ha, one_pow]
  have hb2 : b 0 ^ 2 + b 1 ^ 2 = 1 := by rw [← eucNorm_sq, hb, one_pow]
  have hlag : dot a b ^ 2 + cross a b ^ 2 = 1 := by
    have : dot a b ^ 2 + cross a b ^ 2 = (a 0 ^ 2 + a 1 ^ 2) * (b 0 ^ 2 + b 1 ^ 2) := by
      simp only [dot, cross]
      ring
    rw [this, ha2, hb2, one_mul]
  have hdot1 : dot a b ≤ 1 := by nlinarith [sq_nonneg (cross a b), sq_nonneg (dot a b - 1)]
  have hsum : (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 ≤ (2 * |cross a b|) ^ 2 := by
    have e : (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 = 2 - 2 * dot a b := by
      simp only [dot]
      nlinarith
    rw [e, mul_pow, sq_abs]
    nlinarith
  have hc := abs_nonneg (cross a b)
  rw [norm_fin_two]
  refine max_le ?_ ?_
  · refine (sq_le_sq₀ (abs_nonneg _) (by positivity)).1 ?_
    rw [sq_abs]
    simp only [Pi.sub_apply]
    nlinarith [sq_nonneg (a 1 - b 1)]
  · refine (sq_le_sq₀ (abs_nonneg _) (by positivity)).1 ?_
    rw [sq_abs]
    simp only [Pi.sub_apply]
    nlinarith [sq_nonneg (a 0 - b 0)]

/-! ### Growth rates through exponential bounds -/

/-- If `n⁻¹ log a_n → l`, then eventually `a_n ≤ e^{n (l + ε)}`. -/
theorem eventually_le_exp_of_tendsto {a : ℕ → ℝ} {l : ℝ} (ha : ∀ n, 0 < a n)
    (h : Tendsto (fun n : ℕ => Real.log (a n) / n) atTop (𝓝 l)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, a n ≤ Real.exp (n * (l + ε)) := by
  filter_upwards [h.eventually (gt_mem_nhds (by linarith : l < l + ε)),
    eventually_gt_atTop 0] with n hn hn0
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  rw [div_lt_iff₀ hn'] at hn
  rw [← Real.exp_log (ha n)]
  exact Real.exp_le_exp.2 (by linarith)

/-- If `n⁻¹ log a_n → l`, then eventually `e^{n (l - ε)} ≤ a_n`. -/
theorem eventually_exp_le_of_tendsto {a : ℕ → ℝ} {l : ℝ} (ha : ∀ n, 0 < a n)
    (h : Tendsto (fun n : ℕ => Real.log (a n) / n) atTop (𝓝 l)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.exp (n * (l - ε)) ≤ a n := by
  filter_upwards [h.eventually (lt_mem_nhds (by linarith : l - ε < l)),
    eventually_gt_atTop 0] with n hn hn0
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  rw [lt_div_iff₀ hn'] at hn
  rw [← Real.exp_log (ha n)]
  exact Real.exp_le_exp.2 (by linarith)

/-- A positive sequence with `a_n ≤ C e^{n (l + ε)}` and `C' e^{n (l - ε)} ≤ a_n` eventually, for
every `ε > 0`, has the growth rate `n⁻¹ log a_n → l`. -/
theorem tendsto_log_div_of_bounds {a : ℕ → ℝ} {l : ℝ} (ha : ∀ n, 0 < a n)
    (hup : ∀ ε > 0, ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, a n ≤ C * Real.exp (n * (l + ε)))
    (hlow : ∀ ε > 0, ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop, C * Real.exp (n * (l - ε)) ≤ a n) :
    Tendsto (fun n : ℕ => Real.log (a n) / n) atTop (𝓝 l) := by
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨C, hC, hev⟩ := hlow ((l - b) / 2) (by linarith)
    have h0 : Tendsto (fun n : ℕ => Real.log C / n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    filter_upwards [hev, h0.eventually (lt_mem_nhds (by linarith : -((l - b) / 2) < 0)),
      eventually_gt_atTop 0] with n hn hn2 hn0
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
    have hlog : Real.log C + n * (l - (l - b) / 2) ≤ Real.log (a n) := by
      have := Real.log_le_log (by positivity) hn
      rwa [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp] at this
    rw [lt_div_iff₀ hn']
    rw [lt_div_iff₀ hn'] at hn2
    nlinarith
  · obtain ⟨C, hev⟩ := hup ((b - l) / 2) (by linarith)
    have hC : ∀ᶠ n : ℕ in atTop, 0 < C := hev.mono fun n hn =>
      pos_of_mul_pos_left ((ha n).trans_le hn) (Real.exp_pos _).le
    obtain ⟨n₁, hn₁⟩ := hC.exists
    have hC' : 0 < C := hn₁
    have h0 : Tendsto (fun n : ℕ => Real.log C / n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    filter_upwards [hev, h0.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < (b - l) / 2)),
      eventually_gt_atTop 0] with n hn hn2 hn0
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
    have hlog : Real.log (a n) ≤ Real.log C + n * (l + (b - l) / 2) := by
      have := Real.log_le_log (ha n) hn
      rwa [Real.log_mul hC'.ne' (Real.exp_pos _).ne', Real.log_exp] at this
    rw [div_lt_iff₀ hn']
    rw [div_lt_iff₀ hn'] at hn2
    nlinarith

/-! ### The deterministic theorem -/

/-- One step of the slow directions: if `M' = B M` with `‖B‖, ‖B⁻¹‖ ≤ K`, `s` is a slow vector of
`M` and `s'` one of `M'`, then `|s ∧ s'| ≤ 32 K⁴ |det M| / α_1(M)²`. -/
theorem abs_cross_slow_succ_le {M B : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.det ≠ 0)
    (hB : B.det ≠ 0) {K : ℝ} (hK : ‖B‖ ≤ K) (hK' : ‖B⁻¹‖ ≤ K) {s s' : Fin 2 → ℝ}
    (hs : ‖M *ᵥ s‖ ≤ 2 * |M.det| / ‖M‖)
    (hs' : ‖(B * M) *ᵥ s'‖ ≤ 2 * |(B * M).det| / ‖B * M‖) :
    |cross s s'| ≤ 32 * K ^ 4 * (|M.det| / ‖M‖ ^ 2) := by
  have hBM : (B * M).det ≠ 0 := by rw [det_mul]; exact mul_ne_zero hB hM
  have hMpos : 0 < ‖M‖ := norm_pos_of_det_ne_zero hM
  have hBMpos : 0 < ‖B * M‖ := norm_pos_of_det_ne_zero hBM
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hK
  have hd := abs_nonneg M.det
  have hinv : M = B⁻¹ * (B * M) := by
    rw [← Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hB), Matrix.one_mul]
  have h1 : ‖M *ᵥ s'‖ ≤ 2 * K * (2 * |(B * M).det| / ‖B * M‖) := by
    conv_lhs => rw [hinv, ← mulVec_mulVec]
    calc ‖B⁻¹ *ᵥ ((B * M) *ᵥ s')‖ ≤ 2 * ‖B⁻¹‖ * ‖(B * M) *ᵥ s'‖ := norm_mulVec_le _ _
      _ ≤ 2 * K * (2 * |(B * M).det| / ‖B * M‖) := by gcongr
  have h2 : |(B * M).det| ≤ 2 * K ^ 2 * |M.det| := by
    rw [det_mul, abs_mul]
    have := (abs_det_le_two_mul_sq_norm B).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg B) hK 2) (by norm_num))
    exact mul_le_mul_of_nonneg_right this hd
  have h3 : ‖M‖ ≤ K * ‖B * M‖ := by
    conv_lhs => rw [hinv]
    exact (l2_opNorm_mul _ _).trans (by gcongr)
  have h4 : ‖M *ᵥ s'‖ ≤ 8 * K ^ 4 * |M.det| / ‖M‖ := by
    refine h1.trans ?_
    rw [mul_div_assoc', div_le_div_iff₀ hBMpos hMpos]
    calc 2 * K * (2 * |(B * M).det|) * ‖M‖
        ≤ 2 * K * (2 * (2 * K ^ 2 * |M.det|)) * (K * ‖B * M‖) := by gcongr
      _ = 8 * K ^ 4 * |M.det| * ‖B * M‖ := by ring
  have h5 := abs_cross_le_of_slow hM (C := 2) (by simpa using hs) s'
  calc |cross s s'| ≤ 2 * 2 * ‖M *ᵥ s'‖ / ‖M‖ := h5
    _ ≤ 2 * 2 * (8 * K ^ 4 * |M.det| / ‖M‖) / ‖M‖ := by gcongr
    _ = 32 * K ^ 4 * (|M.det| / ‖M‖ ^ 2) := by field_simp; ring

/-- **The deterministic planar Oseledets theorem.** Let `M_{n+1} = B_n M_n` be invertible
planar matrices with `‖B_n‖, ‖B_n⁻¹‖ ≤ K`, `n⁻¹ log α_1(M_n) → l_1` and
`n⁻¹ log α_2(M_n) → l_2 < l_1`, where `α_2(M) = |det M| / ‖M‖`. Then a non-zero `u` grows at
the rate `l_2` and a non-zero `w` grows at the rate `l_1`: `n⁻¹ log |M_n u| → l_2` and
`n⁻¹ log |M_n w| → l_1`. This is the two-dimensional argument behind the filtration of
`sec:lyapunov_exponents` (tex lines 1508 to 1530): `u` is the limit of the slow directions of
`M_n`, and `w` is perpendicular to it. -/
theorem exists_slow_fast_of_tendsto {M B : ℕ → Matrix (Fin 2) (Fin 2) ℝ}
    (hMB : ∀ n, M (n + 1) = B n * M n) (hM : ∀ n, (M n).det ≠ 0) (hB : ∀ n, (B n).det ≠ 0)
    {K : ℝ} (hK : ∀ n, ‖B n‖ ≤ K) (hK' : ∀ n, ‖(B n)⁻¹‖ ≤ K) {l₁ l₂ : ℝ} (hlt : l₂ < l₁)
    (h₁ : Tendsto (fun n : ℕ => Real.log ‖M n‖ / n) atTop (𝓝 l₁))
    (h₂ : Tendsto (fun n : ℕ => Real.log (|(M n).det| / ‖M n‖) / n) atTop (𝓝 l₂)) :
    ∃ u w : Fin 2 → ℝ, u ≠ 0 ∧ w ≠ 0 ∧
      Tendsto (fun n : ℕ => Real.log ‖M n *ᵥ u‖ / n) atTop (𝓝 l₂) ∧
      Tendsto (fun n : ℕ => Real.log ‖M n *ᵥ w‖ / n) atTop (𝓝 l₁) := by
  have hMn : ∀ n, 0 < ‖M n‖ := fun n => norm_pos_of_det_ne_zero (hM n)
  have hdn : ∀ n, 0 < |(M n).det| := fun n => abs_pos.2 (hM n)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  -- The slow vectors and the choice of signs.
  choose s hs1 hs2 using fun n => exists_slow_vector (M n) (hM n)
  set e := alignSeq s with he_def
  have he1 : ∀ n, eucNorm (e n) = 1 := fun n => by
    rw [he_def]
    rcases alignSeq_eq_or s n with h | h <;> rw [h]
    · exact hs1 n
    · rw [eucNorm_neg]; exact hs1 n
  have he2 : ∀ n, ‖M n *ᵥ e n‖ ≤ 2 * |(M n).det| / ‖M n‖ := fun n => by
    rw [he_def]
    rcases alignSeq_eq_or s n with h | h <;> rw [h]
    · exact hs2 n
    · rw [mulVec_neg, norm_neg]; exact hs2 n
  -- The ratio `ρ_n = α_2(M_n) / α_1(M_n)` and the steps of the slow directions.
  set ρ : ℕ → ℝ := fun n => |(M n).det| / ‖M n‖ ^ 2 with hρ_def
  have hρpos : ∀ n, 0 < ρ n := fun n => div_pos (hdn n) (pow_pos (hMn n) 2)
  set C := 64 * K ^ 4 with hC_def
  have hC0 : 0 ≤ C := by positivity
  have hstep : ∀ n, dist (e n) (e (n + 1)) ≤ C * ρ n := by
    intro n
    have hc : |cross (e n) (e (n + 1))| ≤ 32 * K ^ 4 * ρ n := by
      have hcs := abs_cross_slow_succ_le (hM n) (hB n) (hK n) (hK' n) (he2 n)
        (s' := e (n + 1)) (by rw [← hMB]; exact he2 (n + 1))
      exact hcs
    rw [dist_eq_norm]
    calc ‖e n - e (n + 1)‖ ≤ 2 * |cross (e n) (e (n + 1))| :=
          norm_sub_le_two_abs_cross (he1 n) (he1 (n + 1)) (dot_alignSeq_nonneg s n)
      _ ≤ 2 * (32 * K ^ 4 * ρ n) := by gcongr
      _ = C * ρ n := by rw [hC_def]; ring
  have hρrate : Tendsto (fun n : ℕ => Real.log (ρ n) / n) atTop (𝓝 (l₂ - l₁)) := by
    refine (h₂.sub h₁).congr fun n => ?_
    rw [← sub_div]
    congr 1
    rw [hρ_def]
    dsimp only
    rw [show |(M n).det| / ‖M n‖ ^ 2 = |(M n).det| / ‖M n‖ / ‖M n‖ by ring,
      Real.log_div (div_pos (hdn n) (hMn n)).ne' (hMn n).ne']
  -- Geometric bounds for the steps.
  have hgeo : ∀ δ, 0 < δ → ∃ N, ∀ n ≥ N,
      dist (e n) (e (n + 1)) ≤ C * Real.exp (l₂ - l₁ + δ) ^ n := by
    intro δ hδ
    obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_le_exp_of_tendsto hρpos hρrate hδ)
    refine ⟨N, fun n hn => (hstep n).trans ?_⟩
    rw [← Real.exp_nat_mul]
    exact mul_le_mul_of_nonneg_left (hN n hn) hC0
  -- The limit `u` of the slow directions.
  have hr : ∀ δ, δ < l₁ - l₂ → Real.exp (l₂ - l₁ + δ) < 1 := fun δ hδ =>
    Real.exp_lt_one_iff.2 (by linarith)
  have hrate : ∀ δ, 0 < δ → δ < l₁ - l₂ → ∀ u, Tendsto e atTop (𝓝 u) → ∃ N, ∀ n ≥ N,
      ‖e n - u‖ ≤ C / (1 - Real.exp (l₂ - l₁ + δ)) * Real.exp (l₂ - l₁ + δ) ^ n := by
    intro δ hδ hδ' u hu
    obtain ⟨N, hN⟩ := hgeo δ hδ
    set r := Real.exp (l₂ - l₁ + δ) with hr_def
    have hr1 : r < 1 := hr δ hδ'
    have hd := dist_le_of_le_geometric_of_tendsto r (C * r ^ N) hr1 (f := fun k => e (k + N))
      (fun k => by
        have := hN (k + N) (by omega)
        rw [pow_add, show k + N + 1 = k + 1 + N by omega] at this
        calc dist (e (k + N)) (e (k + 1 + N)) ≤ C * (r ^ k * r ^ N) := this
          _ = C * r ^ N * r ^ k := by ring)
      ((tendsto_add_atTop_iff_nat N).2 hu)
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + N := ⟨n - N, by omega⟩
    have h := hd k
    rw [dist_eq_norm] at h
    have hr1' : 0 < 1 - r := by linarith
    calc ‖e (k + N) - u‖ ≤ C * r ^ N * r ^ k / (1 - r) := h
      _ = C / (1 - r) * r ^ (k + N) := by rw [pow_add]; field_simp
  obtain ⟨N₀, hN₀⟩ := hgeo ((l₁ - l₂) / 2) (by linarith)
  have hcauchy : CauchySeq fun k => e (k + N₀) := by
    refine cauchySeq_of_le_geometric (Real.exp (l₂ - l₁ + (l₁ - l₂) / 2))
      (C * Real.exp (l₂ - l₁ + (l₁ - l₂) / 2) ^ N₀) (hr _ (by linarith)) fun k => ?_
    have := hN₀ (k + N₀) (by omega)
    rw [pow_add, show k + N₀ + 1 = k + 1 + N₀ by omega] at this
    calc dist (e (k + N₀)) (e (k + 1 + N₀)) ≤ _ := this
      _ = _ := by ring
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hcauchy
  have heu : Tendsto e atTop (𝓝 u) := (tendsto_add_atTop_iff_nat N₀).1 hu
  have hu1 : eucNorm u = 1 := by
    have h := (continuous_eucNorm.tendsto u).comp heu
    have hconst : (eucNorm ∘ e) = fun _ => (1 : ℝ) := funext fun n => he1 n
    rw [hconst] at h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp [eucNorm] at hu1
  have hunorm : 0 < ‖u‖ := norm_pos_iff.2 hu0
  set w := perp u with hw_def
  have hw0 : w ≠ 0 := perp_ne_zero hu0
  have hwnorm : ‖w‖ = ‖u‖ := norm_perp u
  refine ⟨u, w, hu0, hw0, ?_, ?_⟩
  · -- The vector `u` grows at the rate `l_2`.
    refine tendsto_log_div_of_bounds (fun n => norm_pos_iff.2
      (mulVec_ne_zero_of_det_ne_zero (hM n) hu0)) (fun ε hε => ?_) (fun ε hε => ?_)
    · set δ := min (ε / 2) ((l₁ - l₂) / 2) with hδ_def
      have hδ : 0 < δ := lt_min (by linarith) (by linarith)
      have hδ1 : δ < l₁ - l₂ := (min_le_right _ _).trans_lt (by linarith)
      have hδ2 : δ ≤ ε / 2 := min_le_left _ _
      obtain ⟨N, hN⟩ := hrate δ hδ hδ1 u heu
      set r := Real.exp (l₂ - l₁ + δ) with hr_def
      have hr1 : r < 1 := hr δ hδ1
      set C' := C / (1 - r) with hC'_def
      have hC'0 : 0 ≤ C' := div_nonneg hC0 (by linarith)
      refine ⟨2 + 2 * C', ?_⟩
      filter_upwards [eventually_ge_atTop N, eventually_le_exp_of_tendsto hMn h₁ hδ,
        eventually_le_exp_of_tendsto (fun n => div_pos (hdn n) (hMn n)) h₂ hδ] with n hn ha hb
      have hsplit : M n *ᵥ u = M n *ᵥ e n + M n *ᵥ (u - e n) := by
        rw [← mulVec_add, add_sub_cancel]
      have hdiff : ‖u - e n‖ ≤ C' * r ^ n := by rw [norm_sub_rev]; exact hN n hn
      have hexp1 : Real.exp (n * (l₂ + δ)) ≤ Real.exp (n * (l₂ + ε)) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n))
      have hexp2 : Real.exp (n * (l₁ + δ)) * r ^ n ≤ Real.exp (n * (l₂ + ε)) := by
        rw [hr_def, ← Real.exp_nat_mul, ← Real.exp_add]
        exact Real.exp_le_exp.2 (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      have hrn : 0 ≤ r ^ n := pow_nonneg (Real.exp_pos _).le n
      calc ‖M n *ᵥ u‖ ≤ ‖M n *ᵥ e n‖ + ‖M n *ᵥ (u - e n)‖ := by
            rw [hsplit]; exact norm_add_le _ _
        _ ≤ 2 * (|(M n).det| / ‖M n‖) + 2 * ‖M n‖ * ‖u - e n‖ := by
            gcongr
            · exact (he2 n).trans_eq (mul_div_assoc _ _ _)
            · exact norm_mulVec_le _ _
        _ ≤ 2 * Real.exp (n * (l₂ + δ)) + 2 * Real.exp (n * (l₁ + δ)) * (C' * r ^ n) := by
            gcongr
        _ = 2 * Real.exp (n * (l₂ + δ)) + 2 * C' * (Real.exp (n * (l₁ + δ)) * r ^ n) := by
            ring
        _ ≤ 2 * Real.exp (n * (l₂ + ε)) + 2 * C' * Real.exp (n * (l₂ + ε)) := by gcongr
        _ = (2 + 2 * C') * Real.exp (n * (l₂ + ε)) := by ring
    · refine ⟨‖u‖ / 4, by positivity, ?_⟩
      filter_upwards [eventually_exp_le_of_tendsto (fun n => div_pos (hdn n) (hMn n)) h₂ hε]
        with n hn
      have h := abs_det_mul_norm_le (M n) u
      have hMn' := hMn n
      calc ‖u‖ / 4 * Real.exp (n * (l₂ - ε)) ≤ ‖u‖ / 4 * (|(M n).det| / ‖M n‖) := by gcongr
        _ = |(M n).det| * ‖u‖ / (4 * ‖M n‖) := by field_simp
        _ ≤ ‖M n *ᵥ u‖ := by
            rw [div_le_iff₀ (by positivity)]
            linarith
  · -- The vector `w` perpendicular to `u` grows at the rate `l_1`.
    refine tendsto_log_div_of_bounds (fun n => norm_pos_iff.2
      (mulVec_ne_zero_of_det_ne_zero (hM n) hw0)) (fun ε hε => ?_) (fun ε hε => ?_)
    · refine ⟨2 * ‖w‖, ?_⟩
      filter_upwards [eventually_le_exp_of_tendsto hMn h₁ hε] with n hn
      calc ‖M n *ᵥ w‖ ≤ 2 * ‖M n‖ * ‖w‖ := norm_mulVec_le _ _
        _ ≤ 2 * Real.exp (n * (l₁ + ε)) * ‖w‖ := by gcongr
        _ = 2 * ‖w‖ * Real.exp (n * (l₁ + ε)) := by ring
    · refine ⟨1 / 8, by norm_num, ?_⟩
      have hcross : Tendsto (fun n => cross (e n) w) atTop (𝓝 (cross u w)) := by
        have hc : Continuous fun v : Fin 2 → ℝ => cross v w := by
          unfold cross
          fun_prop
        exact (hc.tendsto u).comp heu
      have hcu : cross u w = 1 := by
        rw [hw_def, cross_perp, ← eucNorm_sq, hu1, one_pow]
      rw [hcu] at hcross
      filter_upwards [hcross.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1)),
        eventually_exp_le_of_tendsto hMn h₁ hε] with n hn hn'
      have h := abs_cross_le_of_slow (hM n) (C := 2) (by simpa [mul_div_assoc] using he2 n) w
      have hMn' := hMn n
      have habs : 1 / 2 ≤ |cross (e n) w| := hn.le.trans (le_abs_self _)
      have h2 : ‖M n‖ / 8 ≤ ‖M n *ᵥ w‖ := by
        have h3 : 1 / 2 ≤ 2 * 2 * ‖M n *ᵥ w‖ / ‖M n‖ := habs.trans h
        rw [le_div_iff₀ hMn'] at h3
        linarith
      calc 1 / 8 * Real.exp (n * (l₁ - ε)) ≤ 1 / 8 * ‖M n‖ := by gcongr
        _ = ‖M n‖ / 8 := by ring
        _ ≤ ‖M n *ᵥ w‖ := h2

end MatrixTuple

end BoxLike
