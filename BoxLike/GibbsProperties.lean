module

/-
Unlabelled claims of the article about the equilibrium state and the two Gibbs measures: the
comment on the method in the introduction (tex lines 507 to 507), `sec:affinity_dim` (tex lines
2241 to 2256), `sec:normalisation` (tex lines 2236 to 2250) and `sec:gibbs_measures` (tex lines
2489 to 2500, 2581 to 2607 and 2634 to 2636), with `eq:tau_cylinder`.

* `IsSubmultiplicative`, `IsQuasiBernoulli`, `IsBernoulli`: sub-multiplicative, quasi-Bernoulli
  and Bernoulli measures on the full shift.
* `gapExp`, `svf_eq_norm_rpow_mul_abs_det_rpow`: the constant `c_s` and the form
  `φ^s(A) = ‖A‖^{c_s} |det A|^{(s - c_s)/2}` of the singular value function for `s ≤ 2`.
* `System.exists_mul_svf_le`: along the words `D^n R D^n` the singular value function fails to be
  super-multiplicative by an exponentially large factor.
* `System.HasGibbsBoundsWith`, `IsGibbsWith`: the Gibbs bounds of `thm:irred_eq_state` and the
  Gibbs property of `sec:gibbs_measures` with their constants made explicit.
* `System.HasGibbsBoundsWith.measureReal_cylinder_append_le`,
  `System.HasGibbsBounds.submultiplicative`: `μ[𝐢𝐣] ≤ C³ μ[𝐢] μ[𝐣]`.
* `System.HasGibbsBounds.cylinder_bounds_dimaff`: `C⁻¹ φ^s(A_𝐢) ≤ μ[𝐢] ≤ C φ^s(A_𝐢)` at
  `s = dimaff(𝖠)`.
* `System.HasGibbsBoundsWith.mul_measureReal_cylinder_append_le`,
  `System.HasGibbsBounds.exists_mul_measureReal_cylinder_le`, `System.not_quasiBernoulli`,
  `System.not_forall_measureReal_cylinder_eq_prod`, `System.not_isBernoulli`: for a proximal
  box-like tuple with rotations and `0 < s < 2`, a measure with the Gibbs bounds is neither
  quasi-Bernoulli nor Bernoulli.
* `System.IsEquilibriumState.submultiplicative`, `System.IsEquilibriumState.cylinder_bounds_dimaff`:
  sub-multiplicativity and the cylinder bounds of the equilibrium state of an irreducible
  tuple, from the Gibbs bounds of Feng–Käenmäki, `FengKaenmakiGibbs`, which the library proves
  (`fengKaenmakiGibbs_holds`).
* `System.IsEquilibriumState.not_quasiBernoulli`, `System.IsEquilibriumState.not_isBernoulli`:
  the equilibrium state of a proximal box-like tuple with rotations is neither quasi-Bernoulli
  nor Bernoulli, from the Gibbs bounds of `EquilibriumGibbsStatement`, which the library proves
  (`equilibriumGibbs`).
* `IsGibbsWith.measureReal_cylinder_le_succ`, `IsGibbsWith.doubling`, `IsGibbs.doubling`:
  `ν[𝐢|_n] ≤ C² exp(P + ‖f‖_∞) ν[𝐢|_{n+1}]`;
  `IsGibbsWith.measureReal_preimage_shift_cylinder_le` is the companion for an extension to the
  left, and `exists_mem_subshift_zero_eq` identifies `‖f‖_∞`.
* `cylinder_tau_inter_subshift`, `map_unCode_restrict_range_tau_cylinder`,
  `IsGibbs.map_unCode_restrict_range_tau_cylinder_pos`: `eq:tau_cylinder` and
  `\overline{τ}_*ν([𝐢|_n]) = ν([τ(𝐢)|_n]) > 0`.
* `mutuallySingular_of_ergodic_of_ne`: distinct ergodic probability measures are mutually
  singular.
* `System.potential₁_tau`: `f_{1,s}(τ(𝐢)) = f_{2,s}(ω(𝐢))`.
* `System.potential₁_sub_potential₂`, `System.sum_potential₁_sub_sum_potential₂_const`:
  `S_n f_{1,s}(𝐣) - S_n f_{2,s}(𝐣) = c_s n (log |a_{i_0}| - log |b_{i_0}|)`.
* `System.not_isGibbs_potential₁_and_potential₂`, `System.GibbsDecomposition.ne`,
  `System.GibbsDecomposition.mutuallySingular`: `μ_1 ≠ μ_2` and `μ_1 ⟂ μ_2`.
* `System.GibbsDecomposition.map_tau_eq_map_omega`, `System.GibbsDecomposition.map_tau_cylinder`,
  `System.GibbsDecomposition.map_tau_univ_pos`, `System.GibbsDecomposition.map_omega_univ_pos`,
  `System.GibbsDecomposition.map_absolutelyContinuous`: `\overline{τ}_*μ_1 = \overline{ω}_*μ_2`,
  `\overline{τ}_*μ_2 = \overline{ω}_*μ_1`, positivity, and absolute continuity with respect to
  `μ`.
-/
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.GibbsOrientation
public import Mathlib.Dynamics.Ergodic.Extreme

@[expose] public section

namespace BoxLike

open MeasureTheory Set
open scoped Matrix.Norms.L2Operator

universe u

/-! ### Sub-multiplicative, quasi-Bernoulli and Bernoulli measures -/

section Definitions

variable {α : Type*} [MeasurableSpace α]

/-- A sub-multiplicative measure, `sec:affinity_dim`, tex lines 2129 to 2131: there is `C ≥ 1`
with `μ[𝐢𝐣] ≤ C μ[𝐢] μ[𝐣]` for all finite words `𝐢, 𝐣 ∈ Σ_*^+`. The words of `Σ_*^+` are
non-empty. -/
def IsSubmultiplicative (μ : Measure (ℤ → α)) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ m n : ℕ, 0 < m → 0 < n → ∀ (w : Fin m → α) (w' : Fin n → α),
    μ.real (cylinder (Fin.append w w')) ≤ C * (μ.real (cylinder w) * μ.real (cylinder w'))

/-- A quasi-Bernoulli measure, tex lines 507 to 507: the measure of the concatenation of two
words is comparable to the product of the measures of the words,
`C⁻¹ μ[𝐢] μ[𝐣] ≤ μ[𝐢𝐣] ≤ C μ[𝐢] μ[𝐣]` for all `𝐢, 𝐣 ∈ Σ_*^+`. -/
def IsQuasiBernoulli (μ : Measure (ℤ → α)) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ m n : ℕ, 0 < m → 0 < n → ∀ (w : Fin m → α) (w' : Fin n → α),
    C⁻¹ * (μ.real (cylinder w) * μ.real (cylinder w')) ≤ μ.real (cylinder (Fin.append w w')) ∧
      μ.real (cylinder (Fin.append w w')) ≤ C * (μ.real (cylinder w) * μ.real (cylinder w'))

/-- A Bernoulli measure, `sec:normalisation`, tex lines 2236 to 2241: there is a probability
vector `p` with `μ[i_k ⋯ i_ℓ] = p_{i_k} ⋯ p_{i_ℓ}` for every cylinder
`[i_k ⋯ i_ℓ] = {𝐣 : j_k = i_k, …, j_ℓ = i_ℓ}` of the two-sided shift, which is
`σ^{-k}[w]` for the word `w = i_k ⋯ i_ℓ`. -/
def IsBernoulli [Fintype α] (μ : Measure (ℤ → α)) : Prop :=
  ∃ p : α → ℝ, (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ ∀ (k : ℤ) (n : ℕ), 0 < n → ∀ w : Fin n → α,
    μ.real (shift k ⁻¹' cylinder w) = ∏ j, p (w j)

variable {μ : Measure (ℤ → α)}

/-- A quasi-Bernoulli measure is sub-multiplicative. -/
theorem IsQuasiBernoulli.isSubmultiplicative (h : IsQuasiBernoulli μ) :
    IsSubmultiplicative μ := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C, hC, fun m n hm hn w w' => (h m n hm hn w w').2⟩

/-- The measure of a cylinder of a Bernoulli measure is the product of the measures of its
symbols. -/
theorem IsBernoulli.measureReal_cylinder_eq_prod [Fintype α] (h : IsBernoulli μ) {n : ℕ}
    (hn : 0 < n) (w : Fin n → α) : μ.real (cylinder w) = ∏ k, μ.real (cylinder ![w k]) := by
  obtain ⟨p, -, -, hp⟩ := h
  have h0 : ∀ {m : ℕ} (v : Fin m → α), shift 0 ⁻¹' cylinder v = cylinder v := fun v =>
    Set.ext fun x => by rw [Set.mem_preimage, shift_zero]
  have h1 : ∀ i : α, μ.real (cylinder ![i]) = p i := fun i => by
    rw [← h0, hp 0 1 one_pos]
    simp
  rw [← h0 w, hp 0 n hn]
  exact Finset.prod_congr rfl fun k _ => (h1 (w k)).symm

/-- A measure whose cylinders have the product of the measures of their symbols as measure is
quasi-Bernoulli, with constant `1`. -/
theorem isQuasiBernoulli_of_measureReal_cylinder_eq_prod
    (h : ∀ n : ℕ, 0 < n → ∀ w : Fin n → α,
      μ.real (cylinder w) = ∏ k, μ.real (cylinder ![w k])) : IsQuasiBernoulli μ := by
  refine ⟨1, le_rfl, fun m n hm hn w w' => ?_⟩
  have e : μ.real (cylinder (Fin.append w w')) = μ.real (cylinder w) * μ.real (cylinder w') := by
    rw [h (m + n) (by omega), h m hm, h n hn, Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  rw [e]
  simp

/-- A Bernoulli measure is quasi-Bernoulli. -/
theorem IsBernoulli.isQuasiBernoulli [Fintype α] (h : IsBernoulli μ) : IsQuasiBernoulli μ :=
  isQuasiBernoulli_of_measureReal_cylinder_eq_prod fun _ hn w =>
    h.measureReal_cylinder_eq_prod hn w

end Definitions

/-! ### The singular value function through `c_s` -/

/-- The constant `c_s` of `sec:gibbs_measures`, tex line 2470: `c_s = s` for `s < 1` and
`c_s = 2 - s` for `1 ≤ s`. -/
noncomputable def gapExp (s : ℝ) : ℝ := if s < 1 then s else 2 - s

/-- `c_s > 0` for `0 < s < 2`. -/
theorem gapExp_pos {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) : 0 < gapExp s := by
  unfold gapExp
  split_ifs <;> linarith

/-- `φ^s(A) = ‖A‖^{c_s} |det A|^{(s - c_s)/2}` for `s ≤ 2`: the exponent of `|det A|` is `0` for
`s ≤ 1` and `s - 1` for `1 < s ≤ 2`. -/
theorem svf_eq_norm_rpow_mul_abs_det_rpow {s : ℝ} (hs2 : s ≤ 2)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    svf s A = ‖A‖ ^ gapExp s * |A.det| ^ ((s - gapExp s) / 2) := by
  unfold svf gapExp
  rcases lt_trichotomy s 1 with h | rfl | h
  · rw [ite_eq_left h.le, ite_eq_left h, sub_self, zero_div, Real.rpow_zero, mul_one]
  · norm_num
  · rw [ite_eq_right (not_le.2 h), ite_eq_left hs2, ite_eq_right (not_lt.2 h.le)]
    congr 2
    ring

/-- The determinant is multiplicative, so a failure of super-multiplicativity of the norm passes
to `φ^s` with the exponent `c_s`. -/
theorem mul_svf_mul_le_of_norm {s : ℝ} (hs2 : s ≤ 2) {A B : Matrix (Fin 2) (Fin 2) ℝ} {K : ℝ}
    (h : K * ‖A * B‖ ^ gapExp s ≤ ‖A‖ ^ gapExp s * ‖B‖ ^ gapExp s) :
    K * svf s (A * B) ≤ svf s A * svf s B := by
  rw [svf_eq_norm_rpow_mul_abs_det_rpow hs2 (A * B), svf_eq_norm_rpow_mul_abs_det_rpow hs2 A,
    svf_eq_norm_rpow_mul_abs_det_rpow hs2 B, Matrix.det_mul, abs_mul,
    Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  have hd : 0 ≤ |A.det| ^ ((s - gapExp s) / 2) * |B.det| ^ ((s - gapExp s) / 2) :=
    mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
  calc K * (‖A * B‖ ^ gapExp s *
          (|A.det| ^ ((s - gapExp s) / 2) * |B.det| ^ ((s - gapExp s) / 2)))
      = K * ‖A * B‖ ^ gapExp s *
          (|A.det| ^ ((s - gapExp s) / 2) * |B.det| ^ ((s - gapExp s) / 2)) := by ring
    _ ≤ ‖A‖ ^ gapExp s * ‖B‖ ^ gapExp s *
          (|A.det| ^ ((s - gapExp s) / 2) * |B.det| ^ ((s - gapExp s) / 2)) :=
        mul_le_mul_of_nonneg_right h hd
    _ = _ := by ring

/-- The arithmetic of the norms of `D^n`, `R D^n` and `D^n R D^n`, with `α ≥ β` the moduli of the
entries of `D` and `Γ ≥ γ` those of `R`. -/
private theorem div_mul_div_pow_mul_le {α β γ Γ x y z : ℝ} (hα : 0 ≤ α) (hβ : 0 < β)
    (hγ : 0 ≤ γ) (hΓ : 0 < Γ) (n : ℕ) (hx : α ^ n ≤ x) (hy : γ * α ^ n ≤ y)
    (hz : z ≤ Γ * (α * β) ^ n) : γ / Γ * (α / β) ^ n * z ≤ x * y :=
  calc γ / Γ * (α / β) ^ n * z ≤ γ / Γ * (α / β) ^ n * (Γ * (α * β) ^ n) :=
        mul_le_mul_of_nonneg_left hz (by positivity)
    _ = α ^ n * (γ * α ^ n) := by
        rw [div_pow, mul_pow]
        field_simp
    _ ≤ x * y := mul_le_mul hx hy (by positivity) ((pow_nonneg hα n).trans hx)

/-- For `D = diag(a, b)` and the anti-diagonal matrix `R` with entries `c`, `d`, the norm of
`D^n R D^n` is smaller than the product of the norms of `D^n` and `R D^n` by the factor
`(min{|c|, |d|} / max{|c|, |d|}) (max{|a|, |b|} / min{|a|, |b|})^n`. -/
theorem mul_norm_boxMat_mul_le {a b c d : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (n : ℕ) :
    min |c| |d| / max |c| |d| * (max |a| |b| / min |a| |b|) ^ n *
        ‖boxMat 0 (a ^ n) (b ^ n) * boxMat 1 (c * b ^ n) (d * a ^ n)‖ ≤
      ‖boxMat 0 (a ^ n) (b ^ n)‖ * ‖boxMat 1 (c * b ^ n) (d * a ^ n)‖ := by
  have hab : |a| * |b| = max |a| |b| * min |a| |b| := abs_mul_abs_eq_max_mul_min a b
  have hmax : ∀ x y : ℝ, max x y ^ n ≤ max (x ^ n) (y ^ n) := fun x y => by
    rcases le_total x y with h | h
    · rw [max_eq_right h]
      exact le_max_right _ _
    · rw [max_eq_left h]
      exact le_max_left _ _
  refine div_mul_div_pow_mul_le (le_max_of_le_left (abs_nonneg a))
    (lt_min (abs_pos.2 ha) (abs_pos.2 hb)) (le_min (abs_nonneg c) (abs_nonneg d))
    (lt_max_of_lt_left (abs_pos.2 hc)) n ?_ ?_ ?_
  · rw [norm_boxMat, abs_pow, abs_pow]
    exact hmax _ _
  · rw [norm_boxMat, abs_mul, abs_mul, abs_pow, abs_pow]
    rcases le_total |a| |b| with h | h
    · rw [max_eq_right h]
      exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (pow_nonneg (abs_nonneg b) n)) (le_max_left _ _)
    · rw [max_eq_left h]
      exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _)
        (pow_nonneg (abs_nonneg a) n)) (le_max_right _ _)
  · have hpow : 0 ≤ (max |a| |b| * min |a| |b|) ^ n := by rw [← hab]; positivity
    have e1 : |a ^ n * (c * b ^ n)| = |c| * (max |a| |b| * min |a| |b|) ^ n := by
      rw [← hab, abs_mul, abs_mul, abs_pow, abs_pow, mul_pow]
      ring
    have e2 : |b ^ n * (d * a ^ n)| = |d| * (max |a| |b| * min |a| |b|) ^ n := by
      rw [← hab, abs_mul, abs_mul, abs_pow, abs_pow, mul_pow]
      ring
    rw [boxMat_mul, ite_eq_left rfl, ite_eq_left rfl, norm_boxMat, e1, e2]
    exact max_le (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow)

namespace System

/-! ### The failure of super-multiplicativity -/

section Words

variable {ι : Type u} (S : System ι)

/-- `A_𝐮^n = diag(a^n, b^n)` for a word `𝐮` with `A_𝐮 = diag(a, b)`. -/
theorem matWord_flatten_replicate {u : List ι} {a b : ℝ} (hu : S.matWord u = boxMat 0 a b)
    (n : ℕ) : S.matWord (List.replicate n u).flatten = boxMat 0 (a ^ n) (b ^ n) := by
  induction n with
  | zero =>
    ext k l
    fin_cases k <;> fin_cases l <;> simp
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, matWord_append, hu, ih, boxMat_mul]
    simp [pow_succ']

/-- `A_j A_𝐮^n` is the anti-diagonal matrix with entries `a_j b^n` and `b_j a^n`, for a word `𝐮`
with `A_𝐮 = diag(a, b)` and an anti-diagonal generator `A_j`. -/
theorem matWord_cons_flatten_replicate {u : List ι} {a b : ℝ}
    (hu : S.matWord u = boxMat 0 a b) {j : ι} (hj : S.o j = 1) (n : ℕ) :
    S.matWord (j :: (List.replicate n u).flatten) =
      boxMat 1 (S.a j * b ^ n) (S.b j * a ^ n) := by
  rw [matWord_cons, S.matWord_flatten_replicate hu, mat, hj, boxMat_mul, ite_eq_right (by decide),
    ite_eq_right (by decide), add_zero]

/-- A proximal box-like tuple has a non-empty word `𝐮` whose product is a diagonal matrix
`diag(a, b)` with `|a| ≠ |b|`: a proximal product `A_𝐮` is not anti-diagonal. -/
theorem Proximal.exists_matWord_eq (hprox : S.Proximal) :
    ∃ (u : List ι) (a b : ℝ), u ≠ [] ∧ S.oWord u = 0 ∧ S.matWord u = boxMat 0 a b ∧ a ≠ 0 ∧
      b ≠ 0 ∧ |a| ≠ |b| := by
  obtain ⟨u, hu0, hu⟩ := hprox
  have hmat := S.matWord_eq u
  rcases zmod_two_cases (S.oWord u) with ho | ho
  · rw [ho] at hmat
    rw [hmat] at hu
    exact ⟨u, _, _, hu0, ho, hmat, S.gDeriv_ne_zero _, S.gDeriv_ne_zero _,
      isProximalMatrix_boxMat_zero.1 hu⟩
  · rw [hmat, ho] at hu
    exact absurd hu (not_isProximalMatrix_boxMat_one _ _)

/-- The failure of super-multiplicativity of the singular value function, tex lines 507 to 507:
for a proximal box-like tuple with rotations and `0 < s < 2` there are a diagonal block `D = A_𝐮`
with entries `a`, `b` of distinct moduli and an anti-diagonal generator `R = A_j` such that
`φ^s(D^n) φ^s(R D^n) ≥ c q^n φ^s(D^n R D^n)` with `q = (max{|a|, |b|} / min{|a|, |b|})^{c_s} > 1`.
The word `𝐮^n` is `(List.replicate n u).flatten`. -/
theorem exists_mul_svf_le {s : ℝ} (hrot : S.WithRotations) (hprox : S.Proximal) (hs0 : 0 < s)
    (hs2 : s < 2) :
    ∃ (u : List ι) (j : ι) (c q : ℝ), u ≠ [] ∧ S.oWord u = 0 ∧ S.o j = 1 ∧ 0 < c ∧ 1 < q ∧
      ∀ n : ℕ, c * q ^ n * svf s (S.matWord
          ((List.replicate n u).flatten ++ j :: (List.replicate n u).flatten)) ≤
        svf s (S.matWord (List.replicate n u).flatten) *
          svf s (S.matWord (j :: (List.replicate n u).flatten)) := by
  obtain ⟨u, a, b, hu0, ho, hu, ha, hb, hne⟩ := hprox.exists_matWord_eq
  obtain ⟨j, hj⟩ := hrot.2
  have ht := gapExp_pos hs0 hs2
  have hβ : 0 < min |a| |b| := lt_min (abs_pos.2 ha) (abs_pos.2 hb)
  have hq : 1 < max |a| |b| / min |a| |b| := (one_lt_div hβ).2 (min_lt_max.2 hne)
  have hc : 0 < min |S.a j| |S.b j| / max |S.a j| |S.b j| :=
    div_pos (lt_min (abs_pos.2 (S.a_ne_zero j)) (abs_pos.2 (S.b_ne_zero j)))
      (lt_max_of_lt_left (abs_pos.2 (S.a_ne_zero j)))
  refine ⟨u, j, (min |S.a j| |S.b j| / max |S.a j| |S.b j|) ^ gapExp s,
    (max |a| |b| / min |a| |b|) ^ gapExp s, hu0, ho, hj, Real.rpow_pos_of_pos hc _,
    Real.one_lt_rpow hq ht, fun n => ?_⟩
  rw [matWord_append, S.matWord_flatten_replicate hu, S.matWord_cons_flatten_replicate hu hj]
  refine mul_svf_mul_le_of_norm hs2.le ?_
  have key := Real.rpow_le_rpow (by positivity)
    (mul_norm_boxMat_mul_le ha hb (S.a_ne_zero j) (d := S.b j) n) ht.le
  rwa [Real.mul_rpow (by positivity) (norm_nonneg _), Real.mul_rpow hc.le (by positivity),
    ← Real.rpow_pow_comm (zero_lt_one.trans hq).le,
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _)] at key

end Words

/-! ### Consequences of the Gibbs bounds of `thm:irred_eq_state` -/

section GibbsBounds

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] (S : System ι) {s C : ℝ}
  {μ : Measure (ℤ → ι)}

/-- The Gibbs bounds of `thm:irred_eq_state` with the constant `C ≥ 1` made explicit. -/
def HasGibbsBoundsWith (C s : ℝ) (μ : Measure (ℤ → ι)) : Prop :=
  1 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ w : Fin n → ι,
    C⁻¹ * (Real.exp (-(n * S.pressure s)) * svf s (S.matWord (List.ofFn w))) ≤
        μ.real (cylinder w) ∧
      μ.real (cylinder w) ≤
        C * (Real.exp (-(n * S.pressure s)) * svf s (S.matWord (List.ofFn w)))

/-- `System.HasGibbsBounds` asks for some constant. -/
theorem hasGibbsBounds_iff : S.HasGibbsBounds s μ ↔ ∃ C, S.HasGibbsBoundsWith C s μ := Iff.rfl

variable {S}

/-- A measure with the Gibbs bounds charges every cylinder. -/
theorem HasGibbsBoundsWith.measureReal_cylinder_pos (h : S.HasGibbsBoundsWith C s μ) {n : ℕ}
    (hn : 0 < n) (w : Fin n → ι) : 0 < μ.real (cylinder w) :=
  lt_of_lt_of_le (mul_pos (inv_pos.2 (one_pos.trans_le h.1))
    (mul_pos (Real.exp_pos _) (S.svf_matWord_pos s _))) (h.2 n hn w).1

/-- The display of tex lines 2134 to 2137: by the Gibbs bounds with constant `C` and the
sub-multiplicativity of the singular value function,
`μ[𝐢𝐣] ≤ C exp(-(|𝐢| + |𝐣|) P(𝖠, s)) φ^s(A_𝐢) φ^s(A_𝐣) ≤ C³ μ[𝐢] μ[𝐣]`. -/
theorem HasGibbsBoundsWith.measureReal_cylinder_append_le (hs : 0 ≤ s)
    (h : S.HasGibbsBoundsWith C s μ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (w : Fin m → ι)
    (w' : Fin n → ι) :
    μ.real (cylinder (Fin.append w w')) ≤
        C * (Real.exp (-(((m : ℝ) + n) * S.pressure s)) *
          (svf s (S.matWord (List.ofFn w)) * svf s (S.matWord (List.ofFn w')))) ∧
      C * (Real.exp (-(((m : ℝ) + n) * S.pressure s)) *
          (svf s (S.matWord (List.ofFn w)) * svf s (S.matWord (List.ofFn w')))) ≤
        C ^ 3 * (μ.real (cylinder w) * μ.real (cylinder w')) := by
  obtain ⟨hC, hb⟩ := h
  have hC0 : 0 < C := one_pos.trans_le hC
  have hexp : Real.exp (-(((m : ℝ) + n) * S.pressure s)) =
      Real.exp (-(m * S.pressure s)) * Real.exp (-(n * S.pressure s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  constructor
  · have h1 := (hb (m + n) (by omega) (Fin.append w w')).2
    rw [List.ofFn_fin_append, matWord_append, Nat.cast_add] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (svf_mul_le hs _ _) (Real.exp_pos _).le) hC0.le)
  · have h2 := (hb m hm w).1
    have h3 := (hb n hn w').1
    rw [inv_mul_le_iff₀ hC0] at h2 h3
    calc C * (Real.exp (-(((m : ℝ) + n) * S.pressure s)) *
            (svf s (S.matWord (List.ofFn w)) * svf s (S.matWord (List.ofFn w'))))
        = C * (Real.exp (-(m * S.pressure s)) * svf s (S.matWord (List.ofFn w)) *
            (Real.exp (-(n * S.pressure s)) * svf s (S.matWord (List.ofFn w')))) := by
          rw [hexp]
          ring
      _ ≤ C * (C * μ.real (cylinder w) * (C * μ.real (cylinder w'))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h2 h3
            (mul_nonneg (Real.exp_pos _).le (svf_nonneg _ _))
            (mul_nonneg hC0.le measureReal_nonneg)) hC0.le
      _ = C ^ 3 * (μ.real (cylinder w) * μ.real (cylinder w')) := by ring

/-- The equilibrium state is sub-multiplicative, tex lines 2132 to 2138: a measure with the Gibbs
bounds of `thm:irred_eq_state` with constant `C` is sub-multiplicative with constant `C³`. -/
theorem HasGibbsBounds.submultiplicative (hs : 0 ≤ s) (h : S.HasGibbsBounds s μ) :
    IsSubmultiplicative μ := by
  obtain ⟨C, h⟩ := (hasGibbsBounds_iff S).1 h
  refine ⟨C ^ 3, one_le_pow₀ h.1, fun m n hm hn w w' => ?_⟩
  obtain ⟨h1, h2⟩ := h.measureReal_cylinder_append_le hs hm hn w w'
  exact h1.trans h2

/-- Tex lines 2250 to 2256, with the constant of the Gibbs bounds: at `s = dimaff(𝖠)` the pressure
vanishes and `C⁻¹ φ^s(A_𝐢) ≤ μ[𝐢] ≤ C φ^s(A_𝐢)` for all `𝐢 ∈ Σ_*^+`. -/
theorem HasGibbsBoundsWith.cylinder_bounds_dimaff [Nonempty ι]
    (h : S.HasGibbsBoundsWith C S.dimaff μ) {n : ℕ} (hn : 0 < n) (w : Fin n → ι) :
    C⁻¹ * svf S.dimaff (S.matWord (List.ofFn w)) ≤ μ.real (cylinder w) ∧
      μ.real (cylinder w) ≤ C * svf S.dimaff (S.matWord (List.ofFn w)) := by
  have hb := h.2 n hn w
  rwa [S.pressure_dimaff, mul_zero, neg_zero, Real.exp_zero, one_mul] at hb

/-- Tex lines 2250 to 2256: at `s = dimaff(𝖠)` a measure with the Gibbs bounds of
`thm:irred_eq_state` gives each cylinder a mass comparable to the value of the singular value
function, `C⁻¹ φ^s(A_𝐢) ≤ μ[𝐢] ≤ C φ^s(A_𝐢)` for all `𝐢 ∈ Σ_*^+`. -/
theorem HasGibbsBounds.cylinder_bounds_dimaff [Nonempty ι] (h : S.HasGibbsBounds S.dimaff μ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ w : Fin n → ι,
      C⁻¹ * svf S.dimaff (S.matWord (List.ofFn w)) ≤ μ.real (cylinder w) ∧
        μ.real (cylinder w) ≤ C * svf S.dimaff (S.matWord (List.ofFn w)) := by
  obtain ⟨C, h⟩ := (hasGibbsBounds_iff S).1 h
  exact ⟨C, h.1, fun n hn w => h.cylinder_bounds_dimaff hn w⟩

/-- The Gibbs property transfers a failure of super-multiplicativity to the measure, tex lines
523 to 524: if `κ φ^s(A_𝐢 A_𝐣) ≤ φ^s(A_𝐢) φ^s(A_𝐣)` for non-empty words `𝐢`, `𝐣`, then
`κ C⁻³ μ[𝐢𝐣] ≤ μ[𝐢] μ[𝐣]` for a measure with the Gibbs bounds with constant `C`. The word of a
list `l` is `l.get`. -/
theorem HasGibbsBoundsWith.mul_measureReal_cylinder_append_le (h : S.HasGibbsBoundsWith C s μ)
    {l l' : List ι} (hl : l ≠ []) (hl' : l' ≠ []) {κ : ℝ} (hκ : 0 ≤ κ)
    (hsvf : κ * svf s (S.matWord (l ++ l')) ≤ svf s (S.matWord l) * svf s (S.matWord l')) :
    κ / C ^ 3 * μ.real (cylinder (Fin.append l.get l'.get)) ≤
      μ.real (cylinder l.get) * μ.real (cylinder l'.get) := by
  obtain ⟨hC, hb⟩ := h
  have hC0 : 0 < C := one_pos.trans_le hC
  have hlen : 0 < l.length := List.length_pos_of_ne_nil hl
  have hlen' : 0 < l'.length := List.length_pos_of_ne_nil hl'
  have h1 := (hb (l.length + l'.length) (by omega) (Fin.append l.get l'.get)).2
  have h2 := (hb l.length hlen l.get).1
  have h3 := (hb l'.length hlen' l'.get).1
  rw [List.ofFn_fin_append, List.ofFn_get, List.ofFn_get] at h1
  rw [List.ofFn_get] at h2 h3
  have hexp : Real.exp (-(((l.length + l'.length : ℕ) : ℝ) * S.pressure s)) =
      Real.exp (-(l.length * S.pressure s)) * Real.exp (-(l'.length * S.pressure s)) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  calc κ / C ^ 3 * μ.real (cylinder (Fin.append l.get l'.get))
      ≤ κ / C ^ 3 * (C * (Real.exp (-(((l.length + l'.length : ℕ) : ℝ) * S.pressure s)) *
          svf s (S.matWord (l ++ l')))) :=
        mul_le_mul_of_nonneg_left h1 (div_nonneg hκ (pow_pos hC0 3).le)
    _ = C⁻¹ * C⁻¹ * (Real.exp (-(((l.length + l'.length : ℕ) : ℝ) * S.pressure s)) *
          (κ * svf s (S.matWord (l ++ l')))) := by
        field_simp
    _ ≤ C⁻¹ * C⁻¹ * (Real.exp (-(((l.length + l'.length : ℕ) : ℝ) * S.pressure s)) *
          (svf s (S.matWord l) * svf s (S.matWord l'))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsvf (Real.exp_pos _).le)
          (mul_nonneg (inv_pos.2 hC0).le (inv_pos.2 hC0).le)
    _ = C⁻¹ * (Real.exp (-(l.length * S.pressure s)) * svf s (S.matWord l)) *
          (C⁻¹ * (Real.exp (-(l'.length * S.pressure s)) * svf s (S.matWord l'))) := by
        rw [hexp]
        ring
    _ ≤ μ.real (cylinder l.get) * μ.real (cylinder l'.get) :=
        mul_le_mul h2 h3 (mul_nonneg (inv_pos.2 hC0).le
          (mul_nonneg (Real.exp_pos _).le (svf_nonneg _ _))) measureReal_nonneg

/-- The failure of the lower quasi-Bernoulli bound, tex lines 507 to 507: for a proximal box-like
tuple with rotations and `0 < s < 2` there are a diagonal block `D = A_𝐮` and an anti-diagonal
generator `R = A_j` such that a measure with the Gibbs bounds of `thm:irred_eq_state` satisfies
`μ[𝐮^n] μ[j 𝐮^n] ≥ c q^n μ[𝐮^n j 𝐮^n]` for all `n`, with `q > 1`. The word `𝐮^n` is
`(List.replicate n u).flatten`, and the word of a list `l` is `l.get`. -/
theorem HasGibbsBounds.exists_mul_measureReal_cylinder_le (hrot : S.WithRotations)
    (hprox : S.Proximal) (hs0 : 0 < s) (hs2 : s < 2) (h : S.HasGibbsBounds s μ) :
    ∃ (u : List ι) (j : ι) (c q : ℝ), u ≠ [] ∧ S.oWord u = 0 ∧ S.o j = 1 ∧ 0 < c ∧ 1 < q ∧
      ∀ n : ℕ, 0 < n → c * q ^ n * μ.real (cylinder (Fin.append
          (List.replicate n u).flatten.get (j :: (List.replicate n u).flatten).get)) ≤
        μ.real (cylinder (List.replicate n u).flatten.get) *
          μ.real (cylinder (j :: (List.replicate n u).flatten).get) := by
  obtain ⟨K, h⟩ := (hasGibbsBounds_iff S).1 h
  obtain ⟨u, j, c, q, hu0, ho, hj, hc, hq, hsvf⟩ := S.exists_mul_svf_le hrot hprox hs0 hs2
  have hK0 : 0 < K := one_pos.trans_le h.1
  refine ⟨u, j, c / K ^ 3, q, hu0, ho, hj, div_pos hc (pow_pos hK0 3), hq, fun n hn => ?_⟩
  have hne : (List.replicate n u).flatten ≠ [] := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [List.replicate_succ, List.flatten_cons]
    exact List.append_ne_nil_of_left_ne_nil hu0 _
  have key := h.mul_measureReal_cylinder_append_le hne (List.cons_ne_nil j _)
    (mul_nonneg hc.le (pow_nonneg (zero_le_one.trans hq.le) n)) (hsvf n)
  rwa [mul_div_right_comm] at key

/-- The equilibrium state is not quasi-Bernoulli, tex lines 507 to 507: for a proximal box-like
tuple with rotations and `0 < s < 2`, a measure with the Gibbs bounds of `thm:irred_eq_state` is
not quasi-Bernoulli. -/
theorem not_quasiBernoulli (hrot : S.WithRotations) (hprox : S.Proximal) (hs0 : 0 < s)
    (hs2 : s < 2) (h : S.HasGibbsBounds s μ) : ¬ IsQuasiBernoulli μ := by
  rintro ⟨C, hC, hqb⟩
  obtain ⟨u, j, c, q, hu0, -, -, hc, hq, hfail⟩ :=
    h.exists_mul_measureReal_cylinder_le hrot hprox hs0 hs2
  obtain ⟨K, h⟩ := (hasGibbsBounds_iff S).1 h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / c) hq
  have hC0 : 0 < C := one_pos.trans_le hC
  have hlen : 0 < (List.replicate (n + 1) u).flatten.length := by
    rw [List.replicate_succ, List.flatten_cons, List.length_append]
    exact Nat.add_pos_left (List.length_pos_of_ne_nil hu0) _
  have hlen' : 0 < (j :: (List.replicate (n + 1) u).flatten).length := Nat.succ_pos _
  have hpos := h.measureReal_cylinder_pos (Nat.add_pos_left hlen _)
    (Fin.append (List.replicate (n + 1) u).flatten.get
      (j :: (List.replicate (n + 1) u).flatten).get)
  have h1 := hfail (n + 1) n.succ_pos
  have h2 := (hqb _ _ hlen hlen' (List.replicate (n + 1) u).flatten.get
    (j :: (List.replicate (n + 1) u).flatten).get).1
  rw [inv_mul_le_iff₀ hC0] at h2
  have h3 : c * q ^ (n + 1) ≤ C := le_of_mul_le_mul_right (h1.trans h2) hpos
  have h4 : q ^ n ≤ q ^ (n + 1) := pow_le_pow_right₀ hq.le n.le_succ
  rw [div_lt_iff₀ hc] at hn
  nlinarith

/-- The equilibrium state is not a Bernoulli measure, tex lines 507 to 507 and 2362 to 2368, in
the strong form that the measures of the cylinders are not the products of the measures of their
symbols. -/
theorem not_forall_measureReal_cylinder_eq_prod (hrot : S.WithRotations) (hprox : S.Proximal)
    (hs0 : 0 < s) (hs2 : s < 2) (h : S.HasGibbsBounds s μ) :
    ¬ ∀ n : ℕ, 0 < n → ∀ w : Fin n → ι,
      μ.real (cylinder w) = ∏ k, μ.real (cylinder ![w k]) := fun hprod =>
  not_quasiBernoulli hrot hprox hs0 hs2 h
    (isQuasiBernoulli_of_measureReal_cylinder_eq_prod hprod)

/-- The equilibrium state is not a Bernoulli measure, tex lines 507 to 507 and 2362 to 2368: for
a proximal box-like tuple with rotations and `0 < s < 2`, a measure with the Gibbs bounds of
`thm:irred_eq_state` is not Bernoulli. -/
theorem not_isBernoulli (hrot : S.WithRotations) (hprox : S.Proximal) (hs0 : 0 < s)
    (hs2 : s < 2) (h : S.HasGibbsBounds s μ) : ¬ IsBernoulli μ := fun hB =>
  not_quasiBernoulli hrot hprox hs0 hs2 h hB.isQuasiBernoulli

/-! ### The equilibrium state -/

/-- Tex lines 2244 to 2250: for an irreducible tuple and `0 < s < 2` every invariant
`s`-equilibrium state is sub-multiplicative. Proved from the Gibbs bounds of Feng–Käenmäki,
`FengKaenmakiGibbs`, which `fengKaenmakiGibbs_holds` proves. -/
theorem IsEquilibriumState.submultiplicative (hfk : FengKaenmakiGibbs.{u})
    [MeasurableSingletonClass ι] (hirr : S.Irreducible) (hs0 : 0 < s) (hs2 : s < 2)
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) : IsSubmultiplicative μ :=
  (hfk S hirr hs0 hs2 μ hinv heq).submultiplicative hs0.le

/-- Tex lines 2250 to 2256: for an irreducible tuple with `0 < dimaff(𝖠) < 2` every invariant
equilibrium state `μ` at `s = dimaff(𝖠)` satisfies `C⁻¹ φ^s(A_𝐢) ≤ μ[𝐢] ≤ C φ^s(A_𝐢)` for all
`𝐢 ∈ Σ_*^+`. Proved from the Gibbs bounds of Feng–Käenmäki, `FengKaenmakiGibbs`, which
`fengKaenmakiGibbs_holds` proves. -/
theorem IsEquilibriumState.cylinder_bounds_dimaff (hfk : FengKaenmakiGibbs.{u}) [Nonempty ι]
    [MeasurableSingletonClass ι] (hirr : S.Irreducible) (hs0 : 0 < S.dimaff)
    (hs2 : S.dimaff < 2) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ w : Fin n → ι,
      C⁻¹ * svf S.dimaff (S.matWord (List.ofFn w)) ≤ μ.real (cylinder w) ∧
        μ.real (cylinder w) ≤ C * svf S.dimaff (S.matWord (List.ofFn w)) :=
  (hfk S hirr hs0 hs2 μ hinv heq).cylinder_bounds_dimaff

/-- Tex lines 520 to 524: the `s`-equilibrium state of a proximal box-like tuple with rotations
is not quasi-Bernoulli for `0 < s < 2`. Proved from the Gibbs bounds of `thm:irred_eq_state`
for tuples with rotations, `EquilibriumGibbsStatement`. -/
theorem IsEquilibriumState.not_quasiBernoulli (hfk : EquilibriumGibbsStatement.{u})
    [MeasurableSingletonClass ι] (hrot : S.WithRotations) (hprox : S.Proximal) (hs0 : 0 < s)
    (hs2 : s < 2) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) : ¬ IsQuasiBernoulli μ :=
  System.not_quasiBernoulli hrot hprox hs0 hs2 (hfk S hrot hs0 hs2 μ hinv heq)

/-- Tex lines 524 to 525 and 2362 to 2368: the `s`-equilibrium state of a proximal box-like tuple
with rotations is not a Bernoulli measure for `0 < s < 2`. Proved from the Gibbs bounds of
`thm:irred_eq_state` for tuples with rotations, `EquilibriumGibbsStatement`; the second iterates
of `thm:two-block-normalisation` are not needed. -/
theorem IsEquilibriumState.not_isBernoulli (hfk : EquilibriumGibbsStatement.{u})
    [MeasurableSingletonClass ι] (hrot : S.WithRotations) (hprox : S.Proximal) (hs0 : 0 < s)
    (hs2 : s < 2) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) : ¬ IsBernoulli μ :=
  System.not_isBernoulli hrot hprox hs0 hs2 (hfk S hrot hs0 hs2 μ hinv heq)

end GibbsBounds

end System

/-! ### Gibbs measures on `Σ_Z` are doubling -/

/-- Every symbol occurs at time `0` in `Σ_Z`. Hence the supremum norm over `Σ_Z` of a potential
`f(𝐣) = φ(j_0)` is the maximum of `|φ|` over the alphabet. -/
theorem exists_mem_subshift_zero_eq {ι : Type*} (o : ι → ZMod 2) (p : ι × ZMod 2) :
    ∃ y ∈ subshift o, y 0 = p := by
  obtain ⟨i, c⟩ := p
  rcases zmod_two_cases c with rfl | rfl
  · exact ⟨tau o fun _ => i, tau_mem_subshift _, tau_zero _⟩
  · exact ⟨omega o fun _ => i, omega_mem_subshift _, omega_zero _⟩

section Gibbs

variable {ι : Type u} [MeasurableSpace ι] {o : ι → ZMod 2} {φ φ' : ι × ZMod 2 → ℝ}
  {ν : Measure (ℤ → ι × ZMod 2)} {P C P' C' : ℝ} {y : ℤ → ι × ZMod 2}

/-- The Gibbs property of `sec:gibbs_measures` with the constants `P = P_Z(φ)` and `C` made
explicit. -/
def IsGibbsWith (o : ι → ZMod 2) (φ : ι × ZMod 2 → ℝ) (ν : Measure (ℤ → ι × ZMod 2))
    (P C : ℝ) : Prop :=
  0 < C ∧ ∀ y ∈ subshift o, ∀ n : ℕ, 0 < n →
    C⁻¹ * Real.exp (-(n * P) + ∑ k ∈ Finset.range n, φ (y k)) ≤
        ν.real (cylinder fun k : Fin n => y k) ∧
      ν.real (cylinder fun k : Fin n => y k) ≤
        C * Real.exp (-(n * P) + ∑ k ∈ Finset.range n, φ (y k))

/-- `IsGibbs` asks for some constants. -/
theorem isGibbs_iff : IsGibbs o φ ν ↔ ∃ P C, IsGibbsWith o φ ν P C := Iff.rfl

/-- The constant of a Gibbs measure is at least `1`. -/
theorem IsGibbsWith.one_le (h : IsGibbsWith o φ ν P C) (hy : y ∈ subshift o) : 1 ≤ C := by
  obtain ⟨hC, hb⟩ := h
  have h1 : C⁻¹ ≤ C :=
    le_of_mul_le_mul_right ((hb y hy 1 one_pos).1.trans (hb y hy 1 one_pos).2) (Real.exp_pos _)
  by_contra hlt
  have h2 : 1 < C⁻¹ := (one_lt_inv₀ hC).2 (not_le.1 hlt)
  linarith

/-- The sharp form of the display of tex lines 2375 to 2377:
`ν[𝐢|_n] ≤ C² exp(P - f(σ^n 𝐢)) ν[𝐢|_{n+1}]` for `𝐢 ∈ Σ_Z` and `n ≥ 1`. -/
theorem IsGibbsWith.measureReal_cylinder_le_succ (h : IsGibbsWith o φ ν P C)
    (hy : y ∈ subshift o) {n : ℕ} (hn : 0 < n) :
    ν.real (cylinder fun k : Fin n => y k) ≤
      C ^ 2 * Real.exp (P - φ (y n)) * ν.real (cylinder fun k : Fin (n + 1) => y k) := by
  obtain ⟨hC, hb⟩ := h
  have h1 := (hb y hy n hn).2
  have h2 := (hb y hy (n + 1) n.succ_pos).1
  rw [inv_mul_le_iff₀ hC] at h2
  have hexp : Real.exp (-(n * P) + ∑ k ∈ Finset.range n, φ (y k)) =
      Real.exp (P - φ (y n)) *
        Real.exp (-(((n + 1 : ℕ) : ℝ) * P) + ∑ k ∈ Finset.range (n + 1), φ (y k)) := by
    rw [← Real.exp_add, Finset.sum_range_succ]
    congr 1
    push_cast
    ring
  calc ν.real (cylinder fun k : Fin n => y k)
      ≤ C * (Real.exp (P - φ (y n)) *
          Real.exp (-(((n + 1 : ℕ) : ℝ) * P) + ∑ k ∈ Finset.range (n + 1), φ (y k))) := by
        rw [← hexp]
        exact h1
    _ ≤ C * (Real.exp (P - φ (y n)) * (C * ν.real (cylinder fun k : Fin (n + 1) => y k))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le) hC.le
    _ = C ^ 2 * Real.exp (P - φ (y n)) * ν.real (cylinder fun k : Fin (n + 1) => y k) := by
        ring

/-- The companion of `IsGibbsWith.measureReal_cylinder_le_succ` for an extension to the left, for
an invariant Gibbs measure: `ν[i_1 ⋯ i_n] ≤ C² exp(P - f(𝐢)) ν[i_0 i_1 ⋯ i_n]` for `𝐢 ∈ Σ_Z` and
`n ≥ 1`, where `[i_1 ⋯ i_n] = σ^{-1}[(σ𝐢)|_n]`. The balls of the two-sided shift are cylinders
`[i_{-m} ⋯ i_n]`, so the doubling property of tex lines 2378 to 2381 uses both inequalities. -/
theorem IsGibbsWith.measureReal_preimage_shift_cylinder_le [MeasurableSingletonClass ι]
    (h : IsGibbsWith o φ ν P C) (hinv : MeasurePreserving (shift 1) ν ν) (hy : y ∈ subshift o)
    {n : ℕ} (hn : 0 < n) :
    ν.real (shift 1 ⁻¹' cylinder fun k : Fin n => shift 1 y k) ≤
      C ^ 2 * Real.exp (P - φ (y 0)) * ν.real (cylinder fun k : Fin (n + 1) => y k) := by
  obtain ⟨hC, hb⟩ := h
  have h1 := (hb (shift 1 y) (shift_mem_subshift o hy 1) n hn).2
  have h2 := (hb y hy (n + 1) n.succ_pos).1
  rw [inv_mul_le_iff₀ hC] at h2
  have hsum : ∑ k ∈ Finset.range (n + 1), φ (y k) =
      φ (y 0) + ∑ k ∈ Finset.range n, φ (shift 1 y k) := by
    rw [Finset.sum_range_succ', add_comm, Nat.cast_zero]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [shift_apply, Nat.cast_succ, add_comm]
  have hexp : Real.exp (-(n * P) + ∑ k ∈ Finset.range n, φ (shift 1 y k)) =
      Real.exp (P - φ (y 0)) *
        Real.exp (-(((n + 1 : ℕ) : ℝ) * P) + ∑ k ∈ Finset.range (n + 1), φ (y k)) := by
    rw [← Real.exp_add, hsum]
    congr 1
    push_cast
    ring
  rw [hinv.measureReal_preimage (measurableSet_cylinder _).nullMeasurableSet]
  calc ν.real (cylinder fun k : Fin n => shift 1 y k)
      ≤ C * (Real.exp (P - φ (y 0)) *
          Real.exp (-(((n + 1 : ℕ) : ℝ) * P) + ∑ k ∈ Finset.range (n + 1), φ (y k))) := by
        rw [← hexp]
        exact h1
    _ ≤ C * (Real.exp (P - φ (y 0)) * (C * ν.real (cylinder fun k : Fin (n + 1) => y k))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le) hC.le
    _ = C ^ 2 * Real.exp (P - φ (y 0)) * ν.real (cylinder fun k : Fin (n + 1) => y k) := by
        ring

/-- A Gibbs measure is doubling, tex lines 2374 to 2381:
`ν[𝐢|_n] ≤ C² exp(P_Z(f) + ‖f‖_∞) ν[𝐢|_{n+1}]` for all `𝐢 ∈ Σ_Z` and `n ∈ ℕ`. The norm `‖φ‖` of
the one-symbol potential is the supremum norm `max_p |φ(p)|` over the alphabet, which is
`‖f‖_∞` by `exists_mem_subshift_zero_eq`. The article's constant is an upper bound for the sharp
constant `C² exp(P - f(σ^n 𝐢))` of `IsGibbsWith.measureReal_cylinder_le_succ`. The case `n = 0`
uses that `ν` is a probability measure. -/
theorem IsGibbsWith.doubling [Fintype ι] [IsProbabilityMeasure ν] (h : IsGibbsWith o φ ν P C)
    (hy : y ∈ subshift o) (n : ℕ) :
    ν.real (cylinder fun k : Fin n => y k) ≤
      C ^ 2 * Real.exp (P + ‖φ‖) * ν.real (cylinder fun k : Fin (n + 1) => y k) := by
  have hφ : ∀ p, -φ p ≤ ‖φ‖ := fun p =>
    (neg_le_abs _).trans (Real.norm_eq_abs (φ p) ▸ norm_le_pi_norm φ p)
  have hexp : ∀ k : ℤ, Real.exp (P - φ (y k)) ≤ Real.exp (P + ‖φ‖) := fun k =>
    Real.exp_le_exp.2 (by linarith [hφ (y k)])
  have hC1 := h.one_le hy
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 := (h.2 y hy 1 one_pos).1
    rw [inv_mul_le_iff₀ h.1] at h1
    have h2 : Real.exp (P - φ (y 0)) *
        Real.exp (-(((1 : ℕ) : ℝ) * P) + ∑ k ∈ Finset.range 1, φ (y k)) = 1 := by
      rw [← Real.exp_add, ← Real.exp_zero]
      congr 1
      simp
    calc ν.real (cylinder fun k : Fin 0 => y k) ≤ 1 := measureReal_le_one
      _ = Real.exp (P - φ (y 0)) *
          Real.exp (-(((1 : ℕ) : ℝ) * P) + ∑ k ∈ Finset.range 1, φ (y k)) := h2.symm
      _ ≤ Real.exp (P + ‖φ‖) * (C * ν.real (cylinder fun k : Fin (0 + 1) => y k)) :=
          mul_le_mul (hexp 0) h1 (Real.exp_pos _).le (Real.exp_pos _).le
      _ ≤ C ^ 2 * Real.exp (P + ‖φ‖) * ν.real (cylinder fun k : Fin (0 + 1) => y k) := by
          have hnn : 0 ≤ Real.exp (P + ‖φ‖) * ν.real (cylinder fun k : Fin (0 + 1) => y k) :=
            mul_nonneg (Real.exp_pos _).le measureReal_nonneg
          nlinarith [mul_le_mul_of_nonneg_right hC1 (zero_le_one.trans hC1)]
  · refine (h.measureReal_cylinder_le_succ hy hn).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hexp n) (sq_nonneg C)) measureReal_nonneg

/-- A Gibbs measure is doubling, tex lines 2374 to 2381, for the constants `P` and `C` of the
Gibbs property. -/
theorem IsGibbs.doubling [Fintype ι] [IsProbabilityMeasure ν] (h : IsGibbs o φ ν) :
    ∃ P C : ℝ, IsGibbsWith o φ ν P C ∧ ∀ y ∈ subshift o, ∀ n : ℕ,
      ν.real (cylinder fun k : Fin n => y k) ≤
        C ^ 2 * Real.exp (P + ‖φ‖) * ν.real (cylinder fun k : Fin (n + 1) => y k) := by
  obtain ⟨P, C, h⟩ := isGibbs_iff.1 h
  exact ⟨P, C, h, fun y hy n => h.doubling hy n⟩

/-- If `ν` has the Gibbs property for `φ` with constants `P`, `C` and for `φ'` with constants `P'`,
`C'`, then `(-nP + S_n φ(𝐣)) - (-nP' + S_n φ'(𝐣)) ≤ log(C C')` for all `𝐣 ∈ Σ_Z` and `n ≥ 1`. -/
theorem IsGibbsWith.sub_le_log (h : IsGibbsWith o φ ν P C) (h' : IsGibbsWith o φ' ν P' C')
    (hy : y ∈ subshift o) {n : ℕ} (hn : 0 < n) :
    (-(n * P) + ∑ k ∈ Finset.range n, φ (y k)) - (-(n * P') + ∑ k ∈ Finset.range n, φ' (y k)) ≤
      Real.log (C * C') := by
  have h1 := (h.2 y hy n hn).1.trans (h'.2 y hy n hn).2
  rw [inv_mul_le_iff₀ h.1, ← mul_assoc] at h1
  rw [Real.le_log_iff_exp_le (mul_pos h.1 h'.1), Real.exp_sub, div_le_iff₀ (Real.exp_pos _)]
  exact h1

end Gibbs

/-! ### The cylinders of `τ(Σ)` -/

section TauCylinder

variable {ι : Type u} {o : ι → ZMod 2}

/-- `eq:tau_cylinder`: `[τ(𝐢)|_n] = τ([𝐢|_n])` as subsets of `Σ_Z`, for `n ≥ 1`. -/
theorem cylinder_tau_inter_subshift (o : ι → ZMod 2) (x : ℤ → ι) {n : ℕ} (hn : 0 < n) :
    cylinder (fun k : Fin n => tau o x k) ∩ subshift o =
      tau o '' cylinder fun k : Fin n => x k := by
  ext y
  constructor
  · rintro ⟨hy, hys⟩
    have h0 : y 0 = tau o x 0 := by simpa using hy ⟨0, hn⟩
    obtain ⟨x', rfl⟩ : y ∈ range (tau o) := by
      rw [range_tau]
      exact ⟨hys, by rw [h0, tau_zero]⟩
    exact ⟨x', fun k => congrArg Prod.fst (hy k), rfl⟩
  · rintro ⟨x', hx', rfl⟩
    refine ⟨fun k => ?_, tau_mem_subshift x'⟩
    have hk : ∀ j : Fin n, x' j = x j := hx'
    change tau o x' k = tau o x k
    rw [tau_apply, tau_apply, hk k, eps_natCast, eps_natCast]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    exact congrArg o (hk ⟨j, (Finset.mem_range.1 hj).trans k.2⟩)

variable [MeasurableSpace ι] [MeasurableSingletonClass ι] {ν : Measure (ℤ → ι × ZMod 2)}

/-- Tex line 2604: `\overline{τ}_*ν([𝐢|_n]) = ν([τ(𝐢)|_n])` for a measure `ν` carried by `Σ_Z`,
`𝐢 ∈ Σ` and `n ≥ 1`, by `eq:tau_cylinder`. -/
theorem map_unCode_restrict_range_tau_cylinder (hν : ν (subshift o)ᶜ = 0) (x : ℤ → ι) {n : ℕ}
    (hn : 0 < n) :
    (ν.restrict (range (tau o))).map unCode (cylinder fun k : Fin n => x k) =
      ν (cylinder fun k : Fin n => tau o x k) := by
  have hm : MeasurableSet (cylinder fun k : Fin n => x k) := measurableSet_cylinder _
  rw [Measure.map_apply measurable_unCode hm, Measure.restrict_apply (measurable_unCode hm),
    inter_comm, ← tau_image_eq, ← cylinder_tau_inter_subshift o x hn, measure_inter_conull hν]

/-- Tex lines 2604 to 2605: `\overline{τ}_*ν([𝐢|_n]) = ν([τ(𝐢)|_n]) > 0` for a Gibbs measure `ν`
carried by `Σ_Z`, `𝐢 ∈ Σ` and `n ≥ 1`. -/
theorem IsGibbs.map_unCode_restrict_range_tau_cylinder_pos {φ : ι × ZMod 2 → ℝ}
    (h : IsGibbs o φ ν) (hν : ν (subshift o)ᶜ = 0) (x : ℤ → ι) {n : ℕ} (hn : 0 < n) :
    0 < (ν.restrict (range (tau o))).map unCode (cylinder fun k : Fin n => x k) := by
  rw [map_unCode_restrict_range_tau_cylinder hν x hn]
  have hpos := h.measureReal_cylinder_pos (tau_mem_subshift x) hn
  rw [measureReal_def] at hpos
  exact (ENNReal.toReal_pos_iff.1 hpos).1

end TauCylinder

/-! ### Distinct ergodic measures are mutually singular -/

/-- Distinct ergodic invariant probability measures are mutually singular. The absolutely
continuous part of `μ` with respect to `ν` is invariant, hence a multiple `c • ν` of `ν`. If
`c = 0`, then `μ` is its singular part. If `c ≠ 0`, then `ν ≪ μ`, and an invariant probability
measure which is absolutely continuous with respect to an ergodic one equals it. -/
theorem mutuallySingular_of_ergodic_of_ne {X : Type*} [MeasurableSpace X] {T : X → X}
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμ : Ergodic T μ)
    (hν : Ergodic T ν) (hne : μ ≠ ν) : μ ⟂ₘ ν := by
  obtain ⟨c, hc⟩ := hν.eq_smul_of_absolutelyContinuous
    (hμ.toMeasurePreserving.withDensity_rnDeriv hν.toMeasurePreserving)
    (withDensity_absolutelyContinuous ν (μ.rnDeriv ν))
  have hdec : μ = μ.singularPart ν + c • ν := hc ▸ μ.haveLebesgueDecomposition_add ν
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [zero_smul, add_zero] at hdec
    rw [hdec]
    exact Measure.mutuallySingular_singularPart μ ν
  · have hνμ : ν ≪ μ := by
      refine Measure.AbsolutelyContinuous.mk fun A _ hA => ?_
      have h := congrArg (fun m : Measure X => m A) hdec
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, hA] at h
      have h0 : c * ν A = 0 := (add_eq_zero.1 h.symm).2
      exact (mul_eq_zero.1 h0).resolve_left hc0
    exact absurd (hμ.eq_of_absolutelyContinuous hν.toMeasurePreserving hνμ).symm hne

namespace System

/-! ### The two Gibbs measures are distinct -/

section Potentials

variable {ι : Type u} (S : System ι) {s : ℝ}

/-- `f_{1,s}(τ(𝐢)) = f_{2,s}(ω(𝐢))`, tex lines 2450 to 2451. The identity
`f_{2,s}(τ(𝐢)) = f_{1,s}(ω(𝐢))` is `System.potential₂_tau`. -/
theorem potential₁_tau (s : ℝ) (x : ℤ → ι) (k : ℤ) :
    S.potential₁ s (tau S.o x k) = S.potential₂ s (omega S.o x k) := by
  simp only [potential₂, omega_apply, tau_apply, add_assoc,
    show (1 : ZMod 2) + 1 = 0 from by decide, add_zero]

/-- `f_{1,s} - f_{2,s} = c_s (log |g'_{j_0}| - log |g'_{j_0 ± N}|)`, the direct calculation of
tex lines 2465 to 2470 for a single symbol. -/
theorem potential₁_sub_potential₂ (s : ℝ) (p : ι × ZMod 2) :
    S.potential₁ s p - S.potential₂ s p =
      gapExp s * (Real.log |S.ratio p| - Real.log |S.ratio (p.1, p.2 + 1)|) := by
  have h2 : p.2 + 1 + 1 = p.2 := by
    rw [add_assoc, show (1 : ZMod 2) + 1 = 0 from by decide, add_zero]
  unfold potential₂ potential₁ gapExp
  simp only [h2]
  split_ifs <;> ring

/-- Tex lines 2584 to 2589: along the constant sequence `𝐣 = ⋯ i i i ⋯` of `Σ_Z`,
`S_n f_{1,s}(𝐣) - S_n f_{2,s}(𝐣) = c_s n (log |a_i| - log |b_i|)`. -/
theorem sum_potential₁_sub_sum_potential₂_const (s : ℝ) {y : ℤ → ι × ZMod 2} {i : ι}
    (hy : ∀ k : ℕ, y k = (i, 0)) (n : ℕ) :
    ∑ k ∈ Finset.range n, S.potential₁ s (y k) - ∑ k ∈ Finset.range n, S.potential₂ s (y k) =
      gapExp s * n * (Real.log |S.a i| - Real.log |S.b i|) := by
  have h := S.potential₁_sub_potential₂ s (i, 0)
  simp only [zero_add, ratio_zero, ratio_one] at h
  simp only [hy]
  rw [← Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, h]
  ring

variable [MeasurableSpace ι]

/-- Tex lines 2582 to 2593: for a tuple with a proximal diagonal generator `A_{i_0}` and
`0 < s < 2`, no measure has the Gibbs property for both `f_{1,s}` and `f_{2,s}`. Along the two
fixed points `(i_0, 0)^∞` and `(i_0, 1)^∞` of `Σ_Z` the differences
`S_n f_{1,s} - S_n f_{2,s} = ± c_s n (log |a_{i_0}| - log |b_{i_0}|)` have opposite signs, and the
Gibbs bounds bound `-n(P_1 - P_2) ± c_s n (log |a_{i_0}| - log |b_{i_0}|)` for both signs. -/
theorem not_isGibbs_potential₁_and_potential₂ (hprox : S.HasProximalDiagonal) (hs0 : 0 < s)
    (hs2 : s < 2) {ν : Measure (ℤ → ι × ZMod 2)} (h₁ : IsGibbs S.o (S.potential₁ s) ν)
    (h₂ : IsGibbs S.o (S.potential₂ s) ν) : False := by
  obtain ⟨i, hi, hne⟩ := hprox
  obtain ⟨P₁, C₁, h₁⟩ := isGibbs_iff.1 h₁
  obtain ⟨P₂, C₂, h₂⟩ := isGibbs_iff.1 h₂
  have hy : ∀ c : ZMod 2, (fun _ : ℤ => ((i, c) : ι × ZMod 2)) ∈ subshift S.o := fun c n => by
    simp [Trans, hi]
  have hlog : Real.log |S.a i| ≠ Real.log |S.b i| := fun h =>
    hne (Real.log_injOn_pos (abs_pos.2 (S.a_ne_zero i)) (abs_pos.2 (S.b_ne_zero i)) h)
  have hΔ : gapExp s * (Real.log |S.a i| - Real.log |S.b i|) ≠ 0 :=
    mul_ne_zero (gapExp_pos hs0 hs2).ne' (sub_ne_zero.2 hlog)
  have e0 := S.potential₁_sub_potential₂ s (i, 0)
  have e1 := S.potential₁_sub_potential₂ s (i, 1)
  simp only [zero_add, show (1 : ZMod 2) + 1 = 0 from by decide, ratio_zero, ratio_one] at e0 e1
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.log (C₁ * C₂) /
    |gapExp s * (Real.log |S.a i| - Real.log |S.b i|)|)
  rw [div_lt_iff₀ (abs_pos.2 hΔ)] at hn
  have a1 := h₁.sub_le_log h₂ (hy 0) n.succ_pos
  have a2 := h₂.sub_le_log h₁ (hy 0) n.succ_pos
  have a3 := h₁.sub_le_log h₂ (hy 1) n.succ_pos
  have a4 := h₂.sub_le_log h₁ (hy 1) n.succ_pos
  rw [mul_comm C₂ C₁] at a2 a4
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at a1 a2 a3 a4
  have hn1 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hcast : ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
  rw [hcast] at a1 a2 a3 a4
  have habs := abs_nonneg (gapExp s * (Real.log |S.a i| - Real.log |S.b i|))
  rcases abs_cases (gapExp s * (Real.log |S.a i| - Real.log |S.b i|)) with ⟨h, -⟩ | ⟨h, -⟩ <;>
    rw [h] at hn habs <;> nlinarith

variable {S} {μ : Measure (ℤ → ι)} {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)}

/-- `μ_1 ≠ μ_2`, tex lines 2463 to 2474, for a tuple with a proximal diagonal generator and
`0 < s < 2`. The proof does not use the identity `P_Z(f_{1,s}) = P_Z(f_{2,s})`. -/
theorem GibbsDecomposition.ne (hprox : S.HasProximalDiagonal) (hs0 : 0 < s) (hs2 : s < 2)
    (hdec : S.GibbsDecomposition s μ μ₁ μ₂) : μ₁ ≠ μ₂ := by
  rintro rfl
  exact S.not_isGibbs_potential₁_and_potential₂ hprox hs0 hs2 hdec.gibbs₁ hdec.gibbs₂

/-- The `s`-Gibbs measures `μ_1` and `μ_2` are mutually singular, tex lines 2474 to 2475: they
are distinct ergodic measures. -/
theorem GibbsDecomposition.mutuallySingular (hprox : S.HasProximalDiagonal) (hs0 : 0 < s)
    (hs2 : s < 2) (hdec : S.GibbsDecomposition s μ μ₁ μ₂) : μ₁ ⟂ₘ μ₂ := by
  have := hdec.prob₁
  have := hdec.prob₂
  exact mutuallySingular_of_ergodic_of_ne hdec.ergodic₁ hdec.ergodic₂ (hdec.ne hprox hs0 hs2)

/-! ### The four restrictions of the Gibbs measures -/

/-- Tex lines 2606 to 2607: `\overline{τ}_*μ_1 = \overline{ω}_*μ_2` and
`\overline{τ}_*μ_2 = \overline{ω}_*μ_1`, by cancelling a finite measure in the decompositions of
`thm:eq_state_is_sum`. -/
theorem GibbsDecomposition.map_tau_eq_map_omega (hdec : S.GibbsDecomposition s μ μ₁ μ₂) :
    (μ₁.restrict (range (tau S.o))).map unCode =
        (μ₂.restrict (range (omega S.o))).map unCode ∧
      (μ₂.restrict (range (tau S.o))).map unCode =
        (μ₁.restrict (range (omega S.o))).map unCode := by
  have := hdec.prob₁
  have := hdec.prob₂
  constructor
  · have h := hdec.eq_tau.symm.trans hdec.eq₂
    rwa [add_comm, Measure.add_right_inj] at h
  · have h := hdec.eq_tau.symm.trans hdec.eq₁
    rwa [Measure.add_right_inj] at h

/-- Tex lines 2604 to 2605: `\overline{τ}_*μ_k([𝐢|_n]) = μ_k([τ(𝐢)|_n]) > 0` for all `𝐢 ∈ Σ`,
`n ≥ 1` and both `k`. -/
theorem GibbsDecomposition.map_tau_cylinder [MeasurableSingletonClass ι]
    (hdec : S.GibbsDecomposition s μ μ₁ μ₂) (x : ℤ → ι) {n : ℕ} (hn : 0 < n) :
    ((μ₁.restrict (range (tau S.o))).map unCode (cylinder fun k : Fin n => x k) =
        μ₁ (cylinder fun k : Fin n => tau S.o x k) ∧
      0 < (μ₁.restrict (range (tau S.o))).map unCode (cylinder fun k : Fin n => x k)) ∧
    (μ₂.restrict (range (tau S.o))).map unCode (cylinder fun k : Fin n => x k) =
        μ₂ (cylinder fun k : Fin n => tau S.o x k) ∧
      0 < (μ₂.restrict (range (tau S.o))).map unCode (cylinder fun k : Fin n => x k) :=
  ⟨⟨map_unCode_restrict_range_tau_cylinder hdec.supp₁ x hn,
      hdec.gibbs₁.map_unCode_restrict_range_tau_cylinder_pos hdec.supp₁ x hn⟩,
    map_unCode_restrict_range_tau_cylinder hdec.supp₂ x hn,
    hdec.gibbs₂.map_unCode_restrict_range_tau_cylinder_pos hdec.supp₂ x hn⟩

/-- `\overline{τ}_*μ_k(Σ) > 0` for both `k`, tex lines 2485 to 2486. -/
theorem GibbsDecomposition.map_tau_univ_pos (hdec : S.GibbsDecomposition s μ μ₁ μ₂) :
    0 < (μ₁.restrict (range (tau S.o))).map unCode univ ∧
      0 < (μ₂.restrict (range (tau S.o))).map unCode univ := by
  have := hdec.prob₁
  obtain ⟨y⟩ := nonempty_of_isProbabilityMeasure μ₁
  have : Nonempty ι := ⟨(y 0).1⟩
  simp only [Measure.map_apply measurable_unCode MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply_univ]
  exact ⟨hdec.gibbs₁.measure_range_tau_pos hdec.supp₁,
    hdec.gibbs₂.measure_range_tau_pos hdec.supp₂⟩

/-- `\overline{ω}_*μ_k(Σ) > 0` for both `k`, the counterpart of tex lines 2485 to 2486 for
`ω`. -/
theorem GibbsDecomposition.map_omega_univ_pos (hdec : S.GibbsDecomposition s μ μ₁ μ₂) :
    0 < (μ₁.restrict (range (omega S.o))).map unCode univ ∧
      0 < (μ₂.restrict (range (omega S.o))).map unCode univ := by
  rw [← hdec.map_tau_eq_map_omega.1, ← hdec.map_tau_eq_map_omega.2]
  exact hdec.map_tau_univ_pos.symm

/-- Tex lines 2634 to 2636: `\overline{τ}_*μ_1`, `\overline{τ}_*μ_2`, `\overline{ω}_*μ_1` and
`\overline{ω}_*μ_2` are absolutely continuous with respect to `μ`. -/
theorem GibbsDecomposition.map_absolutelyContinuous (hdec : S.GibbsDecomposition s μ μ₁ μ₂) :
    ((μ₁.restrict (range (tau S.o))).map unCode ≪ μ ∧
        (μ₂.restrict (range (tau S.o))).map unCode ≪ μ) ∧
      (μ₁.restrict (range (omega S.o))).map unCode ≪ μ ∧
        (μ₂.restrict (range (omega S.o))).map unCode ≪ μ := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have h := hdec.eq_tau
    exact h ▸ (Measure.le_add_right le_rfl).absolutelyContinuous
  · have h := hdec.eq_tau
    exact h ▸ (Measure.le_add_left le_rfl).absolutelyContinuous
  · have h := hdec.eq_omega
    exact h ▸ (Measure.le_add_right le_rfl).absolutelyContinuous
  · have h := hdec.eq_omega
    exact h ▸ (Measure.le_add_left le_rfl).absolutelyContinuous

end Potentials

end System

end BoxLike
