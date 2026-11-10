module

/-
The tuple and the pressure of `ex:projection_double_dimensional`, tex lines 2779 to 2785 and
3014 to 3029: the four maps form a proximal irreducible box-like tuple with rotations, the
matrix `M(u) = 2 (a^u, a^u; b^u, b^u)` has the only non-zero eigenvalue `2 a^u + 2 b^u`, the
partition sums `∑_{|𝐢| = n} φ^u(A_𝐢)` are comparable with `(1, 1) M(u)^n (1, 1)ᵀ`, and hence
`P(𝖠, u) = log(2 a^u + 2 b^u)` for `0 ≤ u ≤ 1` and `dimaff = s_1`.

* `PrescribedExample.sys_mat_of_lt`, `PrescribedExample.sys_mat_of_le`: the linear parts
  `diag(a, b)` and the anti-diagonal matrix with entries `a`, `b`.
* `PrescribedExample.withRotations`, `PrescribedExample.isProximalMatrix_mat_of_lt`,
  `PrescribedExample.hasProximalDiagonal`, `PrescribedExample.proximal`,
  `PrescribedExample.mat_mulVec_e1_of_le`, `PrescribedExample.mat_mulVec_e2_of_le`,
  `PrescribedExample.irreducible`: the geometry of the tuple.
* `PrescribedExample.M`, `PrescribedExample.transfer_eq_mulVec`,
  `PrescribedExample.M_mulVec_eigenvector`, `PrescribedExample.charpoly_M`,
  `PrescribedExample.M_pow_succ`: the matrix `M(u)` as the operator `System.transfer`, its
  positive eigenvector, its characteristic polynomial `X (X - (2 a^u + 2 b^u))` and its powers.
* `PrescribedExample.one_dotProduct_M_pow`: `(1, 1) M(u)^n (1, 1)ᵀ = 2 (2 a^u + 2 b^u)^n`.
* `PrescribedExample.svfSum_le_mulVec`: the two-sided partition-sum estimate.
* `PrescribedExample.pressure_eq`: `P(𝖠, u) = log(2 a^u + 2 b^u)` for `0 ≤ u ≤ 1`.
* `PrescribedExample.dimaff_eq_of_rpow`, `PrescribedExample.dimaff_paramsOf`: `dimaff = s` when
  `2 a^s + 2 b^s = 1` with `0 ≤ s ≤ 1`, in particular `dimaff = s_1` for `paramsOf`.
* `PrescribedExample.M_paramsOf`, `PrescribedExample.M_paramsOf_mulVec`:
  `M(s_1) = (p, p; 1 - p, 1 - p)` and `M(s_1) (p, 1 - p)ᵀ = (p, 1 - p)ᵀ`.
-/
public import BoxLike.Example
public import BoxLike.PrescribedExample.Parameters

@[expose] public section

namespace BoxLike

namespace PrescribedExample

open Matrix Filter Topology Polynomial

variable (P : Params) (t : Fin 8 → ℝ)

/-! ### The tuple -/

/-- The orientations of the system of `ex:projection_double_dimensional`. -/
@[simp] theorem sys_o (i : Fin 4) : (sys P t).o i = orient i := rfl

/-- The first-row entry `a` of every linear part in `ex:projection_double_dimensional`. -/
@[simp] theorem sys_a (i : Fin 4) : (sys P t).a i = P.a := rfl

/-- The second-row entry `b` of every linear part in `ex:projection_double_dimensional`. -/
@[simp] theorem sys_b (i : Fin 4) : (sys P t).b i = P.b := rfl

/-- The contraction ratio of the symbol `(i, c)` of the projective system of
`ex:projection_double_dimensional`: `a` for `c = 0` and `b` for `c = 1`. -/
theorem sys_ratio (p : Fin 4 × ZMod 2) :
    (sys P t).ratio p = if p.2 = 0 then P.a else P.b := rfl

/-- The maps `φ_1`, `φ_2` of `ex:projection_double_dimensional` are diagonal. -/
theorem orient_of_lt {i : Fin 4} (hi : (i : ℕ) < 2) : orient i = 0 := by
  simp [orient, hi]

/-- The maps `φ_3`, `φ_4` of `ex:projection_double_dimensional` are anti-diagonal. -/
theorem orient_of_le {i : Fin 4} (hi : 2 ≤ (i : ℕ)) : orient i = 1 := by
  simp [orient, not_lt.2 hi]

/-- `φ_1` is diagonal (`ex:projection_double_dimensional`). -/
@[simp] theorem orient_zero : orient 0 = 0 := by decide

/-- `φ_2` is diagonal (`ex:projection_double_dimensional`). -/
@[simp] theorem orient_one : orient 1 = 0 := by decide

/-- `φ_3` is anti-diagonal (`ex:projection_double_dimensional`). -/
@[simp] theorem orient_two : orient 2 = 1 := by decide

/-- `φ_4` is anti-diagonal (`ex:projection_double_dimensional`). -/
@[simp] theorem orient_three : orient 3 = 1 := by decide

/-- Every map of `ex:projection_double_dimensional` contracts the first coordinate of its image
by `a`. -/
@[simp] theorem abs_sys_ratio_zero (i : Fin 4) : |(sys P t).ratio (i, 0)| = P.a := by
  simp [abs_of_pos P.a_pos]

/-- Every map of `ex:projection_double_dimensional` contracts the second coordinate of its
image by `b`. -/
@[simp] theorem abs_sys_ratio_one (i : Fin 4) : |(sys P t).ratio (i, 1)| = P.b := by
  simp [abs_of_pos P.b_pos]

/-- The diagonal linear parts `A_i = diag(a, b)`, `i ∈ {1, 2}`, of
`ex:projection_double_dimensional`. -/
theorem sys_mat_of_lt {i : Fin 4} (hi : (i : ℕ) < 2) : (sys P t).mat i = boxMat 0 P.a P.b := by
  simp [System.mat, orient_of_lt hi]

/-- The anti-diagonal linear parts `A_i`, `i ∈ {3, 4}`, of `ex:projection_double_dimensional`,
with first-row entry `a` and second-row entry `b`. -/
theorem sys_mat_of_le {i : Fin 4} (hi : 2 ≤ (i : ℕ)) : (sys P t).mat i = boxMat 1 P.a P.b := by
  simp [System.mat, orient_of_le hi]

/-- The tuple of `ex:projection_double_dimensional` is box-like with rotations. -/
theorem withRotations : (sys P t).WithRotations :=
  ⟨⟨0, orient_zero⟩, ⟨2, orient_two⟩⟩

/-- The diagonal generators of `ex:projection_double_dimensional` are proximal, since
`0 < b < a`. -/
theorem isProximalMatrix_mat_of_lt {i : Fin 4} (hi : (i : ℕ) < 2) :
    IsProximalMatrix ((sys P t).mat i) := by
  rw [sys_mat_of_lt P t hi, isProximalMatrix_boxMat_zero, abs_of_pos P.a_pos,
    abs_of_pos P.b_pos]
  exact P.b_lt_a.ne'

/-- The tuple of `ex:projection_double_dimensional` contains a proximal diagonal generator. -/
theorem hasProximalDiagonal : (sys P t).HasProximalDiagonal := by
  refine ⟨0, orient_zero, ?_⟩
  rw [sys_a, sys_b, abs_of_pos P.a_pos, abs_of_pos P.b_pos]
  exact P.b_lt_a.ne'

/-- The tuple of `ex:projection_double_dimensional` is proximal. -/
theorem proximal : (sys P t).Proximal := (hasProximalDiagonal P t).proximal

/-- The anti-diagonal generators of `ex:projection_double_dimensional` send the first axis to
the second. -/
theorem mat_mulVec_e1_of_le {i : Fin 4} (hi : 2 ≤ (i : ℕ)) :
    (sys P t).mat i *ᵥ ![1, 0] = ![0, P.b] := by
  rw [sys_mat_of_le P t hi]
  ext j; fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The anti-diagonal generators of `ex:projection_double_dimensional` send the second axis to
the first. -/
theorem mat_mulVec_e2_of_le {i : Fin 4} (hi : 2 ≤ (i : ℕ)) :
    (sys P t).mat i *ᵥ ![0, 1] = ![P.a, 0] := by
  rw [sys_mat_of_le P t hi]
  ext j; fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The tuple of `ex:projection_double_dimensional` is irreducible: the invariant lines of the
proximal diagonal generators are the axes, which the anti-diagonal generators interchange. -/
theorem irreducible : (sys P t).Irreducible :=
  System.irreducible_of_hasProximalDiagonal (withRotations P t) (hasProximalDiagonal P t)

/-! ### The matrix `M(u)` -/

/-- The matrix `M(u) = 2 (a^u, a^u; b^u, b^u)` of `ex:projection_double_dimensional`, whose
`(i, j)` entry sums the `u`-th powers of the contractions from coordinate `j` to coordinate
`i`. -/
noncomputable def M (u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (2 : ℝ) • !![P.a ^ u, P.a ^ u; P.b ^ u, P.b ^ u]

/-- The eigenvalue `2 a^u + 2 b^u` of `M(u)`. -/
noncomputable def rho (u : ℝ) : ℝ := 2 * P.a ^ u + 2 * P.b ^ u

/-- `2 a^u + 2 b^u > 0`. -/
theorem rho_pos (u : ℝ) : 0 < rho P u := by
  have := Real.rpow_pos_of_pos P.a_pos u
  have := Real.rpow_pos_of_pos P.b_pos u
  unfold rho
  positivity

variable {P} in
/-- The first row of `M(u)` as the operator `System.transfer`: every map contracts the first
coordinate of its image by `a`. -/
theorem transfer_zero (u : ℝ) (v : ZMod 2 → ℝ) :
    (sys P t).transfer u v 0 = 2 * P.a ^ u * (v 0 + v 1) := by
  simp only [System.transfer, Fin.sum_univ_four, abs_sys_ratio_zero, sys_o, orient_zero,
    orient_one, orient_two, orient_three, zero_add]
  ring

variable {P} in
/-- The second row of `M(u)` as the operator `System.transfer`: every map contracts the second
coordinate of its image by `b`. -/
theorem transfer_one (u : ℝ) (v : ZMod 2 → ℝ) :
    (sys P t).transfer u v 1 = 2 * P.b ^ u * (v 0 + v 1) := by
  simp only [System.transfer, Fin.sum_univ_four, abs_sys_ratio_one, sys_o, orient_zero,
    orient_one, orient_two, orient_three, add_zero, show (1 : ZMod 2) + 1 = 0 by decide]
  ring

/-- The operator `System.transfer` of the system of `ex:projection_double_dimensional` is the
matrix `M(u)`. -/
theorem transfer_eq_mulVec (u : ℝ) (v : ZMod 2 → ℝ) :
    ![(sys P t).transfer u v 0, (sys P t).transfer u v 1] = M P u *ᵥ ![v 0, v 1] := by
  ext i
  fin_cases i <;>
    simp [M, transfer_zero, transfer_one, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- The iterates of `System.transfer` are the powers `M(u)^n`. -/
theorem iterate_transfer_eq_mulVec (u : ℝ) (n : ℕ) (v : ZMod 2 → ℝ) :
    ![((sys P t).transfer u)^[n] v 0, ((sys P t).transfer u)^[n] v 1] =
      M P u ^ n *ᵥ ![v 0, v 1] := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, transfer_eq_mulVec, Matrix.mulVec_mulVec, pow_succ]

/-- `M(u) (a^u, b^u)ᵀ = (2 a^u + 2 b^u) (a^u, b^u)ᵀ`: a positive eigenvector of `M(u)`. -/
theorem M_mulVec_eigenvector (u : ℝ) :
    M P u *ᵥ ![P.a ^ u, P.b ^ u] = rho P u • ![P.a ^ u, P.b ^ u] := by
  ext i
  fin_cases i <;> simp [M, rho, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- The characteristic polynomial of `M(u)` is `X (X - (2 a^u + 2 b^u))`: the matrix has rank
one and `2 a^u + 2 b^u` is its only non-zero eigenvalue. -/
theorem charpoly_M (u : ℝ) : (M P u).charpoly = X * (X - C (rho P u)) := by
  rw [Matrix.charpoly_fin_two]
  have htr : (M P u).trace = rho P u := by
    simp [M, rho, Matrix.trace_fin_two]
  have hdet : (M P u).det = 0 := by
    simp [M, Matrix.det_fin_two]
  rw [htr, hdet, C_0]
  ring

/-- `M(u)^{n+1} = (2 a^u + 2 b^u)^n M(u)`, since `M(u)` has rank one. -/
theorem M_pow_succ (u : ℝ) (n : ℕ) : M P u ^ (n + 1) = rho P u ^ n • M P u := by
  have hsq : M P u * M P u = rho P u • M P u := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, rho, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Matrix.smul_mul, hsq, smul_smul, pow_succ]

/-- `(1, 1) M(u)^n (1, 1)ᵀ = 2 (2 a^u + 2 b^u)^n`. -/
theorem one_dotProduct_M_pow (u : ℝ) (n : ℕ) :
    ![1, 1] ⬝ᵥ (M P u ^ n *ᵥ ![1, 1]) = 2 * rho P u ^ n := by
  rcases n with _ | n
  · simp [dotProduct, Fin.sum_univ_two]
    norm_num
  · rw [M_pow_succ, Matrix.smul_mulVec, dotProduct_smul, pow_succ]
    simp [M, rho, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-! ### The pressure -/

/-- The two-sided partition-sum estimate of `ex:projection_double_dimensional`:
`∑_{|𝐢| = n} φ^u(A_𝐢) ≤ (1, 1) M(u)^n (1, 1)ᵀ ≤ 2 ∑_{|𝐢| = n} φ^u(A_𝐢)` for `0 ≤ u ≤ 1`. Each
product `A_𝐢` has two non-zero entries, whose moduli are its singular values. -/
theorem svfSum_le_mulVec {u : ℝ} (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) (n : ℕ) :
    (sys P t).svfSum u n ≤ ![1, 1] ⬝ᵥ (M P u ^ n *ᵥ ![1, 1]) ∧
      ![1, 1] ⬝ᵥ (M P u ^ n *ᵥ ![1, 1]) ≤ 2 * (sys P t).svfSum u n := by
  have h := (sys P t).svfSum_bounds (v := fun _ => 1) hu₀ hu₁ (fun _ => one_pos) n
  have e := iterate_transfer_eq_mulVec P t u n fun _ => 1
  have e' : ![1, 1] ⬝ᵥ (M P u ^ n *ᵥ ![1, 1]) =
      ((sys P t).transfer u)^[n] (fun _ => 1) 0 + ((sys P t).transfer u)^[n] (fun _ => 1) 1 := by
    rw [← e]
    simp [dotProduct, Fin.sum_univ_two]
  rw [e']
  simpa using h

/-- `(2 a^u + 2 b^u)^n ≤ ∑_{|𝐢| = n} φ^u(A_𝐢) ≤ 2 (2 a^u + 2 b^u)^n` for `0 ≤ u ≤ 1`. -/
theorem svfSum_bounds_rho {u : ℝ} (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) (n : ℕ) :
    rho P u ^ n ≤ (sys P t).svfSum u n ∧ (sys P t).svfSum u n ≤ 2 * rho P u ^ n := by
  have h := svfSum_le_mulVec P t hu₀ hu₁ n
  rw [one_dotProduct_M_pow] at h
  constructor <;> linarith [h.1, h.2]

/-- `P(𝖠, u) = log(2 a^u + 2 b^u)` for `0 ≤ u ≤ 1` (`ex:projection_double_dimensional`):
taking logarithms in the two-sided estimate, dividing by `n` and letting `n → ∞`. -/
theorem pressure_eq {u : ℝ} (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) :
    (sys P t).pressure u = Real.log (2 * P.a ^ u + 2 * P.b ^ u) := by
  obtain ⟨δ, hδ⟩ := (sys P t).exists_ratioLowerBound
  have hρ := rho_pos P u
  have hlower : ∀ n : ℕ, 0 < n → Real.log (rho P u) ≤ Real.log ((sys P t).svfSum u n) / n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h := Real.log_le_log (pow_pos hρ n) (svfSum_bounds_rho P t hu₀ hu₁ n).1
    rw [Real.log_pow] at h
    rw [le_div_iff₀ hn']
    linarith
  have hupper : ∀ n : ℕ, 0 < n →
      Real.log ((sys P t).svfSum u n) / n ≤ Real.log (rho P u) + Real.log 2 / n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h := Real.log_le_log (hδ.svfSum_pos hu₀ n) (svfSum_bounds_rho P t hu₀ hu₁ n).2
    rw [Real.log_mul two_ne_zero (pow_pos hρ n).ne', Real.log_pow] at h
    rw [div_le_iff₀ hn', add_mul, div_mul_cancel₀ _ hn'.ne']
    linarith
  have hlim : Tendsto (fun n : ℕ => Real.log (rho P u) + Real.log 2 / n) atTop
      (𝓝 (Real.log (rho P u))) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2))
  exact tendsto_nhds_unique (hδ.tendsto_pressure hu₀)
    (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      ((eventually_gt_atTop 0).mono hlower) ((eventually_gt_atTop 0).mono hupper))

/-- If `2 a^s + 2 b^s = 1` with `0 ≤ s ≤ 1`, then the affinity dimension of the system of
`ex:projection_double_dimensional` is `s`. -/
theorem dimaff_eq_of_rpow {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (h : 2 * P.a ^ s + 2 * P.b ^ s = 1) : (sys P t).dimaff = s := by
  refine (sys P t).dimaff_eq hs₀ ?_
  rw [pressure_eq P t hs₀ hs₁, h, Real.log_one]

/-- `dimaff = s_1` for the parameters `a = (p/2)^{1/s_1}`, `b = ((1-p)/2)^{1/s_1}` of
`ex:projection_double_dimensional`, since `2 a^{s_1} + 2 b^{s_1} = 1`. -/
theorem dimaff_paramsOf {s₁ p : ℝ} (hs₀ : 0 < s₁) (hs₁ : s₁ ≤ 1) (hp₀ : 1 / 2 < p)
    (hp₁ : p < 1) : (sys (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁) t).dimaff = s₁ :=
  dimaff_eq_of_rpow _ t hs₀.le hs₁
    (two_mul_aOf_rpow_add hs₀ (by linarith) hp₁.le)

/-- `M(s_1) = (p, p; 1 - p, 1 - p)` for the parameters of `ex:projection_double_dimensional`,
since `2 a^{s_1} = p` and `2 b^{s_1} = 1 - p`. -/
theorem M_paramsOf {s₁ p : ℝ} (hs₀ : 0 < s₁) (hs₁ : s₁ ≤ 1) (hp₀ : 1 / 2 < p) (hp₁ : p < 1) :
    M (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁) s₁ = !![p, p; 1 - p, 1 - p] := by
  have ha : aOf s₁ p ^ s₁ = p / 2 := aOf_rpow hs₀ (by linarith)
  have hb : bOf s₁ p ^ s₁ = (1 - p) / 2 := bOf_rpow hs₀ hp₁.le
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M, ha, hb] <;> ring

/-- `M(s_1) v = v` for `v = (p, 1 - p)ᵀ` (`ex:projection_double_dimensional`). -/
theorem M_paramsOf_mulVec {s₁ p : ℝ} (hs₀ : 0 < s₁) (hs₁ : s₁ ≤ 1) (hp₀ : 1 / 2 < p)
    (hp₁ : p < 1) : M (paramsOf s₁ p hs₀ hs₁ hp₀ hp₁) s₁ *ᵥ ![p, 1 - p] = ![p, 1 - p] := by
  rw [M_paramsOf]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

end PrescribedExample

end BoxLike
