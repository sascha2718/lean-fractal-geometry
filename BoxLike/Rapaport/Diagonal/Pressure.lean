module

/-
The singular value pressure and the affinity dimension of a diagonal planar system, and the
Käenmäki weights at the affinity dimension: Rapaport's definition (7.1) of the affinity dimension
(arXiv:2309.03985, lines 1939 to 1953 of `rapaport.tex`) and the computation `s = dim_L(Φ, p)`
for the weights `p_i = φ^s(i)` (7.3) in the proof of his Theorem 1.3 (lines 2028 to 2077), for
`d = 2`.

For a system `S` without rotations, `A_i = diag(a_i, b_i)`, the product along a word is
`diag(∏ a, ∏ b)`, and Rapaport's two functions `φ_σ^s`, `σ ∈ S_2`, are the multiplicative
functions `φa` (coordinate `a` first) and `φb` (coordinate `b` first). The singular value
function of a diagonal matrix is the larger of the two, so the `n`-th singular value sum lies
between `max(Φa, Φb)^n` and `Φa^n + Φb^n`, and the pressure is `log max(Φa, Φb)`.

* `φa`, `φb`: Rapaport's `φ_σ^s` (lines 1940 to 1948) at a diagonal matrix `diag(x, y)`, for
  the identity and the transposition `σ`.
* `φa_nonneg`, `φb_nonneg`, `φa_pos`, `φb_pos`, `φa_eq_exp`, `log_φa`, `φa_mul`, `φa_one_one`,
  `φa_list_prod`, `φb_list_prod`, `φa_zero`, `φa_comm_of_two_le`: positivity,
  `φ^s = exp Λ(log |x|, log |y|, s)`, multiplicativity, and the symmetry of `φ^s` for `s = 0`
  and `s ≥ 2`.
* `svf_diag`, `abs_mul_rpow_eq`, `max_rpow_mul_eq`, `svf_boxMat_eq_max`: the singular value
  function of a diagonal or anti-diagonal matrix in the three ranges of `s`, and
  `φ^s(diag(x, y)) = max(φa, φb)` for `s ≥ 0`.
* `matWord_eq_of_diag`, `svf_matWord_diag`, `svfSum_diag`: the products `A_𝐢` of a system
  without rotations and their singular value functions.
* `Φa`, `Φb`, `Φa_pos`, `Φb_pos`, `Φa_zero`, `Φb_zero`, `Φa_eq_Φb_of_two_le`, `Φa_pow`,
  `Φb_pow`: the sums `∑_i φ_σ^s(i)` of (7.1) and their powers.
* `max_pow_le_svfSum`, `svfSum_le_add`: `max(Φa, Φb)^n ≤ ∑_{|𝐢| = n} φ^s(A_𝐢) ≤ Φa^n + Φb^n`.
* `max_Φ_pos`, `pressure_diag`, `exp_pressure_diag`: `P(s) = log max(Φa(s), Φb(s))` for
  `s ≥ 0`.
* `strictAntiOn_max_Φ`, `continuousOn_max_Φ`, `max_Φ_zero`, `tendsto_max_Φ_atTop`: the function
  `s ↦ max(Φa(s), Φb(s))` is continuous and strictly decreasing on `[0, ∞)`, from `#ι` to `0`.
* `dimaff_diag`, `dimaff_eq_of_max_eq_one`, `le_dimaff_iff`, `lt_dimaff_iff`: (7.1), the
  affinity dimension is the unique `s ≥ 0` with `max(Φa(s), Φb(s)) = 1`.
* `swapExp`, `swapExp_pos`, `energy_swap`, `φa_swap`, `sum_mul_energy`, `lyapDim_eq_of_neg`: the
  algebra of the energy `Λ` of `eq:energy_def` behind the computation of lines 2047 to 2077.
* `sum_negMulLog_eq`, `sum_negMulLog_add_energy`, `sum_mul_log_abs_neg`, `lyapDim_weights`: for
  the weights `p_i = φ^s(diag(x_i, y_i))`, normalised or not, `H(p) + Λ(λ_x, λ_y, s) = 0` and
  `dim_L(H(p), λ_x, λ_y) = s` for every `s`.
* `sum_negMulLog_le_of_le_one`, `lt_sum_negMulLog_of_one_lt`, `sum_negMulLog_lt_of_lt_two`,
  `le_sum_negMulLog_of_two_le`: Rapaport's bounds on `H(p)` in terms of `χ_1 = -λ_x` and
  `χ_2 = -λ_y` in the three ranges of `s`.
* `swapExp_mul_le`, `swapExp_mul_lt`, `swapExp_mul_sub_le`, `swapExp_mul_sub_lt`,
  `sum_mul_log_le_of_le`, `sum_mul_log_lt_of_le`, `sum_mul_log_eq_iff`: the concavity step
  (lines 2055 to 2066), `χ_1 ≤ χ_2` when `∑ φ_σ^s ≤ ∑ φ^s` and `0 < s < 2`, strictly unless
  `|x_i| = |y_i|` for every `i`.
* `kwA`, `kwB`, `kwA_pos`, `kwB_pos`, `sum_kwA`, `sum_kwB`, `dimaff_eq_lyapDim_kwA`,
  `dimaff_eq_lyapDim_kwB`, `sum_kwA_mul_log_le`, `sum_kwB_mul_log_le`, `sum_kwA_mul_log_lt`,
  `sum_kwB_mul_log_lt`, `kwA_eq_kwB`: the Käenmäki weights `p_i = φ^s(i)` at `s = dimaff`, for
  either order of the coordinates.
* `kaenmaki_weights`: `dimaff = dim_L(H(p), λ_weak, λ_strong)` for a positive probability vector
  `p` given by `φa` or `φb`, with the two exponents in order.
-/
public import BoxLike.AffinityDim
public import BoxLike.LyapunovDim
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

@[expose] public section

namespace BoxLike.Rapaport.Diagonal

open Filter Topology

/-! ### Rapaport's functions `φ_σ^s` at a diagonal matrix -/

/-- Rapaport's `φ_σ^s` (lines 1940 to 1948 of the source) for `d = 2` and the identity `σ`, at the
diagonal matrix `diag(x, y)`: `|x|^s` for `s ≤ 1`, `|x| |y|^{s-1}` for `1 < s ≤ 2` and
`(|x| |y|)^{s/2}` for `s > 2`. Rapaport's case split at `m = ⌊s⌋` gives the same values for
`s ≥ 0`, the two formulas agreeing at `s = 1` and at `s = 2`. -/
noncomputable def φa (s x y : ℝ) : ℝ :=
  if s ≤ 1 then |x| ^ s else if s ≤ 2 then |x| * |y| ^ (s - 1) else (|x| * |y|) ^ (s / 2)

/-- Rapaport's `φ_σ^s` (lines 1940 to 1948 of the source) for the transposition `σ` of `S_2`: the
function `φa` with the roles of the two coordinates exchanged. -/
noncomputable def φb (s x y : ℝ) : ℝ := φa s y x

theorem φa_nonneg (s x y : ℝ) : 0 ≤ φa s x y := by
  unfold φa
  split_ifs <;> positivity

theorem φb_nonneg (s x y : ℝ) : 0 ≤ φb s x y := φa_nonneg s y x

/-- `φ_σ^s(i) > 0` (line 1940 of the source) when both entries are non-zero. -/
theorem φa_pos {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (s : ℝ) : 0 < φa s x y := by
  have hx' := abs_pos.2 hx
  have hy' := abs_pos.2 hy
  unfold φa
  split_ifs
  · exact Real.rpow_pos_of_pos hx' _
  · exact mul_pos hx' (Real.rpow_pos_of_pos hy' _)
  · exact Real.rpow_pos_of_pos (mul_pos hx' hy') _

theorem φb_pos {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (s : ℝ) : 0 < φb s x y := φa_pos hy hx s

/-- `φ^s(diag(x, y)) = exp Λ(log |x|, log |y|, s)`, with the energy `Λ` of `eq:energy_def`. -/
theorem φa_eq_exp {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (s : ℝ) :
    φa s x y = Real.exp (energy (Real.log |x|) (Real.log |y|) s) := by
  have hx' := abs_pos.2 hx
  have hy' := abs_pos.2 hy
  unfold φa energy
  split_ifs
  · rw [Real.rpow_def_of_pos hx', mul_comm]
  · rw [Real.rpow_def_of_pos hy', Real.exp_add, Real.exp_log hx', mul_comm (s - 1)]
  · rw [Real.rpow_def_of_pos (mul_pos hx' hy'), Real.log_mul hx'.ne' hy'.ne', mul_comm]

/-- `log φ^s(diag(x, y)) = Λ(log |x|, log |y|, s)`. -/
theorem log_φa {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (s : ℝ) :
    Real.log (φa s x y) = energy (Real.log |x|) (Real.log |y|) s := by
  rw [φa_eq_exp hx hy, Real.log_exp]

/-- `φ_σ^s` is multiplicative on diagonal matrices. -/
theorem φa_mul (s x y x' y' : ℝ) : φa s (x * x') (y * y') = φa s x y * φa s x' y' := by
  unfold φa
  simp only [abs_mul]
  split_ifs
  · exact Real.mul_rpow (abs_nonneg _) (abs_nonneg _)
  · rw [Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    ring
  · rw [show |x| * |x'| * (|y| * |y'|) = (|x| * |y|) * (|x'| * |y'|) by ring,
      Real.mul_rpow (by positivity) (by positivity)]

theorem φa_one_one (s : ℝ) : φa s 1 1 = 1 := by
  simp [φa]

/-- `φ_σ^s(diag(∏ x, ∏ y)) = ∏ φ_σ^s(diag(x, y))`: multiplicativity along a word. -/
theorem φa_list_prod {ι : Type*} (s : ℝ) (f g : ι → ℝ) (l : List ι) :
    φa s (l.map f).prod (l.map g).prod = (l.map fun i => φa s (f i) (g i)).prod := by
  induction l with
  | nil => exact φa_one_one s
  | cons i l ih => simp only [List.map_cons, List.prod_cons, φa_mul, ih]

/-- Multiplicativity of `φb` along a word. -/
theorem φb_list_prod {ι : Type*} (s : ℝ) (f g : ι → ℝ) (l : List ι) :
    φb s (l.map f).prod (l.map g).prod = (l.map fun i => φb s (f i) (g i)).prod :=
  φa_list_prod s g f l

theorem φa_zero (x y : ℝ) : φa 0 x y = 1 := by
  simp [φa]

/-- For `s ≥ 2` the two functions `φ_σ^s` coincide. -/
theorem φa_comm_of_two_le {s : ℝ} (hs : 2 ≤ s) (x y : ℝ) : φa s x y = φa s y x := by
  unfold φa
  rcases hs.lt_or_eq with h | rfl
  · rw [ite_eq_right (by linarith), ite_eq_right (by linarith), ite_eq_right (by linarith),
      ite_eq_right (by linarith), mul_comm]
  · norm_num [mul_comm]

/-! ### The singular value function of a diagonal matrix -/

/-- The singular value function of `diag(x, y)`, or of the anti-diagonal matrix with the same
entries, in the three ranges of `s`: `α_1 = max{|x|, |y|}` and `α_1 α_2 = |x| |y|`. -/
theorem svf_diag (s : ℝ) (c : ZMod 2) (x y : ℝ) :
    svf s (boxMat c x y) =
      if s ≤ 1 then max |x| |y| ^ s
      else if s ≤ 2 then max |x| |y| ^ (2 - s) * (|x| * |y|) ^ (s - 1)
      else (|x| * |y|) ^ (s / 2) := by
  rw [svf, norm_boxMat, abs_det_boxMat]

/-- `|u| |v|^{s-1} = |u|^{2-s} (|u| |v|)^{s-1}`. -/
theorem abs_mul_rpow_eq (s u v : ℝ) :
    |u| * |v| ^ (s - 1) = |u| ^ (2 - s) * (|u| * |v|) ^ (s - 1) := by
  have h1 : (2 - s) + (s - 1) = 1 := by ring
  rw [Real.mul_rpow (abs_nonneg u) (abs_nonneg v), ← mul_assoc,
    ← Real.rpow_add' (abs_nonneg u) (by rw [h1]; exact one_ne_zero), h1, Real.rpow_one]

/-- `α_1^{2-s} (α_1 α_2)^{s-1} = max{|x| |y|^{s-1}, |y| |x|^{s-1}}` for `s ≤ 2`: the singular
value function of `diag(x, y)` for `1 < s ≤ 2` is the larger of the two `φ_σ^s`. -/
theorem max_rpow_mul_eq {s : ℝ} (hs2 : s ≤ 2) (x y : ℝ) :
    max |x| |y| ^ (2 - s) * (|x| * |y|) ^ (s - 1) =
      max (|x| * |y| ^ (s - 1)) (|y| * |x| ^ (s - 1)) := by
  rw [abs_mul_rpow_eq s x y, abs_mul_rpow_eq s y x, mul_comm |y| |x|,
    ← max_mul_of_nonneg _ _ (Real.rpow_nonneg (by positivity) _)]
  congr 1
  rcases le_total |x| |y| with h | h
  · rw [max_eq_right h, max_eq_right (Real.rpow_le_rpow (abs_nonneg _) h (by linarith))]
  · rw [max_eq_left h, max_eq_left (Real.rpow_le_rpow (abs_nonneg _) h (by linarith))]

/-- `φ^s(diag(x, y)) = max_σ φ_σ^s(diag(x, y))` for `s ≥ 0`, and likewise for the anti-diagonal
matrix with the same entries. -/
theorem svf_boxMat_eq_max {s : ℝ} (hs : 0 ≤ s) (c : ZMod 2) (x y : ℝ) :
    svf s (boxMat c x y) = max (φa s x y) (φb s x y) := by
  rw [svf_diag]
  unfold φb φa
  split_ifs with h1 h2
  · rcases le_total |x| |y| with h | h
    · rw [max_eq_right h, max_eq_right (Real.rpow_le_rpow (abs_nonneg _) h hs)]
    · rw [max_eq_left h, max_eq_left (Real.rpow_le_rpow (abs_nonneg _) h hs)]
  · exact max_rpow_mul_eq h2 x y
  · rw [mul_comm |y| |x|, max_self]

/-! ### Diagonal systems -/

section System

variable {ι : Type*} (S : System ι)

/-- In a system without rotations,
`A_𝐢 = diag(a_{i_0} ⋯ a_{i_{n-1}}, b_{i_0} ⋯ b_{i_{n-1}})`: the library's `System.matWord_eq`
together with `System.codeWord_eq_axisWord`, `System.gDeriv_axisWord_zero` and
`System.gDeriv_axisWord_one`. -/
theorem matWord_eq_of_diag (hdiag : ∀ i, S.o i = 0) (w : List ι) :
    S.matWord w = boxMat 0 (w.map S.a).prod (w.map S.b).prod := by
  induction w with
  | nil => ext i j; fin_cases i <;> fin_cases j <;> simp
  | cons i w ih =>
    rw [System.matWord_cons, ih, System.mat, hdiag i, boxMat_mul]
    simp

/-- `φ^s(A_𝐢) = max(∏ φa, ∏ φb)` along a word of a system without rotations, `s ≥ 0`. -/
theorem svf_matWord_diag (hdiag : ∀ i, S.o i = 0) {s : ℝ} (hs : 0 ≤ s) (w : List ι) :
    svf s (S.matWord w) =
      max (w.map fun i => φa s (S.a i) (S.b i)).prod
        (w.map fun i => φb s (S.a i) (S.b i)).prod := by
  rw [matWord_eq_of_diag S hdiag, svf_boxMat_eq_max hs, φa_list_prod, φb_list_prod]

variable [Fintype ι]

/-- Rapaport's sum `∑_{i ∈ Λ} φ_σ^s(i)` of (7.1) for the identity `σ`. -/
noncomputable def Φa (s : ℝ) : ℝ := ∑ i, φa s (S.a i) (S.b i)

/-- Rapaport's sum `∑_{i ∈ Λ} φ_σ^s(i)` of (7.1) for the transposition `σ`. -/
noncomputable def Φb (s : ℝ) : ℝ := ∑ i, φb s (S.a i) (S.b i)

theorem Φa_pos [Nonempty ι] (s : ℝ) : 0 < Φa S s :=
  Finset.sum_pos (fun i _ => φa_pos (S.a_ne_zero i) (S.b_ne_zero i) s) Finset.univ_nonempty

theorem Φb_pos [Nonempty ι] (s : ℝ) : 0 < Φb S s :=
  Finset.sum_pos (fun i _ => φb_pos (S.a_ne_zero i) (S.b_ne_zero i) s) Finset.univ_nonempty

theorem Φa_zero : Φa S 0 = Fintype.card ι := by
  simp [Φa, φa_zero]

theorem Φb_zero : Φb S 0 = Fintype.card ι := by
  simp [Φb, φb, φa_zero]

/-- For `s ≥ 2` the two sums of (7.1) coincide. -/
theorem Φa_eq_Φb_of_two_le {s : ℝ} (hs : 2 ≤ s) : Φa S s = Φb S s :=
  Finset.sum_congr rfl fun _ _ => φa_comm_of_two_le hs _ _

/-- `(∑_i φ^s(i))^n = ∑_{|𝐢| = n} ∏_k φ^s(i_k)`. -/
theorem Φa_pow (s : ℝ) (n : ℕ) :
    Φa S s ^ n = ∑ w : Fin n → ι, ∏ k, φa s (S.a (w k)) (S.b (w k)) := by
  rw [Φa, Finset.sum_pow', Fintype.piFinset_univ]

/-- `(∑_i φ_σ^s(i))^n = ∑_{|𝐢| = n} ∏_k φ_σ^s(i_k)` for the transposition `σ`. -/
theorem Φb_pow (s : ℝ) (n : ℕ) :
    Φb S s ^ n = ∑ w : Fin n → ι, ∏ k, φb s (S.a (w k)) (S.b (w k)) := by
  rw [Φb, Finset.sum_pow', Fintype.piFinset_univ]

/-- The singular value sums of a system without rotations, `s ≥ 0`. -/
theorem svfSum_diag (hdiag : ∀ i, S.o i = 0) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    S.svfSum s n = ∑ w : Fin n → ι,
      max (∏ k, φa s (S.a (w k)) (S.b (w k))) (∏ k, φb s (S.a (w k)) (S.b (w k))) := by
  unfold System.svfSum
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [svf_matWord_diag S hdiag hs]
  simp only [List.map_ofFn, List.prod_ofFn, Function.comp_def]

/-- `max(Φa, Φb)^n ≤ ∑_{|𝐢| = n} φ^s(A_𝐢)`. -/
theorem max_pow_le_svfSum (hdiag : ∀ i, S.o i = 0) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    max (Φa S s) (Φb S s) ^ n ≤ S.svfSum s n := by
  rw [svfSum_diag S hdiag hs]
  rcases le_total (Φa S s) (Φb S s) with h | h
  · rw [max_eq_right h, Φb_pow]
    exact Finset.sum_le_sum fun w _ => le_max_right _ _
  · rw [max_eq_left h, Φa_pow]
    exact Finset.sum_le_sum fun w _ => le_max_left _ _

/-- `∑_{|𝐢| = n} φ^s(A_𝐢) ≤ Φa^n + Φb^n`. -/
theorem svfSum_le_add (hdiag : ∀ i, S.o i = 0) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    S.svfSum s n ≤ Φa S s ^ n + Φb S s ^ n := by
  rw [svfSum_diag S hdiag hs, Φa_pow, Φb_pow, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun w _ => max_le_add_of_nonneg
    (Finset.prod_nonneg fun k _ => φa_nonneg _ _ _) (Finset.prod_nonneg fun k _ => φb_nonneg _ _ _)

/-- `max(Φa(0), Φb(0)) = #ι`. -/
theorem max_Φ_zero : max (Φa S 0) (Φb S 0) = Fintype.card ι := by
  rw [Φa_zero, Φb_zero, max_self]

variable [Nonempty ι]

theorem max_Φ_pos (s : ℝ) : 0 < max (Φa S s) (Φb S s) :=
  lt_max_of_lt_left (Φa_pos S s)

/-- The pressure of a system without rotations: `P(s) = log max(Φa(s), Φb(s))` for `s ≥ 0`.
As in `System.IsHomDiag.pressure_eq`, the limit of `log (∑_{|𝐢| = n} φ^s(A_𝐢)) / n` is
squeezed between `log max(Φa, Φb)` and `log max(Φa, Φb) + log 2 / n`. -/
theorem pressure_diag (hdiag : ∀ i, S.o i = 0) {s : ℝ} (hs : 0 ≤ s) :
    S.pressure s = Real.log (max (Φa S s) (Φb S s)) := by
  obtain ⟨δ, hδ⟩ := S.exists_ratioLowerBound
  have hM0 := max_Φ_pos S s
  refine tendsto_nhds_unique (hδ.tendsto_pressure hs) ?_
  have hup : Tendsto (fun n : ℕ => Real.log (max (Φa S s) (Φb S s)) + Real.log 2 / n) atTop
      (𝓝 (Real.log (max (Φa S s) (Φb S s)))) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hn']
    have h := Real.log_le_log (pow_pos hM0 n) (max_pow_le_svfSum S hdiag hs n)
    rw [Real.log_pow] at h
    linarith [mul_comm (n : ℝ) (Real.log (max (Φa S s) (Φb S s)))]
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : Φa S s ^ n ≤ max (Φa S s) (Φb S s) ^ n :=
      pow_le_pow_left₀ (Φa_pos S s).le (le_max_left _ _) n
    have h2 : Φb S s ^ n ≤ max (Φa S s) (Φb S s) ^ n :=
      pow_le_pow_left₀ (Φb_pos S s).le (le_max_right _ _) n
    have hle : S.svfSum s n ≤ 2 * max (Φa S s) (Φb S s) ^ n := by
      linarith [svfSum_le_add S hdiag hs n]
    have h := Real.log_le_log (hδ.svfSum_pos hs n) hle
    rw [Real.log_mul two_ne_zero (pow_pos hM0 n).ne', Real.log_pow] at h
    rw [div_le_iff₀ hn', add_mul, div_mul_cancel₀ _ hn'.ne']
    linarith [mul_comm (n : ℝ) (Real.log (max (Φa S s) (Φb S s)))]

/-- `exp P(s) = max(Φa(s), Φb(s))` for `s ≥ 0`. -/
theorem exp_pressure_diag (hdiag : ∀ i, S.o i = 0) {s : ℝ} (hs : 0 ≤ s) :
    Real.exp (S.pressure s) = max (Φa S s) (Φb S s) := by
  rw [pressure_diag S hdiag hs, Real.exp_log (max_Φ_pos S s)]

/-- `s ↦ max(Φa(s), Φb(s))` is strictly decreasing on `[0, ∞)`. -/
theorem strictAntiOn_max_Φ (hdiag : ∀ i, S.o i = 0) :
    StrictAntiOn (fun s => max (Φa S s) (Φb S s)) (Set.Ici 0) := by
  intro s hs t ht hst
  simp only
  rw [← exp_pressure_diag S hdiag hs, ← exp_pressure_diag S hdiag ht]
  exact Real.exp_lt_exp.2 (S.strictAntiOn_pressure hs ht hst)

/-- `s ↦ max(Φa(s), Φb(s))` is continuous on `[0, ∞)`. -/
theorem continuousOn_max_Φ (hdiag : ∀ i, S.o i = 0) :
    ContinuousOn (fun s => max (Φa S s) (Φb S s)) (Set.Ici 0) :=
  (Real.continuous_exp.comp_continuousOn S.continuousOn_pressure).congr fun _ hs =>
    (exp_pressure_diag S hdiag hs).symm

/-- `max(Φa(s), Φb(s)) → 0` as `s → ∞`. -/
theorem tendsto_max_Φ_atTop (hdiag : ∀ i, S.o i = 0) :
    Tendsto (fun s => max (Φa S s) (Φb S s)) atTop (𝓝 0) := by
  refine (Real.tendsto_exp_atBot.comp S.tendsto_pressure_atTop).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  exact exp_pressure_diag S hdiag hs

/-- (7.1): `max(Φa(dimaff), Φb(dimaff)) = 1`. -/
theorem dimaff_diag (hdiag : ∀ i, S.o i = 0) : max (Φa S S.dimaff) (Φb S S.dimaff) = 1 := by
  rw [← exp_pressure_diag S hdiag S.dimaff_nonneg, S.pressure_dimaff, Real.exp_zero]

/-- (7.1): the affinity dimension is the unique `s ≥ 0` with `max(Φa(s), Φb(s)) = 1`. -/
theorem dimaff_eq_of_max_eq_one (hdiag : ∀ i, S.o i = 0) {s : ℝ} (hs : 0 ≤ s)
    (h : max (Φa S s) (Φb S s) = 1) : S.dimaff = s :=
  S.dimaff_eq hs (by rw [pressure_diag S hdiag hs, h, Real.log_one])

/-- `s ≤ dimaff` if and only if `max(Φa(s), Φb(s)) ≥ 1`, for `s ≥ 0`. -/
theorem le_dimaff_iff (hdiag : ∀ i, S.o i = 0) {s : ℝ} (hs : 0 ≤ s) :
    s ≤ S.dimaff ↔ 1 ≤ max (Φa S s) (Φb S s) := by
  rw [← dimaff_diag S hdiag]
  exact ((strictAntiOn_max_Φ S hdiag).le_iff_ge (Set.mem_Ici.2 S.dimaff_nonneg)
    (Set.mem_Ici.2 hs)).symm

/-- `s < dimaff` if and only if `max(Φa(s), Φb(s)) > 1`, for `s ≥ 0`. -/
theorem lt_dimaff_iff (hdiag : ∀ i, S.o i = 0) {s : ℝ} (hs : 0 ≤ s) :
    s < S.dimaff ↔ 1 < max (Φa S s) (Φb S s) := by
  rw [← dimaff_diag S hdiag]
  exact ((strictAntiOn_max_Φ S hdiag).lt_iff_gt (Set.mem_Ici.2 S.dimaff_nonneg)
    (Set.mem_Ici.2 hs)).symm

end System

/-! ### The energy and the Lyapunov dimension -/

/-- The exponent of `|y| / |x|` in `φ_σ^s / φ^s`, `σ` the transposition: Rapaport's `s - m` for
`s ≤ 1` and `m + 1 - s` for `1 < s ≤ 2`, where `m = ⌊s⌋` (lines 2055 to 2066 of the source), and
`0` for `s > 2`. -/
noncomputable def swapExp (s : ℝ) : ℝ := if s ≤ 1 then s else if s ≤ 2 then 2 - s else 0

theorem swapExp_pos {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) : 0 < swapExp s := by
  unfold swapExp
  split_ifs <;> linarith

/-- Exchanging the two exponents in the energy `Λ` of `eq:energy_def` adds
`swapExp s (l_2 - l_1)`. -/
theorem energy_swap (l1 l2 s : ℝ) :
    energy l2 l1 s = energy l1 l2 s + swapExp s * (l2 - l1) := by
  unfold energy swapExp
  split_ifs <;> ring

/-- `φ_σ^s(diag(x, y)) = φ^s(diag(x, y)) (|y| / |x|)^{swapExp s}` for the transposition `σ`,
in exponential form. -/
theorem φa_swap {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (s : ℝ) :
    φa s y x = φa s x y * Real.exp (swapExp s * (Real.log |y| - Real.log |x|)) := by
  rw [φa_eq_exp hy hx, φa_eq_exp hx hy, energy_swap, Real.exp_add]

/-- The energy `Λ` of `eq:energy_def` is linear in the pair of exponents. -/
theorem sum_mul_energy {ι : Type*} [Fintype ι] (p u v : ι → ℝ) (s : ℝ) :
    ∑ i, p i * energy (u i) (v i) s = energy (∑ i, p i * u i) (∑ i, p i * v i) s := by
  unfold energy
  split_ifs
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- `dim_L(h, l_1, l_2) = s` when `h + Λ(l_1, l_2, s) = 0` and both exponents are negative,
whatever their order: the library's `lyapDim_eq` without its hypothesis `l_2 ≤ l_1`, which the
computation of `eq:diml_min2` does not use. -/
theorem lyapDim_eq_of_neg {h l1 l2 s : ℝ} (hl1 : l1 < 0) (hl2 : l2 < 0)
    (heq : h + energy l1 l2 s = 0) : lyapDim h l1 l2 = s := by
  have hl1' : l1 ≠ 0 := hl1.ne
  have hl2' : l2 ≠ 0 := hl2.ne
  unfold energy at heq
  unfold lyapDim
  split_ifs at heq with hs1 hs2
  · have hh : h = -(s * l1) := by linarith
    have hle : h ≤ -l1 := by
      have := mul_nonneg (sub_nonneg.2 hs1) (neg_nonneg.2 hl1.le)
      rw [hh]; nlinarith
    rw [ite_eq_left hle, hh]
    field_simp
  · have hh : h = -(l1 + (s - 1) * l2) := by linarith
    have hs1' : 0 < s - 1 := by linarith
    have hn : ¬ h ≤ -l1 := by
      have := mul_pos hs1' (neg_pos.2 hl2)
      rw [hh, not_le]; nlinarith
    have hle : h ≤ -l1 - l2 := by
      have := mul_nonneg (show 0 ≤ 2 - s by linarith) (neg_nonneg.2 hl2.le)
      rw [hh]; nlinarith
    rw [ite_eq_right hn, ite_eq_left hle, hh]
    field_simp
    ring
  · have hh : h = -(s / 2 * (l1 + l2)) := by linarith
    have hs2' : 0 < s / 2 - 1 := by linarith
    have hsum : l1 + l2 < 0 := by linarith
    have hn2 : ¬ h ≤ -l1 - l2 := by
      have := mul_pos hs2' (neg_pos.2 hsum)
      rw [hh, not_le]; nlinarith
    have hn1 : ¬ h ≤ -l1 := fun hle => hn2 (by linarith)
    rw [ite_eq_right hn1, ite_eq_right hn2, hh]
    have : l1 + l2 ≠ 0 := hsum.ne
    field_simp

/-! ### The weights `p_i = φ^s(i)` -/

section Weights

variable {ι : Type*} [Fintype ι] {x y : ι → ℝ}

/-- `H(p) = -Λ(λ_x, λ_y, s)` for the weights `p_i = φ^s(diag(x_i, y_i))`, normalised or not,
where `λ_x = ∑ p_i log |x_i|` and `λ_y = ∑ p_i log |y_i|`: `log p_i = Λ(log |x_i|, log |y_i|, s)`
and `Λ` is linear in the exponents (lines 2049 and 2069 of the source). -/
theorem sum_negMulLog_eq (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0) (s : ℝ) :
    ∑ i, Real.negMulLog (φa s (x i) (y i)) =
      -energy (∑ i, φa s (x i) (y i) * Real.log |x i|)
        (∑ i, φa s (x i) (y i) * Real.log |y i|) s := by
  calc ∑ i, Real.negMulLog (φa s (x i) (y i))
      = -∑ i, φa s (x i) (y i) * energy (Real.log |x i|) (Real.log |y i|) s := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Real.negMulLog, log_φa (hx i) (hy i)]
        ring
    _ = _ := by rw [sum_mul_energy]

/-- `H(p) + Λ(λ_x, λ_y, s) = 0` for the weights `p_i = φ^s(diag(x_i, y_i))`. -/
theorem sum_negMulLog_add_energy (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0) (s : ℝ) :
    ∑ i, Real.negMulLog (φa s (x i) (y i)) +
      energy (∑ i, φa s (x i) (y i) * Real.log |x i|)
        (∑ i, φa s (x i) (y i) * Real.log |y i|) s = 0 := by
  rw [sum_negMulLog_eq hx hy]
  ring

/-- The exponent `∑ p_i log |x_i|` is negative for positive weights and `0 < |x_i| < 1`. -/
theorem sum_mul_log_abs_neg [Nonempty ι] {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    (hx : ∀ i, x i ≠ 0) (hx1 : ∀ i, |x i| < 1) : ∑ i, p i * Real.log |x i| < 0 :=
  Finset.sum_neg
    (fun i _ => mul_neg_of_pos_of_neg (hp i) (Real.log_neg (abs_pos.2 (hx i)) (hx1 i)))
    Finset.univ_nonempty

/-- `s = dim_L(H(p), λ_x, λ_y)` for the weights `p_i = φ^s(diag(x_i, y_i))`, for every `s`
(lines 2047 to 2077 of the source): the identity is algebraic, and the weights form a probability
vector exactly when `∑ φ^s(i) = 1`. -/
theorem lyapDim_weights [Nonempty ι] (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (hx1 : ∀ i, |x i| < 1) (hy1 : ∀ i, |y i| < 1) (s : ℝ) :
    lyapDim (∑ i, Real.negMulLog (φa s (x i) (y i))) (∑ i, φa s (x i) (y i) * Real.log |x i|)
      (∑ i, φa s (x i) (y i) * Real.log |y i|) = s :=
  lyapDim_eq_of_neg (sum_mul_log_abs_neg (fun i => φa_pos (hx i) (hy i) s) hx hx1)
    (sum_mul_log_abs_neg (fun i => φa_pos (hx i) (hy i) s) hy hy1)
    (sum_negMulLog_add_energy hx hy s)

/-- `H(p) ≤ χ_1` for `s ≤ 1`, where `χ_1 = -λ_x`: the first case of `eq:diml_min2`. -/
theorem sum_negMulLog_le_of_le_one (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (hx1 : ∀ i, |x i| < 1) {s : ℝ} (hs1 : s ≤ 1) [Nonempty ι] :
    ∑ i, Real.negMulLog (φa s (x i) (y i)) ≤ -∑ i, φa s (x i) (y i) * Real.log |x i| := by
  have hlx := sum_mul_log_abs_neg (fun i => φa_pos (hx i) (hy i) s) hx hx1
  rw [sum_negMulLog_eq hx hy]
  unfold energy
  rw [ite_eq_left hs1]
  nlinarith

/-- `χ_1 < H(p)` for `s > 1`, where `χ_1 = -λ_x` (line 2069 of the source). -/
theorem lt_sum_negMulLog_of_one_lt (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (hx1 : ∀ i, |x i| < 1) (hy1 : ∀ i, |y i| < 1) {s : ℝ} (hs1 : 1 < s) [Nonempty ι] :
    -∑ i, φa s (x i) (y i) * Real.log |x i| < ∑ i, Real.negMulLog (φa s (x i) (y i)) := by
  have hlx := sum_mul_log_abs_neg (fun i => φa_pos (hx i) (hy i) s) hx hx1
  have hly := sum_mul_log_abs_neg (fun i => φa_pos (hx i) (hy i) s) hy hy1
  rw [sum_negMulLog_eq hx hy]
  unfold energy
  rw [ite_eq_right (not_le.2 hs1)]
  split_ifs with hs2
  · nlinarith
  · nlinarith

/-- `H(p) < χ_1 + χ_2` for `s < 2`, where `χ_1 = -λ_x`, `χ_2 = -λ_y` (line 2069 of the
source). -/
theorem sum_negMulLog_lt_of_lt_two (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (hx1 : ∀ i, |x i| < 1) (hy1 : ∀ i, |y i| < 1) {s : ℝ} (hs2 : s < 2) [Nonempty ι] :
    ∑ i, Real.negMulLog (φa s (x i) (y i)) <
      -∑ i, φa s (x i) (y i) * Real.log |x i| - ∑ i, φa s (x i) (y i) * Real.log |y i| := by
  have hlx := sum_mul_log_abs_neg (fun i => φa_pos (hx i) (hy i) s) hx hx1
  have hly := sum_mul_log_abs_neg (fun i => φa_pos (hx i) (hy i) s) hy hy1
  rw [sum_negMulLog_eq hx hy]
  unfold energy
  rw [ite_eq_left hs2.le] at *
  split_ifs with hs1
  · nlinarith
  · nlinarith

/-- `χ_1 + χ_2 ≤ H(p)` for `s ≥ 2`, where `χ_1 = -λ_x`, `χ_2 = -λ_y` (line 2049 of the
source). -/
theorem le_sum_negMulLog_of_two_le (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (hx1 : ∀ i, |x i| < 1) (hy1 : ∀ i, |y i| < 1) {s : ℝ} (hs2 : 2 ≤ s) [Nonempty ι] :
    -∑ i, φa s (x i) (y i) * Real.log |x i| - ∑ i, φa s (x i) (y i) * Real.log |y i| ≤
      ∑ i, Real.negMulLog (φa s (x i) (y i)) := by
  have hlx := sum_mul_log_abs_neg (fun i => φa_pos (hx i) (hy i) s) hx hx1
  have hly := sum_mul_log_abs_neg (fun i => φa_pos (hx i) (hy i) s) hy hy1
  rw [sum_negMulLog_eq hx hy]
  unfold energy
  rcases hs2.lt_or_eq with h | rfl
  · rw [ite_eq_right (by linarith), ite_eq_right (by linarith)]
    nlinarith
  · rw [ite_eq_right (by norm_num), ite_eq_left le_rfl]
    linarith

/-- One term of the concavity step of lines 2055 to 2059 of the source:
`c (p log |v| - p log |u|) ≤ φ_σ^s - p` for `p = φ^s(diag(u, v))` and `c = swapExp s`, from
`t + 1 ≤ e^t`. -/
theorem swapExp_mul_le {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) (s : ℝ) :
    swapExp s * (φa s u v * Real.log |v| - φa s u v * Real.log |u|) ≤ φa s v u - φa s u v := by
  rw [φa_swap hu hv]
  have he := mul_le_mul_of_nonneg_left
    (Real.add_one_le_exp (swapExp s * (Real.log |v| - Real.log |u|))) (φa_pos hu hv s).le
  linarith

/-- The strict form of `swapExp_mul_le` for `0 < s < 2` and `|u| ≠ |v|`. -/
theorem swapExp_mul_lt {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2)
    (huv : |u| ≠ |v|) :
    swapExp s * (φa s u v * Real.log |v| - φa s u v * Real.log |u|) < φa s v u - φa s u v := by
  rw [φa_swap hu hv]
  have ht : swapExp s * (Real.log |v| - Real.log |u|) ≠ 0 := by
    refine mul_ne_zero (swapExp_pos hs0 hs2).ne' (sub_ne_zero.2 fun h => huv ?_)
    exact (Real.log_injOn_pos (Set.mem_Ioi.2 (abs_pos.2 hv)) (Set.mem_Ioi.2 (abs_pos.2 hu)) h).symm
  have he := mul_lt_mul_of_pos_left (Real.add_one_lt_exp ht) (φa_pos hu hv s)
  linarith

/-- The concavity step of lines 2055 to 2066 of the source, without normalisation:
`swapExp s (λ_y - λ_x) ≤ ∑ φ_σ^s(i) - ∑ φ^s(i)` for the weights `p_i = φ^s(diag(x_i, y_i))`. -/
theorem swapExp_mul_sub_le (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0) (s : ℝ) :
    swapExp s * (∑ i, φa s (x i) (y i) * Real.log |y i| -
      ∑ i, φa s (x i) (y i) * Real.log |x i|) ≤
      ∑ i, φa s (y i) (x i) - ∑ i, φa s (x i) (y i) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i _ => swapExp_mul_le (hx i) (hy i) s

/-- The strict form of `swapExp_mul_sub_le` for `0 < s < 2` when `|x_i| ≠ |y_i|` for some
`i`. -/
theorem swapExp_mul_sub_lt (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0) {s : ℝ} (hs0 : 0 < s)
    (hs2 : s < 2) (hne : ∃ i, |x i| ≠ |y i|) :
    swapExp s * (∑ i, φa s (x i) (y i) * Real.log |y i| -
      ∑ i, φa s (x i) (y i) * Real.log |x i|) <
      ∑ i, φa s (y i) (x i) - ∑ i, φa s (x i) (y i) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
  obtain ⟨j, hj⟩ := hne
  exact Finset.sum_lt_sum (fun i _ => swapExp_mul_le (hx i) (hy i) s)
    ⟨j, Finset.mem_univ _, swapExp_mul_lt (hx j) (hy j) hs0 hs2 hj⟩

/-- Rapaport's `χ_1 ≤ χ_2` (lines 2055 to 2066 of the source): for `0 < s < 2` and
`∑ φ_σ^s(i) ≤ ∑ φ^s(i)`, the weights `p_i = φ^s(diag(x_i, y_i))` give `λ_y ≤ λ_x`. -/
theorem sum_mul_log_le_of_le (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0) {s : ℝ} (hs0 : 0 < s)
    (hs2 : s < 2) (h : ∑ i, φa s (y i) (x i) ≤ ∑ i, φa s (x i) (y i)) :
    ∑ i, φa s (x i) (y i) * Real.log |y i| ≤ ∑ i, φa s (x i) (y i) * Real.log |x i| := by
  have key := swapExp_mul_sub_le hx hy s
  by_contra hlt
  have := mul_pos (swapExp_pos hs0 hs2) (sub_pos.2 (not_le.1 hlt))
  linarith

/-- `λ_y < λ_x` in `sum_mul_log_le_of_le` when `|x_i| ≠ |y_i|` for some `i`. -/
theorem sum_mul_log_lt_of_le (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0) {s : ℝ} (hs0 : 0 < s)
    (hs2 : s < 2) (h : ∑ i, φa s (y i) (x i) ≤ ∑ i, φa s (x i) (y i))
    (hne : ∃ i, |x i| ≠ |y i|) :
    ∑ i, φa s (x i) (y i) * Real.log |y i| < ∑ i, φa s (x i) (y i) * Real.log |x i| := by
  have key := swapExp_mul_sub_lt hx hy hs0 hs2 hne
  by_contra hle
  have := mul_nonneg (swapExp_pos hs0 hs2).le (sub_nonneg.2 (not_lt.1 hle))
  linarith

/-- In the setting of `sum_mul_log_le_of_le` the two exponents coincide exactly when
`|x_i| = |y_i|` for every `i`. -/
theorem sum_mul_log_eq_iff (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0) {s : ℝ} (hs0 : 0 < s)
    (hs2 : s < 2) (h : ∑ i, φa s (y i) (x i) ≤ ∑ i, φa s (x i) (y i)) :
    ∑ i, φa s (x i) (y i) * Real.log |y i| = ∑ i, φa s (x i) (y i) * Real.log |x i| ↔
      ∀ i, |x i| = |y i| := by
  constructor
  · intro heq
    by_contra hne
    exact (sum_mul_log_lt_of_le hx hy hs0 hs2 h (not_forall.1 hne)).ne heq
  · intro hxy
    exact Finset.sum_congr rfl fun i _ => by rw [hxy i]

end Weights

/-! ### The Käenmäki weights at the affinity dimension -/

section Kaenmaki

variable {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)

/-- The Käenmäki weights `p_i = φ^s(i)` at `s = dimaff` with the coordinate `a` first:
Rapaport's weights (7.3) (lines 2036 to 2044 of the source) under his normalisation (7.2) that the
identity attains the maximum in (7.1). -/
noncomputable def kwA (i : ι) : ℝ := φa S.dimaff (S.a i) (S.b i)

/-- The Käenmäki weights `p_i = φ_σ^s(i)` at `s = dimaff` with the coordinate `b` first, `σ` the
transposition: Rapaport's weights after the permutation of coordinates of line 2032. -/
noncomputable def kwB (i : ι) : ℝ := φb S.dimaff (S.a i) (S.b i)

theorem kwA_pos (i : ι) : 0 < kwA S i := φa_pos (S.a_ne_zero i) (S.b_ne_zero i) _

theorem kwB_pos (i : ι) : 0 < kwB S i := φb_pos (S.a_ne_zero i) (S.b_ne_zero i) _

/-- The weights `kwA` form a probability vector when the identity attains the maximum in
(7.1) (line 2034 of the source). -/
theorem sum_kwA (hdiag : ∀ i, S.o i = 0) (h : Φb S S.dimaff ≤ Φa S S.dimaff) :
    ∑ i, kwA S i = 1 := by
  have := dimaff_diag S hdiag
  rwa [max_eq_left h] at this

/-- The weights `kwB` form a probability vector when the transposition attains the maximum in
(7.1). -/
theorem sum_kwB (hdiag : ∀ i, S.o i = 0) (h : Φa S S.dimaff ≤ Φb S S.dimaff) :
    ∑ i, kwB S i = 1 := by
  have := dimaff_diag S hdiag
  rwa [max_eq_right h] at this

/-- `dimaff = dim_L(H(p), λ_a, λ_b)` for `p = kwA` (lines 2047 to 2077 of the source). -/
theorem dimaff_eq_lyapDim_kwA :
    S.dimaff = lyapDim (∑ i, Real.negMulLog (kwA S i)) (∑ i, kwA S i * Real.log |S.a i|)
      (∑ i, kwA S i * Real.log |S.b i|) :=
  (lyapDim_weights S.a_ne_zero S.b_ne_zero S.abs_a_lt_one S.abs_b_lt_one S.dimaff).symm

/-- `dimaff = dim_L(H(p), λ_b, λ_a)` for `p = kwB`. -/
theorem dimaff_eq_lyapDim_kwB :
    S.dimaff = lyapDim (∑ i, Real.negMulLog (kwB S i)) (∑ i, kwB S i * Real.log |S.b i|)
      (∑ i, kwB S i * Real.log |S.a i|) :=
  (lyapDim_weights S.b_ne_zero S.a_ne_zero S.abs_b_lt_one S.abs_a_lt_one S.dimaff).symm

/-- `λ_b ≤ λ_a` for `p = kwA` when `0 < dimaff < 2` and the identity attains the maximum in
(7.1): Rapaport's `χ_1 ≤ χ_2` (lines 2055 to 2066 of the source). -/
theorem sum_kwA_mul_log_le (h : Φb S S.dimaff ≤ Φa S S.dimaff) (hs0 : 0 < S.dimaff)
    (hs2 : S.dimaff < 2) :
    ∑ i, kwA S i * Real.log |S.b i| ≤ ∑ i, kwA S i * Real.log |S.a i| :=
  sum_mul_log_le_of_le S.a_ne_zero S.b_ne_zero hs0 hs2 h

/-- `λ_a ≤ λ_b` for `p = kwB` when `0 < dimaff < 2` and the transposition attains the maximum
in (7.1). -/
theorem sum_kwB_mul_log_le (h : Φa S S.dimaff ≤ Φb S S.dimaff) (hs0 : 0 < S.dimaff)
    (hs2 : S.dimaff < 2) :
    ∑ i, kwB S i * Real.log |S.a i| ≤ ∑ i, kwB S i * Real.log |S.b i| :=
  sum_mul_log_le_of_le S.b_ne_zero S.a_ne_zero hs0 hs2 h

/-- `λ_b < λ_a` in `sum_kwA_mul_log_le` when `|a_i| ≠ |b_i|` for some `i`. -/
theorem sum_kwA_mul_log_lt (h : Φb S S.dimaff ≤ Φa S S.dimaff) (hs0 : 0 < S.dimaff)
    (hs2 : S.dimaff < 2) (hne : ∃ i, |S.a i| ≠ |S.b i|) :
    ∑ i, kwA S i * Real.log |S.b i| < ∑ i, kwA S i * Real.log |S.a i| :=
  sum_mul_log_lt_of_le S.a_ne_zero S.b_ne_zero hs0 hs2 h hne

/-- `λ_a < λ_b` in `sum_kwB_mul_log_le` when `|a_i| ≠ |b_i|` for some `i`. -/
theorem sum_kwB_mul_log_lt (h : Φa S S.dimaff ≤ Φb S S.dimaff) (hs0 : 0 < S.dimaff)
    (hs2 : S.dimaff < 2) (hne : ∃ i, |S.a i| ≠ |S.b i|) :
    ∑ i, kwB S i * Real.log |S.a i| < ∑ i, kwB S i * Real.log |S.b i| :=
  sum_mul_log_lt_of_le S.b_ne_zero S.a_ne_zero hs0 hs2 h (hne.imp fun _ h => Ne.symm h)

/-- For `s = 0` and for `s ≥ 2` the two weight vectors coincide. -/
theorem kwA_eq_kwB (hs : ¬ (0 < S.dimaff ∧ S.dimaff < 2)) : kwA S = kwB S := by
  funext i
  rcases S.dimaff_nonneg.eq_or_lt with h0 | h0
  · simp only [kwA, kwB, φb, ← h0, φa_zero]
  · exact φa_comm_of_two_le (not_lt.1 fun h2 => hs ⟨h0, h2⟩) _ _

/-- The Käenmäki weights at the affinity dimension of a system without rotations (lines 2028 to
2077 of the source): a positive probability vector `p`, given by `φ^s` with one of the two orders
of the coordinates, whose Lyapunov dimension `dim_L(H(p), λ_weak, λ_strong)` is `dimaff`. The
weaker exponent comes first: `λ_b ≤ λ_a` when `p = φa`, `λ_a ≤ λ_b` when `p = φb`, strictly when
`0 < dimaff < 2` and `|a_i| ≠ |b_i|` for some `i`. For `0 < dimaff < 2` the order is Rapaport's
concavity step; for `dimaff = 0` and `dimaff ≥ 2` the two weight vectors coincide and the
alternative is chosen by the order of the exponents. -/
theorem kaenmaki_weights (hdiag : ∀ i, S.o i = 0) :
    ∃ p : ι → ℝ, (∀ i, 0 < p i) ∧ ∑ i, p i = 1 ∧
      (((∀ i, p i = φa S.dimaff (S.a i) (S.b i)) ∧
          ∑ i, p i * Real.log |S.b i| ≤ ∑ i, p i * Real.log |S.a i| ∧
          (0 < S.dimaff → S.dimaff < 2 → (∃ i, |S.a i| ≠ |S.b i|) →
            ∑ i, p i * Real.log |S.b i| < ∑ i, p i * Real.log |S.a i|) ∧
          S.dimaff = lyapDim (∑ i, Real.negMulLog (p i)) (∑ i, p i * Real.log |S.a i|)
            (∑ i, p i * Real.log |S.b i|)) ∨
        ((∀ i, p i = φb S.dimaff (S.a i) (S.b i)) ∧
          ∑ i, p i * Real.log |S.a i| ≤ ∑ i, p i * Real.log |S.b i| ∧
          (0 < S.dimaff → S.dimaff < 2 → (∃ i, |S.a i| ≠ |S.b i|) →
            ∑ i, p i * Real.log |S.a i| < ∑ i, p i * Real.log |S.b i|) ∧
          S.dimaff = lyapDim (∑ i, Real.negMulLog (p i)) (∑ i, p i * Real.log |S.b i|)
            (∑ i, p i * Real.log |S.a i|))) := by
  by_cases hmid : 0 < S.dimaff ∧ S.dimaff < 2
  · rcases le_total (Φb S S.dimaff) (Φa S S.dimaff) with h | h
    · exact ⟨kwA S, kwA_pos S, sum_kwA S hdiag h, Or.inl ⟨fun _ => rfl,
        sum_kwA_mul_log_le S h hmid.1 hmid.2, fun hs0 hs2 hne => sum_kwA_mul_log_lt S h hs0 hs2 hne,
        dimaff_eq_lyapDim_kwA S⟩⟩
    · exact ⟨kwB S, kwB_pos S, sum_kwB S hdiag h, Or.inr ⟨fun _ => rfl,
        sum_kwB_mul_log_le S h hmid.1 hmid.2, fun hs0 hs2 hne => sum_kwB_mul_log_lt S h hs0 hs2 hne,
        dimaff_eq_lyapDim_kwB S⟩⟩
  · have hAB := kwA_eq_kwB S hmid
    have hΦ : Φa S S.dimaff = Φb S S.dimaff := Finset.sum_congr rfl fun i _ => congrFun hAB i
    have h1 : ∑ i, kwA S i = 1 := sum_kwA S hdiag hΦ.ge
    rcases le_total (∑ i, kwA S i * Real.log |S.b i|) (∑ i, kwA S i * Real.log |S.a i|) with h | h
    · exact ⟨kwA S, kwA_pos S, h1, Or.inl ⟨fun _ => rfl, h,
        fun hs0 hs2 _ => absurd ⟨hs0, hs2⟩ hmid, dimaff_eq_lyapDim_kwA S⟩⟩
    · have hL := dimaff_eq_lyapDim_kwB S
      rw [← hAB] at hL
      exact ⟨kwA S, kwA_pos S, h1, Or.inr ⟨fun i => congrFun hAB i, h,
        fun hs0 hs2 _ => absurd ⟨hs0, hs2⟩ hmid, hL⟩⟩

end Kaenmaki

end BoxLike.Rapaport.Diagonal
