module

/-
A concrete rational system accompanying `sec:dimension_of_projections`:
`φ_1(x, y) = (x/10, y/20 + 3/5)`, `φ_2(x, y) = (y/30 + 3/10, x/40 + 9/10)`, whose coordinate
marginals of the equilibrium state have two distinct pointwise dimensions.
It is not the example of the article: the prescribed-dimension family of
`ex:projection_double_dimensional` is formalised in `BoxLike/PrescribedExample/`.

General lemmas, in the namespace `BoxLike.System`:

* `System.le_abs_gWord_sub`, `System.le_gap`, `System.projExpSeparation_of_le_abs`: the
  common-prefix argument. If the maps `g_j` send a set `I ∋ 0` into itself, their images of `I`
  are at mutual distance at least `δ` and every ratio is at least `ρ`, then
  `Δ_n^Ψ ≥ δ ρ^{n-1}`, and the projective exponential separation condition holds.
* `System.svfSum_one`, `System.pressure_le`: `P(𝖠, s) ≤ n⁻¹ log ∑_{|𝐢| = n} φ^s(A_𝐢)`, and the
  first sum is `∑_i φ^s(A_i)`.
* `System.transfer`, `System.sum_abs_gDeriv_rpow_mul`, `System.svfSum_bounds`,
  `System.pressure_eq_log_of_eigenvector`: the matrix `M(s)` as an operator on the two axes, its
  powers as sums over words, the comparison with `∑_{|𝐢| = n} φ^s(A_𝐢)` for `0 ≤ s ≤ 1`, and
  `P(𝖠, s) = log ρ` for a positive eigenvector with eigenvalue `ρ`.
* `System.main1_of_le_one`, `System.main2_of_le_one`: `thm:main1` and `thm:main2` for
  `0 < s ≤ 1`. The two pointwise dimensions are `s` and `s λ_1/λ_2`, they are distinct, both
  occur on sets of positive measure, the marginals are double-dimensional, and
  `s < 2 - λ_1/λ_2` holds.
* `System.marginal_eq_zero_of_disjoint`: the marginal `(proj_c)_*(π_*μ)` is carried by
  `proj_c(X)`.

The example, in the namespace `BoxLike.Example`:

* `sys`, `sys_phi_zero`, `sys_phi_one`, `sys_mat_zero`, `sys_mat_one`, `sys_g_zero_zero` to
  `sys_g_one_one`: the system, its two maps, their linear parts and the four maps of its
  projective system.
* `withRotations`, `hasProximalDiagonal`, `isProximalMatrix_mat_zero`, `proximal`,
  `irreducible`.
* `phi_zero_image_square`, `phi_one_image_square`, `strongSeparation`, `strongOpenSet`: the
  image rectangles of `[0,1]²` and the strong separation condition.
* `le_gap`, `projExpSeparation`: `Δ_n^Ψ ≥ 40^{1-n}/5` for `n ≥ 1`.
* `pressure_one_le`, `dimaff_pos_lt_one`: `P(𝖠, 1) ≤ log(2/15) < 0` and `0 < dimaff < 1`.
* `marginal_doubleDim`: the conclusion of the example for the coordinate marginals.
* `dimH_attractor`: `\dim_H(X) = dimaff(X)`, from `thm:main2`.
* `coord_zero_attractor_subset`, `coord_one_attractor_subset`, `mutuallySingular_marginal`:
  `proj_x(X) ⊆ [0, 1/3]`, `proj_y(X) ⊆ [3/5, 37/40]`, and the two marginals are mutually
  singular.
* `M`, `svfSum_le_mulVec`, `spectralRadius_M`, `pressure_eq_log_spectralRadius`,
  `spectralRadius_M_zero`, `spectralRadius_M_one_le`: the matrix `M(t)`, the comparison with
  the singular-value sums, `P(𝖠, t) = log ρ(M(t))` for `0 ≤ t ≤ 1`, `ρ(M(0)) = 2` and
  `ρ(M(1)) ≤ 2/15`.
* `dimaff_charEq`, `eq_dimaff_of_charEq`: the affinity dimension is the only solution of
  `(1 - 10^{-s})(1 - 20^{-s}) = 1200^{-s}` in `(0, 1]`.

The explicit values of `λ_1`, `λ_2` through the Markov measure and their numerical
approximations are out of scope.
-/
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.MainTwo
public import BoxLike.MeasureDimDouble
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology
open scoped ENNReal

universe u

namespace System

variable {ι : Type u} (S : System ι)

/-! ### The common-prefix argument -/

section Gap

variable {S} {I : Set ℝ} {δ ρ : ℝ}

/-- If every `g_j` sends `I` into itself, then so does every composition `g_𝐣`. -/
theorem gWord_mem (hI : ∀ p, ∀ t ∈ I, S.g p t ∈ I) (u : List (ι × ZMod 2)) {t : ℝ}
    (ht : t ∈ I) : S.gWord u t ∈ I := by
  induction u with
  | nil => exact ht
  | cons p u ih => exact hI p _ ih

/-- The common-prefix argument of `Example.sys`. Suppose that every `g_j`
sends `I` into itself, that the images `g_j(I)` are at mutual distance at least `δ`, and that
every contraction ratio is at least `ρ` in modulus. Then two distinct words `𝐣`, `𝐣'` of the same
length `n` satisfy `|g_𝐣(t) - g_𝐣'(t')| ≥ δ ρ^{n-1}` for all `t, t' ∈ I`: the common prefix
has length at most `n - 1` and the first letters that differ contribute `δ`. -/
theorem le_abs_gWord_sub (hδ : 0 ≤ δ) (hρ : S.RatioLowerBound ρ)
    (hI : ∀ p, ∀ t ∈ I, S.g p t ∈ I)
    (hsep : ∀ p q, p ≠ q → ∀ t ∈ I, ∀ t' ∈ I, δ ≤ |S.g p t - S.g q t'|)
    (u u' : List (ι × ZMod 2)) (hlen : u.length = u'.length) (hne : u ≠ u') {t t' : ℝ}
    (ht : t ∈ I) (ht' : t' ∈ I) :
    δ * ρ ^ (u.length - 1) ≤ |S.gWord u t - S.gWord u' t'| := by
  induction u generalizing u' with
  | nil =>
    cases u' with
    | nil => exact absurd rfl hne
    | cons q w' => simp at hlen
  | cons p w ih =>
    cases u' with
    | nil => simp at hlen
    | cons q w' =>
      have hlen' : w.length = w'.length := by simpa using hlen
      simp only [gWord_cons, Function.comp_apply, List.length_cons, Nat.add_sub_cancel]
      by_cases hpq : p = q
      · subst hpq
        have hne' : w ≠ w' := fun h => hne (by rw [h])
        have hw : w.length ≠ 0 := by
          intro h0
          have h1 : w = [] := List.length_eq_zero_iff.1 h0
          have h2 : w' = [] := List.length_eq_zero_iff.1 (hlen' ▸ h0)
          exact hne' (h1.trans h2.symm)
        have h := ih w' hlen' hne'
        have e : S.g p (S.gWord w t) - S.g p (S.gWord w' t') =
            S.ratio p * (S.gWord w t - S.gWord w' t') := by
          simp only [g]; ring
        rw [e, abs_mul, ← pow_sub_one_mul hw, ← mul_assoc, mul_comm]
        exact mul_le_mul (hρ.2 p) h (mul_nonneg hδ (pow_nonneg hρ.1.le _)) (abs_nonneg _)
      · refine le_trans ?_ (hsep p q hpq _ (gWord_mem hI w ht) _ (gWord_mem hI w' ht'))
        exact mul_le_of_le_one_right hδ
          (pow_le_one₀ hρ.1.le ((hρ.2 p).trans (S.abs_ratio_lt_one p).le))

/-- The lower bound `Δ_n^Ψ ≥ δ ρ^{n-1}` from the common-prefix argument of
`Example.sys`, for a set `I ∋ 0` that every `g_j` sends into itself, with
the images `g_j(I)` at mutual distance at least `δ` and all ratios at least `ρ` in modulus. The
condition of equal derivatives in the definition of `Δ_n^Ψ` is not used. -/
theorem le_gap (hδ : 0 ≤ δ) (hρ : S.RatioLowerBound ρ) (h0 : (0 : ℝ) ∈ I)
    (hI : ∀ p, ∀ t ∈ I, S.g p t ∈ I)
    (hsep : ∀ p q, p ≠ q → ∀ t ∈ I, ∀ t' ∈ I, δ ≤ |S.g p t - S.g q t'|) (n : ℕ) :
    ENNReal.ofReal (δ * ρ ^ (n - 1)) ≤ S.gap n := by
  refine le_iInf fun u => le_iInf fun u' => le_iInf fun hu => le_iInf fun hu' =>
    le_iInf fun hne => le_iInf fun _ => ENNReal.ofReal_le_ofReal ?_
  have h := le_abs_gWord_sub hδ hρ hI hsep u u' (hu.trans hu'.symm) hne h0 h0
  rwa [hu] at h

/-- Under the hypotheses of `le_gap` with `δ > 0` the projective exponential separation
condition of `sec:exponential_separation` holds, with `c = min{δ, ρ}` and every `n ≥ 1`. -/
theorem projExpSeparation_of_le_abs (hδ : 0 < δ) (hρ : S.RatioLowerBound ρ) (h0 : (0 : ℝ) ∈ I)
    (hI : ∀ p, ∀ t ∈ I, S.g p t ∈ I)
    (hsep : ∀ p q, p ≠ q → ∀ t ∈ I, ∀ t' ∈ I, δ ≤ |S.g p t - S.g q t'|) :
    S.ProjExpSeparation := by
  have hc : 0 < min δ ρ := lt_min hδ hρ.1
  refine ⟨min δ ρ, hc, fun k => k + 1, fun a b h => Nat.succ_lt_succ h, fun k => ?_⟩
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (le_gap hδ.le hρ h0 hI hsep (k + 1))
  rw [Nat.add_sub_cancel, pow_succ']
  exact mul_le_mul (min_le_left _ _) (pow_le_pow_left₀ hc.le (min_le_right _ _) k)
    (pow_nonneg hc.le _) hδ.le

end Gap

/-! ### The pressure is at most its finite approximations -/

section Pressure

variable [Fintype ι]

/-- The sum over the words of length one: `∑_{|𝐢| = 1} φ^s(A_𝐢) = ∑_i φ^s(A_i)`. -/
theorem svfSum_one (s : ℝ) : S.svfSum s 1 = ∑ i, svf s (S.mat i) := by
  rw [svfSum]
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι) _ _ fun w => ?_
  simp [matWord]

/-- The pressure of `sec:affinity_dim` is the infimum of a sub-additive sequence:
`P(𝖠, s) ≤ n⁻¹ log ∑_{|𝐢| = n} φ^s(A_𝐢)` for every `n ≥ 1`. -/
theorem pressure_le [Nonempty ι] {s : ℝ} (hs : 0 ≤ s) {n : ℕ} (hn : 1 ≤ n) :
    S.pressure s ≤ Real.log (S.svfSum s n) / n := by
  obtain ⟨δ, hδ⟩ := S.exists_ratioLowerBound
  exact csInf_le ((hδ.bddBelow hs).mono (Set.image_subset_range _ _)) ⟨n, hn, rfl⟩

end Pressure

/-! ### The pressure below the exponent one through the matrix `M(s)` -/

section Transfer

variable [Fintype ι] {s ρ : ℝ} {v : ZMod 2 → ℝ}

omit [Fintype ι] in
/-- `φ^s(A_𝐢) = max{|g'_𝐣|, |g'_𝐣'|}^s` for `s ≤ 1`, where `𝐣`, `𝐣'` are the two paths of `Σ_Z`
over `𝐢`: the larger coordinate contraction to the power `s`, as in
`Example.sys`. -/
theorem svf_matWord_of_le_one (hs1 : s ≤ 1) (w : List ι) :
    svf s (S.matWord w) =
      max |S.gDeriv (S.codeWord 0 w)| |S.gDeriv (S.codeWord 1 w)| ^ s := by
  rw [matWord_eq, svf_boxMat_of_le_one hs1]

/-- The matrix `M(s)` of `Example.sys` for a general box-like system, as
an operator on vectors indexed by the two axes: its entries are
`M(s)_{c,c'} = ∑ {|g'_{(i,c)}|^s : c + o(i) = c'}`. -/
noncomputable def transfer (s : ℝ) (v : ZMod 2 → ℝ) (c : ZMod 2) : ℝ :=
  ∑ i, |S.ratio (i, c)| ^ s * v (c + S.o i)

/-- The operator `M(s)` is homogeneous. -/
theorem transfer_smul (s a : ℝ) (v : ZMod 2 → ℝ) : S.transfer s (a • v) = a • S.transfer s v := by
  funext c
  simp only [transfer, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- An eigenvector of `M(s)` is an eigenvector of `M(s)^n`. -/
theorem iterate_transfer_of_eigenvector (hv : S.transfer s v = ρ • v) (n : ℕ) :
    (S.transfer s)^[n] v = ρ ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, transfer_smul, hv, smul_smul, pow_succ]

/-- "Multiplication of these matrices records the two possible coordinate contractions of each
word", tex lines 2844 to 2845: `(M(s)^n v)(c) = ∑_{|𝐢| = n} |g'_𝐣|^s v(c + o(𝐢))`, where `𝐣` is
the path of `Σ_Z` over `𝐢` starting on the axis `c`. -/
theorem sum_abs_gDeriv_rpow_mul (s : ℝ) (n : ℕ) (v : ZMod 2 → ℝ) (c : ZMod 2) :
    ∑ w : Fin n → ι, |S.gDeriv (S.codeWord c (List.ofFn w))| ^ s *
      v (c + S.oWord (List.ofFn w)) = ((S.transfer s)^[n] v) c := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [sum_ofFn_add n 1 fun w => |S.gDeriv (S.codeWord c w)| ^ s * v (c + S.oWord w),
      Function.iterate_succ_apply, ← ih]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [transfer, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι) _ _ fun h => ?_
    simp [codeWord_append, gDeriv_append, oWord_append, abs_mul,
      Real.mul_rpow (abs_nonneg _) (abs_nonneg _), add_assoc, mul_assoc]

/-- The two-sided comparison of `Example.sys`, tex lines 2849 to 2855, for
a positive vector `v` in place of `(1, 1)`: for `0 ≤ s ≤ 1`,
`min(v) ∑_{|𝐢| = n} φ^s(A_𝐢) ≤ (1, 1) M(s)^n v ≤ 2 max(v) ∑_{|𝐢| = n} φ^s(A_𝐢)`. The factor two
compares the maximum of two terms with their sum. -/
theorem svfSum_bounds (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hvpos : ∀ c, 0 < v c) (n : ℕ) :
    min (v 0) (v 1) * S.svfSum s n ≤
        ((S.transfer s)^[n] v) 0 + ((S.transfer s)^[n] v) 1 ∧
      ((S.transfer s)^[n] v) 0 + ((S.transfer s)^[n] v) 1 ≤
        2 * max (v 0) (v 1) * S.svfSum s n := by
  have hmin : ∀ c, min (v 0) (v 1) ≤ v c := fun c => by
    rcases zmod_two_cases c with rfl | rfl
    exacts [min_le_left _ _, min_le_right _ _]
  have hmax : ∀ c, v c ≤ max (v 0) (v 1) := fun c => by
    rcases zmod_two_cases c with rfl | rfl
    exacts [le_max_left _ _, le_max_right _ _]
  have hm0 : 0 < min (v 0) (v 1) := lt_min (hvpos 0) (hvpos 1)
  rw [← S.sum_abs_gDeriv_rpow_mul s n v 0, ← S.sum_abs_gDeriv_rpow_mul s n v 1,
    ← Finset.sum_add_distrib, svfSum, Finset.mul_sum, Finset.mul_sum]
  have key : ∀ w : List ι,
      svf s (S.matWord w) ≤
          |S.gDeriv (S.codeWord 0 w)| ^ s + |S.gDeriv (S.codeWord 1 w)| ^ s ∧
        |S.gDeriv (S.codeWord 0 w)| ^ s ≤ svf s (S.matWord w) ∧
        |S.gDeriv (S.codeWord 1 w)| ^ s ≤ svf s (S.matWord w) := by
    intro w
    rw [S.svf_matWord_of_le_one hs1]
    have hx : 0 ≤ |S.gDeriv (S.codeWord 0 w)| ^ s := Real.rpow_nonneg (abs_nonneg _) _
    have hy : 0 ≤ |S.gDeriv (S.codeWord 1 w)| ^ s := Real.rpow_nonneg (abs_nonneg _) _
    refine ⟨?_, Real.rpow_le_rpow (abs_nonneg _) (le_max_left _ _) hs0,
      Real.rpow_le_rpow (abs_nonneg _) (le_max_right _ _) hs0⟩
    rcases le_total |S.gDeriv (S.codeWord 0 w)| |S.gDeriv (S.codeWord 1 w)| with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  constructor
  · refine Finset.sum_le_sum fun w _ => ?_
    obtain ⟨h1, -, -⟩ := key (List.ofFn w)
    have hx : 0 ≤ |S.gDeriv (S.codeWord 0 (List.ofFn w))| ^ s :=
      Real.rpow_nonneg (abs_nonneg _) _
    have hy : 0 ≤ |S.gDeriv (S.codeWord 1 (List.ofFn w))| ^ s :=
      Real.rpow_nonneg (abs_nonneg _) _
    have h2 := mul_le_mul_of_nonneg_left h1 hm0.le
    have h3 := mul_le_mul_of_nonneg_left (hmin (0 + S.oWord (List.ofFn w))) hx
    have h4 := mul_le_mul_of_nonneg_left (hmin (1 + S.oWord (List.ofFn w))) hy
    linarith
  · refine Finset.sum_le_sum fun w _ => ?_
    obtain ⟨-, h1, h2⟩ := key (List.ofFn w)
    have h3 := mul_le_mul h1 (hmax (0 + S.oWord (List.ofFn w))) (hvpos _).le
      (svf_nonneg s _)
    have h4 := mul_le_mul h2 (hmax (1 + S.oWord (List.ofFn w))) (hvpos _).le
      (svf_nonneg s _)
    linarith

/-- `P(𝖠, s) = log ρ(M(s))` for `0 ≤ s ≤ 1`, as in `Example.sys`, for every
box-like system: if `v` is a positive vector with `M(s) v = ρ v`, then `P(𝖠, s) = log ρ`. -/
theorem pressure_eq_log_of_eigenvector [Nonempty ι] (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hvpos : ∀ c, 0 < v c) (hv : ∀ c, S.transfer s v c = ρ * v c) :
    S.pressure s = Real.log ρ := by
  obtain ⟨δ, hδ⟩ := S.exists_ratioLowerBound
  have hρ : 0 < ρ := by
    have hpos : 0 < S.transfer s v 0 :=
      Finset.sum_pos (fun i _ => mul_pos
        (Real.rpow_pos_of_pos (abs_pos.2 (S.ratio_ne_zero _)) _) (hvpos _)) Finset.univ_nonempty
    rw [hv 0] at hpos
    exact (pos_iff_pos_of_mul_pos hpos).2 (hvpos 0)
  have hiter : ∀ n : ℕ, ((S.transfer s)^[n] v) 0 + ((S.transfer s)^[n] v) 1 =
      ρ ^ n * (v 0 + v 1) := by
    intro n
    rw [S.iterate_transfer_of_eigenvector (funext hv : S.transfer s v = ρ • v) n]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hm0 : 0 < min (v 0) (v 1) := lt_min (hvpos 0) (hvpos 1)
  have hM0 : 0 < max (v 0) (v 1) := hm0.trans_le min_le_max
  have hv01 : 0 < v 0 + v 1 := add_pos (hvpos 0) (hvpos 1)
  have hC₁ : 0 < (v 0 + v 1) / (2 * max (v 0) (v 1)) := by positivity
  have hC₂ : 0 < (v 0 + v 1) / min (v 0) (v 1) := by positivity
  have hlower : ∀ n : ℕ, 0 < n →
      Real.log ρ + Real.log ((v 0 + v 1) / (2 * max (v 0) (v 1))) / n ≤
        Real.log (S.svfSum s n) / n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : (v 0 + v 1) / (2 * max (v 0) (v 1)) * ρ ^ n ≤ S.svfSum s n := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      linarith [(S.svfSum_bounds hs0 hs1 hvpos n).2, hiter n]
    have h2 := Real.log_le_log (mul_pos hC₁ (pow_pos hρ n)) h1
    rw [Real.log_mul hC₁.ne' (pow_pos hρ n).ne', Real.log_pow] at h2
    rw [le_div_iff₀ hn', add_mul, div_mul_cancel₀ _ hn'.ne']
    linarith
  have hupper : ∀ n : ℕ, 0 < n →
      Real.log (S.svfSum s n) / n ≤
        Real.log ρ + Real.log ((v 0 + v 1) / min (v 0) (v 1)) / n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : S.svfSum s n ≤ (v 0 + v 1) / min (v 0) (v 1) * ρ ^ n := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hm0]
      linarith [(S.svfSum_bounds hs0 hs1 hvpos n).1, hiter n]
    have h2 := Real.log_le_log (hδ.svfSum_pos hs0 n) h1
    rw [Real.log_mul hC₂.ne' (pow_pos hρ n).ne', Real.log_pow] at h2
    rw [div_le_iff₀ hn', add_mul, div_mul_cancel₀ _ hn'.ne']
    linarith
  have hlim : ∀ C : ℝ, Tendsto (fun n : ℕ => Real.log ρ + C / n) atTop (𝓝 (Real.log ρ)) := by
    intro C
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat C)
  exact tendsto_nhds_unique (hδ.tendsto_pressure hs0)
    (tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim _) (hlim _)
      ((eventually_gt_atTop 0).mono hlower) ((eventually_gt_atTop 0).mono hupper))

end Transfer

/-! ### `thm:main1` and `thm:main2` below the exponent one -/

section MainOne

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] {s : ℝ}

/-- `thm:main1` for `0 < s ≤ 1`, as used in `Example.sys` and in the first
case of the proof of `thm:main1`. The equilibrium identity reads `h_0(μ) = -s λ_1(𝖠, μ)`, so
the two pointwise dimensions of the coordinate marginals are `s` and
`s λ_1(𝖠, μ)/λ_2(𝖠, μ)`. They are distinct because `λ_2(𝖠, μ) < λ_1(𝖠, μ) < 0`, both occur on
sets of positive measure, so the marginal is double-dimensional and not exact-dimensional. The
threshold
`s < 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)` of `thm:main1` holds for every `s ≤ 1`, as the proof of
`thm:main1` notes. -/
theorem main1_of_le_one (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hjr : JordanRapaportDimension.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (hs0 : 0 < s) (hs1 : s ≤ 1) (hP : S.pressure s = 0)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) (c : ZMod 2) :
    HasLocalDimPair (S.marginal c μ) s (s * (S.lyapunov₁ μ / S.lyapunov₂ μ)) ∧
      s * (S.lyapunov₁ μ / S.lyapunov₂ μ) < s ∧
      s < 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∧
      0 < S.marginal c μ {x | HasLocalDim (S.marginal c μ) x s} ∧
      0 < S.marginal c μ
        {x | HasLocalDim (S.marginal c μ) x (s * (S.lyapunov₁ μ / S.lyapunov₂ μ))} ∧
      IsDoubleDim (S.marginal c μ) ∧
      ¬ ∃ d, IsExactDim (S.marginal c μ) d := by
  have hs2 : s < 2 := by linarith
  obtain ⟨ν₁, ν₂, hf₁, hf₂, hne₁, hne₂, hsum, hd₁, hd₂⟩ :=
    S.marginal_decomposition hfk hfjj hjr hrot hprox hsep hs0 hs2 μ hinv heq c
  have hl := S.simple_lyapunov hms hrot hprox hs0 hs2 μ hinv heq
  have hl1 := S.lyapunov₁_neg hinv
  have hl2 : S.lyapunov₂ μ < 0 := hl.trans hl1
  have henergy : entropy μ + energy (S.lyapunov₁ μ) (S.lyapunov₂ μ) s = 0 := by
    rw [← heq.pressure_eq hinv hs0.le, hP]
  have hh : entropy μ = -(s * S.lyapunov₁ μ) := by
    rw [energy, ite_eq_left hs1] at henergy
    linarith
  have hratio : S.lyapunov₁ μ / S.lyapunov₂ μ < 1 := by
    rw [div_lt_one_of_neg hl2]
    exact hl
  have hlt : s * (S.lyapunov₁ μ / S.lyapunov₂ μ) < s := by
    have := mul_lt_mul_of_pos_left hratio hs0
    linarith
  have e₁ : min 1 (-entropy μ / S.lyapunov₁ μ) = s := by
    rw [hh, neg_neg, mul_div_assoc, div_self hl1.ne, mul_one, min_eq_right hs1]
  have e₂ : min 1 (-entropy μ / S.lyapunov₂ μ) = s * (S.lyapunov₁ μ / S.lyapunov₂ μ) := by
    rw [hh, neg_neg, mul_div_assoc, min_eq_right (by linarith)]
  rw [e₁] at hd₁
  rw [e₂] at hd₂
  rw [hsum]
  refine ⟨hd₁.hasLocalDimPair_add hd₂, hlt, by linarith,
    hd₁.measure_hasLocalDim_add_left_pos hne₁, hd₂.measure_hasLocalDim_add_right_pos hne₂,
    hd₁.isDoubleDim_add hd₂ hne₁ hne₂ hlt.ne', ?_⟩
  rw [isExactDim_add_iff hd₁ hd₂ hne₁ hne₂]
  exact hlt.ne'

/-- `thm:main2` for `dimaff(X) ≤ 1`: the alternative `dimaff(X) ≤ 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)` holds
for every such `X`, because `λ_2(𝖠, μ) < λ_1(𝖠, μ) < 0` gives `λ_1(𝖠, μ)/λ_2(𝖠, μ) < 1`. Hence
`\dim_H(X) = dimaff(X)` without a separation condition on the planar system. -/
theorem main2_of_le_one (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hjr : JordanRapaportDimension.{u})
    (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u}) (hly : FengLedrappierYoung.{u})
    (hlyb : FengLedrappierYoungBar.{u}) [Nonempty ι] (hrot : S.WithRotations)
    (hprox : S.Proximal) (hsep : S.ProjExpSeparation) (h1 : S.dimaff ≤ 1)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ) : dimH S.attractor = ENNReal.ofReal S.dimaff := by
  have := S.nontrivial_of_withRotations hrot
  have hl := S.simple_lyapunov hms hrot hprox S.dimaff_pos (by linarith) μ hinv heq
  have hl2 : S.lyapunov₂ μ < 0 := hl.trans (S.lyapunov₁_neg hinv)
  have hratio : S.lyapunov₁ μ / S.lyapunov₂ μ < 1 := by
    rw [div_lt_one_of_neg hl2]
    exact hl
  exact S.main2 hms hfk hfjj hjr hfi hfib hly hlyb hrot hprox hsep (by linarith) μ hinv heq
    (Or.inl (by linarith))

end MainOne

/-! ### The supports of the coordinate marginals -/

/-- The coordinate functions `proj_x` and `proj_y` are measurable. -/
theorem measurable_coord (c : ZMod 2) : Measurable (coord c) := by
  unfold coord
  split_ifs <;> fun_prop

/-- The coordinate marginal `(proj_c)_*(π_*μ)` gives no mass to a Borel set that does not meet
`proj_c(X)`. -/
theorem marginal_eq_zero_of_disjoint [Finite ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (c : ZMod 2) (μ : Measure (ℤ → ι)) {A : Set ℝ} (hA : MeasurableSet A)
    (hdisj : Disjoint A (coord c '' S.attractor)) : S.marginal c μ A = 0 := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  rw [marginal, Measure.map_apply (measurable_coord c) hA,
    Measure.map_apply hS.measurable_proj (measurable_coord c hA)]
  convert measure_empty (μ := μ)
  ext x
  simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
  exact fun hx => Set.disjoint_left.1 hdisj hx ⟨S.proj x, ⟨x, rfl⟩, rfl⟩

end System

/-! ### The example -/

namespace Example

open BoxLike.System
open scoped Matrix

/-- The system `Φ = (φ_1, φ_2)` of `Example.sys`, over the alphabet
`Fin 2`: the index `0` is the diagonal map `φ_1` and the index `1` is the anti-diagonal map
`φ_2`. -/
noncomputable def sys : System (Fin 2) where
  o := ![0, 1]
  a := ![1 / 10, 1 / 30]
  b := ![1 / 20, 1 / 40]
  v := ![(0, 3 / 5), (3 / 10, 9 / 10)]
  a_ne_zero i := by fin_cases i <;> norm_num
  b_ne_zero i := by fin_cases i <;> norm_num
  abs_a_lt_one i := by fin_cases i <;> norm_num [abs_lt]
  abs_b_lt_one i := by fin_cases i <;> norm_num [abs_lt]

/-- The first map of `Example.sys`: `φ_1(x, y) = (x/10, y/20 + 3/5)`. -/
@[simp] theorem sys_phi_zero (z : ℝ × ℝ) : sys.phi 0 z = (z.1 / 10, z.2 / 20 + 3 / 5) := by
  ext <;> simp [System.phi, sys] <;> ring

/-- The second map of `Example.sys`:
`φ_2(x, y) = (y/30 + 3/10, x/40 + 9/10)`. -/
@[simp] theorem sys_phi_one (z : ℝ × ℝ) :
    sys.phi 1 z = (z.2 / 30 + 3 / 10, z.1 / 40 + 9 / 10) := by
  ext <;> simp [System.phi, sys, show (1 : ZMod 2) + 1 = 0 from by decide] <;> ring

/-- The linear part `A_1 = diag(1/10, 1/20)` of `Example.sys`. -/
@[simp] theorem sys_mat_zero : sys.mat 0 = !![1 / 10, 0; 0, 1 / 20] := rfl

/-- The anti-diagonal linear part `A_2` of `Example.sys`. -/
@[simp] theorem sys_mat_one : sys.mat 1 = !![0, 1 / 30; 1 / 40, 0] := rfl

/-- The first map `g_1(t) = t/10` of the projective system of
`Example.sys`. -/
@[simp] theorem sys_g_zero_zero (t : ℝ) : sys.g (0, 0) t = t / 10 := by
  simp [System.g, System.trans, sys]; ring

/-- The second map `g_2(t) = t/30 + 3/10` of the projective system of
`Example.sys`. -/
@[simp] theorem sys_g_one_zero (t : ℝ) : sys.g (1, 0) t = t / 30 + 3 / 10 := by
  simp [System.g, System.trans, sys]; ring

/-- The third map `g_3(t) = t/20 + 3/5` of the projective system of
`Example.sys`. -/
@[simp] theorem sys_g_zero_one (t : ℝ) : sys.g (0, 1) t = t / 20 + 3 / 5 := by
  simp [System.g, System.trans, sys]; ring

/-- The fourth map `g_4(t) = t/40 + 9/10` of the projective system of
`Example.sys`. -/
@[simp] theorem sys_g_one_one (t : ℝ) : sys.g (1, 1) t = t / 40 + 9 / 10 := by
  simp [System.g, System.trans, sys]; ring

/-! ### Rotations, proximality, irreducibility -/

/-- The tuple of `Example.sys` is box-like with rotations: `A_1` is
diagonal and `A_2` is anti-diagonal. -/
theorem withRotations : sys.WithRotations := ⟨⟨0, rfl⟩, ⟨1, rfl⟩⟩

/-- The tuple of `Example.sys` contains the proximal diagonal generator
`A_1 = diag(1/10, 1/20)`. -/
theorem hasProximalDiagonal : sys.HasProximalDiagonal := by
  refine ⟨0, rfl, ?_⟩
  simp only [sys, Matrix.cons_val_zero]
  norm_num [abs_of_pos]

/-- The matrix `A_1` of `Example.sys` is proximal. -/
theorem isProximalMatrix_mat_zero : IsProximalMatrix (sys.mat 0) := by
  have h : sys.mat 0 = boxMat 0 (1 / 10) (1 / 20) := rfl
  rw [h, isProximalMatrix_boxMat_zero]
  norm_num [abs_of_pos]

/-- The tuple of `Example.sys` is proximal. -/
theorem proximal : sys.Proximal := hasProximalDiagonal.proximal

/-- The tuple of `Example.sys` is irreducible: the only invariant lines of
`A_1` are the coordinate axes and `A_2` interchanges them. -/
theorem irreducible : sys.Irreducible :=
  irreducible_of_hasProximalDiagonal withRotations hasProximalDiagonal

/-! ### Strong separation -/

/-- The unit square `[0,1]²`. -/
def square : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1

/-- The image `φ_1([0,1]²) = [0, 1/10] × [3/5, 13/20]` of `Example.sys`. -/
theorem phi_zero_image_square :
    sys.phi 0 '' square = Set.Icc (0 : ℝ) (1 / 10) ×ˢ Set.Icc (3 / 5 : ℝ) (13 / 20) := by
  ext z
  simp only [square, Set.mem_image, Set.mem_prod, Set.mem_Icc, sys_phi_zero]
  constructor
  · rintro ⟨w, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> dsimp only <;> linarith
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨(10 * z.1, 20 * (z.2 - 3 / 5)), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · dsimp only; linarith
    · dsimp only; linarith
    · dsimp only; linarith
    · dsimp only; linarith
    · ext <;> dsimp only <;> ring

/-- The image `φ_2([0,1]²) = [3/10, 1/3] × [9/10, 37/40]` of
`Example.sys`. -/
theorem phi_one_image_square :
    sys.phi 1 '' square = Set.Icc (3 / 10 : ℝ) (1 / 3) ×ˢ Set.Icc (9 / 10 : ℝ) (37 / 40) := by
  ext z
  simp only [square, Set.mem_image, Set.mem_prod, Set.mem_Icc, sys_phi_one]
  constructor
  · rintro ⟨w, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> dsimp only <;> linarith
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨(40 * (z.2 - 9 / 10), 30 * (z.1 - 3 / 10)), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · dsimp only; linarith
    · dsimp only; linarith
    · dsimp only; linarith
    · dsimp only; linarith
    · ext <;> dsimp only <;> ring

/-- Both maps of `Example.sys` send `[0,1]²` into itself. -/
theorem phi_image_square_subset (i : Fin 2) : sys.phi i '' square ⊆ square := by
  revert i
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · rw [phi_zero_image_square]
    exact Set.prod_mono (Set.Icc_subset_Icc le_rfl (by norm_num))
      (Set.Icc_subset_Icc (by norm_num) (by norm_num))
  · rw [phi_one_image_square]
    exact Set.prod_mono (Set.Icc_subset_Icc (by norm_num) (by norm_num))
      (Set.Icc_subset_Icc (by norm_num) (by norm_num))

/-- The two image rectangles of `Example.sys` are disjoint. -/
theorem disjoint_phi_image_square : Disjoint (sys.phi 0 '' square) (sys.phi 1 '' square) := by
  rw [phi_zero_image_square, phi_one_image_square]
  refine Set.disjoint_left.2 fun z hz hz' => ?_
  have h1 : z.1 ≤ 1 / 10 := hz.1.2
  have h2 : 3 / 10 ≤ z.1 := hz'.1.1
  linarith

/-- The unit square is compact. -/
theorem isCompact_square : IsCompact square := isCompact_Icc.prod isCompact_Icc

/-- The unit square is non-empty. -/
theorem square_nonempty : square.Nonempty :=
  ⟨(0, 0), ⟨Set.left_mem_Icc.2 zero_le_one, Set.left_mem_Icc.2 zero_le_one⟩⟩

/-- The self-affine set of `Example.sys` lies in `[0,1]²`. -/
theorem attractor_subset_square : sys.attractor ⊆ square :=
  sys.attractor_subset_of_invariant isCompact_square square_nonempty phi_image_square_subset

/-- The planar system of `Example.sys` satisfies the strong separation
condition. -/
theorem strongSeparation : sys.StrongSeparation := by
  refine sys.strongSeparation_of_invariant isCompact_square square_nonempty
    phi_image_square_subset ?_
  have key : ∀ i j : Fin 2, i ≠ j → Disjoint (sys.phi i '' square) (sys.phi j '' square) :=
    Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨fun h => absurd rfl h,
      fun _ => disjoint_phi_image_square⟩, Fin.forall_fin_two.2
      ⟨fun _ => disjoint_phi_image_square.symm, fun h => absurd rfl h⟩⟩
  exact fun i j hij => key i j hij

/-- The planar system of `Example.sys` satisfies the strong open set
condition. -/
theorem strongOpenSet : sys.StrongOpenSet := strongSeparation.strongOpenSet

/-! ### Projective exponential separation -/

/-- The four symbols of the projective system of `Example.sys`. -/
theorem symbol_cases (p : Fin 2 × ZMod 2) :
    p = (0, 0) ∨ p = (1, 0) ∨ p = (0, 1) ∨ p = (1, 1) := by
  revert p; decide

/-- Every contraction ratio of the projective system of `Example.sys` is
at least `1/40`. -/
theorem ratioLowerBound : sys.RatioLowerBound (1 / 40) := by
  refine ⟨by norm_num, fun p => ?_⟩
  rcases symbol_cases p with rfl | rfl | rfl | rfl <;>
    simp only [ratio_zero, ratio_one, sys, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    norm_num [abs_of_pos]

/-- The four maps of the projective system of `Example.sys` send `[0,1]`
into itself. -/
theorem g_mem_Icc (p : Fin 2 × ZMod 2) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    sys.g p t ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := ht
  rcases symbol_cases p with rfl | rfl | rfl | rfl <;>
    simp only [sys_g_zero_zero, sys_g_one_zero, sys_g_zero_one, sys_g_one_one, Set.mem_Icc] <;>
    constructor <;> linarith

/-- The images of `[0,1]` under the four maps of the projective system of
`Example.sys`, namely `[0, 1/10]`, `[3/10, 1/3]`, `[3/5, 13/20]` and
`[9/10, 37/40]`, are pairwise at distance at least `1/5`. -/
theorem le_abs_g_sub (p q : Fin 2 × ZMod 2) (hpq : p ≠ q) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (t' : ℝ) (ht' : t' ∈ Set.Icc (0 : ℝ) 1) : 1 / 5 ≤ |sys.g p t - sys.g q t'| := by
  obtain ⟨h0, h1⟩ := ht
  obtain ⟨h0', h1'⟩ := ht'
  rcases symbol_cases p with rfl | rfl | rfl | rfl <;>
    rcases symbol_cases q with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl hpq
    | (simp only [sys_g_zero_zero, sys_g_one_zero, sys_g_zero_one, sys_g_one_one]
       exact le_abs.2 (Or.inl (by linarith)))
    | (simp only [sys_g_zero_zero, sys_g_one_zero, sys_g_zero_one, sys_g_one_one]
       exact le_abs.2 (Or.inr (by linarith)))

/-- The gap bound `Δ_n^Ψ ≥ 40^{1-n}/5` for every `n ≥ 1` of
`Example.sys`. -/
theorem le_gap {n : ℕ} (hn : 1 ≤ n) :
    ENNReal.ofReal ((40 : ℝ) ^ (1 - (n : ℤ)) / 5) ≤ sys.gap n := by
  have h := System.le_gap (by norm_num : (0 : ℝ) ≤ 1 / 5) ratioLowerBound
    (Set.left_mem_Icc.2 zero_le_one) g_mem_Icc le_abs_g_sub n
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have e : (40 : ℝ) ^ (1 - ((m + 1 : ℕ) : ℤ)) / 5 = 1 / 5 * (1 / 40) ^ (m + 1 - 1) := by
    rw [Nat.add_sub_cancel, show (1 : ℤ) - ((m + 1 : ℕ) : ℤ) = -(m : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast, one_div, one_div, inv_pow]
    ring
  rw [e]
  exact h

/-- The system of `Example.sys` satisfies the projective exponential
separation condition. -/
theorem projExpSeparation : sys.ProjExpSeparation :=
  System.projExpSeparation_of_le_abs (by norm_num : (0 : ℝ) < 1 / 5) ratioLowerBound
    (Set.left_mem_Icc.2 zero_le_one) g_mem_Icc le_abs_g_sub

/-! ### The affinity dimension lies in `(0, 1)` -/

/-- `P(𝖠, 1) ≤ log ∑_i ‖A_i‖ = log(1/10 + 1/30) = log(2/15)` for the tuple of
`Example.sys`. The same bound holds for `ρ(M(1))`. -/
theorem pressure_one_le : sys.pressure 1 ≤ Real.log (2 / 15) := by
  have h := sys.pressure_le zero_le_one (le_refl 1)
  rw [System.svfSum_one, Fin.sum_univ_two, Nat.cast_one, div_one] at h
  have e0 : svf 1 (sys.mat 0) = 1 / 10 := by
    have hm : sys.mat 0 = boxMat 0 (1 / 10) (1 / 20) := rfl
    rw [hm, svf_boxMat_of_le_one le_rfl, Real.rpow_one]
    norm_num [abs_of_pos]
  have e1 : svf 1 (sys.mat 1) = 1 / 30 := by
    have hm : sys.mat 1 = boxMat 1 (1 / 30) (1 / 40) := rfl
    rw [hm, svf_boxMat_of_le_one le_rfl, Real.rpow_one]
    norm_num [abs_of_pos]
  rw [e0, e1] at h
  norm_num at h ⊢
  exact h

/-- The affinity dimension of `Example.sys` lies in `(0, 1)`. -/
theorem dimaff_pos_lt_one : 0 < sys.dimaff ∧ sys.dimaff < 1 := by
  refine ⟨sys.dimaff_pos, ?_⟩
  by_contra hlt
  have h1 : (1 : ℝ) ≤ sys.dimaff := not_lt.1 hlt
  have h := sys.strictAntiOn_pressure.antitoneOn (Set.mem_Ici.2 zero_le_one)
    (Set.mem_Ici.2 sys.dimaff_nonneg) h1
  rw [sys.pressure_dimaff] at h
  have hneg : Real.log (2 / 15) < 0 := Real.log_neg (by norm_num) (by norm_num)
  linarith [pressure_one_le]

/-! ### The conclusion of the example -/

/-- The projection-dimension conclusion for `Example.sys`. Let `μ` be an invariant
`s`-equilibrium state for `s = dimaff(X)`. The pointwise dimension of each coordinate marginal
of `μ` is `s` or `s λ_1(𝖠, μ)/λ_2(𝖠, μ)` almost everywhere. These values are distinct, the
threshold `s < 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)` of `thm:main1` holds, both values occur on sets of
positive marginal measure, so the marginal is double-dimensional and not exact-dimensional. -/
theorem marginal_doubleDim (hms : MorrisShmerkinLyapunov.{0}) (hfk : EquilibriumGibbsStatement.{0})
    (hfjj : FraserJordanJurgaDecomposition.{0}) (hjr : JordanRapaportDimension.{0})
    (μ : Measure (ℤ → Fin 2)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : sys.IsEquilibriumState sys.dimaff μ)
    (c : ZMod 2) :
    HasLocalDimPair (sys.marginal c μ) sys.dimaff
        (sys.dimaff * (sys.lyapunov₁ μ / sys.lyapunov₂ μ)) ∧
      sys.dimaff * (sys.lyapunov₁ μ / sys.lyapunov₂ μ) < sys.dimaff ∧
      sys.dimaff < 2 - sys.lyapunov₁ μ / sys.lyapunov₂ μ ∧
      0 < sys.marginal c μ {x | HasLocalDim (sys.marginal c μ) x sys.dimaff} ∧
      0 < sys.marginal c μ {x | HasLocalDim (sys.marginal c μ) x
        (sys.dimaff * (sys.lyapunov₁ μ / sys.lyapunov₂ μ))} ∧
      IsDoubleDim (sys.marginal c μ) ∧
      ¬ ∃ d, IsExactDim (sys.marginal c μ) d :=
  sys.main1_of_le_one hms hfk hfjj hjr withRotations proximal projExpSeparation
    dimaff_pos_lt_one.1 dimaff_pos_lt_one.2.le sys.pressure_dimaff μ hinv heq c

/-- `\dim_H(X) = dimaff(X)` for the self-affine set of `Example.sys`, from
`thm:main2`, given an invariant `s`-equilibrium state `μ` for `s = dimaff(X)`. The first
alternative of `thm:main2` holds because `dimaff(X) < 1`. -/
theorem dimH_attractor (hms : MorrisShmerkinLyapunov.{0}) (hfk : EquilibriumGibbsStatement.{0})
    (hfjj : FraserJordanJurgaDecomposition.{0}) (hjr : JordanRapaportDimension.{0})
    (hfi : FengInfoSum.{0}) (hfib : FengInfoSumBar.{0}) (hly : FengLedrappierYoung.{0})
    (hlyb : FengLedrappierYoungBar.{0}) (μ : Measure (ℤ → Fin 2)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : sys.IsEquilibriumState sys.dimaff μ) :
    dimH sys.attractor = ENNReal.ofReal sys.dimaff :=
  sys.main2_of_le_one hms hfk hfjj hjr hfi hfib hly hlyb withRotations proximal
    projExpSeparation dimaff_pos_lt_one.2.le μ hinv heq

/-! ### The supports of the two marginals -/

/-- The self-affine set of `Example.sys` lies in the union of the two image
rectangles. -/
theorem attractor_subset_union :
    sys.attractor ⊆ Set.Icc (0 : ℝ) (1 / 10) ×ˢ Set.Icc (3 / 5 : ℝ) (13 / 20) ∪
      Set.Icc (3 / 10 : ℝ) (1 / 3) ×ˢ Set.Icc (9 / 10 : ℝ) (37 / 40) := by
  intro z hz
  rw [sys.attractor_eq_iUnion] at hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
  have hi' := Set.image_mono attractor_subset_square hi
  revert hi' hi
  revert i
  refine Fin.forall_fin_two.2 ⟨fun _ h => Or.inl ?_, fun _ h => Or.inr ?_⟩
  · rwa [phi_zero_image_square] at h
  · rwa [phi_one_image_square] at h

/-- `proj_x(X) ⊆ [0, 1/3]` in `Example.sys`. -/
theorem coord_zero_attractor_subset : coord 0 '' sys.attractor ⊆ Set.Icc (0 : ℝ) (1 / 3) := by
  rintro _ ⟨z, hz, rfl⟩
  rcases attractor_subset_union hz with h | h
  · exact ⟨h.1.1, h.1.2.trans (by norm_num)⟩
  · exact ⟨le_trans (by norm_num) h.1.1, h.1.2⟩

/-- `proj_y(X) ⊆ [3/5, 37/40]` in `Example.sys`. -/
theorem coord_one_attractor_subset :
    coord 1 '' sys.attractor ⊆ Set.Icc (3 / 5 : ℝ) (37 / 40) := by
  rintro _ ⟨z, hz, rfl⟩
  rcases attractor_subset_union hz with h | h
  · exact ⟨h.2.1, h.2.2.trans (by norm_num)⟩
  · exact ⟨le_trans (by norm_num) h.2.1, h.2.2⟩

/-- The marginal `(proj_x)_*(π_*μ)` of `Example.sys` is carried by
`[0, 1/3]`, for every measure `μ` on `Σ`. -/
theorem marginal_zero_compl_Icc (μ : Measure (ℤ → Fin 2)) :
    sys.marginal 0 μ (Set.Icc (0 : ℝ) (1 / 3))ᶜ = 0 :=
  sys.marginal_eq_zero_of_disjoint 0 μ measurableSet_Icc.compl
    ((disjoint_compl_left (a := Set.Icc (0 : ℝ) (1 / 3))).mono_right
      coord_zero_attractor_subset)

/-- The marginal `(proj_y)_*(π_*μ)` of `Example.sys` is carried by
`[3/5, 37/40]`, for every measure `μ` on `Σ`. -/
theorem marginal_one_compl_Icc (μ : Measure (ℤ → Fin 2)) :
    sys.marginal 1 μ (Set.Icc (3 / 5 : ℝ) (37 / 40))ᶜ = 0 :=
  sys.marginal_eq_zero_of_disjoint 1 μ measurableSet_Icc.compl
    ((disjoint_compl_left (a := Set.Icc (3 / 5 : ℝ) (37 / 40))).mono_right
      coord_one_attractor_subset)

/-- The two coordinate marginals of `Example.sys` have disjoint supports:
they are mutually singular, for every measure `μ` on `Σ`. -/
theorem mutuallySingular_marginal (μ : Measure (ℤ → Fin 2)) :
    sys.marginal 0 μ ⟂ₘ sys.marginal 1 μ := by
  refine ⟨(Set.Icc (0 : ℝ) (1 / 3))ᶜ, measurableSet_Icc.compl, marginal_zero_compl_Icc μ, ?_⟩
  · rw [compl_compl]
    refine sys.marginal_eq_zero_of_disjoint 1 μ measurableSet_Icc ?_
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    have h1 : x ≤ 1 / 3 := hx.2
    have h2 : 3 / 5 ≤ x := (coord_one_attractor_subset hx').1
    linarith

/-! ### The pressure and the characteristic equation -/

/-- The matrix `M(t)` of `Example.sys`. -/
noncomputable def M (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(10 : ℝ) ^ (-t), (30 : ℝ) ^ (-t); (40 : ℝ) ^ (-t), (20 : ℝ) ^ (-t)]

/-- The larger root `(p + q + √((p - q)² + 4e)) / 2` of `(x - p)(x - q) = e`. -/
noncomputable def perron (p q e : ℝ) : ℝ := (p + q + Real.sqrt ((p - q) ^ 2 + 4 * e)) / 2

/-- The number `perron p q e` solves `(x - p)(x - q) = e` and exceeds `p` and `q`, for
`e > 0`. -/
theorem perron_spec {p q e : ℝ} (he : 0 < e) :
    (perron p q e - p) * (perron p q e - q) = e ∧ p < perron p q e ∧ q < perron p q e := by
  have hD : 0 ≤ (p - q) ^ 2 + 4 * e := by positivity
  have hsq : Real.sqrt ((p - q) ^ 2 + 4 * e) ^ 2 = (p - q) ^ 2 + 4 * e := Real.sq_sqrt hD
  have hlt : |p - q| < Real.sqrt ((p - q) ^ 2 + 4 * e) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  have h1 := (abs_lt.1 hlt).1
  have h2 := (abs_lt.1 hlt).2
  refine ⟨?_, ?_, ?_⟩
  · unfold perron
    linear_combination (1 / 4 : ℝ) * hsq
  · unfold perron; linarith
  · unfold perron; linarith

/-- The spectral radius `ρ(M(t))` of `Example.sys` in closed form: the
larger root of the characteristic polynomial of `M(t)`. -/
noncomputable def perronRoot (t : ℝ) : ℝ :=
  perron ((10 : ℝ) ^ (-t)) ((20 : ℝ) ^ (-t)) ((30 : ℝ) ^ (-t) * (40 : ℝ) ^ (-t))

/-- `|1/x|^t = x^{-t}` for `x > 0`. -/
theorem abs_one_div_rpow {x : ℝ} (hx : 0 < x) (t : ℝ) : |1 / x| ^ t = x ^ (-t) := by
  rw [abs_of_pos (by positivity), one_div, Real.inv_rpow hx.le, Real.rpow_neg hx.le]

/-- The first row of `M(t)` of `Example.sys` as an operator. -/
theorem transfer_zero (t : ℝ) (v : ZMod 2 → ℝ) :
    sys.transfer t v 0 = (10 : ℝ) ^ (-t) * v 0 + (30 : ℝ) ^ (-t) * v 1 := by
  have r00 : |sys.ratio (0, 0)| ^ t = (10 : ℝ) ^ (-t) := abs_one_div_rpow (by norm_num) t
  have r10 : |sys.ratio (1, 0)| ^ t = (30 : ℝ) ^ (-t) := abs_one_div_rpow (by norm_num) t
  have o0 : sys.o 0 = 0 := rfl
  have o1 : sys.o 1 = 1 := rfl
  rw [System.transfer, Fin.sum_univ_two, r00, r10, o0, o1, add_zero, zero_add]

/-- The second row of `M(t)` of `Example.sys` as an operator. -/
theorem transfer_one (t : ℝ) (v : ZMod 2 → ℝ) :
    sys.transfer t v 1 = (40 : ℝ) ^ (-t) * v 0 + (20 : ℝ) ^ (-t) * v 1 := by
  have r01 : |sys.ratio (0, 1)| ^ t = (20 : ℝ) ^ (-t) := abs_one_div_rpow (by norm_num) t
  have r11 : |sys.ratio (1, 1)| ^ t = (40 : ℝ) ^ (-t) := abs_one_div_rpow (by norm_num) t
  have o0 : sys.o 0 = 0 := rfl
  have o1 : sys.o 1 = 1 := rfl
  rw [System.transfer, Fin.sum_univ_two, r01, r11, o0, o1, add_zero,
    show (1 : ZMod 2) + 1 = 0 by decide, add_comm]

/-- The operator `System.transfer` of the system of `Example.sys` is the
matrix `M(t)` of the article. -/
theorem transfer_eq_mulVec (t : ℝ) (v : ZMod 2 → ℝ) :
    ![sys.transfer t v 0, sys.transfer t v 1] = M t *ᵥ ![v 0, v 1] := by
  ext i
  fin_cases i <;>
    simp [M, transfer_zero, transfer_one, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The iterates of `System.transfer` are the powers `M(t)^n`. -/
theorem iterate_transfer_eq_mulVec (t : ℝ) (n : ℕ) (v : ZMod 2 → ℝ) :
    ![((sys.transfer t)^[n] v) 0, ((sys.transfer t)^[n] v) 1] = M t ^ n *ᵥ ![v 0, v 1] := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, transfer_eq_mulVec, Matrix.mulVec_mulVec, pow_succ]

/-- The comparison of singular-value sums and transfer-matrix powers for `Example.sys`:
`∑_{|𝐢| = n} φ^t(A_𝐢) ≤ (1, 1) M(t)^n (1, 1)ᵀ ≤ 2 ∑_{|𝐢| = n} φ^t(A_𝐢)` for `0 ≤ t ≤ 1`. -/
theorem svfSum_le_mulVec {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) :
    sys.svfSum t n ≤ ![1, 1] ⬝ᵥ (M t ^ n *ᵥ ![1, 1]) ∧
      ![1, 1] ⬝ᵥ (M t ^ n *ᵥ ![1, 1]) ≤ 2 * sys.svfSum t n := by
  have h := sys.svfSum_bounds (v := fun _ => 1) ht0 ht1 (fun _ => one_pos) n
  have e := iterate_transfer_eq_mulVec t n fun _ => 1
  have e' : ![1, 1] ⬝ᵥ (M t ^ n *ᵥ ![1, 1]) =
      ((sys.transfer t)^[n] fun _ => 1) 0 + ((sys.transfer t)^[n] fun _ => 1) 1 := by
    rw [← e]
    simp [dotProduct, Fin.sum_univ_two]
  rw [e']
  simpa using h

/-- `P(𝖠, t) = log ρ(M(t))` for `0 ≤ t ≤ 1` in `Example.sys`, with the
spectral radius in closed form. The positive eigenvector of `M(t)` is
`(30^{-t}, ρ(M(t)) - 10^{-t})`. -/
theorem pressure_eq_log_perronRoot {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    sys.pressure t = Real.log (perronRoot t) := by
  have he : 0 < (30 : ℝ) ^ (-t) * (40 : ℝ) ^ (-t) := by positivity
  obtain ⟨hchar, hp, -⟩ := perron_spec (p := (10 : ℝ) ^ (-t)) (q := (20 : ℝ) ^ (-t)) he
  refine sys.pressure_eq_log_of_eigenvector
    (v := fun c => if c = 0 then (30 : ℝ) ^ (-t) else perronRoot t - (10 : ℝ) ^ (-t)) ht0 ht1
    (fun c => ?_) fun c => ?_
  · split_ifs
    · positivity
    · exact sub_pos.2 hp
  · rcases zmod_two_cases c with rfl | rfl
    · rw [transfer_zero]
      simp only [ite_true, ite_eq_right (show (1 : ZMod 2) ≠ 0 by decide)]
      ring
    · rw [transfer_one]
      simp only [ite_true, ite_eq_right (show (1 : ZMod 2) ≠ 0 by decide)]
      unfold perronRoot
      linear_combination -hchar

/-- The spectral radius `ρ(M(t))` is positive. -/
theorem perronRoot_pos (t : ℝ) : 0 < perronRoot t := by
  have he : 0 < (30 : ℝ) ^ (-t) * (40 : ℝ) ^ (-t) := by positivity
  have hp0 : 0 < (10 : ℝ) ^ (-t) := by positivity
  exact hp0.trans (perron_spec he).2.1

/-- The spectrum of `M(t)` consists of the roots of its characteristic polynomial. -/
theorem mem_spectrum_M (t k : ℝ) :
    k ∈ spectrum ℝ (M t) ↔
      (k - (10 : ℝ) ^ (-t)) * (k - (20 : ℝ) ^ (-t)) = (30 : ℝ) ^ (-t) * (40 : ℝ) ^ (-t) := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    Matrix.algebraMap_eq_diagonal, Matrix.det_fin_two]
  simp only [M, Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, ne_eq, zero_ne_one, one_ne_zero,
    not_false_eq_true, Matrix.diagonal_apply_ne, zero_sub]
  constructor <;> intro h <;> linarith

/-- The spectral radius of `M(t)` in `Example.sys` is the larger root of
its characteristic polynomial. -/
theorem spectralRadius_M (t : ℝ) : spectralRadius ℝ (M t) = ENNReal.ofReal (perronRoot t) := by
  have he : 0 < (30 : ℝ) ^ (-t) * (40 : ℝ) ^ (-t) := by positivity
  obtain ⟨hchar, hp, hq⟩ := perron_spec (p := (10 : ℝ) ^ (-t)) (q := (20 : ℝ) ^ (-t)) he
  have hp0 : 0 < (10 : ℝ) ^ (-t) := by positivity
  have hq0 : 0 < (20 : ℝ) ^ (-t) := by positivity
  have hr : 0 < perronRoot t := perronRoot_pos t
  rw [spectralRadius_eq_of_unital]
  refine le_antisymm (iSup₂_le fun k hk => ?_) ?_
  · rw [mem_spectrum_M] at hk
    have hfac : (k - perronRoot t) *
        (k - ((10 : ℝ) ^ (-t) + (20 : ℝ) ^ (-t) - perronRoot t)) = 0 := by
      unfold perronRoot
      linear_combination hk - hchar
    rw [← enorm_eq_nnnorm, Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    rcases mul_eq_zero.1 hfac with h | h
    · rw [sub_eq_zero.1 h, abs_of_pos hr]
    · rw [sub_eq_zero.1 h, abs_le]
      unfold perronRoot
      constructor <;> linarith
  · have hmem : perronRoot t ∈ spectrum ℝ (M t) := (mem_spectrum_M t _).2 hchar
    refine le_trans ?_ (le_iSup₂ (f := fun k _ => (‖k‖₊ : ℝ≥0∞)) (perronRoot t) hmem)
    rw [← enorm_eq_nnnorm, Real.enorm_eq_ofReal_abs, abs_of_pos hr]

/-- The formula `P(𝖠, t) = log ρ(M(t))` for `0 ≤ t ≤ 1` of `Example.sys`,
with Mathlib's spectral radius. -/
theorem pressure_eq_log_spectralRadius {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    sys.pressure t = Real.log (spectralRadius ℝ (M t)).toReal := by
  rw [spectralRadius_M, ENNReal.toReal_ofReal (perronRoot_pos t).le]
  exact pressure_eq_log_perronRoot ht0 ht1

/-- `ρ(M(0)) = 2` in `Example.sys`. -/
theorem spectralRadius_M_zero : spectralRadius ℝ (M 0) = 2 := by
  have h : perronRoot 0 = 2 := by
    unfold perronRoot perron
    rw [neg_zero, Real.rpow_zero, Real.rpow_zero, Real.rpow_zero, Real.rpow_zero,
      show ((1 : ℝ) - 1) ^ 2 + 4 * (1 * 1) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
    norm_num
  rw [spectralRadius_M, h]
  norm_num

/-- `ρ(M(1)) ≤ 2/15` in `Example.sys`. -/
theorem spectralRadius_M_one_le : spectralRadius ℝ (M 1) ≤ ENNReal.ofReal (2 / 15) := by
  rw [spectralRadius_M]
  refine ENNReal.ofReal_le_ofReal ?_
  unfold perronRoot perron
  have h : Real.sqrt (((10 : ℝ) ^ (-(1 : ℝ)) - (20 : ℝ) ^ (-(1 : ℝ))) ^ 2 +
      4 * ((30 : ℝ) ^ (-(1 : ℝ)) * (40 : ℝ) ^ (-(1 : ℝ)))) ≤ 7 / 60 := by
    rw [Real.sqrt_le_iff]
    simp only [Real.rpow_neg_one]
    norm_num
  simp only [Real.rpow_neg_one] at h ⊢
  linarith

/-- The equation `ρ(M(t)) = 1` is equivalent to `(1 - 10^{-t})(1 - 20^{-t}) = 1200^{-t}`, for
`t > 0`, as in `Example.sys`. -/
theorem perronRoot_eq_one_iff {t : ℝ} (ht : 0 < t) :
    perronRoot t = 1 ↔
      (1 - (10 : ℝ) ^ (-t)) * (1 - (20 : ℝ) ^ (-t)) = (1200 : ℝ) ^ (-t) := by
  have he : 0 < (30 : ℝ) ^ (-t) * (40 : ℝ) ^ (-t) := by positivity
  obtain ⟨hchar, hp, hq⟩ := perron_spec (p := (10 : ℝ) ^ (-t)) (q := (20 : ℝ) ^ (-t)) he
  have h1200 : (1200 : ℝ) ^ (-t) = (30 : ℝ) ^ (-t) * (40 : ℝ) ^ (-t) := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]
    norm_num
  have hq1 : (20 : ℝ) ^ (-t) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.2 ht)
  rw [h1200]
  constructor
  · intro h
    unfold perronRoot at h
    rw [h] at hchar
    exact hchar
  · intro h
    have hfac : (1 - perronRoot t) *
        (1 - ((10 : ℝ) ^ (-t) + (20 : ℝ) ^ (-t) - perronRoot t)) = 0 := by
      unfold perronRoot
      linear_combination h - hchar
    rcases mul_eq_zero.1 hfac with h' | h'
    · linarith
    · unfold perronRoot at h'
      linarith

/-- The characteristic equation of `Example.sys`: the affinity dimension
`s` satisfies `(1 - 10^{-s})(1 - 20^{-s}) = 1200^{-s}`. -/
theorem dimaff_charEq :
    (1 - (10 : ℝ) ^ (-sys.dimaff)) * (1 - (20 : ℝ) ^ (-sys.dimaff)) =
      (1200 : ℝ) ^ (-sys.dimaff) := by
  obtain ⟨h0, h1⟩ := dimaff_pos_lt_one
  have hP := pressure_eq_log_perronRoot h0.le h1.le
  rw [sys.pressure_dimaff] at hP
  exact (perronRoot_eq_one_iff h0).1
    (Real.eq_one_of_pos_of_log_eq_zero (perronRoot_pos _) hP.symm)

/-- The characteristic equation of `Example.sys` has no solution in
`(0, 1]` other than the affinity dimension. -/
theorem eq_dimaff_of_charEq {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    (h : (1 - (10 : ℝ) ^ (-t)) * (1 - (20 : ℝ) ^ (-t)) = (1200 : ℝ) ^ (-t)) :
    t = sys.dimaff := by
  have hP := pressure_eq_log_perronRoot ht0.le ht1
  rw [(perronRoot_eq_one_iff ht0).2 h, Real.log_one] at hP
  exact (sys.dimaff_eq ht0.le hP).symm

end Example

end BoxLike
