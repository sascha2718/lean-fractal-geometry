module

/-
`eq:simple_lyapunov` in `sec:normalisation`, tex lines 2243 to 2256: for a proximal box-like
tuple with rotations and `0 < s < 2` the equilibrium state has distinct Lyapunov exponents. The
article quotes Morris–Shmerkin, Trans. Amer. Math. Soc. 371 (2019), Lemmas 3.4 and 3.5
(numbering of arXiv:1602.08789v3): an equilibrium state with `λ_1 = λ_2` is Bernoulli, and a
measure with the Gibbs bounds is not. This module proves Lemma 3.4, combines it with Lemma 3.5
(`System.not_isBernoulli`), and derives the literature statement `MorrisShmerkinLyapunov` from
the Gibbs bounds of every equilibrium state, `EquilibriumGibbsStatement`.

Lemma 3.4 is Gibbs' inequality. With `q_i = |det A_i|^{s/2}`, equal exponents give
`Λ(𝖠, μ, s) = (s/2)(λ_1 + λ_2) = ∑_i μ([i]) log q_i`, so that
`P(𝖠, s) = h_0(μ) + ∑_i μ([i]) log q_i ≤ H_μ(𝒫) + ∑_i μ([i]) log q_i ≤ log ∑_i q_i ≤ P(𝖠, s)`.
Equality forces `h_0(μ) = H_μ(𝒫)`, and `μ` is Bernoulli.

* `abs_det_rpow_le_svf`, `System.abs_det_matWord_rpow_le_svf`: `|det A|^{s/2} ≤ φ^s(A)` for
  `s ≥ 0`, since `|det A| ≤ ‖A‖²`.
* `System.sum_abs_det_matWord_rpow`, `System.log_sum_abs_det_rpow_le_pressure`:
  `∑_{|𝐢| = n} |det A_𝐢|^t = (∑_i |det A_i|^t)^n` and `log ∑_i |det A_i|^{s/2} ≤ P(𝖠, s)`.
* `energy_self`: `Λ = s λ` when `λ_1 = λ_2 = λ`.
* `System.IsEquilibriumState.pressure_eq_of_lyapunov_eq`,
  `System.IsEquilibriumState.entropy_eq_blockEntropy_one_of_lyapunov_eq`: the equilibrium
  equation with equal exponents, and `h_0(μ) = H_μ(𝒫)`.
* `System.IsEquilibriumState.isBernoulli_of_lyapunov_eq`,
  `System.IsEquilibriumState.eq_bernoulli_of_lyapunov_eq`: Morris–Shmerkin, Lemma 3.4; the
  equilibrium state is the Bernoulli measure with the weights
  `p_i = |det A_i|^{s/2} / ∑_j |det A_j|^{s/2}`.
* `System.IsEquilibriumState.lyapunov₂_lt_lyapunov₁_of_hasGibbsBounds`: `eq:simple_lyapunov`
  for an equilibrium state with the Gibbs bounds.
* `morrisShmerkinLyapunov_of_equilibriumGibbs`: `EquilibriumGibbsStatement` implies
  `MorrisShmerkinLyapunov`.
* `System.IsEquilibriumState.lyapunov₂_lt_lyapunov₁_of_withRotations`,
  `morrisShmerkinLyapunov_holds`: `eq:simple_lyapunov` for every equilibrium state of a proximal
  box-like tuple with rotations, and the statement `MorrisShmerkinLyapunov`, with the Gibbs bounds
  of `equilibriumGibbs` (`BoxLike/EquilibriumGibbs.lean`). No literature premise is used.
-/
public import BoxLike.BernoulliEquilibrium
public import BoxLike.EquilibriumGibbs
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.GibbsProperties
public import BoxLike.Literature
public import BoxLike.Proximal
public import BoxLike.Support.PressureConvexity

@[expose] public section

namespace BoxLike

open MeasureTheory
open scoped Matrix.Norms.L2Operator

universe u

/-! ### The singular value function and the determinant -/

/-- `|det A|^{s/2} ≤ φ^s(A)` for `s ≥ 0` and every real `2 × 2` matrix, from
`|det A| = α_1(A) α_2(A) ≤ α_1(A)²`. Used in the proof of Morris–Shmerkin, Lemma 3.4, for
`eq:simple_lyapunov`. -/
theorem abs_det_rpow_le_svf {s : ℝ} (hs : 0 ≤ s) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    |A.det| ^ (s / 2) ≤ svf s A := by
  have hd := MatrixTuple.abs_det_le_norm_sq A
  have key : ∀ t : ℝ, 0 ≤ t → |A.det| ^ (t / 2) ≤ ‖A‖ ^ t := fun t ht => by
    calc |A.det| ^ (t / 2) ≤ (‖A‖ ^ 2) ^ (t / 2) :=
          Real.rpow_le_rpow (abs_nonneg _) hd (by linarith)
      _ = ‖A‖ ^ t := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
          congr 1
          push_cast
          ring
  unfold svf
  split_ifs with h1 h2
  · exact key s hs
  · rcases (abs_nonneg A.det).eq_or_lt with h0 | h0
    · rw [← h0, Real.zero_rpow (by linarith)]
      positivity
    · rw [show s / 2 = (2 - s) / 2 + (s - 1) by ring, Real.rpow_add h0]
      exact mul_le_mul_of_nonneg_right (key _ (by linarith)) (by positivity)
  · exact le_rfl

namespace System

section Pressure

variable {ι : Type*} (S : System ι)

/-- `|det A_𝐢|^{s/2} ≤ φ^s(A_𝐢)` for the products of the system and `s ≥ 0`. Used in the proof
of Morris–Shmerkin, Lemma 3.4, for `eq:simple_lyapunov`. -/
theorem abs_det_matWord_rpow_le_svf {s : ℝ} (hs : 0 ≤ s) (w : List ι) :
    |(S.matWord w).det| ^ (s / 2) ≤ svf s (S.matWord w) :=
  abs_det_rpow_le_svf hs _

variable [Fintype ι]

/-- `∑_{|𝐢| = n} |det A_𝐢|^t = (∑_i |det A_i|^t)^n`: the determinant is multiplicative. Used
in the proof of Morris–Shmerkin, Lemma 3.4, for `eq:simple_lyapunov`. -/
theorem sum_abs_det_matWord_rpow (t : ℝ) (n : ℕ) :
    ∑ w : Fin n → ι, |(S.matWord (List.ofFn w)).det| ^ t = (∑ i, |(S.mat i).det| ^ t) ^ n := by
  induction n with
  | zero => simp [matWord]
  | succ n ih =>
    have h1 : ∑ w : Fin 1 → ι, |(S.matWord (List.ofFn w)).det| ^ t =
        ∑ i, |(S.mat i).det| ^ t :=
      (Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι).symm _ _ fun i => by simp [matWord]).symm
    rw [sum_ofFn_add n 1 fun w => |(S.matWord w).det| ^ t, pow_succ, ← ih, ← h1,
      Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => ?_
    rw [matWord_append, Matrix.det_mul, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]

/-- `log ∑_i |det A_i|^{s/2} ≤ P(𝖠, s)` for `s ≥ 0`: by `|det A_𝐢|^{s/2} ≤ φ^s(A_𝐢)`, the sum
`∑_{|𝐢| = n} φ^s(A_𝐢)` is at least `(∑_i |det A_i|^{s/2})^n`. Used in the proof of
Morris–Shmerkin, Lemma 3.4, for `eq:simple_lyapunov`. -/
theorem log_sum_abs_det_rpow_le_pressure [Nonempty ι] {s : ℝ} (hs : 0 ≤ s) :
    Real.log (∑ i, |(S.mat i).det| ^ (s / 2)) ≤ S.pressure s := by
  have hq : 0 < ∑ i, |(S.mat i).det| ^ (s / 2) :=
    Finset.sum_pos (fun i _ => S.rpow_abs_det_mat_pos _ i) Finset.univ_nonempty
  refine le_csInf ⟨_, 1, Set.mem_Ici.2 le_rfl, rfl⟩ ?_
  rintro _ ⟨n, hn, rfl⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : (∑ i, |(S.mat i).det| ^ (s / 2)) ^ n ≤ S.svfSum s n := by
    rw [← S.sum_abs_det_matWord_rpow, svfSum]
    exact Finset.sum_le_sum fun w _ => S.abs_det_matWord_rpow_le_svf hs _
  rw [le_div_iff₀ hn', mul_comm, ← Real.log_pow]
  exact Real.log_le_log (pow_pos hq n) hle

end Pressure

end System

/-- `Λ = s λ` when the two Lyapunov exponents are equal to `λ`: each of the three lines of
`eq:energy_def` reads `s λ`. Used for `eq:simple_lyapunov`. -/
theorem energy_self (l s : ℝ) : energy l l s = s * l := by
  unfold energy
  split_ifs <;> ring

namespace System

/-! ### Equal Lyapunov exponents: Morris–Shmerkin, Lemma 3.4 -/

section LemmaThreeFour

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {S : System ι} {s : ℝ} {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]

/-- The equilibrium equation `eq:eq_state_def` for equal Lyapunov exponents:
`P(𝖠, s) = h_0(μ) + ∑_i μ([i]) log |det A_i|^{s/2}`, since
`Λ(𝖠, μ, s) = (s/2)(λ_1 + λ_2) = (s/2) ∑_i μ([i]) log |det A_i|`. A step of the proof of
Morris–Shmerkin, Lemma 3.4, for `eq:simple_lyapunov`. -/
theorem IsEquilibriumState.pressure_eq_of_lyapunov_eq (heq : S.IsEquilibriumState s μ)
    (hinv : MeasurePreserving (shift 1) μ μ) (hs : 0 ≤ s)
    (hl : S.lyapunov₁ μ = S.lyapunov₂ μ) :
    S.pressure s =
      entropy μ + ∑ i, μ.real (cylinder ![i]) * Real.log (|(S.mat i).det| ^ (s / 2)) := by
  have hsum := S.lyapunov₁_add_lyapunov₂ hinv
  rw [← hl] at hsum
  rw [heq.pressure_eq hinv hs, ← hl, energy_self]
  have e : s * S.lyapunov₁ μ = s / 2 * (S.lyapunov₁ μ + S.lyapunov₁ μ) := by ring
  rw [e, hsum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_rpow (by simpa using S.rpow_abs_det_mat_pos 1 i)]
  ring

/-- For equal Lyapunov exponents an `s`-equilibrium state has the entropy of its one-symbol
distribution, `h_0(μ) = H_μ(𝒫)`, and that distribution attains equality in Gibbs' inequality
for the weights `|det A_i|^{s/2}`: the chain
`P(𝖠, s) = h_0(μ) + ∑_i μ([i]) log q_i ≤ H_μ(𝒫) + ∑_i μ([i]) log q_i ≤ log ∑_i q_i ≤ P(𝖠, s)`
is an equality. The core of the proof of Morris–Shmerkin, Lemma 3.4, for
`eq:simple_lyapunov`. -/
theorem IsEquilibriumState.entropy_eq_blockEntropy_one_of_lyapunov_eq
    (heq : S.IsEquilibriumState s μ) (hinv : MeasurePreserving (shift 1) μ μ) (hs : 0 ≤ s)
    (hl : S.lyapunov₁ μ = S.lyapunov₂ μ) :
    entropy μ = blockEntropy μ 1 ∧
      blockEntropy μ 1 + ∑ i, μ.real (cylinder ![i]) * Real.log (|(S.mat i).det| ^ (s / 2)) =
        Real.log (∑ i, |(S.mat i).det| ^ (s / 2)) := by
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
  have hP := heq.pressure_eq_of_lyapunov_eq hinv hs hl
  have hG := blockEntropy_one_add_sum_le μ (fun i => |(S.mat i).det| ^ (s / 2))
    (S.rpow_abs_det_mat_pos (s / 2))
  have hH := entropy_le_blockEntropy_one hinv
  have hL := S.log_sum_abs_det_rpow_le_pressure hs
  constructor <;> linarith

/-- Morris–Shmerkin, Trans. Amer. Math. Soc. 371 (2019), Lemma 3.4 (numbering of
arXiv:1602.08789v3), used for `eq:simple_lyapunov` (tex lines 2243 to 2247): an invariant
`s`-equilibrium state with `λ_1(𝖠, μ) = λ_2(𝖠, μ)` is Bernoulli, with the probability vector
`p_i = μ([i])`. The proof needs `s ≥ 0` only. -/
theorem IsEquilibriumState.isBernoulli_of_lyapunov_eq (heq : S.IsEquilibriumState s μ)
    (hinv : MeasurePreserving (shift 1) μ μ) (hs : 0 ≤ s)
    (hl : S.lyapunov₁ μ = S.lyapunov₂ μ) : IsBernoulli μ := by
  have hent := (heq.entropy_eq_blockEntropy_one_of_lyapunov_eq hinv hs hl).1
  exact ⟨fun i => μ.real (cylinder ![i]), fun _ => measureReal_nonneg,
    sum_measureReal_cylinder_one μ, fun k _ _ w =>
      measureReal_preimage_shift_cylinder_eq_prod_of_entropy_eq hinv hent k w⟩

/-- Morris–Shmerkin, Lemma 3.4, with the weights: an invariant `s`-equilibrium state with
`λ_1(𝖠, μ) = λ_2(𝖠, μ)` is the Bernoulli measure with the weights
`p_i = |det A_i|^{s/2} / ∑_j |det A_j|^{s/2}` of tex line 2261, by the equality case of Gibbs'
inequality. Used for `eq:simple_lyapunov`. -/
theorem IsEquilibriumState.eq_bernoulli_of_lyapunov_eq (heq : S.IsEquilibriumState s μ)
    (hinv : MeasurePreserving (shift 1) μ μ) (hs : 0 ≤ s)
    (hl : S.lyapunov₁ μ = S.lyapunov₂ μ) : μ = bernoulli (S.detWeightMeasure s) := by
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
  obtain ⟨hent, hGeq⟩ := heq.entropy_eq_blockEntropy_one_of_lyapunov_eq hinv hs hl
  refine eq_bernoulli_of_measureReal_cylinder _ fun k n w => ?_
  rw [measureReal_preimage_shift_cylinder_eq_prod_of_entropy_eq hinv hent k w]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [measureReal_cylinder_eq_of_blockEntropy_one_add_sum_eq μ _ (S.rpow_abs_det_mat_pos _) hGeq,
    measureReal_detWeightMeasure_singleton, detWeight]

end LemmaThreeFour

/-! ### Distinct Lyapunov exponents -/

section SimpleLyapunov

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {S : System ι} {s : ℝ} {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]

/-- `eq:simple_lyapunov`, tex lines 2243 to 2256: for a proximal box-like tuple with rotations
and `0 < s < 2`, an invariant `s`-equilibrium state with the Gibbs bounds of
`thm:irred_eq_state` has `λ_2(𝖠, μ) < λ_1(𝖠, μ)`. Morris–Shmerkin, Trans. Amer. Math. Soc. 371
(2019), Lemma 3.5 (`System.not_isBernoulli`): the measure is not Bernoulli; Lemma 3.4
(`System.IsEquilibriumState.isBernoulli_of_lyapunov_eq`): the exponents differ. -/
theorem IsEquilibriumState.lyapunov₂_lt_lyapunov₁_of_hasGibbsBounds
    (heq : S.IsEquilibriumState s μ) (hinv : MeasurePreserving (shift 1) μ μ)
    (hrot : S.WithRotations) (hprox : S.Proximal) (hs0 : 0 < s) (hs2 : s < 2)
    (hG : S.HasGibbsBounds s μ) : S.lyapunov₂ μ < S.lyapunov₁ μ :=
  lt_of_le_of_ne (S.lyapunov₂_le_lyapunov₁ hinv) fun hl =>
    System.not_isBernoulli hrot hprox hs0 hs2 hG
      (heq.isBernoulli_of_lyapunov_eq hinv hs0.le hl.symm)

end SimpleLyapunov

end System

/-- The literature statement `MorrisShmerkinLyapunov` follows from `EquilibriumGibbsStatement`,
the Gibbs bounds of every invariant equilibrium state of a box-like tuple with rotations for
`0 < s < 2`: a proximal diagonal generator makes the tuple proximal, and
`System.IsEquilibriumState.lyapunov₂_lt_lyapunov₁_of_hasGibbsBounds` gives
`eq:simple_lyapunov`, along Morris–Shmerkin, Trans. Amer. Math. Soc. 371 (2019), Lemmas 3.4 and
3.5. -/
theorem morrisShmerkinLyapunov_of_equilibriumGibbs (h : EquilibriumGibbsStatement.{u}) :
    MorrisShmerkinLyapunov.{u} := by
  intro ι _ _ _ S hrot hpd s hs0 hs2 μ _ hinv heq
  exact heq.lyapunov₂_lt_lyapunov₁_of_hasGibbsBounds hinv hrot hpd.proximal hs0 hs2
    (h S hrot hs0 hs2 μ hinv heq)

/-- `eq:simple_lyapunov` (tex lines 2243 to 2256): for a proximal box-like tuple with rotations
and `0 < s < 2` every invariant `s`-equilibrium state has `λ_2(𝖠, μ) < λ_1(𝖠, μ)`. The Gibbs
bounds are `System.IsEquilibriumState.hasGibbsBounds_of_withRotations`; no literature premise is
used. -/
theorem System.IsEquilibriumState.lyapunov₂_lt_lyapunov₁_of_withRotations {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] {S : System ι} {s : ℝ}
    {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] (heq : S.IsEquilibriumState s μ)
    (hinv : MeasurePreserving (shift 1) μ μ) (hrot : S.WithRotations) (hprox : S.Proximal)
    (hs0 : 0 < s) (hs2 : s < 2) : S.lyapunov₂ μ < S.lyapunov₁ μ :=
  heq.lyapunov₂_lt_lyapunov₁_of_hasGibbsBounds hinv hrot hprox hs0 hs2
    (heq.hasGibbsBounds_of_withRotations hrot hs0 hinv)

/-- The statement `MorrisShmerkinLyapunov` of `eq:simple_lyapunov` holds: the library proves
Morris–Shmerkin's Lemmas 3.4 and 3.5 and the Gibbs bounds of every equilibrium state of a
box-like tuple with rotations (`equilibriumGibbs`). -/
theorem morrisShmerkinLyapunov_holds : MorrisShmerkinLyapunov.{u} :=
  morrisShmerkinLyapunov_of_equilibriumGibbs equilibriumGibbs

end BoxLike
