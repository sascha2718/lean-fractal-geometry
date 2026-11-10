module

/-
The singular value pressure `P(𝖠, s)` of an arbitrary tuple `𝖠 ∈ GL_2(ℝ)^N` (`sec:affinity_dim`,
tex lines 2048 to 2060): the limit defining it exists by Fekete's lemma, the function
`s ↦ P(𝖠, s)` is continuous on `[0, ∞)` and convex between consecutive integers, and, when
`max_i ‖A_i‖ < 1`, it is strictly decreasing with `P(𝖠, 0) = log N ≥ 0` and
`P(𝖠, s) → -∞`, so that `dimaff(𝖠)` is well defined. Invertibility of the matrices is the
hypothesis `∀ i, (A i).det ≠ 0`, as in `BoxLike/MatrixTuple.lean`.

The objects are those of `BoxLike/MatrixTuple.lean`. On each of the intervals `[0, 1]`, `[1, 2]`
and `[2, ∞)` the function `s ↦ log φ^s(A)` is affine for an invertible matrix `A`, so the sums
`∑_{|𝐢| = n} φ^s(A_𝐢)` are sums of exponentials of affine functions, whose logarithms are convex
by the weighted inequality of the arithmetic and geometric means; the pressure is a pointwise
limit of these convex functions divided by `n`.

* `MatrixTuple.abs_det_le_norm_sq`: `|det A| = α_1(A) α_2(A) ≤ α_1(A)²` with `α_1(A) = ‖A‖`.
* `MatrixTuple.norm_adjugate`, `MatrixTuple.inv_norm_inv_eq_abs_det_div_norm`: `‖adj A‖ = ‖A‖`
  and `α_2(A) = ‖A⁻¹‖⁻¹ = |det A| / ‖A‖` (tex lines 1467 to 1471).
* `MatrixTuple.svf_eq_rpow_mul_rpow`: `φ^s(A) = α_1(A)^{p(s)} α_2(A)^{s - p(s)}`, with
  `α_2(A) = |det A| / ‖A‖` and `p(s)` the exponent `svfExp s` of `BoxLike/AffinityDim.lean`.
* `MatrixTuple.Convexity.svf_add_le`, `MatrixTuple.Convexity.le_svf_add`:
  `α_2(A)^δ φ^s(A) ≤ φ^{s+δ}(A) ≤ α_1(A)^δ φ^s(A)`.
* `MatrixTuple.Convexity.tendsto_pressure`: the limit defining `P(𝖠, s)` exists, `s ≥ 0`.
* `MatrixTuple.convexOn_log_sum_exp`: `s ↦ log ∑_w exp(a_w + s b_w)` is convex.
* `MatrixTuple.pressure_convexOn_Icc_zero_one`, `MatrixTuple.pressure_convexOn_Icc_one_two`,
  `MatrixTuple.pressure_convexOn_Ici_two`, `MatrixTuple.pressure_convexOn_Icc_nat`: the
  pressure is convex on `[0, 1]`, on `[1, 2]`, on `[2, ∞)`, hence on every `[k, k + 1]`.
* `MatrixTuple.pressure_increment_bounds`, `MatrixTuple.pressure_continuousOn_Ici`:
  `(t - s) log ρ ≤ P(𝖠, t) - P(𝖠, s) ≤ (t - s) log R` for `0 ≤ s ≤ t`, where
  `ρ ≤ α_2(A_i)` and `α_1(A_i) ≤ R`; hence `P(𝖠, ·)` is continuous on `[0, ∞)`.
* `MatrixTuple.pressure_at_zero`, `MatrixTuple.pressure_strictAntiOn_Ici`,
  `MatrixTuple.pressure_tendsto_atBot`, `MatrixTuple.pressure_existsUnique_eq_zero`: the
  remaining assertions of tex lines 2057 to 2060 under `max_i ‖A_i‖ < 1`.
* `System.pressure_convexOn_Icc_nat`, `System.pressure_convexOn_Ici_two`: the box-like
  specialisation.
-/
public import BoxLike.AffinityDim
public import BoxLike.MatrixTuple
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

namespace BoxLike

open Filter Topology Set Matrix
open scoped Matrix.Norms.L2Operator

/-! ### Singular values of a real `2 × 2` matrix -/

namespace MatrixTuple

/-- The squared length of the image of a unit coordinate vector is at most `‖A‖²`: the columns
of `A` have length at most `α_1(A)`. -/
theorem col_sq_le_norm_sq (A : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) :
    A 0 j ^ 2 + A 1 j ^ 2 ≤ ‖A‖ ^ 2 := by
  let x : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (Pi.single j 1)
  have hx : ‖x‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    fin_cases j <;> simp [x, Fin.sum_univ_two]
  have hAx : ‖toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A x‖ ≤ ‖A‖ := by
    have h := ContinuousLinearMap.le_opNorm (toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A) x
    rwa [l2_opNorm_toEuclideanCLM, hx, mul_one] at h
  have hsq : ‖toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A x‖ ^ 2 = A 0 j ^ 2 + A 1 j ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    simp [x]
  rw [← hsq]
  exact pow_le_pow_left₀ (norm_nonneg _) hAx 2

/-- `|det A| = α_1(A) α_2(A) ≤ α_1(A)²`, with `α_1(A) = ‖A‖` the `ℓ²` operator norm: the
determinant of a real `2 × 2` matrix is at most the product of the lengths of its columns. -/
theorem abs_det_le_norm_sq (A : Matrix (Fin 2) (Fin 2) ℝ) : |A.det| ≤ ‖A‖ ^ 2 := by
  have h0 := col_sq_le_norm_sq A 0
  have h1 := col_sq_le_norm_sq A 1
  have hdet : A.det ^ 2 ≤ (‖A‖ ^ 2) ^ 2 := by
    rw [det_fin_two]
    have hlag : (A 0 0 * A 1 1 - A 0 1 * A 1 0) ^ 2 ≤
        (A 0 0 ^ 2 + A 1 0 ^ 2) * (A 0 1 ^ 2 + A 1 1 ^ 2) := by
      nlinarith [sq_nonneg (A 0 0 * A 0 1 + A 1 0 * A 1 1)]
    exact hlag.trans (mul_le_mul h0 h1 (by positivity) (by positivity)) |>.trans_eq (by ring)
  have := sq_le_sq.1 hdet
  rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖A‖ ^ 2)] at this

/-- The rotation `J` of the plane by a right angle. -/
def quarterTurn : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- The adjugate of a `2 × 2` matrix is `J Aᵀ Jᵀ`. -/
theorem adjugate_eq_quarterTurn (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.adjugate = quarterTurn * Aᵀ * quarterTurnᵀ := by
  rw [adjugate_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [quarterTurn, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

/-- The identity matrix has operator norm at most `1`. -/
theorem norm_one_fin_two_le : ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self (1 : Matrix (Fin 2) (Fin 2) ℝ)
  rw [conjTranspose_one, one_mul] at h
  nlinarith [norm_nonneg (1 : Matrix (Fin 2) (Fin 2) ℝ)]

/-- The rotation `J` has operator norm at most `1`. -/
theorem norm_quarterTurn_le : ‖quarterTurn‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self quarterTurn
  have h1 : quarterTurnᴴ * quarterTurn = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [quarterTurn, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h1] at h
  nlinarith [norm_nonneg quarterTurn, norm_one_fin_two_le]

/-- The adjugate has operator norm at most that of the matrix. -/
theorem norm_adjugate_le (A : Matrix (Fin 2) (Fin 2) ℝ) : ‖A.adjugate‖ ≤ ‖A‖ := by
  rw [adjugate_eq_quarterTurn]
  have hT : ‖Aᵀ‖ = ‖A‖ := by
    rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose]
  have hJT : ‖quarterTurnᵀ‖ ≤ 1 := by
    rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose]
    exact norm_quarterTurn_le
  calc ‖quarterTurn * Aᵀ * quarterTurnᵀ‖ ≤ ‖quarterTurn * Aᵀ‖ * ‖quarterTurnᵀ‖ :=
        l2_opNorm_mul _ _
    _ ≤ (‖quarterTurn‖ * ‖Aᵀ‖) * 1 :=
        mul_le_mul (l2_opNorm_mul _ _) hJT (norm_nonneg _) (by positivity)
    _ ≤ ‖A‖ := by
        rw [hT, mul_one]
        nlinarith [norm_quarterTurn_le, norm_nonneg A]

/-- The adjugate of a `2 × 2` matrix has the operator norm of the matrix. -/
theorem norm_adjugate (A : Matrix (Fin 2) (Fin 2) ℝ) : ‖A.adjugate‖ = ‖A‖ := by
  refine le_antisymm (norm_adjugate_le A) ?_
  have h := norm_adjugate_le A.adjugate
  rwa [adjugate_adjugate A (by simp), Fintype.card_fin, Nat.sub_self, pow_zero, one_smul] at h

/-- `‖A⁻¹‖ = ‖A‖ / |det A|` for a real `2 × 2` matrix; both sides vanish for a singular matrix. -/
theorem norm_inv_eq_norm_div_abs_det (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖A⁻¹‖ = ‖A‖ / |A.det| := by
  rw [inv_def, Ring.inverse_eq_inv', norm_smul, norm_inv, Real.norm_eq_abs, norm_adjugate,
    div_eq_inv_mul]

/-- Tex lines 1544 to 1548: `α_2(A) = ‖A⁻¹‖⁻¹`, where the library's second singular value is
`|det A| / ‖A‖`; together with `α_1(A) = ‖A‖` this gives `|det A| = α_1(A) α_2(A)` for an
invertible matrix. -/
theorem inv_norm_inv_eq_abs_det_div_norm (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖A⁻¹‖⁻¹ = |A.det| / ‖A‖ := by
  rw [norm_inv_eq_norm_div_abs_det, inv_div]

/-- An invertible matrix has positive operator norm. -/
theorem norm_pos_of_det_ne_zero {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0) : 0 < ‖A‖ := by
  rcases (norm_nonneg A).lt_or_eq with h | h
  · exact h
  · have := abs_det_le_norm_sq A
    rw [← h] at this
    have h2 : |A.det| = 0 := le_antisymm (by simpa using this) (abs_nonneg _)
    exact absurd (abs_eq_zero.1 h2) hA

/-- The second singular value `α_2(A) = |det A| / ‖A‖` is at most `α_1(A) = ‖A‖`. -/
theorem abs_det_div_norm_le_norm {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0) :
    |A.det| / ‖A‖ ≤ ‖A‖ := by
  have hn := norm_pos_of_det_ne_zero hA
  rw [div_le_iff₀ hn, ← sq]
  exact abs_det_le_norm_sq A

/-- The second singular value `α_2(A) = |det A| / ‖A‖` of an invertible matrix is positive. -/
theorem abs_det_div_norm_pos {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0) :
    0 < |A.det| / ‖A‖ :=
  div_pos (abs_pos.2 hA) (norm_pos_of_det_ne_zero hA)

/-- `φ^s(A) = α_1(A)^{p(s)} α_2(A)^{s - p(s)}` for an invertible matrix `A`, with
`α_1(A) = ‖A‖`, `α_2(A) = |det A| / ‖A‖` and `p(s)` equal to `s`, `1` or `s / 2` on the three
ranges of `sec:Singular_value_function`. -/
theorem svf_eq_rpow_mul_rpow {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0) (s : ℝ) :
    svf s A = ‖A‖ ^ svfExp s * (|A.det| / ‖A‖) ^ (s - svfExp s) := by
  have hn := norm_pos_of_det_ne_zero hA
  have hd := abs_pos.2 hA
  unfold svfExp svf
  split_ifs with h1 h2
  · rw [sub_self, Real.rpow_zero, mul_one]
  · rw [Real.rpow_one, Real.div_rpow hd.le hn.le, show (2 : ℝ) - s = 1 - (s - 1) by ring,
      Real.rpow_sub hn, Real.rpow_one]
    ring
  · rw [Real.div_rpow hd.le hn.le, show s - s / 2 = s / 2 by ring, mul_div_assoc',
      mul_div_cancel_left₀ _ (Real.rpow_pos_of_pos hn _).ne']

/-! ### Slope bounds and the Fekete limit -/

namespace Convexity

variable {A : Matrix (Fin 2) (Fin 2) ℝ}

/-- `φ^{s+δ}(A) ≤ α_1(A)^δ φ^s(A)` for an invertible matrix `A` and `δ ≥ 0`. -/
theorem svf_add_le (hA : A.det ≠ 0) (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    svf (s + δ) A ≤ ‖A‖ ^ δ * svf s A := by
  have hn := norm_pos_of_det_ne_zero hA
  have h2 := abs_det_div_norm_pos hA
  have h1 := svfExp_le_svfExp_add s hδ
  have h3 := svfExp_add_le s hδ
  rw [svf_eq_rpow_mul_rpow hA, svf_eq_rpow_mul_rpow hA]
  have hsplit : ‖A‖ ^ svfExp (s + δ) * (|A.det| / ‖A‖) ^ (s + δ - svfExp (s + δ)) =
      (‖A‖ ^ svfExp s * (|A.det| / ‖A‖) ^ (s - svfExp s)) *
        (‖A‖ ^ (svfExp (s + δ) - svfExp s) *
          (|A.det| / ‖A‖) ^ (δ - (svfExp (s + δ) - svfExp s))) := by
    rw [mul_mul_mul_comm, ← Real.rpow_add hn, ← Real.rpow_add h2]
    congr 2 <;> ring
  rw [hsplit, mul_comm (‖A‖ ^ δ)]
  exact mul_le_mul_of_nonneg_left
    (rpow_mul_rpow_sub_le h2 (abs_det_div_norm_le_norm hA) (by linarith))
    (by positivity)

/-- `α_2(A)^δ φ^s(A) ≤ φ^{s+δ}(A)` for an invertible matrix `A` and `δ ≥ 0`. -/
theorem le_svf_add (hA : A.det ≠ 0) (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (|A.det| / ‖A‖) ^ δ * svf s A ≤ svf (s + δ) A := by
  have hn := norm_pos_of_det_ne_zero hA
  have h2 := abs_det_div_norm_pos hA
  have h1 := svfExp_le_svfExp_add s hδ
  rw [svf_eq_rpow_mul_rpow hA, svf_eq_rpow_mul_rpow hA]
  have hsplit : ‖A‖ ^ svfExp (s + δ) * (|A.det| / ‖A‖) ^ (s + δ - svfExp (s + δ)) =
      (‖A‖ ^ svfExp s * (|A.det| / ‖A‖) ^ (s - svfExp s)) *
        (‖A‖ ^ (svfExp (s + δ) - svfExp s) *
          (|A.det| / ‖A‖) ^ (δ - (svfExp (s + δ) - svfExp s))) := by
    rw [mul_mul_mul_comm, ← Real.rpow_add hn, ← Real.rpow_add h2]
    congr 2 <;> ring
  rw [hsplit, mul_comm ((|A.det| / ‖A‖) ^ δ)]
  exact mul_le_mul_of_nonneg_left
    (rpow_le_rpow_mul_rpow_sub δ h2 (abs_det_div_norm_le_norm hA) (by linarith))
    (by positivity)

/-- `φ^s(A) ≥ α_2(A)^s` for an invertible matrix `A` and `s ≥ 0`. -/
theorem rpow_le_svf (hA : A.det ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    (|A.det| / ‖A‖) ^ s ≤ svf s A := by
  have h := le_svf_add hA 0 hs
  rwa [zero_add, show svf 0 A = 1 by simp [svf], mul_one] at h

variable {ι : Type*} {B : ι → Matrix (Fin 2) (Fin 2) ℝ}

/-- `A_{i 𝐢} = A_i A_𝐢`. -/
theorem word_cons (i : ι) (w : List ι) : word B (i :: w) = B i * word B w := rfl

/-- The product of an invertible tuple along a word is invertible. -/
theorem det_word_ne_zero (hB : ∀ i, (B i).det ≠ 0) (w : List ι) : (word B w).det ≠ 0 := by
  induction w with
  | nil => simp
  | cons i w ih => rw [word_cons, det_mul]; exact mul_ne_zero (hB i) ih

/-- The second singular value is super-multiplicative: `α_2(AB) ≥ α_2(A) α_2(B)`. -/
theorem mul_abs_det_div_norm_le {A A' : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0)
    (hA' : A'.det ≠ 0) :
    (|A.det| / ‖A‖) * (|A'.det| / ‖A'‖) ≤ |(A * A').det| / ‖A * A'‖ := by
  have hn := norm_pos_of_det_ne_zero hA
  have hn' := norm_pos_of_det_ne_zero hA'
  have hAA' : (A * A').det ≠ 0 := by rw [det_mul]; exact mul_ne_zero hA hA'
  have hnn := norm_pos_of_det_ne_zero hAA'
  rw [div_mul_div_comm, det_mul, abs_mul]
  exact div_le_div_of_nonneg_left (by positivity) hnn (l2_opNorm_mul A A')

/-- `α_1(A_𝐢) ≤ R^{|𝐢|}` when every `‖A_i‖ ≤ R`. -/
theorem norm_word_le {R : ℝ} (hR : 0 ≤ R) (hB : ∀ i, ‖B i‖ ≤ R) (w : List ι) :
    ‖word B w‖ ≤ R ^ w.length := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [word_cons, List.length_cons, pow_succ']
    exact (l2_opNorm_mul _ _).trans (mul_le_mul (hB i) ih (norm_nonneg _) hR)

/-- `α_2(A_𝐢) ≥ ρ^{|𝐢|}` when every `α_2(A_i) ≥ ρ ≥ 0`. -/
theorem pow_le_abs_det_div_norm_word {ρ : ℝ} (hρ : 0 ≤ ρ) (hB : ∀ i, (B i).det ≠ 0)
    (hρB : ∀ i, ρ ≤ |(B i).det| / ‖B i‖) (w : List ι) :
    ρ ^ w.length ≤ |(word B w).det| / ‖word B w‖ := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [word_cons, List.length_cons, pow_succ']
    exact (mul_le_mul (hρB i) ih (pow_nonneg hρ _) (abs_det_div_norm_pos (hB i)).le).trans
      (mul_abs_det_div_norm_le (hB i) (det_word_ne_zero hB w))

variable [Fintype ι]

/-- Common bounds `0 < ρ ≤ α_2(A_i)` and `α_1(A_i) ≤ R` of an invertible tuple, with `ρ ≤ R`
when the alphabet is non-empty. -/
theorem exists_singular_bounds [Nonempty ι] (hB : ∀ i, (B i).det ≠ 0) :
    ∃ ρ R : ℝ, 0 < ρ ∧ ρ ≤ R ∧ (∀ i, ρ ≤ |(B i).det| / ‖B i‖) ∧ ∀ i, ‖B i‖ ≤ R := by
  obtain ⟨i₀, -, h₀⟩ := Finset.exists_min_image Finset.univ (fun i => |(B i).det| / ‖B i‖)
    Finset.univ_nonempty
  obtain ⟨i₁, -, h₁⟩ := Finset.exists_max_image Finset.univ (fun i => ‖B i‖)
    Finset.univ_nonempty
  refine ⟨|(B i₀).det| / ‖B i₀‖, ‖B i₁‖, abs_det_div_norm_pos (hB i₀), ?_,
    fun i => h₀ i (Finset.mem_univ _), fun i => h₁ i (Finset.mem_univ _)⟩
  exact (abs_det_div_norm_le_norm (hB i₀)).trans (h₁ i₀ (Finset.mem_univ _))

/-- The sums `∑_{|𝐢| = n} φ^s(A_𝐢)` are sub-multiplicative in `n`. -/
theorem svfSum_add_le {s : ℝ} (hs : 0 ≤ s) (m n : ℕ) :
    svfSum B s (m + n) ≤ svfSum B s m * svfSum B s n := by
  rw [svfSum, sum_ofFn_add m n fun w => svf s (word B w), svfSum, svfSum, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun h _ => ?_
  rw [word_append]
  exact svf_mul_le hs _ _

/-- `∑_{|𝐢| = n} φ^s(A_𝐢) ≥ ρ^{sn}` for an invertible tuple over a non-empty alphabet. -/
theorem rpow_pow_le_svfSum [Nonempty ι] (hB : ∀ i, (B i).det ≠ 0) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hρB : ∀ i, ρ ≤ |(B i).det| / ‖B i‖) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    (ρ ^ n) ^ s ≤ svfSum B s n := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  set w : List ι := List.ofFn fun _ : Fin n => i
  have h1 : (ρ ^ n) ^ s ≤ svf s (word B w) := by
    refine le_trans ?_ (rpow_le_svf (det_word_ne_zero hB w) hs)
    refine Real.rpow_le_rpow (pow_nonneg hρ _) ?_ hs
    have := pow_le_abs_det_div_norm_word hρ hB hρB w
    rwa [List.length_ofFn] at this
  refine h1.trans ?_
  exact Finset.single_le_sum (f := fun w : Fin n → ι => svf s (word B (List.ofFn w)))
    (fun w _ => svf_nonneg _ _) (Finset.mem_univ _)

/-- The sums `∑_{|𝐢| = n} φ^s(A_𝐢)` of an invertible tuple over a non-empty alphabet are
positive. -/
theorem svfSum_pos [Nonempty ι] (hB : ∀ i, (B i).det ≠ 0) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    0 < svfSum B s n := by
  obtain ⟨ρ, R, hρ, -, hρB, -⟩ := exists_singular_bounds hB
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos (pow_pos hρ _) _)
    (rpow_pow_le_svfSum hB hρ.le hρB hs n)

/-- The limit defining `P(𝖠, s)` in `sec:affinity_dim` exists for an invertible tuple and
`s ≥ 0`, by Fekete's lemma, and it is the infimum `MatrixTuple.pressure`. -/
theorem tendsto_pressure [Nonempty ι] (hB : ∀ i, (B i).det ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun n : ℕ => Real.log (svfSum B s n) / n) atTop (𝓝 (pressure B s)) := by
  obtain ⟨ρ, R, hρ, -, hρB, -⟩ := exists_singular_bounds hB
  have hsub : Subadditive fun n => Real.log (svfSum B s n) := by
    intro m n
    rw [← Real.log_mul (svfSum_pos hB hs m).ne' (svfSum_pos hB hs n).ne']
    exact Real.log_le_log (svfSum_pos hB hs _) (svfSum_add_le hs m n)
  have hbdd : BddBelow (Set.range fun n : ℕ => Real.log (svfSum B s n) / n) := by
    refine ⟨min 0 (s * Real.log ρ), ?_⟩
    rintro _ ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      refine (min_le_right _ _).trans ?_
      rw [le_div_iff₀ hn']
      have h := Real.log_le_log (Real.rpow_pos_of_pos (pow_pos hρ _) _)
        (rpow_pow_le_svfSum hB hρ.le hρB hs n)
      rw [Real.log_rpow (pow_pos hρ _), Real.log_pow] at h
      linarith [h, mul_comm (s * Real.log ρ) (n : ℝ), mul_assoc s (n : ℝ) (Real.log ρ),
        mul_left_comm s (n : ℝ) (Real.log ρ)]
  have h := hsub.tendsto_lim hbdd
  rwa [Subadditive.lim] at h

end Convexity

/-! ### Convexity of `log ∑ exp` -/

/-- `s ↦ log ∑_w exp(a_w + s b_w)` is convex on `ℝ` for a non-empty finite index set: the weighted
inequality of the arithmetic and geometric means applied to the normalised terms. -/
theorem convexOn_log_sum_exp {W : Type*} [Fintype W] [Nonempty W] (a b : W → ℝ) :
    ConvexOn ℝ univ fun s => Real.log (∑ w, Real.exp (a w + s * b w)) := by
  refine ⟨convex_univ, fun s _ t _ θ η hθ hη hθη => ?_⟩
  simp only [smul_eq_mul]
  set X := ∑ w, Real.exp (a w + s * b w)
  set Y := ∑ w, Real.exp (a w + t * b w)
  have hX : 0 < X := Finset.sum_pos (fun w _ => Real.exp_pos _) Finset.univ_nonempty
  have hY : 0 < Y := Finset.sum_pos (fun w _ => Real.exp_pos _) Finset.univ_nonempty
  have hterm : ∀ w, Real.exp (a w + (θ * s + η * t) * b w) ≤
      X ^ θ * Y ^ η * (θ * (Real.exp (a w + s * b w) / X) +
        η * (Real.exp (a w + t * b w) / Y)) := by
    intro w
    have hx := Real.exp_pos (a w + s * b w)
    have hy := Real.exp_pos (a w + t * b w)
    have hgm := Real.geom_mean_le_arith_mean2_weighted hθ hη (div_pos hx hX).le
      (div_pos hy hY).le hθη
    have hid : Real.exp (a w + (θ * s + η * t) * b w) =
        X ^ θ * Y ^ η * ((Real.exp (a w + s * b w) / X) ^ θ *
          (Real.exp (a w + t * b w) / Y) ^ η) := by
      rw [Real.div_rpow hx.le hX.le, Real.div_rpow hy.le hY.le]
      have hXθ : 0 < X ^ θ := Real.rpow_pos_of_pos hX θ
      have hYη : 0 < Y ^ η := Real.rpow_pos_of_pos hY η
      field_simp
      rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
      congr 1
      have : a w = (θ + η) * a w := by rw [hθη, one_mul]
      linear_combination this
    rw [hid]
    exact mul_le_mul_of_nonneg_left hgm (by positivity)
  have hsum : ∑ w, Real.exp (a w + (θ * s + η * t) * b w) ≤ X ^ θ * Y ^ η := by
    refine (Finset.sum_le_sum fun w _ => hterm w).trans_eq ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.sum_div, ← Finset.sum_div, div_self hX.ne', div_self hY.ne', mul_one, mul_one,
      hθη, mul_one]
  have hpos : 0 < ∑ w, Real.exp (a w + (θ * s + η * t) * b w) :=
    Finset.sum_pos (fun w _ => Real.exp_pos _) Finset.univ_nonempty
  calc Real.log (∑ w, Real.exp (a w + (θ * s + η * t) * b w))
      ≤ Real.log (X ^ θ * Y ^ η) := Real.log_le_log hpos hsum
    _ = θ * Real.log X + η * Real.log Y := by
      rw [Real.log_mul (Real.rpow_pos_of_pos hX θ).ne' (Real.rpow_pos_of_pos hY η).ne',
        Real.log_rpow hX, Real.log_rpow hY]

/-! ### Convexity of the pressure -/

variable {ι : Type*} [Fintype ι] {A : ι → Matrix (Fin 2) (Fin 2) ℝ}

/-- If on a set `I ⊆ [0, ∞)` every `φ^s(A_𝐢)` is the exponential of a function affine in `s`,
then the pressure is convex on `I`. -/
theorem pressure_convexOn_of_svf_eq_exp (hA : ∀ i, (A i).det ≠ 0) {I : Set ℝ}
    (hI : Convex ℝ I) (hI0 : I ⊆ Ici 0) (c d : Matrix (Fin 2) (Fin 2) ℝ → ℝ)
    (hexp : ∀ s ∈ I, ∀ w : List ι, svf s (word A w) = Real.exp (c (word A w) + s * d (word A w))) :
    ConvexOn ℝ I (pressure A) := by
  by_cases hι : Nonempty ι
  swap
  · have hconst : ∀ s, pressure A s = 0 := by
      intro s
      have hsum : ∀ n : ℕ, 1 ≤ n → svfSum A s n = 0 := by
        intro n hn
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
        have : IsEmpty (Fin (1 + m) → ι) := by
          rw [not_nonempty_iff] at hι
          infer_instance
        simp [svfSum]
      have himg : (fun n : ℕ => Real.log (svfSum A s n) / n) '' Ici 1 = {0} := by
        ext x
        simp only [mem_image, mem_Ici, mem_singleton_iff]
        constructor
        · rintro ⟨n, hn, rfl⟩
          rw [hsum n hn, Real.log_zero, zero_div]
        · rintro rfl
          exact ⟨1, le_rfl, by rw [hsum 1 le_rfl, Real.log_zero, zero_div]⟩
      rw [pressure, himg, csInf_singleton]
    have : pressure A = fun _ => 0 := funext hconst
    rw [this]
    exact convexOn_const 0 hI
  refine ⟨hI, fun s hs t ht θ η hθ hη hθη => ?_⟩
  have hu := hI hs ht hθ hη hθη
  have hconv : ∀ n : ℕ, ConvexOn ℝ univ fun u =>
      Real.log (∑ w : Fin n → ι, Real.exp (c (word A (List.ofFn w)) +
        u * d (word A (List.ofFn w)))) := fun n =>
    convexOn_log_sum_exp (fun w : Fin n → ι => c (word A (List.ofFn w)))
      (fun w : Fin n → ι => d (word A (List.ofFn w)))
  have hF : ∀ u ∈ I, ∀ n : ℕ, Real.log (svfSum A u n) =
      Real.log (∑ w : Fin n → ι, Real.exp (c (word A (List.ofFn w)) +
        u * d (word A (List.ofFn w)))) := by
    intro u hu n
    rw [svfSum]
    congr 1
    exact Finset.sum_congr rfl fun w _ => hexp u hu _
  have hlim : ∀ u ∈ I, Tendsto (fun n : ℕ => Real.log (svfSum A u n) / n) atTop
      (𝓝 (pressure A u)) := fun u hu => Convexity.tendsto_pressure hA (hI0 hu)
  have hle : (fun n : ℕ => Real.log (svfSum A (θ • s + η • t) n) / n) ≤ᶠ[atTop]
      fun n : ℕ => θ * (Real.log (svfSum A s n) / n) + η * (Real.log (svfSum A t n) / n) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h := (hconv n).2 (mem_univ s) (mem_univ t) hθ hη hθη
    simp only [smul_eq_mul] at h
    rw [hF s hs, hF t ht, hF _ hu]
    simp only [smul_eq_mul]
    rw [mul_div_assoc', mul_div_assoc', ← add_div]
    exact div_le_div_of_nonneg_right h hn'.le
  have := le_of_tendsto_of_tendsto (hlim _ hu)
    (((hlim s hs).const_mul θ).add ((hlim t ht).const_mul η)) hle
  simpa only [smul_eq_mul] using this

/-- `log φ^s(A)` for an invertible matrix, written as an affine function of `s` on `[0, 1]`:
`φ^s(A) = exp(s log ‖A‖)`. -/
theorem svf_eq_exp_of_mem_Icc_zero_one {B : Matrix (Fin 2) (Fin 2) ℝ} (hB : B.det ≠ 0) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : svf s B = Real.exp (0 + s * Real.log ‖B‖) := by
  rw [zero_add, svf, ite_eq_left hs.2, Real.rpow_def_of_pos (norm_pos_of_det_ne_zero hB), mul_comm]

/-- `log φ^s(A)` for an invertible matrix, written as an affine function of `s` on `[1, 2]`:
`φ^s(A) = α_1(A) α_2(A)^{s-1} = exp(log α_1 - log α_2 + s log α_2)`. -/
theorem svf_eq_exp_of_mem_Icc_one_two {B : Matrix (Fin 2) (Fin 2) ℝ} (hB : B.det ≠ 0) {s : ℝ}
    (hs : s ∈ Icc (1 : ℝ) 2) :
    svf s B = Real.exp ((Real.log ‖B‖ - Real.log (|B.det| / ‖B‖)) +
      s * Real.log (|B.det| / ‖B‖)) := by
  have hn := norm_pos_of_det_ne_zero hB
  have h2 := abs_det_div_norm_pos hB
  have hexp : svfExp s = 1 := by
    unfold svfExp
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [ite_eq_left h.symm.le, ← h]
    · rw [ite_eq_right (not_le.2 h), ite_eq_left hs.2]
  rw [svf_eq_rpow_mul_rpow hB, hexp, Real.rpow_one, Real.rpow_def_of_pos h2,
    ← Real.exp_log hn, ← Real.exp_add, Real.log_exp]
  congr 1
  ring

/-- `log φ^s(A)` for an invertible matrix, written as an affine function of `s` on `[2, ∞)`:
`φ^s(A) = |det A|^{s/2} = exp(s (log |det A|) / 2)`. -/
theorem svf_eq_exp_of_mem_Ici_two {B : Matrix (Fin 2) (Fin 2) ℝ} (hB : B.det ≠ 0) {s : ℝ}
    (hs : s ∈ Ici (2 : ℝ)) : svf s B = Real.exp (0 + s * (Real.log |B.det| / 2)) := by
  have hd := abs_pos.2 hB
  have hs2 : (2 : ℝ) ≤ s := hs
  have hval : svf s B = |B.det| ^ (s / 2) := by
    unfold svf
    rw [ite_eq_right (by linarith)]
    rcases eq_or_lt_of_le hs2 with h | h
    · rw [ite_eq_left h.symm.le, ← h]
      norm_num
    · rw [ite_eq_right (not_le.2 h)]
  rw [hval, Real.rpow_def_of_pos hd, zero_add]
  congr 1
  ring

/-- The pressure of an invertible tuple is convex on `[0, 1]` (tex line 2056). -/
theorem pressure_convexOn_Icc_zero_one (hA : ∀ i, (A i).det ≠ 0) :
    ConvexOn ℝ (Icc 0 1) (pressure A) :=
  pressure_convexOn_of_svf_eq_exp hA (convex_Icc 0 1) (fun _ hs => hs.1) (fun _ => 0)
    (fun B => Real.log ‖B‖)
    (fun _ hs w => svf_eq_exp_of_mem_Icc_zero_one (Convexity.det_word_ne_zero hA w) hs)

/-- The pressure of an invertible tuple is convex on `[1, 2]` (tex line 2056). -/
theorem pressure_convexOn_Icc_one_two (hA : ∀ i, (A i).det ≠ 0) :
    ConvexOn ℝ (Icc 1 2) (pressure A) :=
  pressure_convexOn_of_svf_eq_exp hA (convex_Icc 1 2)
    (fun _ hs => zero_le_one.trans hs.1)
    (fun B => Real.log ‖B‖ - Real.log (|B.det| / ‖B‖)) (fun B => Real.log (|B.det| / ‖B‖))
    (fun _ hs w => svf_eq_exp_of_mem_Icc_one_two (Convexity.det_word_ne_zero hA w) hs)

/-- The pressure of an invertible tuple is convex on `[2, ∞)`; there
`P(𝖠, s) = lim_n n⁻¹ log ∑_{|𝐢| = n} |det A_𝐢|^{s/2}`. -/
theorem pressure_convexOn_Ici_two (hA : ∀ i, (A i).det ≠ 0) :
    ConvexOn ℝ (Ici 2) (pressure A) :=
  pressure_convexOn_of_svf_eq_exp hA (convex_Ici 2)
    (fun _ hs => zero_le_two.trans hs) (fun _ => 0) (fun B => Real.log |B.det| / 2)
    (fun _ hs w => svf_eq_exp_of_mem_Ici_two (Convexity.det_word_ne_zero hA w) hs)

/-- Tex lines 2153 and 2154: the pressure `s ↦ P(𝖠, s)` of a tuple `𝖠 ∈ GL_2(ℝ)^N` is convex
between consecutive integers, that is, on every interval `[k, k + 1]` with `k ∈ ℕ`. -/
theorem pressure_convexOn_Icc_nat (hA : ∀ i, (A i).det ≠ 0) (k : ℕ) :
    ConvexOn ℝ (Icc (k : ℝ) (k + 1)) (pressure A) := by
  rcases k with _ | _ | k
  · simpa using pressure_convexOn_Icc_zero_one hA
  · have h : ((0 + 1 : ℕ) : ℝ) + 1 = 2 := by norm_num
    rw [h]
    simpa using pressure_convexOn_Icc_one_two hA
  · refine (pressure_convexOn_Ici_two hA).subset (fun x hx => ?_) (convex_Icc _ _)
    have : (2 : ℝ) ≤ ((k + 1 + 1 : ℕ) : ℝ) := by
      have : (2 : ℕ) ≤ k + 1 + 1 := by omega
      exact_mod_cast this
    exact this.trans hx.1

/-! ### Continuity and monotonicity of the pressure -/

/-- The singular value sums move between `(ρⁿ)^δ` and `(Rⁿ)^δ` times their value when the
exponent grows by `δ ≥ 0`, where `ρ ≤ α_2(A_i)` and `α_1(A_i) ≤ R`. -/
theorem svfSum_add_bounds (hA : ∀ i, (A i).det ≠ 0) {ρ R : ℝ} (hρ : 0 ≤ ρ) (hR : 0 ≤ R)
    (hρA : ∀ i, ρ ≤ |(A i).det| / ‖A i‖) (hRA : ∀ i, ‖A i‖ ≤ R) (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (n : ℕ) :
    (ρ ^ n) ^ δ * svfSum A s n ≤ svfSum A (s + δ) n ∧
      svfSum A (s + δ) n ≤ (R ^ n) ^ δ * svfSum A s n := by
  rw [svfSum, svfSum, Finset.mul_sum, Finset.mul_sum]
  constructor
  · refine Finset.sum_le_sum fun w _ => ?_
    have hw := Convexity.det_word_ne_zero hA (List.ofFn w)
    refine le_trans ?_ (Convexity.le_svf_add hw s hδ)
    refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (pow_nonneg hρ _) ?_ hδ)
      (svf_nonneg _ _)
    have := Convexity.pow_le_abs_det_div_norm_word hρ hA hρA (List.ofFn w)
    rwa [List.length_ofFn] at this
  · refine Finset.sum_le_sum fun w _ => ?_
    have hw := Convexity.det_word_ne_zero hA (List.ofFn w)
    refine (Convexity.svf_add_le hw s hδ).trans ?_
    refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (norm_nonneg _) ?_ hδ)
      (svf_nonneg _ _)
    have := Convexity.norm_word_le hR hRA (List.ofFn w)
    rwa [List.length_ofFn] at this

/-- The increments of the pressure of an invertible tuple:
`(t - s) log ρ ≤ P(𝖠, t) - P(𝖠, s) ≤ (t - s) log R` for `0 ≤ s ≤ t`, where `0 < ρ ≤ α_2(A_i)` and
`α_1(A_i) ≤ R` for every `i`. -/
theorem pressure_increment_bounds [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρA : ∀ i, ρ ≤ |(A i).det| / ‖A i‖) (hRA : ∀ i, ‖A i‖ ≤ R) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    (t - s) * Real.log ρ ≤ pressure A t - pressure A s ∧
      pressure A t - pressure A s ≤ (t - s) * Real.log R := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hρR : ρ ≤ R :=
    (hρA i).trans ((abs_det_div_norm_le_norm (hA i)).trans (hRA i))
  have hR : 0 < R := hρ.trans_le hρR
  set δ := t - s
  have hδ : 0 ≤ δ := sub_nonneg.2 hst
  have ht : t = s + δ := by ring
  have hsδ : 0 ≤ s + δ := add_nonneg hs hδ
  have hpos := fun (u : ℝ) (hu : 0 ≤ u) (n : ℕ) => Convexity.svfSum_pos hA hu n
  have htend := fun (u : ℝ) (hu : 0 ≤ u) => Convexity.tendsto_pressure hA hu
  rw [ht]
  constructor
  · have hle : (fun n : ℕ => δ * Real.log ρ + Real.log (svfSum A s n) / n) ≤ᶠ[atTop]
        fun n : ℕ => Real.log (svfSum A (s + δ) n) / n := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hp : 0 < (ρ ^ n) ^ δ := Real.rpow_pos_of_pos (pow_pos hρ _) _
      have hlog := Real.log_le_log (mul_pos hp (hpos s hs n))
        (svfSum_add_bounds hA hρ.le hR.le hρA hRA s hδ n).1
      rw [Real.log_mul hp.ne' (hpos s hs n).ne', Real.log_rpow (pow_pos hρ _),
        Real.log_pow] at hlog
      rw [le_div_iff₀ hn', add_mul, div_mul_cancel₀ _ hn'.ne']
      linarith [mul_assoc δ (n : ℝ) (Real.log ρ), mul_right_comm δ (n : ℝ) (Real.log ρ)]
    have := le_of_tendsto_of_tendsto (tendsto_const_nhds.add (htend s hs)) (htend _ hsδ) hle
    linarith
  · have hle : (fun n : ℕ => Real.log (svfSum A (s + δ) n) / n) ≤ᶠ[atTop]
        fun n : ℕ => δ * Real.log R + Real.log (svfSum A s n) / n := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hp : 0 < (R ^ n) ^ δ := Real.rpow_pos_of_pos (pow_pos hR _) _
      have hlog := Real.log_le_log (hpos _ hsδ n)
        (svfSum_add_bounds hA hρ.le hR.le hρA hRA s hδ n).2
      rw [Real.log_mul hp.ne' (hpos s hs n).ne', Real.log_rpow (pow_pos hR _),
        Real.log_pow] at hlog
      rw [div_le_iff₀ hn', add_mul, div_mul_cancel₀ _ hn'.ne']
      linarith [mul_assoc δ (n : ℝ) (Real.log R), mul_right_comm δ (n : ℝ) (Real.log R)]
    have := le_of_tendsto_of_tendsto (htend _ hsδ) (tendsto_const_nhds.add (htend s hs)) hle
    linarith

/-- Tex lines 2153 and 2154: the pressure `s ↦ P(𝖠, s)` of a tuple `𝖠 ∈ GL_2(ℝ)^N` is continuous
on `[0, ∞)`; it is Lipschitz there. -/
theorem pressure_continuousOn_Ici (hA : ∀ i, (A i).det ≠ 0) :
    ContinuousOn (pressure A) (Ici 0) := by
  by_cases hι : Nonempty ι
  swap
  · have hconst : pressure A = fun _ => 0 := by
      funext s
      have hsum : ∀ n : ℕ, 1 ≤ n → svfSum A s n = 0 := by
        intro n hn
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
        have : IsEmpty (Fin (1 + m) → ι) := by
          rw [not_nonempty_iff] at hι
          infer_instance
        simp [svfSum]
      have himg : (fun n : ℕ => Real.log (svfSum A s n) / n) '' Ici 1 = {0} := by
        ext x
        simp only [mem_image, mem_Ici, mem_singleton_iff]
        constructor
        · rintro ⟨n, hn, rfl⟩
          rw [hsum n hn, Real.log_zero, zero_div]
        · rintro rfl
          exact ⟨1, le_rfl, by rw [hsum 1 le_rfl, Real.log_zero, zero_div]⟩
      rw [pressure, himg, csInf_singleton]
    rw [hconst]
    exact continuousOn_const
  obtain ⟨ρ, R, hρ, hρR, hρA, hRA⟩ := Convexity.exists_singular_bounds hA
  set K : ℝ := max |Real.log ρ| |Real.log R|
  have hK : 0 ≤ K := le_max_of_le_left (abs_nonneg _)
  have habs : ∀ x y : ℝ, 0 ≤ x → x ≤ y → |pressure A x - pressure A y| ≤ K * |x - y| := by
    intro x y hx hxy
    obtain ⟨h1, h2⟩ := pressure_increment_bounds hA hρ hρA hRA hx hxy
    have hxy' : 0 ≤ y - x := sub_nonneg.2 hxy
    rw [abs_sub_comm, abs_sub_comm x y, abs_of_nonneg hxy', abs_le]
    have hρK : -K ≤ Real.log ρ := (neg_le.2 (le_max_left _ _ |>.trans' (neg_le_abs _)))
    have hRK : Real.log R ≤ K := (le_abs_self _).trans (le_max_right _ _)
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hρK hxy']
    · nlinarith [mul_le_mul_of_nonneg_left hRK hxy']
  refine LipschitzOnWith.continuousOn (K := K.toNNReal)
    (LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_)
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK]
  rcases le_total x y with hxy | hxy
  · exact habs x y hx hxy
  · rw [abs_sub_comm, abs_sub_comm x y]
    exact habs y x hy hxy

/-- `P(𝖠, 0) = log N`, so `P(𝖠, 0) ≥ 0` for a non-empty alphabet (tex line 2058); no hypothesis on
the matrices is needed, since `φ^0 = 1`. -/
theorem pressure_at_zero : pressure A 0 = Real.log (Fintype.card ι) := by
  have hsum : ∀ n : ℕ, svfSum A 0 n = (Fintype.card ι : ℝ) ^ n := fun n => by
    simp [svfSum, svf]
  have himg : (fun n : ℕ => Real.log (svfSum A 0 n) / n) '' Ici 1 =
      {Real.log (Fintype.card ι)} := by
    ext x
    simp only [mem_image, mem_Ici, mem_singleton_iff]
    constructor
    · rintro ⟨n, hn, rfl⟩
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      rw [hsum n, Real.log_pow, mul_div_cancel_left₀ _ hn']
    · rintro rfl
      exact ⟨1, le_rfl, by rw [hsum 1, pow_one, Nat.cast_one, div_one]⟩
  rw [pressure, himg, csInf_singleton]

/-- Tex lines 2154 and 2155: if `max_i ‖A_i‖ < 1`, the pressure is strictly decreasing on
`[0, ∞)`. -/
theorem pressure_strictAntiOn_Ici [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0)
    (hlt : ∀ i, ‖A i‖ < 1) : StrictAntiOn (pressure A) (Ici 0) := by
  obtain ⟨ρ, R, hρ, hρR, hρA, hRA⟩ := Convexity.exists_singular_bounds hA
  obtain ⟨i₁, -, h₁⟩ := Finset.exists_max_image Finset.univ (fun i => ‖A i‖)
    Finset.univ_nonempty
  have hR1 : ∀ i, ‖A i‖ ≤ ‖A i₁‖ := fun i => h₁ i (Finset.mem_univ _)
  have hlogR : Real.log ‖A i₁‖ < 0 :=
    Real.log_neg (norm_pos_of_det_ne_zero (hA i₁)) (hlt i₁)
  intro s hs t _ hst
  have h' := (pressure_increment_bounds hA hρ hρA hR1 hs hst.le).2
  have hneg : (t - s) * Real.log ‖A i₁‖ < 0 := mul_neg_of_pos_of_neg (sub_pos.2 hst) hlogR
  linarith

/-- Tex line 2155: if `max_i ‖A_i‖ < 1`, then `P(𝖠, s) → -∞` as `s → ∞`. -/
theorem pressure_tendsto_atBot [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0)
    (hlt : ∀ i, ‖A i‖ < 1) : Tendsto (pressure A) atTop atBot := by
  obtain ⟨ρ, R, hρ, hρR, hρA, hRA⟩ := Convexity.exists_singular_bounds hA
  obtain ⟨i₁, -, h₁⟩ := Finset.exists_max_image Finset.univ (fun i => ‖A i‖)
    Finset.univ_nonempty
  have hR1 : ∀ i, ‖A i‖ ≤ ‖A i₁‖ := fun i => h₁ i (Finset.mem_univ _)
  have hlogR : Real.log ‖A i₁‖ < 0 :=
    Real.log_neg (norm_pos_of_det_ne_zero (hA i₁)) (hlt i₁)
  have hlin : Tendsto (fun t : ℝ => pressure A 0 + t * Real.log ‖A i₁‖) atTop atBot :=
    tendsto_atBot_add_const_left _ _ ((tendsto_mul_const_atBot_of_neg hlogR).2 tendsto_id)
  refine tendsto_atBot_mono' atTop ?_ hlin
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have h' := (pressure_increment_bounds hA hρ hρA hR1 le_rfl ht).2
  rw [sub_zero] at h'
  linarith

/-- Tex lines 2155 to 2157: if `max_i ‖A_i‖ < 1`, the pressure has a unique zero on `[0, ∞)`,
which defines the affinity dimension `dimaff(𝖠)`. -/
theorem pressure_existsUnique_eq_zero [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0)
    (hlt : ∀ i, ‖A i‖ < 1) : ∃! s : ℝ, 0 ≤ s ∧ pressure A s = 0 := by
  have h0 : 0 ≤ pressure A 0 := by
    rw [pressure_at_zero]
    exact Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  obtain ⟨x, hx, hx0⟩ : ∃ x : ℝ, pressure A x < 0 ∧ 0 ≤ x :=
    (((pressure_tendsto_atBot hA hlt).eventually (eventually_lt_atBot (0 : ℝ))).and
      (eventually_ge_atTop (0 : ℝ))).exists
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hx0
    ((pressure_continuousOn_Ici hA).mono Icc_subset_Ici_self)
    (⟨hx.le, h0⟩ : (0 : ℝ) ∈ Icc (pressure A x) (pressure A 0))
  exact ⟨z, ⟨hz.1, hz0⟩, fun w hw =>
    (pressure_strictAntiOn_Ici hA hlt).injOn hw.1 hz.1 (hw.2.trans hz0.symm)⟩

end MatrixTuple

/-! ### The box-like specialisation -/

namespace System

variable {ι : Type*} [Fintype ι] (S : System ι)

omit [Fintype ι] in
/-- The linear parts of a box-like system are invertible. -/
theorem mat_det_ne_zero (i : ι) : (S.mat i).det ≠ 0 := by
  rw [mat]
  rcases zmod_two_cases (S.o i) with h | h <;>
    simp [h, det_fin_two, S.a_ne_zero i, S.b_ne_zero i]

/-- The pressure of a box-like system is the pressure of the tuple `S.mat`, as functions. -/
theorem pressure_eq_tuple_fun : S.pressure = MatrixTuple.pressure S.mat := rfl

/-- The pressure of a box-like system is convex between consecutive integers (tex line
2153). -/
theorem pressure_convexOn_Icc_nat (k : ℕ) : ConvexOn ℝ (Icc (k : ℝ) (k + 1)) S.pressure := by
  rw [pressure_eq_tuple_fun]
  exact MatrixTuple.pressure_convexOn_Icc_nat S.mat_det_ne_zero k

/-- The pressure of a box-like system is convex on `[2, ∞)`. -/
theorem pressure_convexOn_Ici_two : ConvexOn ℝ (Ici (2 : ℝ)) S.pressure := by
  rw [pressure_eq_tuple_fun]
  exact MatrixTuple.pressure_convexOn_Ici_two S.mat_det_ne_zero

end System

end BoxLike
