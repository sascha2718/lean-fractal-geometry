import Mathlib
import GeometricMeasureTheory.Box.BoxDimension
import FractalGeometry.LinearCocycles.Pressure
import FractalGeometry.LinearCocycles.Products
import FractalGeometry.LinearCocycles.SingularValue
import FractalGeometry.LinearCocycles.SingularValueExponents
import FractalGeometry.Symbolic.Concatenation


open GeometricMeasureTheory

namespace FractalGeometry

open Filter Topology Set Matrix

open scoped Matrix.Norms.L2Operator

namespace MatrixTuple

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

def quarterTurn : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

theorem adjugate_eq_quarterTurn (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.adjugate = quarterTurn * Aᵀ * quarterTurnᵀ := by
  rw [adjugate_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [quarterTurn, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

theorem norm_one_fin_two_le : ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self (1 : Matrix (Fin 2) (Fin 2) ℝ)
  rw [conjTranspose_one, one_mul] at h
  nlinarith [norm_nonneg (1 : Matrix (Fin 2) (Fin 2) ℝ)]

theorem norm_quarterTurn_le : ‖quarterTurn‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self quarterTurn
  have h1 : quarterTurnᴴ * quarterTurn = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [quarterTurn, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h1] at h
  nlinarith [norm_nonneg quarterTurn, norm_one_fin_two_le]

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

theorem norm_adjugate (A : Matrix (Fin 2) (Fin 2) ℝ) : ‖A.adjugate‖ = ‖A‖ := by
  refine le_antisymm (norm_adjugate_le A) ?_
  have h := norm_adjugate_le A.adjugate
  rwa [adjugate_adjugate A (by simp), Fintype.card_fin, Nat.sub_self, pow_zero, one_smul] at h

theorem norm_inv_eq_norm_div_abs_det (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖A⁻¹‖ = ‖A‖ / |A.det| := by
  rw [inv_def, Ring.inverse_eq_inv', norm_smul, norm_inv, Real.norm_eq_abs, norm_adjugate,
    div_eq_inv_mul]

theorem norm_pos_of_det_ne_zero {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0) : 0 < ‖A‖ := by
  rcases (norm_nonneg A).lt_or_eq with h | h
  · exact h
  · have := abs_det_le_norm_sq A
    rw [← h] at this
    have h2 : |A.det| = 0 := le_antisymm (by simpa using this) (abs_nonneg _)
    exact absurd (abs_eq_zero.1 h2) hA

theorem abs_det_div_norm_le_norm {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0) :
    |A.det| / ‖A‖ ≤ ‖A‖ := by
  have hn := norm_pos_of_det_ne_zero hA
  rw [div_le_iff₀ hn, ← sq]
  exact abs_det_le_norm_sq A

theorem abs_det_div_norm_pos {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0) :
    0 < |A.det| / ‖A‖ :=
  div_pos (abs_pos.2 hA) (norm_pos_of_det_ne_zero hA)

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

namespace Convexity

variable {A : Matrix (Fin 2) (Fin 2) ℝ}

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

theorem rpow_le_svf (hA : A.det ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    (|A.det| / ‖A‖) ^ s ≤ svf s A := by
  have h := le_svf_add hA 0 hs
  rwa [zero_add, show svf 0 A = 1 by simp [svf], mul_one] at h

variable {ι : Type*} {B : ι → Matrix (Fin 2) (Fin 2) ℝ}

theorem word_cons (i : ι) (w : List ι) : word B (i :: w) = B i * word B w := rfl

theorem det_word_ne_zero (hB : ∀ i, (B i).det ≠ 0) (w : List ι) : (word B w).det ≠ 0 := by
  induction w with
  | nil => simp
  | cons i w ih => rw [word_cons, det_mul]; exact mul_ne_zero (hB i) ih

theorem mul_abs_det_div_norm_le {A A' : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0)
    (hA' : A'.det ≠ 0) :
    (|A.det| / ‖A‖) * (|A'.det| / ‖A'‖) ≤ |(A * A').det| / ‖A * A'‖ := by
  have hn := norm_pos_of_det_ne_zero hA
  have hn' := norm_pos_of_det_ne_zero hA'
  have hAA' : (A * A').det ≠ 0 := by rw [det_mul]; exact mul_ne_zero hA hA'
  have hnn := norm_pos_of_det_ne_zero hAA'
  rw [div_mul_div_comm, det_mul, abs_mul]
  exact div_le_div_of_nonneg_left (by positivity) hnn (l2_opNorm_mul A A')

theorem norm_word_le {R : ℝ} (hR : 0 ≤ R) (hB : ∀ i, ‖B i‖ ≤ R) (w : List ι) :
    ‖word B w‖ ≤ R ^ w.length := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [word_cons, List.length_cons, pow_succ']
    exact (l2_opNorm_mul _ _).trans (mul_le_mul (hB i) ih (norm_nonneg _) hR)

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

theorem exists_singular_bounds [Nonempty ι] (hB : ∀ i, (B i).det ≠ 0) :
    ∃ ρ R : ℝ, 0 < ρ ∧ ρ ≤ R ∧ (∀ i, ρ ≤ |(B i).det| / ‖B i‖) ∧ ∀ i, ‖B i‖ ≤ R := by
  obtain ⟨i₀, -, h₀⟩ := Finset.exists_min_image Finset.univ (fun i => |(B i).det| / ‖B i‖)
    Finset.univ_nonempty
  obtain ⟨i₁, -, h₁⟩ := Finset.exists_max_image Finset.univ (fun i => ‖B i‖)
    Finset.univ_nonempty
  refine ⟨|(B i₀).det| / ‖B i₀‖, ‖B i₁‖, abs_det_div_norm_pos (hB i₀), ?_,
    fun i => h₀ i (Finset.mem_univ _), fun i => h₁ i (Finset.mem_univ _)⟩
  exact (abs_det_div_norm_le_norm (hB i₀)).trans (h₁ i₀ (Finset.mem_univ _))

theorem svfSum_add_le {s : ℝ} (hs : 0 ≤ s) (m n : ℕ) :
    svfSum B s (m + n) ≤ svfSum B s m * svfSum B s n := by
  rw [svfSum, sum_ofFn_add m n fun w => svf s (word B w), svfSum, svfSum, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun h _ => ?_
  rw [word_append]
  exact svf_mul_le hs _ _

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

theorem svfSum_pos [Nonempty ι] (hB : ∀ i, (B i).det ≠ 0) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    0 < svfSum B s n := by
  obtain ⟨ρ, R, hρ, -, hρB, -⟩ := exists_singular_bounds hB
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos (pow_pos hρ _) _)
    (rpow_pow_le_svfSum hB hρ.le hρB hs n)

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

variable {ι : Type*} [Fintype ι] {A : ι → Matrix (Fin 2) (Fin 2) ℝ}

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

end FractalGeometry
