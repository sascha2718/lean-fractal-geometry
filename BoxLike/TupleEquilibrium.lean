module

/-
The thermodynamic formalism of `sec:affinity_dim` for an arbitrary tuple
`𝖠 = (A_1, …, A_N)` of invertible planar matrices, the setting of `thm:irred_eq_state`: the
existence of the limits defining `P(𝖠, s)` and `Λ(𝖠, μ, s)`, the variational inequality
`eq:variational`, and the fact that an equilibrium state that is unique among the invariant
measures is ergodic. A tuple of invertible matrices is `A : ι → Matrix (Fin 2) (Fin 2) ℝ` with
`∀ i, (A i).det ≠ 0`, as in `BoxLike/MatrixTuple.lean`. No contraction is assumed.

* `TupleIrreducible.nonempty`: an irreducible tuple has a letter.
* `MatrixTuple.word_det_ne_zero`, `MatrixTuple.norm_word_pos`, `MatrixTuple.svf_word_pos`: the
  products `A_𝐢` are invertible and `φ^s(A_𝐢) > 0`.
* `MatrixTuple.normLowerBound`, `MatrixTuple.pow_le_norm_word`, `MatrixTuple.detLowerBound`,
  `MatrixTuple.pow_le_abs_det_word`: `δ^{|𝐢|} ≤ ‖A_𝐢‖` and `d^{|𝐢|} ≤ |det A_𝐢|` with
  `δ, d > 0`, from `‖A_𝐢‖ ≥ ‖A_𝐢 B‖ / ‖B‖`, applied to `B = A_i⁻¹`.
* `MatrixTuple.exists_le_log_svf_word`: `log φ^s(A_𝐢) ≥ c |𝐢|` for some constant `c`.
* `MatrixTuple.svfSum_add_le`, `MatrixTuple.tendsto_pressure`: sub-multiplicativity of the
  sums `∑_{|𝐢| = n} φ^s(A_𝐢)` and the existence of the limit defining `P(𝖠, s)`, by Fekete's
  lemma.
* `MatrixTuple.tendsto_energyLim`: the limit defining `Λ(𝖠, μ, s)` exists for an invariant `μ`.
* `MatrixTuple.entropy_add_energyLim_le_pressure`: `eq:variational`.
* `negMulLog_mix_le`, `blockEntropy_mix_le`, `entropy_mix_le`, `integral_futureWord_mix`: the
  entropy of a convex combination is at most the combination of the entropies, and the
  integrals of functions of the prefixes are affine.
* `cond_measurePreserving`, `measureReal_eq_mix_cond`: for an invariant set `E` the conditional
  measures `μ[·|E]` and `μ[·|Eᶜ]` are invariant and `μ` is their convex combination.
* `MatrixTuple.IsEquilibriumState.of_mix`: a component of positive weight of an equilibrium
  state is an equilibrium state.
* `MatrixTuple.ergodic_of_unique`: an equilibrium state that is the only invariant equilibrium
  state is ergodic. This is the remark of Feng–Käenmäki before their Proposition 1.2 that the
  extreme points of the set of equilibrium states are ergodic, which the article uses for the
  ergodicity in `thm:irred_eq_state`.
* `System.ergodic_of_unique`: the specialisation to box-like systems, whose linear parts are
  invertible by `System.det_mat_ne_zero`.
-/
public import BoxLike.Classification
public import BoxLike.EntropyFactor
public import BoxLike.MatrixTuple
public import BoxLike.Variational
public import Mathlib.Probability.ConditionalProbability

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology ProbabilityTheory
open scoped Matrix.Norms.L2Operator ENNReal

/-! ### The identity matrix -/

/-- `‖I‖ = 1` for the `ℓ²` operator norm on planar matrices. -/
theorem norm_one_fin_two : ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ = 1 := by
  have h1 : (1 : Matrix (Fin 2) (Fin 2) ℝ) = boxMat 0 1 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [h1, norm_boxMat]
  norm_num

/-- An irreducible tuple has at least one matrix: over the empty alphabet every line is
invariant. -/
theorem TupleIrreducible.nonempty {ι : Type*} {A : ι → Matrix (Fin 2) (Fin 2) ℝ}
    (h : TupleIrreducible A) : Nonempty ι := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  exact h ⟨![1, 0], fun h0 => by simpa using congrFun h0 0, fun i => isEmptyElim i⟩

namespace MatrixTuple

variable {ι : Type*} (A : ι → Matrix (Fin 2) (Fin 2) ℝ)

/-! ### Products along words -/

/-- `A_{i 𝐢} = A_i A_𝐢`. -/
@[simp] theorem word_cons (i : ι) (w : List ι) : word A (i :: w) = A i * word A w := by
  simp [word]

variable {A}

/-- The products of invertible matrices are invertible. -/
theorem word_det_ne_zero (hA : ∀ i, (A i).det ≠ 0) (w : List ι) : (word A w).det ≠ 0 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [word_cons, Matrix.det_mul]
    exact mul_ne_zero (hA i) ih

/-- `|det A_𝐢| > 0`. -/
theorem abs_det_word_pos (hA : ∀ i, (A i).det ≠ 0) (w : List ι) : 0 < |(word A w).det| :=
  abs_pos.2 (word_det_ne_zero hA w)

/-- `‖A_𝐢‖ > 0`. -/
theorem norm_word_pos (hA : ∀ i, (A i).det ≠ 0) (w : List ι) : 0 < ‖word A w‖ := by
  refine norm_pos_iff.2 fun h => word_det_ne_zero hA w ?_
  rw [h]
  simp

/-- `φ^s(A_𝐢) > 0`. -/
theorem svf_word_pos (hA : ∀ i, (A i).det ≠ 0) (s : ℝ) (w : List ι) :
    0 < svf s (word A w) := by
  have hn := norm_word_pos hA w
  have hd := abs_det_word_pos hA w
  unfold svf
  split_ifs
  · exact Real.rpow_pos_of_pos hn _
  · exact mul_pos (Real.rpow_pos_of_pos hn _) (Real.rpow_pos_of_pos hd _)
  · exact Real.rpow_pos_of_pos hd _

/-- The singular value function is sub-multiplicative along words:
`log φ^s(A_𝐢 A_𝐣) ≤ log φ^s(A_𝐢) + log φ^s(A_𝐣)` for `s ≥ 0`. -/
theorem log_svf_word_append_le (hA : ∀ i, (A i).det ≠ 0) {s : ℝ} (hs : 0 ≤ s)
    (w w' : List ι) :
    Real.log (svf s (word A (w ++ w'))) ≤
      Real.log (svf s (word A w)) + Real.log (svf s (word A w')) := by
  have h := svf_word_pos hA s (w ++ w')
  rw [word_append] at h
  rw [← Real.log_mul (svf_word_pos hA s w).ne' (svf_word_pos hA s w').ne', word_append]
  exact Real.log_le_log h (svf_mul_le hs _ _)

/-- `log |det A_𝐢 A_𝐣| = log |det A_𝐢| + log |det A_𝐣|`. -/
theorem log_abs_det_word_append (hA : ∀ i, (A i).det ≠ 0) (w w' : List ι) :
    Real.log |(word A (w ++ w')).det| =
      Real.log |(word A w).det| + Real.log |(word A w').det| := by
  rw [word_append, Matrix.det_mul, abs_mul,
    Real.log_mul (abs_det_word_pos hA w).ne' (abs_det_word_pos hA w').ne']

/-! ### Exponential bounds on the products -/

variable [Fintype ι]

variable (A) in
/-- The constant `δ = (1 + ∑_i ‖A_i⁻¹‖)⁻¹ > 0` with `δ ‖A_i⁻¹‖ ≤ 1` for every `i`. -/
noncomputable def normLowerBound : ℝ := (1 + ∑ i, ‖(A i)⁻¹‖)⁻¹

omit [Fintype ι] in
/-- `1 + ∑_i f_i > 0` for non-negative `f`; the denominators of `normLowerBound` and
`detLowerBound`. -/
theorem one_add_sum_pos {f : ι → ℝ} [Fintype ι] (hf : ∀ i, 0 ≤ f i) : 0 < 1 + ∑ i, f i :=
  add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ => hf i)

omit [Fintype ι] in
/-- `f_i ≤ 1 + ∑_j f_j` for non-negative `f`. -/
theorem le_one_add_sum {f : ι → ℝ} [Fintype ι] (hf : ∀ i, 0 ≤ f i) (i : ι) :
    f i ≤ 1 + ∑ j, f j := by
  have := Finset.single_le_sum (f := f) (fun j _ => hf j) (Finset.mem_univ i)
  linarith

/-- `δ > 0`. -/
theorem normLowerBound_pos : 0 < normLowerBound A :=
  inv_pos.2 (one_add_sum_pos fun _ => norm_nonneg _)

/-- `δ ‖A_i⁻¹‖ ≤ 1` for every letter `i`. -/
theorem normLowerBound_mul_le (i : ι) : normLowerBound A * ‖(A i)⁻¹‖ ≤ 1 := by
  rw [normLowerBound, inv_mul_le_iff₀ (one_add_sum_pos fun _ => norm_nonneg _), mul_one]
  exact le_one_add_sum (fun j => norm_nonneg ((A j)⁻¹)) i

/-- `δ^{|𝐢|} ≤ ‖A_𝐢‖`: since `A_𝐢 = A_i⁻¹ (A_i A_𝐢)`, the norm grows at least by the factor
`‖A_i⁻¹‖⁻¹ ≥ δ` with every letter. -/
theorem pow_le_norm_word (hA : ∀ i, (A i).det ≠ 0) (w : List ι) :
    normLowerBound A ^ w.length ≤ ‖word A w‖ := by
  induction w with
  | nil => simp
  | cons i w ih =>
    have hinv : (A i)⁻¹ * A i = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hA i))
    have hle : ‖word A w‖ ≤ ‖(A i)⁻¹‖ * ‖A i * word A w‖ := by
      calc ‖word A w‖ = ‖(A i)⁻¹ * (A i * word A w)‖ := by
            rw [← mul_assoc, hinv, one_mul]
        _ ≤ ‖(A i)⁻¹‖ * ‖A i * word A w‖ := Matrix.l2_opNorm_mul _ _
    have hδ := normLowerBound_pos (A := A)
    rw [word_cons, List.length_cons, pow_succ']
    calc normLowerBound A * normLowerBound A ^ w.length
        ≤ normLowerBound A * ‖word A w‖ := mul_le_mul_of_nonneg_left ih hδ.le
      _ ≤ normLowerBound A * (‖(A i)⁻¹‖ * ‖A i * word A w‖) :=
          mul_le_mul_of_nonneg_left hle hδ.le
      _ = (normLowerBound A * ‖(A i)⁻¹‖) * ‖A i * word A w‖ := by ring
      _ ≤ 1 * ‖A i * word A w‖ :=
          mul_le_mul_of_nonneg_right (normLowerBound_mul_le i) (norm_nonneg _)
      _ = ‖A i * word A w‖ := one_mul _

variable (A) in
/-- The constant `d = (1 + ∑_i |det A_i|⁻¹)⁻¹ > 0` with `d ≤ |det A_i|` for every `i`. -/
noncomputable def detLowerBound : ℝ := (1 + ∑ i, |(A i).det|⁻¹)⁻¹

/-- `d > 0`. -/
theorem detLowerBound_pos : 0 < detLowerBound A :=
  inv_pos.2 (one_add_sum_pos fun _ => inv_nonneg.2 (abs_nonneg _))

/-- `d ≤ |det A_i|` for every letter `i` of an invertible tuple. -/
theorem detLowerBound_le (hA : ∀ i, (A i).det ≠ 0) (i : ι) : detLowerBound A ≤ |(A i).det| := by
  have hpos := abs_pos.2 (hA i)
  rw [detLowerBound, inv_le_comm₀ (one_add_sum_pos fun _ => inv_nonneg.2 (abs_nonneg _)) hpos]
  exact le_one_add_sum (fun j => inv_nonneg.2 (abs_nonneg ((A j).det))) i

/-- `d^{|𝐢|} ≤ |det A_𝐢|`, by multiplicativity of the determinant. -/
theorem pow_le_abs_det_word (hA : ∀ i, (A i).det ≠ 0) (w : List ι) :
    detLowerBound A ^ w.length ≤ |(word A w).det| := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [word_cons, Matrix.det_mul, abs_mul, List.length_cons, pow_succ']
    exact mul_le_mul (detLowerBound_le hA i) ih (pow_nonneg detLowerBound_pos.le _)
      (abs_nonneg _)

/-- `log ‖A_𝐢‖ ≥ |𝐢| log δ`. -/
theorem le_log_norm_word (hA : ∀ i, (A i).det ≠ 0) (w : List ι) :
    Real.log (normLowerBound A) * w.length ≤ Real.log ‖word A w‖ := by
  have h := Real.log_le_log (pow_pos normLowerBound_pos _) (pow_le_norm_word hA w)
  rwa [Real.log_pow, mul_comm] at h

/-- `log |det A_𝐢| ≥ |𝐢| log d`. -/
theorem le_log_abs_det_word (hA : ∀ i, (A i).det ≠ 0) (w : List ι) :
    Real.log (detLowerBound A) * w.length ≤ Real.log |(word A w).det| := by
  have h := Real.log_le_log (pow_pos detLowerBound_pos _) (pow_le_abs_det_word hA w)
  rwa [Real.log_pow, mul_comm] at h

/-- `log φ^s(A_𝐢) ≥ c |𝐢|` for a constant `c`, for every `s ≥ 0`. -/
theorem exists_le_log_svf_word (hA : ∀ i, (A i).det ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    ∃ c : ℝ, ∀ w : List ι, c * w.length ≤ Real.log (svf s (word A w)) := by
  have hn := fun w => norm_word_pos hA w
  have hd := fun w => abs_det_word_pos hA w
  have h1 := le_log_norm_word hA
  have h2 := le_log_abs_det_word hA
  by_cases hs1 : s ≤ 1
  · refine ⟨s * Real.log (normLowerBound A), fun w => ?_⟩
    rw [svf, ite_eq_left hs1, Real.log_rpow (hn w), mul_assoc]
    exact mul_le_mul_of_nonneg_left (h1 w) hs
  by_cases hs2 : s ≤ 2
  · refine ⟨(2 - s) * Real.log (normLowerBound A) + (s - 1) * Real.log (detLowerBound A),
      fun w => ?_⟩
    rw [svf, ite_eq_right hs1, ite_eq_left hs2,
      Real.log_mul (Real.rpow_pos_of_pos (hn w) _).ne' (Real.rpow_pos_of_pos (hd w) _).ne',
      Real.log_rpow (hn w), Real.log_rpow (hd w), add_mul, mul_assoc, mul_assoc]
    exact add_le_add (mul_le_mul_of_nonneg_left (h1 w) (by linarith))
      (mul_le_mul_of_nonneg_left (h2 w) (by linarith))
  · refine ⟨s / 2 * Real.log (detLowerBound A), fun w => ?_⟩
    rw [svf, ite_eq_right hs1, ite_eq_right hs2, Real.log_rpow (hd w), mul_assoc]
    exact mul_le_mul_of_nonneg_left (h2 w) (by linarith)

/-! ### The pressure -/

variable (A) in
/-- The sums `∑_{|𝐢| = n} φ^s(A_𝐢)` are sub-multiplicative in `n`. -/
theorem svfSum_add_le {s : ℝ} (hs : 0 ≤ s) (m n : ℕ) :
    svfSum A s (m + n) ≤ svfSum A s m * svfSum A s n := by
  rw [svfSum, sum_ofFn_add m n fun w => svf s (word A w), svfSum, svfSum, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun h _ => ?_
  rw [word_append]
  exact svf_mul_le hs _ _

/-- `∑_{|𝐢| = n} φ^s(A_𝐢) > 0` over a non-empty alphabet. -/
theorem svfSum_pos [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) (s : ℝ) (n : ℕ) :
    0 < svfSum A s n :=
  Finset.sum_pos (fun _ _ => svf_word_pos hA s _) Finset.univ_nonempty

/-- The sequence `log ∑_{|𝐢| = n} φ^s(A_𝐢)` is sub-additive. -/
theorem subadditive_log_svfSum [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    Subadditive fun n => Real.log (svfSum A s n) := by
  intro m n
  rw [← Real.log_mul (svfSum_pos hA s m).ne' (svfSum_pos hA s n).ne']
  exact Real.log_le_log (svfSum_pos hA s _) (svfSum_add_le A hs m n)

/-- The quotients `n⁻¹ log ∑_{|𝐢| = n} φ^s(A_𝐢)` are bounded below. -/
theorem bddBelow_log_svfSum_div [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    BddBelow (Set.range fun n : ℕ => Real.log (svfSum A s n) / n) := by
  obtain ⟨c, hc⟩ := exists_le_log_svf_word hA hs
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine ⟨min 0 c, ?_⟩
  rintro _ ⟨n, rfl⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    refine (min_le_right _ _).trans ?_
    rw [le_div_iff₀ hn']
    have hw := hc (List.ofFn fun _ : Fin n => i)
    rw [List.length_ofFn] at hw
    have hle : svf s (word A (List.ofFn fun _ : Fin n => i)) ≤ svfSum A s n :=
      Finset.single_le_sum (f := fun w : Fin n → ι => svf s (word A (List.ofFn w)))
        (fun w _ => (svf_word_pos hA s _).le) (Finset.mem_univ _)
    exact hw.trans (Real.log_le_log (svf_word_pos hA s _) hle)

/-- The limit defining `P(𝖠, s)` exists, by Fekete's lemma, and equals the infimum
`MatrixTuple.pressure`. -/
theorem tendsto_pressure [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun n : ℕ => Real.log (svfSum A s n) / n) atTop (𝓝 (pressure A s)) := by
  have h := (subadditive_log_svfSum hA hs).tendsto_lim (bddBelow_log_svfSum_div hA hs)
  rwa [Subadditive.lim] at h

/-- The pressure is at most `n⁻¹ log ∑_{|𝐢| = n} φ^s(A_𝐢)` for every `n ≥ 1`. -/
theorem pressure_le_log_svfSum_div [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) {s : ℝ}
    (hs : 0 ≤ s) {n : ℕ} (hn : 1 ≤ n) : pressure A s ≤ Real.log (svfSum A s n) / n :=
  csInf_le (BddBelow.mono (Set.image_subset_range _ _) (bddBelow_log_svfSum_div hA hs))
    ⟨n, hn, rfl⟩

/-! ### The energy and the variational inequality -/

variable [MeasurableSpace ι] [MeasurableSingletonClass ι] {μ : Measure (ℤ → ι)}
  [IsProbabilityMeasure μ]

/-- The limit defining `Λ(𝖠, μ, s)` exists for an invariant measure, by Fekete's lemma. -/
theorem tendsto_energyLim (hA : ∀ i, (A i).det ≠ 0) (hμ : MeasurePreserving (shift 1) μ μ)
    {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun n : ℕ => (∫ x, Real.log (svf s (word A (futureWord x n))) ∂μ) / n) atTop
      (𝓝 (energyLim A s μ)) := by
  obtain ⟨c, hc⟩ := exists_le_log_svf_word hA hs
  obtain ⟨L, hL⟩ := exists_tendsto_integral_futureWord_div hμ
    (G := fun w => Real.log (svf s (word A w))) (log_svf_word_append_le hA hs) hc
  rw [energyLim, hL.limUnder_eq]
  exact hL

/-- `eq:variational` at level `n`:
`∫ log φ^s(A_{𝐢|_n}) dμ(𝐢) + H_μ(𝒫_0^{n-1}) ≤ log ∑_{|𝐢| = n} φ^s(A_𝐢)`, by Jensen's
inequality for the logarithm with the weights `μ([𝐢])`. -/
theorem integral_log_svf_add_blockEntropy_le (hA : ∀ i, (A i).det ≠ 0) (n : ℕ) (s : ℝ) :
    (∫ x, Real.log (svf s (word A (futureWord x n))) ∂μ) + blockEntropy μ n
      ≤ Real.log (svfSum A s n) := by
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
  have hZ : 0 < svfSum A s n := svfSum_pos hA s n
  have h := sum_mul_log_add_sum_negMulLog_le (p := fun w : Fin n → ι => μ.real (cylinder w))
    (a := fun w => svf s (word A (List.ofFn w))) (fun _ => measureReal_nonneg)
    (sum_measureReal_cylinder μ n) (fun _ => svf_word_pos hA s _) hZ
  rw [← svfSum, div_self hZ.ne', sub_self, add_zero] at h
  rw [integral_comp_futureWord_eq_sum μ fun w => Real.log (svf s (word A w))]
  exact h

/-- `eq:variational`: `h_0(μ) + Λ(𝖠, μ, s) ≤ P(𝖠, s)` for every invariant probability measure
`μ` and every `s ≥ 0`. -/
theorem entropy_add_energyLim_le_pressure (hA : ∀ i, (A i).det ≠ 0)
    (hμ : MeasurePreserving (shift 1) μ μ) {s : ℝ} (hs : 0 ≤ s) :
    entropy μ + energyLim A s μ ≤ pressure A s := by
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
  refine le_of_tendsto_of_tendsto' ((tendsto_entropy hμ).add (tendsto_energyLim hA hμ hs))
    (tendsto_pressure hA hs) fun n => ?_
  rw [← add_div, add_comm]
  exact div_le_div_of_nonneg_right (integral_log_svf_add_blockEntropy_le hA n s)
    (Nat.cast_nonneg n)

end MatrixTuple

/-! ### Convex combinations of invariant measures -/

/-- The defect of concavity of `-x log x` on a convex combination:
`η(t a + (1 - t) b) ≤ t η(a) + (1 - t) η(b) + a η(t) + b η(1 - t)` with `η(x) = -x log x`,
from the sub-additivity `negMulLog_add_le` and `η(t a) = a η(t) + t η(a)`. -/
theorem negMulLog_mix_le {t a b : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.negMulLog (t * a + (1 - t) * b) ≤
      t * Real.negMulLog a + (1 - t) * Real.negMulLog b +
        (a * Real.negMulLog t + b * Real.negMulLog (1 - t)) := by
  have h := negMulLog_add_le (mul_nonneg ht0 ha) (mul_nonneg (by linarith : 0 ≤ 1 - t) hb)
  rw [Real.negMulLog_mul, Real.negMulLog_mul] at h
  linarith

section Mixture

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ μ₁ μ₂ : Measure (ℤ → α)} {t : ℝ}

/-- The block entropy of a convex combination `μ = t μ_1 + (1 - t) μ_2` is at most the convex
combination of the block entropies plus `η(t) + η(1 - t)`. -/
theorem blockEntropy_mix_le [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1)
    (hmix : ∀ {n : ℕ} (w : Fin n → α),
      μ.real (cylinder w) = t * μ₁.real (cylinder w) + (1 - t) * μ₂.real (cylinder w))
    (n : ℕ) :
    blockEntropy μ n ≤ t * blockEntropy μ₁ n + (1 - t) * blockEntropy μ₂ n +
      (Real.negMulLog t + Real.negMulLog (1 - t)) := by
  have key := Finset.sum_le_sum fun (w : Fin n → α) (_ : w ∈ Finset.univ) =>
    negMulLog_mix_le ht0 ht1 (measureReal_nonneg (μ := μ₁) (s := cylinder w))
      (measureReal_nonneg (μ := μ₂) (s := cylinder w))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    sum_measureReal_cylinder, one_mul] at key
  simp only [blockEntropy, hmix]
  exact key

/-- The entropy of a convex combination of invariant probability measures is at most the
convex combination of the entropies. -/
theorem entropy_mix_le [IsProbabilityMeasure μ] [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (hμ : MeasurePreserving (shift 1) μ μ)
    (hμ₁ : MeasurePreserving (shift 1) μ₁ μ₁) (hμ₂ : MeasurePreserving (shift 1) μ₂ μ₂)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hmix : ∀ {n : ℕ} (w : Fin n → α),
      μ.real (cylinder w) = t * μ₁.real (cylinder w) + (1 - t) * μ₂.real (cylinder w)) :
    entropy μ ≤ t * entropy μ₁ + (1 - t) * entropy μ₂ := by
  set c := Real.negMulLog t + Real.negMulLog (1 - t)
  have hlim : Tendsto (fun n : ℕ => (t * blockEntropy μ₁ n + (1 - t) * blockEntropy μ₂ n + c) /
      n) atTop (𝓝 (t * entropy μ₁ + (1 - t) * entropy μ₂ + 0)) := by
    refine ((((tendsto_entropy hμ₁).const_mul t).add ((tendsto_entropy hμ₂).const_mul (1 - t))).add
      (tendsto_const_div_atTop_nhds_zero_nat c)).congr fun n => ?_
    simp only [add_div, mul_div_assoc]
  rw [add_zero] at hlim
  exact le_of_tendsto_of_tendsto' (tendsto_entropy hμ) hlim fun n =>
    div_le_div_of_nonneg_right (blockEntropy_mix_le ht0 ht1 hmix n) (Nat.cast_nonneg n)

/-- The integral of a function of the prefix `𝐢|_n` is affine along a convex combination of
measures. -/
theorem integral_futureWord_mix [IsFiniteMeasure μ] [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (hmix : ∀ {n : ℕ} (w : Fin n → α),
      μ.real (cylinder w) = t * μ₁.real (cylinder w) + (1 - t) * μ₂.real (cylinder w))
    (G : List α → ℝ) (n : ℕ) :
    ∫ x, G (futureWord x n) ∂μ =
      t * ∫ x, G (futureWord x n) ∂μ₁ + (1 - t) * ∫ x, G (futureWord x n) ∂μ₂ := by
  rw [integral_comp_futureWord_eq_sum μ G n, integral_comp_futureWord_eq_sum μ₁ G n,
    integral_comp_futureWord_eq_sum μ₂ G n, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [hmix]
  ring

end Mixture

section Conditional

variable {α : Type*} [MeasurableSpace α] {μ : Measure (ℤ → α)} {E : Set (ℤ → α)}

/-- For an invariant set `E` the conditional measure `μ[·|E]` of an invariant measure is
invariant. -/
theorem cond_measurePreserving (hμ : MeasurePreserving (shift 1) μ μ) (hE : MeasurableSet E)
    (hinv : shift 1 ⁻¹' E = E) : MeasurePreserving (shift 1) μ[|E] μ[|E] := by
  have h := hμ.restrict_preimage hE
  rw [hinv] at h
  refine ⟨measurable_shift 1, ?_⟩
  rw [ProbabilityTheory.cond, Measure.map_smul, h.map_eq]
  exact (measurable_shift 1).aemeasurable

/-- A probability measure is the convex combination
`μ = μ(E) μ[·|E] + (1 - μ(E)) μ[·|Eᶜ]` of its conditional measures, when `0 < μ(E) < 1`. -/
theorem measureReal_eq_mix_cond [IsProbabilityMeasure μ] (hE : MeasurableSet E)
    (hE0 : μ E ≠ 0) (hE1 : μ Eᶜ ≠ 0) (A : Set (ℤ → α)) :
    μ.real A = μ.real E * (μ[|E]).real A + (1 - μ.real E) * (μ[|Eᶜ]).real A := by
  have hr0 : μ.real E ≠ 0 := by
    rw [measureReal_def]
    exact ENNReal.toReal_ne_zero.2 ⟨hE0, measure_ne_top _ _⟩
  have hr1 : μ.real Eᶜ ≠ 0 := by
    rw [measureReal_def]
    exact ENNReal.toReal_ne_zero.2 ⟨hE1, measure_ne_top _ _⟩
  have hc : 1 - μ.real E = μ.real Eᶜ := by
    rw [measureReal_compl hE, probReal_univ]
  have h1 : (μ[|E]).real A = (μ.real E)⁻¹ * μ.real (E ∩ A) := by
    rw [measureReal_def, cond_apply hE, ENNReal.toReal_mul, ENNReal.toReal_inv]
    rfl
  have h2 : (μ[|Eᶜ]).real A = (μ.real Eᶜ)⁻¹ * μ.real (Eᶜ ∩ A) := by
    rw [measureReal_def, cond_apply hE.compl, ENNReal.toReal_mul, ENNReal.toReal_inv]
    rfl
  have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := A) hE
  rw [hc, h1, h2, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hr0, mul_inv_cancel₀ hr1, one_mul,
    one_mul, ← hsplit, Set.inter_comm, Set.sdiff_eq, Set.inter_comm A Eᶜ]

end Conditional

namespace MatrixTuple

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {A : ι → Matrix (Fin 2) (Fin 2) ℝ}

/-- The energy is affine along a convex combination of invariant probability measures. -/
theorem energyLim_mix (hA : ∀ i, (A i).det ≠ 0) {s : ℝ} (hs : 0 ≤ s)
    {μ μ₁ μ₂ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (hμ : MeasurePreserving (shift 1) μ μ)
    (hμ₁ : MeasurePreserving (shift 1) μ₁ μ₁) (hμ₂ : MeasurePreserving (shift 1) μ₂ μ₂) {t : ℝ}
    (hmix : ∀ {n : ℕ} (w : Fin n → ι),
      μ.real (cylinder w) = t * μ₁.real (cylinder w) + (1 - t) * μ₂.real (cylinder w)) :
    energyLim A s μ = t * energyLim A s μ₁ + (1 - t) * energyLim A s μ₂ := by
  refine tendsto_nhds_unique (tendsto_energyLim hA hμ hs) ?_
  refine (((tendsto_energyLim hA hμ₁ hs).const_mul t).add
    ((tendsto_energyLim hA hμ₂ hs).const_mul (1 - t))).congr fun n => ?_
  rw [integral_futureWord_mix hmix (fun w => Real.log (svf s (word A w))) n, add_div,
    mul_div_assoc, mul_div_assoc]

/-- A component of positive weight of an `s`-equilibrium state is an `s`-equilibrium state:
the entropy is at most affine and the energy is affine along convex combinations, and every
invariant measure satisfies `eq:variational`. -/
theorem IsEquilibriumState.of_mix (hA : ∀ i, (A i).det ≠ 0) {s : ℝ} (hs : 0 ≤ s)
    {μ μ₁ μ₂ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (hμ : MeasurePreserving (shift 1) μ μ)
    (hμ₁ : MeasurePreserving (shift 1) μ₁ μ₁) (hμ₂ : MeasurePreserving (shift 1) μ₂ μ₂) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hmix : ∀ {n : ℕ} (w : Fin n → ι),
      μ.real (cylinder w) = t * μ₁.real (cylinder w) + (1 - t) * μ₂.real (cylinder w))
    (heq : IsEquilibriumState A s μ) : IsEquilibriumState A s μ₁ := by
  have hE := entropy_mix_le hμ hμ₁ hμ₂ ht0.le ht1 hmix
  have hΛ := energyLim_mix hA hs hμ hμ₁ hμ₂ hmix
  have v₁ := entropy_add_energyLim_le_pressure hA hμ₁ hs
  have v₂ := entropy_add_energyLim_le_pressure hA hμ₂ hs
  have h₂ := mul_le_mul_of_nonneg_left v₂ (by linarith : (0 : ℝ) ≤ 1 - t)
  have key : t * pressure A s ≤ t * (entropy μ₁ + energyLim A s μ₁) := by
    have : pressure A s = entropy μ + energyLim A s μ := heq
    nlinarith
  exact le_antisymm (le_of_mul_le_mul_left key ht0) v₁

/-- An `s`-equilibrium state that is the only invariant `s`-equilibrium state is ergodic. If an
invariant set `E` had `0 < μ(E) < 1`, the conditional measure `μ[·|E]` would be a component of
positive weight, hence an equilibrium state, hence `μ`, but it vanishes on `Eᶜ`. This is the
remark of Feng–Käenmäki (Discrete Contin. Dyn. Syst. 30 (2011), before Definition 1.1) that the
extreme points of the set of equilibrium states are ergodic. -/
theorem ergodic_of_unique (hA : ∀ i, (A i).det ≠ 0) {s : ℝ} (hs : 0 ≤ s)
    {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ)
    (heq : IsEquilibriumState A s μ)
    (huniq : ∀ ν : Measure (ℤ → ι), IsProbabilityMeasure ν → MeasurePreserving (shift 1) ν ν →
      IsEquilibriumState A s ν → ν = μ) :
    Ergodic (shift 1) μ := by
  refine ⟨hμ, ⟨fun E hE hinv => ?_⟩⟩
  rw [eventuallyEmptyOrUniv_iff', ae_eq_empty, ae_eq_univ]
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hE0, hE1⟩ := hcon
  have hinvc : shift 1 ⁻¹' Eᶜ = Eᶜ := by rw [Set.preimage_compl, hinv]
  have := cond_isProbabilityMeasure (μ := μ) hE0
  have := cond_isProbabilityMeasure (μ := μ) hE1
  have hμ₁ := cond_measurePreserving hμ hE hinv
  have hμ₂ := cond_measurePreserving hμ hE.compl hinvc
  have ht0 : 0 < μ.real E := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hE0 (measure_ne_top _ _)
  have heq₁ := heq.of_mix hA hs hμ hμ₁ hμ₂ ht0 measureReal_le_one
    (fun w => measureReal_eq_mix_cond hE hE0 hE1 (cylinder w))
  have h := huniq _ inferInstance hμ₁ heq₁
  have hzero : μ[Eᶜ|E] = 0 := by
    rw [cond_apply hE, Set.inter_compl_self, measure_empty, mul_zero]
  rw [h] at hzero
  exact hE1 hzero

end MatrixTuple

/-! ### Box-like systems -/

namespace System

variable {ι : Type*} (S : System ι) [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- `MatrixTuple.ergodic_of_unique` for a box-like system: an `s`-equilibrium state that is the
only invariant `s`-equilibrium state is ergodic. -/
theorem ergodic_of_unique {s : ℝ} (hs : 0 ≤ s) {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState s μ)
    (huniq : ∀ ν : Measure (ℤ → ι), IsProbabilityMeasure ν → MeasurePreserving (shift 1) ν ν →
      S.IsEquilibriumState s ν → ν = μ) :
    Ergodic (shift 1) μ :=
  MatrixTuple.ergodic_of_unique S.det_mat_ne_zero hs hμ heq huniq

end System

end BoxLike
