module

/-
The limits of `sec:lyapunov_exponents` and `eq:energy_def` of `sec:affinity_dim`, for an
invariant probability measure `μ` on the two-sided full shift over a finite alphabet. The
singular value `α_1(A) = ‖A‖` is sub-multiplicative, `α_2(A) = |det A| / ‖A‖` is
super-multiplicative on the products `A_𝐢`, and `μ` is invariant, so the limits exist by
Fekete's lemma.

* `integrable_comp_block`, `integrable_comp_futureWord`: a function of the block
  `x_0 ⋯ x_{n-1}` is integrable for every finite measure.
* `futureWord_add`, `integral_comp_shift`: `𝐢|_{m+n} = 𝐢|_m (σ^m 𝐢)|_n`, and the integral of an
  invariant measure does not change under `σ^m`.
* `exists_tendsto_integral_futureWord_div`,
  `exists_tendsto_integral_futureWord_div_of_superadditive`: Fekete's lemma for the averages
  `n⁻¹ ∫ G(𝐢|_n) dμ(𝐢)` of a sub-additive or super-additive function `G` of words.
* `System.norm_matWord`, `System.abs_det_div_norm_matWord`: `α_1(A_𝐢)` and `α_2(A_𝐢)` are the
  maximum and the minimum of the two moduli `|g'|` over `𝐢`.
* `System.tendsto_lyapunov₁`, `System.tendsto_lyapunov₂`: the limits defining `λ_1(𝖠, μ)` and
  `λ_2(𝖠, μ)` exist.
* `System.RatioLowerBound.log_le_lyapunov₂`, `System.lyapunov₂_le_lyapunov₁`,
  `System.lyapunov₁_neg`: `-∞ < λ_2(𝖠, μ) ≤ λ_1(𝖠, μ) < 0`.
* `System.tendsto_energyLim`, `System.energyLim_eq`: the `s`-energy
  `Λ(𝖠, μ, s)` as a limit, the existence of the limit, and `eq:energy_def`.
* `System.lyapBarLim`, `System.lyapBarLim_eq`: the limit defining `\overline{λ}(𝖠, ν)` is the
  integral `∫ log |g'_{j_0}| dν` for an invariant measure `ν` on the shift over `ι × ZMod 2`.
-/
public import BoxLike.Thermodynamic
public import Mathlib.Analysis.Subadditive
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator

/-! ### Functions of finitely many coordinates -/

section futureWord

variable {α : Type*}

/-- The prefix `𝐢|_n` is the list of the entries of the block `x_0 ⋯ x_{n-1}`. -/
theorem futureWord_eq_ofFn_block (x : ℤ → α) (n : ℕ) :
    futureWord x n = List.ofFn (block n x) := by
  apply List.ext_getElem <;> simp [futureWord]

/-- `𝐢|_{m+n} = 𝐢|_m (σ^m 𝐢)|_n`. -/
theorem futureWord_add (x : ℤ → α) (m n : ℕ) :
    futureWord x (m + n) = futureWord x m ++ futureWord (shift m x) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, futureWord_succ, ih, futureWord_succ, List.append_assoc, shift_apply,
      Nat.cast_add]

variable [MeasurableSpace α]

/-- The integral of an invariant measure does not change under `σ^m`, `m ∈ ℕ`. -/
theorem integral_comp_shift {μ : Measure (ℤ → α)} (hμ : MeasurePreserving (shift 1) μ μ)
    (m : ℕ) {F : (ℤ → α) → ℝ} (hF : Measurable F) :
    ∫ x, F (shift m x) ∂μ = ∫ x, F x ∂μ := by
  have h := measurePreserving_shift_natCast hμ m
  rw [← integral_map h.measurable.aemeasurable hF.aestronglyMeasurable, h.map_eq]

variable [Finite α] [MeasurableSingletonClass α]

/-- A function of the block `x_0 ⋯ x_{n-1}` is measurable: the blocks of length `n` form a
finite discrete space. -/
theorem measurable_comp_block {n : ℕ} (F : (Fin n → α) → ℝ) :
    Measurable fun x : ℤ → α => F (block n x) :=
  (Measurable.of_discrete (f := F)).comp (measurable_block n)

/-- A function of the block `x_0 ⋯ x_{n-1}` is integrable for every finite measure: it is
measurable and takes finitely many values. -/
theorem integrable_comp_block {μ : Measure (ℤ → α)} [IsFiniteMeasure μ] {n : ℕ}
    (F : (Fin n → α) → ℝ) : Integrable (fun x => F (block n x)) μ :=
  (Integrable.of_finite (f := F)).comp_measurable (measurable_block n)

/-- A function of the prefix `𝐢|_n` is measurable. -/
theorem measurable_comp_futureWord (G : List α → ℝ) (n : ℕ) :
    Measurable fun x : ℤ → α => G (futureWord x n) := by
  simp only [futureWord_eq_ofFn_block]
  exact measurable_comp_block fun w : Fin n → α => G (List.ofFn w)

/-- A function of the prefix `𝐢|_n` is integrable for every finite measure. -/
theorem integrable_comp_futureWord {μ : Measure (ℤ → α)} [IsFiniteMeasure μ] (G : List α → ℝ)
    (n : ℕ) : Integrable (fun x => G (futureWord x n)) μ := by
  simp only [futureWord_eq_ofFn_block]
  exact integrable_comp_block fun w : Fin n → α => G (List.ofFn w)

variable {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ] {G H : List α → ℝ} {c : ℝ}

/-- The integral of a function of the prefix `𝐢|_n` is monotone in the function. -/
theorem integral_futureWord_mono (h : ∀ w, G w ≤ H w) (n : ℕ) :
    ∫ x, G (futureWord x n) ∂μ ≤ ∫ x, H (futureWord x n) ∂μ :=
  integral_mono (integrable_comp_futureWord G n) (integrable_comp_futureWord H n) fun _ => h _

/-- If `G(𝐢) ≥ c |𝐢|` for all words, then `n⁻¹ ∫ G(𝐢|_n) dμ(𝐢) ≥ c` for `n ≥ 1`. -/
theorem le_integral_futureWord_div (hc : ∀ w, c * w.length ≤ G w) {n : ℕ} (hn : 0 < n) :
    c ≤ (∫ x, G (futureWord x n) ∂μ) / n := by
  rw [le_div_iff₀ (Nat.cast_pos.2 hn)]
  calc c * n = ∫ _, c * n ∂μ := by simp
    _ ≤ ∫ x, G (futureWord x n) ∂μ :=
      integral_mono (integrable_const _) (integrable_comp_futureWord G n) fun x => by
        simpa using hc (futureWord x n)

/-- If `G(𝐢) ≤ c |𝐢|` for all words, then `n⁻¹ ∫ G(𝐢|_n) dμ(𝐢) ≤ c` for `n ≥ 1`. -/
theorem integral_futureWord_div_le (hc : ∀ w, G w ≤ c * w.length) {n : ℕ} (hn : 0 < n) :
    (∫ x, G (futureWord x n) ∂μ) / n ≤ c := by
  rw [div_le_iff₀ (Nat.cast_pos.2 hn)]
  calc ∫ x, G (futureWord x n) ∂μ ≤ ∫ _, c * n ∂μ :=
      integral_mono (integrable_comp_futureWord G n) (integrable_const _) fun x => by
        simpa using hc (futureWord x n)
    _ = c * n := by simp

/-- Fekete's lemma for an invariant measure: if `G` is sub-additive on words and
`G(𝐢) ≥ c |𝐢|`, then the averages `n⁻¹ ∫ G(𝐢|_n) dμ(𝐢)` converge. -/
theorem exists_tendsto_integral_futureWord_div (hμ : MeasurePreserving (shift 1) μ μ)
    (hsub : ∀ w w', G (w ++ w') ≤ G w + G w') (hc : ∀ w, c * w.length ≤ G w) :
    ∃ L, Tendsto (fun n : ℕ => (∫ x, G (futureWord x n) ∂μ) / n) atTop (𝓝 L) := by
  have hsub' : Subadditive fun n : ℕ => ∫ x, G (futureWord x n) ∂μ := by
    intro m n
    have hint : Integrable (fun x => G (futureWord (shift m x) n)) μ :=
      (measurePreserving_shift_natCast hμ m).integrable_comp_of_integrable
        (integrable_comp_futureWord G n)
    calc ∫ x, G (futureWord x (m + n)) ∂μ
        ≤ ∫ x, (G (futureWord x m) + G (futureWord (shift m x) n)) ∂μ :=
          integral_mono (integrable_comp_futureWord G _)
            ((integrable_comp_futureWord G m).add hint) fun x => by
              rw [futureWord_add]; exact hsub _ _
      _ = ∫ x, G (futureWord x m) ∂μ + ∫ x, G (futureWord x n) ∂μ := by
          rw [integral_add (integrable_comp_futureWord G m) hint,
            integral_comp_shift hμ m (measurable_comp_futureWord G n)]
  have hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, G (futureWord x n) ∂μ) / n) := by
    refine ⟨min 0 c, ?_⟩
    rintro _ ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact (min_le_right _ _).trans (le_integral_futureWord_div hc hn)
  exact ⟨_, hsub'.tendsto_lim hbdd⟩

/-- Fekete's lemma for an invariant measure: if `G` is super-additive on words and
`G(𝐢) ≤ c |𝐢|`, then the averages `n⁻¹ ∫ G(𝐢|_n) dμ(𝐢)` converge. -/
theorem exists_tendsto_integral_futureWord_div_of_superadditive
    (hμ : MeasurePreserving (shift 1) μ μ) (hsup : ∀ w w', G w + G w' ≤ G (w ++ w'))
    (hc : ∀ w, G w ≤ c * w.length) :
    ∃ L, Tendsto (fun n : ℕ => (∫ x, G (futureWord x n) ∂μ) / n) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := exists_tendsto_integral_futureWord_div hμ (G := fun w => -G w) (c := -c)
    (fun w w' => by linarith [hsup w w']) (fun w => by linarith [hc w])
  refine ⟨-L, hL.neg.congr fun n => ?_⟩
  rw [integral_neg, neg_div, neg_neg]

end futureWord

/-- The `s`-energy `Λ(𝖠, μ, s)` of `eq:energy_def` is, for fixed `s`, a linear function of the
two Lyapunov exponents. -/
theorem exists_energy_eq_linear (s : ℝ) :
    ∃ c₁ c₂ : ℝ, ∀ l1 l2, energy l1 l2 s = c₁ * l1 + c₂ * l2 := by
  unfold energy
  split_ifs
  · exact ⟨s, 0, fun _ _ => by ring⟩
  · exact ⟨1, s - 1, fun _ _ => by ring⟩
  · exact ⟨s / 2, s / 2, fun _ _ => by ring⟩

namespace System

/-! ### The singular values of the products `A_𝐢` -/

section Word

variable {ι : Type*} (S : System ι)

/-- `α_1(A_𝐢)` is the larger of the two moduli `|g'|` over `𝐢`. -/
theorem norm_matWord (w : List ι) :
    ‖S.matWord w‖ = max |S.gDeriv (S.codeWord 0 w)| |S.gDeriv (S.codeWord 1 w)| := by
  rw [matWord_eq, norm_boxMat]

/-- `α_1(A_𝐢) α_2(A_𝐢) = |det A_𝐢|` is the product of the two moduli `|g'|` over `𝐢`. -/
theorem abs_det_matWord (w : List ι) :
    |(S.matWord w).det| = |S.gDeriv (S.codeWord 0 w)| * |S.gDeriv (S.codeWord 1 w)| := by
  rw [matWord_eq, abs_det_boxMat]

/-- `α_1(A_𝐢) > 0`. -/
theorem norm_matWord_pos (w : List ι) : 0 < ‖S.matWord w‖ := by
  rw [norm_matWord]
  exact lt_max_of_lt_left (abs_pos.2 (S.gDeriv_ne_zero _))

/-- `|det A_𝐢| > 0`. -/
theorem abs_det_matWord_pos (w : List ι) : 0 < |(S.matWord w).det| := by
  rw [abs_det_matWord]
  exact mul_pos (abs_pos.2 (S.gDeriv_ne_zero _)) (abs_pos.2 (S.gDeriv_ne_zero _))

/-- `α_2(A_𝐢) = |det A_𝐢| / ‖A_𝐢‖` is the smaller of the two moduli `|g'|` over `𝐢`. -/
theorem abs_det_div_norm_matWord (w : List ι) :
    |(S.matWord w).det| / ‖S.matWord w‖ =
      min |S.gDeriv (S.codeWord 0 w)| |S.gDeriv (S.codeWord 1 w)| := by
  have h := S.norm_matWord_pos w
  rw [norm_matWord] at h
  rw [abs_det_matWord, norm_matWord, abs_mul_abs_eq_max_mul_min, mul_div_cancel_left₀ _ h.ne']

/-- `α_2(A_𝐢) > 0`. -/
theorem abs_det_div_norm_matWord_pos (w : List ι) :
    0 < |(S.matWord w).det| / ‖S.matWord w‖ :=
  div_pos (S.abs_det_matWord_pos w) (S.norm_matWord_pos w)

/-- `log α_2(A_𝐢) = log |det A_𝐢| - log α_1(A_𝐢)`. -/
theorem log_abs_det_div_norm_matWord (w : List ι) :
    Real.log (|(S.matWord w).det| / ‖S.matWord w‖) =
      Real.log |(S.matWord w).det| - Real.log ‖S.matWord w‖ :=
  Real.log_div (S.abs_det_matWord_pos w).ne' (S.norm_matWord_pos w).ne'

/-- `α_2(A_𝐢) ≤ α_1(A_𝐢)`, in logarithmic form. -/
theorem log_abs_det_div_norm_matWord_le (w : List ι) :
    Real.log (|(S.matWord w).det| / ‖S.matWord w‖) ≤ Real.log ‖S.matWord w‖ := by
  refine Real.log_le_log (S.abs_det_div_norm_matWord_pos w) ?_
  rw [abs_det_div_norm_matWord, norm_matWord]
  exact min_le_max

/-- The singular value `α_1` is sub-multiplicative: `log α_1(A_𝐢 A_𝐣) ≤ log α_1(A_𝐢) +
log α_1(A_𝐣)`. -/
theorem log_norm_matWord_append_le (w w' : List ι) :
    Real.log ‖S.matWord (w ++ w')‖ ≤ Real.log ‖S.matWord w‖ + Real.log ‖S.matWord w'‖ := by
  have h := S.norm_matWord_pos (w ++ w')
  rw [matWord_append] at h
  rw [← Real.log_mul (S.norm_matWord_pos w).ne' (S.norm_matWord_pos w').ne', matWord_append]
  exact Real.log_le_log h (norm_mul_le _ _)

/-- The determinant is multiplicative: `log |det A_𝐢 A_𝐣| = log |det A_𝐢| + log |det A_𝐣|`. -/
theorem log_abs_det_matWord_append (w w' : List ι) :
    Real.log |(S.matWord (w ++ w')).det| =
      Real.log |(S.matWord w).det| + Real.log |(S.matWord w').det| := by
  rw [matWord_append, Matrix.det_mul, abs_mul,
    Real.log_mul (S.abs_det_matWord_pos w).ne' (S.abs_det_matWord_pos w').ne']

/-- The singular value `α_2` is super-multiplicative on the products `A_𝐢`:
`log α_2(A_𝐢) + log α_2(A_𝐣) ≤ log α_2(A_𝐢 A_𝐣)`. -/
theorem le_log_abs_det_div_norm_matWord_append (w w' : List ι) :
    Real.log (|(S.matWord w).det| / ‖S.matWord w‖) +
        Real.log (|(S.matWord w').det| / ‖S.matWord w'‖) ≤
      Real.log (|(S.matWord (w ++ w')).det| / ‖S.matWord (w ++ w')‖) := by
  rw [log_abs_det_div_norm_matWord, log_abs_det_div_norm_matWord, log_abs_det_div_norm_matWord,
    log_abs_det_matWord_append]
  linarith [S.log_norm_matWord_append_le w w']

/-- `φ^s(A_𝐢) > 0`. -/
theorem svf_matWord_pos (s : ℝ) (w : List ι) : 0 < svf s (S.matWord w) := by
  have hn := S.norm_matWord_pos w
  have hd := S.abs_det_matWord_pos w
  unfold svf
  split_ifs
  · exact Real.rpow_pos_of_pos hn _
  · exact mul_pos (Real.rpow_pos_of_pos hn _) (Real.rpow_pos_of_pos hd _)
  · exact Real.rpow_pos_of_pos hd _

/-- `eq:energy_def` for a single word: `log φ^s(A_𝐢)` is the `s`-energy of the pair
`log α_1(A_𝐢)`, `log α_2(A_𝐢)`. -/
theorem log_svf_matWord (s : ℝ) (w : List ι) :
    Real.log (svf s (S.matWord w)) =
      energy (Real.log ‖S.matWord w‖) (Real.log (|(S.matWord w).det| / ‖S.matWord w‖)) s := by
  have hn := S.norm_matWord_pos w
  have hd := S.abs_det_matWord_pos w
  rw [log_abs_det_div_norm_matWord]
  unfold svf energy
  split_ifs
  · rw [Real.log_rpow hn]
  · rw [Real.log_mul (Real.rpow_pos_of_pos hn _).ne' (Real.rpow_pos_of_pos hd _).ne',
      Real.log_rpow hn, Real.log_rpow hd]
    ring
  · rw [Real.log_rpow hd]
    ring

/-- The singular value function is sub-multiplicative:
`log φ^s(A_𝐢 A_𝐣) ≤ log φ^s(A_𝐢) + log φ^s(A_𝐣)` for `s ≥ 0`. -/
theorem log_svf_matWord_append_le {s : ℝ} (hs : 0 ≤ s) (w w' : List ι) :
    Real.log (svf s (S.matWord (w ++ w'))) ≤
      Real.log (svf s (S.matWord w)) + Real.log (svf s (S.matWord w')) := by
  have h := S.svf_matWord_pos s (w ++ w')
  rw [matWord_append] at h
  rw [← Real.log_mul (S.svf_matWord_pos s w).ne' (S.svf_matWord_pos s w').ne', matWord_append]
  exact Real.log_le_log h (svf_mul_le hs _ _)

variable {S} {δ r M : ℝ}

/-- `log α_1(A_𝐢) ≥ |𝐢| log δ` when every `|a_i|` and `|b_i|` is at least `δ`. -/
theorem RatioLowerBound.le_log_norm_matWord (hδ : S.RatioLowerBound δ) (w : List ι) :
    Real.log δ * w.length ≤ Real.log ‖S.matWord w‖ := by
  have h : δ ^ w.length ≤ ‖S.matWord w‖ := by
    rw [norm_matWord]
    exact le_max_of_le_left (by simpa using hδ.le_abs_gDeriv (S.codeWord 0 w))
  have h' := Real.log_le_log (pow_pos hδ.1 _) h
  rwa [Real.log_pow, mul_comm] at h'

/-- `log α_2(A_𝐢) ≥ |𝐢| log δ` when every `|a_i|` and `|b_i|` is at least `δ`. -/
theorem RatioLowerBound.le_log_abs_det_div_norm_matWord (hδ : S.RatioLowerBound δ)
    (w : List ι) :
    Real.log δ * w.length ≤ Real.log (|(S.matWord w).det| / ‖S.matWord w‖) := by
  have h : δ ^ w.length ≤ |(S.matWord w).det| / ‖S.matWord w‖ := by
    rw [abs_det_div_norm_matWord]
    exact le_min (by simpa using hδ.le_abs_gDeriv (S.codeWord 0 w))
      (by simpa using hδ.le_abs_gDeriv (S.codeWord 1 w))
  have h' := Real.log_le_log (pow_pos hδ.1 _) h
  rwa [Real.log_pow, mul_comm] at h'

/-- `log φ^s(A_𝐢) ≥ s |𝐢| log δ` when every `|a_i|` and `|b_i|` is at least `δ`. -/
theorem RatioLowerBound.le_log_svf_matWord (hδ : S.RatioLowerBound δ) {s : ℝ} (hs : 0 ≤ s)
    (w : List ι) : s * Real.log δ * w.length ≤ Real.log (svf s (S.matWord w)) := by
  have h := Real.log_le_log (Real.rpow_pos_of_pos (pow_pos hδ.1 _) _) (hδ.le_svf_matWord hs w)
  rw [Real.log_rpow (pow_pos hδ.1 _), Real.log_pow] at h
  calc s * Real.log δ * w.length = s * (w.length * Real.log δ) := by ring
    _ ≤ Real.log (svf s (S.matWord w)) := h

/-- `log α_1(A_𝐢) ≤ |𝐢| log r` when every `|a_i|` and `|b_i|` is at most `r`. -/
theorem Bounds.log_norm_matWord_le (hS : S.Bounds r M) (w : List ι) :
    Real.log ‖S.matWord w‖ ≤ Real.log r * w.length := by
  have h : ‖S.matWord w‖ ≤ r ^ w.length := by
    rw [norm_matWord]
    exact max_le (by simpa using hS.abs_gDeriv_le (S.codeWord 0 w))
      (by simpa using hS.abs_gDeriv_le (S.codeWord 1 w))
  have h' := Real.log_le_log (S.norm_matWord_pos w) h
  rwa [Real.log_pow, mul_comm] at h'

variable (S)

/-- `log |g'_{𝐣|_n}| = ∑_{k<n} log |g'_{j_k}|`. -/
theorem log_abs_gDeriv_futureWord (y : ℤ → ι × ZMod 2) (n : ℕ) :
    Real.log |S.gDeriv (futureWord y n)| =
      ∑ k ∈ Finset.range n, Real.log |S.ratio (y k)| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [futureWord_succ, gDeriv_append, abs_mul,
      Real.log_mul (abs_ne_zero.2 (S.gDeriv_ne_zero _)) (abs_ne_zero.2 (S.gDeriv_ne_zero _)),
      ih, Finset.sum_range_succ]
    simp

end Word

/-! ### The Lyapunov exponents -/

section Lyapunov

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]

/-- The limit defining `λ_1(𝖠, μ)` exists, by Fekete's lemma: `α_1` is sub-multiplicative and
`μ` is invariant. -/
theorem tendsto_lyapunov₁ (hμ : MeasurePreserving (shift 1) μ μ) :
    Tendsto (fun n : ℕ => (∫ x, Real.log ‖S.matWord (futureWord x n)‖ ∂μ) / n) atTop
      (𝓝 (S.lyapunov₁ μ)) := by
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
  obtain ⟨δ, hδ⟩ := S.exists_ratioLowerBound
  obtain ⟨L, hL⟩ := exists_tendsto_integral_futureWord_div hμ
    (G := fun w => Real.log ‖S.matWord w‖) S.log_norm_matWord_append_le
    hδ.le_log_norm_matWord
  rw [lyapunov₁, hL.limUnder_eq]
  exact hL

/-- The limit defining `λ_2(𝖠, μ)` exists, by Fekete's lemma: `α_2` is super-multiplicative
and `μ` is invariant. -/
theorem tendsto_lyapunov₂ (hμ : MeasurePreserving (shift 1) μ μ) :
    Tendsto (fun n : ℕ =>
      (∫ x, Real.log (|(S.matWord (futureWord x n)).det| / ‖S.matWord (futureWord x n)‖) ∂μ) / n)
      atTop (𝓝 (S.lyapunov₂ μ)) := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  obtain ⟨L, hL⟩ := exists_tendsto_integral_futureWord_div_of_superadditive hμ
    (G := fun w => Real.log (|(S.matWord w).det| / ‖S.matWord w‖))
    S.le_log_abs_det_div_norm_matWord_append
    fun w => (S.log_abs_det_div_norm_matWord_le w).trans (hS.log_norm_matWord_le w)
  rw [lyapunov₂, hL.limUnder_eq]
  exact hL

/-- `λ_1(𝖠, μ) < 0`: every `|a_i|` and `|b_i|` is less than one. -/
theorem lyapunov₁_neg (hμ : MeasurePreserving (shift 1) μ μ) : S.lyapunov₁ μ < 0 := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  have hr : 0 < r :=
    (abs_pos.2 (S.ratio_ne_zero ((nonempty_of_isProbabilityMeasure μ).some 0, 0))).trans_le
      (hS.abs_ratio_le _)
  have hle : S.lyapunov₁ μ ≤ Real.log r :=
    le_of_tendsto (S.tendsto_lyapunov₁ hμ) ((eventually_gt_atTop 0).mono fun n hn =>
      integral_futureWord_div_le hS.log_norm_matWord_le hn)
  exact hle.trans_lt (Real.log_neg hr hS.r_lt_one)

/-- `λ_2(𝖠, μ) ≤ λ_1(𝖠, μ)`. -/
theorem lyapunov₂_le_lyapunov₁ (hμ : MeasurePreserving (shift 1) μ μ) :
    S.lyapunov₂ μ ≤ S.lyapunov₁ μ :=
  le_of_tendsto_of_tendsto' (S.tendsto_lyapunov₂ hμ) (S.tendsto_lyapunov₁ hμ) fun n =>
    div_le_div_of_nonneg_right
      (integral_futureWord_mono S.log_abs_det_div_norm_matWord_le n) (Nat.cast_nonneg n)

variable {S} in
/-- `-∞ < λ_2(𝖠, μ)`: the exponent is at least `log δ` when every `|a_i|` and `|b_i|` is at
least `δ`. -/
theorem RatioLowerBound.log_le_lyapunov₂ {δ : ℝ} (hδ : S.RatioLowerBound δ)
    (hμ : MeasurePreserving (shift 1) μ μ) : Real.log δ ≤ S.lyapunov₂ μ :=
  ge_of_tendsto (S.tendsto_lyapunov₂ hμ) ((eventually_gt_atTop 0).mono fun _ hn =>
    le_integral_futureWord_div hδ.le_log_abs_det_div_norm_matWord hn)

end Lyapunov

/-! ### The energy -/

section Energy

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]

/-- The limit defining `Λ(𝖠, μ, s)` exists, by Fekete's lemma: `φ^s` is sub-multiplicative for
`s ≥ 0` and `μ` is invariant. -/
theorem tendsto_energyLim (hμ : MeasurePreserving (shift 1) μ μ) {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun n : ℕ => (∫ x, Real.log (svf s (S.matWord (futureWord x n))) ∂μ) / n) atTop
      (𝓝 (S.energyLim s μ)) := by
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
  obtain ⟨δ, hδ⟩ := S.exists_ratioLowerBound
  obtain ⟨L, hL⟩ := exists_tendsto_integral_futureWord_div hμ
    (G := fun w => Real.log (svf s (S.matWord w))) (S.log_svf_matWord_append_le hs)
    (hδ.le_log_svf_matWord hs)
  rw [energyLim, hL.limUnder_eq]
  exact hL

/-- `eq:energy_def`: the `s`-energy is `s λ_1` for `0 ≤ s ≤ 1`, `λ_1 + (s - 1) λ_2` for
`1 < s ≤ 2` and `(s / 2) (λ_1 + λ_2)` for `s > 2`. -/
theorem energyLim_eq (hμ : MeasurePreserving (shift 1) μ μ) {s : ℝ} (hs : 0 ≤ s) :
    S.energyLim s μ = energy (S.lyapunov₁ μ) (S.lyapunov₂ μ) s := by
  obtain ⟨c₁, c₂, hc⟩ := exists_energy_eq_linear s
  have h := ((S.tendsto_lyapunov₁ hμ).const_mul c₁).add ((S.tendsto_lyapunov₂ hμ).const_mul c₂)
  rw [← hc] at h
  refine tendsto_nhds_unique (S.tendsto_energyLim hμ hs) (h.congr fun n => ?_)
  have h₁ : Integrable (fun x => Real.log ‖S.matWord (futureWord x n)‖) μ :=
    integrable_comp_futureWord (fun w => Real.log ‖S.matWord w‖) n
  have h₂ : Integrable (fun x =>
      Real.log (|(S.matWord (futureWord x n)).det| / ‖S.matWord (futureWord x n)‖)) μ :=
    integrable_comp_futureWord (fun w => Real.log (|(S.matWord w).det| / ‖S.matWord w‖)) n
  simp only [log_svf_matWord, hc]
  rw [integral_add (h₁.const_mul c₁) (h₂.const_mul c₂), integral_const_mul, integral_const_mul]
  ring

variable {S} in
/-- The equilibrium identity `eq:eq_state_def` with the energy in the piecewise form of
`eq:energy_def`. -/
theorem IsEquilibriumState.pressure_eq {s : ℝ} (heq : S.IsEquilibriumState s μ)
    (hμ : MeasurePreserving (shift 1) μ μ) (hs : 0 ≤ s) :
    S.pressure s = entropy μ + energy (S.lyapunov₁ μ) (S.lyapunov₂ μ) s := by
  rw [← S.energyLim_eq hμ hs]
  exact heq

variable {S} in
/-- An invariant measure satisfying the equilibrium identity with the energy in the piecewise
form of `eq:energy_def` is an `s`-equilibrium state. -/
theorem IsEquilibriumState.of_pressure_eq {s : ℝ} (hμ : MeasurePreserving (shift 1) μ μ)
    (hs : 0 ≤ s) (h : S.pressure s = entropy μ + energy (S.lyapunov₁ μ) (S.lyapunov₂ μ) s) :
    S.IsEquilibriumState s μ := by
  unfold IsEquilibriumState
  rw [S.energyLim_eq hμ hs]
  exact h

end Energy

/-! ### The Lyapunov exponent of the projective system -/

section LyapBar

/-- The Lyapunov exponent `\overline{λ}(𝖠, ν) = lim_n n⁻¹ ∫ log |g'_{𝐣|_n}(0)| dν(𝐣)` of the
projective system, as the limit of `sec:lyapunov_exponents`. -/
noncomputable def lyapBarLim {ι : Type*} [MeasurableSpace ι] (S : System ι)
    (ν : Measure (ℤ → ι × ZMod 2)) : ℝ :=
  limUnder atTop fun n : ℕ => (∫ y, Real.log |S.gDeriv (futureWord y n)| ∂ν) / n

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {ν : Measure (ℤ → ι × ZMod 2)}

/-- For an invariant measure every coordinate has the same distribution:
`∫ log |g'_{j_k}| dν(𝐣) = ∫ log |g'_{j_0}| dν(𝐣)`. -/
theorem integral_log_abs_ratio_apply (hν : MeasurePreserving (shift 1) ν ν) (k : ℕ) :
    ∫ y, Real.log |S.ratio (y k)| ∂ν = S.lyapBar ν := by
  have h := integral_comp_shift hν k (F := fun y => Real.log |S.ratio (y 0)|)
    ((Measurable.of_discrete (f := fun p : ι × ZMod 2 => Real.log |S.ratio p|)).comp
      (measurable_pi_apply 0))
  simpa [lyapBar] using h

variable [IsProbabilityMeasure ν]

/-- `∫ log |g'_{𝐣|_n}| dν(𝐣) = n ∫ log |g'_{j_0}| dν(𝐣)` for an invariant measure `ν`. -/
theorem integral_log_abs_gDeriv_futureWord (hν : MeasurePreserving (shift 1) ν ν) (n : ℕ) :
    ∫ y, Real.log |S.gDeriv (futureWord y n)| ∂ν = n * S.lyapBar ν := by
  have hint : ∀ k : ℕ, Integrable (fun y : ℤ → ι × ZMod 2 => Real.log |S.ratio (y k)|) ν :=
    fun k =>
      (Integrable.of_finite (f := fun p : ι × ZMod 2 => Real.log |S.ratio p|)).comp_measurable
        (measurable_pi_apply (k : ℤ))
  simp only [log_abs_gDeriv_futureWord]
  rw [integral_finsetSum _ fun k _ => hint k,
    Finset.sum_congr rfl fun k _ => S.integral_log_abs_ratio_apply hν k]
  simp

/-- The limit defining `\overline{λ}(𝖠, ν)` in `sec:lyapunov_exponents` is the integral
`∫ log |g'_{j_0}| dν(𝐣)` of `thm:eq_state_is_sum`, for an invariant measure `ν`. -/
theorem lyapBarLim_eq (hν : MeasurePreserving (shift 1) ν ν) : S.lyapBarLim ν = S.lyapBar ν := by
  have h : Tendsto (fun n : ℕ => (∫ y, Real.log |S.gDeriv (futureWord y n)| ∂ν) / n) atTop
      (𝓝 (S.lyapBar ν)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [S.integral_log_abs_gDeriv_futureWord hν, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 hn)]
  exact h.limUnder_eq

end LyapBar

end System

end BoxLike
