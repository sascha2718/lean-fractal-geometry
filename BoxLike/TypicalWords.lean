module

/-
The typical words of the proof of `thm:main2` in `sec:dimension_result_proof` (tex line 3470
to 3683): for the equilibrium state `μ` of a box-like system with rotations containing a
proximal diagonal generator, with `0 < s < 2` and `P(𝖠, s) = 0`, finite families `W_n` of words
of length `n → ∞` with a common diagonal planar matrix `A_w = diag(a_n, b_n)`, with
`log #W_n / n → h_0(μ)`, `log |a_n| / n → λ_1(𝖠, μ)` and `log |b_n| / n → λ_2(𝖠, μ)`.

The families are selected from the Gibbs measure `μ_1` of `f_{1,s}` on `Σ_Z`: the Birkhoff
averages of `f_{1,1}` and `f_{2,1}` converge in measure, the good set is covered by the lifted
cylinders of the good words, whose measures the Gibbs bounds control, and a pigeonhole on the
count vectors and the orientation of the words gives a class on which the two coordinate
derivatives and the orientation are constant. The article returns to the horizontal orientation
through the mixing of `μ_1` (tex lines 3474 to 3477); here one anti-diagonal generator is appended
to the words of a class of odd orientation instead, which changes the lengths by at most one and
none of the limits. The Shannon–McMillan–Breiman theorem of tex line 3478 is not needed: the
Gibbs bounds and the Birkhoff averages of `f_{1,1}`, `f_{2,1}` give the cardinality bounds.

* `exists_block_eq_of_pos`, `System.codeWord_add_one`, `System.count_codeWord_one`,
  `System.gDeriv_eq_prod_count`: the path on the second axis is the flipped path on the first
  axis, and `g'_𝐣` is a function of the count vector of `𝐣`.
* `System.exists_o_eq_one_of_oWord_eq_one`, `System.exists_diagonal_of_class`: a word of odd
  orientation contains an anti-diagonal generator, and appending it returns a class to the
  horizontal orientation.
* `tendsto_div_add_of_tendsto_div`, `tendsto_errorTerm_div`, `tendsto_of_abs_sub_le`: the
  real-variable limits.
* `tendsto_measure_birkhoff_bad`: convergence in measure of the Birkhoff averages.
* `System.exists_class`: the counting step for one tolerance `ε` and one length `n`.
* `System.exists_class_of_gibbs`: the selection for one tolerance `ε`.
* `System.exists_typical_words_of_gibbs`: the typical words of a Gibbs measure on `Σ_Z`.
* `System.exists_typical_words`: the typical words of the equilibrium state, tex line 3470 to
  3683.
-/
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.FengEntropy
public import BoxLike.PressureZ
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology

universe u

/-! ### Words and their count vectors -/

/-- Every word of positive length is the block of some sequence. -/
theorem exists_block_eq_of_pos {α : Type*} {n : ℕ} (hn : 0 < n) (w : Fin n → α) :
    ∃ x : ℤ → α, block n x = w := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact ⟨extendWord w, block_extendWord w⟩

/-- The symmetry exchanging the two axes is injective. -/
theorem flipSymbol_injective {ι : Type*} :
    Function.Injective (flipSymbol : ι × ZMod 2 → ι × ZMod 2) :=
  Function.LeftInverse.injective flipSymbol_flipSymbol

namespace System

variable {ι : Type*} (S : System ι)

/-- The path of `Σ_Z` over `𝐢` starting on the axis `c + 1` is the path starting on the axis `c`
with every symbol flipped to the other axis. -/
theorem codeWord_add_one (c : ZMod 2) (w : List ι) :
    S.codeWord (c + 1) w = (S.codeWord c w).map flipSymbol := by
  induction w generalizing c with
  | nil => simp
  | cons i w ih =>
    rw [codeWord_cons, codeWord_cons, List.map_cons, add_right_comm, ih]
    rfl

/-- The count vector of the path on the second axis is the count vector of the path on the
first axis at the flipped symbols. -/
theorem count_codeWord_one [DecidableEq ι] (w : List ι) (p : ι × ZMod 2) :
    (S.codeWord 1 w).count p = (S.codeWord 0 w).count (flipSymbol p) := by
  have h := S.codeWord_add_one 0 w
  rw [zero_add] at h
  rw [h]
  conv_lhs => rw [← flipSymbol_flipSymbol p]
  exact List.count_map_of_injective _ _ flipSymbol_injective _

/-- The derivative `g'_𝐣` is a function of the count vector of `𝐣`: it is the product of the
`g'_j` to the number of occurrences of `j`, as in tex lines 3491 to 3494. -/
theorem gDeriv_eq_prod_count [Fintype ι] [DecidableEq ι] (u : List (ι × ZMod 2)) :
    S.gDeriv u = ∏ p, S.ratio p ^ u.count p := by
  rw [gDeriv, Finset.prod_list_map_count]
  refine Finset.prod_subset (Finset.subset_univ _) fun p _ hp => ?_
  rw [List.count_eq_zero_of_not_mem (by simpa using hp), pow_zero]

/-- A word of diagonal generators has even orientation. -/
theorem oWord_eq_zero_of_forall {w : List ι} (h : ∀ i ∈ w, S.o i = 0) : S.oWord w = 0 := by
  rw [oWord]
  exact List.sum_eq_zero fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact h i hi

/-- A word of odd orientation contains an anti-diagonal generator. -/
theorem exists_o_eq_one_of_oWord_eq_one {w : List ι} (h : S.oWord w = 1) : ∃ i, S.o i = 1 := by
  by_contra hne
  have : ∀ i ∈ w, S.o i = 0 := fun i _ => by
    rcases zmod_two_cases (S.o i) with h0 | h1
    · exact h0
    · exact absurd ⟨i, h1⟩ hne
  rw [S.oWord_eq_zero_of_forall this] at h
  exact absurd h (by decide)

/-- The logarithms of the contraction ratios of the projective system are bounded. -/
theorem exists_abs_log_abs_ratio_le [Fintype ι] :
    ∃ K : ℝ, ∀ p, abs (Real.log |S.ratio p|) ≤ K :=
  ⟨∑ p, abs (Real.log |S.ratio p|), fun p =>
    Finset.single_le_sum (f := fun p => abs (Real.log |S.ratio p|)) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ p)⟩

/-- A class of words of length `n` with common orientation `c` and common coordinate
derivatives `a`, `b` becomes a class of words of length `n + e`, `e ≤ 1`, with diagonal planar
matrix `diag(a', b')`: for `c = 1` one anti-diagonal generator is appended, which multiplies
the derivatives by its entries. This replaces the use of mixing in tex lines 3474 to 3477. -/
theorem exists_diagonal_of_class [Nonempty ι] {K : ℝ} (hK : ∀ p, abs (Real.log |S.ratio p|) ≤ K)
    {W : Finset (List ι)} (hW : W.Nonempty) {n : ℕ} {a b : ℝ} {c : ZMod 2}
    (hmem : ∀ w ∈ W, w.length = n ∧ S.oWord w = c ∧ S.gDeriv (S.codeWord 0 w) = a ∧
      S.gDeriv (S.codeWord 1 w) = b) :
    ∃ (e : ℕ) (W' : Finset (List ι)) (a' b' : ℝ), e ≤ 1 ∧ W'.card = W.card ∧ W'.Nonempty ∧
      (∀ w ∈ W', w.length = n + e ∧ S.matWord w = boxMat 0 a' b') ∧
      abs (Real.log |a'| - Real.log |a|) ≤ K ∧ abs (Real.log |b'| - Real.log |b|) ≤ K := by
  classical
  obtain ⟨w₀, hw₀⟩ := hW
  obtain ⟨-, hc, ha, hb⟩ := hmem w₀ hw₀
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK (Classical.arbitrary ι, 0))
  have ha0 : a ≠ 0 := ha ▸ S.gDeriv_ne_zero _
  have hb0 : b ≠ 0 := hb ▸ S.gDeriv_ne_zero _
  rcases zmod_two_cases c with rfl | rfl
  · refine ⟨0, W, a, b, Nat.zero_le _, rfl, ⟨w₀, hw₀⟩,
      fun w hw => ⟨by rw [(hmem w hw).1, add_zero], ?_⟩, by simpa using hK0, by simpa using hK0⟩
    rw [matWord_eq, (hmem w hw).2.1, (hmem w hw).2.2.1, (hmem w hw).2.2.2]
  · obtain ⟨i, hi⟩ := S.exists_o_eq_one_of_oWord_eq_one hc
    refine ⟨1, W.image (· ++ [i]), a * S.b i, b * S.a i, le_rfl,
      Finset.card_image_of_injective _ (List.append_left_injective _),
      ⟨w₀ ++ [i], Finset.mem_image_of_mem _ hw₀⟩, ?_, ?_, ?_⟩
    · intro w hw
      obtain ⟨w', hw', rfl⟩ := Finset.mem_image.1 hw
      obtain ⟨hl, hc', ha', hb'⟩ := hmem w' hw'
      refine ⟨by simp [hl], ?_⟩
      rw [matWord_append, matWord_eq, hc', ha', hb', matWord_cons, matWord_nil, mul_one, mat, hi,
        boxMat_mul]
      simp [show (1 : ZMod 2) + 1 = 0 from by decide]
    · rw [abs_mul, Real.log_mul (abs_ne_zero.2 ha0) (abs_ne_zero.2 (S.b_ne_zero i)),
        add_sub_cancel_left]
      exact hK (i, 1)
    · rw [abs_mul, Real.log_mul (abs_ne_zero.2 hb0) (abs_ne_zero.2 (S.a_ne_zero i)),
        add_sub_cancel_left]
      exact hK (i, 0)

end System

/-! ### Real-variable limits -/

/-- Changing the lengths by at most one and the numerators by a bounded amount does not change
the limit of the averages `u_m / L_m`. -/
theorem tendsto_div_add_of_tendsto_div {u v : ℕ → ℝ} {L e : ℕ → ℕ} {l K : ℝ}
    (hL : Tendsto L atTop atTop) (he : ∀ m, e m ≤ 1)
    (hu : Tendsto (fun m => u m / L m) atTop (𝓝 l)) (hv : ∀ m, |v m - u m| ≤ K) :
    Tendsto (fun m => v m / (L m + e m : ℕ)) atTop (𝓝 l) := by
  have hL' : Tendsto (fun m => (L m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hL
  have hinv : Tendsto (fun m => 1 / (L m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hL'
  have hpos : ∀ᶠ m in atTop, (0 : ℝ) < L m := hL'.eventually (eventually_gt_atTop 0)
  have h1 : Tendsto (fun m => (L m : ℝ) / (L m + e m)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun m => (e m : ℝ) / (L m + e m)) atTop (𝓝 0) := by
      refine squeeze_zero' (hpos.mono fun m hm => ?_) (hpos.mono fun m hm => ?_) hinv
      · exact div_nonneg (Nat.cast_nonneg _) (by positivity)
      · rw [div_le_div_iff₀ (by positivity) hm, one_mul]
        have : (e m : ℝ) ≤ 1 := by exact_mod_cast he m
        nlinarith [Nat.cast_nonneg (α := ℝ) (e m)]
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub h0
    rw [sub_zero] at this
    refine this.congr' (hpos.mono fun m hm => ?_)
    field_simp
    ring
  have h2 : Tendsto (fun m => (v m - u m) / (L m + e m)) atTop (𝓝 0) := by
    have hK : 0 ≤ K := (abs_nonneg _).trans (hv 0)
    refine squeeze_zero_norm' (hpos.mono fun m hm => ?_) (hinv.const_mul K |>.trans_eq ?_)
    · have hm' : (0 : ℝ) < L m + e m := by linarith [Nat.cast_nonneg (α := ℝ) (e m)]
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hm']
      calc |v m - u m| / ((L m : ℝ) + e m) ≤ K / (L m : ℝ) := by
            gcongr
            · exact hv m
            · linarith [Nat.cast_nonneg (α := ℝ) (e m)]
        _ = K * (1 / (L m : ℝ)) := by ring
    · simp
  have := (hu.mul h1).add h2
  rw [mul_one, add_zero] at this
  refine this.congr' (hpos.mono fun m hm => ?_)
  push_cast
  field_simp
  ring

/-- `log (n + 1) / n → 0`. -/
theorem tendsto_log_add_one_div :
    Tendsto (fun n : ℕ => Real.log (n + 1) / n) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
    (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, pow_one]
  congr 1
  ring

/-- The error term `(A + D log (n + 1)) / n` of the counting bounds tends to zero. -/
theorem tendsto_errorTerm_div (A D : ℝ) :
    Tendsto (fun n : ℕ => (A + D * Real.log (n + 1)) / n) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => A / n) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat A
  have h2 := tendsto_log_add_one_div.const_mul D
  rw [mul_zero] at h2
  have := h1.add h2
  rw [add_zero] at this
  refine this.congr fun n => ?_
  ring

/-- A sequence within `3 / (m + 1)` of `l` converges to `l`. -/
theorem tendsto_of_abs_sub_le {u : ℕ → ℝ} {l : ℝ}
    (h : ∀ m, |u m - l| ≤ 3 * (1 / ((m : ℝ) + 1))) : Tendsto u atTop (𝓝 l) := by
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm h ?_
  simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 3

/-! ### Birkhoff averages -/

section Birkhoff

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The Birkhoff theorem of tex line 3478 in the form of convergence in measure: for an ergodic
measure `ν` on the shift over `ι × ZMod 2` and a function `f` of the symbol `y_0`, the measure
of the set where the average `n⁻¹ ∑_{k<n} f(y_k)` is at distance at least `ε` from `∫ f dν`
tends to zero. -/
theorem tendsto_measure_birkhoff_bad {ν : Measure (ℤ → ι × ZMod 2)} [IsProbabilityMeasure ν]
    (herg : Ergodic (shift 1) ν) (f : ι × ZMod 2 → ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      ν {y | ε ≤ |(∑ k ∈ Finset.range n, f (y k)) / n - ∫ y, f (y 0) ∂ν|}) atTop (𝓝 0) := by
  have hint : Integrable (fun y : ℤ → ι × ZMod 2 => f (y 0)) ν :=
    (Integrable.of_finite (f := f)).comp_measurable (measurable_pi_apply (0 : ℤ))
  have hae := birkhoff_ergodic herg hint
  have hmeas : ∀ n : ℕ, Measurable fun y : ℤ → ι × ZMod 2 =>
      (∑ k ∈ Finset.range n, f (y k)) / n := fun n => by
    have : Measurable fun y : ℤ → ι × ZMod 2 => ∑ k ∈ Finset.range n, f (y k) :=
      Finset.measurable_sum (f := fun (k : ℕ) (y : ℤ → ι × ZMod 2) => f (y k)) _
        fun k _ => (Measurable.of_discrete (f := f)).comp (measurable_pi_apply (k : ℤ))
    exact this.div_const _
  have h := tendstoInMeasure_of_tendsto_ae (μ := ν)
    (f := fun n y => (∑ k ∈ Finset.range n, f (y k)) / n)
    (g := fun _ => ∫ y, f (y 0) ∂ν) (fun n => (hmeas n).aestronglyMeasurable) ?_
  · have := h (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
    refine this.congr fun n => ?_
    congr 1
    ext y
    simp only [Set.mem_ofPred_eq, edist_dist, Real.dist_eq]
    exact ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)
  · refine hae.mono fun y hy => ?_
    refine hy.congr fun n => ?_
    rw [birkhoffAverage_shift_one]
    simp

end Birkhoff

/-! ### The selection of the words -/

namespace System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)

/-- The counting step of tex lines 3476 to 3494 for one tolerance `ε` and one length `n`. Let
`ν` be a probability measure on the shift over `ι × ZMod 2` with the Gibbs bounds for `f_{1,s}`
at pressure `0` with constant `C`, and suppose that the set of points of `τ(Σ)` whose Birkhoff
averages of `f_{1,1}` and `f_{2,1}` of length `n` lie within `ε` of `l₁` and `l₂` has measure at
least `η > 0`. Then there is a non-empty class `W` of words of length `n` with common
orientation `c` and common coordinate derivatives `a`, `b`, with `log |a| / n` within `ε` of
`l₁` and `log |b| / n` within `ε` of `l₂`, and with
`log η - log C - log 2 - 2N log (n + 1) - n (Λ + 2ε) ≤ log #W ≤ log C + n (2ε - Λ)`, where
`Λ = energy l₁ l₂ s` is the `s`-energy of `eq:energy_def`. -/
theorem exists_class {s l₁ l₂ : ℝ} (hs0 : 0 < s) (hs2 : s < 2)
    {ν : Measure (ℤ → ι × ZMod 2)} [IsProbabilityMeasure ν] {C : ℝ} (hC : 0 < C)
    (hgibbs : ∀ y ∈ subshift S.o, ∀ n : ℕ, 0 < n →
      C⁻¹ * Real.exp (∑ k ∈ Finset.range n, S.potential₁ s (y k)) ≤
          ν.real (cylinder fun k : Fin n => y k) ∧
        ν.real (cylinder fun k : Fin n => y k) ≤
          C * Real.exp (∑ k ∈ Finset.range n, S.potential₁ s (y k)))
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) {n : ℕ} (hn : 0 < n)
    (hgood : η ≤ ν.real (Set.range (tau S.o) \
      ({y | ε ≤ |(∑ k ∈ Finset.range n, S.potential₁ 1 (y k)) / n - l₁|} ∪
        {y | ε ≤ |(∑ k ∈ Finset.range n, S.potential₂ 1 (y k)) / n - l₂|}))) :
    ∃ (W : Finset (List ι)) (a b : ℝ) (c : ZMod 2), W.Nonempty ∧
      (∀ w ∈ W, w.length = n ∧ S.oWord w = c ∧ S.gDeriv (S.codeWord 0 w) = a ∧
        S.gDeriv (S.codeWord 1 w) = b) ∧
      |Real.log |a| / n - l₁| < ε ∧ |Real.log |b| / n - l₂| < ε ∧
      Real.log η - Real.log C - Real.log 2 - Fintype.card (ι × ZMod 2) * Real.log (n + 1) -
        n * (energy l₁ l₂ s + 2 * ε) ≤ Real.log W.card ∧
      Real.log W.card ≤ Real.log C + n * (2 * ε - energy l₁ l₂ s) := by
  classical
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  -- the Birkhoff sums of a point of `τ(Σ)` through its word
  have hsum₁ : ∀ x : ℤ → ι, ∑ k ∈ Finset.range n, S.potential₁ 1 (tau S.o x k) =
      Real.log |S.gDeriv (S.codeWord 0 (List.ofFn (block n x)))| := by
    intro x
    rw [sum_potential₁_tau, ← futureWord_eq_ofFn_block, codeWord_futureWord_tau]
    simp
  have hsum₂ : ∀ x : ℤ → ι, ∑ k ∈ Finset.range n, S.potential₂ 1 (tau S.o x k) =
      Real.log |S.gDeriv (S.codeWord 1 (List.ofFn (block n x)))| := by
    intro x
    rw [sum_potential₂_tau, ← futureWord_eq_ofFn_block, codeWord_futureWord_omega]
    simp
  have hsums : ∀ x : ℤ → ι, ∑ k ∈ Finset.range n, S.potential₁ s (tau S.o x k) =
      if s < 1 then s * Real.log |S.gDeriv (S.codeWord 0 (List.ofFn (block n x)))|
      else Real.log |S.gDeriv (S.codeWord 0 (List.ofFn (block n x)))| +
        (s - 1) * Real.log |S.gDeriv (S.codeWord 1 (List.ofFn (block n x)))| := by
    intro x
    rw [sum_potential₁_tau, ← futureWord_eq_ofFn_block, codeWord_futureWord_tau,
      codeWord_futureWord_omega]
  -- the good words
  set good : Finset (Fin n → ι) := Finset.univ.filter fun w =>
    |Real.log |S.gDeriv (S.codeWord 0 (List.ofFn w))| / n - l₁| < ε ∧
      |Real.log |S.gDeriv (S.codeWord 1 (List.ofFn w))| / n - l₂| < ε with hgood_def
  have hcover : Set.range (tau S.o) \
      ({y | ε ≤ |(∑ k ∈ Finset.range n, S.potential₁ 1 (y k)) / n - l₁|} ∪
        {y | ε ≤ |(∑ k ∈ Finset.range n, S.potential₂ 1 (y k)) / n - l₂|}) ⊆
      ⋃ w ∈ good, cylinder (liftBlock S.o 0 w) := by
    rintro y ⟨⟨x, rfl⟩, hy⟩
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hy
    refine Set.mem_iUnion₂.2 ⟨block n x, ?_, ?_⟩
    · rw [hgood_def, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [← hsum₁]; exact hy.1
      · rw [← hsum₂]; exact hy.2
    · have h := block_eq_liftBlock (tau_mem_subshift (o := S.o) x) n
      simp only [tau_apply, eps_zero, unCode_tau] at h
      exact fun k => congrFun h k
  have hmeas_le : ν.real (Set.range (tau S.o) \
      ({y | ε ≤ |(∑ k ∈ Finset.range n, S.potential₁ 1 (y k)) / n - l₁|} ∪
        {y | ε ≤ |(∑ k ∈ Finset.range n, S.potential₂ 1 (y k)) / n - l₂|})) ≤
      ∑ w ∈ good, ν.real (cylinder (liftBlock S.o 0 w)) :=
    (measureReal_mono hcover (measure_ne_top _ _)).trans (measureReal_biUnion_finset_le _ _)
  -- the Gibbs bounds for the lifted cylinders
  have hgibbs' : ∀ w : Fin n → ι,
      C⁻¹ * Real.exp (if s < 1 then s * Real.log |S.gDeriv (S.codeWord 0 (List.ofFn w))|
        else Real.log |S.gDeriv (S.codeWord 0 (List.ofFn w))| +
          (s - 1) * Real.log |S.gDeriv (S.codeWord 1 (List.ofFn w))|) ≤
        ν.real (cylinder (liftBlock S.o 0 w)) ∧
      ν.real (cylinder (liftBlock S.o 0 w)) ≤
        C * Real.exp (if s < 1 then s * Real.log |S.gDeriv (S.codeWord 0 (List.ofFn w))|
          else Real.log |S.gDeriv (S.codeWord 0 (List.ofFn w))| +
            (s - 1) * Real.log |S.gDeriv (S.codeWord 1 (List.ofFn w))|) := by
    intro w
    obtain ⟨x, hx⟩ := exists_block_eq_of_pos hn w
    have h := hgibbs (tau S.o x) (tau_mem_subshift (o := S.o) x) n hn
    have hb : (fun k : Fin n => tau S.o x k) = liftBlock S.o 0 w := by
      have := block_eq_liftBlock (tau_mem_subshift (o := S.o) x) n
      simp only [tau_apply, eps_zero, unCode_tau, hx] at this
      exact this
    rw [hb, hsums x, hx] at h
    exact h
  -- the good words have Birkhoff sums of `f_{1,s}` within `2εn` of `nΛ`
  have hclose : ∀ w ∈ good,
      |(if s < 1 then s * Real.log |S.gDeriv (S.codeWord 0 (List.ofFn w))|
        else Real.log |S.gDeriv (S.codeWord 0 (List.ofFn w))| +
          (s - 1) * Real.log |S.gDeriv (S.codeWord 1 (List.ofFn w))|) -
        n * energy l₁ l₂ s| ≤ 2 * ε * n := by
    intro w hw
    rw [hgood_def, Finset.mem_filter] at hw
    obtain ⟨-, h1, h2⟩ := hw
    set u := Real.log |S.gDeriv (S.codeWord 0 (List.ofFn w))| / n - l₁ with hu
    set v := Real.log |S.gDeriv (S.codeWord 1 (List.ofFn w))| / n - l₂ with hv
    have hα : Real.log |S.gDeriv (S.codeWord 0 (List.ofFn w))| = n * (l₁ + u) := by
      rw [hu, mul_add, mul_sub, mul_div_cancel₀ _ hn'.ne']; ring
    have hβ : Real.log |S.gDeriv (S.codeWord 1 (List.ofFn w))| = n * (l₂ + v) := by
      rw [hv, mul_add, mul_sub, mul_div_cancel₀ _ hn'.ne']; ring
    rw [abs_lt] at h1 h2
    rw [hα, hβ, energy]
    have hεn : 0 < ε * n := mul_pos hε hn'
    have hs2' : s * (ε * n) ≤ 2 * (ε * n) := mul_le_mul_of_nonneg_right hs2.le hεn.le
    have hu1 : n * u ≤ n * ε := mul_le_mul_of_nonneg_left h1.2.le hn'.le
    have hu2 : n * -ε ≤ n * u := mul_le_mul_of_nonneg_left h1.1.le hn'.le
    rcases lt_or_ge s 1 with hs1 | hs1
    · rw [ite_eq_left hs1, ite_eq_left hs1.le, abs_le]
      have hsu1 : s * (n * u) ≤ s * (n * ε) := mul_le_mul_of_nonneg_left hu1 hs0.le
      have hsu2 : s * (n * -ε) ≤ s * (n * u) := mul_le_mul_of_nonneg_left hu2 hs0.le
      constructor <;> nlinarith
    · rw [ite_eq_right (not_lt.2 hs1)]
      rcases hs1.lt_or_eq with hs1' | rfl
      · rw [ite_eq_right (not_le.2 hs1'), ite_eq_left hs2.le, abs_le]
        have hs1'' : 0 ≤ s - 1 := by linarith
        have hv1 : (s - 1) * (n * v) ≤ (s - 1) * (n * ε) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2.2.le hn'.le) hs1''
        have hv2 : (s - 1) * (n * -ε) ≤ (s - 1) * (n * v) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2.1.le hn'.le) hs1''
        constructor <;> nlinarith
      · rw [ite_eq_left le_rfl, abs_le]
        constructor <;> nlinarith
  -- the counting bounds for the number `N` of good words
  set N := good.card with hN
  have hlow : ∀ w ∈ good, C⁻¹ * Real.exp (n * (energy l₁ l₂ s - 2 * ε)) ≤
      ν.real (cylinder (liftBlock S.o 0 w)) := fun w hw =>
    le_trans (by gcongr; linarith [abs_le.1 (hclose w hw)]) (hgibbs' w).1
  have hup : ∀ w ∈ good, ν.real (cylinder (liftBlock S.o 0 w)) ≤
      C * Real.exp (n * (energy l₁ l₂ s + 2 * ε)) := fun w hw =>
    (hgibbs' w).2.trans (by gcongr; linarith [abs_le.1 (hclose w hw)])
  have hsum_le_one : ∑ w ∈ good, ν.real (cylinder (liftBlock S.o 0 w)) ≤ 1 := by
    have hinj : Function.Injective (liftBlock S.o 0 : (Fin n → ι) → Fin n → ι × ZMod 2) :=
      fun w w' h => funext fun k => by simpa using congrArg (fun v => (v k).1) h
    rw [← Finset.sum_image (f := fun v => ν.real (cylinder v)) hinj.injOn,
      ← sum_measureReal_cylinder ν n]
    exact Finset.sum_le_univ_sum_of_nonneg fun _ => measureReal_nonneg
  have hN1 : (N : ℝ) * (C⁻¹ * Real.exp (n * (energy l₁ l₂ s - 2 * ε))) ≤ 1 := by
    have := Finset.card_nsmul_le_sum good _ _ hlow
    rw [nsmul_eq_mul] at this
    exact this.trans hsum_le_one
  have hN2 : η ≤ N * (C * Real.exp (n * (energy l₁ l₂ s + 2 * ε))) := by
    have := Finset.sum_le_card_nsmul good _ _ hup
    rw [nsmul_eq_mul] at this
    exact hgood.trans (hmeas_le.trans this)
  have hNpos : 0 < (N : ℝ) := by
    by_contra h
    have : (N : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg _)
    rw [this, zero_mul] at hN2
    exact absurd hN2 (not_le.2 hη)
  -- pigeonhole on the count vectors and the orientation
  set D := Fintype.card (ι × ZMod 2) with hD
  set key : (Fin n → ι) → ℝ × ℝ × ZMod 2 := fun w =>
    (S.gDeriv (S.codeWord 0 (List.ofFn w)), S.gDeriv (S.codeWord 1 (List.ofFn w)),
      S.oWord (List.ofFn w)) with hkey
  set F : (ι × ZMod 2 → ℕ) × ZMod 2 → ℝ × ℝ × ZMod 2 := fun q =>
    (∏ p, S.ratio p ^ q.1 p, ∏ p, S.ratio p ^ q.1 (flipSymbol p), q.2) with hF
  set t := ((Fintype.piFinset fun _ : ι × ZMod 2 => Finset.range (n + 1)) ×ˢ
    (Finset.univ : Finset (ZMod 2))).image F with ht_def
  have hmaps : ∀ w ∈ good, key w ∈ t := by
    intro w _
    refine Finset.mem_image.2
      ⟨(fun p => (S.codeWord 0 (List.ofFn w)).count p, S.oWord (List.ofFn w)), ?_, ?_⟩
    · rw [Finset.mem_product, Fintype.mem_piFinset]
      refine ⟨fun p => Finset.mem_range.2 ?_, Finset.mem_univ _⟩
      show (S.codeWord 0 (List.ofFn w)).count p < n + 1
      have := List.count_le_length (a := p) (l := S.codeWord 0 (List.ofFn w))
      rw [length_codeWord, List.length_ofFn] at this
      omega
    · simp only [hF, hkey]
      rw [gDeriv_eq_prod_count, gDeriv_eq_prod_count]
      simp only [count_codeWord_one]
  have ht_card : (t.card : ℝ) ≤ 2 * (n + 1) ^ D := by
    have h := Finset.card_image_le (s := (Fintype.piFinset fun _ : ι × ZMod 2 =>
      Finset.range (n + 1)) ×ˢ (Finset.univ : Finset (ZMod 2))) (f := F)
    rw [Finset.card_product, Fintype.card_piFinset, Finset.card_univ, ZMod.card] at h
    simp only [Finset.card_range, Finset.prod_const, Finset.card_univ] at h
    calc (t.card : ℝ) ≤ (((n + 1) ^ D * 2 : ℕ) : ℝ) := by exact_mod_cast h
      _ = 2 * (n + 1) ^ D := by push_cast; ring
  obtain ⟨w₀, hw₀⟩ : good.Nonempty := Finset.card_pos.1 (Nat.cast_pos.1 hNpos)
  have ht : t.Nonempty := ⟨key w₀, hmaps w₀ hw₀⟩
  have htpos : (0 : ℝ) < t.card := Nat.cast_pos.2 (Finset.card_pos.2 ht)
  obtain ⟨k, -, hk⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (b := (N : ℝ) / t.card) hmaps ht (by rw [nsmul_eq_mul, mul_div_cancel₀ _ htpos.ne'])
  set W' := good.filter fun w => key w = k with hW'
  have hW'pos : (0 : ℝ) < W'.card := lt_of_lt_of_le (div_pos hNpos htpos) hk
  have hN3 : (N : ℝ) ≤ W'.card * (2 * (n + 1) ^ D) := by
    rw [div_le_iff₀ htpos] at hk
    calc (N : ℝ) ≤ W'.card * t.card := hk
      _ ≤ W'.card * (2 * (n + 1) ^ D) := by gcongr
  obtain ⟨a, b, c⟩ := k
  have hmem : ∀ w ∈ W', S.oWord (List.ofFn w) = c ∧
      S.gDeriv (S.codeWord 0 (List.ofFn w)) = a ∧ S.gDeriv (S.codeWord 1 (List.ofFn w)) = b := by
    intro w hw
    rw [hW', Finset.mem_filter] at hw
    simp only [hkey, Prod.mk.injEq] at hw
    exact ⟨hw.2.2.2, hw.2.1, hw.2.2.1⟩
  obtain ⟨w₁, hw₁⟩ : W'.Nonempty := Finset.card_pos.1 (Nat.cast_pos.1 hW'pos)
  have hw₁g : w₁ ∈ good := (Finset.mem_filter.1 hw₁).1
  rw [hgood_def, Finset.mem_filter] at hw₁g
  obtain ⟨-, ha₁, hb₁⟩ := hw₁g
  obtain ⟨-, ha₁', hb₁'⟩ := hmem w₁ hw₁
  rw [ha₁'] at ha₁
  rw [hb₁'] at hb₁
  -- the logarithmic bounds
  have hNlog_up : Real.log N ≤ Real.log C + n * (2 * ε - energy l₁ l₂ s) := by
    have h : (N : ℝ) ≤ C * Real.exp (n * (2 * ε - energy l₁ l₂ s)) := by
      rw [← le_div_iff₀ (by positivity), one_div, mul_inv, inv_inv, ← Real.exp_neg] at hN1
      have e : -(n * (energy l₁ l₂ s - 2 * ε)) = n * (2 * ε - energy l₁ l₂ s) := by ring
      rw [e] at hN1
      exact hN1
    calc Real.log N ≤ Real.log (C * Real.exp (n * (2 * ε - energy l₁ l₂ s))) :=
          Real.log_le_log hNpos h
      _ = _ := by rw [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hNlog_low : Real.log η ≤ Real.log N + Real.log C + n * (energy l₁ l₂ s + 2 * ε) := by
    calc Real.log η ≤ Real.log (N * (C * Real.exp (n * (energy l₁ l₂ s + 2 * ε)))) :=
          Real.log_le_log hη hN2
      _ = _ := by
        rw [Real.log_mul hNpos.ne' (by positivity), Real.log_mul hC.ne' (Real.exp_pos _).ne',
          Real.log_exp, add_assoc]
  have hW'log : Real.log W'.card ≤ Real.log N :=
    Real.log_le_log hW'pos (by exact_mod_cast Finset.card_filter_le _ _)
  have hNlog_W : Real.log N ≤ Real.log W'.card + Real.log 2 + D * Real.log (n + 1) := by
    calc Real.log N ≤ Real.log (W'.card * (2 * (n + 1) ^ D)) := Real.log_le_log hNpos hN3
      _ = _ := by
        rw [Real.log_mul hW'pos.ne' (by positivity), Real.log_mul two_ne_zero (by positivity),
          Real.log_pow, add_assoc]
  refine ⟨W'.image List.ofFn, a, b, c, (Finset.card_pos.1 (Nat.cast_pos.1 hW'pos)).image _, ?_,
    ha₁, hb₁, ?_, ?_⟩
  · intro w hw
    obtain ⟨w', hw', rfl⟩ := Finset.mem_image.1 hw
    exact ⟨List.length_ofFn, hmem w' hw'⟩
  · rw [Finset.card_image_of_injective _ List.ofFn_injective]
    linarith
  · rw [Finset.card_image_of_injective _ List.ofFn_injective]
    linarith

/-- The selection of tex lines 3476 to 3494 for one tolerance `ε`: for an ergodic Gibbs
measure `ν` of `f_{1,s}` at pressure `0` carried by `Σ_Z`, with `∫ f_{1,1} dν = l₁` and
`∫ f_{2,1} dν = l₂`, and for every `m`, there are a length `n ≥ m` and a non-empty class `W` of
words of length `n` with common orientation and common coordinate derivatives `a`, `b`, such
that `log #W / n` is within `3ε` of `-Λ`, `log |a| / n` within `3ε` of `l₁` and `log |b| / n`
within `3ε` of `l₂`, where `Λ = energy l₁ l₂ s`. -/
theorem exists_class_of_gibbs {s l₁ l₂ : ℝ} (hs0 : 0 < s) (hs2 : s < 2)
    (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν] (herg : Ergodic (shift 1) ν)
    (hsupp : ν (subshift S.o)ᶜ = 0) (hgibbs : IsGibbsAt S.o (S.potential₁ s) ν 0)
    (hl₁ : ∫ y, S.potential₁ 1 (y 0) ∂ν = l₁) (hl₂ : ∫ y, S.potential₂ 1 (y 0) ∂ν = l₂)
    {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    ∃ (n : ℕ) (W : Finset (List ι)) (a b : ℝ) (c : ZMod 2), m ≤ n ∧ 0 < n ∧ W.Nonempty ∧
      (∀ w ∈ W, w.length = n ∧ S.oWord w = c ∧ S.gDeriv (S.codeWord 0 w) = a ∧
        S.gDeriv (S.codeWord 1 w) = b) ∧
      |Real.log W.card / n + energy l₁ l₂ s| ≤ 3 * ε ∧
      |Real.log |a| / n - l₁| ≤ 3 * ε ∧ |Real.log |b| / n - l₂| ≤ 3 * ε := by
  have : Nonempty ι := ⟨((nonempty_of_isProbabilityMeasure ν).some 0).1⟩
  have hE : 0 < ν.real (Set.range (tau S.o)) :=
    ENNReal.toReal_pos
      ((isGibbs_iff_exists_isGibbsAt.2 ⟨0, hgibbs⟩).measure_range_tau_pos hsupp).ne'
      (measure_ne_top _ _)
  obtain ⟨C, hC, hG⟩ := hgibbs
  simp only [mul_zero, neg_zero, zero_add] at hG
  set η := ν.real (Set.range (tau S.o)) / 2 with hη_def
  have hη : 0 < η := half_pos hE
  set Bad : ℕ → Set (ℤ → ι × ZMod 2) := fun n =>
    {y | ε ≤ |(∑ k ∈ Finset.range n, S.potential₁ 1 (y k)) / n - l₁|} ∪
      {y | ε ≤ |(∑ k ∈ Finset.range n, S.potential₂ 1 (y k)) / n - l₂|} with hBad
  have hbad₁ := tendsto_measure_birkhoff_bad herg (S.potential₁ 1) hε
  have hbad₂ := tendsto_measure_birkhoff_bad herg (S.potential₂ 1) hε
  rw [hl₁] at hbad₁
  rw [hl₂] at hbad₂
  have hbad : Tendsto (fun n : ℕ => ν.real (Bad n)) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => ν (Bad n)) atTop (𝓝 0) := by
      have := hbad₁.add hbad₂
      rw [add_zero] at this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this
        (fun _ => zero_le) (fun _ => measure_union_le _ _)
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    rw [ENNReal.toReal_zero] at this
    exact this
  have hev1 : ∀ᶠ n : ℕ in atTop, η ≤ ν.real (Set.range (tau S.o) \ Bad n) := by
    filter_upwards [hbad.eventually_lt_const hη] with n hn
    have h1 : ν.real (Set.range (tau S.o)) ≤
        ν.real (Set.range (tau S.o) \ Bad n) + ν.real (Bad n) :=
      (measureReal_mono (Set.subset_sdiff_union _ _) (measure_ne_top _ _)).trans
        (measureReal_union_le _ _)
    rw [hη_def] at hn ⊢
    linarith
  have herr := tendsto_errorTerm_div (|Real.log C| + Real.log 2 + |Real.log η|)
    (Fintype.card (ι × ZMod 2))
  have hev2 := herr.eventually_lt_const hε
  obtain ⟨n, hn1, hn2, hnm, hn0⟩ :=
    (hev1.and (hev2.and ((eventually_ge_atTop m).and (eventually_gt_atTop 0)))).exists
  obtain ⟨W, a, b, c, hW, hmem, ha, hb, hlow, hup⟩ :=
    S.exists_class hs0 hs2 hC hG hε hη hn0 hn1
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  refine ⟨n, W, a, b, c, hnm, hn0, hW, hmem, ?_, ha.le.trans (by linarith),
    hb.le.trans (by linarith)⟩
  rw [div_lt_iff₀ hn'] at hn2
  have hD : 0 ≤ (Fintype.card (ι × ZMod 2) : ℝ) * Real.log (n + 1) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have e : Real.log W.card / n + energy l₁ l₂ s = (Real.log W.card + n * energy l₁ l₂ s) / n := by
    field_simp
  rw [e, abs_div, abs_of_pos hn', div_le_iff₀ hn', abs_le]
  constructor <;> linarith [le_abs_self (Real.log C), neg_abs_le (Real.log C),
    le_abs_self (Real.log η), neg_abs_le (Real.log η)]

/-- The typical words of a Gibbs measure, tex lines 3470 to 3503 for a measure on `Σ_Z`: let
`ν` be an ergodic probability measure carried by `Σ_Z` with the Gibbs bounds for `f_{1,s}` at
pressure `0`, `0 < s < 2`, and let `l₁ = ∫ f_{1,1} dν`, `l₂ = ∫ f_{2,1} dν`. Then there are
lengths `n_m → ∞` and non-empty finite families `W_m` of words of length `n_m` with a common
diagonal planar matrix `A_w = diag(a_m, b_m)`, such that `log #W_m / n_m → -Λ`,
`log |a_m| / n_m → l₁` and `log |b_m| / n_m → l₂`, where `Λ = energy l₁ l₂ s` is the
`s`-energy of `eq:energy_def` at `l₁`, `l₂`. The article's use of mixing to return to the
horizontal orientation (tex lines 3474 to 3477) is replaced by appending one anti-diagonal
generator to the words of a class of odd orientation. -/
theorem exists_typical_words_of_gibbs {s l₁ l₂ : ℝ} (hs0 : 0 < s) (hs2 : s < 2)
    (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν] (herg : Ergodic (shift 1) ν)
    (hsupp : ν (subshift S.o)ᶜ = 0) (hgibbs : IsGibbsAt S.o (S.potential₁ s) ν 0)
    (hl₁ : ∫ y, S.potential₁ 1 (y 0) ∂ν = l₁) (hl₂ : ∫ y, S.potential₂ 1 (y 0) ∂ν = l₂) :
    ∃ (n : ℕ → ℕ) (W : ℕ → Finset (List ι)) (a b : ℕ → ℝ),
      Tendsto n atTop atTop ∧ (∀ m, 0 < n m) ∧ (∀ m, (W m).Nonempty) ∧
      (∀ m, ∀ w ∈ W m, w.length = n m ∧ S.matWord w = boxMat 0 (a m) (b m)) ∧
      Tendsto (fun m => Real.log (W m).card / n m) atTop (𝓝 (-energy l₁ l₂ s)) ∧
      Tendsto (fun m => Real.log |a m| / n m) atTop (𝓝 l₁) ∧
      Tendsto (fun m => Real.log |b m| / n m) atTop (𝓝 l₂) := by
  have : Nonempty ι := ⟨((nonempty_of_isProbabilityMeasure ν).some 0).1⟩
  obtain ⟨K, hK⟩ := S.exists_abs_log_abs_ratio_le
  have key : ∀ m : ℕ, ∃ (n : ℕ) (W : Finset (List ι)) (a b : ℝ) (c : ZMod 2),
      m ≤ n ∧ 0 < n ∧ W.Nonempty ∧
      (∀ w ∈ W, w.length = n ∧ S.oWord w = c ∧ S.gDeriv (S.codeWord 0 w) = a ∧
        S.gDeriv (S.codeWord 1 w) = b) ∧
      |Real.log W.card / n + energy l₁ l₂ s| ≤ 3 * (1 / ((m : ℝ) + 1)) ∧
      |Real.log |a| / n - l₁| ≤ 3 * (1 / ((m : ℝ) + 1)) ∧
      |Real.log |b| / n - l₂| ≤ 3 * (1 / ((m : ℝ) + 1)) := fun m =>
    S.exists_class_of_gibbs hs0 hs2 ν herg hsupp hgibbs hl₁ hl₂ (by positivity) m
  choose n W a b c hmn hn0 hW hmem hcard ha hb using key
  have fix : ∀ m, ∃ (e : ℕ) (W' : Finset (List ι)) (a' b' : ℝ), e ≤ 1 ∧
      W'.card = (W m).card ∧ W'.Nonempty ∧
      (∀ w ∈ W', w.length = n m + e ∧ S.matWord w = boxMat 0 a' b') ∧
      abs (Real.log |a'| - Real.log |a m|) ≤ K ∧ abs (Real.log |b'| - Real.log |b m|) ≤ K :=
    fun m => S.exists_diagonal_of_class hK (hW m) (hmem m)
  choose e W' a' b' he hcard' hW' hmem' ha' hb' using fix
  have hL : Tendsto n atTop atTop := tendsto_atTop_mono hmn tendsto_id
  refine ⟨fun m => n m + e m, W', a', b', ?_, fun m => Nat.add_pos_left (hn0 m) _, hW', hmem',
    ?_, ?_, ?_⟩
  · exact tendsto_atTop_mono (fun m => (hmn m).trans (Nat.le_add_right _ _)) tendsto_id
  · refine tendsto_div_add_of_tendsto_div (K := 0) (u := fun m => Real.log ((W m).card : ℝ))
      (v := fun m => Real.log ((W' m).card : ℝ)) hL he (tendsto_of_abs_sub_le fun m => ?_)
      fun m => by simp [hcard']
    rw [sub_neg_eq_add]
    exact hcard m
  · exact tendsto_div_add_of_tendsto_div hL he (tendsto_of_abs_sub_le ha) ha'
  · exact tendsto_div_add_of_tendsto_div hL he (tendsto_of_abs_sub_le hb) hb'

/-- The typical words of the equilibrium state, tex lines 3470 to 3503 in the proof of
`thm:main2`: for a box-like system with rotations containing a proximal diagonal generator,
`0 < s < 2` with `P(𝖠, s) = 0`, and an invariant `s`-equilibrium state `μ`, there are lengths
`n_m → ∞` and non-empty finite families `W_m` of words of length `n_m` with a common diagonal
planar matrix `A_w = diag(a_m, b_m)`, such that `log #W_m / n_m → h_0(μ)`,
`log |a_m| / n_m → λ_1(𝖠, μ)` and `log |b_m| / n_m → λ_2(𝖠, μ)`. The families are selected
from the Gibbs measure `μ_1` of `thm:eq_state_is_sum`, whose Gibbs constant is `P(𝖠, s) = 0`
and whose integrals of `f_{1,1}` and `f_{2,1}` are the Lyapunov exponents; the entropy enters
through `eq:eq_state_def`, `h_0(μ) = -Λ(𝖠, μ, s)`.
Depends on: `EquilibriumGibbsStatement` (`thm:irred_eq_state`), `FraserJordanJurgaDecomposition`
(`thm:eq_state_is_sum`), `System.GibbsDecomposition.isGibbsAt₁`,
`System.GibbsDecomposition.lyapunov₁_eq_integral`,
`System.GibbsDecomposition.lyapunov₂_eq_integral_potential₂`, `birkhoff_ergodic`. -/
theorem exists_typical_words {ι : Type u} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι) {s : ℝ}
    (hfk : EquilibriumGibbsStatement.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal) (hs0 : 0 < s) (hs2 : s < 2)
    (hP : S.pressure s = 0) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState s μ) :
    ∃ (n : ℕ → ℕ) (W : ℕ → Finset (List ι)) (a b : ℕ → ℝ),
      Tendsto n atTop atTop ∧ (∀ m, 0 < n m) ∧ (∀ m, (W m).Nonempty) ∧
      (∀ m, ∀ w ∈ W m, w.length = n m ∧ S.matWord w = boxMat 0 (a m) (b m)) ∧
      Tendsto (fun m => Real.log (W m).card / n m) atTop (𝓝 (entropy μ)) ∧
      Tendsto (fun m => Real.log |a m| / n m) atTop (𝓝 (S.lyapunov₁ μ)) ∧
      Tendsto (fun m => Real.log |b m| / n m) atTop (𝓝 (S.lyapunov₂ μ)) := by
  have hgibbs := hfk S hrot hs0 hs2 μ hinv heq
  obtain ⟨μ₁, μ₂, hdec⟩ := hfjj S hrot hdiag hs0 hs2 μ hinv hgibbs
  have := hdec.prob₁
  have hG := hdec.isGibbsAt₁ hs0 hs2
  rw [hP] at hG
  have hent : -energy (S.lyapunov₁ μ) (S.lyapunov₂ μ) s = entropy μ := by
    have h := heq.pressure_eq hinv hs0.le
    rw [hP] at h
    linarith
  obtain ⟨n, W, a, b, h⟩ := S.exists_typical_words_of_gibbs hs0 hs2 μ₁ hdec.ergodic₁ hdec.supp₁
    hG hdec.lyapunov₁_eq_integral.symm hdec.lyapunov₂_eq_integral_potential₂.symm
  rw [hent] at h
  exact ⟨n, W, a, b, h⟩

end System

end BoxLike
