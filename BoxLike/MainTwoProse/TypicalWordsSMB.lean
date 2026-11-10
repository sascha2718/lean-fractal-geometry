module

/-
The typical words of the proof of `thm:main2` in `sec:dimension_result_proof`, by the route of
the prose: the Gibbs measure `μ_1` of `f_{1,t}` on `Σ_Z` returns to the horizontal orientation
`τ(Σ)`, the words of `W_{n,ε}` start and end in `τ(Σ)` and have their cylinder measures and
coordinate derivatives controlled by the Shannon–McMillan–Breiman and Birkhoff theorems, the
counting bounds `exp(n(h-ε)) ≤ #W_{n,ε} ≤ exp(n(h+ε))` follow from the cylinder measures (here
with a constant in front of the lower bound), and a pigeonhole on the digit frequencies `k⃗` of
the `2N` symbols keeps a class `W_{n,ε}(k⃗)` with constant coordinate derivatives. The result
is a sequence of finite families `W_n` of planar words of length `n` with a common diagonal
matrix `A_w = diag(a_n, b_n)` and the limits `eq:diagonal-subsystem-limits`:
`log #W_n / n → h_0(μ)`, `log |a_n| / n → λ_1(𝖠, μ)` and `log |b_n| / n → λ_2(𝖠, μ)`. The
manuscript obtains the returns to `τ(Σ)` from the mixing of `μ_1`; here they come from
ergodicity through Cesàro averages.

The Shannon–McMillan–Breiman theorem enters as the hypothesis
`hsmb : ShannonMcMillanBreimanStatement.{u}` of `BoxLike/SMBStatement.lean`, a result of the
library (`shannonMcMillanBreiman` in `BoxLike/ShannonMcMillanBreiman.lean`), not a literature
hypothesis.

* `measurable_info`, `tendsto_measure_smb_bad`: the Shannon–McMillan–Breiman theorem in the form
  of convergence in measure.
* `frequently_half_le_of_tendsto_cesaro`, `tendsto_cesaro_measure_inter_shift`,
  `frequently_measure_inter_shift_ge`: the return `ν(E ∩ σ^{-n} E) ≥ ν(E)² / 2` for infinitely
  many `n`, from the mean ergodic form of `n⁻¹ ∑_{k<n} ν(E ∩ σ^{-k} E) → ν(E)²`.
* `System.returnSet`, `System.typicalBad`: the set `τ(Σ) ∩ σ^{-n} τ(Σ)` and the exceptional set
  of the two theorems.
* `System.block_tau`, `System.shift_tau_mem_range_tau_iff`, `System.liftBlock_zero_injective`,
  `System.sum_potential₁_one_tau`, `System.sum_potential₂_one_tau`: a word starting in `E` is the
  lift of its planar word, it ends in `E` exactly when its planar matrix is diagonal, forgetting
  the orientation is injective on these words, and their Birkhoff sums are the logarithms of
  their coordinate derivatives.
* `System.exists_class_smb`: the counting and the pigeonhole for one tolerance and one length,
  with the pigeonhole lemmas of `BoxLike/MainTwoProse/Pigeonhole.lean`.
* `System.exists_class_smb_of_ergodic`: the selection for one tolerance.
* `System.exists_typical_words_smb`: the typical words of an ergodic measure on `Σ_Z`.
* `System.exists_typical_words_prose`: the typical words of the equilibrium state.
-/
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.General
public import BoxLike.Main
public import BoxLike.MainTwoProse.Pigeonhole
public import BoxLike.SMBStatement
public import BoxLike.TypicalWords

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology

universe u

section SMB

variable {α : Type u} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The information function `𝐣 ↦ -n⁻¹ log ν([j_0 ⋯ j_{n-1}])` is Borel: it factors through the
block of length `n`, a map into a finite discrete space. -/
theorem measurable_info (ν : Measure (ℤ → α)) (n : ℕ) :
    Measurable fun y : ℤ → α => -Real.log (ν.real (cylinder (block n y))) / n :=
  (Measurable.of_discrete (f := fun w : Fin n → α => -Real.log (ν.real (cylinder w)) / n)).comp
    (measurable_block n)

/-- The Shannon–McMillan–Breiman theorem of the proof of `thm:main2` in the form of convergence
in measure: for an ergodic measure `ν`, the measure of the set where
`-n⁻¹ log ν([j_0 ⋯ j_{n-1}])` is at distance at least `ε` from `h(ν)` tends to zero. -/
theorem tendsto_measure_smb_bad (hsmb : ShannonMcMillanBreimanStatement.{u})
    {ν : Measure (ℤ → α)} [IsProbabilityMeasure ν] (herg : Ergodic (shift 1) ν) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      ν {y | ε ≤ |-Real.log (ν.real (cylinder (block n y))) / n - entropy ν|}) atTop (𝓝 0) := by
  have hae := hsmb α ν herg
  have h := tendstoInMeasure_of_tendsto_ae (μ := ν)
    (f := fun n y => -Real.log (ν.real (cylinder (block n y))) / n)
    (g := fun _ => entropy ν) (fun n => (measurable_info ν n).aestronglyMeasurable) hae
  have := h (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  refine this.congr fun n => ?_
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq, edist_dist, Real.dist_eq]
  exact ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)

end SMB

/-- A real sequence bounded above whose Cesàro means converge to `L > 0` is at least `L / 2`
infinitely often. -/
theorem frequently_half_le_of_tendsto_cesaro {a : ℕ → ℝ} {L B : ℝ} (hB : ∀ k, a k ≤ B)
    (hL : 0 < L) (h : Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, a k) / n) atTop (𝓝 L)) :
    ∃ᶠ k in atTop, L / 2 ≤ a k := by
  rw [Filter.frequently_atTop]
  intro K
  by_contra hcon
  push Not at hcon
  have hbound : ∀ n : ℕ, (∑ k ∈ Finset.range n, a k) ≤ (min n K : ℕ) * |B| + n * (L / 2) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      rcases lt_or_ge n K with hn | hn
      · have hmin : min (n + 1) K = min n K + 1 := by omega
        rw [hmin, Nat.cast_add, Nat.cast_one, Nat.cast_succ]
        linarith [hB n, le_abs_self B]
      · have hmin : min (n + 1) K = min n K := by omega
        rw [hmin, Nat.cast_succ]
        linarith [hcon n hn]
  have hlim : Tendsto (fun n : ℕ => (K * |B|) / n + L / 2) atTop (𝓝 (0 + L / 2)) :=
    (tendsto_const_div_atTop_nhds_zero_nat _).add tendsto_const_nhds
  have hle : L ≤ 0 + L / 2 := by
    refine le_of_tendsto_of_tendsto h hlim ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
    rw [div_le_iff₀ hn', add_mul, div_mul_cancel₀ _ hn'.ne']
    have h1 : ((min n K : ℕ) : ℝ) * |B| ≤ K * |B| :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_right n K) (abs_nonneg B)
    nlinarith [hbound n]
  linarith

section Return

variable {α : Type*} [MeasurableSpace α]

/-- The mean ergodic form of the return of an ergodic measure to a set of positive measure:
`n⁻¹ ∑_{k<n} ν(E ∩ σ^{-k} E) → ν(E)²`. -/
theorem tendsto_cesaro_measure_inter_shift {ν : Measure (ℤ → α)} [IsProbabilityMeasure ν]
    (herg : Ergodic (shift 1) ν) {E : Set (ℤ → α)} (hE : MeasurableSet E) :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, ν.real (E ∩ shift k ⁻¹' E)) / n) atTop
      (𝓝 (ν.real E ^ 2)) := by
  set f : (ℤ → α) → ℝ := E.indicator 1 with hf
  have hfm : Measurable f := measurable_one.indicator hE
  have hfi : Integrable f ν := (integrable_const (1 : ℝ)).indicator hE
  have hfE : ∫ y, f y ∂ν = ν.real E := integral_indicator_one hE
  have hb := birkhoff_ergodic herg hfi
  have hf01 : ∀ y, 0 ≤ f y ∧ f y ≤ 1 := fun y => by
    by_cases hy : y ∈ E <;> simp [hf, hy]
  have hsm : ∀ k : ℕ, Measurable fun y => f (shift k y) := fun k => hfm.comp (measurable_shift k)
  have havg : ∀ n : ℕ, ∀ y, birkhoffAverage ℝ (shift 1) f n y =
      (∑ k ∈ Finset.range n, f (shift k y)) / n := fun n y => birkhoffAverage_shift_one f n y
  -- dominated convergence for `f · avg_n`
  have hconv : Tendsto (fun n : ℕ => ∫ y, f y * birkhoffAverage ℝ (shift 1) f n y ∂ν) atTop
      (𝓝 (∫ y, f y * ν.real E ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun n => ?_)
      (integrable_const 1) (fun n => Eventually.of_forall fun y => ?_) ?_
    · have : Measurable fun y => f y * birkhoffAverage ℝ (shift 1) f n y := by
        simp only [havg]
        exact hfm.mul ((Finset.measurable_sum _ fun k _ => hsm k).div_const _)
      exact this.aestronglyMeasurable
    · rw [havg, Real.norm_eq_abs]
      have hs0 : 0 ≤ ∑ k ∈ Finset.range n, f (shift k y) :=
        Finset.sum_nonneg fun k _ => (hf01 _).1
      have hs1 : ∑ k ∈ Finset.range n, f (shift k y) ≤ n := by
        have := Finset.sum_le_sum (s := Finset.range n) fun k _ => (hf01 (shift k y)).2
        simpa using this
      have hq0 : 0 ≤ (∑ k ∈ Finset.range n, f (shift k y)) / n := div_nonneg hs0 (Nat.cast_nonneg _)
      have hq1 : (∑ k ∈ Finset.range n, f (shift k y)) / n ≤ 1 := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · rw [div_le_one (Nat.cast_pos.2 hn)]; exact hs1
      rw [abs_of_nonneg (mul_nonneg (hf01 y).1 hq0)]
      calc f y * ((∑ k ∈ Finset.range n, f (shift k y)) / n) ≤ 1 * 1 :=
            mul_le_mul (hf01 y).2 hq1 hq0 zero_le_one
        _ = 1 := one_mul 1
    · filter_upwards [hb] with y hy
      rw [← hfE]
      exact hy.const_mul (f y)
  have hlim : ∫ y, f y * ν.real E ∂ν = ν.real E ^ 2 := by
    rw [integral_mul_const, hfE, sq]
  rw [hlim] at hconv
  refine hconv.congr fun n => ?_
  have hpt : ∀ y, f y * birkhoffAverage ℝ (shift 1) f n y =
      (∑ k ∈ Finset.range n, (E ∩ shift k ⁻¹' E).indicator 1 y) / n := by
    intro y
    rw [havg, mul_div_assoc', Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Set.inter_indicator_one]
    simp only [hf, Set.indicator, Pi.mul_apply, Pi.one_apply, mul_ite, mul_one, mul_zero]
    rfl
  simp only [hpt]
  rw [integral_div, integral_finsetSum]
  · congr 1
    exact Finset.sum_congr rfl fun k _ =>
      integral_indicator_one (hE.inter (measurable_shift k hE))
  · exact fun k _ => (integrable_const (1 : ℝ)).indicator (hE.inter (measurable_shift k hE))

/-- The return to the horizontal orientation in the proof of `thm:main2`: for an ergodic
measure `ν` and a Borel set `E` of positive measure, `ν(E ∩ σ^{-n} E) ≥ ν(E)² / 2` for
infinitely many `n`. -/
theorem frequently_measure_inter_shift_ge {ν : Measure (ℤ → α)} [IsProbabilityMeasure ν]
    (herg : Ergodic (shift 1) ν) {E : Set (ℤ → α)} (hE : MeasurableSet E) (hpos : 0 < ν.real E) :
    ∃ᶠ n : ℕ in atTop, ν.real E ^ 2 / 2 ≤ ν.real (E ∩ shift n ⁻¹' E) :=
  frequently_half_le_of_tendsto_cesaro (B := 1) (fun _ => measureReal_le_one) (by positivity)
    (tendsto_cesaro_measure_inter_shift herg hE)

end Return

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι)

/-- The set `E ∩ σ^{-n} E` with `E = τ(Σ)` of the proof of `thm:main2`: the points of `Σ_Z` that
are in the horizontal orientation at the times `0` and `n`. -/
def returnSet (n : ℕ) : Set (ℤ → ι × ZMod 2) :=
  Set.range (tau S.o) ∩ shift n ⁻¹' Set.range (tau S.o)

/-- The exceptional set of the proof of `thm:main2` for the tolerance `ε` at length `n`: the
points at which `-n⁻¹ log ν([j_0 ⋯ j_{n-1}])` is at distance at least `ε` from `h`, or one of
the Birkhoff averages of `f_{1,1}` and `f_{2,1}` is at distance at least `ε` from `l₁`,
respectively `l₂`. -/
def typicalBad (ν : Measure (ℤ → ι × ZMod 2)) (h l₁ l₂ ε : ℝ) (n : ℕ) :
    Set (ℤ → ι × ZMod 2) :=
  {y | ε ≤ |-Real.log (ν.real (cylinder (block n y))) / n - h|} ∪
    ({y | ε ≤ |(∑ k ∈ Finset.range n, S.potential₁ 1 (y k)) / n - l₁|} ∪
      {y | ε ≤ |(∑ k ∈ Finset.range n, S.potential₂ 1 (y k)) / n - l₂|})

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The block of `τ(𝐢)` of length `n` is the lift along the horizontal axis of the block of
`𝐢`. -/
theorem block_tau (x : ℤ → ι) (n : ℕ) : block n (tau S.o x) = liftBlock S.o 0 (block n x) := by
  have h := block_eq_liftBlock (tau_mem_subshift (o := S.o) x) n
  simpa only [tau_apply, eps_zero, unCode_tau] using h

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- `σ^n(τ(𝐢)) ∈ τ(Σ)` exactly when the word `𝐢|_n` has an even number of anti-diagonal
generators, that is, when its planar matrix is diagonal. -/
theorem shift_tau_mem_range_tau_iff (x : ℤ → ι) (n : ℕ) :
    shift n (tau S.o x) ∈ Set.range (tau S.o) ↔ S.oWord (List.ofFn (block n x)) = 0 := by
  rw [← futureWord_eq_ofFn_block, oWord_futureWord, range_tau]
  simp only [Set.mem_ofPred_eq, shift_apply, add_zero, tau_apply]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun k => ?_, h⟩
    have := tau_mem_subshift (o := S.o) x (n + k)
    simpa [Trans, shift_apply, add_assoc] using this

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Forgetting the orientation is injective on the words of `Σ_Z` starting on the horizontal
axis (proof of `thm:main2`): such a word is the lift `liftBlock o 0 w` of its planar word `w`. -/
theorem liftBlock_zero_injective (o : ι → ZMod 2) {n : ℕ} :
    Function.Injective (liftBlock o 0 : (Fin n → ι) → Fin n → ι × ZMod 2) :=
  fun w w' h => funext fun k => by simpa using congrArg (fun v => (v k).1) h

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The Birkhoff sum of `f_{1,1}` along `τ(𝐢)` is `log |g'|` along the horizontal path over
`𝐢|_n`. -/
theorem sum_potential₁_one_tau (x : ℤ → ι) (n : ℕ) :
    ∑ k ∈ Finset.range n, S.potential₁ 1 (tau S.o x k) =
      Real.log |S.gDeriv (S.codeWord 0 (List.ofFn (block n x)))| := by
  rw [sum_potential₁_tau, ← futureWord_eq_ofFn_block, codeWord_futureWord_tau]
  simp

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The Birkhoff sum of `f_{2,1}` along `τ(𝐢)` is `log |g'|` along the vertical path over
`𝐢|_n`. -/
theorem sum_potential₂_one_tau (x : ℤ → ι) (n : ℕ) :
    ∑ k ∈ Finset.range n, S.potential₂ 1 (tau S.o x k) =
      Real.log |S.gDeriv (S.codeWord 1 (List.ofFn (block n x)))| := by
  rw [sum_potential₂_tau, ← futureWord_eq_ofFn_block, codeWord_futureWord_omega]
  simp

/-- The counting step of the proof of `thm:main2` for one tolerance `ε` and one length `n`.
Suppose that the cylinders of `Σ_Z` of positive length have positive `ν`-measure and that the
returning points `τ(Σ) ∩ σ^{-n} τ(Σ)` outside the exceptional set have measure at least
`η > 0`. The words of these points start and end in the horizontal orientation, so their planar
matrices are diagonal, and their cylinders have measure between `e^{-n(h+ε)}` and
`e^{-n(h-ε)}`. Hence there are at least `η e^{n(h-ε)}` and at most `e^{n(h+ε)}` of them. A
largest class with a common count vector of the `2N` symbols loses at most the factor
`(n+1)^{2N}`, and on it both coordinate derivatives are constant. The result is a non-empty
family `W` of planar words of length `n` with a common diagonal matrix `diag(a, b)`, with
`|log |a| / n - l₁| < ε`, `|log |b| / n - l₂| < ε` and
`log η + n (h - ε) - 2N log (n + 1) ≤ log #W ≤ n (h + ε)`. -/
theorem exists_class_smb {ν : Measure (ℤ → ι × ZMod 2)} [IsProbabilityMeasure ν]
    (hpos : ∀ y ∈ subshift S.o, ∀ n : ℕ, 0 < n → 0 < ν.real (cylinder (block n y)))
    {h l₁ l₂ ε η : ℝ} (hη : 0 < η) {n : ℕ} (hn : 0 < n)
    (hgood : η ≤ ν.real (S.returnSet n \ S.typicalBad ν h l₁ l₂ ε n)) :
    ∃ (W : Finset (List ι)) (a b : ℝ), W.Nonempty ∧
      (∀ w ∈ W, w.length = n ∧ S.matWord w = boxMat 0 a b) ∧
      |Real.log |a| / n - l₁| < ε ∧ |Real.log |b| / n - l₂| < ε ∧
      Real.log η + n * (h - ε) - Fintype.card (ι × ZMod 2) * Real.log (n + 1) ≤
        Real.log W.card ∧
      Real.log W.card ≤ n * (h + ε) := by
  classical
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set m : (Fin n → ι) → ℝ := fun u => ν.real (cylinder (liftBlock S.o 0 u)) with hm
  set A : (Fin n → ι) → ℝ := fun u => S.gDeriv (S.codeWord 0 (List.ofFn u)) with hA
  set B : (Fin n → ι) → ℝ := fun u => S.gDeriv (S.codeWord 1 (List.ofFn u)) with hB
  set good : Finset (Fin n → ι) := Finset.univ.filter fun u =>
    S.oWord (List.ofFn u) = 0 ∧ 0 < m u ∧ |-Real.log (m u) / n - h| < ε ∧
      |Real.log |A u| / n - l₁| < ε ∧ |Real.log |B u| / n - l₂| < ε with hgood_def
  -- the returning typical points lie in the cylinders of the good words
  have hcover : S.returnSet n \ S.typicalBad ν h l₁ l₂ ε n ⊆
      ⋃ u ∈ good, cylinder (liftBlock S.o 0 u) := by
    rintro y ⟨⟨⟨x, rfl⟩, hret⟩, hy⟩
    simp only [typicalBad, Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hy
    have hb := S.block_tau x n
    refine Set.mem_iUnion₂.2 ⟨block n x, ?_, ?_⟩
    · rw [hgood_def, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, (S.shift_tau_mem_range_tau_iff x n).1 hret, ?_, ?_, ?_, ?_⟩
      · have := hpos _ (tau_mem_subshift x) n hn
        rwa [hb] at this
      · have := hy.1
        rwa [hb] at this
      · have := hy.2.1
        rwa [S.sum_potential₁_one_tau] at this
      · have := hy.2.2
        rwa [S.sum_potential₂_one_tau] at this
    · rw [← hb]
      exact fun k => rfl
  have hle : η ≤ ∑ u ∈ good, m u :=
    hgood.trans ((measureReal_mono hcover (measure_ne_top _ _)).trans
      (measureReal_biUnion_finset_le _ _))
  -- forgetting the orientation is injective on the words starting in `τ(Σ)`
  have hinj := liftBlock_zero_injective S.o (n := n)
  have hsum1 : ∑ u ∈ good, m u ≤ 1 := by
    rw [hm, ← Finset.sum_image (f := fun v => ν.real (cylinder v)) hinj.injOn,
      ← sum_measureReal_cylinder ν n]
    exact Finset.sum_le_univ_sum_of_nonneg fun _ => measureReal_nonneg
  -- the bounds of the Shannon–McMillan–Breiman theorem for the good words
  have hlow : ∀ u ∈ good, Real.exp (-(n * (h + ε))) ≤ m u := by
    intro u hu
    rw [hgood_def, Finset.mem_filter] at hu
    obtain ⟨-, -, hpos', hsmb, -, -⟩ := hu
    rw [abs_lt] at hsmb
    have h1 : -(n * (h + ε)) ≤ Real.log (m u) := by
      have := hsmb.2
      rw [sub_lt_iff_lt_add', div_lt_iff₀ hn'] at this
      linarith
    calc Real.exp (-(n * (h + ε))) ≤ Real.exp (Real.log (m u)) := Real.exp_le_exp.2 h1
      _ = m u := Real.exp_log hpos'
  have hup : ∀ u ∈ good, m u ≤ Real.exp (-(n * (h - ε))) := by
    intro u hu
    rw [hgood_def, Finset.mem_filter] at hu
    obtain ⟨-, -, hpos', hsmb, -, -⟩ := hu
    rw [abs_lt] at hsmb
    have h1 : Real.log (m u) ≤ -(n * (h - ε)) := by
      have := hsmb.1
      rw [lt_sub_iff_add_lt', lt_div_iff₀ hn'] at this
      linarith
    calc m u = Real.exp (Real.log (m u)) := (Real.exp_log hpos').symm
      _ ≤ Real.exp (-(n * (h - ε))) := Real.exp_le_exp.2 h1
  -- the cardinality bounds
  set N := good.card with hN
  have hN1 : (N : ℝ) * Real.exp (-(n * (h + ε))) ≤ 1 := by
    have := Finset.card_nsmul_le_sum good m _ hlow
    rw [nsmul_eq_mul] at this
    exact this.trans hsum1
  have hN2 : η ≤ N * Real.exp (-(n * (h - ε))) := by
    have := Finset.sum_le_card_nsmul good m _ hup
    rw [nsmul_eq_mul] at this
    exact hle.trans this
  have hNpos : (0 : ℝ) < N := by
    by_contra hc
    have : (N : ℝ) = 0 := le_antisymm (not_lt.1 hc) (Nat.cast_nonneg _)
    rw [this, zero_mul] at hN2
    exact absurd hN2 (not_le.2 hη)
  have hNlog_up : Real.log N ≤ n * (h + ε) := by
    have h1 : (N : ℝ) ≤ Real.exp (n * (h + ε)) := by
      rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _), one_mul] at hN1
      exact hN1
    calc Real.log N ≤ Real.log (Real.exp (n * (h + ε))) := Real.log_le_log hNpos h1
      _ = n * (h + ε) := Real.log_exp _
  have hNlog_low : Real.log η + n * (h - ε) ≤ Real.log N := by
    have h1 := Real.log_le_log hη hN2
    rw [Real.log_mul hNpos.ne' (Real.exp_pos _).ne', Real.log_exp] at h1
    linarith
  -- the pigeonhole on the count vectors of the `2N` symbols: at most `(n+1)^{2N}` classes
  set D := Fintype.card (ι × ZMod 2) with hD
  set key : (Fin n → ι) → ι × ZMod 2 → ℕ := fun u p => (S.codeWord 0 (List.ofFn u)).count p
    with hkey
  set t := Fintype.piFinset fun _ : ι × ZMod 2 => Finset.range (n + 1) with ht_def
  have hmaps : ∀ u ∈ good, key u ∈ t := fun u _ =>
    countVector_mem_piFinset (by rw [length_codeWord, List.length_ofFn])
  have ht_card : t.card = (n + 1) ^ D := card_piFinset_range _ n
  have hgood_ne : good.Nonempty := Finset.card_pos.1 (Nat.cast_pos.1 hNpos)
  obtain ⟨k, -, hW'ne, hN3⟩ := exists_large_class hmaps hgood_ne
  set W' := good.filter fun u => key u = k with hW'
  have hW'pos : (0 : ℝ) < W'.card := Nat.cast_pos.2 (Finset.card_pos.2 hW'ne)
  -- on a class both coordinate derivatives are constant
  obtain ⟨u₁, hu₁⟩ := hW'ne
  set a : ℝ := A u₁ with ha
  set b : ℝ := B u₁ with hb
  have hmem : ∀ u ∈ W', S.oWord (List.ofFn u) = 0 ∧ A u = a ∧ B u = b := by
    intro u hu
    rw [hW', Finset.mem_filter] at hu hu₁
    have hku : key u = key u₁ := hu.2.trans hu₁.2.symm
    have hcount : ∀ p, (S.codeWord 0 (List.ofFn u)).count p =
        (S.codeWord 0 (List.ofFn u₁)).count p := fun p => congrFun hku p
    have hug := hu.1
    rw [hgood_def, Finset.mem_filter] at hug
    exact ⟨hug.2.1, S.gDeriv_codeWord_eq_of_count_eq hcount 0,
      S.gDeriv_codeWord_eq_of_count_eq hcount 1⟩
  have hu₁g : u₁ ∈ good := (Finset.mem_filter.1 hu₁).1
  rw [hgood_def, Finset.mem_filter] at hu₁g
  obtain ⟨-, -, -, -, ha₁, hb₁⟩ := hu₁g
  -- the logarithmic bounds, with the pigeonhole loss `log (n+1)^{2N} = 2N log (n + 1)`
  have hW'log : Real.log W'.card ≤ Real.log N :=
    Real.log_le_log hW'pos (by exact_mod_cast Finset.card_filter_le _ _)
  have hloss : Real.log N ≤ Real.log W'.card + D * Real.log (n + 1) := by
    have h := log_card_le_log_card_class_add ⟨u₁, hu₁⟩ (pow_pos (Nat.succ_pos n) D)
      (by rw [← ht_card]; exact hN3) hgood_ne
    push_cast at h
    rwa [Real.log_pow] at h
  refine ⟨W'.image List.ofFn, a, b, (Finset.card_pos.1 (Nat.cast_pos.1 hW'pos)).image _, ?_,
    ha₁, hb₁, ?_, ?_⟩
  · intro w hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨ho, hau, hbu⟩ := hmem u hu
    refine ⟨List.length_ofFn, ?_⟩
    rw [matWord_eq, ho]
    exact congrArg₂ _ hau hbu
  · rw [Finset.card_image_of_injective _ List.ofFn_injective]
    linarith
  · rw [Finset.card_image_of_injective _ List.ofFn_injective]
    linarith


/-- The selection of the proof of `thm:main2` for one tolerance `ε`: let `ν` be an ergodic
probability measure on `{1, …, 2N}^ℤ` whose cylinders of `Σ_Z` of positive length have positive
measure and with `ν(τ(Σ)) > 0`, and write `h = h(ν)`, `l₁ = ∫ f_{1,1} dν`, `l₂ = ∫ f_{2,1} dν`.
For every `m` there are a length `n ≥ m` and a non-empty family `W` of planar words of length
`n` with a common diagonal matrix `diag(a, b)`, with `log #W / n`, `log |a| / n`, `log |b| / n`
within `2ε` of `h`, `l₁`, `l₂`. The return `ν(τ(Σ) ∩ σ^{-n} τ(Σ)) ≥ ν(τ(Σ))² / 2` holds for
infinitely many `n` by ergodicity, the exceptional sets of the Shannon–McMillan–Breiman and
Birkhoff theorems have measure below `ν(τ(Σ))² / 4` for all large `n`, and the pigeonhole loss
`2N log (n + 1) / n` tends to zero. -/
theorem exists_class_smb_of_ergodic (hsmb : ShannonMcMillanBreimanStatement.{u})
    (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν] (herg : Ergodic (shift 1) ν)
    (hpos : ∀ y ∈ subshift S.o, ∀ n : ℕ, 0 < n → 0 < ν.real (cylinder (block n y)))
    (hE : 0 < ν.real (Set.range (tau S.o))) {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    ∃ (n : ℕ) (W : Finset (List ι)) (a b : ℝ), m ≤ n ∧ 0 < n ∧ W.Nonempty ∧
      (∀ w ∈ W, w.length = n ∧ S.matWord w = boxMat 0 a b) ∧
      |Real.log W.card / n - entropy ν| ≤ 2 * ε ∧
      |Real.log |a| / n - ∫ y, S.potential₁ 1 (y 0) ∂ν| ≤ 2 * ε ∧
      |Real.log |b| / n - ∫ y, S.potential₂ 1 (y 0) ∂ν| ≤ 2 * ε := by
  set h := entropy ν with hh
  set l₁ := ∫ y, S.potential₁ 1 (y 0) ∂ν with hl₁
  set l₂ := ∫ y, S.potential₂ 1 (y 0) ∂ν with hl₂
  set L := ν.real (Set.range (tau S.o)) ^ 2 with hL_def
  have hL : 0 < L := by positivity
  set η := L / 4 with hη_def
  have hη : 0 < η := by positivity
  -- the return to the horizontal orientation
  have hret := frequently_measure_inter_shift_ge herg (measurableSet_range_tau S.o) hE
  -- the exceptional sets of the Shannon–McMillan–Breiman and Birkhoff theorems
  have hb0 := tendsto_measure_smb_bad hsmb herg hε
  have hb1 := tendsto_measure_birkhoff_bad herg (S.potential₁ 1) hε
  have hb2 := tendsto_measure_birkhoff_bad herg (S.potential₂ 1) hε
  have hbad : Tendsto (fun n : ℕ => ν.real (S.typicalBad ν h l₁ l₂ ε n)) atTop (𝓝 0) := by
    have h3 : Tendsto (fun n : ℕ => ν (S.typicalBad ν h l₁ l₂ ε n)) atTop (𝓝 0) := by
      have := hb0.add (hb1.add hb2)
      rw [add_zero, add_zero] at this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this
        (fun _ => zero_le) (fun n => ?_)
      exact (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h3
    rwa [ENNReal.toReal_zero] at this
  -- the pigeonhole loss
  have herr := tendsto_errorTerm_div (|Real.log η|) (Fintype.card (ι × ZMod 2))
  obtain ⟨n, hn1, hn2, hn3, hnm, hn0⟩ := (hret.and_eventually
    ((hbad.eventually_lt_const (show (0 : ℝ) < L / 4 by positivity)).and
      ((herr.eventually_lt_const hε).and
        ((eventually_ge_atTop m).and (eventually_gt_atTop 0))))).exists
  have hgood : η ≤ ν.real (S.returnSet n \ S.typicalBad ν h l₁ l₂ ε n) := by
    have h1 : ν.real (S.returnSet n) ≤
        ν.real (S.returnSet n \ S.typicalBad ν h l₁ l₂ ε n) +
          ν.real (S.typicalBad ν h l₁ l₂ ε n) :=
      (measureReal_mono (Set.subset_sdiff_union _ _) (measure_ne_top _ _)).trans
        (measureReal_union_le _ _)
    have h2 : L / 2 ≤ ν.real (S.returnSet n) := hn1
    rw [hη_def]
    linarith
  obtain ⟨W, a, b, hW, hmem, ha, hb, hlow, hup⟩ := S.exists_class_smb hpos hη hn0 hgood
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  refine ⟨n, W, a, b, hnm, hn0, hW, hmem, ?_, ha.le.trans (by linarith),
    hb.le.trans (by linarith)⟩
  rw [div_lt_iff₀ hn'] at hn3
  have hD : 0 ≤ (Fintype.card (ι × ZMod 2) : ℝ) * Real.log (n + 1) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
  have e : Real.log W.card / n - h = (Real.log W.card - n * h) / n := by field_simp
  rw [e, abs_div, abs_of_pos hn', div_le_iff₀ hn', abs_le]
  constructor <;> nlinarith [le_abs_self (Real.log η), neg_abs_le (Real.log η)]

/-- The typical words of the proof of `thm:main2` for an ergodic measure `ν` on
`{1, …, 2N}^ℤ` whose cylinders of `Σ_Z` of positive length have positive measure, with
`ν(τ(Σ)) > 0`: lengths `n_m → ∞` and non-empty families `W_m` of planar words of length `n_m`
with a common diagonal matrix `A_w = diag(a_m, b_m)` such that `log #W_m / n_m → h(ν)`,
`log |a_m| / n_m → ∫ f_{1,1} dν` and `log |b_m| / n_m → ∫ f_{2,1} dν`. The tolerances
`ε_m = 1/(m+1)` tend to zero. -/
theorem exists_typical_words_smb (hsmb : ShannonMcMillanBreimanStatement.{u})
    (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν] (herg : Ergodic (shift 1) ν)
    (hpos : ∀ y ∈ subshift S.o, ∀ n : ℕ, 0 < n → 0 < ν.real (cylinder (block n y)))
    (hE : 0 < ν.real (Set.range (tau S.o))) :
    ∃ (n : ℕ → ℕ) (W : ℕ → Finset (List ι)) (a b : ℕ → ℝ),
      Tendsto n atTop atTop ∧ (∀ m, 0 < n m) ∧ (∀ m, (W m).Nonempty) ∧
      (∀ m, ∀ w ∈ W m, w.length = n m ∧ S.matWord w = boxMat 0 (a m) (b m)) ∧
      Tendsto (fun m => Real.log (W m).card / n m) atTop (𝓝 (entropy ν)) ∧
      Tendsto (fun m => Real.log |a m| / n m) atTop (𝓝 (∫ y, S.potential₁ 1 (y 0) ∂ν)) ∧
      Tendsto (fun m => Real.log |b m| / n m) atTop (𝓝 (∫ y, S.potential₂ 1 (y 0) ∂ν)) := by
  have key : ∀ m : ℕ, ∃ (n : ℕ) (W : Finset (List ι)) (a b : ℝ), m ≤ n ∧ 0 < n ∧
      W.Nonempty ∧ (∀ w ∈ W, w.length = n ∧ S.matWord w = boxMat 0 a b) ∧
      |Real.log W.card / n - entropy ν| ≤ 2 * (1 / ((m : ℝ) + 1)) ∧
      |Real.log |a| / n - ∫ y, S.potential₁ 1 (y 0) ∂ν| ≤ 2 * (1 / ((m : ℝ) + 1)) ∧
      |Real.log |b| / n - ∫ y, S.potential₂ 1 (y 0) ∂ν| ≤ 2 * (1 / ((m : ℝ) + 1)) :=
    fun m => S.exists_class_smb_of_ergodic hsmb ν herg hpos hE (by positivity) m
  choose n W a b hmn hn0 hW hmem hcard ha hb using key
  have h23 : ∀ m : ℕ, 2 * (1 / ((m : ℝ) + 1)) ≤ 3 * (1 / ((m : ℝ) + 1)) := fun m => by
    have : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1) := by positivity
    linarith
  exact ⟨n, W, a, b, tendsto_atTop_mono hmn tendsto_id, hn0, hW, hmem,
    tendsto_of_abs_sub_le fun m => (hcard m).trans (h23 m),
    tendsto_of_abs_sub_le fun m => (ha m).trans (h23 m),
    tendsto_of_abs_sub_le fun m => (hb m).trans (h23 m)⟩

/-- The typical words of the equilibrium state in the proof of `thm:main2`: for a box-like
system with rotations containing a proximal diagonal generator, `0 < s < 2` and an invariant
`s`-equilibrium state `μ`, there are lengths `n_m → ∞` and non-empty families `W_m` of planar
words of length `n_m` with a common diagonal matrix `A_w = diag(a_m, b_m)` such that
`log #W_m / n_m → h_0(μ)`, `log |a_m| / n_m → λ_1(𝖠, μ)` and `log |b_m| / n_m → λ_2(𝖠, μ)`.
The families are selected from the Gibbs measure `μ_1` of `f_{1,s}` of `thm:eq_state_is_sum`,
which charges every cylinder of `Σ_Z`, has entropy `h_0(μ)` (`thm:entropy_eq_gibbs`) and the
integrals `∫ f_{1,1} dμ_1 = λ_1`, `∫ f_{2,1} dμ_1 = λ_2`, by the Shannon–McMillan–Breiman
theorem, the Birkhoff theorem, the return of `μ_1` to `τ(Σ)` and the pigeonhole on the count
vectors.
Depends on: `ShannonMcMillanBreimanStatement`, `EquilibriumGibbsStatement`,
`FraserJordanJurgaDecomposition`. -/
theorem exists_typical_words_prose (hsmb : ShannonMcMillanBreimanStatement.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal) {s : ℝ} (hs0 : 0 < s)
    (hs2 : s < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState s μ) :
    ∃ (n : ℕ → ℕ) (W : ℕ → Finset (List ι)) (a b : ℕ → ℝ),
      Tendsto n atTop atTop ∧ (∀ m, 0 < n m) ∧ (∀ m, (W m).Nonempty) ∧
      (∀ m, ∀ w ∈ W m, w.length = n m ∧ S.matWord w = boxMat 0 (a m) (b m)) ∧
      Tendsto (fun m => Real.log (W m).card / n m) atTop (𝓝 (entropy μ)) ∧
      Tendsto (fun m => Real.log |a m| / n m) atTop (𝓝 (S.lyapunov₁ μ)) ∧
      Tendsto (fun m => Real.log |b m| / n m) atTop (𝓝 (S.lyapunov₂ μ)) := by
  have : Nonempty ι := nonempty_of_measure μ
  have hgibbs := hfk S hrot hs0 hs2 μ hinv heq
  obtain ⟨μ₁, μ₂, hdec⟩ := hfjj S hrot hdiag hs0 hs2 μ hinv hgibbs
  have := hdec.prob₁
  have hpos : ∀ y ∈ subshift S.o, ∀ n : ℕ, 0 < n → 0 < μ₁.real (cylinder (block n y)) :=
    fun y hy n hn => hdec.gibbs₁.measureReal_cylinder_pos hy hn
  have hE : 0 < μ₁.real (Set.range (tau S.o)) :=
    ENNReal.toReal_pos (hdec.gibbs₁.measure_range_tau_pos hdec.supp₁).ne' (measure_ne_top _ _)
  obtain ⟨n, W, a, b, h⟩ := S.exists_typical_words_smb hsmb μ₁ hdec.ergodic₁ hpos hE
  rw [hdec.entropy_eq₁, ← hdec.lyapunov₁_eq_integral,
    ← hdec.lyapunov₂_eq_integral_potential₂] at h
  exact ⟨n, W, a, b, h⟩

end System

end BoxLike
