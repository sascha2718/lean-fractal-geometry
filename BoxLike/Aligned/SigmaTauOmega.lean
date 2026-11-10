module

/-
`thm:sigma_tau_omega_positive_eq_measure` of `sec:normalisation` by the counting argument of its
proof.

Let `U = ⋃_{j_0 = ℓ+1}^N [j_0]` be the union of the one-symbol cylinders of the anti-diagonal
generators. For `𝐢 ∈ Σ'`, `eq:sigma_tau_omega_positive_eq_measure1` gives the counting inequality
`1_{Σ^τ}(σ^k 𝐢) + 1_{Σ^τ}(σ^{k+1} 𝐢) ≥ 1_U(σ^k 𝐢)` for every `k ∈ ℕ`. Summed over
`k ∈ {0, …, n-1}`, each `k` with `σ^k 𝐢 ∈ Σ^τ` is counted at most twice, so
`#{k < n : σ^k 𝐢 ∈ U} ≤ 2 #{k < n : σ^k 𝐢 ∈ Σ^τ} + 1`. Birkhoff's pointwise ergodic theorem for
the indicators of `Σ^τ` and `U` then gives `μ(Σ^τ) ≥ ½ μ(U)` at a `μ`-typical point of `Σ'`, and
`μ(U) > 0` by full support. The same holds for `Σ^ω`.

* `System.antiDiagSet`, `System.measurableSet_antiDiagSet`: the set `U`.
* `System.indicator_antiDiagSet_le`: the counting inequality at one time `k`.
* `System.iterate_mem_SigmaPrime`: `σ^k(Σ') ⊆ Σ'`.
* `System.birkhoffSum_antiDiagSet_le`: the summed counting inequality.
* `System.measureReal_antiDiagSet_le`: `μ(U) ≤ 2 μ(Σ^τ)` and `μ(U) ≤ 2 μ(Σ^ω)` by Birkhoff.
* `System.sigma_tau_omega_positive_eq_measure`: `thm:sigma_tau_omega_positive_eq_measure`.

The only import is `BoxLike.SigmaMeasure`, so `BoxLike.GibbsOrientation` can import this module.
-/
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.SigmaMeasure

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

universe u

namespace System

/-! ### The counting inequality -/

section AntiDiagonal

variable {ι : Type u} (S : System ι)

/-- The union `⋃_{j_0 = ℓ+1}^N [j_0]` of the one-symbol cylinders of the anti-diagonal generators
(proof of `thm:sigma_tau_omega_positive_eq_measure`): the sequences whose symbol at time `0` has
an anti-diagonal matrix. -/
def antiDiagSet : Set (ℤ → ι) := {x | S.o (x 0) = 1}

/-- The set `⋃_{j_0 = ℓ+1}^N [j_0]` is Borel. -/
theorem measurableSet_antiDiagSet [MeasurableSpace ι] [Finite ι] [MeasurableSingletonClass ι] :
    MeasurableSet S.antiDiagSet :=
  show MeasurableSet ((fun x : ℤ → ι => x 0) ⁻¹' (S.o ⁻¹' {1})) from
    measurable_pi_apply (0 : ℤ) (Set.toFinite (S.o ⁻¹' {1})).measurableSet

/-- The one-symbol cylinder `[i]` of an anti-diagonal generator `A_i` lies in
`⋃_{j_0 = ℓ+1}^N [j_0]`. -/
theorem cylinder_subset_antiDiagSet {i : ι} (hi : S.o i = 1) :
    (cylinder fun _ : Fin 1 => i) ⊆ S.antiDiagSet := fun x hx => by
  have h := hx 0
  simp only [Fin.val_zero, Nat.cast_zero] at h
  change S.o (x 0) = 1
  rw [h, hi]

end AntiDiagonal

section Counting

variable {ι : Type u} [MeasurableSpace ι] (S : System ι)

/-- The counting inequality in the proof of `thm:sigma_tau_omega_positive_eq_measure`, at one
time: for `𝐢 ∈ Σ'`,
`1_{Σ^τ}(𝐢) + 1_{Σ^τ}(σ(𝐢)) ≥ 1_{⋃_{j_0 > ℓ} [j_0]}(𝐢)` and the same for `Σ^ω`. If `A_{i_0}` is
anti-diagonal, then `eq:sigma_tau_omega_positive_eq_measure1` places `σ(𝐢)` in `Σ^τ` when
`𝐢 ∈ Σ^ω` and in `Σ^ω` when `𝐢 ∈ Σ^τ`.
Depends on: `eq:sigma_tau_omega_positive_eq_measure1` (`shift_mem_SigmaTau_iff`). -/
theorem indicator_antiDiagSet_le (μ : Measure (ℤ → ι)) {x : ℤ → ι}
    (hx : x ∈ S.SigmaPrime μ) :
    S.antiDiagSet.indicator (1 : (ℤ → ι) → ℝ) x ≤
        (S.SigmaTau μ).indicator 1 x + (S.SigmaTau μ).indicator 1 (shift 1 x) ∧
      S.antiDiagSet.indicator (1 : (ℤ → ι) → ℝ) x ≤
        (S.SigmaOmega μ).indicator 1 x + (S.SigmaOmega μ).indicator 1 (shift 1 x) := by
  have h0 : ∀ (E : Set (ℤ → ι)) (y : ℤ → ι), 0 ≤ E.indicator (1 : (ℤ → ι) → ℝ) y :=
    fun E y => indicator_nonneg (fun _ _ => zero_le_one) y
  by_cases hU : x ∈ S.antiDiagSet
  · have hU' : S.o (x 0) = 1 := hU
    obtain ⟨hτ, hω⟩ := S.shift_mem_SigmaTau_iff μ x
    rw [indicator_of_mem hU, Pi.one_apply]
    rcases hx with hx | hx
    · refine ⟨?_, ?_⟩
      · rw [indicator_of_mem hx, Pi.one_apply]
        linarith [h0 (S.SigmaTau μ) (shift 1 x)]
      · rw [indicator_of_mem (hω.2 (Or.inr ⟨hU', hx⟩)), Pi.one_apply]
        linarith [h0 (S.SigmaOmega μ) x]
    · refine ⟨?_, ?_⟩
      · rw [indicator_of_mem (hτ.2 (Or.inr ⟨hU', hx⟩)), Pi.one_apply]
        linarith [h0 (S.SigmaTau μ) x]
      · rw [indicator_of_mem hx, Pi.one_apply]
        linarith [h0 (S.SigmaOmega μ) (shift 1 x)]
  · rw [indicator_of_notMem hU]
    exact ⟨add_nonneg (h0 _ _) (h0 _ _), add_nonneg (h0 _ _) (h0 _ _)⟩

/-- `σ^k(Σ') ⊆ Σ'` for every `k ∈ ℕ` (`sec:lyapunov_exponents`, tex line 1521), so the
counting inequality holds at every time along a point of `Σ'`. -/
theorem iterate_mem_SigmaPrime (μ : Measure (ℤ → ι)) {x : ℤ → ι} (hx : x ∈ S.SigmaPrime μ)
    (k : ℕ) : (shift 1)^[k] x ∈ S.SigmaPrime μ := by
  induction k with
  | zero => exact hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (S.shift_mem_SigmaPrime_iff μ _).2 ih

omit [MeasurableSpace ι] in
/-- Summing a bounded non-negative function along the orbit of `σ(𝐢)` instead of `𝐢` changes the
sum by at most one: `∑_{k<n} f(σ^{k+1} 𝐢) ≤ ∑_{k<n} f(σ^k 𝐢) + 1` when `0 ≤ f ≤ 1`. -/
theorem birkhoffSum_shift_le {f : (ℤ → ι) → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (n : ℕ) (x : ℤ → ι) :
    birkhoffSum (shift 1) f n (shift 1 x) ≤ birkhoffSum (shift 1) f n x + 1 := by
  have h := birkhoffSum_succ_apply (shift 1) f n x
  rw [birkhoffSum_succ_apply'] at h
  linarith [hf0 x, hf1 ((shift 1)^[n] x)]

/-- The summed counting inequality in the proof of `thm:sigma_tau_omega_positive_eq_measure`:
for `𝐢 ∈ Σ'` and `n ∈ ℕ`, summing the counting inequality over `k ∈ {0, …, n-1}` counts each `k`
with `σ^k(𝐢) ∈ Σ^τ` at most twice, so
`#{k < n : σ^k 𝐢 ∈ ⋃_{j_0 > ℓ} [j_0]} ≤ 2 #{k < n : σ^k 𝐢 ∈ Σ^τ} + 1`, and the same for `Σ^ω`.
Depends on: `indicator_antiDiagSet_le`, `iterate_mem_SigmaPrime`. -/
theorem birkhoffSum_antiDiagSet_le (μ : Measure (ℤ → ι)) {x : ℤ → ι}
    (hx : x ∈ S.SigmaPrime μ) (n : ℕ) :
    birkhoffSum (shift 1) (S.antiDiagSet.indicator (1 : (ℤ → ι) → ℝ)) n x ≤
        2 * birkhoffSum (shift 1) ((S.SigmaTau μ).indicator 1) n x + 1 ∧
      birkhoffSum (shift 1) (S.antiDiagSet.indicator (1 : (ℤ → ι) → ℝ)) n x ≤
        2 * birkhoffSum (shift 1) ((S.SigmaOmega μ).indicator 1) n x + 1 := by
  have h0 : ∀ (E : Set (ℤ → ι)) (y : ℤ → ι), 0 ≤ E.indicator (1 : (ℤ → ι) → ℝ) y :=
    fun E y => indicator_nonneg (fun _ _ => zero_le_one) y
  have h1 : ∀ (E : Set (ℤ → ι)) (y : ℤ → ι), E.indicator (1 : (ℤ → ι) → ℝ) y ≤ 1 :=
    fun E y => indicator_le_self' (fun _ _ => zero_le_one) y
  -- The orbit of `σ(𝐢)` is the shifted orbit of `𝐢`.
  have hsh : ∀ (E : Set (ℤ → ι)),
      birkhoffSum (shift 1) (E.indicator (1 : (ℤ → ι) → ℝ)) n (shift 1 x) =
      ∑ k ∈ Finset.range n, E.indicator (1 : (ℤ → ι) → ℝ) (shift 1 ((shift 1)^[k] x)) :=
    fun E => Finset.sum_congr rfl fun k _ => by
      rw [← Function.iterate_succ_apply (shift 1) k x, Function.iterate_succ_apply']
  have key : ∀ (E : Set (ℤ → ι)),
      (∀ k : ℕ, S.antiDiagSet.indicator (1 : (ℤ → ι) → ℝ) ((shift 1)^[k] x) ≤
        E.indicator 1 ((shift 1)^[k] x) + E.indicator 1 (shift 1 ((shift 1)^[k] x))) →
      birkhoffSum (shift 1) (S.antiDiagSet.indicator (1 : (ℤ → ι) → ℝ)) n x ≤
        2 * birkhoffSum (shift 1) (E.indicator 1) n x + 1 := by
    intro E hE
    have hsum : birkhoffSum (shift 1) (S.antiDiagSet.indicator (1 : (ℤ → ι) → ℝ)) n x ≤
        birkhoffSum (shift 1) (E.indicator 1) n x +
          birkhoffSum (shift 1) (E.indicator 1) n (shift 1 x) := by
      rw [hsh E, birkhoffSum, birkhoffSum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun k _ => hE k
    linarith [birkhoffSum_shift_le (h0 E) (h1 E) n x]
  exact ⟨key _ fun k => (S.indicator_antiDiagSet_le μ (S.iterate_mem_SigmaPrime μ hx k)).1,
    key _ fun k => (S.indicator_antiDiagSet_le μ (S.iterate_mem_SigmaPrime μ hx k)).2⟩

end Counting

/-! ### Birkhoff's theorem and `thm:sigma_tau_omega_positive_eq_measure` -/

section Birkhoff

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {s : ℝ}

/-- Proof of `thm:sigma_tau_omega_positive_eq_measure`, Birkhoff's step: for an invariant ergodic
probability measure `μ`, Birkhoff's pointwise ergodic theorem gives
`μ(Σ^τ) = lim_n n⁻¹ #{k < n : σ^k 𝐢 ∈ Σ^τ}` and
`μ(⋃_{j_0 > ℓ} [j_0]) = lim_n n⁻¹ #{k < n : σ^k 𝐢 ∈ ⋃_{j_0 > ℓ} [j_0]}` for `μ`-almost every
`𝐢 ∈ Σ'`, and the summed counting inequality gives `μ(⋃_{j_0 > ℓ} [j_0]) ≤ 2 μ(Σ^τ)` in the
limit. The same holds for `Σ^ω`.
Depends on: `birkhoff_ergodic`, `measure_SigmaPrime_compl`, `birkhoffSum_antiDiagSet_le`. -/
theorem measureReal_antiDiagSet_le (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (herg : Ergodic (shift 1) μ) :
    μ.real S.antiDiagSet ≤ 2 * μ.real (S.SigmaTau μ) ∧
      μ.real S.antiDiagSet ≤ 2 * μ.real (S.SigmaOmega μ) := by
  have hU := S.measurableSet_antiDiagSet
  have hint : ∀ {E : Set (ℤ → ι)}, MeasurableSet E →
      Integrable (E.indicator (1 : (ℤ → ι) → ℝ)) μ :=
    fun hE => (integrable_const (1 : ℝ)).indicator hE
  have hB : ∀ {E : Set (ℤ → ι)}, MeasurableSet E → ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => birkhoffAverage ℝ (shift 1) (E.indicator (1 : (ℤ → ι) → ℝ)) n x) atTop
        (𝓝 (μ.real E)) := fun hE => by
    simpa only [integral_indicator_one hE] using birkhoff_ergodic herg (hint hE)
  -- The limit of the summed counting inequality at a typical point of `Σ'`.
  have hlim : ∀ {E : Set (ℤ → ι)}, MeasurableSet E →
      (∀ x ∈ S.SigmaPrime μ, ∀ n : ℕ,
        birkhoffSum (shift 1) (S.antiDiagSet.indicator (1 : (ℤ → ι) → ℝ)) n x ≤
          2 * birkhoffSum (shift 1) (E.indicator 1) n x + 1) →
      μ.real S.antiDiagSet ≤ 2 * μ.real E := by
    intro E hE hcount
    have hSig : ∀ᵐ x ∂μ, x ∈ S.SigmaPrime μ := S.measure_SigmaPrime_compl μ hinv herg
    obtain ⟨x, hxSig, hxU, hxE⟩ := (hSig.and ((hB hU).and (hB hE))).exists
    have hR : Tendsto (fun n : ℕ => 2 * birkhoffAverage ℝ (shift 1) (E.indicator 1) n x +
        (n : ℝ)⁻¹) atTop (𝓝 (2 * μ.real E + 0)) :=
      (hxE.const_mul 2).add tendsto_inv_atTop_nhds_zero_nat
    rw [add_zero] at hR
    refine le_of_tendsto_of_tendsto' hxU hR fun n => ?_
    have hc := hcount x hxSig n
    simp only [birkhoffAverage, smul_eq_mul]
    have hn : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.2 n.cast_nonneg
    calc (n : ℝ)⁻¹ * birkhoffSum (shift 1) (S.antiDiagSet.indicator 1) n x
        ≤ (n : ℝ)⁻¹ * (2 * birkhoffSum (shift 1) (E.indicator 1) n x + 1) :=
          mul_le_mul_of_nonneg_left hc hn
      _ = 2 * ((n : ℝ)⁻¹ * birkhoffSum (shift 1) (E.indicator 1) n x) + (n : ℝ)⁻¹ := by ring
  exact ⟨hlim (S.measurableSet_SigmaTau μ) fun x hx n => (S.birkhoffSum_antiDiagSet_le μ hx n).1,
    hlim (S.measurableSet_SigmaOmega μ) fun x hx n => (S.birkhoffSum_antiDiagSet_le μ hx n).2⟩

/-- `thm:sigma_tau_omega_positive_eq_measure`: `μ(Σ^τ) > 0` and `μ(Σ^ω) > 0` for the
ergodic `s`-equilibrium state, `0 < s < 2`, of a box-like tuple with rotations; proximality is
not used. The statement is that of `sigma_tau_omega_positive`. The counting inequality from
`eq:sigma_tau_omega_positive_eq_measure1` is summed along the orbit, Birkhoff's theorem gives
`μ(Σ^τ) ≥ ½ μ(⋃_{j_0 > ℓ} [j_0])` and `μ(Σ^ω) ≥ ½ μ(⋃_{j_0 > ℓ} [j_0])`, and
`μ(⋃_{j_0 > ℓ} [j_0]) > 0` because the equilibrium state is fully supported. The ergodicity `herg`
comes from `thm:irred_eq_state`; full support from its Gibbs bounds
(`EquilibriumGibbsStatement`, which the library proves).
Depends on: `measureReal_antiDiagSet_le`, `HasGibbsBounds.measure_cylinder_pos`. -/
theorem sigma_tau_omega_positive_eq_measure (hfk : EquilibriumGibbsStatement.{u})
    (hrot : S.WithRotations) (hs0 : 0 < s) (hs2 : s < 2)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (herg : Ergodic (shift 1) μ) (heq : S.IsEquilibriumState s μ) :
    0 < μ (S.SigmaTau μ) ∧ 0 < μ (S.SigmaOmega μ) := by
  obtain ⟨i, hi⟩ := hrot.2
  -- Full support: the anti-diagonal cylinder `[i]` has positive mass.
  have hcyl := (hfk S hrot hs0 hs2 μ hinv heq).measure_cylinder_pos i
  have hUpos : 0 < μ.real S.antiDiagSet := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hcyl.trans_le (measure_mono (S.cylinder_subset_antiDiagSet hi))).ne'
      (measure_ne_top μ _)
  obtain ⟨hτ, hω⟩ := S.measureReal_antiDiagSet_le μ hinv herg
  have hpos : ∀ E : Set (ℤ → ι), 0 < 2 * μ.real E → 0 < μ E := fun E h => by
    rw [measureReal_def] at h
    exact (ENNReal.toReal_pos_iff.1 (pos_of_mul_pos_right h zero_le_two)).1
  exact ⟨hpos _ (hUpos.trans_le hτ), hpos _ (hUpos.trans_le hω)⟩

end Birkhoff


end System

end BoxLike
