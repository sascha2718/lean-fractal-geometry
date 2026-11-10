module

/-
Multiscale entropy of planar measures along the non-conformal partitions `ℰ_n`, for the proof
of Rapaport's theorem (arXiv:2309.03985v1): Lemma 2.1 of the source (lines 815 to 823), the
entropy of a measure as an average of the local entropies of its components, with the
increment, monotonicity and counting bounds behind it and the scaling of components by
`A_χ^i` ((2.6), lines 760 to 763).

* The constant `Exps.c₀ = log 4 + χ₁ + χ₂`: `Exps.c₀_pos`; `log_natCast_le_log_of_le`.
* Components: the instance `isZeroOrProbabilityMeasure_comp`, `cavg_div`.
* Increments: `cent_E_add_le`, `cent_E_succ_le`, `ent_E_mono`, `ent_E_sub_eq_cent`,
  `ent_E_sub_le`.
* Counting bounds: `ent_E_le`, `ent_E_zero_le`, `ent_E_le_of_inBall_one`,
  `ent_E_le_two_log_four_add`, `ent_E_div_le_of_inBall_one`, `ent_E_div_le_const`.
* Lemma 2.1: `sum_cent_E_eq`, `abs_ent_E_div_sub_avg_le`, `ent_E_div_le_avg_add`,
  `avg_le_ent_E_div_add`.
* Components and scaling: `cent_E_eq_cavg`, `abs_ent_E_add_sub_ent_map_resc_le`,
  `ent_comp_E_resc`, `ent_comp_E_le_ent_map_resc_add`, `exists_inBall_map_resc_comp`.
-/
public import BoxLike.Rapaport.Entropy.Basic
public import BoxLike.Rapaport.Entropy.Rect

@[expose] public section

namespace BoxLike.Rapaport

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The constant `c₀ = log 4 + χ₁ + χ₂`: a cell of `ℰ_n` meets at most `e^{c₀}` cells of
`ℰ_{n+1}`, so that `H(θ, ℰ_{n+m} ∣ ℰ_n) ≤ c₀ m` (the `O(m)` of Lemma 2.1 of the source, lines
815 to 823). -/
noncomputable def Exps.c₀ (χ : Exps) : ℝ := Real.log 4 + χ.χ₁ + χ.χ₂

/-- The constant `c₀` is positive. -/
theorem Exps.c₀_pos (χ : Exps) : 0 < χ.c₀ := by
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have := χ.pos
  have := χ.pos₂
  unfold Exps.c₀
  linarith

/-- `log N ≤ log x` for a natural number `N ≤ x` and `x ≥ 1`, including `N = 0`. -/
theorem log_natCast_le_log_of_le {N : ℕ} {x : ℝ} (hx : 1 ≤ x) (h : (N : ℝ) ≤ x) :
    Real.log N ≤ Real.log x := by
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_nonneg hx
  · exact Real.log_le_log (by exact_mod_cast hpos) h

/-- A component `θ_{f = b}` is a probability measure or the zero measure. -/
instance isZeroOrProbabilityMeasure_comp {X L : Type*} [MeasurableSpace X] (θ : Measure X)
    (f : X → L) (b : L) : IsZeroOrProbabilityMeasure (comp θ f b) :=
  inferInstanceAs (IsZeroOrProbabilityMeasure (θ[|f ⁻¹' {b}]))

/-- The component average commutes with division by a constant. -/
theorem cavg_div {X L : Type*} [MeasurableSpace X] {θ : Measure X} {f : X → L}
    (hfin : FiniteLabels θ f) (F : Measure X → ℝ) (a : ℝ) :
    cavg θ f (fun ρ => F ρ / a) = cavg θ f F / a := by
  simp only [cavg_eq_sum hfin, Finset.sum_div, mul_div_assoc]

section Multiscale

variable (χ : Exps) {θ : Measure (ℝ × ℝ)}

/-! ### Increments of the entropy along `ℰ_n` -/

/-- The conditional entropy of `ℰ_{n+m}` given `ℰ_n` is at most `log 4 + (χ₁ + χ₂) m` for
`m ≥ 0`: every cell of `ℰ_n` meets at most `4 e^{(χ₁+χ₂) m}` cells of `ℰ_{n+m}` (Section 2.5 of
the source, used in the proof of Lemma 2.1, lines 815 to 823). -/
theorem cent_E_add_le [IsProbabilityMeasure θ] (hθ : BddSupp θ) (n : ℤ) {m : ℤ} (hm : 0 ≤ m) :
    cent θ (χ.E (n + m)) (χ.E n) ≤ Real.log 4 + (χ.χ₁ + χ.χ₂) * m := by
  have hfb := χ.fiberBound_E_E (n := n) (m := n + m) (by linarith)
  refine (cent_le_log_of_fiber_card (χ.measurable_E _) (χ.measurable_E _)
    (hθ.finiteLabels_E χ _) (hθ.finiteLabels_E χ _) hfb).trans ?_
  have he : ((n + m : ℤ) : ℝ) - n = m := by push_cast; ring
  rw [he]
  have hm' : (0 : ℝ) ≤ m := Int.cast_nonneg hm
  have hexp : 1 ≤ Real.exp ((χ.χ₁ + χ.χ₂) * m) :=
    Real.one_le_exp (mul_nonneg (by linarith [χ.pos, χ.pos₂]) hm')
  refine (log_natCast_le_log_of_le (by linarith) (Nat.floor_le (by positivity))).trans_eq ?_
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]

/-- One level of refinement: `H(θ, ℰ_{n+1} ∣ ℰ_n) ≤ c₀` (Section 2.5 of the source). -/
theorem cent_E_succ_le [IsProbabilityMeasure θ] (hθ : BddSupp θ) (n : ℤ) :
    cent θ (χ.E (n + 1)) (χ.E n) ≤ χ.c₀ := by
  have h := cent_E_add_le χ hθ n (m := 1) zero_le_one
  rw [Int.cast_one, mul_one] at h
  unfold Exps.c₀
  linarith

/-- The entropy of `ℰ_n` increases with `n`, since `ℰ_m` refines `ℰ_n` for `n ≤ m` (Rapaport,
lines 705 to 712). -/
theorem ent_E_mono [IsProbabilityMeasure θ] (hθ : BddSupp θ) {n m : ℤ} (hnm : n ≤ m) :
    ent θ (χ.E n) ≤ ent θ (χ.E m) := by
  obtain ⟨φ, hφ⟩ := χ.E_factor hnm
  exact ent_le_of_factor (χ.measurable_E m) (hθ.finiteLabels_E χ m) φ hφ

/-- The chain rule (2.3) for the refinement `ℰ_{n+m}` of `ℰ_n`, `m ≥ 0`:
`H(θ, ℰ_{n+m}) - H(θ, ℰ_n) = H(θ, ℰ_{n+m} ∣ ℰ_n)`. -/
theorem ent_E_sub_eq_cent (n : ℤ) {m : ℤ} (hm : 0 ≤ m) :
    ent θ (χ.E (n + m)) - ent θ (χ.E n) = cent θ (χ.E (n + m)) (χ.E n) := by
  obtain ⟨φ, hφ⟩ := χ.E_factor (show n ≤ n + m by linarith)
  have h : ent θ (fun x => (χ.E (n + m) x, χ.E n x)) = ent θ (χ.E (n + m)) := by
    refine ent_eq_of_injective (φ := fun b => (b, φ b)) (fun _ _ h => (Prod.mk.inj h).1) ?_
    funext x
    simp [hφ]
  unfold cent
  rw [h]

/-- The entropy of `ℰ_n` grows by at most `c₀ m` over `m ≥ 0` levels. -/
theorem ent_E_sub_le [IsProbabilityMeasure θ] (hθ : BddSupp θ) (n : ℤ) {m : ℤ} (hm : 0 ≤ m) :
    ent θ (χ.E (n + m)) - ent θ (χ.E n) ≤ χ.c₀ * m := by
  rw [ent_E_sub_eq_cent χ n hm]
  rcases hm.eq_or_lt with h0 | h1
  · subst h0
    rw [add_zero, cent_self, Int.cast_zero, mul_zero]
  · have h := cent_E_add_le χ hθ n hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h1
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have : Real.log 4 ≤ Real.log 4 * m := le_mul_of_one_le_right h4 hm1
    unfold Exps.c₀
    nlinarith

/-! ### Counting bounds -/

/-- A measure carried by a ball of radius `R` meets at most `(2 e^{χ₂ n} R + 2)^2` cells of
`ℰ_n`, `n ≥ 0`, so `H(θ, ℰ_n) ≤ 2 log (2 e^{χ₂ n} R + 2)` (Rapaport (2.1), line 680). -/
theorem ent_E_le [IsZeroOrProbabilityMeasure θ] {c : ℝ × ℝ} {R : ℝ} (hθ : InBall θ c R)
    (hR : 0 ≤ R) {n : ℤ} (hn : 0 ≤ n) :
    ent θ (χ.E n) ≤ 2 * Real.log (Real.exp (χ.χ₂ * n) * (2 * R) + 2) := by
  set y := Real.exp (χ.χ₂ * n) * (2 * R) + 2 with hy
  have hy2 : 2 ≤ y := by
    have : 0 ≤ Real.exp (χ.χ₂ * n) * (2 * R) := by positivity
    linarith
  have hlog : 0 ≤ 2 * Real.log y := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ y)
    linarith
  rcases eq_zero_or_isProbabilityMeasure θ with rfl | _
  · rw [ent_zero]
    exact hlog
  obtain ⟨s, hs, hcard⟩ := χ.exists_finset_E_image_closedBall n c hR
  have hae : ∀ᵐ z ∂θ, χ.E n z ∈ s :=
    hθ.ae_mem_closedBall.mono fun z hz => hs ⟨z, hz, rfl⟩
  refine (ent_le_log_of_ae_mem (χ.measurable_E n) s hae).trans ?_
  have h₁ : Real.exp (χ.χ₁ * n) ≤ Real.exp (χ.χ₂ * n) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right χ.lt.le (Int.cast_nonneg hn))
  have hx : 0 ≤ Real.exp (χ.χ₁ * n) * (2 * R) + 2 := by positivity
  have hxy : Real.exp (χ.χ₁ * n) * (2 * R) + 2 ≤ y :=
    add_le_add_left (mul_le_mul_of_nonneg_right h₁ (by linarith)) 2
  have hcard' : (s.card : ℝ) ≤ y ^ 2 := by
    refine hcard.trans ?_
    rw [sq]
    exact mul_le_mul hxy le_rfl (by linarith) (by linarith)
  have hpow := Real.log_pow y 2
  push_cast at hpow
  rw [← hpow]
  exact log_natCast_le_log_of_le (by nlinarith) hcard'

/-- A measure carried by a ball of radius `R` has `H(θ, ℰ_0) ≤ 2 log (2R + 2)`: the bound on
`H(θ, ℰ_0)` in terms of the diameter in Lemma 2.1 of the source (lines 815 to 823). -/
theorem ent_E_zero_le [IsZeroOrProbabilityMeasure θ] {c : ℝ × ℝ} {R : ℝ} (hθ : InBall θ c R)
    (hR : 0 ≤ R) : ent θ (χ.E 0) ≤ 2 * Real.log (2 * R + 2) := by
  simpa using ent_E_le χ hθ hR le_rfl

/-- A measure carried by a ball of radius `1`, such as a rescaled component `A_χ^i θ_{x,i}`, has
`H(ρ, ℰ_m) ≤ 2 log (2 e^{χ₂ m} + 2)` for `m ≥ 0`. -/
theorem ent_E_le_of_inBall_one {ρ : Measure (ℝ × ℝ)} [IsZeroOrProbabilityMeasure ρ]
    {z : ℝ × ℝ} (h : InBall ρ z 1) {m : ℤ} (hm : 0 ≤ m) :
    ent ρ (χ.E m) ≤ 2 * Real.log (2 * Real.exp (χ.χ₂ * m) + 2) := by
  have := ent_E_le χ h zero_le_one hm
  rwa [mul_one, mul_comm (Real.exp _) 2] at this

/-- The linear form of `ent_E_le_of_inBall_one`: `H(ρ, ℰ_m) ≤ 2 log 4 + 2 χ₂ m`. -/
theorem ent_E_le_two_log_four_add {ρ : Measure (ℝ × ℝ)} [IsZeroOrProbabilityMeasure ρ]
    {z : ℝ × ℝ} (h : InBall ρ z 1) {m : ℤ} (hm : 0 ≤ m) :
    ent ρ (χ.E m) ≤ 2 * Real.log 4 + 2 * χ.χ₂ * m := by
  refine (ent_E_le_of_inBall_one χ h hm).trans ?_
  have he : 1 ≤ Real.exp (χ.χ₂ * m) :=
    Real.one_le_exp (mul_nonneg χ.pos₂.le (Int.cast_nonneg hm))
  have hle : Real.log (2 * Real.exp (χ.χ₂ * m) + 2) ≤ Real.log (4 * Real.exp (χ.χ₂ * m)) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at hle
  linarith

/-- The normalised entropy of a measure carried by a ball of radius `1` at level `m ≥ 1`:
`H(ρ, ℰ_m) / m ≤ 2 χ₂ + 2 log 4 / m`, the bound `O(1)` in the proof of Lemma 3.6 of the source
(lines 1061 to 1064). -/
theorem ent_E_div_le_of_inBall_one {ρ : Measure (ℝ × ℝ)} [IsZeroOrProbabilityMeasure ρ]
    {z : ℝ × ℝ} (h : InBall ρ z 1) {m : ℕ} (hm : 1 ≤ m) :
    ent ρ (χ.E m) / m ≤ 2 * χ.χ₂ + 2 * Real.log 4 / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have := ent_E_le_two_log_four_add χ h (m := m) (Int.natCast_nonneg m)
  rw [Int.cast_natCast] at this
  rw [div_le_iff₀ hm', add_mul, div_mul_cancel₀ _ hm'.ne']
  linarith

/-- The uniform form of `ent_E_div_le_of_inBall_one`: `H(ρ, ℰ_m) / m ≤ 2 χ₂ + 2 log 4` for every
`m ≥ 1`. -/
theorem ent_E_div_le_const {ρ : Measure (ℝ × ℝ)} [IsZeroOrProbabilityMeasure ρ]
    {z : ℝ × ℝ} (h : InBall ρ z 1) {m : ℕ} (hm : 1 ≤ m) :
    ent ρ (χ.E m) / m ≤ 2 * χ.χ₂ + 2 * Real.log 4 := by
  refine (ent_E_div_le_of_inBall_one χ h hm).trans ?_
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h4 : 0 ≤ 2 * Real.log 4 := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
  have : 2 * Real.log 4 / m ≤ 2 * Real.log 4 := div_le_self h4 hm1
  linarith

/-! ### Lemma 2.1: entropy as an average of local entropies -/

/-- The telescoping identity behind Lemma 2.1 of the source (lines 815 to 823):
`∑_{i=1}^{n} H(θ, ℰ_{i+m} ∣ ℰ_i) = ∑_{k=0}^{m-1} (H(θ, ℰ_{n+1+k}) - H(θ, ℰ_{1+k}))`. -/
theorem sum_cent_E_eq (n m : ℕ) :
    ∑ i ∈ Finset.range n, cent θ (χ.E ((i + 1 : ℕ) + m)) (χ.E (i + 1 : ℕ)) =
      ∑ k ∈ Finset.range m, (ent θ (χ.E (n + 1 + k : ℕ)) - ent θ (χ.E (1 + k : ℕ))) := by
  set a : ℕ → ℝ := fun j => ent θ (χ.E j) with ha
  have hc : ∀ i : ℕ, cent θ (χ.E ((i + 1 : ℕ) + m)) (χ.E (i + 1 : ℕ)) =
      a (i + 1 + m) - a (i + 1) := by
    intro i
    rw [← ent_E_sub_eq_cent χ _ (Int.natCast_nonneg m)]
    simp only [ha]
    push_cast
    rfl
  have h1 : ∀ i : ℕ, a (i + 1 + m) - a (i + 1) =
      ∑ k ∈ Finset.range m, (a (i + k + 2) - a (i + k + 1)) := by
    intro i
    have := Finset.sum_range_sub (fun k => a (i + 1 + k)) m
    simp only [add_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show i + 1 + (k + 1) = i + k + 2 by omega, show i + 1 + k = i + k + 1 by omega]
  have h2 : ∀ k : ℕ, a (n + 1 + k) - a (1 + k) =
      ∑ i ∈ Finset.range n, (a (i + k + 2) - a (i + k + 1)) := by
    intro k
    have := Finset.sum_range_sub (fun i => a (i + 1 + k)) n
    simp only [zero_add] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show i + 1 + 1 + k = i + k + 2 by omega, show i + 1 + k = i + k + 1 by omega]
  rw [Finset.sum_congr rfl fun i _ => (hc i).trans (h1 i), Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => (h2 k).symm

/-- Lemma 2.1 of the source (lines 815 to 823), Hochman's Lemma 3.4: for `m ≥ 1` and every `n`,
`|H(θ, ℰ_n) / n - 𝔼_{1 ≤ i ≤ n} (H(θ, ℰ_{i+m} ∣ ℰ_i) / m)| ≤ (c₀ m + H(θ, ℰ_0)) / n`; with
`ent_E_zero_le` the error is `O((m + log R) / n)` for `θ` carried by a ball of radius `R`. -/
theorem abs_ent_E_div_sub_avg_le [IsProbabilityMeasure θ] (hθ : BddSupp θ) (n : ℕ) {m : ℕ}
    (hm : 1 ≤ m) :
    |ent θ (χ.E n) / n -
        (∑ i ∈ Finset.range n, cent θ (χ.E ((i + 1 : ℕ) + m)) (χ.E (i + 1 : ℕ)) / m) / n| ≤
      (χ.c₀ * m + ent θ (χ.E 0)) / n := by
  set a : ℕ → ℝ := fun j => ent θ (χ.E j) with ha
  have hc0 := χ.c₀_pos
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hup : ∀ j k : ℕ, k + 1 ≤ m → a (j + 1 + k) ≤ a j + χ.c₀ * m := by
    intro j k hk
    have h := ent_E_sub_le χ hθ j (m := (1 + k : ℕ)) (Int.natCast_nonneg _)
    have e : ((j : ℤ) + ((1 + k : ℕ) : ℤ)) = ((j + 1 + k : ℕ) : ℤ) := by push_cast; ring
    rw [e] at h
    have hk' : ((1 + k : ℕ) : ℝ) ≤ m := by exact_mod_cast (by omega : 1 + k ≤ m)
    have : χ.c₀ * ((1 + k : ℕ) : ℤ) ≤ χ.c₀ * m := by
      rw [Int.cast_natCast]
      exact mul_le_mul_of_nonneg_left hk' hc0.le
    simp only [ha]
    linarith
  have hlow : ∀ j k : ℕ, a j ≤ a (j + 1 + k) := fun j k =>
    ent_E_mono χ hθ (by exact_mod_cast (by omega : j ≤ j + 1 + k))
  have hnn : ∀ j, 0 ≤ a j := fun j => ent_nonneg _
  set S := ∑ k ∈ Finset.range m, (a (n + 1 + k) - a (1 + k)) with hS
  have hsum : ∑ i ∈ Finset.range n, cent θ (χ.E ((i + 1 : ℕ) + m)) (χ.E (i + 1 : ℕ)) / m =
      S / m := by
    rw [← Finset.sum_div, sum_cent_E_eq χ n m]
  have hSup : S ≤ m * (a n + χ.c₀ * m) := by
    have := Finset.sum_le_card_nsmul (Finset.range m) (fun k => a (n + 1 + k) - a (1 + k))
      (a n + χ.c₀ * m) fun k hk => by
        have h1 := hup n k (Finset.mem_range.1 hk)
        have h2 := hnn (1 + k)
        linarith
    rwa [Finset.card_range, nsmul_eq_mul] at this
  have hSlow : m * (a n - a 0 - χ.c₀ * m) ≤ S := by
    have := Finset.card_nsmul_le_sum (Finset.range m) (fun k => a (n + 1 + k) - a (1 + k))
      (a n - a 0 - χ.c₀ * m) fun k hk => by
        have h1 := hlow n k
        have h2 := hup 0 k (Finset.mem_range.1 hk)
        rw [zero_add] at h2
        linarith
    rwa [Finset.card_range, nsmul_eq_mul] at this
  have hS1 : S / m ≤ a n + χ.c₀ * m := by
    rw [div_le_iff₀ hm']
    linarith
  have hS2 : a n - a 0 - χ.c₀ * m ≤ S / m := by
    rw [le_div_iff₀ hm']
    linarith
  rw [hsum, ← sub_div, abs_div, Nat.abs_cast]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n)
  rw [abs_le]
  have := hnn 0
  change -(χ.c₀ * m + a 0) ≤ a n - S / m ∧ a n - S / m ≤ χ.c₀ * m + a 0
  constructor <;> linarith

/-- One half of Lemma 2.1 of the source (lines 815 to 823): the normalised entropy is at most the
average local entropy plus `(c₀ m + H(θ, ℰ_0)) / n`. -/
theorem ent_E_div_le_avg_add [IsProbabilityMeasure θ] (hθ : BddSupp θ) (n : ℕ) {m : ℕ}
    (hm : 1 ≤ m) :
    ent θ (χ.E n) / n ≤
      (∑ i ∈ Finset.range n, cent θ (χ.E ((i + 1 : ℕ) + m)) (χ.E (i + 1 : ℕ)) / m) / n +
        (χ.c₀ * m + ent θ (χ.E 0)) / n := by
  have := (abs_le.1 (abs_ent_E_div_sub_avg_le χ hθ n hm)).2
  linarith

/-- The other half of Lemma 2.1 of the source (lines 815 to 823): the average local entropy is at
most the normalised entropy plus `(c₀ m + H(θ, ℰ_0)) / n`. -/
theorem avg_le_ent_E_div_add [IsProbabilityMeasure θ] (hθ : BddSupp θ) (n : ℕ) {m : ℕ}
    (hm : 1 ≤ m) :
    (∑ i ∈ Finset.range n, cent θ (χ.E ((i + 1 : ℕ) + m)) (χ.E (i + 1 : ℕ)) / m) / n ≤
      ent θ (χ.E n) / n + (χ.c₀ * m + ent θ (χ.E 0)) / n := by
  have := (abs_le.1 (abs_ent_E_div_sub_avg_le χ hθ n hm)).1
  linarith

/-! ### Components and scaling -/

/-- The local entropy average of the source (line 809): `H(θ, ℰ_{i+m} ∣ ℰ_i)` is the average of
`H(θ_{x,i}, ℰ_{i+m})` over the components of `θ` at level `i`. -/
theorem cent_E_eq_cavg [IsProbabilityMeasure θ] (hθ : BddSupp θ) (i m : ℤ) :
    cent θ (χ.E (i + m)) (χ.E i) = cavg θ (χ.E i) (fun ρ => ent ρ (χ.E (i + m))) :=
  cent_eq_cavg (χ.measurable_E _) (χ.measurable_E _) (hθ.finiteLabels_E χ _)
    (hθ.finiteLabels_E χ _)

/-- Scaling (2.6) of the source (lines 760 to 763) for entropy: for a measure `ρ` of bounded
support, `|H(ρ, ℰ_{i+m}) - H(A_χ^i ρ, ℰ_m)| ≤ log 9`. -/
theorem abs_ent_E_add_sub_ent_map_resc_le (ρ : Measure (ℝ × ℝ)) [IsZeroOrProbabilityMeasure ρ]
    (hρ : BddSupp ρ) (i m : ℤ) :
    |ent ρ (χ.E (i + m)) - ent (ρ.map (χ.resc i)) (χ.E m)| ≤ Real.log 9 := by
  rcases eq_zero_or_isProbabilityMeasure ρ with rfl | _
  · rw [Measure.map_zero, ent_zero, ent_zero, sub_self, abs_zero]
    exact Real.log_nonneg (by norm_num)
  rw [ent_map (χ.measurable_resc i) (χ.measurable_E m)]
  have hbd : BddSupp (ρ.map (χ.resc i)) := hρ.map_diagMap _ _
  have hfin : FiniteLabels ρ (χ.E m ∘ χ.resc i) :=
    (finiteLabels_map_iff (χ.measurable_resc i) (χ.measurable_E m)).1 (hbd.finiteLabels_E χ m)
  have h := abs_ent_sub_ent_le_log_of_commensurable (χ.measurable_E (i + m))
    ((χ.measurable_E m).comp (χ.measurable_resc i)) (hρ.finiteLabels_E χ _) hfin
    (χ.fiberBound_E_resc i m) (χ.fiberBound_E_resc_symm i m)
  simpa using h

/-- Scaling (2.6) of the source for the components at level `i`:
`|H(θ_{x,i}, ℰ_{i+m}) - H(A_χ^i θ_{x,i}, ℰ_m)| ≤ log 9` (lines 760 to 763, used in the proof of
Lemma 3.6, line 1057). Null components are zero measures and satisfy it trivially. -/
theorem ent_comp_E_resc (hθ : BddSupp θ) (i m : ℤ) (b : ℤ × ℤ) :
    |ent (comp θ (χ.E i) b) (χ.E (i + m)) - ent ((comp θ (χ.E i) b).map (χ.resc i)) (χ.E m)| ≤
      Real.log 9 :=
  abs_ent_E_add_sub_ent_map_resc_le χ _ (hθ.cond _) i m

/-- The one-sided form of `ent_comp_E_resc` used in the proof of Lemma 3.6 of the source:
`H(θ_{x,i}, ℰ_{i+m}) ≤ H(A_χ^i θ_{x,i}, ℰ_m) + log 9`. -/
theorem ent_comp_E_le_ent_map_resc_add (hθ : BddSupp θ) (i m : ℤ) (b : ℤ × ℤ) :
    ent (comp θ (χ.E i) b) (χ.E (i + m)) ≤
      ent ((comp θ (χ.E i) b).map (χ.resc i)) (χ.E m) + Real.log 9 := by
  have := (abs_le.1 (ent_comp_E_resc χ hθ i m b)).2
  linarith

/-- A component at level `i`, rescaled by `A_χ^i`, is carried by a ball of radius `1` (Rect's
`Exps.inBall_map_resc_comp`, the normalisation behind (2.6) of the source, lines 760 to 763). -/
theorem exists_inBall_map_resc_comp (θ : Measure (ℝ × ℝ)) (i : ℤ) (b : ℤ × ℤ) :
    ∃ z, InBall ((comp θ (χ.E i) b).map (χ.resc i)) z 1 :=
  ⟨_, χ.inBall_map_resc_comp θ i b⟩

end Multiscale

end BoxLike.Rapaport
