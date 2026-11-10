module

/-
Small coordinate variances force small entropy, and positive entropy forces many levels whose
rescaled components have a coordinate variance bounded below: Lemmas 3.5 and 3.6 of Rapaport
(arXiv:2309.03985v1, lines 1023 to 1073 of the source; Hochman's Lemma 4.4 and its consequence)
for `d = 2`.

* Chebyshev for planar measures: `memLp_fst_of_inBall`, `memLp_snd_of_inBall`,
  `measureReal_abs_sub_integral_ge_le`, `compl_closedBall_subset`,
  `measureReal_compl_closedBall_mean_le`.
* Lemma 3.5: `ent_E_div_lt_of_var_le`.
* Lemma 3.6: `exists_many_levels_var_gt`.
-/
public import BoxLike.Rapaport.Entropy.Multiscale

@[expose] public section

namespace BoxLike.Rapaport

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ### Chebyshev's inequality for planar measures -/

section Chebyshev

variable {θ : Measure (ℝ × ℝ)} {c : ℝ × ℝ} {R : ℝ}

/-- A coordinate is bounded on a ball: `‖z.1‖ ≤ ‖c‖ + R` for `‖z - c‖ ≤ R`. -/
private theorem norm_fst_le_of_norm_sub_le {z : ℝ × ℝ} (h : ‖z - c‖ ≤ R) : ‖z.1‖ ≤ ‖c‖ + R := by
  have := norm_sub_norm_le z c
  have := norm_fst_le z
  linarith

/-- A coordinate is bounded on a ball: `‖z.2‖ ≤ ‖c‖ + R` for `‖z - c‖ ≤ R`. -/
private theorem norm_snd_le_of_norm_sub_le {z : ℝ × ℝ} (h : ‖z - c‖ ≤ R) : ‖z.2‖ ≤ ‖c‖ + R := by
  have := norm_sub_norm_le z c
  have := norm_snd_le z
  linarith

/-- The first coordinate of a finite measure carried by a ball is square integrable. -/
theorem memLp_fst_of_inBall [IsFiniteMeasure θ] (h : InBall θ c R) :
    MemLp (fun z : ℝ × ℝ => z.1) 2 θ :=
  MemLp.of_bound measurable_fst.aestronglyMeasurable (‖c‖ + R)
    (Filter.Eventually.mono h fun _ hz => norm_fst_le_of_norm_sub_le hz)

/-- The second coordinate of a finite measure carried by a ball is square integrable. -/
theorem memLp_snd_of_inBall [IsFiniteMeasure θ] (h : InBall θ c R) :
    MemLp (fun z : ℝ × ℝ => z.2) 2 θ :=
  MemLp.of_bound measurable_snd.aestronglyMeasurable (‖c‖ + R)
    (Filter.Eventually.mono h fun _ hz => norm_snd_le_of_norm_sub_le hz)

/-- Chebyshev's inequality in real form: `θ {|X - 𝔼 X| ≥ r} ≤ Var X / r²`. -/
theorem measureReal_abs_sub_integral_ge_le [IsFiniteMeasure θ] {X : ℝ × ℝ → ℝ}
    (hX : MemLp X 2 θ) {r : ℝ} (hr : 0 < r) :
    θ.real {z | r ≤ |X z - ∫ w, X w ∂θ|} ≤ variance X θ / r ^ 2 :=
  ENNReal.toReal_le_of_le_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))
    (meas_ge_le_variance_div_sq hX hr)

/-- The complement of the sup-norm ball of radius `r` about `w` lies in the union of the two
coordinate strips `{r ≤ |z.1 - w.1|}` and `{r ≤ |z.2 - w.2|}`. -/
theorem compl_closedBall_subset (w : ℝ × ℝ) (r : ℝ) :
    (Metric.closedBall w r)ᶜ ⊆ {z | r ≤ |z.1 - w.1|} ∪ {z | r ≤ |z.2 - w.2|} := by
  intro z hz
  rw [Set.mem_compl_iff, Metric.mem_closedBall, not_le, Prod.dist_eq, lt_max_iff,
    Real.dist_eq, Real.dist_eq] at hz
  rcases hz with h | h
  · exact Or.inl (le_of_lt h)
  · exact Or.inr (le_of_lt h)

/-- Chebyshev's inequality in both coordinates: a planar probability measure carried by a ball
gives mass at most `(Var π₁ θ + Var π₂ θ) / r²` to the complement of the sup-norm ball of radius
`r > 0` about its mean (the first step in the proof of Lemma 3.5 of the source, Hochman's Lemma
4.4). -/
theorem measureReal_compl_closedBall_mean_le [IsProbabilityMeasure θ] (h : InBall θ c R)
    {r : ℝ} (hr : 0 < r) :
    θ.real (Metric.closedBall (∫ z, z.1 ∂θ, ∫ z, z.2 ∂θ) r)ᶜ ≤ (var₁ θ + var₂ θ) / r ^ 2 := by
  refine (measureReal_mono (compl_closedBall_subset _ r)).trans ?_
  refine (measureReal_union_le _ _).trans ?_
  rw [add_div]
  exact add_le_add (measureReal_abs_sub_integral_ge_le (memLp_fst_of_inBall h) hr)
    (measureReal_abs_sub_integral_ge_le (memLp_snd_of_inBall h) hr)

end Chebyshev

/-! ### Lemma 3.5: small variances give small entropy -/

section Variance

variable (χ : Exps)

/-- Lemma 3.5 of the source (lines 1023 to 1032), Hochman's Lemma 4.4, for `d = 2`: for every
`ε > 0` and `m ≥ M(ε)` there is `δ > 0` such that every planar probability measure carried by a
ball of radius `ε⁻¹` with `Var(π₁ θ) ≤ δ` and `Var(π₂ θ) ≤ δ` has `H(θ, ℰ_m) / m < ε`. The
source asks for `0 < ε < 1` and a support of diameter at most `ε⁻¹`; a ball of radius `ε⁻¹`
contains every such support. -/
theorem ent_E_div_lt_of_var_le :
    ∀ ε > 0, ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ∃ δ > 0,
      ∀ (θ : Measure (ℝ × ℝ)) [IsProbabilityMeasure θ] (c : ℝ × ℝ),
        InBall θ c ε⁻¹ → var₁ θ ≤ δ → var₂ θ ≤ δ → ent θ (χ.E m) / m < ε := by
  intro ε hε
  refine ⟨⌈(4 * Real.log 4 + 2 * Real.log 2) / ε⌉₊ + 1, fun m hm => ?_⟩
  have hmpos : (0 : ℝ) < m := by
    have : 1 ≤ m := le_trans (Nat.le_add_left 1 _) hm
    exact_mod_cast this
  have hmM : 4 * Real.log 4 + 2 * Real.log 2 < ε * m := by
    have h1 := Nat.le_ceil ((4 * Real.log 4 + 2 * Real.log 2) / ε)
    have h2 : ((⌈(4 * Real.log 4 + 2 * Real.log 2) / ε⌉₊ + 1 : ℕ) : ℝ) ≤ m := by
      exact_mod_cast hm
    push_cast at h2
    have h3 : (4 * Real.log 4 + 2 * Real.log 2) / ε < m := by linarith
    rw [div_lt_iff₀ hε] at h3
    linarith
  set K := 2 * Real.log (Real.exp (χ.χ₂ * ((m : ℤ) : ℝ)) * (2 * ε⁻¹) + 2) with hK
  have hK0 : 0 ≤ K := by
    have : 1 ≤ Real.exp (χ.χ₂ * ((m : ℤ) : ℝ)) * (2 * ε⁻¹) + 2 := by
      have : 0 ≤ Real.exp (χ.χ₂ * ((m : ℤ) : ℝ)) * (2 * ε⁻¹) := by positivity
      linarith
    have := Real.log_nonneg this
    linarith
  set Ex := Real.exp (2 * χ.χ₂ * m) with hEx
  set D := 2 * Ex * (K + 1) with hD
  have hDpos : 0 < D := by positivity
  set δ := ε * m / (4 * D) with hδ
  refine ⟨δ, by positivity, fun θ _ c hθ hv₁ hv₂ => ?_⟩
  set r := Real.exp (-(χ.χ₂ * m)) with hr
  have hrpos : 0 < r := Real.exp_pos _
  set w : ℝ × ℝ := (∫ z, z.1 ∂θ, ∫ z, z.2 ∂θ) with hw
  set B := Metric.closedBall w r with hBdef
  have hB : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hbd : BddSupp θ := ⟨c, _, hθ⟩
  have htwo := ent_le_two_pieces (χ.measurable_E m) (hbd.finiteLabels_E χ m) hB
  -- the piece inside the small ball meets at most `16` cells
  have hin : InBall (θ[|B]) w r := Filter.Eventually.mono (ae_cond_mem hB) fun z hz => by
    rwa [hBdef, Metric.mem_closedBall, dist_eq_norm] at hz
  have hent_in : ent (θ[|B]) (χ.E m) ≤ 2 * Real.log 4 := by
    have h := ent_E_le χ hin hrpos.le (n := m) (Int.natCast_nonneg m)
    have e : Real.exp (χ.χ₂ * ((m : ℤ) : ℝ)) * (2 * r) + 2 = 4 := by
      rw [Int.cast_natCast, hr, mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
      norm_num
    rwa [e] at h
  -- the piece outside is carried by the ball of radius `ε⁻¹`
  have hent_out : ent (θ[|Bᶜ]) (χ.E m) ≤ K :=
    ent_E_le χ (hθ.cond _) (inv_nonneg.2 hε.le) (Int.natCast_nonneg m)
  -- Chebyshev for the mass outside
  have hr2 : (r ^ 2)⁻¹ = Ex := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [hr, hEx, sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]
    congr 1
    ring
  have hmass : θ.real Bᶜ ≤ 2 * δ * Ex := by
    refine (measureReal_compl_closedBall_mean_le hθ hrpos).trans ?_
    rw [div_eq_mul_inv, hr2]
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  have hout : θ.real Bᶜ * ent (θ[|Bᶜ]) (χ.E m) ≤ ε * m / 4 := by
    have h1 : θ.real Bᶜ * ent (θ[|Bᶜ]) (χ.E m) ≤ 2 * δ * Ex * K :=
      mul_le_mul hmass hent_out (ent_nonneg _) (by positivity)
    have h2 : 2 * δ * Ex * K ≤ δ * D := by
      rw [hD]
      have : 0 ≤ δ * Ex := by positivity
      nlinarith
    have h3 : δ * D = ε * m / 4 := by
      rw [hδ]
      field_simp
    linarith
  have hinside : θ.real B * ent (θ[|B]) (χ.E m) ≤ 2 * Real.log 4 :=
    (mul_le_of_le_one_left (ent_nonneg _) measureReal_le_one).trans hent_in
  have hεm : 0 < ε * m := by positivity
  have hent : ent θ (χ.E m) < ε * m := by linarith
  rwa [div_lt_iff₀ hmpos]

/-! ### Lemma 3.6: positive entropy gives many levels of large variance -/

/-- Lemma 3.6 of the source (lines 1034 to 1073) for `d = 2`: for `0 < ε < 1` there are `δ > 0`
and `N` such that, for `n ≥ N` and a planar probability measure `θ` carried by a ball of radius
`ε⁻¹` with `H(θ, ℰ_n) / n > ε`, more than `δ n` of the levels `1 ≤ b ≤ n` (written `b = i + 1`,
`i < n`) have the property that the components `θ_{x,b}` with `Var(π_j A_χ^b θ_{x,b}) > δ` for
some `j` carry mass more than `δ`. -/
theorem exists_many_levels_var_gt :
    ∀ ε, 0 < ε → ε < 1 → ∃ δ > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (θ : Measure (ℝ × ℝ)) [IsProbabilityMeasure θ] (c : ℝ × ℝ), InBall θ c ε⁻¹ →
        ε < ent θ (χ.E n) / n →
        δ * n < (((Finset.range n).filter (fun i => δ < cavg θ (χ.E (i + 1 : ℕ))
          (fun ρ => if δ < var₁ (ρ.map (χ.resc (i + 1 : ℕ))) ∨
            δ < var₂ (ρ.map (χ.resc (i + 1 : ℕ))) then 1 else 0))).card : ℝ) := by
  intro ε hε hε1
  -- the uniform bound on the normalised entropy of a rescaled component
  set Bc := 2 * χ.χ₂ + 2 * Real.log 4 + 1 with hBc
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hBc1 : 1 < Bc := by have := χ.pos₂; linarith
  have hBcpos : 0 < Bc := by linarith
  -- Lemma 3.5 at the scale `ε / 8`
  have hε8 : 0 < ε / 8 := by positivity
  obtain ⟨M, hM⟩ := ent_E_div_lt_of_var_le χ (ε / 8) hε8
  obtain ⟨m, hmM, hm1, hm9⟩ : ∃ m : ℕ, M ≤ m ∧ 1 ≤ m ∧ Real.log 9 / m ≤ ε / 4 := by
    refine ⟨max (max M ⌈4 * Real.log 9 / ε⌉₊) 1, le_max_of_le_left (le_max_left _ _),
      le_max_right _ _, ?_⟩
    have hc := Nat.le_ceil (4 * Real.log 9 / ε)
    have hc' : (⌈4 * Real.log 9 / ε⌉₊ : ℝ) ≤ (max (max M ⌈4 * Real.log 9 / ε⌉₊) 1 : ℕ) := by
      exact_mod_cast le_max_of_le_left (le_max_right _ _)
    have hpos : (0 : ℝ) < (max (max M ⌈4 * Real.log 9 / ε⌉₊) 1 : ℕ) := by
      exact_mod_cast lt_of_lt_of_le Nat.one_pos (le_max_right _ _)
    rw [div_le_iff₀ hpos]
    have : 4 * Real.log 9 / ε * ε = 4 * Real.log 9 := div_mul_cancel₀ _ hε.ne'
    nlinarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  obtain ⟨δ', hδ', hδ'prop⟩ := hM m hmM
  set δ := min δ' (ε / (16 * Bc)) with hδdef
  have hδpos : 0 < δ := lt_min hδ' (by positivity)
  have hδle : δ ≤ δ' := min_le_left _ _
  have hδle' : δ ≤ ε / (16 * Bc) := min_le_right _ _
  -- the threshold on `n`
  set K0 := 2 * Real.log (2 * ε⁻¹ + 2) with hK0
  refine ⟨δ, hδpos, ⌈4 * (χ.c₀ * m + K0) / ε⌉₊ + 1, fun n hn θ _ c hθ hent => ?_⟩
  have hnpos : (0 : ℝ) < n := by
    have : 1 ≤ n := le_trans (Nat.le_add_left 1 _) hn
    exact_mod_cast this
  have hnN : χ.c₀ * m + K0 < ε / 4 * n := by
    have h1 := Nat.le_ceil (4 * (χ.c₀ * m + K0) / ε)
    have h2 : ((⌈4 * (χ.c₀ * m + K0) / ε⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    have h3 : 4 * (χ.c₀ * m + K0) / ε < n := by linarith
    rw [div_lt_iff₀ hε] at h3
    linarith
  have hbd : BddSupp θ := ⟨c, _, hθ⟩
  -- Lemma 2.1
  have h21 := ent_E_div_le_avg_add χ hbd n hm1
  have he0 : ent θ (χ.E 0) ≤ K0 := ent_E_zero_le χ hθ (inv_nonneg.2 hε.le)
  set G : ℕ → ℝ := fun i => cavg θ (χ.E (i + 1 : ℕ))
    (fun ρ => ent (ρ.map (χ.resc (i + 1 : ℕ))) (χ.E m) / m) with hG
  -- the local entropy and the rescaled local entropy
  have hcent : ∀ i : ℕ, cent θ (χ.E ((i + 1 : ℕ) + m)) (χ.E (i + 1 : ℕ)) / m ≤
      G i + Real.log 9 / m := by
    intro i
    have hfin := hbd.finiteLabels_E χ ((i + 1 : ℕ) : ℤ)
    rw [cent_E_eq_cavg χ hbd, ← cavg_div hfin]
    calc cavg θ (χ.E (i + 1 : ℕ)) (fun ρ => ent ρ (χ.E ((i + 1 : ℕ) + m)) / m)
        ≤ cavg θ (χ.E (i + 1 : ℕ))
            (fun ρ => ent (ρ.map (χ.resc (i + 1 : ℕ))) (χ.E m) / m + Real.log 9 / m) := by
          refine cavg_mono hfin fun b _ => ?_
          have := ent_comp_E_le_ent_map_resc_add χ hbd ((i + 1 : ℕ) : ℤ) m b
          rw [← add_div]
          exact div_le_div_of_nonneg_right this hmpos.le
      _ = G i + Real.log 9 / m := by
          rw [cavg_add hfin, cavg_const (χ.measurable_E _) hfin]
  -- the bound on the rescaled local entropies
  have hGle : ∀ i : ℕ, G i ≤ Bc := by
    intro i
    refine cavg_le_of_le (χ.measurable_E _) (hbd.finiteLabels_E χ _) fun b _ => ?_
    obtain ⟨z, hz⟩ := exists_inBall_map_resc_comp χ θ ((i + 1 : ℕ) : ℤ) b
    have := ent_E_div_le_const χ hz hm1
    linarith
  -- the average of the rescaled local entropies exceeds `ε / 2`
  have hsumG : ε / 2 * n < ∑ i ∈ Finset.range n, G i := by
    have h1 : ∑ i ∈ Finset.range n, cent θ (χ.E ((i + 1 : ℕ) + m)) (χ.E (i + 1 : ℕ)) / m ≤
        ∑ i ∈ Finset.range n, G i + n * (Real.log 9 / m) := by
      refine (Finset.sum_le_sum fun i _ => hcent i).trans_eq ?_
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← add_div, div_le_div_iff_of_pos_right hnpos] at h21
    rw [lt_div_iff₀ hnpos] at hent
    have h2 : (n : ℝ) * (Real.log 9 / m) ≤ n * (ε / 4) :=
      mul_le_mul_of_nonneg_left hm9 hnpos.le
    linarith
  -- Markov over the levels
  set I := (Finset.range n).filter (fun i => ε / 4 < G i) with hI
  have hIcard : ε / (4 * Bc) * n < I.card := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range n) (fun i => ε / 4 < G i) G
    have hIs : ∑ i ∈ I, G i ≤ I.card * Bc := by
      have := Finset.sum_le_card_nsmul I G Bc fun i _ => hGle i
      rwa [nsmul_eq_mul] at this
    have hnIs : ∑ i ∈ (Finset.range n).filter (fun i => ¬ ε / 4 < G i), G i ≤ n * (ε / 4) := by
      have := Finset.sum_le_card_nsmul ((Finset.range n).filter (fun i => ¬ ε / 4 < G i)) G
        (ε / 4) fun i hi => not_lt.1 (Finset.mem_filter.1 hi).2
      rw [nsmul_eq_mul] at this
      have hc : (((Finset.range n).filter (fun i => ¬ ε / 4 < G i)).card : ℝ) ≤ n := by
        exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range n).le
      have : 0 ≤ ε / 4 := by positivity
      nlinarith
    have h1 : ε / 4 * n < I.card * Bc := by linarith
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    linarith
  -- Markov inside a level and Lemma 3.5 in the contrapositive
  have hkey : ∀ i, ε / 4 < G i → δ < cavg θ (χ.E (i + 1 : ℕ))
      (fun ρ => if δ < var₁ (ρ.map (χ.resc (i + 1 : ℕ))) ∨
        δ < var₂ (ρ.map (χ.resc (i + 1 : ℕ))) then 1 else 0) := by
    intro i hi
    have hf := χ.measurable_E ((i + 1 : ℕ) : ℤ)
    have hfin := hbd.finiteLabels_E χ ((i + 1 : ℕ) : ℤ)
    have htB : ε / 8 < Bc := by linarith
    have hmk := cavg_indicator_ge hf hfin (F := fun ρ =>
      ent (ρ.map (χ.resc (i + 1 : ℕ))) (χ.E m) / m) htB fun b _ => by
        obtain ⟨z, hz⟩ := exists_inBall_map_resc_comp χ θ ((i + 1 : ℕ) : ℤ) b
        have := ent_E_div_le_const χ hz hm1
        linarith
    have hmono : cavg θ (χ.E (i + 1 : ℕ)) (fun ρ =>
        if ε / 8 < ent (ρ.map (χ.resc (i + 1 : ℕ))) (χ.E m) / m then 1 else 0) ≤
        cavg θ (χ.E (i + 1 : ℕ)) (fun ρ => if δ < var₁ (ρ.map (χ.resc (i + 1 : ℕ))) ∨
          δ < var₂ (ρ.map (χ.resc (i + 1 : ℕ))) then 1 else 0) := by
      refine cavg_mono hfin fun b hb => ?_
      have := comp_isProbabilityMeasure hb
      split_ifs with hlt hvar hvar
      · exact le_rfl
      · exfalso
        rw [not_or, not_lt, not_lt] at hvar
        obtain ⟨z, hz⟩ := exists_inBall_map_resc_comp χ θ ((i + 1 : ℕ) : ℤ) b
        have hz' := hz.mono ((one_le_inv₀ hε8).2 (by linarith))
        have := hδ'prop _ z hz' (hvar.1.trans hδle) (hvar.2.trans hδle)
        linarith
      · exact zero_le_one
      · exact le_rfl
    have hG8 : ε / 8 / Bc ≤ (G i - ε / 8) / (Bc - ε / 8) := by
      have h1 : ε / 8 / Bc ≤ (G i - ε / 8) / Bc :=
        div_le_div_of_nonneg_right (by linarith) hBcpos.le
      have h2 : (G i - ε / 8) / Bc ≤ (G i - ε / 8) / (Bc - ε / 8) :=
        div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
      linarith
    have hδ8 : δ < ε / 8 / Bc := by
      have : ε / (16 * Bc) < ε / 8 / Bc := by
        rw [div_div]
        exact div_lt_div_of_pos_left hε (by positivity) (by nlinarith)
      linarith
    linarith
  have hsub : I ⊆ (Finset.range n).filter (fun i => δ < cavg θ (χ.E (i + 1 : ℕ))
      (fun ρ => if δ < var₁ (ρ.map (χ.resc (i + 1 : ℕ))) ∨
        δ < var₂ (ρ.map (χ.resc (i + 1 : ℕ))) then 1 else 0)) := by
    intro i hi
    rw [hI, Finset.mem_filter] at hi
    rw [Finset.mem_filter]
    exact ⟨hi.1, hkey i hi.2⟩
  have hcard : (I.card : ℝ) ≤ (((Finset.range n).filter (fun i => δ < cavg θ (χ.E (i + 1 : ℕ))
      (fun ρ => if δ < var₁ (ρ.map (χ.resc (i + 1 : ℕ))) ∨
        δ < var₂ (ρ.map (χ.resc (i + 1 : ℕ))) then 1 else 0))).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hδn : δ * n ≤ ε / (4 * Bc) * n := by
    refine mul_le_mul_of_nonneg_right (hδle'.trans ?_) hnpos.le
    exact div_le_div_of_nonneg_left hε.le (by positivity) (by linarith)
  linarith

end Variance

end BoxLike.Rapaport
