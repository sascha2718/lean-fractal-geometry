import FractalGeometry.Probability.GridPercolation.GatzourasLalley

/-!
# Growth of occupied columns

Dimitrios Gatzouras and Steven P. Lalley, "Statistically self-affine sets:
Hausdorff and box dimensions", Journal of Theoretical Probability 7 (1994),
437–468, DOI 10.1007/BF02214277. This is the independent Bernoulli-child
specialisation of Proposition 3.5 in the March 1993 author version.

On survival, the logarithm of the number of occupied columns at generation `n`,
divided by `n`, converges almost surely to the logarithm of `GridLaw.lam`.
-/

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {A : GridLaw} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

theorem ae_eventually_exists_retained_good_root (hX : IsPercolation P X) (hm : 1 < A.m)
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (D : ℕ → Set (Configuration A))
    (hD : ∀ a, MeasurableSet (D a))
    (hp : ∀ᶠ a : ℕ in atTop, ENNReal.ofReal ρ ≤ P {ω | config X ω ∈ D a}) :
    ∀ᵐ ω ∂P, ω ∈ survival X → ∀ᶠ a : ℕ in atTop,
      ∃ u ∈ retainedDigitWords X (bfloor δ a) ω, deepVector X (wordOfDigits u) ω ∈ D a := by
  classical
  let := hX.toIsProbabilityMeasure
  obtain ⟨a₀, ha₀⟩ := eventually_atTop.mp hp
  have hpρ (a : ℕ) (ha : a₀ ≤ a) : ρ ≤ (P {ω | config X ω ∈ D a}).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp (ha₀ a ha)
  let bad : ℕ → Set Ω := fun a => if a₀ ≤ a then
      {ω | ⌊Real.sqrt A.m ^ bfloor δ a⌋₊ + 1 ≤ descendantCountBelow X [] (bfloor δ a) ω ∧
        (((retainedDigitWords X (bfloor δ a) ω).filter fun u =>
          deepVector X (wordOfDigits u) ω ∈ D a).card : ℝ) <
            (P {ω | config X ω ∈ D a}).toReal * descendantCountBelow X [] (bfloor δ a) ω / 2}
      else ∅
  have hbad (a : ℕ) : P (bad a) ≤ ENNReal.ofReal (4 / (ρ * Real.sqrt A.m ^ bfloor δ a)) := by
    by_cases ha : a₀ ≤ a
    · simp only [bad, ite_eq_left ha]
      refine (measure_descendantCount_ge_inter_card_filter_lt_le hX (hD a)
        (hρ.trans_le (hpρ a ha)) _ (Nat.succ_pos _)).trans ?_
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have hB : Real.sqrt A.m ^ bfloor δ a ≤
          ((⌊Real.sqrt A.m ^ bfloor δ a⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast
        exact (Nat.lt_floor_add_one _).le
      exact mul_le_mul (hpρ a ha) hB (by positivity) (hρ.le.trans (hpρ a ha))
    · simp [bad, ha]
  have hsum : (∑' a, P (bad a)) ≠ ∞ :=
    ne_top_of_le_ne_top (tsum_ofReal_four_div_sqrt_pow_ne_top hm hρ hδ
      (g := fun a => bfloor δ a) fun a => lt_bfloor_cast_add_one δ a)
      (ENNReal.tsum_le_tsum hbad)
  have hbtend : Tendsto (fun a : ℕ => bfloor δ a) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hδ)
  filter_upwards [ae_exists_pos_eventually_descendantCount_ge hX hm,
    ae_eventually_notMem hsum] with ω hg hnot hs
  obtain ⟨c, hc, hZ⟩ := hg hs
  filter_upwards [hnot, hbtend.eventually hZ,
    hbtend.eventually (eventually_floor_sqrt_pow_add_one_le hm hc),
    eventually_ge_atTop a₀] with a hnot haZ haB ha
  simp only [bad, ite_eq_left ha, Set.mem_ofPred_eq, not_and, not_lt] at hnot
  have hBZ : ⌊Real.sqrt A.m ^ bfloor δ a⌋₊ + 1 ≤
      descendantCountBelow X [] (bfloor δ a) ω := by exact_mod_cast haB.trans haZ
  have hZpos : (0 : ℝ) < descendantCountBelow X [] (bfloor δ a) ω := by
    have : 0 < descendantCountBelow X [] (bfloor δ a) ω := (Nat.succ_pos _).trans_le hBZ
    exact_mod_cast this
  have hcount := hnot hBZ
  have hppos := hρ.trans_le (hpρ a ha)
  have hcountpos : 0 < ((retainedDigitWords X (bfloor δ a) ω).filter fun u =>
      deepVector X (wordOfDigits u) ω ∈ D a).card := by
    exact_mod_cast (lt_of_lt_of_le (by positivity :
      0 < (P {ω | config X ω ∈ D a}).toReal * descendantCountBelow X [] (bfloor δ a) ω / 2)
      hcount)
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hcountpos
  exact ⟨u, (Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2⟩

omit [MeasurableSpace Ω] in
lemma wordOfCoordinates_append {b L : ℕ} (u : DigitWord A b)
    (v : ColumnWord A L) (r : RowWord A L) :
    wordOfCoordinates (Fin.append (fun i => (u i).1) v) (Fin.append (fun i => (u i).2) r) =
      wordOfDigits u ++ wordOfCoordinates v r := by
  unfold wordOfCoordinates wordOfDigits
  rw [List.ofFn_add]
  congr 1 <;> apply congrArg List.ofFn <;> funext i <;> simp

omit [MeasurableSpace Ω] in
theorem prunedColumnCountBelow_le_total {b L : ℕ} {u : DigitWord A b} {ω : Ω}
    (hu : Retained X ω (wordOfDigits u)) :
    prunedColumnCountBelow X (wordOfDigits u) L ω ≤ prunedColumnCount X (b + L) ω := by
  classical
  unfold prunedColumnCount prunedColumnCountBelow
  refine Finset.card_le_card_of_injOn (fun v => Fin.append (fun i => (u i).1) v) ?_ ?_
  · intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
    obtain ⟨r, hr, hd⟩ := hv
    refine ⟨Fin.append (fun i => (u i).2) r, ?_, ?_⟩
    · rw [wordOfCoordinates_append, retainedBelow_append_iff]
      exact ⟨(retained_iff_retainedBelow_nil X ω _).mp hu, by simpa using hr⟩
    · rw [wordOfCoordinates_append, List.nil_append]
      exact hd
  · intro v _ w _ h
    funext i
    have := congrFun h (Fin.natAdd b i)
    simpa using this

omit [MeasurableSpace Ω] in
lemma prunedColumnCount_le_occupied (ω : Ω) (L : ℕ) :
    prunedColumnCount X L ω ≤ occupiedColumnCount X L ω := by
  classical
  unfold prunedColumnCount prunedColumnCountBelow occupiedColumnCount occupiedColumnCountBelow
  apply Finset.card_le_card
  intro v hv
  obtain ⟨r, hr, -⟩ := (Finset.mem_filter.mp hv).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rw [tubePopulationBelow, Finset.card_pos]
  exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩

lemma tendsto_sub_bfloor {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    Tendsto (fun a : ℕ => a - bfloor δ a) atTop atTop := by
  apply tendsto_atTop.mpr
  intro n
  filter_upwards [eventually_ge_atTop ⌈(n : ℝ) / (1 - δ)⌉₊] with a ha
  have h1 : (n : ℝ) / (1 - δ) ≤ a := (Nat.le_ceil _).trans (by exact_mod_cast ha)
  have h2 : (n : ℝ) ≤ a * (1 - δ) := by rwa [div_le_iff₀ (by linarith)] at h1
  apply (Nat.cast_le (α := ℝ)).mp
  rw [Nat.cast_sub (bfloor_le_self hδ1.le a)]
  nlinarith [bfloor_cast_le hδ0 a]

theorem ae_eventually_projectionRate_lower (hX : IsPercolation P X) (hm : 1 < A.m)
    {η : ℝ} (hη : 0 < η) :
    ∀ᵐ ω ∂P, ω ∈ survival X → ∀ᶠ a : ℕ in atTop,
      Real.log A.lam - η ≤ Real.log (occupiedColumnCount X a ω) / a := by
  have hlam := A.lam_pos hm
  have hloglam := Real.log_nonneg (A.one_le_lam hm)
  let δ : ℝ := min (1 / 2) (η / (2 * (Real.log A.lam + 1)))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hloss : 2 * δ * Real.log A.lam ≤ η := by
    have hd := min_le_right (1 / 2 : ℝ) (η / (2 * (Real.log A.lam + 1)))
    have hd' : δ * (2 * (Real.log A.lam + 1)) ≤ η :=
      (le_div_iff₀ (by positivity)).mp hd
    nlinarith
  obtain ⟨ρ, hρ, hp⟩ := forall_exists_measure_prunedColumnCount_ge_of_isPercolation hX hm δ hδ
  let D : ℕ → Set (Configuration A) := fun a =>
    {x | A.lam ^ ((1 - δ) * ((a - bfloor δ a : ℕ) : ℝ)) ≤
      (prunedColumnCountConfig x [] (a - bfloor δ a) : ℝ)}
  have hD (a : ℕ) : MeasurableSet (D a) :=
    measurableSet_le measurable_const
      (measurable_from_nat.comp (measurable_prunedColumnCountConfig [] _))
  have hp' : ∀ᶠ a : ℕ in atTop, ENNReal.ofReal ρ ≤ P {ω | config X ω ∈ D a} :=
    (tendsto_sub_bfloor hδ.le hδ1).eventually hp
  filter_upwards [ae_eventually_exists_retained_good_root hX hm hδ hρ D hD hp'] with ω hω hs
  filter_upwards [hω hs, eventually_ge_atTop 1] with a ha ha1
  obtain ⟨u, hu, hdeep⟩ := ha
  change A.lam ^ ((1 - δ) * ((a - bfloor δ a : ℕ) : ℝ)) ≤
    (prunedColumnCountConfig (deepVector X (wordOfDigits u) ω) [] (a - bfloor δ a) : ℝ) at hdeep
  rw [deepVector_eq_rebase, prunedColumnCountConfig_rebase, List.append_nil] at hdeep
  have hcount : prunedColumnCountBelow X (wordOfDigits u) (a - bfloor δ a) ω ≤
      occupiedColumnCount X a ω := by
    have h := prunedColumnCountBelow_le_total (L := a - bfloor δ a) (mem_retainedDigitWords.mp hu)
    rw [Nat.add_sub_of_le (bfloor_le_self hδ1.le a)] at h
    exact h.trans (prunedColumnCount_le_occupied ω a)
  have hbound : A.lam ^ ((1 - δ) * ((a - bfloor δ a : ℕ) : ℝ)) ≤
      (occupiedColumnCount X a ω : ℝ) := hdeep.trans (by exact_mod_cast hcount)
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha1
  apply (le_div_iff₀ hapos).mpr
  refine le_trans ?_ (Real.log_le_log (Real.rpow_pos_of_pos hlam _) hbound)
  rw [Real.log_rpow hlam, Nat.cast_sub (bfloor_le_self hδ1.le a)]
  have hb := bfloor_cast_le hδ.le a
  have h1 := mul_le_mul_of_nonneg_right hb (mul_nonneg (sub_nonneg.mpr hδ1.le) hloglam)
  have h2 := mul_le_mul_of_nonneg_left hloss hapos.le
  have h3 := mul_nonneg (sq_nonneg δ) (mul_nonneg hapos.le hloglam)
  nlinarith

theorem ae_eventually_projectionRate_upper (hX : IsPercolation P X) (hm : 1 < A.m)
    {η : ℝ} (hη : 0 < η) :
    ∀ᵐ ω ∂P, ∀ᶠ a : ℕ in atTop,
      Real.log (occupiedColumnCount X a ω) / a ≤ Real.log A.lam + η := by
  let := hX.toIsProbabilityMeasure
  let bad : ℕ → Set Ω := fun a => {ω |
    Real.exp (a * (Real.log A.lam + η)) ≤ (occupiedColumnCount X a ω : ℝ)}
  have hint (a : ℕ) : Integrable (fun ω => (occupiedColumnCount X a ω : ℝ)) P := by
    exact integrable_of_abs_le hX
      (measurable_from_nat.comp (measurable_occupiedColumnCount hX a)) ((A.M : ℝ) ^ a)
      (fun ω => by
        rw [abs_of_nonneg (Nat.cast_nonneg _)]
        exact columnCountFun_le a (config X ω))
  have hbad (a : ℕ) : P (bad a) ≤ ENNReal.ofReal (Real.exp (-η) ^ a) := by
    rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)]
    have hmark := mul_meas_ge_le_integral_of_nonneg
      (μ := P) (f := fun ω => (occupiedColumnCount X a ω : ℝ))
      (Eventually.of_forall fun _ => Nat.cast_nonneg _) (hint a)
      (Real.exp (a * (Real.log A.lam + η)))
    change Real.exp (a * (Real.log A.lam + η)) * (P (bad a)).toReal ≤ _ at hmark
    rw [mul_comm] at hmark
    have hmark := (le_div_iff₀ (Real.exp_pos (a * (Real.log A.lam + η)))).mpr hmark
    have hquot : A.lam ^ a / Real.exp (a * (Real.log A.lam + η)) = Real.exp (-η) ^ a := by
      have hpow : A.lam ^ a = Real.exp (a * Real.log A.lam) := by
        rw [← Real.log_pow, Real.exp_log (pow_pos (A.lam_pos hm) _)]
      rw [hpow, ← Real.exp_sub, ← Real.exp_nat_mul]
      congr 1
      ring
    rw [← hquot]
    exact hmark.trans (div_le_div_of_nonneg_right (integral_occupiedColumnCount_le_lam_pow hX a)
      (Real.exp_pos _).le)
  have hs : Summable fun a : ℕ => Real.exp (-η) ^ a :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (by rw [Real.exp_lt_one_iff]; linarith)
  have hsum : (∑' a, P (bad a)) ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' a : ℕ, Real.exp (-η) ^ a)) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun a => by positivity) hs]
    exact ENNReal.tsum_le_tsum hbad
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω, eventually_ge_atTop 1] with a ha ha1
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha1
  have hcount : (occupiedColumnCount X a ω : ℝ) < Real.exp (a * (Real.log A.lam + η)) :=
    lt_of_not_ge ha
  rcases Nat.eq_zero_or_pos (occupiedColumnCount X a ω) with hzero | hpos
  · simp only [hzero, Nat.cast_zero, Real.log_zero, zero_div]
    exact add_nonneg (Real.log_nonneg (A.one_le_lam hm)) hη.le
  · apply (div_le_iff₀ hapos).mpr
    have h := Real.log_le_log (by exact_mod_cast hpos) hcount.le
    rw [Real.log_exp] at h
    simpa only [mul_comm] using h

/-- The projection-population growth formula of Gatzouras–Lalley (1994),
Proposition 3.5 in the authors' March 1993 version, for independent Bernoulli retention. -/
theorem gatzourasLalley_projectionGrowth (hX : IsPercolation P X) (hm : 1 < A.m) :
    ∀ᵐ ω ∂P, ω ∈ survival X →
      Tendsto (fun a : ℕ => Real.log (occupiedColumnCount X a ω) / a) atTop
        (𝓝 (Real.log A.lam)) := by
  have hlo : ∀ᵐ ω ∂P, ∀ j : ℕ, ω ∈ survival X → ∀ᶠ a : ℕ in atTop,
      Real.log A.lam - 1 / ((j : ℝ) + 1) ≤ Real.log (occupiedColumnCount X a ω) / a :=
    ae_all_iff.mpr fun j => ae_eventually_projectionRate_lower hX hm (by positivity)
  have hup : ∀ᵐ ω ∂P, ∀ j : ℕ, ∀ᶠ a : ℕ in atTop,
      Real.log (occupiedColumnCount X a ω) / a ≤ Real.log A.lam + 1 / ((j : ℝ) + 1) :=
    ae_all_iff.mpr fun j => ae_eventually_projectionRate_upper hX hm (by positivity)
  filter_upwards [hlo, hup] with ω hlo hup hs
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  apply eventually_atTop.mp
  filter_upwards [hlo j hs, hup j] with a ha hb
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end FractalGeometry.Probability.GridPercolation
