import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.ApproxSquareBoxDimensions
import FractalGeometry.Probability.GridPercolation.ApproxSquareCount
import FractalGeometry.Probability.GridPercolation.ApproxSquares
import FractalGeometry.Probability.GridPercolation.BlockIndependence
import FractalGeometry.Probability.GridPercolation.ColumnOffspring
import FractalGeometry.Probability.GridPercolation.Configuration
import FractalGeometry.Probability.GridPercolation.DigitCoordinates
import FractalGeometry.Probability.GridPercolation.Floor
import FractalGeometry.Probability.GridPercolation.FloorBounds
import FractalGeometry.Probability.GridPercolation.Lambda
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.LawInvariance
import FractalGeometry.Probability.GridPercolation.LowerCovering
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.Processes
import FractalGeometry.Probability.GridPercolation.PrunedSurvival
import FractalGeometry.Probability.GridPercolation.RootIndependence
import FractalGeometry.Probability.GridPercolation.SecondMomentRoots
import FractalGeometry.Probability.GridPercolation.ShallowEvents
import FractalGeometry.Probability.GridPercolation.SurvivalGrowth
import FractalGeometry.Probability.GridPercolation.WordCoordinates
import FractalGeometry.Probability.GridPercolation.WordSplitting

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory ProbabilityTheory Filter Topology

open scoped ENNReal

variable {A : GridLaw} {Ω : Type*} {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

noncomputable def splitCode (a : ℕ) (u : DigitWord A (bfloor A.Gamma a))
    (v : ColumnWord A (a - bfloor A.Gamma a)) : SquareCode A a :=
  (fun l => if h : (l : ℕ) < bfloor A.Gamma a then (u ⟨l, h⟩).1
      else v ⟨l - bfloor A.Gamma a, by have := l.isLt; omega⟩,
    fun l => (u l).2)

lemma memCell_splitCode (a : ℕ) (u : DigitWord A (bfloor A.Gamma a))
    (v : ColumnWord A (a - bfloor A.Gamma a)) (r : RowWord A (a - bfloor A.Gamma a)) :
    (splitCode a u v).MemCell (wordOfDigits u ++ wordOfCoordinates v r) := by
  have hb := A.bfloor_le a
  refine ⟨?_, fun l => ?_, fun l => ?_⟩
  · simp only [List.length_append, length_wordOfDigits, length_wordOfCoordinates]
    omega
  · by_cases hl : (l : ℕ) < bfloor A.Gamma a
    · rw [colD_append_left _ _ (by simpa using hl), colD_wordOfDigits u hl]
      simp only [splitCode, SquareCode.col, dite_eq_left hl]
    · rw [colD_append_right _ _ (by simpa using not_lt.mp hl)]
      simp only [length_wordOfDigits]
      rw [colD_wordOfCoordinates v r (by have := l.isLt; omega)]
      simp only [splitCode, SquareCode.col, dite_eq_right hl]
  · rw [rowD_append_left _ _ (by simp), rowD_wordOfDigits u l.isLt]
    simp [splitCode]

theorem sum_prunedColumnCountBelow_le_card_limitMeetingCodes (ω : Ω) (a : ℕ) :
    ∑ u ∈ retainedDigitWords X (bfloor A.Gamma a) ω,
        prunedColumnCountBelow X (wordOfDigits u) (a - bfloor A.Gamma a) ω ≤
      (limitMeetingCodes X ω a).card := by
  classical
  let t : DigitWord A (bfloor A.Gamma a) → Finset (ColumnWord A (a - bfloor A.Gamma a)) :=
    fun u => (Finset.univ : Finset (ColumnWord A (a - bfloor A.Gamma a))).filter fun v =>
      ∃ r : RowWord A (a - bfloor A.Gamma a),
        RetainedBelow X ω (wordOfDigits u) (wordOfCoordinates v r) ∧
          HasInfiniteDescentBelow X ω (wordOfDigits u ++ wordOfCoordinates v r)
  have hsum : ∑ u ∈ retainedDigitWords X (bfloor A.Gamma a) ω,
        prunedColumnCountBelow X (wordOfDigits u) (a - bfloor A.Gamma a) ω =
      ((retainedDigitWords X (bfloor A.Gamma a) ω).sigma t).card := by
    rw [Finset.card_sigma]
    rfl
  rw [hsum]
  refine Finset.card_le_card_of_injOn (fun p => splitCode a p.1 p.2) ?_ ?_
  · rintro ⟨u, v⟩ hp
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, t, Finset.mem_filter,
      Finset.mem_univ, true_and] at hp
    obtain ⟨hu, r, hret, hdesc⟩ := hp
    have hW : Retained X ω (wordOfDigits u ++ wordOfCoordinates v r) := by
      rw [retained_iff_retainedBelow_nil, retainedBelow_append_iff]
      exact ⟨mem_retainedDigitWords.mp hu, by simpa using hret⟩
    obtain ⟨z, hz, hzF⟩ := rect_inter_limitSet_nonempty hW hdesc
    simp only [Finset.mem_coe, mem_limitMeetingCodes]
    exact ⟨z, rect_subset_region_of_memCell (memCell_splitCode a u v r) hz, hzF⟩
  · rintro ⟨u, v⟩ _ ⟨u', v'⟩ _ h
    simp only [splitCode, Prod.mk.injEq] at h
    obtain ⟨hcol, hrow⟩ := h
    have huu : u = u' := by
      funext i
      have hi : (i : ℕ) < bfloor A.Gamma a := i.isLt
      have h1 := congrFun hcol ⟨i, lt_of_lt_of_le i.isLt (A.bfloor_le a)⟩
      have h2 := congrFun hrow i
      simp only [dite_eq_left hi] at h1
      exact Prod.ext h1 h2
    subst huu
    have hvv : v = v' := by
      funext j
      have hj : ¬ (bfloor A.Gamma a + (j : ℕ) < bfloor A.Gamma a) := by omega
      have h1 := congrFun hcol ⟨bfloor A.Gamma a + j, by have := j.isLt; omega⟩
      simp only [dite_eq_right hj] at h1
      convert h1 using 2 <;> exact Fin.ext (by simp)
    subst hvv
    rfl

lemma sbox_log_M_eq_gamma_log_m_add :
    A.sbox * Real.log A.M = A.Gamma * Real.log A.m + (1 - A.Gamma) * Real.log A.lam := by
  have hlogM := A.log_M_pos
  have hlogN := A.log_N_pos
  rw [GridLaw.sbox, GridLaw.sproj, GridLaw.Gamma]
  field_simp

lemma approximateSquareRate_le_log_div (ω : Ω) {a : ℕ} (ha : 1 ≤ a) :
    approximateSquareRate X ω a ≤ Real.log (A.M * A.N) / Real.log A.M := by
  have hlogM := A.log_M_pos
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha
  have hMN : (1 : ℝ) ≤ A.M * A.N :=
    one_le_mul_of_one_le_of_one_le A.one_le_M_real A.one_lt_N_real.le
  rw [approximateSquareRate, div_le_div_iff₀ (by positivity) hlogM]
  have hcard : ((limitMeetingCodes X ω a).card : ℝ) ≤ ((A.M : ℝ) * A.N) ^ a := by
    have h1 : (limitMeetingCodes X ω a).card ≤ Fintype.card (SquareCode A a) :=
      Finset.card_le_univ _
    rw [card_squareCode] at h1
    have h2 : A.M ^ a * A.N ^ (bfloor A.Gamma a) ≤ (A.M * A.N) ^ a := by
      rw [mul_pow]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right A.hN_pos (A.bfloor_le a))
    exact_mod_cast h1.trans h2
  have hlog : Real.log ((limitMeetingCodes X ω a).card : ℝ) ≤ a * Real.log (A.M * A.N) := by
    rcases Nat.eq_zero_or_pos (limitMeetingCodes X ω a).card with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact mul_nonneg hapos.le (Real.log_nonneg hMN)
    · calc Real.log ((limitMeetingCodes X ω a).card : ℝ) ≤ Real.log (((A.M : ℝ) * A.N) ^ a) :=
            Real.log_le_log (by exact_mod_cast hpos) hcard
        _ = a * Real.log (A.M * A.N) := by rw [Real.log_pow]
  calc Real.log ((limitMeetingCodes X ω a).card : ℝ) * Real.log A.M ≤
        (a * Real.log (A.M * A.N)) * Real.log A.M := mul_le_mul_of_nonneg_right hlog hlogM.le
    _ = Real.log (A.M * A.N) * (a * Real.log A.M) := by ring

lemma tsum_ofReal_four_div_sqrt_pow_ne_top {m ρ δ : ℝ} (hm : 1 < m) (hρ : 0 < ρ) (hδ : 0 < δ)
    {g : ℕ → ℕ} (hg : ∀ L : ℕ, (L : ℝ) * δ < g L + 1) :
    (∑' L, ENNReal.ofReal (4 / (ρ * Real.sqrt m ^ g L))) ≠ ∞ := by
  set s := Real.sqrt m with hs
  have hs1 : 1 < s := by
    rw [hs, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) hm
  have hs0 : 0 < s := zero_lt_one.trans hs1
  set q := s ^ δ with hq
  have hq1 : 1 < q := Real.one_lt_rpow hs1 hδ
  have hbound : ∀ L : ℕ, 4 / (ρ * s ^ g L) ≤ (4 * s / ρ) * q⁻¹ ^ L := by
    intro L
    have hpow : q ^ L ≤ s ^ g L * s := by
      calc q ^ L = s ^ (δ * (L : ℝ)) := by
            rw [hq, Real.rpow_mul hs0.le, Real.rpow_natCast]
        _ ≤ s ^ ((g L : ℝ) + 1) :=
            Real.rpow_le_rpow_of_exponent_le hs1.le (by linarith [hg L])
        _ = s ^ g L * s := by rw [Real.rpow_add_one hs0.ne', Real.rpow_natCast]
    calc 4 / (ρ * s ^ g L) = (4 * s / ρ) / (s ^ g L * s) := by
          field_simp
      _ ≤ (4 * s / ρ) / q ^ L :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
      _ = (4 * s / ρ) * q⁻¹ ^ L := by rw [inv_pow, div_eq_mul_inv]
  have hsum : Summable fun L : ℕ => (4 * s / ρ) * q⁻¹ ^ L :=
    (summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hq1)).mul_left _
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' L, (4 * s / ρ) * q⁻¹ ^ L)) ?_
  rw [ENNReal.ofReal_tsum_of_nonneg (fun L => by positivity) hsum]
  exact ENNReal.tsum_le_tsum fun L => ENNReal.ofReal_le_ofReal (hbound L)

lemma eventually_floor_sqrt_pow_add_one_le {m c : ℝ} (hm : 1 < m) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ((⌊Real.sqrt m ^ n⌋₊ + 1 : ℕ) : ℝ) ≤ c * m ^ n := by
  set s := Real.sqrt m with hs
  have hs1 : 1 < s := by
    rw [hs, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) hm
  have hss : s * s = m := Real.mul_self_sqrt (by linarith)
  filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt hs1).eventually_ge_atTop (max (2 / c) 1)]
    with n hn
  have h1 : 1 ≤ s ^ n := le_trans (le_max_right _ _) hn
  have h2 : 2 ≤ c * s ^ n := by
    have h := le_trans (le_max_left _ _) hn
    calc (2 : ℝ) = c * (2 / c) := by field_simp
      _ ≤ c * s ^ n := by gcongr
  have hfl : (⌊s ^ n⌋₊ : ℝ) ≤ s ^ n := Nat.floor_le (by positivity)
  push_cast
  calc (⌊s ^ n⌋₊ : ℝ) + 1 ≤ 2 * s ^ n := by linarith
    _ ≤ (c * s ^ n) * s ^ n := by gcongr
    _ = c * m ^ n := by rw [← hss, mul_pow]; ring

variable [MeasurableSpace Ω] {P : Measure Ω}

open scoped Classical in

theorem measure_retainedDigitWords_eq_inter_filter (hX : IsPercolation P X) (k : ℕ)
    (S : Finset (DigitWord A k)) {D : Set (Configuration A)} (hD : MeasurableSet D)
    (Q : Finset (DigitWord A k) → Prop) :
    P ({ω | retainedDigitWords X k ω = S} ∩
        {ω | Q (S.filter fun u => deepVector X (wordOfDigits u) ω ∈ D)}) =
      P {ω | retainedDigitWords X k ω = S} *
        P {ω | Q (S.filter fun u => deepVector X (wordOfDigits u) ω ∈ D)} := by
  classical
  let := hX.toIsProbabilityMeasure
  set C : Set (Configuration A) :=
    {x | ∀ u : DigitWord A k, retainedBelowConfig x [] (wordOfDigits u) ↔ u ∈ S} with hC
  have hCmeas : MeasurableSet C := by
    have hset : C = ⋂ u : DigitWord A k,
        {x : Configuration A | retainedBelowConfig x [] (wordOfDigits u) ↔ u ∈ S} := by
      ext x
      simp [hC]
    rw [hset]
    refine MeasurableSet.iInter fun u => ?_
    by_cases hu : u ∈ S
    · simp only [hu, iff_true]
      exact measurableSet_retainedBelowConfig [] _
    · simp only [hu, iff_false]
      exact (measurableSet_retainedBelowConfig [] _).compl
  have hshallow : {ω | shallowVector X k ω ∈ shallowExtend k ⁻¹' C} =
      {ω | retainedDigitWords X k ω = S} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hC]
    constructor
    · intro h
      ext u
      rw [mem_retainedDigitWords, ← h u]
      exact (retainedBelowConfig_shallow_iff X k ω (by simp)).symm
    · intro h u
      rw [← h, mem_retainedDigitWords]
      exact retainedBelowConfig_shallow_iff X k ω (by simp)

  set side : Finset (DigitWord A k) → DigitWord A k → Set (Configuration A) :=
    fun T u => if u ∈ T then D else Dᶜ with hside
  have hsidemeas : ∀ T u, MeasurableSet (side T u) := by
    intro T u
    simp only [hside]
    split_ifs
    · exact hD
    · exact hD.compl
  set E : Finset (DigitWord A k) → Set Ω :=
    fun T => ⋂ u ∈ S, {ω | deepVector X (wordOfDigits u) ω ∈ side T u} with hE
  have hEmeas : ∀ T, MeasurableSet (E T) := fun T =>
    Finset.measurableSet_biInter S fun u _ =>
      measurable_deepVector hX (wordOfDigits u) (hsidemeas T u)
  have hEeq : ∀ T ∈ S.powerset,
      E T = {ω | (S.filter fun u => deepVector X (wordOfDigits u) ω ∈ D) = T} := by
    intro T hT
    have hTS := Finset.mem_powerset.mp hT
    ext ω
    simp only [hE, hside, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro h
      ext u
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨huS, hD'⟩
        by_contra huT
        have := h u huS
        simp only [huT, ite_false, Set.mem_compl_iff] at this
        exact this hD'
      · intro huT
        refine ⟨hTS huT, ?_⟩
        have := h u (hTS huT)
        simpa [huT] using this
    · intro h u huS
      by_cases huT : u ∈ T
      · simp only [huT, ite_true]
        rw [← h] at huT
        exact (Finset.mem_filter.mp huT).2
      · simp only [huT, ite_false, Set.mem_compl_iff]
        intro hD'
        apply huT
        rw [← h]
        exact Finset.mem_filter.mpr ⟨huS, hD'⟩
  set good := S.powerset.filter Q with hgood
  have hQ : {ω | Q (S.filter fun u => deepVector X (wordOfDigits u) ω ∈ D)} =
      ⋃ T ∈ good, E T := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, hgood, Finset.mem_filter, exists_prop]
    constructor
    · intro h
      refine ⟨S.filter fun u => deepVector X (wordOfDigits u) ω ∈ D,
        ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), h⟩, ?_⟩
      rw [hEeq _ (Finset.mem_powerset.mpr (Finset.filter_subset _ _))]
      rfl
    · rintro ⟨T, ⟨hT, hQT⟩, hωT⟩
      rw [hEeq T hT] at hωT
      simp only [Set.mem_ofPred_eq] at hωT
      rw [hωT]
      exact hQT
  have hdisj : Set.PairwiseDisjoint (↑good) E := by
    intro T hT T' hT' hTT'
    rw [Function.onFun, Set.disjoint_left]
    intro ω h h'
    rw [hEeq T (Finset.mem_filter.mp hT).1] at h
    rw [hEeq T' (Finset.mem_filter.mp hT').1] at h'
    exact hTT' (h.symm.trans h')
  have hprod : ∀ T, P ({ω | retainedDigitWords X k ω = S} ∩ E T) =
      P {ω | retainedDigitWords X k ω = S} * P (E T) := by
    intro T
    have h1 := measure_shallow_inter_biInter hX (wordOfDigits (A := A) (L := k)) (c := k)
      (fun u => length_wordOfDigits u) (wordOfDigits_injective k)
      ((measurable_shallowExtend k) hCmeas) (S := side T) (hsidemeas T) S
    have h2 := measure_shallow_inter_biInter hX (wordOfDigits (A := A) (L := k)) (c := k)
      (fun u => length_wordOfDigits u) (wordOfDigits_injective k)
      (S₀ := Set.univ) MeasurableSet.univ (S := side T) (hsidemeas T) S
    rw [hshallow] at h1
    simp only [Set.mem_univ, Set.ofPred_true, Set.univ_inter, measure_univ, one_mul] at h2
    rw [h1, ← h2]
  rw [hQ, Set.inter_iUnion₂, measure_biUnion_finset _ (fun T _ => hEmeas T),
    measure_biUnion_finset, Finset.mul_sum]
  · exact Finset.sum_congr rfl fun T _ => hprod T
  · intro T hT T' hT' hTT'
    exact (hdisj hT hT' hTT').mono Set.inter_subset_right Set.inter_subset_right
  · exact fun T _ => (measurableSet_retainedDigitWords_eq hX k S).inter (hEmeas T)
  · exact hdisj

open scoped Classical in

theorem measure_card_filter_deep_lt_le (hX : IsPercolation P X) {D : Set (Configuration A)}
    (hD : MeasurableSet D) (hp : 0 < (P {ω | config X ω ∈ D}).toReal) {k : ℕ}
    (S : Finset (DigitWord A k)) (hS : S.Nonempty) :
    P {ω | ((S.filter fun u => deepVector X (wordOfDigits u) ω ∈ D).card : ℝ) <
        (P {ω | config X ω ∈ D}).toReal * S.card / 2} ≤
      ENNReal.ofReal (4 / ((P {ω | config X ω ∈ D}).toReal * S.card)) := by
  classical
  let := hX.toIsProbabilityMeasure
  set p := (P {ω | config X ω ∈ D}).toReal with hpdef
  set Y : DigitWord A k → Ω → ℝ :=
    fun u ω => D.indicator (fun _ => (1 : ℝ)) (deepVector X (wordOfDigits u) ω) with hY
  have hYmeas : ∀ u, Measurable (Y u) := fun u =>
    (measurable_const.indicator hD).comp (measurable_deepVector hX (wordOfDigits u))
  have hYbound : ∀ u ω, |Y u ω| ≤ 1 := by
    intro u ω
    simp only [hY, Set.indicator]
    split_ifs <;> norm_num
  have hYmemLp : ∀ u, MemLp (Y u) 2 P := fun u =>
    MemLp.of_bound (hYmeas u).aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using hYbound u ω)
  have hdeep : ∀ u : DigitWord A k,
      P {ω | deepVector X (wordOfDigits u) ω ∈ D} = P {ω | config X ω ∈ D} := by
    intro u
    have h1 := hX.measure_config_functional_shift (wordOfDigits u) (G := id) measurable_id hD
    simpa only [id, deepVector_eq_rebase] using h1
  have hYint : ∀ u, ∫ ω, Y u ω ∂P = p := by
    intro u
    have hpre : (fun ω => Y u ω) =
        (deepVector X (wordOfDigits u) ⁻¹' D).indicator (fun _ => (1 : ℝ)) := by
      funext ω
      simp [hY, Set.indicator]
    rw [hpre, integral_indicator_const _ (measurable_deepVector hX (wordOfDigits u) hD),
      smul_eq_mul, mul_one, measureReal_def]
    change (P {ω | deepVector X (wordOfDigits u) ω ∈ D}).toReal = p
    rw [hdeep u]
  have hYsq : ∀ u, ∫ ω, (Y u ^ 2) ω ∂P = p := by
    intro u
    have : Y u ^ 2 = Y u := by
      funext ω
      simp only [Pi.pow_apply, hY, Set.indicator]
      split_ifs <;> norm_num
    rw [this]
    exact hYint u
  have hind : iIndepFun (fun u ω => deepVector X (wordOfDigits u) ω) P :=
    (iIndepFun_shallow_deep hX (wordOfDigits (A := A) (L := k))
      (fun u => length_wordOfDigits u) (wordOfDigits_injective k)).precomp
      (Option.some_injective _)
  have hindY : iIndepFun Y P :=
    hind.comp (fun _ x => D.indicator (fun _ => (1 : ℝ)) x)
      (fun _ => measurable_const.indicator hD)
  set Z : Ω → ℝ := ∑ u ∈ S, Y u with hZ
  have hZapply : ∀ ω, Z ω = ∑ u ∈ S, Y u ω := fun ω => by simp [hZ]
  have hcount : ∀ ω, ((S.filter fun u => deepVector X (wordOfDigits u) ω ∈ D).card : ℝ) = Z ω := by
    intro ω
    rw [hZapply, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [hY, Set.indicator]
  have hZmemLp : MemLp Z 2 P := by
    rw [hZ]
    exact memLp_finsetSum' S fun u _ => hYmemLp u
  have hZint : ∫ ω, Z ω ∂P = S.card * p := by
    simp_rw [hZapply]
    rw [integral_finsetSum S fun u _ => (hYmemLp u).integrable one_le_two]
    simp [hYint]
  have hvar : variance Z P ≤ S.card * p := by
    rw [hZ, IndepFun.variance_sum (fun u _ => hYmemLp u)
      (fun u _ v _ huv => hindY.indepFun huv)]
    calc ∑ u ∈ S, variance (Y u) P ≤ ∑ u ∈ S, p := by
          refine Finset.sum_le_sum fun u _ => ?_
          calc variance (Y u) P ≤ P[Y u ^ 2] :=
                variance_le_expectation_sq (hYmeas u).aestronglyMeasurable
            _ = p := hYsq u
      _ = S.card * p := by simp
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hc : 0 < p * S.card / 2 := by positivity
  have hsub : {ω | ((S.filter fun u => deepVector X (wordOfDigits u) ω ∈ D).card : ℝ) <
      p * S.card / 2} ⊆ {ω | p * S.card / 2 ≤ |Z ω - P[Z]|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, hcount] at hω ⊢
    rw [hZint]
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  refine (measure_mono hsub).trans ((meas_ge_le_variance_div_sq hZmemLp hc).trans ?_)
  refine ENNReal.ofReal_le_ofReal ?_
  have hsq : (p * S.card / 2) ^ 2 = p ^ 2 * S.card ^ 2 / 4 := by ring
  rw [hsq, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hvar, mul_pos hp hSpos]

open scoped Classical in

theorem measure_descendantCount_ge_inter_card_filter_lt_le (hX : IsPercolation P X)
    {D : Set (Configuration A)} (hD : MeasurableSet D)
    (hp : 0 < (P {ω | config X ω ∈ D}).toReal) (k : ℕ) {B : ℕ} (hB : 0 < B) :
    P {ω | B ≤ descendantCountBelow X [] k ω ∧
        (((retainedDigitWords X k ω).filter fun u => deepVector X (wordOfDigits u) ω ∈ D).card :
            ℝ) < (P {ω | config X ω ∈ D}).toReal * descendantCountBelow X [] k ω / 2} ≤
      ENNReal.ofReal (4 / ((P {ω | config X ω ∈ D}).toReal * B)) := by
  classical
  let := hX.toIsProbabilityMeasure
  set p := (P {ω | config X ω ∈ D}).toReal with hpdef
  set big := (Finset.univ : Finset (Finset (DigitWord A k))).filter fun S => B ≤ S.card with hbig
  set bad : Finset (DigitWord A k) → Set Ω := fun S =>
    {ω | ((S.filter fun u => deepVector X (wordOfDigits u) ω ∈ D).card : ℝ) < p * S.card / 2}
    with hbad
  have hsub : {ω | B ≤ descendantCountBelow X [] k ω ∧
      (((retainedDigitWords X k ω).filter fun u => deepVector X (wordOfDigits u) ω ∈ D).card :
          ℝ) < p * descendantCountBelow X [] k ω / 2} ⊆
      ⋃ S ∈ big, ({ω | retainedDigitWords X k ω = S} ∩ bad S) := by
    rintro ω ⟨hB', hlt⟩
    refine Set.mem_iUnion₂.mpr ⟨retainedDigitWords X k ω, ?_, rfl, ?_⟩
    · simp only [hbig, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [card_retainedDigitWords]
      exact hB'
    · simp only [hbad, Set.mem_ofPred_eq]
      rw [card_retainedDigitWords]
      exact hlt
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  calc _ ≤ P (⋃ S ∈ big, ({ω | retainedDigitWords X k ω = S} ∩ bad S)) := measure_mono hsub
    _ ≤ ∑ S ∈ big, P ({ω | retainedDigitWords X k ω = S} ∩ bad S) :=
        measure_biUnion_finset_le _ _
    _ = ∑ S ∈ big, P {ω | retainedDigitWords X k ω = S} * P (bad S) :=
        Finset.sum_congr rfl fun S _ => measure_retainedDigitWords_eq_inter_filter hX k S hD
          (fun T => (T.card : ℝ) < p * S.card / 2)
    _ ≤ ∑ S ∈ big, P {ω | retainedDigitWords X k ω = S} * ENNReal.ofReal (4 / (p * B)) := by
        refine Finset.sum_le_sum fun S hS => mul_le_mul_of_nonneg_left ?_ zero_le
        have hSB : B ≤ S.card := (Finset.mem_filter.mp hS).2
        have hSne : S.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hB hSB)
        refine (measure_card_filter_deep_lt_le hX hD hp S hSne).trans ?_
        refine ENNReal.ofReal_le_ofReal ?_
        have hSB' : (B : ℝ) ≤ S.card := by exact_mod_cast hSB
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_left hSB' hp.le)
    _ = (∑ S ∈ big, P {ω | retainedDigitWords X k ω = S}) * ENNReal.ofReal (4 / (p * B)) :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * ENNReal.ofReal (4 / (p * B)) := by
        gcongr
        rw [← measure_biUnion_finset]
        · exact prob_le_one
        · intro S _ S' _ hSS'
          rw [Function.onFun, Set.disjoint_left]
          intro ω h h'
          exact hSS' (h.symm.trans h')
        · exact fun S _ => measurableSet_retainedDigitWords_eq hX k S
    _ = ENNReal.ofReal (4 / (p * B)) := one_mul _

open scoped Classical in

theorem eventually_sbox_sub_le_approximateSquareRate_of_growth (hX : IsPercolation P X)
    (hm : 1 < A.m)
    (hgrowth : ∀ᵐ ω ∂P, ω ∈ survival X →
      ∃ c > 0, ∀ᶠ n : ℕ in atTop, c * A.m ^ n ≤ (descendantCountBelow X [] n ω : ℝ))
    (hproj : ∀ ε > 0, ∃ ρ > 0, ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal ρ ≤ P {ω | A.lam ^ ((1 - ε) * (n : ℝ)) ≤ (prunedColumnCount X n ω : ℝ)})
    {η : ℝ} (hη : 0 < η) :
    ∀ᵐ ω ∂P, ω ∈ survival X → ∀ᶠ a : ℕ in atTop,
      A.sbox - η ≤ approximateSquareRate X ω a := by
  let := hX.toIsProbabilityMeasure
  have hlam := A.one_le_lam hm
  have hlampos := A.lam_pos hm
  have hlogM := A.log_M_pos
  have hlogm : 0 < Real.log A.m := Real.log_pos hm
  have hloglam : 0 ≤ Real.log A.lam := Real.log_nonneg hlam
  have hΓ0 := A.Gamma_pos
  have hΓ1 := A.Gamma_lt_one
  have hs0 : 0 ≤ A.sproj := div_nonneg hloglam hlogM.le
  set ε : ℝ := min 1 (η / (2 * (A.sproj + 1))) with hεdef
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεs : ε * (1 - A.Gamma) * Real.log A.lam ≤ η / 2 * Real.log A.M := by
    have h1 : ε * A.sproj ≤ η / 2 := by
      calc ε * A.sproj ≤ η / (2 * (A.sproj + 1)) * A.sproj :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hs0
        _ ≤ η / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
    have h2 : ε * (1 - A.Gamma) * A.sproj ≤ η / 2 := by
      nlinarith [mul_nonneg (mul_nonneg hε0.le hs0) hΓ0.le]
    have h3 : ε * (1 - A.Gamma) * Real.log A.lam =
        ε * (1 - A.Gamma) * A.sproj * Real.log A.M := by
      rw [GridLaw.sproj, mul_assoc (ε * (1 - A.Gamma)), div_mul_cancel₀ _ hlogM.ne']
    rw [h3]
    exact mul_le_mul_of_nonneg_right h2 hlogM.le
  obtain ⟨ρ, hρ, hev⟩ := hproj ε hε0
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hev
  have hnge : ∀ a : ℕ, (a : ℝ) * (1 - A.Gamma) ≤ ((a - bfloor A.Gamma a : ℕ) : ℝ) := fun a => by
    rw [Nat.cast_sub (A.bfloor_le a)]
    nlinarith [bfloor_cast_le hΓ0.le a]
  set a₀ : ℕ := ⌈(n₀ : ℝ) / (1 - A.Gamma)⌉₊ with ha₀
  have hn₀le : ∀ a : ℕ, a₀ ≤ a → n₀ ≤ a - bfloor A.Gamma a := by
    intro a ha
    have h1 : (n₀ : ℝ) / (1 - A.Gamma) ≤ a := (Nat.le_ceil _).trans (by exact_mod_cast ha)
    have h2 : (n₀ : ℝ) ≤ a * (1 - A.Gamma) := by rwa [div_le_iff₀ (by linarith)] at h1
    exact Nat.cast_le.mp (h2.trans (hnge a))
  set D : ℕ → Set (Configuration A) := fun a =>
    {x | A.lam ^ ((1 - ε) * ((a - bfloor A.Gamma a : ℕ) : ℝ)) ≤
      (prunedColumnCountConfig x [] (a - bfloor A.Gamma a) : ℝ)} with hD
  have hDmeas : ∀ a, MeasurableSet (D a) := fun a =>
    measurableSet_le measurable_const
      (measurable_from_nat.comp (measurable_prunedColumnCountConfig [] _))
  have hpρ : ∀ a : ℕ, a₀ ≤ a → ρ ≤ (P {ω | config X ω ∈ D a}).toReal := by
    intro a ha
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp (hn₀ _ (hn₀le a ha))
  set bad : ℕ → Set Ω := fun a => if a₀ ≤ a then
      {ω | ⌊Real.sqrt A.m ^ bfloor A.Gamma a⌋₊ + 1 ≤
          descendantCountBelow X [] (bfloor A.Gamma a) ω ∧
        (((retainedDigitWords X (bfloor A.Gamma a) ω).filter fun u =>
            deepVector X (wordOfDigits u) ω ∈ D a).card : ℝ) <
          (P {ω | config X ω ∈ D a}).toReal * descendantCountBelow X [] (bfloor A.Gamma a) ω / 2}
      else ∅ with hbad
  have hbadle : ∀ a, P (bad a) ≤
      ENNReal.ofReal (4 / (ρ * Real.sqrt A.m ^ bfloor A.Gamma a)) := by
    intro a
    by_cases ha : a₀ ≤ a
    · rw [hbad]
      dsimp only
      rw [ite_eq_left ha]
      refine (measure_descendantCount_ge_inter_card_filter_lt_le hX (hDmeas a)
        (hρ.trans_le (hpρ a ha)) _ (B := ⌊Real.sqrt A.m ^ bfloor A.Gamma a⌋₊ + 1)
        (Nat.succ_pos _)).trans ?_
      refine ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_)
      have hBge : Real.sqrt A.m ^ bfloor A.Gamma a ≤
          ((⌊Real.sqrt A.m ^ bfloor A.Gamma a⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast
        exact (Nat.lt_floor_add_one _).le
      exact mul_le_mul (hpρ a ha) hBge (by positivity) (hρ.le.trans (hpρ a ha))
    · rw [hbad]
      dsimp only
      rw [ite_eq_right ha]
      simp
  have hsum : (∑' a, P (bad a)) ≠ ∞ :=
    ne_top_of_le_ne_top (tsum_ofReal_four_div_sqrt_pow_ne_top hm hρ hΓ0
      (g := fun a : ℕ => bfloor A.Gamma a) fun a => lt_bfloor_cast_add_one A.Gamma a)
      (ENNReal.tsum_le_tsum hbadle)
  have hbtend : Tendsto (fun a : ℕ => bfloor A.Gamma a) atTop atTop := by
    show Tendsto (fun a : ℕ => ⌊(a : ℝ) * A.Gamma⌋₊) atTop atTop
    exact tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hΓ0)
  filter_upwards [hgrowth, ae_eventually_notMem hsum] with ω hgω hnotbad hs
  obtain ⟨c, hc, hZ⟩ := hgω hs
  have hKev : ∀ᶠ a : ℕ in atTop,
      Real.log A.m - Real.log (ρ * c / 2) ≤ η / 2 * a * Real.log A.M := by
    have ht : Tendsto (fun a : ℕ => η / 2 * Real.log A.M * (a : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
    filter_upwards [ht.eventually_ge_atTop (Real.log A.m - Real.log (ρ * c / 2))] with a ha
    linarith
  filter_upwards [hnotbad, hbtend.eventually hZ,
    hbtend.eventually (eventually_floor_sqrt_pow_add_one_le hm hc),
    eventually_ge_atTop a₀, eventually_ge_atTop 1, hKev] with a habad haZ haB ha ha1 haK
  simp only [hbad, ite_eq_left ha, Set.mem_ofPred_eq, not_and, not_lt] at habad
  have hBZ : ⌊Real.sqrt A.m ^ bfloor A.Gamma a⌋₊ + 1 ≤
      descendantCountBelow X [] (bfloor A.Gamma a) ω := by
    exact_mod_cast haB.trans haZ
  have hcount := habad hBZ
  have hpa := hpρ a ha
  have hcountge : ρ * (c * A.m ^ bfloor A.Gamma a) / 2 ≤
      (((retainedDigitWords X (bfloor A.Gamma a) ω).filter fun u =>
        deepVector X (wordOfDigits u) ω ∈ D a).card : ℝ) := by
    refine le_trans ?_ hcount
    have hZ0 : 0 ≤ c * A.m ^ bfloor A.Gamma a := by positivity
    have := mul_le_mul hpa haZ hZ0 (by positivity)
    linarith
  have hdeep : ∀ u ∈ (retainedDigitWords X (bfloor A.Gamma a) ω).filter fun u =>
      deepVector X (wordOfDigits u) ω ∈ D a,
      A.lam ^ ((1 - ε) * ((a - bfloor A.Gamma a : ℕ) : ℝ)) ≤
        (prunedColumnCountBelow X (wordOfDigits u) (a - bfloor A.Gamma a) ω : ℝ) := by
    intro u hu
    have h := (Finset.mem_filter.mp hu).2
    simp only [hD, Set.mem_ofPred_eq] at h
    rw [deepVector_eq_rebase, prunedColumnCountConfig_rebase, List.append_nil] at h
    exact h
  have hcard : (((retainedDigitWords X (bfloor A.Gamma a) ω).filter fun u =>
        deepVector X (wordOfDigits u) ω ∈ D a).card : ℝ) *
        A.lam ^ ((1 - ε) * ((a - bfloor A.Gamma a : ℕ) : ℝ)) ≤
      ((limitMeetingCodes X ω a).card : ℝ) := by
    have h2 := sum_prunedColumnCountBelow_le_card_limitMeetingCodes (X := X) ω a
    calc _ = ∑ u ∈ (retainedDigitWords X (bfloor A.Gamma a) ω).filter (fun u =>
            deepVector X (wordOfDigits u) ω ∈ D a),
            A.lam ^ ((1 - ε) * ((a - bfloor A.Gamma a : ℕ) : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ u ∈ (retainedDigitWords X (bfloor A.Gamma a) ω).filter (fun u =>
            deepVector X (wordOfDigits u) ω ∈ D a),
            (prunedColumnCountBelow X (wordOfDigits u) (a - bfloor A.Gamma a) ω : ℝ) :=
          Finset.sum_le_sum hdeep
      _ ≤ ∑ u ∈ retainedDigitWords X (bfloor A.Gamma a) ω,
            (prunedColumnCountBelow X (wordOfDigits u) (a - bfloor A.Gamma a) ω : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => Nat.cast_nonneg _
      _ ≤ _ := by exact_mod_cast h2
  set e : ℝ := (1 - ε) * ((a - bfloor A.Gamma a : ℕ) : ℝ) with he
  have hY : 0 < ρ * c / 2 * A.m ^ bfloor A.Gamma a * A.lam ^ e := by positivity
  have hYle : ρ * c / 2 * A.m ^ bfloor A.Gamma a * A.lam ^ e ≤
      ((limitMeetingCodes X ω a).card : ℝ) := by
    calc ρ * c / 2 * A.m ^ bfloor A.Gamma a * A.lam ^ e =
          (ρ * (c * A.m ^ bfloor A.Gamma a) / 2) * A.lam ^ e := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcountge (by positivity)
      _ ≤ _ := hcard
  have hlogY : Real.log (ρ * c / 2 * A.m ^ bfloor A.Gamma a * A.lam ^ e) =
      Real.log (ρ * c / 2) + bfloor A.Gamma a * Real.log A.m + e * Real.log A.lam := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_rpow hlampos]
  have hb1 : (a : ℝ) * A.Gamma - 1 ≤ bfloor A.Gamma a := by
    have := lt_bfloor_cast_add_one A.Gamma a
    linarith
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha1
  rw [approximateSquareRate, le_div_iff₀ (by positivity)]
  refine le_trans ?_ (Real.log_le_log hY hYle)
  rw [hlogY]
  have h1 : ((a : ℝ) * A.Gamma - 1) * Real.log A.m ≤ bfloor A.Gamma a * Real.log A.m :=
    mul_le_mul_of_nonneg_right hb1 hlogm.le
  have h2 : (1 - ε) * ((a : ℝ) * (1 - A.Gamma)) * Real.log A.lam ≤ e * Real.log A.lam :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hnge a) (by linarith)) hloglam
  have h3 : (a : ℝ) * (ε * (1 - A.Gamma) * Real.log A.lam) ≤ a * (η / 2 * Real.log A.M) :=
    mul_le_mul_of_nonneg_left hεs hapos.le
  have h4 : (A.sbox - η) * (a * Real.log A.M) =
      a * (A.sbox * Real.log A.M) - η * a * Real.log A.M := by ring
  rw [h4, sbox_log_M_eq_gamma_log_m_add]
  linarith

theorem ae_le_liminf_approximateSquareRate_of_growth (hX : IsPercolation P X) (hm : 1 < A.m)
    (hgrowth : ∀ᵐ ω ∂P, ω ∈ survival X →
      ∃ c > 0, ∀ᶠ n : ℕ in atTop, c * A.m ^ n ≤ (descendantCountBelow X [] n ω : ℝ))
    (hproj : ∀ ε > 0, ∃ ρ > 0, ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal ρ ≤ P {ω | A.lam ^ ((1 - ε) * (n : ℝ)) ≤ (prunedColumnCount X n ω : ℝ)}) :
    ∀ᵐ ω ∂P, ω ∈ survival X → A.sbox ≤ liminf (approximateSquareRate X ω) atTop := by
  have hall : ∀ᵐ ω ∂P, ∀ j : ℕ, ω ∈ survival X → ∀ᶠ a : ℕ in atTop,
      A.sbox - 1 / ((j : ℝ) + 1) ≤ approximateSquareRate X ω a :=
    ae_all_iff.mpr fun j =>
      eventually_sbox_sub_le_approximateSquareRate_of_growth hX hm hgrowth hproj (by positivity)
  filter_upwards [hall] with ω hω hs
  have hcob : IsCoboundedUnder (· ≥ ·) atTop (approximateSquareRate X ω) :=
    isCoboundedUnder_ge_of_eventually_le atTop
      ((eventually_ge_atTop 1).mono fun a ha => approximateSquareRate_le_log_div ω ha)
  have hj : ∀ j : ℕ, A.sbox - 1 / ((j : ℝ) + 1) ≤ liminf (approximateSquareRate X ω) atTop :=
    fun j => le_liminf_of_le hcob (hω j hs)
  by_contra hlt
  obtain ⟨j, hj'⟩ := exists_nat_one_div_lt (sub_pos.mpr (not_le.mp hlt))
  linarith [hj j]

end FractalGeometry.Probability.GridPercolation
