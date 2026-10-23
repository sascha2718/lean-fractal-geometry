/-
# Section 3.1: Comparison of Hausdorff measure with local ball masses

Proposition 3.5, which bounds Hausdorff measure by the upper density of a measure. It holds for
every measure on a metric space and every set.

The proof works with Mathlib's auxiliary outer measures `MeasureTheory.OuterMeasure.mkMetric'.pre`,
whose supremum over positive scales is `μH[s]`; part (2) uses `hausdorff_vitali`.

| Notes | Lean declaration | Location |
|---|---|---|
| Proposition 3.5 (density comparison) | `density_comparison` | here |
| Exercise 3.6 | part (1) of `density_comparison` | here |
-/
import GeometricMeasureTheory.Covering.HausdorffVitali

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- At every positive scale, the auxiliary outer measure `mkMetric'.pre` is below `μH[s]`. -/
private theorem pre_le_hausdorffMeasure (s : ℝ) {r : ℝ≥0∞} (hr : 0 < r) (A : Set X) :
    OuterMeasure.mkMetric'.pre (fun U : Set X => ediam U ^ s) r A ≤ μH[s] A := by
  rw [Measure.hausdorffMeasure, ← OuterMeasure.coe_mkMetric, OuterMeasure.mkMetric,
    OuterMeasure.mkMetric', OuterMeasure.iSup_apply]
  refine le_iSup_of_le r ?_
  rw [OuterMeasure.iSup_apply]
  exact le_iSup_of_le hr le_rfl

/-- A bound on `mkMetric'.pre` at every positive scale bounds `μH[s]`. -/
private theorem hausdorffMeasure_le_of_forall_pre_le (s : ℝ) (A : Set X) {B : ℝ≥0∞}
    (h : ∀ r : ℝ≥0∞, 0 < r →
      OuterMeasure.mkMetric'.pre (fun U : Set X => ediam U ^ s) r A ≤ B) :
    μH[s] A ≤ B := by
  rw [Measure.hausdorffMeasure, ← OuterMeasure.coe_mkMetric, OuterMeasure.mkMetric,
    OuterMeasure.mkMetric', OuterMeasure.iSup_apply]
  refine iSup_le fun r => ?_
  rw [OuterMeasure.iSup_apply]
  exact iSup_le fun hr => h r hr

/-- If `a ≤ c' * b` for every `c' > c`, then `a ≤ c * b`. -/
private theorem le_mul_of_forall_nnreal_gt {a b : ℝ≥0∞} {c : ℝ≥0} (hc : c ≠ 0)
    (h : ∀ c' : ℝ≥0, c < c' → a ≤ c' * b) : a ≤ c * b := by
  refine ENNReal.le_mul_of_forall_lt (Or.inl (ENNReal.coe_ne_zero.2 hc))
    (Or.inl ENNReal.coe_ne_top) fun a' ha' b' hb' => ?_
  rcases eq_or_ne a' ⊤ with rfl | ha'top
  · rw [ENNReal.top_mul (zero_le.trans_lt hb').ne']
    exact le_top
  · lift a' to ℝ≥0 using ha'top
    exact (h a' (ENNReal.coe_lt_coe.1 ha')).trans (by gcongr)

/-- If `c' * b ≤ a` for every `0 < c' < c`, then `c * b ≤ a`. -/
private theorem mul_le_of_forall_nnreal_lt {a b : ℝ≥0∞} {c : ℝ≥0}
    (h : ∀ c' : ℝ≥0, 0 < c' → c' < c → (c' : ℝ≥0∞) * b ≤ a) : c * b ≤ a := by
  refine ENNReal.mul_le_of_forall_lt fun a' ha' b' hb' => ?_
  lift a' to ℝ≥0 using ne_top_of_lt ha'
  rcases eq_or_ne a' 0 with rfl | ha'0
  · simp
  · exact (by gcongr : (a' : ℝ≥0∞) * b' ≤ a' * b).trans
      (h a' (pos_iff_ne_zero.2 ha'0) (ENNReal.coe_lt_coe.1 ha'))

omit [BorelSpace X] in
/-- If the balls centred at a point `x ∈ U` with radii below `R` have mass at most `c' r ^ s`, and
`diam U < R`, then `μ U ≤ c' (diam U) ^ s`. -/
private theorem measure_le_mul_ediam_rpow (μ : Measure X) {s : ℝ} {c' : ℝ≥0} {R : ℝ} {x : X}
    (hx : ∀ r, 0 < r → r < R → μ (ball x r) ≤ c' * ENNReal.ofReal r ^ s) {U : Set X}
    (hxU : x ∈ U) (hUtop : ediam U ≠ ⊤) (hUR : (ediam U).toReal < R) :
    μ U ≤ c' * ediam U ^ s := by
  have hsub : ∀ η, 0 < η → U ⊆ ball x ((ediam U).toReal + η) := by
    intro η hη y hy
    rw [mem_ball, dist_edist]
    exact (ENNReal.toReal_mono hUtop (edist_le_ediam_of_mem hy hxU)).trans_lt
      (lt_add_of_pos_right _ hη)
  have hcont : Continuous fun η : ℝ => ENNReal.ofReal ((ediam U).toReal + η) ^ s :=
    ENNReal.continuous_rpow_const.comp
      (ENNReal.continuous_ofReal.comp (continuous_const.add continuous_id))
  have hlim := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simp only [add_zero, ENNReal.ofReal_toReal hUtop] at hlim
  refine ge_of_tendsto (ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.coe_ne_top)) ?_
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hUR)] with η hη
  have hd0 : 0 ≤ (ediam U).toReal := ENNReal.toReal_nonneg
  exact (measure_mono (hsub η hη.1)).trans
    (hx _ (by linarith [hη.1]) (by linarith [hη.2]))

/-- Proposition 3.5 (`thm:density-comparison`): (1) if `limsup_{r → 0} μ(B(x, r)) / r^s ≤ c` on `E`,
then `𝓗^s(E) ≥ μ(E) / c`; (2) if `limsup_{r → 0} μ(B(x, r)) / r^s ≥ c` on `E`, then
`𝓗^s(E) ≤ 2^s μ(X) / c`. -/
theorem density_comparison (μ : Measure X) {s : ℝ} (hs : 0 < s) (E : Set X) {c : ℝ≥0}
    (hc : c ≠ 0) :
    ((∀ x ∈ E, limsup (fun r : ℝ => μ (ball x r) / ENNReal.ofReal r ^ s) (𝓝[>] 0) ≤ c) →
        μ E / c ≤ μH[s] E) ∧
      ((∀ x ∈ E, (c : ℝ≥0∞) ≤ limsup (fun r : ℝ => μ (ball x r) / ENNReal.ofReal r ^ s) (𝓝[>] 0)) →
        μH[s] E ≤ 2 ^ s * μ univ / c) := by
  have hc0 : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hc
  have hpow0 : ∀ r : ℝ, 0 < r → ENNReal.ofReal r ^ s ≠ 0 := fun r hr =>
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hr) ENNReal.ofReal_ne_top).ne'
  have hpowtop : ∀ r : ℝ, ENNReal.ofReal r ^ s ≠ ⊤ := fun r =>
    ENNReal.rpow_ne_top_of_nonneg hs.le ENNReal.ofReal_ne_top
  constructor
  · intro hE
    rw [ENNReal.div_le_iff hc0 ENNReal.coe_ne_top, mul_comm]
    refine le_mul_of_forall_nnreal_gt hc fun c' hcc' => ?_
    have hc'0 : (c' : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 (zero_le.trans_lt hcc').ne'
    let F : ℕ → Set X := fun n => {x | x ∈ E ∧ ∀ r : ℝ, 0 < r → r < 1 / ((n : ℝ) + 1) →
      μ (ball x r) ≤ c' * ENNReal.ofReal r ^ s}
    have hFmono : Monotone F := by
      intro n m hnm x hx
      refine ⟨hx.1, fun r hr hrm => hx.2 r hr (hrm.trans_le ?_)⟩
      gcongr
    have hEF : E ⊆ ⋃ n, F n := by
      intro x hx
      have hev := eventually_lt_of_limsup_lt ((hE x hx).trans_lt (ENNReal.coe_lt_coe.2 hcc'))
      obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < u from hu)
      refine mem_iUnion.2 ⟨n, hx, fun r hr hrn => ?_⟩
      exact ((ENNReal.div_lt_iff (Or.inl (hpow0 r hr)) (Or.inl (hpowtop r))).1
        (hsub ⟨hr, hrn.trans hn⟩)).le
    have hF : ∀ n, μ (F n) ≤ c' * μH[s] E := by
      intro n
      have hr0 : 0 < ENNReal.ofReal (1 / ((n : ℝ) + 2)) := ENNReal.ofReal_pos.2 (by positivity)
      have hle : (c'⁻¹ : ℝ≥0∞) • OuterMeasure.restrict (F n) μ.toOuterMeasure ≤
          OuterMeasure.mkMetric'.pre (fun U : Set X => ediam U ^ s)
            (ENNReal.ofReal (1 / ((n : ℝ) + 2))) := by
        refine OuterMeasure.mkMetric'.le_pre.2 fun U hU => ?_
        simp only [smul_apply, OuterMeasure.restrict_apply,
          Measure.coe_toOuterMeasure, smul_eq_mul]
        rw [ENNReal.inv_mul_le_iff hc'0 ENNReal.coe_ne_top]
        rcases (U ∩ F n).eq_empty_or_nonempty with h | ⟨x, hxU, hxF⟩
        · simp [h]
        · have hUtop : ediam U ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hU
          refine (measure_mono inter_subset_left).trans
            (measure_le_mul_ediam_rpow μ hxF.2 hxU hUtop ?_)
          calc (ediam U).toReal ≤ 1 / ((n : ℝ) + 2) :=
                ENNReal.toReal_le_of_le_ofReal (by positivity) hU
            _ < 1 / ((n : ℝ) + 1) := by gcongr; linarith
      have h := hle (F n)
      simp only [smul_apply, OuterMeasure.restrict_apply,
        Measure.coe_toOuterMeasure, smul_eq_mul, inter_self] at h
      rw [ENNReal.inv_mul_le_iff hc'0 ENNReal.coe_ne_top] at h
      have hH : OuterMeasure.mkMetric'.pre (fun U : Set X => ediam U ^ s)
          (ENNReal.ofReal (1 / ((n : ℝ) + 2))) (F n) ≤ μH[s] E :=
        (pre_le_hausdorffMeasure s hr0 _).trans (measure_mono fun x hx => hx.1)
      exact h.trans (by gcongr)
    calc μ E ≤ μ (⋃ n, F n) := measure_mono hEF
      _ = ⨆ n, μ (F n) := hFmono.measure_iUnion
      _ ≤ c' * μH[s] E := iSup_le hF
  · intro hE
    rcases eq_or_ne (μ univ) ⊤ with htop | htop
    · have h2 : (2 : ℝ≥0∞) ^ s ≠ 0 := (ENNReal.rpow_pos two_pos ENNReal.ofNat_ne_top).ne'
      rw [htop, ENNReal.mul_top h2, ENNReal.top_div_of_ne_top ENNReal.coe_ne_top]
      exact le_top
    rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl ENNReal.coe_ne_top), mul_comm]
    refine mul_le_of_forall_nnreal_lt fun c' hc'0 hc'c => ?_
    have hc'0' : (c' : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hc'0.ne'
    rw [mul_comm, ← ENNReal.le_div_iff_mul_le (Or.inl hc'0') (Or.inl ENNReal.coe_ne_top)]
    refine hausdorffMeasure_le_of_forall_pre_le s E fun r hr => ?_
    obtain ⟨δ, -, hδ0, hδr⟩ := ENNReal.lt_iff_exists_real_btwn.1 hr
    have hδ : 0 < δ := ENNReal.ofReal_pos.1 hδ0
    refine (OuterMeasure.mkMetric'.mono_pre _ hδr.le E).trans ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl hc'0') (Or.inl ENNReal.coe_ne_top)]
    let t : Set (X × ℝ) := {p | p.1 ∈ E ∧ 0 < p.2 ∧ p.2 < δ / 2 ∧
      (c' : ℝ≥0∞) * ENNReal.ofReal p.2 ^ s ≤ μ (ball p.1 p.2)}
    have hfine : ∀ x ∈ E, ∀ ε : ℝ, 0 < ε →
        ∃ i ∈ t, x ∈ closedBall (Prod.fst i) (Prod.snd i) ∧ Prod.snd i < ε := by
      intro x hx ε hε
      have hfreq := frequently_lt_of_lt_limsup
        (h := (ENNReal.coe_lt_coe.2 hc'c).trans_le (hE x hx))
      obtain ⟨ρ, hρ, hρI⟩ :=
        (hfreq.and_eventually (Ioo_mem_nhdsGT (lt_min hε (half_pos hδ)))).exists
      refine ⟨(x, ρ), ⟨hx, hρI.1, hρI.2.trans_le (min_le_right _ _), ?_⟩,
        mem_closedBall_self hρI.1.le, hρI.2.trans_le (min_le_left _ _)⟩
      exact ((ENNReal.lt_div_iff_mul_lt (Or.inl (hpow0 ρ hρI.1)) (Or.inl (hpowtop ρ))).1 hρ).le
    obtain ⟨u, hut, hu, hdisj, hnull⟩ :=
      hausdorff_vitali hs t Prod.fst Prod.snd (fun i hi => hi.2.1) E hfine
    set B : Set X := ⋃ i ∈ u, closedBall (Prod.fst i) (Prod.snd i) with hB
    set S : ℝ≥0∞ := ∑' i : u, ENNReal.ofReal (i : X × ℝ).2 ^ s with hS
    have hSle : (c' : ℝ≥0∞) * S ≤ μ univ := by
      calc (c' : ℝ≥0∞) * S = ∑' i : u, (c' : ℝ≥0∞) * ENNReal.ofReal (i : X × ℝ).2 ^ s :=
            ENNReal.tsum_mul_left.symm
        _ ≤ ∑' i : u, μ (closedBall (i : X × ℝ).1 (i : X × ℝ).2) :=
            ENNReal.tsum_le_tsum fun i =>
              (hut i.2).2.2.2.trans (measure_mono ball_subset_closedBall)
        _ = μ B := (measure_biUnion hu hdisj fun _ _ => measurableSet_closedBall).symm
        _ ≤ μ univ := measure_mono (subset_univ _)
    have hSne : S ≠ ⊤ := by
      intro h
      rw [h, ENNReal.mul_top hc'0'] at hSle
      exact htop (top_le_iff.1 hSle)
    have hN : μH[s] (E \ B) = 0 := hnull.resolve_right hSne
    set p := OuterMeasure.mkMetric'.pre (fun U : Set X => ediam U ^ s) (ENNReal.ofReal δ)
      with hp
    have hpN : p (E \ B) = 0 :=
      le_antisymm ((pre_le_hausdorffMeasure s hδ0 _).trans hN.le) zero_le
    have hpB : p B ≤ 2 ^ s * S := by
      calc p B ≤ ∑' i : u, p (closedBall (i : X × ℝ).1 (i : X × ℝ).2) := measure_biUnion_le p hu _
        _ ≤ ∑' i : u, 2 ^ s * ENNReal.ofReal (i : X × ℝ).2 ^ s := by
          refine ENNReal.tsum_le_tsum fun i => ?_
          have hi := hut i.2
          have hdiam : ediam (closedBall (i : X × ℝ).1 (i : X × ℝ).2) ≤
              2 * ENNReal.ofReal (i : X × ℝ).2 := by
            rw [← closedEBall_ofReal hi.2.1.le]
            exact ediam_closedEBall_le
          have hdiamδ : 2 * ENNReal.ofReal (i : X × ℝ).2 ≤ ENNReal.ofReal δ := by
            rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
            exact ENNReal.ofReal_le_ofReal (by linarith [hi.2.2.1])
          refine (OuterMeasure.mkMetric'.pre_le (hdiam.trans hdiamδ)).trans ?_
          rw [← ENNReal.mul_rpow_of_nonneg _ _ hs.le]
          exact ENNReal.rpow_le_rpow hdiam hs.le
        _ = 2 ^ s * S := ENNReal.tsum_mul_left
    calc p E * c' ≤ (p B + p (E \ B)) * c' := by
          gcongr
          exact (measure_mono (sdiff_subset_iff.1 subset_rfl)).trans (measure_union_le _ _)
      _ ≤ 2 ^ s * S * c' := by rw [hpN, add_zero]; gcongr
      _ = 2 ^ s * (c' * S) := by ring
      _ ≤ 2 ^ s * μ univ := by gcongr

end GeometricMeasureTheory
