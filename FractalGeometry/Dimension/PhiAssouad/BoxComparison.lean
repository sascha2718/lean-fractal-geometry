import Mathlib
import FractalGeometry.Dimension.PhiAssouad.BoxRate
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Dimension.PhiAssouad.DimensionFunction
import FractalGeometry.Dimension.PhiAssouad.FiniteCovers
import FractalGeometry.Dimension.PhiAssouad.PlaneBounds
import FractalGeometry.Dimension.PhiAssouad.ScaleIdentity

namespace FractalGeometry.Dimension.PhiAssouad

/-!
The upper box bound for phi-Assouad dimension, in the bounded planar case:
Corollary 2.7 of Amlan Banaji, Alex Rutar and Sascha Troscheit, "Interpolating
with generalized Assouad dimensions", Journal of Geometric Analysis 35(9)
(2025), article 270, doi:10.1007/s12220-025-02099-w, arXiv:2308.12975.
This namespace uses diameter covering counts and real-valued logarithmic limits.
-/

open Filter Topology Set

open scoped ENNReal

namespace DimFun

theorem continuousOn (φ : DimFun) : ContinuousOn φ.toFun (Ioo 0 1) := by
  intro R₀ hR₀
  have hlog : 0 < Real.log (1 / R₀) := Real.log_pos (one_lt_one_div hR₀.1 hR₀.2)
  set c : ℝ := φ.toFun R₀ * Real.log (1 / R₀) with hc
  have hgcont : ContinuousAt (fun R : ℝ => c / Real.log (1 / R)) R₀ := by
    refine continuousAt_const.div ?_ hlog.ne'
    exact (continuousAt_const.div continuousAt_id hR₀.1.ne').log
      (one_div_pos.mpr hR₀.1).ne'
  have hgval : c / Real.log (1 / R₀) = φ.toFun R₀ := by
    rw [hc]
    field_simp
  have hglim : Tendsto (fun R : ℝ => c / Real.log (1 / R)) (𝓝 R₀) (𝓝 (φ.toFun R₀)) := by
    have h := hgcont.tendsto
    rwa [hgval] at h
  have hlower : ∀ R ∈ Ioo (0 : ℝ) 1, min (φ.toFun R₀) (c / Real.log (1 / R)) ≤ φ.toFun R := by
    intro R hR
    have hlogR : 0 < Real.log (1 / R) := Real.log_pos (one_lt_one_div hR.1 hR.2)
    rcases le_total R R₀ with h | h
    · refine min_le_of_right_le ?_
      rw [div_le_iff₀ hlogR]
      exact φ.gap_mono R hR R₀ hR₀ h
    · exact min_le_of_left_le (φ.mono R₀ hR₀ R hR h)
  have hupper : ∀ R ∈ Ioo (0 : ℝ) 1, φ.toFun R ≤ max (φ.toFun R₀) (c / Real.log (1 / R)) := by
    intro R hR
    have hlogR : 0 < Real.log (1 / R) := Real.log_pos (one_lt_one_div hR.1 hR.2)
    rcases le_total R R₀ with h | h
    · exact le_max_of_le_left (φ.mono R hR R₀ hR₀ h)
    · refine le_max_of_le_right ?_
      rw [le_div_iff₀ hlogR]
      exact φ.gap_mono R₀ hR₀ R hR h
  have hev : ∀ᶠ R in 𝓝 R₀, R ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhds hR₀.1 hR₀.2
  have hlo : Tendsto (fun R => min (φ.toFun R₀) (c / Real.log (1 / R))) (𝓝 R₀)
      (𝓝 (φ.toFun R₀)) := by
    have h := (tendsto_const_nhds (x := φ.toFun R₀)).min hglim
    rwa [min_self] at h
  have hhi : Tendsto (fun R => max (φ.toFun R₀) (c / Real.log (1 / R))) (𝓝 R₀)
      (𝓝 (φ.toFun R₀)) := by
    have h := (tendsto_const_nhds (x := φ.toFun R₀)).max hglim
    rwa [max_self] at h
  have h : Tendsto φ.toFun (𝓝 R₀) (𝓝 (φ.toFun R₀)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi (hev.mono hlower) (hev.mono hupper)
  exact ContinuousAt.continuousWithinAt h

noncomputable def stepScale (φ : DimFun) (R : ℝ) : ℝ := (2 * R) ^ (1 + φ.toFun (2 * R))

noncomputable def stepGap (φ : DimFun) (R : ℝ) : ℝ := φ.toFun (2 * R) * Real.log (1 / (2 * R))

lemma stepScale_pos (φ : DimFun) {R : ℝ} (hR : 0 < R) : 0 < φ.stepScale R :=
  Real.rpow_pos_of_pos (by linarith) _

lemma stepScale_eq (φ : DimFun) {R : ℝ} (hR : 0 < R) :
    φ.stepScale R = 2 * R * Real.exp (-φ.stepGap R) := by
  have hρ : 0 < 2 * R := by linarith
  rw [stepScale, stepGap, Real.rpow_add hρ, Real.rpow_one, Real.rpow_def_of_pos hρ, one_div,
    Real.log_inv]
  ring_nf

lemma continuousOn_stepScale (φ : DimFun) {Rb : ℝ} (hRb : Rb < 1 / 2) :
    ContinuousOn φ.stepScale (Ioc 0 Rb) := by
  have hmaps : MapsTo (fun R : ℝ => 2 * R) (Ioc 0 Rb) (Ioo 0 1) :=
    fun R hR => ⟨by linarith [hR.1], by linarith [hR.2]⟩
  have hφ : ContinuousOn (fun R => φ.toFun (2 * R)) (Ioc 0 Rb) :=
    φ.continuousOn.comp (continuousOn_const.mul continuousOn_id) hmaps
  show ContinuousOn (fun R => (2 * R) ^ (1 + φ.toFun (2 * R))) (Ioc 0 Rb)
  exact (continuousOn_const.mul continuousOn_id).rpow (continuousOn_const.add hφ)
    (fun R hR => Or.inl (by linarith [hR.1] : (0 : ℝ) < 2 * R).ne')

end DimFun

lemma coverNum_ne_top_of_isBounded {X : Set (ℝ × ℝ)} (hbdd : Bornology.IsBounded X) {r : ℝ}
    (hr : 0 < r) : coverNum r X ≠ ⊤ := by
  obtain ⟨ρ, hρ⟩ := (Metric.isBounded_iff_subset_ball (0 : ℝ × ℝ)).mp hbdd
  have hsub : X ⊆ Metric.eball (0 : ℝ × ℝ) (ENNReal.ofReal (max ρ r)) := by
    intro y hy
    have h1 := hρ hy
    rw [Metric.mem_ball] at h1
    rw [Metric.mem_eball, edist_lt_ofReal]
    exact lt_of_lt_of_le h1 (le_max_left _ _)
  have h2 := coverNum_eball_le (0 : ℝ × ℝ) hr (le_max_right ρ r)
  intro htop
  have h3 : (coverNum r X : ℝ≥0∞) ≤ ENNReal.ofReal (16 * (max ρ r / r) ^ 2) :=
    (ENat.toENNReal_le.mpr (coverNum_mono hsub)).trans h2
  rw [htop, ENat.toENNReal_top] at h3
  exact ENNReal.ofReal_ne_top (top_le_iff.mp h3)

theorem coverNum_stepScale_le (φ : DimFun) {X : Set (ℝ × ℝ)} {s C R : ℝ}
    (hbound : ∀ R : ℝ, 0 < R → R < 1 → ∀ x ∈ X,
      (coverNum (R ^ (1 + φ.toFun R)) (X ∩ Metric.eball x (ENNReal.ofReal R)) : ℝ≥0∞) ≤
        ENNReal.ofReal (C * R ^ (-φ.toFun R * s)))
    (hC : 0 < C) (hR0 : 0 < R) (hR1 : 2 * R < 1) :
    (coverNum (φ.stepScale R) X : ℝ≥0∞) ≤
      (coverNum R X : ℝ≥0∞) * ENNReal.ofReal (C * (2 * R) ^ (-φ.toFun (2 * R) * s)) := by
  classical
  obtain ⟨C0, hcov, hdiam, henc⟩ := exists_isCover_encard_eq R X
  set B := ENNReal.ofReal (C * (2 * R) ^ (-φ.toFun (2 * R) * s)) with hB
  by_cases hfin : C0.Finite
  · have hsub : X ⊆ ⋃ S ∈ hfin.toFinset, X ∩ S := by
      intro y hy
      obtain ⟨S, hS, hyS⟩ := hcov hy
      exact Set.mem_iUnion₂.mpr ⟨S, hfin.mem_toFinset.mpr hS, hy, hyS⟩
    have h1 : coverNum (φ.stepScale R) X ≤
        ∑ S ∈ hfin.toFinset, coverNum (φ.stepScale R) (X ∩ S) :=
      (coverNum_mono hsub).trans (coverNum_biUnion_le _ _ _)
    have hterm : ∀ S ∈ hfin.toFinset, (coverNum (φ.stepScale R) (X ∩ S) : ℝ≥0∞) ≤ B := by
      intro S hS
      rcases (X ∩ S).eq_empty_or_nonempty with he | ⟨x, hxX, hxS⟩
      · rw [he]
        have h0 : coverNum (φ.stepScale R) (∅ : Set (ℝ × ℝ)) ≤ 0 := by
          refine le_trans (coverNum_le_of_isCover (C := (∅ : Set (Set (ℝ × ℝ)))) (by simp)
            (fun T hT => absurd hT (Set.notMem_empty _))) ?_
          simp
        refine le_trans (ENat.toENNReal_le.mpr h0) ?_
        simp
      · have hsubS : X ∩ S ⊆ X ∩ Metric.eball x (ENNReal.ofReal (2 * R)) := by
          rintro y ⟨hyX, hyS⟩
          refine ⟨hyX, ?_⟩
          rw [Metric.mem_eball]
          calc edist y x ≤ Metric.ediam S := Metric.edist_le_ediam_of_mem hyS hxS
            _ ≤ ENNReal.ofReal R := hdiam S (hfin.mem_toFinset.mp hS)
            _ < ENNReal.ofReal (2 * R) :=
                (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
        calc (coverNum (φ.stepScale R) (X ∩ S) : ℝ≥0∞)
            ≤ (coverNum (φ.stepScale R) (X ∩ Metric.eball x (ENNReal.ofReal (2 * R))) :
                ℝ≥0∞) := ENat.toENNReal_le.mpr (coverNum_mono hsubS)
          _ ≤ B := hbound (2 * R) (by linarith) hR1 x hxX
    calc (coverNum (φ.stepScale R) X : ℝ≥0∞)
        ≤ ((∑ S ∈ hfin.toFinset, coverNum (φ.stepScale R) (X ∩ S) : ℕ∞) : ℝ≥0∞) :=
          ENat.toENNReal_le.mpr h1
      _ = ∑ S ∈ hfin.toFinset, (coverNum (φ.stepScale R) (X ∩ S) : ℝ≥0∞) :=
          toENNReal_finset_sum _ _
      _ ≤ ∑ _S ∈ hfin.toFinset, B := Finset.sum_le_sum hterm
      _ = (hfin.toFinset.card : ℝ≥0∞) * B := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = (coverNum R X : ℝ≥0∞) * B := by
          rw [← henc, hfin.encard_eq_coe_toFinset_card]
          simp
  · have hinf : coverNum R X = ⊤ := by
      rw [← henc]
      exact Set.encard_eq_top_iff.mpr hfin
    have hB0 : B ≠ 0 := by
      rw [hB, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact mul_pos hC (Real.rpow_pos_of_pos (by linarith) _)
    rw [hinf, ENat.toENNReal_top, ENNReal.top_mul hB0]
    exact le_top

lemma iterate_mem_Ioc {h : ℝ → ℝ} {Rb : ℝ} (hpos : ∀ R ∈ Ioc 0 Rb, 0 < h R)
    (hhalf : ∀ R ∈ Ioc 0 Rb, h R ≤ R / 2) {R : ℝ} (hR : R ∈ Ioc 0 Rb) :
    ∀ n : ℕ, h^[n] R ∈ Ioc 0 Rb
  | 0 => hR
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      have hy := iterate_mem_Ioc hpos hhalf hR n
      exact ⟨hpos _ hy, (hhalf _ hy).trans (by linarith [hy.1, hy.2])⟩

theorem coverNum_iterate_le {h : ℝ → ℝ} {F : ℝ → ℝ≥0∞} {Rb t : ℝ}
    (hpos : ∀ R ∈ Ioc 0 Rb, 0 < h R) (hhalf : ∀ R ∈ Ioc 0 Rb, h R ≤ R / 2)
    (hstep : ∀ R ∈ Ioc 0 Rb, F (h R) ≤ F R * ENNReal.ofReal ((R / h R) ^ t))
    {R₀ : ℝ} (hR₀ : R₀ ∈ Ioc 0 Rb) (n : ℕ) :
    F (h^[n] R₀) ≤ F R₀ * ENNReal.ofReal ((R₀ / h^[n] R₀) ^ t) := by
  induction n with
  | zero =>
      simp [div_self hR₀.1.ne']
  | succ n ih =>
      have hy := iterate_mem_Ioc hpos hhalf hR₀ n
      have hhy := hpos _ hy
      rw [Function.iterate_succ_apply']
      calc F (h (h^[n] R₀))
          ≤ F (h^[n] R₀) * ENNReal.ofReal ((h^[n] R₀ / h (h^[n] R₀)) ^ t) := hstep _ hy
        _ ≤ F R₀ * ENNReal.ofReal ((R₀ / h^[n] R₀) ^ t) *
              ENNReal.ofReal ((h^[n] R₀ / h (h^[n] R₀)) ^ t) := by gcongr
        _ = F R₀ * ENNReal.ofReal ((R₀ / h (h^[n] R₀)) ^ t) := by
            rw [mul_assoc, ← ENNReal.ofReal_mul
                (Real.rpow_nonneg (div_pos hR₀.1 hy.1).le _),
              ← Real.mul_rpow (div_pos hR₀.1 hy.1).le (div_pos hy.1 hhy).le]
            congr 3
            field_simp [hy.1.ne', hhy.ne']

theorem exists_iterate_eq {h : ℝ → ℝ} {Rb : ℝ} (hRb : 0 < Rb)
    (hpos : ∀ R ∈ Ioc 0 Rb, 0 < h R) (hhalf : ∀ R ∈ Ioc 0 Rb, h R ≤ R / 2)
    (hcont : ContinuousOn h (Ioc 0 Rb)) {r : ℝ} (hr0 : 0 < r) (hr : r ≤ h Rb) :
    ∃ R₀ ∈ Icc (h Rb) Rb, ∃ n : ℕ, h^[n] R₀ = r := by
  classical
  have hRbI : Rb ∈ Ioc 0 Rb := ⟨hRb, le_rfl⟩
  have hmem := iterate_mem_Ioc hpos hhalf hRbI
  have hdecay : ∀ n : ℕ, h^[n] Rb ≤ Rb / 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', pow_succ, ← div_div]
        calc h (h^[n] Rb) ≤ h^[n] Rb / 2 := hhalf _ (hmem n)
          _ ≤ Rb / 2 ^ n / 2 := by linarith
  have hcontn : ∀ n : ℕ, ContinuousOn (h^[n]) (Ioc 0 Rb) := by
    intro n
    induction n with
    | zero => exact continuousOn_id
    | succ n ih =>
        rw [Function.iterate_succ']
        exact hcont.comp ih (fun R hR => iterate_mem_Ioc hpos hhalf hR n)
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (Rb / r) (one_lt_two : (1 : ℝ) < 2)
  have hex : ∃ n : ℕ, h^[n + 1] Rb < r := by
    have h1 : Rb / 2 ^ N < r := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hr0] at hN
      linarith
    have h2 : Rb / 2 ^ (N + 1) ≤ Rb / 2 ^ N := by
      rw [pow_succ, ← div_div]
      linarith [div_pos hRb (by positivity : (0 : ℝ) < 2 ^ N)]
    exact ⟨N, (hdecay (N + 1)).trans_lt (h2.trans_lt h1)⟩
  have hnlt : h^[Nat.find hex + 1] Rb < r := Nat.find_spec hex
  have hnge : r ≤ h^[Nat.find hex] Rb := by
    rcases hk : Nat.find hex with _ | m
    · simp only [Function.iterate_zero, id_eq]
      linarith [hhalf Rb hRbI]
    · have hmin := Nat.find_min hex (show m < Nat.find hex by omega)
      exact not_lt.mp hmin
  set n := Nat.find hex
  have hab : h Rb ≤ Rb := (hhalf Rb hRbI).trans (by linarith)
  have hsubI : Icc (h Rb) Rb ⊆ Ioc 0 Rb :=
    fun R hR => ⟨lt_of_lt_of_le (hpos Rb hRbI) hR.1, hR.2⟩
  have hrmem : r ∈ Icc (h^[n] (h Rb)) (h^[n] Rb) := by
    refine ⟨?_, hnge⟩
    rw [← Function.iterate_succ_apply]
    exact hnlt.le
  obtain ⟨R₀, hR₀, hR₀eq⟩ := intermediate_value_Icc hab ((hcontn n).mono hsubI) hrmem
  exact ⟨R₀, hR₀, n, hR₀eq⟩

theorem upperBoxDim_le_dimAphi (φ : DimFun) {X : Set (ℝ × ℝ)} (hbdd : Bornology.IsBounded X) :
    upperBoxDim X ≤ dimAphi φ.toFun X := by
  classical
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set δ : ℝ := ε / 3 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨s, hsmem, hslt⟩ := exists_lt_of_csInf_lt (phiAssouadExponents_nonempty φ X)
    (show sInf (PhiAssouadExponents φ.toFun X) < dimAphi φ.toFun X + δ from
      lt_add_of_pos_right _ hδ0)
  obtain ⟨hs0, C, hC, hbound⟩ := hsmem
  set t : ℝ := s + δ with ht
  have ht0 : 0 ≤ t := by linarith

  have htwo : Tendsto (fun R : ℝ => 2 * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h := (tendsto_const_nhds (x := (2 : ℝ))).mul (tendsto_id (x := 𝓝 (0 : ℝ)))
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with R hR
      exact mul_pos two_pos (Set.mem_Ioi.mp hR)
  have hgap : Tendsto φ.stepGap (𝓝[>] 0) atTop := φ.gap_tendsto.comp htwo
  have hev : ∀ᶠ R in 𝓝[>] (0 : ℝ), R < 1 / 4 ∧ Real.log 4 ≤ φ.stepGap R ∧
      Real.log (C * 2 ^ t) / δ ≤ φ.stepGap R := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num),
      hgap.eventually_ge_atTop (Real.log 4),
      hgap.eventually_ge_atTop (Real.log (C * 2 ^ t) / δ)] with R hR h1 h2
    exact ⟨hR.2, h1, h2⟩
  obtain ⟨Rb, hRb0, hRbsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hev
  have hRb0' : 0 < Rb := hRb0
  have hprop : ∀ R ∈ Ioc 0 Rb, R < 1 / 4 ∧ Real.log 4 ≤ φ.stepGap R ∧
      Real.log (C * 2 ^ t) / δ ≤ φ.stepGap R := fun R hR => hRbsub hR
  have hRbI : Rb ∈ Ioc 0 Rb := ⟨hRb0', le_rfl⟩
  have hRb14 : Rb < 1 / 4 := (hprop Rb hRbI).1
  have hposI : ∀ R ∈ Ioc 0 Rb, 0 < φ.stepScale R := fun R hR => φ.stepScale_pos hR.1
  have hhalfI : ∀ R ∈ Ioc 0 Rb, φ.stepScale R ≤ R / 2 := by
    intro R hR
    obtain ⟨-, hg4, -⟩ := hprop R hR
    rw [φ.stepScale_eq hR.1]
    have hexp : Real.exp (-φ.stepGap R) ≤ 1 / 4 := by
      calc Real.exp (-φ.stepGap R) ≤ Real.exp (-Real.log 4) := Real.exp_le_exp.mpr (by linarith)
        _ = 1 / 4 := by
            rw [Real.exp_neg, Real.exp_log (by norm_num)]
            norm_num
    nlinarith [hR.1]
  have hstep : ∀ R ∈ Ioc 0 Rb, (coverNum (φ.stepScale R) X : ℝ≥0∞) ≤
      (coverNum R X : ℝ≥0∞) * ENNReal.ofReal ((R / φ.stepScale R) ^ t) := by
    intro R hR
    obtain ⟨hR14, -, hgC⟩ := hprop R hR
    have hρ : 0 < 2 * R := by linarith [hR.1]
    refine (coverNum_stepScale_le φ hbound hC hR.1 (by linarith)).trans ?_
    gcongr
    have hq : R / φ.stepScale R = Real.exp (φ.stepGap R) / 2 := by
      rw [φ.stepScale_eq hR.1, Real.exp_neg]
      field_simp [hR.1.ne']
    have hform : (2 * R) ^ (-φ.toFun (2 * R) * s) = Real.exp (s * φ.stepGap R) := by
      rw [phi_rpow_eq_exp_gap φ hρ]
      rfl
    rw [hform, hq, Real.div_rpow (Real.exp_pos _).le (by norm_num), ← Real.exp_mul,
      le_div_iff₀ (Real.rpow_pos_of_pos two_pos t)]
    have hC2 : C * 2 ^ t ≤ Real.exp (δ * φ.stepGap R) := by
      have hlog := (div_le_iff₀ hδ0).mp hgC
      calc C * 2 ^ t = Real.exp (Real.log (C * 2 ^ t)) :=
            (Real.exp_log (mul_pos hC (Real.rpow_pos_of_pos two_pos t))).symm
        _ ≤ Real.exp (δ * φ.stepGap R) := Real.exp_le_exp.mpr (by linarith)
    calc C * Real.exp (s * φ.stepGap R) * 2 ^ t
        = Real.exp (s * φ.stepGap R) * (C * 2 ^ t) := by ring
      _ ≤ Real.exp (s * φ.stepGap R) * Real.exp (δ * φ.stepGap R) :=
          mul_le_mul_of_nonneg_left hC2 (Real.exp_pos _).le
      _ = Real.exp (φ.stepGap R * t) := by
          rw [← Real.exp_add, ht]
          ring_nf
  have hcontI := φ.continuousOn_stepScale (by linarith : Rb < 1 / 2)
  have hKtop : coverNum (φ.stepScale Rb) X ≠ ⊤ :=
    coverNum_ne_top_of_isBounded hbdd (hposI Rb hRbI)
  set k₀ : ℕ := (coverNum (φ.stepScale Rb) X).toNat with hk₀
  have hK : coverNum (φ.stepScale Rb) X = (k₀ : ℕ∞) := (ENat.natCast_toNat hKtop).symm

  have hcovr : ∀ r ∈ Ioc 0 (φ.stepScale Rb),
      ((coverNum r X).toNat : ℝ) ≤ k₀ * (1 / r) ^ t := by
    intro r hr
    obtain ⟨R₀, hR₀, n, hn⟩ := exists_iterate_eq hRb0' hposI hhalfI hcontI hr.1 hr.2
    have hR₀I : R₀ ∈ Ioc 0 Rb := ⟨lt_of_lt_of_le (hposI Rb hRbI) hR₀.1, hR₀.2⟩
    have hchain := coverNum_iterate_le (F := fun R => (coverNum R X : ℝ≥0∞))
      hposI hhalfI hstep hR₀I n
    beta_reduce at hchain
    rw [hn] at hchain
    have h1 : (coverNum r X : ℝ≥0∞) ≤ (k₀ : ℝ≥0∞) * ENNReal.ofReal ((1 / r) ^ t) := by
      refine hchain.trans (mul_le_mul' ?_ (ENNReal.ofReal_le_ofReal ?_))
      · calc (coverNum R₀ X : ℝ≥0∞) ≤ (coverNum (φ.stepScale Rb) X : ℝ≥0∞) :=
              ENat.toENNReal_le.mpr (coverNum_anti hR₀.1)
          _ = (k₀ : ℝ≥0∞) := by rw [hK, ENat.toENNReal_coe]
      · exact Real.rpow_le_rpow (div_pos hR₀I.1 hr.1).le
          (div_le_div_of_nonneg_right (by linarith [hR₀I.2]) hr.1.le) ht0
    have hrtop : coverNum r X ≠ ⊤ := coverNum_ne_top_of_isBounded hbdd hr.1
    rw [← ENat.natCast_toNat hrtop, ENat.toENNReal_coe,
      ← ENNReal.ofReal_natCast ((coverNum r X).toNat), ← ENNReal.ofReal_natCast k₀,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Nat.cast_nonneg _)
      (Real.rpow_nonneg (one_div_pos.mpr hr.1).le _))).mp h1

  have hlogtend : Tendsto (fun r : ℝ => Real.log (1 / r)) (𝓝[>] 0) atTop := by
    refine (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    simp [one_div, Real.log_inv]
  have hrate : ∀ᶠ r in 𝓝[>] (0 : ℝ), boxCoverRate X r ≤ t + δ := by
    filter_upwards [Ioo_mem_nhdsGT (hposI Rb hRbI), Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1),
      hlogtend.eventually_ge_atTop (Real.log k₀ / δ)] with r hrI hr1 hlogk
    have hlogpos : 0 < Real.log (1 / r) := Real.log_pos (one_lt_one_div hr1.1 hr1.2)
    have hb := hcovr r ⟨hrI.1, hrI.2.le⟩
    rw [boxCoverRate, div_le_iff₀ hlogpos]
    rcases Nat.eq_zero_or_pos (coverNum r X).toNat with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      positivity
    · have hn1 : (1 : ℝ) ≤ (coverNum r X).toNat := by exact_mod_cast hpos
      have hy : 0 < (1 / r) ^ t := Real.rpow_pos_of_pos (one_div_pos.mpr hrI.1) _
      have hk0 : (0 : ℝ) < k₀ := by
        rcases Nat.eq_zero_or_pos k₀ with hk | hk
        · rw [hk, Nat.cast_zero, zero_mul] at hb
          linarith
        · exact_mod_cast hk
      have hlogk' : Real.log k₀ ≤ δ * Real.log (1 / r) := by
        rw [div_le_iff₀ hδ0] at hlogk
        linarith
      calc Real.log (coverNum r X).toNat ≤ Real.log (k₀ * (1 / r) ^ t) :=
            Real.log_le_log (by linarith) hb
        _ = Real.log k₀ + t * Real.log (1 / r) := by
            rw [Real.log_mul hk0.ne' hy.ne', Real.log_rpow (one_div_pos.mpr hrI.1)]
        _ ≤ (t + δ) * Real.log (1 / r) := by nlinarith
  have hcob : IsCoboundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ)) (boxCoverRate X) := by
    refine IsCoboundedUnder.of_frequently_ge (a := 0) (Eventually.frequently ?_)
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with r hr
    exact div_nonneg (Real.log_natCast_nonneg _) (Real.log_pos (one_lt_one_div hr.1 hr.2)).le
  calc upperBoxDim X ≤ t + δ := limsup_le_of_le hcob hrate
    _ < dimAphi φ.toFun X + ε := by
        have : dimAphi φ.toFun X = sInf (PhiAssouadExponents φ.toFun X) := rfl
        rw [ht, hδ] at *
        linarith

end FractalGeometry.Dimension.PhiAssouad
