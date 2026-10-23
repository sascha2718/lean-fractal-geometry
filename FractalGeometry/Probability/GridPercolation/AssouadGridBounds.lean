import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Assouad
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Dimension.PhiAssouad.FiniteCovers
import FractalGeometry.Dimension.PhiAssouad.PlaneRectangles
import FractalGeometry.Probability.GridPercolation.ApproxSquares
import FractalGeometry.Probability.GridPercolation.GridCoveringReduction
import FractalGeometry.Probability.GridPercolation.LocalCoveringScales

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open Set

open scoped ENNReal

variable {E : Type*} [PseudoEMetricSpace E]

noncomputable def gridCell (M a : ℕ) (p : ℕ × ℕ) : Set (ℝ × ℝ) :=
  Set.Icc ((p.1 : ℝ) / (M : ℝ) ^ a) (((p.1 : ℝ) + 1) / (M : ℝ) ^ a) ×ˢ
    Set.Icc ((p.2 : ℝ) / (M : ℝ) ^ a) (((p.2 : ℝ) + 1) / (M : ℝ) ^ a)

lemma ediam_gridCell_le {M : ℕ} (hM : 1 ≤ M) (a : ℕ) (p : ℕ × ℕ) :
    Metric.ediam (gridCell M a p) ≤ ENNReal.ofReal ((M : ℝ) ^ a)⁻¹ := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le one_pos hM
  have hpow : (0 : ℝ) < (M : ℝ) ^ a := by positivity
  apply ediam_prod_Icc_le
  · rw [← sub_div, add_sub_cancel_left, one_div]
  · rw [← sub_div, add_sub_cancel_left, one_div]

lemma exists_gridIndex {M : ℕ} (hM : 1 ≤ M) (a : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ i : ℕ, i < M ^ a ∧ (i : ℝ) / (M : ℝ) ^ a ≤ t ∧ t ≤ ((i : ℝ) + 1) / (M : ℝ) ^ a := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le one_pos hM
  have hpow : (0 : ℝ) < (M : ℝ) ^ a := by positivity
  have hMa : 1 ≤ M ^ a := Nat.one_le_pow _ _ (lt_of_lt_of_le one_pos hM)
  refine ⟨min ⌊t * (M : ℝ) ^ a⌋₊ (M ^ a - 1), by omega, ?_, ?_⟩
  · rw [div_le_iff₀ hpow]
    calc ((min ⌊t * (M : ℝ) ^ a⌋₊ (M ^ a - 1) : ℕ) : ℝ) ≤ (⌊t * (M : ℝ) ^ a⌋₊ : ℝ) :=
          Nat.cast_le.mpr (min_le_left _ _)
      _ ≤ t * (M : ℝ) ^ a := Nat.floor_le (by positivity)
  · rw [le_div_iff₀ hpow]
    rcases le_total ⌊t * (M : ℝ) ^ a⌋₊ (M ^ a - 1) with h | h
    · rw [min_eq_left h]
      exact (Nat.lt_floor_add_one _).le
    · rw [min_eq_right h]
      have h1 : (((M ^ a - 1 : ℕ) : ℝ) + 1) = (M : ℝ) ^ a := by
        have : (M ^ a - 1 : ℕ) + 1 = M ^ a := by omega
        exact_mod_cast this
      rw [h1]
      nlinarith

lemma unitSquare_subset_iUnion_gridCell {M : ℕ} (hM : 1 ≤ M) (a : ℕ) :
    Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 ⊆
      ⋃ p ∈ (Finset.range (M ^ a) ×ˢ Finset.range (M ^ a)), gridCell M a p := by
  rintro ⟨x, y⟩ ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
  obtain ⟨i, hi, hi1, hi2⟩ := exists_gridIndex hM a hx0 hx1
  obtain ⟨j, hj, hj1, hj2⟩ := exists_gridIndex hM a hy0 hy1
  refine Set.mem_iUnion₂.mpr ⟨(i, j), ?_, ⟨⟨hi1, hi2⟩, ⟨hj1, hj2⟩⟩⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi, Finset.mem_range.mpr hj⟩

lemma gridCell_subset_eball {M : ℕ} (hM : 2 ≤ M) (K : ℕ) (p : ℕ × ℕ) {y : ℝ × ℝ}
    (hy : y ∈ gridCell M (K + 1) p) :
    gridCell M (K + 1) p ⊆ Metric.eball y (ENNReal.ofReal (gridScale M K)) := by
  intro z hz
  have hM1 : (1 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le one_lt_two hM
  have hpos : (0 : ℝ) < gridScale M K := by rw [gridScale_eq_inv_pow]; positivity
  rw [Metric.mem_eball]
  have hdiam := ediam_gridCell_le (le_trans one_le_two hM) (K + 1) p
  have h1 : edist z y ≤ ENNReal.ofReal ((M : ℝ) ^ (K + 1))⁻¹ :=
    le_trans (Metric.edist_le_ediam_of_mem hz hy) hdiam
  refine lt_of_le_of_lt h1 ?_
  rw [gridScale_eq_inv_pow]
  apply ENNReal.ofReal_lt_ofReal_iff'.mpr
  refine ⟨?_, by positivity⟩
  rw [pow_succ, mul_inv]
  have hMK : (0 : ℝ) < ((M : ℝ) ^ K)⁻¹ := by positivity
  have hinv : (M : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hM1
  nlinarith

lemma exists_grid_bracket_ordinary {M : ℕ} (hM : 2 ≤ M) {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (K : ℕ) (hRK : R ≤ gridScale M K) :
    ∃ k q : ℕ, K ≤ k ∧ R ≤ gridScale M k ∧ gridScale M (k + q) ≤ r ∧
      (M : ℝ) ^ (q : ℝ) ≤ (M : ℝ) ^ (2 : ℝ) * (R / r) := by
  have hM1 : (1 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le one_lt_two hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hlogM : 0 < Real.log M := Real.log_pos hM1
  have hR0 : 0 < R := lt_of_lt_of_le hr hrR
  set u : ℝ := Real.log (1 / R) / Real.log M with hu
  set w : ℝ := Real.log (1 / r) / Real.log M with hw
  have hRrepr : R = (M : ℝ) ^ (-u) := by
    rw [hu, Real.rpow_def_of_pos hM0]
    rw [show Real.log M * -(Real.log (1 / R) / Real.log M) = Real.log R by
      rw [one_div, Real.log_inv]; field_simp]
    rw [Real.exp_log hR0]
  have hrrepr : r = (M : ℝ) ^ (-w) := by
    rw [hw, Real.rpow_def_of_pos hM0]
    rw [show Real.log M * -(Real.log (1 / r) / Real.log M) = Real.log r by
      rw [one_div, Real.log_inv]; field_simp]
    rw [Real.exp_log hr]
  have huw : u ≤ w := by
    rw [hu, hw]
    apply div_le_div_of_nonneg_right _ hlogM.le
    apply Real.log_le_log (by positivity)
    exact one_div_le_one_div_of_le hr hrR
  have hKu : (K : ℝ) ≤ u := by
    have h1 : (M : ℝ) ^ (-u) ≤ (M : ℝ) ^ (-(K : ℝ)) := by
      rw [← hRrepr]; unfold gridScale at hRK; exact hRK
    have h2 := (Real.rpow_le_rpow_left_iff hM1).mp h1
    linarith
  have hu0 : 0 ≤ u := le_trans (Nat.cast_nonneg K) hKu
  set k : ℕ := ⌊u⌋₊ with hk
  set K' : ℕ := ⌈w⌉₊ with hK'
  have hku : (k : ℝ) ≤ u := Nat.floor_le hu0
  have hwK' : w ≤ K' := Nat.le_ceil w
  have hkK' : k ≤ K' := by
    have : (k : ℝ) ≤ K' := le_trans hku (le_trans huw hwK')
    exact_mod_cast this
  refine ⟨k, K' - k, ?_, ?_, ?_, ?_⟩
  · exact Nat.le_floor hKu
  · rw [hRrepr]
    unfold gridScale
    exact Real.rpow_le_rpow_of_exponent_le hM1.le (neg_le_neg hku)
  · rw [hrrepr]
    unfold gridScale
    rw [Nat.add_sub_cancel' hkK']
    exact Real.rpow_le_rpow_of_exponent_le hM1.le (neg_le_neg hwK')
  · have hqcast : ((K' - k : ℕ) : ℝ) = (K' : ℝ) - k := by rw [Nat.cast_sub hkK']
    have hK'lt : (K' : ℝ) < w + 1 := Nat.ceil_lt_add_one (le_trans hu0 huw)
    have hult : u < k + 1 := Nat.lt_floor_add_one u
    have hq : ((K' - k : ℕ) : ℝ) ≤ (w - u) + 2 := by rw [hqcast]; linarith
    have hratio : R / r = (M : ℝ) ^ (w - u) := by
      rw [hRrepr, hrrepr, ← Real.rpow_sub hM0]
      congr 1
      ring
    rw [hratio, ← Real.rpow_add hM0]
    apply Real.rpow_le_rpow_of_exponent_le hM1.le
    linarith

lemma exists_depth_at_level {M : ℕ} (hM : 2 ≤ M) {r : ℝ} (hr : 0 < r) (K : ℕ)
    (hrK : r ≤ gridScale M K) :
    ∃ q : ℕ, gridScale M (K + q) ≤ r ∧
      (M : ℝ) ^ (q : ℝ) ≤ (M : ℝ) ^ (2 : ℝ) * (gridScale M K / r) := by
  obtain ⟨k, q, hKk, houter, hinner, hratio⟩ :=
    exists_grid_bracket_ordinary hM hr hrK K le_rfl
  have hM1 : (1 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le one_lt_two hM
  have hkK : k = K := by
    by_contra hne
    have hlt : K < k := lt_of_le_of_ne hKk (Ne.symm hne)
    have : gridScale M k < gridScale M K := by
      unfold gridScale
      apply Real.rpow_lt_rpow_of_exponent_lt hM1
      have : (K : ℝ) < k := by exact_mod_cast hlt
      linarith
    linarith
  subst hkK
  exact ⟨q, hinner, hratio⟩

theorem dimA_le_of_eventually_grid_bound {M : ℕ} (hM : 2 ≤ M) {X : Set (ℝ × ℝ)}
    (hXsub : X ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) {s C : ℝ} (hs : 0 ≤ s) (hC : 0 < C)
    (K : ℕ)
    (hgrid : ∀ k, K ≤ k → ∀ q : ℕ, ∀ x ∈ X,
      (coverNum (gridScale M (k + q)) (X ∩ Metric.eball x (ENNReal.ofReal (gridScale M k))) :
        ℝ≥0∞) ≤ ENNReal.ofReal (C * ((M : ℝ) ^ (q : ℝ)) ^ s)) :
    dimA X ≤ s := by
  classical
  have hM1 : (1 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le one_lt_two hM
  have hM0 : (0 : ℝ) < M := by linarith
  set S : Finset (ℕ × ℕ) := Finset.range (M ^ (K + 1)) ×ˢ Finset.range (M ^ (K + 1)) with hS
  set n₀ : ℝ := (S.card : ℝ) with hn₀
  have hn₀0 : 0 ≤ n₀ := Nat.cast_nonneg _
  set Cp : ℝ := max 1 (C * (M : ℝ) ^ (2 * s)) with hCp
  have hCp0 : 0 < Cp := lt_of_lt_of_le one_pos (le_max_left _ _)
  set Cfull : ℝ := max (C * (M : ℝ) ^ (2 * s)) (n₀ * Cp) with hCfull
  have hCfull0 : 0 < Cfull := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  apply csInf_le (bddBelow_assouadExponents X)
  refine ⟨hs, Cfull, hCfull0, ?_⟩
  intro R r hr hrR hR1 x hx
  have hR0 : 0 < R := lt_of_lt_of_le hr hrR
  have hRr : 1 ≤ R / r := by rw [le_div_iff₀ hr]; linarith
  have hpowpos : 0 < (R / r) ^ s := Real.rpow_pos_of_pos (by positivity) s
  by_cases hRK : R ≤ gridScale M K
  ·
    obtain ⟨k, q, hKk, houter, hinner, hratio⟩ := exists_grid_bracket_ordinary hM hr hrR K hRK
    have h1 := hgrid k hKk q x hx
    have hmono : coverNum r (X ∩ Metric.eball x (ENNReal.ofReal R)) ≤
        coverNum (gridScale M (k + q))
          (X ∩ Metric.eball x (ENNReal.ofReal (gridScale M k))) :=
      coverNum_inter_eball_le_of_scale_bracket houter hinner
    refine le_trans (ENat.toENNReal_le.mpr hmono) (le_trans h1 (ENNReal.ofReal_le_ofReal ?_))
    have hMq0 : 0 ≤ (M : ℝ) ^ (q : ℝ) := by positivity
    have hpow : ((M : ℝ) ^ (q : ℝ)) ^ s ≤ ((M : ℝ) ^ (2 : ℝ) * (R / r)) ^ s :=
      Real.rpow_le_rpow hMq0 hratio hs
    calc C * ((M : ℝ) ^ (q : ℝ)) ^ s ≤ C * ((M : ℝ) ^ (2 : ℝ) * (R / r)) ^ s :=
          mul_le_mul_of_nonneg_left hpow hC.le
      _ = C * (M : ℝ) ^ (2 * s) * (R / r) ^ s := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hM0.le]
          ring
      _ ≤ Cfull * (R / r) ^ s :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hpowpos.le
  ·
    push Not at hRK
    have hXcov : X ∩ Metric.eball x (ENNReal.ofReal R) ⊆ ⋃ p ∈ S, X ∩ gridCell M (K + 1) p := by
      intro z hz
      have hz' := unitSquare_subset_iUnion_gridCell (le_trans one_le_two hM) (K + 1) (hXsub hz.1)
      obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp hz'
      exact Set.mem_iUnion₂.mpr ⟨p, hp, hz.1, hzp⟩
    have hpiece : ∀ p ∈ S, (coverNum r (X ∩ gridCell M (K + 1) p) : ℝ≥0∞) ≤
        ENNReal.ofReal (Cp * (R / r) ^ s) := by
      intro p _
      by_cases hne : (X ∩ gridCell M (K + 1) p).Nonempty
      · obtain ⟨y, hyX, hyp⟩ := hne
        have hsub : X ∩ gridCell M (K + 1) p ⊆
            X ∩ Metric.eball y (ENNReal.ofReal (gridScale M K)) :=
          Set.inter_subset_inter_right _ (gridCell_subset_eball hM K p hyp)
        by_cases hrK : r ≤ gridScale M K
        · obtain ⟨q, hinner, hratio⟩ := exists_depth_at_level hM hr K hrK
          have hmono : coverNum r (X ∩ gridCell M (K + 1) p) ≤
              coverNum (gridScale M (K + q))
                (X ∩ Metric.eball y (ENNReal.ofReal (gridScale M K))) :=
            le_trans (coverNum_mono hsub) (coverNum_anti hinner)
          have h1 := hgrid K le_rfl q y hyX
          refine le_trans (ENat.toENNReal_le.mpr hmono)
            (le_trans h1 (ENNReal.ofReal_le_ofReal ?_))
          have hratio' : (M : ℝ) ^ (q : ℝ) ≤ (M : ℝ) ^ (2 : ℝ) * (R / r) := by
            refine le_trans hratio ?_
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact div_le_div_of_nonneg_right hRK.le hr.le
          have hpow : ((M : ℝ) ^ (q : ℝ)) ^ s ≤ ((M : ℝ) ^ (2 : ℝ) * (R / r)) ^ s :=
            Real.rpow_le_rpow (by positivity) hratio' hs
          calc C * ((M : ℝ) ^ (q : ℝ)) ^ s ≤ C * ((M : ℝ) ^ (2 : ℝ) * (R / r)) ^ s :=
                mul_le_mul_of_nonneg_left hpow hC.le
            _ = C * (M : ℝ) ^ (2 * s) * (R / r) ^ s := by
                rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hM0.le]
                ring
            _ ≤ Cp * (R / r) ^ s :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) hpowpos.le
        ·
          push Not at hrK
          have hdiam : Metric.ediam (X ∩ gridCell M (K + 1) p) ≤ ENNReal.ofReal r := by
            refine le_trans (Metric.ediam_mono Set.inter_subset_right)
              (le_trans (ediam_gridCell_le (le_trans one_le_two hM) (K + 1) p)
                (ENNReal.ofReal_le_ofReal ?_))
            have h1 : ((M : ℝ) ^ (K + 1))⁻¹ ≤ ((M : ℝ) ^ K)⁻¹ := by
              apply inv_anti₀ (by positivity)
              exact pow_le_pow_right₀ hM1.le (Nat.le_succ K)
            rw [gridScale_eq_inv_pow] at hrK
            linarith
          have h1 : coverNum r (X ∩ gridCell M (K + 1) p) ≤ 1 := by
            refine le_trans (coverNum_le_of_isCover (C := {X ∩ gridCell M (K + 1) p})
              (by simp) ?_) ?_
            · intro T hT
              rw [Set.mem_singleton_iff] at hT
              rw [hT]
              exact hdiam
            · simp
          refine le_trans (ENat.toENNReal_le.mpr h1) ?_
          rw [ENat.toENNReal_one, ← ENNReal.ofReal_one]
          apply ENNReal.ofReal_le_ofReal
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ Cp * (R / r) ^ s :=
                mul_le_mul (le_max_left _ _) (Real.one_le_rpow hRr hs) zero_le_one hCp0.le
      · rw [Set.not_nonempty_iff_eq_empty] at hne
        rw [hne]
        have h0 : coverNum r (∅ : Set (ℝ × ℝ)) ≤ 0 := by
          refine le_trans (coverNum_le_of_isCover (C := (∅ : Set (Set (ℝ × ℝ)))) (by simp)
            (fun T hT => absurd hT (Set.notMem_empty _))) ?_
          simp
        refine le_trans (ENat.toENNReal_le.mpr h0) ?_
        simp
    have hsum : (coverNum r (X ∩ Metric.eball x (ENNReal.ofReal R)) : ℝ≥0∞) ≤
        ∑ p ∈ S, (coverNum r (X ∩ gridCell M (K + 1) p) : ℝ≥0∞) := by
      have h1 := coverNum_mono (r := r) hXcov
      have h2 := coverNum_biUnion_le r S (fun p => X ∩ gridCell M (K + 1) p)
      have h3 := ENat.toENNReal_le.mpr (le_trans h1 h2)
      rw [toENNReal_finset_sum] at h3
      exact h3
    calc (coverNum r (X ∩ Metric.eball x (ENNReal.ofReal R)) : ℝ≥0∞)
        ≤ ∑ p ∈ S, (coverNum r (X ∩ gridCell M (K + 1) p) : ℝ≥0∞) := hsum
      _ ≤ ∑ _p ∈ S, ENNReal.ofReal (Cp * (R / r) ^ s) := Finset.sum_le_sum hpiece
      _ = (S.card : ℝ≥0∞) * ENNReal.ofReal (Cp * (R / r) ^ s) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ENNReal.ofReal (n₀ * (Cp * (R / r) ^ s)) := by
          rw [ENNReal.ofReal_mul hn₀0, hn₀, ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (Cfull * (R / r) ^ s) := by
          apply ENNReal.ofReal_le_ofReal
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) hpowpos.le

end FractalGeometry.Probability.GridPercolation
