import FractalGeometry.Probability.GridPercolation.CarpetRefinements
import FractalGeometry.Dimension.PhiAssouad.PlaneBounds
import FractalGeometry.Probability.GridPercolation.FloorBounds

namespace FractalGeometry.Probability.GridPercolation

open FractalGeometry.Dimension.PhiAssouad Filter Topology
open scoped ENNReal

variable {A : GridLaw}

lemma GridLaw.exists_B_eq_Bmax (A : GridLaw) : ∃ i, A.B i = A.Bmax := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty A.B
  exact ⟨i, by rw [A.Bmax_eq_sup, hi]⟩

lemma ediam_region_le {k : ℕ} (c : SquareCode A k) :
    Metric.ediam c.region ≤ ENNReal.ofReal (A.N * gridScale A.M k) := by
  have hM : (0 : ℝ) < A.M := by exact_mod_cast A.hM_pos
  have hN : (0 : ℝ) < A.N := by exact_mod_cast A.hN_pos
  unfold SquareCode.region
  apply ediam_prod_Icc_le <;> simp only [add_sub_cancel_left, gridScale_eq_inv_pow]
  · exact le_mul_of_one_le_left (by positivity) A.one_lt_N_real.le
  · have hp := A.lt_pow_bfloor_succ k
    rw [pow_succ] at hp
    rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

lemma region_subset_ball {k : ℕ} (c : SquareCode A k) {x : ℝ × ℝ} (hx : x ∈ c.region) :
    c.region ⊆ Metric.eball x (ENNReal.ofReal (2 * A.N * gridScale A.M k)) := by
  have hN : (0 : ℝ) < A.N := by exact_mod_cast A.hN_pos
  have hM : (0 : ℝ) < A.M := by exact_mod_cast A.hM_pos
  have hg : 0 < gridScale A.M k := by rw [gridScale_eq_inv_pow]; positivity
  intro y hy
  apply lt_of_le_of_lt ((Metric.edist_le_ediam_of_mem hy hx).trans (ediam_region_le c))
  apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
  nlinarith

lemma constantCode_meets_carpet {i : Fin A.M} {j : Fin A.N} (hj : j ∈ A.rows i) (k : ℕ) :
    ∃ x ∈ carpet A, x ∈ (constantCode i j k).region := by
  have hp : 0 < A.p i j := by simpa [GridLaw.rows] using hj
  have hi : i ∈ A.cols := by simpa [GridLaw.cols] using (show ∃ j, 0 < A.p i j from ⟨j, hp⟩)
  have hc : (constantCode i j k).Admissible := ⟨fun _ => hi, fun _ => hj⟩
  obtain ⟨x, hx, hK, -⟩ := admissible_region_meets_carpet_and_truncate (le_refl k)
    ⟨(i, j), hp⟩ hc
  exact ⟨x, hK, hx⟩

lemma exists_carpet_depth (q : ℕ) : ∃ k : ℕ,
    bfloor A.Gamma (k + q) ≤ k ∧ 2 * A.N * gridScale A.M k < 1 := by
  have hM : (1 : ℝ) < A.M := by exact_mod_cast A.hM
  have hN : (0 : ℝ) < A.N := by exact_mod_cast A.hN_pos
  have hΓ := A.Gamma_lt_one
  have he : ∀ᶠ k : ℕ in atTop, 2 * (A.N : ℝ) < (A.M : ℝ) ^ k :=
    (tendsto_pow_atTop_atTop_of_one_lt hM).eventually_gt_atTop _
  obtain ⟨k, hk, hpow⟩ := ((eventually_ge_atTop ⌈q * A.Gamma / (1 - A.Gamma)⌉₊).and he).exists
  refine ⟨k, ?_, ?_⟩
  · apply Nat.floor_le_of_le
    have hle : (q : ℝ) * A.Gamma / (1 - A.Gamma) ≤ k :=
      (Nat.le_ceil _).trans (by exact_mod_cast hk)
    have := (div_le_iff₀ (by linarith : 0 < 1 - A.Gamma)).mp hle
    push_cast
    nlinarith
  · rw [gridScale_eq_inv_pow, ← div_eq_mul_inv, div_lt_one (by positivity)]
    exact hpow

theorem carpet_count_le_exponent {s C : ℝ} (_hs : 0 ≤ s) (hC : 0 < C)
    (hcover : ∀ R r : ℝ, 0 < r → r ≤ R → R < 1 → ∀ x ∈ carpet A,
      (coverNum r (carpet A ∩ Metric.eball x (ENNReal.ofReal R)) : ℝ≥0∞) ≤
        ENNReal.ofReal (C * (R / r) ^ s))
    {i : Fin A.M} {j : Fin A.N} (hj : j ∈ A.rows i) (q : ℕ) :
    ∃ k : ℕ, ((A.B i : ℝ) ^ (bfloor A.Gamma (k + q) - bfloor A.Gamma k) * (A.Ax : ℝ) ^ q) ≤
      25 * C * ((2 * A.N : ℝ) * (A.M : ℝ) ^ q) ^ s := by
  obtain ⟨k, hb, hR1⟩ := exists_carpet_depth (A := A) q
  obtain ⟨x, hxK, hxc⟩ := constantCode_meets_carpet hj k
  have hM : (0 : ℝ) < A.M := by exact_mod_cast A.hM_pos
  have hN : (0 : ℝ) < A.N := by exact_mod_cast A.hN_pos
  let R := 2 * A.N * gridScale A.M k
  let r := gridScale A.M (k + q)
  have hr : 0 < r := by dsimp [r]; rw [gridScale_eq_inv_pow]; positivity
  have hR : 0 < R := by dsimp [R]; rw [gridScale_eq_inv_pow]; positivity
  have hratio : R / r = 2 * A.N * (A.M : ℝ) ^ q := by
    dsimp [R, r]
    simp only [gridScale_eq_inv_pow, pow_add]
    field_simp
  have hrR : r ≤ R := by
    rw [← one_le_div hr, hratio]
    exact one_le_mul_of_one_le_of_one_le
      (by nlinarith [A.one_lt_N_real]) (one_le_pow₀ A.one_le_M_real)
  have hlocal := carpet_local_cover_lower hj hb
  have hmono : carpet A ∩ (constantCode i j k).region ⊆
      carpet A ∩ Metric.eball x (ENNReal.ofReal R) :=
    Set.inter_subset_inter_right _ (region_subset_ball _ hxc)
  have hbound : ((A.B i ^ (bfloor A.Gamma (k + q) - bfloor A.Gamma k) * A.Ax ^ q : ℕ) : ℝ≥0∞) ≤
      25 * ENNReal.ofReal (C * (R / r) ^ s) := by
    calc
      _ ≤ (25 : ℝ≥0∞) * coverNum r (carpet A ∩ (constantCode i j k).region) := by
        exact_mod_cast hlocal
      _ ≤ 25 * coverNum r (carpet A ∩ Metric.eball x (ENNReal.ofReal R)) := by
        gcongr
        exact coverNum_mono hmono
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcover R r hr hrR hR1 x hxK) zero_le
  have hright : (25 : ℝ≥0∞) * ENNReal.ofReal (C * (R / r) ^ s) =
      ENNReal.ofReal (25 * C * (R / r) ^ s) := by
    conv_rhs => rw [mul_assoc, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 25)]
    norm_num
  rw [hright] at hbound
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  have hnonneg : 0 ≤ 25 * C * (R / r) ^ s := by positivity
  simp only [ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hnonneg] at hreal
  exact ⟨k, by simpa only [hratio, Nat.cast_mul, Nat.cast_pow] using hreal⟩

lemma GridLaw.sAdet_mul_log_M (A : GridLaw) :
    A.sAdet * Real.log A.M = Real.log A.Ax + A.Gamma * Real.log A.Bmax := by
  unfold GridLaw.sAdet GridLaw.Gamma
  have hM := A.log_M_pos.ne'
  have hN := A.log_N_pos.ne'
  field_simp

theorem carpet_assouad_lower (hm : 1 < A.m) : A.sAdet ≤ dimA (carpet A) := by
  apply le_csInf (show (AssouadExponents (carpet A)).Nonempty from
    ⟨2, two_mem_assouadExponents _⟩)
  intro s hs
  obtain ⟨hs, C, hC, hcover⟩ := hs
  obtain ⟨i, hi⟩ := A.exists_B_eq_Bmax
  have hB : (0 : ℝ) < A.Bmax := by exact_mod_cast A.Bmax_pos_of_m_pos (zero_lt_one.trans hm)
  have hB1 : (1 : ℝ) ≤ A.Bmax := by
    exact_mod_cast A.Bmax_pos_of_m_pos (zero_lt_one.trans hm)
  have hAx : (0 : ℝ) < A.Ax := by exact_mod_cast A.one_le_Ax hm
  have hM : (0 : ℝ) < A.M := by exact_mod_cast A.hM_pos
  have hN : (0 : ℝ) < A.N := by exact_mod_cast A.hN_pos
  have hrows : (A.rows i).Nonempty := by
    rw [← Finset.card_pos, ← A.B_eq_card_rows, hi]
    exact A.Bmax_pos_of_m_pos (zero_lt_one.trans hm)
  obtain ⟨j, hj⟩ := hrows
  let D : ℝ := 25 * C * (2 * A.N : ℝ) ^ s
  have hD : 0 < D := by dsimp [D]; positivity
  have hbound (q : ℕ) :
      (q : ℝ) * (Real.log A.Ax + A.Gamma * Real.log A.Bmax - s * Real.log A.M) ≤
        Real.log D + Real.log A.Bmax := by
    obtain ⟨k, hk⟩ := carpet_count_le_exponent hs hC hcover hj q
    rw [hi, Real.mul_rpow (by positivity) (by positivity)] at hk
    have hk' : (A.Bmax : ℝ) ^ (bfloor A.Gamma (k + q) - bfloor A.Gamma k) * (A.Ax : ℝ) ^ q ≤
        D * ((A.M : ℝ) ^ q) ^ s := by
      dsimp [D]
      nlinarith [hk]
    have hlog := Real.log_le_log (by positivity) hk'
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_mul hD.ne' (by positivity), Real.log_rpow (by positivity), Real.log_pow] at hlog
    have hb : (q : ℝ) * A.Gamma - 1 ≤
        ((bfloor A.Gamma (k + q) - bfloor A.Gamma k : ℕ) : ℝ) := by
      rw [Nat.cast_sub (A.bfloor_mono (Nat.le_add_right k q))]
      have h1 := lt_bfloor_cast_add_one A.Gamma (k + q)
      have h2 := bfloor_cast_le A.Gamma_pos.le k
      push_cast at h1
      nlinarith
    have hlow := mul_le_mul_of_nonneg_right hb (Real.log_nonneg hB1)
    nlinarith
  by_contra h
  have hgap : 0 < Real.log A.Ax + A.Gamma * Real.log A.Bmax - s * Real.log A.M := by
    rw [← A.sAdet_mul_log_M]
    nlinarith [A.log_M_pos, not_le.mp h]
  obtain ⟨q, hq⟩ := exists_nat_gt ((Real.log D + Real.log A.Bmax) /
    (Real.log A.Ax + A.Gamma * Real.log A.Bmax - s * Real.log A.M))
  have hq' := (div_lt_iff₀ hgap).mp hq
  linarith [hbound q]

/-- Mackay's Assouad-dimension formula for the deterministic support carpet,
under a nontriviality hypothesis on the grid law. -/
theorem carpet_dimA (hm : 1 < A.m) : dimA (carpet A) = A.sAdet :=
  le_antisymm (carpet_assouad_upper hm) (carpet_assouad_lower hm)

end FractalGeometry.Probability.GridPercolation
