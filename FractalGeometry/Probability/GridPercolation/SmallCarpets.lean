import FractalGeometry.Probability.GridPercolation.CarpetLowerBound

namespace FractalGeometry.Probability.GridPercolation

open FractalGeometry.Dimension.PhiAssouad
open scoped ENNReal

variable {A : GridLaw}

namespace GridLaw

variable (A : GridLaw)

lemma sAdet_eq_zero (h : ∀ a b, Allowed A a → Allowed A b → a = b) : A.sAdet = 0 := by
  have hAx : A.Ax ≤ 1 := by
    refine Finset.card_le_one.mpr fun i hi i' hi' => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
    obtain ⟨j, hj⟩ := hi
    obtain ⟨j', hj'⟩ := hi'
    exact congrArg Prod.fst (h (i, j) (i', j') hj hj')
  have hBmax : A.Bmax ≤ 1 := by
    refine ciSup_le fun i => Finset.card_le_one.mpr fun j hj j' hj' => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
    exact congrArg Prod.snd (h (i, j) (i, j') hj hj')
  have hlog : ∀ n : ℕ, n ≤ 1 → Real.log n = 0 := by
    intro n hn
    interval_cases n <;> simp
  rw [sAdet, hlog _ hAx, hlog _ hBmax, zero_div, zero_div, add_zero]


end GridLaw

lemma eq_of_abs_sub_le_inv_pow {x y b : ℝ} (hb : 1 < b) (h : ∀ k : ℕ, |x - y| ≤ (b ^ k)⁻¹) :
    x = y := by
  by_contra hxy
  have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hd (inv_lt_one_of_one_lt₀ hb)
  have := h k
  rw [← inv_pow] at this
  linarith



theorem carpet_subsingleton (h : ∀ a b, Allowed A a → Allowed A b → a = b) :
    (carpet A).Subsingleton := by
  intro z hz z' hz'
  have key : ∀ k : ℕ,
      |z.1 - z'.1| ≤ ((A.M : ℝ) ^ k)⁻¹ ∧ |z.2 - z'.2| ≤ ((A.N : ℝ) ^ k)⁻¹ := by
    intro k
    obtain ⟨w, ⟨hwk, hwD⟩, hzw⟩ := Set.mem_iUnion₂.mp (Set.mem_iInter.mp hz k)
    obtain ⟨w', ⟨hwk', hwD'⟩, hzw'⟩ := Set.mem_iUnion₂.mp (Set.mem_iInter.mp hz' k)
    have hwD := (deterministic_retained w).mp hwD
    have hwD' := (deterministic_retained w').mp hwD'
    have hww : w' = w := by
      apply List.ext_getElem (hwk'.trans hwk.symm)
      intro n h1 h2
      exact h _ _ (hwD' _ (List.getElem_mem h1)) (hwD _ (List.getElem_mem h2))
    subst hww hwk
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := rect_subset_digit_prod w' hzw
    obtain ⟨⟨h1', h2'⟩, h3', h4'⟩ := rect_subset_digit_prod w' hzw'
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have hM : (1 : ℝ) < A.M := by exact_mod_cast lt_of_lt_of_le one_lt_two A.hM
  exact Prod.ext (eq_of_abs_sub_le_inv_pow hM fun k => (key k).1)
    (eq_of_abs_sub_le_inv_pow A.one_lt_N_real fun k => (key k).2)



theorem dimA_eq_zero_of_subsingleton {E : Type*} [PseudoEMetricSpace E] {Y : Set E}
    (hY : Y.Subsingleton) : dimA Y = 0 := by
  have h0 : (0 : ℝ) ∈ AssouadExponents Y := by
    refine ⟨le_rfl, 1, one_pos, fun R r _ _ _ x _ => ?_⟩
    have hcov : coverNum r (Y ∩ Metric.eball x (ENNReal.ofReal R)) ≤ 1 := by
      refine (coverNum_le_of_isCover (C := {Y ∩ Metric.eball x (ENNReal.ofReal R)})
        (by simp) ?_).trans (by simp)
      intro S hS
      rw [Set.mem_singleton_iff.mp hS, Metric.ediam_subsingleton (hY.anti Set.inter_subset_left)]
      exact bot_le
    rw [Real.rpow_zero, mul_one, ENNReal.ofReal_one]
    calc (coverNum r (Y ∩ Metric.eball x (ENNReal.ofReal R)) : ℝ≥0∞)
        ≤ ((1 : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_le.mpr hcov
      _ = 1 := ENat.toENNReal_one
  exact le_antisymm (csInf_le (bddBelow_assouadExponents Y) h0) (le_csInf ⟨0, h0⟩ fun s hs => hs.1)


end FractalGeometry.Probability.GridPercolation
