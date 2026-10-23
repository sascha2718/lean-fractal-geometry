import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.BlockColumnMoments
import FractalGeometry.Probability.GridPercolation.BlockColumnProcess
import FractalGeometry.Probability.GridPercolation.Lambda
import FractalGeometry.Probability.GridPercolation.LambdaTilt
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.OccupiedColumnMean
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.Processes
import FractalGeometry.Probability.GridPercolation.PrunedSurvival
import FractalGeometry.Probability.GridPercolation.SecondMoments

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory ProbabilityTheory Filter Topology

open scoped ENNReal

variable {A : GridLaw} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

theorem exists_measure_prunedColumnCount_ge_of_lam_eq_one (hX : IsPercolation P X)
    (hm : 1 < A.m) (hlam : A.lam = 1) (ε : ℝ) :
    ∃ ρ > 0, ∀ n : ℕ, ENNReal.ofReal ρ ≤
      P {ω | A.lam ^ ((1 - ε) * (n : ℝ)) ≤ (prunedColumnCount X n ω : ℝ)} := by
  let := hX.toIsProbabilityMeasure
  refine ⟨(P (survival X)).toReal,
    ENNReal.toReal_pos (measure_survival_pos_of_one_lt_m hX hm).ne' (measure_ne_top _ _),
    fun n => ?_⟩
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  refine measure_mono fun ω hs => ?_
  show A.lam ^ ((1 - ε) * (n : ℝ)) ≤ (prunedColumnCount X n ω : ℝ)
  rw [hlam, Real.one_rpow]
  exact_mod_cast one_le_prunedColumnCount_of_mem_survival hs n

theorem exists_measure_prunedColumnCount_ge_of_mean (hX : IsPercolation P X) (hm : 1 < A.m)
    (hlam : 1 < A.lam) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmean : ∀ᶠ ℓ : ℕ in atTop,
      A.lam ^ ((1 - ε / 2) * (ℓ : ℝ)) ≤ ∫ ω, (occupiedColumnCount X ℓ ω : ℝ) ∂P) :
    ∃ ρ > 0, ∀ᶠ n : ℕ in atTop, ENNReal.ofReal ρ ≤
      P {ω | A.lam ^ ((1 - ε) * (n : ℝ)) ≤ (prunedColumnCount X n ω : ℝ)} := by
  let := hX.toIsProbabilityMeasure
  obtain ⟨ℓ, hℓ, hℓ1⟩ := (hmean.and (eventually_ge_atTop 1)).exists
  set μ := ∫ ω, (occupiedColumnCount X ℓ ω : ℝ) ∂P with hμdef
  have hlam0 : 0 < A.lam := by linarith
  have hℓpos : (0 : ℝ) < ℓ := Nat.cast_pos.mpr (by omega)
  have hexp_pos : 0 < (1 - ε / 2) * (ℓ : ℝ) := mul_pos (by linarith) hℓpos
  have hμ1 : 1 < μ := lt_of_lt_of_le (Real.one_lt_rpow hlam hexp_pos) hℓ
  obtain ⟨ρ, hρ, hbound⟩ := exists_measure_prunedColumnCount_block_ge hX hm hμ1
  set ps := (P (survival X)).toReal with hps
  have hps_pos : 0 < ps :=
    ENNReal.toReal_pos (measure_survival_pos_of_one_lt_m hX hm).ne' (measure_ne_top _ _)
  refine ⟨ρ, hρ, ?_⟩
  have hL : 0 < Real.log A.lam := Real.log_pos hlam
  have htend : Tendsto (fun n : ℕ => ε / 2 * Real.log A.lam * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  filter_upwards [htend.eventually_ge_atTop
      ((1 - ε / 2) * ℓ * Real.log A.lam - Real.log (ps / 2))] with n hn
  have hdiv : (n : ℝ) - ℓ ≤ ((n / ℓ : ℕ) : ℝ) * ℓ := by
    have h1 : n ≤ n / ℓ * ℓ + ℓ := (Nat.lt_div_mul_add (by omega)).le
    have h2 : (n : ℝ) ≤ ((n / ℓ : ℕ) : ℝ) * ℓ + ℓ := by exact_mod_cast h1
    linarith
  have hμpow : A.lam ^ ((1 - ε / 2) * ((n : ℝ) - ℓ)) ≤ μ ^ (n / ℓ) := by
    calc A.lam ^ ((1 - ε / 2) * ((n : ℝ) - ℓ))
        ≤ A.lam ^ ((1 - ε / 2) * (ℓ : ℝ) * ((n / ℓ : ℕ) : ℝ)) := by
          apply Real.rpow_le_rpow_of_exponent_le hlam.le
          have := mul_le_mul_of_nonneg_left hdiv (show (0 : ℝ) ≤ 1 - ε / 2 by linarith)
          linarith
      _ = (A.lam ^ ((1 - ε / 2) * (ℓ : ℝ))) ^ (n / ℓ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hlam0.le]
      _ ≤ μ ^ (n / ℓ) := pow_le_pow_left₀ (by positivity) hℓ _
  have hkey : A.lam ^ ((1 - ε) * (n : ℝ)) ≤ ps / 2 * μ ^ (n / ℓ) := by
    calc A.lam ^ ((1 - ε) * (n : ℝ))
        ≤ ps / 2 * A.lam ^ ((1 - ε / 2) * ((n : ℝ) - ℓ)) := by
          rw [Real.rpow_def_of_pos hlam0, Real.rpow_def_of_pos hlam0,
            ← Real.exp_log (show 0 < ps / 2 by positivity), ← Real.exp_add]
          exact Real.exp_le_exp.mpr (by nlinarith [hn])
      _ ≤ ps / 2 * μ ^ (n / ℓ) := by gcongr
  refine (hbound (n / ℓ)).trans (measure_mono fun ω hω => ?_)
  have hω' : ps / 2 * μ ^ (n / ℓ) ≤ (prunedColumnCount X (n / ℓ * ℓ) ω : ℝ) := hω
  have hmono : prunedColumnCount X (n / ℓ * ℓ) ω ≤ prunedColumnCount X n ω :=
    monotone_prunedColumnCount X ω (Nat.div_mul_le_self n ℓ)
  show A.lam ^ ((1 - ε) * (n : ℝ)) ≤ (prunedColumnCount X n ω : ℝ)
  calc A.lam ^ ((1 - ε) * (n : ℝ)) ≤ ps / 2 * μ ^ (n / ℓ) := hkey
    _ ≤ prunedColumnCount X (n / ℓ * ℓ) ω := hω'
    _ ≤ prunedColumnCount X n ω := by exact_mod_cast hmono

theorem forall_exists_measure_prunedColumnCount_ge (hX : IsPercolation P X) (hm : 1 < A.m)
    (hmean : 1 < A.lam → ∀ ε > 0, ∀ᶠ ℓ : ℕ in atTop,
      A.lam ^ ((1 - ε) * (ℓ : ℝ)) ≤ ∫ ω, (occupiedColumnCount X ℓ ω : ℝ) ∂P) :
    ∀ ε > 0, ∃ ρ > 0, ∀ᶠ n : ℕ in atTop, ENNReal.ofReal ρ ≤
      P {ω | A.lam ^ ((1 - ε) * (n : ℝ)) ≤ (prunedColumnCount X n ω : ℝ)} := by
  intro ε hε
  rcases (A.one_le_lam hm).eq_or_lt with h1 | h1
  · obtain ⟨ρ, hρ, h⟩ := exists_measure_prunedColumnCount_ge_of_lam_eq_one hX hm h1.symm ε
    exact ⟨ρ, hρ, Eventually.of_forall h⟩
  · have hε'0 : 0 < min ε 1 := lt_min hε one_pos
    obtain ⟨ρ, hρ, h⟩ := exists_measure_prunedColumnCount_ge_of_mean hX hm h1 hε'0
      (min_le_right _ _) (hmean h1 (min ε 1 / 2) (by positivity))
    refine ⟨ρ, hρ, h.mono fun n hn => hn.trans (measure_mono fun ω hω => ?_)⟩
    have hω' : A.lam ^ ((1 - min ε 1) * (n : ℝ)) ≤ (prunedColumnCount X n ω : ℝ) := hω
    show A.lam ^ ((1 - ε) * (n : ℝ)) ≤ (prunedColumnCount X n ω : ℝ)
    refine le_trans (Real.rpow_le_rpow_of_exponent_le h1.le ?_) hω'
    have hle : min ε 1 ≤ ε := min_le_left _ _
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith

theorem eventually_lam_rpow_le_integral_occupiedColumnCount (hX : IsPercolation P X)
    (hlam : 1 < A.lam) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ ℓ : ℕ in atTop,
      A.lam ^ ((1 - ε) * (ℓ : ℝ)) ≤ ∫ ω, (occupiedColumnCount X ℓ ω : ℝ) ∂P := by
  classical
  have hlam0 : 0 < A.lam := by linarith
  have hL : 0 < Real.log A.lam := Real.log_pos hlam
  set c := ε / 2 * Real.log A.lam with hc
  have hcpos : 0 < c := by positivity
  have htilt := eventually_lam_pow_mul_exp_le_sum_minPrefixMeanProduct A hcpos
  have hpoly : ∀ᶠ ℓ : ℕ in atTop, 4 * (1 + A.N * (ℓ : ℝ)) ≤ Real.exp (c * ℓ) := by
    filter_upwards [eventually_ge_atTop (max 1 ⌈16 * ((A.N : ℝ) + 1) / c ^ 2⌉₊)] with ℓ hℓ
    have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast le_of_max_le_left hℓ
    have hℓc : 16 * ((A.N : ℝ) + 1) / c ^ 2 ≤ ℓ :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hℓ)
    have hℓc' : 16 * ((A.N : ℝ) + 1) ≤ c ^ 2 * ℓ := by
      rw [div_le_iff₀ (by positivity)] at hℓc
      linarith
    have hexp : (c * ℓ / 2 + 1) * (c * ℓ / 2 + 1) ≤ Real.exp (c * ℓ) := by
      have h := Real.add_one_le_exp (c * ℓ / 2)
      have h0 : 0 ≤ c * ℓ / 2 + 1 := by positivity
      calc (c * ℓ / 2 + 1) * (c * ℓ / 2 + 1) ≤ Real.exp (c * ℓ / 2) * Real.exp (c * ℓ / 2) :=
            mul_le_mul h h h0 (Real.exp_pos _).le
        _ = Real.exp (c * ℓ) := by
            rw [← Real.exp_add]
            congr 1
            ring
    have hN : (0 : ℝ) ≤ A.N := Nat.cast_nonneg _
    have hprod := mul_le_mul_of_nonneg_left hℓc' (show (0 : ℝ) ≤ ℓ by linarith)
    nlinarith [hexp, hprod, hℓ1, hN, hcpos]
  filter_upwards [htilt, hpoly] with ℓ hℓ hp
  have hallowed : allowedColumnWords A ℓ =
      (Finset.univ : Finset (ColumnWord A ℓ)).filter (fun σ => ∀ l, σ l ∈ A.cols) := by
    ext σ
    simp [mem_allowedColumnWords]
  have hsum : (∑ σ ∈ allowedColumnWords A ℓ, minPrefixMeanProduct σ) =
      ∑ σ ∈ (Finset.univ : Finset (ColumnWord A ℓ)).filter (fun σ => ∀ l, σ l ∈ A.cols),
        (Finset.range (ℓ + 1)).inf' Finset.nonempty_range_add_one
          (fun k => ∏ l ∈ Finset.univ.filter (fun l : Fin ℓ => (l : ℕ) < k), A.E (σ l)) := by
    rw [hallowed]
    rfl
  have hmean := sum_minPrefix_div_le_integral_occupiedColumnCount hX (P := P) ℓ
  rw [← hsum] at hmean
  have hden : 0 < 4 * (1 + A.N * (ℓ : ℝ)) := by positivity
  have hleft : A.lam ^ ((1 - ε) * (ℓ : ℝ)) * (4 * (1 + A.N * (ℓ : ℝ))) ≤
      A.lam ^ ℓ * Real.exp (-c * ℓ) := by
    have h1 : A.lam ^ ℓ * Real.exp (-c * ℓ) = Real.exp ((1 - ε / 2) * Real.log A.lam * ℓ) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hlam0, ← Real.exp_add, hc]
      congr 1
      ring
    rw [h1, Real.rpow_def_of_pos hlam0]
    calc Real.exp (Real.log A.lam * ((1 - ε) * ℓ)) * (4 * (1 + A.N * ℓ))
        ≤ Real.exp (Real.log A.lam * ((1 - ε) * ℓ)) * Real.exp (c * ℓ) := by gcongr
      _ = Real.exp ((1 - ε / 2) * Real.log A.lam * ℓ) := by
          rw [← Real.exp_add, hc]
          congr 1
          ring
  calc A.lam ^ ((1 - ε) * (ℓ : ℝ))
      ≤ A.lam ^ ℓ * Real.exp (-c * ℓ) / (4 * (1 + A.N * ℓ)) := by
        rw [le_div_iff₀ hden]
        exact hleft
    _ ≤ (∑ σ ∈ allowedColumnWords A ℓ, minPrefixMeanProduct σ) / (4 * (1 + A.N * ℓ)) := by
        gcongr
    _ ≤ ∫ ω, (occupiedColumnCount X ℓ ω : ℝ) ∂P := hmean

theorem forall_exists_measure_prunedColumnCount_ge_of_isPercolation (hX : IsPercolation P X)
    (hm : 1 < A.m) :
    ∀ ε > 0, ∃ ρ > 0, ∀ᶠ n : ℕ in atTop, ENNReal.ofReal ρ ≤
      P {ω | A.lam ^ ((1 - ε) * (n : ℝ)) ≤ (prunedColumnCount X n ω : ℝ)} :=
  forall_exists_measure_prunedColumnCount_ge hX hm fun hlam _ hε =>
    eventually_lam_rpow_le_integral_occupiedColumnCount hX hlam hε

end FractalGeometry.Probability.GridPercolation
