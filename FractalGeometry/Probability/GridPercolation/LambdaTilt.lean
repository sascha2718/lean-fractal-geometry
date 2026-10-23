import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.Lambda
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Processes

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open Finset Filter

lemma exp_le_one_add_add_sq {x : ℝ} (hx : |x| ≤ 1) : Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hx)).2
  linarith

namespace GridLaw

variable (A : GridLaw)

noncomputable def colLogBound : ℝ := 1 + ∑ i ∈ A.cols, |Real.log (A.E i)|

lemma one_le_colLogBound : 1 ≤ A.colLogBound :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)

lemma colLogBound_pos : 0 < A.colLogBound := lt_of_lt_of_le one_pos A.one_le_colLogBound

lemma abs_log_E_le_colLogBound {i : Fin A.M} (hi : i ∈ A.cols) :
    |Real.log (A.E i)| ≤ A.colLogBound := by
  have h := Finset.single_le_sum (f := fun i => |Real.log (A.E i)|)
    (fun _ _ => abs_nonneg _) hi
  unfold colLogBound
  linarith

noncomputable def colDeriv (β : ℝ) : ℝ := ∑ i ∈ A.cols, A.E i ^ β * Real.log (A.E i)

lemma colSum_nonneg_real (β : ℝ) : 0 ≤ A.colSum β :=
  Finset.sum_nonneg fun i _ => Real.rpow_nonneg (A.E_nonneg i) _

lemma colSum_add_le (β : ℝ) {u : ℝ} (hu : |u| ≤ A.colLogBound⁻¹) :
    A.colSum (β + u) ≤
      A.colSum β + u * A.colDeriv β + u ^ 2 * A.colLogBound ^ 2 * A.colSum β := by
  have hterm : ∀ i ∈ A.cols, A.E i ^ (β + u) ≤
      A.E i ^ β + u * (A.E i ^ β * Real.log (A.E i)) +
        u ^ 2 * A.colLogBound ^ 2 * A.E i ^ β := by
    intro i hi
    have hE := A.E_pos_of_mem_cols hi
    have hL := A.colLogBound_pos
    have hlog := A.abs_log_E_le_colLogBound hi
    have hx : |Real.log (A.E i) * u| ≤ 1 := by
      rw [abs_mul]
      calc |Real.log (A.E i)| * |u| ≤ A.colLogBound * A.colLogBound⁻¹ :=
            mul_le_mul hlog hu (abs_nonneg _) hL.le
        _ = 1 := mul_inv_cancel₀ hL.ne'
    have hexp := exp_le_one_add_add_sq hx
    have hsq : Real.log (A.E i) ^ 2 ≤ A.colLogBound ^ 2 :=
      sq_le_sq' (abs_le.mp hlog).1 (abs_le.mp hlog).2
    have hβ : 0 ≤ A.E i ^ β := Real.rpow_nonneg hE.le β
    rw [Real.rpow_add hE, Real.rpow_def_of_pos hE u]
    have h1 : A.E i ^ β * Real.exp (Real.log (A.E i) * u) ≤
        A.E i ^ β * (1 + Real.log (A.E i) * u + (Real.log (A.E i) * u) ^ 2) :=
      mul_le_mul_of_nonneg_left hexp hβ
    have h2 : A.E i ^ β * (Real.log (A.E i) * u) ^ 2 ≤
        u ^ 2 * A.colLogBound ^ 2 * A.E i ^ β := by
      have h3 : A.E i ^ β * (Real.log (A.E i) * u) ^ 2 =
          (u ^ 2 * A.E i ^ β) * Real.log (A.E i) ^ 2 := by ring
      have h4 : u ^ 2 * A.colLogBound ^ 2 * A.E i ^ β =
          (u ^ 2 * A.E i ^ β) * A.colLogBound ^ 2 := by ring
      rw [h3, h4]
      exact mul_le_mul_of_nonneg_left hsq (mul_nonneg (sq_nonneg u) hβ)
    have h5 : A.E i ^ β * (1 + Real.log (A.E i) * u + (Real.log (A.E i) * u) ^ 2) =
        A.E i ^ β + u * (A.E i ^ β * Real.log (A.E i)) +
          A.E i ^ β * (Real.log (A.E i) * u) ^ 2 := by ring
    linarith
  calc A.colSum (β + u) = ∑ i ∈ A.cols, A.E i ^ (β + u) := rfl
    _ ≤ ∑ i ∈ A.cols, (A.E i ^ β + u * (A.E i ^ β * Real.log (A.E i)) +
        u ^ 2 * A.colLogBound ^ 2 * A.E i ^ β) := Finset.sum_le_sum hterm
    _ = A.colSum β + u * A.colDeriv β + u ^ 2 * A.colLogBound ^ 2 * A.colSum β := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rfl

lemma colSum_add_le_mul_exp {β : ℝ} (hpos : 0 < A.colSum β) {u : ℝ}
    (hu : |u| ≤ A.colLogBound⁻¹) :
    A.colSum (β + u) ≤ A.colSum β *
      Real.exp (u * (A.colDeriv β / A.colSum β) + u ^ 2 * A.colLogBound ^ 2) := by
  have h := A.colSum_add_le β hu
  have hexp := Real.add_one_le_exp
    (u * (A.colDeriv β / A.colSum β) + u ^ 2 * A.colLogBound ^ 2)
  have hne := hpos.ne'
  have heq : A.colSum β + u * A.colDeriv β + u ^ 2 * A.colLogBound ^ 2 * A.colSum β =
      A.colSum β * (u * (A.colDeriv β / A.colSum β) + u ^ 2 * A.colLogBound ^ 2 + 1) := by
    field_simp
    ring
  calc A.colSum (β + u) ≤ _ := h
    _ = _ := heq
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp hpos.le

lemma exists_colSum_tilt (hc : A.cols.Nonempty) :
    ∃ β ∈ Set.Icc (0 : ℝ) 1, A.colSum β = A.lam ∧ 0 < A.lam ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ (t - β) * A.colDeriv β := by
  obtain ⟨β, hβ, hval, hmin⟩ := A.lam_isMinOn
  have hpos : 0 < A.colSum β :=
    Finset.sum_pos (fun i hi => Real.rpow_pos_of_pos (A.E_pos_of_mem_cols hi) β) hc
  refine ⟨β, hβ, hval, by rw [← hval]; exact hpos, fun t ht => ?_⟩
  by_contra hneg
  push Not at hneg
  have hLpos : 0 < A.colLogBound := A.colLogBound_pos
  have hL1 : 1 ≤ A.colLogBound := A.one_le_colLogBound
  obtain ⟨v, hv⟩ : ∃ v, v = t - β := ⟨_, rfl⟩
  rw [← hv] at hneg
  have hvne : v ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hneg
    exact lt_irrefl 0 hneg
  have hvabs : |v| ≤ 1 := by
    rw [abs_le, hv]
    constructor <;> linarith [ht.1, ht.2, hβ.1, hβ.2]
  have hv2 : 0 < v ^ 2 := by positivity
  have hden : 0 < 2 * (v ^ 2 * A.colLogBound ^ 2 * A.colSum β) := by positivity
  obtain ⟨s, hs⟩ : ∃ s, s = min A.colLogBound⁻¹
      (-(v * A.colDeriv β) / (2 * (v ^ 2 * A.colLogBound ^ 2 * A.colSum β))) := ⟨_, rfl⟩
  have hs0 : 0 < s := by
    rw [hs]
    exact lt_min (inv_pos.mpr hLpos) (div_pos (by linarith) hden)
  have hsL : s ≤ A.colLogBound⁻¹ := by rw [hs]; exact min_le_left _ _
  have hs1 : s ≤ 1 := hsL.trans (inv_le_one_of_one_le₀ hL1)
  have hs2 : s ≤ -(v * A.colDeriv β) / (2 * (v ^ 2 * A.colLogBound ^ 2 * A.colSum β)) := by
    rw [hs]; exact min_le_right _ _
  have hu : |s * v| ≤ A.colLogBound⁻¹ := by
    rw [abs_mul, abs_of_pos hs0]
    calc s * |v| ≤ s * 1 := mul_le_mul_of_nonneg_left hvabs hs0.le
      _ = s := mul_one s
      _ ≤ A.colLogBound⁻¹ := hsL
  have hconv : β + s * v = (1 - s) * β + s * t := by rw [hv]; ring
  have hmem : β + s * v ∈ Set.Icc (0 : ℝ) 1 := by
    rw [hconv]
    constructor
    · nlinarith [mul_nonneg hs0.le ht.1, mul_nonneg (sub_nonneg.mpr hs1) hβ.1]
    · nlinarith [mul_le_mul_of_nonneg_left ht.2 hs0.le,
        mul_le_mul_of_nonneg_left hβ.2 (sub_nonneg.mpr hs1)]
  have hup := A.colSum_add_le β hu
  have hlow := hmin _ hmem
  have h0 : 0 ≤ s * v * A.colDeriv β + (s * v) ^ 2 * A.colLogBound ^ 2 * A.colSum β := by
    linarith
  have hsd : s * (2 * (v ^ 2 * A.colLogBound ^ 2 * A.colSum β)) ≤ -(v * A.colDeriv β) :=
    (le_div_iff₀ hden).mp hs2
  have h1 := mul_le_mul_of_nonneg_left hsd hs0.le
  have h2 := mul_neg_of_pos_of_neg hs0 hneg
  nlinarith [h0, h1, h2]

end GridLaw

variable {A : GridLaw}

noncomputable def prefixMeanProduct {ℓ : ℕ} (σ : ColumnWord A ℓ) (k : ℕ) : ℝ :=
  ∏ l ∈ univ.filter (fun l : Fin ℓ => (l : ℕ) < k), A.E (σ l)

noncomputable def minPrefixMeanProduct {ℓ : ℕ} (σ : ColumnWord A ℓ) : ℝ :=
  (range (ℓ + 1)).inf' ⟨0, by simp⟩ (prefixMeanProduct σ)

noncomputable def allowedColumnWords (A : GridLaw) (ℓ : ℕ) : Finset (ColumnWord A ℓ) :=
  Fintype.piFinset fun _ => A.cols

noncomputable def prefixLogSum {ℓ : ℕ} (σ : ColumnWord A ℓ) (k : ℕ) : ℝ :=
  ∑ l ∈ univ.filter (fun l : Fin ℓ => (l : ℕ) < k), Real.log (A.E (σ l))

def prefixCount (ℓ k : ℕ) : ℕ := (univ.filter (fun l : Fin ℓ => (l : ℕ) < k)).card

noncomputable def tiltWeight {ℓ : ℕ} (β : ℝ) (σ : ColumnWord A ℓ) : ℝ :=
  ∏ l, A.E (σ l) ^ β

lemma mem_allowedColumnWords {ℓ : ℕ} {σ : ColumnWord A ℓ} :
    σ ∈ allowedColumnWords A ℓ ↔ ∀ l, σ l ∈ A.cols :=
  Fintype.mem_piFinset

lemma E_pos_of_mem_allowedColumnWords {ℓ : ℕ} {σ : ColumnWord A ℓ}
    (hσ : σ ∈ allowedColumnWords A ℓ) (l : Fin ℓ) : 0 < A.E (σ l) :=
  A.E_pos_of_mem_cols (mem_allowedColumnWords.mp hσ l)

lemma prefixCount_le (ℓ k : ℕ) : prefixCount ℓ k ≤ ℓ :=
  (card_filter_le _ _).trans (by simp)

lemma minPrefixMeanProduct_nonneg {ℓ : ℕ} (σ : ColumnWord A ℓ) :
    0 ≤ minPrefixMeanProduct σ :=
  Finset.le_inf' _ _ fun _ _ => Finset.prod_nonneg fun _ _ => A.E_nonneg _

lemma tiltWeight_nonneg {ℓ : ℕ} (β : ℝ) (σ : ColumnWord A ℓ) : 0 ≤ tiltWeight β σ :=
  Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (A.E_nonneg _) _

lemma prefixMeanProduct_eq_exp {ℓ : ℕ} {σ : ColumnWord A ℓ}
    (hσ : σ ∈ allowedColumnWords A ℓ) (k : ℕ) :
    prefixMeanProduct σ k = Real.exp (prefixLogSum σ k) := by
  rw [prefixLogSum, Real.exp_sum, prefixMeanProduct]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Real.exp_log (E_pos_of_mem_allowedColumnWords hσ l)]

lemma tiltWeight_eq_exp {ℓ : ℕ} {σ : ColumnWord A ℓ}
    (hσ : σ ∈ allowedColumnWords A ℓ) (β : ℝ) :
    tiltWeight β σ = Real.exp (β * ∑ l, Real.log (A.E (σ l))) := by
  rw [Finset.mul_sum, Real.exp_sum, tiltWeight]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Real.rpow_def_of_pos (E_pos_of_mem_allowedColumnWords hσ l), mul_comm]

lemma sum_prod_rpow_eq {ℓ : ℕ} (β : ℝ) (a : Fin ℓ → ℝ) :
    ∑ σ ∈ allowedColumnWords A ℓ, ∏ l, A.E (σ l) ^ (β + a l) =
      ∏ l, A.colSum (β + a l) := by
  rw [allowedColumnWords]
  exact (Finset.prod_univ_sum (fun _ : Fin ℓ => A.cols)
    (fun l i => A.E i ^ (β + a l))).symm

lemma sum_tiltWeight_eq {ℓ : ℕ} (β : ℝ) :
    ∑ σ ∈ allowedColumnWords A ℓ, tiltWeight β σ = A.colSum β ^ ℓ := by
  have h := sum_prod_rpow_eq (A := A) (ℓ := ℓ) β (fun _ => 0)
  simp only [add_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  exact h

lemma sum_prod_rpow_le {ℓ : ℕ} {β : ℝ} (hpos : 0 < A.colSum β) (a : Fin ℓ → ℝ)
    (ha : ∀ l, |a l| ≤ A.colLogBound⁻¹) :
    ∑ σ ∈ allowedColumnWords A ℓ, ∏ l, A.E (σ l) ^ (β + a l) ≤
      A.colSum β ^ ℓ * Real.exp (∑ l, (a l * (A.colDeriv β / A.colSum β) +
        a l ^ 2 * A.colLogBound ^ 2)) := by
  rw [sum_prod_rpow_eq, Real.exp_sum]
  calc ∏ l, A.colSum (β + a l)
      ≤ ∏ l, (A.colSum β * Real.exp (a l * (A.colDeriv β / A.colSum β) +
          a l ^ 2 * A.colLogBound ^ 2)) :=
        Finset.prod_le_prod₀ (fun _ _ => A.colSum_nonneg_real _)
          fun l _ => A.colSum_add_le_mul_exp hpos (ha l)
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma sum_filter_tiltWeight_le {ℓ : ℕ} {β : ℝ} (hpos : 0 < A.colSum β) (a : Fin ℓ → ℝ)
    (ha : ∀ l, |a l| ≤ A.colLogBound⁻¹) (θ : ℝ) :
    ∑ σ ∈ (allowedColumnWords A ℓ).filter
        (fun σ => θ < ∑ l, a l * Real.log (A.E (σ l))), tiltWeight β σ ≤
      A.colSum β ^ ℓ * Real.exp (-θ + ∑ l, (a l * (A.colDeriv β / A.colSum β) +
        a l ^ 2 * A.colLogBound ^ 2)) := by
  have hpoint : ∀ σ ∈ allowedColumnWords A ℓ,
      ∏ l, A.E (σ l) ^ (β + a l) =
        tiltWeight β σ * Real.exp (∑ l, a l * Real.log (A.E (σ l))) := by
    intro σ hσ
    rw [tiltWeight, Real.exp_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    have hE := E_pos_of_mem_allowedColumnWords hσ l
    rw [Real.rpow_add hE, Real.rpow_def_of_pos hE (a l), mul_comm (Real.log _) (a l)]
  have hprod_nonneg : ∀ σ : ColumnWord A ℓ, 0 ≤ ∏ l, A.E (σ l) ^ (β + a l) :=
    fun σ => Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (A.E_nonneg _) _
  calc ∑ σ ∈ (allowedColumnWords A ℓ).filter
          (fun σ => θ < ∑ l, a l * Real.log (A.E (σ l))), tiltWeight β σ
      ≤ ∑ σ ∈ (allowedColumnWords A ℓ).filter
          (fun σ => θ < ∑ l, a l * Real.log (A.E (σ l))),
          Real.exp (-θ) * ∏ l, A.E (σ l) ^ (β + a l) := by
        refine Finset.sum_le_sum fun σ hσ => ?_
        rw [Finset.mem_filter] at hσ
        rw [hpoint σ hσ.1]
        have hw := tiltWeight_nonneg β σ
        have h1 : 1 ≤ Real.exp (-θ) * Real.exp (∑ l, a l * Real.log (A.E (σ l))) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by linarith [hσ.2])
        calc tiltWeight β σ = tiltWeight β σ * 1 := (mul_one _).symm
          _ ≤ tiltWeight β σ *
              (Real.exp (-θ) * Real.exp (∑ l, a l * Real.log (A.E (σ l)))) :=
            mul_le_mul_of_nonneg_left h1 hw
          _ = Real.exp (-θ) *
              (tiltWeight β σ * Real.exp (∑ l, a l * Real.log (A.E (σ l)))) := by ring
    _ ≤ ∑ σ ∈ allowedColumnWords A ℓ, Real.exp (-θ) * ∏ l, A.E (σ l) ^ (β + a l) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun σ _ _ => mul_nonneg (Real.exp_pos _).le (hprod_nonneg σ)
    _ = Real.exp (-θ) * ∑ σ ∈ allowedColumnWords A ℓ, ∏ l, A.E (σ l) ^ (β + a l) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-θ) * (A.colSum β ^ ℓ * Real.exp (∑ l, (a l * (A.colDeriv β / A.colSum β) +
          a l ^ 2 * A.colLogBound ^ 2))) :=
        mul_le_mul_of_nonneg_left (sum_prod_rpow_le hpos a ha) (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_add]; ring

lemma eventually_tilt_sizes {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ ℓ : ℕ in atTop, 1 ≤ ℓ ∧ 2 ≤ Real.exp (ε / 2 * ℓ) ∧
      ((ℓ : ℝ) + 2) * Real.exp (-c * ℓ) ≤ 1 / 2 := by
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈2 / ε⌉₊,
    eventually_ge_atTop ⌈24 / c ^ 2⌉₊] with ℓ h1 h2 h3
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast h1
  have hℓ2 : 2 / ε ≤ ℓ := (Nat.le_ceil _).trans (by exact_mod_cast h2)
  have hℓ3 : 24 / c ^ 2 ≤ ℓ := (Nat.le_ceil _).trans (by exact_mod_cast h3)
  refine ⟨h1, ?_, ?_⟩
  · have he := Real.add_one_le_exp (ε / 2 * ℓ)
    have h2ε : 2 ≤ ℓ * ε := (div_le_iff₀ hε).mp hℓ2
    linarith
  · have hcl' : 0 ≤ c * ℓ := mul_nonneg hc.le (Nat.cast_nonneg _)
    have he := Real.add_one_le_exp (c * ℓ / 2)
    have hsq : Real.exp (c * ℓ) = Real.exp (c * ℓ / 2) * Real.exp (c * ℓ / 2) := by
      rw [← Real.exp_add]; ring_nf
    have h24 : 24 ≤ ℓ * c ^ 2 := (div_le_iff₀ (pow_pos hc 2)).mp hℓ3
    have hprod := mul_le_mul he he (by linarith) (Real.exp_pos _).le
    have h24ℓ := mul_le_mul_of_nonneg_right h24 (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)
    have hbig : 2 * ((ℓ : ℝ) + 2) ≤ Real.exp (c * ℓ) := by
      rw [hsq]
      linarith
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    linarith

lemma mul_le_prefixCount_mul {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {β μ : ℝ} (hpos : 0 < A.colSum β)
    (hμ : μ = A.colDeriv β / A.colSum β)
    (hopt : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ (t - β) * A.colDeriv β) (k : ℕ) :
    β * ℓ * μ ≤ prefixCount ℓ k * μ := by
  have hℓpos : (0 : ℝ) < ℓ := Nat.cast_pos.mpr hℓ
  have hℓne := hℓpos.ne'
  have hSne := hpos.ne'
  have hp : (prefixCount ℓ k : ℝ) ≤ ℓ := by exact_mod_cast prefixCount_le ℓ k
  have h01 : (prefixCount ℓ k : ℝ) / ℓ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (Nat.cast_nonneg _) hℓpos.le, (div_le_one hℓpos).mpr hp⟩
  have h1 : 0 ≤ ((prefixCount ℓ k : ℝ) / ℓ - β) * A.colDeriv β * (ℓ / A.colSum β) :=
    mul_nonneg (hopt _ h01) (div_nonneg hℓpos.le hpos.le)
  have h2 : ((prefixCount ℓ k : ℝ) / ℓ - β) * A.colDeriv β * (ℓ / A.colSum β) =
      prefixCount ℓ k * μ - β * ℓ * μ := by
    rw [hμ]
    field_simp
  linarith

lemma sum_filter_prefixLogSum_lt_le {ℓ : ℕ} {β μ t δ c : ℝ} (hpos : 0 < A.colSum β)
    (hμ : μ = A.colDeriv β / A.colSum β) (ht0 : 0 < t) (htL : t ≤ A.colLogBound⁻¹)
    (hrate : -t * δ + t ^ 2 * A.colLogBound ^ 2 = -c) (k : ℕ) :
    ∑ σ ∈ (allowedColumnWords A ℓ).filter
        (fun σ => prefixLogSum σ k < prefixCount ℓ k * μ - δ * ℓ), tiltWeight β σ ≤
      A.colSum β ^ ℓ * Real.exp (-c * ℓ) := by
  obtain ⟨a, ha⟩ : ∃ a : Fin ℓ → ℝ, a = fun l : Fin ℓ => if (l : ℕ) < k then -t else 0 :=
    ⟨_, rfl⟩
  have habs : ∀ l, |a l| ≤ A.colLogBound⁻¹ := by
    intro l
    simp only [ha]
    split_ifs
    · rw [abs_neg, abs_of_pos ht0]; exact htL
    · rw [abs_zero]; exact (inv_pos.mpr A.colLogBound_pos).le
  have hsum_a : ∀ σ : ColumnWord A ℓ,
      ∑ l, a l * Real.log (A.E (σ l)) = -t * prefixLogSum σ k := by
    intro σ
    rw [prefixLogSum, Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [ha]
    split_ifs <;> ring
  have hexpo : ∑ l, (a l * μ + a l ^ 2 * A.colLogBound ^ 2) =
      (prefixCount ℓ k : ℝ) * (-t * μ + t ^ 2 * A.colLogBound ^ 2) := by
    rw [prefixCount, Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [ha]
    split_ifs <;> push_cast <;> ring
  have hsub : (allowedColumnWords A ℓ).filter
        (fun σ => prefixLogSum σ k < prefixCount ℓ k * μ - δ * ℓ) ⊆
      (allowedColumnWords A ℓ).filter
        (fun σ => -t * (prefixCount ℓ k * μ - δ * ℓ) < ∑ l, a l * Real.log (A.E (σ l))) := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ ⊢
    refine ⟨hσ.1, ?_⟩
    rw [hsum_a]
    exact mul_lt_mul_of_neg_left hσ.2 (neg_neg_of_pos ht0)
  have hp : (prefixCount ℓ k : ℝ) ≤ ℓ := by exact_mod_cast prefixCount_le ℓ k
  have hsqL : 0 ≤ t ^ 2 * A.colLogBound ^ 2 := by positivity
  have h := sum_filter_tiltWeight_le (β := β) hpos a habs (-t * (prefixCount ℓ k * μ - δ * ℓ))
  rw [← hμ, hexpo] at h
  calc _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun σ _ _ => tiltWeight_nonneg β σ
    _ ≤ _ := h
    _ ≤ A.colSum β ^ ℓ * Real.exp (-c * ℓ) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (pow_nonneg hpos.le ℓ)
        have h1 := mul_le_mul_of_nonneg_right hp hsqL
        have h2 : (ℓ : ℝ) * (-t * δ + t ^ 2 * A.colLogBound ^ 2) = ℓ * (-c) := by rw [hrate]
        linarith

lemma sum_filter_logSum_gt_le {ℓ : ℕ} {β μ t δ c : ℝ} (hpos : 0 < A.colSum β)
    (hμ : μ = A.colDeriv β / A.colSum β) (ht0 : 0 < t) (htL : t ≤ A.colLogBound⁻¹)
    (hrate : -t * δ + t ^ 2 * A.colLogBound ^ 2 = -c) :
    ∑ σ ∈ (allowedColumnWords A ℓ).filter
        (fun σ => (ℓ : ℝ) * μ + δ * ℓ < ∑ l, Real.log (A.E (σ l))), tiltWeight β σ ≤
      A.colSum β ^ ℓ * Real.exp (-c * ℓ) := by
  have habs : ∀ l : Fin ℓ, |(fun _ : Fin ℓ => t) l| ≤ A.colLogBound⁻¹ := fun _ => by
    show |t| ≤ _
    rw [abs_of_pos ht0]
    exact htL
  have hsub : (allowedColumnWords A ℓ).filter
        (fun σ => (ℓ : ℝ) * μ + δ * ℓ < ∑ l, Real.log (A.E (σ l))) ⊆
      (allowedColumnWords A ℓ).filter
        (fun σ => t * (ℓ * μ + δ * ℓ) <
          ∑ l, (fun _ : Fin ℓ => t) l * Real.log (A.E (σ l))) := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ ⊢
    refine ⟨hσ.1, ?_⟩
    show t * (ℓ * μ + δ * ℓ) < ∑ l, t * Real.log (A.E (σ l))
    rw [← Finset.mul_sum]
    exact mul_lt_mul_of_pos_left hσ.2 ht0
  have h := sum_filter_tiltWeight_le (β := β) hpos (fun _ : Fin ℓ => t) habs
    (t * (ℓ * μ + δ * ℓ))
  rw [← hμ] at h
  calc _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun σ _ _ => tiltWeight_nonneg β σ
    _ ≤ _ := h
    _ = A.colSum β ^ ℓ * Real.exp (-c * ℓ) := by
        congr 2
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        linear_combination (ℓ : ℝ) * hrate

lemma exp_mul_sub_bad_le_minPrefixMeanProduct {ℓ : ℕ} {β μ δ : ℝ}
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hδ : 0 ≤ δ)
    (hmono : ∀ k, β * ℓ * μ ≤ prefixCount ℓ k * μ) {σ : ColumnWord A ℓ}
    (hσ : σ ∈ allowedColumnWords A ℓ) :
    Real.exp (-(2 * δ) * ℓ) * (tiltWeight β σ -
      (∑ k ∈ range (ℓ + 1),
          (if prefixLogSum σ k < prefixCount ℓ k * μ - δ * ℓ then tiltWeight β σ else 0) +
        (if (ℓ : ℝ) * μ + δ * ℓ < ∑ l, Real.log (A.E (σ l)) then tiltWeight β σ else 0))) ≤
      minPrefixMeanProduct σ := by
  have hw0 := tiltWeight_nonneg β σ
  have hite0 : ∀ k ∈ range (ℓ + 1), 0 ≤
      (if prefixLogSum σ k < prefixCount ℓ k * μ - δ * ℓ then tiltWeight β σ else 0) :=
    fun k _ => by split_ifs <;> simp [hw0]
  have hite0' : 0 ≤
      (if (ℓ : ℝ) * μ + δ * ℓ < ∑ l, Real.log (A.E (σ l)) then tiltWeight β σ else 0) := by
    split_ifs <;> simp [hw0]
  by_cases hbad : (∃ k ∈ range (ℓ + 1), prefixLogSum σ k < prefixCount ℓ k * μ - δ * ℓ) ∨
      (ℓ : ℝ) * μ + δ * ℓ < ∑ l, Real.log (A.E (σ l))
  · have hge : tiltWeight β σ ≤ ∑ k ∈ range (ℓ + 1),
          (if prefixLogSum σ k < prefixCount ℓ k * μ - δ * ℓ then tiltWeight β σ else 0) +
        (if (ℓ : ℝ) * μ + δ * ℓ < ∑ l, Real.log (A.E (σ l)) then tiltWeight β σ else 0) := by
      rcases hbad with ⟨k, hk, hlt⟩ | hlt
      · have h1 : (if prefixLogSum σ k < prefixCount ℓ k * μ - δ * ℓ then tiltWeight β σ
            else 0) ≤ ∑ k ∈ range (ℓ + 1),
              (if prefixLogSum σ k < prefixCount ℓ k * μ - δ * ℓ then tiltWeight β σ
                else 0) :=
          Finset.single_le_sum hite0 hk
        rw [ite_eq_left hlt] at h1
        linarith
      · have h1 := Finset.sum_nonneg hite0
        rw [ite_eq_left hlt]
        linarith
    have hnonpos : Real.exp (-(2 * δ) * ℓ) * (tiltWeight β σ -
        (∑ k ∈ range (ℓ + 1),
            (if prefixLogSum σ k < prefixCount ℓ k * μ - δ * ℓ then tiltWeight β σ else 0) +
          (if (ℓ : ℝ) * μ + δ * ℓ < ∑ l, Real.log (A.E (σ l)) then tiltWeight β σ
            else 0))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith)
    exact hnonpos.trans (minPrefixMeanProduct_nonneg σ)
  · push Not at hbad
    obtain ⟨hk, h'⟩ := hbad
    rw [Finset.sum_eq_zero fun k hk' => ite_eq_right (not_lt.mpr (hk k hk')),
      ite_eq_right (not_lt.mpr h'), add_zero, sub_zero]
    have hmin : Real.exp (β * ℓ * μ - δ * ℓ) ≤ minPrefixMeanProduct σ := by
      refine Finset.le_inf' _ _ fun k hk' => ?_
      rw [prefixMeanProduct_eq_exp hσ k]
      exact Real.exp_le_exp.mpr (by linarith [hk k hk', hmono k])
    have hw : tiltWeight β σ ≤ Real.exp (β * ℓ * μ + δ * ℓ) := by
      rw [tiltWeight_eq_exp hσ]
      refine Real.exp_le_exp.mpr ?_
      have hδℓ : 0 ≤ δ * ℓ := mul_nonneg hδ (Nat.cast_nonneg _)
      have h1 := mul_le_mul_of_nonneg_left h' hβ.1
      have h2 := mul_nonneg (sub_nonneg.mpr hβ.2) hδℓ
      linarith
    calc Real.exp (-(2 * δ) * ℓ) * tiltWeight β σ
        ≤ Real.exp (-(2 * δ) * ℓ) * Real.exp (β * ℓ * μ + δ * ℓ) :=
          mul_le_mul_of_nonneg_left hw (Real.exp_pos _).le
      _ = Real.exp (β * ℓ * μ - δ * ℓ) := by rw [← Real.exp_add]; ring_nf
      _ ≤ minPrefixMeanProduct σ := hmin

lemma sum_mul_sub_ite_eq {ι : Type*} (W : Finset ι) (w : ι → ℝ) (n : ℕ) (P : ℕ → ι → Prop)
    [∀ k, DecidablePred (P k)] (Q : ι → Prop) [DecidablePred Q] (e : ℝ) :
    ∑ σ ∈ W, e * (w σ - (∑ k ∈ range n, (if P k σ then w σ else 0) +
        (if Q σ then w σ else 0))) =
      e * (∑ σ ∈ W, w σ - (∑ k ∈ range n, ∑ σ ∈ W.filter (P k), w σ +
        ∑ σ ∈ W.filter Q, w σ)) := by
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_comm]
  simp only [Finset.sum_filter]

theorem eventually_lam_pow_mul_exp_le_sum_minPrefixMeanProduct (A : GridLaw) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ ℓ : ℕ in atTop, A.lam ^ ℓ * Real.exp (-ε * ℓ) ≤
      ∑ σ ∈ allowedColumnWords A ℓ, minPrefixMeanProduct σ := by
  rcases A.cols.eq_empty_or_nonempty with hc | hc
  · have hlam : A.lam = 0 := by
      obtain ⟨β, -, hval, -⟩ := A.lam_isMinOn
      rw [← hval, GridLaw.colSum, hc, Finset.sum_empty]
    filter_upwards [eventually_ge_atTop 1] with ℓ hℓ
    rw [hlam, zero_pow (by omega), zero_mul]
    exact Finset.sum_nonneg fun σ _ => minPrefixMeanProduct_nonneg σ
  obtain ⟨β, hβ, hval, hlam, hopt⟩ := A.exists_colSum_tilt hc
  have hpos : 0 < A.colSum β := by rw [hval]; exact hlam
  have hLpos := A.colLogBound_pos
  have hLne : A.colLogBound ≠ 0 := hLpos.ne'
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = A.colDeriv β / A.colSum β := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = min 1 (ε / 4) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min one_pos (by linarith)
  have hδ1 : δ ≤ 1 := by rw [hδ]; exact min_le_left _ _
  have hδε : δ ≤ ε / 4 := by rw [hδ]; exact min_le_right _ _
  have hL2pos : 0 < 2 * A.colLogBound ^ 2 := mul_pos two_pos (pow_pos hLpos 2)
  obtain ⟨t, ht⟩ : ∃ t, t = δ / (2 * A.colLogBound ^ 2) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; exact div_pos hδ0 hL2pos
  have htL : t ≤ A.colLogBound⁻¹ := by
    rw [ht, div_le_iff₀ hL2pos]
    have hinv : A.colLogBound⁻¹ * (2 * A.colLogBound ^ 2) = 2 * A.colLogBound := by
      rw [sq, ← mul_assoc, mul_comm (A.colLogBound⁻¹) 2, mul_assoc 2,
        inv_mul_cancel_left₀ hLne]
    rw [hinv]
    linarith [A.one_le_colLogBound]
  obtain ⟨c, hcdef⟩ : ∃ c, c = δ ^ 2 / (4 * A.colLogBound ^ 2) := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [hcdef]; exact div_pos (pow_pos hδ0 2) (mul_pos (by norm_num) (pow_pos hLpos 2))
  have hrate : -t * δ + t ^ 2 * A.colLogBound ^ 2 = -c := by
    rw [ht, hcdef]
    field_simp
    ring
  filter_upwards [eventually_tilt_sizes hε hc0] with ℓ ⟨hℓ1, hexpε, hsmall⟩
  have hℓpos : (0 : ℝ) < ℓ := Nat.cast_pos.mpr hℓ1
  have hlamℓ : 0 ≤ A.lam ^ ℓ := pow_nonneg hlam.le ℓ
  have hE0 : 0 < Real.exp (-(2 * δ) * ℓ) := Real.exp_pos _
  have hbadsum : ∑ k ∈ range (ℓ + 1), ∑ σ ∈ (allowedColumnWords A ℓ).filter
        (fun σ => prefixLogSum σ k < prefixCount ℓ k * μ - δ * ℓ), tiltWeight β σ +
      ∑ σ ∈ (allowedColumnWords A ℓ).filter
        (fun σ => (ℓ : ℝ) * μ + δ * ℓ < ∑ l, Real.log (A.E (σ l))), tiltWeight β σ ≤
      ((ℓ : ℝ) + 2) * (A.lam ^ ℓ * Real.exp (-c * ℓ)) := by
    have hk := fun k => sum_filter_prefixLogSum_lt_le (ℓ := ℓ) hpos hμ ht0 htL hrate k
    have h' := sum_filter_logSum_gt_le (ℓ := ℓ) hpos hμ ht0 htL hrate
    rw [hval] at h'
    calc _ ≤ ∑ _k ∈ range (ℓ + 1), A.lam ^ ℓ * Real.exp (-c * ℓ) +
          A.lam ^ ℓ * Real.exp (-c * ℓ) :=
        add_le_add (Finset.sum_le_sum fun k _ => (hk k).trans_eq (by rw [hval])) h'
      _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
  have htotal : ∑ σ ∈ allowedColumnWords A ℓ, tiltWeight β σ = A.lam ^ ℓ := by
    rw [sum_tiltWeight_eq, hval]
  have hfin : Real.exp (-ε * ℓ) ≤ Real.exp (-(2 * δ) * ℓ) * (1 / 2) := by
    have h1 : Real.exp (-ε * ℓ) = Real.exp (-(ε / 2 * ℓ)) * Real.exp (-(ε / 2 * ℓ)) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (-(ε / 2 * ℓ)) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      norm_num
      exact hexpε
    have h3 : Real.exp (-(ε / 2 * ℓ)) ≤ Real.exp (-(2 * δ) * ℓ) := by
      refine Real.exp_le_exp.mpr ?_
      have := mul_le_mul_of_nonneg_right (show 2 * δ ≤ ε / 2 by linarith) hℓpos.le
      linarith
    rw [h1]
    calc Real.exp (-(ε / 2 * ℓ)) * Real.exp (-(ε / 2 * ℓ))
        ≤ Real.exp (-(ε / 2 * ℓ)) * (1 / 2) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_right h3 (by norm_num)
  have hX : ((ℓ : ℝ) + 2) * (A.lam ^ ℓ * Real.exp (-c * ℓ)) ≤ A.lam ^ ℓ * (1 / 2) := by
    calc ((ℓ : ℝ) + 2) * (A.lam ^ ℓ * Real.exp (-c * ℓ))
        = A.lam ^ ℓ * (((ℓ : ℝ) + 2) * Real.exp (-c * ℓ)) := by ring
      _ ≤ A.lam ^ ℓ * (1 / 2) := mul_le_mul_of_nonneg_left hsmall hlamℓ
  have hsplit := sum_mul_sub_ite_eq (allowedColumnWords A ℓ) (tiltWeight β) (ℓ + 1)
    (fun k σ => prefixLogSum σ k < prefixCount ℓ k * μ - δ * ℓ)
    (fun σ => (ℓ : ℝ) * μ + δ * ℓ < ∑ l, Real.log (A.E (σ l))) (Real.exp (-(2 * δ) * ℓ))
  calc A.lam ^ ℓ * Real.exp (-ε * ℓ)
      ≤ A.lam ^ ℓ * (Real.exp (-(2 * δ) * ℓ) * (1 / 2)) :=
        mul_le_mul_of_nonneg_left hfin hlamℓ
    _ ≤ Real.exp (-(2 * δ) * ℓ) *
          (A.lam ^ ℓ - ((ℓ : ℝ) + 2) * (A.lam ^ ℓ * Real.exp (-c * ℓ))) := by
        have h := mul_le_mul_of_nonneg_left hX hE0.le
        rw [mul_sub]
        have heq : A.lam ^ ℓ * (Real.exp (-(2 * δ) * ℓ) * (1 / 2)) =
            Real.exp (-(2 * δ) * ℓ) * A.lam ^ ℓ -
              Real.exp (-(2 * δ) * ℓ) * (A.lam ^ ℓ * (1 / 2)) := by ring
        rw [heq]
        exact sub_le_sub_left h _
    _ ≤ Real.exp (-(2 * δ) * ℓ) * (∑ σ ∈ allowedColumnWords A ℓ, tiltWeight β σ -
          (∑ k ∈ range (ℓ + 1), ∑ σ ∈ (allowedColumnWords A ℓ).filter
              (fun σ => prefixLogSum σ k < prefixCount ℓ k * μ - δ * ℓ), tiltWeight β σ +
            ∑ σ ∈ (allowedColumnWords A ℓ).filter
              (fun σ => (ℓ : ℝ) * μ + δ * ℓ < ∑ l, Real.log (A.E (σ l))), tiltWeight β σ)) := by
        rw [htotal]
        exact mul_le_mul_of_nonneg_left (by linarith [hbadsum]) hE0.le
    _ = _ := hsplit.symm
    _ ≤ _ := Finset.sum_le_sum fun σ hσ =>
        exp_mul_sub_bad_le_minPrefixMeanProduct hβ hδ0.le
          (mul_le_prefixCount_mul hℓ1 hpos hμ hopt) hσ

end FractalGeometry.Probability.GridPercolation
