import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.Law

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open Finset

noncomputable def explorationEta (A : GridLaw) (j : ℕ) : ℝ :=
  (1 - (Real.sqrt (Real.sqrt A.m))⁻¹) / 4 * ((Real.sqrt (Real.sqrt A.m))⁻¹) ^ j

noncomputable def explorationSize (A : GridLaw) (K : ℕ → ℝ) (k₀ j : ℕ) : ℕ :=
  ⌈K (k₀ + j) * A.m ^ (k₀ + j)⌉₊

noncomputable def explorationThreshold (A : GridLaw) (K : ℕ → ℝ) (k₀ : ℕ) : ℕ → ℝ
  | 0 => A.m ^ k₀
  | j + 1 => (1 - explorationEta A j) * A.m *
      (explorationThreshold A K k₀ j - explorationSize A K k₀ j)

noncomputable def explorationFailure (A : GridLaw) (K : ℕ → ℝ) (k₀ j : ℕ) : ℝ :=
  Real.exp (-(2 * explorationEta A j ^ 2 * A.m ^ 2 *
    (explorationThreshold A K k₀ j - explorationSize A K k₀ j) / ((A.M : ℝ) * A.N) ^ 2))

lemma geomPartialSum_mul_le {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (1 - x) * ∑ i ∈ range n, x ^ i ≤ 1 := by
  have h := geom_sum_mul x n
  have hpow : 0 ≤ x ^ n := pow_nonneg hx n
  have h' : (1 - x) * ∑ i ∈ range n, x ^ i = 1 - x ^ n := by
    rw [show (1 - x) * ∑ i ∈ range n, x ^ i = -((∑ i ∈ range n, x ^ i) * (x - 1)) by ring, h]
    ring
  linarith

lemma exp_neg_le_one_div_add_one {y : ℝ} (hy : 0 ≤ y) : Real.exp (-y) ≤ 1 / (y + 1) := by
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by linarith) (Real.add_one_le_exp y)

lemma exploration_one_lt_sqrt {x : ℝ} (hx : 1 < x) : 1 < Real.sqrt x := by
  have h := Real.sqrt_lt_sqrt zero_le_one hx
  rwa [Real.sqrt_one] at h

lemma explorationRatio_mem (A : GridLaw) (hm : 1 < A.m) :
    0 < (Real.sqrt (Real.sqrt A.m))⁻¹ ∧ (Real.sqrt (Real.sqrt A.m))⁻¹ < 1 := by
  have hs := exploration_one_lt_sqrt (exploration_one_lt_sqrt hm)
  exact ⟨inv_pos.mpr (by linarith), inv_lt_one_of_one_lt₀ hs⟩

lemma explorationEta_nonneg (A : GridLaw) (hm : 1 < A.m) (j : ℕ) : 0 ≤ explorationEta A j := by
  obtain ⟨ht0, ht1⟩ := explorationRatio_mem A hm
  unfold explorationEta
  generalize (Real.sqrt (Real.sqrt A.m))⁻¹ = t at ht0 ht1 ⊢
  exact mul_nonneg (by linarith) (pow_nonneg ht0.le j)

lemma explorationEta_le_one (A : GridLaw) (hm : 1 < A.m) (j : ℕ) : explorationEta A j ≤ 1 := by
  obtain ⟨ht0, ht1⟩ := explorationRatio_mem A hm
  unfold explorationEta
  generalize (Real.sqrt (Real.sqrt A.m))⁻¹ = t at ht0 ht1 ⊢
  have hpow : t ^ j ≤ 1 := pow_le_one₀ ht0.le ht1.le
  have hd : 0 ≤ (1 - t) / 4 := by linarith
  calc (1 - t) / 4 * t ^ j ≤ (1 - t) / 4 * 1 := mul_le_mul_of_nonneg_left hpow hd
    _ ≤ 1 := by linarith

lemma sum_explorationEta_le (A : GridLaw) (hm : 1 < A.m) (J : ℕ) :
    ∑ j ∈ range J, explorationEta A j ≤ 1 / 4 := by
  obtain ⟨ht0, ht1⟩ := explorationRatio_mem A hm
  unfold explorationEta
  generalize (Real.sqrt (Real.sqrt A.m))⁻¹ = t at ht0 ht1 ⊢
  rw [← Finset.mul_sum]
  have h := geomPartialSum_mul_le ht0.le J
  have heq : (1 - t) / 4 * ∑ i ∈ range J, t ^ i = ((1 - t) * ∑ i ∈ range J, t ^ i) / 4 := by
    ring
  rw [heq]
  linarith

lemma explorationEta_sq_mul_pow (A : GridLaw) (hm : 1 < A.m) (k₀ j : ℕ) :
    explorationEta A j ^ 2 * A.m ^ (k₀ + j) =
      ((1 - (Real.sqrt (Real.sqrt A.m))⁻¹) / 4) ^ 2 * A.m ^ k₀ * Real.sqrt A.m ^ j := by
  have hm0 : 0 < A.m := by linarith
  have hr0 : 0 < Real.sqrt A.m := Real.sqrt_pos.mpr hm0
  have hs2 : Real.sqrt (Real.sqrt A.m) ^ 2 = Real.sqrt A.m := Real.sq_sqrt hr0.le
  have htm : ((Real.sqrt (Real.sqrt A.m))⁻¹) ^ 2 * A.m = Real.sqrt A.m := by
    rw [inv_pow, hs2, inv_mul_eq_div, div_eq_iff hr0.ne']
    exact (Real.mul_self_sqrt hm0.le).symm
  unfold explorationEta
  generalize (1 - (Real.sqrt (Real.sqrt A.m))⁻¹) / 4 = d
  generalize (Real.sqrt (Real.sqrt A.m))⁻¹ = t at htm
  calc (d * t ^ j) ^ 2 * A.m ^ (k₀ + j) = d ^ 2 * A.m ^ k₀ * (t ^ 2 * A.m) ^ j := by ring
    _ = d ^ 2 * A.m ^ k₀ * Real.sqrt A.m ^ j := by rw [htm]

lemma threshold_invariant_aux {η a μ : ℕ → ℝ} (hη0 : ∀ j, 0 ≤ η j) (hη1 : ∀ j, η j ≤ 1)
    (ha : ∀ j, 0 ≤ a j) (hμ0 : μ 0 = 1) (hμ : ∀ j, μ (j + 1) = (1 - η j) * (μ j - a j)) :
    ∀ j, μ j ≤ 1 ∧ 1 - ∑ i ∈ range j, (η i + a i) ≤ μ j := by
  intro j
  induction j with
  | zero => simp [hμ0]
  | succ j ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [hμ j, Finset.sum_range_succ]
      have e0 := hη0 j
      have e1 := hη1 j
      have a0 := ha j
      constructor
      · nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr e1),
          mul_nonneg (sub_nonneg.mpr e1) a0]
      · nlinarith [mul_le_mul_of_nonneg_left h1 e0, mul_nonneg e0 a0]

theorem exists_explorationStart (A : GridLaw) (hm : 1 < A.m) :
    ∃ k₀ : ℕ, ∀ K : ℕ → ℝ, (∀ n, 0 ≤ K n) → Summable K → ∑' n, K n ≤ 1 / 4 →
      (∀ j, 0 ≤ explorationEta A j ∧ explorationEta A j ≤ 1) ∧
      (∀ j, (explorationSize A K k₀ j : ℝ) ≤ explorationThreshold A K k₀ j) ∧
      (∀ J, ∑ j ∈ Finset.range J, explorationFailure A K k₀ j ≤ 1 / 2) := by
  have hm0 : 0 < A.m := by linarith
  obtain ⟨ht0, ht1⟩ := explorationRatio_mem A hm
  have hd0 : 0 < (1 - (Real.sqrt (Real.sqrt A.m))⁻¹) / 4 := by linarith
  have hr1 : 0 < Real.sqrt A.m - 1 := by linarith [exploration_one_lt_sqrt hm]
  have hMN : (0 : ℝ) < (A.M : ℝ) * A.N := by
    have hM0 : (0 : ℝ) < A.M := by exact_mod_cast A.hM_pos
    have hN0 : (0 : ℝ) < A.N := by exact_mod_cast A.hN_pos
    positivity
  have hu : 0 < 1 - A.m⁻¹ := by linarith [inv_lt_one_of_one_lt₀ hm]
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = ((1 - (Real.sqrt (Real.sqrt A.m))⁻¹) / 4) ^ 2 * A.m ^ 2 /
      (8 * ((A.M : ℝ) * A.N) ^ 2) := ⟨_, rfl⟩
  have hγ0 : 0 < γ := by
    rw [hγ]
    exact div_pos (mul_pos (pow_pos hd0 2) (pow_pos hm0 2))
      (mul_pos (by norm_num) (pow_pos hMN 2))
  obtain ⟨k₀, hk₀⟩ := pow_unbounded_of_one_lt
    (max (max 16 (8 / (1 - A.m⁻¹))) (max 3 (1 / (Real.sqrt A.m - 1)) / γ)) hm
  have hk16 : 16 ≤ A.m ^ k₀ :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hk₀.le
  have hk8 : 8 ≤ A.m ^ k₀ * (1 - A.m⁻¹) :=
    (div_le_iff₀ hu).mp (((le_max_right _ _).trans (le_max_left _ _)).trans hk₀.le)
  have hkx : max 3 (1 / (Real.sqrt A.m - 1)) ≤ A.m ^ k₀ * γ :=
    (div_le_iff₀ hγ0).mp ((le_max_right _ _).trans hk₀.le)
  have hx3 : 3 ≤ γ * A.m ^ k₀ := by
    linarith [le_max_left 3 (1 / (Real.sqrt A.m - 1))]
  have hx1 : 1 ≤ γ * A.m ^ k₀ * (Real.sqrt A.m - 1) := by
    have h := (le_max_right 3 (1 / (Real.sqrt A.m - 1))).trans hkx
    rw [div_le_iff₀ hr1] at h
    linarith
  refine ⟨k₀, fun K hK0 hKs hKsum => ?_⟩
  have hp0 : ∀ j, 0 < A.m ^ (k₀ + j) := fun j => pow_pos hm0 _
  have hKle : ∀ n, K n ≤ 1 / 4 := fun n => (hKs.le_tsum n fun i _ => hK0 i).trans hKsum
  have hceil : ∀ j, (explorationSize A K k₀ j : ℝ) ≤ K (k₀ + j) * A.m ^ (k₀ + j) + 1 := by
    intro j
    unfold explorationSize
    exact (Nat.ceil_lt_add_one (mul_nonneg (hK0 _) (hp0 j).le)).le

  have hμ0 : explorationThreshold A K k₀ 0 / A.m ^ (k₀ + 0) = 1 := by
    simp only [explorationThreshold, add_zero]
    exact div_self (pow_ne_zero _ hm0.ne')
  have hstep : ∀ j, explorationThreshold A K k₀ (j + 1) / A.m ^ (k₀ + (j + 1)) =
      (1 - explorationEta A j) * (explorationThreshold A K k₀ j / A.m ^ (k₀ + j) -
        (explorationSize A K k₀ j : ℝ) / A.m ^ (k₀ + j)) := by
    intro j
    have h1 := (hp0 j).ne'
    have h2 := hm0.ne'
    simp only [explorationThreshold]
    rw [← add_assoc, pow_succ]
    field_simp
  have hinv : ∀ j, explorationThreshold A K k₀ j / A.m ^ (k₀ + j) ≤ 1 ∧
      1 - ∑ i ∈ range j, (explorationEta A i + (explorationSize A K k₀ i : ℝ) / A.m ^ (k₀ + i)) ≤
        explorationThreshold A K k₀ j / A.m ^ (k₀ + j) :=
    threshold_invariant_aux (fun j => explorationEta_nonneg A hm j)
      (fun j => explorationEta_le_one A hm j)
      (a := fun j => (explorationSize A K k₀ j : ℝ) / A.m ^ (k₀ + j))
      (μ := fun j => explorationThreshold A K k₀ j / A.m ^ (k₀ + j))
      (fun j => div_nonneg (Nat.cast_nonneg _) (hp0 j).le) hμ0 hstep

  have hpinv : ∀ i, (A.m ^ (k₀ + i))⁻¹ = (A.m ^ k₀)⁻¹ * A.m⁻¹ ^ i := by
    intro i
    rw [pow_add, mul_inv, inv_pow]
  have hterm : ∀ i, (explorationSize A K k₀ i : ℝ) / A.m ^ (k₀ + i) ≤
      K (k₀ + i) + (A.m ^ k₀)⁻¹ * A.m⁻¹ ^ i := by
    intro i
    rw [← hpinv, div_le_iff₀ (hp0 i), add_mul, inv_mul_cancel₀ (hp0 i).ne']
    exact hceil i
  have hsize_sum : ∀ j,
      ∑ i ∈ range j, (explorationSize A K k₀ i : ℝ) / A.m ^ (k₀ + i) ≤ 3 / 8 := by
    intro j
    have hKpart : ∑ i ∈ range j, K (k₀ + i) ≤ 1 / 4 := by
      have h := Finset.sum_range_add K k₀ j
      have h0 : 0 ≤ ∑ i ∈ range k₀, K i := Finset.sum_nonneg fun i _ => hK0 i
      have h3 : ∑ i ∈ range (k₀ + j), K i ≤ ∑' n, K n := hKs.sum_le_tsum _ fun i _ => hK0 i
      linarith
    have hgeom : (A.m ^ k₀)⁻¹ * ∑ i ∈ range j, A.m⁻¹ ^ i ≤ 1 / 8 := by
      have hgs := geomPartialSum_mul_le (inv_nonneg.mpr hm0.le) j
      have hgs0 : 0 ≤ ∑ i ∈ range j, A.m⁻¹ ^ i :=
        Finset.sum_nonneg fun i _ => pow_nonneg (inv_nonneg.mpr hm0.le) i
      rw [inv_mul_le_iff₀ (pow_pos hm0 k₀)]
      nlinarith [mul_le_mul_of_nonneg_right hk8 hgs0,
        mul_le_mul_of_nonneg_left hgs (pow_pos hm0 k₀).le]
    calc ∑ i ∈ range j, (explorationSize A K k₀ i : ℝ) / A.m ^ (k₀ + i)
        ≤ ∑ i ∈ range j, (K (k₀ + i) + (A.m ^ k₀)⁻¹ * A.m⁻¹ ^ i) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = ∑ i ∈ range j, K (k₀ + i) + (A.m ^ k₀)⁻¹ * ∑ i ∈ range j, A.m⁻¹ ^ i := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 3 / 8 := by linarith

  have hmain : ∀ j, (explorationSize A K k₀ j : ℝ) + A.m ^ (k₀ + j) / 16 ≤
      explorationThreshold A K k₀ j := by
    intro j
    have hμ : 3 / 8 ≤ explorationThreshold A K k₀ j / A.m ^ (k₀ + j) := by
      have h := (hinv j).2
      have h1 := sum_explorationEta_le A hm j
      have h2 := hsize_sum j
      rw [Finset.sum_add_distrib] at h
      linarith
    rw [le_div_iff₀ (hp0 j)] at hμ
    have hpj : 16 ≤ A.m ^ (k₀ + j) :=
      hk16.trans (pow_le_pow_right₀ hm.le (Nat.le_add_right k₀ j))
    have hc := hceil j
    have hK := mul_le_mul_of_nonneg_right (hKle (k₀ + j)) (hp0 j).le
    linarith

  have hfail : ∀ j, explorationFailure A K k₀ j ≤
      Real.exp (-(γ * A.m ^ k₀)) * Real.exp (-(γ * A.m ^ k₀) * (Real.sqrt A.m - 1)) ^ j := by
    intro j
    have hdiff : A.m ^ (k₀ + j) / 16 ≤
        explorationThreshold A K k₀ j - explorationSize A K k₀ j := by
      linarith [hmain j]
    have hbern : 1 + (j : ℝ) * (Real.sqrt A.m - 1) ≤ Real.sqrt A.m ^ j := by
      simpa using one_add_mul_le_pow (show (-2 : ℝ) ≤ Real.sqrt A.m - 1 by linarith) j
    have hηsq := explorationEta_sq_mul_pow A hm k₀ j
    have harg : γ * A.m ^ k₀ * (1 + j * (Real.sqrt A.m - 1)) ≤
        2 * explorationEta A j ^ 2 * A.m ^ 2 *
          (explorationThreshold A K k₀ j - explorationSize A K k₀ j) /
            ((A.M : ℝ) * A.N) ^ 2 := by
      rw [le_div_iff₀ (pow_pos hMN 2)]
      have hA : 0 ≤ 2 * explorationEta A j ^ 2 * A.m ^ 2 := by positivity
      have hMN2 : ((A.M : ℝ) * A.N) ^ 2 ≠ 0 := (pow_pos hMN 2).ne'
      have hM0' : (A.M : ℝ) ≠ 0 := by exact_mod_cast A.hM_pos.ne'
      have hN0' : (A.N : ℝ) ≠ 0 := by exact_mod_cast A.hN_pos.ne'
      have hs0 : Real.sqrt (Real.sqrt A.m) ≠ 0 := (inv_pos.mp ht0).ne'
      calc γ * A.m ^ k₀ * (1 + j * (Real.sqrt A.m - 1)) * ((A.M : ℝ) * A.N) ^ 2
          ≤ γ * A.m ^ k₀ * Real.sqrt A.m ^ j * ((A.M : ℝ) * A.N) ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (pow_pos hMN 2).le
            exact mul_le_mul_of_nonneg_left hbern (mul_pos hγ0 (pow_pos hm0 k₀)).le
        _ = 2 * (explorationEta A j ^ 2 * A.m ^ (k₀ + j)) * A.m ^ 2 / 16 := by
            rw [hηsq, hγ]
            field_simp
            ring
        _ = 2 * explorationEta A j ^ 2 * A.m ^ 2 * (A.m ^ (k₀ + j) / 16) := by ring
        _ ≤ 2 * explorationEta A j ^ 2 * A.m ^ 2 *
              (explorationThreshold A K k₀ j - explorationSize A K k₀ j) :=
            mul_le_mul_of_nonneg_left hdiff hA
    calc explorationFailure A K k₀ j
        = Real.exp (-(2 * explorationEta A j ^ 2 * A.m ^ 2 *
            (explorationThreshold A K k₀ j - explorationSize A K k₀ j) /
              ((A.M : ℝ) * A.N) ^ 2)) := rfl
      _ ≤ Real.exp (-(γ * A.m ^ k₀ * (1 + j * (Real.sqrt A.m - 1)))) :=
          Real.exp_le_exp.mpr (neg_le_neg harg)
      _ = Real.exp (-(γ * A.m ^ k₀)) *
            Real.exp (-(γ * A.m ^ k₀) * (Real.sqrt A.m - 1)) ^ j := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          congr 1
          ring
  have hq0 : 0 ≤ Real.exp (-(γ * A.m ^ k₀) * (Real.sqrt A.m - 1)) := (Real.exp_pos _).le
  have hq : Real.exp (-(γ * A.m ^ k₀) * (Real.sqrt A.m - 1)) ≤ 1 / 2 := by
    rw [neg_mul]
    refine (exp_neg_le_one_div_add_one (by linarith)).trans ?_
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hexp : Real.exp (-(γ * A.m ^ k₀)) ≤ 1 / 4 := by
    refine (exp_neg_le_one_div_add_one (by linarith)).trans ?_
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  refine ⟨fun j => ⟨explorationEta_nonneg A hm j, explorationEta_le_one A hm j⟩,
    fun j => by linarith [hmain j, hp0 j], fun J => ?_⟩
  have hS := geomPartialSum_mul_le hq0 J
  have hS0 : 0 ≤ ∑ j ∈ range J, Real.exp (-(γ * A.m ^ k₀) * (Real.sqrt A.m - 1)) ^ j :=
    Finset.sum_nonneg fun j _ => pow_nonneg hq0 j
  have hS2 : ∑ j ∈ range J, Real.exp (-(γ * A.m ^ k₀) * (Real.sqrt A.m - 1)) ^ j ≤ 2 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 / 2 - Real.exp (-(γ * A.m ^ k₀) *
      (Real.sqrt A.m - 1)) by linarith) hS0]
  calc ∑ j ∈ range J, explorationFailure A K k₀ j
      ≤ ∑ j ∈ range J, Real.exp (-(γ * A.m ^ k₀)) *
          Real.exp (-(γ * A.m ^ k₀) * (Real.sqrt A.m - 1)) ^ j :=
        Finset.sum_le_sum fun j _ => hfail j
    _ = Real.exp (-(γ * A.m ^ k₀)) *
          ∑ j ∈ range J, Real.exp (-(γ * A.m ^ k₀) * (Real.sqrt A.m - 1)) ^ j := by
        rw [Finset.mul_sum]
    _ ≤ 1 / 4 * 2 := mul_le_mul hexp hS2 hS0 (by norm_num)
    _ = 1 / 2 := by norm_num

end FractalGeometry.Probability.GridPercolation
