import Mathlib
import FractalGeometry.Entropy.Lq.Basic
import FractalGeometry.Entropy.Lq.Prop413
import FractalGeometry.Entropy.Lq.Prop68
import FractalGeometry.Entropy.Lq.Section4
import FractalGeometry.Entropy.Lq.Statements

open MeasureTheory Filter Topology Set

namespace FractalGeometry

namespace Lq

theorem ite_eq_of_pos {α : Sort*} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

theorem ite_eq_of_neg {α : Sort*} {c : Prop} [Decidable c] (h : ¬ c) {a b : α} :
    (if c then a else b) = b := by simp [h]

theorem measureReal_dyadicIco_eq_zero_of_Ico {μ : Measure ℝ} (hμ : μ (Set.Ico 0 1)ᶜ = 0)
    {m : ℕ} {k : ℤ} (hk : ¬ (0 ≤ k ∧ k < 2 ^ m)) : μ.real (dyadicIco m k) = 0 := by
  rw [measureReal_def, ENNReal.toReal_eq_zero_iff]
  left
  refine measure_mono_null (show dyadicIco m k ⊆ (Set.Ico 0 1)ᶜ from fun x hx hx' => hk ?_) hμ
  rw [mem_dyadicIco_iff] at hx
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have h1 := Int.floor_le (x * 2 ^ m)
  have h2 := Int.lt_floor_add_one (x * 2 ^ m)
  rw [hx] at h1 h2
  obtain ⟨hx1, hx2⟩ := hx'
  constructor
  · have : (-1 : ℝ) < k := by nlinarith
    have : (-1 : ℤ) < k := by exact_mod_cast this
    omega
  · have : (k : ℝ) < 2 ^ m := by nlinarith
    exact_mod_cast this

theorem isDyadicMeasure_discretize {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ (Set.Ico 0 1)ᶜ = 0) (m : ℕ) : IsDyadicMeasure m (discretize μ m) := by
  refine ⟨fun k => by unfold discretize; split_ifs <;> simp [measureReal_nonneg], ?_, ?_⟩
  · intro k hk
    by_contra h
    exact hk (by unfold discretize; rw [ite_eq_of_neg h])
  · have h := tsum_measureReal_dyadicIco μ m
    rw [tsum_eq_sum (s := Finset.Ico (0 : ℤ) (2 ^ m)) fun k hk =>
      measureReal_dyadicIco_eq_zero_of_Ico hμ (by simpa [Finset.mem_Ico] using hk)] at h
    rw [probReal_univ] at h
    rw [← h]
    refine Finset.sum_congr rfl fun k hk => ?_
    unfold discretize
    rw [ite_eq_of_pos (Finset.mem_Ico.mp hk)]

theorem discLq_discretize {μ : Measure ℝ} (hμ : μ (Set.Ico 0 1)ᶜ = 0) {q : ℝ} (hq : 0 < q)
    (m : ℕ) : discLq m q (discretize μ m) = lqSum μ q m := by
  unfold lqSum discLq
  rw [tsum_eq_sum (s := Finset.Ico (0 : ℤ) (2 ^ m)) fun k hk => by
    rw [measureReal_dyadicIco_eq_zero_of_Ico hμ (by simpa [Finset.mem_Ico] using hk),
      Real.zero_rpow hq.ne']]
  refine Finset.sum_congr rfl fun k hk => ?_
  unfold discretize
  rw [ite_eq_of_pos (Finset.mem_Ico.mp hk)]

theorem sub_emod_mem_Ico (m : ℕ) (k i : ℤ) : (k - i) % 2 ^ m ∈ Finset.Ico (0 : ℤ) (2 ^ m) := by
  rw [Finset.mem_Ico]
  exact ⟨Int.emod_nonneg _ (by positivity), Int.emod_lt_of_pos _ (by positivity)⟩

theorem sub_sub_emod_emod {m : ℕ} {k i : ℤ} (hi : i ∈ Finset.Ico (0 : ℤ) (2 ^ m)) :
    (k - (k - i) % 2 ^ m) % 2 ^ m = i := by
  rw [Finset.mem_Ico] at hi
  rw [Int.sub_emod, Int.emod_emod_of_dvd _ (dvd_refl _), ← Int.sub_emod, sub_sub_cancel]
  exact Int.emod_eq_of_lt hi.1 hi.2

theorem circConv_comm (m : ℕ) (μ ν : ℤ → ℝ) : circConv m μ ν = circConv m ν μ := by
  funext k
  unfold circConv
  split_ifs with hk
  · refine Finset.sum_nbij' (fun i => (k - i) % 2 ^ m) (fun i => (k - i) % 2 ^ m)
      (fun i _ => sub_emod_mem_Ico m k i) (fun i _ => sub_emod_mem_Ico m k i)
      (fun i hi => sub_sub_emod_emod hi) (fun i hi => sub_sub_emod_emod hi) fun i hi => ?_
    rw [sub_sub_emod_emod hi, mul_comm]
  · rfl

theorem discLq_circTranslate (m : ℕ) (q : ℝ) (a : ℤ) (μ : ℤ → ℝ) :
    discLq m q (circTranslate m a μ) = discLq m q μ := by
  unfold discLq circTranslate
  refine Finset.sum_nbij' (fun k => (k - a) % 2 ^ m) (fun k => (k + a) % 2 ^ m)
    (fun k _ => sub_emod_mem_Ico m k a) (fun k _ => by
      rw [Finset.mem_Ico]
      exact ⟨Int.emod_nonneg _ (by positivity), Int.emod_lt_of_pos _ (by positivity)⟩)
    (fun k hk => ?_) (fun k hk => ?_) fun k hk => ?_
  · rw [Finset.mem_Ico] at hk
    rw [Int.add_emod, Int.emod_emod_of_dvd _ (dvd_refl _), ← Int.add_emod, sub_add_cancel]
    exact Int.emod_eq_of_lt hk.1 hk.2
  · rw [Finset.mem_Ico] at hk
    rw [Int.sub_emod, Int.emod_emod_of_dvd _ (dvd_refl _), ← Int.sub_emod, add_sub_cancel_right]
    exact Int.emod_eq_of_lt hk.1 hk.2
  · rw [ite_eq_of_pos (Finset.mem_Ico.mp hk)]

theorem discLq_circConv_le {m : ℕ} {ν : ℤ → ℝ} (hν : IsDyadicMeasure m ν) {μ : ℤ → ℝ}
    (hμ : ∀ k, 0 ≤ μ k) {q : ℝ} (hq : 1 ≤ q) : discLq m q (circConv m ν μ) ≤ discLq m q μ := by
  unfold discLq
  have hJ : ∀ k ∈ Finset.Ico (0 : ℤ) (2 ^ m), circConv m ν μ k ^ q ≤
      ∑ i ∈ Finset.Ico (0 : ℤ) (2 ^ m), ν i * μ ((k - i) % 2 ^ m) ^ q := by
    intro k hk
    unfold circConv
    rw [ite_eq_of_pos (Finset.mem_Ico.mp hk)]
    exact Real.rpow_arith_mean_le_arith_mean_rpow _ ν _ (fun i _ => hν.nonneg i)
      hν.sum_eq_one (fun i _ => hμ _) hq
  calc ∑ k ∈ Finset.Ico (0 : ℤ) (2 ^ m), circConv m ν μ k ^ q
      ≤ ∑ k ∈ Finset.Ico (0 : ℤ) (2 ^ m), ∑ i ∈ Finset.Ico (0 : ℤ) (2 ^ m),
          ν i * μ ((k - i) % 2 ^ m) ^ q := Finset.sum_le_sum hJ
    _ = ∑ i ∈ Finset.Ico (0 : ℤ) (2 ^ m), ν i *
          ∑ k ∈ Finset.Ico (0 : ℤ) (2 ^ m), μ ((k - i) % 2 ^ m) ^ q := by
        rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.Ico (0 : ℤ) (2 ^ m), ν i * ∑ k ∈ Finset.Ico (0 : ℤ) (2 ^ m), μ k ^ q := by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        exact Finset.sum_nbij' (fun k => (k - i) % 2 ^ m) (fun k => (k + i) % 2 ^ m)
          (fun k _ => sub_emod_mem_Ico m k i) (fun k _ => by
            rw [Finset.mem_Ico]
            exact ⟨Int.emod_nonneg _ (by positivity), Int.emod_lt_of_pos _ (by positivity)⟩)
          (fun k hk => by
            rw [Finset.mem_Ico] at hk
            rw [Int.add_emod, Int.emod_emod_of_dvd _ (dvd_refl _), ← Int.add_emod,
              sub_add_cancel]
            exact Int.emod_eq_of_lt hk.1 hk.2)
          (fun k hk => by
            rw [Finset.mem_Ico] at hk
            rw [Int.sub_emod, Int.emod_emod_of_dvd _ (dvd_refl _), ← Int.sub_emod,
              add_sub_cancel_right]
            exact Int.emod_eq_of_lt hk.1 hk.2)
          fun k _ => rfl
    _ = ∑ k ∈ Finset.Ico (0 : ℤ) (2 ^ m), μ k ^ q := by
        rw [← Finset.sum_mul, hν.sum_eq_one, one_mul]

def cellsAt (m n : ℕ) (A : Finset ℤ) : Finset ℤ := A.image fun x => x / 2 ^ (m - n)

theorem ediv_two_pow_ediv {m n n' : ℕ} (hn : n ≤ n') (hn' : n' ≤ m) (x : ℤ) :
    x / 2 ^ (m - n') / 2 ^ (n' - n) = x / 2 ^ (m - n) := by
  rw [Int.ediv_ediv_of_nonneg (by positivity), ← pow_add]
  congr 2
  omega

theorem card_cellsAt_eq_prod {A : Finset ℤ} {m D ℓ : ℕ} (hm : m = ℓ * D) (hA : A.Nonempty)
    (hA0 : ∀ x ∈ A, 0 ≤ x ∧ x < 2 ^ m) {R : ℕ → ℕ}
    (hR : ∀ s < ℓ, ∀ x ∈ A, branching m (s * D) ((s + 1) * D) A x = R s) :
    ∀ s ≤ ℓ, (cellsAt m (s * D) A).card = ∏ t ∈ Finset.range s, R t := by
  classical
  intro s
  induction s with
  | zero =>
    intro _
    simp only [zero_mul, Finset.range_zero, Finset.prod_empty]
    rw [Finset.card_eq_one]
    refine ⟨0, ?_⟩
    ext c
    simp only [cellsAt, Finset.mem_image, Finset.mem_singleton, Nat.sub_zero]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Int.ediv_eq_zero_of_lt (hA0 x hx).1 (hA0 x hx).2
    · rintro rfl
      obtain ⟨x, hx⟩ := hA
      exact ⟨x, hx, Int.ediv_eq_zero_of_lt (hA0 x hx).1 (hA0 x hx).2⟩
  | succ s ih =>
    intro hs
    have hsl : s < ℓ := by omega
    have hsD : (s + 1) * D ≤ m := by rw [hm]; exact Nat.mul_le_mul_right D hs
    rw [Finset.prod_range_succ, ← ih hsl.le]

    set g : ℤ → ℤ := fun c => c / 2 ^ ((s + 1) * D - s * D)
    have hg : ∀ x : ℤ, g (x / 2 ^ (m - (s + 1) * D)) = x / 2 ^ (m - s * D) := fun x =>
      ediv_two_pow_ediv (by nlinarith) hsD x
    have hmaps : ∀ c ∈ cellsAt m ((s + 1) * D) A, g c ∈ cellsAt m (s * D) A := by
      intro c hc
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
      rw [hg]
      exact Finset.mem_image_of_mem _ hx
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_const_nat fun c hc => ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
    rw [← hR s hsl x hx]
    unfold branching
    congr 1
    ext c'
    simp only [cellsAt, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hyc⟩
      rw [hg] at hyc
      exact ⟨y, ⟨hy, hyc⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hyc⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, by rw [hg]; exact hyc⟩

theorem card_eq_prod_branching {A : Finset ℤ} {m D ℓ : ℕ} (hm : m = ℓ * D) (hA : A.Nonempty)
    (hA0 : ∀ x ∈ A, 0 ≤ x ∧ x < 2 ^ m) {R : ℕ → ℕ}
    (hR : ∀ s < ℓ, ∀ x ∈ A, branching m (s * D) ((s + 1) * D) A x = R s) :
    A.card = ∏ t ∈ Finset.range ℓ, R t := by
  rw [← card_cellsAt_eq_prod hm hA hA0 hR ℓ le_rfl]
  unfold cellsAt
  rw [← hm, Nat.sub_self, pow_zero]
  simp

theorem mem_of_measureReal_dyadicIco_pos {μ : Measure ℝ} (hμ : μ (Set.Icc (3 / 8) (5 / 8))ᶜ = 0)
    {m : ℕ} (hm : 3 ≤ m) {k : ℤ} (hk : 0 < μ.real (dyadicIco m k)) :
    2 ^ (m - 2) < k ∧ k < 3 * 2 ^ (m - 2) := by
  by_contra hno
  apply hk.ne'
  rw [measureReal_def, ENNReal.toReal_eq_zero_iff]
  left
  refine measure_mono_null (show dyadicIco m k ⊆ (Set.Icc (3 / 8) (5 / 8))ᶜ from
    fun x hx hx' => hno ?_) hμ
  rw [mem_dyadicIco_iff] at hx
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hpow : (2 : ℝ) ^ m = 8 * 2 ^ (m - 3) := by
    rw [show m = (m - 3) + 3 by omega, pow_add]; norm_num; ring
  have hpow2 : (2 : ℤ) ^ (m - 2) = 2 * 2 ^ (m - 3) := by
    rw [show m - 2 = (m - 3) + 1 by omega, pow_succ]; ring
  have h1 := Int.floor_le (x * 2 ^ m)
  have h2 := Int.lt_floor_add_one (x * 2 ^ m)
  rw [hx] at h1 h2
  obtain ⟨hx1, hx2⟩ := hx'
  have h3 : (1 : ℝ) ≤ 2 ^ (m - 3) := one_le_pow₀ (by norm_num)
  have hlo : (2 : ℝ) * 2 ^ (m - 3) < k := by nlinarith
  have hhi : (k : ℝ) < 6 * 2 ^ (m - 3) := by nlinarith
  rw [hpow2]
  constructor
  · exact_mod_cast hlo
  · have : (k : ℝ) < 3 * (2 * 2 ^ (m - 3)) := by linarith
    exact_mod_cast this

theorem exists_offset {μ : Measure ℝ} (hμ : μ (Set.Icc (3 / 8) (5 / 8))ᶜ = 0) {m : ℕ}
    (hm : 3 ≤ m) {a : ℤ} {A : Finset ℤ}
    (hpos : ∀ x ∈ A, 0 < circTranslate m a (discretize μ m) x)
    (hmid : ∀ x ∈ A, InMiddleHalf m x) :
    ∃ e : ℤ, ∀ x ∈ A, circTranslate m a (discretize μ m) x = μ.real (dyadicIco m (x + e)) ∧
      2 ^ (m - 2) < x + e ∧ x + e < 3 * 2 ^ (m - 2) := by
  classical
  have key : ∀ x ∈ A, 0 ≤ x ∧ x < 2 ^ m ∧
      circTranslate m a (discretize μ m) x = μ.real (dyadicIco m ((x - a) % 2 ^ m)) ∧
      2 ^ (m - 2) < (x - a) % 2 ^ m ∧ (x - a) % 2 ^ m < 3 * 2 ^ (m - 2) ∧
      2 ^ m ≤ 4 * x ∧ 4 * x ≤ 3 * 2 ^ m := by
    intro x hx
    have h := hpos x hx
    unfold circTranslate at h ⊢
    by_cases hx0 : 0 ≤ x ∧ x < 2 ^ m
    · rw [ite_eq_of_pos hx0] at h ⊢
      have hk0 : 0 ≤ (x - a) % 2 ^ m ∧ (x - a) % 2 ^ m < 2 ^ m :=
        ⟨Int.emod_nonneg _ (by positivity), Int.emod_lt_of_pos _ (by positivity)⟩
      unfold discretize at h ⊢
      rw [ite_eq_of_pos hk0] at h ⊢
      have hb := mem_of_measureReal_dyadicIco_pos hμ hm h
      have hmx := hmid x hx
      unfold InMiddleHalf at hmx
      rw [Int.emod_eq_of_lt hx0.1 hx0.2] at hmx
      exact ⟨hx0.1, hx0.2, rfl, hb.1, hb.2, hmx.1, hmx.2⟩
    · rw [ite_eq_of_neg hx0] at h
      exact absurd h (lt_irrefl 0)
  rcases A.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, fun x hx => absurd hx (Finset.notMem_empty x)⟩
  refine ⟨(x₀ - a) % 2 ^ m - x₀, fun x hx => ?_⟩
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := key x hx
  obtain ⟨h0', h1', h2', h3', h4', h5', h6'⟩ := key x₀ hx₀
  have hpow : (2 : ℤ) ^ m = 4 * 2 ^ (m - 2) := by
    rw [show m = (m - 2) + 2 by omega, pow_add]; norm_num; ring

  have hcong : ((x - a) % 2 ^ m - x) % 2 ^ m = ((x₀ - a) % 2 ^ m - x₀) % 2 ^ m := by
    rw [Int.sub_emod, Int.emod_emod_of_dvd _ (dvd_refl _), ← Int.sub_emod,
      Int.sub_emod ((x₀ - a) % 2 ^ m), Int.emod_emod_of_dvd _ (dvd_refl _), ← Int.sub_emod]
    congr 1; ring
  have heq : (x - a) % 2 ^ m - x = (x₀ - a) % 2 ^ m - x₀ := by
    have hd : (2 ^ m : ℤ) ∣ ((x - a) % 2 ^ m - x) - ((x₀ - a) % 2 ^ m - x₀) :=
      Int.ModEq.dvd hcong.symm
    obtain ⟨t, ht⟩ := hd
    have : t = 0 := by
      by_contra ht0
      rcases lt_or_gt_of_ne ht0 with htn | htp
      · have : (2 : ℤ) ^ m * t ≤ -2 ^ m := by nlinarith
        omega
      · have : (2 : ℤ) ^ m ≤ 2 ^ m * t := by nlinarith
        omega
    rw [this, mul_zero] at ht
    linarith
  have hxe : x + ((x₀ - a) % 2 ^ m - x₀) = (x - a) % 2 ^ m := by linarith
  rw [hxe]
  exact ⟨h2, h3, h4⟩

def gridIco (m n : ℕ) (e c : ℤ) : Set ℝ :=
  Set.Ico (((c * 2 ^ (m - n) + e : ℤ) : ℝ) / 2 ^ m) ((((c + 1) * 2 ^ (m - n) + e : ℤ) : ℝ) / 2 ^ m)

noncomputable def levelSum (μ : Measure ℝ) (q : ℝ) (m n : ℕ) (e : ℤ) (A : Finset ℤ) : ℝ :=
  ∑ c ∈ cellsAt m n A, μ.real (gridIco m n e c) ^ q

theorem gridIco_self (m : ℕ) (e c : ℤ) : gridIco m m e c = dyadicIco m (c + e) := by
  simp only [gridIco, dyadicIco, Nat.sub_self, pow_zero, mul_one]
  push_cast
  ring_nf

theorem gridIco_eq_subIco {m n D : ℕ} (hD : 3 ≤ D) (hnD : n + D ≤ m) (e c' : ℤ) (j : ℕ) :
    gridIco m (n + D) e (c' * 2 ^ (D - 3) + j) =
      subIco (((c' * 2 ^ (m - (n + 3)) + e : ℤ) : ℝ) / 2 ^ m) (n + 3 + (D - 3)) j := by
  have h1 : (2 : ℝ) ^ (m - (n + 3)) = 2 ^ (D - 3) * 2 ^ (m - (n + D)) := by
    rw [← pow_add]; congr 1; omega
  have h2 : (2 : ℝ) ^ m = 2 ^ (n + 3 + (D - 3)) * 2 ^ (m - (n + D)) := by
    rw [← pow_add]; congr 1; omega
  simp only [gridIco, subIco]
  push_cast
  rw [h1]
  congr 1
  · rw [h2]; field_simp; ring
  · rw [h2]; field_simp; ring

theorem emod_eight_of_inMiddleHalf {m n : ℕ} (hn : n + 3 ≤ m) {x : ℤ}
    (hx : InMiddleHalf (m - n) x) :
    2 ≤ (x / 2 ^ (m - (n + 3))) % 8 ∧ (x / 2 ^ (m - (n + 3))) % 8 ≤ 6 := by
  unfold InMiddleHalf at hx
  set b : ℤ := 2 ^ (m - (n + 3))
  have hb : 0 < b := by positivity
  have hpow : (2 : ℤ) ^ (m - n) = b * 8 := by
    simp only [b]; rw [show m - n = (m - (n + 3)) + 3 by omega, pow_add]; norm_num
  rw [hpow] at hx
  set y := x % (b * 8)
  have hy0 : 0 ≤ y := Int.emod_nonneg _ (by positivity)
  have hyl : y < b * 8 := Int.emod_lt_of_pos _ (by positivity)
  have hxy : x / b % 8 = y / b := by
    have hx' : x = b * 8 * (x / (b * 8)) + y := (Int.mul_ediv_add_emod x (b * 8)).symm
    have : x / b = 8 * (x / (b * 8)) + y / b := by
      conv_lhs => rw [hx']
      rw [show b * 8 * (x / (b * 8)) + y = y + b * (8 * (x / (b * 8))) by ring,
        Int.add_mul_ediv_left _ _ hb.ne']
      ring
    rw [this, Int.add_emod, Int.mul_emod_right, zero_add]
    have hlt : y / b < 8 := by rw [Int.ediv_lt_iff_lt_mul hb]; linarith
    rw [Int.emod_emod_of_dvd _ (dvd_refl 8)]
    exact Int.emod_eq_of_lt (Int.ediv_nonneg hy0 hb.le) hlt
  rw [hxy]
  constructor
  · rw [Int.le_ediv_iff_mul_le hb]; linarith
  · have : y / b < 7 := by rw [Int.ediv_lt_iff_lt_mul hb]; nlinarith
    omega

theorem doubleIco_subset_gridIco {m n : ℕ} (hn : n + 3 ≤ m) (e c' : ℤ) (h2 : 2 ≤ c' % 8)
    (h6 : c' % 8 ≤ 6) :
    doubleIco (((c' * 2 ^ (m - (n + 3)) + e : ℤ) : ℝ) / 2 ^ m) (n + 3) ⊆
      gridIco m n e (c' / 8) := by
  intro x hx
  simp only [doubleIco, Set.mem_Ico] at hx
  simp only [gridIco, Set.mem_Ico]
  have hc : c' = 8 * (c' / 8) + c' % 8 := (Int.mul_ediv_add_emod c' 8).symm
  set r := c' % 8
  set c := c' / 8
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast h2
  have hr6 : (r : ℝ) ≤ 6 := by exact_mod_cast h6
  set Q : ℝ := 2 ^ (m - (n + 3))
  have hQ : 0 < Q := by positivity
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hpow1 : (2 : ℝ) ^ (m - n) = 8 * Q := by
    simp only [Q]; rw [show m - n = (m - (n + 3)) + 3 by omega, pow_add]; norm_num; ring
  have hpowm : (2 : ℝ) ^ m = 2 ^ (n + 3 + 1) * Q / 2 := by
    simp only [Q]
    rw [← pow_add, show n + 3 + 1 + (m - (n + 3)) = m + 1 by omega, pow_succ]; ring
  have hcR : (c' : ℝ) = 8 * c + r := by exact_mod_cast hc
  push_cast at hx ⊢
  rw [hcR] at hx
  rw [hpow1]
  set u : ℝ := (8 * c + r) * Q + e
  have e1 : u / 2 ^ m - 1 / 2 ^ (n + 3 + 1) = (u - Q / 2) / 2 ^ m := by
    rw [hpowm]; field_simp
  have e3 : u / 2 ^ m + 3 / 2 ^ (n + 3 + 1) = (u + 3 * Q / 2) / 2 ^ m := by
    rw [hpowm]; field_simp
  obtain ⟨hx1, hx2⟩ := hx
  rw [e1, div_le_iff₀ h2m] at hx1
  rw [e3, lt_div_iff₀ h2m] at hx2
  have hrQ : 2 * Q ≤ r * Q := mul_le_mul_of_nonneg_right hr2 hQ.le
  have hrQ6 : r * Q ≤ 6 * Q := mul_le_mul_of_nonneg_right hr6 hQ.le
  simp only [u] at hx1 hx2
  constructor
  · rw [div_le_iff₀ h2m]; nlinarith
  · rw [lt_div_iff₀ h2m]; nlinarith

theorem levelSum_add_le (μ : Measure ℝ) [IsFiniteMeasure μ] {q : ℝ} (hq : 1 ≤ q) {m n D : ℕ}
    (hD : 3 ≤ D) (hnD : n + D ≤ m) (e : ℤ) {A : Finset ℤ}
    (hmid : ∀ x ∈ A, InMiddleHalf (m - n) x) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (H : ∀ c' ∈ cellsAt m (n + 3) A,
      ∑ c'' ∈ (cellsAt m (n + D) A).filter (fun c'' => c'' / 2 ^ (D - 3) = c'),
        μ.real (gridIco m (n + D) e c'') ^ q ≤
        Λ * μ.real (doubleIco (((c' * 2 ^ (m - (n + 3)) + e : ℤ) : ℝ) / 2 ^ m) (n + 3)) ^ q) :
    levelSum μ q m (n + D) e A ≤ 5 * Λ * levelSum μ q m n e A := by
  classical
  have hn3 : n + 3 ≤ m := by omega
  unfold levelSum
  have hdiv1 : ∀ x : ℤ, x / 2 ^ (m - (n + D)) / 2 ^ (D - 3) = x / 2 ^ (m - (n + 3)) := by
    intro x
    have := ediv_two_pow_ediv (m := m) (n := n + 3) (n' := n + D) (by omega) hnD x
    rwa [show n + D - (n + 3) = D - 3 by omega] at this
  have hdiv2 : ∀ x : ℤ, x / 2 ^ (m - (n + 3)) / 8 = x / 2 ^ (m - n) := by
    intro x
    have := ediv_two_pow_ediv (m := m) (n := n) (n' := n + 3) (by omega) hn3 x
    rwa [show n + 3 - n = 3 by omega] at this
  have hmaps1 : ∀ c'' ∈ cellsAt m (n + D) A, c'' / 2 ^ (D - 3) ∈ cellsAt m (n + 3) A := by
    intro c'' hc''
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc''
    rw [hdiv1]
    exact Finset.mem_image_of_mem _ hx
  have hmaps2 : ∀ c' ∈ cellsAt m (n + 3) A, c' / 8 ∈ cellsAt m n A := by
    intro c' hc'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc'
    rw [hdiv2]
    exact Finset.mem_image_of_mem _ hx
  have hr : ∀ c' ∈ cellsAt m (n + 3) A, 2 ≤ c' % 8 ∧ c' % 8 ≤ 6 := by
    intro c' hc'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc'
    exact emod_eight_of_inMiddleHalf hn3 (hmid x hx)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps1]
  calc ∑ c' ∈ cellsAt m (n + 3) A, ∑ c'' ∈ (cellsAt m (n + D) A).filter
        (fun c'' => c'' / 2 ^ (D - 3) = c'), μ.real (gridIco m (n + D) e c'') ^ q
      ≤ ∑ c' ∈ cellsAt m (n + 3) A, Λ *
          μ.real (doubleIco (((c' * 2 ^ (m - (n + 3)) + e : ℤ) : ℝ) / 2 ^ m) (n + 3)) ^ q :=
        Finset.sum_le_sum H
    _ ≤ ∑ c' ∈ cellsAt m (n + 3) A, Λ * μ.real (gridIco m n e (c' / 8)) ^ q := by
        refine Finset.sum_le_sum fun c' hc' => mul_le_mul_of_nonneg_left ?_ hΛ
        exact Real.rpow_le_rpow measureReal_nonneg (measureReal_mono
          (doubleIco_subset_gridIco hn3 e c' (hr c' hc').1 (hr c' hc').2) (measure_ne_top _ _))
          (by linarith)
    _ = ∑ c ∈ cellsAt m n A, ∑ c' ∈ (cellsAt m (n + 3) A).filter (fun c' => c' / 8 = c),
          Λ * μ.real (gridIco m n e c) ^ q := by
        rw [← Finset.sum_fiberwise_of_maps_to hmaps2]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' hc' => ?_
        rw [(Finset.mem_filter.mp hc').2]
    _ ≤ ∑ c ∈ cellsAt m n A, 5 * (Λ * μ.real (gridIco m n e c) ^ q) := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hΛ (Real.rpow_nonneg measureReal_nonneg _))
        have hsub : (cellsAt m (n + 3) A).filter (fun c' => c' / 8 = c) ⊆
            (Finset.Icc (2 : ℤ) 6).image fun r => 8 * c + r := by
          intro c' hc'
          obtain ⟨hc'1, hc'2⟩ := Finset.mem_filter.mp hc'
          rw [Finset.mem_image]
          refine ⟨c' % 8, Finset.mem_Icc.mpr (hr c' hc'1), ?_⟩
          rw [← hc'2]
          exact Int.mul_ediv_add_emod c' 8
        have := (Finset.card_le_card hsub).trans Finset.card_image_le
        have h5 : (Finset.Icc (2 : ℤ) 6).card = 5 := by simp
        rw [h5] at this
        exact_mod_cast this
    _ = 5 * Λ * ∑ c ∈ cellsAt m n A, μ.real (gridIco m n e c) ^ q := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun c _ => by ring

theorem sum_children_eq (μ : Measure ℝ) (q : ℝ) {m n D : ℕ} (hD : 3 ≤ D) (hnD : n + D ≤ m)
    (e : ℤ) (A : Finset ℤ) (c' : ℤ) :
    ∃ Dj : Finset ℕ, (∀ j ∈ Dj, j < 2 ^ (D - 3)) ∧
      Dj.card = ((cellsAt m (n + D) A).filter (fun c'' => c'' / 2 ^ (D - 3) = c')).card ∧
      ∑ c'' ∈ (cellsAt m (n + D) A).filter (fun c'' => c'' / 2 ^ (D - 3) = c'),
        μ.real (gridIco m (n + D) e c'') ^ q =
      ∑ j ∈ Dj, μ.real (subIco (((c' * 2 ^ (m - (n + 3)) + e : ℤ) : ℝ) / 2 ^ m)
        (n + 3 + (D - 3)) j) ^ q := by
  classical
  set F := (cellsAt m (n + D) A).filter (fun c'' => c'' / 2 ^ (D - 3) = c')
  set j : ℤ → ℕ := fun c'' => (c'' % 2 ^ (D - 3)).toNat
  have hpos : (0 : ℤ) < 2 ^ (D - 3) := by positivity
  have hj : ∀ c'' ∈ F, c'' = c' * 2 ^ (D - 3) + (j c'' : ℤ) := by
    intro c'' hc''
    have h1 := (Finset.mem_filter.mp hc'').2
    have h2 := Int.mul_ediv_add_emod c'' (2 ^ (D - 3))
    simp only [j]
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hpos.ne'), ← h1]
    linarith
  have hinj : Set.InjOn j ↑F := by
    intro a ha b hb hab
    rw [hj a ha, hj b hb, hab]
  refine ⟨F.image j, fun i hi => ?_, Finset.card_image_of_injOn hinj, ?_⟩
  · obtain ⟨c'', _, rfl⟩ := Finset.mem_image.mp hi
    have := Int.emod_lt_of_pos c'' hpos
    have h0 := Int.emod_nonneg c'' hpos.ne'
    simp only [j]
    rw [Int.toNat_lt h0]
    exact_mod_cast this
  · rw [Finset.sum_image fun a ha b hb hab => hinj ha hb hab]
    refine Finset.sum_congr rfl fun c'' hc'' => ?_
    conv_lhs => rw [hj c'' hc'']
    rw [gridIco_eq_subIco hD hnD]

theorem card_children_le {m D s : ℕ} (hD : 3 ≤ D) (hsD : (s + 1) * D ≤ m) {A : Finset ℤ} {R : ℕ}
    (hR : ∀ x ∈ A, branching m (s * D) ((s + 1) * D) A x = R) {c' : ℤ}
    (hc' : c' ∈ cellsAt m (s * D + 3) A) :
    ((cellsAt m (s * D + D) A).filter (fun c'' => c'' / 2 ^ (D - 3) = c')).card ≤ R := by
  classical
  obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hc'
  rw [← hR x₀ hx₀]
  unfold branching
  refine Finset.card_le_card fun c'' hc'' => ?_
  obtain ⟨hc''1, hc''2⟩ := Finset.mem_filter.mp hc''
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hc''1
  have e1 : s * D + D = (s + 1) * D := by ring
  rw [Finset.mem_image]
  refine ⟨y, Finset.mem_filter.mpr ⟨hy, ?_⟩, by rw [e1]⟩
  have hdiv1 := ediv_two_pow_ediv (m := m) (n := s * D + 3) (n' := s * D + D) (by omega)
    (by rw [e1]; exact hsD) y
  rw [show s * D + D - (s * D + 3) = D - 3 by omega] at hdiv1
  rw [hdiv1] at hc''2
  have h2 := ediv_two_pow_ediv (m := m) (n := s * D) (n' := s * D + 3) (by omega) (by
    have : s * D + 3 ≤ s * D + D := by omega
    rw [e1] at this; omega) y
  have h3 := ediv_two_pow_ediv (m := m) (n := s * D) (n' := s * D + 3) (by omega) (by
    have : s * D + 3 ≤ s * D + D := by omega
    rw [e1] at this; omega) x₀
  rw [← h2, ← h3, hc''2]

theorem levelSum_le_prod (μ : Measure ℝ) [IsFiniteMeasure μ] {q : ℝ} (hq : 1 ≤ q)
    {m D ℓ : ℕ} (hm : m = ℓ * D) (hD : 3 ≤ D) (e : ℤ) {A : Finset ℤ}
    (hmid : ∀ x ∈ A, ∀ s < ℓ, InMiddleHalf (m - s * D) x) (Λ : ℕ → ℝ) (hΛ : ∀ s, 0 ≤ Λ s)
    (H : ∀ s < ℓ, ∀ c' ∈ cellsAt m (s * D + 3) A,
      ∑ c'' ∈ (cellsAt m (s * D + D) A).filter (fun c'' => c'' / 2 ^ (D - 3) = c'),
        μ.real (gridIco m (s * D + D) e c'') ^ q ≤
        Λ s * μ.real (doubleIco (((c' * 2 ^ (m - (s * D + 3)) + e : ℤ) : ℝ) / 2 ^ m)
          (s * D + 3)) ^ q) :
    ∀ s ≤ ℓ, levelSum μ q m (s * D) e A ≤
      (∏ t ∈ Finset.range s, (5 * Λ t)) * levelSum μ q m 0 e A := by
  intro s
  induction s with
  | zero => intro _; simp
  | succ s ih =>
    intro hs
    have hsl : s < ℓ := by omega
    have hsD : s * D + D ≤ m := by rw [hm]; nlinarith
    have h1 := levelSum_add_le μ hq hD hsD e (fun x hx => hmid x hx s hsl) (hΛ s) (H s hsl)
    rw [show (s + 1) * D = s * D + D by ring, Finset.prod_range_succ]
    calc levelSum μ q m (s * D + D) e A ≤ 5 * Λ s * levelSum μ q m (s * D) e A := h1
      _ ≤ 5 * Λ s * ((∏ t ∈ Finset.range s, (5 * Λ t)) * levelSum μ q m 0 e A) :=
          mul_le_mul_of_nonneg_left (ih hsl.le) (by linarith [hΛ s])
      _ = _ := by ring

theorem levelSum_zero_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] {q : ℝ} (hq : 0 < q)
    {m : ℕ} (e : ℤ) {A : Finset ℤ} (hA0 : ∀ x ∈ A, 0 ≤ x ∧ x < 2 ^ m) :
    levelSum μ q m 0 e A ≤ 1 := by
  classical
  unfold levelSum
  have hsub : cellsAt m 0 A ⊆ {0} := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
    rw [Finset.mem_singleton, Nat.sub_zero]
    exact Int.ediv_eq_zero_of_lt (hA0 x hx).1 (hA0 x hx).2
  calc ∑ c ∈ cellsAt m 0 A, μ.real (gridIco m 0 e c) ^ q
      ≤ ∑ c ∈ ({0} : Finset ℤ), μ.real (gridIco m 0 e c) ^ q :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun c _ _ =>
          Real.rpow_nonneg measureReal_nonneg _
    _ ≤ 1 := by
        rw [Finset.sum_singleton]
        exact Real.rpow_le_one measureReal_nonneg measureReal_le_one hq.le

theorem levelSum_self (μ : Measure ℝ) (q : ℝ) (m : ℕ) (e : ℤ) (A : Finset ℤ) :
    levelSum μ q m m e A = ∑ x ∈ A, μ.real (dyadicIco m (x + e)) ^ q := by
  unfold levelSum cellsAt
  rw [Nat.sub_self, pow_zero]
  simp only [Int.ediv_one, Finset.image_id']
  exact Finset.sum_congr rfl fun x _ => by rw [gridIco_self]

theorem card_small_scales_ge {ℓ D : ℕ} (hD : 1 ≤ D) {R : ℕ → ℕ} (hR : ∀ s < ℓ, 1 ≤ R s)
    {Ts σ δ δ' ξ τ q : ℝ} (hq : 1 < q) (hσ : 0 < σ) (hTs : Ts < 1) (hδδ' : δ ≤ δ')
    (hδ'σ : δ' ≤ σ) (hδ'Ts : 2 * δ' ≤ 1 - Ts)
    (hδ'3 : δ' * (2 - Ts + 2 * σ) ≤ (1 - Ts) * σ / 2)
    (hξ : ξ / (q - 1) + δ ≤ (1 - τ / (q - 1)) / 2)
    (hA : ((∏ s ∈ Finset.range ℓ, R s : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((ℓ * D : ℕ) * (Ts + δ')))
    (hS1 : σ * (ℓ * D : ℕ) - δ * (ℓ * D : ℕ) ≤ D * (fullScales δ ℓ D R).card)
    (hS2 : (D : ℝ) * (fullScales δ ℓ D R).card ≤
      (τ + ξ) / (q - 1) * (ℓ * D : ℕ) + δ * (ℓ * D : ℕ)) :
    (1 - Ts) * σ / 4 * (1 - τ / (q - 1)) / 2 * ℓ ≤
      (((Finset.range ℓ).filter fun s => s ∉ fullScales δ ℓ D R ∧
        (R s : ℝ) ≤ (2 : ℝ) ^ ((Ts - (1 - Ts) * σ / 4) * D)).card : ℝ) := by
  classical
  set κ := (1 - Ts) * σ / 4 with hκ
  set S := fullScales δ ℓ D R
  set S' := (Finset.range ℓ).filter fun s => s ∉ S
  set S₁ := (Finset.range ℓ).filter fun s => s ∉ S ∧ (R s : ℝ) ≤ (2 : ℝ) ^ ((Ts - κ) * D)
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hm : ((ℓ * D : ℕ) : ℝ) = ℓ * D := by push_cast; ring
  rw [hm] at hA hS1 hS2
  set lg : ℕ → ℝ := fun s => Real.logb 2 (R s)
  have hlg0 : ∀ s ∈ Finset.range ℓ, 0 ≤ lg s := fun s hs =>
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hR s (Finset.mem_range.mp hs))
  have hRpos : ∀ s ∈ Finset.range ℓ, (0 : ℝ) < R s := fun s hs => by
    have := hR s (Finset.mem_range.mp hs); positivity

  have hsum : ∑ s ∈ Finset.range ℓ, lg s ≤ ℓ * D * (Ts + δ') := by
    have hprod : (0 : ℝ) < ((∏ s ∈ Finset.range ℓ, R s : ℕ) : ℝ) := by
      push_cast; exact Finset.prod_pos fun s hs => hRpos s hs
    have := (Real.logb_le_iff_le_rpow (by norm_num) hprod).mpr hA
    push_cast at this
    rwa [Real.logb_prod _ _ fun s hs => (hRpos s hs).ne'] at this

  have hSsub : S ⊆ Finset.range ℓ := Finset.filter_subset _ _
  have hlgS : ∀ s ∈ S, (1 - δ) * D ≤ lg s := by
    intro s hs
    have := (Finset.mem_filter.mp hs).2
    exact (Real.le_logb_iff_rpow_le (by norm_num) (hRpos s (hSsub hs))).mpr this
  have hsplit : ∑ s ∈ Finset.range ℓ, lg s = ∑ s ∈ S, lg s + ∑ s ∈ S', lg s := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range ℓ) (fun s => s ∈ S)]
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext s; simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨Finset.mem_range.mp (hSsub h), h⟩
  have hcardS : (S.card : ℝ) + S'.card = ℓ := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.range ℓ) (fun s => s ∈ S)
    rw [Finset.card_range] at this
    have e : (Finset.range ℓ).filter (fun s => s ∈ S) = S := by
      ext s; simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨Finset.mem_range.mp (hSsub h), h⟩
    rw [e] at this
    exact_mod_cast this
  have hsumS : (1 - δ) * D * S.card ≤ ∑ s ∈ S, lg s := by
    have := Finset.card_nsmul_le_sum S lg ((1 - δ) * D) hlgS
    rw [nsmul_eq_mul] at this
    linarith

  set m₁ : ℝ := D * S.card
  set m₂ : ℝ := D * S'.card
  have hm12 : (ℓ : ℝ) * D = m₁ + m₂ := by
    simp only [m₁, m₂]; rw [← mul_add, hcardS]; ring
  have hm₂0 : 0 ≤ m₂ := by positivity
  have hS'sum : ∑ s ∈ S', lg s ≤ (Ts - 2 * κ) * m₂ := by
    have hm₁S : (1 - δ) * D * S.card = (1 - δ) * m₁ := by simp only [m₁]; ring
    have h1 : ∑ s ∈ S', lg s ≤ ℓ * D * (Ts + δ') - (1 - δ) * m₁ := by
      rw [hsplit] at hsum; linarith
    have hcoef : 0 ≤ 1 - δ - Ts - δ' := by linarith
    have h2 : (σ - δ) * (ℓ * D) ≤ m₁ := by
      have e : (σ - δ) * (ℓ * D) = σ * (ℓ * D) - δ * (ℓ * D) := by ring
      linarith
    have hσδ : 0 ≤ σ - δ := by linarith
    have hm₁0 : 0 ≤ m₁ := by positivity
    have hm₂ℓ : m₂ ≤ ℓ * D := by linarith
    have h3 : (1 - δ - Ts - δ') * ((σ - δ) * m₂) ≤ (1 - δ - Ts - δ') * m₁ :=
      mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hm₂ℓ hσδ).trans h2) hcoef
    have h4 : ∑ s ∈ S', lg s ≤ (Ts + δ') * m₂ - (1 - δ - Ts - δ') * m₁ := by
      rw [hm12] at h1
      have e : (m₁ + m₂) * (Ts + δ') - (1 - δ) * m₁ =
          (Ts + δ') * m₂ - (1 - δ - Ts - δ') * m₁ := by ring
      linarith
    have h5 : (Ts + δ') - (1 - δ - Ts - δ') * (σ - δ) ≤ Ts - 2 * κ := by
      have hA1 : (1 - Ts - 2 * δ') * (σ - δ') ≤ (1 - δ - Ts - δ') * (σ - δ) :=
        mul_le_mul (by linarith) (by linarith) (by linarith) hcoef
      have hA2 : (1 - Ts - 2 * δ') * (σ - δ') =
          (1 - Ts) * σ - δ' * (2 - Ts + 2 * σ) + δ' + 2 * δ' ^ 2 := by ring
      have hA3 : 0 ≤ 2 * δ' ^ 2 := by positivity
      rw [hκ]
      linarith
    have h6 := mul_le_mul_of_nonneg_right h5 hm₂0
    have e : ((Ts + δ') - (1 - δ - Ts - δ') * (σ - δ)) * m₂ =
        (Ts + δ') * m₂ - (1 - δ - Ts - δ') * ((σ - δ) * m₂) := by ring
    linarith

  have hκ0 : 0 < κ := by
    have : 0 < 1 - Ts := by linarith
    rw [hκ]; positivity
  have hS₁ : κ * S'.card ≤ S₁.card := by
    have hdiff : S' = S₁ ∪ S'.filter (fun s => ¬ (R s : ℝ) ≤ (2 : ℝ) ^ ((Ts - κ) * D)) := by
      ext s; simp only [S', S₁, Finset.mem_union, Finset.mem_filter]; tauto
    have hdisj : Disjoint S₁ (S'.filter fun s => ¬ (R s : ℝ) ≤ (2 : ℝ) ^ ((Ts - κ) * D)) := by
      rw [Finset.disjoint_left]
      intro s hs1 hs2
      exact (Finset.mem_filter.mp hs2).2 (Finset.mem_filter.mp hs1).2.2
    set T := S'.filter fun s => ¬ (R s : ℝ) ≤ (2 : ℝ) ^ ((Ts - κ) * D)
    have hcardS' : (S'.card : ℝ) = S₁.card + T.card := by
      rw [hdiff, Finset.card_union_of_disjoint hdisj]; push_cast; ring
    have hT : (Ts - κ) * D * T.card ≤ ∑ s ∈ T, lg s := by
      have := Finset.card_nsmul_le_sum T lg ((Ts - κ) * D) fun s hs => by
        have h := (Finset.mem_filter.mp hs).2
        push Not at h
        have hsr : s ∈ Finset.range ℓ := (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).1
        exact ((Real.lt_logb_iff_rpow_lt (by norm_num) (hRpos s hsr)).mpr h).le
      rw [nsmul_eq_mul] at this
      linarith
    have hTS' : ∑ s ∈ T, lg s ≤ ∑ s ∈ S', lg s :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun s hs _ =>
        hlg0 s (Finset.mem_filter.mp hs).1
    have hkey : (Ts - κ) * D * T.card ≤ (Ts - 2 * κ) * (D * S'.card) := by
      linarith [hS'sum]
    rw [hcardS'] at hkey ⊢
    have hS₁0 : (0 : ℝ) ≤ S₁.card := Nat.cast_nonneg _
    have h6 : κ * (S₁.card + T.card) * D ≤ (Ts - κ) * S₁.card * D := by linarith
    have h7 : κ * (S₁.card + T.card) ≤ (Ts - κ) * S₁.card :=
      le_of_mul_le_mul_right h6 (by linarith)
    have h8 : (Ts - κ) * S₁.card ≤ 1 * S₁.card :=
      mul_le_mul_of_nonneg_right (by linarith) hS₁0
    linarith

  have hq1 : 0 < q - 1 := by linarith
  have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  have hS' : (1 - τ / (q - 1)) / 2 * ℓ ≤ S'.card := by
    have h1 : (S.card : ℝ) * D ≤ (((τ + ξ) / (q - 1) + δ) * ℓ) * D := by
      have e1 : (S.card : ℝ) * D = m₁ := by simp only [m₁]; ring
      have e2 : (((τ + ξ) / (q - 1) + δ) * ℓ) * D =
          (τ + ξ) / (q - 1) * (ℓ * D) + δ * (ℓ * D) := by ring
      linarith
    have h2 : (S.card : ℝ) ≤ ((τ + ξ) / (q - 1) + δ) * ℓ :=
      le_of_mul_le_mul_right h1 (by linarith)
    have e : ((τ + ξ) / (q - 1) + δ) * ℓ = τ / (q - 1) * ℓ + (ξ / (q - 1) + δ) * ℓ := by ring
    have h3 := mul_le_mul_of_nonneg_right hξ hℓ0
    linarith
  calc (1 - Ts) * σ / 4 * (1 - τ / (q - 1)) / 2 * ℓ = κ * ((1 - τ / (q - 1)) / 2 * ℓ) := by
        rw [hκ]; ring
    _ ≤ κ * S'.card := mul_le_mul_of_nonneg_left hS' hκ0.le
    _ ≤ S₁.card := hS₁

theorem core_arith {ℓ D : ℕ} (hℓ : 1 ≤ ℓ) (hD6 : 6 ≤ D) {τ η γ δ ξ q N₁ : ℝ}
    (hη : 0 < η) (hγ : 0 < γ) (hδ : 0 ≤ δ)
    (hsmall : (q + 1) * δ + ξ ≤ η * γ / 8) (hDbig : Real.logb 2 5 + 3 * τ ≤ η * γ * D / 8)
    (hN₁ : γ * ℓ ≤ N₁)
    (h : -(q * δ * (ℓ * D)) - (τ + ξ) * (ℓ * D) <
      ℓ * Real.logb 2 5 - (τ + η) * (D - 3) * N₁ - (τ - δ) * (D - 3) * (ℓ - N₁)) : False := by
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hD' : (6 : ℝ) ≤ D := by exact_mod_cast hD6
  have hD3 : 0 ≤ (D : ℝ) - 3 := by linarith

  have h1 : η * (D - 3) * (γ * ℓ) ≤ η * (D - 3) * N₁ :=
    mul_le_mul_of_nonneg_left hN₁ (mul_nonneg hη.le hD3)
  have hN₁0 : 0 ≤ N₁ := le_trans (by positivity) hN₁
  have h2 : 0 ≤ δ * (D - 3) * N₁ := mul_nonneg (mul_nonneg hδ hD3) hN₁0
  have e : (τ + η) * (D - 3) * N₁ + (τ - δ) * (D - 3) * (ℓ - N₁) =
      (τ - δ) * (D - 3) * ℓ + η * (D - 3) * N₁ + δ * (D - 3) * N₁ := by ring
  have h3 : -(q * δ * (ℓ * D)) - (τ + ξ) * (ℓ * D) <
      ℓ * Real.logb 2 5 - (τ - δ) * (D - 3) * ℓ - η * (D - 3) * (γ * ℓ) := by linarith

  have h4 : ℓ * (η * γ * (D - 3)) < ℓ * (Real.logb 2 5 + 3 * τ + (q + 1) * δ * D + ξ * D) := by
    have : ℓ * (η * γ * (D - 3)) = η * (D - 3) * (γ * ℓ) := by ring
    have hδD : 0 ≤ δ * 3 := by positivity
    nlinarith
  have h5 : η * γ * (D - 3) < Real.logb 2 5 + 3 * τ + (q + 1) * δ * D + ξ * D :=
    lt_of_mul_lt_mul_left h4 (by linarith)
  have h6 : ((q + 1) * δ + ξ) * D ≤ η * γ / 8 * D :=
    mul_le_mul_of_nonneg_right hsmall (by linarith)
  have h7 : η * γ * D / 2 ≤ η * γ * (D - 3) := by nlinarith [mul_pos hη hγ]
  nlinarith [mul_pos hη hγ]

theorem discLq_pos {m : ℕ} {ν : ℤ → ℝ} (hν : IsDyadicMeasure m ν) (q : ℝ) :
    0 < discLq m q ν := by
  obtain ⟨k, hk, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.Ico (0 : ℤ) (2 ^ m))
    (f := ν) (by rw [hν.sum_eq_one]; norm_num)
  have hpos : 0 < ν k := lt_of_le_of_ne (hν.nonneg k) (Ne.symm hne)
  unfold discLq
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos hpos q) (Finset.single_le_sum
    (f := fun k => ν k ^ q) (fun j _ => Real.rpow_nonneg (hν.nonneg j) _) hk)

set_option maxHeartbeats 4000000 in

theorem theorem51_of_inverseTheorem (hinv : InverseTheorem) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμ : μ (Set.Icc (3 / 8) (5 / 8))ᶜ = 0) {q : ℝ} (hq : 1 < q)
    (hd : DifferentiableAt ℝ (lqSpectrum μ) q) (hτ : lqSpectrum μ q < q - 1)
    (h413 : Proposition413 μ q) : Theorem51 μ q := by
  classical
  have hμ11 : μ (Set.Icc (-1) 1)ᶜ = 0 := measure_mono_null (Set.compl_subset_compl.mpr
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩) hμ
  have hμ01 : μ (Set.Ico 0 1)ᶜ = 0 := measure_mono_null (Set.compl_subset_compl.mpr
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩) hμ
  intro σ hσ
  set τ := lqSpectrum μ q with hτdef
  set Ts := legendre μ q with hTsdef
  obtain ⟨hTsα, hα1⟩ := lemma_4_9 zero_le_one hμ11 hq hd hτ
  have hTs1 : Ts < 1 := lt_of_le_of_lt hTsα hα1
  have hτ0 : 0 ≤ τ := lqSpectrum_nonneg zero_le_one hμ11 hq.le
  have hq1 : 0 < q - 1 := by linarith
  set κ := (1 - Ts) * σ / 4 with hκdef
  have hκ : 0 < κ := by have : 0 < 1 - Ts := by linarith
                        positivity
  obtain ⟨η, hη, ev_i⟩ := h413.1 (κ / 2) (by positivity)
  have hτq : τ / (q - 1) < 1 := by rw [div_lt_one hq1]; exact hτ
  set γ := κ * (1 - τ / (q - 1)) / 2 with hγdef
  have hγ : 0 < γ := by have : 0 < 1 - τ / (q - 1) := by linarith
                        positivity

  set δ' := min ((1 - Ts) / 4) (min σ ((1 - Ts) * σ / (2 * (2 - Ts + 2 * σ)))) with hδ'def
  have hTs' : 0 < 2 - Ts + 2 * σ := by linarith
  have hδ'pos : 0 < δ' := lt_min (by linarith) (lt_min hσ (by
    have : 0 < 1 - Ts := by linarith
    positivity))
  have hδ'Ts : 2 * δ' ≤ 1 - Ts := by
    have := min_le_left ((1 - Ts) / 4) (min σ ((1 - Ts) * σ / (2 * (2 - Ts + 2 * σ)))); linarith
  have hδ'σ : δ' ≤ σ := (min_le_right _ _).trans (min_le_left _ _)
  have hδ'3 : δ' * (2 - Ts + 2 * σ) ≤ (1 - Ts) * σ / 2 := by
    have h : δ' ≤ (1 - Ts) * σ / (2 * (2 - Ts + 2 * σ)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    calc δ' * (2 - Ts + 2 * σ) ≤ (1 - Ts) * σ / (2 * (2 - Ts + 2 * σ)) * (2 - Ts + 2 * σ) :=
          mul_le_mul_of_nonneg_right h hTs'.le
      _ = (1 - Ts) * σ / 2 := by
          have hne : (2 - Ts + σ * 2) ≠ 0 := by linarith
          field_simp
  obtain ⟨δ₀, hδ₀, h410⟩ := lemma_4_10 zero_le_one hμ11 hq hd hδ'pos

  set ξ := min (δ₀ / 2) (min (η * γ / 16) ((q - 1) * (1 - τ / (q - 1)) / 8)) with hξdef
  have hξ : 0 < ξ := lt_min (by positivity) (lt_min (by positivity) (by
    have : 0 < 1 - τ / (q - 1) := by linarith
    positivity))
  set δ := min (δ₀ / (2 * q)) (min δ' (min (η * γ / (16 * (q + 1))) ((1 - τ / (q - 1)) / 8)))
    with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (lt_min hδ'pos (lt_min (by positivity) (by
    have : 0 < 1 - τ / (q - 1) := by linarith
    positivity)))
  have hδδ' : δ ≤ δ' := (min_le_right _ _).trans (min_le_left _ _)
  have hqδξ : q * δ + ξ ≤ δ₀ := by
    have h1 : δ ≤ δ₀ / (2 * q) := min_le_left _ _
    have h2 : ξ ≤ δ₀ / 2 := min_le_left _ _
    have h3 : q * δ ≤ δ₀ / 2 := by
      calc q * δ ≤ q * (δ₀ / (2 * q)) := mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = δ₀ / 2 := by field_simp
    linarith
  have hsmall : (q + 1) * δ + ξ ≤ η * γ / 8 := by
    have h1 : δ ≤ η * γ / (16 * (q + 1)) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have h2 : ξ ≤ η * γ / 16 := (min_le_right _ _).trans (min_le_left _ _)
    have h3 : (q + 1) * δ ≤ η * γ / 16 := by
      calc (q + 1) * δ ≤ (q + 1) * (η * γ / (16 * (q + 1))) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = η * γ / 16 := by field_simp
    linarith
  have hξδ : ξ / (q - 1) + δ ≤ (1 - τ / (q - 1)) / 2 := by
    have h1 : δ ≤ (1 - τ / (q - 1)) / 8 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have h2 : ξ ≤ (q - 1) * (1 - τ / (q - 1)) / 8 := (min_le_right _ _).trans (min_le_right _ _)
    have h3 : ξ / (q - 1) ≤ (1 - τ / (q - 1)) / 8 := by
      rw [div_le_iff₀ hq1]; linarith
    have : 0 < 1 - τ / (q - 1) := by linarith
    linarith
  have ev_ii := h413.2 δ hδ
  obtain ⟨Ni, hNi⟩ := eventually_atTop.mp ev_i
  obtain ⟨Nii, hNii⟩ := eventually_atTop.mp ev_ii

  set D₀ : ℕ := Ni + Nii + 6 + ⌈8 * (Real.logb 2 5 + 3 * τ) / (η * γ)⌉₊ + ⌈6 * |Ts| / κ⌉₊
  obtain ⟨ε₀, hε₀, D, hDD₀, ev21⟩ := hinv q hq δ hδ D₀ (by omega)
  have hD6 : 6 ≤ D := by omega
  have hDi : Ni ≤ D - 3 := by omega
  have hDii : Nii ≤ D - 3 := by omega
  have hD' : (6 : ℝ) ≤ D := by exact_mod_cast hD6
  have hDbig : Real.logb 2 5 + 3 * τ ≤ η * γ * D / 8 := by
    have h1 : 8 * (Real.logb 2 5 + 3 * τ) / (η * γ) ≤ D := by
      calc 8 * (Real.logb 2 5 + 3 * τ) / (η * γ)
          ≤ ⌈8 * (Real.logb 2 5 + 3 * τ) / (η * γ)⌉₊ := Nat.le_ceil _
        _ ≤ D := by exact_mod_cast (show ⌈8 * (Real.logb 2 5 + 3 * τ) / (η * γ)⌉₊ ≤ D by omega)
    rw [div_le_iff₀ (by positivity)] at h1
    linarith
  have hDκ : (Ts - κ) * D ≤ (Ts - κ / 2) * ((D - 3 : ℕ) : ℝ) := by
    have h1 : 6 * |Ts| / κ ≤ D := by
      calc 6 * |Ts| / κ ≤ ⌈6 * |Ts| / κ⌉₊ := Nat.le_ceil _
        _ ≤ D := by exact_mod_cast (show ⌈6 * |Ts| / κ⌉₊ ≤ D by omega)
    rw [div_le_iff₀ hκ] at h1
    have hD3 : ((D - 3 : ℕ) : ℝ) = D - 3 := by push_cast [show 3 ≤ D by omega]; ring
    rw [hD3]
    have := neg_abs_le Ts
    have := le_abs_self Ts
    nlinarith
  set ε := min (ε₀ * q / 2) ξ with hεdef
  have hε : 0 < ε := lt_min (by positivity) hξ
  refine ⟨ε, hε, D, by omega, ?_⟩
  have hDpos : 0 < D := by omega
  have hscale : Tendsto (fun ℓ : ℕ => ℓ * D) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun ℓ hℓ => le_trans hℓ (Nat.le_mul_of_pos_right ℓ hDpos)⟩
  have ev_cor := hscale.eventually (eventually_lqSum_le zero_le_one hμ11 hq.le
    (show τ - ε₀ * q / 2 < τ by have : 0 < ε₀ * q / 2 := by positivity
                                linarith))
  have ev_410 := hscale.eventually (h410 (q * δ + ξ) (by positivity) hqδξ)
  filter_upwards [ev21, ev_cor, ev_410, eventually_ge_atTop 3] with ℓ h21 hcor h410ℓ hℓ3
    ν hν hνq
  set m := ℓ * D with hmdef
  have hm3 : 3 ≤ m := le_trans hℓ3 (Nat.le_mul_of_pos_right ℓ hDpos)
  have hmR : (m : ℝ) = ℓ * D := by simp only [m]; push_cast; ring
  have hm0 : (0 : ℝ) < m := by have : (3 : ℝ) ≤ m := by exact_mod_cast hm3
                               linarith
  set d := discretize μ m
  have hdd : IsDyadicMeasure m d := isDyadicMeasure_discretize hμ01 m
  have hdLq : discLq m q d = lqSum μ q m := discLq_discretize hμ01 (by linarith) m
  by_contra hcon
  push Not at hcon
  have hconv_le : discLq m q (circConv m ν d) ≤ lqSum μ q m := by
    rw [← hdLq]; exact discLq_circConv_le hν hdd.nonneg hq.le

  have h52 : (2 : ℝ) ^ (-((τ + ξ) * m)) < lqSum μ q m := by
    by_contra h
    push Not at h
    have : (2 : ℝ) ^ (-((τ + ξ) * m)) ≤ (2 : ℝ) ^ (-((τ + ε) * m)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        have := mul_le_mul_of_nonneg_right (min_le_right (ε₀ * q / 2) ξ) hm0.le
        linarith)
    linarith

  have hhyp : (2 : ℝ) ^ (-(ε₀ * (m : ℕ))) * discLq m q d ^ (1 / q) ≤
      discLq m q (circConv m d ν) ^ (1 / q) := by
    rw [circConv_comm]
    have hd0 : 0 ≤ discLq m q d := (discLq_pos hdd q).le
    have h1 : (2 : ℝ) ^ (-(ε₀ * q * m)) * discLq m q d ≤ discLq m q (circConv m ν d) := by
      have h2 : (2 : ℝ) ^ (-(ε₀ * q * m)) * discLq m q d ≤
          (2 : ℝ) ^ (-(ε₀ * q * m)) * (2 : ℝ) ^ (-((τ - ε₀ * q / 2) * m)) :=
        mul_le_mul_of_nonneg_left (by rw [hdLq]; exact hcor) (by positivity)
      have h3 : (2 : ℝ) ^ (-(ε₀ * q * m)) * (2 : ℝ) ^ (-((τ - ε₀ * q / 2) * m)) ≤
          (2 : ℝ) ^ (-((τ + ε) * m)) := by
        rw [two_rpow_mul_two_rpow]
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have := mul_le_mul_of_nonneg_right (min_le_left (ε₀ * q / 2) ξ) hm0.le
        nlinarith
      linarith
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (-(ε₀ * q * m)) := Real.rpow_pos_of_pos (by norm_num) _
    have hq0 : (0 : ℝ) ≤ 1 / q := by
      have : (0 : ℝ) < q := by linarith
      exact (div_pos one_pos this).le
    have e : -(ε₀ * q * (m : ℝ)) * (1 / q) = -(ε₀ * m) := by
      have : (q : ℝ) ≠ 0 := by linarith
      field_simp
    calc (2 : ℝ) ^ (-(ε₀ * (m : ℕ))) * discLq m q d ^ (1 / q)
        = ((2 : ℝ) ^ (-(ε₀ * q * m)) * discLq m q d) ^ (1 / q) := by
          rw [Real.mul_rpow h2pos.le hd0, ← Real.rpow_mul (by norm_num), e]
      _ ≤ discLq m q (circConv m ν d) ^ (1 / q) :=
          Real.rpow_le_rpow (mul_nonneg h2pos.le hd0) h1 hq0
  obtain ⟨a, b, A, B, R', R'', hIC⟩ := h21 d ν hdd hν hhyp
  set μ' := circTranslate m a d with hμ'def
  have hA0 : ∀ x ∈ A, 0 ≤ x ∧ x < 2 ^ m := by
    intro x hx
    have h := hIC.pos_A x hx
    by_contra hx'
    simp only [μ', circTranslate, ite_eq_of_neg hx'] at h
    exact lt_irrefl 0 h
  have hmid : ∀ x ∈ A, ∀ s < ℓ, InMiddleHalf (m - s * D) x := fun x hx s hs =>
    hIC.middle_A x hx s hs
  have hmid0 : ∀ x ∈ A, InMiddleHalf m x := fun x hx => by
    have := hIC.middle_A x hx 0 (by omega)
    simpa using this
  obtain ⟨e, he⟩ := exists_offset hμ hm3 hIC.pos_A hmid0
  have he' : ∀ x ∈ A, μ' x = μ.real (dyadicIco m (x + e)) := fun x hx => (he x hx).1

  have hdLq' : discLq m q μ' = lqSum μ q m := by rw [hμ'def, discLq_circTranslate, hdLq]
  have hAsum0 : 0 ≤ ∑ x ∈ A, μ' x ^ q :=
    Finset.sum_nonneg fun x hx => Real.rpow_nonneg (hIC.pos_A x hx).le _
  have hAi : (2 : ℝ) ^ (-(q * δ * m)) * lqSum μ q m ≤ ∑ x ∈ A, μ' x ^ q := by
    have h := hIC.lq_A
    have hL0 : 0 ≤ discLq m q μ' := by rw [hdLq']; exact lqSum_nonneg _ _ _
    have h2 := Real.rpow_le_rpow (by positivity) h (by linarith : (0 : ℝ) ≤ q)
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hL0 _), ← Real.rpow_mul hL0,
      ← Real.rpow_mul hAsum0, ← Real.rpow_mul (by norm_num),
      show 1 / q * q = 1 by field_simp, Real.rpow_one, Real.rpow_one, hdLq'] at h2
    have e : -(δ * ((ℓ * D : ℕ) : ℝ)) * q = -(q * δ * m) := by simp only [m]; ring
    rw [e] at h2
    exact h2
  have hlq_pos : 0 < lqSum μ q m := lt_trans (by positivity) h52
  have hAsum_pos : 0 < ∑ x ∈ A, μ' x ^ q := lt_of_lt_of_le (by positivity) hAi
  have hAne : A.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at hAsum_pos
    exact lt_irrefl 0 hAsum_pos

  have hR'1 : ∀ s < ℓ, 1 ≤ R' s := by
    intro s hs
    obtain ⟨x, hx⟩ := hAne
    rw [← hIC.regular_A s hs x hx]
    unfold branching
    exact Finset.card_pos.mpr ⟨x / 2 ^ (m - (s + 1) * D),
      Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hx, rfl⟩)⟩
  have hcardA : A.card = ∏ s ∈ Finset.range ℓ, R' s :=
    card_eq_prod_branching rfl hAne hA0 hIC.regular_A

  obtain ⟨x₀, hx₀, hmax⟩ := A.exists_max_image μ' hAne
  set M := μ' x₀
  have hM : 0 < M := hIC.pos_A x₀ hx₀
  have hM1 : M ≤ 1 := by
    show μ' x₀ ≤ 1
    rw [he' x₀ hx₀]; exact measureReal_le_one
  set αt := -Real.logb 2 (M / 2) / m
  have hαt : (2 : ℝ) ^ (-(αt * m)) = M / 2 := by
    simp only [αt]
    rw [div_mul_cancel₀ _ hm0.ne', neg_neg, Real.rpow_logb (by norm_num) (by norm_num)
      (by positivity)]
  have hαt0 : 0 ≤ αt := by
    simp only [αt]
    refine div_nonneg ?_ hm0.le
    have : Real.logb 2 (M / 2) ≤ 0 := Real.logb_nonpos (by norm_num) (by positivity)
      (by linarith)
    linarith
  have hinj : Set.InjOn (fun x => x + e) ↑A := fun x _ y _ h => by simpa using h
  have hcardA' : (A.card : ℝ) ≤ (2 : ℝ) ^ (m * (Ts + δ')) := by
    have hcell : ∀ k ∈ A.image (fun x => x + e), (2 : ℝ) ^ (-(αt * m)) ≤
        μ.real (dyadicIco m k) ∧ μ.real (dyadicIco m k) ≤ 2 * (2 : ℝ) ^ (-(αt * m)) := by
      intro k hk
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
      rw [← he' x hx, hαt]
      constructor
      · have := hIC.flat_A x hx x₀ hx₀; linarith
      · have := hmax x hx; linarith
    have hsum : (2 : ℝ) ^ (-((τ + (q * δ + ξ)) * m)) ≤
        ∑ k ∈ A.image (fun x => x + e), μ.real (dyadicIco m k) ^ q := by
      rw [Finset.sum_image hinj]
      have e1 : ∑ x ∈ A, μ.real (dyadicIco m (x + e)) ^ q = ∑ x ∈ A, μ' x ^ q :=
        Finset.sum_congr rfl fun x hx => by rw [he' x hx]
      rw [e1]
      calc (2 : ℝ) ^ (-((τ + (q * δ + ξ)) * m))
          = (2 : ℝ) ^ (-(q * δ * m)) * (2 : ℝ) ^ (-((τ + ξ) * m)) := by
            rw [two_rpow_mul_two_rpow]; congr 1; ring
        _ ≤ (2 : ℝ) ^ (-(q * δ * m)) * lqSum μ q m :=
            mul_le_mul_of_nonneg_left h52.le (by positivity)
        _ ≤ _ := hAi
    have := h410ℓ (A.image fun x => x + e) αt hαt0 hcell hsum
    rwa [Finset.card_image_of_injOn hinj] at this

  have hνpos := discLq_pos hν q
  have hS1 : σ * m - δ * m ≤ D * (fullScales δ ℓ D R').card := by
    have h := hIC.count_le
    rw [discLq_circTranslate] at h
    have h1 : σ * m ≤ Real.logb 2 (discLq m q ν ^ (-(1 / (q - 1)))) := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (Real.rpow_pos_of_pos hνpos _),
        Real.rpow_neg hνpos.le]
      have hνq' : discLq m q ν ^ (1 / (q - 1)) ≤ (2 : ℝ) ^ (-(σ * m)) := hνq
      calc (2 : ℝ) ^ (σ * m) = ((2 : ℝ) ^ (-(σ * m)))⁻¹ := by
            rw [Real.rpow_neg (by norm_num), inv_inv]
        _ ≤ (discLq m q ν ^ (1 / (q - 1)))⁻¹ :=
            inv_anti₀ (Real.rpow_pos_of_pos hνpos _) hνq'
    have e1 : (((ℓ * D : ℕ) : ℝ)) = m := rfl
    rw [e1] at h
    linarith
  have hS2 : (D : ℝ) * (fullScales δ ℓ D R').card ≤ (τ + ξ) / (q - 1) * m + δ * m := by
    have h := hIC.le_count
    rw [hdLq'] at h
    have h1 : Real.logb 2 (lqSum μ q m ^ (-(1 / (q - 1)))) ≤ (τ + ξ) / (q - 1) * m := by
      rw [Real.logb_le_iff_le_rpow (by norm_num) (Real.rpow_pos_of_pos hlq_pos _)]
      have hneg : -(1 / (q - 1)) ≤ 0 := by
        have : 0 < 1 / (q - 1) := by positivity
        linarith
      have h2 := Real.rpow_le_rpow_of_nonpos (by positivity) h52.le hneg
      rw [← Real.rpow_mul (by norm_num)] at h2
      have e2 : -((τ + ξ) * (m : ℝ)) * -(1 / (q - 1)) = (τ + ξ) / (q - 1) * m := by
        field_simp
      rw [e2] at h2
      exact h2
    have e1 : (((ℓ * D : ℕ) : ℝ)) = m := rfl
    rw [e1] at h
    linarith

  have hD3 : 3 ≤ D := by omega
  have hcount := card_small_scales_ge (ℓ := ℓ) (D := D) (by omega) hR'1 hq hσ hTs1 hδδ' hδ'σ
    hδ'Ts hδ'3 hξδ (by rw [← hcardA]; exact hcardA') hS1 hS2
  set S₁ := (Finset.range ℓ).filter fun s => s ∉ fullScales δ ℓ D R' ∧
    (R' s : ℝ) ≤ (2 : ℝ) ^ ((Ts - (1 - Ts) * σ / 4) * D) with hS₁def
  have hS₁sub : S₁ ⊆ Finset.range ℓ := Finset.filter_subset _ _

  set Λ : ℕ → ℝ := fun s => if s ∈ S₁ then (2 : ℝ) ^ (-((τ + η) * ((D - 3 : ℕ) : ℝ)))
    else (2 : ℝ) ^ (-((τ - δ) * ((D - 3 : ℕ) : ℝ))) with hΛdef
  have hΛ0 : ∀ s, 0 ≤ Λ s := fun s => by
    simp only [Λ]; split_ifs <;> positivity
  have hH : ∀ s < ℓ, ∀ c' ∈ cellsAt m (s * D + 3) A,
      ∑ c'' ∈ (cellsAt m (s * D + D) A).filter (fun c'' => c'' / 2 ^ (D - 3) = c'),
        μ.real (gridIco m (s * D + D) e c'') ^ q ≤
        Λ s * μ.real (doubleIco (((c' * 2 ^ (m - (s * D + 3)) + e : ℤ) : ℝ) / 2 ^ m)
          (s * D + 3)) ^ q := by
    intro s hs c' hc'
    have hsD' : (s + 1) * D ≤ m := by simp only [m]; exact Nat.mul_le_mul_right D hs
    have hsD : s * D + D ≤ m := by rw [show s * D + D = (s + 1) * D by ring]; exact hsD'
    obtain ⟨Dj, hDj, hDjcard, hDjsum⟩ := sum_children_eq μ q hD3 hsD e A c'
    rw [hDjsum]
    by_cases hsS : s ∈ S₁
    · simp only [Λ, ite_eq_of_pos hsS]
      have hcb : (Dj.card : ℝ) ≤ (2 : ℝ) ^ ((legendre μ q - κ / 2) * ((D - 3 : ℕ) : ℝ)) := by
        have h1 : Dj.card ≤ R' s := by
          rw [hDjcard]
          exact card_children_le hD3 hsD' (hIC.regular_A s hs) hc'
        have h2 : (R' s : ℝ) ≤ (2 : ℝ) ^ ((Ts - κ) * D) := (Finset.mem_filter.mp hsS).2.2
        calc (Dj.card : ℝ) ≤ R' s := by exact_mod_cast h1
          _ ≤ (2 : ℝ) ^ ((Ts - κ) * D) := h2
          _ ≤ (2 : ℝ) ^ ((legendre μ q - κ / 2) * ((D - 3 : ℕ) : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hDκ
      exact hNi (D - 3) hDi (s * D + 3) _ Dj hDj hcb
    · simp only [Λ, ite_eq_of_neg hsS]
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun j hj =>
        Finset.mem_range.mpr (hDj j hj)) fun j _ _ => Real.rpow_nonneg measureReal_nonneg _) ?_
      exact hNii (D - 3) hDii (s * D + 3) _
  have hL := levelSum_le_prod μ hq.le rfl hD3 e hmid Λ hΛ0 hH ℓ le_rfl
  have hL0 := levelSum_zero_le_one μ (by linarith : (0 : ℝ) < q) (m := m) e hA0
  have hLm : levelSum μ q m (ℓ * D) e A = ∑ x ∈ A, μ' x ^ q := by
    show levelSum μ q m m e A = _
    rw [levelSum_self]
    exact Finset.sum_congr rfl fun x hx => by rw [he' x hx]

  have hfilter : (Finset.range ℓ).filter (fun s => s ∈ S₁) = S₁ := by
    ext s; simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hS₁sub h, h⟩⟩
  have hfilter' : ((Finset.range ℓ).filter (fun s => s ∉ S₁)).card = ℓ - S₁.card := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.range ℓ) (fun s => s ∈ S₁)
    rw [hfilter, Finset.card_range] at this
    omega
  set x₁ : ℝ := -((τ + η) * ((D - 3 : ℕ) : ℝ))
  set x₂ : ℝ := -((τ - δ) * ((D - 3 : ℕ) : ℝ))
  have hprod : ∏ t ∈ Finset.range ℓ, (5 * Λ t) =
      (2 : ℝ) ^ (ℓ * Real.logb 2 5 + x₁ * S₁.card + x₂ * (ℓ - S₁.card : ℕ)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    simp only [Λ]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, hfilter, hfilter']
    rw [← Real.rpow_natCast, ← Real.rpow_natCast ((2 : ℝ) ^ x₁),
      ← Real.rpow_natCast ((2 : ℝ) ^ x₂), ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num)]
    have h5 : (5 : ℝ) ^ (ℓ : ℝ) = (2 : ℝ) ^ (ℓ * Real.logb 2 5) := by
      rw [mul_comm, Real.rpow_mul (by norm_num),
        Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]
    rw [h5, two_rpow_mul_two_rpow, two_rpow_mul_two_rpow]
    congr 1
    ring

  have hfinal : (2 : ℝ) ^ (-(q * δ * m) + -((τ + ξ) * m)) <
      (2 : ℝ) ^ (ℓ * Real.logb 2 5 + x₁ * S₁.card + x₂ * (ℓ - S₁.card : ℕ)) := by
    rw [← two_rpow_mul_two_rpow, ← hprod]
    calc (2 : ℝ) ^ (-(q * δ * m)) * (2 : ℝ) ^ (-((τ + ξ) * m))
        < (2 : ℝ) ^ (-(q * δ * m)) * lqSum μ q m :=
          mul_lt_mul_of_pos_left h52 (by positivity)
      _ ≤ ∑ x ∈ A, μ' x ^ q := hAi
      _ = levelSum μ q m (ℓ * D) e A := hLm.symm
      _ ≤ (∏ t ∈ Finset.range ℓ, (5 * Λ t)) * levelSum μ q m 0 e A := hL
      _ ≤ ∏ t ∈ Finset.range ℓ, (5 * Λ t) := by
          have : 0 ≤ ∏ t ∈ Finset.range ℓ, (5 * Λ t) :=
            Finset.prod_nonneg fun t _ => by have := hΛ0 t; positivity
          exact mul_le_of_le_one_right this hL0
  have hexp := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hfinal
  have hD3R : ((D - 3 : ℕ) : ℝ) = D - 3 := by push_cast [hD3]; ring
  have hS₁.cardℓ : S₁.card ≤ ℓ := by
    have := Finset.card_le_card hS₁sub; rwa [Finset.card_range] at this
  have hℓN : ((ℓ - S₁.card : ℕ) : ℝ) = ℓ - S₁.card := by push_cast [hS₁.cardℓ]; ring
  simp only [x₁, x₂, hD3R, hℓN] at hexp
  rw [hmR] at hexp
  refine core_arith (ℓ := ℓ) (D := D) (τ := τ) (η := η) (γ := γ) (δ := δ) (ξ := ξ) (q := q)
    (N₁ := S₁.card) (by omega) hD6 hη hγ hδ.le hsmall hDbig ?_ ?_
  · have := hcount
    simp only [hγdef, hκdef]
    linarith
  · linarith

end Lq

end FractalGeometry
