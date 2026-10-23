import Mathlib
import ExactOverlaps.SelfSimilar.CompactSupport
import FractalGeometry.Entropy.Lq.Statement
import FractalGeometry.Pressure.Rectangular.LyapunovStatement
import FractalGeometry.SelfSimilar.SimilarityWords

open MeasureTheory Filter Topology Set

namespace FractalGeometry

namespace Lq

def dyadicIco (m : ℕ) (k : ℤ) : Set ℝ := Set.Ico ((k : ℝ) / 2 ^ m) ((k + 1) / 2 ^ m)

noncomputable def lqSum (ν : Measure ℝ) (q : ℝ) (m : ℕ) : ℝ :=
  ∑' k : ℤ, ν.real (dyadicIco m k) ^ q

noncomputable def lqSpectrum (ν : Measure ℝ) (q : ℝ) : ℝ :=
  Filter.liminf (fun m : ℕ => -Real.logb 2 (lqSum ν q m) / m) Filter.atTop

variable {κ : Type*}

def wordRatio (r : κ → ℝ) (u : List κ) : ℝ := (u.map r).prod

def wordWeight (p : κ → ℝ) (u : List κ) : ℝ := (u.map p).prod

@[simp] theorem wordRatio_nil (r : κ → ℝ) : wordRatio r [] = 1 := rfl

@[simp] theorem wordWeight_nil (p : κ → ℝ) : wordWeight p [] = 1 := rfl

theorem wordRatio_append (r : κ → ℝ) (u v : List κ) :
    wordRatio r (u ++ v) = wordRatio r u * wordRatio r v := by
  simp [wordRatio]

theorem wordWeight_append (p : κ → ℝ) (u v : List κ) :
    wordWeight p (u ++ v) = wordWeight p u * wordWeight p v := by
  simp [wordWeight]

theorem wordWeight_pos {p : κ → ℝ} (hp : ∀ j, 0 < p j) (u : List κ) : 0 < wordWeight p u := by
  unfold wordWeight
  induction u with
  | nil => simp
  | cons j u ih => simpa using mul_pos (hp j) ih

theorem abs_wordRatio_le_one {r : κ → ℝ} (hr1 : ∀ j, |r j| < 1) (u : List κ) :
    |wordRatio r u| ≤ 1 := by
  unfold wordRatio
  induction u with
  | nil => simp
  | cons j u ih =>
    simp only [List.map_cons, List.prod_cons, abs_mul]
    calc |r j| * |(u.map r).prod| ≤ 1 * 1 :=
          mul_le_mul (hr1 j).le ih (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1

theorem abs_wordRatio_le_pow {r : κ → ℝ} {ρ : ℝ} (hρ : ∀ j, |r j| ≤ ρ) (u : List κ) :
    |wordRatio r u| ≤ ρ ^ u.length := by
  unfold wordRatio
  induction u with
  | nil => simp
  | cons j u ih =>
    simp only [List.map_cons, List.prod_cons, abs_mul, List.length_cons, pow_succ]
    rw [mul_comm (ρ ^ u.length)]
    exact mul_le_mul (hρ j) ih (abs_nonneg _) ((abs_nonneg _).trans (hρ j))

theorem abs_wordRatio_ne_zero {r : κ → ℝ} (hr : ∀ j, r j ≠ 0) (u : List κ) :
    wordRatio r u ≠ 0 := by
  unfold wordRatio
  induction u with
  | nil => simp
  | cons j u ih => simpa using mul_ne_zero (hr j) ih

noncomputable def omega (r : κ → ℝ) (m : ℕ) : Finset (List κ) :=
  open Classical in
  if h : {u : List κ | ShmerkinStopping r m u}.Finite then h.toFinset else ∅

theorem exists_ratio_bound [Finite κ] {r : κ → ℝ} (hr1 : ∀ j, |r j| < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ j, |r j| ≤ ρ := by
  cases isEmpty_or_nonempty κ with
  | inl h => exact ⟨1 / 2, by norm_num, by norm_num, fun j => (IsEmpty.false j).elim⟩
  | inr h =>
    obtain ⟨j₀, hj₀⟩ := Finite.exists_max fun j => |r j|
    exact ⟨max |r j₀| (1 / 2), by positivity, max_lt (hr1 j₀) (by norm_num),
      fun j => le_max_of_le_left (hj₀ j)⟩

theorem finite_shmerkinStopping [Finite κ] {r : κ → ℝ} (hr1 : ∀ j, |r j| < 1) (m : ℕ) :
    {u : List κ | ShmerkinStopping r m u}.Finite := by
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := exists_ratio_bound hr1
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 2 ^ (-(m : ℝ)) by positivity) hρ1
  refine (List.finite_length_le κ N).subset ?_
  intro u hu
  obtain ⟨-, -, h2⟩ := hu
  have h3 := abs_wordRatio_le_pow (r := r) hρ u.dropLast
  have h4 : ρ ^ N < ρ ^ u.dropLast.length := by
    unfold wordRatio at h3
    linarith
  have h5 : u.dropLast.length < N := (pow_lt_pow_iff_right_of_lt_one₀ hρ0 hρ1).mp h4
  simp only [List.length_dropLast] at h5
  show u.length ≤ N
  omega

theorem mem_omega [Finite κ] {r : κ → ℝ} (hr1 : ∀ j, |r j| < 1) {m : ℕ} {u : List κ} :
    u ∈ omega r m ↔ ShmerkinStopping r m u := by
  classical
  unfold omega
  have h := finite_shmerkinStopping hr1 m
  simp [h]

theorem not_stopping_of_lt {r : κ → ℝ} {m : ℕ} {v : List κ}
    (hv : (2 : ℝ) ^ (-(m : ℝ)) < |wordRatio r v|) : ¬ ShmerkinStopping r m v :=
  fun h => absurd h.2.1 (not_le.mpr hv)

theorem stopping_append_singleton {r : κ → ℝ} {m : ℕ} {v : List κ} {j : κ}
    (hv : (2 : ℝ) ^ (-(m : ℝ)) < |wordRatio r v|)
    (hj : |wordRatio r (v ++ [j])| ≤ (2 : ℝ) ^ (-(m : ℝ))) :
    ShmerkinStopping r m (v ++ [j]) := by
  refine ⟨by simp, hj, ?_⟩
  rw [List.dropLast_concat]
  exact hv

theorem eq_of_stopping_of_prefix {r : κ → ℝ} (hr1 : ∀ j, |r j| < 1) {m : ℕ} {w u : List κ}
    (hw : |wordRatio r w| ≤ (2 : ℝ) ^ (-(m : ℝ))) (hu : ShmerkinStopping r m u)
    (hwu : w <+: u) : u = w := by
  obtain ⟨x, rfl⟩ := hwu
  rcases List.eq_nil_or_concat' x with hx | ⟨y, b, rfl⟩
  · simp [hx]
  · exfalso
    have h1 : (2 : ℝ) ^ (-(m : ℝ)) < |wordRatio r (w ++ (y ++ [b])).dropLast| := hu.2.2
    rw [← List.append_assoc, List.dropLast_concat, wordRatio_append, abs_mul] at h1
    have h2 := abs_wordRatio_le_one hr1 y
    have h3 : |wordRatio r w| * |wordRatio r y| ≤ |wordRatio r w| :=
      mul_le_of_le_one_right (abs_nonneg _) h2
    linarith

theorem sum_omega_prefix_eq [Fintype κ] [DecidableEq κ] {r : κ → ℝ} (hr1 : ∀ j, |r j| < 1)
    {M' : Type*}
    [AddCommMonoid M'] (F : List κ → M') (hF : ∀ v, F v = ∑ j, F (v ++ [j])) (m : ℕ) :
    ∀ n : ℕ, ∀ v : List κ, (2 : ℝ) ^ (-(m : ℝ)) < |wordRatio r v| →
      (∀ w, v <+: w → (2 : ℝ) ^ (-(m : ℝ)) < |wordRatio r w| → w.length < v.length + n) →
      ∑ u ∈ (omega r m).filter (fun u => v <+: u), F u = F v := by
  intro n
  induction n with
  | zero =>
    intro v hv hlen
    exact absurd (hlen v (List.prefix_refl v) hv) (by simp)
  | succ n ih =>
    intro v hv hlen
    have hsplit : (omega r m).filter (fun u => v <+: u) =
        Finset.univ.biUnion fun j => (omega r m).filter (fun u => v ++ [j] <+: u) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hu, x, rfl⟩
        rcases x with _ | ⟨j, x⟩
        · exact absurd ((mem_omega hr1).mp hu) (not_stopping_of_lt (by simpa using hv))
        · exact ⟨j, hu, x, by simp⟩
      · rintro ⟨j, hu, hju⟩
        exact ⟨hu, (List.prefix_append v [j]).trans hju⟩
    have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset κ))
        fun j => (omega r m).filter (fun u => v ++ [j] <+: u) := by
      intro j _ j' _ hjj'
      rw [Function.onFun, Finset.disjoint_left]
      intro u hu hu'
      simp only [Finset.mem_filter] at hu hu'
      have hlen : (v ++ [j]).length = (v ++ [j']).length := by simp
      have heq : v ++ [j] = v ++ [j'] :=
        (List.prefix_of_prefix_length_le hu.2 hu'.2 hlen.le).eq_of_length hlen
      exact hjj' (by simpa using heq)
    rw [hsplit, Finset.sum_biUnion hdisj, hF v]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : |wordRatio r (v ++ [j])| ≤ (2 : ℝ) ^ (-(m : ℝ))
    · have hmem : v ++ [j] ∈ (omega r m).filter (fun u => v ++ [j] <+: u) := by
        simp only [Finset.mem_filter]
        exact ⟨(mem_omega hr1).mpr (stopping_append_singleton hv hj), List.prefix_refl _⟩
      rw [Finset.sum_eq_single_of_mem _ hmem]
      intro u hu hne
      simp only [Finset.mem_filter] at hu
      exact absurd (eq_of_stopping_of_prefix hr1 hj ((mem_omega hr1).mp hu.1) hu.2) hne
    · replace hj := not_le.mp hj
      refine ih (v ++ [j]) hj fun w hw hw' => ?_
      have := hlen w ((List.prefix_append v [j]).trans hw) hw'
      simp only [List.length_append, List.length_singleton]
      omega

theorem sum_omega_eq [Fintype κ] {r : κ → ℝ} (hr1 : ∀ j, |r j| < 1) {M' : Type*}
    [AddCommMonoid M'] (F : List κ → M') (hF : ∀ v, F v = ∑ j, F (v ++ [j])) {m : ℕ}
    (hm : 1 ≤ m) : ∑ u ∈ omega r m, F u = F [] := by
  classical
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := exists_ratio_bound hr1
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 2 ^ (-(m : ℝ)) by positivity) hρ1
  have h1 : (2 : ℝ) ^ (-(m : ℝ)) < |wordRatio r []| := by
    simp only [wordRatio_nil, abs_one]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith)
  have h := sum_omega_prefix_eq hr1 F hF m N [] h1 fun w _ hw => by
    have h3 := abs_wordRatio_le_pow (r := r) hρ w
    have h4 : ρ ^ N < ρ ^ w.length := by linarith
    simpa using (pow_lt_pow_iff_right_of_lt_one₀ hρ0 hρ1).mp h4
  rw [← h]
  congr 1
  ext u
  simp

noncomputable def ratioSet (r : κ → ℝ) (m : ℕ) : Finset ℝ :=
  open Classical in (omega r m).image (wordRatio r)

theorem exists_length_bound [Finite κ] {r : κ → ℝ} (hr1 : ∀ j, |r j| < 1) :
    ∃ A : ℕ, ∀ m : ℕ, ∀ u : List κ, ShmerkinStopping r m u → u.length ≤ A * (m + 1) := by
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := exists_ratio_bound hr1
  obtain ⟨A, hA⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / 2 by norm_num) hρ1
  refine ⟨A + 1, fun m u hu => ?_⟩
  by_contra hlen
  push Not at hlen
  have h2 := hu.2.2
  have h3 := abs_wordRatio_le_pow (r := r) hρ u.dropLast
  have hle : A * m ≤ u.dropLast.length := by
    simp only [List.length_dropLast]
    have : (A + 1) * (m + 1) = A * m + A + m + 1 := by ring
    omega
  have h4 : ρ ^ u.dropLast.length ≤ ρ ^ (A * m) := pow_le_pow_of_le_one hρ0.le hρ1.le hle
  have h5 : ρ ^ (A * m) ≤ (1 / 2) ^ m := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hA.le m
  have h6 : ((1 : ℝ) / 2) ^ m = (2 : ℝ) ^ (-(m : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
  unfold wordRatio at h3
  change (2 : ℝ) ^ (-(m : ℝ)) < |wordRatio r u.dropLast| at h2
  unfold wordRatio at h2
  linarith

theorem wordRatio_eq_prod_count [Fintype κ] [DecidableEq κ] (r : κ → ℝ) (u : List κ) :
    wordRatio r u = ∏ j, r j ^ u.count j := by
  unfold wordRatio
  rw [Finset.prod_list_map_count]
  refine Finset.prod_subset (Finset.subset_univ _) fun j _ hj => ?_
  rw [List.mem_toFinset] at hj
  simp [List.count_eq_zero_of_not_mem hj]

theorem card_ratioSet_le [Fintype κ] {r : κ → ℝ} (hr1 : ∀ j, |r j| < 1) :
    ∃ A : ℕ, ∀ m : ℕ, (ratioSet r m).card ≤ (A * (m + 1) + 1) ^ Fintype.card κ := by
  classical
  obtain ⟨A, hA⟩ := exists_length_bound hr1
  refine ⟨A, fun m => ?_⟩
  set B := A * (m + 1)
  have hsub : ratioSet r m ⊆ ((omega r m).image fun u => fun j => u.count j).image
      fun c : κ → ℕ => ∏ j, r j ^ c j := by
    intro x hx
    unfold ratioSet at hx
    rw [Finset.mem_image] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    rw [Finset.image_image, Finset.mem_image]
    exact ⟨u, hu, (wordRatio_eq_prod_count r u).symm⟩
  have hsub2 : ((omega r m).image fun u => fun j => u.count j) ⊆
      Fintype.piFinset fun _ : κ => Finset.range (B + 1) := by
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨u, hu, rfl⟩ := hc
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_range]
    have := hA m u ((mem_omega hr1).mp hu)
    have := List.count_le_length (a := j) (l := u)
    omega
  calc (ratioSet r m).card ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_image_le
    _ ≤ _ := Finset.card_le_card hsub2
    _ = (B + 1) ^ Fintype.card κ := by simp

theorem sum_omega_weight_rpow_le [Fintype κ] {r p : κ → ℝ} (hr : ∀ j, r j ≠ 0)
    (hr1 : ∀ j, |r j| < 1) (hp : ∀ j, 0 < p j) {q β : ℝ} (hβ : 0 ≤ β)
    (hsum : ∑ j, p j ^ q * |r j| ^ (-β) ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    ∑ u ∈ omega r m, wordWeight p u ^ q ≤ (2 : ℝ) ^ (-(m * β)) := by
  classical
  cases isEmpty_or_nonempty κ with
  | inl h =>
    have : omega r m = ∅ := by
      ext u
      simp only [Finset.notMem_empty, iff_false]
      intro hu
      obtain ⟨j, -⟩ := List.exists_mem_of_ne_nil u ((mem_omega hr1).mp hu).1
      exact IsEmpty.false j
    rw [this, Finset.sum_empty]
    positivity
  | inr hne =>
  set S := ∑ j, p j ^ q * |r j| ^ (-β) with hS
  have hpos : ∀ j, 0 < p j ^ q * |r j| ^ (-β) := fun j =>
    mul_pos (Real.rpow_pos_of_pos (hp j) _)
      (Real.rpow_pos_of_pos (abs_pos.mpr (hr j)) _)
  have hS0 : 0 < S := Finset.sum_pos (fun j _ => hpos j) Finset.univ_nonempty
  let F : List κ → ℝ := fun u => wordWeight p u ^ q * |wordRatio r u| ^ (-β) / S ^ u.length
  have hF : ∀ v, F v = ∑ j, F (v ++ [j]) := by
    intro v
    have hwv : 0 ≤ wordWeight p v := (wordWeight_pos hp v).le
    simp only [F, wordWeight_append, wordRatio_append, abs_mul, List.length_append,
      List.length_singleton, pow_succ]
    have h1 : ∀ j, (wordWeight p v * wordWeight p [j]) ^ q *
        (|wordRatio r v| * |wordRatio r [j]|) ^ (-β) / (S ^ v.length * S) =
        wordWeight p v ^ q * |wordRatio r v| ^ (-β) / S ^ v.length *
          (p j ^ q * |r j| ^ (-β)) / S := by
      intro j
      rw [Real.mul_rpow hwv (wordWeight_pos hp [j]).le,
        Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
      simp only [wordWeight, wordRatio, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one]
      field_simp
    simp_rw [h1]
    rw [← Finset.sum_div, ← Finset.mul_sum, ← hS]
    field_simp
  have hsumF := sum_omega_eq hr1 F hF hm
  have hF0 : F [] = 1 := by simp [F]
  rw [hF0] at hsumF
  have hterm : ∀ u ∈ omega r m,
      wordWeight p u ^ q * (2 : ℝ) ^ (m * β) ≤ F u := by
    intro u hu
    have hst := (mem_omega hr1).mp hu
    have hlam : 0 < |wordRatio r u| := abs_pos.mpr (abs_wordRatio_ne_zero hr u)
    have h1 : (2 : ℝ) ^ (m * β) ≤ |wordRatio r u| ^ (-β) := by
      have h2 : |wordRatio r u| ≤ (2 : ℝ) ^ (-(m : ℝ)) := hst.2.1
      calc (2 : ℝ) ^ (m * β) = ((2 : ℝ) ^ (-(m : ℝ))) ^ (-β) := by
            rw [← Real.rpow_mul (by norm_num)]; ring_nf
        _ ≤ |wordRatio r u| ^ (-β) :=
            Real.rpow_le_rpow_of_nonpos hlam h2 (by linarith)
    have hS1 : S ^ u.length ≤ 1 := pow_le_one₀ hS0.le hsum
    have hw : 0 ≤ wordWeight p u ^ q := Real.rpow_nonneg (wordWeight_pos hp u).le _
    calc wordWeight p u ^ q * (2 : ℝ) ^ (m * β)
        ≤ wordWeight p u ^ q * |wordRatio r u| ^ (-β) := mul_le_mul_of_nonneg_left h1 hw
      _ ≤ wordWeight p u ^ q * |wordRatio r u| ^ (-β) / S ^ u.length := by
          rw [le_div_iff₀ (pow_pos hS0 _)]
          exact mul_le_of_le_one_right (mul_nonneg hw (Real.rpow_nonneg hlam.le _)) hS1
  have hsum2 : (∑ u ∈ omega r m, wordWeight p u ^ q) * (2 : ℝ) ^ (m * β) ≤ 1 := by
    rw [Finset.sum_mul, ← hsumF]
    exact Finset.sum_le_sum hterm
  calc ∑ u ∈ omega r m, wordWeight p u ^ q
      = (∑ u ∈ omega r m, wordWeight p u ^ q) * (2 : ℝ) ^ (m * β) *
          (2 : ℝ) ^ (-(m * β)) := by
        rw [mul_assoc, ← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero, mul_one]
    _ ≤ 1 * (2 : ℝ) ^ (-(m * β)) := mul_le_mul_of_nonneg_right hsum2 (by positivity)
    _ = (2 : ℝ) ^ (-(m * β)) := one_mul _

theorem mem_dyadicIco_iff {m : ℕ} {k : ℤ} {x : ℝ} : x ∈ dyadicIco m k ↔ ⌊x * 2 ^ m⌋ = k := by
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  rw [dyadicIco, Set.mem_Ico, Int.floor_eq_iff, div_le_iff₀ h2, lt_div_iff₀ h2]

theorem measurableSet_dyadicIco (m : ℕ) (k : ℤ) : MeasurableSet (dyadicIco m k) :=
  measurableSet_Ico

theorem pairwise_disjoint_dyadicIco (m : ℕ) : Pairwise (Function.onFun Disjoint (dyadicIco m)) := by
  intro k l hkl
  rw [Function.onFun, Set.disjoint_left]
  intro x hk hl
  rw [mem_dyadicIco_iff] at hk hl
  exact hkl (hk.symm.trans hl)

theorem iUnion_dyadicIco (m : ℕ) : (⋃ k, dyadicIco m k) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨_, mem_dyadicIco_iff.mpr rfl⟩

theorem summable_measureReal_dyadicIco (ν : Measure ℝ) [IsFiniteMeasure ν] (m : ℕ) :
    Summable fun k => ν.real (dyadicIco m k) := by
  have h := measure_iUnion (μ := ν) (pairwise_disjoint_dyadicIco m) (measurableSet_dyadicIco m)
  rw [iUnion_dyadicIco] at h
  exact ENNReal.summable_toReal (h ▸ measure_ne_top ν _)

theorem tsum_measureReal_dyadicIco (ν : Measure ℝ) [IsFiniteMeasure ν] (m : ℕ) :
    ∑' k, ν.real (dyadicIco m k) = ν.real Set.univ := by
  have h := measure_iUnion (μ := ν) (pairwise_disjoint_dyadicIco m) (measurableSet_dyadicIco m)
  rw [iUnion_dyadicIco] at h
  rw [measureReal_def, h, ENNReal.tsum_toReal_eq (fun k => measure_ne_top ν _)]
  rfl

theorem measureReal_dyadicIco_rpow_le (ν : Measure ℝ) [IsFiniteMeasure ν] {q : ℝ} (hq : 1 ≤ q)
    (m : ℕ) (k : ℤ) :
    ν.real (dyadicIco m k) ^ q ≤ ν.real Set.univ ^ (q - 1) * ν.real (dyadicIco m k) := by
  have h0 : 0 ≤ ν.real (dyadicIco m k) := measureReal_nonneg
  have h1 : ν.real (dyadicIco m k) ≤ ν.real Set.univ := measureReal_mono (Set.subset_univ _)
  calc ν.real (dyadicIco m k) ^ q = ν.real (dyadicIco m k) ^ (q - 1) * ν.real (dyadicIco m k) := by
        rw [← Real.rpow_add_one' h0 (by linarith)]; ring_nf
    _ ≤ ν.real Set.univ ^ (q - 1) * ν.real (dyadicIco m k) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow h0 h1 (by linarith)) h0

theorem summable_lq (ν : Measure ℝ) [IsFiniteMeasure ν] {q : ℝ} (hq : 1 ≤ q) (m : ℕ) :
    Summable fun k => ν.real (dyadicIco m k) ^ q :=
  Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg measureReal_nonneg _)
    (measureReal_dyadicIco_rpow_le ν hq m)
    ((summable_measureReal_dyadicIco ν m).mul_left _)

theorem lqSum_nonneg (ν : Measure ℝ) (q : ℝ) (m : ℕ) : 0 ≤ lqSum ν q m :=
  tsum_nonneg fun _ => Real.rpow_nonneg measureReal_nonneg _

theorem sum_le_lqSum (ν : Measure ℝ) [IsFiniteMeasure ν] {q : ℝ} (hq : 1 ≤ q) (m : ℕ)
    (s : Finset ℤ) : ∑ k ∈ s, ν.real (dyadicIco m k) ^ q ≤ lqSum ν q m :=
  (summable_lq ν hq m).sum_le_tsum s fun _ _ => Real.rpow_nonneg measureReal_nonneg _

theorem lqSum_le (ν : Measure ℝ) [IsFiniteMeasure ν] {q : ℝ} (hq : 1 ≤ q) (m : ℕ) :
    lqSum ν q m ≤ ν.real Set.univ ^ q := by
  calc lqSum ν q m ≤ ∑' k, ν.real Set.univ ^ (q - 1) * ν.real (dyadicIco m k) :=
        (summable_lq ν hq m).tsum_le_tsum (measureReal_dyadicIco_rpow_le ν hq m)
          ((summable_measureReal_dyadicIco ν m).mul_left _)
    _ = ν.real Set.univ ^ q := by
        rw [tsum_mul_left, tsum_measureReal_dyadicIco,
          ← Real.rpow_add_one' measureReal_nonneg (by linarith)]
        ring_nf

theorem lqSum_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν] {q : ℝ} (hq : 1 ≤ q) (m : ℕ) :
    lqSum ν q m ≤ 1 := by
  have := lqSum_le ν hq m
  simpa using this

theorem lqSum_anti (ν : Measure ℝ) [IsProbabilityMeasure ν] {q₁ q₂ : ℝ} (hq₁ : 1 ≤ q₁)
    (hq : q₁ ≤ q₂) (m : ℕ) : lqSum ν q₂ m ≤ lqSum ν q₁ m := by
  refine (summable_lq ν (hq₁.trans hq) m).tsum_le_tsum (fun k => ?_) (summable_lq ν hq₁ m)
  have h0 : 0 ≤ ν.real (dyadicIco m k) := measureReal_nonneg
  have h1 : ν.real (dyadicIco m k) ≤ 1 := measureReal_le_one
  rcases h0.lt_or_eq with h0 | h0
  · exact Real.rpow_le_rpow_of_exponent_ge h0 h1 hq
  · rw [← h0, Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]

noncomputable def dyadicCover (L : ℝ) (m : ℕ) : Finset ℤ := Finset.Icc ⌊-L * 2 ^ m⌋ ⌊L * 2 ^ m⌋

theorem measureReal_dyadicIco_eq_zero {ν : Measure ℝ} {L : ℝ} (hL : ν (Set.Icc (-L) L)ᶜ = 0)
    {m : ℕ} {k : ℤ} (hk : k ∉ dyadicCover L m) : ν.real (dyadicIco m k) = 0 := by
  rw [measureReal_def, ENNReal.toReal_eq_zero_iff]
  left
  refine measure_mono_null (show dyadicIco m k ⊆ (Set.Icc (-L) L)ᶜ from
    fun x hx hxL => hk ?_) hL
  rw [mem_dyadicIco_iff] at hx
  rw [dyadicCover, Finset.mem_Icc, ← hx]
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  exact ⟨Int.floor_le_floor (mul_le_mul_of_nonneg_right hxL.1 h2.le),
    Int.floor_le_floor (mul_le_mul_of_nonneg_right hxL.2 h2.le)⟩

theorem card_dyadicCover_le {L : ℝ} (hL : 0 ≤ L) (m : ℕ) :
    ((dyadicCover L m).card : ℝ) ≤ (2 * L + 2) * 2 ^ m := by
  have h2 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have h3 := Int.floor_le (L * 2 ^ m)
  have h4 := Int.lt_floor_add_one (-L * 2 ^ m)
  have hle : ⌊-L * 2 ^ m⌋ ≤ ⌊L * 2 ^ m⌋ := Int.floor_le_floor (by nlinarith)
  have h5 : ((dyadicCover L m).card : ℤ) = ⌊L * 2 ^ m⌋ + 1 - ⌊-L * 2 ^ m⌋ := by
    rw [dyadicCover, Int.card_Icc, Int.toNat_of_nonneg (by omega)]
  have h6 : ((dyadicCover L m).card : ℝ) = ((⌊L * 2 ^ m⌋ + 1 - ⌊-L * 2 ^ m⌋ : ℤ) : ℝ) := by
    rw [← h5]; norm_cast
  rw [h6]
  push_cast
  nlinarith

theorem sum_dyadicCover_measureReal {ν : Measure ℝ} [IsProbabilityMeasure ν] {L : ℝ}
    (hL : ν (Set.Icc (-L) L)ᶜ = 0) (m : ℕ) :
    ∑ k ∈ dyadicCover L m, ν.real (dyadicIco m k) = 1 := by
  have h := tsum_measureReal_dyadicIco ν m
  rw [tsum_eq_sum (s := dyadicCover L m) (fun k hk => measureReal_dyadicIco_eq_zero hL hk)] at h
  simpa using h

theorem lqSum_eq_sum_dyadicCover {ν : Measure ℝ} {L : ℝ} (hL : ν (Set.Icc (-L) L)ᶜ = 0)
    {q : ℝ} (hq : 0 < q) (m : ℕ) :
    lqSum ν q m = ∑ k ∈ dyadicCover L m, ν.real (dyadicIco m k) ^ q := by
  unfold lqSum
  refine tsum_eq_sum fun k hk => ?_
  rw [measureReal_dyadicIco_eq_zero hL hk, Real.zero_rpow hq.ne']

theorem lqSum_ge {ν : Measure ℝ} [IsProbabilityMeasure ν] {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ν (Set.Icc (-L) L)ᶜ = 0) {q : ℝ} (hq : 1 ≤ q) (m : ℕ) :
    ((2 * L + 2) * 2 ^ m) ^ (1 - q) ≤ lqSum ν q m := by
  rw [lqSum_eq_sum_dyadicCover hL (by linarith)]
  set K := dyadicCover L m
  have h := Real.rpow_sum_le_const_mul_sum_rpow K (fun k => ν.real (dyadicIco m k)) hq
  simp only [abs_of_nonneg measureReal_nonneg] at h
  have hsum := sum_dyadicCover_measureReal hL m
  rw [hsum, Real.one_rpow] at h
  have hne : K.Nonempty := Finset.nonempty_of_sum_ne_zero (by rw [hsum]; norm_num)
  have hK : (0 : ℝ) < K.card := by exact_mod_cast hne.card_pos
  have hK2 := card_dyadicCover_le hL0 m
  calc ((2 * L + 2) * 2 ^ m) ^ (1 - q) ≤ (K.card : ℝ) ^ (1 - q) :=
        Real.rpow_le_rpow_of_nonpos hK hK2 (by linarith)
    _ ≤ ∑ k ∈ K, ν.real (dyadicIco m k) ^ q := by
        rw [show 1 - q = -(q - 1) by ring, Real.rpow_neg hK.le, inv_eq_one_div,
          div_le_iff₀ (Real.rpow_pos_of_pos hK _)]
        linarith [mul_comm ((K.card : ℝ) ^ (q - 1)) (∑ k ∈ K, ν.real (dyadicIco m k) ^ q)]

noncomputable def lqExponent (ν : Measure ℝ) (q : ℝ) (m : ℕ) : ℝ :=
  -Real.logb 2 (lqSum ν q m) / m

theorem lqSpectrum_eq (ν : Measure ℝ) (q : ℝ) :
    lqSpectrum ν q = Filter.liminf (lqExponent ν q) Filter.atTop := rfl

section Spectrum

variable {ν : Measure ℝ} [IsProbabilityMeasure ν] {L : ℝ} (hL0 : 0 ≤ L)
  (hL : ν (Set.Icc (-L) L)ᶜ = 0) {q : ℝ} (hq : 1 ≤ q)

include hL0 hL hq

theorem lqSum_pos (m : ℕ) : 0 < lqSum ν q m :=
  lt_of_lt_of_le (Real.rpow_pos_of_pos (by positivity) _) (lqSum_ge hL0 hL hq m)

omit hL0 hL in

theorem lqExponent_nonneg (m : ℕ) : 0 ≤ lqExponent ν q m := by
  unfold lqExponent
  have h := Real.logb_nonpos (b := 2) (by norm_num) (lqSum_nonneg ν q m) (lqSum_le_one ν hq m)
  exact div_nonneg (by linarith) (Nat.cast_nonneg m)

theorem lqExponent_le (m : ℕ) :
    lqExponent ν q m ≤ (q - 1) * (Real.logb 2 (2 * L + 2) + 1) := by
  unfold lqExponent
  have hlog : 1 ≤ Real.logb 2 (2 * L + 2) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    norm_num
    linarith
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [CharP.cast_eq_zero, div_zero]
    nlinarith
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hS := lqSum_ge hL0 hL hq m
  have hpos : (0 : ℝ) < (2 * L + 2) * 2 ^ m := by positivity
  have h1 : (1 - q) * (Real.logb 2 (2 * L + 2) + m) ≤ Real.logb 2 (lqSum ν q m) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (lqSum_pos hL0 hL hq m)]
    convert hS using 1
    rw [mul_comm, Real.rpow_mul (by norm_num)]
    congr 1
    rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by linarith),
      Real.rpow_natCast]
  rw [div_le_iff₀ (by positivity)]
  have := mul_nonneg (mul_nonneg (sub_nonneg.mpr hq) (le_trans zero_le_one hlog))
    (sub_nonneg.mpr hm')
  nlinarith

omit hL0 hL in

theorem isBoundedUnder_ge_lqExponent :
    IsBoundedUnder (· ≥ ·) atTop (lqExponent ν q) :=
  isBoundedUnder_of_eventually_ge (Eventually.of_forall (lqExponent_nonneg hq))

theorem isBoundedUnder_le_lqExponent :
    IsBoundedUnder (· ≤ ·) atTop (lqExponent ν q) :=
  isBoundedUnder_of_eventually_le (Eventually.of_forall (lqExponent_le hL0 hL hq))

theorem lqSpectrum_nonneg : 0 ≤ lqSpectrum ν q :=
  le_liminf_of_le (isBoundedUnder_le_lqExponent hL0 hL hq).isCoboundedUnder_flip
    (Eventually.of_forall (lqExponent_nonneg hq))

theorem eventually_lqSum_le {b : ℝ} (hb : b < lqSpectrum ν q) :
    ∀ᶠ m : ℕ in atTop, lqSum ν q m ≤ (2 : ℝ) ^ (-(b * m)) := by
  have h := eventually_lt_of_lt_liminf hb (isBoundedUnder_ge_lqExponent hq)
  filter_upwards [h, eventually_ge_atTop 1] with m hm hm1
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm1
  rw [lt_div_iff₀ hm'] at hm
  have : Real.logb 2 (lqSum ν q m) < -(b * m) := by linarith
  exact ((Real.logb_lt_iff_lt_rpow (by norm_num) (lqSum_pos hL0 hL hq m)).mp this).le

omit hq in

theorem lqSpectrum_mono {q₁ q₂ : ℝ} (hq₁ : 1 ≤ q₁) (hq : q₁ ≤ q₂) :
    lqSpectrum ν q₁ ≤ lqSpectrum ν q₂ := by
  refine liminf_le_liminf (Eventually.of_forall fun m => ?_)
    (isBoundedUnder_ge_lqExponent hq₁)
    (isBoundedUnder_le_lqExponent hL0 hL (hq₁.trans hq)).isCoboundedUnder_flip
  show -Real.logb 2 (lqSum ν q₁ m) / m ≤ -Real.logb 2 (lqSum ν q₂ m) / m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_le_div_iff_of_pos_right hm', neg_le_neg_iff]
  exact Real.logb_le_logb_of_le (by norm_num) (lqSum_pos hL0 hL (hq₁.trans hq) m)
    (lqSum_anti ν hq₁ hq m)

end Spectrum

theorem rpow_sum_eq_sum_rpow_of_card_le_one {ι : Type*} {s : Finset ι} (hs : s.card ≤ 1)
    (w : ι → ℝ) {q : ℝ} (hq : q ≠ 0) : (∑ i ∈ s, w i) ^ q = ∑ i ∈ s, w i ^ q := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · simp [Real.zero_rpow hq]
  · have : s = {i} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hi, fun j hj => Finset.card_le_one.mp hs j hj i hi⟩
    simp [this]

theorem sum_image_rpow_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ℤ) (h : ι → ℝ)
    (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) {q : ℝ} (hq : 1 ≤ q)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, g i = g j → h i = h j → i = j) :
    ∑ k ∈ s.image g, (∑ i ∈ s with g i = k, w i) ^ q ≤
      ((s.image h).card : ℝ) ^ (q - 1) * ∑ i ∈ s, w i ^ q := by
  set Λ := s.image h
  have hfib : ∀ k, ∑ i ∈ s with g i = k, w i =
      ∑ l ∈ Λ, ∑ i ∈ (s.filter fun i => g i = k).filter (fun i => h i = l), w i := by
    intro k
    rw [Finset.sum_fiberwise_of_maps_to]
    intro i hi
    exact Finset.mem_image_of_mem h (Finset.mem_filter.mp hi).1
  have hone : ∀ k l, ((s.filter fun i => g i = k).filter (fun i => h i = l)).card ≤ 1 := by
    intro k l
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    exact hinj a ha.1.1 b hb.1.1 (ha.1.2.trans hb.1.2.symm) (ha.2.trans hb.2.symm)
  calc ∑ k ∈ s.image g, (∑ i ∈ s with g i = k, w i) ^ q
      ≤ ∑ k ∈ s.image g, (Λ.card : ℝ) ^ (q - 1) *
          ∑ l ∈ Λ, (∑ i ∈ (s.filter fun i => g i = k).filter (fun i => h i = l), w i) ^ q := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [hfib k]
        have := Real.rpow_sum_le_const_mul_sum_rpow Λ
          (fun l => ∑ i ∈ (s.filter fun i => g i = k).filter (fun i => h i = l), w i) hq
        have hnn : ∀ l, 0 ≤ ∑ i ∈ (s.filter fun i => g i = k).filter (fun i => h i = l), w i :=
          fun l => Finset.sum_nonneg fun i hi =>
            hw i (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
        simpa only [abs_of_nonneg (hnn _)] using this
    _ = (Λ.card : ℝ) ^ (q - 1) * ∑ k ∈ s.image g,
          ∑ l ∈ Λ, ∑ i ∈ (s.filter fun i => g i = k).filter (fun i => h i = l), w i ^ q := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        exact rpow_sum_eq_sum_rpow_of_card_le_one (hone k l) w (by linarith)
    _ = (Λ.card : ℝ) ^ (q - 1) * ∑ i ∈ s, w i ^ q := by
        congr 1
        rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image g) (g := g)
          (fun i hi => Finset.mem_image_of_mem g hi)]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_fiberwise_of_maps_to]
        intro i hi
        exact Finset.mem_image_of_mem h (Finset.mem_filter.mp hi).1

theorem measureReal_sum_dirac {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (x : ι → ℝ) {A : Set ℝ} (hA : MeasurableSet A) [DecidablePred (· ∈ A)] :
    (∑ i ∈ s, ENNReal.ofReal (w i) • Measure.dirac (x i)).real A =
      ∑ i ∈ s with x i ∈ A, w i := by
  rw [measureReal_def, Measure.finsetSum_apply, ENNReal.toReal_sum, Finset.sum_filter]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]
    by_cases hx : x i ∈ A
    · simp [hx, hw i hi]
    · simp [hx]
  · intro i _
    rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (by by_cases hx : x i ∈ A <;> simp [hx])

theorem lqSum_sum_dirac {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (x : ι → ℝ) {q : ℝ} (hq : 0 < q) (n : ℕ) :
    lqSum (∑ i ∈ s, ENNReal.ofReal (w i) • Measure.dirac (x i)) q n =
      ∑ k ∈ s.image (fun i => ⌊x i * 2 ^ n⌋),
        (∑ i ∈ s with ⌊x i * 2 ^ n⌋ = k, w i) ^ q := by
  classical
  have hcell : ∀ k, (∑ i ∈ s, ENNReal.ofReal (w i) • Measure.dirac (x i)).real
      (dyadicIco n k) = ∑ i ∈ s with ⌊x i * 2 ^ n⌋ = k, w i := by
    intro k
    rw [measureReal_sum_dirac s w hw x (measurableSet_dyadicIco n k)]
    congr 1
    ext i
    simp [mem_dyadicIco_iff]
  unfold lqSum
  simp_rw [hcell]
  refine tsum_eq_sum fun k hk => ?_
  have : (s.filter fun i => ⌊x i * 2 ^ n⌋ = k) = ∅ := by
    ext i
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
    intro hi hik
    exact hk (Finset.mem_image.mpr ⟨i, hi, hik⟩)
  rw [this, Finset.sum_empty, Real.zero_rpow hq.ne']

variable [Fintype κ]

noncomputable def stoppedMeasure (r t p : κ → ℝ) (m : ℕ) : Measure ℝ :=
  ∑ u ∈ omega r m, ENNReal.ofReal (wordWeight p u) • Measure.dirac (simWord r t u 0)

theorem lqSum_stoppedMeasure_le {r t p : κ → ℝ} (hr1 : ∀ j, |r j| < 1) (hp : ∀ j, 0 < p j)
    {m n : ℕ} {R : ℝ}
    (hsep : ∀ u v : List κ, u ≠ v → ShmerkinStopping r m u → ShmerkinStopping r m v →
      (u.map r).prod = (v.map r).prod →
      (2 : ℝ) ^ (-(R * m)) ≤ |simWord r t u 0 - simWord r t v 0|)
    (hn : R * m ≤ n) {q : ℝ} (hq : 1 ≤ q) :
    lqSum (stoppedMeasure r t p m) q n ≤
      ((ratioSet r m).card : ℝ) ^ (q - 1) * ∑ u ∈ omega r m, wordWeight p u ^ q := by
  classical
  unfold stoppedMeasure
  rw [lqSum_sum_dirac _ _ (fun u _ => (wordWeight_pos hp u).le) _ (by linarith)]
  have hR : ratioSet r m = (omega r m).image (wordRatio r) := by
    unfold ratioSet; congr
  rw [hR]
  refine sum_image_rpow_le _ _ _ _ (fun u _ => (wordWeight_pos hp u).le) hq ?_
  intro u hu v hv hfl hrat
  by_contra hne
  have h1 := hsep u v hne ((mem_omega hr1).mp hu) ((mem_omega hr1).mp hv) hrat
  have h2 := Int.abs_sub_lt_one_of_floor_eq_floor hfl
  rw [← sub_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n)] at h2
  have h3 : (2 : ℝ) ^ (-(n : ℝ)) ≤ (2 : ℝ) ^ (-(R * m)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h4 : |simWord r t u 0 - simWord r t v 0| < (2 : ℝ) ^ (-(n : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, ← one_div,
      lt_div_iff₀ (by positivity)]
    exact h2
  linarith

omit [Fintype κ] in

theorem simWord_eq_affine (r t : κ → ℝ) (u : List κ) :
    simWord r t u = fun x => wordRatio r u * x + simWord r t u 0 :=
  funext fun x => simWord_apply r t u x

omit [Fintype κ] in

theorem measurable_simWord (r t : κ → ℝ) (u : List κ) : Measurable (simWord r t u) := by
  rw [simWord_eq_affine]
  fun_prop

structure IsSelfSimilar (r t p : κ → ℝ) (μ : Measure ℝ) : Prop where
  ratio_ne_zero : ∀ j, r j ≠ 0
  abs_ratio_lt_one : ∀ j, |r j| < 1
  weight_pos : ∀ j, 0 < p j
  weight_sum : ∑ j, p j = 1
  isProbabilityMeasure : IsProbabilityMeasure μ
  stationary : μ = ∑ j, ENNReal.ofReal (p j) • μ.map (fun x => r j * x + t j)

namespace IsSelfSimilar

variable {r t p : κ → ℝ} {μ : Measure ℝ}

noncomputable def toSystem (h : IsSelfSimilar r t p μ) : ExactOverlaps.SelfSimilar.System κ where
  map j := ⟨r j, h.ratio_ne_zero j, t j⟩
  contracting j := h.abs_ratio_lt_one j
  weight j := (p j).toNNReal
  weight_sum := by
    rw [← NNReal.coe_inj, NNReal.coe_sum]
    simp only [Real.coe_toNNReal _ (h.weight_pos _).le, NNReal.coe_one]
    exact h.weight_sum

theorem exists_support (h : IsSelfSimilar r t p μ) :
    ∃ L : ℝ, 0 ≤ L ∧ μ (Set.Icc (-L) L)ᶜ = 0 := by
  have := h.isProbabilityMeasure
  obtain ⟨R, hR, hμ⟩ := h.toSystem.exists_closedBall_full_measure (ν := μ) h.stationary
  refine ⟨R, hR.le, ?_⟩
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hμ
  exact hμ

theorem eq_sum_omega (h : IsSelfSimilar r t p μ) {m : ℕ} (hm : 1 ≤ m) :
    μ = ∑ u ∈ omega r m, ENNReal.ofReal (wordWeight p u) • μ.map (simWord r t u) := by
  set F : List κ → Measure ℝ := fun u => ENNReal.ofReal (wordWeight p u) • μ.map (simWord r t u)
  have hF : ∀ v, F v = ∑ j, F (v ++ [j]) := by
    intro v
    have hv := measurable_simWord r t v
    have hj : ∀ j, simWord r t [j] = fun x => r j * x + t j := fun j => by
      funext x; simp
    have e1 : ∀ j, F (v ++ [j]) = ENNReal.ofReal (wordWeight p v) •
        (ENNReal.ofReal (p j) • μ.map (fun x => r j * x + t j)).map (simWord r t v) := by
      intro j
      simp only [F, wordWeight_append]
      rw [Measure.map_smul _ hv.aemeasurable, Measure.map_map hv (by fun_prop), smul_smul,
        ← ENNReal.ofReal_mul (wordWeight_pos h.weight_pos v).le, simWord_append, hj]
      simp [wordWeight]
    simp_rw [e1, ← Finset.smul_sum]
    simp only [F]
    congr 1
    conv_lhs => rw [h.stationary]
    rw [← Measure.mapₗ_apply_of_measurable hv, map_sum]
    simp only [Measure.mapₗ_apply_of_measurable hv]
  have := sum_omega_eq h.abs_ratio_lt_one F hF hm
  simpa [F] using this.symm

end IsSelfSimilar

end Lq

end FractalGeometry
