import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Pressure.ParityShift.PeriodicWords
import FractalGeometry.Pressure.ParityShift.SymbolicMetric
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.OrientationCoding
import FractalGeometry.Symbolic.ParityShift
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology Set

section Holder

variable {ι : Type*} {o : ι → ZMod 2} {f : (ℤ → ι × ZMod 2) → ℝ}

def IsHolderPotential (o : ι → ZMod 2) (f : (ℤ → ι × ZMod 2) → ℝ) : Prop :=
  ∃ K α : ℝ, 0 ≤ K ∧ 0 < α ∧ ∀ y ∈ subshift o, ∀ z ∈ subshift o,
    |f y - f z| ≤ K * symDist y z ^ α

theorem IsHolderPotential.exists_abs_sub_le_pow (hf : IsHolderPotential o f) :
    ∃ K θ : ℝ, 0 ≤ K ∧ 0 < θ ∧ θ < 1 ∧ ∀ y ∈ subshift o, ∀ z ∈ subshift o, ∀ k : ℕ,
      (∀ i : ℤ, i.natAbs ≤ k → z i = y i) → |f y - f z| ≤ K * θ ^ k := by
  obtain ⟨K, α, hK, hα, h⟩ := hf
  refine ⟨K, (1 / 2 : ℝ) ^ α, hK, by positivity,
    Real.rpow_lt_one (by norm_num) (by norm_num) hα, fun y hy z hz k hk => ?_⟩
  refine (h y hy z hz).trans (mul_le_mul_of_nonneg_left ?_ hK)
  have hd := (symDist_lt_pow_iff k).2 hk
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_natCast]
  exact Real.rpow_le_rpow (symDist_nonneg _ _) hd.le hα.le

structure HasBoundedDistortion (o : ι → ZMod 2) (f : (ℤ → ι × ZMod 2) → ℝ) (B D : ℝ) :
    Prop where
  abs_le_bound : ∀ z ∈ subshift o, |f z| ≤ B
  distortion : ∀ n : ℕ, ∀ y ∈ subshift o, ∀ z ∈ subshift o, (∀ k : ℕ, k < n → y k = z k) →
    |birkhoffSum (shift 1) f n y - birkhoffSum (shift 1) f n z| ≤ D

theorem pow_min_le_add {θ : ℝ} (h0 : 0 ≤ θ) (a b : ℕ) :
    θ ^ min a b ≤ θ ^ a + θ ^ b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    linarith [pow_nonneg h0 b]
  · rw [min_eq_right h]
    linarith [pow_nonneg h0 a]

theorem sum_pow_le_inv {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, θ ^ j ≤ (1 - θ)⁻¹ := by
  have hpos : 0 < 1 - θ := by linarith
  have hg := geom_sum_mul θ n
  rw [← one_div, le_div_iff₀ hpos]
  nlinarith [pow_nonneg h0 n]

theorem IsHolderPotential.exists_hasBoundedDistortion [Nonempty ι] (hf : IsHolderPotential o f) :
    ∃ B D : ℝ, 0 ≤ B ∧ 0 ≤ D ∧ HasBoundedDistortion o f B D := by
  obtain ⟨K, θ, hK, hθ0, hθ1, hvar⟩ := hf.exists_abs_sub_le_pow
  obtain ⟨K', α, hK', hα, hhol⟩ := hf
  obtain ⟨i⟩ := ‹Nonempty ι›
  set y₀ : ℤ → ι × ZMod 2 := tau o fun _ => i
  have hy₀ : y₀ ∈ subshift o := tau_mem_subshift _
  have hB0 : 0 ≤ |f y₀| + K' := add_nonneg (abs_nonneg _) hK'
  have hD0 : 0 ≤ 2 * K * (1 - θ)⁻¹ :=
    mul_nonneg (mul_nonneg zero_le_two hK) (inv_nonneg.2 (by linarith))
  refine ⟨|f y₀| + K', 2 * K * (1 - θ)⁻¹, hB0, hD0, ⟨?_, ?_⟩⟩
  · intro z hz
    have h1 := hhol z hz y₀ hy₀
    have h2 : symDist z y₀ ^ α ≤ 1 :=
      Real.rpow_le_one (symDist_nonneg _ _) (symDist_le_one _ _) hα.le
    have h3 : |f z| ≤ |f y₀| + |f z - f y₀| := by
      have := abs_add_le (f y₀) (f z - f y₀)
      simpa using this
    nlinarith [mul_le_mul_of_nonneg_left h2 hK']
  · intro n y hy z hz hyz
    unfold birkhoffSum
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ j : ℕ, j ∈ Finset.range n →
        abs (f ((shift (1 : ℤ))^[j] y) - f ((shift (1 : ℤ))^[j] z)) ≤
          K * (θ ^ j + θ ^ (n - 1 - j)) := by
      intro j hj
      have hj' := Finset.mem_range.1 hj
      rw [iterate_shift_one]
      refine (hvar _ (shift_mem_subshift o hy _) _ (shift_mem_subshift o hz _)
        (min j (n - 1 - j)) fun i hi => ?_).trans ?_
      · simp only [shift_apply]
        have h0 : 0 ≤ (j : ℤ) + i := by omega
        have h1 : ((j : ℤ) + i).toNat < n := by omega
        have := hyz ((j : ℤ) + i).toNat h1
        rw [Int.toNat_of_nonneg h0] at this
        exact this.symm
      · exact mul_le_mul_of_nonneg_left (pow_min_le_add hθ0.le _ _) hK
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    have hrefl : ∑ j ∈ Finset.range n, θ ^ (n - 1 - j) = ∑ j ∈ Finset.range n, θ ^ j :=
      Finset.sum_range_reflect (fun j => θ ^ j) n
    rw [hrefl]
    have hs := sum_pow_le_inv hθ0.le hθ1 n
    nlinarith

end Holder

section Sums

variable {ι : Type*} [Fintype ι] {o : ι → ZMod 2} {f : (ℤ → ι × ZMod 2) → ℝ} {B D : ℝ}

variable (o f) in

noncomputable def cylSup (n : ℕ) (w : Fin n → ι × ZMod 2) : ℝ :=
  sSup ((birkhoffSum (shift 1) f n) '' (cylinder w ∩ subshift o))

omit [Fintype ι] in

theorem exists_mem_cylinder_of_isAdmissible [Nonempty ι] {n : ℕ} {w : Fin n → ι × ZMod 2}
    (hw : IsAdmissible o w) : ∃ y ∈ subshift o, y ∈ cylinder w := by
  rcases n with _ | n
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨tau o fun _ => i, tau_mem_subshift _, fun k => k.elim0⟩
  · obtain ⟨y, hy, hyw⟩ := hw.exists_block_eq
    exact ⟨y, hy, fun k => by rw [← hyw]; rfl⟩

omit [Fintype ι] in

theorem HasBoundedDistortion.abs_birkhoffSum_le (h : HasBoundedDistortion o f B D) (n : ℕ)
    {y : ℤ → ι × ZMod 2} (hy : y ∈ subshift o) : |birkhoffSum (shift 1) f n y| ≤ n * B := by
  unfold birkhoffSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ j ∈ Finset.range n, abs (f ((shift 1)^[j] y)) ≤ B := fun j _ => by
    rw [iterate_shift_one]
    exact h.abs_le_bound _ (shift_mem_subshift o hy _)
  refine (Finset.sum_le_sum this).trans ?_
  simp

omit [Fintype ι] in

theorem HasBoundedDistortion.cylSup_bounds (h : HasBoundedDistortion o f B D) {n : ℕ}
    {w : Fin n → ι × ZMod 2} {y : ℤ → ι × ZMod 2} (hy : y ∈ subshift o)
    (hyw : y ∈ cylinder w) :
    birkhoffSum (shift 1) f n y ≤ cylSup o f n w ∧
      cylSup o f n w ≤ birkhoffSum (shift 1) f n y + D := by
  have hle : ∀ t ∈ (birkhoffSum (shift 1) f n) '' (cylinder w ∩ subshift o),
      t ≤ birkhoffSum (shift 1) f n y + D := by
    rintro _ ⟨z, ⟨hzw, hz⟩, rfl⟩
    have hyz : ∀ k : ℕ, k < n → y k = z k := fun k hk =>
      (hyw ⟨k, hk⟩).trans (hzw ⟨k, hk⟩).symm
    have := h.distortion n y hy z hz hyz
    have := (abs_le.1 this).1
    linarith
  have hne : ((birkhoffSum (shift 1) f n) '' (cylinder w ∩ subshift o)).Nonempty :=
    ⟨_, y, ⟨hyw, hy⟩, rfl⟩
  exact ⟨le_csSup ⟨_, hle⟩ ⟨y, ⟨hyw, hy⟩, rfl⟩, csSup_le hne hle⟩

variable (o f) in

open Classical in

noncomputable def admissibleSumPot (n : ℕ) : ℝ :=
  ∑ w : Fin n → ι × ZMod 2, if IsAdmissible o w then Real.exp (cylSup o f n w) else 0

variable (o f) in

open Classical in

noncomputable def periodicSumPot (n : ℕ) : ℝ :=
  ∑ w : Fin n → ι × ZMod 2, if IsCyclicAdmissible o w then Real.exp (cylSup o f n w) else 0

variable (o f) in

noncomputable def pressureZPot : ℝ :=
  limUnder atTop fun n : ℕ => Real.log (periodicSumPot o f n) / n

variable (o f) in

theorem periodicSumPot_le_admissibleSumPot (n : ℕ) :
    periodicSumPot o f n ≤ admissibleSumPot o f n := by
  classical
  refine Finset.sum_le_sum fun w _ => ?_
  by_cases h : IsCyclicAdmissible o w
  · rw [ite_eq_left h, ite_eq_left h.isAdmissible]
  · rw [ite_eq_right h]
    positivity

theorem HasBoundedDistortion.admissibleSumPot_add_le [Nonempty ι]
    (h : HasBoundedDistortion o f B D) (m n : ℕ) :
    admissibleSumPot o f (m + n) ≤ admissibleSumPot o f m * admissibleSumPot o f n := by
  classical
  have hbdd : ∀ (k : ℕ) (w : Fin k → ι × ZMod 2),
      BddAbove ((birkhoffSum (shift 1) f k) '' (cylinder w ∩ subshift o)) := by
    intro k w
    refine ⟨k * B, ?_⟩
    rintro _ ⟨z, ⟨-, hz⟩, rfl⟩
    exact (le_abs_self _).trans (h.abs_birkhoffSum_le k hz)
  have key : ∀ (u : Fin m → ι × ZMod 2) (v : Fin n → ι × ZMod 2),
      IsAdmissible o (Fin.append u v) →
        cylSup o f (m + n) (Fin.append u v) ≤ cylSup o f m u + cylSup o f n v := by
    intro u v huv
    obtain ⟨y, hy, hyuv⟩ := exists_mem_cylinder_of_isAdmissible huv
    refine csSup_le ⟨_, y, ⟨hyuv, hy⟩, rfl⟩ ?_
    rintro _ ⟨z, ⟨hz, hzs⟩, rfl⟩
    rw [cylinder_append] at hz
    rw [birkhoffSum_add_right_apply, iterate_shift_one]
    exact add_le_add (le_csSup (hbdd m u) ⟨z, ⟨hz.1, hzs⟩, rfl⟩)
      (le_csSup (hbdd n v) ⟨shift m z, ⟨hz.2, shift_mem_subshift o hzs _⟩, rfl⟩)
  calc admissibleSumPot o f (m + n)
      = ∑ p : (Fin m → ι × ZMod 2) × (Fin n → ι × ZMod 2),
          if IsAdmissible o (Fin.append p.1 p.2) then
            Real.exp (cylSup o f (m + n) (Fin.append p.1 p.2)) else 0 :=
        (Fintype.sum_equiv (Fin.appendEquiv m n) _ _ fun p => rfl).symm
    _ = ∑ u : Fin m → ι × ZMod 2, ∑ v : Fin n → ι × ZMod 2,
          if IsAdmissible o (Fin.append u v) then
            Real.exp (cylSup o f (m + n) (Fin.append u v)) else 0 := Fintype.sum_prod_type _
    _ ≤ admissibleSumPot o f m * admissibleSumPot o f n := by
        rw [admissibleSumPot, admissibleSumPot, Finset.sum_mul_sum]
        refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
        by_cases huv : IsAdmissible o (Fin.append u v)
        · obtain ⟨hu, hv⟩ := huv.of_append
          rw [ite_eq_left huv, ite_eq_left hu, ite_eq_left hv, ← Real.exp_add]
          exact Real.exp_le_exp.2 (key u v huv)
        · rw [ite_eq_right huv]
          positivity

theorem HasBoundedDistortion.exp_le_admissibleSumPot [Nonempty ι]
    (h : HasBoundedDistortion o f B D) (n : ℕ) :
    Real.exp (-(n * B)) ≤ admissibleSumPot o f n := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  set y : ℤ → ι × ZMod 2 := tau o fun _ => i
  have hy : y ∈ subshift o := tau_mem_subshift _
  have hw := isAdmissible_block hy n
  have hyw : y ∈ cylinder (block n y) := fun _ => rfl
  have h1 : Real.exp (-(n * B)) ≤ Real.exp (cylSup o f n (block n y)) := by
    refine Real.exp_le_exp.2 ?_
    have := (abs_le.1 (h.abs_birkhoffSum_le n hy)).1
    linarith [(h.cylSup_bounds hy hyw).1]
  refine h1.trans ?_
  have h2 := Finset.single_le_sum (f := fun w : Fin n → ι × ZMod 2 =>
    if IsAdmissible o w then Real.exp (cylSup o f n w) else 0)
    (fun w _ => by positivity) (Finset.mem_univ (block n y))
  rwa [ite_eq_left hw] at h2

theorem HasBoundedDistortion.admissibleSumPot_pos [Nonempty ι]
    (h : HasBoundedDistortion o f B D) (n : ℕ) : 0 < admissibleSumPot o f n :=
  (Real.exp_pos _).trans_le (h.exp_le_admissibleSumPot n)

theorem HasBoundedDistortion.exp_mul_admissibleSumPot_le_periodicSumPot
    (h : HasBoundedDistortion o f B D) (h0 : ∃ i, o i = 0) (n : ℕ) :
    Real.exp (-(B + D)) * admissibleSumPot o f (n + 1) ≤ periodicSumPot o f (n + 2) := by
  classical
  have : Nonempty ι := ⟨h0.choose⟩
  set G : (Fin (n + 2) → ι × ZMod 2) → ℝ := fun v =>
    if IsCyclicAdmissible o v then Real.exp (cylSup o f (n + 2) v) else 0 with hG
  have hG0 : ∀ v, 0 ≤ G v := fun v => by rw [hG]; positivity
  calc Real.exp (-(B + D)) * admissibleSumPot o f (n + 1)
      = ∑ w : Fin (n + 1) → ι × ZMod 2,
          Real.exp (-(B + D)) * if IsAdmissible o w then Real.exp (cylSup o f (n + 1) w)
            else 0 := by
        rw [admissibleSumPot, Finset.mul_sum]
    _ ≤ ∑ w : Fin (n + 1) → ι × ZMod 2, ∑ r : ι × ZMod 2, G (Fin.cons r w) := by
        refine Finset.sum_le_sum fun w _ => ?_
        by_cases hw : IsAdmissible o w
        · obtain ⟨r, h1, h2⟩ := hw.exists_closing h0
          refine le_trans ?_ (Finset.single_le_sum (f := fun r : ι × ZMod 2 => G (Fin.cons r w))
            (fun r _ => hG0 _) (Finset.mem_univ r))
          have hcyc := IsCyclicAdmissible.cons hw h1 h2
          have hGc : G (Fin.cons r w) = Real.exp (cylSup o f (n + 2) (Fin.cons r w)) :=
            ite_eq_left hcyc
          rw [hGc, ite_eq_left hw, ← Real.exp_add]
          refine Real.exp_le_exp.2 ?_
          obtain ⟨z, hz, hzw⟩ := exists_mem_cylinder_of_isAdmissible hcyc.isAdmissible
          have hσz : shift 1 z ∈ cylinder w := by
            intro k
            have := hzw k.succ
            simp only [Fin.cons_succ] at this
            rw [shift_apply, ← this]
            congr 1
            simp [add_comm]
          have hσ := shift_mem_subshift o hz 1
          have hb1 := (h.cylSup_bounds hz hzw).1
          have hb2 := (h.cylSup_bounds hσ hσz).2
          rw [birkhoffSum_succ_apply'] at hb1
          have hfz := (abs_le.1 (h.abs_le_bound z hz)).1
          linarith
        · rw [ite_eq_right hw, mul_zero]
          exact Finset.sum_nonneg fun r _ => hG0 _
    _ = ∑ p : (ι × ZMod 2) × (Fin (n + 1) → ι × ZMod 2), G (Fin.cons p.1 p.2) :=
        (Fintype.sum_prod_type_right
          fun p : (ι × ZMod 2) × (Fin (n + 1) → ι × ZMod 2) => G (Fin.cons p.1 p.2)).symm
    _ = periodicSumPot o f (n + 2) :=
        Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (n + 2) => ι × ZMod 2) _ _ fun p => rfl

theorem HasBoundedDistortion.subadditive_log_admissibleSumPot [Nonempty ι]
    (h : HasBoundedDistortion o f B D) :
    Subadditive fun n => Real.log (admissibleSumPot o f n) := by
  intro m n
  rw [← Real.log_mul (h.admissibleSumPot_pos m).ne' (h.admissibleSumPot_pos n).ne']
  exact Real.log_le_log (h.admissibleSumPot_pos _) (h.admissibleSumPot_add_le m n)

theorem HasBoundedDistortion.bddBelow_log_admissibleSumPot_div [Nonempty ι]
    (h : HasBoundedDistortion o f B D) :
    BddBelow (Set.range fun n : ℕ => Real.log (admissibleSumPot o f n) / n) := by
  refine ⟨min 0 (-B), ?_⟩
  rintro _ ⟨n, rfl⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    refine (min_le_right _ _).trans ?_
    rw [le_div_iff₀ hn']
    have h1 := Real.log_le_log (Real.exp_pos _) (h.exp_le_admissibleSumPot n)
    rw [Real.log_exp] at h1
    linarith [mul_comm B (n : ℝ)]

theorem HasBoundedDistortion.tendsto_log_admissibleSumPot_div [Nonempty ι]
    (h : HasBoundedDistortion o f B D) :
    ∃ L, Tendsto (fun n : ℕ => Real.log (admissibleSumPot o f n) / n) atTop (𝓝 L) :=
  ⟨_, h.subadditive_log_admissibleSumPot.tendsto_lim h.bddBelow_log_admissibleSumPot_div⟩

theorem HasBoundedDistortion.tendsto_log_periodicSumPot_div (h : HasBoundedDistortion o f B D)
    (h0 : ∃ i, o i = 0) {L : ℝ}
    (hL : Tendsto (fun n : ℕ => Real.log (admissibleSumPot o f n) / n) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => Real.log (periodicSumPot o f n) / n) atTop (𝓝 L) := by
  have : Nonempty ι := ⟨h0.choose⟩
  set c : ℝ := Real.exp (-(B + D)) / admissibleSumPot o f 1
  have hc : 0 < c := div_pos (Real.exp_pos _) (h.admissibleSumPot_pos 1)
  have hle : ∀ n, 2 ≤ n → c * admissibleSumPot o f n ≤ periodicSumPot o f n := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have h1 := h.admissibleSumPot_pos (o := o) (f := f) 1
    have h2 : admissibleSumPot o f (k + 2) ≤
        admissibleSumPot o f 1 * admissibleSumPot o f (k + 1) := by
      have := h.admissibleSumPot_add_le 1 (k + 1)
      rwa [show 1 + (k + 1) = k + 2 by omega] at this
    calc c * admissibleSumPot o f (k + 2)
        ≤ c * (admissibleSumPot o f 1 * admissibleSumPot o f (k + 1)) :=
          mul_le_mul_of_nonneg_left h2 hc.le
      _ = Real.exp (-(B + D)) * admissibleSumPot o f (k + 1) := by
          simp only [c]
          field_simp
      _ ≤ periodicSumPot o f (k + 2) := h.exp_mul_admissibleSumPot_le_periodicSumPot h0 k
  have hlow : Tendsto (fun n : ℕ => Real.log c / n + Real.log (admissibleSumPot o f n) / n)
      atTop (𝓝 L) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (Real.log c)).add hL
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hL ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hA := h.admissibleSumPot_pos (o := o) (f := f) n
    have h1 := Real.log_le_log (mul_pos hc hA) (hle n hn)
    rw [Real.log_mul hc.ne' hA.ne'] at h1
    rw [← add_div]
    exact div_le_div_of_nonneg_right h1 (Nat.cast_nonneg n)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hP : 0 < periodicSumPot o f n :=
      (mul_pos hc (h.admissibleSumPot_pos n)).trans_le (hle n hn)
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hP (periodicSumPot_le_admissibleSumPot o f n)) (Nat.cast_nonneg n)

theorem HasBoundedDistortion.tendsto_pressureZPot (h : HasBoundedDistortion o f B D)
    (h0 : ∃ i, o i = 0) :
    Tendsto (fun n : ℕ => Real.log (periodicSumPot o f n) / n) atTop (𝓝 (pressureZPot o f)) := by
  have : Nonempty ι := ⟨h0.choose⟩
  obtain ⟨L, hL⟩ := h.tendsto_log_admissibleSumPot_div
  have h1 := h.tendsto_log_periodicSumPot_div h0 hL
  rwa [pressureZPot, h1.limUnder_eq]

theorem HasBoundedDistortion.tendsto_pressureZPot_admissibleSumPot
    (h : HasBoundedDistortion o f B D) (h0 : ∃ i, o i = 0) :
    Tendsto (fun n : ℕ => Real.log (admissibleSumPot o f n) / n) atTop
      (𝓝 (pressureZPot o f)) := by
  have : Nonempty ι := ⟨h0.choose⟩
  obtain ⟨L, hL⟩ := h.tendsto_log_admissibleSumPot_div
  rwa [tendsto_nhds_unique (h.tendsto_pressureZPot h0) (h.tendsto_log_periodicSumPot_div h0 hL)]

end Sums

section Gibbs

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {o : ι → ZMod 2} {f : (ℤ → ι × ZMod 2) → ℝ} {ν : Measure (ℤ → ι × ZMod 2)} {B D P C : ℝ}

theorem IsGibbsPotential.tendsto_log_admissibleSumPot [IsProbabilityMeasure ν]
    (hν : ν (subshift o)ᶜ = 0) (hg : IsGibbsPotential o f ν P C)
    (h : HasBoundedDistortion o f B D) :
    Tendsto (fun n : ℕ => Real.log (admissibleSumPot o f n) / n) atTop (𝓝 P) := by
  classical
  have : Nonempty ι := ⟨((nonempty_of_isProbabilityMeasure ν).some 0).1⟩
  obtain ⟨hC, hb⟩ := hg
  set c : ℝ := C⁻¹ * Real.exp (-D)
  have hc : 0 < c := mul_pos (inv_pos.2 hC) (Real.exp_pos _)
  have key : ∀ n : ℕ,
      c * (Real.exp (-((n + 1 : ℕ) * P)) * admissibleSumPot o f (n + 1)) ≤ 1 ∧
        1 ≤ C * (Real.exp (-((n + 1 : ℕ) * P)) * admissibleSumPot o f (n + 1)) := by
    intro n
    rw [← sum_measureReal_cylinder_of_isAdmissible hν (n + 1), admissibleSumPot, Finset.mul_sum,
      Finset.mul_sum, Finset.mul_sum]
    refine ⟨Finset.sum_le_sum fun w _ => ?_, Finset.sum_le_sum fun w _ => ?_⟩ <;>
      by_cases hw : IsAdmissible o w
    · obtain ⟨y, hy, rfl⟩ := hw.exists_block_eq
      rw [ite_eq_left hw, ite_eq_left hw]
      have hyw : y ∈ cylinder (block (n + 1) y) := fun _ => rfl
      have hsup := (h.cylSup_bounds hy hyw).2
      have hlow := (hb y hy (n + 1) (Nat.succ_pos n)).1
      calc c * (Real.exp (-((n + 1 : ℕ) * P)) *
            Real.exp (cylSup o f (n + 1) (block (n + 1) y)))
          ≤ C⁻¹ * Real.exp (-((n + 1 : ℕ) * P) + birkhoffSum (shift 1) f (n + 1) y) := by
            simp only [c]
            rw [mul_assoc, ← Real.exp_add, ← Real.exp_add]
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (inv_pos.2 hC).le
            linarith
        _ ≤ ν.real (cylinder (block (n + 1) y)) := hlow
    · rw [ite_eq_right hw, ite_eq_right hw]; simp
    · obtain ⟨y, hy, rfl⟩ := hw.exists_block_eq
      rw [ite_eq_left hw, ite_eq_left hw]
      have hyw : y ∈ cylinder (block (n + 1) y) := fun _ => rfl
      have hsup := (h.cylSup_bounds hy hyw).1
      have hupp := (hb y hy (n + 1) (Nat.succ_pos n)).2
      calc ν.real (cylinder (block (n + 1) y))
          ≤ C * Real.exp (-((n + 1 : ℕ) * P) + birkhoffSum (shift 1) f (n + 1) y) := hupp
        _ ≤ C * (Real.exp (-((n + 1 : ℕ) * P)) *
            Real.exp (cylSup o f (n + 1) (block (n + 1) y))) := by
            rw [← Real.exp_add]
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hC.le
    · rw [ite_eq_right hw, ite_eq_right hw]; simp
  have hlow : Tendsto (fun n : ℕ => P - Real.log C / n) atTop (𝓝 P) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (Real.log C))
  have hupp : Tendsto (fun n : ℕ => P + (-Real.log c) / n) atTop (𝓝 P) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (-Real.log c))
  have hlog : ∀ n : ℕ, 0 < n → (n : ℝ) * P - Real.log C ≤ Real.log (admissibleSumPot o f n) ∧
      Real.log (admissibleSumPot o f n) ≤ n * P + (-Real.log c) := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hA := h.admissibleSumPot_pos (o := o) (f := f) (k + 1)
    have hE := Real.exp_pos (-((k + 1 : ℕ) * P))
    obtain ⟨h1, h2⟩ := key k
    have h1' := Real.log_le_log (mul_pos hc (mul_pos hE hA)) h1
    have h2' := Real.log_le_log one_pos h2
    rw [Real.log_mul hc.ne' (mul_pos hE hA).ne', Real.log_mul hE.ne' hA.ne',
      Real.log_exp, Real.log_one] at h1'
    rw [Real.log_mul hC.ne' (mul_pos hE hA).ne', Real.log_mul hE.ne' hA.ne',
      Real.log_exp, Real.log_one] at h2'
    constructor <;> linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hn', sub_mul, div_mul_cancel₀ _ hn'.ne']
    linarith [(hlog n hn).1, mul_comm P (n : ℝ)]
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn', add_mul, div_mul_cancel₀ _ hn'.ne']
    linarith [(hlog n hn).2, mul_comm P (n : ℝ)]

theorem IsGibbsPotential.pressure_eq (h0 : ∃ i, o i = 0) [IsProbabilityMeasure ν]
    (hν : ν (subshift o)ᶜ = 0) (hg : IsGibbsPotential o f ν P C)
    (h : HasBoundedDistortion o f B D) : P = pressureZPot o f :=
  tendsto_nhds_unique (hg.tendsto_log_admissibleSumPot hν h)
    (h.tendsto_pressureZPot_admissibleSumPot h0)

theorem IsGibbsPotential.pressure_eq_of_isHolder (h0 : ∃ i, o i = 0) [IsProbabilityMeasure ν]
    (hν : ν (subshift o)ᶜ = 0) (hg : IsGibbsPotential o f ν P C)
    (hf : IsHolderPotential o f) : P = pressureZPot o f := by
  have : Nonempty ι := ⟨h0.choose⟩
  obtain ⟨B, D, -, -, h⟩ := hf.exists_hasBoundedDistortion
  exact hg.pressure_eq h0 hν h

end Gibbs

end FractalGeometry
