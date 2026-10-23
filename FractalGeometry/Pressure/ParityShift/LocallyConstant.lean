import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.LinearCocycles.SingularValue
import FractalGeometry.Pressure.ParityShift.PeriodicWords
import FractalGeometry.Pressure.Rectangular.Defs
import FractalGeometry.Pressure.Rectangular.Matrices
import FractalGeometry.Pressure.Rectangular.PotentialSums
import FractalGeometry.Pressure.Rectangular.Pressure
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.SelfAffine.Rectangular.Orientation
import FractalGeometry.SelfAffine.Rectangular.SingularValues
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.OrientationCoding
import FractalGeometry.Symbolic.ParityCylinders
import FractalGeometry.Symbolic.ParityShift
import FractalGeometry.Symbolic.PeriodicWords
import FractalGeometry.Symbolic.WordAverages

open FractalGeometry.Ergodic

namespace FractalGeometry

open Filter Topology MeasureTheory

section Words

variable {ι : Type*} (o : ι → ZMod 2) {n : ℕ}

theorem block_extendWord {α : Type*} (w : Fin (n + 1) → α) :
    block (n + 1) (extendWord w) = w :=
  funext (extendWord_natCast w)

theorem codeFrom_zero (x : ℤ → ι) : codeFrom o 0 x = tau o x := by
  funext k; simp [codeFrom]

theorem codeFrom_one (x : ℤ → ι) : codeFrom o 1 x = omega o x := by
  funext k; simp [codeFrom, add_comm]

variable {o}

theorem block_eq_liftBlock {y : ℤ → ι × ZMod 2} (hy : y ∈ subshift o) (n : ℕ) :
    block n y = liftBlock o (y 0).2 (block n (unCode y)) :=
  funext fun k => mem_cylinder_liftBlock hy (w := block n (unCode y)) (fun _ => rfl) k

theorem block_codeFrom_extendWord (o : ι → ZMod 2) (c : ZMod 2) (w : Fin (n + 1) → ι) :
    block (n + 1) (codeFrom o c (extendWord w)) = liftBlock o c w := by
  have h := block_eq_liftBlock (codeFrom_mem_subshift o c (extendWord w)) (n + 1)
  have h0 : (codeFrom o c (extendWord w) 0).2 = c := by simp [codeFrom]
  have h1 : block (n + 1) (unCode (codeFrom o c (extendWord w))) = w := block_extendWord w
  rwa [h0, h1] at h

theorem isAdmissible_liftBlock (o : ι → ZMod 2) (c : ZMod 2) (w : Fin (n + 1) → ι) :
    IsAdmissible o (liftBlock o c w) := by
  rw [← block_codeFrom_extendWord]
  exact isAdmissible_block (codeFrom_mem_subshift o c (extendWord w)) _

theorem IsAdmissible.mem_range_liftBlock {v : Fin (n + 1) → ι × ZMod 2}
    (hv : IsAdmissible o v) :
    v ∈ Set.range fun p : (Fin (n + 1) → ι) × ZMod 2 => liftBlock o p.2 p.1 := by
  obtain ⟨y, hy, rfl⟩ := hv.exists_block_eq
  exact ⟨(block (n + 1) (unCode y), (y 0).2), (block_eq_liftBlock hy _).symm⟩

end Words

section Sums

variable {ι : Type*} [Fintype ι] (o : ι → ZMod 2) (φ : ι × ZMod 2 → ℝ)

open Classical in

noncomputable def admissibleSum (n : ℕ) : ℝ :=
  ∑ w : Fin n → ι × ZMod 2, if IsAdmissible o w then Real.exp (∑ k, φ (w k)) else 0

theorem exists_le_potential [Nonempty ι] : ∃ m, ∀ p, m ≤ φ p := by
  obtain ⟨p, -, hp⟩ := Finset.exists_min_image Finset.univ φ Finset.univ_nonempty
  exact ⟨φ p, fun q => hp q (Finset.mem_univ _)⟩

variable {φ}

theorem exp_le_admissibleSum [Nonempty ι] {m : ℝ} (hm : ∀ p, m ≤ φ p) (n : ℕ) :
    Real.exp (n * m) ≤ admissibleSum o φ n := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hw := isAdmissible_block (tau_mem_subshift (o := o) fun _ => i) n
  have h1 : Real.exp (n * m) ≤ Real.exp (∑ k, φ (block n (tau o fun _ => i) k)) := by
    refine Real.exp_le_exp.2 ?_
    have := Finset.card_nsmul_le_sum Finset.univ
      (fun k : Fin n => φ (block n (tau o fun _ => i) k)) m fun k _ => hm _
    simpa using this
  refine h1.trans ?_
  have h2 := Finset.single_le_sum (f := fun w : Fin n → ι × ZMod 2 =>
    if IsAdmissible o w then Real.exp (∑ k, φ (w k)) else 0)
    (fun w _ => by positivity) (Finset.mem_univ (block n (tau o fun _ => i)))
  rwa [ite_eq_left hw] at h2

theorem admissibleSum_pos [Nonempty ι] (n : ℕ) : 0 < admissibleSum o φ n := by
  obtain ⟨m, hm⟩ := exists_le_potential φ
  exact (Real.exp_pos _).trans_le (exp_le_admissibleSum o hm n)

variable (φ)

theorem admissibleSum_succ (n : ℕ) :
    admissibleSum o φ (n + 1) =
      ∑ w : Fin (n + 1) → ι, ∑ c : ZMod 2, Real.exp (∑ k, φ (liftBlock o c w k)) := by
  classical
  rw [admissibleSum, ← Fintype.sum_of_injective _ (liftBlock_injective o)
    (fun p : (Fin (n + 1) → ι) × ZMod 2 => Real.exp (∑ k, φ (liftBlock o p.2 p.1 k))) _
    (fun v hv => ite_eq_right fun h => hv h.mem_range_liftBlock)
    (fun p => (ite_eq_left (isAdmissible_liftBlock o p.2 p.1)).symm), Fintype.sum_prod_type]

end Sums

section Gibbs

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {o : ι → ZMod 2} {φ : ι × ZMod 2 → ℝ} {ν : Measure (ℤ → ι × ZMod 2)}

def IsGibbsAt (o : ι → ZMod 2) (φ : ι × ZMod 2 → ℝ) (ν : Measure (ℤ → ι × ZMod 2))
    (P : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ y ∈ subshift o, ∀ n : ℕ, 0 < n →
    C⁻¹ * Real.exp (-(n * P) + ∑ k ∈ Finset.range n, φ (y k)) ≤
        ν.real (cylinder fun k : Fin n => y k) ∧
      ν.real (cylinder fun k : Fin n => y k) ≤
        C * Real.exp (-(n * P) + ∑ k ∈ Finset.range n, φ (y k))

theorem IsGibbsAt.tendsto_log_admissibleSum [IsProbabilityMeasure ν]
    (hν : ν (subshift o)ᶜ = 0) {P : ℝ} (h : IsGibbsAt o φ ν P) :
    Tendsto (fun n : ℕ => Real.log (admissibleSum o φ n) / n) atTop (𝓝 P) := by
  classical
  have : Nonempty ι := ⟨((nonempty_of_isProbabilityMeasure ν).some 0).1⟩
  obtain ⟨C, hC, hb⟩ := h
  have key : ∀ n : ℕ,
      C⁻¹ * (Real.exp (-((n + 1 : ℕ) * P)) * admissibleSum o φ (n + 1)) ≤ 1 ∧
        1 ≤ C * (Real.exp (-((n + 1 : ℕ) * P)) * admissibleSum o φ (n + 1)) := by
    intro n
    rw [← sum_measureReal_cylinder_of_isAdmissible hν (n + 1), admissibleSum, Finset.mul_sum,
      Finset.mul_sum, Finset.mul_sum]
    refine ⟨Finset.sum_le_sum fun w _ => ?_, Finset.sum_le_sum fun w _ => ?_⟩ <;>
      by_cases hw : IsAdmissible o w
    · obtain ⟨y, hy, rfl⟩ := hw.exists_block_eq
      rw [ite_eq_left hw, ite_eq_left hw, ← Real.exp_add]
      have := (hb y hy (n + 1) (Nat.succ_pos n)).1
      rwa [Finset.sum_range] at this
    · rw [ite_eq_right hw, ite_eq_right hw]; simp
    · obtain ⟨y, hy, rfl⟩ := hw.exists_block_eq
      rw [ite_eq_left hw, ite_eq_left hw, ← Real.exp_add]
      have := (hb y hy (n + 1) (Nat.succ_pos n)).2
      rwa [Finset.sum_range] at this
    · rw [ite_eq_right hw, ite_eq_right hw]; simp
  have hlow : Tendsto (fun n : ℕ => P - Real.log C / n) atTop (𝓝 P) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (Real.log C))
  have hupp : Tendsto (fun n : ℕ => P + Real.log C / n) atTop (𝓝 P) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (Real.log C))
  have hlog : ∀ n : ℕ, 0 < n → (n : ℝ) * P - Real.log C ≤ Real.log (admissibleSum o φ n) ∧
      Real.log (admissibleSum o φ n) ≤ n * P + Real.log C := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hA := admissibleSum_pos o (φ := φ) (k + 1)
    have hE := Real.exp_pos (-((k + 1 : ℕ) * P))
    obtain ⟨h1, h2⟩ := key k
    have h1' := Real.log_le_log (mul_pos (inv_pos.2 hC) (mul_pos hE hA)) h1
    have h2' := Real.log_le_log one_pos h2
    rw [Real.log_mul (inv_pos.2 hC).ne' (mul_pos hE hA).ne', Real.log_mul hE.ne' hA.ne',
      Real.log_exp, Real.log_inv, Real.log_one] at h1'
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

end Gibbs

namespace RectangularIFS

section Pressure

variable {ι : Type*} (S : RectangularIFS ι) {n : ℕ}

theorem svf_matWord_ofFn (w : Fin (n + 1) → ι) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    svf s (S.matWord (List.ofFn w)) =
      max (Real.exp (∑ k, S.potential₁ s (liftBlock S.o 0 w k)))
        (Real.exp (∑ k, S.potential₁ s (liftBlock S.o 1 w k))) := by
  have h := S.svf_matWord_futureWord (extendWord w) (n + 1) hs0 hs2
  rw [futureWord_eq_ofFn_block, block_extendWord] at h
  have h0 := block_codeFrom_extendWord S.o 0 w
  have h1 := block_codeFrom_extendWord S.o 1 w
  rw [codeFrom_zero] at h0
  rw [codeFrom_one] at h1
  rw [h, Finset.sum_range, Finset.sum_range, ← h0, ← h1]
  rfl

variable [Fintype ι]

theorem svfSum_le_admissibleSum (n : ℕ) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    S.svfSum s (n + 1) ≤ admissibleSum S.o (S.potential₁ s) (n + 1) ∧
      admissibleSum S.o (S.potential₁ s) (n + 1) ≤ 2 * S.svfSum s (n + 1) := by
  rw [admissibleSum_succ, svfSum, Finset.mul_sum]
  refine ⟨Finset.sum_le_sum fun w _ => ?_, Finset.sum_le_sum fun w _ => ?_⟩
  · rw [S.svf_matWord_ofFn w hs0 hs2, sum_zmod_two]
    exact max_le_add_of_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  · rw [S.svf_matWord_ofFn w hs0 hs2, sum_zmod_two]
    linarith [le_max_left (Real.exp (∑ k, S.potential₁ s (liftBlock S.o 0 w k)))
      (Real.exp (∑ k, S.potential₁ s (liftBlock S.o 1 w k))),
      le_max_right (Real.exp (∑ k, S.potential₁ s (liftBlock S.o 0 w k)))
      (Real.exp (∑ k, S.potential₁ s (liftBlock S.o 1 w k)))]

theorem tendsto_log_admissibleSum_potential₁ [Nonempty ι] {s : ℝ} (hs0 : 0 < s)
    (hs2 : s < 2) :
    Tendsto (fun n : ℕ => Real.log (admissibleSum S.o (S.potential₁ s) n) / n) atTop
      (𝓝 (S.pressure s)) := by
  obtain ⟨δ, hδ⟩ := S.exists_ratioLowerBound
  have hP := hδ.tendsto_pressure hs0.le
  have hpos := fun n => hδ.svfSum_pos hs0.le n
  have hupp : Tendsto (fun n : ℕ => Real.log 2 / n + Real.log (S.svfSum s n) / n) atTop
      (𝓝 (S.pressure s)) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)).add hP
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hP hupp ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (hpos _) (S.svfSum_le_admissibleSum k hs0 hs2).1) (Nat.cast_nonneg _)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h := Real.log_le_log (admissibleSum_pos S.o (k + 1))
      (S.svfSum_le_admissibleSum k hs0 hs2).2
    rw [Real.log_mul two_ne_zero (hpos _).ne'] at h
    rw [← add_div]
    exact div_le_div_of_nonneg_right h (Nat.cast_nonneg _)

end Pressure

section Decomposition

variable {ι : Type*} [MeasurableSpace ι] {S : RectangularIFS ι} {s : ℝ} {μ : Measure (ℤ → ι)}
  {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)}

variable [Fintype ι] [MeasurableSingletonClass ι]

theorem _root_.FractalGeometry.IsGibbsAt.eq_pressure₁ {ν : Measure (ℤ → ι × ZMod 2)}
    [IsProbabilityMeasure ν] (hν : ν (subshift S.o)ᶜ = 0) (hs0 : 0 < s) (hs2 : s < 2) {P : ℝ}
    (h : IsGibbsAt S.o (S.potential₁ s) ν P) : P = S.pressure s :=
  haveI : Nonempty ι := ⟨((nonempty_of_isProbabilityMeasure ν).some 0).1⟩
  tendsto_nhds_unique (h.tendsto_log_admissibleSum hν)
    (S.tendsto_log_admissibleSum_potential₁ hs0 hs2)

end Decomposition

end RectangularIFS

end FractalGeometry
