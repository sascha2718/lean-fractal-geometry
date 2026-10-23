import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.LinearCocycles.PressureBounds
import FractalGeometry.LinearCocycles.SingularValue
import FractalGeometry.Pressure.Rectangular.Bernoulli
import FractalGeometry.Pressure.Rectangular.Defs
import FractalGeometry.Pressure.Rectangular.DeterminantPotential
import FractalGeometry.Pressure.Rectangular.Equilibrium
import FractalGeometry.Pressure.Rectangular.EquilibriumStatement
import FractalGeometry.Pressure.Rectangular.Exponents
import FractalGeometry.Pressure.Rectangular.Gibbs
import FractalGeometry.Pressure.Rectangular.LyapunovStatement
import FractalGeometry.Pressure.Rectangular.Matrices
import FractalGeometry.Pressure.Rectangular.Pressure
import FractalGeometry.Pressure.Rectangular.Proximal
import FractalGeometry.Pressure.SingularValueEnergy
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.Symbolic.BernoulliEntropy
import FractalGeometry.Symbolic.Concatenation
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

/-!
Ian D. Morris and Pablo Shmerkin, "On equality of Hausdorff and affinity dimensions,
via self-affine measures on positive subsystems", Transactions of the American
Mathematical Society 371(3) (2019), 1547–1582, Theorem 3.1 and Lemmas 3.4–3.5.
DOI: 10.1090/tran/7119; arXiv:1602.08789.

This proves the distinct-Lyapunov-exponent conclusion for finite contractive
rectangular matrix families with both diagonal and anti-diagonal matrices and a
proximal diagonal generator, at singular-value parameter `0 < s < 2`.
The full-support conclusion and the general irreducible-matrix theorem are not
asserted by this endpoint.
-/

namespace FractalGeometry

open MeasureTheory

open scoped Matrix.Norms.L2Operator

universe u

theorem abs_det_rpow_le_svf {s : ℝ} (hs : 0 ≤ s) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    |A.det| ^ (s / 2) ≤ svf s A := by
  have hd := MatrixTuple.abs_det_le_norm_sq A
  have key : ∀ t : ℝ, 0 ≤ t → |A.det| ^ (t / 2) ≤ ‖A‖ ^ t := fun t ht => by
    calc |A.det| ^ (t / 2) ≤ (‖A‖ ^ 2) ^ (t / 2) :=
          Real.rpow_le_rpow (abs_nonneg _) hd (by linarith)
      _ = ‖A‖ ^ t := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
          congr 1
          push_cast
          ring
  unfold svf
  split_ifs with h1 h2
  · exact key s hs
  · rcases (abs_nonneg A.det).eq_or_lt with h0 | h0
    · rw [← h0, Real.zero_rpow (by linarith)]
      positivity
    · rw [show s / 2 = (2 - s) / 2 + (s - 1) by ring, Real.rpow_add h0]
      exact mul_le_mul_of_nonneg_right (key _ (by linarith)) (by positivity)
  · exact le_rfl

namespace RectangularIFS

section Pressure

variable {ι : Type*} (S : RectangularIFS ι)

theorem abs_det_matWord_rpow_le_svf {s : ℝ} (hs : 0 ≤ s) (w : List ι) :
    |(S.matWord w).det| ^ (s / 2) ≤ svf s (S.matWord w) :=
  abs_det_rpow_le_svf hs _

variable [Fintype ι]

theorem sum_abs_det_matWord_rpow (t : ℝ) (n : ℕ) :
    ∑ w : Fin n → ι, |(S.matWord (List.ofFn w)).det| ^ t = (∑ i, |(S.mat i).det| ^ t) ^ n := by
  induction n with
  | zero => simp [matWord]
  | succ n ih =>
    have h1 : ∑ w : Fin 1 → ι, |(S.matWord (List.ofFn w)).det| ^ t =
        ∑ i, |(S.mat i).det| ^ t :=
      (Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι).symm _ _ fun i => by simp [matWord]).symm
    rw [sum_ofFn_add n 1 fun w => |(S.matWord w).det| ^ t, pow_succ, ← ih, ← h1,
      Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => ?_
    rw [matWord_append, Matrix.det_mul, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]

theorem log_sum_abs_det_rpow_le_pressure [Nonempty ι] {s : ℝ} (hs : 0 ≤ s) :
    Real.log (∑ i, |(S.mat i).det| ^ (s / 2)) ≤ S.pressure s := by
  have hq : 0 < ∑ i, |(S.mat i).det| ^ (s / 2) :=
    Finset.sum_pos (fun i _ => S.rpow_abs_det_mat_pos _ i) Finset.univ_nonempty
  refine le_csInf ⟨_, 1, Set.mem_Ici.2 le_rfl, rfl⟩ ?_
  rintro _ ⟨n, hn, rfl⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : (∑ i, |(S.mat i).det| ^ (s / 2)) ^ n ≤ S.svfSum s n := by
    rw [← S.sum_abs_det_matWord_rpow, svfSum]
    exact Finset.sum_le_sum fun w _ => S.abs_det_matWord_rpow_le_svf hs _
  rw [le_div_iff₀ hn', mul_comm, ← Real.log_pow]
  exact Real.log_le_log (pow_pos hq n) hle

end Pressure

end RectangularIFS

theorem energy_self (l s : ℝ) : energy l l s = s * l := by
  unfold energy
  split_ifs <;> ring

namespace RectangularIFS

section LemmaThreeFour

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {S : RectangularIFS ι} {s : ℝ} {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]

theorem IsEquilibriumState.pressure_eq_of_lyapunov_eq (heq : S.IsEquilibriumState s μ)
    (hinv : MeasurePreserving (shift 1) μ μ) (hs : 0 ≤ s)
    (hl : S.lyapunov₁ μ = S.lyapunov₂ μ) :
    S.pressure s =
      entropy μ + ∑ i, μ.real (cylinder ![i]) * Real.log (|(S.mat i).det| ^ (s / 2)) := by
  have hsum := S.lyapunov₁_add_lyapunov₂ hinv
  rw [← hl] at hsum
  rw [heq.pressure_eq hinv hs, ← hl, energy_self]
  have e : s * S.lyapunov₁ μ = s / 2 * (S.lyapunov₁ μ + S.lyapunov₁ μ) := by ring
  rw [e, hsum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_rpow (by simpa using S.rpow_abs_det_mat_pos 1 i)]
  ring

theorem IsEquilibriumState.entropy_eq_blockEntropy_one_of_lyapunov_eq
    (heq : S.IsEquilibriumState s μ) (hinv : MeasurePreserving (shift 1) μ μ) (hs : 0 ≤ s)
    (hl : S.lyapunov₁ μ = S.lyapunov₂ μ) :
    entropy μ = blockEntropy μ 1 ∧
      blockEntropy μ 1 + ∑ i, μ.real (cylinder ![i]) * Real.log (|(S.mat i).det| ^ (s / 2)) =
        Real.log (∑ i, |(S.mat i).det| ^ (s / 2)) := by
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
  have hP := heq.pressure_eq_of_lyapunov_eq hinv hs hl
  have hG := blockEntropy_one_add_sum_le μ (fun i => |(S.mat i).det| ^ (s / 2))
    (S.rpow_abs_det_mat_pos (s / 2))
  have hH := entropy_le_blockEntropy_one hinv
  have hL := S.log_sum_abs_det_rpow_le_pressure hs
  constructor <;> linarith

theorem IsEquilibriumState.isBernoulli_of_lyapunov_eq (heq : S.IsEquilibriumState s μ)
    (hinv : MeasurePreserving (shift 1) μ μ) (hs : 0 ≤ s)
    (hl : S.lyapunov₁ μ = S.lyapunov₂ μ) : IsBernoulli μ := by
  have hent := (heq.entropy_eq_blockEntropy_one_of_lyapunov_eq hinv hs hl).1
  exact ⟨fun i => μ.real (cylinder ![i]), fun _ => measureReal_nonneg,
    sum_measureReal_cylinder_one μ, fun k _ _ w =>
      measureReal_preimage_shift_cylinder_eq_prod_of_entropy_eq hinv hent k w⟩

end LemmaThreeFour

section SimpleLyapunov

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {S : RectangularIFS ι} {s : ℝ} {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]

theorem IsEquilibriumState.lyapunov₂_lt_lyapunov₁_of_hasGibbsBounds
    (heq : S.IsEquilibriumState s μ) (hinv : MeasurePreserving (shift 1) μ μ)
    (hrot : S.HasBothOrientations) (hprox : S.Proximal) (hs0 : 0 < s) (hs2 : s < 2)
    (hG : S.HasGibbsBounds s μ) : S.lyapunov₂ μ < S.lyapunov₁ μ :=
  lt_of_le_of_ne (S.lyapunov₂_le_lyapunov₁ hinv) fun hl =>
    RectangularIFS.not_isBernoulli hrot hprox hs0 hs2 hG
      (heq.isBernoulli_of_lyapunov_eq hinv hs0.le hl.symm)

end SimpleLyapunov

end RectangularIFS

theorem morrisShmerkinLyapunov_of_equilibriumGibbs (h : EquilibriumGibbsStatement.{u}) :
    MorrisShmerkinLyapunov.{u} := by
  intro ι _ _ _ S hrot hpd s hs0 hs2 μ _ hinv heq
  exact heq.lyapunov₂_lt_lyapunov₁_of_hasGibbsBounds hinv hrot hpd.proximal hs0 hs2
    (h S hrot hs0 hs2 μ hinv heq)

theorem morrisShmerkinLyapunov_holds : MorrisShmerkinLyapunov.{u} :=
  morrisShmerkinLyapunov_of_equilibriumGibbs equilibriumGibbs

end FractalGeometry
