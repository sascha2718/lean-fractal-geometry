import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.LinearCocycles.Pressure
import FractalGeometry.LinearCocycles.SingularValue
import FractalGeometry.Pressure.DeterminantEquilibrium
import FractalGeometry.Pressure.Rectangular.Bernoulli
import FractalGeometry.Pressure.Rectangular.Defs
import FractalGeometry.Pressure.Rectangular.EquilibriumStatement
import FractalGeometry.Pressure.Rectangular.Exponents
import FractalGeometry.Pressure.Rectangular.Gibbs
import FractalGeometry.Pressure.Rectangular.Invertibility
import FractalGeometry.Pressure.Rectangular.LiftedGibbs
import FractalGeometry.Pressure.Rectangular.Matrices
import FractalGeometry.Pressure.Rectangular.Pressure
import FractalGeometry.Pressure.SingularValueBlocks
import FractalGeometry.Pressure.SingularValueEquilibrium
import FractalGeometry.Pressure.SingularValueStatement
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.ParityShift
import FractalGeometry.Symbolic.RelativeEntropy
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory

universe u

namespace RectangularIFS

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {S : RectangularIFS ι} {s : ℝ}

theorem IsEquilibriumState.blockRelEntropy_le (hs : 0 ≤ s) {μ ν : Measure (ℤ → ι)}
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) {K : ℝ} (hK : S.HasGibbsBoundsWith K s ν) {n : ℕ}
    (hn : 0 < n) : blockRelEntropy μ ν n ≤ Real.log K := by
  have hK0 : 0 < K := one_pos.trans_le hK.1
  have hpos := hK.measureReal_cylinder_pos hn
  have hblock := (MatrixTuple.isEquilibriumState_iff_forall S.det_mat_ne_zero hs hinv).1 heq n hn
  change (n : ℝ) * S.pressure s ≤ blockEntropy μ n +
    ∑ w : Fin n → ι, μ.real (cylinder w) * Real.log (svf s (S.matWord (List.ofFn w))) at hblock
  have hlog : ∀ w : Fin n → ι, Real.log (svf s (S.matWord (List.ofFn w))) ≤
      Real.log K + n * S.pressure s + Real.log (ν.real (cylinder w)) := by
    intro w
    have hl := ((hK.2 n hn w).1)
    have hφ : svf s (S.matWord (List.ofFn w)) ≤
        K * ν.real (cylinder w) * Real.exp (n * S.pressure s) := by
      rw [inv_mul_le_iff₀ hK0] at hl
      have e := Real.exp_pos (n * S.pressure s)
      calc svf s (S.matWord (List.ofFn w))
          = Real.exp (-(n * S.pressure s)) * svf s (S.matWord (List.ofFn w)) *
              Real.exp (n * S.pressure s) := by
            rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
              mul_one]
        _ ≤ K * ν.real (cylinder w) * Real.exp (n * S.pressure s) :=
            mul_le_mul_of_nonneg_right hl e.le
    have h := Real.log_le_log (S.svf_matWord_pos s _) hφ
    rwa [Real.log_mul (mul_pos hK0 (hpos w)).ne' (Real.exp_pos _).ne', Real.log_exp,
      Real.log_mul hK0.ne' (hpos w).ne', add_right_comm] at h
  have hsum : ∑ w : Fin n → ι, μ.real (cylinder w) * Real.log (svf s (S.matWord (List.ofFn w)))
      ≤ Real.log K + n * S.pressure s +
        ∑ w : Fin n → ι, μ.real (cylinder w) * Real.log (ν.real (cylinder w)) := by
    calc ∑ w : Fin n → ι, μ.real (cylinder w) * Real.log (svf s (S.matWord (List.ofFn w)))
        ≤ ∑ w : Fin n → ι, μ.real (cylinder w) *
            (Real.log K + n * S.pressure s + Real.log (ν.real (cylinder w))) :=
          Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hlog w) measureReal_nonneg
      _ = (∑ w : Fin n → ι, μ.real (cylinder w)) * (Real.log K + n * S.pressure s) +
            ∑ w : Fin n → ι, μ.real (cylinder w) * Real.log (ν.real (cylinder w)) := by
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun w _ => by ring
      _ = _ := by rw [sum_measureReal_cylinder μ n, one_mul]
  rw [blockRelEntropy_eq n fun w => (hpos w).ne']
  linarith

theorem IsEquilibriumState.absolutelyContinuous_of_hasGibbsBounds (hs : 0 ≤ s)
    {μ ν : Measure (ℤ → ι)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hinv : MeasurePreserving (shift 1) μ μ) (hνinv : MeasurePreserving (shift 1) ν ν)
    (heq : S.IsEquilibriumState s μ) (hg : S.HasGibbsBounds s ν) : μ ≪ ν := by
  obtain ⟨K, hK⟩ := (S.hasGibbsBounds_iff).1 hg
  exact absolutelyContinuous_of_blockRelEntropy_le hinv hνinv
    (fun n hn => hK.measureReal_cylinder_pos hn) fun n hn => heq.blockRelEntropy_le hs hinv hK hn

theorem IsEquilibriumState.eq_of_hasGibbsBounds (hs : 0 ≤ s) {μ ν : Measure (ℤ → ι)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hinv : MeasurePreserving (shift 1) μ μ)
    (hν : Ergodic (shift 1) ν) (heq : S.IsEquilibriumState s μ) (hg : S.HasGibbsBounds s ν) :
    μ = ν :=
  hν.eq_of_absolutelyContinuous hinv
    (heq.absolutelyContinuous_of_hasGibbsBounds hs hinv hν.toMeasurePreserving hg)

theorem IsEquilibriumState.eq_map_unCode (hs0 : 0 < s) (hs2 : s < 2)
    {ν : Measure (ℤ → ι × ZMod 2)} [IsProbabilityMeasure ν] (hν : ν (subshift S.o)ᶜ = 0)
    (herg : Ergodic (shift 1) ν) (hg : IsGibbs S.o (S.potential₁ s) ν) {μ : Measure (ℤ → ι)}
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) : μ = ν.map unCode :=
  heq.eq_of_hasGibbsBounds hs0.le hinv (ergodic_map_unCode herg)
    (S.hasGibbsBounds_map_unCode hs0 hs2 hν hg)

theorem IsEquilibriumState.hasGibbsBounds_of_hasBothOrientations (hrot : S.HasBothOrientations) (hs0 : 0 < s)
    {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) : S.HasGibbsBounds s μ := by
  rcases lt_or_ge s 2 with hs2 | hs2
  · obtain ⟨ν, hp, hν, herg, hg⟩ := S.exists_isGibbs_potential₁ hrot s
    rw [heq.eq_map_unCode hs0 hs2 hν herg hg hinv]
    exact S.hasGibbsBounds_map_unCode hs0 hs2 hν hg
  · have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
    rw [heq.eq_bernoulli hinv hs2]
    exact S.hasGibbsBounds_bernoulli hs2

variable (S)

end RectangularIFS

theorem equilibriumGibbs : EquilibriumGibbsStatement.{u} :=
  fun _ hrot _ hs0 _ _ _ hinv heq => heq.hasGibbsBounds_of_hasBothOrientations hrot hs0 hinv

end FractalGeometry
