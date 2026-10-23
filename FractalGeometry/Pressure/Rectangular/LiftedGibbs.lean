import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.LinearCocycles.SingularValue
import FractalGeometry.Pressure.ParityShift.Bowen
import FractalGeometry.Pressure.ParityShift.CoordinatePotential
import FractalGeometry.Pressure.ParityShift.GibbsBounds
import FractalGeometry.Pressure.ParityShift.LocallyConstant
import FractalGeometry.Pressure.ParityShift.PeriodicWords
import FractalGeometry.Pressure.ParityShift.SymbolicMetric
import FractalGeometry.Pressure.Rectangular.Defs
import FractalGeometry.Pressure.Rectangular.Gibbs
import FractalGeometry.Pressure.Rectangular.Matrices
import FractalGeometry.Pressure.Rectangular.Pressure
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.OrientationCoding
import FractalGeometry.Symbolic.ParityCylinders
import FractalGeometry.Symbolic.ParityShift
import FractalGeometry.Symbolic.PeriodicWords
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory

theorem RectangularIFS.exists_isGibbs_potential₁ {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : RectangularIFS ι) (hrot : S.HasBothOrientations) (s : ℝ) :
    ∃ μ₁ : Measure (ℤ → ι × ZMod 2), IsProbabilityMeasure μ₁ ∧ μ₁ (subshift S.o)ᶜ = 0 ∧
      Ergodic (shift 1) μ₁ ∧ IsGibbs S.o (S.potential₁ s) μ₁ := by
  obtain ⟨ν, hp, hs, herg, P, C, hg⟩ := bowenGibbsExistence S.o hrot.1 hrot.2 _
    (isHolderPotential_apply_zero (o := S.o) (S.potential₁ s))
  exact ⟨ν, hp, hs, herg, isGibbs_iff.2 ⟨P, C, (isGibbsPotential_iff_isGibbsWith _).1 hg⟩⟩

section Image

variable {ι : Type*} [MeasurableSpace ι] {ν : Measure (ℤ → ι × ZMod 2)}

theorem ergodic_map_unCode (h : Ergodic (shift 1) ν) : Ergodic (shift 1) (ν.map unCode) :=
  (⟨measurable_unCode, rfl⟩ : MeasurePreserving unCode ν (ν.map unCode))
    |>.ergodic_of_ergodic_semiconj h (measurable_shift 1) fun _ => rfl

variable [Fintype ι] [MeasurableSingletonClass ι] (S : RectangularIFS ι) {s : ℝ}

theorem RectangularIFS.exists_isGibbsWith_pressure (hs0 : 0 < s) (hs2 : s < 2) [IsProbabilityMeasure ν]
    (hν : ν (subshift S.o)ᶜ = 0) (hg : IsGibbs S.o (S.potential₁ s) ν) :
    ∃ C, IsGibbsWith S.o (S.potential₁ s) ν (S.pressure s) C := by
  obtain ⟨P, C, hPC⟩ := isGibbs_iff.1 hg
  have hP : P = S.pressure s := IsGibbsAt.eq_pressure₁ (S := S) hν hs0 hs2 ⟨C, hPC⟩
  exact ⟨C, hP ▸ hPC⟩

omit [Fintype ι] [MeasurableSingletonClass ι] in

theorem RectangularIFS.measureReal_cylinder_liftBlock_bounds {P C : ℝ}
    (hC : IsGibbsWith S.o (S.potential₁ s) ν P C) (m : ℕ) (w : Fin (m + 1) → ι) (c : ZMod 2) :
    C⁻¹ * (Real.exp (-((m + 1 : ℕ) * P)) *
        Real.exp (∑ k, S.potential₁ s (liftBlock S.o c w k))) ≤
        ν.real (cylinder (liftBlock S.o c w)) ∧
      ν.real (cylinder (liftBlock S.o c w)) ≤
        C * (Real.exp (-((m + 1 : ℕ) * P)) *
          Real.exp (∑ k, S.potential₁ s (liftBlock S.o c w k))) := by
  have hy := codeFrom_mem_subshift S.o c (extendWord w)
  have hblock := block_codeFrom_extendWord S.o c w
  have hsum : ∑ k ∈ Finset.range (m + 1), S.potential₁ s (codeFrom S.o c (extendWord w) k) =
      ∑ k, S.potential₁ s (liftBlock S.o c w k) := by
    rw [Finset.sum_range]
    exact Finset.sum_congr rfl fun k _ => congrArg (S.potential₁ s) (congrFun hblock k)
  have hcyl : (cylinder fun k : Fin (m + 1) => codeFrom S.o c (extendWord w) k) =
      cylinder (liftBlock S.o c w) := congrArg cylinder hblock
  have h := hC.2 _ hy (m + 1) m.succ_pos
  rw [hsum, Real.exp_add, hcyl] at h
  exact h

theorem RectangularIFS.hasGibbsBounds_map_unCode (hs0 : 0 < s) (hs2 : s < 2) [IsProbabilityMeasure ν]
    (hν : ν (subshift S.o)ᶜ = 0) (hg : IsGibbs S.o (S.potential₁ s) ν) :
    S.HasGibbsBounds s (ν.map unCode) := by
  obtain ⟨C, hC⟩ := S.exists_isGibbsWith_pressure hs0 hs2 hν hg
  obtain ⟨i⟩ : Nonempty ι := ⟨((nonempty_of_isProbabilityMeasure ν).some 0).1⟩
  have hC1 : 1 ≤ C := hC.one_le (tau_mem_subshift fun _ => i)
  have hC0 : 0 < C := by linarith
  refine ⟨2 * C, by linarith, fun n hn w => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsplit : (ν.map unCode).real (cylinder w) =
      ν.real (cylinder (liftBlock S.o 0 w)) + ν.real (cylinder (liftBlock S.o 1 w)) := by
    rw [map_measureReal_apply measurable_unCode (measurableSet_cylinder w),
      measureReal_preimage_unCode_cylinder hν w, sum_zmod_two]
  rw [hsplit, S.svf_matWord_ofFn w hs0 hs2]
  obtain ⟨l0, u0⟩ := S.measureReal_cylinder_liftBlock_bounds hC m w 0
  obtain ⟨l1, u1⟩ := S.measureReal_cylinder_liftBlock_bounds hC m w 1
  have hX := Real.exp_pos (-((m + 1 : ℕ) * S.pressure s))
  have hE0 := Real.exp_pos (∑ k, S.potential₁ s (liftBlock S.o 0 w k))
  have hE1 := Real.exp_pos (∑ k, S.potential₁ s (liftBlock S.o 1 w k))
  generalize Real.exp (-((m + 1 : ℕ) * S.pressure s)) = X at hX l0 u0 l1 u1 ⊢
  generalize Real.exp (∑ k, S.potential₁ s (liftBlock S.o 0 w k)) = E0 at hE0 l0 u0 ⊢
  generalize Real.exp (∑ k, S.potential₁ s (liftBlock S.o 1 w k)) = E1 at hE1 l1 u1 ⊢
  have hM : max E0 E1 ≤ E0 + E1 := max_le_add_of_nonneg hE0.le hE1.le
  have hM0 : E0 ≤ max E0 E1 := le_max_left E0 E1
  have hM1 : E1 ≤ max E0 E1 := le_max_right E0 E1
  constructor
  · calc (2 * C)⁻¹ * (X * max E0 E1) ≤ C⁻¹ * (X * (E0 + E1)) :=
          mul_le_mul (inv_anti₀ hC0 (by linarith)) (mul_le_mul_of_nonneg_left hM hX.le)
            (by positivity) (inv_nonneg.2 hC0.le)
      _ = C⁻¹ * (X * E0) + C⁻¹ * (X * E1) := by ring
      _ ≤ _ := add_le_add l0 l1
  · calc ν.real (cylinder (liftBlock S.o 0 w)) + ν.real (cylinder (liftBlock S.o 1 w))
        ≤ C * (X * E0) + C * (X * E1) := add_le_add u0 u1
      _ = C * (X * (E0 + E1)) := by ring
      _ ≤ C * (X * (2 * max E0 E1)) := by
          gcongr
          linarith
      _ = 2 * C * (X * max E0 E1) := by ring

end Image

end FractalGeometry
