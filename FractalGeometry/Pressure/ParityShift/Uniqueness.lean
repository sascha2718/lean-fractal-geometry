import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Pressure.GibbsUniqueness
import FractalGeometry.Pressure.ParityShift.HolderPotential
import FractalGeometry.Pressure.ParityShift.PeriodicWords
import FractalGeometry.Pressure.ParityShift.SymbolicMetric
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.OrientationCoding
import FractalGeometry.Symbolic.ParityShift
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology Set

open scoped ENNReal symmDiff

section Uniqueness

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {o : ι → ZMod 2} {f : (ℤ → ι × ZMod 2) → ℝ} {ν ν' : Measure (ℤ → ι × ZMod 2)}
  {B D P C P' C' : ℝ}

theorem IsGibbsPotential.pressure_eq_pressure [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hν : ν (subshift o)ᶜ = 0) (hν' : ν' (subshift o)ᶜ = 0) (hg : IsGibbsPotential o f ν P C)
    (hg' : IsGibbsPotential o f ν' P' C') (h : HasBoundedDistortion o f B D) : P = P' :=
  tendsto_nhds_unique (hg.tendsto_log_admissibleSumPot hν h)
    (hg'.tendsto_log_admissibleSumPot hν' h)

theorem IsGibbsPotential.measure_cylinder_le [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hν : ν (subshift o)ᶜ = 0) (hν' : ν' (subshift o)ᶜ = 0) (hg : IsGibbsPotential o f ν P C)
    (hg' : IsGibbsPotential o f ν' P' C') (h : HasBoundedDistortion o f B D) (n : ℕ)
    (w : Fin n → ι × ZMod 2) :
    ν' (cylinder w) ≤ ENNReal.ofReal (C * C') * ν (cylinder w) := by
  have : Nonempty ι := ⟨((nonempty_of_isProbabilityMeasure ν).some 0).1⟩
  have hPP := hg.pressure_eq_pressure hν hν' hg' h
  subst hPP
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hy₀ : tau o (fun _ => i) ∈ subshift o := tau_mem_subshift _
  have hC1 := hg.one_le hy₀
  have hC1' := hg'.one_le hy₀
  by_cases hw : IsAdmissible o w
  · rcases n with _ | n
    · have huniv : (cylinder w) = univ := eq_univ_of_forall fun _ k => k.elim0
      rw [huniv, measure_univ, measure_univ, mul_one]
      exact ENNReal.one_le_ofReal.2 (by nlinarith)
    · obtain ⟨y, hy, rfl⟩ := hw.exists_block_eq
      have h1 := (hg'.2 y hy (n + 1) (Nat.succ_pos n)).2
      have h2 := (hg.2 y hy (n + 1) (Nat.succ_pos n)).1
      have hreal : ν'.real (cylinder (block (n + 1) y)) ≤
          C * C' * ν.real (cylinder (block (n + 1) y)) := by
        rw [inv_mul_le_iff₀ hg.1] at h2
        calc ν'.real (cylinder (block (n + 1) y))
            ≤ C' * Real.exp (-((n + 1 : ℕ) * P) + birkhoffSum (shift 1) f (n + 1) y) := h1
          _ ≤ C' * (C * ν.real (cylinder (block (n + 1) y))) :=
            mul_le_mul_of_nonneg_left h2 hg'.1.le
          _ = C * C' * ν.real (cylinder (block (n + 1) y)) := by ring
      rw [← ofReal_measureReal, ← ofReal_measureReal, ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal hreal
  · have hsub : cylinder w ⊆ (subshift o)ᶜ := fun y hy hys =>
      hw ((funext hy : block n y = w) ▸ isAdmissible_block hys n)
    rw [measure_mono_null hsub hν']
    exact zero_le

theorem IsGibbsPotential.eq_of_ergodic [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hν : ν (subshift o)ᶜ = 0) (hν' : ν' (subshift o)ᶜ = 0) (hg : IsGibbsPotential o f ν P C)
    (hg' : IsGibbsPotential o f ν' P' C') (h : HasBoundedDistortion o f B D)
    (herg : Ergodic (shift 1) ν) (hinv' : MeasurePreserving (shift 1) ν' ν') : ν' = ν := by
  refine herg.eq_of_absolutelyContinuous hinv' fun A hA0 => ?_
  have hle : ∀ {A : Set (ℤ → ι × ZMod 2)}, MeasurableSet A →
      ν' A ≤ ENNReal.ofReal (C * C') * ν A := fun hA =>
    le_of_cylinder_le herg.toMeasurePreserving hinv' ENNReal.ofReal_ne_top
      (fun n w => hg.measure_cylinder_le hν hν' hg' h n w) hA
  obtain ⟨A', hAA', hA'm, hA'0⟩ := exists_measurable_superset_of_null hA0
  exact measure_mono_null hAA' (le_antisymm ((hle hA'm).trans (by rw [hA'0, mul_zero]))
    zero_le)

theorem IsGibbsPotential.eq_of_ergodic_of_isHolder [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] (hν : ν (subshift o)ᶜ = 0) (hν' : ν' (subshift o)ᶜ = 0)
    (hg : IsGibbsPotential o f ν P C) (hg' : IsGibbsPotential o f ν' P' C')
    (hf : IsHolderPotential o f) (herg : Ergodic (shift 1) ν)
    (hinv' : MeasurePreserving (shift 1) ν' ν') : ν' = ν := by
  have : Nonempty ι := ⟨((nonempty_of_isProbabilityMeasure ν).some 0).1⟩
  obtain ⟨B, D, -, -, h⟩ := hf.exists_hasBoundedDistortion
  exact hg.eq_of_ergodic hν hν' hg' h herg hinv'

end Uniqueness

end FractalGeometry
