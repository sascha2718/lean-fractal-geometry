import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.LinearCocycles.SingularValue
import FractalGeometry.Pressure.GibbsUniqueness
import FractalGeometry.Pressure.Rectangular.Defs
import FractalGeometry.Pressure.Rectangular.Gibbs
import FractalGeometry.Pressure.Rectangular.Matrices
import FractalGeometry.Pressure.Rectangular.Pressure
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.OrientationCoding
import FractalGeometry.Symbolic.ParityCylinders
import FractalGeometry.Symbolic.ParityFlip
import FractalGeometry.Symbolic.ParityMeasurability
import FractalGeometry.Symbolic.ParityRanges
import FractalGeometry.Symbolic.ParityShift
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Set

section Uniqueness

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : RectangularIFS ι) {s : ℝ} {μ ν : Measure (ℤ → ι)}

omit [MeasurableSingletonClass ι] in

theorem RectangularIFS.measureReal_cylinder_le_of_hasGibbsBounds [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {K L : ℝ} (hK : S.HasGibbsBoundsWith K s μ)
    (hL : S.HasGibbsBoundsWith L s ν) (n : ℕ) (w : Fin n → ι) :
    μ.real (cylinder w) ≤ K * L * ν.real (cylinder w) := by
  obtain ⟨hK1, hKb⟩ := hK
  obtain ⟨hL1, hLb⟩ := hL
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have huniv : cylinder w = univ := eq_univ_of_forall fun _ k => k.elim0
    rw [huniv, probReal_univ, probReal_univ, mul_one]
    nlinarith
  · have h1 := (hKb n hn w).2
    have h2 := (hLb n hn w).1
    rw [inv_mul_le_iff₀ (by linarith)] at h2
    calc μ.real (cylinder w)
        ≤ K * (Real.exp (-(n * S.pressure s)) * svf s (S.matWord (List.ofFn w))) := h1
      _ ≤ K * (L * ν.real (cylinder w)) := mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = K * L * ν.real (cylinder w) := by ring

theorem RectangularIFS.eq_of_hasGibbsBounds [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MeasurePreserving (shift 1) μ μ) (hν : Ergodic (shift 1) ν)
    (hgμ : S.HasGibbsBounds s μ) (hgν : S.HasGibbsBounds s ν) : μ = ν := by
  obtain ⟨K, hK⟩ := (S.hasGibbsBounds_iff).1 hgμ
  obtain ⟨L, hL⟩ := (S.hasGibbsBounds_iff).1 hgν
  have hK1 := hK.1
  have hL1 := hL.1
  have hcyl : ∀ (n : ℕ) (w : Fin n → ι),
      μ (cylinder w) ≤ ENNReal.ofReal (K * L) * ν (cylinder w) := by
    intro n w
    rw [← ofReal_measureReal, ← ofReal_measureReal, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (S.measureReal_cylinder_le_of_hasGibbsBounds hK hL n w)
  refine hν.eq_of_absolutelyContinuous hμ fun A hA0 => ?_
  obtain ⟨A', hAA', hA'm, hA'0⟩ := exists_measurable_superset_of_null hA0
  have hle := le_of_cylinder_le hν.toMeasurePreserving hμ ENNReal.ofReal_ne_top hcyl hA'm
  exact measure_mono_null hAA' (le_antisymm (hle.trans (by rw [hA'0, mul_zero])) zero_le)

end Uniqueness

section Flip

variable {ι : Type*}

@[simp] theorem flipAxis_flipAxis (y : ℤ → ι × ZMod 2) : flipAxis (flipAxis y) = y :=
  funext fun n => flipSymbol_flipSymbol (y n)

theorem preimage_flipAxis_range_tau (o : ι → ZMod 2) :
    flipAxis ⁻¹' range (tau o) = range (omega o) := by
  ext y
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [← flipAxis_tau, hx, flipAxis_flipAxis]
  · rintro ⟨x, rfl⟩
    exact ⟨x, (flipAxis_omega o x).symm⟩

theorem preimage_flipAxis_range_omega (o : ι → ZMod 2) :
    flipAxis ⁻¹' range (omega o) = range (tau o) := by
  ext y
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [← flipAxis_omega, hx, flipAxis_flipAxis]
  · rintro ⟨x, rfl⟩
    exact ⟨x, (flipAxis_tau o x).symm⟩

variable [MeasurableSpace ι] {o : ι → ZMod 2} {ν : Measure (ℤ → ι × ZMod 2)}

theorem map_unCode_restrict_map_flipAxis {R : Set (ℤ → ι × ZMod 2)} (hR : MeasurableSet R) :
    ((ν.map flipAxis).restrict R).map unCode = (ν.restrict (flipAxis ⁻¹' R)).map unCode := by
  rw [Measure.restrict_map measurable_flipAxis hR,
    Measure.map_map measurable_unCode measurable_flipAxis]
  rfl

variable [Fintype ι] [MeasurableSingletonClass ι]

theorem map_unCode_restrict_range_tau_map_flipAxis :
    ((ν.map flipAxis).restrict (range (tau o))).map unCode =
      (ν.restrict (range (omega o))).map unCode := by
  rw [map_unCode_restrict_map_flipAxis (measurableSet_range_tau o), preimage_flipAxis_range_tau]

theorem map_unCode_restrict_range_omega_map_flipAxis :
    ((ν.map flipAxis).restrict (range (omega o))).map unCode =
      (ν.restrict (range (tau o))).map unCode := by
  rw [map_unCode_restrict_map_flipAxis (measurableSet_range_omega o),
    preimage_flipAxis_range_omega]

end Flip

section Decompositions

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {o : ι → ZMod 2} {ν : Measure (ℤ → ι × ZMod 2)}

theorem restrict_range_tau_add_restrict_range_omega (hν : ν (subshift o)ᶜ = 0) :
    ν.restrict (range (tau o)) + ν.restrict (range (omega o)) = ν := by
  rw [← Measure.restrict_union disjoint_range_tau_range_omega (measurableSet_range_omega o),
    range_tau_union_range_omega]
  exact Measure.restrict_eq_self_of_ae_mem hν

theorem map_unCode_eq₁ (hν : ν (subshift o)ᶜ = 0) :
    ν.map unCode = (ν.restrict (range (tau o))).map unCode +
      (ν.restrict (range (omega o))).map unCode := by
  rw [← Measure.map_add _ _ measurable_unCode, restrict_range_tau_add_restrict_range_omega hν]

theorem map_unCode_eq_tau (hν : ν (subshift o)ᶜ = 0) :
    ν.map unCode = (ν.restrict (range (tau o))).map unCode +
      ((ν.map flipAxis).restrict (range (tau o))).map unCode := by
  rw [map_unCode_restrict_range_tau_map_flipAxis]
  exact map_unCode_eq₁ hν

theorem map_unCode_eq_omega (hν : ν (subshift o)ᶜ = 0) :
    ν.map unCode = (ν.restrict (range (omega o))).map unCode +
      ((ν.map flipAxis).restrict (range (omega o))).map unCode := by
  rw [map_unCode_restrict_range_omega_map_flipAxis, add_comm]
  exact map_unCode_eq₁ hν

theorem map_unCode_eq₂ (hν : ν (subshift o)ᶜ = 0) :
    ν.map unCode = ((ν.map flipAxis).restrict (range (tau o))).map unCode +
      ((ν.map flipAxis).restrict (range (omega o))).map unCode := by
  rw [map_unCode_restrict_range_tau_map_flipAxis, map_unCode_restrict_range_omega_map_flipAxis,
    add_comm]
  exact map_unCode_eq₁ hν

end Decompositions

end FractalGeometry
