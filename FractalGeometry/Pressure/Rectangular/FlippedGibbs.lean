import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.Pressure.Rectangular.Defs
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.ParityFlip
import FractalGeometry.Symbolic.ParityMeasures
import FractalGeometry.Symbolic.ParityShift
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory

section Flip

variable {ι : Type*}

theorem preimage_flipAxis_subshift (o : ι → ZMod 2) : flipAxis ⁻¹' subshift o = subshift o := by
  ext y
  change (∀ n, Trans o (flipSymbol (y n)) (flipSymbol (y (n + 1)))) ↔
    ∀ n, Trans o (y n) (y (n + 1))
  exact forall_congr' fun n => trans_flipSymbol_iff (y n) (y (n + 1))

theorem preimage_flipAxis_cylinder {n : ℕ} (w : Fin n → ι × ZMod 2) :
    flipAxis ⁻¹' cylinder w = cylinder fun k => flipSymbol (w k) := by
  ext y
  refine forall_congr' fun k => ?_
  change flipSymbol (y k) = w k ↔ y k = flipSymbol (w k)
  constructor
  · intro h
    rw [← h, flipSymbol_flipSymbol]
  · intro h
    rw [h, flipSymbol_flipSymbol]

variable [MeasurableSpace ι] {ν : Measure (ℤ → ι × ZMod 2)}

theorem map_flipAxis_subshift_compl [Fintype ι] [MeasurableSingletonClass ι]
    {o : ι → ZMod 2} (hν : ν (subshift o)ᶜ = 0) : ν.map flipAxis (subshift o)ᶜ = 0 := by
  rw [Measure.map_apply measurable_flipAxis (measurableSet_subshift o).compl, Set.preimage_compl,
    preimage_flipAxis_subshift, hν]

theorem ergodic_map_flipAxis (h : Ergodic (shift 1) ν) : Ergodic (shift 1) (ν.map flipAxis) :=
  (⟨measurable_flipAxis, rfl⟩ : MeasurePreserving flipAxis ν (ν.map flipAxis))
    |>.ergodic_of_ergodic_semiconj h (measurable_shift 1) fun _ => rfl

theorem RectangularIFS.isGibbs_potential₂_map_flipAxis [Fintype ι] [MeasurableSingletonClass ι]
    (S : RectangularIFS ι) {s : ℝ} (hg : IsGibbs S.o (S.potential₁ s) ν) :
    IsGibbs S.o (S.potential₂ s) (ν.map flipAxis) := by
  obtain ⟨P, C, hC, hb⟩ := hg
  refine ⟨P, C, hC, fun y hy n hn => ?_⟩
  have hy' : flipAxis y ∈ subshift S.o := by
    rw [← Set.mem_preimage, preimage_flipAxis_subshift]
    exact hy
  have hcyl : (ν.map flipAxis).real (cylinder fun k : Fin n => y k) =
      ν.real (cylinder fun k : Fin n => flipAxis y k) := by
    rw [map_measureReal_apply measurable_flipAxis (measurableSet_cylinder _),
      preimage_flipAxis_cylinder]
    rfl
  rw [hcyl]
  exact hb (flipAxis y) hy' n hn

end Flip

end FractalGeometry
