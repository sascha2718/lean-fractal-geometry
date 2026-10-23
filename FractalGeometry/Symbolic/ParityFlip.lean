import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.Symbolic.OrientationCoding
import FractalGeometry.Symbolic.ParityShift

open FractalGeometry.Ergodic

namespace FractalGeometry

open Filter Topology MeasureTheory

section FlipSymbol

variable {ι : Type*} {o : ι → ZMod 2} {n : ℕ}

def flipSymbol (p : ι × ZMod 2) : ι × ZMod 2 := (p.1, p.2 + 1)

@[simp] theorem flipSymbol_flipSymbol (p : ι × ZMod 2) : flipSymbol (flipSymbol p) = p := by
  refine Prod.ext rfl ?_
  change p.2 + 1 + 1 = p.2
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem trans_flipSymbol_iff (p q : ι × ZMod 2) :
    Trans o (flipSymbol p) (flipSymbol q) ↔ Trans o p q := by
  change q.2 + 1 = p.2 + 1 + o p.1 ↔ q.2 = p.2 + o p.1
  generalize o p.1 = a
  generalize p.2 = c
  generalize q.2 = c'
  revert a c c'; decide

end FlipSymbol

section FlipAxis

variable {ι : Type*}

def flipAxis (y : ℤ → ι × ZMod 2) : ℤ → ι × ZMod 2 := fun n => flipSymbol (y n)

theorem flipAxis_tau (o : ι → ZMod 2) (x : ℤ → ι) : flipAxis (tau o x) = omega o x := rfl

theorem flipAxis_omega (o : ι → ZMod 2) (x : ℤ → ι) : flipAxis (omega o x) = tau o x :=
  funext fun n => flipSymbol_flipSymbol (tau o x n)

theorem measurable_flipAxis [MeasurableSpace ι] :
    Measurable (flipAxis : (ℤ → ι × ZMod 2) → ℤ → ι × ZMod 2) :=
  Measurable.of_eval fun n => (measurable_fst.comp (measurable_pi_apply n)).prodMk
    ((measurable_snd.comp (measurable_pi_apply n)).add_const 1)

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

end FlipAxis

end FractalGeometry
