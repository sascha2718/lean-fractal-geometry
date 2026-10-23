import Mathlib
import FractalGeometry.Symbolic.Shift

namespace FractalGeometry

open Filter Topology MeasureTheory

section Words

variable {ι : Type*} (o : ι → ZMod 2) {n : ℕ}

def extendWord {α : Type*} (w : Fin (n + 1) → α) : ℤ → α :=
  fun k => w (Fin.ofNat (n + 1) k.toNat)

theorem extendWord_natCast {α : Type*} (w : Fin (n + 1) → α) (k : Fin (n + 1)) :
    extendWord w (k : ℤ) = w k := by
  simp [extendWord]

variable {o}

end Words

section Periodic

variable {ι : Type*} {o : ι → ZMod 2} {n : ℕ}

def periodicExtension {α : Type*} (w : Fin (n + 1) → α) : ℤ → α := fun k =>
  extendWord w (k % ((n + 1 : ℕ) : ℤ))

theorem periodicExtension_natCast {α : Type*} (w : Fin (n + 1) → α) (k : Fin (n + 1)) :
    periodicExtension w (k : ℤ) = w k := by
  have h : ((k : ℕ) : ℤ) % ((n + 1 : ℕ) : ℤ) = (k : ℕ) :=
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast k.isLt)
  rw [periodicExtension, h, extendWord_natCast]

theorem shift_periodicExtension {α : Type*} (w : Fin (n + 1) → α) :
    shift ((n + 1 : ℕ) : ℤ) (periodicExtension w) = periodicExtension w := by
  funext k
  simp only [shift_apply, periodicExtension, Int.add_emod_left]

end Periodic

end FractalGeometry
