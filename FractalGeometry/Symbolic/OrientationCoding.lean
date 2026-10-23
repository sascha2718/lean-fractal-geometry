import Mathlib
import GeometricMeasureTheory.Box.ModifiedBox
import FractalGeometry.SelfAffine.Rectangular.Orientation

open GeometricMeasureTheory

namespace FractalGeometry

variable {ι : Type*} (o : ι → ZMod 2)

def tau (x : ℤ → ι) : ℤ → ι × ZMod 2 := fun n => (x n, eps o x n)

def omega (x : ℤ → ι) : ℤ → ι × ZMod 2 := fun n => (x n, eps o x n + 1)

variable {o}

@[simp] theorem tau_apply (x : ℤ → ι) (n : ℤ) : tau o x n = (x n, eps o x n) := rfl

@[simp] theorem omega_apply (x : ℤ → ι) (n : ℤ) : omega o x n = (x n, eps o x n + 1) := rfl

end FractalGeometry
