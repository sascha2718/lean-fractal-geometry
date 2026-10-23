import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.SelfAffine.Rectangular.Orientation
import FractalGeometry.Symbolic.OrientationCoding
import FractalGeometry.Symbolic.ParityShift

open FractalGeometry.Ergodic

namespace FractalGeometry

variable {ι : Type*} (o : ι → ZMod 2)

variable {o}

@[simp] theorem unCode_tau (x : ℤ → ι) : unCode (tau o x) = x := rfl

@[simp] theorem unCode_omega (x : ℤ → ι) : unCode (omega o x) = x := rfl

theorem omega_mem_subshift (x : ℤ → ι) : omega o x ∈ subshift o := fun n => by
  simp [Trans, eps_add_one, add_right_comm]

theorem range_tau : Set.range (tau o) = {y ∈ subshift o | (y 0).2 = 0} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨tau_mem_subshift x, by simp⟩
  · rintro ⟨hy, h0⟩
    refine ⟨unCode y, funext fun n => ?_⟩
    rw [tau_apply, unCode_apply, Prod.ext_iff]
    exact ⟨rfl, by rw [snd_eq_of_mem_subshift hy n, h0, zero_add]⟩

theorem range_omega : Set.range (omega o) = {y ∈ subshift o | (y 0).2 = 1} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨omega_mem_subshift x, by simp⟩
  · rintro ⟨hy, h0⟩
    refine ⟨unCode y, funext fun n => ?_⟩
    rw [omega_apply, unCode_apply, Prod.ext_iff]
    exact ⟨rfl, by rw [snd_eq_of_mem_subshift hy n, h0, add_comm]⟩

theorem range_tau_union_range_omega :
    Set.range (tau o) ∪ Set.range (omega o) = subshift o := by
  rw [range_tau, range_omega]
  ext y
  constructor
  · rintro (h | h) <;> exact h.1
  · intro hy
    have : (y 0).2 = 0 ∨ (y 0).2 = 1 := by
      generalize (y 0).2 = c
      revert c; decide
    exact this.imp (fun h => ⟨hy, h⟩) fun h => ⟨hy, h⟩

theorem disjoint_range_tau_range_omega :
    Disjoint (Set.range (tau o)) (Set.range (omega o)) := by
  rw [range_tau, range_omega, Set.disjoint_left]
  rintro y ⟨-, h0⟩ ⟨-, h1⟩
  rw [h0] at h1
  exact absurd h1 (by decide)

end FractalGeometry
