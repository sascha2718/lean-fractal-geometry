import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.SelfAffine.Rectangular.Orientation
import FractalGeometry.Symbolic.OrientationCoding
import FractalGeometry.Symbolic.ParityShiftTopology
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

variable {ι : Type*} (o : ι → ZMod 2)

def Trans (p q : ι × ZMod 2) : Prop := q.2 = p.2 + o p.1

theorem exists_trans_trans (h0 : ∃ i, o i = 0) (h1 : ∃ i, o i = 1) (p q : ι × ZMod 2) :
    ∃ r, Trans o p r ∧ Trans o r q := by
  obtain ⟨i0, hi0⟩ := h0
  obtain ⟨i1, hi1⟩ := h1
  have key : ∀ d : ZMod 2, ∃ j, o j = d := by
    intro d
    have : d = 0 ∨ d = 1 := by revert d; decide
    rcases this with rfl | rfl
    exacts [⟨i0, hi0⟩, ⟨i1, hi1⟩]
  obtain ⟨j, hj⟩ := key (q.2 + (p.2 + o p.1))
  refine ⟨(j, p.2 + o p.1), rfl, ?_⟩
  change q.2 = p.2 + o p.1 + o j
  rw [hj]
  generalize o p.1 = a
  generalize p.2 = c
  generalize q.2 = c'
  revert a c c'; decide

def subshift : Set (ℤ → ι × ZMod 2) := {y | ∀ n, Trans o (y n) (y (n + 1))}

theorem mem_subshift {y : ℤ → ι × ZMod 2} :
    y ∈ subshift o ↔ ∀ n, (y (n + 1)).2 = (y n).2 + o (y n).1 := Iff.rfl

theorem shift_mem_subshift {y : ℤ → ι × ZMod 2} (hy : y ∈ subshift o) (n : ℤ) :
    shift n y ∈ subshift o := by
  intro k
  have h := hy (n + k)
  rw [mem_subshift] at hy
  simpa [Trans, add_assoc] using hy (n + k)

def unCode (y : ℤ → ι × ZMod 2) : ℤ → ι := fun n => (y n).1

variable {o}

@[simp] theorem unCode_apply (y : ℤ → ι × ZMod 2) (n : ℤ) : unCode y n = (y n).1 := rfl

theorem tau_mem_subshift (x : ℤ → ι) : tau o x ∈ subshift o := fun n => by
  simp [Trans, eps_add_one]

theorem snd_eq_of_mem_subshift {y : ℤ → ι × ZMod 2} (hy : y ∈ subshift o) (n : ℤ) :
    (y n).2 = (y 0).2 + eps o (unCode y) n := by
  have h : (fun n => (y 0).2 + (y n).2) = eps o (unCode y) := by
    apply eq_eps_of_succ
    · exact CharTwo.add_self_eq_zero _
    · intro m
      rw [mem_subshift] at hy
      rw [hy m, unCode_apply, add_assoc]
  rw [← h, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

end FractalGeometry
