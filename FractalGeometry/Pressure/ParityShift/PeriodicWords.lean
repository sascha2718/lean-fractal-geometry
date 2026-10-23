import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.LinearCocycles.Monomial
import FractalGeometry.SelfAffine.Rectangular.Orientation
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.ParityShift
import FractalGeometry.Symbolic.PeriodicWords
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open Filter Topology MeasureTheory

section Words

variable {ι : Type*} (o : ι → ZMod 2) {n : ℕ}

def IsAdmissible (w : Fin n → ι × ZMod 2) : Prop :=
  ∀ (k : Fin n) (h : (k : ℕ) + 1 < n), Trans o (w k) (w ⟨k + 1, h⟩)

def IsCyclicAdmissible (w : Fin n → ι × ZMod 2) : Prop :=
  IsAdmissible o w ∧ ∀ h : 0 < n, Trans o (w ⟨n - 1, Nat.sub_lt h one_pos⟩) (w ⟨0, h⟩)

def codeFrom (c : ZMod 2) (x : ℤ → ι) : ℤ → ι × ZMod 2 := fun k => (x k, c + eps o x k)

theorem codeFrom_mem_subshift (c : ZMod 2) (x : ℤ → ι) : codeFrom o c x ∈ subshift o :=
  fun k => by simp [codeFrom, Trans, eps_add_one, add_assoc]

variable {o}

theorem isAdmissible_block {y : ℤ → ι × ZMod 2} (hy : y ∈ subshift o) (n : ℕ) :
    IsAdmissible o (block n y) := by
  intro k h
  have := hy (k : ℤ)
  simpa [block] using this

theorem IsAdmissible.exists_block_eq {w : Fin (n + 1) → ι × ZMod 2} (hw : IsAdmissible o w) :
    ∃ y ∈ subshift o, block (n + 1) y = w := by
  set x : ℤ → ι := extendWord fun k => (w k).1 with hx
  have hy := codeFrom_mem_subshift o (w 0).2 x
  refine ⟨codeFrom o (w 0).2 x, hy, ?_⟩
  have key : ∀ (k : ℕ) (hk : k < n + 1), codeFrom o (w 0).2 x k = w ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h0 : x 0 = (w 0).1 := extendWord_natCast (fun k => (w k).1) 0
      simp [codeFrom, h0]
    | succ k ih =>
      intro hk
      have hk' : k < n + 1 := by omega
      have h1 : x ((k + 1 : ℕ) : ℤ) = (w ⟨k + 1, hk⟩).1 :=
        extendWord_natCast (fun k => (w k).1) ⟨k + 1, hk⟩
      have h2 := hy (k : ℤ)
      rw [ih hk'] at h2
      have h3 := hw ⟨k, hk'⟩ hk
      refine Prod.ext ?_ ?_
      · simpa [codeFrom] using h1
      · rw [Nat.cast_succ]
        exact h2.trans h3.symm
  exact funext fun k => key k k.isLt

theorem IsCyclicAdmissible.isAdmissible {w : Fin n → ι × ZMod 2}
    (hw : IsCyclicAdmissible o w) : IsAdmissible o w := hw.1

theorem IsAdmissible.of_append {m : ℕ} {u : Fin m → ι × ZMod 2} {v : Fin n → ι × ZMod 2}
    (h : IsAdmissible o (Fin.append u v)) : IsAdmissible o u ∧ IsAdmissible o v := by
  constructor
  · intro k hk
    have h' := h (Fin.castAdd n k) (by simp; omega)
    rw [Fin.append_left] at h'
    have e : (⟨((Fin.castAdd n k : Fin (m + n)) : ℕ) + 1, by simp; omega⟩ : Fin (m + n)) =
        Fin.castAdd n ⟨k + 1, hk⟩ := rfl
    rw [e, Fin.append_left] at h'
    exact h'
  · intro k hk
    have h' := h (Fin.natAdd m k) (by simp; omega)
    rw [Fin.append_right] at h'
    have e : (⟨((Fin.natAdd m k : Fin (m + n)) : ℕ) + 1, by simp; omega⟩ : Fin (m + n)) =
        Fin.natAdd m ⟨k + 1, hk⟩ := rfl
    rw [e, Fin.append_right] at h'
    exact h'

theorem IsCyclicAdmissible.cons {w : Fin (n + 1) → ι × ZMod 2} (hw : IsAdmissible o w)
    {r : ι × ZMod 2} (h1 : Trans o r (w 0)) (h2 : Trans o (w (Fin.last n)) r) :
    IsCyclicAdmissible o (Fin.cons r w : Fin (n + 2) → ι × ZMod 2) := by
  refine ⟨fun k => ?_, fun _ => ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) k
    · intro h
      have e : (⟨((0 : Fin (n + 2)) : ℕ) + 1, h⟩ : Fin (n + 2)) = Fin.succ 0 := rfl
      rw [e, Fin.cons_zero, Fin.cons_succ]
      exact h1
    · intro h
      have hj : (j : ℕ) + 1 < n + 1 := by simpa using h
      have e : (⟨((Fin.succ j : Fin (n + 2)) : ℕ) + 1, h⟩ : Fin (n + 2)) =
          Fin.succ ⟨j + 1, hj⟩ := rfl
      rw [e, Fin.cons_succ, Fin.cons_succ]
      exact hw j hj
  · have e1 : (⟨n + 2 - 1, Nat.sub_lt (Nat.succ_pos _) one_pos⟩ : Fin (n + 2)) =
        Fin.succ (Fin.last n) := rfl
    have e2 : (⟨0, Nat.succ_pos _⟩ : Fin (n + 2)) = 0 := rfl
    rw [e1, e2, Fin.cons_zero, Fin.cons_succ]
    exact h2

theorem IsAdmissible.exists_closing (h0 : ∃ i, o i = 0) {w : Fin (n + 1) → ι × ZMod 2}
    (hw : IsAdmissible o w) : ∃ r, Trans o r (w 0) ∧ Trans o (w (Fin.last n)) r := by
  obtain ⟨y, hy, rfl⟩ := hw.exists_block_eq
  obtain ⟨i0, hi0⟩ := h0
  have key : ∃ j, o j = eps o (unCode y) ((n + 1 : ℕ) : ℤ) := by
    rcases zmod_two_cases (eps o (unCode y) ((n + 1 : ℕ) : ℤ)) with h | h
    · exact ⟨i0, hi0.trans h.symm⟩
    · have hne : eps o (unCode y) ((n + 1 : ℕ) : ℤ) ≠ 0 := by rw [h]; decide
      rw [eps_natCast] at hne
      obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      refine ⟨unCode y a, ?_⟩
      rw [h]
      exact (zmod_two_cases (o (unCode y a))).resolve_left ha
  obtain ⟨j, hj⟩ := key
  have hs := snd_eq_of_mem_subshift hy ((n + 1 : ℕ) : ℤ)
  refine ⟨(j, (y ((n + 1 : ℕ) : ℤ)).2), ?_, ?_⟩
  · change (y ((0 : Fin (n + 1)) : ℕ)).2 = (y ((n + 1 : ℕ) : ℤ)).2 + o j
    rw [hs, hj, add_assoc, CharTwo.add_self_eq_zero, add_zero, Fin.val_zero, Nat.cast_zero]
  · have h := hy (n : ℤ)
    rw [Nat.cast_succ]
    exact h

end Words

section Periodic

variable {ι : Type*} {o : ι → ZMod 2} {n : ℕ}

def periodicPoints (o : ι → ZMod 2) (n : ℕ) : Set (ℤ → ι × ZMod 2) :=
  {y | y ∈ subshift o ∧ shift n y = y}

theorem eq_of_shift_eq_of_block_eq {α : Type*} {y y' : ℤ → α}
    (hy : shift ((n + 1 : ℕ) : ℤ) y = y) (hy' : shift ((n + 1 : ℕ) : ℤ) y' = y')
    (h : block (n + 1) y = block (n + 1) y') : y = y' := by
  have key : ∀ z : ℤ → α, shift ((n + 1 : ℕ) : ℤ) z = z →
      ∀ k : ℤ, z k = z (k % ((n + 1 : ℕ) : ℤ)) := by
    intro z hz k
    have hstep : ∀ a : ℤ, z (((n + 1 : ℕ) : ℤ) + a) = z a := fun a => congrFun hz a
    have hmul : ∀ (j : ℤ) (a : ℤ), z (a + ((n + 1 : ℕ) : ℤ) * j) = z a := by
      intro j
      induction j using Int.induction_on with
      | zero => intro a; simp
      | succ j ih =>
        intro a
        rw [mul_add, mul_one, ← add_assoc, add_comm, hstep, ih]
      | pred j ih =>
        intro a
        have h1 := hstep (a + ((n + 1 : ℕ) : ℤ) * (-(j : ℤ) - 1))
        rw [← h1, ← ih a]
        congr 1
        ring
    have h2 := hmul (k / ((n + 1 : ℕ) : ℤ)) (k % ((n + 1 : ℕ) : ℤ))
    rw [Int.emod_add_mul_ediv] at h2
    exact h2
  funext k
  have hk0 : 0 ≤ k % ((n + 1 : ℕ) : ℤ) := Int.emod_nonneg _ (by positivity)
  have hk1 : k % ((n + 1 : ℕ) : ℤ) < ((n + 1 : ℕ) : ℤ) := Int.emod_lt_of_pos _ (by positivity)
  have hlt : (k % ((n + 1 : ℕ) : ℤ)).toNat < n + 1 := (Int.toNat_lt hk0).2 hk1
  have h3 := congrFun h ⟨_, hlt⟩
  simp only [block_apply, Int.toNat_of_nonneg hk0] at h3
  rw [key y hy k, key y' hy' k, h3]

theorem IsCyclicAdmissible.periodicExtension_mem_subshift {w : Fin (n + 1) → ι × ZMod 2}
    (hw : IsCyclicAdmissible o w) : periodicExtension w ∈ subshift o := by
  intro k
  have hN : (0 : ℤ) < ((n + 1 : ℕ) : ℤ) := by positivity
  have hk0 : 0 ≤ k % ((n + 1 : ℕ) : ℤ) := Int.emod_nonneg _ hN.ne'
  have hk1 : k % ((n + 1 : ℕ) : ℤ) < ((n + 1 : ℕ) : ℤ) := Int.emod_lt_of_pos _ hN
  have hsucc : (k + 1) % ((n + 1 : ℕ) : ℤ) =
      (k % ((n + 1 : ℕ) : ℤ) + 1) % ((n + 1 : ℕ) : ℤ) := (Int.emod_add_emod k _ 1).symm
  unfold periodicExtension
  rw [hsucc]
  generalize k % ((n + 1 : ℕ) : ℤ) = m at hk0 hk1
  lift m to ℕ using hk0
  have hm : m < n + 1 := by exact_mod_cast hk1
  rw [extendWord_natCast w ⟨m, hm⟩]
  by_cases hm' : m + 1 < n + 1
  · have h1 : ((m : ℤ) + 1) % ((n + 1 : ℕ) : ℤ) = ((m + 1 : ℕ) : ℤ) := by
      rw [Nat.cast_succ]
      exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hm')
    rw [h1, extendWord_natCast w ⟨m + 1, hm'⟩]
    exact hw.1 ⟨m, hm⟩ hm'
  · have hmn : m = n := by omega
    subst hmn
    have h1 : ((m : ℤ) + 1) % ((m + 1 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) := by
      rw [Nat.cast_succ, Int.emod_self, Nat.cast_zero]
    rw [h1, extendWord_natCast w ⟨0, Nat.succ_pos m⟩]
    exact hw.2 (Nat.succ_pos m)

theorem bijOn_block_periodicPoints (o : ι → ZMod 2) (n : ℕ) :
    Set.BijOn (block (n + 1)) (periodicPoints o (n + 1)) {w | IsCyclicAdmissible o w} := by
  refine ⟨?_, ?_, ?_⟩
  · rintro y ⟨hy, hper⟩
    refine ⟨isAdmissible_block hy _, fun _ => ?_⟩
    have h := hy ((n : ℕ) : ℤ)
    have h0 : y (((n : ℕ) : ℤ) + 1) = y 0 := by
      have := congrFun hper 0
      simpa [add_comm] using this
    rw [h0] at h
    simpa [block] using h
  · rintro y ⟨-, hy⟩ y' ⟨-, hy'⟩ h
    exact eq_of_shift_eq_of_block_eq hy hy' h
  · intro w hw
    exact ⟨periodicExtension w, ⟨hw.periodicExtension_mem_subshift, shift_periodicExtension w⟩,
      funext (periodicExtension_natCast w)⟩

end Periodic

section Gibbs

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {o : ι → ZMod 2} {φ : ι × ZMod 2 → ℝ} {ν : Measure (ℤ → ι × ZMod 2)}

open Classical in

theorem sum_measureReal_cylinder_of_isAdmissible [IsProbabilityMeasure ν]
    (hν : ν (subshift o)ᶜ = 0) (n : ℕ) :
    ∑ w : Fin n → ι × ZMod 2, (if IsAdmissible o w then ν.real (cylinder w) else 0) = 1 := by
  rw [← sum_measureReal_cylinder ν n]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs with hw
  · rfl
  · have hsub : cylinder w ⊆ (subshift o)ᶜ := fun y hy hys =>
      hw ((funext hy : block n y = w) ▸ isAdmissible_block hys n)
    rw [measureReal_def, measure_mono_null hsub hν, ENNReal.toReal_zero]

end Gibbs

end FractalGeometry
