import Mathlib
import FractalGeometry.Probability.Branching.Descendants
import FractalGeometry.Probability.Branching.Law
import FractalGeometry.Probability.Branching.Process
import FractalGeometry.Probability.Branching.Survival
import FractalGeometry.Probability.Branching.Words

namespace FractalGeometry.Probability.Branching

open Filter Topology MeasureTheory

open scoped ENNReal

variable {A : Law} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.arity) → Ω → Bool}

omit [MeasurableSpace Ω] in

theorem exists_retained_hasInfiniteDescent_of_mem_survival {ω : Ω} (hs : ω ∈ survival X)
    (L : ℕ) :
    ∃ w : Word A, w.length = L ∧ Retained X ω w ∧ HasInfiniteDescentBelow X ω w := by
  classical
  have hdesc : HasInfiniteDescentBelow X ω [] :=
    (hasInfiniteDescentBelow_nil_iff_mem_survival X ω).mpr hs
  choose u hu using fun n => hdesc (L + n)
  let f : ℕ → {w : Word A // w.length = L} := fun n =>
    ⟨(wordOfDigits (u n)).take L, by
      rw [List.length_take, length_wordOfDigits]
      exact Nat.min_eq_left (Nat.le_add_right L n)⟩
  have : Finite {w : Word A // w.length = L} := (List.finite_length_eq _ L).to_subtype
  obtain ⟨w₀, hw₀⟩ := Finite.exists_infinite_fiber f
  have hinf : (f ⁻¹' {w₀}).Infinite := Set.infinite_coe_iff.mp hw₀
  refine ⟨w₀.1, w₀.2, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := hinf.nonempty
    have hn' : (wordOfDigits (u n)).take L = w₀.1 :=
      congrArg Subtype.val (show f n = w₀ from hn)
    have hret : RetainedBelow X ω [] (wordOfDigits (u n)) := hu n
    have := hret.take L
    rw [← retained_iff_retainedBelow_nil, hn'] at this
    exact this
  · intro d
    obtain ⟨n, hn, hdn⟩ := not_bddAbove_iff.mp hinf.not_bddAbove d
    have hn' : (wordOfDigits (u n)).take L = w₀.1 :=
      congrArg Subtype.val (show f n = w₀ from hn)
    set rest := (wordOfDigits (u n)).drop L with hrest
    have hsplit : wordOfDigits (u n) = w₀.1 ++ rest := by
      rw [← hn', hrest, List.take_append_drop]
    have hret : RetainedBelow X ω [] (w₀.1 ++ rest) := by
      rw [← hsplit]
      exact hu n
    have hbelow : RetainedBelow X ω w₀.1 rest := by
      have := (retainedBelow_append_iff X ω [] _ _).mp hret
      simpa using this.2
    have hlen : (rest.take d).length = d := by
      rw [List.length_take, hrest, List.length_drop, length_wordOfDigits]
      omega
    refine ⟨fun i => (rest.take d).get (Fin.cast hlen.symm i), ?_⟩
    have hw : wordOfDigits (fun i : Fin d => (rest.take d).get (Fin.cast hlen.symm i)) =
        rest.take d := by
      apply List.ext_getElem
      · simp [hlen]
      · intro i h1 h2
        simp [wordOfDigits]
    rw [hw]
    exact hbelow.take d

omit [MeasurableSpace Ω] in

theorem one_le_descendantCountBelow_of_mem_survival {ω : Ω} (hs : ω ∈ survival X) (j : ℕ) :
    1 ≤ descendantCountBelow X [] j ω := by
  classical
  obtain ⟨w, hwj, hret⟩ := hs j
  set u : DigitWord A j := fun l => w.get (Fin.cast hwj.symm l) with hu
  have hw : wordOfDigits u = w := by
    apply List.ext_getElem
    · simp [hwj]
    · intro i h1 h2
      simp [wordOfDigits, hu]
  unfold descendantCountBelow
  refine Finset.card_pos.mpr ⟨u, ?_⟩
  rw [Set.mem_toFinset, Set.mem_ofPred_eq, hw, retainedBelow_nil_iff_retained]
  exact hret

end FractalGeometry.Probability.Branching
