import Mathlib
import FractalGeometry.Probability.Branching.Configuration
import FractalGeometry.Probability.Branching.Descendants
import FractalGeometry.Probability.Branching.IdenticalLaws
import FractalGeometry.Probability.Branching.Law
import FractalGeometry.Probability.Branching.Process
import FractalGeometry.Probability.Branching.Survival
import FractalGeometry.Probability.Branching.SurvivalDescendants
import FractalGeometry.Probability.Branching.Words

namespace FractalGeometry.Probability.Branching

open Filter MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {A : Law} {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
  {X : Word A -> (Fin A.arity) -> Omega -> Bool}

omit [MeasurableSpace Omega] in

theorem descendantCountBelow_nil_pos_mono
    (X : Word A -> (Fin A.arity) -> Omega -> Bool)
    {j k : Nat} (hjk : j <= k) (omega : Omega)
    (hk : 0 < descendantCountBelow X [] k omega) :
    0 < descendantCountBelow X [] j omega := by
  classical
  unfold descendantCountBelow at hk ⊢
  rw [Finset.card_pos] at hk ⊢
  obtain ⟨u, hu⟩ := hk
  simp only [Set.mem_toFinset, Set.mem_ofPred_eq] at hu ⊢
  let u' : DigitWord A j := Fin.take j hjk u
  refine ⟨u', ?_⟩
  simp only [Set.mem_toFinset, Set.mem_ofPred_eq]
  have htake := hu.take j
  have hword : wordOfDigits u' = (wordOfDigits u).take j := by
    exact Fin.ofFn_take_eq_take_ofFn hjk u
  rw [hword]
  exact htake

omit [MeasurableSpace Omega] in

theorem survival_eq_iInter_descendantCountBelow_nil_pos
    (X : Word A -> (Fin A.arity) -> Omega -> Bool) :
    survival X = ⋂ L : Nat, {omega | 0 < descendantCountBelow X [] L omega} := by
  ext omega
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · intro hs L
    exact (one_le_descendantCountBelow_of_mem_survival (X := X) hs L)
  · intro h L
    have hL := h L
    unfold descendantCountBelow at hL
    rw [Finset.card_pos] at hL
    obtain ⟨u, hu⟩ := hL
    simp only [Set.mem_toFinset, Set.mem_ofPred_eq] at hu
    refine ⟨wordOfDigits u, by simp [wordOfDigits], ?_⟩
    exact (retainedBelow_nil_iff_retained X omega (wordOfDigits u)).mp hu

theorem measurableSet_descendantCountBelow_nil_pos (hX : IsPercolation P X) (L : Nat) :
    MeasurableSet {omega | 0 < descendantCountBelow X [] L omega} := by
  have hnatmeas : Measurable (descendantCountBelow X [] L) := by
    rw [show descendantCountBelow X [] L =
        fun omega => descendantCountConfig (config X omega) [] L by
      funext omega; exact descendantCountBelow_eq_config [] L omega]
    exact (measurable_descendantCountConfig [] L).comp (measurable_config hX)
  exact measurableSet_lt measurable_const hnatmeas

end FractalGeometry.Probability.Branching
