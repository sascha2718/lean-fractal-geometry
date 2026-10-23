import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Pressure.ParityShift.FiniteGibbsBounds
import FractalGeometry.Pressure.ParityShift.SymbolicMetric
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.InvariantProbability
import FractalGeometry.Symbolic.ParityShift
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology Set

section Clopen

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

theorem continuous_measureReal_of_isClopen {U : Set X} (hU : IsClopen U) :
    Continuous fun ν : ProbabilityMeasure X => (ν : Measure X).real U := by
  refine (ProbabilityMeasure.continuous_integral_continuousMap
    (⟨U.indicator 1, hU.continuous_indicator continuous_const⟩ : C(X, ℝ))).congr fun ν => ?_
  exact integral_indicator_one hU.isOpen.measurableSet

end Clopen

section Closed

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {o : ι → ZMod 2}

variable (o) in

def notTransSet (k : ℤ) : Set (ℤ → ι × ZMod 2) := {y | ¬ Trans o (y k) (y (k + 1))}

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in

theorem compl_subshift_eq_iUnion : (subshift o)ᶜ = ⋃ k : ℤ, notTransSet o k := by
  ext y
  simp [subshift, notTransSet]

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in

theorem isClopen_notTransSet [TopologicalSpace ι] [DiscreteTopology ι] (k : ℤ) :
    IsClopen (notTransSet o k) := by
  have hc : Continuous fun y : ℤ → ι × ZMod 2 => (y k, y (k + 1)) :=
    (continuous_apply k).prodMk (continuous_apply (k + 1))
  exact (isClopen_discrete {p : (ι × ZMod 2) × (ι × ZMod 2) | ¬ Trans o p.1 p.2}).preimage hc

variable [TopologicalSpace ι] [DiscreteTopology ι]

theorem isClosed_setOf_carried :
    IsClosed {ν : ProbabilityMeasure (ℤ → ι × ZMod 2) | (ν : Measure _) (subshift o)ᶜ = 0} := by
  have he : {ν : ProbabilityMeasure (ℤ → ι × ZMod 2) | (ν : Measure _) (subshift o)ᶜ = 0} =
      ⋂ k : ℤ, {ν : ProbabilityMeasure (ℤ → ι × ZMod 2) |
        (ν : Measure _).real (notTransSet o k) = 0} := by
    ext ν
    simp only [mem_ofPred_eq, mem_iInter, compl_subshift_eq_iUnion, measure_iUnion_null_iff]
    exact forall_congr' fun k => (measureReal_eq_zero_iff (measure_ne_top _ _)).symm
  rw [he]
  exact isClosed_iInter fun k =>
    isClosed_eq (continuous_measureReal_of_isClopen (isClopen_notTransSet k)) continuous_const

theorem isClosed_setOf_gibbsUpTo (f : (ℤ → ι × ZMod 2) → ℝ) (P C : ℝ) (N : ℕ) :
    IsClosed {ν : ProbabilityMeasure (ℤ → ι × ZMod 2) | GibbsUpTo o f ν P C N} := by
  simp only [GibbsUpTo, ofPred_and, ofPred_forall]
  refine isClosed_const.inter (isClosed_iInter fun y => isClosed_iInter fun _ =>
    isClosed_iInter fun n => isClosed_iInter fun _ => isClosed_iInter fun _ => ?_)
  exact (isClosed_le continuous_const (continuous_measureReal_cylinder _)).inter
    (isClosed_le (continuous_measureReal_cylinder _) continuous_const)

end Closed

section Limit

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {o : ι → ZMod 2} {f : (ℤ → ι × ZMod 2) → ℝ} {ν : Measure (ℤ → ι × ZMod 2)} {P C : ℝ}

omit [Fintype ι] [MeasurableSingletonClass ι] in

theorem GibbsUpTo.mono {M N : ℕ} (h : GibbsUpTo o f ν P C N) (hMN : M ≤ N) :
    GibbsUpTo o f ν P C M :=
  ⟨h.1, fun y hy n hn hnM => h.2 y hy n hn (hnM.trans hMN)⟩

theorem exists_isGibbsPotential_of_forall_gibbsUpTo
    (h : ∀ N : ℕ, ∃ ν : Measure (ℤ → ι × ZMod 2), IsProbabilityMeasure ν ∧
      MeasurePreserving (shift 1) ν ν ∧ ν (subshift o)ᶜ = 0 ∧ GibbsUpTo o f ν P C N) :
    ∃ ν : Measure (ℤ → ι × ZMod 2), IsProbabilityMeasure ν ∧ MeasurePreserving (shift 1) ν ν ∧
      ν (subshift o)ᶜ = 0 ∧ IsGibbsPotential o f ν P C := by
  let : TopologicalSpace ι := ⊥
  have : DiscreteTopology ι := ⟨rfl⟩
  have : BorelSpace (ι × ZMod 2) := inferInstance
  have : BorelSpace (ℤ → ι × ZMod 2) := inferInstance
  set K : ℕ → Set (ProbabilityMeasure (ℤ → ι × ZMod 2)) := fun N =>
    InvariantMeasures (ι × ZMod 2) ∩
      ({ν | (ν : Measure _) (subshift o)ᶜ = 0} ∩ {ν | GibbsUpTo o f ν P C N}) with hK
  have hclosed : ∀ N, IsClosed (K N) := fun N =>
    isClosed_invariantMeasures.inter
      (isClosed_setOf_carried.inter (isClosed_setOf_gibbsUpTo f P C N))
  have hmono : ∀ N, K (N + 1) ⊆ K N := fun N ν hν =>
    ⟨hν.1, hν.2.1, GibbsUpTo.mono hν.2.2 N.le_succ⟩
  have hne : ∀ N, (K N).Nonempty := fun N => by
    obtain ⟨ν, hp, hinv, hs, hg⟩ := h N
    exact ⟨⟨ν, hp⟩, hinv, hs, hg⟩
  obtain ⟨ν, hν⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hmono hne
    (hclosed 0).isCompact hclosed
  rw [mem_iInter] at hν
  exact ⟨ν, inferInstance, (hν 0).1, (hν 0).2.1,
    isGibbsPotential_iff_forall_gibbsUpTo.2 fun N => (hν N).2.2⟩

end Limit

end FractalGeometry
