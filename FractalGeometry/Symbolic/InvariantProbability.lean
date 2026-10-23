import Mathlib
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.Shift
import FractalGeometry.Symbolic.WordAverages
import FractalGeometry.Symbolic.WordIntegrals

namespace FractalGeometry

open Filter MeasureTheory Topology

open scoped BoundedContinuousFunction

section Continuity

variable {ι : Type*} [Fintype ι] [TopologicalSpace ι] [DiscreteTopology ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

omit [Fintype ι] [DiscreteTopology ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in

theorem continuous_shift (n : ℤ) : Continuous (shift n : (ℤ → ι) → ℤ → ι) :=
  continuous_pi fun k => continuous_apply (n + k)

omit [Fintype ι] [DiscreteTopology ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in

theorem continuous_block (n : ℕ) : Continuous (block n : (ℤ → ι) → Fin n → ι) :=
  continuous_pi fun k => continuous_apply (k : ℤ)

theorem continuous_integral_comp_block {n : ℕ} (F : (Fin n → ι) → ℝ) :
    Continuous fun ν : ProbabilityMeasure (ℤ → ι) =>
      ∫ x, F (block n x) ∂(ν : Measure (ℤ → ι)) :=
  ProbabilityMeasure.continuous_integral_continuousMap
    (⟨fun x => F (block n x), continuous_of_discreteTopology.comp (continuous_block n)⟩ :
      C(ℤ → ι, ℝ))

theorem continuous_measureReal_cylinder {n : ℕ} (w : Fin n → ι) :
    Continuous fun ν : ProbabilityMeasure (ℤ → ι) => (ν : Measure (ℤ → ι)).real (cylinder w) := by
  classical
  refine (continuous_integral_comp_block fun v : Fin n → ι => if v = w then (1 : ℝ) else 0).congr
    fun ν => ?_
  exact (integral_comp_block_eq_sum (ν : Measure (ℤ → ι))
    fun v : Fin n → ι => if v = w then (1 : ℝ) else 0).trans (by simp)

end Continuity

section Invariant

variable {ι : Type*} [Fintype ι] [TopologicalSpace ι] [DiscreteTopology ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

variable (ι) in

def InvariantMeasures : Set (ProbabilityMeasure (ℤ → ι)) :=
  {ν | MeasurePreserving (shift 1) (ν : Measure (ℤ → ι)) (ν : Measure (ℤ → ι))}

theorem mem_invariantMeasures_iff {ν : ProbabilityMeasure (ℤ → ι)} :
    ν ∈ InvariantMeasures ι ↔ ∀ f : (ℤ → ι) →ᵇ ℝ,
      ∫ x, f (shift 1 x) ∂(ν : Measure (ℤ → ι)) = ∫ x, f x ∂(ν : Measure (ℤ → ι)) := by
  constructor
  · intro hν f
    have h := integral_comp_shift hν 1 (F := fun x => f x) f.continuous.measurable
    rwa [Nat.cast_one] at h
  · intro h
    refine ⟨measurable_shift 1, ?_⟩
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    rw [integral_map (measurable_shift 1).aemeasurable
      f.continuous.measurable.aestronglyMeasurable]
    exact h f

theorem isClosed_invariantMeasures : IsClosed (InvariantMeasures ι) := by
  have he : InvariantMeasures ι = ⋂ f : (ℤ → ι) →ᵇ ℝ,
      {ν : ProbabilityMeasure (ℤ → ι) |
        ∫ x, f (shift 1 x) ∂(ν : Measure (ℤ → ι)) = ∫ x, f x ∂(ν : Measure (ℤ → ι))} := by
    ext ν
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact mem_invariantMeasures_iff
  rw [he]
  refine isClosed_iInter fun f => isClosed_eq ?_ ?_
  · exact ProbabilityMeasure.continuous_integral_continuousMap
      (⟨fun x => f (shift 1 x), f.continuous.comp (continuous_shift 1)⟩ : C(ℤ → ι, ℝ))
  · exact ProbabilityMeasure.continuous_integral_continuousMap
      (⟨fun x => f x, f.continuous⟩ : C(ℤ → ι, ℝ))

end Invariant

section Infimum

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem subadditive_integral_futureWord {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) {G : List ι → ℝ}
    (hsub : ∀ w w', G (w ++ w') ≤ G w + G w') :
    Subadditive fun n : ℕ => ∫ x, G (futureWord x n) ∂μ := by
  intro m n
  have hint : Integrable (fun x => G (futureWord (shift m x) n)) μ :=
    (measurePreserving_shift_natCast hμ m).integrable_comp_of_integrable
      (integrable_comp_futureWord G n)
  calc ∫ x, G (futureWord x (m + n)) ∂μ
      ≤ ∫ x, (G (futureWord x m) + G (futureWord (shift m x) n)) ∂μ :=
        integral_mono (integrable_comp_futureWord G _)
          ((integrable_comp_futureWord G m).add hint) fun x => by
            rw [futureWord_add]; exact hsub _ _
    _ = ∫ x, G (futureWord x m) ∂μ + ∫ x, G (futureWord x n) ∂μ := by
        rw [integral_add (integrable_comp_futureWord G m) hint,
          integral_comp_shift hμ m (measurable_comp_futureWord G n)]

end Infimum

end FractalGeometry
