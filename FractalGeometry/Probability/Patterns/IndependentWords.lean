import Mathlib
import FractalGeometry.Probability.Patterns.Defs

namespace FractalGeometry.Probability.Patterns

open MeasureTheory ProbabilityTheory Metric

open scoped ENNReal

variable {ι X Ω : Type*} [MetricSpace X] [Fintype ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [MeasurableSpace Ω]

noncomputable def wordAt [Nonempty ι] (s : ℕ) {n : ℕ} (v : Word ι n) (j : ℕ) : ι :=
  if h : j - s < n ∧ s ≤ j then v ⟨j - s, h.1⟩ else Classical.arbitrary ι

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace Ω] in

theorem wordAt_apply [Nonempty ι] (s : ℕ) {n : ℕ} (v : Word ι n) (i : Fin n) :
    wordAt s v (s + i) = v i := by
  unfold wordAt
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 1
  ext
  simp

section IID

variable {p : Weights ι} {P : Measure Ω} {I : ℕ → Ω → ι} (hI : IsIIDProcess p P I)

include hI

theorem IsIIDProcess.measure_cylinder (S : Finset ℕ) (a : ℕ → ι) :
    P {ω | ∀ j ∈ S, I j ω = a j} = ∏ j ∈ S, ENNReal.ofReal (p.p (a j)) := by
  have h := hI.indep.measure_inter_preimage_eq_mul S (sets := fun j => {a j})
    (fun j _ => measurableSet_singleton _)
  have hset : {ω | ∀ j ∈ S, I j ω = a j} = ⋂ j ∈ S, I j ⁻¹' {a j} := by
    ext ω
    simp [Set.mem_iInter]
  rw [hset, h]
  exact Finset.prod_congr rfl fun j _ => hI.law j (a j)

end IID

end FractalGeometry.Probability.Patterns
