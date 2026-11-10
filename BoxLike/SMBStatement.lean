module

/-
The statement of the Shannon–McMillan–Breiman theorem for the two-sided shift over a finite
alphabet, as `sec:entropies` uses it before `thm:feng_entropy_kolmogorov_sinai` and as the proof
of `thm:main2` uses it for its typical words. This module only states the theorem; the library
proves it in its own module. It is a result to be proved, not a literature hypothesis: a
numbered result in `Solution` never takes it as a premise.

* `ShannonMcMillanBreimanStatement`: for an ergodic shift-invariant probability measure `μ` on
  `ℤ → α`, `-n⁻¹ log μ([x_0 ⋯ x_{n-1}]) → h(μ)` for `μ`-almost every `x`.
-/
public import BoxLike.Entropy
public import Mathlib.Dynamics.Ergodic.Ergodic

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology

universe u

/-- The Shannon–McMillan–Breiman theorem for the two-sided shift over a finite alphabet in the
universe `u` (`sec:entropies`): for every ergodic shift-invariant probability measure `μ`,
`-n⁻¹ log μ(𝒫_0^{n-1}(x)) → h(μ)` for `μ`-almost every `x`, where `𝒫_0^{n-1}(x)` is the
cylinder of `x_0 ⋯ x_{n-1}` and `h(μ)` is the entropy rate `entropy μ`. -/
def ShannonMcMillanBreimanStatement : Prop :=
  ∀ (α : Type u) [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ], Ergodic (shift 1) μ →
      ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => -Real.log (μ.real (cylinder (block n x))) / n) atTop
        (𝓝 (entropy μ))

end BoxLike
