module

/-
Measurability of the codings and of the canonical projections, for the push-forwards of
`sec:two_sided_shift_space` and `sec:dimension_of_projections`. The alphabet carries a
discrete measurable structure and the sequence spaces carry the product `σ`-algebra, which is
the Borel `σ`-algebra of the product topology.

* `measurable_eps`, `measurable_tau`, `measurable_omega`: the orientation cocycle and the
  codings `τ`, `ω` are measurable.
* `System.Bounds.measurable_projBar`, `System.Bounds.measurable_proj`: the canonical
  projections `\overline{π}` and `π` are measurable.
-/
public import BoxLike.Projection
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.MeasurableSpace.Instances

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology

variable {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]

/-- The orientation cocycle `𝐢 ↦ ε_n(𝐢)` is measurable: it depends on finitely many
coordinates. -/
theorem measurable_eps (o : ι → ZMod 2) (n : ℤ) : Measurable fun x : ℤ → ι => eps o x n := by
  rcases n with n | n
  · change Measurable fun x : ℤ → ι => ∑ j ∈ Finset.range n, o (x j)
    exact Finset.measurable_sum _ fun j _ =>
      (Measurable.of_discrete (f := o)).comp (measurable_pi_apply _)
  · change Measurable fun x : ℤ → ι => ∑ j ∈ Finset.range (n + 1), o (x (-(j + 1 : ℤ)))
    exact Finset.measurable_sum _ fun j _ =>
      (Measurable.of_discrete (f := o)).comp (measurable_pi_apply _)

/-- The coding `τ` is measurable. -/
theorem measurable_tau (o : ι → ZMod 2) : Measurable (tau o) :=
  measurable_pi_iff.2 fun n => (measurable_pi_apply n).prodMk (measurable_eps o n)

/-- The coding `ω` is measurable. -/
theorem measurable_omega (o : ι → ZMod 2) : Measurable (omega o) :=
  measurable_pi_iff.2 fun n =>
    (measurable_pi_apply n).prodMk ((measurable_eps o n).add_const 1)

namespace System

variable {S : System ι} {r M : ℝ}

/-- The derivative `g'_{𝐣|_k}` is a measurable function of `𝐣`. -/
theorem measurable_gDeriv_futureWord (S : System ι) (k : ℕ) :
    Measurable fun y : ℤ → ι × ZMod 2 => S.gDeriv (futureWord y k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : (fun y : ℤ → ι × ZMod 2 => S.gDeriv (futureWord y (k + 1))) =
        fun y => S.gDeriv (futureWord y k) * S.ratio (y k) := by
      funext y
      rw [futureWord_succ, gDeriv_append]
      simp
    rw [h]
    exact ih.mul ((Measurable.of_discrete (f := S.ratio)).comp (measurable_pi_apply _))

/-- The terms of the series defining `\overline{π}` are measurable. -/
theorem measurable_projBarTerm (S : System ι) (k : ℕ) :
    Measurable fun y : ℤ → ι × ZMod 2 => S.projBarTerm y k :=
  (S.measurable_gDeriv_futureWord k).mul
    ((Measurable.of_discrete (f := S.trans)).comp (measurable_pi_apply _))

/-- The canonical projection `\overline{π}` is measurable, as a pointwise limit of functions
of finitely many coordinates. -/
theorem Bounds.measurable_projBar (hS : S.Bounds r M) : Measurable S.projBar := by
  refine measurable_of_tendsto_metrizable
    (f := fun n y => ∑ k ∈ Finset.range n, S.projBarTerm y k)
    (fun n => Finset.measurable_sum _ fun k _ => S.measurable_projBarTerm k) ?_
  exact tendsto_pi_nhds.2 fun y => (hS.summable_projBarTerm y).hasSum.tendsto_sum_nat

/-- The canonical projection `π` is measurable. -/
theorem Bounds.measurable_proj (hS : S.Bounds r M) : Measurable S.proj :=
  (hS.measurable_projBar.comp (measurable_tau S.o)).prodMk
    (hS.measurable_projBar.comp (measurable_omega S.o))

end System

end BoxLike
