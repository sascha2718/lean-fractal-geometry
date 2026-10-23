import Mathlib
import FractalGeometry.Probability.Branching.Process
import FractalGeometry.Probability.Branching.IndependentVectors

namespace FractalGeometry.Probability.Branching

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {A : Law} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → Fin A.arity → Ω → Bool}

noncomputable def totalOffspring (X : Word A → Fin A.arity → Ω → Bool)
    (w : Word A) (ω : Ω) : ℕ :=
  ∑ i, if X w i ω = true then 1 else 0

theorem measurable_totalOffspring (hX : IsPercolation P X) (w : Word A) :
    Measurable (totalOffspring X w) := by
  unfold totalOffspring
  exact Finset.measurable_fun_sum _ fun i _ =>
    measurable_const.ite ((hX.measurable w i) (measurableSet_singleton true)) measurable_const

theorem totalOffspring_le (X : Word A → Fin A.arity → Ω → Bool)
    (w : Word A) (ω : Ω) : totalOffspring X w ω ≤ A.arity := by
  unfold totalOffspring
  calc ∑ i, (if X w i ω = true then 1 else 0 : ℕ) ≤ ∑ _i : Fin A.arity, 1 :=
      Finset.sum_le_sum fun i _ => by split <;> omega
    _ = A.arity := by simp

theorem integral_totalOffspring (hX : IsPercolation P X) (w : Word A) :
    ∫ ω, (totalOffspring X w ω : ℝ) ∂P = A.m := by
  let := hX.toIsProbabilityMeasure
  have hm (i : Fin A.arity) : MeasurableSet {ω | X w i ω = true} :=
    (hX.measurable w i) (measurableSet_singleton true)
  have heq : (fun ω => (totalOffspring X w ω : ℝ)) =
      fun ω => ∑ i, {ω | X w i ω = true}.indicator (fun _ => (1 : ℝ)) ω := by
    funext ω
    simp [totalOffspring, Set.indicator_apply]
  rw [heq, integral_finsetSum]
  · simp only [integral_indicator (hm _), integral_const, smul_eq_mul, mul_one, Law.m]
    apply Finset.sum_congr rfl
    intro i _
    rw [measureReal_def, Measure.restrict_apply_univ, hX.prob,
      ENNReal.toReal_ofReal (A.p_nonneg i)]
  · intro i _
    exact (integrable_const (1 : ℝ)).indicator (hm i)

theorem iIndepFun_totalOffspring_of_injective (hX : IsPercolation P X)
    {I : Type*} (roots : I → Word A) (hr : Function.Injective roots) :
    iIndepFun (fun c ω => (totalOffspring X (roots c) ω : ℝ)) P := by
  let := hX.toIsProbabilityMeasure
  have hraw : iIndepFun (fun q : (i : I) × Fin A.arity => X (roots q.1) q.2) P := by
    apply hX.indep.precomp (g := fun q : (i : I) × Fin A.arity => (roots q.1, q.2))
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    have hij : i = j := hr (congrArg Prod.fst h)
    have hab : a = b := congrArg Prod.snd h
    subst j; subst b; rfl
  have hvec := iIndepFun_curry_of_uncurry (fun i a => hX.measurable (roots i) a) hraw
  have hsum := hvec.comp
    (fun _ (z : Fin A.arity → Bool) => (∑ i, if z i = true then 1 else 0 : ℕ))
    (fun _ => measurable_of_finite _)
  exact hsum.comp (fun _ (n : ℕ) => (n : ℝ)) (fun _ => measurable_from_nat)

end FractalGeometry.Probability.Branching
