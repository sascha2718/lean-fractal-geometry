module

/-
The entropy threshold case of the proof of `thm:main2` in `sec:dimension_result_proof`: when
`#W_n ≤ |b_n|⁻¹`, "the conditional entropy is
`H_{ν_n}(𝒫 | \widehat{ξ_1^⊥}) = log #W_n + log |b_n| dim((proj_y ∘ π_n)_*ν_n) = 0`. Further,
since `ξ_2` refines `ξ_1^⊥`, we obtain `h_2(ν_n) = 0`." In the notation of these docstrings,
`q_{y,n} = 0` and `0 ≤ q_n ≤ q_{y,n}`. The inequality `q_n ≤ q_{y,n}` is the monotonicity of the
conditional entropy under refinement: the atom `ξ_2(𝐢)` of the planar point lies in the atom
`ξ_1^⊥(𝐢)` of the vertical coordinate, so `\widehat{ξ_1^⊥} ⊆ \widehat{ξ_2}`, and the conditional
Jensen inequality for the concave function `η(t) = -t log t` and the tower property of the
conditional expectations give `H(𝒫 | \widehat{ξ_2}) ≤ H(𝒫 | \widehat{ξ_1^⊥})`.

* `saturated_anti`: a finer partition has a larger `σ`-algebra of unions of atoms.
* `condEntropy_nonneg`, `condEntropy_le_of_subset`: `H_μ(𝒫 | \widehat{ξ}) ≥ 0`, and the
  monotonicity of the conditional entropy under refinement.
* `System.dimEntropy_two_le_condEntropy_xiPerp`: `q_n = h_2 ≤ H(𝒫 | \widehat{ξ_1^⊥})` for every
  system and every finite measure.
* `System.IsHomDiag.condEntropy_xiPerp_eq_zero_of_le`,
  `System.IsHomDiag.dimEntropy_two_eq_zero_of_le`: `q_{y,n} = 0` and `q_n = 0` when
  `log #W_n ≤ -log |b_n|`, for the partitions `ξ_1^⊥` and `ξ_2` of `sec:entropies`, which
  condition on the past as well; `BoxLike/MainTwoProse/SubsystemEntropies.lean` has the same
  step for the conditional entropies of the prose, which the endpoint uses.
-/
public import BoxLike.MainTwoProse.ScalarFeng
public import BoxLike.PastEntropy
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

@[expose] public section

namespace BoxLike

open MeasureTheory ProbabilityTheory Filter Set

universe u

/-! ### Monotonicity of the conditional entropy -/

/-- A finer partition has a larger `σ`-algebra of unions of atoms: if `ξ(x) ⊆ ξ'(x)` for every
`x`, then `\widehat{ξ'} ⊆ \widehat{ξ}`. -/
theorem saturated_anti {Ω : Type*} [MeasurableSpace Ω] {ξ ξ' : Ω → Set Ω}
    (h : ∀ x, ξ x ⊆ ξ' x) : saturated ξ' ≤ saturated ξ :=
  fun _ hA => ⟨hA.1, fun x y hy => hA.2 x y (h x hy)⟩

section Entropy

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The conditional entropy is non-negative. -/
theorem condEntropy_nonneg (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (ξ : (ℤ → α) → Set (ℤ → α)) : 0 ≤ condEntropy μ ξ :=
  integral_nonneg fun x => condInfo_nonneg μ ξ x

/-- Conditioning on a finer partition gives at least as much information (proof of
`thm:main2`): if the atom `ξ(x)` lies in the atom `ξ'(x)` for every `x`, then
`H_μ(𝒫 | \widehat{ξ}) ≤ H_μ(𝒫 | \widehat{ξ'})`. The conditional entropies are
`∫ ∑_a η(E_μ(1_{[a]} | ·)) dμ` with `η(t) = -t log t`, `E_μ(1_{[a]} | \widehat{ξ'})` is the
conditional expectation of `E_μ(1_{[a]} | \widehat{ξ})` given `\widehat{ξ'}`, and the conditional
Jensen inequality for the concave `η` gives the inequality for every symbol `a`. -/
theorem condEntropy_le_of_subset (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ]
    {ξ ξ' : (ℤ → α) → Set (ℤ → α)} (h : ∀ x, ξ x ⊆ ξ' x) :
    condEntropy μ ξ ≤ condEntropy μ ξ' := by
  have hm := saturated_le (Ω := ℤ → α) ξ
  have hm' := saturated_le (Ω := ℤ → α) ξ'
  have hle : saturated ξ' ≤ saturated ξ := saturated_anti h
  rw [condEntropy_eq_integral_sum_negMulLog, condEntropy_eq_integral_sum_negMulLog]
  have hint : ∀ (m : MeasurableSpace (ℤ → α)) (_ : m ≤ MeasurableSpace.pi) (a : α),
      Integrable (fun x => Real.negMulLog ((μ⟦{y : ℤ → α | y 0 = a} | m⟧) x)) μ := by
    intro m hm a
    refine Integrable.of_mem_Icc 0 1 ?_ ?_
    · exact (Real.continuous_negMulLog.measurable.comp
        (stronglyMeasurable_condExp.measurable.mono hm le_rfl)).aemeasurable
    · filter_upwards [condExp_indicator_mem_Icc (μ := μ) hm (measurableSet_coord_zero_eq a)]
        with x hx
      exact negMulLog_mem_Icc hx
  rw [integral_finsetSum _ fun a _ => hint _ hm a, integral_finsetSum _ fun a _ => hint _ hm' a]
  refine Finset.sum_le_sum fun a _ => ?_
  set f := μ⟦{y : ℤ → α | y 0 = a} | saturated ξ⟧ with hf
  have hf01 := condExp_indicator_mem_Icc (μ := μ) hm (measurableSet_coord_zero_eq a)
  have htower : μ[f | saturated ξ'] =ᵐ[μ] μ⟦{y : ℤ → α | y 0 = a} | saturated ξ'⟧ :=
    condExp_condExp_of_le hle hm
  have hJ := Real.concaveOn_negMulLog.condExp_map_le hm'
    Real.continuous_negMulLog.continuousOn.upperSemicontinuousOn
    (hf01.mono fun x hx => hx.1) isClosed_Ici integrable_condExp (hint _ hm a)
  have hcomp : (fun x => Real.negMulLog ((μ⟦{y : ℤ → α | y 0 = a} | saturated ξ'⟧) x)) =ᵐ[μ]
      Real.negMulLog ∘ μ[f | saturated ξ'] :=
    htower.mono fun x hx => by simp only [Function.comp_apply, hx]
  calc ∫ x, Real.negMulLog (f x) ∂μ = ∫ x, μ[Real.negMulLog ∘ f | saturated ξ'] x ∂μ :=
        (integral_condExp hm').symm
    _ ≤ ∫ x, (Real.negMulLog ∘ μ[f | saturated ξ']) x ∂μ :=
        integral_mono_ae integrable_condExp ((hint _ hm' a).congr hcomp) hJ
    _ = ∫ x, Real.negMulLog ((μ⟦{y : ℤ → α | y 0 = a} | saturated ξ'⟧) x) ∂μ :=
        (integral_congr_ae hcomp).symm

end Entropy

/-! ### The entropy threshold -/

namespace System

/-- `q_n = h_2(μ) ≤ H(𝒫 | \widehat{ξ_1^⊥})`: the atom `ξ_2(𝐢)` lies in the atom `ξ_1^⊥(𝐢)`
(`sec:entropies`), so conditioning on the planar point gives at least as much information as
conditioning on the coordinate orthogonal to `V^1` (proof of `thm:main2`). -/
theorem dimEntropy_two_le_condEntropy_xiPerp {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (S : System ι) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] :
    S.dimEntropy μ 2 ≤ condEntropy μ (S.xiPerp μ) :=
  condEntropy_le_of_subset μ (S.xi_two_subset_xiPerp μ)

namespace IsHomDiag

variable {κ : Type u} [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ] [Nonempty κ]
  {T : System κ} {a b : ℝ} (hT : T.IsHomDiag a b)
include hT

/-- `q_{y,n} = 0` when `log #W_n ≤ -log |b_n|` (proof of `thm:main2`): then
`d_{y,n} = log #W_n / (-log |b_n|)` and the scalar Ledrappier–Young formula gives
`q_{y,n} = log #W_n + d_{y,n} log |b_n| = 0`.
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem condEntropy_xiPerp_eq_zero_of_le (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (hab : |b| ≤ |a|)
    (hfreey : Function.Injective (simWord (fun _ : κ => b) (fun k => T.trans (k, 1))))
    (hH : Real.log (Fintype.card κ) ≤ -Real.log |b|) :
    condEntropy (uniformBernoulli κ) (T.xiPerp (uniformBernoulli κ)) = 0 := by
  have hqy := hT.condEntropy_xiPerp_eq_scalar hly hkk hab hfreey
  have hlb : 0 < -Real.log |b| := neg_pos.2 hT.log_abs_b_neg
  rw [min_eq_right ((div_le_one hlb).2 hH), mul_div_cancel₀ _ hlb.ne', sub_self] at hqy
  exact hqy

/-- The entropy threshold case of the proof of `thm:main2`: if `log #W_n ≤ -log |b_n|`, then
`0 ≤ q_n ≤ q_{y,n} = 0`, so `q_n = h_2(ν_n) = 0`, "since `ξ_2` refines `ξ_1^⊥`".
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem dimEntropy_two_eq_zero_of_le (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (hab : |b| ≤ |a|)
    (hfreey : Function.Injective (simWord (fun _ : κ => b) (fun k => T.trans (k, 1))))
    (hH : Real.log (Fintype.card κ) ≤ -Real.log |b|) :
    T.dimEntropy (uniformBernoulli κ) 2 = 0 := by
  refine le_antisymm ?_ (condEntropy_nonneg _ _)
  calc T.dimEntropy (uniformBernoulli κ) 2
      ≤ condEntropy (uniformBernoulli κ) (T.xiPerp (uniformBernoulli κ)) :=
        T.dimEntropy_two_le_condEntropy_xiPerp _
    _ = 0 := hT.condEntropy_xiPerp_eq_zero_of_le hly hkk hab hfreey hH

end IsHomDiag

end System

end BoxLike
