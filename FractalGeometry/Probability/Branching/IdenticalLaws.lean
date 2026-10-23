import Mathlib
import FractalGeometry.Probability.Branching.Configuration
import FractalGeometry.Probability.Branching.Descendants
import FractalGeometry.Probability.Branching.Law
import FractalGeometry.Probability.Branching.Process
import FractalGeometry.Probability.Branching.RetainedWords
import FractalGeometry.Probability.Branching.Words

namespace FractalGeometry.Probability.Branching

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {A : Law} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.arity) → Ω → Bool}

def shiftFamily (X : Word A → (Fin A.arity) → Ω → Bool) (root : Word A) :
    Word A → (Fin A.arity) → Ω → Bool :=
  fun w a => X (root ++ w) a

lemma shiftCoordinate_injective (root : Word A) :
    Function.Injective fun q : Word A × (Fin A.arity) => (root ++ q.1, q.2) := by
  rintro ⟨u, a⟩ ⟨u', a'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [List.append_cancel_left h1, h2]

theorem IsPercolation.shift (hX : IsPercolation P X) (root : Word A) :
    IsPercolation P (shiftFamily X root) where
  isProbabilityMeasure := hX.isProbabilityMeasure
  measurable := fun w a => hX.measurable (root ++ w) a
  indep := hX.indep.precomp (shiftCoordinate_injective root)
  prob := fun w a => hX.prob (root ++ w) a

def config (X : Word A → (Fin A.arity) → Ω → Bool) (ω : Ω) : Configuration A :=
  fun q => X q.1 q.2 ω

lemma measurable_config (hX : IsPercolation P X) : Measurable (config X) :=
  Measurable.of_eval fun q => hX.measurable q.1 q.2

lemma map_bool_eq_of_prob {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {f : Ω → Bool}
    {g : Ω' → Bool} [IsProbabilityMeasure P] [IsProbabilityMeasure P'] (hf : Measurable f)
    (hg : Measurable g) (h : P {ω | f ω = true} = P' {ω | g ω = true}) :
    P.map f = P'.map g := by
  refine Measure.ext_iff_singleton.mpr fun b => ?_
  rw [Measure.map_apply hf (measurableSet_singleton b),
    Measure.map_apply hg (measurableSet_singleton b)]
  cases b
  · have h1 : f ⁻¹' {false} = {ω | f ω = true}ᶜ := by ext ω; simp
    have h2 : g ⁻¹' {false} = {ω | g ω = true}ᶜ := by ext ω; simp
    rw [h1, h2, measure_compl (measurableSet_eq_fun hf measurable_const) (measure_ne_top _ _),
      measure_compl (measurableSet_eq_fun hg measurable_const) (measure_ne_top _ _), h,
      measure_univ, measure_univ]
  · exact h

section Transfer

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
  {X' : Word A → (Fin A.arity) → Ω' → Bool}

theorem IsPercolation.map_config_eq (hX : IsPercolation P X) (hX' : IsPercolation P' X') :
    P.map (config X) = P'.map (config X') := by
  let : IsProbabilityMeasure P := hX.toIsProbabilityMeasure
  let : IsProbabilityMeasure P' := hX'.toIsProbabilityMeasure
  have h1 := (iIndepFun_iff_map_fun_eq_infinitePi_map₀
    (aemeasurable_pi_iff.2 fun q : Word A × (Fin A.arity) =>
      (hX.measurable q.1 q.2).aemeasurable)).mp hX.indep
  have h2 := (iIndepFun_iff_map_fun_eq_infinitePi_map₀
    (aemeasurable_pi_iff.2 fun q : Word A × (Fin A.arity) =>
      (hX'.measurable q.1 q.2).aemeasurable)).mp hX'.indep
  have hmarg : (fun q : Word A × (Fin A.arity) => P.map (X q.1 q.2)) =
      fun q => P'.map (X' q.1 q.2) := by
    funext q
    apply map_bool_eq_of_prob (hX.measurable q.1 q.2) (hX'.measurable q.1 q.2)
    rw [hX.prob, hX'.prob]
  show P.map (fun ω (q : Word A × (Fin A.arity)) => X q.1 q.2 ω) =
    P'.map (fun ω (q : Word A × (Fin A.arity)) => X' q.1 q.2 ω)
  rw [h1, h2, hmarg]

theorem IsPercolation.measure_config_functional_eq (hX : IsPercolation P X)
    (hX' : IsPercolation P' X') {β : Type*} [MeasurableSpace β] {G : Configuration A → β}
    (hG : Measurable G) {s : Set β} (hs : MeasurableSet s) :
    P {ω | G (config X ω) ∈ s} = P' {ω | G (config X' ω) ∈ s} := by
  have h1 : {ω | G (config X ω) ∈ s} = config X ⁻¹' (G ⁻¹' s) := rfl
  have h2 : {ω | G (config X' ω) ∈ s} = config X' ⁻¹' (G ⁻¹' s) := rfl
  rw [h1, h2, ← Measure.map_apply (measurable_config hX) (hG hs),
    ← Measure.map_apply (measurable_config hX') (hG hs), hX.map_config_eq hX']

end Transfer

theorem IsPercolation.measure_config_functional_shift (hX : IsPercolation P X)
    (root : Word A) {β : Type*} [MeasurableSpace β] {G : Configuration A → β}
    (hG : Measurable G) {s : Set β} (hs : MeasurableSet s) :
    P {ω | G (rebase root (config X ω)) ∈ s} = P {ω | G (config X ω) ∈ s} :=
  (hX.shift root).measure_config_functional_eq hX hG hs

noncomputable def descendantCountConfig (x : Configuration A) (root : Word A) (j : ℕ) :
    ℕ := by
  classical
  exact {u : DigitWord A j | retainedBelowConfig x root (wordOfDigits u)}.toFinset.card

omit [MeasurableSpace Ω] in

lemma descendantCountBelow_eq_config (root : Word A) (j : ℕ) (ω : Ω) :
    descendantCountBelow X root j ω = descendantCountConfig (config X ω) root j := rfl

lemma measurable_descendantCountConfig (root : Word A) (j : ℕ) :
    Measurable fun x : Configuration A => descendantCountConfig x root j := by
  classical
  rw [show (fun x : Configuration A => descendantCountConfig x root j) = fun x =>
      ∑ u ∈ (Finset.univ : Finset (DigitWord A j)),
        if retainedBelowConfig x root (wordOfDigits u) then 1 else 0 by
    funext x
    unfold descendantCountConfig
    rw [Set.toFinset_ofPred]
    exact Finset.card_filter _ _]
  exact Finset.measurable_fun_sum _ fun u _ =>
    Measurable.ite (measurableSet_retainedBelowConfig root (wordOfDigits u))
      measurable_const measurable_const

end FractalGeometry.Probability.Branching
