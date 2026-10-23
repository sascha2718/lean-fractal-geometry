import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Symbolic.Conditional
import FractalGeometry.Symbolic.ConditionalMeasures
import FractalGeometry.Symbolic.ConditionalRefinement
import FractalGeometry.Symbolic.Disintegration

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal

section Saturated

variable {Ω : Type*} [MeasurableSpace Ω]

theorem saturated_mono {ξ ξ' : Ω → Set Ω} (hfine : ∀ x, ξ' x ⊆ ξ x) :
    saturated ξ ≤ saturated ξ' :=
  fun _ hA => ⟨hA.1, fun x y hxy => hA.2 x y (hfine x hxy)⟩

end Saturated

section Conditional

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]

theorem exists_countable_piSystem_saturated {ξ : Ω → Set Ω} (hξ : IsMeasurablePartition ξ) :
    ∃ C : Set (Set Ω), C.Countable ∧ IsPiSystem C ∧ univ ∈ C ∧
      saturated ξ = MeasurableSpace.generateFrom C := by
  obtain ⟨f, hf, hfξ⟩ := hξ
  have hb := TopologicalSpace.isBasis_countableBasis ℝ
  obtain ⟨C, hCc, hCpi, hCuniv, hCgen⟩ := exists_countable_piSystem_generateFrom
    ((TopologicalSpace.countable_countableBasis ℝ).image (preimage f))
  refine ⟨C, hCc, hCpi, hCuniv, ?_⟩
  rw [hCgen, saturated_eq_comap hf hfξ, ← MeasurableSpace.comap_generateFrom,
    ← hb.borel_eq_generateFrom, BorelSpace.measurable_eq (α := ℝ)]

theorem double_conditional (μ : Measure Ω) [IsProbabilityMeasure μ] {ξ ξ' : Ω → Set Ω}
    (_hξ : IsMeasurablePartition ξ) (hξ' : IsMeasurablePartition ξ')
    (hfine : ∀ x, ξ' x ⊆ ξ x) :
    (∀ᵐ j ∂μ, ∀ᵐ i ∂condMeas μ ξ j, condMeas (condMeas μ ξ j) ξ' i = condMeas μ ξ' i) ∧
    ∀ A, MeasurableSet A →
      ∫⁻ j, ∫⁻ i, condMeas μ ξ' i A ∂condMeas μ ξ j ∂μ = ∫⁻ i, condMeas μ ξ' i A ∂μ := by
  have hm := saturated_le (Ω := Ω) ξ
  have hm' := saturated_le (Ω := Ω) ξ'
  have hmono := saturated_mono hfine
  have hκ' : ∀ A, MeasurableSet A → Measurable fun i => condMeas μ ξ' i A := fun A hA =>
    (measurable_condMeas μ ξ' hA).mono hm' le_rfl
  have hκ'm : Measurable (condMeas μ ξ') := Measure.measurable_of_measurable_coe _ hκ'
  refine ⟨?_, fun A hA => ?_⟩
  swap
  · have h := setLIntegral_lintegral_condMeas μ ξ (hκ' A hA) (B := univ) MeasurableSet.univ
    simpa using h
  obtain ⟨𝒜, h𝒜c, h𝒜pi, h𝒜univ, h𝒜gen⟩ := exists_countable_piSystem_generateFrom
    (MeasurableSpace.countable_countableGeneratingSet (α := Ω))
  rw [MeasurableSpace.generateFrom_countableGeneratingSet] at h𝒜gen
  obtain ⟨ℬ, hℬc, hℬpi, hℬuniv, hℬgen⟩ := exists_countable_piSystem_saturated hξ'
  have h𝒜m : ∀ A ∈ 𝒜, MeasurableSet A := fun A hA => by
    rw [← h𝒜gen]
    exact MeasurableSpace.measurableSet_generateFrom hA
  have hℬm : ∀ B ∈ ℬ, MeasurableSet[saturated ξ'] B := fun B hB => by
    rw [hℬgen]
    exact MeasurableSpace.measurableSet_generateFrom hB

  have h1 : ∀ A ∈ 𝒜, ∀ B ∈ ℬ, ∀ᵐ j ∂μ,
      ∫⁻ i in B, condMeas μ ξ' i A ∂condMeas μ ξ j = condMeas μ ξ j (A ∩ B) := by
    intro A hA B hB
    have hAm := h𝒜m A hA
    have hBm := hℬm B hB
    refine ae_eq_of_forall_setLIntegral_eq_of_le hm ?_
      (measurable_condMeas μ ξ (hAm.inter (hm' _ hBm))) fun C hC => ?_
    · exact Measurable.setLIntegral_kernel (κ := condExpKernel μ (saturated ξ)) (hκ' A hAm)
        (hm' _ hBm)
    · have hBC : MeasurableSet[saturated ξ'] (B ∩ C) :=
        @MeasurableSet.inter _ (saturated ξ') _ _ hBm (hmono _ hC)
      simp_rw [← lintegral_indicator (hm' _ hBm)]
      rw [setLIntegral_lintegral_condMeas μ ξ ((hκ' A hAm).indicator (hm' _ hBm)) hC,
        setLIntegral_indicator (hm' _ hBm), setLIntegral_condMeas μ ξ' hAm hBC,
        setLIntegral_condMeas μ ξ (hAm.inter (hm' _ hBm)) hC, inter_assoc]
  have h2 : ∀ᵐ j ∂μ, ∀ A ∈ 𝒜, ∀ B ∈ ℬ,
      ∫⁻ i in B, condMeas μ ξ' i A ∂condMeas μ ξ j = condMeas μ ξ j (A ∩ B) :=
    (ae_ball_iff h𝒜c).2 fun A hA => (ae_ball_iff hℬc).2 (h1 A hA)
  filter_upwards [h2] with j hj

  have h3 : ∀ B ∈ ℬ, ∀ A, MeasurableSet A →
      ∫⁻ i in B, condMeas μ ξ' i A ∂condMeas μ ξ j = condMeas μ ξ j (A ∩ B) := by
    intro B hB A hA
    have hext : (condMeas μ ξ j).restrict B
        = ((condMeas μ ξ j).restrict B).bind (condMeas μ ξ') := by
      refine ext_of_generate_finite 𝒜 h𝒜gen.symm h𝒜pi (fun A hA => ?_) ?_
      · rw [Measure.bind_apply (h𝒜m A hA) hκ'm.aemeasurable,
          Measure.restrict_apply (h𝒜m A hA), hj A hA B hB]
      · rw [Measure.bind_apply MeasurableSet.univ hκ'm.aemeasurable,
          Measure.restrict_apply MeasurableSet.univ, hj univ h𝒜univ B hB]
    rw [← Measure.bind_apply hA hκ'm.aemeasurable, ← hext, Measure.restrict_apply hA]

  have h4 : ∀ A B, MeasurableSet A → MeasurableSet[saturated ξ'] B →
      ∫⁻ i in B, condMeas μ ξ' i A ∂condMeas μ ξ j = condMeas μ ξ j (A ∩ B) := by
    intro A B hA hB
    have hext : ((condMeas μ ξ j).restrict A).trim hm'
        = ((condMeas μ ξ j).withDensity fun i => condMeas μ ξ' i A).trim hm' := by
      refine ext_of_generate_finite ℬ hℬgen hℬpi (fun B hB => ?_) ?_
      · rw [trim_measurableSet_eq hm' (hℬm B hB), trim_measurableSet_eq hm' (hℬm B hB),
          Measure.restrict_apply (hm' _ (hℬm B hB)), withDensity_apply _ (hm' _ (hℬm B hB)),
          h3 B hB A hA, inter_comm]
      · rw [trim_measurableSet_eq hm' MeasurableSet.univ,
          trim_measurableSet_eq hm' MeasurableSet.univ,
          Measure.restrict_apply MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ,
          h3 univ hℬuniv A hA, inter_comm]
    have h5 := congrArg (fun ρ : @Measure Ω (saturated ξ') => ρ B) hext
    simp only [trim_measurableSet_eq hm' hB, Measure.restrict_apply (hm' _ hB),
      withDensity_apply _ (hm' _ hB)] at h5
    rw [← h5, inter_comm]
  filter_upwards [condMeas_unique (condMeas μ ξ j) ξ' (condMeas μ ξ')
    (fun A hA => measurable_condMeas μ ξ' hA) h4] with i hi
  exact hi.symm

end Conditional

end FractalGeometry
