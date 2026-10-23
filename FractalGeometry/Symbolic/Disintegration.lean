import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Symbolic.Conditional
import FractalGeometry.Symbolic.ConditionalMeasures
import FractalGeometry.Symbolic.ConditionalRefinement

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal

section Tools

variable {Ω : Type*}

theorem exists_countable_piSystem_generateFrom {S : Set (Set Ω)} (hS : S.Countable) :
    ∃ C : Set (Set Ω), C.Countable ∧ IsPiSystem C ∧ univ ∈ C ∧
      MeasurableSpace.generateFrom C = MeasurableSpace.generateFrom S := by
  classical
  have : Countable S := hS.to_subtype
  refine ⟨range fun F : Finset S => ⋂ s ∈ F, (s : Set Ω), countable_range _, ?_, ⟨∅, by simp⟩,
    ?_⟩
  · rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩ -
    exact ⟨F ∪ G, Finset.set_biInter_inter F G _⟩
  · apply le_antisymm
    · apply MeasurableSpace.generateFrom_le
      rintro _ ⟨F, rfl⟩
      exact Finset.measurableSet_biInter F fun s _ =>
        MeasurableSpace.measurableSet_generateFrom s.2
    · apply MeasurableSpace.generateFrom_mono
      intro s hs
      exact ⟨{⟨s, hs⟩}, by simp⟩

variable {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

theorem ae_eq_of_forall_setLIntegral_eq_of_le (hm : m ≤ mΩ) {μ : Measure Ω} [IsFiniteMeasure μ]
    {f g : Ω → ℝ≥0∞} (hf : Measurable[m] f) (hg : Measurable[m] g)
    (h : ∀ B, MeasurableSet[m] B → ∫⁻ x in B, f x ∂μ = ∫⁻ x in B, g x ∂μ) : f =ᵐ[μ] g := by
  have key : f =ᵐ[μ.trim hm] g := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hf hg fun B hB _ => ?_
    rw [restrict_trim hm μ hB, lintegral_trim hm hf, lintegral_trim hm hg]
    exact h B hB
  exact ae_eq_of_ae_eq_trim key

end Tools

section Disintegration

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

theorem setLIntegral_lintegral_condMeas (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Set Ω)
    {g : Ω → ℝ≥0∞} (hg : Measurable g) {B : Set Ω} (hB : MeasurableSet[saturated ξ] B) :
    ∫⁻ x in B, ∫⁻ y, g y ∂condMeas μ ξ x ∂μ = ∫⁻ x in B, g x ∂μ := by
  have hm := saturated_le (Ω := Ω) ξ
  have h1 := lintegral_mul_lintegral_condMeas μ ξ
    ((measurable_const : Measurable[saturated ξ] fun _ : Ω => (1 : ℝ≥0∞)).indicator hB) hg
  rw [← lintegral_indicator (hm _ hB), ← lintegral_indicator (hm _ hB)]
  calc ∫⁻ x, B.indicator (fun x => ∫⁻ y, g y ∂condMeas μ ξ x) x ∂μ
      = ∫⁻ x, B.indicator (fun _ => (1 : ℝ≥0∞)) x * ∫⁻ y, g y ∂condMeas μ ξ x ∂μ :=
        lintegral_congr fun x => by by_cases hx : x ∈ B <;> simp [hx]
    _ = ∫⁻ x, B.indicator (fun _ => (1 : ℝ≥0∞)) x * g x ∂μ := h1
    _ = ∫⁻ x, B.indicator g x ∂μ :=
        lintegral_congr fun x => by by_cases hx : x ∈ B <;> simp [hx]

theorem condMeas_unique (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Set Ω)
    (K : Ω → Measure Ω) (hK : ∀ A, MeasurableSet A → Measurable[saturated ξ] fun x => K x A)
    (hint : ∀ A B, MeasurableSet A → MeasurableSet[saturated ξ] B →
      ∫⁻ x in B, K x A ∂μ = μ (A ∩ B)) :
    ∀ᵐ x ∂μ, K x = condMeas μ ξ x := by
  obtain ⟨C, hCc, hCpi, hCuniv, hCgen⟩ := exists_countable_piSystem_generateFrom
    (MeasurableSpace.countable_countableGeneratingSet (α := Ω))
  rw [MeasurableSpace.generateFrom_countableGeneratingSet] at hCgen
  have hCm : ∀ A ∈ C, MeasurableSet A := fun A hA => by
    rw [← hCgen]
    exact MeasurableSpace.measurableSet_generateFrom hA
  have h1 : ∀ A ∈ C, ∀ᵐ x ∂μ, K x A = condMeas μ ξ x A := fun A hA =>
    ae_eq_of_forall_setLIntegral_eq_of_le (saturated_le ξ) (hK A (hCm A hA))
      (measurable_condMeas μ ξ (hCm A hA)) fun B hB => by
        rw [hint A B (hCm A hA) hB, setLIntegral_condMeas μ ξ (hCm A hA) hB]
  filter_upwards [(ae_ball_iff hCc).2 h1] with x hx
  have : IsFiniteMeasure (K x) := ⟨by rw [hx univ hCuniv]; exact measure_lt_top _ _⟩
  exact ext_of_generate_finite C hCgen.symm hCpi hx (hx univ hCuniv)

theorem condMeas_of_saturated (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Set Ω) {B : Set Ω}
    (hB : MeasurableSet[saturated ξ] B) :
    ∀ᵐ x ∂μ, condMeas μ ξ x B = B.indicator 1 x := by
  have hm := saturated_le (Ω := Ω) ξ
  refine ae_eq_of_forall_setLIntegral_eq_of_le hm (measurable_condMeas μ ξ (hm _ hB))
    ((measurable_const : Measurable[saturated ξ] fun _ : Ω => (1 : ℝ≥0∞)).indicator hB)
    fun C hC => ?_
  rw [setLIntegral_condMeas μ ξ (hm _ hB) hC, lintegral_indicator_one (hm _ hB),
    Measure.restrict_apply (hm _ hB)]

theorem condMeas_atom (μ : Measure Ω) [IsFiniteMeasure μ] {ξ : Ω → Set Ω}
    (hξ : IsMeasurablePartition ξ) : ∀ᵐ x ∂μ, condMeas μ ξ x (ξ x) = 1 := by
  obtain ⟨f, hf, hfξ⟩ := hξ
  have hsat : ∀ U : Set ℝ, MeasurableSet U → MeasurableSet[saturated ξ] (f ⁻¹' U) :=
    fun U hU => ⟨hf hU, fun x y hxy => by simp only [mem_preimage, (hfξ x y).1 hxy]⟩
  have hb := TopologicalSpace.isBasis_countableBasis ℝ
  have h1 : ∀ U ∈ TopologicalSpace.countableBasis ℝ,
      ∀ᵐ x ∂μ, condMeas μ ξ x (f ⁻¹' U) = (f ⁻¹' U).indicator 1 x := fun U hU =>
    condMeas_of_saturated μ ξ (hsat U (hb.isOpen hU).measurableSet)
  filter_upwards [(ae_ball_iff (TopologicalSpace.countable_countableBasis ℝ)).2 h1] with x hx
  have hmeas : MeasurableSet (ξ x) := by
    have : ξ x = f ⁻¹' {f x} := by
      ext y
      exact hfξ x y
    rw [this]
    exact hf (measurableSet_singleton _)
  rw [← prob_compl_eq_zero_iff hmeas]
  have hsub : (ξ x)ᶜ ⊆ ⋃ U ∈ {U ∈ TopologicalSpace.countableBasis ℝ | f x ∈ U}, (f ⁻¹' U)ᶜ := by
    intro y hy
    have hne : f x ≠ f y := fun h => hy ((hfξ x y).2 h.symm)
    obtain ⟨U, hU, hxU, hUy⟩ := hb.exists_subset_of_mem_open
      (show f x ∈ ({f y} : Set ℝ)ᶜ from hne) isOpen_compl_singleton
    refine mem_biUnion (⟨hU, hxU⟩ : U ∈ {U ∈ TopologicalSpace.countableBasis ℝ | f x ∈ U}) ?_
    intro hyU
    exact hUy hyU rfl
  refine measure_mono_null hsub ?_
  refine (measure_biUnion_null_iff
    ((TopologicalSpace.countable_countableBasis ℝ).mono (sep_subset _ _))).2 ?_
  rintro U ⟨hU, hxU⟩
  rw [prob_compl_eq_zero_iff (hf (hb.isOpen hU).measurableSet), hx U hU]
  simp [hxU]

end Disintegration

section Shift

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem ofReal_neg_log_mul_le_one (t : ℝ≥0∞) (ht : t ≤ 1) :
    ENNReal.ofReal (-Real.log t.toReal) * t ≤ 1 := by
  rcases eq_or_ne t 0 with rfl | h0
  · simp
  have htop : t ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top ht
  have hr : 0 < t.toReal := ENNReal.toReal_pos h0 htop
  have hr1 : t.toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using ht)
  have hlog : 0 ≤ -Real.log t.toReal := neg_nonneg.2 (Real.log_nonpos hr.le hr1)
  have h1 := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hr) hr.le
  have h2 : t.toReal * (1 - t.toReal⁻¹) = t.toReal - 1 := by field_simp
  calc ENNReal.ofReal (-Real.log t.toReal) * t
      = ENNReal.ofReal (-Real.log t.toReal * t.toReal) := by
        rw [ENNReal.ofReal_mul hlog, ENNReal.ofReal_toReal htop]
    _ ≤ 1 := ENNReal.ofReal_le_one.2 (by nlinarith)

theorem integrable_condInfo (μ : Measure (ℤ → α)) [IsProbabilityMeasure μ]
    (ξ : (ℤ → α) → Set (ℤ → α)) : Integrable (condInfo μ ξ) μ := by
  classical
  have hm := saturated_le (Ω := ℤ → α) ξ
  set cyl : α → Set (ℤ → α) := fun a => {y | y 0 = a} with hcyl_def
  have hcyl : ∀ a, MeasurableSet (cyl a) := fun a =>
    show MeasurableSet ((fun y : ℤ → α => y 0) ⁻¹' {a}) from
      measurable_pi_apply (0 : ℤ) (measurableSet_singleton a)
  set φ : α → (ℤ → α) → ℝ := fun a x => -Real.log ((condMeas μ ξ x).real (cyl a)) with hφ_def
  have hφm : ∀ a, Measurable[saturated ξ] (φ a) := fun a =>
    (Real.measurable_log.comp (measurable_condMeas μ ξ (hcyl a)).ennreal_toReal).neg
  have hφ0 : ∀ a x, 0 ≤ φ a x := fun a x =>
    neg_nonneg.2 (Real.log_nonpos measureReal_nonneg measureReal_le_one)
  have hsum : condInfo μ ξ = fun x => ∑ a, (cyl a).indicator (φ a) x := by
    funext x
    rw [Finset.sum_eq_single (x 0)]
    · rw [indicator_of_mem (show x ∈ cyl (x 0) from rfl)]
      rfl
    · intro a _ ha
      have hx : x ∉ cyl a := fun h : x 0 = a => ha h.symm
      exact indicator_of_notMem hx (φ a)
    · simp
  rw [hsum]
  refine integrable_finsetSum _ fun a _ => ?_
  rw [integrable_indicator_iff (hcyl a)]
  refine ⟨((hφm a).mono hm le_rfl).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hofReal : Measurable[saturated ξ] fun x => ENNReal.ofReal (φ a x) :=
    ENNReal.measurable_ofReal.comp (hφm a)
  calc ∫⁻ x in cyl a, ‖φ a x‖ₑ ∂μ
      = ∫⁻ x in cyl a ∩ univ, ENNReal.ofReal (φ a x) ∂μ := by
        rw [inter_univ]
        exact lintegral_congr fun x => Real.enorm_of_nonneg (hφ0 a x)
    _ = ∫⁻ x in univ, ENNReal.ofReal (φ a x) * condMeas μ ξ x (cyl a) ∂μ :=
        (setLIntegral_mul_condMeas μ ξ hofReal (hcyl a) MeasurableSet.univ).symm
    _ ≤ ∫⁻ _ in univ, 1 ∂μ := lintegral_mono fun x => ofReal_neg_log_mul_le_one _ prob_le_one
    _ < ∞ := by simp

end Shift

end FractalGeometry
