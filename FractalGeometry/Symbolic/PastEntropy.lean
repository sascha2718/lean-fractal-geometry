module

public import Mathlib
public import FractalGeometry.Symbolic.Conditional
public import FractalGeometry.Symbolic.Entropy
public import FractalGeometry.Symbolic.Partitions
public import FractalGeometry.Symbolic.Shift
public import FractalGeometry.Symbolic.Past

@[expose] public section

namespace FractalGeometry


open MeasureTheory ProbabilityTheory Filter Topology Set

section FiniteCondExp

variable {Ω B : Type*} [MeasurableSpace Ω] [Fintype B] [MeasurableSpace B]
  [MeasurableSingletonClass B] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem setIntegral_comp_fintype {g : Ω → B} (hg : Measurable g) (φ : B → ℝ) (s : Set Ω) :
    ∫ x in s, φ (g x) ∂μ = ∑ b, μ.real (s ∩ g ⁻¹' {b}) * φ b := by
  have hφ : Measurable φ := measurable_of_countable φ
  rw [← integral_map hg.aemeasurable hφ.aestronglyMeasurable,
    integral_fintype (Integrable.of_bound hφ.aestronglyMeasurable (∑ b, ‖φ b‖)
      (ae_of_all _ fun b => Finset.single_le_sum (f := fun b => ‖φ b‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ b)))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_measureReal_apply hg (measurableSet_singleton b),
    measureReal_restrict_apply (hg (measurableSet_singleton b)), inter_comm, smul_eq_mul]

theorem condExp_indicator_comap_fintype {g : Ω → B} (hg : Measurable g) {A : Set Ω}
    (hA : MeasurableSet A) :
    μ⟦A | MeasurableSpace.comap g inferInstance⟧ =ᵐ[μ]
      fun x => μ.real (A ∩ g ⁻¹' {g x}) / μ.real (g ⁻¹' {g x}) := by
  set r : B → ℝ := fun b => μ.real (A ∩ g ⁻¹' {b}) / μ.real (g ⁻¹' {b}) with hr
  have hrm : Measurable r := measurable_of_countable r
  have hr1 : ∀ b, ‖r b‖ ≤ 1 := fun b => by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg measureReal_nonneg measureReal_nonneg)]
    exact div_le_one_of_le₀ (measureReal_mono inter_subset_right) measureReal_nonneg
  have hmeas : Measurable[MeasurableSpace.comap g inferInstance] fun x => r (g x) :=
    hrm.comp (comap_measurable g)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hg.comap_le
    ((integrable_const (1 : ℝ)).indicator hA) (fun s _ _ => ?_) (fun s hs _ => ?_)
    hmeas.stronglyMeasurable.aestronglyMeasurable).symm
  · exact (Integrable.of_bound (hrm.comp hg).aestronglyMeasurable 1
      (ae_of_all _ fun x => hr1 (g x))).integrableOn
  · obtain ⟨T, -, rfl⟩ := hs
    rw [setIntegral_comp_fintype hg r, integral_indicator_const _ hA, smul_eq_mul, mul_one,
      measureReal_restrict_apply hA,
      ← sum_measureReal_inter_preimage_singleton μ
        (fun c => hg (measurableSet_singleton c)) (A ∩ g ⁻¹' T)]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b ∈ T
    · have e : g ⁻¹' T ∩ g ⁻¹' {b} = g ⁻¹' {b} := by
        ext x
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ hb, h⟩⟩
      rw [inter_assoc, e, hr]
      by_cases h0 : μ.real (g ⁻¹' {b}) = 0
      · rw [h0, zero_mul]
        exact (measureReal_mono_null inter_subset_right h0).symm
      · field_simp
    · have e : g ⁻¹' T ∩ g ⁻¹' {b} = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false,
          iff_false, not_and]
        exact fun h h' => hb (h' ▸ h)
      rw [inter_assoc, e, inter_empty, measureReal_empty, zero_mul]

theorem mul_negMulLog_div {p q : ℝ} (hq : p = 0 → q = 0) :
    p * Real.negMulLog (q / p) = Real.negMulLog q + q * Real.log p := by
  by_cases hp : p = 0
  · simp [hp, hq hp]
  · rw [div_eq_mul_inv, Real.negMulLog_mul, Real.negMulLog, Real.negMulLog, Real.log_inv]
    field_simp

theorem integral_sum_negMulLog_condExp_comap {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] {f : Ω → A} {g : Ω → B} (hf : Measurable f)
    (hg : Measurable g) :
    ∫ x, ∑ a, Real.negMulLog ((μ⟦f ⁻¹' {a} | MeasurableSpace.comap g inferInstance⟧) x) ∂μ =
      ∑ b, ∑ a, Real.negMulLog (μ.real (f ⁻¹' {a} ∩ g ⁻¹' {b})) -
        ∑ b, Real.negMulLog (μ.real (g ⁻¹' {b})) := by
  have hfa : ∀ a, MeasurableSet (f ⁻¹' {a}) := fun a => hf (measurableSet_singleton a)
  have hae : ∀ᵐ x ∂μ, ∀ a, (μ⟦f ⁻¹' {a} | MeasurableSpace.comap g inferInstance⟧) x =
      μ.real (f ⁻¹' {a} ∩ g ⁻¹' {g x}) / μ.real (g ⁻¹' {g x}) :=
    ae_all_iff.2 fun a => condExp_indicator_comap_fintype hg (hfa a)
  set φ : B → ℝ := fun b => ∑ a, Real.negMulLog
    (μ.real (f ⁻¹' {a} ∩ g ⁻¹' {b}) / μ.real (g ⁻¹' {b})) with hφ
  have h1 : ∫ x, ∑ a, Real.negMulLog
        ((μ⟦f ⁻¹' {a} | MeasurableSpace.comap g inferInstance⟧) x) ∂μ =
      ∫ x in univ, φ (g x) ∂μ := by
    rw [Measure.restrict_univ]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    exact Finset.sum_congr rfl fun a _ => by rw [hx a]
  rw [h1, setIntegral_comp_fintype hg φ univ, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [univ_inter, hφ, Finset.mul_sum]
  have h2 : ∀ a, μ.real (g ⁻¹' {b}) *
      Real.negMulLog (μ.real (f ⁻¹' {a} ∩ g ⁻¹' {b}) / μ.real (g ⁻¹' {b})) =
      Real.negMulLog (μ.real (f ⁻¹' {a} ∩ g ⁻¹' {b})) +
        μ.real (f ⁻¹' {a} ∩ g ⁻¹' {b}) * Real.log (μ.real (g ⁻¹' {b})) := fun a =>
    mul_negMulLog_div fun h0 => measureReal_mono_null inter_subset_right h0
  have h3 : ∑ a, μ.real (f ⁻¹' {a} ∩ g ⁻¹' {b}) = μ.real (g ⁻¹' {b}) := by
    simp_rw [inter_comm (f ⁻¹' _)]
    exact sum_measureReal_inter_preimage_singleton μ hfa _
  simp_rw [h2]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, h3, Real.negMulLog]
  ring

end FiniteCondExp

section PastFiltration

variable {α : Type*}

def pastBlock (k : ℕ) (x : ℤ → α) : Fin k → α := fun j => x (-(k : ℤ) + j)

theorem pastBlock_shift (k : ℕ) (x : ℤ → α) : pastBlock k (shift k x) = block k x := by
  funext j
  simp [pastBlock, block]

theorem pastBlock_eq_comp_succ (k : ℕ) :
    (pastBlock k : (ℤ → α) → Fin k → α) = (fun w => w ∘ Fin.succ) ∘ pastBlock (k + 1) := by
  funext x j
  simp only [pastBlock, Function.comp_apply, Fin.val_succ]
  congr 1
  push_cast
  ring

theorem pastBlock_eq_comp_past (k : ℕ) :
    (pastBlock k : (ℤ → α) → Fin k → α) = (fun p (j : Fin k) => p (k - 1 - j)) ∘ past := by
  funext x j
  simp only [pastBlock, Function.comp_apply, past]
  congr 1
  have := j.isLt
  omega

variable [MeasurableSpace α]

theorem measurable_pastBlock (k : ℕ) : Measurable (pastBlock k : (ℤ → α) → Fin k → α) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

def pastFiltration (α : Type*) [MeasurableSpace α] :
    Filtration ℕ (inferInstance : MeasurableSpace (ℤ → α)) where
  seq k := MeasurableSpace.comap (pastBlock k) inferInstance
  mono' := monotone_nat_of_le_succ fun k => by
    rw [pastBlock_eq_comp_succ k, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono
      (Measurable.comap_le (Measurable.of_eval fun _ => measurable_pi_apply _))
  le' k := (measurable_pastBlock k).comap_le

theorem iSup_pastFiltration :
    ⨆ k, pastFiltration α k = MeasurableSpace.comap (past : (ℤ → α) → ℕ → α) inferInstance := by
  apply le_antisymm
  · refine iSup_le fun k => ?_
    change MeasurableSpace.comap (pastBlock k) _ ≤ _
    rw [pastBlock_eq_comp_past, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono
      (Measurable.comap_le (Measurable.of_eval fun _ => measurable_pi_apply _))
  · change MeasurableSpace.comap past MeasurableSpace.pi ≤ _
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun n => le_trans ?_ (le_iSup _ (n + 1))
    change _ ≤ MeasurableSpace.comap (pastBlock (n + 1)) _
    rw [MeasurableSpace.comap_comp]
    have e : (fun b : ℕ → α => b n) ∘ past =
        (fun w : Fin (n + 1) → α => w 0) ∘ pastBlock (n + 1) := by
      funext x
      simp only [Function.comp_apply, past, pastBlock]
      congr 1
    rw [e, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (Measurable.comap_le (measurable_pi_apply _))

end PastFiltration

section Increments

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] {μ : Measure (ℤ → α)}

theorem measurableSet_coord_zero_eq (a : α) : MeasurableSet {y : ℤ → α | y 0 = a} := by
  change MeasurableSet ((fun y : ℤ → α => y 0) ⁻¹' {a})
  exact measurable_pi_apply (0 : ℤ) (measurableSet_singleton a)

theorem measureReal_pastBlock_preimage (hinv : MeasurePreserving (shift 1) μ μ) (k : ℕ)
    (v : Fin k → α) : μ.real (pastBlock k ⁻¹' {v}) = μ.real (cylinder v) := by
  rw [← (measurePreserving_shift_natCast hinv k).measureReal_preimage
    (measurable_pastBlock k (measurableSet_singleton v)).nullMeasurableSet]
  congr 1
  ext x
  simp [pastBlock_shift, cylinder_eq_preimage]

theorem measureReal_inter_pastBlock_preimage (hinv : MeasurePreserving (shift 1) μ μ) (k : ℕ)
    (v : Fin k → α) (a : α) :
    μ.real ({y | y 0 = a} ∩ pastBlock k ⁻¹' {v}) =
      μ.real (cylinder (Fin.append v fun _ : Fin 1 => a)) := by
  have hm : MeasurableSet ({y : ℤ → α | y 0 = a} ∩ pastBlock k ⁻¹' {v}) :=
    (measurableSet_coord_zero_eq a).inter (measurable_pastBlock k (measurableSet_singleton v))
  rw [← (measurePreserving_shift_natCast hinv k).measureReal_preimage hm.nullMeasurableSet,
    cylinder_append]
  congr 1
  ext x
  simp [pastBlock_shift, cylinder, block, funext_iff, and_comm]

variable [Fintype α]

omit [MeasurableSingletonClass α] in

theorem blockEntropy_succ_eq_sum (μ : Measure (ℤ → α)) (k : ℕ) :
    blockEntropy μ (k + 1) = ∑ v : Fin k → α, ∑ a,
      Real.negMulLog (μ.real (cylinder (Fin.append v fun _ : Fin 1 => a))) := by
  calc blockEntropy μ (k + 1)
      = ∑ p : (Fin k → α) × (Fin 1 → α),
          Real.negMulLog (μ.real (cylinder (Fin.append p.1 p.2))) :=
        (Fintype.sum_equiv (Fin.appendEquiv k 1) _ _ fun p => rfl).symm
    _ = ∑ v : Fin k → α, ∑ w : Fin 1 → α,
          Real.negMulLog (μ.real (cylinder (Fin.append v w))) := Fintype.sum_prod_type _
    _ = _ := Finset.sum_congr rfl fun v _ =>
        (Fintype.sum_equiv (Equiv.funUnique (Fin 1) α).symm _ _ fun a => rfl).symm

theorem integral_sum_negMulLog_condExp_pastFiltration [IsFiniteMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (k : ℕ) :
    ∫ x, ∑ a, Real.negMulLog ((μ⟦{y | y 0 = a} | pastFiltration α k⟧) x) ∂μ =
      blockEntropy μ (k + 1) - blockEntropy μ k := by
  have h := integral_sum_negMulLog_condExp_comap (μ := μ) (f := fun x : ℤ → α => x 0)
    (g := pastBlock k) (measurable_pi_apply 0) (measurable_pastBlock k)
  refine h.trans ?_
  rw [blockEntropy_succ_eq_sum, blockEntropy]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun a _ => ?_
    rw [← measureReal_inter_pastBlock_preimage hinv]
    rfl
  · exact Finset.sum_congr rfl fun v _ => by rw [measureReal_pastBlock_preimage hinv]

end Increments

section Limit

variable {Ω ι : Type*} [Fintype ι] {m m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [IsFiniteMeasure μ]

theorem condExp_indicator_mem_Icc (hm : m ≤ m0) {A : Set Ω} (hA : MeasurableSet A) :
    ∀ᵐ x ∂μ, (μ⟦A | m⟧) x ∈ Icc (0 : ℝ) 1 := by
  have hint : Integrable (A.indicator fun _ => (1 : ℝ)) μ := (integrable_const 1).indicator hA
  have h0 : 0 ≤ᵐ[μ] μ⟦A | m⟧ :=
    condExp_nonneg (ae_of_all _ fun x => indicator_nonneg (fun _ _ => zero_le_one) x)
  have h1 : μ⟦A | m⟧ ≤ᵐ[μ] μ[fun _ => (1 : ℝ) | m] :=
    condExp_mono hint (integrable_const 1)
      (ae_of_all _ fun x => indicator_le_self' (fun _ _ => zero_le_one) x)
  rw [condExp_const hm] at h1
  filter_upwards [h0, h1] with x hx0 hx1
  exact ⟨hx0, hx1⟩

theorem negMulLog_mem_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : Real.negMulLog t ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.negMulLog_nonneg ht.1 ht.2,
    (Real.negMulLog_le_one_sub_self ht.1).trans (by linarith [ht.1])⟩

theorem tendsto_integral_sum_negMulLog_condExp (ℱ : Filtration ℕ m0) {A : ι → Set Ω}
    (hA : ∀ i, MeasurableSet (A i)) :
    Tendsto (fun k => ∫ x, ∑ i, Real.negMulLog ((μ⟦A i | ℱ k⟧) x) ∂μ) atTop
      (𝓝 (∫ x, ∑ i, Real.negMulLog ((μ⟦A i | ⨆ k, ℱ k⟧) x) ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => (Fintype.card ι : ℝ))
    (fun k => ?_) (integrable_const _) (fun k => ?_) ?_
  · exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      Real.continuous_negMulLog.comp_aestronglyMeasurable
        (stronglyMeasurable_condExp.mono (ℱ.le k)).aestronglyMeasurable
  · have h : ∀ᵐ x ∂μ, ∀ i, (μ⟦A i | ℱ k⟧) x ∈ Icc (0 : ℝ) 1 :=
      ae_all_iff.2 fun i => condExp_indicator_mem_Icc (ℱ.le k) (hA i)
    filter_upwards [h] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => (negMulLog_mem_Icc (hx i)).1)]
    calc ∑ i, Real.negMulLog ((μ⟦A i | ℱ k⟧) x) ≤ ∑ _i : ι, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => (negMulLog_mem_Icc (hx i)).2
      _ = Fintype.card ι := by simp
  · have h : ∀ᵐ x ∂μ, ∀ i, Tendsto (fun k => (μ⟦A i | ℱ k⟧) x) atTop
        (𝓝 ((μ⟦A i | ⨆ k, ℱ k⟧) x)) :=
      ae_all_iff.2 fun i => tendsto_ae_condExp _
    filter_upwards [h] with x hx
    exact tendsto_finsetSum _ fun i _ =>
      (Real.continuous_negMulLog.tendsto _).comp (hx i)

end Limit

section PastEntropy

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]

theorem integral_sum_negMulLog_condExp_past (hinv : MeasurePreserving (shift 1) μ μ) :
    ∫ x, ∑ a, Real.negMulLog
      ((μ⟦{y | y 0 = a} | MeasurableSpace.comap (past : (ℤ → α) → ℕ → α) inferInstance⟧) x) ∂μ =
      entropy μ := by
  have hlim := (tendsto_integral_sum_negMulLog_condExp (μ := μ) (pastFiltration α)
    (A := fun a : α => {y : ℤ → α | y 0 = a}) measurableSet_coord_zero_eq).cesaro
  rw [iSup_pastFiltration] at hlim
  refine tendsto_nhds_unique hlim ((tendsto_entropy hinv).congr fun n => ?_)
  simp_rw [integral_sum_negMulLog_condExp_pastFiltration hinv]
  rw [Finset.sum_range_sub (blockEntropy μ), blockEntropy_zero, sub_zero, div_eq_inv_mul]

end PastEntropy

section Kernel

open scoped ENNReal

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

theorem lintegral_mul_condExpKernel_apply (hm : m ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ]
    {h : Ω → ℝ≥0∞} (hh : Measurable[m] h) {A : Set Ω} (hA : MeasurableSet A) :
    ∫⁻ x, h x * condExpKernel μ m x A ∂μ = ∫⁻ x in A, h x ∂μ := by
  have hF : Measurable[m.prod mΩ] fun p : Ω × Ω => h p.1 * A.indicator 1 p.2 :=
    (hh.comp measurable_fst).mul ((measurable_one.indicator hA).comp measurable_snd)
  have hd : @Measurable Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag :=
    (measurable_id'' hm).prodMk measurable_id
  have h1 := Measure.lintegral_compProd (μ := μ.trim hm) (κ := condExpKernel μ m) hF
  rw [compProd_trim_condExpKernel hm, @lintegral_map Ω (Ω × Ω) mΩ (m.prod mΩ) μ _ _ hF hd,
    lintegral_trim hm (hF.lintegral_kernel_prod_right' (κ := condExpKernel μ m))] at h1
  simp only [Function.diag_apply] at h1
  rw [← lintegral_indicator hA]
  calc ∫⁻ x, h x * condExpKernel μ m x A ∂μ
      = ∫⁻ x, ∫⁻ y, h x * A.indicator 1 y ∂condExpKernel μ m x ∂μ :=
        lintegral_congr fun x => by
          rw [lintegral_const_mul _ (measurable_one.indicator hA), lintegral_indicator_one hA]
    _ = ∫⁻ x, h x * A.indicator 1 x ∂μ := h1.symm
    _ = ∫⁻ x, A.indicator h x ∂μ :=
        lintegral_congr fun x => by by_cases hx : x ∈ A <;> simp [hx]

end Kernel

section CondEntropy

open scoped ENNReal

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem condEntropy_eq_integral_sum_negMulLog (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (ξ : (ℤ → α) → Set (ℤ → α)) :
    condEntropy μ ξ =
      ∫ x, ∑ a, Real.negMulLog ((μ⟦{y | y 0 = a} | saturated ξ⟧) x) ∂μ := by
  have hm := saturated_le (Ω := ℤ → α) ξ
  set q : α → (ℤ → α) → ℝ := fun a x => (condMeas μ ξ x).real {y | y 0 = a}
  have hqm : ∀ a, Measurable[saturated ξ] (q a) := fun a =>
    (measurable_condMeas μ ξ (measurableSet_coord_zero_eq a)).ennreal_toReal
  have hq01 : ∀ a x, q a x ∈ Icc (0 : ℝ) 1 := fun a x => ⟨measureReal_nonneg, measureReal_le_one⟩

  have hR : ∫ x, ∑ a, Real.negMulLog ((μ⟦{y | y 0 = a} | saturated ξ⟧) x) ∂μ =
      ∫ x, ∑ a, Real.negMulLog (q a x) ∂μ := by
    have hae : ∀ᵐ x ∂μ, ∀ a, q a x = (μ⟦{y | y 0 = a} | saturated ξ⟧) x :=
      ae_all_iff.2 fun a => condExpKernel_ae_eq_condExp hm (measurableSet_coord_zero_eq a)
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    exact Finset.sum_congr rfl fun a _ => by rw [hx a]
  set ℓ : α → (ℤ → α) → ℝ≥0∞ := fun a x => ENNReal.ofReal (-Real.log (q a x)) with hℓ
  have hℓm : ∀ a, Measurable[saturated ξ] (ℓ a) := fun a =>
    ((Real.measurable_log.comp (hqm a)).neg).ennreal_ofReal

  have hI : ∀ x, ENNReal.ofReal (condInfo μ ξ x) =
      ∑ a, ({y : ℤ → α | y 0 = a}).indicator (ℓ a) x := fun x => by
    rw [Finset.sum_eq_single (x 0) (fun a _ ha => indicator_of_notMem (fun h => ha h.symm) _)
      (fun h => absurd (Finset.mem_univ _) h), indicator_of_mem (by exact rfl)]
    rfl
  have hIm : Measurable (condInfo μ ξ) := by
    have : condInfo μ ξ = fun x => ∑ a,
        ({y : ℤ → α | y 0 = a}).indicator (fun x => -Real.log (q a x)) x := by
      funext x
      rw [Finset.sum_eq_single (x 0) (fun a _ ha => indicator_of_notMem (fun h => ha h.symm) _)
        (fun h => absurd (Finset.mem_univ _) h), indicator_of_mem (by exact rfl)]
      rfl
    rw [this]
    exact Finset.measurable_sum _ fun a _ =>
      (((Real.measurable_log.comp (hqm a)).neg).mono hm le_rfl).indicator
        (measurableSet_coord_zero_eq a)
  have hGm : Measurable fun x => ∑ a, Real.negMulLog (q a x) :=
    Finset.measurable_sum _ fun a _ =>
      (Real.continuous_negMulLog.measurable.comp (hqm a)).mono hm le_rfl
  rw [hR, condEntropy, integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun x => condInfo_nonneg μ ξ x) hIm.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => Finset.sum_nonneg fun a _ =>
      (negMulLog_mem_Icc (hq01 a x)).1) hGm.aestronglyMeasurable]
  congr 1
  calc ∫⁻ x, ENNReal.ofReal (condInfo μ ξ x) ∂μ
      = ∑ a, ∫⁻ x, ({y : ℤ → α | y 0 = a}).indicator (ℓ a) x ∂μ := by
        simp_rw [hI]
        exact lintegral_finsetSum _ fun a _ =>
          ((hℓm a).mono hm le_rfl).indicator (measurableSet_coord_zero_eq a)
    _ = ∑ a, ∫⁻ x, ENNReal.ofReal (Real.negMulLog (q a x)) ∂μ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [lintegral_indicator (measurableSet_coord_zero_eq a),
          ← lintegral_mul_condExpKernel_apply hm μ (hℓm a) (measurableSet_coord_zero_eq a)]
        refine lintegral_congr fun x => ?_
        have e : condExpKernel μ (saturated ξ) x {y | y 0 = a} = ENNReal.ofReal (q a x) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
        rw [e, hℓ, ← ENNReal.ofReal_mul (neg_nonneg.2 (Real.log_nonpos (hq01 a x).1 (hq01 a x).2)),
          Real.negMulLog]
        congr 1
        ring
    _ = ∫⁻ x, ENNReal.ofReal (∑ a, Real.negMulLog (q a x)) ∂μ := by
        simp_rw [ENNReal.ofReal_sum_of_nonneg fun a _ => (negMulLog_mem_Icc (hq01 a _)).1]
        exact (lintegral_finsetSum _ fun a _ =>
          ((Real.continuous_negMulLog.measurable.comp (hqm a)).mono hm le_rfl).ennreal_ofReal).symm

end CondEntropy

section Compare

variable {Ω : Type*} {m₁ m₂ m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]

theorem condExp_ae_eq_of_inter_eq (hm₁ : m₁ ≤ m0) (hm₂ : m₂ ≤ m0) {D : Set Ω}
    (hD : μ Dᶜ = 0) (h₂₁ : ∀ B, MeasurableSet[m₂] B → MeasurableSet[m₁] (B ∩ D))
    (h₁₂ : ∀ B, MeasurableSet[m₁] B → ∃ B', MeasurableSet[m₂] B' ∧ B' ∩ D = B ∩ D)
    {g : Ω → ℝ} (hg : Integrable g μ) : μ[g | m₁] =ᵐ[μ] μ[g | m₂] := by
  have hDae : ∀ᵐ x ∂μ, x ∈ D := by
    rw [← compl_compl D, ← mem_ae_iff] at hD
    simpa using hD
  have hDm : MeasurableSet[m₁] D := by simpa using h₂₁ univ MeasurableSet.univ
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm₁ hg
    (fun s _ _ => integrable_condExp.integrableOn) (fun B hB _ => ?_) ?_).symm
  · obtain ⟨B', hB', hBB'⟩ := h₁₂ B hB
    have hae : B =ᵐ[μ] B' := by
      filter_upwards [hDae] with x hx
      have h1 : x ∈ B' ∩ D ↔ x ∈ B ∩ D := by rw [hBB']
      simp only [mem_inter_iff, hx, and_true] at h1
      exact propext h1.symm
    rw [setIntegral_congr_set hae, setIntegral_condExp hm₂ hg hB', setIntegral_congr_set hae]
  · refine ⟨D.indicator (μ[g | m₂]), ?_, ?_⟩
    · refine Measurable.stronglyMeasurable ?_
      intro U hU
      have hpre : MeasurableSet[m₁] ((μ[g | m₂]) ⁻¹' U ∩ D) :=
        h₂₁ _ (stronglyMeasurable_condExp.measurable hU)
      rw [indicator_preimage, Set.ite]
      refine hpre.union ?_
      by_cases h0 : (0 : ℝ) ∈ U
      · have : (0 : Ω → ℝ) ⁻¹' U = univ := by ext x; simp [h0]
        rw [this, ← compl_eq_univ_sdiff]
        exact hDm.compl
      · have : (0 : Ω → ℝ) ⁻¹' U = ∅ := by ext x; simp [h0]
        rw [this, empty_sdiff]
        exact @MeasurableSet.empty Ω m₁
    · filter_upwards [hDae] with x hx
      rw [indicator_of_mem hx]

end Compare

section PastPartition

variable {α : Type*} [MeasurableSpace α]

theorem measurableSet_saturated_inter_of_past {D : Set (ℤ → α)} (hD : MeasurableSet D)
    {B : Set (ℤ → α)}
    (hB : MeasurableSet[MeasurableSpace.comap (past : (ℤ → α) → ℕ → α) inferInstance] B) :
    MeasurableSet[saturated (atomsOn D fun x => {y | SamePast y x})] (B ∩ D) := by
  obtain ⟨T, hT, rfl⟩ := hB
  refine ⟨(measurable_past hT).inter hD, fun x y hy => ?_⟩
  by_cases hx : x ∈ D
  · rw [atomsOn_of_mem hx] at hy
    obtain ⟨hp, hyD⟩ := hy
    have e : past y = past x := past_eq_iff.2 hp
    simp [hx, hyD, e]
  · rw [atomsOn_of_notMem hx] at hy
    have hyD : y ∉ D := hy
    simp [hx, hyD]

variable [Fintype α] [MeasurableSingletonClass α]

theorem exists_measurableSet_past_inter_eq {D : Set (ℤ → α)} (hD : MeasurableSet D)
    {B : Set (ℤ → α)}
    (hB : MeasurableSet[saturated (atomsOn D fun x => {y | SamePast y x})] B) :
    ∃ B', MeasurableSet[MeasurableSpace.comap (past : (ℤ → α) → ℕ → α) inferInstance] B' ∧
      B' ∩ D = B ∩ D := by
  classical
  have he := measurableEmbedding_embeddingReal (ℕ → α)
  set e : (ℕ → α) → ℝ := fun p => Real.exp (embeddingReal (ℕ → α) p) with he_def
  have hem : Measurable e := Real.measurable_exp.comp he.measurable
  have hinj : ∀ p p', e p = e p' ↔ p = p' := fun p p' => by
    simp only [he_def, Real.exp_eq_exp, he.injective.eq_iff]
  have hpos : ∀ p, e p ≠ 0 := fun p => (Real.exp_pos _).ne'
  set f : (ℤ → α) → ℝ := fun x => if x ∈ D then e (past x) else 0 with hf_def
  have hf : Measurable f := Measurable.ite hD (hem.comp measurable_past) measurable_const
  have hξ : ∀ x y, y ∈ atomsOn D (fun x => {y | SamePast y x}) x ↔ f y = f x := by
    intro x y
    by_cases hx : x ∈ D
    · rw [atomsOn_of_mem hx]
      by_cases hy : y ∈ D
      · simp [hf_def, hx, hy, hinj, past_eq_iff]
      · simp [hf_def, hx, hy, (hpos _).symm]
    · rw [atomsOn_of_notMem hx]
      by_cases hy : y ∈ D
      · simp [hf_def, hx, hy, hpos]
      · simp [hf_def, hx, hy]
  rw [saturated_eq_comap hf hξ] at hB
  obtain ⟨T, hT, rfl⟩ := hB
  refine ⟨past ⁻¹' (e ⁻¹' T), ⟨e ⁻¹' T, hem hT, rfl⟩, ?_⟩
  ext x
  by_cases hx : x ∈ D <;> simp [hx, hf_def]

theorem condEntropy_atomsOn_samePast {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) {D : Set (ℤ → α)} (hD : MeasurableSet D)
    (hfull : μ Dᶜ = 0) :
    condEntropy μ (atomsOn D fun x => {y | SamePast y x}) = entropy μ := by
  rw [condEntropy_eq_integral_sum_negMulLog, ← integral_sum_negMulLog_condExp_past hinv]
  have hae : ∀ᵐ x ∂μ, ∀ a : α,
      (μ⟦{y | y 0 = a} | saturated (atomsOn D fun x => {y | SamePast y x})⟧) x =
        (μ⟦{y | y 0 = a} |
          MeasurableSpace.comap (past : (ℤ → α) → ℕ → α) inferInstance⟧) x :=
    ae_all_iff.2 fun a => condExp_ae_eq_of_inter_eq (saturated_le _) measurable_past.comap_le
      hfull (fun _ hB => measurableSet_saturated_inter_of_past hD hB)
      (fun _ hB => exists_measurableSet_past_inter_eq hD hB)
      ((integrable_const (1 : ℝ)).indicator (measurableSet_coord_zero_eq a))
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  exact Finset.sum_congr rfl fun a _ => by rw [hx a]

end PastPartition

end FractalGeometry
