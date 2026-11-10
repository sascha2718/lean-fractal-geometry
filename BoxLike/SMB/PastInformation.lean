module

/-
The information functions of the finite pasts and Chung's maximal inequality: the analytic
input of Breiman's proof of the Shannon–McMillan–Breiman theorem that `sec:entropies` cites
before `thm:feng_entropy_kolmogorov_sinai` (tex lines 1885 to 1889).

For a probability measure `μ` on `ℤ → α`, `α` finite, write
`p_k(a, x) = μ(x_0 = a | x_{-k} ⋯ x_{-1})` for the elementary conditional probability given the
last `k` symbols and `I_k(x) = -log p_k(x_0, x)` for the information of the coordinate zero
given the last `k` symbols. Chung's maximal inequality bounds
`μ(x_0 = a, inf_k p_k(a, x) < c) ≤ c` by a stopping-time decomposition, so
`μ(sup_k I_k > t) ≤ #α e^{-t}` and `∫ sup_k I_k dμ ≤ #α` by the layer-cake formula. Lévy's upward
theorem gives `I_k → I_μ(𝒫 | 𝒫^-)` almost everywhere, the conditional information of the
coordinate zero given the past, computed with the partition by the past of any Borel set of
full measure.

* `pastCondProb`, `pastInfo`: `p_k(a, x)` and `I_k(x)`.
* `pastCondProb_nonneg`, `pastCondProb_le_one`, `pastInfo_nonneg`,
  `measurable_pastCondProb`, `measurable_pastInfo`: elementary properties.
* `condExp_ae_eq_pastCondProb`: `p_k(a, ·)` is the conditional probability of `[a]` given
  `x_{-k} ⋯ x_{-1}`.
* `measure_inter_iUnion_pastCondProb_lt_le`: Chung's maximal inequality.
* `measure_exists_lt_pastInfo_le`: `μ(sup_k I_k > t) ≤ #α e^{-t}`.
* `pastInfoMax`, `lintegral_iSup_pastInfo_le`: `∫ sup_k I_k dμ ≤ #α`.
* `pastInfoSup`, `integrable_pastInfoSup`, `abs_pastInfo_le_pastInfoSup`: the integrable
  majorant of the `I_k`.
* `tendsto_pastInfo`: `I_k → I_μ(𝒫 | 𝒫^-)` almost everywhere.
-/
public import BoxLike.FengEntropy
public import BoxLike.PastEntropy
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Layercake

@[expose] public section

namespace BoxLike

open MeasureTheory ProbabilityTheory Filter Topology Set

section PastInfo

variable {α : Type*} [MeasurableSpace α]

/-- The conditional probability `p_k(a, x) = μ(x_0 = a | x_{-k} ⋯ x_{-1})` of the symbol `a` at
time zero given the `k` symbols before time zero (`sec:entropies`, tex lines 1885 to 1889),
the ratio `μ([x_{-k} ⋯ x_{-1} a]) / μ([x_{-k} ⋯ x_{-1}])` of the measures of the sets fixing
these coordinates. -/
noncomputable def pastCondProb (μ : Measure (ℤ → α)) (k : ℕ) (a : α) (x : ℤ → α) : ℝ :=
  μ.real ({y | y 0 = a} ∩ pastBlock k ⁻¹' {pastBlock k x}) /
    μ.real (pastBlock k ⁻¹' {pastBlock k x})

/-- The information `I_k(x) = -log μ(x_0 | x_{-k} ⋯ x_{-1})` of the coordinate zero given the
`k` symbols before time zero (`sec:entropies`, tex lines 1885 to 1889). Lean's `log 0 = 0` gives
`0` where the conditional probability vanishes, which happens on a null set. -/
noncomputable def pastInfo (μ : Measure (ℤ → α)) (k : ℕ) (x : ℤ → α) : ℝ :=
  -Real.log (pastCondProb μ k (x 0) x)

/-- `p_k(a, x) ≥ 0`. -/
theorem pastCondProb_nonneg (μ : Measure (ℤ → α)) (k : ℕ) (a : α) (x : ℤ → α) :
    0 ≤ pastCondProb μ k a x :=
  div_nonneg measureReal_nonneg measureReal_nonneg

/-- `p_k(a, x) ≤ 1`. -/
theorem pastCondProb_le_one (μ : Measure (ℤ → α)) [IsFiniteMeasure μ] (k : ℕ) (a : α)
    (x : ℤ → α) : pastCondProb μ k a x ≤ 1 :=
  div_le_one_of_le₀ (measureReal_mono inter_subset_right) measureReal_nonneg

/-- `I_k(x) ≥ 0`. -/
theorem pastInfo_nonneg (μ : Measure (ℤ → α)) [IsFiniteMeasure μ] (k : ℕ) (x : ℤ → α) :
    0 ≤ pastInfo μ k x :=
  neg_nonneg.2 (Real.log_nonpos (pastCondProb_nonneg μ k _ x) (pastCondProb_le_one μ k _ x))

variable [Fintype α] [MeasurableSingletonClass α]

/-- `p_k(a, ·)` is a function of `x_{-k} ⋯ x_{-1}`, hence measurable with respect to the
`k`-th `σ`-algebra of the filtration of the finite pasts. -/
theorem measurable_pastCondProb (μ : Measure (ℤ → α)) (k : ℕ) (a : α) :
    Measurable[pastFiltration α k] (pastCondProb μ k a) :=
  (measurable_of_countable (fun v : Fin k → α => μ.real ({y | y 0 = a} ∩ pastBlock k ⁻¹' {v}) /
    μ.real (pastBlock k ⁻¹' {v}))).comp (comap_measurable (pastBlock k))

/-- `I_k` is measurable: it is a function of `x_0` and `x_{-k} ⋯ x_{-1}`. -/
theorem measurable_pastInfo (μ : Measure (ℤ → α)) (k : ℕ) : Measurable (pastInfo μ k) := by
  have h : Measurable fun p : α × (ℤ → α) => pastCondProb μ k p.1 p.2 :=
    measurable_from_prod_countable_right fun a =>
      (measurable_pastCondProb μ k a).mono ((pastFiltration α).le k) le_rfl
  have hg : Measurable fun x : ℤ → α => (x 0, x) :=
    (measurable_pi_apply (0 : ℤ)).prodMk measurable_id
  have h2 : Measurable fun x : ℤ → α => pastCondProb μ k (x 0) x := h.comp hg
  show Measurable fun x => -Real.log (pastCondProb μ k (x 0) x)
  exact (Real.measurable_log.comp h2).neg

/-- `p_k(a, ·)` is the conditional probability of the cylinder `[a]` given the `σ`-algebra of
`x_{-k} ⋯ x_{-1}`. -/
theorem condExp_ae_eq_pastCondProb (μ : Measure (ℤ → α)) [IsFiniteMeasure μ] (k : ℕ) (a : α) :
    μ⟦{y | y 0 = a} | pastFiltration α k⟧ =ᵐ[μ] pastCondProb μ k a :=
  condExp_indicator_comap_fintype (B := Fin k → α) (measurable_pastBlock k)
    (measurableSet_coord_zero_eq a)

end PastInfo

/-! ### Chung's maximal inequality -/

section Chung

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ : Measure (ℤ → α)}

/-- The stopping-time step of Chung's maximal inequality: on a set `B` of the `k`-th
`σ`-algebra of the finite pasts on which `p_k(a, ·) < c`, the cylinder `[a]` has measure at
most `c μ(B)`. -/
theorem measureReal_inter_le_of_pastCondProb_lt [IsFiniteMeasure μ] {k : ℕ} {a : α} {c : ℝ}
    {B : Set (ℤ → α)} (hB : MeasurableSet[pastFiltration α k] B)
    (hlt : ∀ x ∈ B, pastCondProb μ k a x < c) :
    μ.real ({y | y 0 = a} ∩ B) ≤ c * μ.real B := by
  have hA := measurableSet_coord_zero_eq (α := α) a
  have hBm : MeasurableSet B := (pastFiltration α).le k _ hB
  have hint : IntegrableOn (pastCondProb μ k a) B μ :=
    (Integrable.of_bound ((measurable_pastCondProb μ k a).mono ((pastFiltration α).le k)
      le_rfl).aestronglyMeasurable 1 (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pastCondProb_nonneg μ k a x)]
        exact pastCondProb_le_one μ k a x)).integrableOn
  calc μ.real ({y | y 0 = a} ∩ B)
      = ∫ x in B, ({y : ℤ → α | y 0 = a}).indicator (fun _ => (1 : ℝ)) x ∂μ := by
        rw [integral_indicator_const _ hA, smul_eq_mul, mul_one, measureReal_restrict_apply hA]
    _ = ∫ x in B, (μ⟦{y | y 0 = a} | pastFiltration α k⟧) x ∂μ :=
        (setIntegral_condExp ((pastFiltration α).le k)
          ((integrable_const (1 : ℝ)).indicator hA) hB).symm
    _ = ∫ x in B, pastCondProb μ k a x ∂μ :=
        setIntegral_congr_ae hBm ((condExp_ae_eq_pastCondProb μ k a).mono fun x hx _ => hx)
    _ ≤ ∫ _ in B, c ∂μ :=
        setIntegral_mono_on hint (integrableOn_const (measure_ne_top _ _)) hBm
          fun x hx => (hlt x hx).le
    _ = c * μ.real B := by rw [setIntegral_const, smul_eq_mul, mul_comm]

/-- Chung's maximal inequality (K. L. Chung, Ann. Math. Statist. 32 (1961)), the key estimate of
the Shannon–McMillan–Breiman theorem cited in `sec:entropies`, tex lines 1885 to 1889: for every
symbol `a` and every `c ≥ 0`,
`μ(x_0 = a, inf_k μ(x_0 = a | x_{-k} ⋯ x_{-1}) < c) ≤ c`. The sets on which the infimum first
drops below `c` at time `k` are disjoint and lie in the `k`-th `σ`-algebra of the finite pasts. -/
theorem measure_inter_iUnion_pastCondProb_lt_le [IsProbabilityMeasure μ] (a : α) {c : ℝ}
    (hc : 0 ≤ c) :
    μ ({y | y 0 = a} ∩ ⋃ k, {x | pastCondProb μ k a x < c}) ≤ ENNReal.ofReal c := by
  set E : ℕ → Set (ℤ → α) := fun k => {x | pastCondProb μ k a x < c} with hE
  have hEm : ∀ k, MeasurableSet[pastFiltration α k] (E k) := fun k =>
    measurable_pastCondProb μ k a measurableSet_Iio
  -- the first time the conditional probability drops below `c`
  set D : ℕ → Set (ℤ → α) := fun k => E k ∩ ⋂ j ∈ Finset.range k, (E j)ᶜ with hD
  have hDm : ∀ k, MeasurableSet[pastFiltration α k] (D k) := fun k =>
    (hEm k).inter (MeasurableSet.biInter (Finset.range k).countable_toSet fun j hj =>
      ((pastFiltration α).mono (Finset.mem_range.1 hj).le _ (hEm j)).compl)
  have hDm' : ∀ k, MeasurableSet (D k) := fun k => (pastFiltration α).le k _ (hDm k)
  have hdisj : Pairwise (Function.onFun Disjoint D) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro x hxi hxj
    rcases lt_or_gt_of_ne hij with h | h
    · exact (Set.mem_iInter₂.1 hxj.2 i (Finset.mem_range.2 h)) hxi.1
    · exact (Set.mem_iInter₂.1 hxi.2 j (Finset.mem_range.2 h)) hxj.1
  have hunion : ⋃ k, E k = ⋃ k, D k := by
    refine Subset.antisymm (fun x hx => ?_) (iUnion_mono fun k => inter_subset_left)
    classical
    have hex : ∃ k, x ∈ E k := mem_iUnion.1 hx
    refine mem_iUnion.2 ⟨Nat.find hex, Nat.find_spec hex, Set.mem_iInter₂.2 fun j hj => ?_⟩
    exact Nat.find_min hex (Finset.mem_range.1 hj)
  have hstep : ∀ k, μ ({y | y 0 = a} ∩ D k) ≤ ENNReal.ofReal c * μ (D k) := fun k => by
    have h := measureReal_inter_le_of_pastCondProb_lt (hDm k) fun x hx => hx.1
    rw [← ofReal_measureReal (measure_ne_top _ _), ← ofReal_measureReal (measure_ne_top μ (D k)),
      ← ENNReal.ofReal_mul hc]
    exact ENNReal.ofReal_le_ofReal h
  calc μ ({y | y 0 = a} ∩ ⋃ k, E k)
      = μ (⋃ k, ({y | y 0 = a} ∩ D k)) := by rw [hunion, inter_iUnion]
    _ = ∑' k, μ ({y | y 0 = a} ∩ D k) :=
        measure_iUnion (fun i j hij => (hdisj hij).mono inter_subset_right inter_subset_right)
          fun k => (measurableSet_coord_zero_eq a).inter (hDm' k)
    _ ≤ ∑' k, ENNReal.ofReal c * μ (D k) := ENNReal.tsum_le_tsum hstep
    _ = ENNReal.ofReal c * μ (⋃ k, D k) := by rw [ENNReal.tsum_mul_left, measure_iUnion hdisj hDm']
    _ ≤ ENNReal.ofReal c := mul_le_of_le_one_right' prob_le_one

/-- The maximal inequality for the information functions: `μ(sup_k I_k > t) ≤ #α e^{-t}` for
every `t ≥ 0`. -/
theorem measure_exists_lt_pastInfo_le [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 ≤ t) :
    μ {x | ∃ k, t < pastInfo μ k x} ≤ Fintype.card α * ENNReal.ofReal (Real.exp (-t)) := by
  have hsub : {x | ∃ k, t < pastInfo μ k x} ⊆
      ⋃ a, ({y | y 0 = a} ∩ ⋃ k, {x | pastCondProb μ k a x < Real.exp (-t)}) := by
    rintro x ⟨k, hk⟩
    refine mem_iUnion.2 ⟨x 0, rfl, mem_iUnion.2 ⟨k, ?_⟩⟩
    have hp0 := pastCondProb_nonneg μ k (x 0) x
    rcases hp0.eq_or_lt with h | h
    · rw [pastInfo, ← h, Real.log_zero, neg_zero] at hk
      exact absurd ht (not_le.2 hk)
    · show pastCondProb μ k (x 0) x < Real.exp (-t)
      rw [← Real.log_lt_iff_lt_exp h]
      rw [pastInfo] at hk
      linarith
  calc μ {x | ∃ k, t < pastInfo μ k x}
      ≤ μ (⋃ a, ({y | y 0 = a} ∩ ⋃ k, {x | pastCondProb μ k a x < Real.exp (-t)})) :=
        measure_mono hsub
    _ ≤ ∑ a, μ ({y | y 0 = a} ∩ ⋃ k, {x | pastCondProb μ k a x < Real.exp (-t)}) :=
        measure_iUnion_fintype_le μ _
    _ ≤ ∑ _a : α, ENNReal.ofReal (Real.exp (-t)) :=
        Finset.sum_le_sum fun a _ => measure_inter_iUnion_pastCondProb_lt_le a (Real.exp_pos _).le
    _ = Fintype.card α * ENNReal.ofReal (Real.exp (-t)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The running maximum `max_{k ≤ K} I_k`. -/
noncomputable def pastInfoMax (μ : Measure (ℤ → α)) (K : ℕ) (x : ℤ → α) : ℝ :=
  (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one fun k => pastInfo μ k x

/-- `∫ sup_k I_k dμ ≤ #α`, from the maximal inequality and the layer-cake formula. This is the
integrability of the supremum of the information functions in Breiman's proof. -/
theorem lintegral_iSup_pastInfo_le [IsProbabilityMeasure μ] :
    ∫⁻ x, ⨆ k, ENNReal.ofReal (pastInfo μ k x) ∂μ ≤ Fintype.card α := by
  have hmax_m : ∀ K, Measurable (pastInfoMax μ K) := fun K =>
    Finset.measurable_range_sup'' fun k _ => measurable_pastInfo μ k
  have hmax_nonneg : ∀ K x, 0 ≤ pastInfoMax μ K x := fun K x =>
    (pastInfo_nonneg μ 0 x).trans (Finset.le_sup' (fun k => pastInfo μ k x)
      (Finset.mem_range.2 (Nat.succ_pos K)))
  have heq : ∀ x, ⨆ k, ENNReal.ofReal (pastInfo μ k x) =
      ⨆ K, ENNReal.ofReal (pastInfoMax μ K x) := fun x => by
    refine le_antisymm (iSup_le fun k => le_iSup_of_le k (ENNReal.ofReal_le_ofReal ?_))
      (iSup_le fun K => ?_)
    · exact Finset.le_sup' (fun k => pastInfo μ k x) (Finset.mem_range.2 (Nat.lt_succ_self k))
    · obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
        fun k => pastInfo μ k x
      rw [pastInfoMax, hk]
      exact le_iSup (fun k => ENNReal.ofReal (pastInfo μ k x)) k
  have hmono : Monotone fun K x => ENNReal.ofReal (pastInfoMax μ K x) := by
    intro K K' hKK' x
    refine ENNReal.ofReal_le_ofReal (Finset.sup'_le _ _ fun k hk => ?_)
    exact Finset.le_sup' (fun k => pastInfo μ k x)
      (Finset.mem_range.2 ((Finset.mem_range.1 hk).trans_le (Nat.succ_le_succ hKK')))
  have hexp : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t)) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 0)
      (ae_of_all _ fun t => (Real.exp_pos _).le), integral_exp_neg_Ioi_zero, ENNReal.ofReal_one]
  have hK : ∀ K, ∫⁻ x, ENNReal.ofReal (pastInfoMax μ K x) ∂μ ≤ Fintype.card α := fun K => by
    rw [lintegral_eq_lintegral_meas_lt μ (ae_of_all _ (hmax_nonneg K))
      (hmax_m K).aemeasurable]
    calc ∫⁻ t in Ioi 0, μ {x | t < pastInfoMax μ K x}
        ≤ ∫⁻ t in Ioi (0 : ℝ), Fintype.card α * ENNReal.ofReal (Real.exp (-t)) := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
          refine (measure_mono fun x hx => ?_).trans
            (measure_exists_lt_pastInfo_le (le_of_lt (mem_Ioi.1 ht)))
          obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
            fun k => pastInfo μ k x
          have hx' : t < pastInfoMax μ K x := hx
          rw [pastInfoMax, hk] at hx'
          exact ⟨k, hx'⟩
      _ = Fintype.card α := by
          rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _), hexp, mul_one]
  simp_rw [heq]
  rw [lintegral_iSup (fun K => (hmax_m K).ennreal_ofReal) hmono]
  exact iSup_le hK

/-- The majorant `sup_k I_k` of the information functions, read as a real number. -/
noncomputable def pastInfoSup (μ : Measure (ℤ → α)) (x : ℤ → α) : ℝ :=
  (⨆ k, ENNReal.ofReal (pastInfo μ k x)).toReal

/-- The supremum of the information functions is measurable in `[0, ∞]`. -/
theorem measurable_iSup_pastInfo (μ : Measure (ℤ → α)) :
    Measurable fun x => ⨆ k, ENNReal.ofReal (pastInfo μ k x) :=
  Measurable.iSup fun k => (measurable_pastInfo μ k).ennreal_ofReal

/-- The supremum of the information functions is integrable (Breiman's lemma). -/
theorem integrable_pastInfoSup [IsProbabilityMeasure μ] : Integrable (pastInfoSup μ) μ :=
  integrable_toReal_of_lintegral_ne_top (measurable_iSup_pastInfo μ).aemeasurable
    (ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) lintegral_iSup_pastInfo_le)

/-- Almost everywhere, every information function is bounded by the integrable majorant. -/
theorem abs_pastInfo_le_pastInfoSup [IsProbabilityMeasure μ] :
    ∀ᵐ x ∂μ, ∀ k, |pastInfo μ k x| ≤ pastInfoSup μ x := by
  filter_upwards [ae_lt_top (measurable_iSup_pastInfo μ)
    (ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) lintegral_iSup_pastInfo_le)] with x hx k
  rw [abs_of_nonneg (pastInfo_nonneg μ k x)]
  exact (ENNReal.ofReal_le_iff_le_toReal hx.ne).1
    (le_iSup (fun k => ENNReal.ofReal (pastInfo μ k x)) k)

/-! ### Convergence to the information given the past -/

/-- Lévy's upward theorem for the information functions: `I_k(x) → I_μ(𝒫 | 𝒫^-)(x)` for
`μ`-almost every `x`, where the limit is the conditional information of the coordinate zero given
the partition by the past of a Borel set `D` of full measure, extended by the atom `Ω ∖ D`
(`sec:entropies`). With `D` the set `Σ'`, the limit is the conditional information
`I_μ(𝒫 | \widehat{ξ}_0)` of the definition of `h_0(μ, 𝐢)`. -/
theorem tendsto_pastInfo [IsProbabilityMeasure μ] {D : Set (ℤ → α)} (hD : MeasurableSet D)
    (hfull : μ Dᶜ = 0) :
    ∀ᵐ x ∂μ, Tendsto (fun k => pastInfo μ k x) atTop
      (𝓝 (condInfo μ (atomsOn D fun x => {y | SamePast y x}) x)) := by
  set ξ := atomsOn D fun x => {y : ℤ → α | SamePast y x} with hξ
  have hA : ∀ a : α, MeasurableSet {y : ℤ → α | y 0 = a} := measurableSet_coord_zero_eq
  have h1 : ∀ᵐ x ∂μ, ∀ a k, (μ⟦{y | y 0 = a} | pastFiltration α k⟧) x = pastCondProb μ k a x :=
    ae_all_iff.2 fun a => ae_all_iff.2 fun k => condExp_ae_eq_pastCondProb μ k a
  have h2 : ∀ᵐ x ∂μ, ∀ a, Tendsto (fun k => (μ⟦{y | y 0 = a} | pastFiltration α k⟧) x) atTop
      (𝓝 ((μ⟦{y | y 0 = a} | ⨆ k, pastFiltration α k⟧) x)) :=
    ae_all_iff.2 fun a => tendsto_ae_condExp _
  have h3 : ∀ᵐ x ∂μ, ∀ a, (μ⟦{y | y 0 = a} | ⨆ k, pastFiltration α k⟧) x =
      (μ⟦{y | y 0 = a} | saturated ξ⟧) x := by
    rw [iSup_pastFiltration]
    exact ae_all_iff.2 fun a => (condExp_ae_eq_of_inter_eq (saturated_le _)
      measurable_past.comap_le hfull (fun _ hB => measurableSet_saturated_inter_of_past hD hB)
      (fun _ hB => exists_measurableSet_past_inter_eq hD hB)
      ((integrable_const (1 : ℝ)).indicator (hA a))).symm
  have h4 : ∀ᵐ x ∂μ, ∀ a, (condMeas μ ξ x).real {y | y 0 = a} =
      (μ⟦{y | y 0 = a} | saturated ξ⟧) x :=
    ae_all_iff.2 fun a => condExpKernel_ae_eq_condExp (saturated_le ξ) (hA a)
  have h5 : ∀ᵐ x ∂μ, ∀ a, x ∈ {y : ℤ → α | y 0 = a} → 0 < condMeas μ ξ x {y | y 0 = a} :=
    ae_all_iff.2 fun a => condMeas_pos_of_mem μ ξ (hA a)
  filter_upwards [h1, h2, h3, h4, h5] with x hx1 hx2 hx3 hx4 hx5
  have hpos : 0 < (condMeas μ ξ x).real {y | y 0 = x 0} :=
    ENNReal.toReal_pos (hx5 (x 0) rfl).ne' (measure_ne_top _ _)
  have hlim : Tendsto (fun k => pastCondProb μ k (x 0) x) atTop
      (𝓝 ((condMeas μ ξ x).real {y | y 0 = x 0})) := by
    rw [hx4 (x 0), ← hx3 (x 0)]
    exact (hx2 (x 0)).congr fun k => hx1 (x 0) k
  exact ((Real.continuousAt_log hpos.ne').tendsto.comp hlim).neg

end Chung

end BoxLike
