/-
# Section 3.3: Ahlfors regular measures

Ahlfors regular measures and sets in a metric space, and the comparison of an Ahlfors regular
measure with Hausdorff measure. The examples after Proposition 3.10 (intervals and Cantor sets) are
in `GeometricMeasureTheory.Covering.AhlforsRegularExamples`.

| Notes | Lean declaration | Location |
|---|---|---|
| Definition 3.9 (Ahlfors regular measure and set) | `IsAhlforsRegular`, `IsAhlforsRegularSet` | here |
| Proposition 3.10 (Ahlfors regular measures and `𝓗^s`) | `ahlfors_hausdorff` | here |
-/
import GeometricMeasureTheory.Covering.DensityComparison

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Definition 3.9 (`def:ahlfors-regular`): a Radon measure `μ` supported on the closed set `E`,
which has at least two points, is Ahlfors `s`-regular with constant `C ≥ 1` if
`C⁻¹ r^s ≤ μ(B(x, r)) ≤ C r^s` for every `x ∈ E` and `0 < r ≤ diam E`. For unbounded `E` every
positive radius is allowed, since then `diam E = ∞`. -/
structure IsAhlforsRegular (μ : Measure X) (s : ℝ) (E : Set X) (C : ℝ≥0) : Prop where
  isClosed : IsClosed E
  nontrivial : E.Nontrivial
  pos : 0 < s
  regular : μ.Regular
  support_eq : μ.support = E
  one_le : 1 ≤ C
  le_measure_ball : ∀ x ∈ E, ∀ r : ℝ, 0 < r → ENNReal.ofReal r ≤ ediam E →
    ENNReal.ofReal r ^ s ≤ C * μ (ball x r)
  measure_ball_le : ∀ x ∈ E, ∀ r : ℝ, 0 < r → ENNReal.ofReal r ≤ ediam E →
    μ (ball x r) ≤ C * ENNReal.ofReal r ^ s

/-- Definition 3.9 (`def:ahlfors-regular`): a set is Ahlfors `s`-regular (Ahlfors–David
`s`-regular) if it supports an Ahlfors `s`-regular measure. -/
def IsAhlforsRegularSet (s : ℝ) (E : Set X) : Prop :=
  ∃ (μ : Measure X) (C : ℝ≥0), IsAhlforsRegular μ s E C

/-! ### Auxiliary facts on Ahlfors regular measures -/

omit [BorelSpace X] in
/-- The complement of the support of an Ahlfors regular measure is null: by inner regularity it
suffices to check compact subsets of the complement, which are covered by finitely many null open
sets. -/
theorem IsAhlforsRegular.measure_compl {μ : Measure X} {s : ℝ} {E : Set X} {C : ℝ≥0}
    (hμ : IsAhlforsRegular μ s E C) : μ Eᶜ = 0 := by
  haveI := hμ.regular
  have hopen : IsOpen Eᶜ := hμ.isClosed.isOpen_compl
  refine le_antisymm ?_ bot_le
  rw [Measure.Regular.innerRegular.measure_eq_iSup hopen]
  refine iSup₂_le fun K hKE => iSup_le fun hK => le_of_eq ?_
  refine hK.measure_zero_of_nhdsWithin (μ := μ) fun x hx => ?_
  have hxE : x ∉ μ.support := hμ.support_eq ▸ hKE hx
  obtain ⟨U, hU, hμU⟩ := Measure.notMem_support_iff_exists.1 hxE
  exact ⟨U, mem_nhdsWithin_of_mem_nhds hU, hμU⟩

omit [BorelSpace X] in
/-- An Ahlfors regular measure gives every set the mass of its intersection with the support. -/
theorem IsAhlforsRegular.measure_inter {μ : Measure X} {s : ℝ} {E : Set X} {C : ℝ≥0}
    (hμ : IsAhlforsRegular μ s E C) (A : Set X) : μ (A ∩ E) = μ A :=
  measure_inter_conull hμ.measure_compl

omit [BorelSpace X] in
/-- An Ahlfors regular measure is finite on compact sets. -/
theorem IsAhlforsRegular.measure_lt_top_of_isCompact {μ : Measure X} {s : ℝ} {E : Set X}
    {C : ℝ≥0} (hμ : IsAhlforsRegular μ s E C) {K : Set X} (hK : IsCompact K) : μ K < ∞ := by
  haveI := hμ.regular
  exact hK.measure_lt_top

omit [MeasurableSpace X] [BorelSpace X] in
/-- Every sufficiently small radius is positive and at most the diameter of a non-trivial set. -/
theorem eventually_pos_ofReal_le_ediam {E : Set X} (hE : E.Nontrivial) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r ∧ ENNReal.ofReal r ≤ ediam E := by
  have h0 : Tendsto (fun r : ℝ => ENNReal.ofReal r) (𝓝 0) (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_id (x := 𝓝 (0 : ℝ)))
  exact eventually_mem_nhdsWithin.and
    (nhdsWithin_le_nhds (h0.eventually (eventually_le_nhds (ediam_pos_iff.2 hE))))

/-- The restriction of a measure to a compact set of finite measure is regular: it is weakly
regular as a finite measure on a metric space, and closed subsets may be replaced by their
compact intersections with the set. -/
theorem regular_restrict_of_isCompact {μ : Measure X} {K : Set X} (hK : IsCompact K)
    (hμK : μ K ≠ ∞) : (μ.restrict K).Regular := by
  haveI : IsFiniteMeasure (μ.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμK.lt_top⟩
  have hw : (μ.restrict K).WeaklyRegular := inferInstance
  have hinner : (μ.restrict K).InnerRegularWRT IsCompact IsOpen := by
    intro U hU r hr
    obtain ⟨F, hFU, hF, hrF⟩ := hw.innerRegular hU r hr
    refine ⟨F ∩ K, inter_subset_left.trans hFU, hK.inter_left hF, ?_⟩
    rwa [Measure.restrict_apply' hK.isClosed.measurableSet, inter_assoc, inter_self,
      ← Measure.restrict_apply' hK.isClosed.measurableSet]
  exact
    { toIsFiniteMeasureOnCompacts := inferInstance
      toOuterRegular := inferInstance
      innerRegular := hinner }

/-- Proposition 3.10 (`thm:ahlfors-hausdorff`): on a compact set `E` carrying an Ahlfors
`s`-regular measure with constant `C`, every `A ⊆ E` satisfies `C⁻¹ μ(A) ≤ 𝓗^s(A) ≤ 2^s C μ(A)`.
In particular `0 < 𝓗^s(E) < ∞`, `dim_H E = s`, and `𝓗^s` restricted to `E` is Ahlfors
`s`-regular. -/
theorem ahlfors_hausdorff {μ : Measure X} {s : ℝ} {E : Set X} {C : ℝ≥0}
    (hμ : IsAhlforsRegular μ s E C) (hE : IsCompact E) :
    (∀ A ⊆ E, μ A / C ≤ μH[s] A ∧ μH[s] A ≤ 2 ^ s * C * μ A) ∧
      0 < μH[s] E ∧ μH[s] E < ∞ ∧ dimH E = ENNReal.ofReal s ∧
      ∃ C' : ℝ≥0, IsAhlforsRegular (μH[s].restrict E) s E C' := by
  haveI := hμ.regular
  have hs := hμ.pos
  have hC0 : C ≠ 0 := (zero_lt_one.trans_le hμ.one_le).ne'
  have hC0' : (C : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hC0
  have hsmall := eventually_pos_ofReal_le_ediam hμ.nontrivial
  have hrpow_pos : ∀ r : ℝ, 0 < r → 0 < ENNReal.ofReal r ^ s := fun r hr =>
    ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hr) ENNReal.ofReal_ne_top
  have hrpow_top : ∀ r : ℝ, ENNReal.ofReal r ^ s ≠ ∞ := fun r =>
    (ENNReal.rpow_lt_top_of_nonneg hs.le ENNReal.ofReal_ne_top).ne
  have h2s : (2 : ℝ≥0∞) ^ s ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg hs.le ENNReal.ofNat_ne_top).ne
  have hne_zero : ∀ (K m : ℝ≥0∞) (r : ℝ), 0 < r → ENNReal.ofReal r ^ s ≤ K * m → m ≠ 0 := by
    rintro K m r hr h rfl
    rw [mul_zero] at h
    exact (hrpow_pos r hr).not_ge h
  have hK0 : (2 : ℝ≥0∞) ^ s * C ≠ 0 :=
    mul_ne_zero (ENNReal.rpow_pos two_pos ENNReal.ofNat_ne_top).ne' hC0'
  have hKtop : (2 : ℝ≥0∞) ^ s * C ≠ ∞ := ENNReal.mul_ne_top h2s ENNReal.coe_ne_top
  -- The upper comparison with an additive error.
  have hupper_eps : ∀ A ⊆ E, ∀ ε : ℝ≥0∞, ε ≠ 0 → μH[s] A ≤ 2 ^ s * C * (μ A + ε) := by
    intro A hAE ε hε
    obtain ⟨U, hAU, hUo, hμU⟩ := A.exists_isOpen_le_add μ hε
    have hdens : ∀ x ∈ A, ((C⁻¹ : ℝ≥0) : ℝ≥0∞) ≤
        limsup (fun r : ℝ => μ.restrict U (ball x r) / ENNReal.ofReal r ^ s) (𝓝[>] 0) := by
      intro x hx
      obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hUo x (hAU hx)
      refine le_limsup_of_frequently_le' (Eventually.frequently ?_)
      filter_upwards [hsmall, nhdsWithin_le_nhds (eventually_lt_nhds hδ)] with r hr hrδ
      rw [Measure.restrict_apply measurableSet_ball,
        inter_eq_left.2 ((ball_subset_ball hrδ.le).trans hδU), ENNReal.coe_inv hC0,
        ENNReal.le_div_iff_mul_le (Or.inl (hrpow_pos r hr.1).ne') (Or.inl (hrpow_top r))]
      calc (C : ℝ≥0∞)⁻¹ * ENNReal.ofReal r ^ s
          ≤ (C : ℝ≥0∞)⁻¹ * (C * μ (ball x r)) := by
            gcongr; exact hμ.le_measure_ball x (hAE hx) r hr.1 hr.2
        _ = μ (ball x r) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hC0' ENNReal.coe_ne_top, one_mul]
    have h := (density_comparison (μ.restrict U) hs A (inv_ne_zero hC0)).2 hdens
    rw [Measure.restrict_apply_univ, ENNReal.coe_inv hC0, div_eq_mul_inv, inv_inv,
      mul_right_comm] at h
    exact h.trans (by gcongr)
  have hcomp : ∀ A ⊆ E, μ A / C ≤ μH[s] A ∧ μH[s] A ≤ 2 ^ s * C * μ A := by
    intro A hAE
    refine ⟨(density_comparison μ hs A hC0).1 fun x hx => ?_, ?_⟩
    · refine limsup_le_of_le (by isBoundedDefault) ?_
      filter_upwards [hsmall] with r hr
      exact ENNReal.div_le_of_le_mul (hμ.measure_ball_le x (hAE hx) r hr.1 hr.2)
    · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
      have hε' : (ε : ℝ≥0∞) / (2 ^ s * C) ≠ 0 :=
        ENNReal.div_ne_zero.2 ⟨ENNReal.coe_ne_zero.2 hε.ne', hKtop⟩
      calc μH[s] A ≤ 2 ^ s * C * (μ A + ε / (2 ^ s * C)) := hupper_eps A hAE _ hε'
        _ = 2 ^ s * C * μ A + ε := by rw [mul_add, ENNReal.mul_div_cancel hK0 hKtop]
  refine ⟨hcomp, ?_⟩
  -- Positivity and finiteness of `𝓗^s(E)`.
  have hμE_top : μ E < ∞ := hμ.measure_lt_top_of_isCompact hE
  obtain ⟨x₀, hx₀⟩ := hμ.nontrivial.nonempty
  obtain ⟨r₀, hr₀⟩ := hsmall.exists
  have hμE_pos : 0 < μ E := by
    have hball := hne_zero _ _ r₀ hr₀.1 (hμ.le_measure_ball x₀ hx₀ r₀ hr₀.1 hr₀.2)
    rw [← hμ.measure_inter (ball x₀ r₀)] at hball
    exact (pos_iff_ne_zero.2 hball).trans_le (measure_mono inter_subset_right)
  have hHpos : 0 < μH[s] E :=
    (ENNReal.div_pos hμE_pos.ne' ENNReal.coe_ne_top).trans_le (hcomp E subset_rfl).1
  have hHtop : μH[s] E < ∞ :=
    (hcomp E subset_rfl).2.trans_lt (ENNReal.mul_lt_top hKtop.lt_top hμE_top)
  refine ⟨hHpos, hHtop, ?_, ?_⟩
  · have hs' : (s.toNNReal : ℝ) = s := Real.coe_toNNReal s hs.le
    exact dimH_of_hausdorffMeasure_ne_zero_ne_top (d := s.toNNReal) (s := E)
      (by rw [hs']; exact hHpos.ne') (by rw [hs']; exact hHtop.ne)
  -- Ahlfors regularity of `𝓗^s` restricted to `E`.
  set ν := μH[s].restrict E
  set C' : ℝ≥0 := (2 : ℝ≥0) ^ s * C * C
  have hC' : (C' : ℝ≥0∞) = 2 ^ s * C * C := by
    simp [C', ENNReal.coe_rpow_of_nonneg _ hs.le]
  have hball : ∀ x ∈ E, ∀ r : ℝ, 0 < r → ENNReal.ofReal r ≤ ediam E →
      ENNReal.ofReal r ^ s ≤ C' * ν (ball x r) ∧ ν (ball x r) ≤ C' * ENNReal.ofReal r ^ s := by
    intro x hx r hr hrE
    obtain ⟨hlo, hup⟩ := hcomp (ball x r ∩ E) inter_subset_right
    rw [hμ.measure_inter (ball x r)] at hlo hup
    rw [ENNReal.div_le_iff hC0' ENNReal.coe_ne_top] at hlo
    have hνb : ν (ball x r) = μH[s] (ball x r ∩ E) := Measure.restrict_apply measurableSet_ball
    rw [hνb, hC']
    constructor
    · calc ENNReal.ofReal r ^ s ≤ C * μ (ball x r) := hμ.le_measure_ball x hx r hr hrE
        _ ≤ C * (μH[s] (ball x r ∩ E) * C) := by gcongr
        _ = 1 * C * C * μH[s] (ball x r ∩ E) := by ring
        _ ≤ 2 ^ s * C * C * μH[s] (ball x r ∩ E) := by
          gcongr; exact ENNReal.one_le_rpow one_le_two hs
    · calc μH[s] (ball x r ∩ E) ≤ 2 ^ s * C * μ (ball x r) := hup
        _ ≤ 2 ^ s * C * (C * ENNReal.ofReal r ^ s) := by
          gcongr; exact hμ.measure_ball_le x hx r hr hrE
        _ = 2 ^ s * C * C * ENNReal.ofReal r ^ s := by ring
  have hsupp : ν.support = E := by
    ext x
    constructor
    · intro hx
      by_contra hxE
      refine ((Measure.mem_support_iff_forall x).1 hx Eᶜ
        (hμ.isClosed.isOpen_compl.mem_nhds hxE)).ne' ?_
      rw [Measure.restrict_apply hμ.isClosed.isOpen_compl.measurableSet, compl_inter_self,
        measure_empty]
    · intro hx
      rw [Measure.mem_support_iff_forall]
      intro U hU
      obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hU
      obtain ⟨r, hr, hrδ⟩ := (hsmall.and (nhdsWithin_le_nhds (eventually_lt_nhds hδ))).exists
      have hne := hne_zero _ _ r hr.1 (hball x hx r hr.1 hr.2).1
      exact (pos_iff_ne_zero.2 hne).trans_le
        (measure_mono ((ball_subset_ball hrδ.le).trans hδU))
  refine ⟨C',
    { isClosed := hμ.isClosed
      nontrivial := hμ.nontrivial
      pos := hs
      regular := regular_restrict_of_isCompact hE hHtop.ne
      support_eq := hsupp
      one_le := one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (NNReal.one_le_rpow one_le_two hs.le) hμ.one_le)
        hμ.one_le
      le_measure_ball := fun x hx r hr hrE => (hball x hx r hr hrE).1
      measure_ball_le := fun x hx r hr hrE => (hball x hx r hr hrE).2 }⟩

end GeometricMeasureTheory
