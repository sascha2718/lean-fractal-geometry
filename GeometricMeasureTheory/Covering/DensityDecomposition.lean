/-
# Section 3.5: The density decomposition

Measurability of the densities, the density inheritance argument, and the decomposition of an
`s`-set into its regular and irregular points. The notes state the decomposition for `1`-sets; the
argument works for every exponent `s > 0`.

| Notes | Lean declaration | Location |
|---|---|---|
| The density level sets are Borel | `measurable_upperDensity`, `measurable_lowerDensity` | here |
| Density inheritance (proof of Theorem 3.20) | `density_inheritance` | here |
| Theorem 3.20 (density decomposition) | `density_decomposition` | here |
-/
import GeometricMeasureTheory.Covering.Densities

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-! ## Semicontinuity of ball masses and countable formulas for the densities -/

omit [BorelSpace X] in
/-- The mass of `E ∩ B(x, r)` is approximated from below by the masses of `E` in smaller
concentric balls. -/
theorem exists_lt_measure_inter_ball_of_lt (μ : Measure X) (E : Set X) {x : X} {r : ℝ}
    {t : ℝ≥0∞} (ht : t < μ (E ∩ ball x r)) : ∃ ρ < r, t < μ (E ∩ ball x ρ) := by
  have hmono : Monotone fun n : ℕ => E ∩ ball x (r - 1 / (n + 1)) := by
    intro m n hmn
    refine inter_subset_inter_right _ (ball_subset_ball ?_)
    gcongr
  have hU : (⋃ n : ℕ, E ∩ ball x (r - 1 / (n + 1))) = E ∩ ball x r := by
    rw [← inter_iUnion]
    congr 1
    ext y
    simp only [mem_iUnion, mem_ball]
    constructor
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / (n + 1) := by positivity
      linarith
    · intro hy
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hy)
      exact ⟨n, by linarith⟩
  rw [← hU, hmono.measure_iUnion] at ht
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 ht
  exact ⟨r - 1 / (n + 1), sub_lt_self r (by positivity), hn⟩

omit [BorelSpace X] in
/-- For every measure `μ`, set `E` and radius `r`, the mass `x ↦ μ (E ∩ B(x, r))` is lower
semicontinuous. -/
theorem lowerSemicontinuous_measure_inter_ball (μ : Measure X) (E : Set X) (r : ℝ) :
    LowerSemicontinuous fun x => μ (E ∩ ball x r) := by
  intro x t ht
  obtain ⟨ρ, hρr, hρ⟩ := exists_lt_measure_inter_ball_of_lt μ E ht
  filter_upwards [ball_mem_nhds x (sub_pos.2 hρr)] with y hy
  refine hρ.trans_le (measure_mono (inter_subset_inter_right _ fun z hz => ?_))
  rw [mem_ball] at hy hz ⊢
  calc dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
    _ < ρ + (r - ρ) := by rw [dist_comm x y]; exact add_lt_add hz hy
    _ = r := by ring

omit [BorelSpace X] in
/-- For `r > 0`, the density ratio `x ↦ μ (E ∩ B(x, r)) / (2r)^s` is lower semicontinuous. -/
theorem lowerSemicontinuous_measure_inter_ball_div (μ : Measure X) (s : ℝ) (E : Set X) {r : ℝ}
    (hr : 0 < r) :
    LowerSemicontinuous fun x => μ (E ∩ ball x r) / ENNReal.ofReal (2 * r) ^ s := by
  have hc : ENNReal.ofReal (2 * r) ^ s ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 (by positivity)) ENNReal.ofReal_ne_top).ne'
  exact (ENNReal.continuous_div_const _ hc).comp_lowerSemicontinuous
    (lowerSemicontinuous_measure_inter_ball μ E r) fun a b hab => ENNReal.div_le_div_right hab _

/-- The intervals `(0, 1/(n+1))` form a countable basis of `𝓝[>] 0`. -/
theorem hasBasis_nhdsGT_zero_one_div :
    (𝓝[>] (0 : ℝ)).HasBasis (fun _ : ℕ => True) fun n => Ioo 0 (1 / (n + 1)) :=
  (nhdsGT_basis 0).to_hasBasis
    (fun _ hε => (exists_nat_one_div_lt hε).imp fun _ hn => ⟨trivial, Ioo_subset_Ioo_right hn.le⟩)
    fun n _ => ⟨1 / (n + 1), by positivity, subset_rfl⟩

/-- The upper density as a countable infimum of suprema of the density ratio over radii in
`(0, 1/(n+1))`. -/
theorem upperDensity_eq_iInf_iSup (s : ℝ) (E : Set X) (x : X) :
    upperDensity s E x = ⨅ n : ℕ, ⨆ r ∈ Ioo (0 : ℝ) (1 / (n + 1)),
      μH[s] (E ∩ ball x r) / ENNReal.ofReal (2 * r) ^ s := by
  rw [upperDensity, hasBasis_nhdsGT_zero_one_div.limsup_eq_iInf_iSup]
  simp only [iInf_true]

omit [BorelSpace X] in
/-- The infimum of the density ratio over radii in `(0, ε)` equals its infimum over rational radii
in `(0, ε)`. -/
theorem iInf_measure_inter_ball_div_eq_rat (μ : Measure X) (s : ℝ) (E : Set X) (x : X) (ε : ℝ) :
    ⨅ r ∈ Ioo (0 : ℝ) ε, μ (E ∩ ball x r) / ENNReal.ofReal (2 * r) ^ s =
      ⨅ q ∈ {q : ℚ | (q : ℝ) ∈ Ioo 0 ε}, μ (E ∩ ball x q) / ENNReal.ofReal (2 * q) ^ s := by
  refine le_antisymm (le_iInf₂ fun q hq => iInf₂_le (q : ℝ) hq) (le_iInf₂ fun r hr => ?_)
  set I := ⨅ q ∈ {q : ℚ | (q : ℝ) ∈ Ioo 0 ε}, μ (E ∩ ball x q) / ENNReal.ofReal (2 * q) ^ s
  have hc : ENNReal.ofReal (2 * r) ^ s ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_pos.2 (by linarith [hr.1])).ne'
      ENNReal.ofReal_ne_top
  have hlim : Tendsto (fun t : ℝ => μ (E ∩ ball x r) / ENNReal.ofReal (2 * t) ^ s) (𝓝[<] r)
      (𝓝 (μ (E ∩ ball x r) / ENNReal.ofReal (2 * r) ^ s)) := by
    refine ENNReal.Tendsto.const_div ?_ (Or.inl hc)
    have hcont : Continuous fun t : ℝ => ENNReal.ofReal (2 * t) ^ s :=
      ENNReal.continuous_rpow_const.comp
        (ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id))
    exact (hcont.tendsto r).mono_left nhdsWithin_le_nhds
  refine isClosed_Ici.mem_of_frequently_of_tendsto (frequently_iff.2 fun hU => ?_) hlim
  obtain ⟨l, hl, hlU⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hU
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (max_lt hl hr.1)
  refine ⟨q, hlU ⟨(le_max_left _ _).trans_lt hq₁, hq₂⟩, ?_⟩
  show I ≤ μ (E ∩ ball x r) / ENNReal.ofReal (2 * q) ^ s
  calc I ≤ μ (E ∩ ball x q) / ENNReal.ofReal (2 * q) ^ s :=
        iInf₂_le q ⟨(le_max_right _ _).trans_lt hq₁, hq₂.trans hr.2⟩
    _ ≤ μ (E ∩ ball x r) / ENNReal.ofReal (2 * q) ^ s :=
        ENNReal.div_le_div_right (measure_mono (inter_subset_inter_right _
          (ball_subset_ball hq₂.le))) _

/-- The lower density as a countable supremum of countable infima of the density ratio over
rational radii in `(0, 1/(n+1))`. -/
theorem lowerDensity_eq_iSup_iInf_rat (s : ℝ) (E : Set X) (x : X) :
    lowerDensity s E x = ⨆ n : ℕ, ⨅ q ∈ {q : ℚ | (q : ℝ) ∈ Ioo (0 : ℝ) (1 / (n + 1))},
      μH[s] (E ∩ ball x q) / ENNReal.ofReal (2 * q) ^ s := by
  rw [lowerDensity, hasBasis_nhdsGT_zero_one_div.liminf_eq_iSup_iInf]
  simp only [iSup_true, iInf_measure_inter_ball_div_eq_rat]

/-! ## Measurability of the densities -/

/-- The upper density is a Borel function of the point. -/
theorem measurable_upperDensity (s : ℝ) (E : Set X) : Measurable (upperDensity s E) := by
  rw [show upperDensity s E = _ from funext (upperDensity_eq_iInf_iSup s E)]
  refine Measurable.iInf fun n => LowerSemicontinuous.measurable ?_
  exact lowerSemicontinuous_biSup fun r hr =>
    lowerSemicontinuous_measure_inter_ball_div μH[s] s E hr.1

/-- The lower density is a Borel function of the point. -/
theorem measurable_lowerDensity (s : ℝ) (E : Set X) : Measurable (lowerDensity s E) := by
  rw [show lowerDensity s E = _ from funext (lowerDensity_eq_iSup_iInf_rat s E)]
  refine Measurable.iSup fun n => Measurable.biInf _ (to_countable _) fun q hq => ?_
  exact (lowerSemicontinuous_measure_inter_ball_div μH[s] s E (r := q) hq.1).measurable

/-! ## Density inheritance and the density decomposition -/

/-- Density inheritance, from the proof of Theorem 3.20: for Borel sets `F ⊆ E` with
`𝓗^s(E) < ∞`, the densities of `F` and `E` agree at `𝓗^s`-almost every point of `F`. -/
theorem density_inheritance {s : ℝ} (hs : 0 < s) {E F : Set X} (hE : MeasurableSet E)
    (hfin : μH[s] E ≠ ∞) (hF : MeasurableSet F) (hFE : F ⊆ E) :
    ∀ᵐ x ∂μH[s], x ∈ F →
      lowerDensity s F x = lowerDensity s E x ∧ upperDensity s F x = upperDensity s E x := by
  have hG : MeasurableSet (E \ F) := hE.diff hF
  have hGfin : μH[s] (E \ F) ≠ ∞ := ne_top_of_le_ne_top hfin (measure_mono sdiff_subset)
  filter_upwards [(density_bounds hs hG hGfin).1] with x hx hxF
  obtain ⟨-, hup⟩ := hx fun h => h.2 hxF
  have htend : Tendsto (fun r : ℝ => μH[s] ((E \ F) ∩ ball x r) / ENNReal.ofReal (2 * r) ^ s)
      (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_le_liminf_of_limsup_le zero_le hup.le
  have hsplit : (fun r : ℝ => μH[s] (E ∩ ball x r) / ENNReal.ofReal (2 * r) ^ s) =
      (fun r : ℝ => μH[s] (F ∩ ball x r) / ENNReal.ofReal (2 * r) ^ s) +
        fun r : ℝ => μH[s] ((E \ F) ∩ ball x r) / ENNReal.ofReal (2 * r) ^ s := by
    ext r
    rw [Pi.add_apply, ← ENNReal.add_div, ← measure_inter_add_sdiff (E ∩ ball x r) hF]
    congr 3
    · ext y
      simp only [mem_inter_iff]
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hFE h.1, h.2⟩, h.1⟩⟩
    · ext y
      simp only [mem_inter_iff, Set.mem_sdiff]
      tauto
  refine ⟨?_, ?_⟩
  · rw [lowerDensity, lowerDensity, hsplit, ENNReal.liminf_add_of_right_tendsto_zero htend]
  · rw [upperDensity, upperDensity, hsplit, ENNReal.limsup_add_of_right_tendsto_zero htend]

/-- Theorem 3.20 (density decomposition, `thm:density-decomposition`): the regular points `R` of an
`s`-set `E` and the irregular points `E \ R` are Borel sets; `R` is a regular `s`-set if it has
positive measure, and `E \ R` is an irregular `s`-set if it has positive measure. -/
theorem density_decomposition {s : ℝ} (hs : 0 < s) {E : Set X} (hE : IsSSet s E) :
    MeasurableSet {x ∈ E | IsRegularPoint s E x} ∧
      MeasurableSet {x ∈ E | ¬IsRegularPoint s E x} ∧
      (0 < μH[s] {x ∈ E | IsRegularPoint s E x} →
        IsRegularSSet s {x ∈ E | IsRegularPoint s E x}) ∧
      (0 < μH[s] {x ∈ E | ¬IsRegularPoint s E x} →
        IsIrregularSSet s {x ∈ E | ¬IsRegularPoint s E x}) := by
  obtain ⟨hEm, -, hEfin⟩ := hE
  have hreg : MeasurableSet {x | IsRegularPoint s E x} :=
    (measurable_lowerDensity s E (measurableSet_singleton 1)).inter
      (measurable_upperDensity s E (measurableSet_singleton 1))
  have hR : MeasurableSet {x ∈ E | IsRegularPoint s E x} := hEm.inter hreg
  have hP : MeasurableSet {x ∈ E | ¬IsRegularPoint s E x} := hEm.inter hreg.compl
  have hsub : ∀ {F : Set X}, MeasurableSet F → F ⊆ E → 0 < μH[s] F → IsSSet s F :=
    fun hF hFE hpos => ⟨hF, hpos, (measure_mono hFE).trans_lt hEfin⟩
  refine ⟨hR, hP, fun hpos => ⟨hsub hR (sep_subset _ _) hpos, ?_⟩,
    fun hpos => ⟨hsub hP (sep_subset _ _) hpos, ?_⟩⟩
  · filter_upwards [density_inheritance hs hEm hEfin.ne hR (sep_subset _ _)] with x hx hxR
    obtain ⟨h₁, h₂⟩ := hx hxR
    exact ⟨h₁.trans hxR.2.1, h₂.trans hxR.2.2⟩
  · filter_upwards [density_inheritance hs hEm hEfin.ne hP (sep_subset _ _)] with x hx hxP
    obtain ⟨h₁, h₂⟩ := hx hxP
    exact fun hreg' => hxP.2 ⟨h₁.symm.trans hreg'.1, h₂.symm.trans hreg'.2⟩

end GeometricMeasureTheory
