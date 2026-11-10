module

/-
The last two steps of the proof of `thm:eq_state_is_sum` (Fraser–Jordan–Jurga, J. Fractal
Geom. 7 (2020), Lemma 1.3 and Corollaries 1.5 and 1.6). No literature premise is used.

Uniqueness: an invariant probability measure `μ` on `Σ` with the Gibbs bounds of
`thm:irred_eq_state` satisfies `μ([w]) ≤ K L ν([w])` for every ergodic `ν` with the same bounds,
hence `μ ≪ ν` and `μ = ν`. The decompositions: for a measure `μ_1` carried by `Σ_Z` and
`μ_2 = flip_*μ_1`, the cover `Σ_Z = τ(Σ) ∪ ω(Σ)` by disjoint sets (`eq:tau_omega_partition`)
gives `q_*μ_1 = \overline{τ}_*μ_1 + \overline{ω}_*μ_1`, and the exchange of the axes maps `ω(Σ)`
onto `τ(Σ)` and commutes with `q`, so `\overline{τ}_*μ_2 = \overline{ω}_*μ_1` and
`\overline{ω}_*μ_2 = \overline{τ}_*μ_1`. The four decompositions of `thm:eq_state_is_sum` of
`q_*μ_1` follow.

* `System.measureReal_cylinder_le_of_hasGibbsBounds`, `System.eq_of_hasGibbsBounds`: two
  measures with the Gibbs bounds have comparable cylinder values, and an invariant probability
  measure with the Gibbs bounds equals every ergodic one.
* `flipAxis_flipAxis`, `preimage_flipAxis_range_tau`, `preimage_flipAxis_range_omega`: the
  exchange of the axes is an involution and exchanges `τ(Σ)` and `ω(Σ)`.
* `restrict_range_tau_add_restrict_range_omega`: `ν = ν|_{τ(Σ)} + ν|_{ω(Σ)}` for `ν` carried by
  `Σ_Z`.
* `map_unCode_restrict_map_flipAxis`, `map_unCode_restrict_range_tau_map_flipAxis`,
  `map_unCode_restrict_range_omega_map_flipAxis`: `\overline{τ}_*(flip_*ν) = \overline{ω}_*ν` and
  `\overline{ω}_*(flip_*ν) = \overline{τ}_*ν`.
* `map_unCode_eq_tau`, `map_unCode_eq_omega`, `map_unCode_eq₁`, `map_unCode_eq₂`: the four
  decompositions of `q_*ν` with `μ_1 = ν` and `μ_2 = flip_*ν`.
-/
public import BoxLike.Support.GibbsUniqueness

@[expose] public section

namespace BoxLike

open MeasureTheory Set

/-! ### Uniqueness of the measure with the Gibbs bounds -/

section Uniqueness

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {s : ℝ} {μ ν : Measure (ℤ → ι)}

omit [MeasurableSingletonClass ι] in
/-- Two probability measures with the Gibbs bounds of `thm:irred_eq_state`, with constants `K` and
`L`, have comparable cylinder values: `μ([w]) ≤ K L ν([w])` for every word `w`, the empty word
included. -/
theorem System.measureReal_cylinder_le_of_hasGibbsBounds [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {K L : ℝ} (hK : S.HasGibbsBoundsWith K s μ)
    (hL : S.HasGibbsBoundsWith L s ν) (n : ℕ) (w : Fin n → ι) :
    μ.real (cylinder w) ≤ K * L * ν.real (cylinder w) := by
  obtain ⟨hK1, hKb⟩ := hK
  obtain ⟨hL1, hLb⟩ := hL
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have huniv : cylinder w = univ := eq_univ_of_forall fun _ k => k.elim0
    rw [huniv, probReal_univ, probReal_univ, mul_one]
    nlinarith
  · have h1 := (hKb n hn w).2
    have h2 := (hLb n hn w).1
    rw [inv_mul_le_iff₀ (by linarith)] at h2
    calc μ.real (cylinder w)
        ≤ K * (Real.exp (-(n * S.pressure s)) * svf s (S.matWord (List.ofFn w))) := h1
      _ ≤ K * (L * ν.real (cylinder w)) := mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = K * L * ν.real (cylinder w) := by ring

/-- `thm:eq_state_is_sum`, uniqueness: an invariant probability measure `μ` on `Σ` with the Gibbs
bounds of `thm:irred_eq_state` equals every ergodic probability measure `ν` with these bounds. By
`System.measureReal_cylinder_le_of_hasGibbsBounds` and invariance, `μ(A) ≤ K L ν(A)` for every
Borel set `A` (`le_of_cylinder_le`), so `μ ≪ ν`, and an invariant probability measure absolutely
continuous with respect to an ergodic one equals it. -/
theorem System.eq_of_hasGibbsBounds [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MeasurePreserving (shift 1) μ μ) (hν : Ergodic (shift 1) ν)
    (hgμ : S.HasGibbsBounds s μ) (hgν : S.HasGibbsBounds s ν) : μ = ν := by
  obtain ⟨K, hK⟩ := (S.hasGibbsBounds_iff).1 hgμ
  obtain ⟨L, hL⟩ := (S.hasGibbsBounds_iff).1 hgν
  have hK1 := hK.1
  have hL1 := hL.1
  have hcyl : ∀ (n : ℕ) (w : Fin n → ι),
      μ (cylinder w) ≤ ENNReal.ofReal (K * L) * ν (cylinder w) := by
    intro n w
    rw [← ofReal_measureReal, ← ofReal_measureReal, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (S.measureReal_cylinder_le_of_hasGibbsBounds hK hL n w)
  refine hν.eq_of_absolutelyContinuous hμ fun A hA0 => ?_
  obtain ⟨A', hAA', hA'm, hA'0⟩ := exists_measurable_superset_of_null hA0
  have hle := le_of_cylinder_le hν.toMeasurePreserving hμ ENNReal.ofReal_ne_top hcyl hA'm
  exact measure_mono_null hAA' (le_antisymm (hle.trans (by rw [hA'0, mul_zero])) zero_le)

end Uniqueness

/-! ### The exchange of the axes and the two codings -/

section Flip

variable {ι : Type*}

/-- The exchange of the axes is an involution. -/
@[simp] theorem flipAxis_flipAxis (y : ℤ → ι × ZMod 2) : flipAxis (flipAxis y) = y :=
  funext fun n => flipSymbol_flipSymbol (y n)

/-- The exchange of the axes maps `ω(Σ)` onto `τ(Σ)`: `flip⁻¹(τ(Σ)) = ω(Σ)`. -/
theorem preimage_flipAxis_range_tau (o : ι → ZMod 2) :
    flipAxis ⁻¹' range (tau o) = range (omega o) := by
  ext y
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [← flipAxis_tau, hx, flipAxis_flipAxis]
  · rintro ⟨x, rfl⟩
    exact ⟨x, (flipAxis_omega o x).symm⟩

/-- The exchange of the axes maps `τ(Σ)` onto `ω(Σ)`: `flip⁻¹(ω(Σ)) = τ(Σ)`. -/
theorem preimage_flipAxis_range_omega (o : ι → ZMod 2) :
    flipAxis ⁻¹' range (omega o) = range (tau o) := by
  ext y
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [← flipAxis_omega, hx, flipAxis_flipAxis]
  · rintro ⟨x, rfl⟩
    exact ⟨x, (flipAxis_tau o x).symm⟩

variable [MeasurableSpace ι] {o : ι → ZMod 2} {ν : Measure (ℤ → ι × ZMod 2)}

/-- The factor map `q = unCode` forgets the axis, so `q_*((flip_*ν)|_R) = q_*(ν|_{flip⁻¹(R)})`
for every Borel set `R`. -/
theorem map_unCode_restrict_map_flipAxis {R : Set (ℤ → ι × ZMod 2)} (hR : MeasurableSet R) :
    ((ν.map flipAxis).restrict R).map unCode = (ν.restrict (flipAxis ⁻¹' R)).map unCode := by
  rw [Measure.restrict_map measurable_flipAxis hR,
    Measure.map_map measurable_unCode measurable_flipAxis]
  rfl

variable [Fintype ι] [MeasurableSingletonClass ι]

/-- `\overline{τ}_*(flip_*ν) = \overline{ω}_*ν`, as noted in `sec:gibbs_measures` (tex lines 2487
to 2607) for `ν = μ_1`, `flip_*ν = μ_2`. -/
theorem map_unCode_restrict_range_tau_map_flipAxis :
    ((ν.map flipAxis).restrict (range (tau o))).map unCode =
      (ν.restrict (range (omega o))).map unCode := by
  rw [map_unCode_restrict_map_flipAxis (measurableSet_range_tau o), preimage_flipAxis_range_tau]

/-- `\overline{ω}_*(flip_*ν) = \overline{τ}_*ν`, as noted in `sec:gibbs_measures` (tex lines 2487
to 2607) for `ν = μ_1`, `flip_*ν = μ_2`. -/
theorem map_unCode_restrict_range_omega_map_flipAxis :
    ((ν.map flipAxis).restrict (range (omega o))).map unCode =
      (ν.restrict (range (tau o))).map unCode := by
  rw [map_unCode_restrict_map_flipAxis (measurableSet_range_omega o),
    preimage_flipAxis_range_omega]

end Flip

/-! ### The four decompositions -/

section Decompositions

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {o : ι → ZMod 2} {ν : Measure (ℤ → ι × ZMod 2)}

/-- `eq:tau_omega_partition` for measures: a measure carried by `Σ_Z` is the sum of its
restrictions to the disjoint Borel sets `τ(Σ)` and `ω(Σ)` that cover `Σ_Z`. -/
theorem restrict_range_tau_add_restrict_range_omega (hν : ν (subshift o)ᶜ = 0) :
    ν.restrict (range (tau o)) + ν.restrict (range (omega o)) = ν := by
  rw [← Measure.restrict_union disjoint_range_tau_range_omega (measurableSet_range_omega o),
    range_tau_union_range_omega]
  exact Measure.restrict_eq_self_of_ae_mem hν

/-- `thm:eq_state_is_sum`, third decomposition `μ = \overline{τ}_*μ_1 + \overline{ω}_*μ_1`, for
`μ = q_*μ_1` and a measure `μ_1 = ν` carried by `Σ_Z`. -/
theorem map_unCode_eq₁ (hν : ν (subshift o)ᶜ = 0) :
    ν.map unCode = (ν.restrict (range (tau o))).map unCode +
      (ν.restrict (range (omega o))).map unCode := by
  rw [← Measure.map_add _ _ measurable_unCode, restrict_range_tau_add_restrict_range_omega hν]

/-- `thm:eq_state_is_sum`, first decomposition `μ = \overline{τ}_*μ_1 + \overline{τ}_*μ_2`, for
`μ = q_*μ_1`, a measure `μ_1 = ν` carried by `Σ_Z` and `μ_2 = flip_*μ_1`. -/
theorem map_unCode_eq_tau (hν : ν (subshift o)ᶜ = 0) :
    ν.map unCode = (ν.restrict (range (tau o))).map unCode +
      ((ν.map flipAxis).restrict (range (tau o))).map unCode := by
  rw [map_unCode_restrict_range_tau_map_flipAxis]
  exact map_unCode_eq₁ hν

/-- `thm:eq_state_is_sum`, second decomposition `μ = \overline{ω}_*μ_1 + \overline{ω}_*μ_2`, for
`μ = q_*μ_1`, a measure `μ_1 = ν` carried by `Σ_Z` and `μ_2 = flip_*μ_1`. -/
theorem map_unCode_eq_omega (hν : ν (subshift o)ᶜ = 0) :
    ν.map unCode = (ν.restrict (range (omega o))).map unCode +
      ((ν.map flipAxis).restrict (range (omega o))).map unCode := by
  rw [map_unCode_restrict_range_omega_map_flipAxis, add_comm]
  exact map_unCode_eq₁ hν

/-- `thm:eq_state_is_sum`, fourth decomposition `μ = \overline{τ}_*μ_2 + \overline{ω}_*μ_2`, for
`μ = q_*μ_1`, a measure `μ_1 = ν` carried by `Σ_Z` and `μ_2 = flip_*μ_1`. -/
theorem map_unCode_eq₂ (hν : ν (subshift o)ᶜ = 0) :
    ν.map unCode = ((ν.map flipAxis).restrict (range (tau o))).map unCode +
      ((ν.map flipAxis).restrict (range (omega o))).map unCode := by
  rw [map_unCode_restrict_range_tau_map_flipAxis, map_unCode_restrict_range_omega_map_flipAxis,
    add_comm]
  exact map_unCode_eq₁ hν

end Decompositions

end BoxLike
