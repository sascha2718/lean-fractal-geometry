/-
# Section 3.2: A Vitali covering theorem for Radon measures

The Vitali covering theorem for Radon measures on `ℝ^d` is Mathlib's Besicovitch covering theorem,
which holds for every s-finite measure on a finite-dimensional real normed space. The comparison of
two Radon measures through their density ratio follows from Mathlib's differentiation theory for
Vitali families.

| Notes | Lean declaration | Location |
|---|---|---|
| Theorem 3.7 (Vitali for Radon measures) | `Besicovitch.exists_disjoint_closedBall_covering_ae` | `Mathlib/MeasureTheory/Covering/Besicovitch.lean` |
| Proposition 3.8 (relative density comparison) | `relative_density_comparison`; the covering argument is `VitaliFamily.measure_le_of_frequently_le` for the Vitali family `Besicovitch.vitaliFamily` of closed balls, with `Besicovitch.tendsto_filterAt` | here; `Mathlib/MeasureTheory/Covering/Differentiation.lean`, `Mathlib/MeasureTheory/Covering/Besicovitch.lean` |
-/
import GeometricMeasureTheory.Covering.DensityComparison

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## Theorem 3.7 (`thm:radon-vitali`)

This is `Besicovitch.exists_disjoint_closedBall_covering_ae`. -/

example (μ : Measure E) [IsLocallyFiniteMeasure μ] (A : Set E) (V : Set (Set E))
    (hV : ∀ x ∈ A, ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ r < δ ∧ closedBall x r ∈ V) :
    ∃ V' ⊆ V, V'.Countable ∧ V'.PairwiseDisjoint id ∧ μ (A \ ⋃₀ V') = 0 := by
  obtain ⟨t, r, ht, -, hr, hnull, hdisj⟩ := Besicovitch.exists_disjoint_closedBall_covering_ae μ
    (fun x => {r | closedBall x r ∈ V}) A
    (fun x hx δ hδ => by
      obtain ⟨r, hr0, hrδ, hrV⟩ := hV x hx δ hδ
      exact ⟨r, hrV, hr0, hrδ⟩)
    (fun _ => 1) fun _ _ => one_pos
  refine ⟨(fun x => closedBall x (r x)) '' t, ?_, ht.image _, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (hr x hx).1
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    exact hdisj hx hy fun h => hxy (by rw [h])
  · rwa [sUnion_image]

/-! ## Proposition 3.8 (`thm:relative-density-comparison`) -/

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- A value below the measure of an open ball is below the measure of a concentric closed ball of
smaller positive radius. -/
private theorem exists_lt_measure_closedBall {m : Measure E} {x : E} {r : ℝ} (hr : 0 < r)
    {a : ℝ≥0∞} (ha : a < m (ball x r)) : ∃ ρ ∈ Ioo 0 r, a < m (closedBall x ρ) := by
  let ρ : ℕ → ℝ := fun n => max (r / 2) (r - 1 / ((n : ℝ) + 1))
  have hρ : ∀ n, ρ n ∈ Ioo 0 r := fun n =>
    ⟨lt_max_of_lt_left (half_pos hr),
      max_lt (half_lt_self hr) (sub_lt_self _ (by positivity))⟩
  have hmono : Monotone fun n => closedBall x (ρ n) := by
    intro n k hnk
    refine closedBall_subset_closedBall (max_le_max le_rfl ?_)
    gcongr
  have hU : ⋃ n, closedBall x (ρ n) = ball x r := by
    refine Subset.antisymm (iUnion_subset fun n => closedBall_subset_ball (hρ n).2) ?_
    intro y hy
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (mem_ball.1 hy))
    exact mem_iUnion.2 ⟨n, mem_closedBall.2 (le_max_of_le_right (by linarith))⟩
  rw [← hU, hmono.measure_iUnion] at ha
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 ha
  exact ⟨ρ n, hρ n, hn⟩

/-- If `a ≤ c' * b` for every `c' > c`, then `a ≤ c * b`. -/
private theorem le_nnreal_mul_of_forall_gt {a b : ℝ≥0∞} {c : ℝ≥0} (hc : c ≠ 0)
    (h : ∀ c' : ℝ≥0, c < c' → a ≤ c' * b) : a ≤ c * b := by
  refine ENNReal.le_mul_of_forall_lt (Or.inl (ENNReal.coe_ne_zero.2 hc))
    (Or.inl ENNReal.coe_ne_top) fun a' ha' b' hb' => ?_
  rcases eq_or_ne a' ⊤ with rfl | ha'top
  · rw [ENNReal.top_mul (zero_le.trans_lt hb').ne']
    exact le_top
  · lift a' to ℝ≥0 using ha'top
    exact (h a' (ENNReal.coe_lt_coe.1 ha')).trans (by gcongr)

/-- If `c' * b ≤ a` for every `0 < c' < c`, then `c * b ≤ a`. -/
private theorem nnreal_mul_le_of_forall_lt {a b : ℝ≥0∞} {c : ℝ≥0}
    (h : ∀ c' : ℝ≥0, 0 < c' → c' < c → (c' : ℝ≥0∞) * b ≤ a) : c * b ≤ a := by
  refine ENNReal.mul_le_of_forall_lt fun a' ha' b' hb' => ?_
  lift a' to ℝ≥0 using ne_top_of_lt ha'
  rcases eq_or_ne a' 0 with rfl | ha'0
  · simp
  · exact (by gcongr : (a' : ℝ≥0∞) * b' ≤ a' * b).trans
      (h a' (pos_iff_ne_zero.2 ha'0) (ENNReal.coe_lt_coe.1 ha'))

/-- Proposition 3.8 (`thm:relative-density-comparison`): for locally finite Borel measures `μ` and
`ν` and `A` contained in the support of `ν`, (1) `liminf μ(B(x, r)) / ν(B(x, r)) ≤ c` on `A` gives
`μ(A) ≤ c ν(A)`, and (2) `limsup μ(B(x, r)) / ν(B(x, r)) ≥ c` on `A` gives `μ(A) ≥ c ν(A)`. -/
theorem relative_density_comparison (μ ν : Measure E) [IsLocallyFiniteMeasure μ]
    [IsLocallyFiniteMeasure ν] {c : ℝ≥0} (hc : c ≠ 0) {A : Set E} (hA : A ⊆ ν.support) :
    ((∀ x ∈ A, liminf (fun r : ℝ => μ (ball x r) / ν (ball x r)) (𝓝[>] 0) ≤ c) →
        μ A ≤ c * ν A) ∧
      ((∀ x ∈ A, (c : ℝ≥0∞) ≤ limsup (fun r : ℝ => μ (ball x r) / ν (ball x r)) (𝓝[>] 0)) →
        c * ν A ≤ μ A) := by
  have hpos : ∀ x ∈ A, ∀ r : ℝ, 0 < r → ν (ball x r) ≠ 0 := fun x hx r hr =>
    ((Measure.mem_support_iff_forall x).1 (hA hx) _ (ball_mem_nhds x hr)).ne'
  have hfin : ∀ (x : E) (r : ℝ), ν (ball x r) ≠ ⊤ := fun _ _ => measure_ball_lt_top.ne
  have htrans : ∀ (x : E) (P : ℝ → Prop) (Q : Set E → Prop), (∃ᶠ r in 𝓝[>] 0, P r) →
      (∀ r, 0 < r → P r → ∃ ρ ∈ Ioo 0 r, Q (closedBall x ρ)) →
      ∃ᶠ a in (Besicovitch.vitaliFamily (μ + ν)).filterAt x, Q a := by
    intro x P Q hP hPQ
    refine (Besicovitch.tendsto_filterAt (μ + ν) x).frequently (frequently_iff.2 fun hU => ?_)
    obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hU
    obtain ⟨r, hPr, hr⟩ := (hP.and_eventually (Ioo_mem_nhdsGT hε)).exists
    obtain ⟨ρ, hρ, hQ⟩ := hPQ r hr.1 hPr
    exact ⟨ρ, hsub ⟨hρ.1, hρ.2.trans hr.2⟩, hQ⟩
  constructor
  · intro h
    refine le_nnreal_mul_of_forall_gt hc fun c' hcc' => ?_
    have key : ∀ x ∈ A, ∃ᶠ a in (Besicovitch.vitaliFamily (μ + ν)).filterAt x,
        μ a ≤ (c' • ν) a := by
      intro x hx
      refine htrans x _ _ (frequently_lt_of_liminf_lt
        (h := (h x hx).trans_lt (ENNReal.coe_lt_coe.2 hcc'))) fun r hr hlt => ?_
      have h1 : μ (ball x r) < (c' • ν) (ball x r) := by
        rw [Measure.coe_nnreal_smul_apply]
        exact (ENNReal.div_lt_iff (Or.inl (hpos x hx r hr)) (Or.inl (hfin x r))).1 hlt
      obtain ⟨ρ, hρ, hlt'⟩ := exists_lt_measure_closedBall hr h1
      exact ⟨ρ, hρ, (measure_mono (closedBall_subset_ball hρ.2)).trans hlt'.le⟩
    have := (Besicovitch.vitaliFamily (μ + ν)).measure_le_of_frequently_le (c' • ν)
      (Measure.AbsolutelyContinuous.rfl.add_right ν) A key
    rwa [Measure.coe_nnreal_smul_apply] at this
  · intro h
    refine nnreal_mul_le_of_forall_lt fun c' hc'0 hc'c => ?_
    have key : ∀ x ∈ A, ∃ᶠ a in (Besicovitch.vitaliFamily (μ + ν)).filterAt x,
        (c' • ν) a ≤ μ a := by
      intro x hx
      refine htrans x _ _ (frequently_lt_of_lt_limsup
        (h := (ENNReal.coe_lt_coe.2 hc'c).trans_le (h x hx))) fun r hr hlt => ?_
      have h1 : (c' • ν) (ball x r) < μ (ball x r) := by
        rw [Measure.coe_nnreal_smul_apply]
        exact (ENNReal.lt_div_iff_mul_lt (Or.inl (hpos x hx r hr)) (Or.inl (hfin x r))).1 hlt
      obtain ⟨ρ, hρ, hlt'⟩ := exists_lt_measure_closedBall hr h1
      exact ⟨ρ, hρ, (measure_mono (closedBall_subset_ball hρ.2)).trans hlt'.le⟩
    have hac : c' • ν ≪ μ + ν := fun U hU => by
      rw [Measure.add_apply, add_eq_zero] at hU
      rw [Measure.coe_nnreal_smul_apply, hU.2, mul_zero]
    have := (Besicovitch.vitaliFamily (μ + ν)).measure_le_of_frequently_le μ hac A key
    rwa [Measure.coe_nnreal_smul_apply] at this

end GeometricMeasureTheory
