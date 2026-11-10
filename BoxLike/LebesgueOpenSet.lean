module

/-
The Lebesgue measure of the open set of the strong open set condition: the case `s ≥ 2` of
`thm:main_extended` in `sec:dimension_result_proof`, tex lines 3385 to 3409.

The plane `ℝ × ℝ` carries the sup metric, so a closed ball of radius `r` is a square of side
`2r`, and `volume` is the product of the Lebesgue measures of the two axes.

* `tendsto_log_mul_sq_div_log`, `volume_closedBall_plane`, `hasLocalDim_normalised_volume`,
  `isExactDim_normalised_volume`: normalised Lebesgue measure on an open set of positive finite
  measure has pointwise dimension two at every point of the set.
* `System.linPart`, `System.det_linPart`, `System.phi_eq_add_linPart`: `φ_i` is the linear map
  of the matrix `A_i` followed by the translation by `v_i`.
* `System.volume_image_phi`: `φ_i` scales Lebesgue measure by `|det A_i|`.
* `System.measurableEmbedding_phi`, `System.measurableSet_image_phi`: `φ_i` maps Borel sets to
  Borel sets.
* `System.volume_iUnion_image_phi`: the change of variables of tex lines 3390 to 3394 for
  pairwise disjoint images.
* `System.Bounds.image_ball_subset`, `System.StrongOpenSet.exists_isBounded`: a large open ball
  is forward invariant, and the open set of the strong open set condition may be taken bounded.
* `System.StrongOpenSet.sum_abs_det_le_one`: `∑_i |det A_i| ≤ 1` under the strong open set
  condition.
* `System.smul_map_restrict_phi`, `System.restrict_iUnion_image_phi`,
  `System.isInvariantMeasure_normalised_volume`: if `∑_i |det A_i| = 1`, then normalised
  Lebesgue measure `ν` on the open set satisfies `ν = ∑_i |det A_i| (φ_i)_*ν`.
* `System.StrongOpenSet.exists_isInvariantMeasure_isExactDim`: the invariant probability
  measure of exact dimension two.
-/
public import BoxLike.MeasureDim
public import BoxLike.SelfAffineMeasure
public import BoxLike.SeparationConditions
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal

/-! ### Normalised Lebesgue measure on an open set has dimension two -/

/-- `log(c r²) / log r → 2` as `r ↓ 0`, for every `c > 0`. This is the limit behind the last
step of the case `s ≥ 2` of `thm:main_extended`, tex lines 3407 to 3409. -/
theorem tendsto_log_mul_sq_div_log {c : ℝ} (hc : 0 < c) :
    Tendsto (fun r : ℝ => Real.log (c * r ^ 2) / Real.log r) (𝓝[>] 0) (𝓝 2) := by
  have h : Tendsto (fun r : ℝ => Real.log c / Real.log r + 2) (𝓝[>] 0) (𝓝 (0 + 2)) :=
    (tendsto_const_nhds.div_atBot Real.tendsto_log_nhdsGT_zero).add_const 2
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with r hr
  have hr0 : r ≠ 0 := hr.1.ne'
  have hlog : Real.log r ≠ 0 := (Real.log_neg hr.1 hr.2).ne
  rw [Real.log_mul hc.ne' (pow_ne_zero 2 hr0), Real.log_pow]
  push_cast
  field_simp

/-- In the sup metric of the plane a closed ball of radius `r` is a square of side `2r`, of
Lebesgue measure `4r²`. -/
theorem volume_closedBall_plane (x : ℝ × ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall x r) = ENNReal.ofReal (4 * r ^ 2) := by
  rw [← closedBall_prod_same, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_closedBall,
    Real.volume_closedBall, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- Normalised Lebesgue measure on an open set `U` of positive finite measure has pointwise
dimension two at every point of `U`, as in tex lines 3407 to 3409: a small closed ball about
the point lies in `U` and has measure `4r² / 𝓛²(U)`. -/
theorem hasLocalDim_normalised_volume {U : Set (ℝ × ℝ)} (hU : IsOpen U) (h0 : volume U ≠ 0)
    (htop : volume U ≠ ∞) {x : ℝ × ℝ} (hx : x ∈ U) :
    HasLocalDim ((volume U)⁻¹ • volume.restrict U) x 2 := by
  obtain ⟨ε, hε, hball⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
  have hV : 0 < (volume U).toReal := ENNReal.toReal_pos h0 htop
  have hc : 0 < 4 / (volume U).toReal := by positivity
  refine (tendsto_log_mul_sq_div_log hc).congr' ?_
  filter_upwards [Ioc_mem_nhdsGT hε] with r hr
  have hr0 : 0 ≤ 4 * r ^ 2 := by positivity
  have hreal : ((volume U)⁻¹ • volume.restrict U).real (closedBall x r) =
      4 / (volume U).toReal * r ^ 2 := by
    rw [Measure.real, Measure.smul_apply, Measure.restrict_apply measurableSet_closedBall,
      inter_eq_left.2 ((closedBall_subset_closedBall hr.2).trans hball),
      volume_closedBall_plane x hr.1.le, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal hr0]
    ring
  rw [hreal]

/-- Normalised Lebesgue measure on an open set of positive finite measure is exact-dimensional
of dimension two, as in tex lines 3407 to 3409. -/
theorem isExactDim_normalised_volume {U : Set (ℝ × ℝ)} (hU : IsOpen U) (h0 : volume U ≠ 0)
    (htop : volume U ≠ ∞) : IsExactDim ((volume U)⁻¹ • volume.restrict U) 2 :=
  Measure.ae_smul_measure ((ae_restrict_mem hU.measurableSet).mono fun _ hx =>
    hasLocalDim_normalised_volume hU h0 htop hx) _

namespace System

variable {ι : Type*} (S : System ι)

/-! ### The maps `φ_i` and Lebesgue measure -/

/-- The linear part `z ↦ A_i z` of `φ_i`, as a linear map of the plane. -/
noncomputable def linPart (i : ι) : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ) (S.mat i)

/-- The determinant of the linear part of `φ_i` is `det A_i`. -/
theorem det_linPart (i : ι) : LinearMap.det (S.linPart i) = (S.mat i).det :=
  LinearMap.det_toLin _ _

/-- `φ_i(z) = v_i + A_i z`, as in `sec:box_like_self_affine`. -/
theorem phi_eq_add_linPart (i : ι) (z : ℝ × ℝ) : S.phi i z = S.v i + S.linPart i z := by
  rcases zmod_two_cases (S.o i) with h | h
  · ext <;> simp [linPart, mat, h, phi, Matrix.toLin_finTwoProd_apply, add_comm]
  · ext <;> simp [linPart, mat, h, phi, Matrix.toLin_finTwoProd_apply, add_comm,
      show (1 : ZMod 2) + 1 = 0 from by decide]

/-- The affine map `φ_i` scales Lebesgue measure by `|det A_i|`. -/
theorem volume_image_phi (i : ι) (U : Set (ℝ × ℝ)) :
    volume (S.phi i '' U) = ENNReal.ofReal |(S.mat i).det| * volume U := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have h : S.phi i '' U = (fun z => S.v i + z) '' (S.linPart i '' U) := by
    rw [image_image]
    exact image_congr fun z _ => S.phi_eq_add_linPart i z
  rw [h, image_add_left, measure_preimage_add, Measure.addHaar_image_linearMap, det_linPart]

/-- `φ_i` is a measurable embedding of the plane: it is continuous and injective. -/
theorem measurableEmbedding_phi (i : ι) : MeasurableEmbedding (S.phi i) :=
  (S.continuous_phi i).measurableEmbedding (S.injective_phi i)

/-- `φ_i` maps Borel sets to Borel sets. -/
theorem measurableSet_image_phi (i : ι) {U : Set (ℝ × ℝ)} (hU : MeasurableSet U) :
    MeasurableSet (S.phi i '' U) :=
  (S.measurableEmbedding_phi i).measurableSet_image.2 hU

/-- The change of variables of tex lines 3390 to 3394: if the images `φ_i(U)` of a Borel set
`U` are pairwise disjoint, then their union has Lebesgue measure `∑_i |det A_i|` times that of
`U`. -/
theorem volume_iUnion_image_phi [Fintype ι] {U : Set (ℝ × ℝ)} (hU : MeasurableSet U)
    (hdisj : Pairwise fun i j => Disjoint (S.phi i '' U) (S.phi j '' U)) :
    volume (⋃ i, S.phi i '' U) = ENNReal.ofReal (∑ i, |(S.mat i).det|) * volume U := by
  rw [measure_iUnion hdisj fun i => S.measurableSet_image_phi i hU, tsum_fintype,
    ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => S.volume_image_phi i U

/-! ### A bounded open set and the sum of the determinants -/

variable {S} in
/-- Under uniform bounds, an open ball about the origin of radius `R` with `rR + M < R` is
mapped into itself by every `φ_i`. This is the large ball of tex lines 3385 to 3386. -/
theorem Bounds.image_ball_subset {r M : ℝ} (hS : S.Bounds r M) {R : ℝ} (hR : r * R + M < R)
    (i : ι) : S.phi i '' ball 0 R ⊆ ball 0 R := by
  rintro _ ⟨z, hz, rfl⟩
  rw [mem_ball] at hz ⊢
  have h0 : dist (S.phi i 0) 0 ≤ M := by
    have h1 := hS.abs_trans_le (i, 0)
    have h2 := hS.abs_trans_le (i, 1)
    simp only [trans, coord_zero, coord_one] at h1 h2
    rw [dist_zero_right, Prod.norm_def]
    simpa [phi, coord] using ⟨h1, h2⟩
  have h1 := hS.dist_phi_le i z 0
  have h2 := mul_le_mul_of_nonneg_left hz.le hS.r_nonneg
  have h3 := dist_triangle (S.phi i z) (S.phi i 0) 0
  linarith

/-- The open set of the strong open set condition may be taken bounded, as in tex lines 3385 to
3560: intersect it with a large forward invariant open ball that contains `X`. -/
theorem StrongOpenSet.exists_isBounded [Finite ι] (h : S.StrongOpenSet) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ Bornology.IsBounded U ∧ (U ∩ S.attractor).Nonempty ∧
      (∀ i, S.phi i '' U ⊆ U) ∧ Pairwise fun i j => Disjoint (S.phi i '' U) (S.phi j '' U) := by
  obtain ⟨U, hU, hne, hsub, hdisj⟩ := h
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  obtain ⟨R, hR, hXR⟩ := S.isCompact_attractor.isBounded.subset_ball_lt (M / (1 - r)) 0
  have hMR : r * R + M < R := by
    have := (div_lt_iff₀ (sub_pos.2 hS.r_lt_one)).1 hR
    linarith
  refine ⟨U ∩ ball 0 R, hU.inter isOpen_ball, isBounded_ball.subset inter_subset_right, ?_,
    fun i => ?_, fun i j hij => ?_⟩
  · obtain ⟨z, hzU, hzX⟩ := hne
    exact ⟨z, ⟨hzU, hXR hzX⟩, hzX⟩
  · exact (image_inter_subset _ _ _).trans
      (inter_subset_inter (hsub i) (hS.image_ball_subset hMR i))
  · exact (hdisj hij).mono (image_mono inter_subset_left) (image_mono inter_subset_left)

/-- Under the strong open set condition `∑_i |det A_i| ≤ 1`, as in tex lines 3387 to 3395: the
images `φ_i(V)` of a bounded feasible open set `V` are pairwise disjoint subsets of `V`, and
`0 < 𝓛²(V) < ∞`. -/
theorem StrongOpenSet.sum_abs_det_le_one [Fintype ι] (h : S.StrongOpenSet) :
    ∑ i, |(S.mat i).det| ≤ 1 := by
  obtain ⟨U, hU, hbdd, hne, hsub, hdisj⟩ := h.exists_isBounded
  have h0 : volume U ≠ 0 := (hU.measure_pos volume (hne.mono inter_subset_left)).ne'
  have htop : volume U ≠ ∞ := hbdd.measure_lt_top.ne
  have hle : ENNReal.ofReal (∑ i, |(S.mat i).det|) * volume U ≤ 1 * volume U := by
    rw [← S.volume_iUnion_image_phi hU.measurableSet hdisj, one_mul]
    exact measure_mono (iUnion_subset hsub)
  exact ENNReal.ofReal_le_one.1 ((ENNReal.mul_le_mul_iff_left h0 htop).1 hle)

/-! ### The invariant measure -/

/-- The push-forward of Lebesgue measure on `U` under `φ_i`, multiplied by `|det A_i|`, is
Lebesgue measure on `φ_i(U)`. This is the first equality of tex lines 3400 to 3403. -/
theorem smul_map_restrict_phi (i : ι) (U : Set (ℝ × ℝ)) :
    ENNReal.ofReal |(S.mat i).det| • (volume.restrict U).map (S.phi i) =
      volume.restrict (S.phi i '' U) := by
  ext E hE
  have hm := (S.measurableEmbedding_phi i).measurable
  rw [Measure.smul_apply, Measure.map_apply hm hE, Measure.restrict_apply (hm hE),
    Measure.restrict_apply hE, smul_eq_mul, ← volume_image_phi, image_preimage_inter]

/-- If `∑_i |det A_i| = 1`, then the pairwise disjoint sets `φ_i(U) ⊆ U` cover `U` up to a
Lebesgue-null set, as in tex lines 3396 to 3398. -/
theorem restrict_iUnion_image_phi [Fintype ι] {U : Set (ℝ × ℝ)} (hU : MeasurableSet U)
    (htop : volume U ≠ ∞) (hsub : ∀ i, S.phi i '' U ⊆ U)
    (hdisj : Pairwise fun i j => Disjoint (S.phi i '' U) (S.phi j '' U))
    (hsum : ∑ i, |(S.mat i).det| = 1) :
    volume.restrict (⋃ i, S.phi i '' U) = volume.restrict U := by
  refine Measure.restrict_congr_set (ae_eq_of_subset_of_measure_ge (iUnion_subset hsub) ?_
    (MeasurableSet.iUnion fun i => S.measurableSet_image_phi i hU).nullMeasurableSet htop)
  rw [S.volume_iUnion_image_phi hU hdisj, hsum, ENNReal.ofReal_one, one_mul]

/-- If `∑_i |det A_i| = 1` and the sets `φ_i(U)` are pairwise disjoint subsets of the Borel set
`U` of finite measure, then normalised Lebesgue measure `ν` on `U` satisfies
`ν = ∑_i |det A_i| (φ_i)_*ν`, as in tex lines 3398 to 3403. -/
theorem isInvariantMeasure_normalised_volume [Fintype ι] {U : Set (ℝ × ℝ)}
    (hU : MeasurableSet U) (htop : volume U ≠ ∞) (hsub : ∀ i, S.phi i '' U ⊆ U)
    (hdisj : Pairwise fun i j => Disjoint (S.phi i '' U) (S.phi j '' U))
    (hsum : ∑ i, |(S.mat i).det| = 1) :
    S.IsInvariantMeasure (fun i => ENNReal.ofReal |(S.mat i).det|)
      ((volume U)⁻¹ • volume.restrict U) := by
  have hterm : ∀ i, ENNReal.ofReal |(S.mat i).det| •
      ((volume U)⁻¹ • volume.restrict U).map (S.phi i) =
      (volume U)⁻¹ • volume.restrict (S.phi i '' U) := fun i => by
    rw [Measure.map_smul _ (S.measurableEmbedding_phi i).measurable.aemeasurable, smul_comm,
      smul_map_restrict_phi]
  unfold IsInvariantMeasure
  simp_rw [hterm]
  rw [← Finset.smul_sum, ← Measure.sum_fintype,
    ← Measure.restrict_iUnion hdisj fun i => S.measurableSet_image_phi i hU,
    S.restrict_iUnion_image_phi hU htop hsub hdisj hsum]

/-- If `∑_i |det A_i| = 1` under the strong open set condition, then normalised Lebesgue measure
on the open set is an invariant probability measure of exact dimension two. This is the
measure `ν` of the case `s ≥ 2` of `thm:main_extended`, tex lines 3396 to 3409. -/
theorem StrongOpenSet.exists_isInvariantMeasure_isExactDim [Fintype ι]
    (h : S.StrongOpenSet) (hsum : ∑ i, |(S.mat i).det| = 1) :
    ∃ ν : Measure (ℝ × ℝ), IsProbabilityMeasure ν ∧
      S.IsInvariantMeasure (fun i => ENNReal.ofReal |(S.mat i).det|) ν ∧ IsExactDim ν 2 := by
  obtain ⟨U, hU, hbdd, hne, hsub, hdisj⟩ := h.exists_isBounded
  have h0 : volume U ≠ 0 := (hU.measure_pos volume (hne.mono inter_subset_left)).ne'
  have htop : volume U ≠ ∞ := hbdd.measure_lt_top.ne
  refine ⟨(volume U)⁻¹ • volume.restrict U, ⟨?_⟩,
    S.isInvariantMeasure_normalised_volume hU.measurableSet htop hsub hdisj hsum,
    isExactDim_normalised_volume hU h0 htop⟩
  rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
    ENNReal.inv_mul_cancel h0 htop]

end System

end BoxLike
