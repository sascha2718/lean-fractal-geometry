module

/-
Changes of basis for planar self-affine sets: the reduction of `sec:irreducibility` (tex lines
777 to 789) and the remark after `thm:two-block-normalisation` (tex lines 2233 to 2234) that
invertible linear changes of coordinates `T` preserve the pressure, the Lyapunov exponents and
the dimensions of planar sets and measures.

For an invertible matrix `T`, the system `T⁻¹ ∘ φ_i ∘ T` has the linear parts `T⁻¹ A_i T` and the
translations `T⁻¹ v_i`; its canonical projection is `T⁻¹ ∘ π` and its attractor is `T⁻¹(X)`.
The map `T` is bi-Lipschitz, so the dimensions of sets and the pointwise dimensions of measures
are preserved; `T⁻¹ A_𝐢 T` and `A_𝐢` have the same determinant and comparable norms, so the
singular value function, the pressure, the Lyapunov exponents, the energy, the equilibrium states
and the Gibbs bounds are preserved. Apart from the all-anti-diagonal case, a proximal tuple is
irreducible and not strongly irreducible exactly when it is box-like with rotations in a basis of
unit vectors; the unit length of the basis vectors makes the conjugated matrices contracting.

* `linMap`, `linHomeomorph`, `linMeasurableEquiv`, `lipschitzWith_linMap`: the linear map `T` of
  the plane.
* `dimH_image_linMap`, `upperBoxDim_image_linMap`, `lowerBoxDim_image_linMap`,
  `packingDim_image_linMap`: invariance of the dimensions of sets.
* `LogComparable`, `LogComparable.tendsto`, `LogComparable.limsup_eq`, `LogComparable.liminf_eq`:
  comparable ball measures have the same pointwise dimensions.
* `hasLocalDim_map_linMap_iff`, `upperLocalDim_map_linMap`, `lowerLocalDim_map_linMap`,
  `isExactDim_map_linMap_iff`, `hasLocalDimPair_map_linMap_iff`, `upperPackingDim_map_linMap`,
  `lowerHausdorffDim_map_linMap`, `upperHausdorffDim_map_linMap`: invariance of the dimensions
  of measures.
* `condNum`, `norm_conj_le`, `norm_le_conj`, `svf_le_mul_of_norm_le`: `α_1(T⁻¹ B T)` and
  `α_1(B)` agree up to the factor `‖T⁻¹‖ ‖T‖`, and so do `φ^s(T⁻¹ B T)` and `φ^s(B)`, `s ≥ 0`.
* `MatrixTuple.conj`, `MatrixTuple.Comparable`, `MatrixTuple.comparable_conj`: the tuple in
  another basis, and tuples with comparable singular values.
* `MatrixTuple.Comparable.pressure_eq`, `MatrixTuple.Comparable.lyapunov₁_eq`,
  `MatrixTuple.Comparable.lyapunov₂_eq`, `MatrixTuple.Comparable.energyLim_eq`,
  `MatrixTuple.Comparable.isEquilibriumState_iff`, `MatrixTuple.Comparable.hasGibbsBounds_iff`:
  invariance of the thermodynamic quantities.
* `MatrixTuple.tupleIrreducible_conj_iff`, `MatrixTuple.tupleStronglyIrreducible_conj_iff`,
  `MatrixTuple.tupleProximal_conj_iff`: the notions of `sec:irreducibility` do not depend on the
  basis.
* `PlanarSystem.StrongSeparation`, `PlanarSystem.StrongOpenSet`: the separation conditions of
  `sec:box_like_self_affine` for a planar system; `System.toPlanar_strongSeparation_iff`,
  `System.toPlanar_strongOpenSet_iff` identify them with those of a box-like system.
* `PlanarSystem.ConjBy`, `PlanarSystem.conj`, `PlanarSystem.ConjBy.symm`: a planar system in
  another basis.
* `PlanarSystem.ConjBy.proj_eq`, `PlanarSystem.ConjBy.attractor_eq`,
  `PlanarSystem.ConjBy.dimH_attractor`, `PlanarSystem.ConjBy.upperBoxDim_attractor`,
  `PlanarSystem.ConjBy.lowerBoxDim_attractor`, `PlanarSystem.ConjBy.packingDim_attractor`: the
  attractor is `T⁻¹(X)`, with the same dimensions.
* `PlanarSystem.ConjBy.strongSeparation_iff`, `PlanarSystem.ConjBy.strongOpenSet_iff`: the
  separation conditions are preserved.
* `PlanarSystem.ConjBy.map_proj`, `PlanarSystem.ConjBy.hasLocalDim_iff`,
  `PlanarSystem.ConjBy.isExactDim_iff`, `PlanarSystem.ConjBy.hasLocalDimPair_iff`,
  `PlanarSystem.ConjBy.upperPackingDim_eq`, `PlanarSystem.ConjBy.lowerHausdorffDim_eq`,
  `PlanarSystem.ConjBy.upperHausdorffDim_eq`: the projected measure is `T⁻¹_*(π_*μ)`, with the
  same pointwise dimensions.
* `PlanarSystem.ConjBy.pressure_eq`, `PlanarSystem.ConjBy.pressure_eq_zero_iff`,
  `PlanarSystem.ConjBy.lyapunov₁_eq`, `PlanarSystem.ConjBy.lyapunov₂_eq`,
  `PlanarSystem.ConjBy.energyLim_eq`,
  `PlanarSystem.ConjBy.isEquilibriumState_iff`, `PlanarSystem.ConjBy.hasGibbsBounds_iff`,
  `PlanarSystem.ConjBy.classification_iff`: the thermodynamic quantities and the notions of
  `sec:irreducibility` are preserved.
* `System.pressure_dimaff_of_conjBy`, `System.dimaff_eq_of_conjBy`: the affinity dimension does
  not depend on the basis.
* `IsUnitBasis`, `SimultaneouslyAntiDiagonal`, `abs_le_norm_of_isUnitBasis`,
  `norm_conj_le_of_isUnitBasis`, `exists_isUnitBasis`: bases of unit vectors.
* `exists_eq_boxMat_of_conj_diag`, `boxType_eq_of_conj`: for a proximal tuple the type,
  diagonal or anti-diagonal, of each matrix does not depend on the basis.
* `irreducible_not_stronglyIrreducible_iff_unitBasis`: tex lines 696 to 698.
* `PlanarSystem.exists_system_of_irreducible`: tex lines 696 to 708 for a planar system.
-/
public import BoxLike.Aligned.BoxLikeSA
public import BoxLike.Classification
public import BoxLike.DimensionFormula
public import BoxLike.MeasureDimBounds
public import BoxLike.Planar.Lyapunov
public import BoxLike.SeparationConditions
public import BoxLike.SetDimensions
public import BoxLike.TupleEquilibrium

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set Matrix Metric
open scoped Matrix.Norms.L2Operator ENNReal NNReal

/-! ### Linear changes of coordinates of the plane -/

section LinMap

variable {T U : Matrix (Fin 2) (Fin 2) ℝ}

/-- The linear map `z ↦ T z` of the plane, for a matrix `T` acting on coordinate vectors. -/
def linMap (T : Matrix (Fin 2) (Fin 2) ℝ) (z : ℝ × ℝ) : ℝ × ℝ := ofVec (T *ᵥ toVec z)

/-- The coordinate vector of `T z` is `T` applied to that of `z`. -/
@[simp] theorem toVec_linMap (T : Matrix (Fin 2) (Fin 2) ℝ) (z : ℝ × ℝ) :
    toVec (linMap T z) = T *ᵥ toVec z :=
  toVec_ofVec _

/-- `T (U z) = (T U) z`. -/
theorem linMap_linMap (T U : Matrix (Fin 2) (Fin 2) ℝ) (z : ℝ × ℝ) :
    linMap T (linMap U z) = linMap (T * U) z := by
  rw [linMap, toVec_linMap, Matrix.mulVec_mulVec, linMap]

/-- The identity matrix acts as the identity. -/
@[simp] theorem linMap_one (z : ℝ × ℝ) : linMap 1 z = z := by
  rw [linMap, Matrix.one_mulVec, ofVec_toVec]

/-- `T⁻¹ (T z) = z` for an invertible `T`. -/
theorem linMap_inv_linMap (hT : T.det ≠ 0) (z : ℝ × ℝ) : linMap T⁻¹ (linMap T z) = z := by
  rw [linMap_linMap, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hT), linMap_one]

/-- `T (T⁻¹ z) = z` for an invertible `T`. -/
theorem linMap_linMap_inv (hT : T.det ≠ 0) (z : ℝ × ℝ) : linMap T (linMap T⁻¹ z) = z := by
  rw [linMap_linMap, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hT), linMap_one]

/-- `linMap T` is additive. -/
theorem linMap_add (T : Matrix (Fin 2) (Fin 2) ℝ) (z w : ℝ × ℝ) :
    linMap T (z + w) = linMap T z + linMap T w := by
  rw [linMap, toVec_add, Matrix.mulVec_add, ofVec_add, linMap, linMap]

/-- `linMap T` commutes with subtraction. -/
theorem linMap_sub (T : Matrix (Fin 2) (Fin 2) ℝ) (z w : ℝ × ℝ) :
    linMap T (z - w) = linMap T z - linMap T w := by
  rw [linMap, toVec_sub, Matrix.mulVec_sub, ofVec_sub, linMap, linMap]

/-- `T 0 = 0`. -/
@[simp] theorem linMap_zero (T : Matrix (Fin 2) (Fin 2) ℝ) : linMap T 0 = 0 := by
  rw [linMap, toVec_zero, Matrix.mulVec_zero, ofVec_zero]

/-- The inverse of an invertible `2 × 2` matrix is invertible. -/
theorem det_inv_ne_zero (hT : T.det ≠ 0) : (T⁻¹).det ≠ 0 := by
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero hT

/-- `(T⁻¹)⁻¹ = T` for an invertible `T`. -/
theorem inv_inv_of_det_ne_zero (hT : T.det ≠ 0) : T⁻¹⁻¹ = T :=
  Matrix.nonsing_inv_nonsing_inv T (isUnit_iff_ne_zero.2 hT)

/-- The supremum norm of the coordinate vector of `z` is the norm of `z`. -/
theorem norm_toVec (z : ℝ × ℝ) : ‖toVec z‖ = ‖z‖ := by
  rw [toVec, norm_vec2, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]

/-- `‖T z‖ ≤ 2 ‖T‖ ‖z‖`, with the `ℓ²` operator norm of `T` and the supremum norm of the
plane. -/
theorem norm_linMap_le (T : Matrix (Fin 2) (Fin 2) ℝ) (z : ℝ × ℝ) :
    ‖linMap T z‖ ≤ 2 * ‖T‖ * ‖z‖ := by
  refine (norm_ofVec_le _).trans ?_
  rw [← norm_toVec z]
  exact norm_mulVec_le T (toVec z)

/-- `linMap T` is Lipschitz with constant `2 ‖T‖`. -/
theorem lipschitzWith_linMap (T : Matrix (Fin 2) (Fin 2) ℝ) :
    LipschitzWith (2 * ‖T‖₊) (linMap T) := by
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  rw [dist_eq_norm, dist_eq_norm, ← linMap_sub]
  push_cast
  exact norm_linMap_le T (z - w)

/-- `linMap T` is continuous. -/
theorem continuous_linMap (T : Matrix (Fin 2) (Fin 2) ℝ) : Continuous (linMap T) :=
  (lipschitzWith_linMap T).continuous

/-- `linMap T` is Borel. -/
theorem measurable_linMap (T : Matrix (Fin 2) (Fin 2) ℝ) : Measurable (linMap T) :=
  (continuous_linMap T).measurable

/-- `linMap T` is injective for an invertible `T`. -/
theorem linMap_injective (hT : T.det ≠ 0) : Function.Injective (linMap T) := fun z w h => by
  rw [← linMap_inv_linMap hT z, h, linMap_inv_linMap hT w]

/-- An invertible `T` gives a homeomorphism of the plane. -/
noncomputable def linHomeomorph (T : Matrix (Fin 2) (Fin 2) ℝ) (hT : T.det ≠ 0) :
    ℝ × ℝ ≃ₜ ℝ × ℝ where
  toFun := linMap T
  invFun := linMap T⁻¹
  left_inv := linMap_inv_linMap hT
  right_inv := linMap_linMap_inv hT
  continuous_toFun := continuous_linMap T
  continuous_invFun := continuous_linMap T⁻¹

/-- An invertible `T` gives a measurable equivalence of the plane. -/
noncomputable def linMeasurableEquiv (T : Matrix (Fin 2) (Fin 2) ℝ) (hT : T.det ≠ 0) :
    ℝ × ℝ ≃ᵐ ℝ × ℝ :=
  (linHomeomorph T hT).toMeasurableEquiv

/-- The measurable equivalence of `T` is `linMap T`. -/
@[simp] theorem coe_linMeasurableEquiv (hT : T.det ≠ 0) :
    ⇑(linMeasurableEquiv T hT) = linMap T :=
  rfl

/-- `closedBall z (r / (2‖T‖)) ⊆ T⁻¹(closedBall (T z) r)`. -/
theorem closedBall_subset_preimage_linMap (hT : T.det ≠ 0) (z : ℝ × ℝ) (r : ℝ) :
    closedBall z ((2 * ‖T‖)⁻¹ * r) ⊆ linMap T ⁻¹' closedBall (linMap T z) r := by
  intro y hy
  have hpos : 0 < 2 * ‖T‖ := by have := norm_pos_of_det_ne_zero hT; positivity
  rw [mem_closedBall] at hy
  rw [mem_preimage, mem_closedBall, dist_eq_norm, ← linMap_sub]
  calc ‖linMap T (y - z)‖ ≤ 2 * ‖T‖ * ‖y - z‖ := norm_linMap_le T _
    _ ≤ 2 * ‖T‖ * ((2 * ‖T‖)⁻¹ * r) := by
        rw [← dist_eq_norm]; exact mul_le_mul_of_nonneg_left hy hpos.le
    _ = r := by rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]

/-- `T⁻¹(closedBall (T z) r) ⊆ closedBall z (2 ‖T⁻¹‖ r)`. -/
theorem preimage_linMap_subset_closedBall (hT : T.det ≠ 0) (z : ℝ × ℝ) (r : ℝ) :
    linMap T ⁻¹' closedBall (linMap T z) r ⊆ closedBall z (2 * ‖T⁻¹‖ * r) := by
  intro y hy
  rw [mem_preimage, mem_closedBall, dist_eq_norm, ← linMap_sub] at hy
  rw [mem_closedBall, dist_eq_norm]
  calc ‖y - z‖ = ‖linMap T⁻¹ (linMap T (y - z))‖ := by rw [linMap_inv_linMap hT]
    _ ≤ 2 * ‖T⁻¹‖ * ‖linMap T (y - z)‖ := norm_linMap_le _ _
    _ ≤ 2 * ‖T⁻¹‖ * r := mul_le_mul_of_nonneg_left hy (by positivity)

end LinMap

/-! ### Dimensions of sets -/

section SetDims

variable {T : Matrix (Fin 2) (Fin 2) ℝ}

/-- `T⁻¹ (T E) = E`. -/
theorem image_linMap_inv_image (hT : T.det ≠ 0) (E : Set (ℝ × ℝ)) :
    linMap T⁻¹ '' (linMap T '' E) = E := by
  rw [image_image]
  simp [linMap_inv_linMap hT]

/-- An invertible linear map preserves the Hausdorff dimension (tex lines 2233 to 2234). -/
theorem dimH_image_linMap (hT : T.det ≠ 0) (E : Set (ℝ × ℝ)) :
    dimH (linMap T '' E) = dimH E := by
  refine le_antisymm (lipschitzWith_linMap T).lipschitzOnWith.dimH_image_le ?_
  calc dimH E = dimH (linMap T⁻¹ '' (linMap T '' E)) := by rw [image_linMap_inv_image hT]
    _ ≤ dimH (linMap T '' E) := (lipschitzWith_linMap T⁻¹).lipschitzOnWith.dimH_image_le

/-- An invertible linear map preserves the upper Minkowski dimension. -/
theorem upperBoxDim_image_linMap (hT : T.det ≠ 0) (E : Set (ℝ × ℝ)) :
    upperBoxDim (linMap T '' E) = upperBoxDim E :=
  upperBoxDim_image_eq (lipschitzWith_linMap T).lipschitzOnWith
    (lipschitzWith_linMap T⁻¹).lipschitzOnWith fun z _ => linMap_inv_linMap hT z

/-- An invertible linear map preserves the lower Minkowski dimension. -/
theorem lowerBoxDim_image_linMap (hT : T.det ≠ 0) (E : Set (ℝ × ℝ)) :
    lowerBoxDim (linMap T '' E) = lowerBoxDim E :=
  lowerBoxDim_image_eq (lipschitzWith_linMap T).lipschitzOnWith
    (lipschitzWith_linMap T⁻¹).lipschitzOnWith fun z _ => linMap_inv_linMap hT z

/-- An invertible linear map preserves the packing dimension. -/
theorem packingDim_image_linMap (hT : T.det ≠ 0) (E : Set (ℝ × ℝ)) :
    packingDim (linMap T '' E) = packingDim E :=
  packingDim_image_eq (lipschitzWith_linMap T).lipschitzOnWith
    (lipschitzWith_linMap T⁻¹).lipschitzOnWith fun z _ => linMap_inv_linMap hT z

end SetDims

/-! ### Comparison of `log m(r) / log r` for comparable functions -/

section LogRatio

/-- Two non-negative functions `m`, `m'` of the radius, monotone on `(0, ∞)`, are comparable if
`m(c_1 r) ≤ m'(r) ≤ m(c_2 r)` for all `r > 0`, with constants `c_1, c_2 > 0`. The measures of the
balls `B(z, r)` and `B(T z, r)` for a measure and its image under an invertible linear map are
comparable in this sense. -/
def LogComparable (m m' : ℝ → ℝ) : Prop :=
  (∀ r, 0 < r → 0 ≤ m r) ∧ (∀ r, 0 < r → 0 ≤ m' r) ∧ MonotoneOn m (Ioi 0) ∧
    MonotoneOn m' (Ioi 0) ∧ ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ r, 0 < r → m (c₁ * r) ≤ m' r ∧ m' r ≤ m (c₂ * r)

variable {m m' : ℝ → ℝ}

/-- Comparability is symmetric, with the constants `c_2⁻¹` and `c_1⁻¹`. -/
theorem LogComparable.symm (h : LogComparable m m') : LogComparable m' m := by
  obtain ⟨h0, h0', hm, hm', c₁, c₂, hc₁, hc₂, h⟩ := h
  refine ⟨h0', h0, hm', hm, c₂⁻¹, c₁⁻¹, inv_pos.2 hc₂, inv_pos.2 hc₁, fun r hr => ⟨?_, ?_⟩⟩
  · have := (h (c₂⁻¹ * r) (by positivity)).2
    rwa [← mul_assoc, mul_inv_cancel₀ hc₂.ne', one_mul] at this
  · have := (h (c₁⁻¹ * r) (by positivity)).1
    rwa [← mul_assoc, mul_inv_cancel₀ hc₁.ne', one_mul] at this

/-- `K / log r → 0` as `r ↓ 0`. -/
theorem tendsto_const_div_log_nhdsGT_zero (K : ℝ) :
    Tendsto (fun r : ℝ => K / Real.log r) (𝓝[>] 0) (𝓝 0) :=
  Real.tendsto_log_nhdsGT_zero.const_div_atBot K

/-- Small radii are less than any positive bound. -/
theorem eventually_nhdsGT_zero_lt {b : ℝ} (hb : 0 < b) : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r ∧ r < b := by
  filter_upwards [eventually_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hb)] with r hr hrb
  exact ⟨hr, hrb⟩

/-- If one of two comparable functions vanishes at a positive radius, both vanish at all small
radii. -/
theorem LogComparable.eventually_eq_zero (h : LogComparable m m') (hz : ¬ ∀ r, 0 < r → 0 < m r) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, m r = 0 ∧ m' r = 0 := by
  obtain ⟨h0, h0', hm, -, c₁, c₂, hc₁, hc₂, h⟩ := h
  push Not at hz
  obtain ⟨ρ, hρ, hmρ⟩ := hz
  have hmρ0 : m ρ = 0 := le_antisymm hmρ (h0 ρ hρ)
  have hzero : ∀ r, 0 < r → r ≤ ρ → m r = 0 := fun r hr hrρ =>
    le_antisymm (hmρ0 ▸ hm hr hρ hrρ) (h0 r hr)
  filter_upwards [eventually_nhdsGT_zero_lt (lt_min hρ (div_pos hρ hc₂))] with r ⟨hr, hrb⟩
  have hr1 : r ≤ ρ := (hrb.trans_le (min_le_left _ _)).le
  have hr2 : c₂ * r ≤ ρ := by
    have := hrb.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ hc₂] at this
    linarith
  refine ⟨hzero r hr hr1, le_antisymm ?_ (h0' r hr)⟩
  calc m' r ≤ m (c₂ * r) := (h r hr).2
    _ = 0 := hzero _ (by positivity) hr2

/-- An eventual upper bound `log m(r) / log r ≤ A` passes to `m'` with an arbitrarily small loss.
If `m > 0`, then `log m'(r) ≥ log m(c_1 r) ≥ A log(c_1 r)` for small `r`, and
`A log c_1 / log r → 0`. -/
theorem LogComparable.eventually_le (h : LogComparable m m') {A : ℝ}
    (hA : ∀ᶠ r in 𝓝[>] (0 : ℝ), Real.log (m r) / Real.log r ≤ A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), Real.log (m' r) / Real.log r ≤ A + ε := by
  by_cases hpos : ∀ r, 0 < r → 0 < m r
  · obtain ⟨-, -, -, -, c₁, c₂, hc₁, hc₂, hc⟩ := h
    have h1 := (tendsto_const_mul_nhdsGT_zero hc₁).eventually hA
    have h2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), A * Real.log c₁ / Real.log r < ε :=
      (tendsto_const_div_log_nhdsGT_zero _).eventually (gt_mem_nhds hε)
    filter_upwards [h1, h2, eventually_nhdsGT_zero_lt (lt_min one_pos (inv_pos.2 hc₁))]
      with r h1 h2 ⟨hr0, hrb⟩
    have hr1 : r < 1 := hrb.trans_le (min_le_left _ _)
    have hcr1 : c₁ * r < 1 := by
      have := mul_lt_mul_of_pos_left (hrb.trans_le (min_le_right _ _)) hc₁
      rwa [mul_inv_cancel₀ hc₁.ne'] at this
    have hlr : Real.log r < 0 := Real.log_neg hr0 hr1
    have hlcr : Real.log (c₁ * r) < 0 := Real.log_neg (by positivity) hcr1
    have e1 : A * Real.log (c₁ * r) ≤ Real.log (m (c₁ * r)) := (div_le_iff_of_neg hlcr).1 h1
    have e2 : Real.log (m (c₁ * r)) ≤ Real.log (m' r) :=
      Real.log_le_log (hpos _ (by positivity)) (hc r hr0).1
    rw [Real.log_mul hc₁.ne' hr0.ne'] at e1
    have e3 : ε * Real.log r < A * Real.log c₁ := (div_lt_iff_of_neg hlr).1 h2
    rw [div_le_iff_of_neg hlr]
    nlinarith
  · have hz := h.eventually_eq_zero hpos
    obtain ⟨r, hr, hr'⟩ := (hA.and hz).exists
    rw [hr'.1, Real.log_zero, zero_div] at hr
    filter_upwards [hz] with r hr''
    rw [hr''.2, Real.log_zero, zero_div]
    linarith

/-- An eventual lower bound `A ≤ log m(r) / log r` passes to `m'` with an arbitrarily small loss.
If `m > 0`, then `log m'(r) ≤ log m(c_2 r) ≤ A log(c_2 r)` for small `r`. -/
theorem LogComparable.eventually_ge (h : LogComparable m m') {A : ℝ}
    (hA : ∀ᶠ r in 𝓝[>] (0 : ℝ), A ≤ Real.log (m r) / Real.log r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), A - ε ≤ Real.log (m' r) / Real.log r := by
  by_cases hpos : ∀ r, 0 < r → 0 < m r
  · obtain ⟨-, -, -, -, c₁, c₂, hc₁, hc₂, hc⟩ := h
    have h1 := (tendsto_const_mul_nhdsGT_zero hc₂).eventually hA
    have h2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), -ε < A * Real.log c₂ / Real.log r :=
      (tendsto_const_div_log_nhdsGT_zero _).eventually (lt_mem_nhds (neg_lt_zero.2 hε))
    filter_upwards [h1, h2, eventually_nhdsGT_zero_lt (lt_min one_pos (inv_pos.2 hc₂))]
      with r h1 h2 ⟨hr0, hrb⟩
    have hr1 : r < 1 := hrb.trans_le (min_le_left _ _)
    have hcr1 : c₂ * r < 1 := by
      have := mul_lt_mul_of_pos_left (hrb.trans_le (min_le_right _ _)) hc₂
      rwa [mul_inv_cancel₀ hc₂.ne'] at this
    have hlr : Real.log r < 0 := Real.log_neg hr0 hr1
    have hlcr : Real.log (c₂ * r) < 0 := Real.log_neg (by positivity) hcr1
    have hm' : 0 < m' r := (hpos _ (by positivity)).trans_le (hc r hr0).1
    have e1 : Real.log (m (c₂ * r)) ≤ A * Real.log (c₂ * r) := (le_div_iff_of_neg hlcr).1 h1
    have e2 : Real.log (m' r) ≤ Real.log (m (c₂ * r)) := Real.log_le_log hm' (hc r hr0).2
    rw [Real.log_mul hc₂.ne' hr0.ne'] at e1
    have e3 : A * Real.log c₂ < -ε * Real.log r := (lt_div_iff_of_neg hlr).1 h2
    rw [le_div_iff_of_neg hlr]
    nlinarith
  · have hz := h.eventually_eq_zero hpos
    obtain ⟨r, hr, hr'⟩ := (hA.and hz).exists
    rw [hr'.1, Real.log_zero, zero_div] at hr
    filter_upwards [hz] with r hr''
    rw [hr''.2, Real.log_zero, zero_div]
    linarith

/-- Comparable functions have the same limit of `log m(r) / log r` as `r ↓ 0`. -/
theorem LogComparable.tendsto (h : LogComparable m m') {d : ℝ}
    (hd : Tendsto (fun r => Real.log (m r) / Real.log r) (𝓝[>] 0) (𝓝 d)) :
    Tendsto (fun r => Real.log (m' r) / Real.log r) (𝓝[>] 0) (𝓝 d) := by
  rw [tendsto_order] at hd ⊢
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have h1 := h.eventually_ge ((hd.1 ((a + d) / 2) (by linarith)).mono fun r hr => hr.le)
      (ε := (d - a) / 4) (by linarith)
    filter_upwards [h1] with r hr
    linarith
  · have h1 := h.eventually_le ((hd.2 ((b + d) / 2) (by linarith)).mono fun r hr => hr.le)
      (ε := (b - d) / 4) (by linarith)
    filter_upwards [h1] with r hr
    linarith

/-- Two sets of reals, each of whose elements lies within any `ε > 0` below an element of the
other, have the same infimum, with the convention `sInf ∅ = 0` and `sInf S = 0` for `S` not
bounded below. -/
theorem sInf_eq_of_forall_add_mem {S S' : Set ℝ} (h : ∀ a ∈ S, ∀ ε > 0, a + ε ∈ S')
    (h' : ∀ a ∈ S', ∀ ε > 0, a + ε ∈ S) : sInf S = sInf S' := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · have hS' : S' = ∅ := eq_empty_of_forall_notMem fun a ha => by
      have := h' a ha 1 one_pos
      rw [hS] at this
      exact this
    rw [hS, hS']
  · have hS' : S'.Nonempty := by
      obtain ⟨a, ha⟩ := hS
      exact ⟨_, h a ha 1 one_pos⟩
    by_cases hb : BddBelow S
    · have hb' : BddBelow S' := by
        obtain ⟨c, hc⟩ := hb
        refine ⟨c - 1, fun a ha => ?_⟩
        have := hc (h' a ha 1 one_pos)
        linarith
      have key : ∀ {X Y : Set ℝ}, Y.Nonempty → BddBelow X → (∀ a ∈ Y, ∀ ε > 0, a + ε ∈ X) →
          sInf X ≤ sInf Y := fun {X Y} hY hX hYX => by
        refine le_of_forall_pos_lt_add fun ε hε => ?_
        obtain ⟨a, ha, hlt⟩ := exists_lt_of_csInf_lt hY (lt_add_of_pos_right (sInf Y) (half_pos hε))
        calc sInf X ≤ a + ε / 2 := csInf_le hX (hYX a ha _ (half_pos hε))
          _ < sInf Y + ε := by linarith
      exact le_antisymm (key hS' hb h') (key hS hb' h)
    · have hb' : ¬ BddBelow S' := fun ⟨c, hc⟩ => hb ⟨c - 1, fun a ha => by
        have := hc (h a ha 1 one_pos)
        linarith⟩
      rw [Real.sInf_of_not_bddBelow hb, Real.sInf_of_not_bddBelow hb']

/-- Two sets of reals, each of whose elements lies within any `ε > 0` above an element of the
other, have the same supremum, with the conventions of `Real.sSup`. -/
theorem sSup_eq_of_forall_sub_mem {S S' : Set ℝ} (h : ∀ a ∈ S, ∀ ε > 0, a - ε ∈ S')
    (h' : ∀ a ∈ S', ∀ ε > 0, a - ε ∈ S) : sSup S = sSup S' := by
  have hneg : ∀ {X Y : Set ℝ}, (∀ a ∈ X, ∀ ε > 0, a - ε ∈ Y) →
      ∀ a ∈ -X, ∀ ε > 0, a + ε ∈ -Y := fun {X Y} hXY a ha ε hε => by
    rw [Set.mem_neg] at ha ⊢
    rw [neg_add']
    exact hXY _ ha ε hε
  have := sInf_eq_of_forall_add_mem (hneg h) (hneg h')
  rw [Real.sInf_neg, Real.sInf_neg] at this
  linarith

/-- Comparable functions have the same `limsup` of `log m(r) / log r` as `r ↓ 0`, as real numbers
with the conventions of `Real.sInf`. -/
theorem LogComparable.limsup_eq (h : LogComparable m m') :
    limsup (fun r => Real.log (m' r) / Real.log r) (𝓝[>] 0) =
      limsup (fun r => Real.log (m r) / Real.log r) (𝓝[>] 0) := by
  rw [Filter.limsup_eq, Filter.limsup_eq]
  exact sInf_eq_of_forall_add_mem (fun a ha ε hε => h.symm.eventually_le ha hε)
    (fun a ha ε hε => h.eventually_le ha hε)

/-- Comparable functions have the same `liminf` of `log m(r) / log r` as `r ↓ 0`. -/
theorem LogComparable.liminf_eq (h : LogComparable m m') :
    liminf (fun r => Real.log (m' r) / Real.log r) (𝓝[>] 0) =
      liminf (fun r => Real.log (m r) / Real.log r) (𝓝[>] 0) := by
  rw [Filter.liminf_eq, Filter.liminf_eq]
  exact sSup_eq_of_forall_sub_mem (fun a ha ε hε => h.symm.eventually_ge ha hε)
    (fun a ha ε hε => h.eventually_ge ha hε)

end LogRatio

/-! ### Dimensions of measures -/

section MeasureDims

variable {T : Matrix (Fin 2) (Fin 2) ℝ} {ν : Measure (ℝ × ℝ)} [IsFiniteMeasure ν]

/-- The measures of the balls `B(z, r)` under `ν` and of `B(T z, r)` under `T_*ν` are comparable,
with the constants `(2 ‖T‖)⁻¹` and `2 ‖T⁻¹‖`. -/
theorem logComparable_map_linMap (hT : T.det ≠ 0) (z : ℝ × ℝ) :
    LogComparable (fun r => ν.real (closedBall z r))
      (fun r => (ν.map (linMap T)).real (closedBall (linMap T z) r)) := by
  have hpos : 0 < ‖T‖ := norm_pos_of_det_ne_zero hT
  have hpos' : 0 < ‖T⁻¹‖ := norm_pos_of_det_ne_zero (det_inv_ne_zero hT)
  have hmap : ∀ r, (ν.map (linMap T)).real (closedBall (linMap T z) r) =
      ν.real (linMap T ⁻¹' closedBall (linMap T z) r) := fun r =>
    map_measureReal_apply (measurable_linMap T) isClosed_closedBall.measurableSet
  refine ⟨fun r _ => measureReal_nonneg, fun r _ => measureReal_nonneg,
    fun r _ r' _ hrr' => measureReal_mono (closedBall_subset_closedBall hrr'),
    fun r _ r' _ hrr' => measureReal_mono (closedBall_subset_closedBall hrr'),
    (2 * ‖T‖)⁻¹, 2 * ‖T⁻¹‖, by positivity, by positivity, fun r _ => ⟨?_, ?_⟩⟩
  · dsimp only
    rw [hmap]
    exact measureReal_mono (closedBall_subset_preimage_linMap hT z r)
  · dsimp only
    rw [hmap]
    exact measureReal_mono (preimage_linMap_subset_closedBall hT z r)

/-- The pointwise dimension is invariant under an invertible linear change of coordinates:
`dimloc(T_*ν, T z) = dimloc(ν, z)` (tex lines 2233 to 2234). -/
theorem hasLocalDim_map_linMap_iff (hT : T.det ≠ 0) (z : ℝ × ℝ) (d : ℝ) :
    HasLocalDim (ν.map (linMap T)) (linMap T z) d ↔ HasLocalDim ν z d :=
  ⟨(logComparable_map_linMap hT z).symm.tendsto, (logComparable_map_linMap hT z).tendsto⟩

/-- `\overline{dim}_loc(T_*ν, T z) = \overline{dim}_loc(ν, z)`. -/
theorem upperLocalDim_map_linMap (hT : T.det ≠ 0) (z : ℝ × ℝ) :
    upperLocalDim (ν.map (linMap T)) (linMap T z) = upperLocalDim ν z :=
  (logComparable_map_linMap hT z).limsup_eq

/-- `\underline{dim}_loc(T_*ν, T z) = \underline{dim}_loc(ν, z)`. -/
theorem lowerLocalDim_map_linMap (hT : T.det ≠ 0) (z : ℝ × ℝ) :
    lowerLocalDim (ν.map (linMap T)) (linMap T z) = lowerLocalDim ν z :=
  (logComparable_map_linMap hT z).liminf_eq

omit [IsFiniteMeasure ν] in
/-- The almost-everywhere filter of `T_*ν` is the image of that of `ν`. -/
theorem ae_map_linMap (hT : T.det ≠ 0) :
    ae (ν.map (linMap T)) = Filter.map (linMap T) (ae ν) := by
  rw [← coe_linMeasurableEquiv hT, MeasurableEquiv.map_ae]

/-- `T_*ν` is exact-dimensional with `dim T_*ν = d` exactly when `ν` is. -/
theorem isExactDim_map_linMap_iff (hT : T.det ≠ 0) (d : ℝ) :
    IsExactDim (ν.map (linMap T)) d ↔ IsExactDim ν d := by
  rw [IsExactDim, IsExactDim, ae_map_linMap hT, Filter.eventually_map]
  simp only [hasLocalDim_map_linMap_iff hT]

/-- The pointwise dimension of `T_*ν` is `d₁` or `d₂` almost everywhere exactly when that of
`ν` is. -/
theorem hasLocalDimPair_map_linMap_iff (hT : T.det ≠ 0) (d₁ d₂ : ℝ) :
    HasLocalDimPair (ν.map (linMap T)) d₁ d₂ ↔ HasLocalDimPair ν d₁ d₂ := by
  rw [HasLocalDimPair, HasLocalDimPair, ae_map_linMap hT, Filter.eventually_map]
  simp only [hasLocalDim_map_linMap_iff hT]

/-- `\overline{dim}_p(T_*ν) = \overline{dim}_p(ν)`. -/
theorem upperPackingDim_map_linMap (hT : T.det ≠ 0) :
    upperPackingDim (ν.map (linMap T)) = upperPackingDim ν := by
  rw [upperPackingDim, upperPackingDim, essSup, essSup, ae_map_linMap hT, ← Filter.limsup_comp]
  congr 1
  funext z
  exact upperLocalDim_map_linMap hT z

/-- `\underline{dim}_H(T_*ν) = \underline{dim}_H(ν)`. -/
theorem lowerHausdorffDim_map_linMap (hT : T.det ≠ 0) :
    lowerHausdorffDim (ν.map (linMap T)) = lowerHausdorffDim ν := by
  rw [lowerHausdorffDim, lowerHausdorffDim, essInf, essInf, ae_map_linMap hT,
    ← Filter.liminf_comp]
  congr 1
  funext z
  exact lowerLocalDim_map_linMap hT z

/-- `\overline{dim}_H(T_*ν) = \overline{dim}_H(ν)`. -/
theorem upperHausdorffDim_map_linMap (hT : T.det ≠ 0) :
    upperHausdorffDim (ν.map (linMap T)) = upperHausdorffDim ν := by
  rw [upperHausdorffDim, upperHausdorffDim, essSup, essSup, ae_map_linMap hT,
    ← Filter.limsup_comp]
  congr 1
  funext z
  exact lowerLocalDim_map_linMap hT z

end MeasureDims

/-! ### Matrix tuples in another basis -/

/-- `T (T⁻¹ M T) T⁻¹ = M`. -/
theorem mul_conj_mul_inv {T : Matrix (Fin 2) (Fin 2) ℝ} (hT : T.det ≠ 0)
    (M : Matrix (Fin 2) (Fin 2) ℝ) : T * (T⁻¹ * M * T) * T⁻¹ = M := by
  have hu := isUnit_iff_ne_zero.2 hT
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mul]

/-- The condition number `‖T⁻¹‖ ‖T‖` of `T`, which bounds the distortion of the singular values
under the change of basis by `T`. -/
noncomputable def condNum (T : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := ‖T⁻¹‖ * ‖T‖

/-- `‖T⁻¹‖ ‖T‖ ≥ 1` for an invertible `T`, since `1 = ‖T⁻¹ T‖`. -/
theorem one_le_condNum {T : Matrix (Fin 2) (Fin 2) ℝ} (hT : T.det ≠ 0) : 1 ≤ condNum T := by
  rw [condNum, ← norm_one_matrix, ← Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hT)]
  exact Matrix.l2_opNorm_mul _ _

/-- `α_1(T⁻¹ B T) ≤ ‖T⁻¹‖ ‖T‖ α_1(B)`. -/
theorem norm_conj_le (T B : Matrix (Fin 2) (Fin 2) ℝ) : ‖T⁻¹ * B * T‖ ≤ condNum T * ‖B‖ := by
  calc ‖T⁻¹ * B * T‖ ≤ ‖T⁻¹ * B‖ * ‖T‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖T⁻¹‖ * ‖B‖ * ‖T‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
    _ = condNum T * ‖B‖ := by rw [condNum]; ring

/-- `α_1(B) ≤ ‖T⁻¹‖ ‖T‖ α_1(T⁻¹ B T)`, from `B = T (T⁻¹ B T) T⁻¹`. -/
theorem norm_le_conj {T : Matrix (Fin 2) (Fin 2) ℝ} (hT : T.det ≠ 0)
    (B : Matrix (Fin 2) (Fin 2) ℝ) : ‖B‖ ≤ condNum T * ‖T⁻¹ * B * T‖ := by
  calc ‖B‖ = ‖T * (T⁻¹ * B * T) * T⁻¹‖ := by rw [mul_conj_mul_inv hT]
    _ ≤ ‖T * (T⁻¹ * B * T)‖ * ‖T⁻¹‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖T‖ * ‖T⁻¹ * B * T‖ * ‖T⁻¹‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
    _ = condNum T * ‖T⁻¹ * B * T‖ := by rw [condNum]; ring

/-- If `|det B'| = |det B|` and `α_1(B') ≤ κ α_1(B)` with `κ ≥ 1`, then `φ^s(B') ≤ κ φ^s(B)` for
every `s ≥ 0`: the exponent of `α_1` in `φ^s` is `s ≤ 1` or `2 - s ≤ 1`, and `φ^s` depends on the
determinant alone for `s > 2`. -/
theorem svf_le_mul_of_norm_le {s κ : ℝ} (hs : 0 ≤ s) (hκ : 1 ≤ κ)
    {B B' : Matrix (Fin 2) (Fin 2) ℝ} (hdet : |B'.det| = |B.det|) (hn : ‖B'‖ ≤ κ * ‖B‖) :
    svf s B' ≤ κ * svf s B := by
  have hκ0 : 0 ≤ κ := by linarith
  have key : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖B'‖ ^ t ≤ κ * ‖B‖ ^ t := fun t ht0 ht1 => by
    calc ‖B'‖ ^ t ≤ (κ * ‖B‖) ^ t := Real.rpow_le_rpow (norm_nonneg _) hn ht0
      _ = κ ^ t * ‖B‖ ^ t := Real.mul_rpow hκ0 (norm_nonneg _)
      _ ≤ κ * ‖B‖ ^ t := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) _)
          simpa using Real.rpow_le_rpow_of_exponent_le hκ ht1
  unfold svf
  split_ifs with h1 h2
  · exact key s hs h1
  · rw [hdet, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (key (2 - s) (by linarith) (by linarith))
      (Real.rpow_nonneg (abs_nonneg _) _)
  · rw [hdet]
    exact le_mul_of_one_le_left (Real.rpow_nonneg (abs_nonneg _) _) hκ

/-- If `x ≤ κ y` and `y ≤ κ x` for positive `x, y`, then `|log x - log y| ≤ log κ`. -/
theorem abs_log_sub_log_le {x y κ : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ κ * y)
    (hyx : y ≤ κ * x) : |Real.log x - Real.log y| ≤ Real.log κ := by
  have hκ : 0 < κ := by
    by_contra h
    push Not at h
    nlinarith
  rw [abs_sub_le_iff]
  constructor
  · have := Real.log_le_log hx hxy
    rw [Real.log_mul hκ.ne' hy.ne'] at this
    linarith
  · have := Real.log_le_log hy hyx
    rw [Real.log_mul hκ.ne' hx.ne'] at this
    linarith

namespace MatrixTuple

variable {ι : Type*}

/-- The tuple `𝖠` in the basis given by the columns of `T`, `(T⁻¹ A_i T)_i`: the linear parts of
the system `T⁻¹ ∘ φ_i ∘ T` (tex lines 696 to 708 and 2352 to 2353). -/
noncomputable def conj (T : Matrix (Fin 2) (Fin 2) ℝ) (A : ι → Matrix (Fin 2) (Fin 2) ℝ) :
    ι → Matrix (Fin 2) (Fin 2) ℝ := fun i => T⁻¹ * A i * T

variable {T : Matrix (Fin 2) (Fin 2) ℝ} {A A' : ι → Matrix (Fin 2) (Fin 2) ℝ} {κ : ℝ}

/-- `(T⁻¹ 𝖠 T)_𝐢 = T⁻¹ A_𝐢 T`. -/
theorem word_conj (hT : T.det ≠ 0) (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (w : List ι) :
    word (conj T A) w = T⁻¹ * word A w * T :=
  (conj_list_prod hT A w).symm

/-- A change of basis keeps the matrices invertible. -/
theorem det_conj_ne_zero (hT : T.det ≠ 0) (hA : ∀ i, (A i).det ≠ 0) (i : ι) :
    (conj T A i).det ≠ 0 := by
  rw [conj, det_inv_mul_mul hT]
  exact hA i

/-- Changing the basis by `T` and then by `T⁻¹` gives back the tuple. -/
theorem conj_inv_conj (hT : T.det ≠ 0) (A : ι → Matrix (Fin 2) (Fin 2) ℝ) :
    conj T⁻¹ (conj T A) = A := by
  funext i
  simp only [conj]
  rw [inv_inv_of_det_ne_zero hT, mul_conj_mul_inv hT]

/-- The tuples `𝖠` and `𝖠'` have comparable singular values with constant `κ ≥ 1`: for every
word, `|det A'_𝐢| = |det A_𝐢|` and `κ⁻¹ α_1(A_𝐢) ≤ α_1(A'_𝐢) ≤ κ α_1(A_𝐢)`. Then also
`α_2 = |det| / α_1` are comparable. This is the relation between `𝖠` and `T⁻¹ 𝖠 T`
(tex line 2233). -/
def Comparable (A A' : ι → Matrix (Fin 2) (Fin 2) ℝ) (κ : ℝ) : Prop :=
  1 ≤ κ ∧ ∀ w : List ι, |(word A' w).det| = |(word A w).det| ∧ ‖word A' w‖ ≤ κ * ‖word A w‖ ∧
    ‖word A w‖ ≤ κ * ‖word A' w‖

/-- Comparability is symmetric. -/
theorem Comparable.symm (h : Comparable A A' κ) : Comparable A' A κ :=
  ⟨h.1, fun w => ⟨(h.2 w).1.symm, (h.2 w).2.2, (h.2 w).2.1⟩⟩

/-- A tuple and the same tuple in another basis have comparable singular values, with the
constant `‖T⁻¹‖ ‖T‖`. -/
theorem comparable_conj (hT : T.det ≠ 0) (A : ι → Matrix (Fin 2) (Fin 2) ℝ) :
    Comparable A (conj T A) (condNum T) :=
  ⟨one_le_condNum hT, fun w => by
    rw [word_conj hT]
    exact ⟨by rw [det_inv_mul_mul hT], norm_conj_le T _, norm_le_conj hT _⟩⟩

/-- The product over a one-letter word is the matrix of the letter. -/
theorem word_singleton (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (i : ι) : word A [i] = A i := by
  simp [word]

/-- A tuple comparable with an invertible tuple is invertible. -/
theorem Comparable.det_ne_zero (h : Comparable A A' κ) (hA : ∀ i, (A i).det ≠ 0) (i : ι) :
    (A' i).det ≠ 0 := by
  have := (h.2 [i]).1
  rw [word_singleton, word_singleton] at this
  exact abs_ne_zero.1 (this ▸ abs_ne_zero.2 (hA i))

/-- `φ^s(A'_𝐢) ≤ κ φ^s(A_𝐢)` for `s ≥ 0`. -/
theorem Comparable.svf_le (h : Comparable A A' κ) {s : ℝ} (hs : 0 ≤ s) (w : List ι) :
    svf s (word A' w) ≤ κ * svf s (word A w) :=
  svf_le_mul_of_norm_le hs h.1 (h.2 w).1 (h.2 w).2.1

/-- `∑_{|𝐢| = n} φ^s(A'_𝐢) ≤ κ ∑_{|𝐢| = n} φ^s(A_𝐢)` for `s ≥ 0`. -/
theorem Comparable.svfSum_le [Fintype ι] (h : Comparable A A' κ) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    svfSum A' s n ≤ κ * svfSum A s n := by
  rw [svfSum, svfSum, Finset.mul_sum]
  exact Finset.sum_le_sum fun w _ => h.svf_le hs _

/-- The sums `∑_{|𝐢| = n} φ^s(A_𝐢)` vanish for `n ≥ 1` over the empty alphabet. -/
theorem svfSum_of_isEmpty [Fintype ι] [IsEmpty ι] (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ)
    {n : ℕ} (hn : 1 ≤ n) : svfSum A s n = 0 := by
  have : IsEmpty (Fin n → ι) := ⟨fun f => isEmptyElim (f ⟨0, hn⟩)⟩
  rw [svfSum, Finset.univ_eq_empty, Finset.sum_empty]

/-- Comparable tuples have the same pressure `P(𝖠, s)`, `s ≥ 0`: the sums
`∑_{|𝐢| = n} φ^s(A_𝐢)` agree up to the factor `κ`, and `n⁻¹ log κ → 0`. -/
theorem Comparable.pressure_eq [Fintype ι] (h : Comparable A A' κ) (hA : ∀ i, (A i).det ≠ 0)
    {s : ℝ} (hs : 0 ≤ s) : pressure A' s = pressure A s := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [pressure, pressure]
    congr 1
    refine Set.image_congr fun n hn => ?_
    rw [svfSum_of_isEmpty _ _ hn, svfSum_of_isEmpty _ _ hn]
  · have hA' := h.det_ne_zero hA
    have key : ∀ {B B' : ι → Matrix (Fin 2) (Fin 2) ℝ}, (∀ i, (B i).det ≠ 0) →
        (∀ i, (B' i).det ≠ 0) → Comparable B B' κ → pressure B' s ≤ pressure B s := by
      intro B B' hB hB' hc
      have t := tendsto_pressure hB hs
      have t' := tendsto_pressure hB' hs
      have tK : Tendsto (fun n : ℕ => Real.log κ / n + Real.log (svfSum B s n) / n) atTop
          (𝓝 (0 + pressure B s)) := (tendsto_const_div_atTop_nhds_zero_nat _).add t
      rw [zero_add] at tK
      refine le_of_tendsto_of_tendsto' t' tK fun n => ?_
      have hpos := svfSum_pos hB s n
      have hpos' := svfSum_pos hB' s n
      have hκ : 0 < κ := lt_of_lt_of_le one_pos hc.1
      rw [← add_div, ← Real.log_mul hκ.ne' hpos.ne']
      exact div_le_div_of_nonneg_right (Real.log_le_log hpos' (hc.svfSum_le hs n))
        (Nat.cast_nonneg n)
    exact le_antisymm (key hA hA' h) (key hA' hA h.symm)

section Measures

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] {μ : Measure (ℤ → ι)}
  [IsProbabilityMeasure μ]

/-- If `|H(𝐢) - G(𝐢)| ≤ c` for all words, then `n⁻¹ ∫ H(𝐢|_n) dμ` and `n⁻¹ ∫ G(𝐢|_n) dμ` have the
same limit. -/
theorem tendsto_integral_futureWord_div_of_abs_sub_le {G H : List ι → ℝ} {c L : ℝ}
    (hGH : ∀ w, |H w - G w| ≤ c)
    (hG : Tendsto (fun n : ℕ => (∫ x, G (futureWord x n) ∂μ) / n) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => (∫ x, H (futureWord x n) ∂μ) / n) atTop (𝓝 L) := by
  have hd : Tendsto (fun n : ℕ => (∫ x, H (futureWord x n) ∂μ) / n -
      (∫ x, G (futureWord x n) ∂μ) / n) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (tendsto_const_div_atTop_nhds_zero_nat c)
    rw [← sub_div, ← integral_sub (integrable_comp_futureWord H n)
      (integrable_comp_futureWord G n), Real.norm_eq_abs, abs_div, Nat.abs_cast]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n)
    have := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun x => H (futureWord x n) - G (futureWord x n)) (C := c)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hGH _)
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
  simpa using hG.add hd

/-- Comparable tuples have the same Lyapunov exponent `λ_1`, for an invariant `μ`. -/
theorem Comparable.lyapunov₁_eq (h : Comparable A A' κ) (hA : ∀ i, (A i).det ≠ 0)
    (hμ : MeasurePreserving (shift 1) μ μ) : lyapunov₁ A' μ = lyapunov₁ A μ := by
  have hA' := h.det_ne_zero hA
  have t' := tendsto_integral_futureWord_div_of_abs_sub_le
    (G := fun w => Real.log ‖word A w‖) (H := fun w => Real.log ‖word A' w‖)
    (fun w => abs_log_sub_log_le (norm_word_pos hA' w) (norm_word_pos hA w) (h.2 w).2.1
      (h.2 w).2.2) (tendsto_lyapunov₁_of_det_ne_zero hA hμ)
  rw [lyapunov₁, t'.limUnder_eq]

/-- Comparable tuples have the same Lyapunov exponent `λ_2`, for an invariant `μ`. -/
theorem Comparable.lyapunov₂_eq (h : Comparable A A' κ) (hA : ∀ i, (A i).det ≠ 0)
    (hμ : MeasurePreserving (shift 1) μ μ) : lyapunov₂ A' μ = lyapunov₂ A μ := by
  have hA' := h.det_ne_zero hA
  have hcmp : ∀ w, |Real.log (|(word A' w).det| / ‖word A' w‖) -
      Real.log (|(word A w).det| / ‖word A w‖)| ≤ Real.log κ := fun w => by
    have hd := abs_det_word_pos hA w
    have hn := norm_word_pos hA w
    have hn' := norm_word_pos hA' w
    rw [(h.2 w).1]
    refine abs_log_sub_log_le (div_pos hd hn') (div_pos hd hn) ?_ ?_
    · rw [div_le_iff₀ hn', show κ * (|(word A w).det| / ‖word A w‖) * ‖word A' w‖ =
        |(word A w).det| * (κ * ‖word A' w‖) / ‖word A w‖ by ring, le_div_iff₀ hn]
      exact mul_le_mul_of_nonneg_left (h.2 w).2.2 hd.le
    · rw [div_le_iff₀ hn, show κ * (|(word A w).det| / ‖word A' w‖) * ‖word A w‖ =
        |(word A w).det| * (κ * ‖word A w‖) / ‖word A' w‖ by ring, le_div_iff₀ hn']
      exact mul_le_mul_of_nonneg_left (h.2 w).2.1 hd.le
  have t' := tendsto_integral_futureWord_div_of_abs_sub_le
    (G := fun w => Real.log (|(word A w).det| / ‖word A w‖))
    (H := fun w => Real.log (|(word A' w).det| / ‖word A' w‖)) hcmp
    (tendsto_lyapunov₂_of_det_ne_zero hA hμ)
  rw [lyapunov₂, t'.limUnder_eq]

/-- Comparable tuples have the same `s`-energy `Λ(𝖠, μ, s)`, `s ≥ 0`, for an invariant `μ`. -/
theorem Comparable.energyLim_eq (h : Comparable A A' κ) (hA : ∀ i, (A i).det ≠ 0)
    (hμ : MeasurePreserving (shift 1) μ μ) {s : ℝ} (hs : 0 ≤ s) :
    energyLim A' s μ = energyLim A s μ := by
  have hA' := h.det_ne_zero hA
  have t' := tendsto_integral_futureWord_div_of_abs_sub_le
    (G := fun w => Real.log (svf s (word A w))) (H := fun w => Real.log (svf s (word A' w)))
    (fun w => abs_log_sub_log_le (svf_word_pos hA' s w) (svf_word_pos hA s w) (h.svf_le hs w)
      (h.symm.svf_le hs w)) (tendsto_energyLim hA hμ hs)
  rw [energyLim, t'.limUnder_eq]

/-- Comparable tuples have the same `s`-equilibrium states, `s ≥ 0`, among the invariant
measures. -/
theorem Comparable.isEquilibriumState_iff (h : Comparable A A' κ) (hA : ∀ i, (A i).det ≠ 0)
    (hμ : MeasurePreserving (shift 1) μ μ) {s : ℝ} (hs : 0 ≤ s) :
    IsEquilibriumState A' s μ ↔ IsEquilibriumState A s μ := by
  rw [IsEquilibriumState, IsEquilibriumState, h.pressure_eq hA hs, h.energyLim_eq hA hμ hs]

end Measures

/-- The Gibbs bounds of `thm:irred_eq_state` pass to a comparable tuple, with the constant
multiplied by `κ`. -/
theorem Comparable.hasGibbsBounds [Fintype ι] [MeasurableSpace ι] (h : Comparable A A' κ)
    (hA : ∀ i, (A i).det ≠ 0) {s : ℝ} (hs : 0 ≤ s) {μ : Measure (ℤ → ι)}
    (hμ : HasGibbsBounds A s μ) :
    HasGibbsBounds A' s μ := by
  obtain ⟨C, hC, hb⟩ := hμ
  have hκ : 1 ≤ κ := h.1
  refine ⟨C * κ, one_le_mul_of_one_le_of_one_le hC hκ, fun n hn w => ?_⟩
  obtain ⟨hl, hu⟩ := hb n hn w
  rw [h.pressure_eq hA hs]
  have he := Real.exp_pos (-(n * pressure A s))
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  have hκ0 : 0 < κ := lt_of_lt_of_le one_pos hκ
  have h1 := h.svf_le hs (List.ofFn w)
  have h2 := h.symm.svf_le hs (List.ofFn w)
  constructor
  · refine le_trans ?_ hl
    rw [mul_inv]
    calc C⁻¹ * κ⁻¹ * (Real.exp (-(n * pressure A s)) * svf s (word A' (List.ofFn w)))
        ≤ C⁻¹ * κ⁻¹ * (Real.exp (-(n * pressure A s)) * (κ * svf s (word A (List.ofFn w)))) := by
          gcongr
      _ = C⁻¹ * (Real.exp (-(n * pressure A s)) * svf s (word A (List.ofFn w))) := by
          field_simp
  · refine hu.trans ?_
    calc C * (Real.exp (-(n * pressure A s)) * svf s (word A (List.ofFn w)))
        ≤ C * (Real.exp (-(n * pressure A s)) * (κ * svf s (word A' (List.ofFn w)))) := by
          gcongr
      _ = C * κ * (Real.exp (-(n * pressure A s)) * svf s (word A' (List.ofFn w))) := by ring

/-- Comparable tuples have the same measures with the Gibbs bounds of `thm:irred_eq_state`. -/
theorem Comparable.hasGibbsBounds_iff [Fintype ι] [MeasurableSpace ι] (h : Comparable A A' κ)
    (hA : ∀ i, (A i).det ≠ 0) {s : ℝ} (hs : 0 ≤ s) {μ : Measure (ℤ → ι)} :
    HasGibbsBounds A' s μ ↔ HasGibbsBounds A s μ :=
  ⟨h.symm.hasGibbsBounds (h.det_ne_zero hA) hs, h.hasGibbsBounds hA hs⟩

/-- Irreducibility does not depend on the basis: a common eigenvector `u` of the `T⁻¹ A_i T`
gives the common eigenvector `T u` of the `A_i`. -/
theorem tupleIrreducible_conj_of (hT : T.det ≠ 0) (h : TupleIrreducible A) :
    TupleIrreducible (conj T A) := by
  rintro ⟨u, hu, hc⟩
  refine h ⟨T *ᵥ u, mulVec_ne_zero_of_det_ne_zero hT hu, fun i => ?_⟩
  obtain ⟨c, hci⟩ := hc i
  exact ⟨c, by rw [mulVec_conj hT, show T⁻¹ * A i * T = conj T A i from rfl, hci,
    Matrix.mulVec_smul]⟩

/-- Strong irreducibility does not depend on the basis: a finite invariant set of lines of the
`T⁻¹ A_i T` is mapped by `T` to one of the `A_i`. -/
theorem tupleStronglyIrreducible_conj_of (hT : T.det ≠ 0) (h : TupleStronglyIrreducible A) :
    TupleStronglyIrreducible (conj T A) := by
  classical
  rintro ⟨s, hne, hs0, hinv⟩
  refine h ⟨s.image (T *ᵥ ·), hne.image _, fun v hv => ?_, fun i v hv => ?_⟩
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
    exact mulVec_ne_zero_of_det_ne_zero hT (hs0 u hu)
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨w, hw, c, hc⟩ := hinv i u hu
    refine ⟨T *ᵥ w, Finset.mem_image_of_mem _ hw, c, ?_⟩
    rw [mulVec_conj hT, show T⁻¹ * A i * T = conj T A i from rfl, hc, Matrix.mulVec_smul]

/-- Proximality does not depend on the basis: `T⁻¹ A_𝐢 T` is proximal when `A_𝐢` is. -/
theorem tupleProximal_conj_of (hT : T.det ≠ 0) (h : TupleProximal A) :
    TupleProximal (conj T A) := by
  obtain ⟨w, hw, hB⟩ := h
  refine ⟨w, hw, ?_⟩
  rw [show (w.map (conj T A)).prod = word (conj T A) w from rfl, word_conj hT]
  exact hB.conj hT

/-- `𝖠` is irreducible exactly when `T⁻¹ 𝖠 T` is. -/
theorem tupleIrreducible_conj_iff (hT : T.det ≠ 0) :
    TupleIrreducible (conj T A) ↔ TupleIrreducible A :=
  ⟨fun h => conj_inv_conj hT A ▸ tupleIrreducible_conj_of (det_inv_ne_zero hT) h,
    tupleIrreducible_conj_of hT⟩

/-- `𝖠` is strongly irreducible exactly when `T⁻¹ 𝖠 T` is. -/
theorem tupleStronglyIrreducible_conj_iff (hT : T.det ≠ 0) :
    TupleStronglyIrreducible (conj T A) ↔ TupleStronglyIrreducible A :=
  ⟨fun h => conj_inv_conj hT A ▸ tupleStronglyIrreducible_conj_of (det_inv_ne_zero hT) h,
    tupleStronglyIrreducible_conj_of hT⟩

/-- `𝖠` is proximal exactly when `T⁻¹ 𝖠 T` is. -/
theorem tupleProximal_conj_iff (hT : T.det ≠ 0) : TupleProximal (conj T A) ↔ TupleProximal A :=
  ⟨fun h => conj_inv_conj hT A ▸ tupleProximal_conj_of (det_inv_ne_zero hT) h,
    tupleProximal_conj_of hT⟩

end MatrixTuple

/-! ### Planar self-affine systems in another basis -/

namespace PlanarSystem

variable {ι : Type*}

/-- The strong separation condition of `sec:box_like_self_affine` for a planar system: the sets
`φ_1(X), …, φ_N(X)` are pairwise disjoint. -/
def StrongSeparation (P : PlanarSystem ι) : Prop :=
  Pairwise fun i j => Disjoint (P.phi i '' P.attractor) (P.phi j '' P.attractor)

/-- The strong open set condition of `sec:box_like_self_affine` for a planar system: there is an
open set `U` with `U ∩ X ≠ ∅`, `⋃_i φ_i(U) ⊆ U`, and `φ_i(U) ∩ φ_j(U) = ∅` whenever `i ≠ j`. -/
def StrongOpenSet (P : PlanarSystem ι) : Prop :=
  ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (U ∩ P.attractor).Nonempty ∧ (∀ i, P.phi i '' U ⊆ U) ∧
    Pairwise fun i j => Disjoint (P.phi i '' U) (P.phi j '' U)

/-- `Q` is the system `P` in the coordinates of the basis formed by the columns of the
invertible matrix `T`: `φ^Q_i = T⁻¹ ∘ φ^P_i ∘ T`, that is `B_i = T⁻¹ A_i T` and `w_i = T⁻¹ v_i`
(tex lines 696 to 708 and 2352 to 2353). -/
structure ConjBy (T : Matrix (Fin 2) (Fin 2) ℝ) (P Q : PlanarSystem ι) : Prop where
  /-- The columns of `T` form a basis. -/
  det_ne_zero : T.det ≠ 0
  /-- The linear parts are `B_i = T⁻¹ A_i T`. -/
  mat_eq : Q.mat = MatrixTuple.conj T P.mat
  /-- The translations are `w_i = T⁻¹ v_i`. -/
  v_eq : ∀ i, Q.v i = linMap T⁻¹ (P.v i)

variable {T : Matrix (Fin 2) (Fin 2) ℝ} {P Q : PlanarSystem ι}

/-- The system `T⁻¹ ∘ φ_i ∘ T`, when its linear parts `T⁻¹ A_i T` are contractions. A basis of
unit vectors in which the matrices are diagonal or anti-diagonal has this property
(`norm_conj_le_of_isUnitBasis`). -/
noncomputable def conj (P : PlanarSystem ι) (T : Matrix (Fin 2) (Fin 2) ℝ) (hT : T.det ≠ 0)
    (hn : ∀ i, ‖T⁻¹ * P.mat i * T‖ < 1) : PlanarSystem ι where
  mat := MatrixTuple.conj T P.mat
  v i := linMap T⁻¹ (P.v i)
  det_ne_zero := MatrixTuple.det_conj_ne_zero hT P.det_ne_zero
  norm_lt_one := hn

/-- `P.conj T` is `P` in the basis `T`. -/
theorem conjBy_conj (P : PlanarSystem ι) (hT : T.det ≠ 0) (hn : ∀ i, ‖T⁻¹ * P.mat i * T‖ < 1) :
    ConjBy T P (P.conj T hT hn) :=
  ⟨hT, rfl, fun _ => rfl⟩

/-- `P` is `Q` in the basis `T⁻¹`. -/
theorem ConjBy.symm (h : ConjBy T P Q) : ConjBy T⁻¹ Q P where
  det_ne_zero := det_inv_ne_zero h.det_ne_zero
  mat_eq := by rw [h.mat_eq, MatrixTuple.conj_inv_conj h.det_ne_zero]
  v_eq i := by rw [h.v_eq, inv_inv_of_det_ne_zero h.det_ne_zero, linMap_linMap_inv h.det_ne_zero]

/-- `φ^Q_i ∘ T⁻¹ = T⁻¹ ∘ φ^P_i`. -/
theorem ConjBy.phi_linMap (h : ConjBy T P Q) (i : ι) (z : ℝ × ℝ) :
    Q.phi i (linMap T⁻¹ z) = linMap T⁻¹ (P.phi i z) := by
  have hu := isUnit_iff_ne_zero.2 h.det_ne_zero
  rw [PlanarSystem.phi, PlanarSystem.phi, h.mat_eq, h.v_eq, linMap_add]
  congr 1
  rw [toVec_linMap, MatrixTuple.conj, linMap, toVec_ofVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc (T⁻¹ * P.mat i), Matrix.mul_nonsing_inv _ hu,
    Matrix.mul_one]

/-- `φ^Q_𝐢 ∘ T⁻¹ = T⁻¹ ∘ φ^P_𝐢` for every finite word. -/
theorem ConjBy.phiWord_linMap (h : ConjBy T P Q) (w : List ι) (z : ℝ × ℝ) :
    Q.phiWord w (linMap T⁻¹ z) = linMap T⁻¹ (P.phiWord w z) := by
  induction w generalizing z with
  | nil => rfl
  | cons i w ih =>
    simp only [phiWord_cons, Function.comp_apply, ih, h.phi_linMap]

/-- `φ^Q_i(T⁻¹ E) = T⁻¹ φ^P_i(E)`. -/
theorem ConjBy.image_phi (h : ConjBy T P Q) (i : ι) (E : Set (ℝ × ℝ)) :
    Q.phi i '' (linMap T⁻¹ '' E) = linMap T⁻¹ '' (P.phi i '' E) := by
  rw [image_image, image_image]
  exact image_congr fun z _ => h.phi_linMap i z

/-- The canonical projection of `Q` is `T⁻¹ ∘ π^P`. -/
theorem ConjBy.proj_apply [Finite ι] (h : ConjBy T P Q) (x : ℤ → ι) :
    Q.proj x = linMap T⁻¹ (P.proj x) := by
  refine tendsto_nhds_unique (Q.tendsto_phiWord x) ?_
  have := ((continuous_linMap T⁻¹).tendsto _).comp (P.tendsto_phiWord x)
  refine this.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [← h.phiWord_linMap, linMap_zero]

/-- `π^Q = T⁻¹ ∘ π^P`. -/
theorem ConjBy.proj_eq [Finite ι] (h : ConjBy T P Q) : Q.proj = linMap T⁻¹ ∘ P.proj :=
  funext h.proj_apply

/-- The attractor of the system in the basis `T` is `T⁻¹(X)`. -/
theorem ConjBy.attractor_eq [Finite ι] (h : ConjBy T P Q) :
    Q.attractor = linMap T⁻¹ '' P.attractor := by
  rw [attractor, attractor, h.proj_eq, range_comp]

/-- A change of basis preserves the Hausdorff dimension of the attractor. -/
theorem ConjBy.dimH_attractor [Finite ι] (h : ConjBy T P Q) :
    dimH Q.attractor = dimH P.attractor := by
  rw [h.attractor_eq, dimH_image_linMap (det_inv_ne_zero h.det_ne_zero)]

/-- A change of basis preserves the upper Minkowski dimension of the attractor. -/
theorem ConjBy.upperBoxDim_attractor [Finite ι] (h : ConjBy T P Q) :
    upperBoxDim Q.attractor = upperBoxDim P.attractor := by
  rw [h.attractor_eq, upperBoxDim_image_linMap (det_inv_ne_zero h.det_ne_zero)]

/-- A change of basis preserves the lower Minkowski dimension of the attractor. -/
theorem ConjBy.lowerBoxDim_attractor [Finite ι] (h : ConjBy T P Q) :
    lowerBoxDim Q.attractor = lowerBoxDim P.attractor := by
  rw [h.attractor_eq, lowerBoxDim_image_linMap (det_inv_ne_zero h.det_ne_zero)]

/-- A change of basis preserves the packing dimension of the attractor. -/
theorem ConjBy.packingDim_attractor [Finite ι] (h : ConjBy T P Q) :
    packingDim Q.attractor = packingDim P.attractor := by
  rw [h.attractor_eq, packingDim_image_linMap (det_inv_ne_zero h.det_ne_zero)]

/-- The strong separation condition passes to the system in another basis. -/
theorem ConjBy.strongSeparation [Finite ι] (h : ConjBy T P Q) (hP : P.StrongSeparation) :
    Q.StrongSeparation := fun i j hij => by
  show Disjoint _ _
  rw [h.attractor_eq, h.image_phi, h.image_phi]
  exact (disjoint_image_iff (linMap_injective (det_inv_ne_zero h.det_ne_zero))).2 (hP hij)

/-- The strong open set condition passes to the system in another basis, with the open set
`T⁻¹(U)`. -/
theorem ConjBy.strongOpenSet [Finite ι] (h : ConjBy T P Q) (hP : P.StrongOpenSet) :
    Q.StrongOpenSet := by
  obtain ⟨U, hU, hne, hsub, hdisj⟩ := hP
  have hinj := linMap_injective (det_inv_ne_zero h.det_ne_zero)
  refine ⟨linMap T⁻¹ '' U, (linHomeomorph T⁻¹ (det_inv_ne_zero h.det_ne_zero)).isOpenMap U hU,
    ?_, fun i => ?_, fun i j hij => ?_⟩
  · rw [h.attractor_eq, ← image_inter hinj]
    exact hne.image _
  · rw [h.image_phi]
    exact image_mono (hsub i)
  · show Disjoint _ _
    rw [h.image_phi, h.image_phi]
    exact (disjoint_image_iff hinj).2 (hdisj hij)

/-- The strong separation condition does not depend on the basis. -/
theorem ConjBy.strongSeparation_iff [Finite ι] (h : ConjBy T P Q) :
    Q.StrongSeparation ↔ P.StrongSeparation :=
  ⟨h.symm.strongSeparation, h.strongSeparation⟩

/-- The strong open set condition does not depend on the basis. -/
theorem ConjBy.strongOpenSet_iff [Finite ι] (h : ConjBy T P Q) :
    Q.StrongOpenSet ↔ P.StrongOpenSet :=
  ⟨h.symm.strongOpenSet, h.strongOpenSet⟩

/-- Irreducibility, strong irreducibility and proximality of the linear parts do not depend on
the basis. -/
theorem ConjBy.classification_iff (h : ConjBy T P Q) :
    (TupleIrreducible Q.mat ↔ TupleIrreducible P.mat) ∧
      (TupleStronglyIrreducible Q.mat ↔ TupleStronglyIrreducible P.mat) ∧
      (TupleProximal Q.mat ↔ TupleProximal P.mat) := by
  rw [h.mat_eq]
  exact ⟨MatrixTuple.tupleIrreducible_conj_iff h.det_ne_zero,
    MatrixTuple.tupleStronglyIrreducible_conj_iff h.det_ne_zero,
    MatrixTuple.tupleProximal_conj_iff h.det_ne_zero⟩

/-- The linear parts in another basis have singular values comparable to those of `𝖠`, with the
constant `‖T⁻¹‖ ‖T‖` (tex line 2233). -/
theorem ConjBy.comparable (h : ConjBy T P Q) :
    MatrixTuple.Comparable P.mat Q.mat (condNum T) := by
  rw [h.mat_eq]
  exact MatrixTuple.comparable_conj h.det_ne_zero P.mat

/-- A change of basis preserves the pressure `P(𝖠, s)`, `s ≥ 0` (tex lines 2233 to 2234). -/
theorem ConjBy.pressure_eq [Fintype ι] (h : ConjBy T P Q) {s : ℝ} (hs : 0 ≤ s) :
    MatrixTuple.pressure Q.mat s = MatrixTuple.pressure P.mat s :=
  h.comparable.pressure_eq P.det_ne_zero hs

/-- The affinity dimension, the unique zero `s ≥ 0` of `s ↦ P(𝖠, s)` (`sec:affinity_dim`), does
not depend on the basis. -/
theorem ConjBy.pressure_eq_zero_iff [Fintype ι] (h : ConjBy T P Q) {s : ℝ} (hs : 0 ≤ s) :
    MatrixTuple.pressure Q.mat s = 0 ↔ MatrixTuple.pressure P.mat s = 0 := by
  rw [h.pressure_eq hs]

section Measures

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- A change of basis preserves the Lyapunov exponent `λ_1(𝖠, μ)` of an invariant `μ`. -/
theorem ConjBy.lyapunov₁_eq (h : ConjBy T P Q) {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) : Q.lyapunov₁ μ = P.lyapunov₁ μ :=
  h.comparable.lyapunov₁_eq P.det_ne_zero hμ

/-- A change of basis preserves the Lyapunov exponent `λ_2(𝖠, μ)` of an invariant `μ`. -/
theorem ConjBy.lyapunov₂_eq (h : ConjBy T P Q) {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) : Q.lyapunov₂ μ = P.lyapunov₂ μ :=
  h.comparable.lyapunov₂_eq P.det_ne_zero hμ

/-- A change of basis preserves the `s`-energy `Λ(𝖠, μ, s)`, `s ≥ 0`. -/
theorem ConjBy.energyLim_eq (h : ConjBy T P Q) {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (shift 1) μ μ) {s : ℝ} (hs : 0 ≤ s) :
    MatrixTuple.energyLim Q.mat s μ = MatrixTuple.energyLim P.mat s μ :=
  h.comparable.energyLim_eq P.det_ne_zero hμ hs

/-- A change of basis preserves the `s`-equilibrium states, `s ≥ 0`. -/
theorem ConjBy.isEquilibriumState_iff (h : ConjBy T P Q) {μ : Measure (ℤ → ι)}
    [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ) {s : ℝ} (hs : 0 ≤ s) :
    MatrixTuple.IsEquilibriumState Q.mat s μ ↔ MatrixTuple.IsEquilibriumState P.mat s μ :=
  h.comparable.isEquilibriumState_iff P.det_ne_zero hμ hs

omit [MeasurableSingletonClass ι] in
/-- A change of basis preserves the Gibbs bounds of `thm:irred_eq_state`, `s ≥ 0`. -/
theorem ConjBy.hasGibbsBounds_iff (h : ConjBy T P Q) {μ : Measure (ℤ → ι)} {s : ℝ}
    (hs : 0 ≤ s) :
    MatrixTuple.HasGibbsBounds Q.mat s μ ↔ MatrixTuple.HasGibbsBounds P.mat s μ :=
  h.comparable.hasGibbsBounds_iff P.det_ne_zero hs

/-- The projection of `μ` for the system in the basis `T` is `T⁻¹_*(π_*μ)`. -/
theorem ConjBy.map_proj (h : ConjBy T P Q) (μ : Measure (ℤ → ι)) :
    μ.map Q.proj = (μ.map P.proj).map (linMap T⁻¹) := by
  rw [Measure.map_map (measurable_linMap _) P.measurable_proj, h.proj_eq]

variable {μ : Measure (ℤ → ι)} [IsFiniteMeasure μ]

/-- A change of basis preserves the pointwise dimensions of the projected measure:
`dimloc(π^Q_*μ, T⁻¹ z) = dimloc(π^P_*μ, z)`. -/
theorem ConjBy.hasLocalDim_iff (h : ConjBy T P Q) (z : ℝ × ℝ) (d : ℝ) :
    HasLocalDim (μ.map Q.proj) (linMap T⁻¹ z) d ↔ HasLocalDim (μ.map P.proj) z d := by
  rw [h.map_proj]
  exact hasLocalDim_map_linMap_iff (det_inv_ne_zero h.det_ne_zero) z d

/-- `\overline{dim}_loc(π^Q_*μ, T⁻¹ z) = \overline{dim}_loc(π^P_*μ, z)`. -/
theorem ConjBy.upperLocalDim_eq (h : ConjBy T P Q) (z : ℝ × ℝ) :
    upperLocalDim (μ.map Q.proj) (linMap T⁻¹ z) = upperLocalDim (μ.map P.proj) z := by
  rw [h.map_proj]
  exact upperLocalDim_map_linMap (det_inv_ne_zero h.det_ne_zero) z

/-- `\underline{dim}_loc(π^Q_*μ, T⁻¹ z) = \underline{dim}_loc(π^P_*μ, z)`. -/
theorem ConjBy.lowerLocalDim_eq (h : ConjBy T P Q) (z : ℝ × ℝ) :
    lowerLocalDim (μ.map Q.proj) (linMap T⁻¹ z) = lowerLocalDim (μ.map P.proj) z := by
  rw [h.map_proj]
  exact lowerLocalDim_map_linMap (det_inv_ne_zero h.det_ne_zero) z

/-- A change of basis preserves exact-dimensionality of the projected measure and its
dimension. -/
theorem ConjBy.isExactDim_iff (h : ConjBy T P Q) (d : ℝ) :
    IsExactDim (μ.map Q.proj) d ↔ IsExactDim (μ.map P.proj) d := by
  rw [h.map_proj]
  exact isExactDim_map_linMap_iff (det_inv_ne_zero h.det_ne_zero) d

/-- A change of basis preserves the two values `d₁`, `d₂` of the pointwise dimension of the
projected measure. -/
theorem ConjBy.hasLocalDimPair_iff (h : ConjBy T P Q) (d₁ d₂ : ℝ) :
    HasLocalDimPair (μ.map Q.proj) d₁ d₂ ↔ HasLocalDimPair (μ.map P.proj) d₁ d₂ := by
  rw [h.map_proj]
  exact hasLocalDimPair_map_linMap_iff (det_inv_ne_zero h.det_ne_zero) d₁ d₂

/-- A change of basis preserves the upper packing dimension of the projected measure. -/
theorem ConjBy.upperPackingDim_eq (h : ConjBy T P Q) :
    upperPackingDim (μ.map Q.proj) = upperPackingDim (μ.map P.proj) := by
  rw [h.map_proj]
  exact upperPackingDim_map_linMap (det_inv_ne_zero h.det_ne_zero)

/-- A change of basis preserves the lower Hausdorff dimension of the projected measure. -/
theorem ConjBy.lowerHausdorffDim_eq (h : ConjBy T P Q) :
    lowerHausdorffDim (μ.map Q.proj) = lowerHausdorffDim (μ.map P.proj) := by
  rw [h.map_proj]
  exact lowerHausdorffDim_map_linMap (det_inv_ne_zero h.det_ne_zero)

/-- A change of basis preserves the upper Hausdorff dimension of the projected measure. -/
theorem ConjBy.upperHausdorffDim_eq (h : ConjBy T P Q) :
    upperHausdorffDim (μ.map Q.proj) = upperHausdorffDim (μ.map P.proj) := by
  rw [h.map_proj]
  exact upperHausdorffDim_map_linMap (det_inv_ne_zero h.det_ne_zero)

end Measures

end PlanarSystem

/-! ### Box-like systems as planar systems -/

namespace System

variable {ι : Type*} (S : System ι)

/-- The maps of the planar system of `S` are the maps of `S`. -/
theorem toPlanar_phi_eq (i : ι) : S.toPlanar.phi i = S.phi i := funext (S.toPlanar_phi i)

/-- The strong separation condition of a box-like system is that of its planar system. -/
theorem toPlanar_strongSeparation_iff [Finite ι] :
    S.toPlanar.StrongSeparation ↔ S.StrongSeparation := by
  simp only [PlanarSystem.StrongSeparation, StrongSeparation, toPlanar_attractor,
    toPlanar_phi_eq]

/-- The strong open set condition of a box-like system is that of its planar system. -/
theorem toPlanar_strongOpenSet_iff [Finite ι] : S.toPlanar.StrongOpenSet ↔ S.StrongOpenSet := by
  simp only [PlanarSystem.StrongOpenSet, StrongOpenSet, toPlanar_attractor, toPlanar_phi_eq]

variable {S} {T : Matrix (Fin 2) (Fin 2) ℝ} {P : PlanarSystem ι}

/-- A planar system that is a box-like system `S` in the basis `T`: the affinity dimension of
`S` is the unique zero `s ≥ 0` of the pressure `P(𝖠, s)` of the original linear parts, so the
affinity dimension does not depend on the basis (tex lines 696 to 708 and 2352 to 2353). -/
theorem pressure_dimaff_of_conjBy [Fintype ι] [Nonempty ι] (h : P.ConjBy T S.toPlanar) :
    MatrixTuple.pressure P.mat S.dimaff = 0 ∧
      ∀ s, 0 ≤ s → MatrixTuple.pressure P.mat s = 0 → s = S.dimaff := by
  have hp : ∀ s, 0 ≤ s → S.pressure s = MatrixTuple.pressure P.mat s := fun s hs => by
    rw [S.pressure_eq_tuple, ← S.toPlanar_mat]
    exact h.pressure_eq hs
  refine ⟨by rw [← hp _ S.dimaff_nonneg, S.pressure_dimaff], fun s hs hs0 => ?_⟩
  rw [← hp s hs] at hs0
  exact (S.dimaff_eq hs hs0).symm

/-- Two box-like systems related by a change of basis have the same affinity dimension. -/
theorem dimaff_eq_of_conjBy [Fintype ι] [Nonempty ι] {S' : System ι}
    (h : S'.toPlanar.ConjBy T S.toPlanar) : S.dimaff = S'.dimaff := by
  obtain ⟨h0, -⟩ := pressure_dimaff_of_conjBy (S := S) (P := S'.toPlanar) h
  have h1 : S'.pressure S.dimaff = 0 := h0
  exact (S'.dimaff_eq S.dimaff_nonneg h1).symm

end System

/-! ### Box-like coordinates in a basis of unit vectors: tex lines 696 to 698 -/

section UnitBasis

variable {ι : Type*}

/-- The columns of `T` are unit vectors forming a basis of the plane. -/
def IsUnitBasis (T : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  T.det ≠ 0 ∧ ∀ j, T 0 j ^ 2 + T 1 j ^ 2 = 1

/-- The matrices of `𝖠` are simultaneously anti-diagonal in some basis: the all-anti-diagonal
case of `sec:irreducibility` (tex lines 664 to 665), which tex line 696 sets apart. -/
def SimultaneouslyAntiDiagonal (A : ι → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ P : Matrix (Fin 2) (Fin 2) ℝ, P.det ≠ 0 ∧ ∀ i, ∃ a b : ℝ, P⁻¹ * A i * P = boxMat 1 a b

/-- The image of a unit vector has length at most `α_1(A) = ‖A‖`. -/
theorem sq_mulVec_le_norm_sq (A : Matrix (Fin 2) (Fin 2) ℝ) {u : Fin 2 → ℝ}
    (hu : u 0 ^ 2 + u 1 ^ 2 = 1) : (A *ᵥ u) 0 ^ 2 + (A *ᵥ u) 1 ^ 2 ≤ ‖A‖ ^ 2 := by
  let x : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 u
  have hx : ‖x‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [x, Fin.sum_univ_two, hu]
  have hAx : ‖toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A x‖ ≤ ‖A‖ := by
    have h := ContinuousLinearMap.le_opNorm (toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A) x
    rwa [l2_opNorm_toEuclideanCLM, hx, mul_one] at h
  have hsq : ‖toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A x‖ ^ 2 =
      (A *ᵥ u) 0 ^ 2 + (A *ᵥ u) 1 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    simp [x]
  rw [← hsq]
  exact pow_le_pow_left₀ (norm_nonneg _) hAx 2

/-- In a basis `T` of unit vectors, the non-zero entries of a diagonal or anti-diagonal matrix
`T⁻¹ A T` are at most `α_1(A) = ‖A‖` in modulus: they are the lengths of the images `A u` of the
basis vectors `u`. This is why the matrices of a contracting tuple are contracting in such a
basis (tex line 698). -/
theorem abs_le_norm_of_isUnitBasis {T A : Matrix (Fin 2) (Fin 2) ℝ} (hT : IsUnitBasis T)
    {c : ZMod 2} {a b : ℝ} (h : T⁻¹ * A * T = boxMat c a b) : |a| ≤ ‖A‖ ∧ |b| ≤ ‖A‖ := by
  have hu := isUnit_iff_ne_zero.2 hT.1
  have hAT : A * T = T * boxMat c a b := by
    rw [← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  have hcol : ∀ j : Fin 2, (A *ᵥ fun i => T i j) 0 ^ 2 + (A *ᵥ fun i => T i j) 1 ^ 2 ≤
      ‖A‖ ^ 2 := fun j => sq_mulVec_le_norm_sq A (hT.2 j)
  have hmv : ∀ i j, (A *ᵥ fun k => T k j) i = (T * boxMat c a b) i j := fun i j => by
    rw [← hAT]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two]
  have key : ∀ x : ℝ, x ^ 2 ≤ ‖A‖ ^ 2 → |x| ≤ ‖A‖ := fun x hx =>
    (sq_le_sq.1 hx).trans_eq (abs_of_nonneg (norm_nonneg A))
  have e0 := hT.2 0
  have e1 := hT.2 1
  have h0 := hcol 0
  have h1 := hcol 1
  simp only [hmv] at h0 h1
  rcases zmod_two_cases c with rfl | rfl
  · simp [Matrix.mul_apply, Fin.sum_univ_two] at h0 h1
    refine ⟨key a ?_, key b ?_⟩
    · calc a ^ 2 = (T 0 0 * a) ^ 2 + (T 1 0 * a) ^ 2 := by linear_combination (-a ^ 2) * e0
        _ ≤ ‖A‖ ^ 2 := h0
    · calc b ^ 2 = (T 0 1 * b) ^ 2 + (T 1 1 * b) ^ 2 := by linear_combination (-b ^ 2) * e1
        _ ≤ ‖A‖ ^ 2 := h1
  · simp [Matrix.mul_apply, Fin.sum_univ_two] at h0 h1
    refine ⟨key a ?_, key b ?_⟩
    · calc a ^ 2 = (T 0 0 * a) ^ 2 + (T 1 0 * a) ^ 2 := by linear_combination (-a ^ 2) * e0
        _ ≤ ‖A‖ ^ 2 := h1
    · calc b ^ 2 = (T 0 1 * b) ^ 2 + (T 1 1 * b) ^ 2 := by linear_combination (-b ^ 2) * e1
        _ ≤ ‖A‖ ^ 2 := h0

/-- In a basis of unit vectors in which `A` is diagonal or anti-diagonal, `‖T⁻¹ A T‖ ≤ ‖A‖`. -/
theorem norm_conj_le_of_isUnitBasis {T A : Matrix (Fin 2) (Fin 2) ℝ} (hT : IsUnitBasis T)
    {c : ZMod 2} {a b : ℝ} (h : T⁻¹ * A * T = boxMat c a b) : ‖T⁻¹ * A * T‖ ≤ ‖A‖ := by
  rw [h, norm_boxMat]
  exact max_le (abs_le_norm_of_isUnitBasis hT h).1 (abs_le_norm_of_isUnitBasis hT h).2

/-- A basis can be normalised to a basis of unit vectors spanning the same two lines: for every
invertible `P` there is a basis `T` of unit vectors such that every matrix that is diagonal or
anti-diagonal in the basis `P` is of the same type in the basis `T`. -/
theorem exists_isUnitBasis {P : Matrix (Fin 2) (Fin 2) ℝ} (hP : P.det ≠ 0) :
    ∃ T, IsUnitBasis T ∧ ∀ (M : Matrix (Fin 2) (Fin 2) ℝ) (c : ZMod 2) (a b : ℝ),
      P⁻¹ * M * P = boxMat c a b → ∃ a' b' : ℝ, T⁻¹ * M * T = boxMat c a' b' := by
  have hdet := Matrix.det_fin_two P
  have key : ∀ j : Fin 2, (P 0 j = 0 → P 1 j = 0 → P.det = 0) → 0 < P 0 j ^ 2 + P 1 j ^ 2 :=
    fun j hz => by
      by_contra hc
      have h0 : P 0 j = 0 := by nlinarith [sq_nonneg (P 0 j), sq_nonneg (P 1 j)]
      have h1 : P 1 j = 0 := by nlinarith [sq_nonneg (P 0 j), sq_nonneg (P 1 j)]
      exact hP (hz h0 h1)
  have hcol : ∀ j : Fin 2, 0 < P 0 j ^ 2 + P 1 j ^ 2 :=
    Fin.forall_fin_two.2 ⟨key 0 fun h0 h1 => by simp [hdet, h0, h1],
      key 1 fun h0 h1 => by simp [hdet, h0, h1]⟩
  set α := (Real.sqrt (P 0 0 ^ 2 + P 1 0 ^ 2))⁻¹ with hα
  set β := (Real.sqrt (P 0 1 ^ 2 + P 1 1 ^ 2))⁻¹ with hβ
  have hα0 : α ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 (hcol 0)).ne'
  have hβ0 : β ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 (hcol 1)).ne'
  have hDinv : (boxMat 0 α β)⁻¹ = boxMat 0 α⁻¹ β⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [boxMat_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hα0, hβ0]
  refine ⟨P * boxMat 0 α β, ⟨?_, fun j => ?_⟩, fun M c a b hM => ?_⟩
  · rw [Matrix.det_mul, boxMat_zero, Matrix.det_fin_two_of]
    simpa using ⟨hP, hα0, hβ0⟩
  · have hs : ∀ x : ℝ, 0 < x → (x.sqrt)⁻¹ ^ 2 * x = 1 := fun x hx => by
      rw [inv_pow, Real.sq_sqrt hx.le, inv_mul_cancel₀ hx.ne']
    have hα2 : α ^ 2 * (P 0 0 ^ 2 + P 1 0 ^ 2) = 1 := by rw [hα]; exact hs _ (hcol 0)
    have hβ2 : β ^ 2 * (P 0 1 ^ 2 + P 1 1 ^ 2) = 1 := by rw [hβ]; exact hs _ (hcol 1)
    have hT0 : ∀ i, (P * boxMat 0 α β) i 0 = P i 0 * α := fun i => by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hT1 : ∀ i, (P * boxMat 0 α β) i 1 = P i 1 * β := fun i => by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases j
    · show (P * boxMat 0 α β) 0 0 ^ 2 + (P * boxMat 0 α β) 1 0 ^ 2 = 1
      rw [hT0, hT0]
      linear_combination hα2
    · show (P * boxMat 0 α β) 0 1 ^ 2 + (P * boxMat 0 α β) 1 1 ^ 2 = 1
      rw [hT1, hT1]
      linear_combination hβ2
  · have e : (P * boxMat 0 α β)⁻¹ * M * (P * boxMat 0 α β) =
        boxMat 0 α⁻¹ β⁻¹ * (P⁻¹ * M * P) * boxMat 0 α β := by
      rw [Matrix.mul_inv_rev, hDinv]
      simp only [Matrix.mul_assoc]
    rw [e, hM, boxMat_mul, boxMat_mul, zero_add, add_zero]
    exact ⟨_, _, rfl⟩

/-- A proximal matrix that is diagonal or anti-diagonal is diagonal with diagonal entries of
distinct moduli. -/
theorem boxMat_of_isProximalMatrix {c : ZMod 2} {a b : ℝ}
    (h : IsProximalMatrix (boxMat c a b)) : c = 0 ∧ |a| ≠ |b| := by
  rcases zmod_two_cases c with rfl | rfl
  · exact ⟨rfl, isProximalMatrix_boxMat_zero.1 h⟩
  · exact absurd h (not_isProximalMatrix_boxMat_one _ _)

/-- A matrix `R` conjugating a diagonal matrix with distinct diagonal entries to a diagonal
matrix is diagonal or anti-diagonal: it maps the eigenlines, the coordinate axes, to the
coordinate axes. -/
theorem exists_eq_boxMat_of_conj_diag {R : Matrix (Fin 2) (Fin 2) ℝ} (hR : R.det ≠ 0)
    {μ₁ μ₂ ν₁ ν₂ : ℝ} (hμ : μ₁ ≠ μ₂) (h : R⁻¹ * boxMat 0 μ₁ μ₂ * R = boxMat 0 ν₁ ν₂) :
    ∃ (c : ZMod 2) (r₁ r₂ : ℝ), R = boxMat c r₁ r₂ := by
  have hu := isUnit_iff_ne_zero.2 hR
  have hMR : boxMat 0 μ₁ μ₂ * R = R * boxMat 0 ν₁ ν₂ := by
    rw [← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
      Matrix.one_mul]
  have e : ∀ i j, (boxMat 0 μ₁ μ₂ * R) i j = (R * boxMat 0 ν₁ ν₂) i j := fun i j => by rw [hMR]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have hd : R 0 0 * R 1 1 - R 0 1 * R 1 0 ≠ 0 := by rwa [← Matrix.det_fin_two]
  have cancel : ∀ {x y z : ℝ}, z ≠ 0 → x * z = z * y → x = y := fun hz hxy =>
    mul_right_cancel₀ hz (hxy.trans (mul_comm _ _))
  by_cases h00 : R 0 0 = 0
  · have h01 : R 0 1 ≠ 0 := fun h' => hd (by rw [h00, h']; ring)
    have h10 : R 1 0 ≠ 0 := fun h' => hd (by rw [h00, h']; ring)
    have a1 := cancel h01 e01
    have a2 := cancel h10 e10
    have h11 : R 1 1 = 0 := by
      by_contra h11
      exact hμ (by rw [a1, cancel h11 e11])
    refine ⟨1, R 0 1, R 1 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h11]
  · have a0 := cancel h00 e00
    have h10 : R 1 0 = 0 := by
      by_contra h10
      exact hμ (by rw [a0, cancel h10 e10])
    have h01 : R 0 1 = 0 := by
      by_contra h01
      have h11 : R 1 1 ≠ 0 := fun h' => hd (by rw [h10, h']; ring)
      exact hμ (by rw [cancel h01 e01, cancel h11 e11])
    refine ⟨0, R 0 0, R 1 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10]

/-- For a proximal tuple of invertible matrices the type of each matrix in a basis in which all
the matrices are diagonal or anti-diagonal does not depend on the basis. The two bases differ by
a matrix that maps the eigenlines of a proximal product to themselves, hence by a diagonal or
anti-diagonal matrix, and conjugation by such a matrix preserves the type. -/
theorem boxType_eq_of_conj {A : ι → Matrix (Fin 2) (Fin 2) ℝ} (hdet : ∀ i, (A i).det ≠ 0)
    (hprox : TupleProximal A) {P Q : Matrix (Fin 2) (Fin 2) ℝ} (hP : P.det ≠ 0)
    (hQ : Q.det ≠ 0) (hPbox : ∀ i, ∃ (c : ZMod 2) (a b : ℝ), P⁻¹ * A i * P = boxMat c a b)
    (hQbox : ∀ i, ∃ (c : ZMod 2) (a b : ℝ), Q⁻¹ * A i * Q = boxMat c a b) {i : ι}
    {c c' : ZMod 2} {a b a' b' : ℝ} (h1 : P⁻¹ * A i * P = boxMat c a b)
    (h2 : Q⁻¹ * A i * Q = boxMat c' a' b') : c = c' := by
  have huP := isUnit_iff_ne_zero.2 hP
  obtain ⟨R, hRdef⟩ : ∃ R, R = P⁻¹ * Q := ⟨_, rfl⟩
  have hR : R.det ≠ 0 := by
    rw [hRdef, Matrix.det_mul]
    exact mul_ne_zero (det_inv_ne_zero hP) hQ
  have hconj : ∀ M, R⁻¹ * (P⁻¹ * M * P) * R = Q⁻¹ * M * Q := fun M => by
    rw [hRdef, Matrix.mul_inv_rev, inv_inv_of_det_ne_zero hP]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P P⁻¹ (M * (P * (P⁻¹ * Q))), Matrix.mul_nonsing_inv _ huP,
      Matrix.one_mul, ← Matrix.mul_assoc P P⁻¹ Q, Matrix.mul_nonsing_inv _ huP, Matrix.one_mul]
  obtain ⟨w, -, hB⟩ := hprox
  obtain ⟨cP, μ₁, μ₂, hPw⟩ := exists_list_prod_eq_boxMat hPbox w
  obtain ⟨cQ, ν₁, ν₂, hQw⟩ := exists_list_prod_eq_boxMat hQbox w
  rw [← conj_list_prod hP] at hPw
  rw [← conj_list_prod hQ] at hQw
  obtain ⟨hcP, hμ⟩ := boxMat_of_isProximalMatrix (hPw ▸ hB.conj hP)
  obtain ⟨hcQ, -⟩ := boxMat_of_isProximalMatrix (hQw ▸ hB.conj hQ)
  have hμ' : μ₁ ≠ μ₂ := fun he => hμ (by rw [he])
  have hRw := hconj (w.map A).prod
  rw [hPw, hQw, hcP, hcQ] at hRw
  obtain ⟨cR, r₁, r₂, hRe⟩ := exists_eq_boxMat_of_conj_diag hR hμ' hRw
  have huR := isUnit_iff_ne_zero.2 hR
  have hi := hconj (A i)
  rw [h1, h2] at hi
  have hmul : boxMat c a b * R = R * boxMat c' a' b' := by
    rw [← hi, ← Matrix.mul_assoc R (R⁻¹ * boxMat c a b) R,
      ← Matrix.mul_assoc R R⁻¹ (boxMat c a b), Matrix.mul_nonsing_inv _ huR, Matrix.one_mul]
  have hab : a ≠ 0 ∧ b ≠ 0 := by
    have hd := det_inv_mul_mul hP (A i)
    rw [h1] at hd
    have hd' : (boxMat c a b).det ≠ 0 := hd ▸ hdet i
    have habs := abs_det_boxMat c a b
    have hne : |a| * |b| ≠ 0 := by rw [← habs]; exact abs_ne_zero.2 hd'
    exact ⟨fun h0 => hne (by rw [h0]; simp), fun h0 => hne (by rw [h0]; simp)⟩
  have hr : r₁ ≠ 0 ∧ r₂ ≠ 0 := by
    have habs := abs_det_boxMat cR r₁ r₂
    rw [← hRe] at habs
    have hne : |r₁| * |r₂| ≠ 0 := by rw [← habs]; exact abs_ne_zero.2 hR
    exact ⟨fun h0 => hne (by rw [h0]; simp), fun h0 => hne (by rw [h0]; simp)⟩
  rw [hRe, boxMat_mul, boxMat_mul] at hmul
  have hfirst : a * (if c = 0 then r₁ else r₂) ≠ 0 := by
    refine mul_ne_zero hab.1 ?_
    split_ifs
    exacts [hr.1, hr.2]
  have htype := boxMat_type_eq hfirst hmul
  calc c = c + cR - cR := by ring
    _ = cR + c' - cR := by rw [htype]
    _ = c' := by ring

/-- The direction `⇐` of tex lines 696 to 698: a proximal tuple of invertible matrices that is
box-like with rotations in some basis is irreducible, not strongly irreducible, and not
simultaneously anti-diagonal in any basis. -/
theorem irreducible_of_conj_isBoxLikeWithRotations {A : ι → Matrix (Fin 2) (Fin 2) ℝ}
    (hdet : ∀ i, (A i).det ≠ 0) (hprox : TupleProximal A) {T : Matrix (Fin 2) (Fin 2) ℝ}
    (hT : T.det ≠ 0) (h : IsBoxLikeWithRotations (MatrixTuple.conj T A)) :
    TupleIrreducible A ∧ ¬ TupleStronglyIrreducible A ∧ ¬ SimultaneouslyAntiDiagonal A := by
  obtain ⟨hbox, ⟨j, aj, bj, hj⟩, ⟨k, ak, bk, hk⟩⟩ := (box_like_sa _).1 h
  have hTbox : ∀ i, ∃ (c : ZMod 2) (a b : ℝ), T⁻¹ * A i * T = boxMat c a b := fun i => by
    obtain ⟨c, a, b, -, -, -, -, he⟩ := hbox i
    exact ⟨c, a, b, he⟩
  have hsbl : SimultaneouslyBoxLike A := ⟨T, hT, hTbox, k, ak, bk, hk⟩
  obtain ⟨hirr, hnsi⟩ := (simultaneouslyBoxLike_iff hdet hprox).1 hsbl
  refine ⟨hirr, hnsi, ?_⟩
  rintro ⟨Q, hQ, hQanti⟩
  obtain ⟨a', b', hQj⟩ := hQanti j
  have := boxType_eq_of_conj hdet hprox hT hQ hTbox
    (fun i => by obtain ⟨a, b, he⟩ := hQanti i; exact ⟨1, a, b, he⟩) hj hQj
  exact absurd this (by decide)

/-- The direction `⇒` of tex lines 696 to 698: a proximal tuple of invertible contracting
matrices that is irreducible, not strongly irreducible, and not simultaneously anti-diagonal in
any basis, is box-like with rotations in a basis of unit vectors. By `thm:A_classification` it
is simultaneously diagonal or anti-diagonal in some basis with an anti-diagonal matrix; a
diagonal matrix occurs since the tuple is not simultaneously anti-diagonal; normalising the basis
vectors keeps the types and makes the entries contracting (`abs_le_norm_of_isUnitBasis`). -/
theorem exists_isUnitBasis_isBoxLikeWithRotations {A : ι → Matrix (Fin 2) (Fin 2) ℝ}
    (hdet : ∀ i, (A i).det ≠ 0) (hnorm : ∀ i, ‖A i‖ < 1) (hprox : TupleProximal A)
    (hirr : TupleIrreducible A) (hnsi : ¬ TupleStronglyIrreducible A)
    (hanti : ¬ SimultaneouslyAntiDiagonal A) :
    ∃ T, IsUnitBasis T ∧ IsBoxLikeWithRotations (MatrixTuple.conj T A) := by
  obtain ⟨P, hP, hPbox, k, ak, bk, hk⟩ := simultaneouslyBoxLike_of_proximal hdet hprox hirr hnsi
  obtain ⟨T, hT, hTP⟩ := exists_isUnitBasis hP
  have hdiag : ∃ j, ∃ a b : ℝ, P⁻¹ * A j * P = boxMat 0 a b := by
    by_contra hcon
    push Not at hcon
    refine hanti ⟨P, hP, fun i => ?_⟩
    obtain ⟨c, a, b, he⟩ := hPbox i
    rcases zmod_two_cases c with rfl | rfl
    · exact absurd he (hcon i a b)
    · exact ⟨a, b, he⟩
  obtain ⟨j, aj, bj, hj⟩ := hdiag
  refine ⟨T, hT, (box_like_sa_of_contracting (MatrixTuple.det_conj_ne_zero hT.1 hdet)
    (fun i => ?_)).2 ⟨fun i => ?_, ?_, ?_⟩⟩
  · obtain ⟨c, a, b, he⟩ := hPbox i
    obtain ⟨a', b', he'⟩ := hTP (A i) c a b he
    exact (norm_conj_le_of_isUnitBasis hT he').trans_lt (hnorm i)
  · obtain ⟨c, a, b, he⟩ := hPbox i
    obtain ⟨a', b', he'⟩ := hTP (A i) c a b he
    exact ⟨c, a', b', he'⟩
  · obtain ⟨a', b', he'⟩ := hTP (A j) 0 aj bj hj
    exact ⟨j, a', b', he'⟩
  · obtain ⟨a', b', he'⟩ := hTP (A k) 1 ak bk hk
    exact ⟨k, a', b', he'⟩

/-- Tex lines 777 to 779: apart from the all-anti-diagonal case, a proximal tuple
`𝖠 ∈ GL_2(ℝ)^N` of contracting matrices is irreducible but not strongly irreducible if and only
if `𝖠` is box-like with rotations in a basis of unit vectors. -/
theorem irreducible_not_stronglyIrreducible_iff_unitBasis {A : ι → Matrix (Fin 2) (Fin 2) ℝ}
    (hdet : ∀ i, (A i).det ≠ 0) (hnorm : ∀ i, ‖A i‖ < 1) (hprox : TupleProximal A) :
    (TupleIrreducible A ∧ ¬ TupleStronglyIrreducible A ∧ ¬ SimultaneouslyAntiDiagonal A) ↔
      ∃ T, IsUnitBasis T ∧ IsBoxLikeWithRotations (MatrixTuple.conj T A) :=
  ⟨fun ⟨hirr, hnsi, hanti⟩ =>
    exists_isUnitBasis_isBoxLikeWithRotations hdet hnorm hprox hirr hnsi hanti,
    fun ⟨_, hT, h⟩ => irreducible_of_conj_isBoxLikeWithRotations hdet hprox hT.1 h⟩

/-- Tex lines 777 to 789 for a planar self-affine set: if the tuple of `X` is proximal,
irreducible, not strongly irreducible and not simultaneously anti-diagonal, then in a basis `T`
of unit vectors the system is a box-like system `S` with rotations; its attractor is `T⁻¹(X)`,
and `S` or its second iterate has a proximal diagonal generator (`thm:box_like_proximal`). -/
theorem PlanarSystem.exists_system_of_irreducible [Finite ι] (P : PlanarSystem ι)
    (hprox : TupleProximal P.mat) (hirr : TupleIrreducible P.mat)
    (hnsi : ¬ TupleStronglyIrreducible P.mat) (hanti : ¬ SimultaneouslyAntiDiagonal P.mat) :
    ∃ T, IsUnitBasis T ∧ ∃ S : System ι, S.WithRotations ∧ P.ConjBy T S.toPlanar ∧
      S.attractor = linMap T⁻¹ '' P.attractor ∧
      (S.HasProximalDiagonal ∨ S.sq.HasProximalDiagonal) := by
  obtain ⟨T, hT, hbox⟩ :=
    exists_isUnitBasis_isBoxLikeWithRotations P.det_ne_zero P.norm_lt_one hprox hirr hnsi hanti
  have hn : ∀ i, ‖T⁻¹ * P.mat i * T‖ < 1 := fun i => by
    obtain ⟨hb, -, -⟩ := (BoxLike.box_like_sa _).1 hbox
    obtain ⟨c, a, b, -, -, -, -, he⟩ := hb i
    exact (norm_conj_le_of_isUnitBasis hT he).trans_lt (P.norm_lt_one i)
  have hQ := P.conjBy_conj hT.1 hn
  obtain ⟨S, hS, hSQ⟩ := (P.conj T hT.1 hn).isBoxLikeWithRotations_iff_exists_system.1 hbox
  rw [← hSQ] at hQ
  have hSprox : S.Proximal := by
    rw [System.proximal_iff_tupleProximal, ← S.toPlanar_mat]
    exact hQ.classification_iff.2.2.2 hprox
  refine ⟨T, hT, S, hS, hQ, ?_, hSprox.hasProximalDiagonal_or_sq⟩
  rw [← S.toPlanar_attractor, hQ.attractor_eq]

end UnitBasis

end BoxLike
