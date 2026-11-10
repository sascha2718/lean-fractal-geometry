module

/-
Rapaport's Theorem 1.2 in the plane for a homogeneous diagonal system `T` (`System.IsHomDiag`)
with `|b| < |a|` and the Bernoulli measure `ν = bernoulli (weightMeasure p)` with arbitrary positive
weights `p`, assuming the core theorem `HomogeneousCore`. This is the glue `Rapaport/Glue.lean` with
the equal weights `1 / #κ` replaced by `p`, together with the parts of
`BoxLike/MainTwoProse/DiagonalSubsystem.lean`, `BoxLike/MainTwoProse/SubsystemEntropies.lean`,
`BoxLike/MainTwoProse/ScalarFeng.lean` and
`BoxLike/MainTwoProse/Endpoint.lean` that the library states for `uniformBernoulli` only. Write
`μ = π_*ν`, `H = ∑_k -p_k log p_k`, `χ₁ = -log |a|`, `χ₂ = -log |b|` and `q = q_n` for the
conditional entropy of the first symbol given the planar point.

* `isFiniteMeasure_bernoulli`: every Bernoulli measure is finite, so that the conditional
  entropies of `ν` are defined without an instance argument for the weights.
* `bernoulli_weightMeasure_cylinder_single`, `measureReal_bernoulli_weightMeasure_cylinder_single`,
  `measureReal_bernoulli_weightMeasure_cylinder_prod`, `entropy_bernoulli_weightMeasure`: the
  cylinder measures of `ν` and its entropy `H`.
* `toHomSystemW`: `T` as a `HomSystem` with the weights `p`; its fields, `toHomSystemW_H`,
  `toHomSystemW_χ₁`, `toHomSystemW_χ₂`, `φ_eq`, `φWord_eq`, `point_eq`: its maps and points are
  those of `IsHomDiag.toHomSystem`, which do not depend on the weights.
* `isInvariant_map_proj`, `bddSupp_map_proj`: `μ` is the self-affine measure of `toHomSystemW`
  and has bounded support.
* `map_fst_eq_marginal`, `map_snd_eq_marginal`, `marginal_eq_sum_weighted`,
  `marginal_isExactDim_weighted`: the coordinate projections of `μ` are self-similar measures
  with the weights `p`, of dimension `min{1, H / χ_c}` by Kittle–Kogler.
* `isExactDim_map_fst`, `isExactDim_map_snd`: the projections have dimension `1` when `χ_c ≤ H`.
* `xSep_of_axisExpSeparation`: exponential separation of the first axis is Rapaport's `XSep`.
* `dimEntropy_zero`, `dimEntropy_one_eq_condEntropyCoord`,
  `condEntropy_xiPerp_eq_condEntropyCoord`, `dimEntropy_two_eq_condEntropyPoint`: the entropies
  `h_0 = H`, `h_1 = q_x`, `h_2 = q` of the planar Ledrappier–Young formula.
* `dimEntropy_one_lineSystem`, `dimEntropy_one_eq_scalar`, `condEntropy_xiPerp_eq_scalar`,
  `condEntropyCoord_zero_eq_scalar`, `condEntropyCoord_one_eq_scalar`: the scalar
  Ledrappier–Young formula `q_c = H - χ_c min{1, H / χ_c}`.
* `condEntropyCoord_one_eq_zero_of_le`, `condEntropyPoint_eq_zero_of_le_weighted`,
  `isExactDim_map_proj_subsystemDim`: for `H ≤ χ₂` (or under strong separation) `q = 0` and
  `dim μ = subsystemDim H χ₁ χ₂`.
* `isExactDim_map_proj_eq`, `condEntropyPoint_nonneg`, `condEntropyPoint_le`, `dim_le`: for
  `χ₁ ≤ H`, `dim μ = 1 + (H - χ₁ - q) / χ₂` with `0 ≤ q ≤ H - χ₁`.
* `isExactDim_map_proj_weighted`, `le_dimH_attractor_weighted`: `dim μ = min{2, dim_L}` with
  `dim_L = lyapDim H (log |a|) (log |b|)`, hence `dim_H X ≥ min{2, dim_L}`, from
  `HomogeneousCore`, `FengLedrappierYoung` and `KittleKoglerDimension`;
  `isExactDim_map_proj_weighted_of_library`, `le_dimH_attractor_weighted_of_library` with the
  library proofs of the last two.
-/
public import BoxLike.Rapaport.Glue
public import BoxLike.MainTwoProse.PastIndependence
public import BoxLike.MainTwoProse.ScalarFeng

@[expose] public section

namespace BoxLike.Rapaport.Weighted

open MeasureTheory Filter Set

universe u

/-! ### Bernoulli measures with arbitrary weights -/

section Bernoulli

/-- Every Bernoulli measure is finite: it is a probability measure when the one-symbol
distribution is one, and the zero measure otherwise (the convention of
`Measure.infinitePi`). The conditional entropies of `bernoulli (weightMeasure p)` are thereby
defined without an instance argument for the weights. -/
instance isFiniteMeasure_bernoulli {ι : Type*} [MeasurableSpace ι] (p : Measure ι) :
    IsFiniteMeasure (bernoulli p) := by
  by_cases h : IsProbabilityMeasure p
  · infer_instance
  · have h0 : bernoulli p = 0 := by
      rw [bernoulli, Measure.infinitePi, dite_eq_right fun h' => h (h' 0)]
    rw [h0]
    infer_instance

variable {κ : Type*} [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ] {p : κ → ℝ}

/-- The cylinder `[k]` of one symbol has the measure `p_k` under `bernoulli (weightMeasure p)`
(`measureReal_uniformBernoulli_cylinder_single` for arbitrary weights). -/
theorem measureReal_bernoulli_weightMeasure_cylinder_single (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1) (k : κ) : (bernoulli (weightMeasure p)).real (cylinder ![k]) = p k := by
  have := isProbabilityMeasure_weightMeasure (fun k => (hp k).le) hp1
  rw [measureReal_bernoulli_cylinder, Fin.prod_univ_one, Matrix.cons_val_zero,
    measureReal_weightMeasure_singleton (hp k).le]

/-- The cylinder `[k]` of one symbol has the measure `p_k`, in `ℝ≥0∞`
(`uniformBernoulli_cylinder_single` for arbitrary weights). -/
theorem bernoulli_weightMeasure_cylinder_single (hp : ∀ k, 0 < p k) (hp1 : ∑ k, p k = 1)
    (k : κ) : bernoulli (weightMeasure p) (cylinder ![k]) = ENNReal.ofReal (p k) := by
  rw [← ofReal_measureReal, measureReal_bernoulli_weightMeasure_cylinder_single hp hp1]

/-- The cylinder measures of `bernoulli (weightMeasure p)` are products of the one-symbol
measures (`measureReal_uniformBernoulli_cylinder_prod` for arbitrary weights). -/
theorem measureReal_bernoulli_weightMeasure_cylinder_prod (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1) {n : ℕ} (w : Fin n → κ) :
    (bernoulli (weightMeasure p)).real (cylinder w) =
      ∏ k, (bernoulli (weightMeasure p)).real (cylinder ![w k]) := by
  have := isProbabilityMeasure_weightMeasure (fun k => (hp k).le) hp1
  rw [measureReal_bernoulli_cylinder]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [measureReal_bernoulli_weightMeasure_cylinder_single hp hp1,
    measureReal_weightMeasure_singleton (hp _).le]

/-- The entropy of `bernoulli (weightMeasure p)` is `H = ∑_k -p_k log p_k`
(`entropy_uniformBernoulli` for arbitrary weights, from `entropy_bernoulli`). -/
theorem entropy_bernoulli_weightMeasure (hp : ∀ k, 0 < p k) (hp1 : ∑ k, p k = 1) :
    entropy (bernoulli (weightMeasure p)) = ∑ k, Real.negMulLog (p k) := by
  have := isProbabilityMeasure_weightMeasure (fun k => (hp k).le) hp1
  rw [entropy_bernoulli]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [measureReal_weightMeasure_singleton (hp k).le]

end Bernoulli

/-! ### The homogeneous system with the weights `p` -/

section Hom

variable {κ : Type u} [Fintype κ] [Nonempty κ] {T : System κ} {a b : ℝ}
  (hT : T.IsHomDiag a b) (hab : |b| < |a|) {p : κ → ℝ} (hp : ∀ k, 0 < p k)
  (hp1 : ∑ k, p k = 1)
include hT

/-- The homogeneous diagonal system `T` with `|b| < |a|` as a `HomSystem` with the weights `p`
(`IsHomDiag.toHomSystem` for arbitrary weights): the common linear part `diag(a, b)` and the
translations `v_k` of `T`. -/
noncomputable def toHomSystemW : HomSystem κ where
  r₁ := a
  r₂ := b
  v := T.v
  p := p
  r₂_ne_zero := hT.b_ne_zero
  abs_r₂_lt := hab
  abs_r₁_lt_one := hT.abs_a_lt_one
  p_pos := hp
  p_sum := hp1

/-- The horizontal contraction of `toHomSystemW` is `a`. -/
@[simp] theorem toHomSystemW_r₁ : (toHomSystemW hT hab hp hp1).r₁ = a := rfl

/-- The vertical contraction of `toHomSystemW` is `b`. -/
@[simp] theorem toHomSystemW_r₂ : (toHomSystemW hT hab hp hp1).r₂ = b := rfl

/-- The translations of `toHomSystemW` are those of `T`. -/
@[simp] theorem toHomSystemW_v : (toHomSystemW hT hab hp hp1).v = T.v := rfl

/-- The weights of `toHomSystemW` are `p`. -/
@[simp] theorem toHomSystemW_p : (toHomSystemW hT hab hp hp1).p = p := rfl

/-- The entropy of `toHomSystemW` is `H = ∑_k -p_k log p_k`. -/
theorem toHomSystemW_H : (toHomSystemW hT hab hp hp1).H = ∑ k, Real.negMulLog (p k) := rfl

/-- The first exponent of `toHomSystemW` is `χ₁ = -log |a|`. -/
theorem toHomSystemW_χ₁ : (toHomSystemW hT hab hp hp1).χ₁ = -Real.log |a| := rfl

/-- The second exponent of `toHomSystemW` is `χ₂ = -log |b|`. -/
theorem toHomSystemW_χ₂ : (toHomSystemW hT hab hp hp1).χ₂ = -Real.log |b| := rfl

/-- The maps of `toHomSystemW` are the maps `φ_k` of `T` (`IsHomDiag.φ_eq`). -/
theorem φ_eq (k : κ) : (toHomSystemW hT hab hp hp1).φ k = T.phi k :=
  IsHomDiag.φ_eq hT hab k

/-- The compositions `φ_u` of `toHomSystemW` are those of `IsHomDiag.toHomSystem`: they do not
depend on the weights. -/
theorem φWord_eq (n : ℕ) (u : Fin n → κ) :
    (toHomSystemW hT hab hp hp1).φWord n u = (IsHomDiag.toHomSystem hT hab).φWord n u := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [HomSystem.φWord, HomSystem.φWord, ih]
    rfl

/-- The points `φ_u(0)` of `toHomSystemW` are those of `IsHomDiag.toHomSystem`. -/
theorem point_eq {n : ℕ} (u : Fin n → κ) :
    (toHomSystemW hT hab hp hp1).point u = (IsHomDiag.toHomSystem hT hab).point u := by
  rw [HomSystem.point, HomSystem.point, φWord_eq]

/-- Exponential separation of the system induced on the first axis is Rapaport's `XSep` for
`toHomSystemW` (Definition 1.1 of the source), from `IsHomDiag.xSep_of_axisExpSeparation`,
since the points `φ_u(0)` do not depend on the weights. -/
theorem xSep_of_axisExpSeparation (h0 : T.AxisExpSeparation 0) :
    (toHomSystemW hT hab hp hp1).XSep := by
  obtain ⟨c, hc, hfr⟩ := IsHomDiag.xSep_of_axisExpSeparation hT hab h0
  refine ⟨c, hc, hfr.mono fun n hn u u' huu' => ?_⟩
  rw [point_eq, point_eq]
  exact hn u u' huu'

end Hom

/-! ### The projected Bernoulli measure -/

section Measure

variable {κ : Type u} [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
  {T : System κ} {a b : ℝ} {p : κ → ℝ}

/-- `μ = π_*ν` has bounded support: it is carried by the compact attractor `X = π(Σ)`
(`IsHomDiag.bddSupp_map_proj` for arbitrary weights). -/
theorem bddSupp_map_proj : BddSupp ((bernoulli (weightMeasure p)).map T.proj) := by
  obtain ⟨r, M, hS⟩ := T.exists_bounds
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ × ℝ)).1 T.isCompact_attractor.isBounded
  refine ⟨0, R, ?_⟩
  refine (ae_map_mem_range T.isCompact_attractor.isClosed.measurableSet
    hS.measurable_proj.aemeasurable).mono fun z hz => ?_
  have := hR hz
  rwa [Metric.mem_closedBall, dist_eq_norm] at this

omit [MeasurableSingletonClass κ] in
/-- The horizontal projection of `μ` is the marginal `ν_x` of `sec:dimension_of_projections`. -/
theorem map_fst_eq_marginal :
    ((bernoulli (weightMeasure p)).map T.proj).map Prod.fst =
      T.marginal 0 (bernoulli (weightMeasure p)) := rfl

omit [MeasurableSingletonClass κ] in
/-- The vertical projection of `μ` is the marginal `ν_y` of `sec:dimension_of_projections`. -/
theorem map_snd_eq_marginal :
    ((bernoulli (weightMeasure p)).map T.proj).map Prod.snd =
      T.marginal 1 (bernoulli (weightMeasure p)) := rfl

/-- `q ≥ 0`: the conditional entropy of the first symbol given the planar point is
non-negative. -/
theorem condEntropyPoint_nonneg : 0 ≤ T.condEntropyPoint (bernoulli (weightMeasure p)) :=
  condEntropy_nonneg _ _

variable (hT : T.IsHomDiag a b)
include hT

/-- `μ = π_*ν` is the self-affine measure of `toHomSystemW`: Hutchinson's equation
`μ = ∑_k p_k (φ_k)_*μ`, from the invariance of the projection of a Bernoulli measure
(`IsHomDiag.isInvariant_map_proj` for arbitrary weights). -/
theorem isInvariant_map_proj [Nonempty κ] (hab : |b| < |a|) (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1) :
    (toHomSystemW hT hab hp hp1).IsInvariant ((bernoulli (weightMeasure p)).map T.proj) := by
  have := isProbabilityMeasure_weightMeasure (fun k => (hp k).le) hp1
  have hinv := T.isInvariantMeasure_map_proj (measurePreserving_shift_bernoulli _ 1)
    fun n w => measureReal_bernoulli_weightMeasure_cylinder_prod hp hp1 w
  unfold System.IsInvariantMeasure at hinv
  refine hinv.trans (Finset.sum_congr rfl fun k _ => ?_)
  dsimp only
  rw [bernoulli_weightMeasure_cylinder_single hp hp1, φ_eq]
  rfl

/-- Each coordinate marginal of `ν` is the self-similar measure of the coordinate maps
`g_{(k, c)}` with the weights `p` (`IsHomDiag.marginal_eq_sum` for arbitrary weights): the
stationarity equation, from the invariance of the projection of a Bernoulli measure and
`eq:phi_def_by_g`. -/
theorem marginal_eq_sum_weighted (hp : ∀ k, 0 < p k) (hp1 : ∑ k, p k = 1) (c : ZMod 2) :
    T.marginal c (bernoulli (weightMeasure p)) =
      ∑ k : κ, ENNReal.ofReal (p k) •
        (T.marginal c (bernoulli (weightMeasure p))).map
          (fun x => T.ratio (k, c) * x + T.trans (k, c)) := by
  have := isProbabilityMeasure_weightMeasure (fun k => (hp k).le) hp1
  have hc : Measurable (System.coord c) := by
    unfold System.coord
    split_ifs
    · exact measurable_fst
    · exact measurable_snd
  have hphi : ∀ i, Measurable (T.phi i) := fun i => (T.continuous_phi i).measurable
  have hg : ∀ k : κ, Measurable fun x : ℝ => T.ratio (k, c) * x + T.trans (k, c) :=
    fun k => (measurable_id.const_mul _).add_const _
  have hinv := T.isInvariantMeasure_map_proj (measurePreserving_shift_bernoulli _ 1)
    fun n w => measureReal_bernoulli_weightMeasure_cylinder_prod hp hp1 w
  unfold System.IsInvariantMeasure at hinv
  refine Measure.ext fun B hB => ?_
  have key : ∀ k : κ, T.phi k ⁻¹' (System.coord c ⁻¹' B) =
      System.coord c ⁻¹' ((fun x => T.ratio (k, c) * x + T.trans (k, c)) ⁻¹' B) := by
    intro k
    ext z
    simp only [Set.mem_preimage, System.coord_phi, hT.o_eq, add_zero, System.g]
  calc T.marginal c (bernoulli (weightMeasure p)) B
      = (bernoulli (weightMeasure p)).map T.proj (System.coord c ⁻¹' B) := by
        rw [System.marginal, Measure.map_apply hc hB]
    _ = ∑ i, bernoulli (weightMeasure p) (cylinder ![i]) *
          (bernoulli (weightMeasure p)).map T.proj (T.phi i ⁻¹' (System.coord c ⁻¹' B)) := by
        conv_lhs => rw [hinv]
        rw [Measure.finsetSum_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (hphi i) (hc hB)]
    _ = ∑ k : κ, ENNReal.ofReal (p k) *
          (bernoulli (weightMeasure p)).map T.proj
            (System.coord c ⁻¹' ((fun x => T.ratio (k, c) * x + T.trans (k, c)) ⁻¹' B)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [bernoulli_weightMeasure_cylinder_single hp hp1, key]
    _ = (∑ k : κ, ENNReal.ofReal (p k) •
          (T.marginal c (bernoulli (weightMeasure p))).map
            (fun x => T.ratio (k, c) * x + T.trans (k, c))) B := by
        rw [Measure.finsetSum_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (hg k) hB, System.marginal,
          Measure.map_apply hc (hg k hB)]

/-- The dimension of a coordinate marginal of `ν` (`IsHomDiag.marginal_isExactDim` for
arbitrary weights): the marginal is the self-similar measure with the weights `p` on the maps
`g_{(k, c)}`, all with the ratio `a` for `c = 0` and `b` for `c = 1`; without exact overlaps
Kittle–Kogler give `dim = min{1, H / χ_c}`.
Depends on: `KittleKoglerDimension`. -/
theorem marginal_isExactDim_weighted [Nonempty κ] (hkk : KittleKoglerDimension.{u})
    (hp : ∀ k, 0 < p k) (hp1 : ∑ k, p k = 1) (c : ZMod 2)
    (hfree : Function.Injective
      (simWord (fun _ : κ => if c = 0 then a else b) (fun k => T.trans (k, c)))) :
    IsExactDim (T.marginal c (bernoulli (weightMeasure p)))
      (min 1 ((∑ k, Real.negMulLog (p k)) / -Real.log |if c = 0 then a else b|)) := by
  have hr0 : (if c = 0 then a else b) ≠ 0 := by
    split_ifs
    exacts [hT.a_ne_zero, hT.b_ne_zero]
  have hr1 : |if c = 0 then a else b| < 1 := by
    split_ifs
    exacts [hT.abs_a_lt_one, hT.abs_b_lt_one]
  have := isProbabilityMeasure_weightMeasure (fun k => (hp k).le) hp1
  have : IsProbabilityMeasure (T.marginal c (bernoulli (weightMeasure p))) := by
    unfold System.marginal
    infer_instance
  have hstat := marginal_eq_sum_weighted hT hp hp1 c
  simp only [hT.ratio_eq] at hstat
  have key := hkk (fun _ : κ => if c = 0 then a else b) (fun k => T.trans (k, c)) p
    (fun _ => hr0) (fun _ => hr1) hp hp1 hfree (T.marginal c (bernoulli (weightMeasure p))) hstat
  have h2 : ∑ k, p k * Real.log |if c = 0 then a else b| = Real.log |if c = 0 then a else b| := by
    rw [← Finset.sum_mul, hp1, one_mul]
  simpa only [h2] using key

/-- The horizontal projection of `μ` has dimension `min{1, H / χ₁} = 1` when `χ₁ ≤ H`
(`IsHomDiag.isExactDim_map_fst` for arbitrary weights), a hypothesis of the core theorem.
Depends on: `KittleKoglerDimension`. -/
theorem isExactDim_map_fst [Nonempty κ] (hkk : KittleKoglerDimension.{u}) (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1) (h0 : T.AxisExpSeparation 0)
    (hH : -Real.log |a| ≤ ∑ k, Real.negMulLog (p k)) :
    IsExactDim (((bernoulli (weightMeasure p)).map T.proj).map Prod.fst) 1 := by
  have hχ : 0 < -Real.log |a| := neg_pos.2 hT.log_abs_a_neg
  have h := marginal_isExactDim_weighted hT hkk hp hp1 0
    (IsHomDiag.simWord_injective_of_axisExpSeparation hT 0 h0)
  simp only [ite_true] at h
  rwa [min_eq_left ((one_le_div hχ).2 hH)] at h

/-- The vertical projection of `μ` has dimension `min{1, H / χ₂} = 1` when `χ₂ ≤ H`
(`IsHomDiag.isExactDim_map_snd` for arbitrary weights), a hypothesis of the core theorem.
Depends on: `KittleKoglerDimension`. -/
theorem isExactDim_map_snd [Nonempty κ] (hkk : KittleKoglerDimension.{u}) (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1) (h1 : T.AxisExpSeparation 1)
    (hH : -Real.log |b| ≤ ∑ k, Real.negMulLog (p k)) :
    IsExactDim (((bernoulli (weightMeasure p)).map T.proj).map Prod.snd) 1 := by
  have hχ : 0 < -Real.log |b| := neg_pos.2 hT.log_abs_b_neg
  have h := marginal_isExactDim_weighted hT hkk hp hp1 1
    (IsHomDiag.simWord_injective_of_axisExpSeparation hT 1 h1)
  simp only [one_ne_zero, ite_false] at h
  rwa [min_eq_left ((one_le_div hχ).2 hH)] at h

/-! ### The entropies of the planar Ledrappier–Young formula -/

/-- `h_0(ν) = H` (`System.IsHomDiag.dimEntropy_zero` for arbitrary weights): the entropy of the
Bernoulli measure, by `dimEntropy_zero_eq_entropy'` and `entropy_bernoulli`. -/
theorem dimEntropy_zero (hab : |b| ≤ |a|) (hp : ∀ k, 0 < p k) (hp1 : ∑ k, p k = 1) :
    T.dimEntropy (bernoulli (weightMeasure p)) 0 = ∑ k, Real.negMulLog (p k) := by
  have := isProbabilityMeasure_weightMeasure (fun k => (hp k).le) hp1
  have hinv := measurePreserving_shift_bernoulli (weightMeasure p) 1
  rw [T.dimEntropy_zero_eq_entropy' _ hinv
    (by rw [hT.sigmaPrime_eq_univ hab hinv, Set.compl_univ, measure_empty]),
    entropy_bernoulli_weightMeasure hp hp1]

/-- `h_1(ν) = q_x` (`System.IsHomDiag.dimEntropy_one_eq_condEntropyCoord` for arbitrary
weights): the atom of `ξ_1` fixes the past and the horizontal coordinate, and the past of a
Bernoulli measure is independent of its future (`condEntropy_samePast_eq_of_future`). -/
theorem dimEntropy_one_eq_condEntropyCoord (hab : |b| ≤ |a|) (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1) :
    T.dimEntropy (bernoulli (weightMeasure p)) 1 =
      T.condEntropyCoord (bernoulli (weightMeasure p)) 0 := by
  have := isProbabilityMeasure_weightMeasure (fun k => (hp k).le) hp1
  have hinv := measurePreserving_shift_bernoulli (weightMeasure p) 1
  unfold System.dimEntropy System.condEntropyCoord
  rw [show T.xi (bernoulli (weightMeasure p)) 1 =
      fun x => {y | SamePast y x ∧ System.coord 0 (T.proj y) = System.coord 0 (T.proj x)} from
    funext (hT.xi_one_eq hab hinv)]
  exact condEntropy_samePast_eq_of_future (weightMeasure p) (T.measurable_coord_proj 0)
    fun x y h => by rw [T.proj_congr h]

/-- `H(𝒫 | \widehat{ξ_1^⊥}) = q_y` (`System.IsHomDiag.condEntropy_xiPerp_eq_condEntropyCoord`
for arbitrary weights): the atom of `ξ_1^⊥` fixes the past and the vertical coordinate, and the
past is independent of the future. -/
theorem condEntropy_xiPerp_eq_condEntropyCoord (hab : |b| ≤ |a|) (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1) :
    condEntropy (bernoulli (weightMeasure p)) (T.xiPerp (bernoulli (weightMeasure p))) =
      T.condEntropyCoord (bernoulli (weightMeasure p)) 1 := by
  have := isProbabilityMeasure_weightMeasure (fun k => (hp k).le) hp1
  have hinv := measurePreserving_shift_bernoulli (weightMeasure p) 1
  unfold System.condEntropyCoord
  rw [show T.xiPerp (bernoulli (weightMeasure p)) =
      fun x => {y | SamePast y x ∧ System.coord 1 (T.proj y) = System.coord 1 (T.proj x)} from
    funext (hT.xiPerp_eq hab hinv)]
  exact condEntropy_samePast_eq_of_future (weightMeasure p) (T.measurable_coord_proj 1)
    fun x y h => by rw [T.proj_congr h]

/-- `h_2(ν) = q` (`System.IsHomDiag.dimEntropy_two_eq_condEntropyPoint` for arbitrary
weights): the atom of `ξ_2` fixes the past and the planar point, and the past is independent of
the future. -/
theorem dimEntropy_two_eq_condEntropyPoint (hab : |b| ≤ |a|) (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1) :
    T.dimEntropy (bernoulli (weightMeasure p)) 2 =
      T.condEntropyPoint (bernoulli (weightMeasure p)) := by
  have := isProbabilityMeasure_weightMeasure (fun k => (hp k).le) hp1
  have hinv := measurePreserving_shift_bernoulli (weightMeasure p) 1
  obtain ⟨r, M, hS⟩ := T.exists_bounds
  unfold System.dimEntropy System.condEntropyPoint
  rw [show T.xi (bernoulli (weightMeasure p)) 2 =
      fun x => {y | SamePast y x ∧ T.proj y = T.proj x} from
    funext (hT.xi_two_eq hab hinv)]
  exact condEntropy_samePast_eq_of_future (weightMeasure p) hS.measurable_proj
    fun x y h => T.proj_congr h

/-! ### The scalar Ledrappier–Young formula -/

/-- The scalar Ledrappier–Young formula `q_c = H - χ_c min{1, H / χ_c}` for the coordinate `c`
(`System.IsHomDiag.dimEntropy_one_lineSystem` for arbitrary weights): the planar formula
`thm:feng1` for the line system of the coordinate `c`, whose partitions `ξ_2` and `ξ_1` agree,
and Kittle–Kogler for the same measure on the horizontal axis.
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem dimEntropy_one_lineSystem [Nonempty κ] (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (hp : ∀ k, 0 < p k) (hp1 : ∑ k, p k = 1) (c : ZMod 2)
    (hfree : Function.Injective
      (simWord (fun _ : κ => if c = 0 then a else b) (fun k => T.trans (k, c)))) :
    (T.lineSystem c).dimEntropy (bernoulli (weightMeasure p)) 1 =
      (∑ k, Real.negMulLog (p k)) - -Real.log |if c = 0 then a else b| *
        min 1 ((∑ k, Real.negMulLog (p k)) / -Real.log |if c = 0 then a else b|) := by
  have hL := hT.lineSystem c
  set r := if c = 0 then a else b with hr_def
  have hr0 : r ≠ 0 := by
    rw [hr_def]
    split_ifs
    exacts [hT.a_ne_zero, hT.b_ne_zero]
  have hr1 : |r| < 1 := by
    rw [hr_def]
    split_ifs
    exacts [hT.abs_a_lt_one, hT.abs_b_lt_one]
  have hlr : Real.log |r| < 0 := Real.log_neg (abs_pos.2 hr0) hr1
  have hrr : |r / 2| < |r| := by
    rw [abs_div, abs_two]
    linarith [abs_pos.2 hr0]
  have := isProbabilityMeasure_weightMeasure (fun k => (hp k).le) hp1
  have hinv := measurePreserving_shift_bernoulli (weightMeasure p) 1
  have hLY := hly (T.lineSystem c) (bernoulli (weightMeasure p)) hinv
    (ergodic_shift_bernoulli _) (hL.lyapunov₂_lt_lyapunov₁ hrr hinv)
  have h2 : (T.lineSystem c).dimEntropy (bernoulli (weightMeasure p)) 2 =
      (T.lineSystem c).dimEntropy (bernoulli (weightMeasure p)) 1 := by
    unfold System.dimEntropy
    rw [hT.xi_two_lineSystem c hinv]
  rw [h2, sub_self, zero_div, add_zero, dimEntropy_zero hL hrr.le hp hp1,
    hL.lyapunov₁_eq hrr.le hinv, hT.map_proj_lineSystem] at hLY
  have hKK := isExactDim_map_prodMk_zero (marginal_isExactDim_weighted hT hkk hp hp1 c hfree)
  have : IsProbabilityMeasure ((T.marginal c (bernoulli (weightMeasure p))).map
      fun t : ℝ => (t, (0 : ℝ))) := by
    unfold System.marginal
    infer_instance
  have heq := IsExactDim.unique (IsProbabilityMeasure.ne_zero _) hLY hKK
  rw [div_eq_iff hlr.ne] at heq
  linarith

/-- `q_x = h_1(ν) = H - χ₁ min{1, H / χ₁}` (`System.IsHomDiag.dimEntropy_one_eq_scalar` for
arbitrary weights): the scalar Ledrappier–Young formula for the horizontal coordinate.
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem dimEntropy_one_eq_scalar [Nonempty κ] (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (hab : |b| ≤ |a|) (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1)
    (hfreex : Function.Injective (simWord (fun _ : κ => a) (fun k => T.trans (k, 0)))) :
    T.dimEntropy (bernoulli (weightMeasure p)) 1 =
      (∑ k, Real.negMulLog (p k)) - -Real.log |a| *
        min 1 ((∑ k, Real.negMulLog (p k)) / -Real.log |a|) := by
  have := isProbabilityMeasure_weightMeasure (fun k => (hp k).le) hp1
  have h := dimEntropy_one_lineSystem hT hly hkk hp hp1 0 (by simpa using hfreex)
  unfold System.dimEntropy at h ⊢
  rw [hT.xi_one_eq_lineSystem hab (measurePreserving_shift_bernoulli _ 1)]
  exact h

/-- `q_y = H(𝒫 | \widehat{ξ_1^⊥}) = H - χ₂ min{1, H / χ₂}`
(`System.IsHomDiag.condEntropy_xiPerp_eq_scalar` for arbitrary weights): the scalar
Ledrappier–Young formula for the vertical coordinate.
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem condEntropy_xiPerp_eq_scalar [Nonempty κ] (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (hab : |b| ≤ |a|) (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1)
    (hfreey : Function.Injective (simWord (fun _ : κ => b) (fun k => T.trans (k, 1)))) :
    condEntropy (bernoulli (weightMeasure p)) (T.xiPerp (bernoulli (weightMeasure p))) =
      (∑ k, Real.negMulLog (p k)) - -Real.log |b| *
        min 1 ((∑ k, Real.negMulLog (p k)) / -Real.log |b|) := by
  have := isProbabilityMeasure_weightMeasure (fun k => (hp k).le) hp1
  have h := dimEntropy_one_lineSystem hT hly hkk hp hp1 1 (by simpa using hfreey)
  unfold System.dimEntropy at h
  rw [hT.xiPerp_eq_lineSystem hab (measurePreserving_shift_bernoulli _ 1)]
  exact h

/-- The scalar Ledrappier–Young formula `q_x = H - χ₁ min{1, H / χ₁}`
(`System.IsHomDiag.condEntropyCoord_zero_eq_scalar` for arbitrary weights).
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem condEntropyCoord_zero_eq_scalar [Nonempty κ] (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (hab : |b| ≤ |a|) (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1)
    (hfreex : Function.Injective (simWord (fun _ : κ => a) (fun k => T.trans (k, 0)))) :
    T.condEntropyCoord (bernoulli (weightMeasure p)) 0 =
      (∑ k, Real.negMulLog (p k)) - -Real.log |a| *
        min 1 ((∑ k, Real.negMulLog (p k)) / -Real.log |a|) := by
  rw [← dimEntropy_one_eq_condEntropyCoord hT hab hp hp1]
  exact dimEntropy_one_eq_scalar hT hly hkk hab hp hp1 hfreex

/-- The scalar Ledrappier–Young formula `q_y = H - χ₂ min{1, H / χ₂}`
(`System.IsHomDiag.condEntropyCoord_one_eq_scalar` for arbitrary weights).
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem condEntropyCoord_one_eq_scalar [Nonempty κ] (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (hab : |b| ≤ |a|) (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1)
    (hfreey : Function.Injective (simWord (fun _ : κ => b) (fun k => T.trans (k, 1)))) :
    T.condEntropyCoord (bernoulli (weightMeasure p)) 1 =
      (∑ k, Real.negMulLog (p k)) - -Real.log |b| *
        min 1 ((∑ k, Real.negMulLog (p k)) / -Real.log |b|) := by
  rw [← condEntropy_xiPerp_eq_condEntropyCoord hT hab hp hp1]
  exact condEntropy_xiPerp_eq_scalar hT hly hkk hab hp hp1 hfreey

/-! ### The case `H ≤ χ₂` -/

/-- `q_y = 0` when `H ≤ χ₂` (`System.IsHomDiag.condEntropyCoord_one_eq_zero_of_le` for
arbitrary weights).
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem condEntropyCoord_one_eq_zero_of_le [Nonempty κ] (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (hab : |b| ≤ |a|) (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1)
    (hfreey : Function.Injective (simWord (fun _ : κ => b) (fun k => T.trans (k, 1))))
    (hH : ∑ k, Real.negMulLog (p k) ≤ -Real.log |b|) :
    T.condEntropyCoord (bernoulli (weightMeasure p)) 1 = 0 := by
  have hlb : 0 < -Real.log |b| := neg_pos.2 hT.log_abs_b_neg
  rw [condEntropyCoord_one_eq_scalar hT hly hkk hab hp hp1 hfreey,
    min_eq_right ((div_le_one hlb).2 hH), mul_div_cancel₀ _ hlb.ne', sub_self]

/-- The entropy threshold case: if `H ≤ χ₂`, then `0 ≤ q ≤ q_y = 0`
(`System.IsHomDiag.condEntropyPoint_eq_zero_of_le` for arbitrary weights).
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem condEntropyPoint_eq_zero_of_le_weighted [Nonempty κ] (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (hab : |b| ≤ |a|) (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1)
    (hfreey : Function.Injective (simWord (fun _ : κ => b) (fun k => T.trans (k, 1))))
    (hH : ∑ k, Real.negMulLog (p k) ≤ -Real.log |b|) :
    T.condEntropyPoint (bernoulli (weightMeasure p)) = 0 := by
  have := isProbabilityMeasure_weightMeasure (fun k => (hp k).le) hp1
  refine le_antisymm ?_ (condEntropy_nonneg _ _)
  calc T.condEntropyPoint (bernoulli (weightMeasure p))
      ≤ T.condEntropyCoord (bernoulli (weightMeasure p)) 1 :=
        T.condEntropyPoint_le_condEntropyCoord _ 1
    _ = 0 := condEntropyCoord_one_eq_zero_of_le hT hly hkk hab hp hp1 hfreey hH

/-- The dimension of `μ` when `q = 0`, that is, when `H ≤ χ₂` or under strong separation
(`System.IsHomDiag.isExactDim_map_proj` for arbitrary weights):
`dim μ = (H - q_x) / χ₁ + q_x / χ₂ = subsystemDim H χ₁ χ₂`.
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem isExactDim_map_proj_subsystemDim [Nonempty κ] (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (hab : |b| < |a|) (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1)
    (hfreex : Function.Injective (simWord (fun _ : κ => a) (fun k => T.trans (k, 0))))
    (hfreey : Function.Injective (simWord (fun _ : κ => b) (fun k => T.trans (k, 1))))
    (hzero : ∑ k, Real.negMulLog (p k) ≤ -Real.log |b| ∨ T.StrongSeparation) :
    IsExactDim ((bernoulli (weightMeasure p)).map T.proj)
      (subsystemDim (∑ k, Real.negMulLog (p k)) (-Real.log |a|) (-Real.log |b|)) := by
  have := isProbabilityMeasure_weightMeasure (fun k => (hp k).le) hp1
  have hinv := measurePreserving_shift_bernoulli (weightMeasure p) 1
  have hq : T.condEntropyPoint (bernoulli (weightMeasure p)) = 0 := by
    rcases hzero with hH | hsep
    · exact condEntropyPoint_eq_zero_of_le_weighted hT hly hkk hab.le hp hp1 hfreey hH
    · exact hsep.condEntropyPoint_eq_zero _
  have hLY := hly T (bernoulli (weightMeasure p)) hinv (ergodic_shift_bernoulli _)
    (hT.lyapunov₂_lt_lyapunov₁ hab hinv)
  rw [dimEntropy_zero hT hab.le hp hp1, dimEntropy_one_eq_condEntropyCoord hT hab.le hp hp1,
    dimEntropy_two_eq_condEntropyPoint hT hab.le hp hp1,
    condEntropyCoord_zero_eq_scalar hT hly hkk hab.le hp hp1 hfreex, hq,
    hT.lyapunov₁_eq hab.le hinv, hT.lyapunov₂_eq hab.le hinv] at hLY
  rw [subsystemDim_eq_ledrappierYoung hT.log_abs_a_neg.ne hT.log_abs_b_neg.ne]
  exact hLY

/-! ### The Ledrappier–Young value for `χ₁ ≤ H` -/

/-- The planar Ledrappier–Young formula `thm:feng1` for `ν` when `χ₁ ≤ H`
(`IsHomDiag.isExactDim_map_proj_eq` for arbitrary weights): with `h_0 = H`,
`h_1 = q_x = H - χ₁` and `h_2 = q`, `dim μ = 1 + (H - χ₁ - q) / χ₂`.
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem isExactDim_map_proj_eq [Nonempty κ] (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (hab : |b| < |a|) (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1)
    (hfreex : Function.Injective (simWord (fun _ : κ => a) (fun k => T.trans (k, 0))))
    (hH : -Real.log |a| ≤ ∑ k, Real.negMulLog (p k)) :
    IsExactDim ((bernoulli (weightMeasure p)).map T.proj)
      (1 + ((∑ k, Real.negMulLog (p k)) - -Real.log |a| -
        T.condEntropyPoint (bernoulli (weightMeasure p))) / -Real.log |b|) := by
  have := isProbabilityMeasure_weightMeasure (fun k => (hp k).le) hp1
  have hinv := measurePreserving_shift_bernoulli (weightMeasure p) 1
  have hχ : 0 < -Real.log |a| := neg_pos.2 hT.log_abs_a_neg
  have hla := hT.log_abs_a_neg.ne
  have hlb := hT.log_abs_b_neg.ne
  have hLY := hly T (bernoulli (weightMeasure p)) hinv (ergodic_shift_bernoulli _)
    (hT.lyapunov₂_lt_lyapunov₁ hab hinv)
  rw [dimEntropy_zero hT hab.le hp hp1, dimEntropy_one_eq_condEntropyCoord hT hab.le hp hp1,
    dimEntropy_two_eq_condEntropyPoint hT hab.le hp hp1,
    condEntropyCoord_zero_eq_scalar hT hly hkk hab.le hp hp1 hfreex,
    hT.lyapunov₁_eq hab.le hinv, hT.lyapunov₂_eq hab.le hinv,
    min_eq_left ((one_le_div hχ).2 hH)] at hLY
  convert hLY using 1
  field_simp
  ring

/-- `q ≤ q_x = H - χ₁` when `χ₁ ≤ H` (`IsHomDiag.condEntropyPoint_le` for arbitrary weights):
conditioning on the planar point gives at least as much information as conditioning on its
first coordinate, and the scalar Ledrappier–Young formula.
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem condEntropyPoint_le [Nonempty κ] (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (hab : |b| < |a|) (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1)
    (hfreex : Function.Injective (simWord (fun _ : κ => a) (fun k => T.trans (k, 0))))
    (hH : -Real.log |a| ≤ ∑ k, Real.negMulLog (p k)) :
    T.condEntropyPoint (bernoulli (weightMeasure p)) ≤
      (∑ k, Real.negMulLog (p k)) - -Real.log |a| := by
  have := isProbabilityMeasure_weightMeasure (fun k => (hp k).le) hp1
  have hχ : 0 < -Real.log |a| := neg_pos.2 hT.log_abs_a_neg
  have h := T.condEntropyPoint_le_condEntropyCoord (bernoulli (weightMeasure p)) 0
  rwa [condEntropyCoord_zero_eq_scalar hT hly hkk hab.le hp hp1 hfreex,
    min_eq_left ((one_le_div hχ).2 hH), mul_one] at h

/-- The exact dimension `α` of `μ` satisfies `α ≤ 1 + (H - χ₁) / χ₂` when `χ₁ ≤ H`, since
`q ≥ 0` (`IsHomDiag.dim_le` for arbitrary weights).
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem dim_le [Nonempty κ] (hly : FengLedrappierYoung.{u}) (hkk : KittleKoglerDimension.{u})
    (hab : |b| < |a|) (hp : ∀ k, 0 < p k) (hp1 : ∑ k, p k = 1)
    (hfreex : Function.Injective (simWord (fun _ : κ => a) (fun k => T.trans (k, 0))))
    (hH : -Real.log |a| ≤ ∑ k, Real.negMulLog (p k)) {α : ℝ}
    (hα : IsExactDim ((bernoulli (weightMeasure p)).map T.proj) α) :
    α ≤ 1 + ((∑ k, Real.negMulLog (p k)) - -Real.log |a|) / -Real.log |b| := by
  have := isProbabilityMeasure_weightMeasure (fun k => (hp k).le) hp1
  have hχ₂ : 0 < -Real.log |b| := neg_pos.2 hT.log_abs_b_neg
  rw [hα.unique (IsProbabilityMeasure.ne_zero _)
    (isExactDim_map_proj_eq hT hly hkk hab hp hp1 hfreex hH)]
  have hq : 0 ≤ T.condEntropyPoint (bernoulli (weightMeasure p)) := condEntropyPoint_nonneg
  have := div_le_div_of_nonneg_right
    (show (∑ k, Real.negMulLog (p k)) - -Real.log |a| -
        T.condEntropyPoint (bernoulli (weightMeasure p)) ≤
      (∑ k, Real.negMulLog (p k)) - -Real.log |a| by linarith) hχ₂.le
  linarith

end Measure

/-! ### The dimension of the projected Bernoulli measure -/

section Main

variable {κ : Type u} [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ] [Nonempty κ]
  {T : System κ} {a b : ℝ} {p : κ → ℝ}

/-- Rapaport's Theorem 1.2 in the plane for the self-affine measure `μ = π_*ν` of a homogeneous
diagonal system with `|b| < |a|`, exponentially separated induced systems on both axes and the
weights `p`, assuming the core theorem: `μ` is exact-dimensional of dimension
`min{2, dim_L(H, log |a|, log |b|)}`. For `H ≤ χ₂` this is `isExactDim_map_proj_subsystemDim`.
For `H > χ₂` both projections of `μ` have dimension `1`, `dim μ = α ≤ 1 + (H - χ₁) / χ₂`, and
the core theorem for `toHomSystemW` gives `α = 1 + (H - χ₁) / χ₂` unless `α = 2`; in both cases
`α = min{2, dim_L}` (the argument of `IsHomDiag.dimH_attractor_eq`).
Depends on: `HomogeneousCore`, `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem isExactDim_map_proj_weighted (hcore : HomogeneousCore.{u})
    (hly : FengLedrappierYoung.{u}) (hkk : KittleKoglerDimension.{u}) (hT : T.IsHomDiag a b)
    (hab : |b| < |a|) (hp : ∀ k, 0 < p k) (hp1 : ∑ k, p k = 1) (h0 : T.AxisExpSeparation 0)
    (h1 : T.AxisExpSeparation 1) :
    IsExactDim ((bernoulli (weightMeasure p)).map T.proj)
      (min 2 (lyapDim (∑ k, Real.negMulLog (p k)) (Real.log |a|) (Real.log |b|))) := by
  have := isProbabilityMeasure_weightMeasure (fun k => (hp k).le) hp1
  have hne : (bernoulli (weightMeasure p)).map T.proj ≠ 0 := IsProbabilityMeasure.ne_zero _
  have hfreex := IsHomDiag.simWord_injective_zero hT h0
  have hfreey := IsHomDiag.simWord_injective_one hT h1
  have hla := hT.log_abs_a_neg
  have hlt : Real.log |b| < Real.log |a| := Real.log_lt_log (abs_pos.2 hT.b_ne_zero) hab
  rcases le_or_gt (∑ k, Real.negMulLog (p k)) (-Real.log |b|) with hH | hH
  · -- `H ≤ χ₂`: the Ledrappier–Young formula with `q = 0`
    have hH2 : ∑ k, Real.negMulLog (p k) ≤ -Real.log |a| - Real.log |b| := by linarith
    have hd := isExactDim_map_proj_subsystemDim hT hly hkk hab hp hp1 hfreex hfreey (Or.inl hH)
    rw [subsystemDim_eq_lyapDim hlt hla hH2] at hd
    rwa [min_eq_right (hd.dim_mem_Icc_two hne).2]
  · -- `H > χ₂`: the core theorem
    have hH1 : -Real.log |a| ≤ ∑ k, Real.negMulLog (p k) := by linarith
    have hα := isExactDim_map_proj_eq hT hly hkk hab hp hp1 hfreex hH1
    rw [min_two_lyapDim_eq hlt hla hH]
    have hα2 := (hα.dim_mem_Icc_two hne).2
    have hβ := dim_le hT hly hkk hab hp hp1 hfreex hH1 hα
    rcases hα2.lt_or_eq with hlt2 | heq2
    · have key := hcore (toHomSystemW hT hab hp hp1) _ (isInvariant_map_proj hT hab hp hp1)
        (bddSupp_map_proj (T := T)) _ hα hlt2 (isExactDim_map_fst hT hkk hp hp1 h0 hH1)
        (isExactDim_map_snd hT hkk hp hp1 h1 hH.le) (xSep_of_axisExpSeparation hT hab hp hp1 h0)
      rw [toHomSystemW_H, toHomSystemW_χ₁, toHomSystemW_χ₂] at key
      rw [← key, min_eq_right hlt2.le]
      exact hα
    · rw [heq2] at hβ hα
      rwa [min_eq_left hβ]

/-- The lower bound `dim_H X ≥ min{2, dim_L(H, log |a|, log |b|)}` for a homogeneous diagonal
system with `|b| < |a|`, exponentially separated induced systems on both axes and the weights
`p`, assuming the core theorem: `dim μ ≤ dim_H X` (`System.le_dimH_attractor`), since `μ` is
carried by `X`.
Depends on: `HomogeneousCore`, `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem le_dimH_attractor_weighted (hcore : HomogeneousCore.{u})
    (hly : FengLedrappierYoung.{u}) (hkk : KittleKoglerDimension.{u}) (hT : T.IsHomDiag a b)
    (hab : |b| < |a|) (hp : ∀ k, 0 < p k) (hp1 : ∑ k, p k = 1) (h0 : T.AxisExpSeparation 0)
    (h1 : T.AxisExpSeparation 1) :
    ENNReal.ofReal (min 2 (lyapDim (∑ k, Real.negMulLog (p k)) (Real.log |a|) (Real.log |b|))) ≤
      dimH T.attractor := by
  have := isProbabilityMeasure_weightMeasure (fun k => (hp k).le) hp1
  exact T.le_dimH_attractor (isExactDim_map_proj_weighted hcore hly hkk hT hab hp hp1 h0 h1)

/-- `isExactDim_map_proj_weighted` with the library proofs `fengLedrappierYoung_holds` and
`kittleKoglerDimension_holds`: only the core theorem remains.
Depends on: `HomogeneousCore`. -/
theorem isExactDim_map_proj_weighted_of_library (hcore : HomogeneousCore.{u})
    (hT : T.IsHomDiag a b) (hab : |b| < |a|) (hp : ∀ k, 0 < p k) (hp1 : ∑ k, p k = 1)
    (h0 : T.AxisExpSeparation 0) (h1 : T.AxisExpSeparation 1) :
    IsExactDim ((bernoulli (weightMeasure p)).map T.proj)
      (min 2 (lyapDim (∑ k, Real.negMulLog (p k)) (Real.log |a|) (Real.log |b|))) :=
  isExactDim_map_proj_weighted hcore fengLedrappierYoung_holds kittleKoglerDimension_holds hT
    hab hp hp1 h0 h1

/-- `le_dimH_attractor_weighted` with the library proofs `fengLedrappierYoung_holds` and
`kittleKoglerDimension_holds`: only the core theorem remains.
Depends on: `HomogeneousCore`. -/
theorem le_dimH_attractor_weighted_of_library (hcore : HomogeneousCore.{u})
    (hT : T.IsHomDiag a b) (hab : |b| < |a|) (hp : ∀ k, 0 < p k) (hp1 : ∑ k, p k = 1)
    (h0 : T.AxisExpSeparation 0) (h1 : T.AxisExpSeparation 1) :
    ENNReal.ofReal (min 2 (lyapDim (∑ k, Real.negMulLog (p k)) (Real.log |a|) (Real.log |b|))) ≤
      dimH T.attractor :=
  le_dimH_attractor_weighted hcore fengLedrappierYoung_holds kittleKoglerDimension_holds hT hab
    hp hp1 h0 h1

end Main

end BoxLike.Rapaport.Weighted
