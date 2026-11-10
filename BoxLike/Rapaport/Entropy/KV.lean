module

/-
The Kaimanovich–Vershik inequality for the non-conformal partitions `ℰ_n` of the plane:
Corollary 5.2 of Rapaport (arXiv:2309.03985v1, lines 1380 to 1429 of the source) for `d = 2`.

Fix `n` and the dyadic levels `i = lvl χ₁ n`, `j = lvl χ₂ n` of `ℰ_n = χ.E n`. The lattice
`Γ = 2^{-i} ℤ × 2^{-j} ℤ` of lines 1390 to 1395 meets every cell of `ℰ_n` in exactly one point,
its lower-left corner (lines 1395 to 1397), and `ξ = χ.latticeMap n` sends a point to the
lattice point of its cell (lines 1397 to 1398). The discretised law `ξα` is the image of the
law `χ.dlaw n α` of the labels of `ℰ_n` under the additive embedding
`latticeHom i j : ℤ × ℤ →+ ℝ × ℝ`, so convolutions of discretised laws are images of discrete
convolutions on `ℤ × ℤ`, and the vendored Kaimanovich–Vershik bound
`iteratedEntropy_le_first_increment` (Rapaport's Lemma 5.1, lines 1371 to 1378) applies. The
comparison (5.3) of lines 1400 to 1421 is proved by a coupling: `θ^{∗k} ∗ σ` and
`(ξθ)^{∗k} ∗ ξσ` are the marginals of the convolution of `k + 1` couplings of a measure with its
discretisation, which is carried by pairs at most `k + 1` meshes apart in each coordinate; the
perturbation count (2.7) then bounds the difference of the entropies by `2 log (2k + 5)`.

* The lattice: `latticePt`, `latticeHom`, `latticeHom_apply`, `coe_latticeHom`,
  `rect_latticePt`, `rect_comp_latticePt`, `measurable_latticePt`,
  `abs_sub_dyadicQuantize_div_le`, `Exps.latticeMap`, `Exps.latticeMap_apply`,
  `Exps.measurable_latticeMap`, `Exps.E_latticeMap`, `Exps.E_comp_latticeMap`,
  `Exps.abs_sub_latticeMap_le`.
* Discretised laws: `Exps.dlaw`, `Exps.dlaw_support_finite`, `Exps.dlaw_toMeasure`,
  `Exps.map_latticeMap_eq`, `Exps.finiteLabels_map_latticeMap`, `Exps.ent_map_latticeMap`,
  `Exps.ent_eq_finiteEntropy_dlaw`, `ent_map_latticePt`, `finiteLabels_map_latticePt`,
  `map_latticePt_conv`, `convPow_map_latticePt_conv`.
* The comparison (5.3): `Exps.abs_ent_convPow_conv_sub_le`.
* Corollary 5.2: `Exps.kv_E_explicit` (error `2 k log 7 + 2 log (2k + 5)`), `Exps.kv_E`
  (error `6 (k + 1) log (k + 2)`) and its normalised form `Exps.kv_E_div`.
-/
public import BoxLike.Rapaport.Entropy.Basic
public import BoxLike.Rapaport.Entropy.Rect
public import ExactOverlaps.Entropy.RepeatedConvolution
public import ExactOverlaps.Entropy.DiscreteMeasureConvolution

@[expose] public section

namespace BoxLike.Rapaport

open MeasureTheory ProbabilityTheory ExactOverlaps.Entropy
open scoped ENNReal

/-! ### Self-convolutions -/

section ConvPow

/-- `θ^{∗0} = δ_0`. -/
private theorem convPow_zero' (θ : Measure (ℝ × ℝ)) : convPow θ 0 = Measure.dirac 0 := rfl

/-- `θ^{∗(k+1)} = θ ∗ θ^{∗k}`. -/
private theorem convPow_succ' (θ : Measure (ℝ × ℝ)) (k : ℕ) :
    convPow θ (k + 1) = θ ∗ convPow θ k := rfl

/-- Self-convolutions of an s-finite measure are s-finite. -/
private theorem sFinite_convPow' (θ : Measure (ℝ × ℝ)) [SFinite θ] (k : ℕ) :
    SFinite (convPow θ k) :=
  sFinite_convk k _

/-- `θ^{∗1} = θ`. -/
private theorem convPow_one' (θ : Measure (ℝ × ℝ)) [SFinite θ] : convPow θ 1 = θ := by
  rw [convPow_succ', convPow_zero', Measure.conv_dirac_zero]

end ConvPow

/-! ### The lattice `Γ = 2^{-i} ℤ × 2^{-j} ℤ` -/

section Lattice

/-- The lattice point `(a 2^{-i}, b 2^{-j})` of the label `c = (a, b)`: the lower-left corner of
the cell of `rect i j` labelled `c`. Its range is Rapaport's lattice `Γ` (line 1393). -/
noncomputable def latticePt (i j : ℤ) (c : ℤ × ℤ) : ℝ × ℝ :=
  ((c.1 : ℝ) / 2 ^ i, (c.2 : ℝ) / 2 ^ j)

/-- `latticePt i j` as an additive homomorphism `ℤ × ℤ →+ ℝ × ℝ`: `Γ` is a subgroup of the
plane (Rapaport, line 1395). -/
noncomputable def latticeHom (i j : ℤ) : ℤ × ℤ →+ ℝ × ℝ where
  toFun := latticePt i j
  map_zero' := by simp [latticePt]
  map_add' a b := by simp [latticePt, add_div]

/-- The additive homomorphism evaluated. -/
@[simp] theorem latticeHom_apply (i j : ℤ) (c : ℤ × ℤ) : latticeHom i j c = latticePt i j c :=
  rfl

/-- The underlying map of `latticeHom i j`. -/
theorem coe_latticeHom (i j : ℤ) : ⇑(latticeHom i j) = latticePt i j := rfl

/-- The lattice point of the label `c` lies in the cell labelled `c`, so every cell of
`rect i j` contains a point of `Γ` (Rapaport, lines 1395 to 1397). -/
theorem rect_latticePt (i j : ℤ) (c : ℤ × ℤ) : rect i j (latticePt i j c) = c := by
  have hi := (dyadic_scale_pos i).ne'
  have hj := (dyadic_scale_pos j).ne'
  simp only [rect, latticePt, dyadicQuantize, mul_div_cancel₀ _ hi, mul_div_cancel₀ _ hj,
    Int.floor_intCast]

/-- `rect i j` is a left inverse of `latticePt i j`: every cell of `rect i j` contains exactly
one point of `Γ` (Rapaport, lines 1395 to 1397). -/
theorem rect_comp_latticePt (i j : ℤ) : rect i j ∘ latticePt i j = id :=
  funext (rect_latticePt i j)

/-- The lattice points depend measurably on the label. -/
@[fun_prop] theorem measurable_latticePt (i j : ℤ) : Measurable (latticePt i j) :=
  measurable_of_countable _

/-- A real number lies within one mesh `2^{-i}` of the lower endpoint of its dyadic cell. -/
theorem abs_sub_dyadicQuantize_div_le (i : ℤ) (x : ℝ) :
    |x - (dyadicQuantize i x : ℝ) / 2 ^ i| ≤ 2 ^ (-i) := by
  have hpos := dyadic_scale_pos i
  have h1 := Int.floor_le ((2 : ℝ) ^ i * x)
  have h2 := Int.lt_floor_add_one ((2 : ℝ) ^ i * x)
  have he : x - (dyadicQuantize i x : ℝ) / 2 ^ i =
      ((2 : ℝ) ^ i * x - ⌊(2 : ℝ) ^ i * x⌋) * ((2 : ℝ) ^ i)⁻¹ := by
    unfold dyadicQuantize
    field_simp
  have hle : |(2 : ℝ) ^ i * x - ⌊(2 : ℝ) ^ i * x⌋| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  rw [he, abs_mul, abs_inv, abs_of_pos hpos, zpow_neg]
  calc |(2 : ℝ) ^ i * x - ⌊(2 : ℝ) ^ i * x⌋| * ((2 : ℝ) ^ i)⁻¹ ≤ 1 * ((2 : ℝ) ^ i)⁻¹ :=
        mul_le_mul_of_nonneg_right hle (inv_nonneg.2 hpos.le)
    _ = ((2 : ℝ) ^ i)⁻¹ := one_mul _

namespace Exps

variable (χ : Exps)

/-- Rapaport's `ξ` (lines 1397 to 1398): the point of the lattice `Γ` in the cell of `ℰ_n`
containing `z`, its lower-left corner. -/
noncomputable def latticeMap (n : ℤ) (z : ℝ × ℝ) : ℝ × ℝ :=
  latticePt (lvl χ.χ₁ n) (lvl χ.χ₂ n) (χ.E n z)

/-- The lattice map in coordinates. -/
theorem latticeMap_apply (n : ℤ) (z : ℝ × ℝ) :
    χ.latticeMap n z = ((dyadicQuantize (lvl χ.χ₁ n) z.1 : ℝ) / 2 ^ lvl χ.χ₁ n,
      (dyadicQuantize (lvl χ.χ₂ n) z.2 : ℝ) / 2 ^ lvl χ.χ₂ n) := rfl

/-- The lattice map is measurable. -/
@[fun_prop] theorem measurable_latticeMap (n : ℤ) : Measurable (χ.latticeMap n) :=
  (measurable_latticePt _ _).comp (χ.measurable_E n)

/-- `ξ` does not leave the cell of `ℰ_n`: `ℰ_n(ξ z) = ℰ_n(z)` (Rapaport, lines 1397 to 1398). -/
theorem E_latticeMap (n : ℤ) (z : ℝ × ℝ) : χ.E n (χ.latticeMap n z) = χ.E n z :=
  rect_latticePt _ _ _

/-- `ℰ_n ∘ ξ = ℰ_n` (Rapaport, lines 1397 to 1398). -/
theorem E_comp_latticeMap (n : ℤ) : χ.E n ∘ χ.latticeMap n = χ.E n :=
  funext (χ.E_latticeMap n)

/-- `ξ` moves a point by at most one mesh in each coordinate, `2^{-lvl χ₁ n}` horizontally and
`2^{-lvl χ₂ n}` vertically (the estimate behind lines 1414 to 1417 of the source). -/
theorem abs_sub_latticeMap_le (n : ℤ) (z : ℝ × ℝ) :
    |z.1 - (χ.latticeMap n z).1| ≤ 2 ^ (-lvl χ.χ₁ n) ∧
      |z.2 - (χ.latticeMap n z).2| ≤ 2 ^ (-lvl χ.χ₂ n) :=
  ⟨abs_sub_dyadicQuantize_div_le _ _, abs_sub_dyadicQuantize_div_le _ _⟩

end Exps

end Lattice

/-! ### Discretised laws -/

section Discrete

/-- The law of the identity labelling under the measure of a law on `ℤ × ℤ` is the law. -/
private theorem toPMF_map_id_toMeasure (P : PMF (ℤ × ℤ)) : (P.toMeasure.map id).toPMF = P :=
  PMF.ext fun c => by
    rw [Measure.toPMF_apply, Measure.map_id,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

/-- The image of a law on `ℤ × ℤ` under `latticePt i j` has the entropy of the law for the
partition `rect i j`: on `Γ` the partition is the partition into points. -/
theorem ent_map_latticePt (i j : ℤ) (P : PMF (ℤ × ℤ)) (hP : P.support.Finite) :
    ent (P.toMeasure.map (latticePt i j)) (rect i j) = finiteEntropy P hP := by
  rw [ent_map (measurable_latticePt i j) (measurable_rect i j), rect_comp_latticePt,
    ent_eq_finiteEntropy' measurable_id (by rwa [toPMF_map_id_toMeasure])]
  exact finiteEntropy_congr (toPMF_map_id_toMeasure P) _ _

/-- The image of a finitely supported law on `ℤ × ℤ` under `latticePt i j` has finitely many
labels of `rect i j`. -/
theorem finiteLabels_map_latticePt (i j : ℤ) (P : PMF (ℤ × ℤ)) (hP : P.support.Finite) :
    FiniteLabels (P.toMeasure.map (latticePt i j)) (rect i j) := by
  rw [finiteLabels_map_iff (measurable_latticePt i j) (measurable_rect i j),
    rect_comp_latticePt, finiteLabels_iff_toPMF measurable_id, toPMF_map_id_toMeasure]
  exact hP

/-- The convolution of the images of two laws on `ℤ × ℤ` under the additive embedding of `Γ` is
the image of their discrete convolution. -/
theorem map_latticePt_conv (i j : ℤ) (P Q : PMF (ℤ × ℤ)) :
    P.toMeasure.map (latticePt i j) ∗ Q.toMeasure.map (latticePt i j) =
      (discreteConvolution P Q).toMeasure.map (latticePt i j) := by
  rw [discreteConvolution_toMeasure, ← coe_latticeHom,
    Measure.map_conv_addMonoidHom _ (measurable_of_countable _)]

/-- Convolution powers of discretised laws are images of the vendored repeated convolutions:
`(ιP)^{∗k} ∗ ιQ = ι(Q ∗ P^{∗k})` for `ι = latticePt i j`. -/
theorem convPow_map_latticePt_conv (i j : ℤ) (P Q : PMF (ℤ × ℤ)) (k : ℕ) :
    convPow (P.toMeasure.map (latticePt i j)) k ∗ Q.toMeasure.map (latticePt i j) =
      (iteratedConvolution Q P k).toMeasure.map (latticePt i j) := by
  induction k with
  | zero => rw [convPow_zero', Measure.dirac_zero_conv]; rfl
  | succ k ih =>
    have := sFinite_convPow' (P.toMeasure.map (latticePt i j)) k
    rw [convPow_succ', Measure.conv_assoc, ih, map_latticePt_conv, discreteConvolution_comm]
    rfl

namespace Exps

variable (χ : Exps)

/-- The law on `ℤ × ℤ` of the labels of `ℰ_n` under `α`; its image under the embedding of the
lattice `Γ` is Rapaport's discretised law `ξα` (`Exps.map_latticeMap_eq`). -/
noncomputable def dlaw (n : ℤ) (α : Measure (ℝ × ℝ)) [IsProbabilityMeasure α] :
    PMF (ℤ × ℤ) :=
  (α.map (χ.E n)).toPMF

variable {α : Measure (ℝ × ℝ)}

/-- Discretising does not change the entropy: `H(ξα, ℰ_n) = H(α, ℰ_n)`. -/
theorem ent_map_latticeMap (n : ℤ) : ent (α.map (χ.latticeMap n)) (χ.E n) = ent α (χ.E n) := by
  rw [ent_map (χ.measurable_latticeMap n) (χ.measurable_E n), E_comp_latticeMap]

/-- The discretised law has finite labels when `α` has. -/
theorem finiteLabels_map_latticeMap {n : ℤ} (h : FiniteLabels α (χ.E n)) :
    FiniteLabels (α.map (χ.latticeMap n)) (χ.E n) := by
  rw [finiteLabels_map_iff (χ.measurable_latticeMap n) (χ.measurable_E n), E_comp_latticeMap]
  exact h

variable [IsProbabilityMeasure α]

/-- The law of the labels is finitely supported when `ℰ_n` has finite labels under `α`. -/
theorem dlaw_support_finite {n : ℤ} (h : FiniteLabels α (χ.E n)) :
    (χ.dlaw n α).support.Finite :=
  (finiteLabels_iff_toPMF (χ.measurable_E n)).1 h

/-- The measure of the law of the labels is the image of `α` under `ℰ_n`. -/
theorem dlaw_toMeasure (n : ℤ) : (χ.dlaw n α).toMeasure = α.map (χ.E n) :=
  Measure.toPMF_toMeasure _

/-- `ξα` is the image of the law of the labels under the embedding of `Γ`. -/
theorem map_latticeMap_eq (n : ℤ) :
    α.map (χ.latticeMap n) = (χ.dlaw n α).toMeasure.map (latticePt (lvl χ.χ₁ n) (lvl χ.χ₂ n)) := by
  rw [dlaw_toMeasure, Measure.map_map (measurable_latticePt _ _) (χ.measurable_E n)]
  rfl

/-- `H(α, ℰ_n)` is the Shannon entropy of the law of the labels. -/
theorem ent_eq_finiteEntropy_dlaw {n : ℤ} (h : FiniteLabels α (χ.E n)) :
    ent α (χ.E n) = finiteEntropy (χ.dlaw n α) (χ.dlaw_support_finite h) :=
  ent_eq_finiteEntropy' (χ.measurable_E n) _

end Exps

end Discrete

/-! ### Couplings and the comparison (5.3) -/

section Coupling

/-- A coupling `π` of `μ` and `μ'` carried by pairs at most `a` apart horizontally and `b`
apart vertically. -/
private def Couple (π : Measure ((ℝ × ℝ) × (ℝ × ℝ))) (μ μ' : Measure (ℝ × ℝ)) (a b : ℝ) :
    Prop :=
  IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧ π.map Prod.snd = μ' ∧
    ∀ᵐ p ∂π, |p.1.1 - p.2.1| ≤ a ∧ |p.1.2 - p.2.2| ≤ b

/-- The set of pairs at most `a` apart horizontally and `b` apart vertically. -/
private theorem measurableSet_close (a b : ℝ) :
    MeasurableSet {p : (ℝ × ℝ) × (ℝ × ℝ) | |p.1.1 - p.2.1| ≤ a ∧ |p.1.2 - p.2.2| ≤ b} := by
  rw [Set.ofPred_and]
  exact (measurableSet_le (by fun_prop) measurable_const).inter
    (measurableSet_le (by fun_prop) measurable_const)

/-- A coupling within `a` and `b` is a coupling within any larger distances. -/
private theorem Couple.mono {π : Measure ((ℝ × ℝ) × (ℝ × ℝ))} {μ μ' : Measure (ℝ × ℝ)}
    {a b a' b' : ℝ} (h : Couple π μ μ' a b) (ha : a ≤ a') (hb : b ≤ b') :
    Couple π μ μ' a' b' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.mono fun _ hp => ⟨hp.1.trans ha, hp.2.trans hb⟩⟩

/-- A measure is coupled with its image under a map moving points by at most `a` horizontally
and `b` vertically. -/
private theorem couple_map (α : Measure (ℝ × ℝ)) [IsProbabilityMeasure α]
    {f : ℝ × ℝ → ℝ × ℝ} (hf : Measurable f) {a b : ℝ} (hab : ∀ z, |z.1 - (f z).1| ≤ a ∧
      |z.2 - (f z).2| ≤ b) :
    Couple (α.map fun z => (z, f z)) α (α.map f) a b := by
  have hm : Measurable fun z : ℝ × ℝ => (z, f z) := measurable_id.prodMk hf
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hm]
    exact Measure.map_id
  · rw [Measure.map_map measurable_snd hm]
    rfl
  · rw [ae_map_iff hm.aemeasurable (measurableSet_close a b)]
    exact ae_of_all _ hab

/-- The Dirac couplings of `δ_0` with itself. -/
private theorem couple_dirac :
    Couple (Measure.dirac 0) (Measure.dirac 0) (Measure.dirac 0) 0 0 := by
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.map_dirac' measurable_fst]
    rfl
  · rw [Measure.map_dirac' measurable_snd]
    rfl
  · rw [ae_dirac_iff (measurableSet_close 0 0)]
    simp

/-- The convolution of two couplings couples the convolutions, and the distances add. -/
private theorem Couple.conv {π π' : Measure ((ℝ × ℝ) × (ℝ × ℝ))} {μ μ' ν ν' : Measure (ℝ × ℝ)}
    {a b a' b' : ℝ} (h : Couple π μ μ' a b) (h' : Couple π' ν ν' a' b') :
    Couple (π ∗ π') (μ ∗ ν) (μ' ∗ ν') (a + a') (b + b') := by
  obtain ⟨hπ, h1, h2, h3⟩ := h
  obtain ⟨hπ', h1', h2', h3'⟩ := h'
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · have := Measure.map_conv_addMonoidHom (μ := π) (ν := π')
      (AddMonoidHom.fst (ℝ × ℝ) (ℝ × ℝ)) measurable_fst
    rw [AddMonoidHom.coe_fst] at this
    rw [this, h1, h1']
  · have := Measure.map_conv_addMonoidHom (μ := π) (ν := π')
      (AddMonoidHom.snd (ℝ × ℝ) (ℝ × ℝ)) measurable_snd
    rw [AddMonoidHom.coe_snd] at this
    rw [this, h2, h2']
  · rw [Measure.conv, ae_map_iff measurable_add.aemeasurable (measurableSet_close _ _)]
    have g₁ := Measure.quasiMeasurePreserving_fst (μ := π) (ν := π').ae h3
    have g₂ := Measure.quasiMeasurePreserving_snd (μ := π) (ν := π').ae h3'
    filter_upwards [g₁, g₂] with p hp hp'
    simp only [Prod.fst_add, Prod.snd_add, add_sub_add_comm]
    exact ⟨(abs_add_le _ _).trans (add_le_add hp.1 hp'.1),
      (abs_add_le _ _).trans (add_le_add hp.2 hp'.2)⟩

/-- `θ^{∗k}` is coupled with `(fθ)^{∗k}` within `k a` horizontally and `k b` vertically. -/
private theorem exists_couple_convPow (θ : Measure (ℝ × ℝ)) [IsProbabilityMeasure θ]
    {f : ℝ × ℝ → ℝ × ℝ} (hf : Measurable f) {a b : ℝ}
    (hab : ∀ z, |z.1 - (f z).1| ≤ a ∧ |z.2 - (f z).2| ≤ b) :
    ∀ k : ℕ, ∃ π, Couple π (convPow θ k) (convPow (θ.map f) k) (k * a) (k * b)
  | 0 => ⟨Measure.dirac 0, by
    rw [convPow_zero', convPow_zero', Nat.cast_zero, zero_mul, zero_mul]
    exact couple_dirac⟩
  | k + 1 => by
    obtain ⟨π, hπ⟩ := exists_couple_convPow θ hf hab k
    refine ⟨_, ((couple_map θ hf hab).conv hπ).mono (le_of_eq ?_) (le_of_eq ?_)⟩ <;>
    · push_cast
      ring

/-- Coupled measures have commensurable entropies for `rect i j`: the perturbation count (2.7)
on the coupling. -/
private theorem abs_ent_sub_le_of_couple {π : Measure ((ℝ × ℝ) × (ℝ × ℝ))}
    {μ μ' : Measure (ℝ × ℝ)} {i j : ℤ} {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h : Couple π μ μ' (C₁ * 2 ^ (-i)) (C₂ * 2 ^ (-j))) (hμ : FiniteLabels μ (rect i j))
    (hμ' : FiniteLabels μ' (rect i j)) :
    |ent μ (rect i j) - ent μ' (rect i j)| ≤
      Real.log (((2 * ⌈C₁⌉₊ + 3) * (2 * ⌈C₂⌉₊ + 3) : ℕ) : ℝ) := by
  classical
  obtain ⟨hπ, h1, h2, h3⟩ := h
  set S := {p : (ℝ × ℝ) × (ℝ × ℝ) | |p.1.1 - p.2.1| ≤ C₁ * 2 ^ (-i) ∧
    |p.1.2 - p.2.2| ≤ C₂ * 2 ^ (-j)}
  have hSm : MeasurableSet S := measurableSet_close _ _
  let G : (ℝ × ℝ) × (ℝ × ℝ) → ℝ × ℝ := S.piecewise Prod.snd Prod.fst
  have hG : Measurable G := Measurable.piecewise hSm measurable_snd measurable_fst
  have hGae : G =ᵐ[π] Prod.snd := by
    filter_upwards [h3] with p hp
    exact Set.piecewise_eq_of_mem _ _ _ hp
  have hpos₁ : 0 ≤ C₁ * (2 : ℝ) ^ (-i) := mul_nonneg hC₁ (dyadic_scale_pos _).le
  have hpos₂ : 0 ≤ C₂ * (2 : ℝ) ^ (-j) := mul_nonneg hC₂ (dyadic_scale_pos _).le
  have hc₁ : ∀ p, |(Prod.fst p : ℝ × ℝ).1 - (G p).1| ≤ C₁ * 2 ^ (-i) := by
    intro p
    by_cases hp : p ∈ S
    · rw [show G p = p.2 from Set.piecewise_eq_of_mem _ _ _ hp]
      exact hp.1
    · rw [show G p = p.1 from Set.piecewise_eq_of_notMem _ _ _ hp, sub_self, abs_zero]
      exact hpos₁
  have hc₂ : ∀ p, |(Prod.fst p : ℝ × ℝ).2 - (G p).2| ≤ C₂ * 2 ^ (-j) := by
    intro p
    by_cases hp : p ∈ S
    · rw [show G p = p.2 from Set.piecewise_eq_of_mem _ _ _ hp]
      exact hp.2
    · rw [show G p = p.1 from Set.piecewise_eq_of_notMem _ _ _ hp, sub_self, abs_zero]
      exact hpos₂
  have hfin₁ : FiniteLabels π (rect i j ∘ Prod.fst) := by
    rw [← finiteLabels_map_iff measurable_fst (measurable_rect i j), h1]
    exact hμ
  have hfin₂ : FiniteLabels π (rect i j ∘ G) := by
    have h' : FiniteLabels π (rect i j ∘ Prod.snd) := by
      rw [← finiteLabels_map_iff measurable_snd (measurable_rect i j), h2]
      exact hμ'
    have he : (fun b => π ((rect i j ∘ G) ⁻¹' {b})) = fun b => π ((rect i j ∘ Prod.snd) ⁻¹' {b}) :=
      funext fun b => measure_congr ((hGae.fun_comp (rect i j)).preimage {b})
    unfold FiniteLabels at h' ⊢
    rwa [he]
  have he₁ : ent μ (rect i j) = ent π (rect i j ∘ Prod.fst) := by
    rw [← h1, ent_map measurable_fst (measurable_rect i j)]
  have he₂ : ent μ' (rect i j) = ent π (rect i j ∘ G) := by
    rw [← h2, ent_map measurable_snd (measurable_rect i j)]
    exact ent_congr_ae (hGae.fun_comp (rect i j)).symm
  rw [he₁, he₂]
  exact abs_ent_sub_ent_le_log_of_commensurable ((measurable_rect i j).comp measurable_fst)
    ((measurable_rect i j).comp hG) hfin₁ hfin₂ (fiberBound_rect_perturb_symm hc₁ hc₂)
    (fiberBound_rect_perturb hc₁ hc₂)

namespace Exps

variable (χ : Exps)

/-- The comparison (5.3) of the source (lines 1400 to 1421): for probability measures `θ`, `σ`
of bounded support, `H(θ^{∗k} ∗ σ, ℰ_n)` and `H((ξθ)^{∗k} ∗ ξσ, ℰ_n)` differ by at most
`2 log (2k + 5)`, since the two convolutions are the marginals of a coupling carried by pairs
at most `k + 1` meshes apart in each coordinate. -/
theorem abs_ent_convPow_conv_sub_le {θ σ : Measure (ℝ × ℝ)} [IsProbabilityMeasure θ]
    [IsProbabilityMeasure σ] (hθ : BddSupp θ) (hσ : BddSupp σ) (n : ℤ) (k : ℕ) :
    |ent (convPow θ k ∗ σ) (χ.E n) -
        ent (convPow (θ.map (χ.latticeMap n)) k ∗ σ.map (χ.latticeMap n)) (χ.E n)| ≤
      2 * Real.log (2 * k + 5) := by
  set i := lvl χ.χ₁ n
  set j := lvl χ.χ₂ n
  have hξ := χ.measurable_latticeMap n
  have hab := χ.abs_sub_latticeMap_le n
  obtain ⟨π, hπ⟩ := exists_couple_convPow θ hξ hab k
  have hc := (hπ.conv (couple_map σ hξ hab)).mono (a' := ((k + 1 : ℕ) : ℝ) * 2 ^ (-i))
    (b' := ((k + 1 : ℕ) : ℝ) * 2 ^ (-j)) (le_of_eq (by push_cast; ring))
    (le_of_eq (by push_cast; ring))
  have hfin : FiniteLabels (convPow θ k ∗ σ) (rect i j) :=
    (hθ.convPow k).conv hσ |>.finiteLabels_E χ n
  have hfin' : FiniteLabels (convPow (θ.map (χ.latticeMap n)) k ∗ σ.map (χ.latticeMap n))
      (rect i j) := by
    rw [χ.map_latticeMap_eq n (α := θ), χ.map_latticeMap_eq n (α := σ),
      convPow_map_latticePt_conv]
    exact finiteLabels_map_latticePt _ _ _ (iteratedConvolution_support_finite _ _
      (χ.dlaw_support_finite (hσ.finiteLabels_E χ n))
      (χ.dlaw_support_finite (hθ.finiteLabels_E χ n)) k)
  have h := abs_ent_sub_le_of_couple (Nat.cast_nonneg _) (Nat.cast_nonneg _) hc hfin hfin'
  rw [Nat.ceil_natCast] at h
  have hN : (((2 * (k + 1) + 3) * (2 * (k + 1) + 3) : ℕ) : ℝ) = (2 * k + 5) * (2 * k + 5) := by
    push_cast
    ring
  have hpos : (0 : ℝ) < 2 * k + 5 := by positivity
  rw [hN, Real.log_mul hpos.ne' hpos.ne'] at h
  calc _ ≤ _ := h
    _ = 2 * Real.log (2 * k + 5) := by ring

/-- Corollary 5.2 of the source (lines 1380 to 1429) for `d = 2`, with an explicit error: for
probability measures `θ`, `σ` of bounded support, every level `n` and every `k`,
`H(θ^{∗k} ∗ σ, ℰ_n) - H(σ, ℰ_n) ≤ k (H(θ ∗ σ, ℰ_n) - H(σ, ℰ_n)) + 2 k log 7 + 2 log (2k + 5)`.
The discrete inequality is the vendored Kaimanovich–Vershik bound
`iteratedEntropy_le_first_increment` (Rapaport's Lemma 5.1, lines 1371 to 1378) on `ℤ × ℤ`,
applied as on lines 1422 to 1425, and the two comparisons are `abs_ent_convPow_conv_sub_le`
for `k` and for `1`. The bound holds for every `k ≥ 0`, not only `k ≥ 1`. -/
theorem kv_E_explicit {θ σ : Measure (ℝ × ℝ)} [IsProbabilityMeasure θ]
    [IsProbabilityMeasure σ] (hθ : BddSupp θ) (hσ : BddSupp σ) (n : ℤ) (k : ℕ) :
    ent (convPow θ k ∗ σ) (χ.E n) - ent σ (χ.E n) ≤
      k * (ent (θ ∗ σ) (χ.E n) - ent σ (χ.E n)) + 2 * k * Real.log 7 +
        2 * Real.log (2 * k + 5) := by
  set ξ := χ.latticeMap n
  have hp := χ.dlaw_support_finite (hθ.finiteLabels_E χ n)
  have hq := χ.dlaw_support_finite (hσ.finiteLabels_E χ n)
  set p := χ.dlaw n θ
  set q := χ.dlaw n σ
  -- the discrete inequality
  have hKV := iteratedEntropy_le_first_increment q p hq hp k
  -- the entropies of the discretised convolutions
  have hd : ∀ m : ℕ, ent (convPow (θ.map ξ) m ∗ σ.map ξ) (χ.E n) =
      iteratedEntropy q p hq hp m := by
    intro m
    rw [χ.map_latticeMap_eq n (α := θ), χ.map_latticeMap_eq n (α := σ),
      convPow_map_latticePt_conv]
    exact ent_map_latticePt _ _ _ _
  have hσq : ent σ (χ.E n) = finiteEntropy q hq :=
    χ.ent_eq_finiteEntropy_dlaw (hσ.finiteLabels_E χ n)
  have h1 : iteratedEntropy q p hq hp 1 =
      finiteEntropy (discreteConvolution q p) (discreteConvolution_support_finite q p hq hp) :=
    rfl
  -- the comparisons (5.3)
  have hk := χ.abs_ent_convPow_conv_sub_le hθ hσ n k
  have h₁ := χ.abs_ent_convPow_conv_sub_le hθ hσ n 1
  rw [convPow_one' θ, hd] at h₁
  rw [hd] at hk
  rw [h1] at h₁
  have h7 : 2 * Real.log (2 * ((1 : ℕ) : ℝ) + 5) = 2 * Real.log 7 := by norm_num
  rw [h7] at h₁
  rw [abs_le] at hk h₁
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [hσq]
  nlinarith [hk.2, h₁.1, hKV]

/-- Corollary 5.2 of the source (lines 1380 to 1429) for `d = 2`: for probability measures `θ`,
`σ` of bounded support, every level `n` and every `k`,
`H(θ^{∗k} ∗ σ, ℰ_n) - H(σ, ℰ_n) ≤ k (H(θ ∗ σ, ℰ_n) - H(σ, ℰ_n)) + 6 (k + 1) log (k + 2)`.
The error depends on `k` only; `kv_E_explicit` has the sharper `2 k log 7 + 2 log (2k + 5)`. -/
theorem kv_E {θ σ : Measure (ℝ × ℝ)} [IsProbabilityMeasure θ] [IsProbabilityMeasure σ]
    (hθ : BddSupp θ) (hσ : BddSupp σ) (n : ℤ) (k : ℕ) :
    ent (convPow θ k ∗ σ) (χ.E n) - ent σ (χ.E n) ≤
      k * (ent (θ ∗ σ) (χ.E n) - ent σ (χ.E n)) + 6 * ((k : ℝ) + 1) * Real.log ((k : ℝ) + 2) := by
  have h := χ.kv_E_explicit hθ hσ n k
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hcube : Real.log (((k : ℝ) + 2) ^ 3) = 3 * Real.log ((k : ℝ) + 2) := Real.log_pow _ _
  have h7 : Real.log 7 ≤ 3 * Real.log ((k : ℝ) + 2) := by
    rw [← hcube]
    exact Real.log_le_log (by norm_num) (by nlinarith [pow_nonneg hk 2, pow_nonneg hk 3])
  have h5 : Real.log (2 * k + 5) ≤ 3 * Real.log ((k : ℝ) + 2) := by
    rw [← hcube]
    exact Real.log_le_log (by positivity) (by nlinarith [pow_nonneg hk 2, pow_nonneg hk 3])
  nlinarith [mul_le_mul_of_nonneg_left h7 hk]

/-- Corollary 5.2 of the source (lines 1380 to 1429) normalised by the level `n ≥ 0`:
`H(θ^{∗k} ∗ σ, ℰ_n)/n - H(σ, ℰ_n)/n ≤ k (H(θ ∗ σ, ℰ_n)/n - H(σ, ℰ_n)/n) + 6 (k + 1) log (k + 2)/n`,
the form used in the proof of Theorem 1.4 (lines 1434 to 1515). For `n = 0` both sides vanish. -/
theorem kv_E_div {θ σ : Measure (ℝ × ℝ)} [IsProbabilityMeasure θ] [IsProbabilityMeasure σ]
    (hθ : BddSupp θ) (hσ : BddSupp σ) (n k : ℕ) :
    ent (convPow θ k ∗ σ) (χ.E n) / n - ent σ (χ.E n) / n ≤
      k * (ent (θ ∗ σ) (χ.E n) / n - ent σ (χ.E n) / n) +
        6 * ((k : ℝ) + 1) * Real.log ((k : ℝ) + 2) / n := by
  have h := χ.kv_E hθ hσ n k
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc ent (convPow θ k ∗ σ) (χ.E n) / n - ent σ (χ.E n) / n =
        (ent (convPow θ k ∗ σ) (χ.E n) - ent σ (χ.E n)) / n := by ring
    _ ≤ (k * (ent (θ ∗ σ) (χ.E n) - ent σ (χ.E n)) +
        6 * ((k : ℝ) + 1) * Real.log ((k : ℝ) + 2)) / n := div_le_div_of_nonneg_right h hn
    _ = _ := by ring

end Exps

end Coupling

end BoxLike.Rapaport
