module

/-
The packing and Minkowski dimensions of a box-like self-affine set: `thm:fraser` (tex lines 398
to 436), the chain `\dim_H X = \dim_P X = \dim_M X = dimaff(X)` and the squeeze of the modified
affinity dimension (tex lines 509 to 515), and tex lines 2074 to 2077 of `sec:affinity_dim`.

Fraser's theorem is stated as in the source (Fraser, "On the packing dimension of box-like
self-affine sets in the plane", Theorem 2.3, numbering of arXiv:1108.2639v1), as two
`Prop`-valued definitions: without a separation condition it bounds the upper Minkowski
dimension, and it asserts that the Minkowski dimension exists only under the rectangular open
set condition. The library proves both (`System.fraserBound_holds` in
`BoxLike/Fraser/UpperBound.lean`, `System.fraserROSC_holds` in `BoxLike/Fraser/Main.lean`).
Those modules import this one, so the results here take the statements as hypotheses, and
`Solution.lean` passes the proofs.

* `System.FalconerBoxBound`, `System.falconerBoxBound`: Falconer's bound
  `\overline{\dim}_M X ≤ min{2, dimaff(X)}`, proved in `BoxLike.FalconerBound`.
* `System.FraserBound`: `thm:fraser`, first part, `\dim_P X = \overline{\dim}_M X ≤ dimmaff(X)`,
  which `System.fraserBound_holds` proves.
* `System.FraserROSC`: `thm:fraser`, second part, `\dim_P X = \dim_M X = dimmaff(X)` under the
  rectangular open set condition, which `System.fraserROSC_holds` proves.
* `System.packingDim_attractor`: `\dim_P X = \overline{\dim}_M X`, the first equality of
  `thm:fraser`, proved.
* `System.falconerBoxBound_iff`, `upperBoxDim_toLp_two`, `System.falconerBoxBound_iff_euclidean`:
  Falconer's bound is `\overline{\dim}_M X ≤ dimaff(X)`, and it reads the same for the Euclidean
  metric.
* `System.falconerBoxBound_of_subsingleton`, `System.fraserBound_of_subsingleton`,
  `System.fraserROSC_of_subsingleton`: the three statements hold for a single map.
* `System.FalconerBoxBound.dimH_le`, `System.FalconerBoxBound.projDim_le`,
  `System.FalconerBoxBound.dimmaff_le_dimaff`: Falconer's bound gives the Hausdorff bound
  `eq:hausdorff_affinity_upper_bound`, `s_1, s_2 ≤ dimaff(X)` and `dimmaff(X) ≤ dimaff(X)`; the
  last two hold without it (`System.projDim_le_dimaff`, `System.dimmaff_le_dimaff`).
* `System.dim_chain`, `System.dim_chain_main2`: the chain of tex lines 510 to 514.
* `System.dimmaff_eq_dimaff`, `System.dimmaff_eq_dimaff_main2`: the squeeze of tex lines 515 to
  550, `dimmaff(X) = dimaff(X)`.
* `System.FraserROSC.dimmaff_eq_dimaff`, `System.FraserROSC.dim_eq_dimaff`: `thm:fraser`, third
  part (Fraser's Corollary 2.5), derived from the second part.
* `System.fraserBound_iff`, `System.fraserROSC_of_le`: beyond `\dim_P X = \overline{\dim}_M X`,
  `thm:fraser` asserts `\overline{\dim}_M X ≤ dimmaff(X)` and, under the rectangular open set
  condition, `dimmaff(X) ≤ \underline{\dim}_M X`.
-/
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.MainTwo
public import BoxLike.ModifiedAffinity
public import Mathlib.Analysis.Normed.Lp.ProdLp

@[expose] public section

namespace BoxLike

open MeasureTheory
open scoped ENNReal NNReal

universe u

namespace System

variable {ι : Type u} [Fintype ι] [Nonempty ι] (S : System ι)

/-! ### The statements of Falconer and Fraser -/

/-- Falconer's bound (Math. Proc. Cambridge Philos. Soc. 103 (1988), cited at tex line 2074)
for the upper Minkowski dimension: `\overline{\dim}_M X ≤ min{2, dimaff(X)}`. The article
uses it in tex lines 510 to 510, "the affinity dimension is an upper bound for the Minkowski
dimension"; `eq:hausdorff_affinity_upper_bound` is its consequence for the Hausdorff dimension
(`FalconerBoxBound.dimH_le`). It holds for every box-like system (`falconerBoxBound`). The
plane carries the sup metric; the statement for the Euclidean metric is the same
(`falconerBoxBound_iff_euclidean`), and the bound by `2` is automatic
(`falconerBoxBound_iff`). -/
def FalconerBoxBound : Prop :=
  upperBoxDim S.attractor ≤ ENNReal.ofReal (min 2 S.dimaff)

/-- Falconer's bound holds for every box-like system (`System.upperBoxDim_attractor_le`). -/
theorem falconerBoxBound : S.FalconerBoxBound := S.upperBoxDim_attractor_le

/-- `thm:fraser`, first part, in the form of the source, Fraser, Theorem 2.3: for every
box-like self-affine set, `\dim_P X = \overline{\dim}_B X ≤ s`, where `s = dimmaff(X)` is the
unique solution of `P(s) = 1`. The article writes `\dim_M X`; without a separation condition
the source asserts nothing about the lower Minkowski dimension. The source assumes at least two
maps; for a single map `X` is a point and the statement holds (`fraserBound_of_subsingleton`).
The first conjunct is `packingDim_attractor`. The library proves the statement for every box-like
system (`fraserBound_holds` in `BoxLike/Fraser/UpperBound.lean`). -/
def FraserBound : Prop :=
  packingDim S.attractor = upperBoxDim S.attractor ∧
    upperBoxDim S.attractor ≤ ENNReal.ofReal S.dimmaff

/-- `thm:fraser`, second part, Fraser, Theorem 2.3: under the rectangular open set condition
the Minkowski dimension of `X` exists and `\dim_P X = \dim_B X = dimmaff(X)`. For a single map
it holds (`fraserROSC_of_subsingleton`). The library proves the statement for every box-like
system (`fraserROSC_holds` in `BoxLike/Fraser/Main.lean`). -/
def FraserROSC : Prop :=
  S.RectangularOpenSet →
    packingDim S.attractor = ENNReal.ofReal S.dimmaff ∧
      lowerBoxDim S.attractor = ENNReal.ofReal S.dimmaff ∧
      upperBoxDim S.attractor = ENNReal.ofReal S.dimmaff

/-! ### The packing dimension of the attractor -/

omit [Fintype ι] [Nonempty ι] in
/-- The maps `φ_i` are bi-Lipschitz, so they preserve the upper Minkowski dimension. -/
theorem upperBoxDim_image_phi (i : ι) (E : Set (ℝ × ℝ)) :
    upperBoxDim (S.phi i '' E) = upperBoxDim E := by
  have hm : 0 < min |S.a i| |S.b i| :=
    lt_min (abs_pos.2 (S.a_ne_zero i)) (abs_pos.2 (S.b_ne_zero i))
  have hanti : AntilipschitzWith (Real.toNNReal (min |S.a i| |S.b i|)⁻¹) (S.phi i) :=
    AntilipschitzWith.of_le_mul_dist fun z w => by
      rw [Real.coe_toNNReal _ (inv_nonneg.2 hm.le), inv_mul_eq_div, le_div_iff₀' hm]
      exact S.le_dist_phi i z w
  exact upperBoxDim_image_eq ((S.lipschitzWith_phi i).lipschitzOnWith)
    ((hanti.to_rightInverse (S.phi_phiInv i)).lipschitzOnWith) fun x _ => S.phiInv_phi i x

omit [Fintype ι] [Nonempty ι] in
/-- The compositions `φ_𝐢` preserve the upper Minkowski dimension. -/
theorem upperBoxDim_image_phiWord (w : List ι) (E : Set (ℝ × ℝ)) :
    upperBoxDim (S.phiWord w '' E) = upperBoxDim E := by
  induction w with
  | nil => simp
  | cons i w ih => rw [phiWord_cons, Set.image_comp, upperBoxDim_image_phi, ih]

/-- `\dim_P X = \overline{\dim}_M X`, the first equality of `thm:fraser`: every open set that
meets `X` contains a copy `φ_𝐢(X)` of `X`, which has the upper Minkowski dimension of `X`, so
Baire's category theorem applies (`packingDim_eq_upperBoxDim`). This is the argument Fraser
quotes at the beginning of the proof of his Theorem 2.3. No separation condition is needed. -/
theorem packingDim_attractor : packingDim S.attractor = upperBoxDim S.attractor := by
  refine packingDim_eq_upperBoxDim S.isCompact_attractor S.attractor_nonempty fun U hU hne => ?_
  refine le_antisymm (upperBoxDim_mono Set.inter_subset_left) ?_
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  obtain ⟨_, ⟨x, rfl⟩, hzU⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU _ hzU
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.1 S.isCompact_attractor.isBounded
  obtain ⟨n, hn⟩ : ∃ n : ℕ, r ^ n * D < ε := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hS.r_nonneg hS.r_lt_one).mul_const D
    rw [zero_mul] at h
    exact (h.eventually (gt_mem_nhds hε)).exists
  have hsub : S.phiWord (futureWord x n) '' S.attractor ⊆ S.attractor ∩ U := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨S.phiWord_mem S.image_attractor_subset _ hy, hball ?_⟩
    rw [Metric.mem_ball, hS.proj_eq_phiWord x n]
    refine lt_of_le_of_lt (hS.dist_phiWord_le _ _ _) ?_
    rw [length_futureWord]
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (hD hy ⟨_, rfl⟩) (pow_nonneg hS.r_nonneg _)) hn
  calc upperBoxDim S.attractor
      = upperBoxDim (S.phiWord (futureWord x n) '' S.attractor) :=
        (S.upperBoxDim_image_phiWord _ _).symm
    _ ≤ upperBoxDim (S.attractor ∩ U) := upperBoxDim_mono hsub

/-- Beyond the equality `\dim_P X = \overline{\dim}_M X` of `packingDim_attractor`, the first
part of `thm:fraser` is the inequality `\overline{\dim}_M X ≤ dimmaff(X)`, which
`upperBoxDim_attractor_le_dimmaff` proves (`BoxLike/Fraser/Upper.lean`). -/
theorem fraserBound_iff :
    S.FraserBound ↔ upperBoxDim S.attractor ≤ ENNReal.ofReal S.dimmaff :=
  ⟨fun h => h.2, fun h => ⟨S.packingDim_attractor, h⟩⟩

/-- Beyond the first part, the second part of `thm:fraser` is the lower bound
`dimmaff(X) ≤ \underline{\dim}_M X` under the rectangular open set condition, which
`dimmaff_le_lowerBoxDim` proves (`BoxLike/Fraser/LowerCover.lean`). -/
theorem fraserROSC_of_le (hB : S.FraserBound)
    (h : S.RectangularOpenSet → ENNReal.ofReal S.dimmaff ≤ lowerBoxDim S.attractor) :
    S.FraserROSC := fun hrosc => by
  have hL := le_antisymm ((lowerBoxDim_le_upperBoxDim _).trans hB.2) (h hrosc)
  have hU := le_antisymm hB.2 ((h hrosc).trans (lowerBoxDim_le_upperBoxDim _))
  exact ⟨hB.1.trans hU, hL, hU⟩

/-! ### Falconer's bound in the Euclidean plane -/

/-- The bound `min{2, ·}` in `FalconerBoxBound` is automatic: a bounded planar set has upper
Minkowski dimension at most `2`, so Falconer's bound is `\overline{\dim}_M X ≤ dimaff(X)`. -/
theorem falconerBoxBound_iff :
    S.FalconerBoxBound ↔ upperBoxDim S.attractor ≤ ENNReal.ofReal S.dimaff := by
  refine ⟨fun h => h.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _)), fun h => ?_⟩
  have h2 : upperBoxDim S.attractor ≤ ENNReal.ofReal 2 := by
    rw [ENNReal.ofReal_ofNat]
    exact upperBoxDim_le_two S.isCompact_attractor.isBounded
  unfold FalconerBoxBound
  rcases le_total 2 S.dimaff with hd | hd
  · rwa [min_eq_left hd]
  · rwa [min_eq_right hd]

omit [Fintype ι] [Nonempty ι] in
/-- The upper Minkowski dimension of a planar set is the same for the sup metric of `ℝ × ℝ` and
for the Euclidean metric of `WithLp 2 (ℝ × ℝ)`, since the identity is bi-Lipschitz. -/
theorem _root_.BoxLike.upperBoxDim_toLp_two (E : Set (ℝ × ℝ)) :
    upperBoxDim (WithLp.toLp 2 '' E) = upperBoxDim E :=
  upperBoxDim_image_eq (WithLp.prod_lipschitzWith_toLp 2 ℝ ℝ).lipschitzOnWith
    (WithLp.prod_lipschitzWith_ofLp 2 ℝ ℝ).lipschitzOnWith fun x _ => WithLp.ofLp_toLp 2 x

/-- `FalconerBoxBound` does not depend on the choice of the sup metric: it is the same bound for
the Euclidean plane, in which Falconer works. -/
theorem falconerBoxBound_iff_euclidean :
    S.FalconerBoxBound ↔
      upperBoxDim (WithLp.toLp 2 '' S.attractor) ≤ ENNReal.ofReal (min 2 S.dimaff) := by
  rw [upperBoxDim_toLp_two]
  rfl

/-! ### The single-map case -/

omit [Fintype ι] [Nonempty ι] in
/-- For a single map `X` is a point. -/
theorem attractor_subsingleton [Subsingleton ι] : S.attractor.Subsingleton := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  rw [Subsingleton.elim x y]

/-- For a single map `dimmaff(X) = 0`: the projections are points, so `ψ^0 = 1` and `Ψ_n^0 = 1`. -/
theorem dimmaff_of_subsingleton [Subsingleton ι] : S.dimmaff = 0 := by
  have hp : ∀ c, S.projDim c = 0 := fun c => by
    rw [projDim, upperBoxDim_subsingleton (S.attractor_subsingleton.image _), ENNReal.toReal_zero]
  have hψ : ∀ w : List ι, S.modSvf 0 w = 1 := fun w => by
    rw [modSvf, S.wordDim_eq hp, Real.rpow_zero, sub_zero, Real.rpow_zero, one_mul]
  have hcard : Fintype.card ι = 1 :=
    le_antisymm (Fintype.card_le_one_iff_subsingleton.2 inferInstance) Fintype.card_pos
  have hsum : ∀ n, S.modSvfSum 0 n = 1 := fun n => by
    simp [modSvfSum, hψ, hcard]
  refine S.dimmaff_eq le_rfl ?_
  simp [modPressure, hsum]

/-- In the single-map case, the degenerate instance that Fraser's standing assumption
`|I| ≥ 2` excludes, `FalconerBoxBound`, `FraserBound` and `FraserROSC` hold: `X` is a point
and `dimmaff(X) = 0`. -/
theorem falconerBoxBound_of_subsingleton [Subsingleton ι] : S.FalconerBoxBound := by
  rw [FalconerBoxBound, upperBoxDim_subsingleton S.attractor_subsingleton]
  exact bot_le

/-- `FraserBound` in the single-map case. -/
theorem fraserBound_of_subsingleton [Subsingleton ι] : S.FraserBound := by
  rw [fraserBound_iff, upperBoxDim_subsingleton S.attractor_subsingleton]
  exact bot_le

/-- `FraserROSC` in the single-map case. -/
theorem fraserROSC_of_subsingleton [Subsingleton ι] : S.FraserROSC := fun _ => by
  have hU := upperBoxDim_subsingleton S.attractor_subsingleton
  rw [S.dimmaff_of_subsingleton, ENNReal.ofReal_zero]
  refine ⟨?_, ?_, hU⟩
  · exact le_antisymm ((packingDim_le_upperBoxDim _).trans_eq hU) bot_le
  · exact le_antisymm ((lowerBoxDim_le_upperBoxDim _).trans_eq hU) bot_le

/-! ### Consequences of Falconer's bound -/

variable {S}

/-- Falconer's bound for the upper Minkowski dimension implies his bound
`eq:hausdorff_affinity_upper_bound` for the Hausdorff dimension, `System.dimH_attractor_le`. -/
theorem FalconerBoxBound.dimH_le (hF : S.FalconerBoxBound) :
    dimH S.attractor ≤ ENNReal.ofReal (min 2 S.dimaff) :=
  (dimH_le_upperBoxDim S.attractor).trans hF

/-- `s_1, s_2 ≤ dimaff(X)` from Falconer's bound: the coordinate projections are Lipschitz images
of `X`. The inequality also holds without it (`projDim_le_dimaff`). -/
theorem FalconerBoxBound.projDim_le (hF : S.FalconerBoxBound) (c : ZMod 2) :
    S.projDim c ≤ S.dimaff := by
  have h : upperBoxDim (coord c '' S.attractor) ≤ ENNReal.ofReal S.dimaff :=
    ((upperBoxDim_image_le ((lipschitzWith_coord c).lipschitzOnWith)).trans hF).trans
      (ENNReal.ofReal_le_ofReal (min_le_right _ _))
  have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal S.dimaff_nonneg] at h'

/-- `dimmaff(X) ≤ dimaff(X)`, tex lines 515 to 515 and 2184, from Falconer's bound through
`s_1, s_2 ≤ dimaff(X)`. The inequality also holds without it (`dimmaff_le_dimaff`). -/
theorem FalconerBoxBound.dimmaff_le_dimaff (hF : S.FalconerBoxBound) : S.dimmaff ≤ S.dimaff :=
  S.dimmaff_le_dimaff_of_projDim_le hF.projDim_le

/-! ### The chain of equalities -/

/-- The chain of tex lines 510 to 514: if `\dim_H X = dimaff(X)`, the conclusion of
`thm:main2`, then Falconer's bound for the upper Minkowski dimension (`falconerBoxBound`)
forces `\dim_H X = \dim_P X = \underline{\dim}_M X = \overline{\dim}_M X = dimaff(X)`. In
particular the Minkowski dimension of `X` exists. -/
theorem dim_chain (hH : dimH S.attractor = ENNReal.ofReal S.dimaff) :
    dimH S.attractor = ENNReal.ofReal S.dimaff ∧
      packingDim S.attractor = ENNReal.ofReal S.dimaff ∧
      lowerBoxDim S.attractor = ENNReal.ofReal S.dimaff ∧
      upperBoxDim S.attractor = ENNReal.ofReal S.dimaff := by
  have hU : upperBoxDim S.attractor ≤ ENNReal.ofReal S.dimaff :=
    S.falconerBoxBound.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))
  have hP := dimH_le_packingDim S.attractor
  have hL := dimH_le_lowerBoxDim S.attractor
  rw [hH] at hP hL
  exact ⟨hH, le_antisymm ((packingDim_le_upperBoxDim _).trans hU) hP,
    le_antisymm ((lowerBoxDim_le_upperBoxDim _).trans hU) hL,
    le_antisymm hU (hL.trans (lowerBoxDim_le_upperBoxDim _))⟩

/-- The squeeze of tex lines 515 to 515 in general form: if
`\overline{\dim}_M X ≤ dimmaff(X) ≤ dimaff(X)` and `\overline{\dim}_M X = dimaff(X)`, then
`dimmaff(X) = dimaff(X)`. -/
theorem dimmaff_eq_dimaff_of_upperBoxDim
    (hB : upperBoxDim S.attractor ≤ ENNReal.ofReal S.dimmaff) (hle : S.dimmaff ≤ S.dimaff)
    (hU : upperBoxDim S.attractor = ENNReal.ofReal S.dimaff) : S.dimmaff = S.dimaff := by
  rw [hU] at hB
  exact le_antisymm hle ((ENNReal.ofReal_le_ofReal_iff S.dimmaff_nonneg).1 hB)

/-- The squeeze of tex lines 515 to 515: if `\dim_H X = dimaff(X)`, then Falconer's bound and
the first part of `thm:fraser` give `dimmaff(X) = dimaff(X)`. Neither the rectangular open set
condition nor full projections are assumed. The hypothesis `hB` is `fraserBound_holds`. -/
theorem dimmaff_eq_dimaff (hB : S.FraserBound)
    (hH : dimH S.attractor = ENNReal.ofReal S.dimaff) : S.dimmaff = S.dimaff :=
  dimmaff_eq_dimaff_of_upperBoxDim hB.2 S.dimmaff_le_dimaff (dim_chain hH).2.2.2

/-! ### Full projections -/

/-- `thm:fraser`, third part, Fraser's Corollary 2.5: under the rectangular open set condition,
if both coordinate projections of `X` have Minkowski dimension `1`, then
`dimmaff(X) = dimaff(X)`. It is derived from the second part of `thm:fraser`: then
`1 ≤ dimmaff(X) = \overline{\dim}_M X ≤ 2`, and `ψ^s = φ^s` for `1 ≤ s ≤ 2`. The hypothesis is
stated for the upper Minkowski dimension, which is the Minkowski dimension of the projection by
`lowerBoxDim_coord_eq`. Without the rectangular open set condition the conclusion holds when
`dimaff(X) ≤ 2` (`dimmaff_eq_dimaff_of_full`). -/
theorem FraserROSC.dimmaff_eq_dimaff (hR : S.FraserROSC) (hrosc : S.RectangularOpenSet)
    (hproj : ∀ c, upperBoxDim (coord c '' S.attractor) = 1) : S.dimmaff = S.dimaff := by
  obtain ⟨-, -, hU⟩ := hR hrosc
  have hp : ∀ c, S.projDim c = 1 := fun c => by rw [projDim, hproj c, ENNReal.toReal_one]
  have h1 : 1 ≤ S.dimmaff := by
    have h := upperBoxDim_image_le ((lipschitzWith_coord 0).lipschitzOnWith) (E := S.attractor)
    rw [hproj, hU, ← ENNReal.ofReal_one] at h
    exact (ENNReal.ofReal_le_ofReal_iff S.dimmaff_nonneg).1 h
  have h2 : S.dimmaff ≤ 2 := by
    have h := upperBoxDim_le_two S.isCompact_attractor.isBounded
    rw [hU, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).1 h
  exact (S.dimaff_eq_dimmaff_of_projDim_eq_one hp h1 h2).symm

/-- Fraser's Corollary 2.5 in full: under the rectangular open set condition, if both
coordinate projections of `X` have Minkowski dimension `1`, then
`\dim_P X = \dim_M X = dimaff(X)`. -/
theorem FraserROSC.dim_eq_dimaff (hR : S.FraserROSC) (hrosc : S.RectangularOpenSet)
    (hproj : ∀ c, upperBoxDim (coord c '' S.attractor) = 1) :
    packingDim S.attractor = ENNReal.ofReal S.dimaff ∧
      lowerBoxDim S.attractor = ENNReal.ofReal S.dimaff ∧
      upperBoxDim S.attractor = ENNReal.ofReal S.dimaff := by
  rw [← hR.dimmaff_eq_dimaff hrosc hproj]
  exact hR hrosc

section MainTwo

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The chain of tex lines 510 to 514 under the hypotheses of `thm:main2`: for a proximal
box-like self-affine set with rotations satisfying the projective exponential separation
condition with `dimaff(X) < 2`, and `dimaff(X) ≤ 2 - λ_1/λ_2` or the strong open set condition,
`\dim_H X = \dim_P X = \dim_M X = dimaff(X)`. -/
theorem dim_chain_main2 (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hjr : JordanRapaportDimension.{u})
    (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u}) (hly : FengLedrappierYoung.{u})
    (hlyb : FengLedrappierYoungBar.{u}) (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.ProjExpSeparation) (h2 : S.dimaff < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    dimH S.attractor = ENNReal.ofReal S.dimaff ∧
      packingDim S.attractor = ENNReal.ofReal S.dimaff ∧
      lowerBoxDim S.attractor = ENNReal.ofReal S.dimaff ∧
      upperBoxDim S.attractor = ENNReal.ofReal S.dimaff :=
  dim_chain (S.main2 hms hfk hfjj hjr hfi hfib hly hlyb hrot hprox hsep h2 μ hinv heq hor)

/-- The squeeze of tex lines 515 to 515 under the hypotheses of `thm:main2`:
`dimmaff(X) = dimaff(X)`, from Falconer's bound and the first part of `thm:fraser`. The
hypothesis `hB` is `fraserBound_holds`. -/
theorem dimmaff_eq_dimaff_main2 (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hjr : JordanRapaportDimension.{u})
    (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u}) (hly : FengLedrappierYoung.{u})
    (hlyb : FengLedrappierYoungBar.{u}) (hB : S.FraserBound)
    (hrot : S.WithRotations) (hprox : S.Proximal) (hsep : S.ProjExpSeparation)
    (h2 : S.dimaff < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    S.dimmaff = S.dimaff :=
  dimmaff_eq_dimaff hB
    (S.main2 hms hfk hfjj hjr hfi hfib hly hlyb hrot hprox hsep h2 μ hinv heq hor)

end MainTwo

end System

end BoxLike
