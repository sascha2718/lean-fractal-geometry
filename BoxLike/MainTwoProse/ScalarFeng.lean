module

/-
The scalar Ledrappier–Young formula for the coordinate projections of the diagonal subsystems
of the proof of `thm:main2` in `sec:dimension_result_proof`. The proof cites Feng's Theorems 1.2
and 1.3 for the self-similar measures `(proj_x ∘ π_n)_*ν_n` and `(proj_y ∘ π_n)_*ν_n` on the
line: `h_1(ν_n) = log #W_n + log |a_n| dim((proj_x ∘ π_n)_*ν_n)` and, under
`it:main2_threshold`,
`H_{ν_n}(𝒫 | \widehat{ξ_1^⊥}) = log #W_n + log |b_n| dim((proj_y ∘ π_n)_*ν_n)`. In the notation of these docstrings, `q_{x,n} = log #W_n + d_{x,n} log |a_n|` and
`q_{y,n} = log #W_n + d_{y,n} log |b_n|`, with `d_{x,n}` and `d_{y,n}` the dimensions of the two
marginals.

Feng's theorems hold for affine iterated function systems in every dimension. The library
records their planar case `d = 2` as `FengLedrappierYoung`, for every box-like system, and their
case `d = 1` for the projective system of a box-like system with rotations as
`FengLedrappierYoungBar`. A diagonal subsystem has no rotation, so the second statement does not
apply to it. The case `d = 1` for the line system `x ↦ r x + t_k` is the planar case for the
degenerate planar system `z ↦ diag(r, r/2) z + (t_k, 0)`, whose attractor lies on the horizontal
axis: its projection of `ν_n` is the image of the self-similar measure under `t ↦ (t, 0)`, its
slow subspace is vertical, its partition `ξ_1` is the partition of the diagonal subsystem by the
past and the coordinate `c` of the coded point, and its partition `ξ_2` equals `ξ_1`, since the
vertical coordinate vanishes. The planar formula then reads `d_c = (q_c - log #W_n) / log |r|`
for the ratio `r` of the coordinate `c`. This is
the scalar Feng interface for the actual subsystem, derived from the existing statement
`FengLedrappierYoung` with no new premise. `BoxLike/ProjectiveLineSystem.lean` applies the same
construction to the projective system of every box-like system
(`System.isExactDim_map_projBar_of_fengLedrappierYoung`).

The conditional entropies `q_{x,n}` and `q_{y,n}` are taken given the past and the coordinate
of the coded point, which are the entropies of Feng's formula; for the Bernoulli measure `ν_n`
the past is independent of the future, as the proof observes.

* `System.lineSystem`: the planar system `diag(r_k, r_k/2) z + (t_k, 0)` of the coordinate `c`.
* `System.IsHomDiag.lineSystem`, `System.IsHomDiag.proj_lineSystem`: it is homogeneous diagonal,
  and its projection is `𝐢 ↦ (coord c (π(𝐢)), 0)`.
* `System.IsHomDiag.xi_one_lineSystem`, `…xi_two_lineSystem`: its partitions `ξ_1 = ξ_2`.
* `isExactDim_map_prodMk_zero`: the embedding `t ↦ (t, 0)` preserves exact dimensions.
* `System.IsHomDiag.dimEntropy_one_lineSystem`: the formula `q_c = H - χ_c d_c`.
* `System.IsHomDiag.dimEntropy_one_eq_scalar`: `q_{x,n} = h_1(ν_n) = log #W_n + d_{x,n} log |a_n|`.
* `System.IsHomDiag.condEntropy_xiPerp_eq_scalar`:
  `q_{y,n} = H(𝒫 | \widehat{ξ_1^⊥}) = log #W_n + d_{y,n} log |b_n|`.
-/
public import BoxLike.LiteratureFeng
public import BoxLike.MainTwoProse.DiagonalSubsystem

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Metric

universe u

/-! ### The embedding of the line as the horizontal axis -/

/-- The embedding `t ↦ (t, 0)` of the line as the horizontal axis is a measurable embedding. -/
theorem measurableEmbedding_prodMk_zero :
    MeasurableEmbedding fun t : ℝ => (t, (0 : ℝ)) := by
  refine MeasurableEmbedding.of_measurable_inverse (measurable_id.prodMk measurable_const)
    ?_ measurable_fst fun t => rfl
  have : Set.range (fun t : ℝ => (t, (0 : ℝ))) = Prod.snd ⁻¹' {0} := by
    ext p
    constructor
    · rintro ⟨t, rfl⟩
      rfl
    · intro hp
      exact ⟨p.1, Prod.ext rfl hp.symm⟩
  rw [this]
  exact measurable_snd (measurableSet_singleton 0)

/-- The embedding `t ↦ (t, 0)` maps closed intervals onto closed balls of the supremum metric
centred on the horizontal axis. -/
theorem preimage_prodMk_zero_closedBall (t r : ℝ) :
    (fun s : ℝ => (s, (0 : ℝ))) ⁻¹' closedBall (t, 0) r = closedBall t r := by
  ext s
  simp only [Set.mem_preimage, mem_closedBall, Prod.dist_eq, dist_self]
  rw [max_eq_left dist_nonneg]

/-- The image of an exact-dimensional measure on the line under `t ↦ (t, 0)` is exact-dimensional
with the same dimension. -/
theorem isExactDim_map_prodMk_zero {m : Measure ℝ} {d : ℝ} (h : IsExactDim m d) :
    IsExactDim (m.map fun t : ℝ => (t, (0 : ℝ))) d := by
  unfold IsExactDim
  rw [measurableEmbedding_prodMk_zero.ae_map_iff]
  filter_upwards [h] with t ht
  unfold HasLocalDim at ht ⊢
  refine ht.congr fun r => ?_
  rw [measureReal_def, measureReal_def,
    Measure.map_apply measurableEmbedding_prodMk_zero.measurable measurableSet_closedBall,
    preimage_prodMk_zero_closedBall]

namespace System

/-! ### The line system of a coordinate -/

variable {κ : Type*}

/-- The planar system `z ↦ diag(r_k, r_k / 2) z + (t_k, 0)` of the coordinate `c` of a system
`T`, with `r_k = g'_{(k, c)}` and `t_k = g_{(k, c)}(0)`: it carries the line system of the
coordinate `c` on the horizontal axis. -/
noncomputable def lineSystem (T : System κ) (c : ZMod 2) : System κ where
  o := T.o
  a k := T.ratio (k, c)
  b k := T.ratio (k, c) / 2
  v k := (T.trans (k, c), 0)
  a_ne_zero _ := T.ratio_ne_zero _
  b_ne_zero _ := div_ne_zero (T.ratio_ne_zero _) two_ne_zero
  abs_a_lt_one _ := T.abs_ratio_lt_one _
  abs_b_lt_one k := by
    rw [abs_div, abs_two]
    have := T.abs_ratio_lt_one (k, c)
    linarith [abs_nonneg (T.ratio (k, c))]

namespace IsHomDiag

variable {T : System κ} {a b : ℝ} (hT : T.IsHomDiag a b)
include hT

/-- The line system of a homogeneous diagonal system is homogeneous diagonal, with the entries
`r` and `r / 2`, where `r` is `a` for `c = 0` and `b` for `c = 1`. -/
theorem lineSystem (c : ZMod 2) :
    (T.lineSystem c).IsHomDiag (if c = 0 then a else b) ((if c = 0 then a else b) / 2) :=
  ⟨hT.o_eq, fun k => hT.ratio_eq k c, fun k => by
    change T.ratio (k, c) / 2 = _
    rw [hT.ratio_eq]⟩

/-- The coordinate `c` of `π(𝐢)` is `\overline{π}` of the constant path on the axis `c` over
`𝐢`. -/
theorem coord_proj (c : ZMod 2) (x : ℤ → κ) :
    coord c (T.proj x) = T.projBar fun k => (x k, c) := by
  rcases zmod_two_cases c with rfl | rfl
  · rw [coord_zero, fst_proj, hT.tau_eq]
  · rw [coord_one, snd_proj, hT.omega_eq]

/-- The projection of the line system is `𝐢 ↦ (coord c (π(𝐢)), 0)`. -/
theorem proj_lineSystem (c : ZMod 2) (x : ℤ → κ) :
    (T.lineSystem c).proj x = (coord c (T.proj x), 0) := by
  have hL := hT.lineSystem c
  rw [proj, hL.tau_eq, hL.omega_eq, hT.coord_proj]
  refine Prod.ext ?_ ?_
  · show (T.lineSystem c).projBar _ = T.projBar _
    unfold projBar projBarTerm
    congr 1
    funext k
    congr 1
    simp [gDeriv, futureWord, List.map_map, Function.comp_def, System.lineSystem, ratio]
  · show (T.lineSystem c).projBar _ = 0
    unfold projBar projBarTerm
    simp [System.lineSystem, trans]

variable [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- The partition `ξ_1` of the line system: the past and the coordinate `c` of the coded point
of the diagonal subsystem. -/
theorem xi_one_lineSystem (c : ZMod 2) {μ : Measure (ℤ → κ)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (x : ℤ → κ) :
    (T.lineSystem c).xi μ 1 x =
      {y | SamePast y x ∧ coord c (T.proj y) = coord c (T.proj x)} := by
  have hL := hT.lineSystem c
  have hr : |(if c = 0 then a else b) / 2| ≤ |if c = 0 then a else b| := by
    rw [abs_div, abs_two]
    linarith [abs_nonneg (if c = 0 then a else b)]
  rw [hL.xi_one_eq hr hinv]
  simp only [hT.proj_lineSystem]

/-- The partition `ξ_2` of the line system equals its partition `ξ_1`, since the vertical
coordinate of its coded points vanishes. -/
theorem xi_two_lineSystem (c : ZMod 2) {μ : Measure (ℤ → κ)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) :
    (T.lineSystem c).xi μ 2 = (T.lineSystem c).xi μ 1 := by
  have hL := hT.lineSystem c
  have hr : |(if c = 0 then a else b) / 2| ≤ |if c = 0 then a else b| := by
    rw [abs_div, abs_two]
    linarith [abs_nonneg (if c = 0 then a else b)]
  funext x
  rw [hL.xi_two_eq hr hinv, hL.xi_one_eq hr hinv]
  ext y
  simp only [Set.mem_ofPred_eq, hT.proj_lineSystem, Prod.mk.injEq, and_true]

/-- The partition `ξ_1` of the diagonal subsystem is the partition `ξ_1` of its horizontal
line system, when `|b| ≤ |a|`. -/
theorem xi_one_eq_lineSystem (hab : |b| ≤ |a|) {μ : Measure (ℤ → κ)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) : T.xi μ 1 = (T.lineSystem 0).xi μ 1 := by
  funext x
  rw [hT.xi_one_eq hab hinv, hT.xi_one_lineSystem 0 hinv]
  simp only [coord_zero]

/-- The partition `ξ_1^⊥` of the diagonal subsystem is the partition `ξ_1` of its vertical line
system, when `|b| ≤ |a|`. -/
theorem xiPerp_eq_lineSystem (hab : |b| ≤ |a|) {μ : Measure (ℤ → κ)} [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) : T.xiPerp μ = (T.lineSystem 1).xi μ 1 := by
  funext x
  rw [hT.xiPerp_eq hab hinv, hT.xi_one_lineSystem 1 hinv]
  simp only [coord_one]

/-- The projection of `ν_n` under the line system is the image of the coordinate marginal under
`t ↦ (t, 0)`. -/
theorem map_proj_lineSystem (c : ZMod 2) (ν : Measure (ℤ → κ)) :
    ν.map (T.lineSystem c).proj = (T.marginal c ν).map fun t : ℝ => (t, (0 : ℝ)) := by
  obtain ⟨r, M, hS⟩ := T.exists_bounds
  have hc : Measurable (coord c) := by
    unfold coord
    split_ifs
    · exact measurable_fst
    · exact measurable_snd
  rw [marginal, Measure.map_map hc hS.measurable_proj,
    Measure.map_map measurableEmbedding_prodMk_zero.measurable (hc.comp hS.measurable_proj)]
  congr 1
  funext x
  exact hT.proj_lineSystem c x

end IsHomDiag

end System

namespace System.IsHomDiag

variable {κ : Type u} [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ] [Nonempty κ]
  {T : System κ} {a b : ℝ} (hT : T.IsHomDiag a b)
include hT

/-- The scalar Ledrappier–Young formula `q_c = log #W_n + d_c log |r|` for the coordinate `c` of
the diagonal subsystem with ratio `r` (proof of `thm:main2`, citing Feng, Theorems 1.2 and 1.3):
the planar formula `thm:feng1` for the line system of the coordinate `c` gives
`dim = (h_1 - log #W_n) / log |r|`, since its partitions `ξ_2` and `ξ_1` agree, and Kittle–Kogler
give `dim = min{1, log #W_n / (-log |r|)}` for the same measure on the horizontal axis.
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem dimEntropy_one_lineSystem (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (c : ZMod 2)
    (hfree : Function.Injective
      (simWord (fun _ : κ => if c = 0 then a else b) (fun k => T.trans (k, c)))) :
    (T.lineSystem c).dimEntropy (uniformBernoulli κ) 1 =
      Real.log (Fintype.card κ) - -Real.log |if c = 0 then a else b| *
        min 1 (Real.log (Fintype.card κ) / -Real.log |if c = 0 then a else b|) := by
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
  have hinv := measurePreserving_shift_uniformBernoulli (κ := κ) 1
  have hLY := hly (T.lineSystem c) (uniformBernoulli κ) hinv ergodic_shift_uniformBernoulli
    (hL.lyapunov₂_lt_lyapunov₁ hrr hinv)
  have h2 : (T.lineSystem c).dimEntropy (uniformBernoulli κ) 2 =
      (T.lineSystem c).dimEntropy (uniformBernoulli κ) 1 := by
    unfold System.dimEntropy
    rw [hT.xi_two_lineSystem c hinv]
  rw [h2, sub_self, zero_div, add_zero, hL.dimEntropy_zero hrr.le,
    hL.lyapunov₁_eq hrr.le hinv, hT.map_proj_lineSystem] at hLY
  have hKK := isExactDim_map_prodMk_zero (hT.marginal_isExactDim hkk c hfree)
  have : IsProbabilityMeasure ((T.marginal c (uniformBernoulli κ)).map
      fun t : ℝ => (t, (0 : ℝ))) := by
    unfold System.marginal
    infer_instance
  have heq := IsExactDim.unique (IsProbabilityMeasure.ne_zero _) hLY hKK
  rw [div_eq_iff hlr.ne] at heq
  linarith

/-- `q_{x,n} = h_1(ν_n) = log #W_n + d_{x,n} log |a_n|` with
`d_{x,n} = min{1, log #W_n / (-log |a_n|)}` (proof of `thm:main2`): the scalar Ledrappier–Young
formula for the horizontal coordinate. The partition
`ξ_1` of the diagonal subsystem conditions on the past and the horizontal coordinate, since its
slow subspace `V^1` is the vertical axis.
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem dimEntropy_one_eq_scalar (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (hab : |b| ≤ |a|)
    (hfreex : Function.Injective (simWord (fun _ : κ => a) (fun k => T.trans (k, 0)))) :
    T.dimEntropy (uniformBernoulli κ) 1 =
      Real.log (Fintype.card κ) - -Real.log |a| *
        min 1 (Real.log (Fintype.card κ) / -Real.log |a|) := by
  have h := hT.dimEntropy_one_lineSystem hly hkk 0 (by simpa using hfreex)
  unfold System.dimEntropy at h ⊢
  rw [hT.xi_one_eq_lineSystem hab (measurePreserving_shift_uniformBernoulli 1)]
  exact h

/-- `q_{y,n} = log #W_n + d_{y,n} log |b_n|` with `d_{y,n} = min{1, log #W_n / (-log |b_n|)}`
(proof of `thm:main2`): the scalar Ledrappier–Young formula for the vertical coordinate, where
`q_{y,n}`
is the conditional entropy given the partition `ξ_1^⊥` by the past and the vertical coordinate.
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem condEntropy_xiPerp_eq_scalar (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (hab : |b| ≤ |a|)
    (hfreey : Function.Injective (simWord (fun _ : κ => b) (fun k => T.trans (k, 1)))) :
    condEntropy (uniformBernoulli κ) (T.xiPerp (uniformBernoulli κ)) =
      Real.log (Fintype.card κ) - -Real.log |b| *
        min 1 (Real.log (Fintype.card κ) / -Real.log |b|) := by
  have h := hT.dimEntropy_one_lineSystem hly hkk 1 (by simpa using hfreey)
  unfold System.dimEntropy at h
  rw [hT.xiPerp_eq_lineSystem hab (measurePreserving_shift_uniformBernoulli 1)]
  exact h

end System.IsHomDiag

end BoxLike
