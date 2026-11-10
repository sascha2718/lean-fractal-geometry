module

/-
The dimension of the coordinate projections in the proof of `thm:main2`,
`sec:dimension_result_proof`, the passage "When `s < 2`, we have `t = s` and
`log #W_n/(-log |a_n|) → -h/λ_1 ≥ min{1, s}` by `eq:diml_min2`. Since `(proj_x ∘ π_n)_*ν_n` is
supported on `proj_x(X)`, it follows that `\dim_H(proj_x(X)) ≥ min{1, s}`. An anti-diagonal
generator maps `proj_x(X)` bi-Lipschitzly into `proj_y(X)`, and so both coordinate projections
of `X` have Hausdorff (and Minkowski) dimension `min{1, s}`": for a proximal box-like
self-affine set `X` with rotations whose projective system has no exact overlaps and
`dimaff(X) < 2`, both coordinate projections of `X` have Hausdorff and Minkowski dimension
`min{1, dimaff(X)}`. This is the statement `sec:intro_fraser` uses for `dimmaff(X) = dimaff(X)`,
and the manuscript deduces `thm:main2` for `s ≤ 1` from it.

The families `W_n` of `BoxLike/MainTwoProse/TypicalWordsSMB.lean`, before the modifications of
cases `it:main2_threshold` and `it:main2_sosc`, give homogeneous diagonal subsystems with the
Bernoulli measures `ν_n` of `BoxLike/MainTwoProse/DiagonalSubsystem.lean`. Kittle–Kogler
(`IsHomDiag.marginal_isExactDim`) give
`dim((proj_x ∘ π_n)_*ν_n) = min{1, log #W_n/(-log |a_n|)}`, and `log #W_n/(-log |a_n|) → -h/λ_1`,
which is `min{1, s}` by `eq:diml_min2`. The measure `(proj_x ∘ π_n)_*ν_n` is carried by
`proj_x(X)`, since the attractor of the subsystem lies in `X`, so the mass distribution
principle gives `\dim_H proj_x(X) ≥ min{1, s}`. An anti-diagonal generator maps `proj_x(X)`
affinely into `proj_y(X)`, and the Hausdorff dimension is invariant under affine bijections of
the line. Both projections are Lipschitz images of `X`, whose upper Minkowski dimension is at
most `s` (`eq:hausdorff_affinity_upper_bound`), and bounded subsets of the line, so their upper
Minkowski dimension is at most `min{1, s}`.

* `dimH_image_affine`: an affine bijection of the line preserves the Hausdorff dimension.
* `min_one_div_neg_eq`: `min{1, -h/λ_1} = min{1, s}` for `h + Λ(𝖠, μ, s) = 0` and `s < 2`.
* `IsExactDim.le_dimH_coord_image`: the mass distribution principle for a coordinate marginal.
* `System.upperBoxDim_coord_le_upperBoxDim_attractor`, `System.upperBoxDim_coord_le_min`: the
  Lipschitz upper bound.
* `System.dimH_coord_add_le`, `System.dimH_coord_eq`: the affine copy of one projection inside
  the other.
* `System.le_dimH_coord_of_family`: the lower bound `\dim_H proj_c(X) ≥ min{1, log #W_n/(-log |r|)}`
  for one family of diagonal words, `r` the contraction ratio of the coordinate `c`.
* `System.le_dimH_coord_zero_normalised`, `System.le_dimH_coord_zero_of_pressure`: the lower
  bound `\dim_H proj_x(X) ≥ min{1, s}`.
* `System.dimH_coord_image_eq`, `System.lowerBoxDim_coord_image_eq`,
  `System.upperBoxDim_coord_image_eq`, `System.projDim_eq_min`: the Hausdorff, lower and upper
  Minkowski dimensions of both projections are `min{1, dimaff(X)}`.
* `System.dimH_coord_image_eq_proved`, `System.projDim_eq_min_proved`: the same with the library
  proofs of the five statements the proof uses, with no literature hypothesis.
-/
public import BoxLike.AffinityMain
public import BoxLike.EquilibriumExistence
public import BoxLike.EquilibriumGibbs
public import BoxLike.FalconerBound
public import BoxLike.FraserJordanJurga.Main
public import BoxLike.General
public import BoxLike.KittleKogler
public import BoxLike.MainTwoProse.DiagonalSubsystem
public import BoxLike.MainTwoProse.TypicalWordsSMB
public import BoxLike.MassDistribution
public import BoxLike.MorrisShmerkin
public import BoxLike.ShannonMcMillanBreiman
public import BoxLike.Subsystem

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set

universe u

/-! ### Affine images on the line -/

/-- An affine bijection `t ↦ a t + b` of the line, `a ≠ 0`, preserves the Hausdorff dimension:
the map and its inverse are Lipschitz. Used in the proof of `thm:main2` for the affine copy of
`proj_x(X)` inside `proj_y(X)`. -/
theorem dimH_image_affine {a : ℝ} (ha : a ≠ 0) (b : ℝ) (F : Set ℝ) :
    dimH ((fun t : ℝ => a * t + b) '' F) = dimH F := by
  have hf : LipschitzWith ‖a‖₊ fun t : ℝ => a * t + b :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, Real.dist_eq, coe_nnnorm, Real.norm_eq_abs, ← abs_mul]
      exact le_of_eq (by ring_nf)
  have hg : LipschitzWith ‖a⁻¹‖₊ fun u : ℝ => a⁻¹ * (u - b) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, Real.dist_eq, coe_nnnorm, Real.norm_eq_abs, ← abs_mul]
      exact le_of_eq (by ring_nf)
  refine le_antisymm (hf.dimH_image_le F) ?_
  have hFF : (fun u : ℝ => a⁻¹ * (u - b)) '' ((fun t : ℝ => a * t + b) '' F) = F := by
    rw [image_image]
    have : ∀ t ∈ F, a⁻¹ * (a * t + b - b) = t := fun t _ => by
      rw [add_sub_cancel_right, inv_mul_cancel_left₀ ha]
    rw [image_congr this, image_id']
  calc dimH F = dimH ((fun u : ℝ => a⁻¹ * (u - b)) '' ((fun t : ℝ => a * t + b) '' F)) := by
        rw [hFF]
    _ ≤ dimH ((fun t : ℝ => a * t + b) '' F) := hg.dimH_image_le _

/-! ### A real-variable lemma -/

/-- `min{1, h/(-λ_1)} = min{1, s}` when `h + Λ(𝖠, μ, s) = 0` and `s < 2`, from `eq:diml_min2`:
`h = -sλ_1` for `s ≤ 1`, and `h > -λ_1` for `1 < s < 2`. It identifies the limit of the
dimensions `min{1, log #W_n/(-log |a_n|)}` in the proof of `thm:main2` with `min{1, s}`. -/
theorem min_one_div_neg_eq {h l1 l2 s : ℝ} (hl : l2 ≤ l1) (hl1 : l1 < 0) (hs2 : s < 2)
    (heq : h + energy l1 l2 s = 0) : min 1 (h / -l1) = min 1 s := by
  have hl2 : l2 < 0 := hl.trans_lt hl1
  have hl1' : -l1 ≠ 0 := (neg_pos.2 hl1).ne'
  unfold energy at heq
  split_ifs at heq with hs1 hs2'
  · have hh : h / -l1 = s := by
      rw [div_eq_iff hl1']
      linear_combination heq
    rw [hh]
  · have h1 : 1 < h / -l1 := by
      rw [one_lt_div (neg_pos.2 hl1)]
      have := mul_pos (sub_pos.2 (not_le.1 hs1)) (neg_pos.2 hl2)
      nlinarith
    rw [min_eq_left h1.le, min_eq_left (not_le.1 hs1).le]
  · exact absurd hs2.le hs2'

/-! ### The mass distribution principle for a coordinate marginal -/

/-- The mass distribution principle for a coordinate projection, the step "since
`(proj_x ∘ π_n)_*ν_n` is supported on `proj_x(X)`, it follows that
`\dim_H(proj_x(X)) ≥ min{1, s}`" of the proof of `thm:main2`: if
the coordinate marginal `(proj_c)_*(π_*ν)` of a probability measure `ν` on the sequence space
of a system `T` is exact-dimensional, and the attractor of `T` lies in a compact set `A`, then
its dimension is at most `\dim_H proj_c(A)`. -/
theorem IsExactDim.le_dimH_coord_image {κ : Type*} [Finite κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] {T : System κ} {ν : Measure (ℤ → κ)}
    [IsProbabilityMeasure ν] {c : ZMod 2} {d : ℝ} (h : IsExactDim (T.marginal c ν) d)
    {A : Set (ℝ × ℝ)} (hA : IsCompact A) (hTA : T.attractor ⊆ A) :
    ENNReal.ofReal d ≤ dimH (System.coord c '' A) := by
  have : IsFiniteMeasure (T.marginal c ν) := by
    unfold System.marginal
    infer_instance
  refine h.le_dimH ?_
  obtain ⟨r, M, hB⟩ := T.exists_bounds
  have hc : Measurable (System.coord c) := (System.continuous_coord c).measurable
  have hAc : MeasurableSet (System.coord c '' A) :=
    (hA.image (System.continuous_coord c)).isClosed.measurableSet
  rw [System.marginal, Measure.map_apply hc hAc, Measure.map_apply hB.measurable_proj (hc hAc)]
  have hpre : T.proj ⁻¹' (System.coord c ⁻¹' (System.coord c '' A)) = univ :=
    eq_univ_of_forall fun x => mem_image_of_mem _ (hTA ⟨x, rfl⟩)
  rw [hpre, measure_univ]
  exact zero_lt_one

namespace System

variable {ι : Type u} [Fintype ι] (S : System ι)

/-! ### The Lipschitz upper bound -/

omit [Fintype ι] in
/-- The coordinate projections are Lipschitz images of `X`, so
`\overline{\dim}_M proj_c(X) ≤ \overline{\dim}_M X` (proof of `thm:main2`). -/
theorem upperBoxDim_coord_le_upperBoxDim_attractor (c : ZMod 2) :
    upperBoxDim (coord c '' S.attractor) ≤ upperBoxDim S.attractor :=
  upperBoxDim_image_le (lipschitzWith_coord c).lipschitzOnWith

/-- `\overline{\dim}_M proj_c(X) ≤ min{1, dimaff(X)}` (proof of `thm:main2`): the projection is
a Lipschitz image of `X`, whose upper Minkowski dimension is at most `dimaff(X)` by
`eq:hausdorff_affinity_upper_bound`, and a bounded subset of the line. -/
theorem upperBoxDim_coord_le_min [Nonempty ι] (c : ZMod 2) :
    upperBoxDim (coord c '' S.attractor) ≤ ENNReal.ofReal (min 1 S.dimaff) := by
  rcases le_total 1 S.dimaff with h | h
  · rw [min_eq_left h, ENNReal.ofReal_one]
    exact S.upperBoxDim_coord_le_one c
  · rw [min_eq_right h]
    exact (S.upperBoxDim_coord_le_upperBoxDim_attractor c).trans
      S.upperBoxDim_attractor_le_dimaff

/-! ### The affine copy of one projection inside the other -/

omit [Fintype ι] in
/-- `\dim_H proj_{c + o(i)}(X) ≤ \dim_H proj_c(X)`: by `eq:phi_def_by_g`, `proj_c(X)` contains
the affine copy `g_{(i,c)}(proj_{c + o(i)}(X))` of `proj_{c + o(i)}(X)`. For an anti-diagonal
generator this is the step "an anti-diagonal generator maps `proj_x(X)` bi-Lipschitzly into
`proj_y(X)`" of the proof of `thm:main2`. -/
theorem dimH_coord_add_le [Finite ι] (i : ι) (c : ZMod 2) :
    dimH (coord (c + S.o i) '' S.attractor) ≤ dimH (coord c '' S.attractor) := by
  have hsub : (fun t : ℝ => S.ratio (i, c) * t + S.trans (i, c)) ''
      (coord (c + S.o i) '' S.attractor) ⊆ coord c '' S.attractor := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨S.phi i z, S.image_attractor_subset i ⟨z, hz, rfl⟩, S.coord_phi c i z⟩
  rw [← dimH_image_affine (S.ratio_ne_zero (i, c)) (S.trans (i, c))]
  exact dimH_mono hsub

omit [Fintype ι] in
/-- For a system with an anti-diagonal generator the two coordinate projections of `X` have the
same Hausdorff dimension: each contains an affine copy of the other (proof of `thm:main2`). -/
theorem dimH_coord_eq [Finite ι] (h : ∃ i, S.o i = 1) (c c' : ZMod 2) :
    dimH (coord c '' S.attractor) = dimH (coord c' '' S.attractor) := by
  obtain ⟨i, hi⟩ := h
  have key : ∀ c : ZMod 2,
      dimH (coord (c + 1) '' S.attractor) ≤ dimH (coord c '' S.attractor) :=
    fun c => hi ▸ S.dimH_coord_add_le i c
  have h01 := key 0
  have h10 := key 1
  rw [show (1 : ZMod 2) + 1 = 0 from by decide] at h10
  rw [zero_add] at h01
  rcases zmod_two_cases c with rfl | rfl <;> rcases zmod_two_cases c' with rfl | rfl
  exacts [rfl, le_antisymm h10 h01, le_antisymm h01 h10, rfl]

/-! ### The lower bound for one family -/

/-- The lower bound `\dim_H proj_c(X) ≥ min{1, log #W_n/(-log |r|)}`, with `r` the contraction
ratio of the coordinate `c`, for one family `W` of diagonal
planar words of length `n` with the common matrix `diag(a, b)` (proof of `thm:main2`): the
coordinate maps of the subsystem generate free semigroups, since the projective system of `Φ`
has no exact overlaps, so Kittle–Kogler give the dimension of the coordinate marginal of
`ν_n`, which is carried by `proj_c(X)`. Neither the case distinction of the proof nor an
inequality between `|a|` and `|b|` enters.
Depends on: `KittleKoglerDimension`. -/
theorem le_dimH_coord_of_family (hkk : KittleKoglerDimension.{u}) [Nonempty ι]
    (hfree : S.NoExactOverlaps) {W : Finset (List ι)} (hW : W.Nonempty) {n : ℕ} (hn : 0 < n)
    {a b : ℝ} (hWn : ∀ w ∈ W, w.length = n ∧ S.matWord w = boxMat 0 a b) (c : ZMod 2) :
    ENNReal.ofReal (min 1 (Real.log W.card / -Real.log |if c = 0 then a else b|)) ≤
      dimH (coord c '' S.attractor) := by
  classical
  let _ : MeasurableSpace W := ⊤
  have : MeasurableSingletonClass W := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have : Nonempty W := hW.to_subtype
  have hlen : ∀ w : W, (w : List ι).length = n := fun w => (hWn w w.2).1
  have hwne : ∀ w : W, (w : List ι) ≠ [] := fun w =>
    List.ne_nil_of_length_pos (by rw [hlen w]; exact hn)
  set T := S.subsystem (fun w : W => (w : List ι)) hwne with hT_def
  have hdiagW : ∀ w : W, S.oWord w = 0 ∧ S.gDeriv (S.codeWord 0 w) = a ∧
      S.gDeriv (S.codeWord 1 w) = b := fun w =>
    (S.matWord_eq_boxMat_zero_iff _ _ _).1 (hWn w w.2).2
  have hT : T.IsHomDiag a b :=
    ⟨fun w => (hdiagW w).1, fun w => (hdiagW w).2.1, fun w => (hdiagW w).2.2⟩
  -- the coordinate maps of the subsystem generate a free semigroup
  have hfreec : Function.Injective
      (simWord (fun _ : W => if c = 0 then a else b) (fun w => T.trans (w, c))) := by
    have key := hfree.simWord_injective (S := S) c (w := fun w : W => (w : List ι))
      (fun w => (hdiagW w).1) hn hlen Subtype.val_injective
    have e1 : (fun _ : W => if c = 0 then a else b) =
        fun w : W => S.gDeriv (S.codeWord c (w : List ι)) := by
      funext w
      rcases zmod_two_cases c with rfl | rfl
      · simp [(hdiagW w).2.1]
      · simp [(hdiagW w).2.2]
    have e2 : (fun w : W => T.trans (w, c)) =
        fun w : W => S.gWord (S.codeWord c (w : List ι)) 0 := by
      funext w
      rw [hT_def, subsystem_trans]
    rw [e1, e2]
    exact key
  have hdim := hT.marginal_isExactDim hkk c hfreec
  rw [Fintype.card_coe] at hdim
  exact IsExactDim.le_dimH_coord_image hdim S.isCompact_attractor S.subsystem_attractor_subset

/-! ### The lower bound `\dim_H proj_x(X) ≥ min{1, s}` -/

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- `\dim_H proj_x(X) ≥ min{1, s}` for a tuple containing a proximal diagonal generator, with
`s` the zero of the pressure in `(0, 2)`, along the prose of the proof of `thm:main2`: the
typical families of `exists_typical_words_prose`, before the modifications of cases
`it:main2_threshold` and `it:main2_sosc`, give `\dim_H proj_x(X) ≥ min{1, log #W_n/(-log |a_n|)}`,
and `log #W_n/(-log |a_n|) → -h/λ_1`, which is `min{1, s}` by `eq:diml_min2`.
Depends on: `ShannonMcMillanBreimanStatement`, `MorrisShmerkinLyapunov`,
`EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, `KittleKoglerDimension`. -/
theorem le_dimH_coord_zero_normalised (hsmb : ShannonMcMillanBreimanStatement.{u})
    (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hkk : KittleKoglerDimension.{u})
    (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal) (hfree : S.NoExactOverlaps)
    {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) (hP : S.pressure s = 0) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) :
    ENNReal.ofReal (min 1 s) ≤ dimH (coord 0 '' S.attractor) := by
  have : Nonempty ι := nonempty_of_measure μ
  have hl := hms S hrot hdiag hs0 hs2 μ hinv heq
  have hl1 := S.lyapunov₁_neg hinv
  have henergy : entropy μ + energy (S.lyapunov₁ μ) (S.lyapunov₂ μ) s = 0 := by
    rw [← heq.pressure_eq hinv hs0.le, hP]
  obtain ⟨n, W, a, b, -, hnpos, hWne, hWn, hH, ha, -⟩ :=
    S.exists_typical_words_prose hsmb hfk hfjj hrot hdiag hs0 hs2 μ hinv heq
  -- the lower bound for each family
  have hle : ∀ m, ENNReal.ofReal (min 1 (Real.log (W m).card / -Real.log |a m|)) ≤
      dimH (coord 0 '' S.attractor) := fun m => by
    have key := S.le_dimH_coord_of_family hkk hfree (hWne m) (hnpos m) (hWn m) 0
    rwa [ite_eq_left rfl] at key
  -- the limit `log #W_n / (-log |a_n|) → -h/λ_1`
  have ha' : Tendsto (fun m => -Real.log |a m| / n m) atTop (𝓝 (-S.lyapunov₁ μ)) := by
    simpa only [neg_div] using ha.neg
  have hdiv : Tendsto (fun m => Real.log (W m).card / n m / (-Real.log |a m| / n m)) atTop
      (𝓝 (entropy μ / -S.lyapunov₁ μ)) :=
    hH.div ha' (neg_pos.2 hl1).ne'
  have hlim : Tendsto (fun m => min 1 (Real.log (W m).card / -Real.log |a m|)) atTop
      (𝓝 (min 1 (entropy μ / -S.lyapunov₁ μ))) := by
    refine tendsto_const_nhds.min (hdiv.congr fun m => ?_)
    have hm : (n m : ℝ) ≠ 0 := by exact_mod_cast (hnpos m).ne'
    rw [div_div_div_cancel_right₀ hm]
  rw [← min_one_div_neg_eq hl.le hl1 hs2 henergy]
  exact le_of_tendsto (ENNReal.continuous_ofReal.tendsto _ |>.comp hlim)
    (Eventually.of_forall fun m => hle m)

/-- `\dim_H proj_x(X) ≥ min{1, s}` for every proximal tuple, with `s` the zero of the pressure
in `(0, 2)`: the reduction to a proximal diagonal generator through
`thm:two-block-normalisation`, with the absence of exact overlaps passing to the second
iterate, as in the proof of `thm:main2`.
Depends on: `ShannonMcMillanBreimanStatement`, `MorrisShmerkinLyapunov`,
`EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, `KittleKoglerDimension`. -/
theorem le_dimH_coord_zero_of_pressure (hsmb : ShannonMcMillanBreimanStatement.{u})
    (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hkk : KittleKoglerDimension.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal) (hfree : S.NoExactOverlaps) {s : ℝ}
    (hs0 : 0 < s) (hs2 : s < 2) (hP : S.pressure s = 0) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) :
    ENNReal.ofReal (min 1 s) ≤ dimH (coord 0 '' S.attractor) := by
  have := nonempty_of_measure μ
  rcases hprox.hasProximalDiagonal_or_sq with h | h
  · exact S.le_dimH_coord_zero_normalised hsmb hms hfk hfjj hkk hrot h hfree hs0 hs2 hP μ hinv
      heq
  · have key := S.sq.le_dimH_coord_zero_normalised hsmb hms hfk hfjj hkk
      (S.sq_withRotations hrot) h hfree.sq hs0 hs2
      (by rw [S.pressure_sq hs0.le, hP, mul_zero]) (μ.map group)
      (measurePreserving_shift_map_group hinv) (heq.map_group hinv hs0.le)
    rwa [S.attractor_sq] at key

/-! ### The dimension of both projections -/

variable [Nonempty ι]

/-- The coordinate projections in the proof of `thm:main2`: for a proximal box-like self-affine
set `X` with rotations whose projective system has no exact overlaps and `dimaff(X) < 2`, both
coordinate projections of `X` have Hausdorff dimension `min{1, dimaff(X)}`. The lower bound for
`proj_x(X)` comes from the typical families and Kittle–Kogler, that for `proj_y(X)` from the
affine copy of `proj_x(X)` inside it, and the upper bound from the Lipschitz images of `X`. An
equilibrium state at `s = dimaff(X)`, from `exists_isEquilibriumState`, provides the typical
families; the conclusion does not refer to it.
Depends on: `ShannonMcMillanBreimanStatement`, `MorrisShmerkinLyapunov`,
`EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, `KittleKoglerDimension`. -/
theorem dimH_coord_image_eq (hsmb : ShannonMcMillanBreimanStatement.{u})
    (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hkk : KittleKoglerDimension.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal) (hfree : S.NoExactOverlaps)
    (h2 : S.dimaff < 2) (c : ZMod 2) :
    dimH (coord c '' S.attractor) = ENNReal.ofReal (min 1 S.dimaff) := by
  have := S.nontrivial_of_withRotations hrot
  obtain ⟨μ, hprob, hinv, heq⟩ := S.exists_isEquilibriumState S.dimaff_nonneg
  refine le_antisymm ((dimH_le_upperBoxDim _).trans (S.upperBoxDim_coord_le_min c)) ?_
  rw [S.dimH_coord_eq hrot.2 c 0]
  exact S.le_dimH_coord_zero_of_pressure hsmb hms hfk hfjj hkk hrot hprox hfree S.dimaff_pos h2
    S.pressure_dimaff μ hinv heq

/-- The coordinate projections in the proof of `thm:main2`: both have lower Minkowski dimension
`min{1, dimaff(X)}`, from `\dim_H ≤ \underline{\dim}_M ≤ \overline{\dim}_M`.
Depends on: `ShannonMcMillanBreimanStatement`, `MorrisShmerkinLyapunov`,
`EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, `KittleKoglerDimension`. -/
theorem lowerBoxDim_coord_image_eq (hsmb : ShannonMcMillanBreimanStatement.{u})
    (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hkk : KittleKoglerDimension.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal) (hfree : S.NoExactOverlaps)
    (h2 : S.dimaff < 2) (c : ZMod 2) :
    lowerBoxDim (coord c '' S.attractor) = ENNReal.ofReal (min 1 S.dimaff) := by
  have := S.nontrivial_of_withRotations hrot
  refine le_antisymm ((lowerBoxDim_le_upperBoxDim _).trans (S.upperBoxDim_coord_le_min c)) ?_
  rw [← S.dimH_coord_image_eq hsmb hms hfk hfjj hkk hrot hprox hfree h2 c]
  exact dimH_le_lowerBoxDim _

/-- The coordinate projections in the proof of `thm:main2`: both have upper Minkowski dimension
`min{1, dimaff(X)}`.
Depends on: `ShannonMcMillanBreimanStatement`, `MorrisShmerkinLyapunov`,
`EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, `KittleKoglerDimension`. -/
theorem upperBoxDim_coord_image_eq (hsmb : ShannonMcMillanBreimanStatement.{u})
    (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hkk : KittleKoglerDimension.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal) (hfree : S.NoExactOverlaps)
    (h2 : S.dimaff < 2) (c : ZMod 2) :
    upperBoxDim (coord c '' S.attractor) = ENNReal.ofReal (min 1 S.dimaff) := by
  have := S.nontrivial_of_withRotations hrot
  refine le_antisymm (S.upperBoxDim_coord_le_min c) ?_
  rw [← S.dimH_coord_image_eq hsmb hms hfk hfjj hkk hrot hprox hfree h2 c]
  exact dimH_le_upperBoxDim _

/-- Fraser's numbers `s_1 = s_2` of `sec:affinity_dim` for a proximal box-like self-affine set
with rotations whose projective system has no exact overlaps and `dimaff(X) < 2`: both
coordinate projections of `X` have Minkowski dimension `min{1, dimaff(X)}` (proof of
`thm:main2`, used in `sec:intro_fraser`).
Depends on: `ShannonMcMillanBreimanStatement`, `MorrisShmerkinLyapunov`,
`EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, `KittleKoglerDimension`. -/
theorem projDim_eq_min (hsmb : ShannonMcMillanBreimanStatement.{u})
    (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hkk : KittleKoglerDimension.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal) (hfree : S.NoExactOverlaps)
    (h2 : S.dimaff < 2) (c : ZMod 2) : S.projDim c = min 1 S.dimaff := by
  rw [projDim, S.upperBoxDim_coord_image_eq hsmb hms hfk hfjj hkk hrot hprox hfree h2 c,
    ENNReal.toReal_ofReal (le_min zero_le_one S.dimaff_nonneg)]

/-! ### Without literature hypotheses -/

/-- `dimH_coord_image_eq` with the five statements it depends on discharged by the library
theorems `shannonMcMillanBreiman`, `morrisShmerkinLyapunov_holds`, `equilibriumGibbs`,
`fraserJordanJurgaDecomposition_holds` and `kittleKoglerDimension_holds`: for a proximal
box-like self-affine set `X` with rotations whose projective system has no exact overlaps and
`dimaff(X) < 2`, both coordinate projections of `X` have Hausdorff dimension
`min{1, dimaff(X)}` (proof of `thm:main2`). -/
theorem dimH_coord_image_eq_proved (hrot : S.WithRotations) (hprox : S.Proximal)
    (hfree : S.NoExactOverlaps) (h2 : S.dimaff < 2) (c : ZMod 2) :
    dimH (coord c '' S.attractor) = ENNReal.ofReal (min 1 S.dimaff) :=
  S.dimH_coord_image_eq shannonMcMillanBreiman morrisShmerkinLyapunov_holds equilibriumGibbs
    fraserJordanJurgaDecomposition_holds kittleKoglerDimension_holds hrot hprox hfree h2 c

/-- `projDim_eq_min` with the five statements it depends on discharged by the library theorems:
both coordinate projections of `X` have Minkowski dimension `min{1, dimaff(X)}` (proof of
`thm:main2`, used in `sec:intro_fraser`). -/
theorem projDim_eq_min_proved (hrot : S.WithRotations) (hprox : S.Proximal)
    (hfree : S.NoExactOverlaps) (h2 : S.dimaff < 2) (c : ZMod 2) :
    S.projDim c = min 1 S.dimaff :=
  S.projDim_eq_min shannonMcMillanBreiman morrisShmerkinLyapunov_holds equilibriumGibbs
    fraserJordanJurgaDecomposition_holds kittleKoglerDimension_holds hrot hprox hfree h2 c

end System

end BoxLike
