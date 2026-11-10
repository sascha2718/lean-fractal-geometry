module

/-
The assembled proof of `thm:main2` in `sec:dimension_result_proof` along the prose:

* the case `s ≥ 2`, where `thm:main_extended` under the strong open set condition gives `s = 2`
  and `dim(π_*μ) = 2`;
* the reduction to a proximal diagonal generator through `thm:two-block-normalisation`;
* the typical families of `BoxLike/MainTwoProse/TypicalWordsSMB.lean`: Shannon–McMillan–Breiman,
  Birkhoff, the return to the horizontal orientation, the pigeonhole of
  `BoxLike/MainTwoProse/Pigeonhole.lean`;
* the genuinely diagonal subsystems of `BoxLike/MainTwoProse/DiagonalSubsystem.lean` with their
  Bernoulli measures `ν_n`, and Kittle–Kogler for the coordinate projections of `(π_n)_*ν_n`;
* the modifications of the families for `1 < s < 2`: the trimming to `min{#W_n, ⌊|b_n|⁻¹⌋}`
  words under `it:main2_threshold`, or the prefix `v` with `φ_v(X) ⊆ U` under `it:main2_sosc`;
* the conditional entropies `q_{x,n}`, `q_{y,n}`, `q_n` of
  `BoxLike/MainTwoProse/SubsystemEntropies.lean`, written `h_1(ν_n)`,
  `H_{ν_n}(𝒫 | \widehat{ξ_1^⊥})` and `h_2(ν_n)` in the manuscript: the scalar Ledrappier–Young
  formula of `BoxLike/MainTwoProse/ScalarFeng.lean`, `0 ≤ q_n ≤ q_{y,n} = 0` by the monotonicity
  of `BoxLike/MainTwoProse/EntropyThreshold.lean`, strong separation and unique coding of
  `BoxLike/MainTwoProse/OpenSetBranch.lean`, and the independence of the past and the future of
  `BoxLike/MainTwoProse/PastIndependence.lean`;
* the planar Ledrappier–Young formula `thm:feng1`, the limit
  `dim((π_n)_*ν_n) → \dim_L(𝖠, μ) = s`, and the upper bound `eq:hausdorff_affinity_upper_bound`.

The manuscript settles `s ≤ 1` from the projection bound of
`BoxLike/MainTwoProse/ProjectionDimension.lean` and Falconer's upper bound; the proof below
treats `0 < s < 2` uniformly through the dimension of `(π_n)_*ν_n`.

* `System.IsHomDiag.isExactDim_map_proj`:
  `dim((π_n)_*ν_n) = d_{x,n} + (log #W_n + d_{x,n} log |a_n|) / (-log |b_n|)`.
* `System.isHomDiag_subsystem`: the subsystem of the words `v w`, `w ∈ W_n`, is homogeneous
  diagonal.
* `System.le_dimH_attractor_of_family`: `\dim_H X ≥ dim((π_n)_*ν_n)` for one family.
* `System.main2_prose_normalised`, `System.main2_prose_of_pressure`, `System.main2_prose_lt_two`:
  the case `0 < s < 2`.
* `System.main2_prose`: `thm:main2` with the hypotheses the proof uses: the statements
  `ShannonMcMillanBreimanStatement`, `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`,
  `FraserJordanJurgaDecomposition` and `KittleKoglerDimension`, which the library proves, and the
  literature hypothesis `FengLedrappierYoung`.
* `System.main2_prose_all`: `thm:main2` with the type of `System.main2_noExactOverlaps_all` and
  the hypothesis `hsmb`.
* `System.main2_noExactOverlaps_prose`: `thm:main2` with exactly the type of
  `System.main2_noExactOverlaps_all`, the Shannon–McMillan–Breiman theorem being the library
  theorem `shannonMcMillanBreiman`.
-/
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.MainTwoEndpoint
public import BoxLike.MainTwoProse.EntropyThreshold
public import BoxLike.MainTwoProse.OpenSetBranch
public import BoxLike.MainTwoProse.SubsystemEntropies
public import BoxLike.MainTwoProse.TypicalWordsSMB
public import BoxLike.ShannonMcMillanBreiman

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set

universe u

/-! ### The dimension of `ν_n` -/

namespace System.IsHomDiag

variable {κ : Type u} [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ] [Nonempty κ]
  {T : System κ} {a b : ℝ} (hT : T.IsHomDiag a b)
include hT

/-- The dimension of `(π_n)_*ν_n` in the proof of `thm:main2`:
`dim((π_n)_*ν_n) = (q_{x,n} - log #W_n) / log |a_n| + (q_n - q_{x,n}) / log |b_n|`, which is
`d_{x,n} + (log #W_n + d_{x,n} log |a_n|) / (-log |b_n|)`. The conditional entropy `q_n` of the
first symbol given the planar point vanishes, by `0 ≤ q_n ≤ q_{y,n} = 0` when
`log #W_n ≤ -log |b_n|` and by unique coding under strong separation; the scalar
Ledrappier–Young formula gives `q_{x,n} = log #W_n + d_{x,n} log |a_n|`; the past and future of
`ν_n` are independent and `V^1` is the vertical axis, so the entropies of the planar
Ledrappier–Young formula `thm:feng1` are
`h_0 = log #W_n`, `h_1 = q_{x,n}` and `h_2 = q_n`, with `λ_1 = log |a_n|`, `λ_2 = log |b_n|`.
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem isExactDim_map_proj (hly : FengLedrappierYoung.{u}) (hkk : KittleKoglerDimension.{u})
    (hab : |b| < |a|)
    (hfreex : Function.Injective (simWord (fun _ : κ => a) (fun k => T.trans (k, 0))))
    (hfreey : Function.Injective (simWord (fun _ : κ => b) (fun k => T.trans (k, 1))))
    (hzero : Real.log (Fintype.card κ) ≤ -Real.log |b| ∨ T.StrongSeparation) :
    IsExactDim ((uniformBernoulli κ).map T.proj)
      (subsystemDim (Real.log (Fintype.card κ)) (-Real.log |a|) (-Real.log |b|)) := by
  have hinv := measurePreserving_shift_uniformBernoulli (κ := κ) 1
  have hq : T.condEntropyPoint (uniformBernoulli κ) = 0 := by
    rcases hzero with hH | hsep
    · exact hT.condEntropyPoint_eq_zero_of_le hly hkk hab.le hfreey hH
    · exact hsep.condEntropyPoint_eq_zero _
  have hLY := hly T (uniformBernoulli κ) hinv ergodic_shift_uniformBernoulli
    (hT.lyapunov₂_lt_lyapunov₁ hab hinv)
  rw [hT.dimEntropy_zero hab.le, hT.dimEntropy_one_eq_condEntropyCoord hab.le,
    hT.dimEntropy_two_eq_condEntropyPoint hab.le,
    hT.condEntropyCoord_zero_eq_scalar hly hkk hab.le hfreex, hq,
    hT.lyapunov₁_eq hab.le hinv, hT.lyapunov₂_eq hab.le hinv] at hLY
  rw [subsystemDim_eq_ledrappierYoung hT.log_abs_a_neg.ne hT.log_abs_b_neg.ne]
  exact hLY

end System.IsHomDiag

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)

/-! ### The subsystem of one family -/

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The subsystem of the words `v w`, `w ∈ W`, of the proof of `thm:main2` is homogeneous
diagonal with the entries `g'_{v,0} a` and `g'_{v,1} b`, when `A_v` is diagonal and every
`w ∈ W` has the planar matrix `diag(a, b)`. -/
theorem isHomDiag_subsystem {v : List ι} (hv : S.oWord v = 0) {W : Finset (List ι)} {a b : ℝ}
    (hWm : ∀ w ∈ W, S.matWord w = boxMat 0 a b)
    (hw : ∀ w : W, v ++ (w : List ι) ≠ []) :
    (S.subsystem (fun w : W => v ++ (w : List ι)) hw).IsHomDiag
      (S.gDeriv (S.codeWord 0 v) * a) (S.gDeriv (S.codeWord 1 v) * b) := by
  have hdiagW : ∀ w : W, S.oWord w = 0 ∧ S.gDeriv (S.codeWord 0 w) = a ∧
      S.gDeriv (S.codeWord 1 w) = b := fun w =>
    (S.matWord_eq_boxMat_zero_iff _ _ _).1 (hWm w w.2)
  refine ⟨fun w => ?_, fun w => ?_, fun w => ?_⟩
  · simp [oWord_append, hv, (hdiagW w).1]
  · simp [codeWord_append, gDeriv_append, hv, (hdiagW w).2.1]
  · simp [codeWord_append, gDeriv_append, hv, (hdiagW w).2.2]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The lower bound `\dim_H X ≥ dim((π_n)_*ν_n)` for one family `W` of diagonal planar words of
length `n` with the common matrix `diag(a, b)`, prefixed by the diagonal word `v`, in either case of
the proof of `thm:main2`: the trimmed family with `log #W_n ≤ -log |b_n|`, or a feasible open set
`U ⊇ φ_v(X)`, in which case the subsystem satisfies the strong separation condition. The
coordinate maps of the subsystem generate free semigroups, since the projective system of `Φ`
has no exact overlaps, and `ν_n` is carried by the attractor of the subsystem, which lies in
`X`.
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem le_dimH_attractor_of_family (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) [Nonempty ι] (hfree : S.NoExactOverlaps) {v : List ι}
    (hv : S.oWord v = 0) {W : Finset (List ι)} (hW : W.Nonempty) {n : ℕ} (hn : 0 < n)
    {a b : ℝ} (hWn : ∀ w ∈ W, w.length = n ∧ S.matWord w = boxMat 0 a b)
    (hab : |S.gDeriv (S.codeWord 1 v) * b| < |S.gDeriv (S.codeWord 0 v) * a|)
    (hzero : Real.log W.card ≤ -Real.log |S.gDeriv (S.codeWord 1 v) * b| ∨
      ∃ U : Set (ℝ × ℝ), IsOpen U ∧ U.Nonempty ∧ (∀ i, S.phi i '' U ⊆ U) ∧
        (Pairwise fun i j => Disjoint (S.phi i '' U) (S.phi j '' U)) ∧
        S.phiWord v '' S.attractor ⊆ U) :
    ENNReal.ofReal (subsystemDim (Real.log W.card) (-Real.log |S.gDeriv (S.codeWord 0 v) * a|)
      (-Real.log |S.gDeriv (S.codeWord 1 v) * b|)) ≤ dimH S.attractor := by
  classical
  let _ : MeasurableSpace W := ⊤
  have : MeasurableSingletonClass W := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have : Nonempty W := hW.to_subtype
  set wd : W → List ι := fun w => v ++ (w : List ι) with hwd
  have hlen : ∀ w, (wd w).length = v.length + n := fun w => by
    simp [hwd, (hWn w w.2).1]
  have hwne : ∀ w, wd w ≠ [] := fun w h => by
    have := hlen w
    rw [h] at this
    simp at this
    omega
  set T := S.subsystem wd hwne with hT_def
  have hT : T.IsHomDiag (S.gDeriv (S.codeWord 0 v) * a) (S.gDeriv (S.codeWord 1 v) * b) :=
    S.isHomDiag_subsystem hv (fun w hw => (hWn w hw).2) hwne
  have hdiagW : ∀ w : W, S.oWord w = 0 ∧ S.gDeriv (S.codeWord 0 w) = a ∧
      S.gDeriv (S.codeWord 1 w) = b := fun w =>
    (S.matWord_eq_boxMat_zero_iff _ _ _).1 (hWn w w.2).2
  -- the coordinate maps of the subsystem generate free semigroups
  have hinj : Function.Injective wd := fun w w' h =>
    Subtype.ext (List.append_cancel_left h)
  have hfreec : ∀ c : ZMod 2, Function.Injective
      (simWord (fun _ : W => S.gDeriv (S.codeWord c v) * if c = 0 then a else b)
        (fun w => T.trans (w, c))) := by
    intro c
    have key := hfree.simWord_injective (S := S) c (w := wd)
      (fun w => by rw [hwd, oWord_append, hv, (hdiagW w).1, add_zero])
      (n := v.length + n) (Nat.add_pos_right _ hn) hlen hinj
    have e1 : (fun _ : W => S.gDeriv (S.codeWord c v) * if c = 0 then a else b) =
        fun w : W => S.gDeriv (S.codeWord c (wd w)) := by
      funext w
      rw [hwd, codeWord_append, gDeriv_append, hv, add_zero]
      rcases zmod_two_cases c with rfl | rfl
      · simp [(hdiagW w).2.1]
      · simp [(hdiagW w).2.2]
    have e2 : (fun w : W => T.trans (w, c)) = fun w : W => S.gWord (S.codeWord c (wd w)) 0 := by
      funext w
      rw [hT_def, subsystem_trans]
    rw [e1, e2]
    exact key
  have hfreex := hfreec 0
  have hfreey := hfreec 1
  simp only [ite_true] at hfreex
  simp only [one_ne_zero, ite_false] at hfreey
  -- the two cases for `q_n = 0`
  have hzero' : Real.log (Fintype.card W) ≤ -Real.log |S.gDeriv (S.codeWord 1 v) * b| ∨
      T.StrongSeparation := by
    rcases hzero with h | ⟨U, -, -, hsub, hdisj, hUv⟩
    · left
      rwa [Fintype.card_coe]
    · right
      exact S.subsystem_strongSeparation hsub hdisj hUv (fun w => ⟨_, rfl⟩)
        (fun w w' => by rw [hlen, hlen]) hinj
  have hdim := hT.isExactDim_map_proj hly hkk hab hfreex hfreey hzero'
  rw [Fintype.card_coe] at hdim
  refine hdim.le_dimH ?_
  obtain ⟨r, M, hB⟩ := T.exists_bounds
  rw [Measure.map_apply hB.measurable_proj S.isCompact_attractor.isClosed.measurableSet]
  have hpre : T.proj ⁻¹' S.attractor = univ :=
    eq_univ_of_forall fun x => S.subsystem_attractor_subset ⟨x, rfl⟩
  rw [hpre, measure_univ]
  exact zero_lt_one

/-! ### The theorem below two -/

/-- `thm:main2`, the lower bound `\dim_H X ≥ s` for a tuple containing a proximal diagonal
generator, with `s` the zero of the pressure in `(0, 2)` and the alternative in the entropy form
`h_0(μ) ≤ -λ_2(𝖠, μ)`, along the prose. The typical families come from the Shannon–McMillan–
Breiman theorem (`exists_typical_words_prose`); in the entropy case the families are trimmed to
`min{#W_n, ⌊|b_n|⁻¹⌋}` words; under the strong open set condition every word is prefixed by a
diagonal word `v` with `φ_v(X) ⊆ U`; the lengths and logarithms of the coordinate contraction
ratios change by bounded amounts; `|b_n| < |a_n|` for all large `n`; and `dim((π_n)_*ν_n) → s`.
Depends on: `ShannonMcMillanBreimanStatement`, `MorrisShmerkinLyapunov`,
`EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, `FengLedrappierYoung`,
`KittleKoglerDimension`. -/
theorem main2_prose_normalised (hsmb : ShannonMcMillanBreimanStatement.{u})
    (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal)
    (hfree : S.NoExactOverlaps) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) (hP : S.pressure s = 0)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) (hor : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    ENNReal.ofReal s ≤ dimH S.attractor := by
  classical
  have : Nonempty ι := nonempty_of_measure μ
  obtain ⟨i₁, h₁⟩ := hrot.2
  have hl := hms S hrot hdiag hs0 hs2 μ hinv heq
  have hl1 := S.lyapunov₁_neg hinv
  have henergy : entropy μ + energy (S.lyapunov₁ μ) (S.lyapunov₂ μ) s = 0 := by
    rw [← heq.pressure_eq hinv hs0.le, hP]
  have hdim := lyapDim_eq hl.le hl1 henergy
  have hh2 : entropy μ ≤ -S.lyapunov₁ μ - S.lyapunov₂ μ :=
    (entropy_lt_of_lt_two hl.le hl1 hs2 henergy).le
  obtain ⟨n, W, a, b, hn, hnpos, hWne, hWn, hH, ha, hb⟩ :=
    S.exists_typical_words_prose hsmb hfk hfjj hrot hdiag hs0 hs2 μ hinv heq
  -- the entries `a_m`, `b_m` are non-zero with modulus below one
  have hab0 : ∀ m, a m ≠ 0 ∧ b m ≠ 0 ∧ |b m| < 1 := fun m => by
    obtain ⟨w, hw⟩ := hWne m
    obtain ⟨hw0, hwa, hwb⟩ := (S.matWord_eq_boxMat_zero_iff _ _ _).1 (hWn m w hw).2
    have hne : w ≠ [] := by
      rintro rfl
      have hl0 := (hWn m _ hw).1
      have hp := hnpos m
      simp at hl0
      omega
    refine ⟨hwa ▸ S.gDeriv_ne_zero _, hwb ▸ S.gDeriv_ne_zero _, ?_⟩
    rw [← hwb]
    exact S.abs_gDeriv_lt_one fun h =>
      hne (List.length_eq_zero_iff.1 (by simpa using congrArg List.length h))
  -- eventually `|b_m| < |a_m|`, from `λ_2 < λ_1`: finitely many lengths are discarded
  have hlt : ∀ᶠ m in atTop, |b m| < |a m| := by
    filter_upwards [hb.eventually_lt ha hl] with m hm
    have hnm : (0 : ℝ) < n m := by exact_mod_cast hnpos m
    rw [div_lt_div_iff_of_pos_right hnm] at hm
    exact (Real.log_lt_log_iff (abs_pos.2 (hab0 m).2.1) (abs_pos.2 (hab0 m).1)).1 hm
  have hn0 : ∀ᶠ m in atTop, (n m : ℝ) ≠ 0 := Eventually.of_forall fun m => by
    exact_mod_cast (hnpos m).ne'
  have ha' : Tendsto (fun m => -Real.log |a m| / n m) atTop (𝓝 (-S.lyapunov₁ μ)) := by
    simpa only [neg_div] using ha.neg
  have hb' : Tendsto (fun m => -Real.log |b m| / n m) atTop (𝓝 (-S.lyapunov₂ μ)) := by
    simpa only [neg_div] using hb.neg
  rcases hor with hent | hsosc
  · -- the entropy case: reduce `W_n` to `min{#W_n, ⌊|b_n|⁻¹⌋}` words
    have hfloor : ∀ m, 1 ≤ ⌊|b m|⁻¹⌋₊ := fun m =>
      (Nat.one_le_floor_iff _).2 (one_le_inv_iff₀.2 ⟨abs_pos.2 (hab0 m).2.1, (hab0 m).2.2.le⟩)
    have hex : ∀ m, ∃ W' ⊆ W m, W'.card = min (W m).card ⌊|b m|⁻¹⌋₊ := fun m =>
      Finset.exists_subset_card_eq (min_le_left _ _)
    choose W' hW'sub hW'card using hex
    have hW'ne : ∀ m, (W' m).Nonempty := fun m => by
      rw [← Finset.card_pos, hW'card]
      exact lt_min (Finset.card_pos.2 (hWne m)) (hfloor m)
    have hWpos : ∀ m, (0 : ℝ) < (W m).card := fun m => by
      exact_mod_cast Finset.card_pos.2 (hWne m)
    have hflpos : ∀ m, (0 : ℝ) < ⌊|b m|⁻¹⌋₊ := fun m => by exact_mod_cast hfloor m
    have hle : ∀ᶠ m in atTop, ENNReal.ofReal (subsystemDim (Real.log (W' m).card)
        (-Real.log |a m|) (-Real.log |b m|)) ≤ dimH S.attractor := by
      filter_upwards [hlt] with m hm
      have key := S.le_dimH_attractor_of_family hly hkk hfree (v := []) (by simp) (hW'ne m)
        (hnpos m) (fun w hw => hWn m w (hW'sub m hw)) (by simpa using hm) (Or.inl ?_)
      · simpa using key
      · simp only [codeWord_nil, gDeriv_nil, one_mul]
        rw [← Real.log_inv]
        refine Real.log_le_log (by exact_mod_cast Finset.card_pos.2 (hW'ne m)) ?_
        calc ((W' m).card : ℝ) ≤ ⌊|b m|⁻¹⌋₊ := by
              exact_mod_cast (hW'card m).trans_le (min_le_right _ _)
          _ ≤ |b m|⁻¹ := Nat.floor_le (inv_nonneg.2 (abs_nonneg _))
    -- the limits still hold after the trimming, including when `h = -λ_2`
    have hfl : Tendsto (fun m => Real.log ⌊|b m|⁻¹⌋₊ / n m) atTop (𝓝 (-S.lyapunov₂ μ)) := by
      have hlow : Tendsto (fun m => (-Real.log 2 + -Real.log |b m|) / ((n m : ℝ) + 0)) atTop
          (𝓝 (-S.lyapunov₂ μ)) :=
        tendsto_add_div_add le_rfl hn hb'
      simp only [add_zero] at hlow
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hb'
        (Eventually.of_forall fun m => ?_) (Eventually.of_forall fun m => ?_)
      · have hnm : (0 : ℝ) ≤ n m := Nat.cast_nonneg _
        refine div_le_div_of_nonneg_right ?_ hnm
        have hx : (0 : ℝ) < |b m|⁻¹ := inv_pos.2 (abs_pos.2 (hab0 m).2.1)
        have h2 : |b m|⁻¹ / 2 ≤ ⌊|b m|⁻¹⌋₊ := by
          have := Nat.lt_floor_add_one |b m|⁻¹
          have h1 : (1 : ℝ) ≤ ⌊|b m|⁻¹⌋₊ := by exact_mod_cast hfloor m
          linarith
        have := Real.log_le_log (by positivity) h2
        rwa [Real.log_div hx.ne' two_ne_zero, Real.log_inv, sub_eq_add_neg, add_comm] at this
      · have hnm : (0 : ℝ) ≤ n m := Nat.cast_nonneg _
        refine div_le_div_of_nonneg_right ?_ hnm
        rw [← Real.log_inv]
        exact Real.log_le_log (hflpos m) (Nat.floor_le (inv_nonneg.2 (abs_nonneg _)))
    have hH' : Tendsto (fun m => Real.log (W' m).card / n m) atTop (𝓝 (entropy μ)) := by
      have : (fun m => Real.log (W' m).card / n m) =
          fun m => min (Real.log (W m).card / n m) (Real.log ⌊|b m|⁻¹⌋₊ / n m) := by
        funext m
        rw [hW'card m, Nat.cast_min, log_min_of_pos (hWpos m) (hflpos m),
          min_div_div_right (Nat.cast_nonneg (α := ℝ) (n m))]
      rw [this, ← min_eq_left hent]
      exact hH.min hfl
    exact le_dimH_of_subsystemDim hl hl1 hh2 hdim hn0 hH' ha' hb' hle
  · -- the strong open set case: prefix every word by `v` with `φ_v(X) ⊆ U`, `A_v` diagonal
    obtain ⟨U, hU, hne, hsub, hdisj⟩ := hsosc
    obtain ⟨v₀, hv₀⟩ := S.exists_phiWord_image_subset hU hne
    obtain ⟨v, hv, hUv⟩ : ∃ v : List ι, S.oWord v = 0 ∧ S.phiWord v '' S.attractor ⊆ U := by
      rcases zmod_two_cases (S.oWord v₀) with h | h
      · exact ⟨v₀, h, hv₀⟩
      · refine ⟨v₀ ++ [i₁], by rw [oWord_append, h, oWord_cons, h₁, oWord_nil]; decide, ?_⟩
        rw [phiWord_append', image_comp]
        refine (image_mono ?_).trans hv₀
        simpa using S.image_attractor_subset i₁
    set av := S.gDeriv (S.codeWord 0 v) with hav
    set bv := S.gDeriv (S.codeWord 1 v) with hbv
    have hav0 : av ≠ 0 := S.gDeriv_ne_zero _
    have hbv0 : bv ≠ 0 := S.gDeriv_ne_zero _
    have hUne : U.Nonempty := hne.mono inter_subset_left
    -- the lengths and the logarithms of the ratios change by bounded amounts
    have hχ₁ : Tendsto (fun m => -Real.log |av * a m| / ((n m : ℝ) + v.length)) atTop
        (𝓝 (-S.lyapunov₁ μ)) := by
      have := tendsto_add_div_add (c := -Real.log |av|) (Nat.cast_nonneg v.length) hn ha'
      refine this.congr fun m => ?_
      rw [abs_mul, Real.log_mul (abs_ne_zero.2 hav0) (abs_ne_zero.2 (hab0 m).1), neg_add]
    have hχ₂ : Tendsto (fun m => -Real.log |bv * b m| / ((n m : ℝ) + v.length)) atTop
        (𝓝 (-S.lyapunov₂ μ)) := by
      have := tendsto_add_div_add (c := -Real.log |bv|) (Nat.cast_nonneg v.length) hn hb'
      refine this.congr fun m => ?_
      rw [abs_mul, Real.log_mul (abs_ne_zero.2 hbv0) (abs_ne_zero.2 (hab0 m).2.1), neg_add]
    have hH' : Tendsto (fun m => Real.log (W m).card / ((n m : ℝ) + v.length)) atTop
        (𝓝 (entropy μ)) := by
      have := tendsto_add_div_add (c := 0) (Nat.cast_nonneg v.length) hn hH
      simpa only [zero_add] using this
    have hn0' : ∀ᶠ m in atTop, ((n m : ℝ) + v.length) ≠ 0 := Eventually.of_forall fun m => by
      have : (0 : ℝ) < n m := by exact_mod_cast hnpos m
      positivity
    have hlt' : ∀ᶠ m in atTop, |bv * b m| < |av * a m| := by
      filter_upwards [hχ₁.eventually_lt hχ₂ (neg_lt_neg hl)] with m hm
      have hnm : (0 : ℝ) < (n m : ℝ) + v.length := by
        have : (0 : ℝ) < n m := by exact_mod_cast hnpos m
        positivity
      rw [div_lt_div_iff_of_pos_right hnm, neg_lt_neg_iff] at hm
      exact (Real.log_lt_log_iff (abs_pos.2 (mul_ne_zero hbv0 (hab0 m).2.1))
        (abs_pos.2 (mul_ne_zero hav0 (hab0 m).1))).1 hm
    have hle : ∀ᶠ m in atTop, ENNReal.ofReal (subsystemDim (Real.log (W m).card)
        (-Real.log |av * a m|) (-Real.log |bv * b m|)) ≤ dimH S.attractor := by
      filter_upwards [hlt'] with m hm
      exact S.le_dimH_attractor_of_family hly hkk hfree hv (hWne m) (hnpos m) (hWn m) hm
        (Or.inr ⟨U, hU, hUne, hsub, hdisj, hUv⟩)
    exact le_dimH_of_subsystemDim hl hl1 hh2 hdim hn0' hH' hχ₁ hχ₂ hle

/-- `thm:main2` with `s` the zero of the pressure in `(0, 2)` and the alternative in the entropy
form, for every proximal tuple: the reduction to a proximal diagonal generator through
`thm:two-block-normalisation`, with the absence of exact overlaps passing to the second
iterate, and the upper bound `eq:hausdorff_affinity_upper_bound`.
Depends on: `ShannonMcMillanBreimanStatement`, `MorrisShmerkinLyapunov`,
`EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, `FengLedrappierYoung`,
`KittleKoglerDimension`. -/
theorem main2_prose_of_pressure (hsmb : ShannonMcMillanBreimanStatement.{u})
    (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (hrot : S.WithRotations) (hprox : S.Proximal)
    (hfree : S.NoExactOverlaps) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) (hP : S.pressure s = 0)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) (hor : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    dimH S.attractor = ENNReal.ofReal s := by
  have := nonempty_of_measure μ
  have hd : S.dimaff = s := S.dimaff_eq hs0.le hP
  refine le_antisymm ?_ ?_
  · have := S.dimH_attractor_le
    rwa [hd, min_eq_right hs2.le] at this
  rcases hprox.hasProximalDiagonal_or_sq with h | h
  · exact S.main2_prose_normalised hsmb hms hfk hfjj hly hkk hrot h hfree hs0 hs2 hP μ hinv heq
      hor
  · have e2 := S.lyapunov₂_sq_map_group (S.tendsto_lyapunov₂ hinv)
    have hor2 : entropy (μ.map group) ≤ -S.sq.lyapunov₂ (μ.map group) ∨ S.sq.StrongOpenSet := by
      rcases hor with h' | h'
      · left
        rw [entropy_map_group hinv, e2]
        linarith
      · exact Or.inr (StrongOpenSet.sq S h')
    have key := S.sq.main2_prose_normalised hsmb hms hfk hfjj hly hkk (S.sq_withRotations hrot) h
      hfree.sq hs0 hs2 (by rw [S.pressure_sq hs0.le, hP, mul_zero]) (μ.map group)
      (measurePreserving_shift_map_group hinv) (heq.map_group hinv hs0.le) hor2
    rwa [S.attractor_sq] at key

/-- `thm:main2` in the case `dimaff(X) < 2`, along the prose: the equivalence
`s ≤ 2 - λ_1/λ_2 ⟺ h_0(μ) ≤ -λ_2` from `eq:diml_min2` and `eq:simple_lyapunov`, then
`main2_prose_of_pressure`.
Depends on: `ShannonMcMillanBreimanStatement`, `MorrisShmerkinLyapunov`,
`EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, `FengLedrappierYoung`,
`KittleKoglerDimension`. -/
theorem main2_prose_lt_two (hsmb : ShannonMcMillanBreimanStatement.{u})
    (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal)
    (hfree : S.NoExactOverlaps) (h2 : S.dimaff < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    dimH S.attractor = ENNReal.ofReal S.dimaff := by
  have := S.nontrivial_of_withRotations hrot
  have hs0 := S.dimaff_pos
  have hl := S.simple_lyapunov hms hrot hprox hs0 h2 μ hinv heq
  have hl1 := S.lyapunov₁_neg hinv
  have henergy : entropy μ + energy (S.lyapunov₁ μ) (S.lyapunov₂ μ) S.dimaff = 0 := by
    rw [← heq.pressure_eq hinv hs0.le, S.pressure_dimaff]
  exact S.main2_prose_of_pressure hsmb hms hfk hfjj hly hkk hrot hprox hfree hs0 h2
    S.pressure_dimaff μ hinv heq (hor.imp (entropy_le_iff hl hl1 h2 henergy).2 id)

/-! ### The theorem -/

variable [Nonempty ι]

/-- `thm:main2`, along the prose. Let `X` be a proximal box-like self-affine set with rotations
whose projective system has no exact overlaps, and let `μ` be the `s`-equilibrium state for
`s = dimaff(X)`. If `dimaff(X) ≤ 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)`, or if `X` satisfies the strong open
set condition, then `\dim_H X = dimaff(X)`. For `s ≥ 2` the threshold alternative is impossible
and the determinant argument of `thm:main_extended` under the strong open set condition gives
`s = 2` and `dim(π_*μ) = 2`, so `\dim_H X = 2` since `π_*μ` is carried by `X ⊆ ℝ²`; for
`0 < s < 2` the finite diagonal subsystems give the lower bound and
`eq:hausdorff_affinity_upper_bound` the upper bound.
Depends on: `ShannonMcMillanBreimanStatement`, `MorrisShmerkinLyapunov`,
`EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`, `FengLedrappierYoung`,
`KittleKoglerDimension`. -/
theorem main2_prose (hsmb : ShannonMcMillanBreimanStatement.{u})
    (hms : MorrisShmerkinLyapunov.{u}) (hfk : EquilibriumGibbsStatement.{u})
    (hfjj : FraserJordanJurgaDecomposition.{u}) (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (hrot : S.WithRotations) (hprox : S.Proximal)
    (hfree : S.NoExactOverlaps) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    dimH S.attractor = ENNReal.ofReal S.dimaff := by
  rcases lt_or_ge S.dimaff 2 with h2 | h2
  · exact S.main2_prose_lt_two hsmb hms hfk hfjj hly hkk hrot hprox hfree h2 μ hinv heq hor
  · have h1neg := S.lyapunov₁_neg hinv
    have h2neg := (S.lyapunov₂_le_lyapunov₁ hinv).trans_lt h1neg
    have hratio : 0 < S.lyapunov₁ μ / S.lyapunov₂ μ := div_pos_of_neg_of_neg h1neg h2neg
    -- `2 - λ_1 / λ_2 < 2 ≤ s`, so the strong open set condition holds
    have hsosc : S.StrongOpenSet := hor.resolve_left (by linarith)
    -- the determinant argument of `thm:main_extended`: `s = 2` and `dim(π_*μ) = 2`
    have hs : S.dimaff = 2 := hsosc.dimaff_eq_two S h2
    have hdim := S.main_extended_ge_two hsosc h2 S.pressure_dimaff μ hinv heq
    -- `π_*μ` is carried by `X ⊆ ℝ²`
    have hlow := S.le_dimH_attractor hdim
    have hup : dimH S.attractor ≤ 2 := by
      calc dimH S.attractor ≤ dimH (univ : Set (ℝ × ℝ)) := dimH_mono (subset_univ _)
        _ = 2 := by
          rw [Real.dimH_univ_eq_finrank, Module.finrank_prod, Module.finrank_self]
          norm_num
    have h2' : ENNReal.ofReal 2 = 2 := by simp
    rw [hs, h2']
    rw [h2'] at hlow
    exact le_antisymm hup hlow

/-- `thm:main2` with the type of `System.main2_noExactOverlaps_all` and the additional
hypothesis `hsmb : ShannonMcMillanBreimanStatement.{u}`, proved along the prose by
`main2_prose`. The hypotheses `FengInfoSumBar` and `FengLedrappierYoungBar` of the type are not
used: the scalar Ledrappier–Young formula for the diagonal subsystems comes from the planar
statement `FengLedrappierYoung`, and `q_n = 0` in the entropy case from the monotonicity of the
conditional entropy. -/
theorem main2_prose_all (hsmb : ShannonMcMillanBreimanStatement.{u})
    (hms : BoxLike.MorrisShmerkinLyapunov.{u})
    (hfk : BoxLike.EquilibriumGibbsStatement.{u})
    (hfjj : BoxLike.FraserJordanJurgaDecomposition.{u})
    (_hfib : BoxLike.FengInfoSumBar.{u}) (hly : BoxLike.FengLedrappierYoung.{u})
    (_hlyb : BoxLike.FengLedrappierYoungBar.{u}) (hkk : BoxLike.KittleKoglerDimension.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal) (hfree : S.NoExactOverlaps)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (BoxLike.shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    dimH S.attractor = ENNReal.ofReal S.dimaff :=
  S.main2_prose hsmb hms hfk hfjj hly hkk hrot hprox hfree μ hinv heq hor

/-- `thm:main2` along the prose, with exactly the type of `System.main2_noExactOverlaps_all`: the
hypothesis `hsmb` of `main2_prose_all` is discharged by the library theorem
`shannonMcMillanBreiman`. The hypotheses `FengInfoSumBar` and `FengLedrappierYoungBar` of the type
are not used.
Depends on: `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`,
`FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem main2_noExactOverlaps_prose (hms : BoxLike.MorrisShmerkinLyapunov.{u})
    (hfk : BoxLike.EquilibriumGibbsStatement.{u})
    (hfjj : BoxLike.FraserJordanJurgaDecomposition.{u})
    (hfib : BoxLike.FengInfoSumBar.{u}) (hly : BoxLike.FengLedrappierYoung.{u})
    (hlyb : BoxLike.FengLedrappierYoungBar.{u}) (hkk : BoxLike.KittleKoglerDimension.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal) (hfree : S.NoExactOverlaps)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (BoxLike.shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    dimH S.attractor = ENNReal.ofReal S.dimaff :=
  S.main2_prose_all shannonMcMillanBreiman hms hfk hfjj hfib hly hlyb hkk hrot hprox hfree μ hinv
    heq hor

end System

end BoxLike
