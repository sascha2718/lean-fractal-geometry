module

/-
`thm:main2` under the absence of projective exact overlaps, by finite diagonal subsystems:
the assembly of the proof of `sec:dimension_result_proof` (tex lines 3451 to 3569), its
consequences for the dimension chain of the introduction (tex lines 509 to 515), and the
application to the example of `prop:ssc_no_overlap_not_pesc` (tex lines 1447 to 1450).

The typical words of `BoxLike/TypicalWords.lean` give families `W_n` of words of a common
length with a common diagonal linear part `diag(a_n, b_n)` and the asymptotics
`log #W_n ∼ n h_0(μ)`, `log |a_n| ∼ n λ_1(𝖠, μ)` and `log |b_n| ∼ n λ_2(𝖠, μ)`. In the entropy
case `h_0(μ) ≤ -λ_2(𝖠, μ)` the family is trimmed to
`min{#W_n, ⌊|b_n|⁻¹⌋}` words; under the strong open set condition every word is prefixed by a
word `v` with `φ_v(X) ⊆ U`. The subsystem of `BoxLike/Subsystem.lean` with the extra
anti-diagonal word of zero weight is a homogeneous system in the sense of
`BoxLike/HomogeneousSubsystem.lean`, and `BoxLike/SubsystemEntropy.lean` gives the exact
dimension `subsystemDim (log #W_n, -log |a_n|, -log |b_n|)` of its Bernoulli measure. The mass
distribution principle bounds `\dim_H X` from below by these dimensions, which tend to
`\dim_L(𝖠, μ) = s`; the upper bound is Falconer's.

* `System.antiWord`, `System.subWords`: the words `v w`, `w ∈ W`, and the anti-diagonal word
  `v i_1 i_0^{n-1}` of the same length.
* `System.le_dimH_attractor_of_words`: the lower bound `\dim_H X ≥ dim((π_n)_*ν_n)` for one family.
* `tendsto_add_div_add`, `le_dimH_of_subsystemDim`: the passage to the limit (tex line 3557
  to 3737).
* `System.main2_noExactOverlaps_normalised`: the lower bound for a tuple containing a proximal
  diagonal generator; `System.main2_noExactOverlaps_of_pressure`: for every proximal tuple,
  through `thm:two-block-normalisation`.
* `System.main2_noExactOverlaps`: `thm:main2`.
* `System.dim_chain_noExactOverlaps`, `System.dimmaff_eq_dimaff_noExactOverlaps`: the chain
  `\dim_H X = \dim_P X = \dim_M X = dimaff(X)` and the squeeze `dimmaff(X) = dimaff(X)` under
  the hypotheses of `thm:main2`.
* `System.dimaff_lt_of_pressure_neg`, `System.dimaff_lt_two_of_sum_abs_det_lt_one`,
  `NoOverlap.dimH_eq_dimaff`: the example of `prop:ssc_no_overlap_not_pesc` has
  `dimaff(X) < 2` and `\dim_H X = dimaff(X)`.
-/
public import BoxLike.EquilibriumExistence
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.FraserChain
public import BoxLike.General
public import BoxLike.MainTwo
public import BoxLike.NoOverlapExample
public import BoxLike.PressureLarge
public import BoxLike.Subsystem
public import BoxLike.SubsystemEntropy
public import BoxLike.TypicalWords

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set

universe u

/-! ### The passage to the limit -/

/-- Bounded perturbations of the data and of the lengths do not change the limits of the
ratios (tex lines 3511 to 3513). -/
theorem tendsto_add_div_add {x : ℕ → ℝ} {n : ℕ → ℕ} {L c d : ℝ} (hd : 0 ≤ d)
    (hn : Tendsto n atTop atTop) (hx : Tendsto (fun m => x m / n m) atTop (𝓝 L)) :
    Tendsto (fun m => (c + x m) / (n m + d)) atTop (𝓝 L) := by
  have h1 : Tendsto (fun m => c / (n m : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat c).comp hn
  have h2 : Tendsto (fun m => (n m : ℝ) / (n m + d)) atTop (𝓝 1) :=
    (tendsto_natCast_div_add_atTop d).comp hn
  have h3 : Tendsto (fun m => (c / n m + x m / n m) * ((n m : ℝ) / (n m + d))) atTop
      (𝓝 ((0 + L) * 1)) := (h1.add hx).mul h2
  rw [zero_add, mul_one] at h3
  refine h3.congr' ?_
  filter_upwards [hn.eventually_ge_atTop 1] with m hm
  have hm' : (0 : ℝ) < n m := by exact_mod_cast hm
  field_simp

/-- The limit step of the proof of `thm:main2` (tex lines 3557 to 3560): lower bounds
`\dim_H X ≥ dim((π_n)_*ν_n)` with `log #W_n / n → h`, `log |a_n| / n → λ_1` and
`log |b_n| / n → λ_2` give `\dim_H X ≥ dim_L = s`. -/
theorem le_dimH_of_subsystemDim {H χ₁ χ₂ : ℕ → ℝ} {n : ℕ → ℝ} {h l₁ l₂ s : ℝ} (hl : l₂ < l₁)
    (hl₁ : l₁ < 0) (hh₂ : h ≤ -l₁ - l₂) (hdim : lyapDim h l₁ l₂ = s)
    (hn : ∀ᶠ m in atTop, n m ≠ 0) (hH : Tendsto (fun m => H m / n m) atTop (𝓝 h))
    (h₁ : Tendsto (fun m => χ₁ m / n m) atTop (𝓝 (-l₁)))
    (h₂ : Tendsto (fun m => χ₂ m / n m) atTop (𝓝 (-l₂))) {D : ENNReal}
    (hle : ∀ᶠ m in atTop, ENNReal.ofReal (subsystemDim (H m) (χ₁ m) (χ₂ m)) ≤ D) :
    ENNReal.ofReal s ≤ D := by
  have hlim := tendsto_subsystemDim (neg_pos.2 hl₁) (neg_pos.2 (hl.trans hl₁)) hH h₁ h₂
  rw [subsystemDim_eq_lyapDim hl hl₁ hh₂, hdim] at hlim
  refine le_of_tendsto (ENNReal.continuous_ofReal.tendsto s |>.comp hlim) ?_
  filter_upwards [hn, hle] with m hm hle
  simpa only [Function.comp_apply, subsystemDim_div _ _ _ hm] using hle

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (S : System ι)

/-! ### The subsystem of a family of words -/

/-- The anti-diagonal word `i_1 i_0^{n-1}` of length `n`, the symbol `none` of the subsystem. -/
def antiWord (i₀ i₁ : ι) (n : ℕ) : List ι := i₁ :: List.replicate (n - 1) i₀

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The anti-diagonal word has length `n`. -/
theorem length_antiWord (i₀ i₁ : ι) {n : ℕ} (hn : 0 < n) : (antiWord i₀ i₁ n).length = n := by
  simp only [antiWord, List.length_cons, List.length_replicate]
  omega

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The anti-diagonal word has an odd number of anti-diagonal generators. -/
theorem oWord_antiWord {i₀ i₁ : ι} (h₀ : S.o i₀ = 0) (h₁ : S.o i₁ = 1) (n : ℕ) :
    S.oWord (antiWord i₀ i₁ n) = 1 := by
  simp only [antiWord, oWord, List.map_cons, List.map_replicate, List.sum_cons,
    List.sum_replicate, h₀, h₁, smul_zero, add_zero]

/-- The words of the subsystem: `v w` for `w ∈ W`, and `v u₀` for the symbol `none`. -/
def subWords (v : List ι) (W : Finset (List ι)) (u₀ : List ι) : Option W → List ι
  | none => v ++ u₀
  | some w => v ++ (w : List ι)

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The word of the symbol `none`. -/
@[simp] theorem subWords_none (v : List ι) (W : Finset (List ι)) (u₀ : List ι) :
    subWords v W u₀ none = v ++ u₀ := rfl

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The word of the symbol `some w`. -/
@[simp] theorem subWords_some (v : List ι) (W : Finset (List ι)) (u₀ : List ι) (w : W) :
    subWords v W u₀ (some w) = v ++ (w : List ι) := rfl

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The lower bound `\dim_H X ≥ dim((π_n)_*ν_n)` for one family `W` of diagonal words of length `n`
with the common linear part `diag(a, b)`, prefixed by the diagonal word `v`, in either of the two
cases of tex lines 3505 to 3515: the trimmed family with `H ≤ χ_2`, or a feasible open set
`U ⊇ φ_v(X)`. -/
theorem le_dimH_attractor_of_words (hfib : FengInfoSumBar.{u}) (hly : FengLedrappierYoung.{u})
    (hlyb : FengLedrappierYoungBar.{u}) (hkk : KittleKoglerDimension.{u}) [Nonempty ι]
    (hfree : S.NoExactOverlaps) {i₀ i₁ : ι} (h₀ : S.o i₀ = 0) (h₁ : S.o i₁ = 1) {v : List ι}
    (hv : S.oWord v = 0) {W : Finset (List ι)} (hW : W.Nonempty) {n : ℕ} (hn : 0 < n) {a b : ℝ}
    (hWn : ∀ w ∈ W, w.length = n ∧ S.matWord w = boxMat 0 a b)
    (hab : |S.gDeriv (S.codeWord 1 v) * b| < |S.gDeriv (S.codeWord 0 v) * a|)
    (hzero : Real.log W.card ≤ -Real.log |S.gDeriv (S.codeWord 1 v) * b| ∨
      ∃ U : Set (ℝ × ℝ), IsOpen U ∧ U.Nonempty ∧ (∀ i, S.phi i '' U ⊆ U) ∧
        (Pairwise fun i j => Disjoint (S.phi i '' U) (S.phi j '' U)) ∧
        S.phiWord v '' S.attractor ⊆ U) :
    ENNReal.ofReal (subsystemDim (Real.log W.card) (-Real.log |S.gDeriv (S.codeWord 0 v) * a|)
      (-Real.log |S.gDeriv (S.codeWord 1 v) * b|)) ≤ dimH S.attractor := by
  classical
  have : Nonempty W := hW.to_subtype
  set u₀ := antiWord i₀ i₁ n with hu₀
  set wd : Option W → List ι := subWords v W u₀ with hwd
  have hlen : ∀ j, (wd j).length = v.length + n := by
    rintro (_ | w)
    · simp [hwd, hu₀, length_antiWord i₀ i₁ hn]
    · simp [hwd, (hWn w w.2).1]
  have hwne : ∀ j, wd j ≠ [] := fun j h => by
    have := hlen j
    rw [h] at this
    simp at this
    omega
  set T := S.subsystem wd hwne with hT
  have hdiagW : ∀ w : W, S.oWord w = 0 ∧ S.gDeriv (S.codeWord 0 w) = a ∧
      S.gDeriv (S.codeWord 1 w) = b := fun w =>
    (S.matWord_eq_boxMat_zero_iff _ _ _).1 (hWn w w.2).2
  -- The subsystem is homogeneous.
  have hhom : T.IsHomogeneousOption (S.gDeriv (S.codeWord 0 v) * a)
      (S.gDeriv (S.codeWord 1 v) * b) := by
    refine ⟨fun w => ?_, fun w => ?_, fun w => ?_, ?_⟩
    · simp [hT, hwd, oWord_append, hv, (hdiagW w).1]
    · simp [hT, hwd, codeWord_append, gDeriv_append, hv, (hdiagW w).2.1]
    · simp [hT, hwd, codeWord_append, gDeriv_append, hv, (hdiagW w).2.2]
    · simp [hT, hwd, hu₀, oWord_append, hv, S.oWord_antiWord h₀ h₁]
  -- The coordinate maps generate free semigroups.
  have hinj : Function.Injective fun w : W => v ++ (w : List ι) := fun w w' h =>
    Subtype.ext (List.append_cancel_left h)
  have hfreec : ∀ c : ZMod 2, Function.Injective
      (simWord (fun _ : W => S.gDeriv (S.codeWord c v) * if c = 0 then a else b)
        (fun w => T.trans (some w, c))) := by
    intro c
    have key := hfree.simWord_injective (S := S) c (w := fun w : W => v ++ (w : List ι))
      (fun w => by rw [oWord_append, hv, (hdiagW w).1, add_zero])
      (n := v.length + n) (Nat.add_pos_right _ hn) (fun w => by simp [(hWn w w.2).1]) hinj
    have e1 : (fun _ : W => S.gDeriv (S.codeWord c v) * if c = 0 then a else b) =
        fun w : W => S.gDeriv (S.codeWord c (v ++ (w : List ι))) := by
      funext w
      rw [codeWord_append, gDeriv_append, hv, add_zero]
      rcases zmod_two_cases c with rfl | rfl
      · simp [(hdiagW w).2.1]
      · simp [(hdiagW w).2.2]
    have e2 : (fun w : W => T.trans (some w, c)) =
        fun w : W => S.gWord (S.codeWord c (v ++ (w : List ι))) 0 := by
      funext w
      rw [hT, subsystem_trans]
      rfl
    rw [e1, e2]
    exact key
  have hfreex := hfreec 0
  have hfreey := hfreec 1
  simp only [ite_true] at hfreex
  simp only [one_ne_zero, ite_false] at hfreey
  have hab' : |S.gDeriv (S.codeWord 1 v) * b| < |S.gDeriv (S.codeWord 0 v) * a| := hab
  -- The two cases for `h_2 = 0`.
  have hzero' : Real.log (Fintype.card W) ≤ -Real.log |S.gDeriv (S.codeWord 1 v) * b| ∨
      ∀ x : ℤ → Option W, (∀ k : ℤ, (x k).isSome) →
        ∀ y : ℤ → Option W, (∀ k : ℤ, (y k).isSome) → T.proj y = T.proj x →
          ∀ k : ℕ, y k = x k := by
    rcases hzero with h | ⟨U, hU, hne, hsub, hdisj, hUv⟩
    · left
      rwa [Fintype.card_coe]
    · right
      intro x _ y _ hxy k
      have hinj' : Function.Injective wd := by
        rintro (_ | w) (_ | w') h
        · rfl
        · exfalso
          have h0 : v ++ u₀ = v ++ (w' : List ι) := h
          have h' : u₀ = (w' : List ι) := List.append_cancel_left h0
          have := (hdiagW w').1
          rw [← h', hu₀, S.oWord_antiWord h₀ h₁] at this
          exact one_ne_zero this
        · exfalso
          have h0 : v ++ (w : List ι) = v ++ u₀ := h
          have h' : (w : List ι) = u₀ := List.append_cancel_left h0
          have := (hdiagW w).1
          rw [h', hu₀, S.oWord_antiWord h₀ h₁] at this
          exact one_ne_zero this
        · have h0 : v ++ (w : List ι) = v ++ (w' : List ι) := h
          exact congrArg some (hinj h0)
      have hatt : T.attractor ⊆ U :=
        (S.subsystem_attractor_subset_image (w := wd) (hw := hwne)
          (by rintro (_ | w) <;> exact ⟨_, rfl⟩)).trans hUv
      exact S.subsystem_future_eq_of_proj_eq hU hne hsub hdisj
        (fun j j' => by rw [hlen, hlen]) hinj' hatt hxy k
  have hdim := hhom.isExactDim_map_proj hfib hly hlyb hkk hab' hfreex hfreey hzero'
  rw [Fintype.card_coe] at hdim
  refine hdim.le_dimH ?_
  obtain ⟨r, M, hB⟩ := T.exists_bounds
  rw [Measure.map_apply hB.measurable_proj S.isCompact_attractor.isClosed.measurableSet]
  have hpre : T.proj ⁻¹' S.attractor = univ :=
    eq_univ_of_forall fun x => S.subsystem_attractor_subset ⟨x, rfl⟩
  rw [hpre, measure_univ]
  exact zero_lt_one

/-! ### The theorem -/

/-- `thm:main2`, the lower bound `\dim_H X ≥ s` for a tuple containing a proximal diagonal
generator, with `s` the zero of the pressure in `(0, 2)` and the alternative in the entropy
form `h_0(μ) ≤ -λ_2(𝖠, μ)` of tex lines 3460 to 3468. -/
theorem main2_noExactOverlaps_normalised (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hfib : FengInfoSumBar.{u}) (hly : FengLedrappierYoung.{u})
    (hlyb : FengLedrappierYoungBar.{u}) (hkk : KittleKoglerDimension.{u})
    (hrot : S.WithRotations) (hdiag : S.HasProximalDiagonal) (hfree : S.NoExactOverlaps)
    {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) (hP : S.pressure s = 0) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ)
    (hor : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    ENNReal.ofReal s ≤ dimH S.attractor := by
  classical
  have : Nonempty ι := nonempty_of_measure μ
  obtain ⟨i₀, h₀⟩ := hrot.1
  obtain ⟨i₁, h₁⟩ := hrot.2
  have hl := hms S hrot hdiag hs0 hs2 μ hinv heq
  have hl1 := S.lyapunov₁_neg hinv
  have henergy : entropy μ + energy (S.lyapunov₁ μ) (S.lyapunov₂ μ) s = 0 := by
    rw [← heq.pressure_eq hinv hs0.le, hP]
  have hdim := lyapDim_eq hl.le hl1 henergy
  have hh2 : entropy μ ≤ -S.lyapunov₁ μ - S.lyapunov₂ μ :=
    (entropy_lt_of_lt_two hl.le hl1 hs2 henergy).le
  obtain ⟨n, W, a, b, hn, hnpos, hWne, hWn, hH, ha, hb⟩ :=
    S.exists_typical_words hfk hfjj hrot hdiag hs0 hs2 hP μ hinv heq
  -- The entries `a_m`, `b_m` are non-zero with modulus below one.
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
  -- Eventually `|b_m| < |a_m|`, from `λ_2 < λ_1`.
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
  · -- The entropy case: trim the families (tex lines 3505 to 3507).
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
    -- The lower bounds from the trimmed families.
    have hle : ∀ᶠ m in atTop, ENNReal.ofReal (subsystemDim (Real.log (W' m).card)
        (-Real.log |a m|) (-Real.log |b m|)) ≤ dimH S.attractor := by
      filter_upwards [hlt] with m hm
      have key := S.le_dimH_attractor_of_words hfib hly hlyb hkk hfree h₀ h₁ (v := [])
        (by simp) (hW'ne m) (hnpos m) (fun w hw => hWn m w (hW'sub m hw))
        (by simpa using hm) (Or.inl ?_)
      · simpa using key
      · simp only [codeWord_nil, gDeriv_nil, one_mul]
        rw [← Real.log_inv]
        refine Real.log_le_log (by exact_mod_cast Finset.card_pos.2 (hW'ne m)) ?_
        calc ((W' m).card : ℝ) ≤ ⌊|b m|⁻¹⌋₊ := by
              exact_mod_cast (hW'card m).trans_le (min_le_right _ _)
          _ ≤ |b m|⁻¹ := Nat.floor_le (inv_nonneg.2 (abs_nonneg _))
    -- The limits of the trimmed data.
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
  · -- The strong open set case: prefix every word by `v` with `φ_v(X) ⊆ U`
    -- (tex lines 3508 to 3515).
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
    -- The limits of the prefixed data.
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
    -- Eventually `|b_v b_m| < |a_v a_m|`.
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
      exact S.le_dimH_attractor_of_words hfib hly hlyb hkk hfree h₀ h₁ hv (hWne m) (hnpos m)
        (hWn m) hm (Or.inr ⟨U, hU, hUne, hsub, hdisj, hUv⟩)
    exact le_dimH_of_subsystemDim hl hl1 hh2 hdim hn0' hH' hχ₁ hχ₂ hle

/-- `thm:main2`, with `s` the zero of the pressure in `(0, 2)` and the alternative in the
entropy form, for every proximal tuple: the reduction to a tuple containing a proximal diagonal
generator through `thm:two-block-normalisation` (tex lines 3455 to 3458), as in
`main_extended_lt_two_aux`. -/
theorem main2_noExactOverlaps_of_pressure (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hfib : FengInfoSumBar.{u}) (hly : FengLedrappierYoung.{u})
    (hlyb : FengLedrappierYoungBar.{u}) (hkk : KittleKoglerDimension.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal) (hfree : S.NoExactOverlaps)
    {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) (hP : S.pressure s = 0) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ)
    (hor : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    dimH S.attractor = ENNReal.ofReal s := by
  have := nonempty_of_measure μ
  have hd : S.dimaff = s := S.dimaff_eq hs0.le hP
  refine le_antisymm ?_ ?_
  · have := S.dimH_attractor_le
    rwa [hd, min_eq_right hs2.le] at this
  rcases hprox.hasProximalDiagonal_or_sq with h | h
  · exact S.main2_noExactOverlaps_normalised hms hfk hfjj hfib hly hlyb hkk hrot h hfree hs0 hs2
      hP μ hinv heq hor
  · have e2 := S.lyapunov₂_sq_map_group (S.tendsto_lyapunov₂ hinv)
    have hor2 : entropy (μ.map group) ≤ -S.sq.lyapunov₂ (μ.map group) ∨ S.sq.StrongOpenSet := by
      rcases hor with h' | h'
      · left
        rw [entropy_map_group hinv, e2]
        linarith
      · exact Or.inr (StrongOpenSet.sq S h')
    have key := S.sq.main2_noExactOverlaps_normalised hms hfk hfjj hfib hly hlyb hkk
      (S.sq_withRotations hrot) h hfree.sq hs0 hs2 (by rw [S.pressure_sq hs0.le, hP, mul_zero])
      (μ.map group) (measurePreserving_shift_map_group hinv) (heq.map_group hinv hs0.le) hor2
    rwa [S.attractor_sq] at key

/-- The case `dimaff(X) < 2` of `thm:main2`. Let `X` be a proximal box-like self-affine set with
rotations whose projective system has no exact overlaps, such that `dimaff(X) < 2`, and let `μ`
be the `s`-equilibrium
state for `s = dimaff(X)`. If `dimaff(X) ≤ 2 - λ_1(𝖠, μ)/λ_2(𝖠, μ)`, or if `X` satisfies the
strong open set condition, then `\dim_H(X) = dimaff(X)`. The upper bound is Falconer's,
`eq:hausdorff_affinity_upper_bound`; the lower bound comes from the finite diagonal subsystems.
Depends on: `MorrisShmerkinLyapunov`, `EquilibriumGibbsStatement`, `FraserJordanJurgaDecomposition`,
`FengInfoSumBar`, `FengLedrappierYoung`, `FengLedrappierYoungBar`, `KittleKoglerDimension`. -/
theorem main2_noExactOverlaps (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hfib : FengInfoSumBar.{u}) (hly : FengLedrappierYoung.{u})
    (hlyb : FengLedrappierYoungBar.{u}) (hkk : KittleKoglerDimension.{u})
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal) (hfree : S.NoExactOverlaps)
    (h2 : S.dimaff < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    dimH S.attractor = ENNReal.ofReal S.dimaff := by
  have := S.nontrivial_of_withRotations hrot
  have hs0 := S.dimaff_pos
  have hl := S.simple_lyapunov hms hrot hprox hs0 h2 μ hinv heq
  have hl1 := S.lyapunov₁_neg hinv
  have henergy : entropy μ + energy (S.lyapunov₁ μ) (S.lyapunov₂ μ) S.dimaff = 0 := by
    rw [← heq.pressure_eq hinv hs0.le, S.pressure_dimaff]
  exact S.main2_noExactOverlaps_of_pressure hms hfk hfjj hfib hly hlyb hkk hrot hprox hfree hs0
    h2 S.pressure_dimaff μ hinv heq (hor.imp (entropy_le_iff hl hl1 h2 henergy).2 id)

/-! ### Consequences for the dimension chain -/

/-- The chain `\dim_H X = \dim_P X = \dim_M X = dimaff(X)` of tex lines 510 to 514 under the
hypotheses of `thm:main2`. -/
theorem dim_chain_noExactOverlaps (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hfib : FengInfoSumBar.{u}) (hly : FengLedrappierYoung.{u})
    (hlyb : FengLedrappierYoungBar.{u}) (hkk : KittleKoglerDimension.{u})
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal) (hfree : S.NoExactOverlaps)
    (h2 : S.dimaff < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    dimH S.attractor = ENNReal.ofReal S.dimaff ∧
      packingDim S.attractor = ENNReal.ofReal S.dimaff ∧
      lowerBoxDim S.attractor = ENNReal.ofReal S.dimaff ∧
      upperBoxDim S.attractor = ENNReal.ofReal S.dimaff :=
  S.dim_chain (S.main2_noExactOverlaps hms hfk hfjj hfib hly hlyb hkk hrot hprox hfree h2 μ hinv
    heq hor)

/-- The squeeze `dimmaff(X) = dimaff(X)` of tex lines 515 to 515 under the hypotheses of
`thm:main2`, with the first part of `thm:fraser` as the hypothesis `hB`, which
`System.fraserBound_holds` proves. -/
theorem dimmaff_eq_dimaff_noExactOverlaps (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hfib : FengInfoSumBar.{u}) (hly : FengLedrappierYoung.{u})
    (hlyb : FengLedrappierYoungBar.{u}) (hkk : KittleKoglerDimension.{u}) [Nonempty ι]
    (hB : S.FraserBound) (hrot : S.WithRotations) (hprox : S.Proximal) (hfree : S.NoExactOverlaps)
    (h2 : S.dimaff < 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    S.dimmaff = S.dimaff :=
  S.dimmaff_eq_dimaff hB (S.main2_noExactOverlaps hms hfk hfjj hfib hly hlyb hkk hrot hprox hfree
    h2 μ hinv heq hor)

/-! ### The example of `prop:ssc_no_overlap_not_pesc` -/

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- A negative pressure at `s ≥ 0` places the affinity dimension below `s`, since the pressure
is strictly decreasing with zero `dimaff(X)`. -/
theorem dimaff_lt_of_pressure_neg [Nonempty ι] {s : ℝ} (hs : 0 ≤ s) (h : S.pressure s < 0) :
    S.dimaff < s := by
  by_contra h'
  rw [not_lt] at h'
  have := S.strictAntiOn_pressure.antitoneOn hs S.dimaff_nonneg h'
  rw [S.pressure_dimaff] at this
  exact absurd h (not_lt.2 this)

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- `∑_i |det A_i| < 1` gives `P(𝖠, 2) < 0` and `dimaff(X) < 2` (tex lines 1447 to 1449). -/
theorem dimaff_lt_two_of_sum_abs_det_lt_one [Nonempty ι] (h : ∑ i, |(S.mat i).det| < 1) :
    S.dimaff < 2 := by
  refine S.dimaff_lt_of_pressure_neg zero_le_two ?_
  rw [S.pressure_of_two_le le_rfl]
  have hpos : ∀ i, 0 < |(S.mat i).det| := fun i => by
    rw [mat, abs_det_boxMat]
    exact mul_pos (abs_pos.2 (S.a_ne_zero i)) (abs_pos.2 (S.b_ne_zero i))
  have e : ∑ i, |(S.mat i).det| ^ ((2 : ℝ) / 2) = ∑ i, |(S.mat i).det| := by
    simp
  rw [e]
  exact Real.log_neg (Finset.sum_pos (fun i _ => hpos i) Finset.univ_nonempty) h

end System

/-- The example of `prop:ssc_no_overlap_not_pesc` satisfies the hypotheses of `thm:main2` and
`\dim_H X = dimaff(X)` (tex lines 1447 to 1450): it satisfies the strong separation condition,
hence the strong open set condition, its projective system has no exact overlaps, it fails the
projective exponential separation condition, and `dimaff(X) < 2` since `∑_i |det A_i| < 1`.
The theorem of Bárány and Käenmäki enters as the hypothesis `NoOverlap.BaranyKaenmakiPair`. -/
theorem NoOverlap.dimH_eq_dimaff (h : NoOverlap.BaranyKaenmakiPair)
    (hms : MorrisShmerkinLyapunov.{0}) (hfk : EquilibriumGibbsStatement.{0})
    (hfjj : FraserJordanJurgaDecomposition.{0}) (hfib : FengInfoSumBar.{0})
    (hly : FengLedrappierYoung.{0}) (hlyb : FengLedrappierYoungBar.{0})
    (hkk : KittleKoglerDimension.{0}) :
    ∃ S : System (Fin 4), S.StrongSeparation ∧ S.NoExactOverlaps ∧ ¬ S.ProjExpSeparation ∧
      S.dimaff < 2 ∧ dimH S.attractor = ENNReal.ofReal S.dimaff := by
  obtain ⟨S, ho, hprox, -, -, -, -, hsep, hfree, hpesc, hdet⟩ :=
    NoOverlap.ssc_no_overlap_not_pesc h
  have hrot : S.WithRotations := ⟨⟨0, by rw [ho]; rfl⟩, ⟨3, by rw [ho]; rfl⟩⟩
  have hfree' : S.NoExactOverlaps := S.noExactOverlaps_iff.2 hfree
  have h2 := S.dimaff_lt_two_of_sum_abs_det_lt_one hdet
  obtain ⟨μ, hprob, hinv, heq⟩ := S.exists_isEquilibriumState S.dimaff_nonneg
  exact ⟨S, hsep, hfree', hpesc, h2, S.main2_noExactOverlaps hms hfk hfjj hfib hly hlyb hkk hrot
    hprox hfree' h2 μ hinv heq (Or.inr hsep.strongOpenSet)⟩

end BoxLike
