module

/-
The comments after `thm:main2` in the introduction (tex lines 498 to 501): "When `s < 2`, the
exponents are distinct and the threshold lies strictly between `1` and `2`. For `s ≥ 2`, the
exponents coincide and the threshold is one. In particular, the absence of projective exact
overlaps suffices whenever `dimaff(X) ≤ 1`, and the strong open set condition is needed only
beyond the threshold. The hypotheses of `thm:main2` force `s ≤ 2`, and the case `s = 2` follows
from the strong open set condition alone."

Here `s` is the parameter of the `s`-equilibrium state `μ`, `s = dimaff(X)` in `thm:main2`, and
the threshold is `2 - λ_1(𝖠, μ) / λ_2(𝖠, μ)`. The distinctness of the exponents for `s < 2` is
`eq:simple_lyapunov`, which the article takes from Morris–Shmerkin; it enters as the hypothesis
`MorrisShmerkinLyapunov` through `System.simple_lyapunov`, and the library proves it
(`morrisShmerkinLyapunov_holds`). The other statements are proved without such hypotheses.

* `one_lt_threshold`, `threshold_lt_two`: `λ_2 < λ_1 < 0` gives `1 < 2 - λ_1/λ_2 < 2`, and
  `λ_2 ≤ λ_1 < 0` gives `0 < λ_1/λ_2 ≤ 1`.
* `System.threshold_mem_Ioo_of_lt_two`, `System.threshold_mem_Ioo_dimaff`: for `0 < s < 2` the
  exponents are distinct and the threshold lies in `(1, 2)`.
* `System.threshold_eq_one_of_two_le`: for `s ≥ 2` the exponents coincide and the threshold is
  `1`.
* `System.dimaff_le_threshold_of_le_one`, `System.main2_of_dimaff_le_one`: `dimaff(X) ≤ 1` lies
  below the threshold, so the absence of projective exact overlaps suffices in `thm:main2`.
* `System.dimaff_lt_two_of_le_threshold`, `System.dimaff_le_two_of_main2_hypotheses`: the
  hypotheses of `thm:main2` force `dimaff(X) ≤ 2`.
* `System.strongOpenSet_of_dimaff_eq_two`, `System.dimH_attractor_of_dimaff_eq_two`,
  `System.main2_of_dimaff_eq_two`: at `dimaff(X) = 2` the hypotheses of `thm:main2` reduce to the
  strong open set condition, which alone gives `dim_H X = dimaff(X)`.
-/
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.General
public import BoxLike.MainTwoEndpoint
public import BoxLike.ProjectionLarge

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

/-- `λ_2 < λ_1 < 0` gives `1 < 2 - λ_1/λ_2`: the ratio `λ_1/λ_2` is less than one. -/
theorem one_lt_threshold {l₁ l₂ : ℝ} (h12 : l₂ < l₁) (h1 : l₁ < 0) : 1 < 2 - l₁ / l₂ := by
  have h2 : l₂ < 0 := h12.trans h1
  have : l₁ / l₂ < 1 := by rw [div_lt_one_of_neg h2]; exact h12
  linarith

/-- `λ_2 ≤ λ_1 < 0` gives `2 - λ_1/λ_2 < 2`: the ratio `λ_1/λ_2` is positive. -/
theorem threshold_lt_two {l₁ l₂ : ℝ} (h12 : l₂ ≤ l₁) (h1 : l₁ < 0) : 2 - l₁ / l₂ < 2 := by
  have : 0 < l₁ / l₂ := div_pos_of_neg_of_neg h1 (h12.trans_lt h1)
  linarith

/-- `λ_2 ≤ λ_1 < 0` gives `1 ≤ 2 - λ_1/λ_2`. -/
theorem one_le_threshold {l₁ l₂ : ℝ} (h12 : l₂ ≤ l₁) (h1 : l₁ < 0) : 1 ≤ 2 - l₁ / l₂ := by
  have h2 : l₂ < 0 := h12.trans_lt h1
  have : l₁ / l₂ ≤ 1 := by rw [div_le_one_of_neg h2]; exact h12
  linarith

namespace System

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι)

/-- Tex lines 491 to 492: for `0 < s < 2` the Lyapunov exponents of the `s`-equilibrium state of a
proximal box-like tuple with rotations are distinct (`eq:simple_lyapunov`, from
Morris–Shmerkin) and the threshold `2 - λ_1/λ_2` lies strictly between `1` and `2`. -/
theorem threshold_mem_Ioo_of_lt_two (hms : MorrisShmerkinLyapunov.{u}) (hrot : S.WithRotations)
    (hprox : S.Proximal) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) :
    S.lyapunov₂ μ < S.lyapunov₁ μ ∧ 1 < 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∧
      2 - S.lyapunov₁ μ / S.lyapunov₂ μ < 2 := by
  have hl := S.simple_lyapunov hms hrot hprox hs0 hs2 μ hinv heq
  have h1 := S.lyapunov₁_neg hinv
  exact ⟨hl, one_lt_threshold hl h1, threshold_lt_two hl.le h1⟩

/-- Tex lines 491 to 492 at `s = dimaff(X) < 2`, the case of `thm:main2`: `dimaff(X) > 0`, since
a tuple with rotations has at least two maps. -/
theorem threshold_mem_Ioo_dimaff (hms : MorrisShmerkinLyapunov.{u}) [Nonempty ι]
    (hrot : S.WithRotations) (hprox : S.Proximal) (hs2 : S.dimaff < 2) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ) :
    S.lyapunov₂ μ < S.lyapunov₁ μ ∧ 1 < 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∧
      2 - S.lyapunov₁ μ / S.lyapunov₂ μ < 2 := by
  have := S.nontrivial_of_withRotations hrot
  exact S.threshold_mem_Ioo_of_lt_two hms hrot hprox S.dimaff_pos hs2 μ hinv heq

/-- Tex lines 492 to 493: for `s ≥ 2` the Lyapunov exponents of the `s`-equilibrium state of a
box-like tuple with rotations coincide and the threshold is one. The equality of the exponents
is `System.IsEquilibriumState.lyapunov_eq_of_two_le`, from the Bernoulli form of the equilibrium
state. -/
theorem threshold_eq_one_of_two_le (hrot : S.WithRotations) {s : ℝ} (hs : 2 ≤ s)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) :
    S.lyapunov₁ μ = S.lyapunov₂ μ ∧ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ = 1 := by
  obtain ⟨h1, h2, -⟩ := heq.lyapunov_eq_of_two_le hrot hinv hs
  have he : S.lyapunov₁ μ = S.lyapunov₂ μ := h1.trans h2.symm
  have hne : S.lyapunov₂ μ ≠ 0 := (he ▸ S.lyapunov₁_neg hinv).ne
  refine ⟨he, ?_⟩
  rw [he, div_self hne]
  norm_num

/-- Tex line 494: `dimaff(X) ≤ 1` lies below the threshold, since `λ_2 ≤ λ_1 < 0` gives
`2 - λ_1/λ_2 ≥ 1` for every invariant `μ`. -/
theorem dimaff_le_threshold_of_le_one [Nonempty ι] (h1 : S.dimaff ≤ 1) (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ) :
    S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ :=
  h1.trans (one_le_threshold (S.lyapunov₂_le_lyapunov₁ hinv) (S.lyapunov₁_neg hinv))

/-- Tex line 494, "the absence of projective exact overlaps suffices whenever `dimaff(X) ≤ 1`":
under the hypotheses of `thm:main2` other than the alternative, `dimaff(X) ≤ 1` gives
`dim_H X = dimaff(X)`. This applies `thm:main2` (`System.main2_noExactOverlaps_all`) and takes
its hypotheses. -/
theorem main2_of_dimaff_le_one (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hfib : FengInfoSumBar.{u}) (hly : FengLedrappierYoung.{u})
    (hlyb : FengLedrappierYoungBar.{u}) (hkk : KittleKoglerDimension.{u}) [Nonempty ι]
    (hrot : S.WithRotations) (hprox : S.Proximal) (hfree : S.NoExactOverlaps)
    (h1 : S.dimaff ≤ 1) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ) :
    dimH S.attractor = ENNReal.ofReal S.dimaff :=
  S.main2_noExactOverlaps_all hms hfk hfjj hfib hly hlyb hkk hrot hprox hfree μ hinv heq
    (Or.inl (S.dimaff_le_threshold_of_le_one h1 μ hinv))

/-- Tex lines 495 to 496: the first alternative of `thm:main2` forces `dimaff(X) < 2`, since the
threshold is less than two. -/
theorem dimaff_lt_two_of_le_threshold [Nonempty ι] (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (h : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ) : S.dimaff < 2 :=
  h.trans_lt (threshold_lt_two (S.lyapunov₂_le_lyapunov₁ hinv) (S.lyapunov₁_neg hinv))

/-- Tex lines 495 to 496: the hypotheses of `thm:main2` force `dimaff(X) ≤ 2`. The first
alternative gives `dimaff(X) < 2`; under the strong open set condition `∑_i |det A_i| ≤ 1`, so
`dimaff(X) ≥ 2` forces `dimaff(X) = 2` (`System.StrongOpenSet.dimaff_eq_two`). -/
theorem dimaff_le_two_of_main2_hypotheses [Nonempty ι] (μ : Measure (ℤ → ι))
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet) : S.dimaff ≤ 2 := by
  rcases hor with h | h
  · exact (S.dimaff_lt_two_of_le_threshold μ hinv h).le
  · rcases le_or_gt S.dimaff 2 with h2 | h2
    · exact h2
    · exact (h.dimaff_eq_two S h2.le).le

/-- Tex lines 496 to 497: at `dimaff(X) = 2` the hypotheses of `thm:main2` reduce to the strong
open set condition, since the threshold is one there. -/
theorem strongOpenSet_of_dimaff_eq_two [Nonempty ι] (hrot : S.WithRotations)
    (h2 : S.dimaff = 2) (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    S.StrongOpenSet := by
  refine hor.resolve_left fun h => ?_
  rw [(S.threshold_eq_one_of_two_le hrot h2.ge μ hinv heq).2, h2] at h
  norm_num at h

/-- Tex lines 496 to 497, "the case `s = 2` follows from the strong open set condition alone": the
strong open set condition and `dimaff(X) = 2` give `dim_H X = dimaff(X)`, without rotations,
proximality, the absence of exact overlaps or a literature hypothesis
(`System.dimH_attractor_of_two_le`). -/
theorem dimH_attractor_of_dimaff_eq_two [Nonempty ι] (hsosc : S.StrongOpenSet)
    (h2 : S.dimaff = 2) : dimH S.attractor = ENNReal.ofReal S.dimaff := by
  rw [S.dimH_attractor_of_two_le hsosc h2.ge, h2]
  norm_num

/-- Tex lines 495 to 497: `thm:main2` at `dimaff(X) = 2` without literature hypotheses and without
proximality or the absence of exact overlaps. -/
theorem main2_of_dimaff_eq_two [Nonempty ι] (hrot : S.WithRotations) (h2 : S.dimaff = 2)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    dimH S.attractor = ENNReal.ofReal S.dimaff :=
  S.dimH_attractor_of_dimaff_eq_two (S.strongOpenSet_of_dimaff_eq_two hrot h2 μ hinv heq hor) h2

end System

end BoxLike
