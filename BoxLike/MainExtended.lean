module

/-
`thm:main_extended` of `sec:dimension_result_proof` in full: the case `s ≥ 2` and the assembly
with the case `0 < s < 2` of `BoxLike/MainTwo.lean`.

For `s ≥ 2` the singular value function is `|det|^{s/2}`. The strong open set condition gives
`∑_i |det A_i| ≤ 1` by comparing Lebesgue measures, so `P(𝖠, s) = 0` forces
`∑_i |det A_i| = 1` and `|det A_i|^{s/2} = |det A_i|`. The equilibrium equation, the bound
`h(μ) ≤ H_μ(𝒫)` and Gibbs' inequality show that `μ` is the Bernoulli measure with weights
`|det A_i|`. Its projection and normalised Lebesgue measure on the open set are invariant
probability measures with the same weights, so they coincide by Hutchinson's theorem, and
normalised Lebesgue measure has exact dimension two.

* `System.abs_det_mat_pos`, `System.abs_det_mat_lt_one`: `0 < |det A_i| < 1`.
* `System.StrongOpenSet.sum_abs_det_eq_one`: `∑_i |det A_i| = 1` when `P(𝖠, s) = 0`, `s ≥ 2`.
* `System.main_extended_ge_two`: `thm:main_extended` for `s ≥ 2`.
* `System.main_extended`: `thm:main_extended`.
-/
public import BoxLike.BernoulliEntropy
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.InvariantMeasure
public import BoxLike.LebesgueOpenSet
public import BoxLike.MainTwo
public import BoxLike.PressureLarge

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

namespace System

variable {ι : Type u} (S : System ι) {s : ℝ}

/-- `|det A_i| > 0`. -/
theorem abs_det_mat_pos (i : ι) : 0 < |(S.mat i).det| := by
  rw [mat, abs_det_boxMat]
  exact mul_pos (abs_pos.2 (S.a_ne_zero i)) (abs_pos.2 (S.b_ne_zero i))

/-- `|det A_i| < 1`. -/
theorem abs_det_mat_lt_one (i : ι) : |(S.mat i).det| < 1 := by
  rw [mat, abs_det_boxMat]
  exact (mul_le_of_le_one_right (abs_nonneg _) (S.abs_b_lt_one i).le).trans_lt
    (S.abs_a_lt_one i)

/-- `|det A_i|^{t} ≤ |det A_i|` for `t ≥ 1`. -/
theorem abs_det_mat_rpow_le {t : ℝ} (ht : 1 ≤ t) (i : ι) :
    |(S.mat i).det| ^ t ≤ |(S.mat i).det| := by
  have h := Real.rpow_le_rpow_of_exponent_ge (S.abs_det_mat_pos i) (S.abs_det_mat_lt_one i).le ht
  rwa [Real.rpow_one] at h

variable [Fintype ι]

/-- Under the strong open set condition, `P(𝖠, s) = 0` with `s ≥ 2` forces
`|det A_i|^{s/2} = |det A_i|` for every `i` and `∑_i |det A_i| = 1`. -/
theorem StrongOpenSet.sum_abs_det_eq_one (hsosc : S.StrongOpenSet) (hs : 2 ≤ s)
    (hP : S.pressure s = 0) :
    (∀ i, |(S.mat i).det| ^ (s / 2) = |(S.mat i).det|) ∧ ∑ i, |(S.mat i).det| = 1 := by
  have ht : 1 ≤ s / 2 := by linarith
  have hpos : 0 < ∑ i, |(S.mat i).det| ^ (s / 2) := by
    obtain ⟨U, -, ⟨z, -, hz⟩, -, -⟩ := hsosc
    obtain ⟨x, -⟩ := hz
    exact Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (S.abs_det_mat_pos i) _)
      ⟨x 0, Finset.mem_univ _⟩
  have hlog : Real.log (∑ i, |(S.mat i).det| ^ (s / 2)) = 0 := by
    rw [← S.pressure_of_two_le hs, hP]
  have hpow : ∑ i, |(S.mat i).det| ^ (s / 2) = 1 :=
    Real.eq_one_of_pos_of_log_eq_zero hpos hlog
  have hle : ∑ i, |(S.mat i).det| ^ (s / 2) ≤ ∑ i, |(S.mat i).det| :=
    Finset.sum_le_sum fun i _ => S.abs_det_mat_rpow_le ht i
  have hsum : ∑ i, |(S.mat i).det| = 1 :=
    le_antisymm hsosc.sum_abs_det_le_one (hpow ▸ hle)
  refine ⟨fun i => ?_, hsum⟩
  have h := (Finset.sum_eq_sum_iff_of_le fun i _ => S.abs_det_mat_rpow_le ht i).1
    (hpow.trans hsum.symm)
  exact h i (Finset.mem_univ i)

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- `thm:main_extended`, the case `s ≥ 2`: under the strong open set condition, if
`P(𝖠, s) = 0` with `s ≥ 2` and `μ` is an `s`-equilibrium state, then `π_*μ` is normalised
Lebesgue measure on an open set and has exact dimension two. Rotations, proximality and the
projective exponential separation condition are not used. -/
theorem main_extended_ge_two (hsosc : S.StrongOpenSet) (hs : 2 ≤ s) (hP : S.pressure s = 0)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) : IsExactDim (μ.map S.proj) 2 := by
  obtain ⟨hterm, hsum⟩ := hsosc.sum_abs_det_eq_one S hs hP
  have hd := S.abs_det_mat_pos
  -- The equilibrium equation reads `0 = h(μ) + ∑_i μ[i] log |det A_i|`.
  have hE := heq.log_sum_eq hinv hs
  have hrw : s / 2 * ∑ i, μ.real (cylinder ![i]) * Real.log |(S.mat i).det| =
      ∑ i, μ.real (cylinder ![i]) * Real.log |(S.mat i).det| := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_left_comm, ← Real.log_rpow (hd i), hterm i]
  rw [hrw, (Finset.sum_congr rfl fun i _ => hterm i :
    ∑ i, |(S.mat i).det| ^ (s / 2) = ∑ i, |(S.mat i).det|)] at hE
  -- Gibbs' inequality and `h(μ) ≤ H_μ(𝒫)` are equalities.
  have hG := blockEntropy_one_add_sum_le μ (fun i => |(S.mat i).det|) hd
  have hH := entropy_le_blockEntropy_one hinv
  have hent : entropy μ = blockEntropy μ 1 := by linarith
  have hGeq : blockEntropy μ 1 + ∑ i, μ.real (cylinder ![i]) * Real.log |(S.mat i).det| =
      Real.log (∑ i, |(S.mat i).det|) := by linarith
  have hweight : ∀ i, μ (cylinder ![i]) = ENNReal.ofReal |(S.mat i).det| := by
    intro i
    have h := measureReal_cylinder_eq_of_blockEntropy_one_add_sum_eq μ _ hd hGeq i
    rw [hsum, div_one] at h
    rw [← h, ofReal_measureReal]
  -- The projection of `μ` and normalised Lebesgue measure are invariant with the same weights.
  have hinvμ := S.isInvariantMeasure_map_proj hinv
    (fun n w => measureReal_cylinder_eq_prod_of_entropy_eq hinv hent w)
  rw [funext hweight] at hinvμ
  obtain ⟨ν, hν, hinvν, hdim⟩ := hsosc.exists_isInvariantMeasure_isExactDim S hsum
  have hp : ∑ i, ENNReal.ofReal |(S.mat i).det| = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _, hsum, ENNReal.ofReal_one]
  rwa [hinvμ.unique hp hinvν]

/-- `thm:main_extended`: let `X` be a proximal box-like self-affine set with rotations
and let `μ` be an `s`-equilibrium state for `s = dimaff(𝖠)`. Assume projective exponential
separation only when `s < 2`. If `h_0(μ) ≤ -λ_2(𝖠, μ)` or the strong open set condition holds, then
`π_*μ` is exact-dimensional with `dim π_*μ = dimaff(𝖠) ≤ 2`. For `s ≥ 2` the entropy
alternative is impossible. -/
theorem main_extended (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hjr : JordanRapaportDimension.{u}) (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u})
    (hly : FengLedrappierYoung.{u}) (hlyb : FengLedrappierYoungBar.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : s < 2 → S.ProjExpSeparation) (hs0 : 0 < s) (hP : S.pressure s = 0)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ)
    (hor : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    IsExactDim (μ.map S.proj) s ∧ s ≤ 2 := by
  have := S.nontrivial_of_withRotations hrot
  rcases lt_or_ge s 2 with hs2 | hs2
  · refine ⟨?_, hs2.le⟩
    exact S.main_extended_lt_two' hms hfk hfjj hjr hfi hfib hly hlyb hrot hprox (hsep hs2)
      hs0 hs2 hP μ hinv heq hor
  · have henergy : entropy μ + energy (S.lyapunov₁ μ) (S.lyapunov₂ μ) s = 0 := by
      rw [← heq.pressure_eq hinv hs0.le, hP]
    have hgt := neg_lt_entropy_of_two_le (S.lyapunov₂_le_lyapunov₁ hinv) (S.lyapunov₁_neg hinv)
      hs2 henergy
    have hsosc := hor.resolve_left (not_le.2 hgt)
    have hsum := (hsosc.sum_abs_det_eq_one S hs2 hP).2
    have hP2 : S.pressure 2 = 0 := by
      rw [S.pressure_of_two_le le_rfl]
      simpa using congrArg Real.log hsum
    have hs_eq : s = 2 := (S.dimaff_eq hs0.le hP).symm.trans (S.dimaff_eq zero_le_two hP2)
    subst s
    exact ⟨S.main_extended_ge_two hsosc le_rfl hP μ hinv heq, le_rfl⟩

/-- A consequence of `thm:main_extended` with `s = dimaff(𝖠)`, the zero of the pressure:
`dim π_*μ = min{2, dimaff(𝖠)}`. -/
theorem main_extended_min (hms : MorrisShmerkinLyapunov.{u})
    (hfk : EquilibriumGibbsStatement.{u}) (hfjj : FraserJordanJurgaDecomposition.{u})
    (hjr : JordanRapaportDimension.{u}) (hfi : FengInfoSum.{u}) (hfib : FengInfoSumBar.{u})
    (hly : FengLedrappierYoung.{u}) (hlyb : FengLedrappierYoungBar.{u})
    [Nonempty ι] (hrot : S.WithRotations) (hprox : S.Proximal)
    (hsep : S.dimaff < 2 → S.ProjExpSeparation)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : entropy μ ≤ -S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    IsExactDim (μ.map S.proj) (min 2 S.dimaff) := by
  have := S.nontrivial_of_withRotations hrot
  obtain ⟨hdim, hs⟩ := S.main_extended hms hfk hfjj hjr hfi hfib hly hlyb hrot hprox hsep
    S.dimaff_pos S.pressure_dimaff μ hinv heq hor
  simpa only [min_eq_right hs] using hdim

end System

end BoxLike
