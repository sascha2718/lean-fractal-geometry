module

/-
The remark at the end of `sec:gibbs_measures`: "At `s = 2`, the potentials
coincide, `f_{1,2} = f_{2,2}`, and hence so do the Gibbs measures."

The manuscript extends the potentials `f_{1,s}`, `f_{2,s}` to `s = 2` using the formula of
the case `1 ≤ s < 2`, which is the definition
`System.potential₁` of the library for every `s ≥ 1`. At `s = 2` both potentials of the symbol
`(i, c)` equal `log |a_i| + log |b_i| = log |det A_i|`. The Gibbs measures then coincide by the
uniqueness of the ergodic Gibbs measure of a potential (`IsGibbs.eq_of_ergodic`).

* `System.potential₁_two`, `System.potential₂_two`: `f_{1,2}(j_0) = f_{2,2}(j_0) = log |det A_i|`
  for `j_0 = (i, c)`.
* `System.potential₁_two_eq_potential₂_two`: `f_{1,2} = f_{2,2}`.
* `System.isGibbs_potential₁_two_iff`: the Gibbs measures for `f_{1,2}` are those for `f_{2,2}`.
* `System.eq_of_isGibbs_potential_two`: an invariant Gibbs probability measure for `f_{2,2}` on
  `Σ_Z` equals the ergodic Gibbs probability measure for `f_{1,2}`.
* `System.GibbsDecomposition.mu₁_eq_mu₂_of_two`: the two `2`-Gibbs measures of a decomposition
  coincide.
-/
public import BoxLike.Support.GibbsUniqueness

@[expose] public section

namespace BoxLike

open MeasureTheory

namespace System

variable {ι : Type*} (S : System ι)

/-- `f_{1,2}(j_0) = log |g'_{j_0}| + log |g'_{j_0 ± N}| = log |a_i| + log |b_i| = log |det A_i|`
for `j_0 = (i, c)` (tex lines 2405 to 2432 at `s = 2`). -/
theorem potential₁_two (p : ι × ZMod 2) :
    S.potential₁ 2 p = Real.log |(S.mat p.1).det| := by
  have hab : Real.log |S.ratio p| + Real.log |S.ratio (p.1, p.2 + 1)| =
      Real.log |S.a p.1| + Real.log |S.b p.1| := by
    rcases zmod_two_cases p.2 with h | h <;> simp [ratio, h, add_comm,
      show (1 : ZMod 2) + 1 = 0 from by decide]
  rw [potential₁, ite_eq_right (by norm_num), show (2 : ℝ) - 1 = 1 by norm_num, one_mul, hab, mat,
    abs_det_boxMat, Real.log_mul (abs_ne_zero.2 (S.a_ne_zero _)) (abs_ne_zero.2 (S.b_ne_zero _))]

/-- `f_{2,2}(j_0) = log |det A_i|` for `j_0 = (i, c)`. -/
theorem potential₂_two (p : ι × ZMod 2) :
    S.potential₂ 2 p = Real.log |(S.mat p.1).det| :=
  S.potential₁_two (p.1, p.2 + 1)

/-- Tex line 2637: at `s = 2` the potentials coincide, `f_{1,2} = f_{2,2}`. -/
theorem potential₁_two_eq_potential₂_two : S.potential₁ 2 = S.potential₂ 2 :=
  funext fun p => by rw [S.potential₁_two, S.potential₂_two]

variable [MeasurableSpace ι]

/-- At `s = 2` the Gibbs measures for `f_{1,2}` are those for `f_{2,2}`. -/
theorem isGibbs_potential₁_two_iff {ν : Measure (ℤ → ι × ZMod 2)} :
    IsGibbs S.o (S.potential₁ 2) ν ↔ IsGibbs S.o (S.potential₂ 2) ν := by
  rw [S.potential₁_two_eq_potential₂_two]

variable [Fintype ι] [MeasurableSingletonClass ι]

/-- Tex line 2637, "and hence so do the Gibbs measures": an invariant Gibbs probability measure
`μ_2` for `f_{2,2}` carried by `Σ_Z` equals every ergodic Gibbs probability measure `μ_1` for
`f_{1,2}` carried by `Σ_Z`, since the two potentials coincide and the ergodic Gibbs measure of a
potential is unique. -/
theorem eq_of_isGibbs_potential_two {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (h₁ : μ₁ (subshift S.o)ᶜ = 0)
    (h₂ : μ₂ (subshift S.o)ᶜ = 0) (hg₁ : IsGibbs S.o (S.potential₁ 2) μ₁)
    (hg₂ : IsGibbs S.o (S.potential₂ 2) μ₂) (herg : Ergodic (shift 1) μ₁)
    (hinv : MeasurePreserving (shift 1) μ₂ μ₂) : μ₂ = μ₁ :=
  IsGibbs.eq_of_ergodic h₁ h₂ hg₁ ((S.isGibbs_potential₁_two_iff).2 hg₂) herg hinv

variable {S}

/-- The `2`-Gibbs measures `μ_1`, `μ_2` of a decomposition of `thm:eq_state_is_sum` at `s = 2`
coincide (tex line 2519). -/
theorem GibbsDecomposition.mu₁_eq_mu₂_of_two {μ : Measure (ℤ → ι)}
    {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)} (h : S.GibbsDecomposition 2 μ μ₁ μ₂) : μ₁ = μ₂ := by
  have := h.prob₁
  have := h.prob₂
  exact (S.eq_of_isGibbs_potential_two h.supp₁ h.supp₂ h.gibbs₁ h.gibbs₂ h.ergodic₁
    h.ergodic₂.toMeasurePreserving).symm

end System

end BoxLike
