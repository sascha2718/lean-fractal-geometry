module

/-
The thermodynamic vocabulary of `sec:lyapunov_exponents`, `sec:affinity_dim` and
`sec:gibbs_measures`, for invariant probability measures on the two-sided shifts over `ι` and
over `ι × ZMod 2`. Invariance of `μ` is `MeasurePreserving (shift 1) μ μ` and ergodicity is
`Ergodic (shift 1) μ`.

* `System.lyapunov₁`, `System.lyapunov₂`: the Lyapunov exponents `λ_1(𝖠, μ)`, `λ_2(𝖠, μ)`, with
  `α_1(A) = ‖A‖` and `α_2(A) = |det A| / ‖A‖`.
* `System.lyapBar`, `System.lyapBar_neg`: the Lyapunov exponent `\overline{λ}(𝖠, ν)` of the
  projective system in the form `∫ log |g'_{j_0}| dν` of `thm:eq_state_is_sum`, and its
  negativity.
* `System.energyLim`, `System.IsEquilibriumState`: the `s`-energy `Λ(𝖠, μ, s)` and
  `eq:eq_state_def`.
* `System.HasGibbsBounds`: the Gibbs bounds of `thm:irred_eq_state`.
* `System.potential₁`, `System.potential₂`: the potentials `f_{1,s}`, `f_{2,s}`.
* `IsGibbs`, `IsGibbs.measureReal_cylinder_pos`: Gibbs measures on `Σ_Z`.
* `System.GibbsDecomposition`: the conclusion of `thm:eq_state_is_sum`.
* `System.marginal`: the coordinate marginals `(proj_x)_*(π_*μ)` and `(proj_y)_*(π_*μ)`.
-/
public import BoxLike.Entropy
public import BoxLike.LyapunovDim
public import BoxLike.Measurable
public import BoxLike.Pressure
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

@[expose] public section

namespace BoxLike

open MeasureTheory Filter
open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [MeasurableSpace ι]

/-- A Gibbs measure on `Σ_Z` for the one-symbol potential `φ`, as in `sec:gibbs_measures`:
`C⁻¹ exp(-nP + S_n φ(𝐣)) ≤ ν([𝐣|_n]) ≤ C exp(-nP + S_n φ(𝐣))` for all `𝐣 ∈ Σ_Z` and `n ≥ 1`.
The constant `P` is the pressure `P_Z(φ)`; the bounds determine it. -/
def IsGibbs (o : ι → ZMod 2) (φ : ι × ZMod 2 → ℝ) (ν : Measure (ℤ → ι × ZMod 2)) : Prop :=
  ∃ P C : ℝ, 0 < C ∧ ∀ y ∈ subshift o, ∀ n : ℕ, 0 < n →
    C⁻¹ * Real.exp (-(n * P) + ∑ k ∈ Finset.range n, φ (y k)) ≤
        ν.real (cylinder fun k : Fin n => y k) ∧
      ν.real (cylinder fun k : Fin n => y k) ≤
        C * Real.exp (-(n * P) + ∑ k ∈ Finset.range n, φ (y k))

/-- A Gibbs measure charges every cylinder of `Σ_Z`. -/
theorem IsGibbs.measureReal_cylinder_pos {o : ι → ZMod 2} {φ : ι × ZMod 2 → ℝ}
    {ν : Measure (ℤ → ι × ZMod 2)} (h : IsGibbs o φ ν) {y : ℤ → ι × ZMod 2}
    (hy : y ∈ subshift o) {n : ℕ} (hn : 0 < n) :
    0 < ν.real (cylinder fun k : Fin n => y k) := by
  obtain ⟨P, C, hC, hb⟩ := h
  exact lt_of_lt_of_le (mul_pos (inv_pos.2 hC) (Real.exp_pos _)) (hb y hy n hn).1

namespace System

variable [MeasurableSingletonClass ι] (S : System ι)

/-- The Lyapunov exponent `λ_1(𝖠, μ) = lim_n n⁻¹ ∫ log α_1(A_{𝐢|_n}) dμ(𝐢)` of
`sec:lyapunov_exponents`. -/
noncomputable def lyapunov₁ (μ : Measure (ℤ → ι)) : ℝ :=
  limUnder atTop fun n : ℕ => (∫ x, Real.log ‖S.matWord (futureWord x n)‖ ∂μ) / n

/-- The Lyapunov exponent `λ_2(𝖠, μ) = lim_n n⁻¹ ∫ log α_2(A_{𝐢|_n}) dμ(𝐢)` of
`sec:lyapunov_exponents`, with `α_2(A) = |det A| / ‖A‖`. -/
noncomputable def lyapunov₂ (μ : Measure (ℤ → ι)) : ℝ :=
  limUnder atTop fun n : ℕ =>
    (∫ x, Real.log (|(S.matWord (futureWord x n)).det| / ‖S.matWord (futureWord x n)‖) ∂μ) / n

/-- The Lyapunov exponent `\overline{λ}(𝖠, ν)` of the projective system. For an invariant
measure the limit defining it in `sec:lyapunov_exponents` is the integral
`∫ log |g'_{j_0}(0)| dν(𝐣) = ∫ f_{1,1} dν` of `thm:eq_state_is_sum`. -/
noncomputable def lyapBar (ν : Measure (ℤ → ι × ZMod 2)) : ℝ :=
  ∫ y, Real.log |S.ratio (y 0)| ∂ν

/-- The `s`-energy `Λ(𝖠, μ, s) = lim_n n⁻¹ ∫ log φ^s(A_{𝐢|_n}) dμ(𝐢)` of `eq:energy_def`, first
line. -/
noncomputable def energyLim (s : ℝ) (μ : Measure (ℤ → ι)) : ℝ :=
  limUnder atTop fun n : ℕ => (∫ x, Real.log (svf s (S.matWord (futureWord x n))) ∂μ) / n

/-- `μ` is an `s`-equilibrium state, `eq:eq_state_def`: `P(𝖠, s) = h_0(μ) + Λ(𝖠, μ, s)`. -/
def IsEquilibriumState [Fintype ι] (s : ℝ) (μ : Measure (ℤ → ι)) : Prop :=
  S.pressure s = entropy μ + S.energyLim s μ

/-- The Gibbs bounds of `thm:irred_eq_state` for a measure `μ` on `Σ`:
`C⁻¹ exp(-|𝐢| P(𝖠, s)) φ^s(A_𝐢) ≤ μ([𝐢]) ≤ C exp(-|𝐢| P(𝖠, s)) φ^s(A_𝐢)` for all finite words
`𝐢 ∈ Σ_*^+`, with a constant `C ≥ 1`. -/
def HasGibbsBounds [Fintype ι] (s : ℝ) (μ : Measure (ℤ → ι)) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ w : Fin n → ι,
    C⁻¹ * (Real.exp (-(n * S.pressure s)) * svf s (S.matWord (List.ofFn w))) ≤
        μ.real (cylinder w) ∧
      μ.real (cylinder w) ≤
        C * (Real.exp (-(n * S.pressure s)) * svf s (S.matWord (List.ofFn w)))

/-- The potential `f_{1,s}` of `sec:gibbs_measures`, as a function of the symbol `j_0`. -/
noncomputable def potential₁ (s : ℝ) (p : ι × ZMod 2) : ℝ :=
  if s < 1 then s * Real.log |S.ratio p|
  else Real.log |S.ratio p| + (s - 1) * Real.log |S.ratio (p.1, p.2 + 1)|

/-- The potential `f_{2,s}` of `sec:gibbs_measures`: `f_{2,s}(j_0) = f_{1,s}` of the symbol on
the other axis. -/
noncomputable def potential₂ (s : ℝ) (p : ι × ZMod 2) : ℝ := S.potential₁ s (p.1, p.2 + 1)

/-- The conclusion of `thm:eq_state_is_sum` for the `s`-equilibrium state `μ`: the `s`-Gibbs
measures `μ_1`, `μ_2`, the four decompositions of `μ`, and the Lyapunov exponents. The
push-forward `\overline{τ}_*ν` of the restriction `ν|_{τ(Σ)}` is
`(ν.restrict (Set.range (tau S.o))).map unCode`. -/
structure GibbsDecomposition (s : ℝ) (μ : Measure (ℤ → ι))
    (μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)) : Prop where
  prob₁ : IsProbabilityMeasure μ₁
  prob₂ : IsProbabilityMeasure μ₂
  ergodic₁ : Ergodic (shift 1) μ₁
  ergodic₂ : Ergodic (shift 1) μ₂
  supp₁ : μ₁ (subshift S.o)ᶜ = 0
  supp₂ : μ₂ (subshift S.o)ᶜ = 0
  gibbs₁ : IsGibbs S.o (S.potential₁ s) μ₁
  gibbs₂ : IsGibbs S.o (S.potential₂ s) μ₂
  eq_tau : μ = (μ₁.restrict (Set.range (tau S.o))).map unCode +
    (μ₂.restrict (Set.range (tau S.o))).map unCode
  eq_omega : μ = (μ₁.restrict (Set.range (omega S.o))).map unCode +
    (μ₂.restrict (Set.range (omega S.o))).map unCode
  eq₁ : μ = (μ₁.restrict (Set.range (tau S.o))).map unCode +
    (μ₁.restrict (Set.range (omega S.o))).map unCode
  eq₂ : μ = (μ₂.restrict (Set.range (tau S.o))).map unCode +
    (μ₂.restrict (Set.range (omega S.o))).map unCode
  lyapunov₁_eq : S.lyapunov₁ μ = S.lyapBar μ₁
  lyapunov₂_eq : S.lyapunov₂ μ = S.lyapBar μ₂

/-- The coordinate marginals `ν_x = (proj_x)_*(π_*μ)` for `c = 0` and `ν_y = (proj_y)_*(π_*μ)`
for `c = 1` of `sec:dimension_of_projections`. -/
noncomputable def marginal (c : ZMod 2) (μ : Measure (ℤ → ι)) : Measure ℝ :=
  (μ.map S.proj).map (coord c)

/-- `\overline{λ}(𝖠, ν) < 0`: every `|g_j'|` is less than one. -/
theorem lyapBar_neg [Finite ι] (ν : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure ν] :
    S.lyapBar ν < 0 := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨y⟩ : Nonempty (ℤ → ι × ZMod 2) := nonempty_of_isProbabilityMeasure ν
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
    (fun p : ι × ZMod 2 => Real.log |S.ratio p|) ⟨y 0, Finset.mem_univ _⟩
  obtain ⟨q, -, hq⟩ := Finset.exists_max_image Finset.univ
    (fun p : ι × ZMod 2 => abs (Real.log |S.ratio p|)) ⟨y 0, Finset.mem_univ _⟩
  have hneg : Real.log |S.ratio p| < 0 :=
    Real.log_neg (abs_pos.2 (S.ratio_ne_zero p)) (S.abs_ratio_lt_one p)
  have hmeas : Measurable fun y : ℤ → ι × ZMod 2 => Real.log |S.ratio (y 0)| :=
    (Measurable.of_discrete (f := fun p : ι × ZMod 2 => Real.log |S.ratio p|)).comp
      (measurable_pi_apply 0)
  have hint : Integrable (fun y : ℤ → ι × ZMod 2 => Real.log |S.ratio (y 0)|) ν :=
    Integrable.of_bound hmeas.aestronglyMeasurable (abs (Real.log |S.ratio q|))
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact hq (y 0) (Finset.mem_univ _))
  calc S.lyapBar ν ≤ ∫ _, Real.log |S.ratio p| ∂ν :=
        integral_mono hint (integrable_const _) fun y => hp (y 0) (Finset.mem_univ _)
    _ = Real.log |S.ratio p| := by simp
    _ < 0 := hneg

end System

end BoxLike
