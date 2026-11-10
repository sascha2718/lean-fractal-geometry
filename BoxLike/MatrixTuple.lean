module

/-
The thermodynamic vocabulary of `sec:lyapunov_exponents`, `sec:affinity_dim` and
`sec:gibbs_measures` for an arbitrary tuple `A : ι → Matrix (Fin 2) (Fin 2) ℝ`, as the article
uses it for planar self-affine sets in `thm:feng_entropy_as_limit`,
`thm:feng_entropy_kolmogorov_sinai`, `thm:feng_entropy_zero`, `thm:irred_eq_state` and
`thm:feng1`. A tuple of invertible matrices is one with `∀ i, (A i).det ≠ 0`, as in
`BoxLike/Classification.lean`. The box-like objects of `BoxLike/Pressure.lean` and
`BoxLike/Thermodynamic.lean` are the objects of the tuple `S.mat`, by definition.

* `MatrixTuple.word`, `MatrixTuple.word_append`: the product `A_𝐢 = A_{i_1} ⋯ A_{i_n}`.
* `MatrixTuple.svfSum`, `MatrixTuple.pressure`: the sums `∑_{|𝐢| = n} φ^s(A_𝐢)` and the
  singular value pressure `P(𝖠, s)`.
* `MatrixTuple.lyapunov₁`, `MatrixTuple.lyapunov₂`, `MatrixTuple.energyLim`: the Lyapunov
  exponents `λ_1(𝖠, μ)`, `λ_2(𝖠, μ)` and the `s`-energy `Λ(𝖠, μ, s)`.
* `MatrixTuple.IsEquilibriumState`, `MatrixTuple.HasGibbsBounds`: `eq:eq_state_def` and the
  Gibbs bounds of `thm:irred_eq_state`.
* `System.matWord_eq_word`, `System.svfSum_eq_tuple`, `System.pressure_eq_tuple`,
  `System.lyapunov₁_eq_tuple`, `System.lyapunov₂_eq_tuple`, `System.energyLim_eq_tuple`,
  `System.isEquilibriumState_iff_tuple`, `System.hasGibbsBounds_iff_tuple`: the box-like
  objects are the tuple objects of `S.mat`.
-/
public import BoxLike.Thermodynamic

@[expose] public section

namespace BoxLike

open MeasureTheory Filter
open scoped Matrix.Norms.L2Operator

namespace MatrixTuple

variable {ι : Type*} (A : ι → Matrix (Fin 2) (Fin 2) ℝ)

/-- The product `A_𝐢 = A_{i_1} ⋯ A_{i_n}` of the matrices along a finite word
(`sec:box_like_self_affine`). -/
def word (w : List ι) : Matrix (Fin 2) (Fin 2) ℝ := (w.map A).prod

@[simp] theorem word_nil : word A [] = 1 := rfl

/-- The product along a concatenation is the product of the two products. -/
theorem word_append (w w' : List ι) : word A (w ++ w') = word A w * word A w' := by
  simp [word]

/-- The sum `∑_{|𝐢| = n} φ^s(A_𝐢)` of `sec:affinity_dim`. -/
noncomputable def svfSum [Fintype ι] (s : ℝ) (n : ℕ) : ℝ :=
  ∑ w : Fin n → ι, svf s (word A (List.ofFn w))

/-- The singular value pressure `P(𝖠, s)` of `sec:affinity_dim`, as the infimum of
`n⁻¹ log ∑_{|𝐢| = n} φ^s(A_𝐢)` over `n ≥ 1`. -/
noncomputable def pressure [Fintype ι] (s : ℝ) : ℝ :=
  sInf ((fun n : ℕ => Real.log (svfSum A s n) / n) '' Set.Ici 1)

variable [MeasurableSpace ι]

/-- The Lyapunov exponent `λ_1(𝖠, μ) = lim_n n⁻¹ ∫ log α_1(A_{𝐢|_n}) dμ(𝐢)` of
`sec:lyapunov_exponents`. -/
noncomputable def lyapunov₁ (μ : Measure (ℤ → ι)) : ℝ :=
  limUnder atTop fun n : ℕ => (∫ x, Real.log ‖word A (futureWord x n)‖ ∂μ) / n

/-- The Lyapunov exponent `λ_2(𝖠, μ) = lim_n n⁻¹ ∫ log α_2(A_{𝐢|_n}) dμ(𝐢)` of
`sec:lyapunov_exponents`, with `α_2(A) = |det A| / ‖A‖`. -/
noncomputable def lyapunov₂ (μ : Measure (ℤ → ι)) : ℝ :=
  limUnder atTop fun n : ℕ =>
    (∫ x, Real.log (|(word A (futureWord x n)).det| / ‖word A (futureWord x n)‖) ∂μ) / n

/-- The `s`-energy `Λ(𝖠, μ, s) = lim_n n⁻¹ ∫ log φ^s(A_{𝐢|_n}) dμ(𝐢)` of `eq:energy_def`. -/
noncomputable def energyLim (s : ℝ) (μ : Measure (ℤ → ι)) : ℝ :=
  limUnder atTop fun n : ℕ => (∫ x, Real.log (svf s (word A (futureWord x n))) ∂μ) / n

/-- `μ` is an `s`-equilibrium state of the tuple, `eq:eq_state_def`:
`P(𝖠, s) = h(μ) + Λ(𝖠, μ, s)`. -/
def IsEquilibriumState [Fintype ι] (s : ℝ) (μ : Measure (ℤ → ι)) : Prop :=
  pressure A s = entropy μ + energyLim A s μ

/-- The Gibbs bounds of `thm:irred_eq_state` for a measure `μ` on `Σ`:
`C⁻¹ exp(-|𝐢| P(𝖠, s)) φ^s(A_𝐢) ≤ μ([𝐢]) ≤ C exp(-|𝐢| P(𝖠, s)) φ^s(A_𝐢)` for all finite words
`𝐢`, with a constant `C ≥ 1`. -/
def HasGibbsBounds [Fintype ι] (s : ℝ) (μ : Measure (ℤ → ι)) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ w : Fin n → ι,
    C⁻¹ * (Real.exp (-(n * pressure A s)) * svf s (word A (List.ofFn w))) ≤
        μ.real (cylinder w) ∧
      μ.real (cylinder w) ≤
        C * (Real.exp (-(n * pressure A s)) * svf s (word A (List.ofFn w)))

end MatrixTuple

namespace System

variable {ι : Type*} (S : System ι)

/-- The product `A_𝐢` of a box-like system is the product of the tuple `S.mat`. -/
theorem matWord_eq_word (w : List ι) : S.matWord w = MatrixTuple.word S.mat w := rfl

/-- The singular value sums of a box-like system are those of the tuple `S.mat`. -/
theorem svfSum_eq_tuple [Fintype ι] (s : ℝ) (n : ℕ) :
    S.svfSum s n = MatrixTuple.svfSum S.mat s n := rfl

/-- The pressure of a box-like system is the pressure of the tuple `S.mat`. -/
theorem pressure_eq_tuple [Fintype ι] (s : ℝ) : S.pressure s = MatrixTuple.pressure S.mat s :=
  rfl

variable [MeasurableSpace ι]

/-- `λ_1(𝖠, μ)` of a box-like system is the exponent of the tuple `S.mat`. -/
theorem lyapunov₁_eq_tuple (μ : Measure (ℤ → ι)) :
    S.lyapunov₁ μ = MatrixTuple.lyapunov₁ S.mat μ := rfl

/-- `λ_2(𝖠, μ)` of a box-like system is the exponent of the tuple `S.mat`. -/
theorem lyapunov₂_eq_tuple (μ : Measure (ℤ → ι)) :
    S.lyapunov₂ μ = MatrixTuple.lyapunov₂ S.mat μ := rfl

/-- The `s`-energy of a box-like system is the energy of the tuple `S.mat`. -/
theorem energyLim_eq_tuple (s : ℝ) (μ : Measure (ℤ → ι)) :
    S.energyLim s μ = MatrixTuple.energyLim S.mat s μ := rfl

/-- The equilibrium states of a box-like system are those of the tuple `S.mat`. -/
theorem isEquilibriumState_iff_tuple [Fintype ι] (s : ℝ) (μ : Measure (ℤ → ι)) :
    S.IsEquilibriumState s μ ↔ MatrixTuple.IsEquilibriumState S.mat s μ := Iff.rfl

/-- The Gibbs bounds of a box-like system are those of the tuple `S.mat`. -/
theorem hasGibbsBounds_iff_tuple [Fintype ι] (s : ℝ) (μ : Measure (ℤ → ι)) :
    S.HasGibbsBounds s μ ↔ MatrixTuple.HasGibbsBounds S.mat s μ := Iff.rfl

end System

end BoxLike
