module

/-
`thm:irred_eq_state` (tex lines 2113 to 2122) for box-like tuples with rotations: for every
`s > 0` there is a unique invariant `s`-equilibrium state; it is ergodic and has the Gibbs bounds.
The article quotes the proposition from Feng–Käenmäki for irreducible tuples; a tuple with
rotations need not be irreducible, and no literature premise is used.

For `0 < s < 2` the candidate is the image `μ_G = q_*μ_1` of Bowen's ergodic Gibbs measure `μ_1`
for `f_{1,s}` on `Σ_Z`, an ergodic probability measure with the Gibbs bounds, with a constant
`K` (`System.exists_isGibbs_potential₁`, `System.hasGibbsBounds_map_unCode`,
`ergodic_map_unCode`). For an invariant `s`-equilibrium state `μ` and `n ≥ 1`, the entropy and
the energy are at most their averages at level `n`, so
`n P(𝖠, s) ≤ H_μ(𝒫_0^{n-1}) + ∑_{|w| = n} μ([w]) log φ^s(A_w)`, and the lower Gibbs bound
`φ^s(A_w) ≤ K e^{n P(𝖠, s)} μ_G([w])` turns this into the bound
`D_n(μ ‖ μ_G) = ∑_{|w| = n} μ([w]) log(μ([w]) / μ_G([w])) ≤ log K` on the relative entropy of
the cylinder partitions. Bounded relative entropy gives `μ ≪ μ_G`
(`absolutelyContinuous_of_blockRelEntropy_le`), and an invariant probability measure absolutely
continuous with respect to an ergodic one equals it. Hence `μ = μ_G`. For `s ≥ 2` the
equilibrium state is the Bernoulli measure of `thm:bernoulli_equilibrium`.

* `System.IsEquilibriumState.blockRelEntropy_le`: `D_n(μ ‖ ν) ≤ log K` for an invariant
  `s`-equilibrium state `μ` and a measure `ν` with the Gibbs bounds with constant `K`.
* `System.IsEquilibriumState.absolutelyContinuous_of_hasGibbsBounds`,
  `System.IsEquilibriumState.eq_of_hasGibbsBounds`: an invariant `s`-equilibrium state is
  absolutely continuous with respect to every invariant probability measure with the Gibbs
  bounds, and equals every ergodic one.
* `System.IsEquilibriumState.eq_map_unCode`: for `0 < s < 2` every invariant `s`-equilibrium
  state is the image `q_*μ_1` of the ergodic `s`-Gibbs measure `μ_1` on `Σ_Z`.
* `System.IsEquilibriumState.hasGibbsBounds_of_withRotations`,
  `System.IsEquilibriumState.ergodic_of_withRotations`, `System.unique_of_withRotations`: the
  Gibbs bounds, ergodicity and uniqueness for a tuple with rotations and `s > 0`.
* `equilibriumGibbs`: `EquilibriumGibbsStatement` is a theorem.
* `System.existsUnique_isEquilibriumState_of_withRotations`,
  `System.irred_eq_state_of_withRotations`: existence and uniqueness of the invariant
  `s`-equilibrium state, and `thm:irred_eq_state` for a tuple with rotations and every `s > 0`.
-/
public import BoxLike.EquilibriumExistence
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.FraserJordanJurga.Gibbs
public import BoxLike.Support.RelativeEntropy
public import BoxLike.TupleEquilibriumLarge
public import BoxLike.TupleErgodicEquilibrium

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

namespace System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {S : System ι} {s : ℝ}

/-! ### The relative entropy of an equilibrium state -/

/-- The relative entropy bound in the proof of `thm:irred_eq_state` for tuples with rotations
(tex lines 2113 to 2122): an invariant `s`-equilibrium state `μ`, `s ≥ 0`, and a measure `ν`
with the Gibbs bounds with constant `K` satisfy
`D_n(μ ‖ ν) = ∑_{|w| = n} μ([w]) log(μ([w]) / ν([w])) ≤ log K` for every `n ≥ 1`. By
`eq:eq_state_def`, `n P(𝖠, s) ≤ H_μ(𝒫_0^{n-1}) + ∑_{|w| = n} μ([w]) log φ^s(A_w)`, and the lower
Gibbs bound gives `log φ^s(A_w) ≤ log K + n P(𝖠, s) + log ν([w])`. -/
theorem IsEquilibriumState.blockRelEntropy_le (hs : 0 ≤ s) {μ ν : Measure (ℤ → ι)}
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) {K : ℝ} (hK : S.HasGibbsBoundsWith K s ν) {n : ℕ}
    (hn : 0 < n) : blockRelEntropy μ ν n ≤ Real.log K := by
  have hK0 : 0 < K := one_pos.trans_le hK.1
  have hpos := hK.measureReal_cylinder_pos hn
  have hblock := (MatrixTuple.isEquilibriumState_iff_forall S.det_mat_ne_zero hs hinv).1 heq n hn
  change (n : ℝ) * S.pressure s ≤ blockEntropy μ n +
    ∑ w : Fin n → ι, μ.real (cylinder w) * Real.log (svf s (S.matWord (List.ofFn w))) at hblock
  have hlog : ∀ w : Fin n → ι, Real.log (svf s (S.matWord (List.ofFn w))) ≤
      Real.log K + n * S.pressure s + Real.log (ν.real (cylinder w)) := by
    intro w
    have hl := ((hK.2 n hn w).1)
    have hφ : svf s (S.matWord (List.ofFn w)) ≤
        K * ν.real (cylinder w) * Real.exp (n * S.pressure s) := by
      rw [inv_mul_le_iff₀ hK0] at hl
      have e := Real.exp_pos (n * S.pressure s)
      calc svf s (S.matWord (List.ofFn w))
          = Real.exp (-(n * S.pressure s)) * svf s (S.matWord (List.ofFn w)) *
              Real.exp (n * S.pressure s) := by
            rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
              mul_one]
        _ ≤ K * ν.real (cylinder w) * Real.exp (n * S.pressure s) :=
            mul_le_mul_of_nonneg_right hl e.le
    have h := Real.log_le_log (S.svf_matWord_pos s _) hφ
    rwa [Real.log_mul (mul_pos hK0 (hpos w)).ne' (Real.exp_pos _).ne', Real.log_exp,
      Real.log_mul hK0.ne' (hpos w).ne', add_right_comm] at h
  have hsum : ∑ w : Fin n → ι, μ.real (cylinder w) * Real.log (svf s (S.matWord (List.ofFn w)))
      ≤ Real.log K + n * S.pressure s +
        ∑ w : Fin n → ι, μ.real (cylinder w) * Real.log (ν.real (cylinder w)) := by
    calc ∑ w : Fin n → ι, μ.real (cylinder w) * Real.log (svf s (S.matWord (List.ofFn w)))
        ≤ ∑ w : Fin n → ι, μ.real (cylinder w) *
            (Real.log K + n * S.pressure s + Real.log (ν.real (cylinder w))) :=
          Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hlog w) measureReal_nonneg
      _ = (∑ w : Fin n → ι, μ.real (cylinder w)) * (Real.log K + n * S.pressure s) +
            ∑ w : Fin n → ι, μ.real (cylinder w) * Real.log (ν.real (cylinder w)) := by
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun w _ => by ring
      _ = _ := by rw [sum_measureReal_cylinder μ n, one_mul]
  rw [blockRelEntropy_eq n fun w => (hpos w).ne']
  linarith

/-- An invariant `s`-equilibrium state, `s ≥ 0`, is absolutely continuous with respect to every
invariant probability measure with the Gibbs bounds of `thm:irred_eq_state`: the relative
entropy of the cylinder partitions is bounded (`IsEquilibriumState.blockRelEntropy_le`). -/
theorem IsEquilibriumState.absolutelyContinuous_of_hasGibbsBounds (hs : 0 ≤ s)
    {μ ν : Measure (ℤ → ι)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hinv : MeasurePreserving (shift 1) μ μ) (hνinv : MeasurePreserving (shift 1) ν ν)
    (heq : S.IsEquilibriumState s μ) (hg : S.HasGibbsBounds s ν) : μ ≪ ν := by
  obtain ⟨K, hK⟩ := (S.hasGibbsBounds_iff).1 hg
  exact absolutelyContinuous_of_blockRelEntropy_le hinv hνinv
    (fun n hn => hK.measureReal_cylinder_pos hn) fun n hn => heq.blockRelEntropy_le hs hinv hK hn

/-- An invariant `s`-equilibrium state, `s ≥ 0`, equals every ergodic probability measure with
the Gibbs bounds of `thm:irred_eq_state`: it is absolutely continuous with respect to it. -/
theorem IsEquilibriumState.eq_of_hasGibbsBounds (hs : 0 ≤ s) {μ ν : Measure (ℤ → ι)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hinv : MeasurePreserving (shift 1) μ μ)
    (hν : Ergodic (shift 1) ν) (heq : S.IsEquilibriumState s μ) (hg : S.HasGibbsBounds s ν) :
    μ = ν :=
  hν.eq_of_absolutelyContinuous hinv
    (heq.absolutelyContinuous_of_hasGibbsBounds hs hinv hν.toMeasurePreserving hg)

/-! ### The equilibrium state of a tuple with rotations -/

/-- `thm:irred_eq_state` for tuples with rotations, the identification of the equilibrium
state: for `0 < s < 2` every invariant `s`-equilibrium state is the image `q_*μ_1` on `Σ` of an
ergodic `s`-Gibbs probability measure `μ_1` carried by `Σ_Z` for `f_{1,s}`. The measure
`q_*μ_1` is ergodic and has the Gibbs bounds (`System.hasGibbsBounds_map_unCode`). -/
theorem IsEquilibriumState.eq_map_unCode (hs0 : 0 < s) (hs2 : s < 2)
    {ν : Measure (ℤ → ι × ZMod 2)} [IsProbabilityMeasure ν] (hν : ν (subshift S.o)ᶜ = 0)
    (herg : Ergodic (shift 1) ν) (hg : IsGibbs S.o (S.potential₁ s) ν) {μ : Measure (ℤ → ι)}
    [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) : μ = ν.map unCode :=
  heq.eq_of_hasGibbsBounds hs0.le hinv (ergodic_map_unCode herg)
    (S.hasGibbsBounds_map_unCode hs0 hs2 hν hg)

/-- `thm:irred_eq_state` for tuples with rotations, the Gibbs bounds: for a box-like tuple with
rotations and `s > 0` every invariant `s`-equilibrium state `μ` satisfies
`C⁻¹ exp(-|𝐢| P(𝖠, s)) φ^s(A_𝐢) ≤ μ([𝐢]) ≤ C exp(-|𝐢| P(𝖠, s)) φ^s(A_𝐢)` for all finite words
`𝐢`. For `0 < s < 2`, `μ = q_*μ_1` (`IsEquilibriumState.eq_map_unCode`); for `s ≥ 2` it is the
Bernoulli measure of `thm:bernoulli_equilibrium`. -/
theorem IsEquilibriumState.hasGibbsBounds_of_withRotations (hrot : S.WithRotations) (hs0 : 0 < s)
    {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) : S.HasGibbsBounds s μ := by
  rcases lt_or_ge s 2 with hs2 | hs2
  · obtain ⟨ν, hp, hν, herg, hg⟩ := S.exists_isGibbs_potential₁ hrot s
    rw [heq.eq_map_unCode hs0 hs2 hν herg hg hinv]
    exact S.hasGibbsBounds_map_unCode hs0 hs2 hν hg
  · have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
    rw [heq.eq_bernoulli hinv hs2]
    exact S.hasGibbsBounds_bernoulli hs2

/-- `thm:irred_eq_state` for tuples with rotations, ergodicity: for a box-like tuple with
rotations and `s > 0` every invariant `s`-equilibrium state is ergodic. For `0 < s < 2` it is the
factor `q_*μ_1` of the ergodic measure `μ_1`; for `s ≥ 2` it is a Bernoulli measure. -/
theorem IsEquilibriumState.ergodic_of_withRotations (hrot : S.WithRotations) (hs0 : 0 < s)
    {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] (hinv : MeasurePreserving (shift 1) μ μ)
    (heq : S.IsEquilibriumState s μ) : Ergodic (shift 1) μ := by
  rcases lt_or_ge s 2 with hs2 | hs2
  · obtain ⟨ν, hp, hν, herg, hg⟩ := S.exists_isGibbs_potential₁ hrot s
    rw [heq.eq_map_unCode hs0 hs2 hν herg hg hinv]
    exact ergodic_map_unCode herg
  · exact heq.ergodic_of_two_le hinv hs2

variable (S)

/-- `thm:irred_eq_state` for tuples with rotations, uniqueness: two invariant `s`-equilibrium
states of a box-like tuple with rotations coincide, for every `s > 0`. For `0 < s < 2` both are
`q_*μ_1`; for `s ≥ 2` both are the Bernoulli measure of `thm:bernoulli_equilibrium`. -/
theorem unique_of_withRotations (hrot : S.WithRotations) (hs0 : 0 < s)
    (μ μ' : Measure (ℤ → ι)) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hinv : MeasurePreserving (shift 1) μ μ) (hinv' : MeasurePreserving (shift 1) μ' μ')
    (heq : S.IsEquilibriumState s μ) (heq' : S.IsEquilibriumState s μ') : μ = μ' := by
  rcases lt_or_ge s 2 with hs2 | hs2
  · obtain ⟨ν, hp, hν, herg, hg⟩ := S.exists_isGibbs_potential₁ hrot s
    rw [heq.eq_map_unCode hs0 hs2 hν herg hg hinv, heq'.eq_map_unCode hs0 hs2 hν herg hg hinv']
  · exact (heq.eq_bernoulli hinv hs2).trans (heq'.eq_bernoulli hinv' hs2).symm

end System

/-- `EquilibriumGibbsStatement` is a theorem: for a box-like tuple with rotations and
`0 < s < 2` every invariant `s`-equilibrium state has the Gibbs bounds of `thm:irred_eq_state`
(tex lines 2113 to 2122). No literature premise is used. -/
theorem equilibriumGibbs : EquilibriumGibbsStatement.{u} :=
  fun _ hrot _ hs0 _ _ _ hinv heq => heq.hasGibbsBounds_of_withRotations hrot hs0 hinv

namespace System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {s : ℝ}

/-- `thm:irred_eq_state` for tuples with rotations, existence and uniqueness: for a box-like
tuple with rotations and every `s > 0` there is exactly one invariant probability measure that
is an `s`-equilibrium state. Existence is the variational construction
(`System.exists_isEquilibriumState`). -/
theorem existsUnique_isEquilibriumState_of_withRotations (hrot : S.WithRotations) (hs0 : 0 < s) :
    ∃! μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
      S.IsEquilibriumState s μ := by
  have : Nonempty ι := ⟨hrot.1.choose⟩
  obtain ⟨μ, hprob, hinv, heq⟩ := S.exists_isEquilibriumState hs0.le
  exact ⟨μ, ⟨hprob, hinv, heq⟩, fun ν ⟨hν, hνinv, hνeq⟩ =>
    S.unique_of_withRotations hrot hs0 ν μ hνinv hinv hνeq heq⟩

/-- `thm:irred_eq_state` for box-like tuples with rotations (tex lines 2113 to 2122): for each
`s > 0` there is an invariant `s`-equilibrium state `μ`, every invariant `s`-equilibrium state
equals `μ`, `μ` is ergodic, and there is a constant `C ≥ 1` with
`C⁻¹ exp(-|𝐢| P(𝖠, s)) φ^s(A_𝐢) ≤ μ([𝐢]) ≤ C exp(-|𝐢| P(𝖠, s)) φ^s(A_𝐢)` for all finite words
`𝐢`. The article states the proposition for irreducible tuples and quotes it from
Feng–Käenmäki; for tuples with rotations it is proved here with no literature premise. -/
theorem irred_eq_state_of_withRotations (hrot : S.WithRotations) (hs0 : 0 < s) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
      S.IsEquilibriumState s μ ∧
      (∀ ν : Measure (ℤ → ι), IsProbabilityMeasure ν → MeasurePreserving (shift 1) ν ν →
        S.IsEquilibriumState s ν → ν = μ) ∧
      Ergodic (shift 1) μ ∧ S.HasGibbsBounds s μ := by
  have : Nonempty ι := ⟨hrot.1.choose⟩
  obtain ⟨μ, hprob, hinv, heq⟩ := S.exists_isEquilibriumState hs0.le
  refine ⟨μ, hprob, hinv, heq, fun ν hν hνinv hνeq => ?_,
    heq.ergodic_of_withRotations hrot hs0 hinv, heq.hasGibbsBounds_of_withRotations hrot hs0 hinv⟩
  exact S.unique_of_withRotations hrot hs0 ν μ hνinv hinv hνeq heq

end System

end BoxLike
