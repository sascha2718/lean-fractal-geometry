module

/-
The existence half of Feng–Käenmäki, Proposition 1.2 (`thm:irred_eq_state`, tex lines 2113 to
2239): a quasi-multiplicative tuple of invertible planar matrices has, for every `q > 0`, an
ergodic invariant probability measure on `Σ = ℤ → ι` with the Gibbs property of the potential
`‖·‖^q`. The source is De-Jun Feng and Antti Käenmäki, *Equilibrium states of the pressure
function for products of matrices*, Discrete Contin. Dyn. Syst. 30 (2011), Proposition 1.2; the
proof here follows the architecture of Bowen's theorem in `BoxLike/Bowen/`.

The proof has three steps. The approximating measures `ν_N` of
`BoxLike/QuasiMultiplicative/GibbsMeasurePeriodic.lean` are invariant probability measures, and
every word satisfies the Gibbs bounds with a fixed constant `C` under `ν_N` for all large `N`
(`NormQMConstants.exists_eventually_gibbs`); so for every length `M` some `ν_N` has the Gibbs
bounds up to length `M`. A weak-star limit point is an invariant Gibbs measure
(`exists_hasNormGibbs_of_forall_normGibbsUpTo`): the sets of these measures are weak-star closed,
non-empty and decreasing in the compact space of Borel probability measures on `Σ`. A Gibbs
measure is ergodic (`HasNormGibbs.ergodic` in
`BoxLike/QuasiMultiplicative/GibbsMeasureErgodic.lean`).

* `MatrixTuple.NormGibbsUpTo`, `MatrixTuple.NormGibbsUpTo.mono`: the Gibbs bounds of `‖·‖^q` for
  the cylinders of length at most `M`.
* `MatrixTuple.isClosed_setOf_normGibbsUpTo`: they are a weak-star closed condition.
* `MatrixTuple.exists_hasNormGibbs_of_forall_normGibbsUpTo`: the limit step.
* `MatrixTuple.NormQuasiMultiplicative.exists_ergodic_hasNormGibbs`: the existence of an ergodic
  invariant Gibbs probability measure.
* `normGibbsExistence`: `NormGibbsExistenceStatement`.
-/
public import BoxLike.InvariantMeasures
public import BoxLike.QuasiMultiplicative.GibbsMeasureErgodic
public import BoxLike.QuasiMultiplicative.GibbsMeasurePeriodic

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator

universe u

namespace MatrixTuple

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι]
  {A : ι → Matrix (Fin 2) (Fin 2) ℝ} {q C : ℝ} {μ : Measure (ℤ → ι)}

/-! ### The Gibbs bounds up to a given length -/

variable (A q C) in
/-- The Gibbs bounds of `‖·‖^q` with constant `C` for the cylinders of length `1 ≤ n ≤ M`
(`thm:irred_eq_state`, the limit step). -/
def NormGibbsUpTo (μ : Measure (ℤ → ι)) (M : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → n ≤ M → ∀ w : Fin n → ι,
    C⁻¹ * (Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn w)‖ ^ q) ≤
        μ.real (cylinder w) ∧
      μ.real (cylinder w) ≤ C * (Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn w)‖ ^ q)

/-- The Gibbs bounds up to length `M` give those up to every length `M' ≤ M`. -/
theorem NormGibbsUpTo.mono {M M' : ℕ} (h : NormGibbsUpTo A q C μ M) (hM : M' ≤ M) :
    NormGibbsUpTo A q C μ M' :=
  fun n hn hnM w => h n hn (hnM.trans hM) w

variable [TopologicalSpace ι] [DiscreteTopology ι] [MeasurableSingletonClass ι]

variable (A q C) in
/-- The Gibbs bounds up to length `M` are a weak-star closed condition on the Borel probability
measures on `Σ`: each bound concerns the continuous mass of a clopen cylinder
(`thm:irred_eq_state`, the limit step). -/
theorem isClosed_setOf_normGibbsUpTo (M : ℕ) :
    IsClosed {ν : ProbabilityMeasure (ℤ → ι) | NormGibbsUpTo A q C (ν : Measure (ℤ → ι)) M} := by
  simp only [NormGibbsUpTo, ofPred_and, ofPred_forall]
  refine isClosed_iInter fun n => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    isClosed_iInter fun w => ?_
  exact (isClosed_le continuous_const (continuous_measureReal_cylinder _)).inter
    (isClosed_le (continuous_measureReal_cylinder _) continuous_const)

end MatrixTuple

/-! ### The limit step -/

namespace MatrixTuple

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {A : ι → Matrix (Fin 2) (Fin 2) ℝ} {q C : ℝ}

/-- The limit step of Feng–Käenmäki, Proposition 1.2 (`thm:irred_eq_state`, tex lines 2113 to
2234): if `C > 0` and for every length `M` some invariant probability measure on `Σ` has the
Gibbs bounds of `‖·‖^q` with constant `C` up to length `M`, then some invariant probability
measure has the Gibbs property of `‖·‖^q`. The sets of these measures form a decreasing sequence
of non-empty weak-star closed subsets of the compact space of Borel probability measures. -/
theorem exists_hasNormGibbs_of_forall_normGibbsUpTo (hC : 0 < C)
    (h : ∀ M : ℕ, ∃ ν : Measure (ℤ → ι), IsProbabilityMeasure ν ∧
      MeasurePreserving (shift 1) ν ν ∧ NormGibbsUpTo A q C ν M) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
      HasNormGibbs A q μ := by
  let : TopologicalSpace ι := ⊥
  have : DiscreteTopology ι := ⟨rfl⟩
  set K : ℕ → Set (ProbabilityMeasure (ℤ → ι)) := fun M =>
    InvariantMeasures ι ∩ {ν | NormGibbsUpTo A q C (ν : Measure (ℤ → ι)) M} with hK
  have hclosed : ∀ M, IsClosed (K M) := fun M =>
    isClosed_invariantMeasures.inter (isClosed_setOf_normGibbsUpTo A q C M)
  have hmono : ∀ M, K (M + 1) ⊆ K M := fun M ν hν => ⟨hν.1, hν.2.mono M.le_succ⟩
  have hne : ∀ M, (K M).Nonempty := fun M => by
    obtain ⟨ν, hp, hinv, hg⟩ := h M
    exact ⟨⟨ν, hp⟩, hinv, hg⟩
  obtain ⟨ν, hν⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hmono hne
    (hclosed 0).isCompact hclosed
  rw [mem_iInter] at hν
  exact ⟨ν, inferInstance, (hν 0).1, C, hC, fun n hn w => (hν n).2 n hn le_rfl w⟩

/-- **Existence of the Gibbs measure** (Feng–Käenmäki, Proposition 1.2, `thm:irred_eq_state`,
tex lines 2113 to 2122): for a quasi-multiplicative tuple of invertible planar matrices over a
non-empty finite alphabet and `q > 0` there is an ergodic invariant probability measure on `Σ`
with the Gibbs property of `‖·‖^q`. The approximating measures `ν_N` have the Gibbs bounds up to
every length for large `N`, a weak-star limit point is an invariant Gibbs measure, and a Gibbs
measure is ergodic. -/
theorem NormQuasiMultiplicative.exists_ergodic_hasNormGibbs [Nonempty ι]
    (hA : ∀ i, (A i).det ≠ 0) (hqm : NormQuasiMultiplicative A) (hq : 0 < q) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ Ergodic (shift 1) μ ∧ HasNormGibbs A q μ := by
  obtain ⟨m, c, h⟩ := hqm.exists_normQMConstants hq.le
  obtain ⟨C, hC, hev⟩ := h.exists_eventually_gibbs hA hq.le
  have hM : ∀ M : ℕ, ∀ᶠ p in atTop, NormGibbsUpTo A q C (normPeriodicMeasure A q p) M := by
    intro M
    have h1 : ∀ n ∈ Finset.range (M + 1), ∀ᶠ p in atTop, 0 < n → ∀ w : Fin n → ι,
        C⁻¹ * (Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn w)‖ ^ q) ≤
            (normPeriodicMeasure A q p).real (cylinder w) ∧
          (normPeriodicMeasure A q p).real (cylinder w) ≤
            C * (Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn w)‖ ^ q) := by
      intro n _
      by_cases hn : 0 < n
      · exact (eventually_all.2 fun w => hev n hn w).mono fun p hp _ => hp
      · exact Eventually.of_forall fun p hn' => absurd hn' hn
    filter_upwards [(eventually_all_finset _).2 h1] with p hp n hn hnM w
    exact hp n (Finset.mem_range.2 (Nat.lt_succ_of_le hnM)) hn w
  obtain ⟨μ, hprob, hinv, hg⟩ := exists_hasNormGibbs_of_forall_normGibbsUpTo hC fun M => by
    obtain ⟨p, hp⟩ := (hM M).exists
    exact ⟨normPeriodicMeasure A q p, isProbabilityMeasure_normPeriodicMeasure hA p,
      measurePreserving_normPeriodicMeasure p, hp⟩
  exact ⟨μ, hprob, hg.ergodic hinv hqm hq.le, hg⟩

end MatrixTuple

/-- **Feng–Käenmäki, Proposition 1.2, existence of the Gibbs measure** (`thm:irred_eq_state`,
tex lines 2113 to 2122): `NormGibbsExistenceStatement` holds. For a non-empty finite alphabet, a
quasi-multiplicative tuple of invertible planar matrices and `q > 0`, some ergodic invariant
probability measure on the two-sided shift `Σ = ℤ → ι` has the Gibbs property of `‖·‖^q`. The
source is Feng–Käenmäki, Discrete Contin. Dyn. Syst. 30 (2011), Proposition 1.2. No literature
premise is used. -/
theorem normGibbsExistence : NormGibbsExistenceStatement.{u} := by
  intro ι _ _ _ _ A hA hqm q hq
  exact MatrixTuple.NormQuasiMultiplicative.exists_ergodic_hasNormGibbs hA hqm hq

end BoxLike
