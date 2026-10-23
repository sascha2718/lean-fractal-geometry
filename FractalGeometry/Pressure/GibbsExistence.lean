import Mathlib
import FractalGeometry.LinearCocycles.Products
import FractalGeometry.Pressure.GibbsErgodicity
import FractalGeometry.Pressure.NormPotential
import FractalGeometry.Pressure.PartitionSums
import FractalGeometry.Pressure.PeriodicApproximation
import FractalGeometry.Pressure.QuasiMultiplicative
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.InvariantProbability
import FractalGeometry.Symbolic.Shift

namespace FractalGeometry

open MeasureTheory Filter Topology Set

open scoped Matrix.Norms.L2Operator

universe u

namespace MatrixTuple

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι]
  {A : ι → Matrix (Fin 2) (Fin 2) ℝ} {q C : ℝ} {μ : Measure (ℤ → ι)}

variable (A q C) in

def NormGibbsUpTo (μ : Measure (ℤ → ι)) (M : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → n ≤ M → ∀ w : Fin n → ι,
    C⁻¹ * (Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn w)‖ ^ q) ≤
        μ.real (cylinder w) ∧
      μ.real (cylinder w) ≤ C * (Real.exp (-(n * normPressure A q)) * ‖word A (List.ofFn w)‖ ^ q)

theorem NormGibbsUpTo.mono {M M' : ℕ} (h : NormGibbsUpTo A q C μ M) (hM : M' ≤ M) :
    NormGibbsUpTo A q C μ M' :=
  fun n hn hnM w => h n hn (hnM.trans hM) w

variable [TopologicalSpace ι] [DiscreteTopology ι] [MeasurableSingletonClass ι]

variable (A q C) in

theorem isClosed_setOf_normGibbsUpTo (M : ℕ) :
    IsClosed {ν : ProbabilityMeasure (ℤ → ι) | NormGibbsUpTo A q C (ν : Measure (ℤ → ι)) M} := by
  simp only [NormGibbsUpTo, ofPred_and, ofPred_forall]
  refine isClosed_iInter fun n => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    isClosed_iInter fun w => ?_
  exact (isClosed_le continuous_const (continuous_measureReal_cylinder _)).inter
    (isClosed_le (continuous_measureReal_cylinder _) continuous_const)

end MatrixTuple

namespace MatrixTuple

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {A : ι → Matrix (Fin 2) (Fin 2) ℝ} {q C : ℝ}

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

theorem normGibbsExistence : NormGibbsExistenceStatement.{u} := by
  intro ι _ _ _ _ A hA hqm q hq
  exact MatrixTuple.NormQuasiMultiplicative.exists_ergodic_hasNormGibbs hA hqm hq

end FractalGeometry
