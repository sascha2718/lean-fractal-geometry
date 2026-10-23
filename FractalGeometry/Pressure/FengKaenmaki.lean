import Mathlib
import FractalGeometry.LinearCocycles.Classification
import FractalGeometry.Pressure.GibbsExistence
import FractalGeometry.Pressure.IrreducibleMatrices
import FractalGeometry.Pressure.NormEquilibriumStatement
import FractalGeometry.Pressure.NormPotential
import FractalGeometry.Pressure.NormUniqueness
import FractalGeometry.Pressure.NormExistence
import FractalGeometry.Pressure.QuasiMultiplicative
import FractalGeometry.Symbolic.NaturalExtension
import FractalGeometry.Symbolic.OneSidedShift
import FractalGeometry.Symbolic.Shift

namespace FractalGeometry

open MeasureTheory

universe u

/-!
Planar invertible-matrix specialisations of the Gibbs and uniqueness parts of
Proposition 1.2 of De-Jun Feng and Antti Käenmäki, "Equilibrium states of the
pressure function for products of matrices", Discrete and Continuous Dynamical
Systems 30(3) (2011), 699–708, doi:10.3934/dcds.2011.30.699,
arXiv:1009.3129v1. The existence endpoint supplies an ergodic equilibrium state
with Gibbs bounds. Pressure differentiability is not asserted here.
-/

theorem MatrixTuple.exists_ergodic_hasNormGibbs_of_irreducible
    {ι : Type u} [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {A : ι → Matrix (Fin 2) (Fin 2) ℝ} (hA : ∀ i, (A i).det ≠ 0) (hirr : TupleIrreducible A)
    {q : ℝ} (hq : 0 < q) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ Ergodic (shift 1) μ ∧
      MatrixTuple.HasNormGibbs A q μ :=
  normGibbsExistence A hA (MatrixTuple.normQuasiMultiplicative_of_irreducible hirr) hq

theorem MatrixTuple.exists_ergodic_hasNormGibbs_forall_eq (h : NormGibbsExistenceStatement.{u})
    {ι : Type u} [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {A : ι → Matrix (Fin 2) (Fin 2) ℝ} (hA : ∀ i, (A i).det ≠ 0) (hirr : TupleIrreducible A)
    {q : ℝ} (hq : 0 < q) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ Ergodic (shift 1) μ ∧
      MatrixTuple.HasNormGibbs A q μ ∧
      ∀ μ' : Measure (ℤ → ι), IsProbabilityMeasure μ' → MeasurePreserving (shift 1) μ' μ' →
        MatrixTuple.IsNormEquilibrium A q μ' → μ' = μ := by
  obtain ⟨μ, hμ, herg, hG⟩ := h A hA (MatrixTuple.normQuasiMultiplicative_of_irreducible hirr) hq
  exact ⟨μ, hμ, herg, hG, fun μ' _ hinv' heq' => heq'.eq_of_hasNormGibbs hA hq.le hinv' herg hG⟩

theorem fengKaenmakiNormEquilibrium_of_normGibbsExistence (h : NormGibbsExistenceStatement.{u}) :
    FengKaenmakiNormEquilibrium.{u} := by
  intro ι _ _ _ A hA hirr q hq ν _ hν heq
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure ν).some 0⟩
  obtain ⟨μG, hμG, -, hG, huniq⟩ := MatrixTuple.exists_ergodic_hasNormGibbs_forall_eq h hA hirr hq
  have key : ∀ (ν' : Measure (ℕ → ι)) [IsProbabilityMeasure ν'],
      MeasurePreserving shiftPlus ν' ν' → MatrixTuple.IsNormEquilibriumPlus A q ν' →
        ν' = μG.map eta := by
    intro ν' _ hν' heq'
    obtain ⟨μ, hμ, hinv, rfl⟩ := exists_map_eta_eq hν'
    rw [huniq μ hμ hinv ((MatrixTuple.isNormEquilibriumPlus_map_eta_iff μ).1 heq')]
  refine ⟨?_, fun ν' _ hν' heq' => (key ν' hν' heq').trans (key ν hν heq).symm⟩
  rw [key ν hν heq, MatrixTuple.hasNormGibbsPlus_map_eta_iff]
  exact hG

theorem fengKaenmakiNormEquilibrium_holds : FengKaenmakiNormEquilibrium.{u} :=
  fengKaenmakiNormEquilibrium_of_normGibbsExistence normGibbsExistence

theorem MatrixTuple.exists_unique_normEquilibrium
    {ι : Type u} [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {A : ι → Matrix (Fin 2) (Fin 2) ℝ} (hA : ∀ i, (A i).det ≠ 0) (hirr : TupleIrreducible A)
    {q : ℝ} (hq : 0 < q) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ Ergodic (shift 1) μ ∧
      MatrixTuple.IsNormEquilibrium A q μ ∧ MatrixTuple.HasNormGibbs A q μ ∧
      ∀ μ' : Measure (ℤ → ι), IsProbabilityMeasure μ' → MeasurePreserving (shift 1) μ' μ' →
        MatrixTuple.IsNormEquilibrium A q μ' → μ' = μ := by
  obtain ⟨μ, hμ, herg, hG, huniq⟩ :=
    MatrixTuple.exists_ergodic_hasNormGibbs_forall_eq normGibbsExistence hA hirr hq
  letI := hμ
  exact ⟨μ, hμ, herg, hG.isNormEquilibrium hA herg.toMeasurePreserving, hG, huniq⟩

end FractalGeometry
