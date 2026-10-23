import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Pressure.ParityShift.Ergodicity
import FractalGeometry.Pressure.ParityShift.FiniteGibbsBounds
import FractalGeometry.Pressure.ParityShift.HolderPotential
import FractalGeometry.Pressure.ParityShift.Limits
import FractalGeometry.Pressure.ParityShift.PeriodicMeasures
import FractalGeometry.Pressure.ParityShift.SymbolicMetric
import FractalGeometry.Pressure.ParityShift.Uniqueness
import FractalGeometry.Symbolic.ParityShift
import FractalGeometry.Symbolic.Shift

/-!
Gibbs measures for Hölder potentials on a finite mixing parity shift.

Rufus Bowen, "Equilibrium states and the ergodic theory of Anosov diffeomorphisms",
Lecture Notes in Mathematics 470, Springer (1975), Theorem 1.4.
DOI: 10.1007/BFb0081279.

This proves the specialisation to symbols `(i, c)` with transition
`c' = c + o i` in `ZMod 2`, where both values of `o` occur. The endpoint gives
existence and uniqueness of an ergodic Gibbs probability measure. It does not
assert the theorem for every mixing subshift of finite type.
-/

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory

universe u

theorem exists_ergodic_isGibbsPotential_of_forall_gibbsUpTo {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] {o : ι → ZMod 2} (h0 : ∃ i, o i = 0)
    (h1 : ∃ i, o i = 1) {f : (ℤ → ι × ZMod 2) → ℝ} (hf : IsHolderPotential o f) {P C : ℝ}
    (h : ∀ N : ℕ, ∃ ν : Measure (ℤ → ι × ZMod 2), IsProbabilityMeasure ν ∧
      MeasurePreserving (shift 1) ν ν ∧ ν (subshift o)ᶜ = 0 ∧ GibbsUpTo o f ν P C N) :
    ∃ ν : Measure (ℤ → ι × ZMod 2), IsProbabilityMeasure ν ∧ ν (subshift o)ᶜ = 0 ∧
      Ergodic (shift 1) ν ∧ IsGibbsPotential o f ν P C := by
  obtain ⟨ν, hp, hinv, hs, hg⟩ := exists_isGibbsPotential_of_forall_gibbsUpTo h
  exact ⟨ν, hp, hs, hg.ergodic_of_isHolder hinv hs hf h0 h1, hg⟩

theorem bowenGibbsExistence {ι : Type u} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (o : ι → ZMod 2) (h0 : ∃ i, o i = 0) (h1 : ∃ i, o i = 1)
    (f : (ℤ → ι × ZMod 2) → ℝ) (hf : IsHolderPotential o f) :
    ∃ ν : Measure (ℤ → ι × ZMod 2), IsProbabilityMeasure ν ∧ ν (subshift o)ᶜ = 0 ∧
      Ergodic (shift 1) ν ∧ ∃ P C : ℝ, IsGibbsPotential o f ν P C := by
  obtain ⟨C, -, hN⟩ := exists_gibbsUpTo_periodic h0 h1 hf
  obtain ⟨ν, hp, hs, herg, hg⟩ := exists_ergodic_isGibbsPotential_of_forall_gibbsUpTo h0 h1 hf hN
  exact ⟨ν, hp, hs, herg, _, C, hg⟩

theorem existsUnique_ergodic_isGibbsPotential {ι : Type u} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (o : ι → ZMod 2) (h0 : ∃ i, o i = 0) (h1 : ∃ i, o i = 1)
    (f : (ℤ → ι × ZMod 2) → ℝ) (hf : IsHolderPotential o f) :
    ∃! ν : Measure (ℤ → ι × ZMod 2), IsProbabilityMeasure ν ∧ ν (subshift o)ᶜ = 0 ∧
      Ergodic (shift 1) ν ∧ ∃ C : ℝ, IsGibbsPotential o f ν (pressureZPot o f) C := by
  obtain ⟨ν, hprob, hsupp, herg, P, C, hg⟩ := bowenGibbsExistence o h0 h1 f hf
  have hP : P = pressureZPot o f := hg.pressure_eq_of_isHolder h0 hsupp hf
  subst hP
  refine ⟨ν, ⟨hprob, hsupp, herg, C, hg⟩, ?_⟩
  rintro ν' ⟨hprob', hsupp', herg', C', hg'⟩
  exact hg.eq_of_ergodic_of_isHolder hsupp hsupp' hg' hf herg herg'.toMeasurePreserving

end FractalGeometry
