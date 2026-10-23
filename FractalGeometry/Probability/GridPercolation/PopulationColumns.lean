import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.ColumnOffspring
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.Processes
import FractalGeometry.Probability.GridPercolation.WordSplitting

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {A : GridLaw} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

def digitSplit {L : ℕ} (u : DigitWord A L) : ColumnWord A L × RowWord A L :=
  (fun l => (u l).1, fun l => (u l).2)

omit [MeasurableSpace Ω] in

lemma wordOfDigits_eq_wordOfCoordinates {L : ℕ} (u : DigitWord A L) :
    wordOfDigits u = wordOfCoordinates (digitSplit u).1 (digitSplit u).2 := by
  unfold wordOfDigits wordOfCoordinates digitSplit
  rfl

omit [MeasurableSpace Ω] in

lemma digitSplit_bijective (L : ℕ) : Function.Bijective (digitSplit (A := A) (L := L)) := by
  constructor
  · intro u u' h
    funext l
    have h1 := congrFun (congrArg Prod.fst h) l
    have h2 := congrFun (congrArg Prod.snd h) l
    exact Prod.ext h1 h2
  · rintro ⟨v, r⟩
    exact ⟨fun l => (v l, r l), rfl⟩

omit [MeasurableSpace Ω] in

theorem descendantCountBelow_nil_eq_sum_tubePopulation (j : ℕ) (ω : Ω) :
    descendantCountBelow X [] j ω = ∑ v : ColumnWord A j, tubePopulation X v ω := by
  classical
  unfold descendantCountBelow tubePopulation tubePopulationBelow
  rw [Set.toFinset_ofPred]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun u : DigitWord A j => (digitSplit u).1)
    (t := Finset.univ) (fun u _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun v _ => ?_

  apply Finset.card_bij (fun u _ => (digitSplit u).2)
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    obtain ⟨hret, hv⟩ := hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hv, ← wordOfDigits_eq_wordOfCoordinates]
    exact hret
  · intro u hu u' hu' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hu'
    apply (digitSplit_bijective j).1
    exact Prod.ext (hu.2.trans hu'.2.symm) h
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    refine ⟨fun l => (v l, r l), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, rfl⟩
    rw [wordOfDigits_eq_wordOfCoordinates]
    exact hr

omit [MeasurableSpace Ω] in

theorem descendantCountBelow_nil_eq_occupiedColumnWeight_one (j : ℕ) (ω : Ω) :
    (descendantCountBelow X [] j ω : ℝ) = occupiedColumnWeight X 1 j ω := by
  rw [descendantCountBelow_nil_eq_sum_tubePopulation]
  unfold occupiedColumnWeight
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Real.rpow_one]

end FractalGeometry.Probability.GridPercolation
