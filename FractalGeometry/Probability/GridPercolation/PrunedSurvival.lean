import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.Configuration
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.LawInvariance
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.Processes
import FractalGeometry.Probability.GridPercolation.PrunedComparison
import FractalGeometry.Probability.GridPercolation.RootIndependence
import FractalGeometry.Probability.GridPercolation.Subtrees
import FractalGeometry.Probability.GridPercolation.SurvivalMeasurability
import FractalGeometry.Probability.GridPercolation.WordSplitting

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open Filter Topology MeasureTheory

open scoped ENNReal

variable {A : GridLaw} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

omit [MeasurableSpace Ω] in

theorem exists_retained_hasInfiniteDescent_of_mem_survival {ω : Ω} (hs : ω ∈ survival X)
    (L : ℕ) :
    ∃ w : Word A, w.length = L ∧ Retained X ω w ∧ HasInfiniteDescentBelow X ω w := by
  classical
  have hdesc : HasInfiniteDescentBelow X ω [] :=
    (hasInfiniteDescentBelow_nil_iff_mem_survival X ω).mpr hs
  choose u hu using fun n => hdesc (L + n)
  let f : ℕ → {w : Word A // w.length = L} := fun n =>
    ⟨(wordOfDigits (u n)).take L, by
      rw [List.length_take, length_wordOfDigits]
      exact Nat.min_eq_left (Nat.le_add_right L n)⟩
  have : Finite {w : Word A // w.length = L} := (List.finite_length_eq _ L).to_subtype
  obtain ⟨w₀, hw₀⟩ := Finite.exists_infinite_fiber f
  have hinf : (f ⁻¹' {w₀}).Infinite := Set.infinite_coe_iff.mp hw₀
  refine ⟨w₀.1, w₀.2, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := hinf.nonempty
    have hn' : (wordOfDigits (u n)).take L = w₀.1 :=
      congrArg Subtype.val (show f n = w₀ from hn)
    have hret : RetainedBelow X ω [] (wordOfDigits (u n)) := hu n
    have := hret.take L
    rw [← retained_iff_retainedBelow_nil, hn'] at this
    exact this
  · intro d
    obtain ⟨n, hn, hdn⟩ := not_bddAbove_iff.mp hinf.not_bddAbove d
    have hn' : (wordOfDigits (u n)).take L = w₀.1 :=
      congrArg Subtype.val (show f n = w₀ from hn)
    set rest := (wordOfDigits (u n)).drop L with hrest
    have hsplit : wordOfDigits (u n) = w₀.1 ++ rest := by
      rw [← hn', hrest, List.take_append_drop]
    have hret : RetainedBelow X ω [] (w₀.1 ++ rest) := by
      rw [← hsplit]
      exact hu n
    have hbelow : RetainedBelow X ω w₀.1 rest := by
      have := (retainedBelow_append_iff X ω [] _ _).mp hret
      simpa using this.2
    have hlen : (rest.take d).length = d := by
      rw [List.length_take, hrest, List.length_drop, length_wordOfDigits]
      omega
    refine ⟨fun i => (rest.take d).get (Fin.cast hlen.symm i), ?_⟩
    have hw : wordOfDigits (fun i : Fin d => (rest.take d).get (Fin.cast hlen.symm i)) =
        rest.take d := by
      apply List.ext_getElem
      · simp [hlen]
      · intro i h1 h2
        simp [wordOfDigits]
    rw [hw]
    exact hbelow.take d

omit [MeasurableSpace Ω] in

theorem one_le_prunedColumnCount_of_mem_survival {ω : Ω} (hs : ω ∈ survival X) (L : ℕ) :
    1 ≤ prunedColumnCount X L ω := by
  classical
  obtain ⟨w, hwL, hret, hdesc⟩ := exists_retained_hasInfiniteDescent_of_mem_survival hs L
  set v : ColumnWord A L := fun l => (w.get (Fin.cast hwL.symm l)).1 with hv
  set r : RowWord A L := fun l => (w.get (Fin.cast hwL.symm l)).2 with hr
  have hw : wordOfCoordinates v r = w := by
    apply List.ext_getElem
    · simp [hwL]
    · intro i h1 h2
      simp [wordOfCoordinates, hv, hr]
  rw [prunedColumnCount_eq_card_counted]
  refine Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, r, ?_, ?_⟩⟩
  · rw [hw, retainedBelow_nil_iff_retained]
    exact hret
  · rw [hw]
    exact hdesc

omit [MeasurableSpace Ω] in

theorem one_le_descendantCountBelow_of_mem_survival {ω : Ω} (hs : ω ∈ survival X) (j : ℕ) :
    1 ≤ descendantCountBelow X [] j ω := by
  classical
  obtain ⟨w, hwj, hret⟩ := hs j
  set u : DigitWord A j := fun l => w.get (Fin.cast hwj.symm l) with hu
  have hw : wordOfDigits u = w := by
    apply List.ext_getElem
    · simp [hwj]
    · intro i h1 h2
      simp [wordOfDigits, hu]
  unfold descendantCountBelow
  refine Finset.card_pos.mpr ⟨u, ?_⟩
  rw [Set.mem_toFinset, Set.mem_ofPred_eq, hw, retainedBelow_nil_iff_retained]
  exact hret

noncomputable def prunedColumnCountConfig (x : Configuration A) (root : Word A) (L : ℕ) :
    ℕ := by
  classical
  exact ((Finset.univ : Finset (ColumnWord A L)).filter fun v =>
    ∃ r : RowWord A L, retainedBelowConfig x root (wordOfCoordinates v r) ∧
      hasInfiniteDescentConfig x (root ++ wordOfCoordinates v r)).card

omit [MeasurableSpace Ω] in

lemma prunedColumnCountBelow_eq_config (root : Word A) (L : ℕ) (ω : Ω) :
    prunedColumnCountBelow X root L ω = prunedColumnCountConfig (config X ω) root L := rfl

lemma prunedColumnCountConfig_rebase (base root : Word A) (x : Configuration A) (L : ℕ) :
    prunedColumnCountConfig (rebase base x) root L =
      prunedColumnCountConfig x (base ++ root) L := by
  classical
  unfold prunedColumnCountConfig
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, retainedBelowConfig_rebase,
    hasInfiniteDescentConfig_rebase, List.append_assoc]

lemma measurableSet_counted_config (root : Word A) {L : ℕ} (v : ColumnWord A L) :
    MeasurableSet {x : Configuration A | ∃ r : RowWord A L,
      retainedBelowConfig x root (wordOfCoordinates v r) ∧
        hasInfiniteDescentConfig x (root ++ wordOfCoordinates v r)} := by
  have : {x : Configuration A | ∃ r : RowWord A L,
      retainedBelowConfig x root (wordOfCoordinates v r) ∧
        hasInfiniteDescentConfig x (root ++ wordOfCoordinates v r)} =
      ⋃ r : RowWord A L, {x | retainedBelowConfig x root (wordOfCoordinates v r)} ∩
        {x | hasInfiniteDescentConfig x (root ++ wordOfCoordinates v r)} := by
    ext x
    simp
  rw [this]
  exact MeasurableSet.iUnion fun r =>
    (measurableSet_retainedBelowConfig _ _).inter (measurableSet_hasInfiniteDescentConfig _)

lemma measurable_prunedColumnCountConfig (root : Word A) (L : ℕ) :
    Measurable fun x : Configuration A => prunedColumnCountConfig x root L := by
  classical
  rw [show (fun x : Configuration A => prunedColumnCountConfig x root L) = fun x =>
      ∑ v ∈ (Finset.univ : Finset (ColumnWord A L)),
        if (∃ r : RowWord A L, retainedBelowConfig x root (wordOfCoordinates v r) ∧
          hasInfiniteDescentConfig x (root ++ wordOfCoordinates v r)) then 1 else 0 by
    funext x
    exact Finset.card_filter _ _]
  exact Finset.measurable_fun_sum _ fun v _ =>
    Measurable.ite (measurableSet_counted_config root v) measurable_const measurable_const

end FractalGeometry.Probability.GridPercolation
