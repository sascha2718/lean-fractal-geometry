import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.ColumnOffspring
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.Processes

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

universe u v

open Finset MeasureTheory Measure ProbabilityTheory Real

open scoped BigOperators

variable {A : GridLaw} {Omega : Type*} [MeasurableSpace Omega]

inductive IndepBlock where
  | left
  | right
  deriving DecidableEq

def IndepBlock.Index (I J : Type u) : IndepBlock -> Type u
  | .left => I
  | .right => J

def IndepBlock.coordinate {Q : Type v} {I J : Type u} (f : I -> Q) (g : J -> Q) :
    (b : IndepBlock) -> IndepBlock.Index I J b -> Q
  | .left, i => f i
  | .right, j => g j

theorem IndepBlock.coordinate_injective {Q : Type v} {I J : Type u}
    {f : I -> Q} {g : J -> Q}
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : forall i j, f i ≠ g j) :
    Function.Injective
      (fun p : (b : IndepBlock) × IndepBlock.Index I J b =>
        IndepBlock.coordinate f g p.1 p.2) := by
  rintro ⟨b, x⟩ ⟨c, y⟩ h
  cases b <;> cases c
  · have hxy : x = y := hf h
    subst y
    rfl
  · exact False.elim (hfg x y h)
  · exact False.elim (hfg y x h.symm)
  · have hxy : x = y := hg h
    subst y
    rfl

theorem iIndepFun.indepFun_coordinateBlocks
    {Q : Type v} {I J : Type u} {Y : Q -> Type*} [forall q, MeasurableSpace (Y q)]
    {P : Measure Omega} {Z : (q : Q) -> Omega -> Y q}
    (hZ : forall q, Measurable (Z q)) (h : iIndepFun Z P)
    (f : I -> Q) (g : J -> Q)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : forall i j, f i ≠ g j) :
    IndepFun (fun omega i => Z (f i) omega) (fun omega j => Z (g j) omega) P := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  let W : (b : IndepBlock) ->
      (x : IndepBlock.Index I J b) -> Omega -> Y (IndepBlock.coordinate f g b x) :=
    fun b x => Z (IndepBlock.coordinate f g b x)
  have hraw : iIndepFun
      (fun p : (b : IndepBlock) × IndepBlock.Index I J b => W p.1 p.2) P := by
    exact h.precomp (IndepBlock.coordinate_injective hf hg hfg)
  have hblocks : iIndepFun (fun b omega x => W b x omega) P :=
    iIndepFun_curry_of_uncurry (fun b x => hZ _) hraw
  change IndepFun
    (fun omega (x : IndepBlock.Index I J IndepBlock.left) => W IndepBlock.left x omega)
    (fun omega (x : IndepBlock.Index I J IndepBlock.right) => W IndepBlock.right x omega) P
  exact hblocks.indepFun (i := IndepBlock.left) (j := IndepBlock.right) (by decide)

abbrev ColumnPastIndex (A : GridLaw) (L : Nat) :=
  (k : Fin L) × (DigitWord A k.val × (Fin A.M × Fin A.N))

abbrev ColumnFutureIndex (A : GridLaw) (L : Nat) :=
  DigitWord A L × (Fin A.M × Fin A.N)

def columnPastCoordinate {L : Nat} (q : ColumnPastIndex A L) :
    Word A × (Fin A.M × Fin A.N) :=
  (wordOfDigits q.2.1, q.2.2)

def columnFutureCoordinate {L : Nat} (q : ColumnFutureIndex A L) :
    Word A × (Fin A.M × Fin A.N) :=
  (wordOfDigits q.1, q.2)

theorem columnPastCoordinate_injective (L : Nat) :
    Function.Injective (columnPastCoordinate (A := A) (L := L)) := by
  rintro ⟨k, u, a⟩ ⟨l, v, b⟩ h
  have hklv : k.val = l.val := by
    have hlen := congrArg (fun q => q.1.length) h
    simpa [columnPastCoordinate, wordOfDigits] using hlen
  have hkl : k = l := Fin.ext hklv
  subst l
  have huv : u = v := by
    apply List.ofFn_injective
    exact congrArg Prod.fst h
  have hab : a = b := congrArg Prod.snd h
  subst v
  subst b
  rfl

theorem columnFutureCoordinate_injective (L : Nat) :
    Function.Injective (columnFutureCoordinate (A := A) (L := L)) := by
  rintro ⟨u, a⟩ ⟨v, b⟩ h
  have huv : u = v := by
    apply List.ofFn_injective
    exact congrArg Prod.fst h
  have hab : a = b := congrArg Prod.snd h
  subst v
  subst b
  rfl

theorem columnPastCoordinate_ne_columnFutureCoordinate (L : Nat)
    (q : ColumnPastIndex A L) (r : ColumnFutureIndex A L) :
    columnPastCoordinate q ≠ columnFutureCoordinate r := by
  intro h
  have hlen := congrArg (fun z => z.1.length) h
  have hk : q.1.val = L := by
    simpa [columnPastCoordinate, columnFutureCoordinate, wordOfDigits] using hlen
  exact (Nat.ne_of_lt q.1.isLt) hk

theorem IsPercolation.indepFun_columnPast_columnFuture
    {P : Measure Omega}
    {X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool}
    (hX : IsPercolation P X) (L : Nat) :
    IndepFun
      (fun omega (q : ColumnPastIndex A L) =>
        X (columnPastCoordinate q).1 (columnPastCoordinate q).2 omega)
      (fun omega (q : ColumnFutureIndex A L) =>
        X (columnFutureCoordinate q).1 (columnFutureCoordinate q).2 omega) P := by
  exact iIndepFun.indepFun_coordinateBlocks
    (fun q => hX.measurable q.1 q.2)
    hX.indep
    columnPastCoordinate columnFutureCoordinate
    (columnPastCoordinate_injective L) (columnFutureCoordinate_injective L)
    (columnPastCoordinate_ne_columnFutureCoordinate L)

abbrev ColumnPastState (A : GridLaw) (L : Nat) := ColumnPastIndex A L -> Bool

abbrev ColumnFutureState (A : GridLaw) (L : Nat) := ColumnFutureIndex A L -> Bool

def columnPastState
    (X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool) (L : Nat) :
    Omega -> ColumnPastState A L :=
  fun omega q => X (columnPastCoordinate q).1 (columnPastCoordinate q).2 omega

def columnFutureState
    (X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool) (L : Nat) :
    Omega -> ColumnFutureState A L :=
  fun omega q => X (columnFutureCoordinate q).1 (columnFutureCoordinate q).2 omega

theorem IsPercolation.measurable_columnPastState
    {P : Measure Omega}
    {X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool}
    (hX : IsPercolation P X) (L : Nat) : Measurable (columnPastState X L) := by
  apply Measurable.of_eval
  intro q
  exact hX.measurable (columnPastCoordinate q).1 (columnPastCoordinate q).2

theorem IsPercolation.measurable_columnFutureState
    {P : Measure Omega}
    {X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool}
    (hX : IsPercolation P X) (L : Nat) : Measurable (columnFutureState X L) := by
  apply Measurable.of_eval
  intro q
  exact hX.measurable (columnFutureCoordinate q).1 (columnFutureCoordinate q).2

theorem IsPercolation.indepFun_columnPastState_columnFutureState
    {P : Measure Omega}
    {X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool}
    (hX : IsPercolation P X) (L : Nat) :
    IndepFun (columnPastState X L) (columnFutureState X L) P :=
  hX.indepFun_columnPast_columnFuture L

def coordinateDigitWord {L : Nat} (v : ColumnWord A L) (r : RowWord A L) :
    DigitWord A L := fun l => (v l, r l)

def columnPastCellIndex {L : Nat} (v : ColumnWord A L) (r : RowWord A L)
    (l : Fin L) : ColumnPastIndex A L :=
  ⟨l,
    Fin.take l.val (Nat.le_of_lt l.isLt) (coordinateDigitWord v r),
    coordinateDigitWord v r l⟩

theorem columnPastCoordinate_columnPastCellIndex {L : Nat}
    (v : ColumnWord A L) (r : RowWord A L) (l : Fin L) :
    columnPastCoordinate (columnPastCellIndex v r l) =
      ((wordOfCoordinates v r).take l.val, coordinateDigitWord v r l) := by
  apply Prod.ext
  · exact Fin.ofFn_take_eq_take_ofFn (Nat.le_of_lt l.isLt)
      (coordinateDigitWord v r)
  · rfl

def retainedFromPast {L : Nat} (past : ColumnPastState A L)
    (v : ColumnWord A L) (r : RowWord A L) : Prop :=
  forall l : Fin L, past (columnPastCellIndex v r l) = true

omit [MeasurableSpace Omega] in

theorem retainedFromPast_columnPastState_iff
    (X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool)
    {L : Nat} (v : ColumnWord A L) (r : RowWord A L) (omega : Omega) :
    retainedFromPast (columnPastState X L omega) v r <->
      RetainedBelow X omega [] (wordOfCoordinates v r) := by
  unfold retainedFromPast RetainedBelow columnPastState
  constructor
  · intro h l
    rw [List.get_eq_getElem]
    let l' : Fin L := ⟨l.val, by
      simpa [wordOfCoordinates] using l.isLt⟩
    have hl := h l'
    simpa [columnPastCoordinate_columnPastCellIndex, l', wordOfCoordinates,
      coordinateDigitWord] using hl
  · intro h l
    let l' : Fin (wordOfCoordinates v r).length := ⟨l.val, by
      simp [wordOfCoordinates]⟩
    have hl := h l'
    simpa [columnPastCoordinate_columnPastCellIndex, l', wordOfCoordinates,
      coordinateDigitWord] using hl

noncomputable def pastTubePopulation {L : Nat} (past : ColumnPastState A L)
    (v : ColumnWord A L) : Nat := by
  classical
  exact ((Finset.univ : Finset (RowWord A L)).filter fun r =>
    retainedFromPast past v r).card

noncomputable def activeRowsFromPast {L : Nat} (past : ColumnPastState A L)
    (v : ColumnWord A L) : RowWord A L -> Bool := by
  classical
  exact fun r => decide (retainedFromPast past v r)

@[simp] theorem activeRowsFromPast_eq_true_iff {L : Nat}
    (past : ColumnPastState A L) (v : ColumnWord A L) (r : RowWord A L) :
    activeRowsFromPast past v r = true <-> retainedFromPast past v r := by
  classical
  simp [activeRowsFromPast]

theorem activeRowsFromPast_card {L : Nat} (past : ColumnPastState A L)
    (v : ColumnWord A L) :
    ((Finset.univ : Finset (RowWord A L)).filter fun r =>
      activeRowsFromPast past v r = true).card = pastTubePopulation past v := by
  classical
  unfold pastTubePopulation
  congr 1

omit [MeasurableSpace Omega] in

theorem pastTubePopulation_columnPastState
    (X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool)
    {L : Nat} (v : ColumnWord A L) (omega : Omega) :
    pastTubePopulation (columnPastState X L omega) v = tubePopulation X v omega := by
  classical
  unfold pastTubePopulation tubePopulation tubePopulationBelow
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact retainedFromPast_columnPastState_iff X v r omega

noncomputable def columnOffspringFromFuture {L : Nat}
    (future : ColumnFutureState A L) (v : ColumnWord A L) (r : RowWord A L)
    (i : Fin A.M) : Nat := by
  classical
  exact ((Finset.univ : Finset (Fin A.N)).filter fun j =>
    future (coordinateDigitWord v r, (i, j)) = true).card

omit [MeasurableSpace Omega] in

theorem columnOffspringFromFuture_columnFutureState
    (X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool)
    {L : Nat} (v : ColumnWord A L) (r : RowWord A L) (i : Fin A.M)
    (omega : Omega) :
    columnOffspringFromFuture (columnFutureState X L omega) v r i =
      columnOffspring X (wordOfCoordinates v r) i omega := by
  classical
  unfold columnOffspringFromFuture columnOffspring columnFutureState
  congr 1

noncomputable def nextColumnWeightFromStates {L : Nat} (beta : Real)
    (past : ColumnPastState A L) (future : ColumnFutureState A L) : Real := by
  classical
  exact ∑ v : ColumnWord A L, ∑ i : Fin A.M,
      ((∑ r : RowWord A L,
        if retainedFromPast past v r then
          columnOffspringFromFuture future v r i
        else 0 : Nat) : Real) ^ beta

omit [MeasurableSpace Omega] in

theorem nextColumnWeightFromStates_states
    (X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool)
    (beta : Real) (L : Nat) (omega : Omega) :
    nextColumnWeightFromStates beta (columnPastState X L omega)
        (columnFutureState X L omega) =
      occupiedColumnWeight X beta (L + 1) omega := by
  classical
  rw [occupiedColumnWeight_succ]
  unfold nextColumnWeightFromStates
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  apply Finset.sum_congr rfl
  intro r _
  rw [columnOffspringFromFuture_columnFutureState]
  by_cases hr : retainedFromPast (columnPastState X L omega) v r
  · rw [ite_eq_left hr, ite_eq_left ((retainedFromPast_columnPastState_iff X v r omega).mp hr)]
  · rw [ite_eq_right hr, ite_eq_right ((not_congr
      (retainedFromPast_columnPastState_iff X v r omega)).mp hr)]

omit [MeasurableSpace Omega] in

theorem nextColumnWeightFromStates_columnFutureState
    (X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool)
    (beta : Real) {L : Nat} (past : ColumnPastState A L) (omega : Omega) :
    nextColumnWeightFromStates beta past (columnFutureState X L omega) =
      ∑ v : ColumnWord A L, ∑ i : Fin A.M,
        (∑ r : RowWord A L, if activeRowsFromPast past v r then
          (columnOffspring X (wordOfCoordinates v r) i omega : Real)
        else 0) ^ beta := by
  classical
  unfold nextColumnWeightFromStates
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  rw [Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro r _
  rw [columnOffspringFromFuture_columnFutureState]
  simp only [activeRowsFromPast_eq_true_iff]

omit [MeasurableSpace Omega] in

theorem active_columnOffspring_sum_reindex
    (X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool)
    {L : Nat} (v : ColumnWord A L) (active : RowWord A L -> Bool)
    (i : Fin A.M) (omega : Omega) :
    let R := (Finset.univ : Finset (RowWord A L)).filter fun r => active r = true
    let roots : Fin R.card -> Word A := fun c =>
      wordOfCoordinates v (R.equivFin.symm c).1
    (∑ r : RowWord A L, if active r then
        (columnOffspring X (wordOfCoordinates v r) i omega : Real) else 0) =
      ∑ c : Fin R.card, (columnOffspring X (roots c) i omega : Real) := by
  classical
  dsimp only
  let R := (Finset.univ : Finset (RowWord A L)).filter fun r => active r = true
  let roots : Fin R.card -> Word A := fun c =>
    wordOfCoordinates v (R.equivFin.symm c).1
  change (∑ r : RowWord A L, if active r then
        (columnOffspring X (wordOfCoordinates v r) i omega : Real) else 0) =
      ∑ c : Fin R.card, (columnOffspring X (roots c) i omega : Real)
  calc
    (∑ r : RowWord A L, if active r then
        (columnOffspring X (wordOfCoordinates v r) i omega : Real) else 0) =
        ∑ r ∈ R, (columnOffspring X (wordOfCoordinates v r) i omega : Real) := by
          rw [show R = (Finset.univ : Finset (RowWord A L)).filter
            (fun r => active r = true) from rfl]
          rw [Finset.sum_filter]
    _ = ∑ r : R, (columnOffspring X (wordOfCoordinates v r.1) i omega : Real) := by
          apply Finset.sum_subtype
          intro r
          rfl
    _ = ∑ c : Fin R.card, (columnOffspring X (roots c) i omega : Real) := by
          exact Fintype.sum_equiv R.equivFin _ _ (fun r => by simp [roots])

theorem active_columnOffspring_roots_injective
    {L : Nat} (v : ColumnWord A L) (active : RowWord A L -> Bool) :
    let R := (Finset.univ : Finset (RowWord A L)).filter fun r => active r = true
    Function.Injective (fun c : Fin R.card =>
      wordOfCoordinates v (R.equivFin.symm c).1) := by
  classical
  dsimp only
  let R := (Finset.univ : Finset (RowWord A L)).filter fun r => active r = true
  intro c d h
  have hr : (R.equivFin.symm c).1 = (R.equivFin.symm d).1 := by
    have hp : (v, (R.equivFin.symm c).1) = (v, (R.equivFin.symm d).1) :=
      (wordOfCoordinates_injective (A := A) L) h
    exact congrArg Prod.snd hp
  apply R.equivFin.symm.injective
  exact Subtype.ext hr

end FractalGeometry.Probability.GridPercolation
