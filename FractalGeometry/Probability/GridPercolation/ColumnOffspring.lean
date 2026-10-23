import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.Processes

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open Finset MeasureTheory Measure ProbabilityTheory Real

open scoped BigOperators

variable {A : GridLaw} {Omega : Type*} [MeasurableSpace Omega]

def snocFinWord {L : Nat} {alpha : Type*} (w : Fin L -> alpha) (a : alpha) :
    Fin (L + 1) -> alpha :=
  Fin.lastCases a w

@[simp] theorem snocFinWord_castSucc {L : Nat} {alpha : Type*}
    (w : Fin L -> alpha) (a : alpha) (l : Fin L) :
    snocFinWord w a l.castSucc = w l := by
  simp [snocFinWord]

@[simp] theorem snocFinWord_last {L : Nat} {alpha : Type*}
    (w : Fin L -> alpha) (a : alpha) :
    snocFinWord w a (Fin.last L) = a := by
  simp [snocFinWord]

def finWordSnocEquiv (L : Nat) (alpha : Type*) :
    (Fin (L + 1) -> alpha) ≃ ((Fin L -> alpha) × alpha) where
  toFun w := (Fin.init w, w (Fin.last L))
  invFun p := snocFinWord p.1 p.2
  left_inv w := by
    funext l
    refine Fin.lastCases ?_ (fun k => ?_) l
    · simp [snocFinWord]
    · simp [snocFinWord, Fin.init]
  right_inv p := by
    rcases p with ⟨w, a⟩
    ext
    · simp [snocFinWord, Fin.init]
    · simp [snocFinWord]

def snocColumnWord {L : Nat} (v : ColumnWord A L) (i : Fin A.M) :
    ColumnWord A (L + 1) := snocFinWord v i

def snocRowWord {L : Nat} (r : RowWord A L) (j : Fin A.N) :
    RowWord A (L + 1) := snocFinWord r j

theorem wordOfCoordinates_snoc {L : Nat}
    (v : ColumnWord A L) (r : RowWord A L) (i : Fin A.M) (j : Fin A.N) :
    wordOfCoordinates (snocColumnWord v i) (snocRowWord r j) =
      wordOfCoordinates v r ++ [(i, j)] := by
  unfold wordOfCoordinates
  rw [List.ofFn_succ', List.concat_eq_append]
  simp only [snocColumnWord, snocRowWord, snocFinWord_castSucc, snocFinWord_last]

theorem wordOfCoordinates_injective (L : Nat) :
    Function.Injective
      (fun p : ColumnWord A L × RowWord A L => wordOfCoordinates p.1 p.2) := by
  rintro ⟨v, r⟩ ⟨w, s⟩ h
  have hfun : (fun l => (v l, r l)) = fun l => (w l, s l) :=
    List.ofFn_injective h
  apply Prod.ext
  · funext l
    exact congrArg Prod.fst (congrFun hfun l)
  · funext l
    exact congrArg Prod.snd (congrFun hfun l)

omit [MeasurableSpace Omega] in

theorem retainedBelow_append_singleton
    (X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool)
    (omega : Omega) (root u : Word A) (a : Fin A.M × Fin A.N) :
    RetainedBelow X omega root (u ++ [a]) <->
      RetainedBelow X omega root u /\ X (root ++ u) a omega = true := by
  constructor
  · intro h
    constructor
    · intro l
      have hl := h ⟨l.val, by simp⟩
      simpa [RetainedBelow, List.get_eq_getElem,
        List.take_append_of_le_length l.isLt.le,
        List.getElem_append_left l.isLt] using hl
    · have hl := h ⟨u.length, by simp⟩
      simpa [RetainedBelow, List.get_eq_getElem] using hl
  · rintro ⟨hu, ha⟩ l
    by_cases hlt : l.val < u.length
    · have hl := hu ⟨l.val, hlt⟩
      simpa [RetainedBelow, List.get_eq_getElem,
        List.take_append_of_le_length hlt.le,
        List.getElem_append_left hlt] using hl
    · have heq : l.val = u.length := by
        have hupper : l.val < u.length + 1 := by simpa using l.isLt
        omega
      simpa [RetainedBelow, List.get_eq_getElem, heq] using ha

omit [MeasurableSpace Omega] in

theorem retainedBelow_wordOfCoordinates_snoc
    (X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool)
    (omega : Omega) (root : Word A) {L : Nat}
    (v : ColumnWord A L) (r : RowWord A L) (i : Fin A.M) (j : Fin A.N) :
    RetainedBelow X omega root
        (wordOfCoordinates (snocColumnWord v i) (snocRowWord r j)) <->
      RetainedBelow X omega root (wordOfCoordinates v r) /\
        X (root ++ wordOfCoordinates v r) (i, j) omega = true := by
  rw [wordOfCoordinates_snoc, retainedBelow_append_singleton]

noncomputable instance decidableRetainedBelow
    (X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool)
    (omega : Omega) (root u : Word A) :
    Decidable (RetainedBelow X omega root u) := Classical.dec _

theorem iIndepFun_curry_of_uncurry
    {I : Type*} {J : I -> Type*} {Y : (i : I) -> J i -> Type*}
    [forall i j, MeasurableSpace (Y i j)]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {Z : (i : I) -> (j : J i) -> Omega -> Y i j}
    (hZ : forall i j, Measurable (Z i j))
    (h : iIndepFun (fun p : (i : I) × J i => Z p.1 p.2) P) :
    iIndepFun (fun i omega j => Z i j omega) P := by
  have hmap : forall i j, IsProbabilityMeasure (P.map (Z i j)) :=
    fun _ _ => inferInstance
  let _ (i : I) (j : J i) : IsProbabilityMeasure (P.map (Z i j)) := hmap i j
  have hinner (i : I) : iIndepFun (Z i) P := by
    apply h.precomp (g := fun j => Sigma.mk i j)
    intro j k hjk
    simpa using hjk
  have hcurry :
      (MeasurableEquiv.piCurry Y) ∘
          (fun omega (p : (i : I) × J i) => Z p.1 p.2 omega) =
        fun omega i j => Z i j omega := by
    ext omega i j
    simp [Sigma.curry]
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  rw [← hcurry, ← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [(iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)).mp h]
  calc
    Measure.map (MeasurableEquiv.piCurry Y)
        (Measure.infinitePi fun p => P.map (Z p.1 p.2)) =
        Measure.infinitePi
          (fun i => Measure.infinitePi fun j => P.map (Z i j)) :=
      Measure.infinitePi_map_piCurry (X := Y)
        (fun i j => P.map (Z i j))
    _ = Measure.infinitePi
          (fun i => P.map (fun omega j => Z i j omega)) := by
      congrm Measure.infinitePi fun i => ?_
      exact ((iIndepFun_iff_map_fun_eq_infinitePi_map (hZ i)).mp (hinner i)).symm

noncomputable def columnOffspring
    (X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool)
    (root : Word A) (i : Fin A.M) (omega : Omega) : Nat := by
  classical
  exact ((Finset.univ : Finset (Fin A.N)).filter fun j => X root (i, j) omega = true).card

omit [MeasurableSpace Omega] in

theorem columnOffspring_eq_sum
    (X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool)
    (root : Word A) (i : Fin A.M) (omega : Omega) :
    columnOffspring X root i omega =
      ∑ j : Fin A.N, if X root (i, j) omega = true then 1 else 0 := by
  classical
  exact Finset.card_filter _ _

omit [MeasurableSpace Omega] in

theorem tubePopulationBelow_snocColumnWord
    (X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool)
    (root : Word A) {L : Nat} (v : ColumnWord A L) (i : Fin A.M)
    (omega : Omega) :
    tubePopulationBelow X root (snocColumnWord v i) omega =
      ∑ r : RowWord A L,
        if RetainedBelow X omega root (wordOfCoordinates v r) then
          columnOffspring X (root ++ wordOfCoordinates v r) i omega
        else 0 := by
  classical
  let e := finWordSnocEquiv L (Fin A.N)
  have hreindex :
      (∑ r' : RowWord A (L + 1),
        if RetainedBelow X omega root
            (wordOfCoordinates (snocColumnWord v i) r') then 1 else 0) =
      ∑ p : RowWord A L × Fin A.N,
        if RetainedBelow X omega root
            (wordOfCoordinates (snocColumnWord v i) (snocRowWord p.1 p.2))
          then 1 else 0 := by
    symm
    apply Fintype.sum_equiv e.symm
    intro p
    rfl
  unfold tubePopulationBelow
  rw [Finset.card_filter]
  change
    (∑ r' : RowWord A (L + 1),
      if RetainedBelow X omega root
          (wordOfCoordinates (snocColumnWord v i) r') then 1 else 0) = _
  rw [hreindex, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : RetainedBelow X omega root (wordOfCoordinates v r)
  · simp only [hr, ite_true, columnOffspring_eq_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp [retainedBelow_wordOfCoordinates_snoc, hr]
  · simp only [hr, ite_false]
    apply Finset.sum_eq_zero
    intro j _
    simp [retainedBelow_wordOfCoordinates_snoc, hr]

theorem measurable_columnOffspring {P : Measure Omega}
    {X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool}
    (hX : IsPercolation P X) (root : Word A) (i : Fin A.M) :
    Measurable (columnOffspring X root i) := by
  classical
  rw [show columnOffspring X root i = fun omega =>
      ∑ j : Fin A.N, if X root (i, j) omega = true then 1 else 0 by
    funext omega
    exact columnOffspring_eq_sum X root i omega]
  exact Finset.measurable_fun_sum _ fun j _ =>
    Measurable.ite (measurableSet_eq_fun (hX.measurable root (i, j)) measurable_const)
      measurable_const measurable_const

theorem iIndepFun_columnOffspring_of_injective
    {P : Measure Omega}
    {X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool}
    (hX : IsPercolation P X) {I : Type*}
    (roots : I -> Word A) (hroots : Function.Injective roots)
    (i : Fin A.M) :
    iIndepFun
      (fun c omega => (columnOffspring X (roots c) i omega : Real)) P := by
  let : IsProbabilityMeasure P := hX.toIsProbabilityMeasure
  let Z : (c : I) -> Fin A.N -> Omega -> Bool :=
    fun c j omega => X (roots c) (i, j) omega
  have hZ : forall c j, Measurable (Z c j) :=
    fun c j => hX.measurable (roots c) (i, j)
  have hraw : iIndepFun (fun p : (c : I) × Fin A.N => Z p.1 p.2) P := by
    apply hX.indep.precomp
      (g := fun p : (c : I) × Fin A.N => (roots p.1, (i, p.2)))
    rintro ⟨c, j⟩ ⟨d, k⟩ h
    have hcd : c = d := hroots (congrArg Prod.fst h)
    subst d
    have hjk : j = k := congrArg (fun q => q.2.2) h
    subst k
    rfl
  have hvec : iIndepFun (fun c omega j => Z c j omega) P :=
    iIndepFun_curry_of_uncurry hZ hraw
  have hcount := hvec.comp
    (fun _ (z : Fin A.N -> Bool) =>
      (((Finset.univ : Finset (Fin A.N)).filter fun j => z j = true).card : Real))
    (fun _ => measurable_of_countable _)
  apply hcount.congr
  intro c
  filter_upwards [] with omega
  rfl

theorem iIndepFun_columnOffspring_pairs_of_injective
    {P : Measure Omega}
    {X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool}
    (hX : IsPercolation P X) {I : Type*}
    (roots : I -> Word A) (hroots : Function.Injective roots) :
    iIndepFun
      (fun q : I × Fin A.M => fun omega =>
        (columnOffspring X (roots q.1) q.2 omega : Real)) P := by
  let : IsProbabilityMeasure P := hX.toIsProbabilityMeasure
  let Z : (q : I × Fin A.M) -> Fin A.N -> Omega -> Bool :=
    fun q j omega => X (roots q.1) (q.2, j) omega
  have hZ : forall q j, Measurable (Z q j) :=
    fun q j => hX.measurable (roots q.1) (q.2, j)
  have hraw : iIndepFun
      (fun p : (q : I × Fin A.M) × Fin A.N => Z p.1 p.2) P := by
    apply hX.indep.precomp
      (g := fun p : (q : I × Fin A.M) × Fin A.N =>
        (roots p.1.1, (p.1.2, p.2)))
    rintro ⟨⟨c, i⟩, j⟩ ⟨⟨d, k⟩, l⟩ h
    have hcd : c = d := hroots (congrArg Prod.fst h)
    subst d
    have hik : i = k := congrArg (fun q => q.2.1) h
    subst k
    have hjl : j = l := congrArg (fun q => q.2.2) h
    subst l
    rfl
  have hvec : iIndepFun (fun q omega j => Z q j omega) P :=
    iIndepFun_curry_of_uncurry hZ hraw
  have hcount := hvec.comp
    (fun _ (z : Fin A.N -> Bool) =>
      (((Finset.univ : Finset (Fin A.N)).filter fun j => z j = true).card : Real))
    (fun _ => measurable_of_countable _)
  apply hcount.congr
  intro q
  filter_upwards [] with omega
  rfl

omit [MeasurableSpace Omega] in

theorem columnOffspring_le
    (X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool)
    (root : Word A) (i : Fin A.M) (omega : Omega) :
    columnOffspring X root i omega <= A.N := by
  classical
  unfold columnOffspring
  simpa using Finset.card_filter_le (Finset.univ : Finset (Fin A.N))
    (fun j : Fin A.N => X root (i, j) omega = true)

theorem integral_columnOffspring {P : Measure Omega} [IsProbabilityMeasure P]
    {X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool}
    (hX : IsPercolation P X) (root : Word A) (i : Fin A.M) :
    ∫ omega, (columnOffspring X root i omega : Real) ∂P = A.E i := by
  have hsum : (fun omega => (columnOffspring X root i omega : Real)) =
      fun omega => ∑ j : Fin A.N,
        if X root (i, j) omega = true then (1 : Real) else 0 := by
    funext omega
    rw [columnOffspring_eq_sum]
    norm_cast
  rw [hsum, integral_finsetSum]
  · unfold GridLaw.E
    apply Finset.sum_congr rfl
    intro j _
    let s : Set Omega := {omega | X root (i, j) omega = true}
    have hs : MeasurableSet s :=
      measurableSet_eq_fun (hX.measurable root (i, j)) measurable_const
    have hfun : (fun omega => if X root (i, j) omega = true then (1 : Real) else 0) =
        s.indicator (fun _ => (1 : Real)) := by
      funext omega
      by_cases hval : X root (i, j) omega = true <;> simp [s, hval]
    rw [hfun]
    change ∫ omega, s.indicator (1 : Omega -> Real) omega ∂P = A.p i j
    rw [integral_indicator_one hs, measureReal_def, hX.prob]
    simp [A.p_nonneg i j]
  · intro j _
    have hm : Measurable fun omega =>
        if X root (i, j) omega = true then (1 : Real) else 0 :=
      Measurable.ite
        (measurableSet_eq_fun (hX.measurable root (i, j)) measurable_const)
        measurable_const measurable_const
    exact Integrable.of_bound hm.aestronglyMeasurable 1 <| by
      filter_upwards [] with omega
      split_ifs <;> simp

noncomputable def occupiedColumnWeight
    (X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool)
    (beta : Real) (L : Nat) (omega : Omega) : Real :=
  ∑ v : ColumnWord A L, (tubePopulation X v omega : Real) ^ beta

omit [MeasurableSpace Omega] in

theorem occupiedColumnWeight_succ
    (X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool)
    (beta : Real) (L : Nat) (omega : Omega) :
    occupiedColumnWeight X beta (L + 1) omega =
      ∑ v : ColumnWord A L, ∑ i : Fin A.M,
        ((∑ r : RowWord A L,
          if RetainedBelow X omega [] (wordOfCoordinates v r) then
            columnOffspring X (wordOfCoordinates v r) i omega
          else 0 : Nat) : Real) ^ beta := by
  classical
  let e := finWordSnocEquiv L (Fin A.M)
  unfold occupiedColumnWeight
  calc
    (∑ v' : ColumnWord A (L + 1), (tubePopulation X v' omega : Real) ^ beta) =
        ∑ p : ColumnWord A L × Fin A.M,
          (tubePopulation X (snocColumnWord p.1 p.2) omega : Real) ^ beta := by
      symm
      apply Fintype.sum_equiv e.symm
      intro p
      rfl
    _ = ∑ v : ColumnWord A L, ∑ i : Fin A.M,
          (tubePopulation X (snocColumnWord v i) omega : Real) ^ beta :=
      Fintype.sum_prod_type _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro i _
      rw [show tubePopulation X (snocColumnWord v i) omega =
          tubePopulationBelow X [] (snocColumnWord v i) omega from rfl,
        tubePopulationBelow_snocColumnWord]
      simp

end FractalGeometry.Probability.GridPercolation
