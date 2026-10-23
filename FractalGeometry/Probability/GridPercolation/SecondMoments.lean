import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.BranchingSecondMoment
import FractalGeometry.Probability.GridPercolation.ColumnOffspring
import FractalGeometry.Probability.GridPercolation.Configuration
import FractalGeometry.Probability.GridPercolation.GenerationConditioning
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.LawInvariance
import FractalGeometry.Probability.GridPercolation.PopulationColumns
import FractalGeometry.Probability.GridPercolation.Process
import FractalGeometry.Probability.GridPercolation.Processes
import FractalGeometry.Probability.GridPercolation.PrunedSurvival
import FractalGeometry.Probability.GridPercolation.SurvivalMeasurability
import FractalGeometry.Probability.GridPercolation.TubeRecurrence
import FractalGeometry.Probability.GridPercolation.WordSplitting

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open Filter MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {A : GridLaw} {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
  {X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool}

theorem integral_nextTubeFromStates_eq (hX : IsPercolation P X)
    {L : Nat} (past : ColumnPastState A L) (v : ColumnWord A L) (i : Fin A.M) :
    integral P (fun omega =>
      nextTubeFromStates past (columnFutureState X L omega) v i) =
      A.E i * (pastTubePopulation past v : Real) := by
  classical
  let : IsProbabilityMeasure P := hX.toIsProbabilityMeasure
  let active : RowWord A L -> Bool := activeRowsFromPast past v
  let R := (Finset.univ : Finset (RowWord A L)).filter fun r => active r = true
  let roots : Fin R.card -> Word A := fun c =>
    wordOfCoordinates v (R.equivFin.symm c).1
  have hnext (omega : Omega) :
      nextTubeFromStates past (columnFutureState X L omega) v i =
        ∑ c : Fin R.card, (columnOffspring X (roots c) i omega : Real) := by
    rw [nextTubeFromStates_columnFutureState]
    exact active_columnOffspring_sum_reindex X v active i omega
  rw [show (fun omega =>
      nextTubeFromStates past (columnFutureState X L omega) v i) =
      fun omega => ∑ c : Fin R.card,
        (columnOffspring X (roots c) i omega : Real) by
        funext omega; rw [hnext omega]]
  rw [integral_finsetSum]
  · simp_rw [integral_columnOffspring hX]
    have hcard : R.card = pastTubePopulation past v :=
      activeRowsFromPast_card past v
    simp [hcard, mul_comm]
  · intro c _
    refine Integrable.of_bound
      (measurable_from_nat.comp
        (measurable_columnOffspring hX (roots c) i)).aestronglyMeasurable A.N ?_
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast columnOffspring_le X (roots c) i omega

theorem integral_nextTubeFromStates_sq_le (hX : IsPercolation P X)
    {L : Nat} (past : ColumnPastState A L) (v : ColumnWord A L) (i : Fin A.M) :
    integral P (fun omega =>
      nextTubeFromStates past (columnFutureState X L omega) v i ^ 2) <=
      A.E i ^ 2 * (pastTubePopulation past v : Real) ^ 2 +
        A.N * A.E i * (pastTubePopulation past v : Real) := by
  classical
  let : IsProbabilityMeasure P := hX.toIsProbabilityMeasure
  let active : RowWord A L -> Bool := activeRowsFromPast past v
  let R := (Finset.univ : Finset (RowWord A L)).filter fun r => active r = true
  let roots : Fin R.card -> Word A := fun c =>
    wordOfCoordinates v (R.equivFin.symm c).1
  have hnext (omega : Omega) :
      nextTubeFromStates past (columnFutureState X L omega) v i =
        ∑ c : Fin R.card, (columnOffspring X (roots c) i omega : Real) := by
    rw [nextTubeFromStates_columnFutureState]
    exact active_columnOffspring_sum_reindex X v active i omega
  rw [show (fun omega =>
      nextTubeFromStates past (columnFutureState X L omega) v i ^ 2) =
      fun omega => (∑ c : Fin R.card,
        (columnOffspring X (roots c) i omega : Real)) ^ 2 by
        funext omega; rw [hnext omega]]
  have hbound := integral_sq_sum_le
    (P := P) (y := R.card)
    (xi := fun c omega => (columnOffspring X (roots c) i omega : Real))
    (K := (A.N : Real)) (mu := A.E i)
    (iIndepFun_columnOffspring_of_injective hX roots
      (active_columnOffspring_roots_injective v active) i)
    (fun c => (measurable_from_nat.comp
      (measurable_columnOffspring hX (roots c) i)))
    (fun _ _ => Nat.cast_nonneg _)
    (fun c omega => by exact_mod_cast columnOffspring_le X (roots c) i omega)
    (fun c => (integral_columnOffspring hX (roots c) i).le)
    (A.E_nonneg i) (by positivity)
  have hcard : R.card = pastTubePopulation past v := by
    exact activeRowsFromPast_card past v
  simpa [hcard] using hbound

noncomputable def totalOffspring
    (X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool)
    (root : Word A) (omega : Omega) : Nat :=
  ∑ i : Fin A.M, columnOffspring X root i omega

theorem measurable_totalOffspring (hX : IsPercolation P X) (root : Word A) :
    Measurable (totalOffspring X root) := by
  unfold totalOffspring
  exact Finset.measurable_fun_sum _ fun i _ => measurable_columnOffspring hX root i

omit [MeasurableSpace Omega] in

theorem totalOffspring_le
    (X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool)
    (root : Word A) (omega : Omega) : totalOffspring X root omega <= A.M * A.N := by
  unfold totalOffspring
  calc
    ∑ i : Fin A.M, columnOffspring X root i omega <= ∑ _i : Fin A.M, A.N :=
      Finset.sum_le_sum fun i _ => columnOffspring_le X root i omega
    _ = A.M * A.N := by simp

theorem integral_totalOffspring (hX : IsPercolation P X) (root : Word A) :
    integral P (fun omega => (totalOffspring X root omega : Real)) = A.m := by
  classical
  let : IsProbabilityMeasure P := hX.toIsProbabilityMeasure
  have hfun : (fun omega => (totalOffspring X root omega : Real)) =
      fun omega => ∑ i : Fin A.M, (columnOffspring X root i omega : Real) := by
    funext omega
    simp [totalOffspring]
  rw [hfun, integral_finsetSum]
  · simp_rw [integral_columnOffspring hX]
    rfl
  · intro i _
    refine Integrable.of_bound
      (measurable_from_nat.comp
        (measurable_columnOffspring hX root i)).aestronglyMeasurable A.N ?_
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast columnOffspring_le X root i omega

theorem iIndepFun_totalOffspring_of_injective (hX : IsPercolation P X)
    {I : Type*} (roots : I -> Word A) (hroots : Function.Injective roots) :
    iIndepFun (fun c omega => (totalOffspring X (roots c) omega : Real)) P := by
  let : IsProbabilityMeasure P := hX.toIsProbabilityMeasure
  have hpair := iIndepFun_columnOffspring_pairs_of_injective hX roots hroots
  have hraw : iIndepFun (fun p : (c : I) × Fin A.M => fun omega =>
      (columnOffspring X (roots p.1) p.2 omega : Real)) P := by
    apply hpair.precomp (g := fun p : (c : I) × Fin A.M => (p.1, p.2))
    rintro ⟨c, i⟩ ⟨d, j⟩ h
    have hcd : c = d := congrArg Prod.fst h
    subst d
    have hij : i = j := congrArg Prod.snd h
    subst j
    rfl
  have hvec : iIndepFun (fun c omega i =>
      (columnOffspring X (roots c) i omega : Real)) P :=
    iIndepFun_curry_of_uncurry
      (fun c i => measurable_from_nat.comp
        (measurable_columnOffspring hX (roots c) i)) hraw
  have hsum := hvec.comp
    (fun _ z => ∑ i : Fin A.M, z i)
    (fun _ => Finset.measurable_fun_sum _ fun i _ => measurable_pi_apply i)
  apply hsum.congr
  intro c
  filter_upwards [] with omega
  simp [totalOffspring]

noncomputable def pastTotalPopulation {L : Nat} (past : ColumnPastState A L) : Nat := by
  classical
  exact ((Finset.univ : Finset (DigitWord A L)).filter fun u =>
    retainedFromPast past (digitSplit u).1 (digitSplit u).2).card

omit [MeasurableSpace Omega] in

theorem pastTotalPopulation_columnPastState (L : Nat) (omega : Omega) :
    pastTotalPopulation (columnPastState X L omega) =
      descendantCountBelow X [] L omega := by
  classical
  unfold pastTotalPopulation descendantCountBelow
  rw [Set.toFinset_ofPred]
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [retainedFromPast_columnPastState_iff]
  rw [← wordOfDigits_eq_wordOfCoordinates]

noncomputable def nextTotalPopulationFromStates {L : Nat}
    (past : ColumnPastState A L) (future : ColumnFutureState A L) : Real :=
  nextColumnWeightFromStates 1 past future

omit [MeasurableSpace Omega] in

theorem nextTotalPopulationFromStates_states (L : Nat) (omega : Omega) :
    nextTotalPopulationFromStates (columnPastState X L omega)
      (columnFutureState X L omega) =
      (descendantCountBelow X [] (L + 1) omega : Real) := by
  rw [nextTotalPopulationFromStates, nextColumnWeightFromStates_states]
  exact (descendantCountBelow_nil_eq_occupiedColumnWeight_one (X := X) (L + 1) omega).symm

noncomputable def activeDigitsFromPast {L : Nat} (past : ColumnPastState A L) :
    DigitWord A L -> Bool := by
  classical
  exact fun u => decide (retainedFromPast past (digitSplit u).1 (digitSplit u).2)

@[simp] theorem activeDigitsFromPast_eq_true_iff {L : Nat}
    (past : ColumnPastState A L) (u : DigitWord A L) :
    activeDigitsFromPast past u = true <->
      retainedFromPast past (digitSplit u).1 (digitSplit u).2 := by
  classical
  simp [activeDigitsFromPast]

omit [MeasurableSpace Omega] in

theorem nextTotalPopulationFromStates_reindex {L : Nat}
    (past : ColumnPastState A L) (omega : Omega) :
    let active : DigitWord A L -> Bool := activeDigitsFromPast past
    let R := (Finset.univ : Finset (DigitWord A L)).filter fun u => active u = true
    let roots : Fin R.card -> Word A := fun c =>
      wordOfDigits (R.equivFin.symm c).1
    nextTotalPopulationFromStates past (columnFutureState X L omega) =
      ∑ c : Fin R.card, (totalOffspring X (roots c) omega : Real) := by
  classical
  dsimp only
  let active : DigitWord A L -> Bool := activeDigitsFromPast past
  let R := (Finset.univ : Finset (DigitWord A L)).filter fun u => active u = true
  let roots : Fin R.card -> Word A := fun c =>
    wordOfDigits (R.equivFin.symm c).1
  let e : DigitWord A L ≃ (ColumnWord A L × RowWord A L) :=
    Equiv.ofBijective digitSplit (digitSplit_bijective L)
  have hpair : nextTotalPopulationFromStates past (columnFutureState X L omega) =
      ∑ p : ColumnWord A L × RowWord A L,
        if retainedFromPast past p.1 p.2 then
          (totalOffspring X (wordOfCoordinates p.1 p.2) omega : Real) else 0 := by
    rw [nextTotalPopulationFromStates,
      nextColumnWeightFromStates_columnFutureState]
    simp only [Real.rpow_one, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : retainedFromPast past v r
    · simp [activeRowsFromPast, hr, totalOffspring]
    · simp [activeRowsFromPast, hr]
  have hdigit : nextTotalPopulationFromStates past (columnFutureState X L omega) =
      ∑ u : DigitWord A L,
        if retainedFromPast past (digitSplit u).1 (digitSplit u).2 then
          (totalOffspring X (wordOfDigits u) omega : Real) else 0 := by
    rw [hpair]
    symm
    exact Fintype.sum_equiv e _ _ fun u => by
      simp only [e, Equiv.coe_ofBijective]
      rw [wordOfDigits_eq_wordOfCoordinates]
      congr
  rw [hdigit]
  calc
    (∑ u : DigitWord A L,
        if retainedFromPast past (digitSplit u).1 (digitSplit u).2 then
          (totalOffspring X (wordOfDigits u) omega : Real) else 0) =
        ∑ u : DigitWord A L, if active u then
          (totalOffspring X (wordOfDigits u) omega : Real) else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      simp [active]
    _ = R.sum (fun u => (totalOffspring X (wordOfDigits u) omega : Real)) := by
      rw [show R = (Finset.univ : Finset (DigitWord A L)).filter
        (fun u => active u = true) from rfl]
      rw [Finset.sum_filter]
    _ = ∑ u : R, (totalOffspring X (wordOfDigits u.1) omega : Real) := by
      apply Finset.sum_subtype
      intro u
      rfl
    _ = ∑ c : Fin R.card, (totalOffspring X (roots c) omega : Real) := by
      exact Fintype.sum_equiv R.equivFin _ _ fun u => by simp [roots]

theorem activeDigitsFromPast_card {L : Nat} (past : ColumnPastState A L) :
    ((Finset.univ : Finset (DigitWord A L)).filter fun u =>
      activeDigitsFromPast past u = true).card = pastTotalPopulation past := by
  classical
  unfold pastTotalPopulation
  congr 1

theorem activeDigitsFromPast_roots_injective {L : Nat}
    (past : ColumnPastState A L) :
    let R := (Finset.univ : Finset (DigitWord A L)).filter fun u =>
      activeDigitsFromPast past u = true
    Function.Injective (fun c : Fin R.card => wordOfDigits (R.equivFin.symm c).1) := by
  classical
  dsimp only
  let R := (Finset.univ : Finset (DigitWord A L)).filter fun u =>
    activeDigitsFromPast past u = true
  intro c d h
  have hud : (R.equivFin.symm c).1 = (R.equivFin.symm d).1 :=
    List.ofFn_injective h
  apply R.equivFin.symm.injective
  exact Subtype.ext hud

theorem integral_nextTotalPopulationFromStates_eq (hX : IsPercolation P X)
    {L : Nat} (past : ColumnPastState A L) :
    integral P (fun omega =>
      nextTotalPopulationFromStates past (columnFutureState X L omega)) =
      A.m * (pastTotalPopulation past : Real) := by
  classical
  let : IsProbabilityMeasure P := hX.toIsProbabilityMeasure
  let R := (Finset.univ : Finset (DigitWord A L)).filter fun u =>
    activeDigitsFromPast past u = true
  let roots : Fin R.card -> Word A := fun c =>
    wordOfDigits (R.equivFin.symm c).1
  have hnext (omega : Omega) :
      nextTotalPopulationFromStates past (columnFutureState X L omega) =
        ∑ c : Fin R.card, (totalOffspring X (roots c) omega : Real) :=
    nextTotalPopulationFromStates_reindex past omega
  rw [show (fun omega =>
      nextTotalPopulationFromStates past (columnFutureState X L omega)) =
      fun omega => ∑ c : Fin R.card, (totalOffspring X (roots c) omega : Real) by
        funext omega; exact hnext omega]
  rw [integral_finsetSum]
  · simp_rw [integral_totalOffspring hX]
    have hcard : R.card = pastTotalPopulation past := activeDigitsFromPast_card past
    simp [hcard, mul_comm]
  · intro c _
    refine Integrable.of_bound
      (measurable_from_nat.comp
        (measurable_totalOffspring hX (roots c))).aestronglyMeasurable
      (A.M * A.N) ?_
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast totalOffspring_le X (roots c) omega

theorem integral_sq_nextTotalPopulationFromStates_le (hX : IsPercolation P X)
    {L : Nat} (past : ColumnPastState A L) :
    integral P (fun omega =>
      nextTotalPopulationFromStates past (columnFutureState X L omega) ^ 2) <=
      A.m ^ 2 * (pastTotalPopulation past : Real) ^ 2 +
        (A.M * A.N) * A.m * (pastTotalPopulation past : Real) := by
  classical
  let : IsProbabilityMeasure P := hX.toIsProbabilityMeasure
  let R := (Finset.univ : Finset (DigitWord A L)).filter fun u =>
    activeDigitsFromPast past u = true
  let roots : Fin R.card -> Word A := fun c =>
    wordOfDigits (R.equivFin.symm c).1
  have hnext (omega : Omega) :
      nextTotalPopulationFromStates past (columnFutureState X L omega) =
        ∑ c : Fin R.card, (totalOffspring X (roots c) omega : Real) :=
    nextTotalPopulationFromStates_reindex past omega
  rw [show (fun omega =>
      nextTotalPopulationFromStates past (columnFutureState X L omega) ^ 2) =
      fun omega => (∑ c : Fin R.card,
        (totalOffspring X (roots c) omega : Real)) ^ 2 by
        funext omega; rw [hnext omega]]
  have hbound := integral_sq_sum_le
    (P := P) (y := R.card)
    (xi := fun c omega => (totalOffspring X (roots c) omega : Real))
    (K := (A.M * A.N : Nat)) (mu := A.m)
    (iIndepFun_totalOffspring_of_injective hX roots <|
      activeDigitsFromPast_roots_injective past)
    (fun c => measurable_from_nat.comp (measurable_totalOffspring hX (roots c)))
    (fun _ _ => Nat.cast_nonneg _)
    (fun c omega => by exact_mod_cast totalOffspring_le X (roots c) omega)
    (fun c => (integral_totalOffspring hX (roots c)).le)
    A.m_nonneg (by positivity)
  have hcard : R.card = pastTotalPopulation past := activeDigitsFromPast_card past
  simpa [hcard] using hbound

omit [MeasurableSpace Omega] in

@[simp] theorem descendantCountBelow_nil_zero
    (X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool) (omega : Omega) :
    descendantCountBelow X [] 0 omega = 1 := by
  classical
  unfold descendantCountBelow
  rw [Finset.card_eq_one]
  refine ⟨fun l : Fin 0 => l.elim0, ?_⟩
  ext u
  simp only [Set.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_singleton]
  constructor
  · intro _
    exact Subsingleton.elim _ _
  · intro _ l
    have hl : l.val < 0 := by simpa [wordOfDigits] using l.isLt
    omega

theorem integral_descendantCountBelow_nil_succ_eq (hX : IsPercolation P X)
    (L : Nat) :
    integral P (fun omega => (descendantCountBelow X [] (L + 1) omega : Real)) =
      A.m * integral P (fun omega => (descendantCountBelow X [] L omega : Real)) := by
  let : IsProbabilityMeasure P := hX.toIsProbabilityMeasure
  have hcoupled := integral_coupled_eq_of_indepFun_finite_states
    (hX.indepFun_columnPastState_columnFutureState L)
    (hX.measurable_columnPastState L)
    (hX.measurable_columnFutureState L)
    (fun past future => nextTotalPopulationFromStates past future)
    (fun past => A.m * (pastTotalPopulation past : Real))
    (fun past => integral_nextTotalPopulationFromStates_eq hX past)
  have hnext : (fun omega => nextTotalPopulationFromStates
      (columnPastState X L omega) (columnFutureState X L omega)) =
      fun omega => (descendantCountBelow X [] (L + 1) omega : Real) := by
    funext omega
    exact nextTotalPopulationFromStates_states L omega
  have hpast : (fun omega =>
      A.m * (pastTotalPopulation (columnPastState X L omega) : Real)) =
      fun omega => A.m * (descendantCountBelow X [] L omega : Real) := by
    funext omega
    rw [pastTotalPopulation_columnPastState]
  rw [hnext, hpast] at hcoupled
  simpa only [integral_const_mul] using hcoupled

theorem integral_descendantCountBelow_nil_eq (hX : IsPercolation P X) (L : Nat) :
    integral P (fun omega => (descendantCountBelow X [] L omega : Real)) = A.m ^ L := by
  let : IsProbabilityMeasure P := hX.toIsProbabilityMeasure
  induction L with
  | zero =>
      have hfun : (fun omega => (descendantCountBelow X [] 0 omega : Real)) =
          fun _ => (1 : Real) := by
        funext omega
        rw [descendantCountBelow_nil_zero]
        norm_num
      rw [hfun, integral_const, probReal_univ, one_smul]
      simp
  | succ L ih =>
      rw [integral_descendantCountBelow_nil_succ_eq hX L, ih, pow_succ]
      ring

theorem integral_sq_descendantCountBelow_nil_succ_le (hX : IsPercolation P X)
    (L : Nat) :
    integral P (fun omega =>
      (descendantCountBelow X [] (L + 1) omega : Real) ^ 2) <=
      A.m ^ 2 * integral P (fun omega =>
        (descendantCountBelow X [] L omega : Real) ^ 2) +
      (A.M * A.N) * A.m * integral P (fun omega =>
        (descendantCountBelow X [] L omega : Real)) := by
  let : IsProbabilityMeasure P := hX.toIsProbabilityMeasure
  have hcoupled := integral_coupled_le_of_indepFun_finite_states
    (hX.indepFun_columnPastState_columnFutureState L)
    (hX.measurable_columnPastState L)
    (hX.measurable_columnFutureState L)
    (fun past future => nextTotalPopulationFromStates past future ^ 2)
    (fun past => A.m ^ 2 * (pastTotalPopulation past : Real) ^ 2 +
      (A.M * A.N) * A.m * (pastTotalPopulation past : Real))
    (fun past => integral_sq_nextTotalPopulationFromStates_le hX past)
  have hnext : (fun omega => nextTotalPopulationFromStates
      (columnPastState X L omega) (columnFutureState X L omega) ^ 2) =
      fun omega => (descendantCountBelow X [] (L + 1) omega : Real) ^ 2 := by
    funext omega
    rw [nextTotalPopulationFromStates_states]
  let Z : Omega -> Real := fun omega => (descendantCountBelow X [] L omega : Real)
  have hpast : (fun omega =>
      A.m ^ 2 * (pastTotalPopulation (columnPastState X L omega) : Real) ^ 2 +
        (A.M * A.N) * A.m *
          (pastTotalPopulation (columnPastState X L omega) : Real)) =
      fun omega => A.m ^ 2 * Z omega ^ 2 + (A.M * A.N) * A.m * Z omega := by
    funext omega
    simp only [Z]
    rw [pastTotalPopulation_columnPastState]
  rw [hnext, hpast] at hcoupled
  have hnatmeas : Measurable (descendantCountBelow X [] L) := by
    rw [show descendantCountBelow X [] L =
        fun omega => descendantCountConfig (config X omega) [] L by
      funext omega; exact descendantCountBelow_eq_config [] L omega]
    exact (measurable_descendantCountConfig [] L).comp (measurable_config hX)
  have hZmeas : Measurable Z := measurable_from_nat.comp hnatmeas
  have hZint : Integrable Z P := by
    refine Integrable.of_bound hZmeas.aestronglyMeasurable
      (((A.M * A.N : Nat) : Real) ^ L) ?_
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    change (descendantCountBelow X [] L omega : Real) <= ((A.M * A.N : Nat) : Real) ^ L
    exact_mod_cast descendantCountBelow_le X [] L omega
  have hZ2int : Integrable (fun omega => Z omega ^ 2) P := by
    refine Integrable.of_bound (hZmeas.pow_const 2).aestronglyMeasurable
      ((((A.M * A.N : Nat) : Real) ^ L) ^ 2) ?_
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _)
      (by
        change (descendantCountBelow X [] L omega : Real) <=
          ((A.M * A.N : Nat) : Real) ^ L
        exact_mod_cast descendantCountBelow_le X [] L omega) 2
  have hrhs : integral P (fun omega =>
      A.m ^ 2 * Z omega ^ 2 + (A.M * A.N) * A.m * Z omega) =
      A.m ^ 2 * integral P (fun omega => Z omega ^ 2) +
        (A.M * A.N) * A.m * integral P Z := by
    rw [integral_add (hZ2int.const_mul _) (hZint.const_mul _),
      integral_const_mul, integral_const_mul]
  rw [hrhs] at hcoupled
  exact hcoupled

theorem integral_sq_descendantCountBelow_nil_le_uniform (hX : IsPercolation P X)
    (hm : 1 < A.m) (L : Nat) :
    integral P (fun omega => (descendantCountBelow X [] L omega : Real) ^ 2) <=
      A.m ^ (2 * L) * (1 + (A.M * A.N) / (A.m - 1)) := by
  let : IsProbabilityMeasure P := hX.toIsProbabilityMeasure
  let a : Nat -> Real := fun n =>
    integral P (fun omega => (descendantCountBelow X [] n omega : Real))
  let b : Nat -> Real := fun n =>
    integral P (fun omega => (descendantCountBelow X [] n omega : Real) ^ 2)
  have ha (n : Nat) : a n = A.m ^ n := integral_descendantCountBelow_nil_eq hX n
  have hb0 : b 0 <= 1 := by
    have hfun : (fun omega => (descendantCountBelow X [] 0 omega : Real) ^ 2) =
        fun _ => (1 : Real) := by
      funext omega
      rw [descendantCountBelow_nil_zero]
      norm_num
    simp only [b]
    rw [hfun, integral_const, probReal_univ, one_smul]
  have hb (n : Nat) : b (n + 1) <=
      A.m ^ 2 * b n + (A.M * A.N) * A.m * a n :=
    integral_sq_descendantCountBelow_nil_succ_le hX n
  exact secondMoment_le_mean_sq_mul_uniform hm (by positivity) ha hb0 hb L

theorem ofReal_one_div_four_uniform_le_descendantCountBelow_nil_ge_half
    (hX : IsPercolation P X) (hm : 1 < A.m) (L : Nat) :
    ENNReal.ofReal (1 / (4 * (1 + (A.M * A.N) / (A.m - 1)))) <=
      P {omega | (1 / 2 : Real) * A.m ^ L <=
        (descendantCountBelow X [] L omega : Real)} := by
  let : IsProbabilityMeasure P := hX.toIsProbabilityMeasure
  let Z : Omega -> Real := fun omega => (descendantCountBelow X [] L omega : Real)
  let B : Real := A.m ^ (2 * L) * (1 + (A.M * A.N) / (A.m - 1))
  have hnatmeas : Measurable (descendantCountBelow X [] L) := by
    rw [show descendantCountBelow X [] L =
        fun omega => descendantCountConfig (config X omega) [] L by
      funext omega; exact descendantCountBelow_eq_config [] L omega]
    exact (measurable_descendantCountConfig [] L).comp (measurable_config hX)
  have hZmeas : Measurable Z := measurable_from_nat.comp hnatmeas
  have hZnonneg (omega : Omega) : 0 <= Z omega := Nat.cast_nonneg _
  have hZbound : exists C : Real, forall omega, Z omega <= C := by
    refine ⟨(((A.M * A.N : Nat) : Real) ^ L), fun omega => ?_⟩
    change (descendantCountBelow X [] L omega : Real) <=
      ((A.M * A.N : Nat) : Real) ^ L
    exact_mod_cast descendantCountBelow_le X [] L omega
  have hB : integral P (fun omega => Z omega ^ 2) <= B :=
    integral_sq_descendantCountBelow_nil_le_uniform hX hm L
  have hden : 0 < A.m - 1 := sub_pos.mpr hm
  have hfactor : 0 < 1 + (A.M * A.N) / (A.m - 1) := by positivity
  have hBpos : 0 < B := by
    dsimp only [B]
    positivity
  have hpaley := one_fourth_mul_sq_integral_div_le_measure_ge_half
    hZmeas hZnonneg hZbound hB hBpos
  have hmean : integral P Z = A.m ^ L := integral_descendantCountBelow_nil_eq hX L
  have hsquare : (A.m ^ L) ^ 2 = A.m ^ (2 * L) := by
    rw [← pow_mul]
    congr 1
    omega
  have hfrac : (A.m ^ L) ^ 2 / (4 * B) =
      1 / (4 * (1 + (A.M * A.N) / (A.m - 1))) := by
    rw [hsquare]
    dsimp only [B]
    field_simp
  have hreal : 1 / (4 * (1 + (A.M * A.N) / (A.m - 1))) <=
      (P {omega | (1 / 2 : Real) * A.m ^ L <= Z omega}).toReal := by
    have hp := hpaley
    rw [hmean] at hp
    have hthreshold : A.m ^ L / 2 = (1 / 2 : Real) * A.m ^ L := by ring
    rw [hthreshold] at hp
    rw [← hfrac]
    exact hp
  rw [← ENNReal.ofReal_toReal (measure_ne_top P
    {omega | (1 / 2 : Real) * A.m ^ L <= Z omega})]
  exact ENNReal.ofReal_le_ofReal hreal

omit [MeasurableSpace Omega] in

theorem descendantCountBelow_nil_pos_mono
    (X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool)
    {j k : Nat} (hjk : j <= k) (omega : Omega)
    (hk : 0 < descendantCountBelow X [] k omega) :
    0 < descendantCountBelow X [] j omega := by
  classical
  unfold descendantCountBelow at hk ⊢
  rw [Finset.card_pos] at hk ⊢
  obtain ⟨u, hu⟩ := hk
  simp only [Set.mem_toFinset, Set.mem_ofPred_eq] at hu ⊢
  let u' : DigitWord A j := Fin.take j hjk u
  refine ⟨u', ?_⟩
  simp only [Set.mem_toFinset, Set.mem_ofPred_eq]
  have htake := hu.take j
  have hword : wordOfDigits u' = (wordOfDigits u).take j := by
    exact Fin.ofFn_take_eq_take_ofFn hjk u
  rw [hword]
  exact htake

omit [MeasurableSpace Omega] in

theorem survival_eq_iInter_descendantCountBelow_nil_pos
    (X : Word A -> (Fin A.M × Fin A.N) -> Omega -> Bool) :
    survival X = ⋂ L : Nat, {omega | 0 < descendantCountBelow X [] L omega} := by
  ext omega
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · intro hs L
    exact (one_le_descendantCountBelow_of_mem_survival (X := X) hs L)
  · intro h L
    have hL := h L
    unfold descendantCountBelow at hL
    rw [Finset.card_pos] at hL
    obtain ⟨u, hu⟩ := hL
    simp only [Set.mem_toFinset, Set.mem_ofPred_eq] at hu
    refine ⟨wordOfDigits u, by simp [wordOfDigits], ?_⟩
    exact (retainedBelow_nil_iff_retained X omega (wordOfDigits u)).mp hu

theorem measurableSet_descendantCountBelow_nil_pos (hX : IsPercolation P X) (L : Nat) :
    MeasurableSet {omega | 0 < descendantCountBelow X [] L omega} := by
  have hnatmeas : Measurable (descendantCountBelow X [] L) := by
    rw [show descendantCountBelow X [] L =
        fun omega => descendantCountConfig (config X omega) [] L by
      funext omega; exact descendantCountBelow_eq_config [] L omega]
    exact (measurable_descendantCountConfig [] L).comp (measurable_config hX)
  exact measurableSet_lt measurable_const hnatmeas

theorem measure_survival_pos_of_one_lt_m (hX : IsPercolation P X) (hm : 1 < A.m) :
    0 < P (survival X) := by
  let : IsProbabilityMeasure P := hX.toIsProbabilityMeasure
  let rho : Real := 1 / (4 * (1 + (A.M * A.N) / (A.m - 1)))
  have hrho : 0 < rho := by
    dsimp only [rho]
    have : 0 < A.m - 1 := sub_pos.mpr hm
    positivity
  let S : Nat -> Set Omega := fun L =>
    {omega | 0 < descendantCountBelow X [] L omega}
  have hSmeas (L : Nat) : MeasurableSet (S L) :=
    measurableSet_descendantCountBelow_nil_pos hX L
  have hSanti : Antitone S := by
    intro j k hjk omega hk
    exact descendantCountBelow_nil_pos_mono X hjk omega hk
  have hlower (L : Nat) : ENNReal.ofReal rho <= P (S L) := by
    have hhalf :=
      ofReal_one_div_four_uniform_le_descendantCountBelow_nil_ge_half hX hm L
    refine hhalf.trans (measure_mono ?_)
    intro omega homega
    simp only [Set.mem_ofPred_eq] at homega ⊢
    have hthreshold : 0 < (1 / 2 : Real) * A.m ^ L := by positivity
    have hpos : 0 < (descendantCountBelow X [] L omega : Real) :=
      lt_of_lt_of_le hthreshold homega
    exact_mod_cast hpos
  have hinter : P (⋂ L, S L) = ⨅ L, P (S L) :=
    hSanti.measure_iInter (fun L => (hSmeas L).nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩
  have hsurv : ENNReal.ofReal rho <= P (survival X) := by
    rw [survival_eq_iInter_descendantCountBelow_nil_pos X, hinter]
    exact le_iInf hlower
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hrho) hsurv

end FractalGeometry.Probability.GridPercolation
