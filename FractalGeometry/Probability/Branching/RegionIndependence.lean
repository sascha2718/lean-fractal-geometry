import Mathlib
import FractalGeometry.Probability.Branching.Configuration
import FractalGeometry.Probability.Branching.GenerationIndependence
import FractalGeometry.Probability.Branching.IdenticalLaws
import FractalGeometry.Probability.Branching.IndependentVectors
import FractalGeometry.Probability.Branching.Law
import FractalGeometry.Probability.Branching.Process

namespace FractalGeometry.Probability.Branching

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {A : Law} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.arity) → Ω → Bool}

def regionVector (X : Word A → (Fin A.arity) → Ω → Bool)
    (R : Set (Word A × (Fin A.arity))) (ω : Ω) : R → Bool :=
  fun q => X q.1.1 q.1.2 ω

def RegionBlockIndex (A : Law) (R : Set (Word A × (Fin A.arity)))
    (T : Finset (Word A)) : Option T → Type
  | none => R
  | some _ => Word A × (Fin A.arity)

def regionCoordinate (R : Set (Word A × (Fin A.arity))) (T : Finset (Word A)) :
    (o : Option T) × RegionBlockIndex A R T o → Word A × (Fin A.arity)
  | ⟨none, q⟩ => q.1
  | ⟨some v, q⟩ => ((v : Word A) ++ q.1, q.2)

def regionDeepBlock (X : Word A → (Fin A.arity) → Ω → Bool)
    (R : Set (Word A × (Fin A.arity))) {T : Finset (Word A)} (o : Option T) (ω : Ω) :
    RegionBlockIndex A R T o → Bool :=
  fun j => X (regionCoordinate R T ⟨o, j⟩).1 (regionCoordinate R T ⟨o, j⟩).2 ω

lemma regionCoordinate_injective (R : Set (Word A × (Fin A.arity)))
    (T : Finset (Word A)) (hT : ∀ v ∈ T, ∀ v' ∈ T, v <+: v' → v = v')
    (hR : ∀ q ∈ R, ∀ v ∈ T, ¬ v <+: q.1) :
    Function.Injective (regionCoordinate R T) := by
  rintro ⟨o, j⟩ ⟨o', j'⟩ h
  rcases o with _ | v <;> rcases o' with _ | v'
  · change j.1 = j'.1 at h
    have hj : j = j' := Subtype.ext h
    rw [hj]
  · exfalso
    change j.1 = ((v' : Word A) ++ j'.1, j'.2) at h
    have h1 : j.1.1 = (v' : Word A) ++ j'.1 := congrArg Prod.fst h
    exact hR j.1 j.2 v'.1 v'.2 (by rw [h1]; exact List.prefix_append _ _)
  · exfalso
    change ((v : Word A) ++ j.1, j.2) = j'.1 at h
    have h1 : (v : Word A) ++ j.1 = j'.1.1 := congrArg Prod.fst h
    exact hR j'.1 j'.2 v.1 v.2 (by rw [← h1]; exact List.prefix_append _ _)
  · change ((v : Word A) ++ j.1, j.2) = ((v' : Word A) ++ j'.1, j'.2) at h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    have hv : v = v' := by
      rcases le_total (v : Word A).length (v' : Word A).length with hl | hl
      · have hp1 : (v : Word A) <+: (v' : Word A) ++ j'.1 := by
          rw [← h1]; exact List.prefix_append _ _
        exact Subtype.ext (hT v.1 v.2 v'.1 v'.2
          (List.prefix_of_prefix_length_le hp1 (List.prefix_append _ _) hl))
      · have hp1 : (v' : Word A) <+: (v : Word A) ++ j.1 := by
          rw [h1]; exact List.prefix_append _ _
        exact (Subtype.ext (hT v'.1 v'.2 v.1 v.2
          (List.prefix_of_prefix_length_le hp1 (List.prefix_append _ _) hl))).symm
    subst hv
    have hu : j.1 = j'.1 := List.append_cancel_left h1
    have hj : j = j' := Prod.ext hu h2
    rw [hj]

theorem iIndepFun_region_deep (hX : IsPercolation P X)
    (R : Set (Word A × (Fin A.arity))) (T : Finset (Word A))
    (hT : ∀ v ∈ T, ∀ v' ∈ T, v <+: v' → v = v')
    (hR : ∀ q ∈ R, ∀ v ∈ T, ¬ v <+: q.1) :
    iIndepFun (fun (o : Option T) ω => regionDeepBlock X R o ω) P := by
  let : IsProbabilityMeasure P := hX.toIsProbabilityMeasure
  have hraw := hX.indep.precomp (regionCoordinate_injective R T hT hR)
  exact iIndepFun_curry_of_uncurry
    (Z := fun (o : Option T) (j : RegionBlockIndex A R T o) ω =>
      X (regionCoordinate R T ⟨o, j⟩).1 (regionCoordinate R T ⟨o, j⟩).2 ω)
    (fun o j => hX.measurable _ _) hraw

theorem measure_region_inter_biInter_deep (hX : IsPercolation P X)
    (R : Set (Word A × (Fin A.arity))) (T : Finset (Word A))
    (hT : ∀ v ∈ T, ∀ v' ∈ T, v <+: v' → v = v')
    (hR : ∀ q ∈ R, ∀ v ∈ T, ¬ v <+: q.1)
    {H : Set (R → Bool)} (hH : MeasurableSet H)
    (S : Word A → Set (Configuration A)) (hS : ∀ v ∈ T, MeasurableSet (S v)) :
    P ({ω | regionVector X R ω ∈ H} ∩ ⋂ v ∈ T, {ω | deepVector X v ω ∈ S v}) =
      P {ω | regionVector X R ω ∈ H} * ∏ v ∈ T, P {ω | config X ω ∈ S v} := by
  classical
  have hind := iIndepFun_region_deep hX R T hT hR
  set s : Option T → Set Ω := fun o =>
    match o with
    | none => {ω | regionVector X R ω ∈ H}
    | some v => {ω | deepVector X v.1 ω ∈ S v.1} with hs
  have hmeas : ∀ o ∈ insert none (T.attach.image some),
      MeasurableSet[MeasurableSpace.comap (fun ω => regionDeepBlock X R o ω) inferInstance]
        (s o) := by
    intro o ho
    rcases o with _ | v
    · refine MeasurableSpace.measurableSet_comap.mpr ⟨H, hH, ?_⟩
      ext ω
      exact Iff.rfl
    · refine MeasurableSpace.measurableSet_comap.mpr ⟨S v.1, hS v.1 v.2, ?_⟩
      ext ω
      exact Iff.rfl
  have h := hind.meas_biInter hmeas
  have hnone : none ∉ T.attach.image some := by simp
  rw [Finset.set_biInter_insert, Finset.set_biInter_finset_image, Finset.prod_insert hnone,
    Finset.prod_image (fun _ _ _ _ h => Option.some_injective _ h)] at h
  have hinter : (⋂ v ∈ T.attach, s (some v)) = ⋂ v ∈ T, {ω | deepVector X v ω ∈ S v} := by
    ext ω
    simp only [hs, Set.mem_iInter, Set.mem_ofPred_eq, Finset.mem_attach, forall_const,
      Subtype.forall]
  have hprod : ∏ v ∈ T.attach, P (s (some v)) = ∏ v ∈ T, P {ω | config X ω ∈ S v} := by
    rw [Finset.prod_attach T (fun v => P {ω | deepVector X v ω ∈ S v})]
    refine Finset.prod_congr rfl fun v hv => ?_
    have hshift := hX.measure_config_functional_shift v (G := id) measurable_id (hS v hv)
    simpa only [id, deepVector_eq_rebase] using hshift
  rw [hinter, hprod] at h
  exact h

end FractalGeometry.Probability.Branching
