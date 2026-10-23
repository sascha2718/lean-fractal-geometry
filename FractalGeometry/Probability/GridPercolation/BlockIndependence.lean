import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.ColumnOffspring
import FractalGeometry.Probability.GridPercolation.Configuration
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.LawInvariance
import FractalGeometry.Probability.GridPercolation.Process

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {A : GridLaw} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

abbrev ShallowCoord (A : GridLaw) (c : ℕ) := {u : Word A // u.length < c} × (Fin A.M × Fin A.N)

def shallowVector (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (c : ℕ) (ω : Ω) :
    ShallowCoord A c → Bool :=
  fun j => X j.1.1 j.2 ω

def deepVector (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (root : Word A) (ω : Ω) :
    Configuration A :=
  fun q => X (root ++ q.1) q.2 ω

omit [MeasurableSpace Ω] in

lemma deepVector_eq_rebase (root : Word A) (ω : Ω) :
    deepVector X root ω = rebase root (config X ω) := rfl

def BlockIndex (A : GridLaw) {ι : Type*} (c : ℕ) : Option ι → Type _
  | none => ShallowCoord A c
  | some _ => Word A × (Fin A.M × Fin A.N)

def partitionCoordinate {ι : Type*} (roots : ι → Word A) (c : ℕ) :
    (o : Option ι) × BlockIndex A (ι := ι) c o → Word A × (Fin A.M × Fin A.N)
  | ⟨none, j⟩ => (j.1.1, j.2)
  | ⟨some i, q⟩ => (roots i ++ q.1, q.2)

lemma partitionCoordinate_injective {ι : Type*} (roots : ι → Word A) {c : ℕ}
    (hlen : ∀ i, (roots i).length = c) (hinj : Function.Injective roots) :
    Function.Injective (partitionCoordinate roots c) := by
  rintro ⟨o, j⟩ ⟨o', j'⟩ h
  rcases o with _ | i <;> rcases o' with _ | i'
  · simp only [partitionCoordinate, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have : j = j' := Prod.ext (Subtype.ext h1) h2
    rw [this]
  · exfalso
    simp only [partitionCoordinate, Prod.mk.injEq] at h
    have hl := congrArg List.length h.1
    rw [List.length_append, hlen i'] at hl
    have := j.1.2
    omega
  · exfalso
    simp only [partitionCoordinate, Prod.mk.injEq] at h
    have hl := congrArg List.length h.1
    rw [List.length_append, hlen i] at hl
    have := j'.1.2
    omega
  · simp only [partitionCoordinate, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hlen' : (roots i).length = (roots i').length := by rw [hlen i, hlen i']
    obtain ⟨hr, hu⟩ := List.append_inj h1 hlen'
    have hii := hinj hr
    subst hii
    have : j = j' := Prod.ext hu h2
    rw [this]

def blockVector (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) {ι : Type*}
    (roots : ι → Word A) (c : ℕ) (o : Option ι) (ω : Ω) : BlockIndex A (ι := ι) c o → Bool :=
  fun j => X (partitionCoordinate roots c ⟨o, j⟩).1 (partitionCoordinate roots c ⟨o, j⟩).2 ω

omit [MeasurableSpace Ω] in
lemma blockVector_none {ι : Type*} (roots : ι → Word A) (c : ℕ) (ω : Ω) :
    blockVector X roots c none ω = shallowVector X c ω := rfl

omit [MeasurableSpace Ω] in
lemma blockVector_some {ι : Type*} (roots : ι → Word A) (c : ℕ) (i : ι) (ω : Ω) :
    blockVector X roots c (some i) ω = deepVector X (roots i) ω := rfl

theorem iIndepFun_shallow_deep (hX : IsPercolation P X) {ι : Type*} (roots : ι → Word A)
    {c : ℕ} (hlen : ∀ i, (roots i).length = c) (hinj : Function.Injective roots) :
    iIndepFun (fun o ω => blockVector X roots c o ω) P := by
  let : IsProbabilityMeasure P := hX.toIsProbabilityMeasure
  have hraw := hX.indep.precomp (partitionCoordinate_injective roots hlen hinj)
  exact iIndepFun_curry_of_uncurry
    (Z := fun (o : Option ι) (j : BlockIndex A (ι := ι) c o) ω =>
      X (partitionCoordinate roots c ⟨o, j⟩).1 (partitionCoordinate roots c ⟨o, j⟩).2 ω)
    (fun o j => hX.measurable _ _) hraw

theorem measure_shallow_inter_biInter (hX : IsPercolation P X) {ι : Type*} [DecidableEq ι]
    (roots : ι → Word A) {c : ℕ} (hlen : ∀ i, (roots i).length = c)
    (hinj : Function.Injective roots) {S₀ : Set (ShallowCoord A c → Bool)}
    (hS₀ : MeasurableSet S₀) {S : ι → Set (Configuration A)}
    (hS : ∀ i, MeasurableSet (S i)) (I : Finset ι) :
    P ({ω | shallowVector X c ω ∈ S₀} ∩ ⋂ i ∈ I, {ω | deepVector X (roots i) ω ∈ S i}) =
      P {ω | shallowVector X c ω ∈ S₀} * ∏ i ∈ I, P {ω | deepVector X (roots i) ω ∈ S i} := by
  classical
  have hind := iIndepFun_shallow_deep hX roots hlen hinj

  set s : Option ι → Set Ω := fun o =>
    match o with
    | none => {ω | shallowVector X c ω ∈ S₀}
    | some i => {ω | deepVector X (roots i) ω ∈ S i} with hs
  have hmeas : ∀ o ∈ insert none (I.image some),
      MeasurableSet[MeasurableSpace.comap (fun ω => blockVector X roots c o ω) inferInstance]
        (s o) := by
    intro o _
    rcases o with _ | i
    · exact MeasurableSpace.measurableSet_comap.mpr ⟨S₀, hS₀, rfl⟩
    · exact MeasurableSpace.measurableSet_comap.mpr ⟨S i, hS i, rfl⟩
  have h := hind.meas_biInter hmeas
  have hnone : none ∉ I.image some := by simp
  rw [Finset.set_biInter_insert, Finset.set_biInter_finset_image, Finset.prod_insert hnone,
    Finset.prod_image (fun _ _ _ _ h => Option.some_injective _ h)] at h
  exact h

theorem measure_forall_retained_eq_prod (hX : IsPercolation P X)
    (F : Finset (Word A × (Fin A.M × Fin A.N))) :
    P {ω | ∀ q ∈ F, X q.1 q.2 ω = true} = ∏ q ∈ F, ENNReal.ofReal (A.p q.2.1 q.2.2) := by
  have hset : {ω | ∀ q ∈ F, X q.1 q.2 ω = true} = ⋂ q ∈ F, {ω | X q.1 q.2 ω = true} := by
    ext ω
    simp
  rw [hset]
  have h := hX.indep.meas_biInter (S := F) (s := fun q => {ω | X q.1 q.2 ω = true})
    fun q _ => MeasurableSpace.measurableSet_comap.mpr ⟨{true}, measurableSet_singleton true, rfl⟩
  rw [h]
  exact Finset.prod_congr rfl fun q _ => hX.prob _ _

end FractalGeometry.Probability.GridPercolation
