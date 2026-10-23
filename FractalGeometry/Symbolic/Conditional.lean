module

public import Mathlib
public import FractalGeometry.Symbolic.Shift

@[expose] public section

namespace FractalGeometry


open MeasureTheory ProbabilityTheory Set

section Partition

variable {Ω : Type*}

open Classical in

def atomsOn (D : Set Ω) (ξ : Ω → Set Ω) (x : Ω) : Set Ω :=
  if x ∈ D then ξ x ∩ D else Dᶜ

theorem atomsOn_of_mem {D : Set Ω} {ξ : Ω → Set Ω} {x : Ω} (hx : x ∈ D) :
    atomsOn D ξ x = ξ x ∩ D := by
  simp [atomsOn, hx]

theorem atomsOn_of_notMem {D : Set Ω} {ξ : Ω → Set Ω} {x : Ω} (hx : x ∉ D) :
    atomsOn D ξ x = Dᶜ := by
  simp [atomsOn, hx]

@[implicit_reducible]

def saturated [m : MeasurableSpace Ω] (ξ : Ω → Set Ω) : MeasurableSpace Ω where
  MeasurableSet' A := MeasurableSet[m] A ∧ ∀ x y, y ∈ ξ x → (x ∈ A ↔ y ∈ A)
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ _ _ => Iff.rfl⟩
  measurableSet_compl A hA := ⟨hA.1.compl, fun x y h => not_congr (hA.2 x y h)⟩
  measurableSet_iUnion f hf := ⟨MeasurableSet.iUnion fun n => (hf n).1, fun x y h => by
    simp only [mem_iUnion]
    exact exists_congr fun n => (hf n).2 x y h⟩

theorem saturated_le [m : MeasurableSpace Ω] (ξ : Ω → Set Ω) : saturated ξ ≤ m :=
  fun _ hA => hA.1

theorem saturated_eq_comap {Y : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace Y] [StandardBorelSpace Y] {f : Ω → Y} (hf : Measurable f)
    {ξ : Ω → Set Ω} (hξ : ∀ x y, y ∈ ξ x ↔ f y = f x) :
    saturated ξ = MeasurableSpace.comap f inferInstance := by
  let := upgradeStandardBorel Y
  apply le_antisymm
  · rintro A ⟨hAm, hsat⟩
    have h1 : AnalyticSet (f '' A) := hAm.analyticSet_image hf
    have h2 : AnalyticSet (f '' Aᶜ) := hAm.compl.analyticSet_image hf
    have hdisj : Disjoint (f '' A) (f '' Aᶜ) := by
      rw [Set.disjoint_left]
      rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
      exact hb ((hsat a b ((hξ a b).2 hab)).1 ha)
    obtain ⟨B, hAB, hBA, hB⟩ := h1.measurablySeparable h2 hdisj
    refine ⟨B, hB, ?_⟩
    ext x
    constructor
    · intro hx
      by_contra hxA
      exact Set.disjoint_left.1 hBA ⟨x, hxA, rfl⟩ hx
    · intro hx
      exact hAB ⟨x, hx, rfl⟩
  · rintro _ ⟨B, hB, rfl⟩
    refine ⟨hf hB, fun x y hxy => ?_⟩
    simp only [mem_preimage, (hξ x y).1 hxy]

variable [MeasurableSpace Ω] [StandardBorelSpace Ω]

noncomputable def condMeas (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Set Ω) (x : Ω) :
    Measure Ω :=
  condExpKernel μ (saturated ξ) x

instance (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Set Ω) (x : Ω) :
    IsProbabilityMeasure (condMeas μ ξ x) := by
  unfold condMeas
  infer_instance

theorem measurable_condMeas (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Set Ω) {A : Set Ω}
    (hA : MeasurableSet A) : Measurable[saturated ξ] fun x => condMeas μ ξ x A :=
  measurable_condExpKernel hA

end Partition

section ShiftEntropy

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

noncomputable def condInfo (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (ξ : (ℤ → α) → Set (ℤ → α)) (x : ℤ → α) : ℝ :=
  -Real.log ((condMeas μ ξ x).real {y | y 0 = x 0})

noncomputable def condEntropy (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (ξ : (ℤ → α) → Set (ℤ → α)) : ℝ :=
  ∫ x, condInfo μ ξ x ∂μ

noncomputable def localEntropy (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (ξ : (ℤ → α) → Set (ℤ → α)) : (ℤ → α) → ℝ :=
  μ[condInfo μ ξ | MeasurableSpace.invariants (shift 1 : (ℤ → α) → ℤ → α)]

theorem condInfo_nonneg (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (ξ : (ℤ → α) → Set (ℤ → α)) (x : ℤ → α) : 0 ≤ condInfo μ ξ x :=
  neg_nonneg.2 (Real.log_nonpos measureReal_nonneg measureReal_le_one)

theorem integral_localEntropy (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (ξ : (ℤ → α) → Set (ℤ → α)) : ∫ x, localEntropy μ ξ x ∂μ = condEntropy μ ξ :=
  integral_condExp (MeasurableSpace.invariants_le _)

end ShiftEntropy

end FractalGeometry
