module

/-
Partitions, conditional measures, conditional information and conditional entropy: the generic
part of `sec:conditional` and of `sec:entropies`, on a standard Borel space `Ω` and on the
two-sided full shift over a finite alphabet.

A partition of `Ω` is a map `ξ : Ω → Set Ω` sending a point to its atom. The conditional
measures are the values of Mathlib's regular conditional probability kernel
`ProbabilityTheory.condExpKernel` given the `σ`-algebra `\widehat{ξ}`.

* `atomsOn`, `atomsOn_of_mem`, `atomsOn_of_notMem`: a partition of a subset `D` of `Ω`, extended
  to a partition of `Ω` by the single atom `Ω ∖ D`.
* `saturated`, `saturated_le`: the `σ`-algebra `\widehat{ξ}` of Borel unions of atoms.
* `IsMeasurablePartition`: the atoms are the fibres of a Borel map into `ℝ`.
* `saturated_eq_comap`: Blackwell's theorem, `\widehat{ξ}` is the pull-back of the Borel
  `σ`-algebra under the map inducing `ξ`.
* `condMeas`, `measurable_condMeas`: the conditional measures `μ_x^ξ`, which are probability
  measures and depend `\widehat{ξ}`-measurably on `x`.
* `condInfo`, `condInfo_nonneg`: the conditional information `I_μ(𝒫 | \widehat{ξ})` of the
  canonical partition `𝒫`.
* `condEntropy`: the conditional entropy `H_μ(𝒫 | \widehat{ξ})`.
* `localEntropy`, `integral_localEntropy`: the pointwise entropy `E_μ(I_μ(𝒫 | \widehat{ξ}) | ℐ)`
  and its integral `H_μ(𝒫 | \widehat{ξ})`.
-/
public import BoxLike.Orientation
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants
public import Mathlib.Probability.Kernel.Condexp

@[expose] public section

namespace BoxLike

open MeasureTheory ProbabilityTheory Set

/-! ### Partitions as atom maps and the `σ`-algebra `\widehat{ξ}` -/

section Partition

variable {Ω : Type*}

open Classical in
/-- A partition of a subset `D` of `Ω`, given by its atom map `ξ`, extended to a partition of
`Ω` by the single extra atom `Ω ∖ D`. The article's partitions `ξ_i`, `ξ_1^⊥` live on the
full-measure set `Σ'` and `\overline{ξ}_i` on `Σ_Z` (`sec:entropies`, tex lines 1777 to 1788 and
1914 to 1920); the conditional measures of a measure on `Σ` or on `{1, …, 2N}^ℤ` giving full
mass to `D` do not see the extra atom. -/
def atomsOn (D : Set Ω) (ξ : Ω → Set Ω) (x : Ω) : Set Ω :=
  if x ∈ D then ξ x ∩ D else Dᶜ

/-- The atom of a point of `D` is the atom of `ξ` cut down to `D`, as for the partitions of
`Σ'` and of `Σ_Z` in `sec:entropies`. -/
theorem atomsOn_of_mem {D : Set Ω} {ξ : Ω → Set Ω} {x : Ω} (hx : x ∈ D) :
    atomsOn D ξ x = ξ x ∩ D := by
  simp [atomsOn, hx]

/-- The atom of a point outside `D` is the extra atom `Ω ∖ D`, which the measures of
`sec:entropies` do not charge. -/
theorem atomsOn_of_notMem {D : Set Ω} {ξ : Ω → Set Ω} {x : Ω} (hx : x ∉ D) :
    atomsOn D ξ x = Dᶜ := by
  simp [atomsOn, hx]

/-- The `σ`-algebra `\widehat{ξ}` of a partition `ξ` given by its atom map (`sec:conditional`,
tex line 1680; Feng, Section 2.1): the Borel sets that are unions of atoms. A set `A` is
saturated when `x ∈ A ↔ y ∈ A` for all `y ∈ ξ(x)`; for an atom map of a partition this says
that `A` is a union of atoms, and in this form the sets form a `σ`-algebra for every map `ξ`. -/
@[implicit_reducible]
def saturated [m : MeasurableSpace Ω] (ξ : Ω → Set Ω) : MeasurableSpace Ω where
  MeasurableSet' A := MeasurableSet[m] A ∧ ∀ x y, y ∈ ξ x → (x ∈ A ↔ y ∈ A)
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ _ _ => Iff.rfl⟩
  measurableSet_compl A hA := ⟨hA.1.compl, fun x y h => not_congr (hA.2 x y h)⟩
  measurableSet_iUnion f hf := ⟨MeasurableSet.iUnion fun n => (hf n).1, fun x y h => by
    simp only [mem_iUnion]
    exact exists_congr fun n => (hf n).2 x y h⟩

/-- `\widehat{ξ}` is a sub-`σ`-algebra of the Borel `σ`-algebra. -/
theorem saturated_le [m : MeasurableSpace Ω] (ξ : Ω → Set Ω) : saturated ξ ≤ m :=
  fun _ hA => hA.1

/-- A measurable partition in the sense used by the article (`sec:conditional`, tex lines 1671
to 1750): the atoms are the fibres of a Borel map into a standard Borel space. Every standard
Borel space embeds measurably into `ℝ`, so the target is `ℝ`. -/
def IsMeasurablePartition [MeasurableSpace Ω] (ξ : Ω → Set Ω) : Prop :=
  ∃ f : Ω → ℝ, Measurable f ∧ ∀ x y, y ∈ ξ x ↔ f y = f x

/-- Blackwell's theorem, proved: for a partition into the fibres of a Borel map `f` between
standard Borel spaces, the Borel sets that are unions of atoms are exactly the preimages of Borel
sets. Hence `\widehat{ξ}` is countably generated, as asserted in `sec:conditional`, tex line
1757, and the two readings of "the `σ`-algebra associated with `ξ`" coincide exactly. -/
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

/-! ### Conditional measures -/

variable [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The conditional measure `μ_x^ξ` of `sec:conditional` (tex lines 1671 to 1685): the value at
`x` of Mathlib's regular conditional probability kernel of `μ` given `\widehat{ξ}`. It needs a
standard Borel space `Ω` and a finite measure `μ`. The kernel is `\widehat{ξ}`-measurable and
satisfies `∫_B μ_x^ξ(A) dμ(x) = μ(A ∩ B)` for `B ∈ \widehat{ξ}` by construction; it is
determined up to a `μ`-null set of points `x`. -/
noncomputable def condMeas (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Set Ω) (x : Ω) :
    Measure Ω :=
  condExpKernel μ (saturated ξ) x

/-- The conditional measures `μ_x^ξ` of `sec:conditional` are probability measures. -/
instance (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Set Ω) (x : Ω) :
    IsProbabilityMeasure (condMeas μ ξ x) := by
  unfold condMeas
  infer_instance

/-- `x ↦ μ_x^ξ(A)` is `\widehat{ξ}`-measurable for every Borel set `A`. -/
theorem measurable_condMeas (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Set Ω) {A : Set Ω}
    (hA : MeasurableSet A) : Measurable[saturated ξ] fun x => condMeas μ ξ x A :=
  measurable_condExpKernel hA

end Partition

/-! ### The sequence spaces are standard Borel -/

section Instances

/-! The instances `condExpKernel` needs. For a finite alphabet with measurable singletons the
alphabet is a discrete measurable space (`MeasurableSingletonClass.toDiscreteMeasurableSpace`),
hence standard Borel (`standardBorelSpace_of_discreteMeasurableSpace`), and so are the countable
products `Σ = ℤ → ι` and `{1, …, 2N}^ℤ = ℤ → ι × ZMod 2` (`StandardBorelSpace.pi_countable`,
`StandardBorelSpace.prod`). -/

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

example : StandardBorelSpace (ℤ → ι) := inferInstance

example : StandardBorelSpace (ℤ → ι × ZMod 2) := inferInstance

end Instances

/-! ### Conditional information and conditional entropy on the shift -/

section ShiftEntropy

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The conditional information `I_μ(𝒫 | \widehat{ξ})(x) = -log E_μ(1_{[x_0]} | \widehat{ξ})(x)`
of the canonical partition `𝒫 = {[i]}` given `\widehat{ξ}` (`sec:conditional`, tex lines 1652 to
1734), with the conditional expectation realised by the kernel: `-log μ_x^ξ([x_0])`. The value is
non-negative. Where `μ_x^ξ([x_0]) = 0` Lean gives `0` and the article `+∞`; this happens on a
`μ`-null set (Feng, Lemma 2.2). -/
noncomputable def condInfo (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (ξ : (ℤ → α) → Set (ℤ → α)) (x : ℤ → α) : ℝ :=
  -Real.log ((condMeas μ ξ x).real {y | y 0 = x 0})

/-- The conditional entropy `H_μ(𝒫 | \widehat{ξ}) = ∫ I_μ(𝒫 | \widehat{ξ}) dμ`
(`sec:conditional`, tex lines 1658 to 1662). -/
noncomputable def condEntropy (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (ξ : (ℤ → α) → Set (ℤ → α)) : ℝ :=
  ∫ x, condInfo μ ξ x ∂μ

/-- The pointwise entropy `E_μ(I_μ(𝒫 | \widehat{ξ}) | ℐ)` of `sec:entropies` (tex line 1808),
where `ℐ` is the `σ`-algebra of shift-invariant Borel sets. It is a conditional expectation and
so is determined up to a `μ`-null set; every statement about it is an almost-everywhere
statement. -/
noncomputable def localEntropy (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (ξ : (ℤ → α) → Set (ℤ → α)) : (ℤ → α) → ℝ :=
  μ[condInfo μ ξ | MeasurableSpace.invariants (shift 1 : (ℤ → α) → ℤ → α)]

/-- The conditional information is non-negative. -/
theorem condInfo_nonneg (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (ξ : (ℤ → α) → Set (ℤ → α)) (x : ℤ → α) : 0 ≤ condInfo μ ξ x :=
  neg_nonneg.2 (Real.log_nonpos measureReal_nonneg measureReal_le_one)

/-- `h(μ) = ∫ h(μ, 𝐢) dμ(𝐢)`: the second equality in the display defining `h_i(μ)`
(`sec:entropies`, tex lines 1813 to 1817). -/
theorem integral_localEntropy (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (ξ : (ℤ → α) → Set (ℤ → α)) : ∫ x, localEntropy μ ξ x ∂μ = condEntropy μ ξ :=
  integral_condExp (MeasurableSpace.invariants_le _)

end ShiftEntropy

end BoxLike
