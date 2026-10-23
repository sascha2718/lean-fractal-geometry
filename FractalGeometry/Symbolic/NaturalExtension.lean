import Mathlib
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.OneSidedShift
import FractalGeometry.Symbolic.SequenceTopology
import FractalGeometry.Symbolic.Shift

namespace FractalGeometry

open MeasureTheory Filter Topology Set

open scoped ENNReal

section Pad

variable {α : Type*}

def padFrom (m : ℕ) (y : ℕ → α) : ℤ → α := fun k => y ((m : ℤ) + k).toNat

theorem etaFrom_padFrom_add (m j : ℕ) (y : ℕ → α) :
    etaFrom m (padFrom (m + j) y) = shiftPlus^[j] y := by
  funext k
  rw [iterate_shiftPlus_apply]
  simp only [etaFrom, padFrom]
  congr 1
  omega

theorem etaFrom_shift_one (m : ℕ) (x : ℤ → α) :
    etaFrom m (shift 1 x) = shiftPlus (etaFrom m x) := by
  funext k
  simp only [etaFrom, shift_apply, shiftPlus_apply]
  congr 1
  push_cast
  ring

theorem etaFrom_zero : (etaFrom 0 : (ℤ → α) → ℕ → α) = eta := by
  funext x k
  simp [etaFrom]

theorem measurable_padFrom [MeasurableSpace α] (m : ℕ) :
    Measurable (padFrom m : (ℕ → α) → ℤ → α) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

theorem continuous_etaFrom [TopologicalSpace α] (m : ℕ) :
    Continuous (etaFrom m : (ℤ → α) → ℕ → α) :=
  continuous_pi fun _ => continuous_apply _

end Pad

section Content

variable {α : Type*} [MeasurableSpace α] {ν : Measure (ℕ → α)}

noncomputable def futureFun (ν : Measure (ℕ → α)) (s : Set (ℤ → α)) : ℝ≥0∞ :=
  limsup (fun j => ν (padFrom j ⁻¹' s)) atTop

theorem futureFun_eq_of_eventually_eq {s : Set (ℤ → α)} {c : ℝ≥0∞}
    (h : ∀ᶠ j in atTop, ν (padFrom j ⁻¹' s) = c) : futureFun ν s = c := by
  rw [futureFun, limsup_congr h, limsup_const]

theorem measure_preimage_padFrom (hν : MeasurePreserving shiftPlus ν ν) {m j : ℕ} (hmj : m ≤ j)
    {B : Set (ℕ → α)} (hB : MeasurableSet B) :
    ν (padFrom j ⁻¹' (etaFrom m ⁻¹' B)) = ν B := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hmj
  rw [← (hν.iterate i).measure_preimage hB.nullMeasurableSet]
  congr 1
  ext y
  simp only [mem_preimage, etaFrom_padFrom_add]

theorem futureFun_preimage_etaFrom (hν : MeasurePreserving shiftPlus ν ν) (m : ℕ)
    {B : Set (ℕ → α)} (hB : MeasurableSet B) : futureFun ν (etaFrom m ⁻¹' B) = ν B :=
  futureFun_eq_of_eventually_eq <|
    (eventually_ge_atTop m).mono fun _ hj => measure_preimage_padFrom hν hj hB

@[simp] theorem futureFun_empty (ν : Measure (ℕ → α)) : futureFun ν ∅ = 0 :=
  futureFun_eq_of_eventually_eq <| Eventually.of_forall fun _ => by simp

theorem futureFun_union (hν : MeasurePreserving shiftPlus ν ν) {s t : Set (ℤ → α)}
    (hs : s ∈ futureSets α) (ht : t ∈ futureSets α) (hst : Disjoint s t) :
    futureFun ν (s ∪ t) = futureFun ν s + futureFun ν t := by
  obtain ⟨m, B, hB, rfl⟩ := hs
  obtain ⟨m', B', hB', rfl⟩ := ht
  rw [futureFun_preimage_etaFrom hν m hB, futureFun_preimage_etaFrom hν m' hB']
  refine futureFun_eq_of_eventually_eq ((eventually_ge_atTop (max m m')).mono fun j hj => ?_)
  rw [preimage_union, measure_union (hst.preimage _)
    (measurable_padFrom j (measurable_etaFrom m' hB')),
    measure_preimage_padFrom hν ((le_max_left m m').trans hj) hB,
    measure_preimage_padFrom hν ((le_max_right m m').trans hj) hB']

end Content

section Clopen

variable {α : Type*} [TopologicalSpace α]

variable (α) in

def clopenFutureSets : Set (Set (ℤ → α)) :=
  {C | ∃ (m : ℕ) (B : Set (ℕ → α)), IsClopen B ∧ C = etaFrom m ⁻¹' B}

theorem isClopen_of_mem_clopenFutureSets {s : Set (ℤ → α)} (hs : s ∈ clopenFutureSets α) :
    IsClopen s := by
  obtain ⟨m, B, hB, rfl⟩ := hs
  exact hB.preimage (continuous_etaFrom m)

theorem isSetAlgebra_clopenFutureSets : IsSetAlgebra (clopenFutureSets α) where
  empty_mem := ⟨0, ∅, isClopen_empty, rfl⟩
  compl_mem := by
    rintro _ ⟨m, B, hB, rfl⟩
    exact ⟨m, Bᶜ, hB.compl, rfl⟩
  union_mem := by
    rintro _ _ ⟨m₁, B₁, hB₁, rfl⟩ ⟨m₂, B₂, hB₂, rfl⟩
    refine ⟨m₁ + m₂, shiftPlus^[m₂] ⁻¹' B₁ ∪ shiftPlus^[m₁] ⁻¹' B₂,
      (hB₁.preimage (continuous_shiftPlus.iterate m₂)).union
        (hB₂.preimage (continuous_shiftPlus.iterate m₁)), ?_⟩
    ext x
    rw [mem_union, mem_preimage, mem_preimage, etaFrom_eq_iterate m₁ m₂ x,
      etaFrom_eq_iterate m₂ m₁ x, Nat.add_comm m₂ m₁]
    rfl

variable [MeasurableSpace α]

theorem clopenFutureSets_subset_futureSets [OpensMeasurableSpace (ℕ → α)] :
    clopenFutureSets α ⊆ futureSets α := by
  rintro _ ⟨m, B, hB, rfl⟩
  exact ⟨m, B, hB.isOpen.measurableSet, rfl⟩

variable [DiscreteTopology α] [MeasurableSingletonClass α]

theorem generateFrom_clopenFutureSets [Countable α] :
    MeasurableSpace.generateFrom (clopenFutureSets α) =
      (inferInstance : MeasurableSpace (ℤ → α)) := by
  refine le_antisymm (MeasurableSpace.generateFrom_le fun s hs => ?_) ?_
  · exact (isClopen_of_mem_clopenFutureSets hs).isOpen.measurableSet
  · refine iSup_le fun k => ?_
    rintro _ ⟨T, -, rfl⟩
    refine MeasurableSpace.measurableSet_generateFrom
      ⟨k.natAbs, (fun y : ℕ → α => y (k + k.natAbs).toNat) ⁻¹' T,
        (isClopen_discrete T).preimage (continuous_apply _), ?_⟩
    ext x
    have h : -(k.natAbs : ℤ) + ((k + k.natAbs).toNat : ℤ) = k := by omega
    change x k ∈ T ↔ x (-(k.natAbs : ℤ) + ((k + k.natAbs).toNat : ℤ)) ∈ T
    rw [h]

theorem generateFrom_isClopen_oneSided [Countable α] :
    MeasurableSpace.generateFrom {B : Set (ℕ → α) | IsClopen B} =
      (inferInstance : MeasurableSpace (ℕ → α)) := by
  refine le_antisymm (MeasurableSpace.generateFrom_le fun B hB => ?_) ?_
  · exact (show IsClopen B from hB).isOpen.measurableSet
  · refine iSup_le fun k => ?_
    rintro _ ⟨T, -, rfl⟩
    exact MeasurableSpace.measurableSet_generateFrom
      ((isClopen_discrete T).preimage (continuous_apply k))

variable {ν : Measure (ℕ → α)}

noncomputable def futureContent [Countable α] (hν : MeasurePreserving shiftPlus ν ν) :
    AddContent ℝ≥0∞ (clopenFutureSets α) :=
  isSetAlgebra_clopenFutureSets.isSetRing.addContent_of_union (futureFun ν) (futureFun_empty ν)
    fun hs ht hst => futureFun_union hν (clopenFutureSets_subset_futureSets hs)
      (clopenFutureSets_subset_futureSets ht) hst

theorem futureContent_apply [Countable α] (hν : MeasurePreserving shiftPlus ν ν) (m : ℕ)
    {B : Set (ℕ → α)} (hB : IsClopen B) : futureContent hν (etaFrom m ⁻¹' B) = ν B :=
  futureFun_preimage_etaFrom hν m hB.isOpen.measurableSet

theorem isSigmaSubadditive_futureContent [Finite α] [IsFiniteMeasure ν]
    (hν : MeasurePreserving shiftPlus ν ν) : (futureContent hν).IsSigmaSubadditive := by
  have hC := (isSetAlgebra_clopenFutureSets (α := α)).isSetRing
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum hC fun f hf hUf hdisj =>
    addContent_iUnion_eq_sum_of_tendsto_zero hC _ ?_ ?_ hf hUf hdisj
  · rintro _ ⟨m, B, hB, rfl⟩
    rw [futureContent_apply hν m hB]
    exact measure_ne_top ν B
  · intro s hs hanti hempty
    obtain ⟨n, hn⟩ : ∃ n, s n = ∅ := by
      by_contra hne
      push Not at hne
      have h := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed s
        (fun i => hanti (Nat.le_succ i)) hne
        (isClopen_of_mem_clopenFutureSets (hs 0)).isClosed.isCompact
        fun i => (isClopen_of_mem_clopenFutureSets (hs i)).isClosed
      rw [hempty] at h
      exact not_nonempty_empty h
    refine tendsto_atTop_of_eventually_const (i₀ := n) fun i hi => ?_
    have hi' : s i = ∅ := subset_empty_iff.1 (hn ▸ hanti hi)
    rw [hi', addContent_empty]

end Clopen

section Extension

variable {ι : Type*} [Finite ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem exists_isFiniteMeasure_map_eta_eq {ν : Measure (ℕ → ι)} [IsFiniteMeasure ν]
    (hν : MeasurePreserving shiftPlus ν ν) :
    ∃ μ : Measure (ℤ → ι), IsFiniteMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
      μ.map eta = ν := by
  let : TopologicalSpace ι := ⊥
  have : DiscreteTopology ι := ⟨rfl⟩
  have hC := (isSetAlgebra_clopenFutureSets (α := ι)).isSetRing
  set μ : Measure (ℤ → ι) := (futureContent hν).measure hC.isSetSemiring
    generateFrom_clopenFutureSets.ge (isSigmaSubadditive_futureContent hν) with hμdef
  have hμ : ∀ (m : ℕ) {B : Set (ℕ → ι)}, IsClopen B → μ (etaFrom m ⁻¹' B) = ν B := by
    intro m B hB
    rw [hμdef, AddContent.measure_eq _ _ generateFrom_clopenFutureSets.symm _ ⟨m, B, hB, rfl⟩,
      futureContent_apply hν m hB]
  have huniv : μ univ = ν univ := by
    simpa using hμ 0 isClopen_univ
  have : IsFiniteMeasure μ := ⟨by rw [huniv]; exact measure_lt_top ν univ⟩
  refine ⟨μ, inferInstance, ⟨measurable_shift 1, ?_⟩, ?_⟩
  · refine ext_of_generate_finite (clopenFutureSets ι) generateFrom_clopenFutureSets.symm
      (fun s hs t ht _ => isSetAlgebra_clopenFutureSets.inter_mem hs ht) ?_ ?_
    · rintro _ ⟨m, B, hB, rfl⟩
      have hpre : shift 1 ⁻¹' (etaFrom m ⁻¹' B) = etaFrom m ⁻¹' (shiftPlus ⁻¹' B) := by
        ext x
        simp only [mem_preimage, etaFrom_shift_one]
      rw [Measure.map_apply (measurable_shift 1) (measurable_etaFrom m hB.isOpen.measurableSet),
        hpre, hμ m (hB.preimage continuous_shiftPlus), hμ m hB,
        hν.measure_preimage hB.isOpen.measurableSet.nullMeasurableSet]
    · rw [Measure.map_apply (measurable_shift 1) MeasurableSet.univ, preimage_univ]
  · refine ext_of_generate_finite {B : Set (ℕ → ι) | IsClopen B}
      generateFrom_isClopen_oneSided.symm (fun s hs t ht _ => IsClopen.inter hs ht) ?_ ?_
    · intro B hB
      have hB' : IsClopen B := hB
      rw [Measure.map_apply measurable_eta hB'.isOpen.measurableSet, ← etaFrom_zero, hμ 0 hB']
    · rw [Measure.map_apply measurable_eta MeasurableSet.univ, preimage_univ, huniv]

theorem exists_map_eta_eq {ν : Measure (ℕ → ι)} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving shiftPlus ν ν) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ MeasurePreserving (shift 1) μ μ ∧
      μ.map eta = ν := by
  obtain ⟨μ, -, hinv, hmap⟩ := exists_isFiniteMeasure_map_eta_eq hν
  refine ⟨μ, ⟨?_⟩, hinv, hmap⟩
  rw [← preimage_univ (f := eta), ← Measure.map_apply measurable_eta MeasurableSet.univ, hmap,
    measure_univ]

end Extension

end FractalGeometry
