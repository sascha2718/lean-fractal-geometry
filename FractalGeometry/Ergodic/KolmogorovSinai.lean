module

public import Mathlib
public import FractalGeometry.Symbolic.Entropy
public import FractalGeometry.Symbolic.Shift
public import FractalGeometry.Symbolic.PastEntropy
public import FractalGeometry.Ergodic.ShannonMcMillanBreiman
public import FractalGeometry.Symbolic.ShiftMeasure

/-!
Kolmogorov–Sinai entropy and the generator identity for a finite-alphabet
 two-sided shift. General finite-partition conditional entropy and approximation
lemmas support the proof. The canonical coordinate partition is a generator.
Reference framework: Rufus Bowen, Equilibrium states and the ergodic theory of
Anosov diffeomorphisms, LNM 470, Springer (1975), Chapter 2,
doi:10.1007/BFb0081279.
-/

@[expose] public section

namespace FractalGeometry

open MeasureTheory ProbabilityTheory Filter Topology Set

section PartEntropy

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  {β γ δ : Type*} [Fintype β] [Fintype γ] [Fintype δ]

noncomputable def partEntropy (f : Ω → β) : ℝ :=
  ∑ b, Real.negMulLog (μ.real (f ⁻¹' {b}))

noncomputable def condPartEntropy (f : Ω → β) (g : Ω → γ) : ℝ :=
  partEntropy μ (fun x => (f x, g x)) - partEntropy μ g

def partJoin (T : Ω → Ω) (f : Ω → β) (n : ℕ) (x : Ω) : Fin n → β :=
  fun i => f (T^[i] x)

noncomputable def partEntropyRate (T : Ω → Ω) (f : Ω → β) : ℝ :=
  limUnder atTop fun n : ℕ => partEntropy μ (partJoin T f n) / n

noncomputable def ksEntropy (T : Ω → Ω) : ℝ :=
  sSup {r | ∃ (m : ℕ) (Q : Ω → Fin m), Measurable Q ∧ partEntropyRate μ T Q = r}

variable {μ}

theorem partEntropy_comp_injective {φ : β → γ} (hφ : Function.Injective φ) (f : Ω → β) :
    partEntropy μ (φ ∘ f) = partEntropy μ f := by
  symm
  refine Fintype.sum_of_injective φ hφ _ _ (fun c hc => ?_) (fun b => ?_)
  · have : (φ ∘ f) ⁻¹' {c} = ∅ := by
      ext x
      simp only [mem_preimage, Function.comp_apply, mem_singleton_iff, mem_empty_iff_false,
        iff_false]
      exact fun h => hc ⟨f x, h⟩
    rw [this, measureReal_empty, Real.negMulLog_zero]
  · have : (φ ∘ f) ⁻¹' {φ b} = f ⁻¹' {b} := by
      ext x
      simp [hφ.eq_iff]
    rw [this]

theorem partEntropy_eq_of_comp {φ : γ → β} (hφ : Function.Injective φ) {f : Ω → β}
    {g : Ω → γ} (h : f = φ ∘ g) : partEntropy μ f = partEntropy μ g := by
  rw [h, partEntropy_comp_injective hφ]

theorem partEntropy_comp_measurePreserving {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    [MeasurableSpace β] [MeasurableSingletonClass β] {f : Ω → β} (hf : Measurable f) :
    partEntropy μ (f ∘ T) = partEntropy μ f := by
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Set.preimage_comp, hT.measureReal_preimage (hf (measurableSet_singleton b)).nullMeasurableSet]

theorem partEntropy_nonneg [IsProbabilityMeasure μ] (f : Ω → β) : 0 ≤ partEntropy μ f :=
  Finset.sum_nonneg fun _ _ => Real.negMulLog_nonneg measureReal_nonneg measureReal_le_one

theorem partEntropy_of_subsingleton [IsProbabilityMeasure μ] [Subsingleton β] (f : Ω → β) :
    partEntropy μ f = 0 := by
  rcases isEmpty_or_nonempty β with hβ | hβ
  · simp [partEntropy]
  · obtain ⟨b⟩ := hβ
    have : Unique β := uniqueOfSubsingleton b
    have hpre : f ⁻¹' {default} = univ := by
      ext x
      simp [Subsingleton.elim (f x) default]
    rw [partEntropy, Fintype.sum_unique, hpre, probReal_univ, Real.negMulLog_one]

omit [MeasurableSpace Ω] [Fintype β] [Fintype γ] in

theorem preimage_pair_singleton (f : Ω → β) (g : Ω → γ) (b : β) (c : γ) :
    (fun x => (f x, g x)) ⁻¹' {(b, c)} = f ⁻¹' {b} ∩ g ⁻¹' {c} := by
  ext x
  simp [Prod.ext_iff]

end PartEntropy

theorem comap_comp_le {Ω γ δ : Type*} [MeasurableSpace γ] [MeasurableSpace δ] {g : Ω → γ}
    (φ : γ → δ) (hφ : Measurable φ) :
    MeasurableSpace.comap (φ ∘ g) (inferInstance : MeasurableSpace δ) ≤
      MeasurableSpace.comap g inferInstance := by
  rw [← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hφ.comap_le

section CondEntropy

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {β γ δ : Type*} [Fintype β] [Fintype γ] [Fintype δ]
  [MeasurableSpace β] [MeasurableSingletonClass β] [MeasurableSpace γ]
  [MeasurableSingletonClass γ] [MeasurableSpace δ] [MeasurableSingletonClass δ]

theorem condPartEntropy_eq_integral [IsFiniteMeasure μ] {f : Ω → β} {g : Ω → γ}
    (hf : Measurable f) (hg : Measurable g) :
    condPartEntropy μ f g =
      ∫ x, ∑ b, Real.negMulLog ((μ⟦f ⁻¹' {b} | MeasurableSpace.comap g inferInstance⟧) x) ∂μ := by
  rw [integral_sum_negMulLog_condExp_comap hf hg, condPartEntropy, partEntropy, partEntropy,
    Fintype.sum_prod_type, Finset.sum_comm]
  simp only [preimage_pair_singleton]

theorem condPartEntropy_nonneg [IsFiniteMeasure μ] {f : Ω → β} {g : Ω → γ}
    (hf : Measurable f) (hg : Measurable g) : 0 ≤ condPartEntropy μ f g := by
  rw [condPartEntropy_eq_integral hf hg]
  have h : ∀ᵐ x ∂μ, ∀ b, (μ⟦f ⁻¹' {b} | MeasurableSpace.comap g inferInstance⟧) x ∈
      Icc (0 : ℝ) 1 :=
    ae_all_iff.2 fun b => condExp_indicator_mem_Icc hg.comap_le (hf (measurableSet_singleton b))
  exact integral_nonneg_of_ae (h.mono fun x hx =>
    Finset.sum_nonneg fun b _ => (negMulLog_mem_Icc (hx b)).1)

omit [Fintype β] [Fintype γ] [Fintype δ] [MeasurableSpace β] [MeasurableSingletonClass β]
  [MeasurableSpace γ] [MeasurableSingletonClass γ] [MeasurableSpace δ]
  [MeasurableSingletonClass δ] [MeasurableSpace Ω] in

theorem integrable_negMulLog_condExp {m m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hm : m ≤ m0) {A : Set Ω} (hA : MeasurableSet A) :
    Integrable (fun x => Real.negMulLog ((μ⟦A | m⟧) x)) μ :=
  Integrable.of_bound (Real.continuous_negMulLog.comp_aestronglyMeasurable
    (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable) 1
    ((condExp_indicator_mem_Icc hm hA).mono fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (negMulLog_mem_Icc hx).1]
      exact (negMulLog_mem_Icc hx).2)

omit [Fintype β] [Fintype γ] [Fintype δ] [MeasurableSpace β] [MeasurableSingletonClass β]
  [MeasurableSpace γ] [MeasurableSingletonClass γ] [MeasurableSpace δ]
  [MeasurableSingletonClass δ] [MeasurableSpace Ω] in

theorem integral_negMulLog_condExp_le {m₁ m₂ m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ m0) {A : Set Ω} (hA : MeasurableSet A) :
    ∫ x, Real.negMulLog ((μ⟦A | m₂⟧) x) ∂μ ≤ ∫ x, Real.negMulLog ((μ⟦A | m₁⟧) x) ∂μ := by
  have h₁ : m₁ ≤ m0 := h₁₂.trans h₂
  have hη : ∀ {m : MeasurableSpace Ω}, m ≤ m0 →
      Integrable (fun x => Real.negMulLog ((μ⟦A | m⟧) x)) μ := fun hm =>
    integrable_negMulLog_condExp hm hA
  have hconc : ConcaveOn ℝ (Icc (0 : ℝ) 1) Real.negMulLog :=
    Real.concaveOn_negMulLog.subset Icc_subset_Ici_self (convex_Icc 0 1)
  have hJ := hconc.condExp_map_le h₁ Real.continuous_negMulLog.continuousOn.upperSemicontinuousOn
    (condExp_indicator_mem_Icc h₂ hA) isClosed_Icc integrable_condExp (hη h₂)
  have htower : μ[μ⟦A | m₂⟧ | m₁] =ᵐ[μ] μ⟦A | m₁⟧ := condExp_condExp_of_le h₁₂ h₂
  calc ∫ x, Real.negMulLog ((μ⟦A | m₂⟧) x) ∂μ
      = ∫ x, (μ[Real.negMulLog ∘ μ⟦A | m₂⟧ | m₁]) x ∂μ := (integral_condExp h₁).symm
    _ ≤ ∫ x, Real.negMulLog ((μ[μ⟦A | m₂⟧ | m₁]) x) ∂μ :=
        integral_mono_ae integrable_condExp
          ((hη h₁).congr (htower.mono fun x hx => by simp only [hx])) hJ
    _ = ∫ x, Real.negMulLog ((μ⟦A | m₁⟧) x) ∂μ :=
        integral_congr_ae (htower.mono fun x hx => by simp only [hx])

theorem condPartEntropy_le_of_comap_le [IsFiniteMeasure μ] {f : Ω → β} {g : Ω → γ}
    {g' : Ω → δ} (hf : Measurable f) (hg : Measurable g) (hg' : Measurable g')
    (hle : MeasurableSpace.comap g' inferInstance ≤ MeasurableSpace.comap g inferInstance) :
    condPartEntropy μ f g ≤ condPartEntropy μ f g' := by
  rw [condPartEntropy_eq_integral hf hg, condPartEntropy_eq_integral hf hg',
    integral_finsetSum _ fun b _ =>
      integrable_negMulLog_condExp hg.comap_le (hf (measurableSet_singleton b)),
    integral_finsetSum _ fun b _ =>
      integrable_negMulLog_condExp hg'.comap_le (hf (measurableSet_singleton b))]
  exact Finset.sum_le_sum fun b _ =>
    integral_negMulLog_condExp_le hle hg.comap_le (hf (measurableSet_singleton b))

theorem condPartEntropy_le_comp [IsFiniteMeasure μ] {f : Ω → β} {g : Ω → γ}
    (hf : Measurable f) (hg : Measurable g) (φ : γ → δ) :
    condPartEntropy μ f g ≤ condPartEntropy μ f (φ ∘ g) :=
  condPartEntropy_le_of_comap_le hf hg ((measurable_of_countable φ).comp hg)
    (comap_comp_le φ (measurable_of_countable φ))

omit [MeasurableSpace β] [MeasurableSingletonClass β] [MeasurableSpace γ]
  [MeasurableSingletonClass γ] [MeasurableSpace δ] [MeasurableSingletonClass δ] in

theorem condPartEntropy_comp_injective {φ : β → δ} (hφ : Function.Injective φ) (f : Ω → β)
    (g : Ω → γ) : condPartEntropy μ (φ ∘ f) g = condPartEntropy μ f g := by
  have hinj : Function.Injective (Prod.map φ (id : γ → γ)) := fun p q h => by
    simp only [Prod.map, Prod.mk.injEq, id] at h
    exact Prod.ext (hφ h.1) h.2
  have h : partEntropy μ (fun x => ((φ ∘ f) x, g x)) = partEntropy μ (fun x => (f x, g x)) :=
    partEntropy_eq_of_comp (φ := Prod.map φ id) hinj rfl
  rw [condPartEntropy, condPartEntropy, h]

omit [MeasurableSpace β] [MeasurableSingletonClass β] [MeasurableSpace γ]
  [MeasurableSingletonClass γ] [MeasurableSpace δ] [MeasurableSingletonClass δ] in

theorem condPartEntropy_pair (f : Ω → β) (f' : Ω → δ) (g : Ω → γ) :
    condPartEntropy μ (fun x => (f x, f' x)) g =
      condPartEntropy μ f g + condPartEntropy μ f' fun x => (f x, g x) := by
  have h : partEntropy μ (fun x => (f' x, (f x, g x))) =
      partEntropy μ (fun x => ((f x, f' x), g x)) :=
    partEntropy_eq_of_comp (φ := fun p : (β × δ) × γ => (p.1.2, (p.1.1, p.2)))
      (fun p q hpq => by
        simp only [Prod.mk.injEq] at hpq
        exact Prod.ext (Prod.ext hpq.2.1 hpq.1) hpq.2.2) rfl
  rw [condPartEntropy, condPartEntropy, condPartEntropy, h]
  ring

theorem condPartEntropy_pair_le [IsFiniteMeasure μ] {f : Ω → β} {f' : Ω → δ} {g : Ω → γ}
    (hf : Measurable f) (hf' : Measurable f') (hg : Measurable g) :
    condPartEntropy μ (fun x => (f x, f' x)) g ≤
      condPartEntropy μ f g + condPartEntropy μ f' g := by
  rw [condPartEntropy_pair]
  have h := condPartEntropy_le_comp (μ := μ) hf' (hf.prodMk hg) Prod.snd
  have e : (Prod.snd ∘ fun x => (f x, g x)) = g := rfl
  rw [e] at h
  linarith

omit [MeasurableSpace β] [MeasurableSingletonClass β] in

theorem condPartEntropy_unit [IsProbabilityMeasure μ] (f : Ω → β) :
    condPartEntropy μ f (fun _ => ()) = partEntropy μ f := by
  rw [condPartEntropy, partEntropy_of_subsingleton (fun _ : Ω => ()), sub_zero]
  exact partEntropy_eq_of_comp (φ := fun b => (b, ())) (fun b b' h => (Prod.mk.inj h).1) rfl

theorem condPartEntropy_le_partEntropy [IsProbabilityMeasure μ] {f : Ω → β} {g : Ω → γ}
    (hf : Measurable f) (hg : Measurable g) : condPartEntropy μ f g ≤ partEntropy μ f := by
  rw [← condPartEntropy_unit f]
  exact condPartEntropy_le_comp hf hg fun _ => ()

theorem partEntropy_le_pair [IsFiniteMeasure μ] {f : Ω → β} {g : Ω → γ} (hf : Measurable f)
    (hg : Measurable g) : partEntropy μ g ≤ partEntropy μ fun x => (f x, g x) := by
  have := condPartEntropy_nonneg (μ := μ) hf hg
  rw [condPartEntropy] at this
  linarith

theorem partEntropy_comp_le [IsFiniteMeasure μ] {g : Ω → γ} (hg : Measurable g) (φ : γ → δ) :
    partEntropy μ (φ ∘ g) ≤ partEntropy μ g := by
  have h := partEntropy_le_pair (μ := μ) hg ((measurable_of_countable φ).comp hg)
  have e : partEntropy μ (fun x => (g x, (φ ∘ g) x)) = partEntropy μ g :=
    partEntropy_eq_of_comp (φ := fun c => (c, φ c)) (fun c c' h => (Prod.mk.inj h).1) rfl
  rw [e] at h
  exact h

theorem condPartEntropy_comp_measurePreserving {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → β} {g : Ω → γ} (hf : Measurable f) (hg : Measurable g) :
    condPartEntropy μ (f ∘ T) (g ∘ T) = condPartEntropy μ f g := by
  rw [condPartEntropy, condPartEntropy, partEntropy_comp_measurePreserving hT hg]
  have : (fun x => ((f ∘ T) x, (g ∘ T) x)) = (fun x => (f x, g x)) ∘ T := rfl
  rw [this, partEntropy_comp_measurePreserving hT (hf.prodMk hg)]

end CondEntropy

section Join

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}
  {β γ : Type*} [Fintype β] [Fintype γ] [MeasurableSpace β] [MeasurableSingletonClass β]
  [MeasurableSpace γ] [MeasurableSingletonClass γ]

omit [MeasurableSpace Ω] [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ] in

theorem partJoin_add (f : Ω → β) (m n : ℕ) :
    partJoin T f (m + n) = (Fin.appendEquiv m n) ∘ fun x =>
      (partJoin T f m x, partJoin T f n (T^[m] x)) := by
  funext x i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [partJoin]
  · simp only [partJoin, Function.comp_apply, Fin.appendEquiv_apply, Fin.append_right,
      Fin.val_natAdd]
    rw [← Function.iterate_add_apply, add_comm]

omit [Fintype β] [MeasurableSingletonClass β] [Fintype γ] [MeasurableSpace γ]
  [MeasurableSingletonClass γ] in

theorem measurable_partJoin (hT : Measurable T) {f : Ω → β} (hf : Measurable f) (n : ℕ) :
    Measurable (partJoin T f n) :=
  Measurable.of_eval fun i => hf.comp (hT.iterate i)

theorem partEntropy_partJoin_add_le [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : Ω → β} (hf : Measurable f) (m n : ℕ) :
    partEntropy μ (partJoin T f (m + n)) ≤
      partEntropy μ (partJoin T f m) + partEntropy μ (partJoin T f n) := by
  have hm := measurable_partJoin hT.measurable hf m
  have hn : Measurable fun x => partJoin T f n (T^[m] x) :=
    (measurable_partJoin hT.measurable hf n).comp (hT.measurable.iterate m)
  rw [partJoin_add, partEntropy_comp_injective (Fin.appendEquiv m n).injective]
  have h := condPartEntropy_le_partEntropy (μ := μ) hm hn
  have hinv : partEntropy μ (fun x => partJoin T f n (T^[m] x)) =
      partEntropy μ (partJoin T f n) :=
    partEntropy_comp_measurePreserving (hT.iterate m) (measurable_partJoin hT.measurable hf n)
  rw [condPartEntropy] at h
  linarith

theorem tendsto_partEntropyRate [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : Ω → β} (hf : Measurable f) :
    Tendsto (fun n : ℕ => partEntropy μ (partJoin T f n) / n) atTop
      (𝓝 (partEntropyRate μ T f)) := by
  have hsub : Subadditive fun n => partEntropy μ (partJoin T f n) := fun m n =>
    partEntropy_partJoin_add_le hT hf m n
  have hbdd : BddBelow (range fun n : ℕ => partEntropy μ (partJoin T f n) / n) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact div_nonneg (partEntropy_nonneg _) (Nat.cast_nonneg n)⟩
  have h := hsub.tendsto_lim hbdd
  rw [partEntropyRate, h.limUnder_eq]
  exact h

theorem condPartEntropy_partJoin_le [IsProbabilityMeasure μ] (hT : Measurable T) {f : Ω → β}
    (hf : Measurable f) {g : Ω → γ} (hg : Measurable g) (n : ℕ) :
    condPartEntropy μ (partJoin T f n) g ≤
      ∑ i ∈ Finset.range n, condPartEntropy μ (f ∘ T^[i]) g := by
  induction n with
  | zero =>
    rw [Finset.sum_range_zero]
    exact (condPartEntropy_le_partEntropy (measurable_partJoin hT hf 0) hg).trans_eq
      (partEntropy_of_subsingleton _)
  | succ n ih =>
    rw [partJoin_add, condPartEntropy_comp_injective (Fin.appendEquiv n 1).injective,
      Finset.sum_range_succ]
    have h1 : partJoin T f 1 ∘ T^[n] = (fun b (_ : Fin 1) => b) ∘ (f ∘ T^[n]) := by
      funext x i
      simp [partJoin]
    refine (condPartEntropy_pair_le (measurable_partJoin hT hf n)
      ((measurable_partJoin hT hf 1).comp (hT.iterate n)) hg).trans ?_
    rw [h1, condPartEntropy_comp_injective (fun b b' h => congrFun h 0)]
    exact add_le_add_left ih _

end Join

section Generator

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

def twoSidedBlock (k : ℕ) (x : ℤ → α) : Fin (2 * k + 1) → α :=
  fun j => x ((j : ℤ) - k)

omit [Fintype α] [MeasurableSingletonClass α] in

theorem measurable_twoSidedBlock (k : ℕ) : Measurable (twoSidedBlock k : (ℤ → α) → _) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in

theorem twoSidedBlock_eq_comp_succ (k : ℕ) :
    (twoSidedBlock k : (ℤ → α) → _) =
      (fun w (j : Fin (2 * k + 1)) => w ⟨j + 1, by omega⟩) ∘ twoSidedBlock (k + 1) := by
  funext x j
  simp only [twoSidedBlock, Function.comp_apply]
  congr 1
  push_cast
  ring

def twoSidedFiltration (α : Type*) [MeasurableSpace α] :
    Filtration ℕ (inferInstance : MeasurableSpace (ℤ → α)) where
  seq k := MeasurableSpace.comap (twoSidedBlock k) inferInstance
  mono' := monotone_nat_of_le_succ fun k => by
    rw [twoSidedBlock_eq_comp_succ k, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono
      (Measurable.comap_le (Measurable.of_eval fun _ => measurable_pi_apply _))
  le' k := (measurable_twoSidedBlock k).comap_le

omit [Fintype α] [MeasurableSingletonClass α] in

theorem iSup_twoSidedFiltration :
    ⨆ k, twoSidedFiltration α k = (inferInstance : MeasurableSpace (ℤ → α)) := by
  refine le_antisymm (iSup_le fun k => (twoSidedFiltration α).le k) ?_
  change MeasurableSpace.pi ≤ _
  refine iSup_le fun j => le_trans ?_ (le_iSup _ j.natAbs)
  change _ ≤ MeasurableSpace.comap (twoSidedBlock j.natAbs) _
  have hlt : (j + j.natAbs).toNat < 2 * j.natAbs + 1 := by omega
  have e : (fun x : ℤ → α => x j) =
      (fun w : Fin (2 * j.natAbs + 1) → α => w ⟨(j + j.natAbs).toNat, hlt⟩) ∘
        twoSidedBlock j.natAbs := by
    funext x
    simp only [Function.comp_apply, twoSidedBlock]
    congr 1
    omega
  rw [e, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (Measurable.comap_le (measurable_pi_apply _))

theorem tendsto_condPartEntropy_twoSidedBlock {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    {f : (ℤ → α) → β} (hf : Measurable f) :
    Tendsto (fun k => condPartEntropy μ f (twoSidedBlock k)) atTop (𝓝 0) := by
  have hA : ∀ b, MeasurableSet (f ⁻¹' {b}) := fun b => hf (measurableSet_singleton b)
  have h := tendsto_integral_sum_negMulLog_condExp (μ := μ) (twoSidedFiltration α) hA
  rw [iSup_twoSidedFiltration] at h
  have hlim : ∫ x, ∑ b, Real.negMulLog ((μ⟦f ⁻¹' {b} |
      (inferInstance : MeasurableSpace (ℤ → α))⟧) x) ∂μ = 0 := by
    refine integral_eq_zero_of_ae (ae_of_all _ fun x => Finset.sum_eq_zero fun b _ => ?_)
    rw [condExp_of_stronglyMeasurable le_rfl
      ((measurable_const.indicator (hA b)).stronglyMeasurable)
      ((integrable_const (1 : ℝ)).indicator (hA b))]
    by_cases hx : x ∈ f ⁻¹' {b}
    · simp [hx]
    · simp [hx]
  rw [hlim] at h
  refine h.congr fun k => ?_
  rw [condPartEntropy_eq_integral hf (measurable_twoSidedBlock k)]
  rfl

variable {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]

theorem partEntropy_partJoin_twoSidedBlock_le (hinv : MeasurePreserving (shift 1) μ μ)
    (k n : ℕ) : partEntropy μ (partJoin (shift 1) (twoSidedBlock k) n) ≤
      blockEntropy μ (n + 2 * k) := by
  have e : partJoin (shift 1) (twoSidedBlock k) n =
      (fun (w : Fin (n + 2 * k) → α) (i : Fin n) (j : Fin (2 * k + 1)) =>
        w ⟨i + j, by omega⟩) ∘ (block (n + 2 * k) ∘ shift (-(k : ℤ))) := by
    funext x i j
    simp only [partJoin, iterate_shift_one, twoSidedBlock, Function.comp_apply, block,
      shift_apply]
    congr 1
    push_cast
    ring
  rw [e]
  refine (partEntropy_comp_le ((measurable_block _).comp (measurable_shift _)) _).trans_eq ?_
  rw [partEntropy_comp_measurePreserving (measurePreserving_shift_neg_natCast hinv k)
    (measurable_block _)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [cylinder_eq_preimage]

theorem partEntropy_partJoin_le (hinv : MeasurePreserving (shift 1) μ μ) {β : Type*}
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] {f : (ℤ → α) → β}
    (hf : Measurable f) (k n : ℕ) :
    partEntropy μ (partJoin (shift 1) f n) ≤
      blockEntropy μ (n + 2 * k) + n * condPartEntropy μ f (twoSidedBlock k) := by
  have hT := hinv.measurable
  have hR := measurable_twoSidedBlock (α := α) k
  have hJf := measurable_partJoin hT hf n
  have hJR := measurable_partJoin hT hR n
  have h1 : partEntropy μ (partJoin (shift 1) f n) ≤ partEntropy μ (fun x =>
      (partJoin (shift 1) f n x, partJoin (shift 1) (twoSidedBlock k) n x)) := by
    have e : partEntropy μ (fun x =>
        (partJoin (shift 1) f n x, partJoin (shift 1) (twoSidedBlock k) n x)) =
        partEntropy μ (fun x =>
          (partJoin (shift 1) (twoSidedBlock k) n x, partJoin (shift 1) f n x)) :=
      partEntropy_eq_of_comp (φ := Prod.swap) Prod.swap_injective rfl
    rw [e]
    exact partEntropy_le_pair hJR hJf
  have h2 : partEntropy μ (fun x => (partJoin (shift 1) f n x,
      partJoin (shift 1) (twoSidedBlock k) n x)) =
      partEntropy μ (partJoin (shift 1) (twoSidedBlock k) n) +
        condPartEntropy μ (partJoin (shift 1) f n) (partJoin (shift 1) (twoSidedBlock k) n) := by
    rw [condPartEntropy]
    ring

  have h5 : condPartEntropy μ (partJoin (shift 1) f n) (partJoin (shift 1) (twoSidedBlock k) n) ≤
      n * condPartEntropy μ f (twoSidedBlock k) := by
    refine (condPartEntropy_partJoin_le hT hf hJR n).trans ?_
    have hterm : ∀ i ∈ Finset.range n,
        condPartEntropy μ (f ∘ (shift 1)^[i]) (partJoin (shift 1) (twoSidedBlock k) n) ≤
          condPartEntropy μ f (twoSidedBlock k) := fun i hi => by
      have hi' : i < n := Finset.mem_range.1 hi
      have e : twoSidedBlock k ∘ (shift 1)^[i] =
          (fun w : Fin n → Fin (2 * k + 1) → α => w ⟨i, hi'⟩) ∘
            partJoin (shift 1) (twoSidedBlock k) n := rfl
      refine (condPartEntropy_le_comp (hf.comp (hT.iterate i)) hJR
        (fun w : Fin n → Fin (2 * k + 1) → α => w ⟨i, hi'⟩)).trans_eq ?_
      rw [← e, condPartEntropy_comp_measurePreserving (hinv.iterate i) hf hR]
    refine (Finset.sum_le_sum hterm).trans_eq ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h6 := partEntropy_partJoin_twoSidedBlock_le hinv k n
  linarith

theorem partEntropyRate_le_entropy (hinv : MeasurePreserving (shift 1) μ μ) {β : Type*}
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] {f : (ℤ → α) → β}
    (hf : Measurable f) : partEntropyRate μ (shift 1) f ≤ entropy μ := by
  have hrate := tendsto_partEntropyRate hinv hf
  have hk : ∀ k : ℕ, partEntropyRate μ (shift 1) f ≤
      entropy μ + condPartEntropy μ f (twoSidedBlock k) := fun k => by

    have hb : Tendsto (fun n : ℕ => blockEntropy μ (n + 2 * k) / n) atTop (𝓝 (entropy μ)) := by
      have h1 := (tendsto_entropy hinv).comp (tendsto_add_atTop_nat (2 * k))
      have h2 : Tendsto (fun n : ℕ => ((n + 2 * k : ℕ) : ℝ) / n) atTop (𝓝 1) := by
        have : Tendsto (fun n : ℕ => 1 + (2 * k : ℝ) / n) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat _)
        rw [add_zero] at this
        refine this.congr' ((eventually_gt_atTop 0).mono fun n hn => ?_)
        have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
        push_cast
        field_simp
      have h3 := h1.mul h2
      rw [mul_one] at h3
      refine h3.congr' ((eventually_gt_atTop 0).mono fun n hn => ?_)
      have hn' : ((n + 2 * k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      simp only [Function.comp_apply]
      field_simp
    have hbound : ∀ᶠ n : ℕ in atTop, partEntropy μ (partJoin (shift 1) f n) / n ≤
        blockEntropy μ (n + 2 * k) / n + condPartEntropy μ f (twoSidedBlock k) :=
      (eventually_gt_atTop 0).mono fun n hn => by
        have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
        rw [div_add' _ _ _ hn'.ne', div_le_div_iff_of_pos_right hn']
        linarith [partEntropy_partJoin_le hinv hf k n]
    exact le_of_tendsto_of_tendsto hrate (hb.add_const _) hbound
  have hlim := (tendsto_condPartEntropy_twoSidedBlock (μ := μ) hf).const_add (entropy μ)
  rw [add_zero] at hlim
  exact ge_of_tendsto hlim (Eventually.of_forall hk)

omit [MeasurableSingletonClass α] [IsProbabilityMeasure μ] in

theorem partEntropyRate_coord_zero :
    partEntropyRate μ (shift 1) (fun x : ℤ → α => x 0) = entropy μ := by
  have e : ∀ n, partEntropy μ (partJoin (shift 1) (fun x : ℤ → α => x 0) n) =
      blockEntropy μ n := fun n => by
    have hj : partJoin (shift 1) (fun x : ℤ → α => x 0) n = block n := by
      funext x i
      simp [partJoin, iterate_shift_one, block]
    rw [hj]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [cylinder_eq_preimage]
  simp only [partEntropyRate, entropy, e]

theorem isGreatest_partEntropyRate (hinv : MeasurePreserving (shift 1) μ μ) :
    IsGreatest {r | ∃ (m : ℕ) (Q : (ℤ → α) → Fin m), Measurable Q ∧
      partEntropyRate μ (shift 1) Q = r} (entropy μ) := by
  refine ⟨⟨Fintype.card α, (Fintype.equivFin α) ∘ fun x => x 0,
    (measurable_of_countable _).comp (measurable_pi_apply 0), ?_⟩, ?_⟩
  · have e : ∀ n, partEntropy μ (partJoin (shift 1) ((Fintype.equivFin α) ∘ fun x => x 0) n) =
        partEntropy μ (partJoin (shift 1) (fun x : ℤ → α => x 0) n) := fun n =>
      partEntropy_eq_of_comp (φ := fun w => (Fintype.equivFin α) ∘ w)
        (fun w w' h => funext fun i => (Fintype.equivFin α).injective (congrFun h i)) rfl
    rw [← partEntropyRate_coord_zero]
    simp only [partEntropyRate, e]
  · rintro _ ⟨m, Q, hQ, rfl⟩
    exact partEntropyRate_le_entropy hinv hQ

theorem ksEntropy_shift_eq_entropy (hinv : MeasurePreserving (shift 1) μ μ) :
    ksEntropy μ (shift 1) = entropy μ :=
  (isGreatest_partEntropyRate hinv).csSup_eq

theorem tendsto_neg_log_cylinder_ksEntropy (herg : Ergodic (shift 1) μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => -Real.log (μ.real (cylinder (block n x))) / n) atTop
      (𝓝 (ksEntropy μ (shift 1))) := by
  rw [ksEntropy_shift_eq_entropy herg.toMeasurePreserving]
  exact tendsto_neg_log_cylinder_entropy herg

end Generator

end FractalGeometry
