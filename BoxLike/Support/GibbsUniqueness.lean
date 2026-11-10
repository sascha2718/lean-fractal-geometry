module

/-
Uniqueness of the ergodic Gibbs measure of a potential of bounded distortion, in particular of a
Hölder potential, on `Σ_Z` (`sec:gibbs_measures`, tex lines 2382 to 2384: "for each Hölder
continuous potential `f` there exists a unique ergodic Gibbs measure"). Uniqueness is proved
here; existence is Bowen's theorem, which the article cites and which the library proves in
`BoxLike/Bowen/Main.lean` (`bowenGibbsExistence`).

Two Gibbs measures for the same potential have the same constant `P` (both are
`lim_n n⁻¹ log ∑_{|w| = n} exp(sup_{[w]} S_n f)`), so their values on cylinders are comparable,
`ν'([w]) ≤ C C' ν([w])`. By invariance the comparison holds on the sets determined by the
coordinates `|k| ≤ m`, which form an algebra generating the Borel `σ`-algebra, and by measure
density on every Borel set. Hence `ν' ≪ ν`, and an invariant measure absolutely continuous with
respect to an ergodic one equals it.

* `window`, `windowSets`, `isSetAlgebra_windowSets`, `generateFrom_windowSets`: the algebra of
  the sets `{𝐢 : (i_{-m}, …, i_m) ∈ F}`.
* `measure_window_preimage`: an invariant measure gives such a set the sum of the measures of
  the cylinders `[w]`, `w ∈ F`.
* `le_of_cylinder_le`: `ν'(A) ≤ K ν(A)` for every Borel set `A` when it holds on the cylinders
  `[w]` and both measures are invariant.
* `IsGibbsPotential.pressure_eq_pressure`, `IsGibbsPotential.measure_cylinder_le`: two Gibbs
  measures for the same potential have the same constant, and comparable cylinder values.
* `IsGibbsPotential.eq_of_ergodic`, `IsGibbsPotential.eq_of_ergodic_of_isHolder`: an invariant
  Gibbs probability measure equals every ergodic Gibbs probability measure for the same
  potential; so the ergodic Gibbs measure is unique.
* `IsGibbs.eq_of_ergodic`, `System.GibbsDecomposition.eq_mu₁`,
  `System.GibbsDecomposition.eq_mu₂`: the same for the one-symbol potentials of the library; the
  `s`-Gibbs measures `μ_1`, `μ_2` are the only invariant Gibbs measures for `f_{1,s}`, `f_{2,s}`.
-/
public import BoxLike.Support.HolderPressure
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Dynamics.Ergodic.Extreme

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set
open scoped ENNReal symmDiff

/-! ### The algebra of sets determined by finitely many coordinates -/

section Window

variable {α : Type*}

/-- The window `(i_{-m}, …, i_m)` of a two-sided sequence, indexed by `Fin (2m + 1)`. -/
def window (m : ℕ) (x : ℤ → α) : Fin (2 * m + 1) → α := fun k => x ((k : ℤ) - m)

/-- The window of `𝐢` is the block of length `2m + 1` of `σ^{-m}(𝐢)`. -/
theorem window_eq_block_shift (m : ℕ) (x : ℤ → α) :
    window m x = block (2 * m + 1) (shift (-(m : ℤ)) x) := by
  funext k
  simp only [window, block_apply, shift_apply]
  congr 1
  ring

/-- The restriction of a window of radius `M` to the window of radius `m ≤ M`. -/
def restrictWindow {M m : ℕ} (h : m ≤ M) (v : Fin (2 * M + 1) → α) : Fin (2 * m + 1) → α :=
  fun k => v ⟨k + (M - m), by omega⟩

/-- The window of radius `m` is the restriction of the window of radius `M ≥ m`. -/
theorem restrictWindow_window {M m : ℕ} (h : m ≤ M) (x : ℤ → α) :
    restrictWindow h (window M x) = window m x := by
  funext k
  simp only [restrictWindow, window]
  congr 1
  push_cast
  rw [Nat.cast_sub h]
  ring

/-- The sets `{𝐢 : (i_{-m}, …, i_m) ∈ F}` determined by finitely many coordinates. -/
def windowSets (α : Type*) : Set (Set (ℤ → α)) :=
  {S | ∃ (m : ℕ) (F : Set (Fin (2 * m + 1) → α)), S = window m ⁻¹' F}

/-- A set determined by the coordinates `|k| ≤ m` is determined by the coordinates `|k| ≤ M` for
`M ≥ m`. -/
theorem window_preimage_eq_of_le {M m : ℕ} (h : m ≤ M) (F : Set (Fin (2 * m + 1) → α)) :
    window m ⁻¹' F = window M ⁻¹' (restrictWindow h ⁻¹' F) := by
  ext x
  simp only [mem_preimage, restrictWindow_window]

/-- The sets determined by finitely many coordinates form an algebra of sets. -/
theorem isSetAlgebra_windowSets : IsSetAlgebra (windowSets α) where
  empty_mem := ⟨0, ∅, rfl⟩
  compl_mem := by
    rintro _ ⟨m, F, rfl⟩
    exact ⟨m, Fᶜ, rfl⟩
  union_mem := by
    rintro _ _ ⟨m₁, F₁, rfl⟩ ⟨m₂, F₂, rfl⟩
    refine ⟨max m₁ m₂, restrictWindow (le_max_left m₁ m₂) ⁻¹' F₁ ∪
      restrictWindow (le_max_right m₁ m₂) ⁻¹' F₂, ?_⟩
    rw [preimage_union, ← window_preimage_eq_of_le, ← window_preimage_eq_of_le]

variable [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

omit [Countable α] [MeasurableSingletonClass α] in
/-- The window map is measurable. -/
theorem measurable_window (m : ℕ) : Measurable (window m : (ℤ → α) → Fin (2 * m + 1) → α) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- The sets determined by finitely many coordinates generate the product `σ`-algebra of `Σ`. -/
theorem generateFrom_windowSets :
    MeasurableSpace.generateFrom (windowSets α) = (inferInstance : MeasurableSpace (ℤ → α)) := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) ?_
  · rintro _ ⟨m, F, rfl⟩
    exact measurable_window m (Set.to_countable F).measurableSet
  · refine iSup_le fun k => ?_
    rintro _ ⟨T, hT, rfl⟩
    refine MeasurableSpace.measurableSet_generateFrom
      ⟨k.natAbs, {v | v ⟨(k + k.natAbs).toNat, by omega⟩ ∈ T}, ?_⟩
    ext x
    simp only [mem_preimage, mem_ofPred_eq, window]
    have h : (((k + k.natAbs).toNat : ℕ) : ℤ) - (k.natAbs : ℤ) = k := by omega
    rw [h]

end Window

/-! ### Comparison of invariant measures through their cylinder values -/

section Comparison

variable {α : Type*} [MeasurableSpace α] [Finite α] [MeasurableSingletonClass α]
  {ν ν' : Measure (ℤ → α)}

/-- An invariant measure gives the set `{𝐢 : (i_{-m}, …, i_m) ∈ F}` the sum of the measures of
the cylinders `[w]`, `w ∈ F`. -/
theorem measure_window_preimage (hinv : MeasurePreserving (shift 1) ν ν) (m : ℕ)
    (F : Finset (Fin (2 * m + 1) → α)) :
    ν (window m ⁻¹' (F : Set (Fin (2 * m + 1) → α))) = ∑ w ∈ F, ν (cylinder w) := by
  have hpre : window m ⁻¹' (F : Set (Fin (2 * m + 1) → α)) =
      shift (-(m : ℤ)) ⁻¹' (block (2 * m + 1) ⁻¹' (F : Set (Fin (2 * m + 1) → α))) := by
    ext x
    simp only [mem_preimage, window_eq_block_shift]
  have hmeas : MeasurableSet (block (2 * m + 1) ⁻¹' (F : Set (Fin (2 * m + 1) → α))) :=
    measurable_block _ (Set.to_countable _).measurableSet
  have hshift : ν (shift (-(m : ℤ)) ⁻¹' (block (2 * m + 1) ⁻¹'
      (F : Set (Fin (2 * m + 1) → α)))) =
        ν (block (2 * m + 1) ⁻¹' (F : Set (Fin (2 * m + 1) → α))) := by
    rw [← (measurePreserving_shift_natCast hinv m).measure_preimage
      ((hmeas.preimage (measurable_shift _)).nullMeasurableSet), ← preimage_comp]
    congr 1
    ext x
    simp [shift_shift]
  rw [hpre, hshift, ← sum_measure_preimage_singleton F fun w _ =>
    measurable_block _ (measurableSet_singleton w)]
  exact Finset.sum_congr rfl fun w _ => by rw [cylinder_eq_preimage]

/-- If `ν'([w]) ≤ K ν([w])` for every cylinder and both measures are finite and invariant, then
`ν'(A) ≤ K ν(A)` for every Borel set `A`: the inequality holds on the algebra of the sets
determined by finitely many coordinates and passes to every Borel set by measure density. -/
theorem le_of_cylinder_le [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (hinv : MeasurePreserving (shift 1) ν ν) (hinv' : MeasurePreserving (shift 1) ν' ν')
    {K : ℝ≥0∞} (hK : K ≠ ∞) (hcyl : ∀ (n : ℕ) (w : Fin n → α), ν' (cylinder w) ≤ K * ν (cylinder w))
    {A : Set (ℤ → α)} (hA : MeasurableSet A) : ν' A ≤ K * ν A := by
  classical
  have := Fintype.ofFinite α
  have hwin : ∀ S ∈ windowSets α, ν' S ≤ K * ν S := by
    rintro _ ⟨m, F, rfl⟩
    have hF : (F : Set (Fin (2 * m + 1) → α)) = ((F.toFinset : Finset _) : Set _) := by simp
    rw [hF, measure_window_preimage hinv' m, measure_window_preimage hinv m, Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => hcyl _ w
  have hdense := Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite (ν + ν')
    isSetAlgebra_windowSets generateFrom_windowSets.symm
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hδ : (0 : ℝ) < ε / (K.toReal + 1) := div_pos hε (by positivity)
  obtain ⟨S, hS, hAS⟩ := hdense.approx A hA (measure_ne_top _ _) (ε / (K.toReal + 1)) hδ
  have hSm : MeasurableSet S := hdense.measurable S hS
  have hsymm : (ν + ν') (A ∆ S) = ν (A ∆ S) + ν' (A ∆ S) := rfl
  have h1 : ν' A ≤ ν' S + ν' (A ∆ S) := by
    calc ν' A ≤ ν' (S ∪ A ∆ S) := measure_mono fun x hx => by
          by_cases hxS : x ∈ S
          · exact Or.inl hxS
          · exact Or.inr (Or.inl ⟨hx, hxS⟩)
      _ ≤ ν' S + ν' (A ∆ S) := measure_union_le _ _
  have h2 : ν S ≤ ν A + ν (A ∆ S) := by
    calc ν S ≤ ν (A ∪ A ∆ S) := measure_mono fun x hx => by
          by_cases hxA : x ∈ A
          · exact Or.inl hxA
          · exact Or.inr (Or.inr ⟨hx, hxA⟩)
      _ ≤ ν A + ν (A ∆ S) := measure_union_le _ _
  have hsmall : (K + 1) * ((ν + ν') (A ∆ S)) ≤ ε := by
    have hlt := hAS.le
    calc (K + 1) * ((ν + ν') (A ∆ S)) ≤ (K + 1) * ENNReal.ofReal (ε / (K.toReal + 1)) :=
          mul_le_mul_right hlt _
      _ = ENNReal.ofReal ((K.toReal + 1) * (ε / (K.toReal + 1))) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add ENNReal.toReal_nonneg
            zero_le_one, ENNReal.ofReal_toReal hK, ENNReal.ofReal_one]
      _ = ε := by
          rw [mul_div_cancel₀ _ (by positivity : K.toReal + 1 ≠ 0)]
          exact ENNReal.ofReal_coe_nnreal
  rw [hsymm] at hsmall
  set x := ν (A ∆ S)
  set y := ν' (A ∆ S)
  have hmid : K * x + y ≤ (K + 1) * (x + y) := by
    calc K * x + y ≤ K * x + ((K * y + x) + y) := add_le_add le_rfl (le_add_left le_rfl)
      _ = (K + 1) * (x + y) := by ring
  calc ν' A ≤ ν' S + y := h1
    _ ≤ K * ν S + y := add_le_add (hwin S hS) le_rfl
    _ ≤ K * (ν A + x) + y := add_le_add (mul_le_mul' le_rfl h2) le_rfl
    _ = K * ν A + (K * x + y) := by rw [mul_add, add_assoc]
    _ ≤ K * ν A + (K + 1) * (x + y) := add_le_add le_rfl hmid
    _ ≤ K * ν A + ε := add_le_add le_rfl hsmall

end Comparison

/-! ### Uniqueness of ergodic Gibbs measures -/

section Uniqueness

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {o : ι → ZMod 2} {f : (ℤ → ι × ZMod 2) → ℝ} {ν ν' : Measure (ℤ → ι × ZMod 2)}
  {B D P C P' C' : ℝ}

/-- Two Gibbs probability measures carried by `Σ_Z` for the same potential of bounded distortion
have the same constant `P`. -/
theorem IsGibbsPotential.pressure_eq_pressure [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hν : ν (subshift o)ᶜ = 0) (hν' : ν' (subshift o)ᶜ = 0) (hg : IsGibbsPotential o f ν P C)
    (hg' : IsGibbsPotential o f ν' P' C') (h : HasBoundedDistortion o f B D) : P = P' :=
  tendsto_nhds_unique (hg.tendsto_log_admissibleSumPot hν h)
    (hg'.tendsto_log_admissibleSumPot hν' h)

/-- Two Gibbs probability measures carried by `Σ_Z` for the same potential of bounded distortion
have comparable cylinder values: `ν'([w]) ≤ C C' ν([w])` for every word `w`. -/
theorem IsGibbsPotential.measure_cylinder_le [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hν : ν (subshift o)ᶜ = 0) (hν' : ν' (subshift o)ᶜ = 0) (hg : IsGibbsPotential o f ν P C)
    (hg' : IsGibbsPotential o f ν' P' C') (h : HasBoundedDistortion o f B D) (n : ℕ)
    (w : Fin n → ι × ZMod 2) :
    ν' (cylinder w) ≤ ENNReal.ofReal (C * C') * ν (cylinder w) := by
  have : Nonempty ι := ⟨((nonempty_of_isProbabilityMeasure ν).some 0).1⟩
  have hPP := hg.pressure_eq_pressure hν hν' hg' h
  subst hPP
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hy₀ : tau o (fun _ => i) ∈ subshift o := tau_mem_subshift _
  have hC1 := hg.one_le hy₀
  have hC1' := hg'.one_le hy₀
  by_cases hw : IsAdmissible o w
  · rcases n with _ | n
    · have huniv : (cylinder w) = univ := eq_univ_of_forall fun _ k => k.elim0
      rw [huniv, measure_univ, measure_univ, mul_one]
      exact ENNReal.one_le_ofReal.2 (by nlinarith)
    · obtain ⟨y, hy, rfl⟩ := hw.exists_block_eq
      have h1 := (hg'.2 y hy (n + 1) (Nat.succ_pos n)).2
      have h2 := (hg.2 y hy (n + 1) (Nat.succ_pos n)).1
      have hreal : ν'.real (cylinder (block (n + 1) y)) ≤
          C * C' * ν.real (cylinder (block (n + 1) y)) := by
        rw [inv_mul_le_iff₀ hg.1] at h2
        calc ν'.real (cylinder (block (n + 1) y))
            ≤ C' * Real.exp (-((n + 1 : ℕ) * P) + birkhoffSum (shift 1) f (n + 1) y) := h1
          _ ≤ C' * (C * ν.real (cylinder (block (n + 1) y))) :=
            mul_le_mul_of_nonneg_left h2 hg'.1.le
          _ = C * C' * ν.real (cylinder (block (n + 1) y)) := by ring
      rw [← ofReal_measureReal, ← ofReal_measureReal, ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal hreal
  · have hsub : cylinder w ⊆ (subshift o)ᶜ := fun y hy hys =>
      hw ((funext hy : block n y = w) ▸ isAdmissible_block hys n)
    rw [measure_mono_null hsub hν']
    exact zero_le

/-- Uniqueness of the ergodic Gibbs measure (tex lines 2382 to 2384), for a potential of bounded
distortion: an invariant Gibbs probability measure carried by `Σ_Z` equals every ergodic Gibbs
probability measure carried by `Σ_Z` for the same potential. -/
theorem IsGibbsPotential.eq_of_ergodic [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hν : ν (subshift o)ᶜ = 0) (hν' : ν' (subshift o)ᶜ = 0) (hg : IsGibbsPotential o f ν P C)
    (hg' : IsGibbsPotential o f ν' P' C') (h : HasBoundedDistortion o f B D)
    (herg : Ergodic (shift 1) ν) (hinv' : MeasurePreserving (shift 1) ν' ν') : ν' = ν := by
  refine herg.eq_of_absolutelyContinuous hinv' fun A hA0 => ?_
  have hle : ∀ {A : Set (ℤ → ι × ZMod 2)}, MeasurableSet A →
      ν' A ≤ ENNReal.ofReal (C * C') * ν A := fun hA =>
    le_of_cylinder_le herg.toMeasurePreserving hinv' ENNReal.ofReal_ne_top
      (fun n w => hg.measure_cylinder_le hν hν' hg' h n w) hA
  obtain ⟨A', hAA', hA'm, hA'0⟩ := exists_measurable_superset_of_null hA0
  exact measure_mono_null hAA' (le_antisymm ((hle hA'm).trans (by rw [hA'0, mul_zero]))
    zero_le)

/-- Uniqueness of the ergodic Gibbs measure of a Hölder potential (tex lines 2382 to 2384): an
invariant Gibbs probability measure carried by `Σ_Z` equals every ergodic Gibbs probability
measure carried by `Σ_Z` for the same Hölder potential. In particular two ergodic Gibbs measures
for the same Hölder potential coincide. -/
theorem IsGibbsPotential.eq_of_ergodic_of_isHolder [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] (hν : ν (subshift o)ᶜ = 0) (hν' : ν' (subshift o)ᶜ = 0)
    (hg : IsGibbsPotential o f ν P C) (hg' : IsGibbsPotential o f ν' P' C')
    (hf : IsHolderPotential o f) (herg : Ergodic (shift 1) ν)
    (hinv' : MeasurePreserving (shift 1) ν' ν') : ν' = ν := by
  have : Nonempty ι := ⟨((nonempty_of_isProbabilityMeasure ν).some 0).1⟩
  obtain ⟨B, D, -, -, h⟩ := hf.exists_hasBoundedDistortion
  exact hg.eq_of_ergodic hν hν' hg' h herg hinv'

/-- Uniqueness of the ergodic Gibbs measure for the one-symbol potentials of the library: an
invariant `IsGibbs` probability measure carried by `Σ_Z` equals every ergodic one for the same
potential. -/
theorem IsGibbs.eq_of_ergodic [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    {φ : ι × ZMod 2 → ℝ} (hν : ν (subshift o)ᶜ = 0) (hν' : ν' (subshift o)ᶜ = 0)
    (hg : IsGibbs o φ ν) (hg' : IsGibbs o φ ν') (herg : Ergodic (shift 1) ν)
    (hinv' : MeasurePreserving (shift 1) ν' ν') : ν' = ν := by
  obtain ⟨P, C, hPC⟩ := isGibbs_iff.1 hg
  obtain ⟨P', C', hPC'⟩ := isGibbs_iff.1 hg'
  exact ((isGibbsPotential_iff_isGibbsWith φ).2 hPC).eq_of_ergodic_of_isHolder hν hν'
    ((isGibbsPotential_iff_isGibbsWith φ).2 hPC') (isHolderPotential_apply_zero φ) herg hinv'

/-- Tex lines 2572 and 2573: the `s`-Gibbs measure `μ_1` of a decomposition of
`thm:eq_state_is_sum` is the only invariant Gibbs probability measure carried by `Σ_Z` for the
potential `f_{1,s}`, so "the Gibbs measure associated to `f_{1,s}`" is well defined. -/
theorem System.GibbsDecomposition.eq_mu₁ {S : System ι} {s : ℝ} {μ : Measure (ℤ → ι)}
    {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)} (h : S.GibbsDecomposition s μ μ₁ μ₂)
    [IsProbabilityMeasure ν'] (hν' : ν' (subshift S.o)ᶜ = 0) (hg : IsGibbs S.o (S.potential₁ s) ν')
    (hinv' : MeasurePreserving (shift 1) ν' ν') : ν' = μ₁ := by
  have := h.prob₁
  exact IsGibbs.eq_of_ergodic h.supp₁ hν' h.gibbs₁ hg h.ergodic₁ hinv'

/-- Tex lines 2572 and 2573: the `s`-Gibbs measure `μ_2` of a decomposition of
`thm:eq_state_is_sum` is the only invariant Gibbs probability measure carried by `Σ_Z` for the
potential `f_{2,s}`. -/
theorem System.GibbsDecomposition.eq_mu₂ {S : System ι} {s : ℝ} {μ : Measure (ℤ → ι)}
    {μ₁ μ₂ : Measure (ℤ → ι × ZMod 2)} (h : S.GibbsDecomposition s μ μ₁ μ₂)
    [IsProbabilityMeasure ν'] (hν' : ν' (subshift S.o)ᶜ = 0) (hg : IsGibbs S.o (S.potential₂ s) ν')
    (hinv' : MeasurePreserving (shift 1) ν' ν') : ν' = μ₂ := by
  have := h.prob₂
  exact IsGibbs.eq_of_ergodic h.supp₂ hν' h.gibbs₂ hg h.ergodic₂ hinv'

end Uniqueness

end BoxLike
