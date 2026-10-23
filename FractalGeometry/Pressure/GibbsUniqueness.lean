import Mathlib
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.Shift

namespace FractalGeometry

open MeasureTheory Filter Topology Set

open scoped ENNReal symmDiff

section Window

variable {α : Type*}

def window (m : ℕ) (x : ℤ → α) : Fin (2 * m + 1) → α := fun k => x ((k : ℤ) - m)

theorem window_eq_block_shift (m : ℕ) (x : ℤ → α) :
    window m x = block (2 * m + 1) (shift (-(m : ℤ)) x) := by
  funext k
  simp only [window, block_apply, shift_apply]
  congr 1
  ring

def restrictWindow {M m : ℕ} (h : m ≤ M) (v : Fin (2 * M + 1) → α) : Fin (2 * m + 1) → α :=
  fun k => v ⟨k + (M - m), by omega⟩

theorem restrictWindow_window {M m : ℕ} (h : m ≤ M) (x : ℤ → α) :
    restrictWindow h (window M x) = window m x := by
  funext k
  simp only [restrictWindow, window]
  congr 1
  push_cast
  rw [Nat.cast_sub h]
  ring

def windowSets (α : Type*) : Set (Set (ℤ → α)) :=
  {S | ∃ (m : ℕ) (F : Set (Fin (2 * m + 1) → α)), S = window m ⁻¹' F}

theorem window_preimage_eq_of_le {M m : ℕ} (h : m ≤ M) (F : Set (Fin (2 * m + 1) → α)) :
    window m ⁻¹' F = window M ⁻¹' (restrictWindow h ⁻¹' F) := by
  ext x
  simp only [mem_preimage, restrictWindow_window]

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

theorem measurable_window (m : ℕ) : Measurable (window m : (ℤ → α) → Fin (2 * m + 1) → α) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

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

section Comparison

variable {α : Type*} [MeasurableSpace α] [Finite α] [MeasurableSingletonClass α]
  {ν ν' : Measure (ℤ → α)}

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

end FractalGeometry
