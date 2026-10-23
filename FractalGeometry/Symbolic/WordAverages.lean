module

public import Mathlib
public import FractalGeometry.Symbolic.Entropy
public import FractalGeometry.Symbolic.Shift
public import FractalGeometry.Symbolic.FutureWords

@[expose] public section

namespace FractalGeometry


open MeasureTheory Filter Topology

open scoped Matrix.Norms.L2Operator

section futureWord

variable {α : Type*}

theorem futureWord_eq_ofFn_block (x : ℤ → α) (n : ℕ) :
    futureWord x n = List.ofFn (block n x) := by
  apply List.ext_getElem <;> simp [futureWord]

theorem futureWord_add (x : ℤ → α) (m n : ℕ) :
    futureWord x (m + n) = futureWord x m ++ futureWord (shift m x) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, futureWord_succ, ih, futureWord_succ, List.append_assoc, shift_apply,
      Nat.cast_add]

variable [MeasurableSpace α]

theorem integral_comp_shift {μ : Measure (ℤ → α)} (hμ : MeasurePreserving (shift 1) μ μ)
    (m : ℕ) {F : (ℤ → α) → ℝ} (hF : Measurable F) :
    ∫ x, F (shift m x) ∂μ = ∫ x, F x ∂μ := by
  have h := measurePreserving_shift_natCast hμ m
  rw [← integral_map h.measurable.aemeasurable hF.aestronglyMeasurable, h.map_eq]

variable [Finite α] [MeasurableSingletonClass α]

theorem measurable_comp_block {n : ℕ} (F : (Fin n → α) → ℝ) :
    Measurable fun x : ℤ → α => F (block n x) :=
  (Measurable.of_discrete (f := F)).comp (measurable_block n)

theorem integrable_comp_block {μ : Measure (ℤ → α)} [IsFiniteMeasure μ] {n : ℕ}
    (F : (Fin n → α) → ℝ) : Integrable (fun x => F (block n x)) μ :=
  (Integrable.of_finite (f := F)).comp_measurable (measurable_block n)

theorem measurable_comp_futureWord (G : List α → ℝ) (n : ℕ) :
    Measurable fun x : ℤ → α => G (futureWord x n) := by
  simp only [futureWord_eq_ofFn_block]
  exact measurable_comp_block fun w : Fin n → α => G (List.ofFn w)

theorem integrable_comp_futureWord {μ : Measure (ℤ → α)} [IsFiniteMeasure μ] (G : List α → ℝ)
    (n : ℕ) : Integrable (fun x => G (futureWord x n)) μ := by
  simp only [futureWord_eq_ofFn_block]
  exact integrable_comp_block fun w : Fin n → α => G (List.ofFn w)

variable {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ] {G H : List α → ℝ} {c : ℝ}

theorem le_integral_futureWord_div (hc : ∀ w, c * w.length ≤ G w) {n : ℕ} (hn : 0 < n) :
    c ≤ (∫ x, G (futureWord x n) ∂μ) / n := by
  rw [le_div_iff₀ (Nat.cast_pos.2 hn)]
  calc c * n = ∫ _, c * n ∂μ := by simp
    _ ≤ ∫ x, G (futureWord x n) ∂μ :=
      integral_mono (integrable_const _) (integrable_comp_futureWord G n) fun x => by
        simpa using hc (futureWord x n)

theorem exists_tendsto_integral_futureWord_div (hμ : MeasurePreserving (shift 1) μ μ)
    (hsub : ∀ w w', G (w ++ w') ≤ G w + G w') (hc : ∀ w, c * w.length ≤ G w) :
    ∃ L, Tendsto (fun n : ℕ => (∫ x, G (futureWord x n) ∂μ) / n) atTop (𝓝 L) := by
  have hsub' : Subadditive fun n : ℕ => ∫ x, G (futureWord x n) ∂μ := by
    intro m n
    have hint : Integrable (fun x => G (futureWord (shift m x) n)) μ :=
      (measurePreserving_shift_natCast hμ m).integrable_comp_of_integrable
        (integrable_comp_futureWord G n)
    calc ∫ x, G (futureWord x (m + n)) ∂μ
        ≤ ∫ x, (G (futureWord x m) + G (futureWord (shift m x) n)) ∂μ :=
          integral_mono (integrable_comp_futureWord G _)
            ((integrable_comp_futureWord G m).add hint) fun x => by
              rw [futureWord_add]; exact hsub _ _
      _ = ∫ x, G (futureWord x m) ∂μ + ∫ x, G (futureWord x n) ∂μ := by
          rw [integral_add (integrable_comp_futureWord G m) hint,
            integral_comp_shift hμ m (measurable_comp_futureWord G n)]
  have hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, G (futureWord x n) ∂μ) / n) := by
    refine ⟨min 0 c, ?_⟩
    rintro _ ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact (min_le_right _ _).trans (le_integral_futureWord_div hc hn)
  exact ⟨_, hsub'.tendsto_lim hbdd⟩

theorem exists_tendsto_integral_futureWord_div_of_superadditive
    (hμ : MeasurePreserving (shift 1) μ μ) (hsup : ∀ w w', G w + G w' ≤ G (w ++ w'))
    (hc : ∀ w, G w ≤ c * w.length) :
    ∃ L, Tendsto (fun n : ℕ => (∫ x, G (futureWord x n) ∂μ) / n) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := exists_tendsto_integral_futureWord_div hμ (G := fun w => -G w) (c := -c)
    (fun w w' => by linarith [hsup w w']) (fun w => by linarith [hc w])
  refine ⟨-L, hL.neg.congr fun n => ?_⟩
  rw [integral_neg, neg_div, neg_neg]

end futureWord

end FractalGeometry
