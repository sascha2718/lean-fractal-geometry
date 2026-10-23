module

public import Mathlib
public import FractalGeometry.Symbolic.Entropy
public import FractalGeometry.Ergodic.Kingman
public import FractalGeometry.Symbolic.WordAverages
public import FractalGeometry.LinearCocycles.Products
public import FractalGeometry.Symbolic.Shift
public import FractalGeometry.LinearCocycles.Lyapunov
public import FractalGeometry.LinearCocycles.Regularity
public import FractalGeometry.Symbolic.FutureWords
public import FractalGeometry.Symbolic.ShiftMeasure
public import FractalGeometry.Symbolic.Past
public import FractalGeometry.Symbolic.PastWords

/-!
Almost-sure logarithmic growth of backward products of a finite family of
invertible real 2-by-2 matrices under an ergodic shift-invariant probability measure.
Both singular-value rates are obtained from Kingman's subadditive ergodic theorem.
Planar specialisation of Harry Furstenberg and Harry Kesten, Products of random
matrices, Annals of Mathematical Statistics 31(2) (1960), 457–469,
doi:10.1214/aoms/1177705909.
-/

@[expose] public section

namespace FractalGeometry

open FractalGeometry.Ergodic

open MeasureTheory Filter Topology Set Matrix

open scoped Matrix.Norms.L2Operator

theorem pastWord_add {α : Type*} (x : ℤ → α) (m n : ℕ) :
    pastWord x (m + n) = pastWord (shift (-(m : ℤ)) x) n ++ pastWord x m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, pastWord_succ, ih, pastWord_succ, List.cons_append, shift_apply]
    congr 2
    push_cast
    ring

section Backward

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem measurable_comp_pastWord (G : List α → ℝ) (n : ℕ) :
    Measurable fun x : ℤ → α => G (pastWord x n) := by
  simp only [pastWord_eq_futureWord]
  exact (measurable_comp_futureWord G n).comp (measurable_shift _)

theorem tendsto_pastWord_of_subadditive {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]
    (herg : Ergodic (shift 1) μ) {G : List α → ℝ} (hsub : ∀ w w', G (w ++ w') ≤ G w + G w')
    {L : ℝ} (hL : Tendsto (fun n : ℕ => (∫ x, G (futureWord x n) ∂μ) / n) atTop (𝓝 L)) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => G (pastWord x n) / n) atTop (𝓝 L) := by
  have hμ := herg.toMeasurePreserving
  have hcoc : IsSubadditiveCocycle (shift (-1)) fun n x => G (pastWord x n) := by
    intro m n x
    dsimp only
    rw [iterate_shift_neg_one, pastWord_add, add_comm (G (pastWord x m))]
    exact hsub _ _
  have hint : ∀ n, Integrable (fun x : ℤ → α => G (pastWord x n)) μ := fun n => by
    simp only [pastWord_eq_futureWord]
    exact (measurePreserving_shift_neg_natCast hμ n).integrable_comp_of_integrable
      (integrable_comp_futureWord G n)
  have hI : ∀ n : ℕ, ∫ x, G (pastWord x n) ∂μ = ∫ x, G (futureWord x n) ∂μ := fun n => by
    simp only [pastWord_eq_futureWord]
    exact integral_comp_shift_neg hμ n (measurable_comp_futureWord G n)
  exact kingman_ergodic_of_tendsto (ergodic_shift_neg_one herg) hcoc
    (fun n => measurable_comp_pastWord G n) hint (hL.congr fun n => by rw [hI])

end Backward

namespace MatrixTuple

variable {ι : Type*} {A : ι → Matrix (Fin 2) (Fin 2) ℝ}

theorem pastProd_succ (x : ℤ → ι) (n : ℕ) :
    pastProd A x (n + 1) = A (x (-((n : ℤ) + 1))) * pastProd A x n := by
  rw [pastProd, pastWord_succ, pastProd]
  simp [word]

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]

theorem tendsto_log_norm_pastProd (hA : ∀ i, (A i).det ≠ 0) (herg : Ergodic (shift 1) μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => Real.log ‖pastProd A x n‖ / n) atTop
      (𝓝 (lyapunov₁ A μ)) :=
  tendsto_pastWord_of_subadditive herg (G := fun w => Real.log ‖word A w‖)
    (log_norm_word_append_le hA) (tendsto_lyapunov₁_of_det_ne_zero hA herg.toMeasurePreserving)

theorem tendsto_log_alpha₂_pastProd (hA : ∀ i, (A i).det ≠ 0) (herg : Ergodic (shift 1) μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ =>
      Real.log (|(pastProd A x n).det| / ‖pastProd A x n‖) / n) atTop (𝓝 (lyapunov₂ A μ)) := by
  have hL := (tendsto_lyapunov₂_of_det_ne_zero hA herg.toMeasurePreserving).neg
  have h := tendsto_pastWord_of_subadditive herg
    (G := fun w => -Real.log (|(word A w).det| / ‖word A w‖))
    (fun w w' => by linarith [le_log_abs_det_div_norm_word_append hA w w'])
    (L := -lyapunov₂ A μ) (hL.congr fun n => by rw [integral_neg, neg_div])
  filter_upwards [h] with x hx
  have hx' := hx.neg
  rw [neg_neg] at hx'
  refine hx'.congr fun n => ?_
  simp only [pastProd, neg_div, neg_neg]

end MatrixTuple

end FractalGeometry
