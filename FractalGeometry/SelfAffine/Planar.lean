import Mathlib
import GeometricMeasureTheory.Box.BoxDimension
import FractalGeometry.LinearCocycles.Norms
import FractalGeometry.LinearCocycles.Products
import FractalGeometry.Symbolic.FutureWords

/-!
Finite planar affine IFS vocabulary. Each linear part is invertible and has
Euclidean operator norm less than one. The coding is the convergent affine
series, and its range is the attractor. There are no separation assumptions.
-/

open GeometricMeasureTheory

namespace FractalGeometry

open MeasureTheory Filter Topology Matrix

open scoped Matrix.Norms.L2Operator

def toVec (z : ℝ × ℝ) : Fin 2 → ℝ := ![z.1, z.2]

def ofVec (u : Fin 2 → ℝ) : ℝ × ℝ := (u 0, u 1)

@[simp] theorem ofVec_toVec (z : ℝ × ℝ) : ofVec (toVec z) = z := rfl

@[simp] theorem ofVec_zero : ofVec 0 = 0 := rfl

theorem ofVec_sub (u u' : Fin 2 → ℝ) : ofVec (u - u') = ofVec u - ofVec u' := rfl

@[simp] theorem toVec_ofVec (u : Fin 2 → ℝ) : toVec (ofVec u) = u := by
  ext j; fin_cases j <;> rfl

theorem toVec_sub (z w : ℝ × ℝ) : toVec (z - w) = toVec z - toVec w := by
  ext j; fin_cases j <;> rfl

@[simp] theorem toVec_zero : toVec 0 = 0 := by
  ext j; fin_cases j <;> rfl

theorem norm_ofVec_le (u : Fin 2 → ℝ) : ‖ofVec u‖ ≤ ‖u‖ := by
  rw [Prod.norm_def]
  exact max_le (norm_le_pi_norm u 0) (norm_le_pi_norm u 1)

structure AffineIFS (ι : Type*) where

  mat : ι → Matrix (Fin 2) (Fin 2) ℝ

  v : ι → ℝ × ℝ

  det_ne_zero : ∀ i, (mat i).det ≠ 0

  norm_lt_one : ∀ i, ‖mat i‖ < 1

namespace AffineIFS

variable {ι : Type*} (P : AffineIFS ι)

def phi (i : ι) (z : ℝ × ℝ) : ℝ × ℝ := ofVec (P.mat i *ᵥ toVec z) + P.v i

def phiWord : List ι → ℝ × ℝ → ℝ × ℝ
  | [] => id
  | i :: w => P.phi i ∘ phiWord w

@[simp] theorem phiWord_nil : P.phiWord [] = id := rfl

@[simp] theorem phiWord_cons (i : ι) (w : List ι) :
    P.phiWord (i :: w) = P.phi i ∘ P.phiWord w := rfl

theorem phi_sub_phi (i : ι) (z w : ℝ × ℝ) :
    P.phi i z - P.phi i w = ofVec (P.mat i *ᵥ toVec (z - w)) := by
  simp only [phi, toVec_sub, mulVec_sub, ofVec_sub]
  abel

theorem phiWord_apply (w : List ι) (z : ℝ × ℝ) :
    P.phiWord w z = P.phiWord w 0 + ofVec (MatrixTuple.word P.mat w *ᵥ toVec z) := by
  induction w generalizing z with
  | nil => simp [MatrixTuple.word]
  | cons i w ih =>
    simp only [phiWord_cons, Function.comp_apply]
    rw [ih z, ih 0]
    simp only [toVec_zero, mulVec_zero, ofVec_zero, add_zero]
    have h := P.phi_sub_phi i (P.phiWord w 0 + ofVec (MatrixTuple.word P.mat w *ᵥ toVec z))
      (P.phiWord w 0)
    rw [add_sub_cancel_left, toVec_ofVec, mulVec_mulVec] at h
    rw [show MatrixTuple.word P.mat (i :: w) = P.mat i * MatrixTuple.word P.mat w by
      simp [MatrixTuple.word], ← h]
    abel

def projTerm (x : ℤ → ι) (k : ℕ) : ℝ × ℝ :=
  ofVec (MatrixTuple.word P.mat (futureWord x k) *ᵥ toVec (P.v (x k)))

noncomputable def proj (x : ℤ → ι) : ℝ × ℝ := ∑' k, P.projTerm x k

theorem phiWord_futureWord (x : ℤ → ι) (n : ℕ) :
    P.phiWord (futureWord x n) 0 = ∑ k ∈ Finset.range n, P.projTerm x k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, futureWord_succ]
    have h : ∀ (w : List ι) (i : ι), P.phiWord (w ++ [i]) 0 = P.phiWord w (P.v i) := by
      intro w i
      induction w with
      | nil => simp [phi, toVec_zero]
      | cons j w ih' => simp only [List.cons_append, phiWord_cons, Function.comp_apply, ih']
    rw [h, P.phiWord_apply, projTerm]

theorem exists_bounds [Finite ι] :
    ∃ r M : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ M ∧ (∀ i, ‖P.mat i‖ ≤ r) ∧ ∀ i, ‖toVec (P.v i)‖ ≤ M := by
  classical
  have := Fintype.ofFinite ι
  by_cases hι : Nonempty ι
  · obtain ⟨i₁, -, h₁⟩ := Finset.exists_max_image Finset.univ (fun i => ‖P.mat i‖)
      Finset.univ_nonempty
    obtain ⟨i₂, -, h₂⟩ := Finset.exists_max_image Finset.univ (fun i => ‖toVec (P.v i)‖)
      Finset.univ_nonempty
    exact ⟨‖P.mat i₁‖, ‖toVec (P.v i₂)‖, norm_nonneg _, P.norm_lt_one i₁, norm_nonneg _,
      fun i => h₁ i (Finset.mem_univ i), fun i => h₂ i (Finset.mem_univ i)⟩
  · exact ⟨0, 0, le_rfl, zero_lt_one, le_rfl, fun i => absurd ⟨i⟩ hι, fun i => absurd ⟨i⟩ hι⟩

theorem norm_word_le {r : ℝ} (hr : 0 ≤ r) (hA : ∀ i, ‖P.mat i‖ ≤ r) (w : List ι) :
    ‖MatrixTuple.word P.mat w‖ ≤ r ^ w.length := by
  induction w with
  | nil =>
    simp only [MatrixTuple.word_nil, List.length_nil, pow_zero]
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp
  | cons i w ih =>
    simp only [MatrixTuple.word, List.map_cons, List.prod_cons, List.length_cons, pow_succ']
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    exact mul_le_mul (hA i) ih (norm_nonneg _) hr

theorem norm_projTerm_le {r M : ℝ} (hr : 0 ≤ r) (hA : ∀ i, ‖P.mat i‖ ≤ r)
    (hv : ∀ i, ‖toVec (P.v i)‖ ≤ M) (x : ℤ → ι) (k : ℕ) :
    ‖P.projTerm x k‖ ≤ 2 * M * r ^ k := by
  refine (norm_ofVec_le _).trans ((norm_mulVec_le _ _).trans ?_)
  have h := P.norm_word_le hr hA (futureWord x k)
  rw [length_futureWord] at h
  have hM : 0 ≤ M := (norm_nonneg _).trans (hv (x k))
  calc 2 * ‖MatrixTuple.word P.mat (futureWord x k)‖ * ‖toVec (P.v (x k))‖
      ≤ 2 * r ^ k * M := by gcongr; exact hv (x k)
    _ = 2 * M * r ^ k := by ring

theorem summable_projTerm [Finite ι] (x : ℤ → ι) : Summable (P.projTerm x) := by
  obtain ⟨r, M, hr, hr1, -, hA, hv⟩ := P.exists_bounds
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hr hr1).mul_left (2 * M)) ?_
  exact fun k => P.norm_projTerm_le hr hA hv x k

theorem tendsto_phiWord [Finite ι] (x : ℤ → ι) :
    Tendsto (fun n => P.phiWord (futureWord x n) 0) atTop (𝓝 (P.proj x)) := by
  simp only [phiWord_futureWord]
  exact (P.summable_projTerm x).hasSum.tendsto_sum_nat

def attractor : Set (ℝ × ℝ) := Set.range P.proj

end AffineIFS

end FractalGeometry
