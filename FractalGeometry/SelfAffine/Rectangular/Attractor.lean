import Mathlib
import GeometricMeasureTheory.Box.ModifiedBox
import FractalGeometry.LinearCocycles.Monomial
import FractalGeometry.SelfAffine.Rectangular.Coding
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.SelfAffine.Rectangular.OpenSet
import FractalGeometry.SelfAffine.Rectangular.Orientation
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.OrientationCoding

open GeometricMeasureTheory

namespace FractalGeometry

open Metric

namespace RectangularIFS

variable {ι : Type*} (S : RectangularIFS ι)

section Continuity

variable [TopologicalSpace ι] [DiscreteTopology ι]

theorem continuous_gDeriv_futureWord (k : ℕ) :
    Continuous fun y : ℤ → ι × ZMod 2 => S.gDeriv (futureWord y k) := by
  induction k with
  | zero => simpa using continuous_const
  | succ k ih =>
    simp only [futureWord_succ, gDeriv_append, gDeriv_cons, gDeriv_nil, mul_one]
    exact ih.mul
      ((continuous_of_discreteTopology (f := S.ratio)).comp (continuous_apply (k : ℤ)))

theorem continuous_projBarTerm (k : ℕ) :
    Continuous fun y : ℤ → ι × ZMod 2 => S.projBarTerm y k :=
  (S.continuous_gDeriv_futureWord k).mul
    ((continuous_of_discreteTopology (f := S.trans)).comp (continuous_apply (k : ℤ)))

variable {S} in

theorem Bounds.continuous_projBar {r M : ℝ} (hS : S.Bounds r M) : Continuous S.projBar := by
  refine continuous_tsum (u := fun k => r ^ k * M) S.continuous_projBarTerm
    ((summable_geometric_of_lt_one hS.r_nonneg hS.r_lt_one).mul_right M) fun k y => ?_
  rw [projBarTerm, Real.norm_eq_abs, abs_mul]
  have h := hS.abs_gDeriv_le (futureWord y k)
  rw [length_futureWord] at h
  exact mul_le_mul h (hS.abs_trans_le _) (abs_nonneg _) (pow_nonneg hS.r_nonneg _)

theorem continuous_eps (o : ι → ZMod 2) (n : ℤ) : Continuous fun x : ℤ → ι => eps o x n := by
  rcases n with n | n
  · change Continuous fun x : ℤ → ι => ∑ j ∈ Finset.range n, o (x j)
    exact continuous_finsetSum _ fun j _ =>
      continuous_of_discreteTopology.comp (continuous_apply _)
  · change Continuous fun x : ℤ → ι => ∑ j ∈ Finset.range (n + 1), o (x (-(j + 1 : ℤ)))
    exact continuous_finsetSum _ fun j _ =>
      continuous_of_discreteTopology.comp (continuous_apply _)

theorem continuous_tau (o : ι → ZMod 2) : Continuous (tau o) :=
  continuous_pi fun n => (continuous_apply n).prodMk (continuous_eps o n)

theorem continuous_omega (o : ι → ZMod 2) : Continuous (omega o) :=
  continuous_pi fun n => (continuous_apply n).prodMk ((continuous_eps o n).add continuous_const)

variable {S} in

theorem Bounds.continuous_proj {r M : ℝ} (hS : S.Bounds r M) : Continuous S.proj :=
  (hS.continuous_projBar.comp (continuous_tau S.o)).prodMk
    (hS.continuous_projBar.comp (continuous_omega S.o))

theorem continuous_proj [Finite ι] : Continuous S.proj := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  exact hS.continuous_proj

end Continuity

theorem isCompact_attractor [Finite ι] : IsCompact S.attractor := by
  let : TopologicalSpace ι := ⊥
  have : DiscreteTopology ι := ⟨rfl⟩
  exact isCompact_range S.continuous_proj

theorem attractor_nonempty [Nonempty ι] : S.attractor.Nonempty :=
  Set.range_nonempty S.proj

theorem attractor_eq_iUnion [Finite ι] : S.attractor = ⋃ i, S.phi i '' S.attractor := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  exact hS.attractor_eq_iUnion

theorem image_attractor_subset [Finite ι] (i : ι) : S.phi i '' S.attractor ⊆ S.attractor :=
  (Set.subset_iUnion (fun i => S.phi i '' S.attractor) i).trans S.attractor_eq_iUnion.symm.subset

theorem abs_coord_sub_le (c : ZMod 2) (z w : ℝ × ℝ) : |coord c z - coord c w| ≤ dist z w := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  unfold coord
  split_ifs
  exacts [le_max_left _ _, le_max_right _ _]

theorem dist_phi_le (i : ι) (z w : ℝ × ℝ) :
    dist (S.phi i z) (S.phi i w) ≤ max |S.a i| |S.b i| * dist z w := by
  have h1 : dist (S.phi i z).1 (S.phi i w).1 ≤ |S.a i| * dist z w := by
    have h : (S.phi i z).1 - (S.phi i w).1 = S.a i * (coord (S.o i) z - coord (S.o i) w) := by
      simp only [phi]; ring
    rw [Real.dist_eq, h, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_coord_sub_le _ z w) (abs_nonneg _)
  have h2 : dist (S.phi i z).2 (S.phi i w).2 ≤ |S.b i| * dist z w := by
    have h : (S.phi i z).2 - (S.phi i w).2 =
        S.b i * (coord (S.o i + 1) z - coord (S.o i + 1) w) := by
      simp only [phi]; ring
    rw [Real.dist_eq, h, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_coord_sub_le _ z w) (abs_nonneg _)
  rw [Prod.dist_eq]
  exact max_le (h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg))
    (h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg))

variable {S} in

theorem Bounds.dist_phi_le {r M : ℝ} (hS : S.Bounds r M) (i : ι) (z w : ℝ × ℝ) :
    dist (S.phi i z) (S.phi i w) ≤ r * dist z w :=
  (S.dist_phi_le i z w).trans (mul_le_mul_of_nonneg_right
    (max_le (hS.abs_ratio_le (i, 0)) (hS.abs_ratio_le (i, 1))) dist_nonneg)

theorem lipschitzWith_phi (i : ι) :
    LipschitzWith ⟨max |S.a i| |S.b i|, le_max_of_le_left (abs_nonneg _)⟩ (S.phi i) :=
  LipschitzWith.of_dist_le_mul (S.dist_phi_le i)

theorem le_dist_phi (i : ι) (z w : ℝ × ℝ) :
    min |S.a i| |S.b i| * dist z w ≤ dist (S.phi i z) (S.phi i w) := by
  have h1 : |S.a i| * |coord (S.o i) z - coord (S.o i) w| ≤ dist (S.phi i z) (S.phi i w) := by
    have h : (S.phi i z).1 - (S.phi i w).1 = S.a i * (coord (S.o i) z - coord (S.o i) w) := by
      simp only [phi]; ring
    rw [← abs_mul, ← h]
    exact abs_coord_sub_le 0 _ _
  have h2 : |S.b i| * |coord (S.o i + 1) z - coord (S.o i + 1) w| ≤
      dist (S.phi i z) (S.phi i w) := by
    have h : (S.phi i z).2 - (S.phi i w).2 =
        S.b i * (coord (S.o i + 1) z - coord (S.o i + 1) w) := by
      simp only [phi]; ring
    rw [← abs_mul, ← h]
    exact abs_coord_sub_le 1 _ _
  have hm : 0 ≤ min |S.a i| |S.b i| := le_min (abs_nonneg _) (abs_nonneg _)
  have ha : ∀ t : ℝ, min |S.a i| |S.b i| * |t| ≤ |S.a i| * |t| := fun t =>
    mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg t)
  have hb : ∀ t : ℝ, min |S.a i| |S.b i| * |t| ≤ |S.b i| * |t| := fun t =>
    mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg t)
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, mul_max_of_nonneg _ _ hm]
  rcases zmod_two_cases (S.o i) with h0 | h0
  · rw [h0, zero_add] at h2
    rw [h0] at h1
    exact max_le ((ha _).trans h1) ((hb _).trans h2)
  · rw [h0, show (1 : ZMod 2) + 1 = 0 from by decide] at h2
    rw [h0] at h1
    exact max_le ((hb _).trans h2) ((ha _).trans h1)

theorem injective_phi (i : ι) : Function.Injective (S.phi i) := by
  intro z w h
  obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h
  simp only [phi] at h1 h2
  have e1 := mul_left_cancel₀ (S.a_ne_zero i) (add_right_cancel h1)
  have e2 := mul_left_cancel₀ (S.b_ne_zero i) (add_right_cancel h2)
  rcases zmod_two_cases (S.o i) with h0 | h0
  · rw [h0] at e1 e2
    exact Prod.ext e1 e2
  · rw [h0] at e1 e2
    exact Prod.ext e2 e1

variable {S} in

theorem Bounds.subset_of_invariant {r M : ℝ} (hS : S.Bounds r M) {K L : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hKsub : K ⊆ ⋃ i, S.phi i '' K) (hL : IsCompact L) (hLne : L.Nonempty)
    (hLsub : ∀ i, S.phi i '' L ⊆ L) : K ⊆ L := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact Set.empty_subset _
  obtain ⟨x₀, hx₀, hmax⟩ := hK.exists_isMaxOn hKne (continuous_infDist_pt L).continuousOn
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hKsub hx₀)
  obtain ⟨y, hy, rfl⟩ := hi
  obtain ⟨l, hl, hyl⟩ := hL.exists_infDist_eq_dist hLne y
  have h1 : infDist (S.phi i y) L ≤ r * infDist y L := by
    rw [hyl]
    exact (infDist_le_dist_of_mem (hLsub i ⟨l, hl, rfl⟩)).trans (hS.dist_phi_le i y l)
  have h2 : infDist y L ≤ infDist (S.phi i y) L := isMaxOn_iff.1 hmax y hy
  have h3 : infDist (S.phi i y) L ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    have h4 := mul_lt_mul_of_pos_right hS.r_lt_one hpos
    have h5 := mul_le_mul_of_nonneg_left h2 hS.r_nonneg
    linarith
  intro x hx
  exact (hL.isClosed.mem_iff_infDist_zero hLne).2
    (le_antisymm ((isMaxOn_iff.1 hmax x hx).trans h3) infDist_nonneg)

end RectangularIFS

end FractalGeometry
