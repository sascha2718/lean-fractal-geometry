import Mathlib
import GeometricMeasureTheory.Box.BoxDimension
import FractalGeometry.LinearCocycles.Products
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.OneSidedShift


open GeometricMeasureTheory

namespace FractalGeometry

open MeasureTheory Filter Topology Set Matrix

open scoped Matrix.Norms.L2Operator

noncomputable def planeLin (B : Matrix (Fin 2) (Fin 2) ℝ) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) B

theorem planeLin_mul (B B' : Matrix (Fin 2) (Fin 2) ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    planeLin (B * B') x = planeLin B (planeLin B' x) := by
  simp [planeLin, map_mul]

@[simp] theorem planeLin_one (x : EuclideanSpace ℝ (Fin 2)) : planeLin 1 x = x := by
  simp [planeLin, map_one]

theorem norm_planeLin (B : Matrix (Fin 2) (Fin 2) ℝ) : ‖planeLin B‖ = ‖B‖ :=
  l2_opNorm_toEuclideanCLM B

theorem planeLin_toLp (B : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    planeLin B (WithLp.toLp 2 x) = WithLp.toLp 2 (B *ᵥ x) := rfl

section Prefix

variable {α : Type*}

def futureWordPlus (y : ℕ → α) (n : ℕ) : List α := (List.range n).map y

@[simp] theorem futureWordPlus_zero (y : ℕ → α) : futureWordPlus y 0 = [] := rfl

@[simp] theorem length_futureWordPlus (y : ℕ → α) (n : ℕ) : (futureWordPlus y n).length = n := by
  simp [futureWordPlus]

theorem futureWordPlus_succ (y : ℕ → α) (n : ℕ) :
    futureWordPlus y (n + 1) = futureWordPlus y n ++ [y n] := by
  simp [futureWordPlus, List.range_succ]

theorem futureWordPlus_succ' (y : ℕ → α) (n : ℕ) :
    futureWordPlus y (n + 1) = y 0 :: futureWordPlus (shiftPlus y) n := by
  simp only [futureWordPlus, List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

theorem futureWordPlus_eq_ofFn (y : ℕ → α) (n : ℕ) :
    futureWordPlus y n = List.ofFn fun j : Fin n => y j := by
  apply List.ext_getElem (by simp [futureWordPlus])
  intro k h1 h2
  simp [futureWordPlus]

theorem futureWord_eq_futureWordPlus (x : ℤ → α) (n : ℕ) :
    futureWord x n = futureWordPlus (eta x) n := rfl

end Prefix

namespace MatrixTuple

variable {ι : Type*} (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (v : ι → EuclideanSpace ℝ (Fin 2))

noncomputable def affineMap (i : ι) (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  planeLin (A i) x + v i

noncomputable def affineWord : List ι → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)
  | [] => id
  | i :: w => affineMap A v i ∘ affineWord w

@[simp] theorem affineWord_nil : affineWord A v [] = id := rfl

@[simp] theorem affineWord_cons (i : ι) (w : List ι) :
    affineWord A v (i :: w) = affineMap A v i ∘ affineWord A v w := rfl

theorem affineWord_append (w w' : List ι) :
    affineWord A v (w ++ w') = affineWord A v w ∘ affineWord A v w' := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [ih, Function.comp_assoc]

theorem word_cons_eq_mul (i : ι) (w : List ι) : word A (i :: w) = A i * word A w := rfl

theorem affineWord_apply (w : List ι) (x : EuclideanSpace ℝ (Fin 2)) :
    affineWord A v w x = planeLin (word A w) x + affineWord A v w 0 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    simp only [affineWord_cons, Function.comp_apply, affineMap, word_cons_eq_mul, planeLin_mul]
    rw [ih, map_add, add_assoc]

theorem affineWord_sub (w : List ι) (x x' : EuclideanSpace ℝ (Fin 2)) :
    affineWord A v w x - affineWord A v w x' = planeLin (word A w) (x - x') := by
  rw [affineWord_apply A v w x, affineWord_apply A v w x', map_sub]
  abel

def ContractionBound (r : ℝ) : Prop := 0 ≤ r ∧ r < 1 ∧ ∀ i, ‖A i‖ ≤ r

theorem exists_contractionBound [Finite ι] (hA : ∀ i, ‖A i‖ < 1) :
    ∃ r, ContractionBound A r := by
  classical
  have := Fintype.ofFinite ι
  by_cases hι : Nonempty ι
  · obtain ⟨i₀, -, h⟩ := Finset.exists_max_image Finset.univ (fun i => ‖A i‖)
      Finset.univ_nonempty
    exact ⟨‖A i₀‖, norm_nonneg _, hA i₀, fun i => h i (Finset.mem_univ _)⟩
  · exact ⟨0, le_rfl, zero_lt_one, fun i => (hι ⟨i⟩).elim⟩

theorem norm_one_matrix_le : ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ ≤ 1 := by
  rw [← norm_planeLin]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [planeLin_one, one_mul]

variable {A} {r : ℝ}

theorem ContractionBound.norm_word_le (hA : ContractionBound A r) (w : List ι) :
    ‖word A w‖ ≤ r ^ w.length := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [word_cons_eq_mul, List.length_cons, pow_succ']
    exact (l2_opNorm_mul _ _).trans (mul_le_mul (hA.2.2 i) ih (norm_nonneg _) hA.1)

theorem ContractionBound.norm_toEuclideanCLM_word_le (hA : ContractionBound A r) (w : List ι)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ‖planeLin (word A w) x‖ ≤ r ^ w.length * ‖x‖ := by
  refine (ContinuousLinearMap.le_opNorm _ x).trans ?_
  rw [norm_planeLin]
  exact mul_le_mul_of_nonneg_right (hA.norm_word_le w) (norm_nonneg _)

variable (A)

noncomputable def projPlusTerm (y : ℕ → ι) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  planeLin (word A (futureWordPlus y k)) (v (y k))

noncomputable def canonicalProjPlus (y : ℕ → ι) : EuclideanSpace ℝ (Fin 2) :=
  ∑' k, projPlusTerm A v y k

noncomputable def canonicalProj (x : ℤ → ι) : EuclideanSpace ℝ (Fin 2) :=
  canonicalProjPlus A v (eta x)

theorem canonicalProj_eq_comp : canonicalProj A v = canonicalProjPlus A v ∘ eta := rfl

theorem range_canonicalProj : range (canonicalProj A v) = range (canonicalProjPlus A v) := by
  rw [canonicalProj_eq_comp, range_comp, eta_surjective.range_eq, image_univ]

theorem affineWord_futureWordPlus_zero (y : ℕ → ι) (n : ℕ) :
    affineWord A v (futureWordPlus y n) 0 = ∑ k ∈ Finset.range n, projPlusTerm A v y k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [futureWordPlus_succ, affineWord_append, Function.comp_apply, affineWord_apply, ih,
      Finset.sum_range_succ, add_comm, projPlusTerm]
    simp [affineMap]

variable {A}

variable [Finite ι]

theorem exists_norm_trans_le : ∃ M : ℝ, 0 ≤ M ∧ ∀ i, ‖v i‖ ≤ M := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨∑ i, ‖v i‖, Finset.sum_nonneg fun i _ => norm_nonneg _, fun i => ?_⟩
  exact Finset.single_le_sum (f := fun i => ‖v i‖) (fun i _ => norm_nonneg _)
    (Finset.mem_univ i)

theorem ContractionBound.summable_projPlusTerm (hA : ContractionBound A r) (y : ℕ → ι) :
    Summable (projPlusTerm A v y) := by
  obtain ⟨M, hM, hv⟩ := exists_norm_trans_le v
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hA.1 hA.2.1).mul_right M) fun k => ?_
  refine (hA.norm_toEuclideanCLM_word_le _ _).trans ?_
  rw [length_futureWordPlus]
  exact mul_le_mul_of_nonneg_left (hv _) (pow_nonneg hA.1 _)

theorem ContractionBound.tendsto_affineWord (hA : ContractionBound A r) (y : ℕ → ι) :
    Tendsto (fun n => affineWord A v (futureWordPlus y n) 0) atTop
      (𝓝 (canonicalProjPlus A v y)) := by
  simp only [affineWord_futureWordPlus_zero]
  exact (hA.summable_projPlusTerm v y).hasSum.tendsto_sum_nat

theorem ContractionBound.canonicalProjPlus_eq_affineMap (hA : ContractionBound A r)
    (y : ℕ → ι) :
    canonicalProjPlus A v y = affineMap A v (y 0) (canonicalProjPlus A v (shiftPlus y)) := by
  have h1 : Tendsto (fun n => affineWord A v (futureWordPlus y (n + 1)) 0) atTop
      (𝓝 (canonicalProjPlus A v y)) :=
    (tendsto_add_atTop_iff_nat 1).2 (hA.tendsto_affineWord v y)
  have hc : Continuous (affineMap A v (y 0)) := by
    unfold affineMap
    fun_prop
  have h2 := (hc.tendsto _).comp (hA.tendsto_affineWord v (shiftPlus y))
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  rw [Function.comp_apply, futureWordPlus_succ', affineWord_cons, Function.comp_apply]

section Measure

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

omit [Finite ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in

theorem projPlusTerm_eq (y : ℕ → ι) (k : ℕ) :
    projPlusTerm A v y k =
      (fun w : Fin (k + 1) → ι =>
        planeLin (word A (List.ofFn fun j : Fin k => w (Fin.castSucc j)))
          (v (w (Fin.last k)))) (fun j => y j) := by
  simp only [projPlusTerm, futureWordPlus_eq_ofFn, Fin.val_castSucc, Fin.val_last]

end Measure

section Attractor

variable [TopologicalSpace ι] [DiscreteTopology ι]

omit [Finite ι] in

theorem continuous_projPlusTerm (k : ℕ) : Continuous fun y : ℕ → ι => projPlusTerm A v y k := by
  have h : (fun y : ℕ → ι => projPlusTerm A v y k) =
      (fun w : Fin (k + 1) → ι =>
        planeLin (word A (List.ofFn fun j : Fin k => w (Fin.castSucc j))) (v (w (Fin.last k)))) ∘
        (fun (y : ℕ → ι) (j : Fin (k + 1)) => y j) := by
    funext y
    exact projPlusTerm_eq v y k
  rw [h]
  exact continuous_of_discreteTopology.comp (continuous_pi fun j => continuous_apply _)

theorem ContractionBound.continuous_canonicalProjPlus (hA : ContractionBound A r) :
    Continuous (canonicalProjPlus A v) := by
  obtain ⟨M, hM, hv⟩ := exists_norm_trans_le v
  refine continuous_tsum (u := fun k => r ^ k * M) (continuous_projPlusTerm v)
    ((summable_geometric_of_lt_one hA.1 hA.2.1).mul_right M) fun k y => ?_
  refine (hA.norm_toEuclideanCLM_word_le _ _).trans ?_
  rw [length_futureWordPlus]
  exact mul_le_mul_of_nonneg_left (hv _) (pow_nonneg hA.1 _)

theorem ContractionBound.isCompact_range_canonicalProjPlus (hA : ContractionBound A r) :
    IsCompact (range (canonicalProjPlus A v)) :=
  isCompact_range (hA.continuous_canonicalProjPlus v)

end Attractor

end MatrixTuple

namespace PlaneCoordinates

noncomputable def toPlane (z : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![z.1, z.2]

@[simp] theorem toPlane_zero : toPlane 0 = 0 := by
  ext j
  fin_cases j <;> rfl

theorem continuous_toPlane : Continuous toPlane := by
  unfold toPlane
  refine (PiLp.continuous_toLp 2 _).comp ?_
  refine continuous_pi fun j => ?_
  fin_cases j
  · simpa using continuous_fst
  · simpa using continuous_snd

end PlaneCoordinates

end FractalGeometry
