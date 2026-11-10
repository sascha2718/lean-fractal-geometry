module

/-
The one-sided canonical projection `π^+ : Σ^+ → ℝ²` of `sec:two_sided_shift_space` (tex lines
814 to 822, `eq:canonical_projection`), the two-sided projection `π = π^+ ∘ η`, the identity
`π(Σ) = π^+(Σ^+) = X`, and `(π^+)_*μ^+ = π_*μ` for `μ = (η_*)^{-1}μ^+` (tex lines 769 and 770),
for an arbitrary affine iterated function system on `ℝ²` in the sense of
`sec:box_like_self_affine` (tex lines 555 to 567): maps `φ_i(x) = A_i x + v_i` with `‖A_i‖ < 1` in
the operator norm. Invertibility of `A_i` is not used. The plane is the Euclidean plane
`EuclideanSpace ℝ (Fin 2)`, on which `A_i` acts through `Matrix.toEuclideanCLM`, so that the
operator norm of the action is the `ℓ²` operator norm `‖A_i‖` of the library.

* `futureWordPlus`, `futureWord_eq_futureWordPlus`: the prefix `𝐢|_n` of a one-sided sequence.
* `MatrixTuple.affineMap`, `MatrixTuple.affineWord`, `MatrixTuple.affineWord_apply`: the maps
  `φ_i` and `φ_𝐢 = φ_{i_0} ∘ ⋯ ∘ φ_{i_{n-1}}`, with `φ_𝐢(x) = A_𝐢 x + φ_𝐢(0)`.
* `MatrixTuple.ContractionBound`, `MatrixTuple.exists_contractionBound`: a common bound `r < 1`
  of the norms `‖A_i‖`.
* `MatrixTuple.canonicalProjPlus`, `MatrixTuple.ContractionBound.canonicalProjPlus_eq_add_tsum`,
  `MatrixTuple.ContractionBound.tendsto_affineWord`: `eq:canonical_projection`, both the series
  `v_{i_0} + ∑_n A_{i_0} ⋯ A_{i_n} v_{i_{n+1}}` and the limit `lim_n φ_{i_0} ∘ ⋯ ∘ φ_{i_n}(0)`.
* `MatrixTuple.ContractionBound.canonicalProjPlus_eq_affineMap`: `π^+(𝐢) = φ_{i_0}(π^+(σ 𝐢))`.
* `MatrixTuple.canonicalProj`, `MatrixTuple.canonicalProj_congr`,
  `MatrixTuple.range_canonicalProj`: `π = π^+ ∘ η`, which depends only on the future
  coordinates, and `π(Σ) = π^+(Σ^+)`.
* `MatrixTuple.ContractionBound.range_canonicalProjPlus_eq_iUnion`,
  `MatrixTuple.ContractionBound.isCompact_range_canonicalProjPlus`,
  `MatrixTuple.range_canonicalProjPlus_nonempty`,
  `MatrixTuple.ContractionBound.eq_range_canonicalProjPlus`: Hutchinson's theorem
  (`eq:self_affine_set_def`): `X = π^+(Σ^+)` is the unique non-empty compact set with
  `X = ⋃_i φ_i(X)`.
* `MatrixTuple.ContractionBound.measurable_canonicalProjPlus`,
  `MatrixTuple.ContractionBound.map_canonicalProjPlus_map_eta`,
  `MatrixTuple.ContractionBound.map_canonicalProjPlus_eq_map_canonicalProj`,
  `MatrixTuple.ContractionBound.exists_ergodic_map_canonicalProjPlus_eq`: `(π^+)_*(η_*μ) = π_*μ`,
  and `(π^+)_*μ^+ = π_*μ` for `μ = (η_*)^{-1}μ^+`, with `μ` ergodic when `μ^+` is.
* `System.toPlane`, `System.planeTrans`, `System.toPlane_phiWord`,
  `System.exists_contractionBound_mat`, `System.toPlane_proj`: the box-like system of the
  library is the affine system `(S.mat, S.planeTrans)`, and its two-sided projection
  `System.proj` is `π`.
* `System.projPlus`, `System.proj_eq_projPlus_comp_eta`, `System.tendsto_phiWordPlus`,
  `System.range_projPlus`, `System.map_projPlus_eq_map_proj`: the one-sided projection of a
  box-like system, `π = π^+ ∘ η`, `eq:canonical_projection` for `π^+`, `X = π^+(Σ^+)` and
  `(π^+)_*μ^+ = π_*μ`.
-/
public import BoxLike.MatrixTuple
public import BoxLike.NaturalExtension
public import BoxLike.Attractor
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Data.List.FinRange
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set Matrix
open scoped Matrix.Norms.L2Operator

/-- The action `x ↦ B x` of a real `2 × 2` matrix on the Euclidean plane, as a continuous linear
map whose operator norm is the `ℓ²` operator norm `‖B‖` of the library. -/
noncomputable def planeLin (B : Matrix (Fin 2) (Fin 2) ℝ) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) B

/-- The action of a product is the composition of the actions. -/
theorem planeLin_mul (B B' : Matrix (Fin 2) (Fin 2) ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    planeLin (B * B') x = planeLin B (planeLin B' x) := by
  simp [planeLin, map_mul]

/-- The action of the identity matrix is the identity. -/
@[simp] theorem planeLin_one (x : EuclideanSpace ℝ (Fin 2)) : planeLin 1 x = x := by
  simp [planeLin, map_one]

/-- The operator norm of the action of `B` is `‖B‖`. -/
theorem norm_planeLin (B : Matrix (Fin 2) (Fin 2) ℝ) : ‖planeLin B‖ = ‖B‖ :=
  l2_opNorm_toEuclideanCLM B

/-- The action of `B` on the Euclidean plane is the matrix-vector product. -/
theorem planeLin_toLp (B : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    planeLin B (WithLp.toLp 2 x) = WithLp.toLp 2 (B *ᵥ x) := rfl

/-! ### Prefixes of one-sided sequences -/

section Prefix

variable {α : Type*}

/-- The prefix `𝐢|_n = i_0 ⋯ i_{n-1}` of a one-sided sequence `𝐢 ∈ Σ^+`. -/
def futureWordPlus (y : ℕ → α) (n : ℕ) : List α := (List.range n).map y

/-- `𝐢|_0` is the empty word. -/
@[simp] theorem futureWordPlus_zero (y : ℕ → α) : futureWordPlus y 0 = [] := rfl

/-- `|𝐢|_n| = n`. -/
@[simp] theorem length_futureWordPlus (y : ℕ → α) (n : ℕ) : (futureWordPlus y n).length = n := by
  simp [futureWordPlus]

/-- `𝐢|_{n+1} = 𝐢|_n i_n`. -/
theorem futureWordPlus_succ (y : ℕ → α) (n : ℕ) :
    futureWordPlus y (n + 1) = futureWordPlus y n ++ [y n] := by
  simp [futureWordPlus, List.range_succ]

/-- `𝐢|_{n+1} = i_0 (σ 𝐢)|_n`. -/
theorem futureWordPlus_succ' (y : ℕ → α) (n : ℕ) :
    futureWordPlus y (n + 1) = y 0 :: futureWordPlus (shiftPlus y) n := by
  simp only [futureWordPlus, List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

/-- The prefix of `𝐢` is the list of its first `n` symbols. -/
theorem futureWordPlus_eq_ofFn (y : ℕ → α) (n : ℕ) :
    futureWordPlus y n = List.ofFn fun j : Fin n => y j := by
  apply List.ext_getElem (by simp [futureWordPlus])
  intro k h1 h2
  simp [futureWordPlus]

/-- The prefix `𝐢|_n` of a two-sided sequence is the prefix of `η(𝐢) = 𝐢^+`. -/
theorem futureWord_eq_futureWordPlus (x : ℤ → α) (n : ℕ) :
    futureWord x n = futureWordPlus (eta x) n := rfl

/-- Two one-sided sequences that agree on `0, …, n - 1` have the same prefix of length `n`. -/
theorem futureWordPlus_congr {y y' : ℕ → α} {n : ℕ} (h : ∀ k < n, y k = y' k) :
    futureWordPlus y n = futureWordPlus y' n := by
  simp only [futureWordPlus]
  exact List.map_congr_left fun k hk => h k (List.mem_range.1 hk)

end Prefix

namespace MatrixTuple

variable {ι : Type*} (A : ι → Matrix (Fin 2) (Fin 2) ℝ) (v : ι → EuclideanSpace ℝ (Fin 2))

/-! ### The affine maps -/

/-- The affine map `φ_i(x) = A_i x + v_i` of `sec:box_like_self_affine` on the Euclidean plane. -/
noncomputable def affineMap (i : ι) (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  planeLin (A i) x + v i

/-- The composition `φ_𝐢 = φ_{i_0} ∘ ⋯ ∘ φ_{i_{n-1}}`. -/
noncomputable def affineWord : List ι → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)
  | [] => id
  | i :: w => affineMap A v i ∘ affineWord w

/-- `φ_∅` is the identity. -/
@[simp] theorem affineWord_nil : affineWord A v [] = id := rfl

/-- `φ_{i 𝐢} = φ_i ∘ φ_𝐢`. -/
@[simp] theorem affineWord_cons (i : ι) (w : List ι) :
    affineWord A v (i :: w) = affineMap A v i ∘ affineWord A v w := rfl

/-- `φ_{𝐢𝐣} = φ_𝐢 ∘ φ_𝐣`. -/
theorem affineWord_append (w w' : List ι) :
    affineWord A v (w ++ w') = affineWord A v w ∘ affineWord A v w' := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [ih, Function.comp_assoc]

/-- `A_{i 𝐢} = A_i A_𝐢`. -/
theorem word_cons_eq_mul (i : ι) (w : List ι) : word A (i :: w) = A i * word A w := rfl

/-- `φ_𝐢(x) = A_𝐢 x + φ_𝐢(0)`: the linear part of `φ_𝐢` is the product `A_𝐢`. -/
theorem affineWord_apply (w : List ι) (x : EuclideanSpace ℝ (Fin 2)) :
    affineWord A v w x = planeLin (word A w) x + affineWord A v w 0 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    simp only [affineWord_cons, Function.comp_apply, affineMap, word_cons_eq_mul, planeLin_mul]
    rw [ih, map_add, add_assoc]

/-- The difference of the images of two points under `φ_𝐢` is the image of their difference
under `A_𝐢`. -/
theorem affineWord_sub (w : List ι) (x x' : EuclideanSpace ℝ (Fin 2)) :
    affineWord A v w x - affineWord A v w x' = planeLin (word A w) (x - x') := by
  rw [affineWord_apply A v w x, affineWord_apply A v w x', map_sub]
  abel

/-! ### Contraction bounds -/

/-- A common bound `0 ≤ r < 1` of the operator norms `‖A_i‖`. -/
def ContractionBound (r : ℝ) : Prop := 0 ≤ r ∧ r < 1 ∧ ∀ i, ‖A i‖ ≤ r

/-- A finite tuple of matrices with `‖A_i‖ < 1`, as in `sec:box_like_self_affine`, has a common
contraction bound. -/
theorem exists_contractionBound [Finite ι] (hA : ∀ i, ‖A i‖ < 1) :
    ∃ r, ContractionBound A r := by
  classical
  have := Fintype.ofFinite ι
  by_cases hι : Nonempty ι
  · obtain ⟨i₀, -, h⟩ := Finset.exists_max_image Finset.univ (fun i => ‖A i‖)
      Finset.univ_nonempty
    exact ⟨‖A i₀‖, norm_nonneg _, hA i₀, fun i => h i (Finset.mem_univ _)⟩
  · exact ⟨0, le_rfl, zero_lt_one, fun i => (hι ⟨i⟩).elim⟩

/-- The norm of the identity matrix is at most `1`. -/
theorem norm_one_matrix_le : ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)‖ ≤ 1 := by
  rw [← norm_planeLin]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [planeLin_one, one_mul]

variable {A} {r : ℝ}

/-- `‖A_𝐢‖ ≤ r^{|𝐢|}`. -/
theorem ContractionBound.norm_word_le (hA : ContractionBound A r) (w : List ι) :
    ‖word A w‖ ≤ r ^ w.length := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [word_cons_eq_mul, List.length_cons, pow_succ']
    exact (l2_opNorm_mul _ _).trans (mul_le_mul (hA.2.2 i) ih (norm_nonneg _) hA.1)

/-- `|A_𝐢 x| ≤ r^{|𝐢|} |x|`. -/
theorem ContractionBound.norm_toEuclideanCLM_word_le (hA : ContractionBound A r) (w : List ι)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ‖planeLin (word A w) x‖ ≤ r ^ w.length * ‖x‖ := by
  refine (ContinuousLinearMap.le_opNorm _ x).trans ?_
  rw [norm_planeLin]
  exact mul_le_mul_of_nonneg_right (hA.norm_word_le w) (norm_nonneg _)

/-! ### The one-sided canonical projection -/

variable (A)

/-- The `k`-th term `A_{i_0} ⋯ A_{i_{k-1}} v_{i_k}` of the series of `eq:canonical_projection`;
the term `k = 0` is `v_{i_0}`. -/
noncomputable def projPlusTerm (y : ℕ → ι) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  planeLin (word A (futureWordPlus y k)) (v (y k))

/-- The one-sided canonical projection `π^+ : Σ^+ → ℝ²` of `eq:canonical_projection`,
`π^+(𝐢) = v_{i_0} + ∑_{n ≥ 0} A_{i_0} ⋯ A_{i_n} v_{i_{n+1}}`. -/
noncomputable def canonicalProjPlus (y : ℕ → ι) : EuclideanSpace ℝ (Fin 2) :=
  ∑' k, projPlusTerm A v y k

/-- The two-sided canonical projection `π = π^+ ∘ η : Σ → ℝ²` of tex lines 738 to 739. -/
noncomputable def canonicalProj (x : ℤ → ι) : EuclideanSpace ℝ (Fin 2) :=
  canonicalProjPlus A v (eta x)

/-- `π = π^+ ∘ η`. -/
theorem canonicalProj_eq_comp : canonicalProj A v = canonicalProjPlus A v ∘ eta := rfl

/-- `π(𝐢) = π^+(𝐢^+)` depends only on the future coordinates of `𝐢` (tex lines 739 and 740). -/
theorem canonicalProj_congr {x x' : ℤ → ι} (h : ∀ k : ℕ, x k = x' k) :
    canonicalProj A v x = canonicalProj A v x' := by
  unfold canonicalProj
  congr 1
  funext k
  exact h k

/-- `π(Σ) = π^+(Σ^+)` (tex line 740). -/
theorem range_canonicalProj : range (canonicalProj A v) = range (canonicalProjPlus A v) := by
  rw [canonicalProj_eq_comp, range_comp, eta_surjective.range_eq, image_univ]

/-- `φ_{𝐢|_n}(0)` is the `n`-th partial sum of the series defining `π^+(𝐢)`. -/
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

/-- The norms `|v_i|` have a common bound. -/
theorem exists_norm_trans_le : ∃ M : ℝ, 0 ≤ M ∧ ∀ i, ‖v i‖ ≤ M := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨∑ i, ‖v i‖, Finset.sum_nonneg fun i _ => norm_nonneg _, fun i => ?_⟩
  exact Finset.single_le_sum (f := fun i => ‖v i‖) (fun i _ => norm_nonneg _)
    (Finset.mem_univ i)

/-- The series of `eq:canonical_projection` converges absolutely. -/
theorem ContractionBound.summable_projPlusTerm (hA : ContractionBound A r) (y : ℕ → ι) :
    Summable (projPlusTerm A v y) := by
  obtain ⟨M, hM, hv⟩ := exists_norm_trans_le v
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hA.1 hA.2.1).mul_right M) fun k => ?_
  refine (hA.norm_toEuclideanCLM_word_le _ _).trans ?_
  rw [length_futureWordPlus]
  exact mul_le_mul_of_nonneg_left (hv _) (pow_nonneg hA.1 _)

/-- `eq:canonical_projection`, the series:
`π^+(𝐢) = v_{i_0} + ∑_{n ≥ 0} A_{i_0} ⋯ A_{i_n} v_{i_{n+1}}`. -/
theorem ContractionBound.canonicalProjPlus_eq_add_tsum (hA : ContractionBound A r)
    (y : ℕ → ι) :
    canonicalProjPlus A v y =
      v (y 0) + ∑' n, planeLin (word A (futureWordPlus y (n + 1))) (v (y (n + 1))) := by
  rw [canonicalProjPlus, (hA.summable_projPlusTerm v y).tsum_eq_zero_add]
  simp [projPlusTerm]

/-- `eq:canonical_projection`, the limit: `π^+(𝐢) = lim_n φ_{i_0} ∘ ⋯ ∘ φ_{i_n}(0)`. -/
theorem ContractionBound.tendsto_affineWord (hA : ContractionBound A r) (y : ℕ → ι) :
    Tendsto (fun n => affineWord A v (futureWordPlus y n) 0) atTop
      (𝓝 (canonicalProjPlus A v y)) := by
  simp only [affineWord_futureWordPlus_zero]
  exact (hA.summable_projPlusTerm v y).hasSum.tendsto_sum_nat

/-- `φ_{𝐢|_n}(x) → π^+(𝐢)` for every starting point `x`. -/
theorem ContractionBound.tendsto_affineWord_apply (hA : ContractionBound A r) (y : ℕ → ι)
    (x : EuclideanSpace ℝ (Fin 2)) :
    Tendsto (fun n => affineWord A v (futureWordPlus y n) x) atTop
      (𝓝 (canonicalProjPlus A v y)) := by
  have hlin : Tendsto (fun n => planeLin (word A (futureWordPlus y n)) x) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n => r ^ n * ‖x‖)
      (fun n => (hA.norm_toEuclideanCLM_word_le _ x).trans_eq ?_) ?_
    · rw [length_futureWordPlus]
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hA.1 hA.2.1).mul_const ‖x‖
  have h := hlin.add (hA.tendsto_affineWord v y)
  rw [zero_add] at h
  refine h.congr fun n => ?_
  rw [affineWord_apply A v _ x]

/-- The one-sided analogue of `π(𝐢) = φ_{i_0}(π(σ 𝐢))`: `π^+(𝐢) = φ_{i_0}(π^+(σ 𝐢))`. -/
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

/-! ### Measurability and the projected measures -/

section Measure

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

omit [Finite ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The terms of the series of `eq:canonical_projection` depend on finitely many coordinates. -/
theorem projPlusTerm_eq (y : ℕ → ι) (k : ℕ) :
    projPlusTerm A v y k =
      (fun w : Fin (k + 1) → ι =>
        planeLin (word A (List.ofFn fun j : Fin k => w (Fin.castSucc j)))
          (v (w (Fin.last k)))) (fun j => y j) := by
  simp only [projPlusTerm, futureWordPlus_eq_ofFn, Fin.val_castSucc, Fin.val_last]

/-- The terms of the series of `eq:canonical_projection` are measurable. -/
theorem measurable_projPlusTerm (k : ℕ) :
    Measurable fun y : ℕ → ι => projPlusTerm A v y k := by
  have := Fintype.ofFinite ι
  have h : (fun y : ℕ → ι => projPlusTerm A v y k) =
      (fun w : Fin (k + 1) → ι =>
        planeLin (word A (List.ofFn fun j : Fin k => w (Fin.castSucc j))) (v (w (Fin.last k)))) ∘
        (fun (y : ℕ → ι) (j : Fin (k + 1)) => y j) := by
    funext y
    exact projPlusTerm_eq v y k
  rw [h]
  exact Measurable.of_discrete.comp (Measurable.of_eval fun j => measurable_pi_apply _)

/-- The one-sided canonical projection `π^+` is measurable. -/
theorem ContractionBound.measurable_canonicalProjPlus (hA : ContractionBound A r) :
    Measurable (canonicalProjPlus A v) := by
  refine measurable_of_tendsto_metrizable
    (f := fun n y => ∑ k ∈ Finset.range n, projPlusTerm A v y k)
    (fun n => Finset.measurable_sum _ fun k _ => measurable_projPlusTerm v k) ?_
  exact tendsto_pi_nhds.2 fun y => (hA.summable_projPlusTerm v y).hasSum.tendsto_sum_nat

/-- The two-sided canonical projection `π` is measurable. -/
theorem ContractionBound.measurable_canonicalProj (hA : ContractionBound A r) :
    Measurable (canonicalProj A v) :=
  (hA.measurable_canonicalProjPlus v).comp measurable_eta

/-- `(π^+)_*(η_*μ) = π_*μ` for every measure `μ` on `Σ`. -/
theorem ContractionBound.map_canonicalProjPlus_map_eta (hA : ContractionBound A r)
    (μ : Measure (ℤ → ι)) :
    (μ.map eta).map (canonicalProjPlus A v) = μ.map (canonicalProj A v) := by
  rw [Measure.map_map (hA.measurable_canonicalProjPlus v) measurable_eta]
  rfl

/-- Tex lines 850 and 851: if `μ^+ ∈ ℳ_σ(Σ^+)` and `μ = (η_*)^{-1}μ^+ ∈ ℳ_σ(Σ)`, then
`(π^+)_*μ^+ = π_*μ`. -/
theorem ContractionBound.map_canonicalProjPlus_eq_map_canonicalProj
    (hA : ContractionBound A r)
    (ν : {ν : Measure (ℕ → ι) // IsProbabilityMeasure ν ∧ MeasurePreserving shiftPlus ν ν}) :
    (ν : Measure (ℕ → ι)).map (canonicalProjPlus A v) =
      ((mapEtaEquiv ι).symm ν : Measure (ℤ → ι)).map (canonicalProj A v) := by
  conv_lhs => rw [← map_eta_mapEtaEquiv_symm ν]
  exact hA.map_canonicalProjPlus_map_eta v _

/-- Tex lines 846 to 851: the projection of an ergodic `μ^+ ∈ ℳ_σ(Σ^+)` under `π^+` is the
projection under `π` of an ergodic `μ ∈ ℳ_σ(Σ)` with `η_*μ = μ^+`. -/
theorem ContractionBound.exists_ergodic_map_canonicalProjPlus_eq (hA : ContractionBound A r)
    {ν : Measure (ℕ → ι)} [IsProbabilityMeasure ν] (hν : Ergodic shiftPlus ν) :
    ∃ μ : Measure (ℤ → ι), IsProbabilityMeasure μ ∧ Ergodic (shift 1) μ ∧ μ.map eta = ν ∧
      ν.map (canonicalProjPlus A v) = μ.map (canonicalProj A v) := by
  obtain ⟨μ, hμ, herg, hmap⟩ := exists_ergodic_map_eta_eq hν
  refine ⟨μ, hμ, herg, hmap, ?_⟩
  rw [← hmap]
  exact hA.map_canonicalProjPlus_map_eta v μ

end Measure

/-! ### The self-affine set -/

section Attractor

variable [TopologicalSpace ι] [DiscreteTopology ι]

omit [Finite ι] in
/-- The terms of the series of `eq:canonical_projection` are continuous. -/
theorem continuous_projPlusTerm (k : ℕ) : Continuous fun y : ℕ → ι => projPlusTerm A v y k := by
  have h : (fun y : ℕ → ι => projPlusTerm A v y k) =
      (fun w : Fin (k + 1) → ι =>
        planeLin (word A (List.ofFn fun j : Fin k => w (Fin.castSucc j))) (v (w (Fin.last k)))) ∘
        (fun (y : ℕ → ι) (j : Fin (k + 1)) => y j) := by
    funext y
    exact projPlusTerm_eq v y k
  rw [h]
  exact continuous_of_discreteTopology.comp (continuous_pi fun j => continuous_apply _)

/-- The one-sided canonical projection `π^+` is continuous. -/
theorem ContractionBound.continuous_canonicalProjPlus (hA : ContractionBound A r) :
    Continuous (canonicalProjPlus A v) := by
  obtain ⟨M, hM, hv⟩ := exists_norm_trans_le v
  refine continuous_tsum (u := fun k => r ^ k * M) (continuous_projPlusTerm v)
    ((summable_geometric_of_lt_one hA.1 hA.2.1).mul_right M) fun k y => ?_
  refine (hA.norm_toEuclideanCLM_word_le _ _).trans ?_
  rw [length_futureWordPlus]
  exact mul_le_mul_of_nonneg_left (hv _) (pow_nonneg hA.1 _)

/-- The self-affine set `X = π^+(Σ^+)` is compact. -/
theorem ContractionBound.isCompact_range_canonicalProjPlus (hA : ContractionBound A r) :
    IsCompact (range (canonicalProjPlus A v)) :=
  isCompact_range (hA.continuous_canonicalProjPlus v)

end Attractor

omit [Finite ι] in
/-- The self-affine set `X = π^+(Σ^+)` of a non-empty alphabet is non-empty. -/
theorem range_canonicalProjPlus_nonempty [Nonempty ι] :
    (range (canonicalProjPlus A v)).Nonempty :=
  range_nonempty _

/-- `eq:self_affine_set_def` for `X = π^+(Σ^+)`: `X = ⋃_i φ_i(X)`. -/
theorem ContractionBound.range_canonicalProjPlus_eq_iUnion (hA : ContractionBound A r) :
    range (canonicalProjPlus A v) = ⋃ i, affineMap A v i '' range (canonicalProjPlus A v) := by
  ext z
  simp only [mem_range, mem_iUnion, mem_image, exists_exists_eq_and]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y 0, shiftPlus y, (hA.canonicalProjPlus_eq_affineMap v y).symm⟩
  · rintro ⟨i, y, rfl⟩
    refine ⟨fun k => Nat.casesOn k i y, ?_⟩
    rw [hA.canonicalProjPlus_eq_affineMap v]
    rfl

/-- Hutchinson's uniqueness (tex lines 562 to 567): `X = π^+(Σ^+)` is the only non-empty compact
set `K ⊆ ℝ²` with `K = ⋃_i φ_i(K)`. A point of `K` has a backward orbit `x = φ_{𝐢|_n}(x_n)` with
`x_n ∈ K`, which converges to `π^+(𝐢)`; conversely `φ_{𝐢|_n}(k) ∈ K` converges to `π^+(𝐢)`. -/
theorem ContractionBound.eq_range_canonicalProjPlus (hA : ContractionBound A r)
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K) (hne : K.Nonempty)
    (hinv : K = ⋃ i, affineMap A v i '' K) : K = range (canonicalProjPlus A v) := by
  have himage : ∀ (w : List ι), affineWord A v w '' K ⊆ K := by
    intro w
    induction w with
    | nil => simp
    | cons i w ih =>
      rw [affineWord_cons, image_comp]
      refine (image_mono ih).trans ?_
      conv_rhs => rw [hinv]
      exact subset_iUnion (fun i => affineMap A v i '' K) i
  apply Subset.antisymm
  · intro x hx
    have hpre : ∀ z : K, ∃ p : ι × K, (z : EuclideanSpace ℝ (Fin 2)) = affineMap A v p.1 p.2 := by
      intro z
      have hz : (z : EuclideanSpace ℝ (Fin 2)) ∈ ⋃ i, affineMap A v i '' K := hinv ▸ z.2
      rw [mem_iUnion] at hz
      obtain ⟨i, z', hz', hzz⟩ := hz
      exact ⟨(i, ⟨z', hz'⟩), hzz.symm⟩
    choose pre hpre using hpre
    let orbit : ℕ → K := fun n => Nat.rec ⟨x, hx⟩ (fun _ z => (pre z).2) n
    let y : ℕ → ι := fun n => (pre (orbit n)).1
    let pt : ℕ → EuclideanSpace ℝ (Fin 2) := fun n => (orbit n).1
    have horbit : ∀ n, x = affineWord A v (futureWordPlus y n) (pt n) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [futureWordPlus_succ, affineWord_append, Function.comp_apply, ih]
        congr 1
        exact hpre (orbit n)
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    have hlim : Tendsto (fun n => affineWord A v (futureWordPlus y n) (pt n)) atTop
        (𝓝 (canonicalProjPlus A v y)) := by
      have hdiff : Tendsto (fun n => affineWord A v (futureWordPlus y n) (pt n) -
          affineWord A v (futureWordPlus y n) 0) atTop (𝓝 0) := by
        refine squeeze_zero_norm (a := fun n => r ^ n * R) (fun n => ?_)
          (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hA.1 hA.2.1).mul_const R)
        rw [affineWord_sub, sub_zero]
        refine (hA.norm_toEuclideanCLM_word_le _ _).trans ?_
        rw [length_futureWordPlus]
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hA.1 _)
        simpa using hR (orbit n).2
      have h := hdiff.add (hA.tendsto_affineWord v y)
      rw [zero_add] at h
      exact h.congr fun n => sub_add_cancel _ _
    have hx' : Tendsto (fun _ : ℕ => x) atTop (𝓝 (canonicalProjPlus A v y)) :=
      hlim.congr fun n => (horbit n).symm
    exact ⟨y, tendsto_nhds_unique hx' tendsto_const_nhds⟩
  · rintro _ ⟨y, rfl⟩
    obtain ⟨k, hk⟩ := hne
    exact hK.isClosed.mem_of_tendsto (hA.tendsto_affineWord_apply v y k)
      (Eventually.of_forall fun n => himage _ ⟨k, hk, rfl⟩)

end MatrixTuple

/-! ### The box-like system as an affine system -/

namespace System

variable {ι : Type*} (S : System ι)

/-- The identification of the plane `ℝ × ℝ` of the library with the Euclidean plane. -/
noncomputable def toPlane (z : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![z.1, z.2]

/-- The identification of `ℝ × ℝ` with the Euclidean plane sends `0` to `0`. -/
@[simp] theorem toPlane_zero : toPlane 0 = 0 := by
  ext j
  fin_cases j <;> rfl

/-- The identification of `ℝ × ℝ` with the Euclidean plane is injective. -/
theorem toPlane_injective : Function.Injective toPlane := by
  intro z z' h
  have h' := congrArg (WithLp.ofLp (p := 2)) h
  simp only [toPlane] at h'
  have h0 := congrFun h' 0
  have h1 := congrFun h' 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  exact Prod.ext h0 h1

/-- The identification of `ℝ × ℝ` with the Euclidean plane is continuous. -/
theorem continuous_toPlane : Continuous toPlane := by
  unfold toPlane
  refine (PiLp.continuous_toLp 2 _).comp ?_
  refine continuous_pi fun j => ?_
  fin_cases j
  · simpa using continuous_fst
  · simpa using continuous_snd

/-- The identification of `ℝ × ℝ` with the Euclidean plane is measurable. -/
theorem measurable_toPlane : Measurable toPlane := continuous_toPlane.measurable

/-- The translations `v_i` of a box-like system in the Euclidean plane. -/
noncomputable def planeTrans (i : ι) : EuclideanSpace ℝ (Fin 2) := toPlane (S.v i)

/-- The affine map `φ_i` of a box-like system is `x ↦ A_i x + v_i` on the Euclidean plane. -/
theorem toPlane_phi (i : ι) (z : ℝ × ℝ) :
    toPlane (S.phi i z) = MatrixTuple.affineMap S.mat S.planeTrans i (toPlane z) := by
  have h := S.phi_eq_mulVec i z
  simp only [MatrixTuple.affineMap, planeTrans, toPlane, planeLin_toLp]
  rw [← WithLp.toLp_add, ← h]

/-- The composition `φ_𝐢` of a box-like system is that of the affine system
`(S.mat, S.planeTrans)`. -/
theorem toPlane_phiWord (w : List ι) (z : ℝ × ℝ) :
    toPlane (S.phiWord w z) = MatrixTuple.affineWord S.mat S.planeTrans w (toPlane z) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [toPlane_phi, ih]

/-- The linear parts of a box-like system have operator norm less than one. -/
theorem norm_mat_lt_one (i : ι) : ‖S.mat i‖ < 1 := by
  rw [mat, norm_boxMat]
  exact max_lt (S.abs_a_lt_one i) (S.abs_b_lt_one i)

/-- A finite box-like system has a common contraction bound. -/
theorem exists_contractionBound_mat [Finite ι] : ∃ r, MatrixTuple.ContractionBound S.mat r :=
  MatrixTuple.exists_contractionBound _ S.norm_mat_lt_one

/-- The two-sided canonical projection `System.proj` of a finite box-like system is the
canonical projection `π = π^+ ∘ η` of the affine system `(S.mat, S.planeTrans)`. -/
theorem toPlane_proj [Finite ι] (x : ℤ → ι) :
    toPlane (S.proj x) = MatrixTuple.canonicalProj S.mat S.planeTrans x := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  obtain ⟨r', hA⟩ := S.exists_contractionBound_mat
  have h1 := (continuous_toPlane.tendsto _).comp (hS.tendsto_phiWord x)
  have h2 := hA.tendsto_affineWord S.planeTrans (eta x)
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  rw [Function.comp_apply, toPlane_phiWord, futureWord_eq_futureWordPlus, toPlane_zero]

/-- The one-sided canonical projection `π^+ : Σ^+ → ℝ²` of a box-like system: the coordinates of
the projection of the affine system `(S.mat, S.planeTrans)`. -/
noncomputable def projPlus (y : ℕ → ι) : ℝ × ℝ :=
  ((MatrixTuple.canonicalProjPlus S.mat S.planeTrans y) 0,
    (MatrixTuple.canonicalProjPlus S.mat S.planeTrans y) 1)

/-- `π^+` corresponds to the one-sided canonical projection of the affine system. -/
theorem toPlane_projPlus (y : ℕ → ι) :
    toPlane (S.projPlus y) = MatrixTuple.canonicalProjPlus S.mat S.planeTrans y := by
  ext j
  fin_cases j <;> rfl

/-- `π = π^+ ∘ η` for a finite box-like system (tex lines 738 to 739). -/
theorem proj_eq_projPlus_comp_eta [Finite ι] : S.proj = S.projPlus ∘ eta := by
  funext x
  apply toPlane_injective
  rw [Function.comp_apply, toPlane_projPlus, toPlane_proj]
  rfl

/-- `eq:canonical_projection` for the one-sided projection of a finite box-like system:
`π^+(𝐢) = lim_n φ_{i_0} ∘ ⋯ ∘ φ_{i_{n-1}}(0)`. -/
theorem tendsto_phiWordPlus [Finite ι] (y : ℕ → ι) :
    Tendsto (fun n => S.phiWord (futureWordPlus y n) 0) atTop (𝓝 (S.projPlus y)) := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  have h := hS.tendsto_phiWord (padFrom 0 y)
  have hy : eta (padFrom 0 y) = y := by
    funext k
    simp [eta, padFrom]
  rw [S.proj_eq_projPlus_comp_eta, Function.comp_apply, hy] at h
  refine h.congr fun n => ?_
  rw [futureWord_eq_futureWordPlus, hy]

/-- `π(Σ) = π^+(Σ^+) = X` for a finite box-like system (tex line 740). -/
theorem range_projPlus [Finite ι] : range S.projPlus = S.attractor := by
  rw [attractor, proj_eq_projPlus_comp_eta, range_comp, eta_surjective.range_eq, image_univ]

/-- The one-sided canonical projection `π^+` of a finite box-like system is measurable. -/
theorem measurable_projPlus [Finite ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] :
    Measurable S.projPlus := by
  obtain ⟨r, hA⟩ := S.exists_contractionBound_mat
  have h := hA.measurable_canonicalProjPlus S.planeTrans
  have hc : ∀ j : Fin 2, Measurable fun z : EuclideanSpace ℝ (Fin 2) => z j := fun j =>
    (continuous_apply j |>.comp (PiLp.continuous_ofLp 2 _)).measurable
  exact ((hc 0).comp h).prodMk ((hc 1).comp h)

/-- Tex lines 850 and 851 for a finite box-like system: if `μ^+ ∈ ℳ_σ(Σ^+)` and
`μ = (η_*)^{-1}μ^+`, then `(π^+)_*μ^+ = π_*μ`. -/
theorem map_projPlus_eq_map_proj [Finite ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ν : {ν : Measure (ℕ → ι) // IsProbabilityMeasure ν ∧ MeasurePreserving shiftPlus ν ν}) :
    (ν : Measure (ℕ → ι)).map S.projPlus =
      ((mapEtaEquiv ι).symm ν : Measure (ℤ → ι)).map S.proj := by
  conv_lhs => rw [← map_eta_mapEtaEquiv_symm ν]
  rw [Measure.map_map S.measurable_projPlus measurable_eta, ← proj_eq_projPlus_comp_eta]

end System

end BoxLike
