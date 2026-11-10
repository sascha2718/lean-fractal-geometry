module

/-
Planar self-affine sets in general: the affine iterated function systems of
`sec:box_like_self_affine` (tex lines 554 to 567) with arbitrary invertible contracting linear
parts, and their canonical projection of `sec:two_sided_shift_space`
(`eq:canonical_projection`). These are the systems of "If `X` is a planar self-affine set" in
`thm:feng_entropy_as_limit`, `thm:feng_entropy_kolmogorov_sinai`, `thm:feng_entropy_zero` and
`thm:feng1`. Points of the plane are pairs, as for the box-like systems of `BoxLike/System.lean`;
the linear parts act on coordinate vectors `Fin 2 → ℝ`, as for the tuples of
`BoxLike/MatrixTuple.lean`. A box-like system is a planar system through `System.toPlanar`, and
its maps and its projection are those of the planar system.

* `toVec`, `ofVec`: coordinate vectors of points of the plane and back.
* `abs_apply_le_l2_opNorm`, `norm_mulVec_le`: entries and the action of a matrix are bounded by
  its `ℓ²` operator norm `α_1`.
* `PlanarSystem`: an affine iterated function system `φ_i(x) = A_i x + v_i` on `ℝ²` with
  `A_i ∈ GL_2(ℝ)` and `‖A_i‖ < 1`.
* `PlanarSystem.phi`, `PlanarSystem.phiWord`, `PlanarSystem.phiWord_apply`: the maps `φ_i`, the
  compositions `φ_𝐢` and their affine form.
* `PlanarSystem.projTerm`, `PlanarSystem.proj`, `PlanarSystem.tendsto_phiWord`: the canonical
  projection `π(𝐢) = v_{i_0} + ∑_n A_{i_0} ⋯ A_{i_n} v_{i_{n+1}}` and
  `π(𝐢) = lim_n φ_{i_0} ∘ ⋯ ∘ φ_{i_{n-1}}(0)` (`eq:canonical_projection`).
* `PlanarSystem.proj_eq`, `PlanarSystem.proj_congr`: `π(𝐢) = φ_{i_0}(π(σ 𝐢))`, and `π` depends
  only on the future `𝐢^+`.
* `PlanarSystem.measurable_proj`: `π` is Borel.
* `PlanarSystem.proj_sub_proj`: `π(𝐣) - π(𝐢) = A_{i_0}(π(σ 𝐣) - π(σ 𝐢))` when `i_0 = j_0`.
* `PlanarSystem.attractor`, `PlanarSystem.attractor_eq_iUnion`: `X = π(Σ)` and
  `eq:self_affine_set_def`.
* `System.toPlanar`, `System.toPlanar_mat`, `System.toPlanar_phi`, `System.toPlanar_phiWord`,
  `System.toPlanar_proj`, `System.toPlanar_attractor`: the box-like system as a planar system.
-/
public import BoxLike.MatrixTuple
public import BoxLike.Lyapunov
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.L2Operator

/-! ### Coordinate vectors -/

/-- The coordinate vector `(z_1, z_2)` of a point `z` of the plane. -/
def toVec (z : ℝ × ℝ) : Fin 2 → ℝ := ![z.1, z.2]

/-- The point of the plane with coordinates `u_0, u_1`. -/
def ofVec (u : Fin 2 → ℝ) : ℝ × ℝ := (u 0, u 1)

/-- The first coordinate of `toVec z` is `z_1`. -/
@[simp] theorem toVec_zero' (z : ℝ × ℝ) : toVec z 0 = z.1 := rfl

/-- The second coordinate of `toVec z` is `z_2`. -/
@[simp] theorem toVec_one' (z : ℝ × ℝ) : toVec z 1 = z.2 := rfl

/-- The first coordinate of `ofVec u` is `u_0`. -/
@[simp] theorem ofVec_fst (u : Fin 2 → ℝ) : (ofVec u).1 = u 0 := rfl

/-- The second coordinate of `ofVec u` is `u_1`. -/
@[simp] theorem ofVec_snd (u : Fin 2 → ℝ) : (ofVec u).2 = u 1 := rfl

/-- `toVec` inverts `ofVec`. -/
@[simp] theorem toVec_ofVec (u : Fin 2 → ℝ) : toVec (ofVec u) = u := by
  ext j; fin_cases j <;> rfl

/-- `ofVec` inverts `toVec`. -/
@[simp] theorem ofVec_toVec (z : ℝ × ℝ) : ofVec (toVec z) = z := rfl

/-- `toVec` is additive. -/
theorem toVec_add (z w : ℝ × ℝ) : toVec (z + w) = toVec z + toVec w := by
  ext j; fin_cases j <;> rfl

/-- `toVec` commutes with subtraction. -/
theorem toVec_sub (z w : ℝ × ℝ) : toVec (z - w) = toVec z - toVec w := by
  ext j; fin_cases j <;> rfl

/-- The coordinate vector of the origin is zero. -/
@[simp] theorem toVec_zero : toVec 0 = 0 := by
  ext j; fin_cases j <;> rfl

/-- `ofVec` is additive. -/
theorem ofVec_add (u u' : Fin 2 → ℝ) : ofVec (u + u') = ofVec u + ofVec u' := rfl

/-- `ofVec` commutes with subtraction. -/
theorem ofVec_sub (u u' : Fin 2 → ℝ) : ofVec (u - u') = ofVec u - ofVec u' := rfl

/-- The point with zero coordinates is the origin. -/
@[simp] theorem ofVec_zero : ofVec 0 = 0 := rfl

/-- `toVec` is injective. -/
theorem toVec_injective : Function.Injective toVec := fun z w h => by
  rw [← ofVec_toVec z, h, ofVec_toVec]

/-- The supremum norm of a point is that of its coordinate vector. -/
theorem norm_ofVec_le (u : Fin 2 → ℝ) : ‖ofVec u‖ ≤ ‖u‖ := by
  rw [Prod.norm_def]
  exact max_le (norm_le_pi_norm u 0) (norm_le_pi_norm u 1)

/-- `ofVec` is continuous. -/
theorem continuous_ofVec : Continuous ofVec := by
  unfold ofVec; fun_prop

/-- `toVec` is continuous. -/
theorem continuous_toVec : Continuous toVec := by
  unfold toVec
  refine continuous_pi fun j => ?_
  fin_cases j
  · exact continuous_fst
  · exact continuous_snd

/-! ### The operator norm -/

/-- The entries of a matrix are bounded by its `ℓ²` operator norm `‖A‖ = α_1(A)`
(`sec:Singular_value_function`). -/
theorem abs_apply_le_l2_opNorm (M : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) : |M i j| ≤ ‖M‖ := by
  have h := M.l2_opNorm_mulVec (EuclideanSpace.single j (1 : ℝ))
  rw [EuclideanSpace.single, PiLp.norm_single, norm_one, mul_one] at h
  refine le_trans (le_of_eq ?_) ((PiLp.norm_apply_le _ i).trans h)
  simp

/-- The supremum norm of `A u` is at most `2 ‖A‖ ‖u‖`, with the `ℓ²` operator norm `‖A‖`. -/
theorem norm_mulVec_le (M : Matrix (Fin 2) (Fin 2) ℝ) (u : Fin 2 → ℝ) :
    ‖M *ᵥ u‖ ≤ 2 * ‖M‖ * ‖u‖ := by
  have hM : 0 ≤ ‖M‖ := norm_nonneg M
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have h0 : |u 0| ≤ ‖u‖ := norm_le_pi_norm u 0
  have h1 : |u 1| ≤ ‖u‖ := norm_le_pi_norm u 1
  have := abs_apply_le_l2_opNorm M i 0
  have := abs_apply_le_l2_opNorm M i 1
  nlinarith [abs_nonneg (M i 0), abs_nonneg (M i 1), abs_nonneg (u 0), abs_nonneg (u 1)]

/-! ### Planar systems -/

/-- An affine iterated function system on the plane (`sec:box_like_self_affine`, tex lines 554
to 638): the maps `φ_i(x) = A_i x + v_i` with `A_i ∈ GL_2(ℝ)`, that is `det A_i ≠ 0`, of
operator norm `‖A_i‖ < 1`. The norm is the `ℓ²` operator norm, `‖A‖ = α_1(A)`. These are the
systems of "If `X` is a planar self-affine set" in `thm:feng_entropy_as_limit`,
`thm:feng_entropy_zero` and `thm:feng1`. -/
structure PlanarSystem (ι : Type*) where
  /-- The linear part `A_i`. -/
  mat : ι → Matrix (Fin 2) (Fin 2) ℝ
  /-- The translation part `v_i`. -/
  v : ι → ℝ × ℝ
  /-- The linear parts are invertible. -/
  det_ne_zero : ∀ i, (mat i).det ≠ 0
  /-- The linear parts are contractions. -/
  norm_lt_one : ∀ i, ‖mat i‖ < 1

namespace PlanarSystem

variable {ι : Type*} (P : PlanarSystem ι)

/-- The affine map `φ_i(z) = A_i z + v_i`. -/
def phi (i : ι) (z : ℝ × ℝ) : ℝ × ℝ := ofVec (P.mat i *ᵥ toVec z) + P.v i

/-- The composition `φ_𝐢 = φ_{i_0} ∘ ⋯ ∘ φ_{i_{n-1}}`. -/
def phiWord : List ι → ℝ × ℝ → ℝ × ℝ
  | [] => id
  | i :: w => P.phi i ∘ phiWord w

/-- `φ_∅` is the identity. -/
@[simp] theorem phiWord_nil : P.phiWord [] = id := rfl

/-- `φ_{i 𝐢} = φ_i ∘ φ_𝐢`. -/
@[simp] theorem phiWord_cons (i : ι) (w : List ι) :
    P.phiWord (i :: w) = P.phi i ∘ P.phiWord w := rfl

/-- `φ_i` is affine: `φ_i(z) - φ_i(w) = A_i (z - w)`. -/
theorem phi_sub_phi (i : ι) (z w : ℝ × ℝ) :
    P.phi i z - P.phi i w = ofVec (P.mat i *ᵥ toVec (z - w)) := by
  simp only [phi, toVec_sub, mulVec_sub, ofVec_sub]
  abel

/-- `φ_𝐢(z) = φ_𝐢(0) + A_𝐢 z`. -/
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

/-- The `k`-th term `A_{𝐢|_k} v_{i_k}` of the canonical projection, with `A_{𝐢|_0}` the
identity. -/
def projTerm (x : ℤ → ι) (k : ℕ) : ℝ × ℝ :=
  ofVec (MatrixTuple.word P.mat (futureWord x k) *ᵥ toVec (P.v (x k)))

/-- The canonical projection `π` of `sec:two_sided_shift_space`,
`π(𝐢) = v_{i_0} + ∑_{n ≥ 0} A_{i_0} ⋯ A_{i_n} v_{i_{n+1}}` (`eq:canonical_projection`). It
depends only on the future coordinates. -/
noncomputable def proj (x : ℤ → ι) : ℝ × ℝ := ∑' k, P.projTerm x k

/-- The partial sums of the canonical projection are `φ_{i_0} ∘ ⋯ ∘ φ_{i_{n-1}}(0)`. -/
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

/-- A uniform bound `max_i ‖A_i‖ ≤ r < 1` and `max_i ‖v_i‖ ≤ M` for a finite system. -/
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

/-- `‖A_𝐢‖ ≤ r^{|𝐢|}`, from the sub-multiplicativity of the operator norm. -/
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

/-- The terms of the canonical projection decay geometrically. -/
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

/-- The series of the canonical projection converges. -/
theorem summable_projTerm [Finite ι] (x : ℤ → ι) : Summable (P.projTerm x) := by
  obtain ⟨r, M, hr, hr1, -, hA, hv⟩ := P.exists_bounds
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hr hr1).mul_left (2 * M)) ?_
  exact fun k => P.norm_projTerm_le hr hA hv x k

/-- `eq:canonical_projection`: `π(𝐢) = lim_n φ_{i_0} ∘ ⋯ ∘ φ_{i_{n-1}}(0)`. -/
theorem tendsto_phiWord [Finite ι] (x : ℤ → ι) :
    Tendsto (fun n => P.phiWord (futureWord x n) 0) atTop (𝓝 (P.proj x)) := by
  simp only [phiWord_futureWord]
  exact (P.summable_projTerm x).hasSum.tendsto_sum_nat

/-- The maps `φ_i` are continuous. -/
theorem continuous_phi (i : ι) : Continuous (P.phi i) := by
  unfold phi
  have : Continuous fun z => P.mat i *ᵥ toVec z :=
    (Matrix.mulVecLin (P.mat i)).continuous_of_finiteDimensional.comp continuous_toVec
  exact (continuous_ofVec.comp this).add continuous_const

/-- `π(𝐢) = φ_{i_0}(π(σ 𝐢))`. -/
theorem proj_eq [Finite ι] (x : ℤ → ι) : P.proj x = P.phi (x 0) (P.proj (shift 1 x)) := by
  have h1 : Tendsto (fun n => P.phiWord (futureWord x (n + 1)) 0) atTop (𝓝 (P.proj x)) :=
    (tendsto_add_atTop_iff_nat 1).2 (P.tendsto_phiWord x)
  have h2 : Tendsto (fun n => P.phi (x 0) (P.phiWord (futureWord (shift 1 x) n) 0)) atTop
      (𝓝 (P.phi (x 0) (P.proj (shift 1 x)))) :=
    ((P.continuous_phi (x 0)).tendsto _).comp (P.tendsto_phiWord (shift 1 x))
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  rw [futureWord_succ', phiWord_cons, Function.comp_apply]

/-- `π(𝐢) = π^+(𝐢^+)` depends only on the future of `𝐢` (`sec:two_sided_shift_space`). -/
theorem proj_congr {x x' : ℤ → ι} (h : ∀ k : ℕ, x k = x' k) : P.proj x = P.proj x' := by
  unfold proj projTerm
  congr 1
  funext k
  rw [futureWord_congr x h k, h k]

/-- For sequences with the same first symbol, `π(𝐣) - π(𝐢) = A_{i_0}(π(σ 𝐣) - π(σ 𝐢))`; this is
the step `(4.11)` of Feng, Lemma 4.4, used for the partitions of `sec:entropies`. -/
theorem proj_sub_proj [Finite ι] {x y : ℤ → ι} (h : y 0 = x 0) :
    toVec (P.proj y - P.proj x) =
      P.mat (x 0) *ᵥ toVec (P.proj (shift 1 y) - P.proj (shift 1 x)) := by
  rw [P.proj_eq y, P.proj_eq x, h, P.phi_sub_phi, toVec_ofVec]

/-- The canonical projection `π` is Borel: it is the pointwise limit of the functions
`φ_{i_0} ∘ ⋯ ∘ φ_{i_{n-1}}(0)` of finitely many coordinates. -/
theorem measurable_proj [Finite ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] :
    Measurable P.proj := by
  refine measurable_of_tendsto_metrizable (f := fun n x => P.phiWord (futureWord x n) 0)
    (fun n => ?_) (tendsto_pi_nhds.2 P.tendsto_phiWord)
  simp only [futureWord_eq_ofFn_block]
  exact (Measurable.of_discrete (f := fun w : Fin n → ι => P.phiWord (List.ofFn w) 0)).comp
    (measurable_block n)

/-- The self-affine set `X = π(Σ)` (`sec:two_sided_shift_space`). -/
def attractor : Set (ℝ × ℝ) := Set.range P.proj

/-- `eq:self_affine_set_def` for `X = π(Σ)`: `X = ⋃_i φ_i(X)`. -/
theorem attractor_eq_iUnion [Finite ι] : P.attractor = ⋃ i, P.phi i '' P.attractor := by
  ext z
  simp only [attractor, Set.mem_range, Set.mem_iUnion, Set.mem_image, exists_exists_eq_and]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x 0, shift 1 x, (P.proj_eq x).symm⟩
  · rintro ⟨i, x, rfl⟩
    refine ⟨fun k => if k = 0 then i else x (k - 1), ?_⟩
    rw [P.proj_eq]
    simp only [ite_true]
    congr 1
    apply P.proj_congr
    intro k
    have : (1 : ℤ) + k ≠ 0 := by omega
    simp [this]

end PlanarSystem

/-! ### Box-like systems are planar systems -/

namespace System

variable {ι : Type*} (S : System ι)

/-- A box-like system is a planar self-affine system: its linear parts `A_i = boxMat` are
invertible, since `|det A_i| = |a_i| |b_i| > 0`, and contracting, since
`‖A_i‖ = max {|a_i|, |b_i|} < 1` (`sec:box_like_self_affine`). -/
noncomputable def toPlanar : PlanarSystem ι where
  mat := S.mat
  v := S.v
  det_ne_zero i := fun h0 => by
    have h := abs_det_boxMat (S.o i) (S.a i) (S.b i)
    rw [show boxMat (S.o i) (S.a i) (S.b i) = S.mat i from rfl, h0, abs_zero] at h
    exact mul_ne_zero (abs_ne_zero.2 (S.a_ne_zero i)) (abs_ne_zero.2 (S.b_ne_zero i)) h.symm
  norm_lt_one i := by
    rw [mat, norm_boxMat]
    exact max_lt (S.abs_a_lt_one i) (S.abs_b_lt_one i)

/-- The linear parts of the planar system of `S` are the box matrices `S.mat`. -/
@[simp] theorem toPlanar_mat : S.toPlanar.mat = S.mat := rfl

/-- The translations of the planar system of `S` are those of `S`. -/
@[simp] theorem toPlanar_v : S.toPlanar.v = S.v := rfl

/-- The maps of the planar system of `S` are the maps `φ_i` of `S`. -/
theorem toPlanar_phi (i : ι) (z : ℝ × ℝ) : S.toPlanar.phi i z = S.phi i z := by
  have h := S.phi_eq_mulVec i z
  rw [PlanarSystem.phi, toPlanar_mat, toPlanar_v]
  apply toVec_injective
  rw [toVec_add, toVec_ofVec]
  exact h.symm

/-- The compositions `φ_𝐢` of the planar system of `S` are those of `S`. -/
theorem toPlanar_phiWord (w : List ι) : S.toPlanar.phiWord w = S.phiWord w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext z
    simp only [PlanarSystem.phiWord_cons, phiWord_cons, Function.comp_apply, ih, toPlanar_phi]

/-- The canonical projection of the planar system of `S` is the projection `π` of `S`, which
the library defines through its coordinates `\overline{π} ∘ τ` and `\overline{π} ∘ ω`
(`eq:commutative_diagram`). Both are the limit of `eq:canonical_projection`. -/
theorem toPlanar_proj [Finite ι] : S.toPlanar.proj = S.proj := by
  funext x
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  refine tendsto_nhds_unique (S.toPlanar.tendsto_phiWord x) ?_
  simpa only [toPlanar_phiWord] using hS.tendsto_phiWord x

/-- The self-affine set of the planar system of `S` is the attractor of `S`. -/
theorem toPlanar_attractor [Finite ι] : S.toPlanar.attractor = S.attractor := by
  rw [PlanarSystem.attractor, toPlanar_proj, attractor]

end System

end BoxLike
