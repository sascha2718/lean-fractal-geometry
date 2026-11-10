module

/-
The self-affine set `X = π(Σ)` of `sec:box_like_self_affine` and `sec:two_sided_shift_space`
as the unique non-empty compact set with `X = ⋃_i φ_i(X)`, and the attractor part of
`thm:two-block-normalisation`.

The plane `ℝ × ℝ` carries the sup metric, the alphabet `ι` and `ZMod 2` carry the discrete
topology, and the sequence spaces `ℤ → ι` and `ℤ → ι × ZMod 2` carry the product topology.

* `System.Bounds.continuous_projBar`, `System.continuous_tau`, `System.continuous_omega`,
  `System.continuous_proj`: the projections `\overline{π}` and `π` and the codings `τ`, `ω`
  are continuous.
* `System.isCompact_attractor`, `System.attractor_nonempty`: `X` is compact and non-empty.
* `System.dist_phi_le`, `System.lipschitzWith_phi`, `System.injective_phi`: in the sup metric
  `φ_i` is an injective contraction with ratio `max{|a_i|, |b_i|} < 1`.
* `System.le_dist_phi`: `φ_i` expands distances by at least `min{|a_i|, |b_i|}`.
* `System.attractor_eq_iUnion`, `System.image_attractor_subset`: `eq:self_affine_set_def`.
* `System.Bounds.subset_of_invariant`, `System.eq_attractor`: Hutchinson's uniqueness, `X` is
  the only non-empty compact set with `X = ⋃_i φ_i(X)`.
* `System.attractor_sq`: `Φ^(2)` has attractor `X`, from `thm:two-block-normalisation`.
-/
public import BoxLike.Grouping
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.MetricSpace.Thickening

@[expose] public section

namespace BoxLike

open Metric

namespace System

variable {ι : Type*} (S : System ι)

/-! ### Continuity of the canonical projections -/

section Continuity

variable [TopologicalSpace ι] [DiscreteTopology ι]

/-- The derivative `g'_{𝐣|_k}` depends continuously on `𝐣`, since it depends on the symbols
`j_0, …, j_{k-1}` only. -/
theorem continuous_gDeriv_futureWord (k : ℕ) :
    Continuous fun y : ℤ → ι × ZMod 2 => S.gDeriv (futureWord y k) := by
  induction k with
  | zero => simpa using continuous_const
  | succ k ih =>
    simp only [futureWord_succ, gDeriv_append, gDeriv_cons, gDeriv_nil, mul_one]
    exact ih.mul
      ((continuous_of_discreteTopology (f := S.ratio)).comp (continuous_apply (k : ℤ)))

/-- Each term `g'_{𝐣|_k} g_{j_k}(0)` of the series defining `\overline{π}(𝐣)` depends
continuously on `𝐣`. -/
theorem continuous_projBarTerm (k : ℕ) :
    Continuous fun y : ℤ → ι × ZMod 2 => S.projBarTerm y k :=
  (S.continuous_gDeriv_futureWord k).mul
    ((continuous_of_discreteTopology (f := S.trans)).comp (continuous_apply (k : ℤ)))

variable {S} in
/-- The canonical projection `\overline{π}` of `sec:projective_system` is continuous: the
series defining it converges uniformly. -/
theorem Bounds.continuous_projBar {r M : ℝ} (hS : S.Bounds r M) : Continuous S.projBar := by
  refine continuous_tsum (u := fun k => r ^ k * M) S.continuous_projBarTerm
    ((summable_geometric_of_lt_one hS.r_nonneg hS.r_lt_one).mul_right M) fun k y => ?_
  rw [projBarTerm, Real.norm_eq_abs, abs_mul]
  have h := hS.abs_gDeriv_le (futureWord y k)
  rw [length_futureWord] at h
  exact mul_le_mul h (hS.abs_trans_le _) (abs_nonneg _) (pow_nonneg hS.r_nonneg _)

/-- The orientation cocycle `ε_n` of `eq:def_of_eps_mod2` is continuous, since it depends on
finitely many symbols. -/
theorem continuous_eps (o : ι → ZMod 2) (n : ℤ) : Continuous fun x : ℤ → ι => eps o x n := by
  rcases n with n | n
  · change Continuous fun x : ℤ → ι => ∑ j ∈ Finset.range n, o (x j)
    exact continuous_finsetSum _ fun j _ =>
      continuous_of_discreteTopology.comp (continuous_apply _)
  · change Continuous fun x : ℤ → ι => ∑ j ∈ Finset.range (n + 1), o (x (-(j + 1 : ℤ)))
    exact continuous_finsetSum _ fun j _ =>
      continuous_of_discreteTopology.comp (continuous_apply _)

/-- The coding `τ` of `eq:def_of_tau_omega` is continuous. -/
theorem continuous_tau (o : ι → ZMod 2) : Continuous (tau o) :=
  continuous_pi fun n => (continuous_apply n).prodMk (continuous_eps o n)

/-- The coding `ω` of `eq:def_of_tau_omega` is continuous. -/
theorem continuous_omega (o : ι → ZMod 2) : Continuous (omega o) :=
  continuous_pi fun n => (continuous_apply n).prodMk ((continuous_eps o n).add continuous_const)

variable {S} in
/-- The canonical projection `π` of `sec:two_sided_shift_space` is continuous, for a system
with uniform bounds. -/
theorem Bounds.continuous_proj {r M : ℝ} (hS : S.Bounds r M) : Continuous S.proj :=
  (hS.continuous_projBar.comp (continuous_tau S.o)).prodMk
    (hS.continuous_projBar.comp (continuous_omega S.o))

/-- The canonical projection `π` of `sec:two_sided_shift_space` is continuous. -/
theorem continuous_proj [Finite ι] : Continuous S.proj := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  exact hS.continuous_proj

end Continuity

/-! ### The self-affine set is compact and non-empty -/

/-- The self-affine set `X = π(Σ)` of `sec:box_like_self_affine` is compact: it is the
continuous image of the compact sequence space `Σ`. -/
theorem isCompact_attractor [Finite ι] : IsCompact S.attractor := by
  let : TopologicalSpace ι := ⊥
  have : DiscreteTopology ι := ⟨rfl⟩
  exact isCompact_range S.continuous_proj

/-- The self-affine set `X = π(Σ)` is non-empty. -/
theorem attractor_nonempty [Nonempty ι] : S.attractor.Nonempty :=
  Set.range_nonempty S.proj

/-- `eq:self_affine_set_def` for a finite system: `X = ⋃_i φ_i(X)`. -/
theorem attractor_eq_iUnion [Finite ι] : S.attractor = ⋃ i, S.phi i '' S.attractor := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  exact hS.attractor_eq_iUnion

/-- `φ_i(X) ⊆ X`, from `eq:self_affine_set_def`. -/
theorem image_attractor_subset [Finite ι] (i : ι) : S.phi i '' S.attractor ⊆ S.attractor :=
  (Set.subset_iUnion (fun i => S.phi i '' S.attractor) i).trans S.attractor_eq_iUnion.symm.subset

/-! ### The maps `φ_i` are injective contractions -/

/-- Each coordinate of two points differs by at most their distance in the sup metric. -/
theorem abs_coord_sub_le (c : ZMod 2) (z w : ℝ × ℝ) : |coord c z - coord c w| ≤ dist z w := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  unfold coord
  split_ifs
  exacts [le_max_left _ _, le_max_right _ _]

/-- In the sup metric `φ_i` contracts distances by `max{|a_i|, |b_i|}`. -/
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

/-- The contraction ratio `max{|a_i|, |b_i|}` of `φ_i` is less than one. -/
theorem max_abs_lt_one (i : ι) : max |S.a i| |S.b i| < 1 :=
  max_lt (S.abs_a_lt_one i) (S.abs_b_lt_one i)

/-- `φ_i` does not increase distances. -/
theorem dist_phi_le_dist (i : ι) (z w : ℝ × ℝ) : dist (S.phi i z) (S.phi i w) ≤ dist z w :=
  (S.dist_phi_le i z w).trans (mul_le_of_le_one_left dist_nonneg (S.max_abs_lt_one i).le)

variable {S} in
/-- Under uniform bounds every `φ_i` contracts distances by the common ratio `r`. -/
theorem Bounds.dist_phi_le {r M : ℝ} (hS : S.Bounds r M) (i : ι) (z w : ℝ × ℝ) :
    dist (S.phi i z) (S.phi i w) ≤ r * dist z w :=
  (S.dist_phi_le i z w).trans (mul_le_mul_of_nonneg_right
    (max_le (hS.abs_ratio_le (i, 0)) (hS.abs_ratio_le (i, 1))) dist_nonneg)

/-- In the sup metric of the plane, `φ_i` is Lipschitz with constant `max{|a_i|, |b_i|}`, as in
`sec:box_like_self_affine`. -/
theorem lipschitzWith_phi (i : ι) :
    LipschitzWith ⟨max |S.a i| |S.b i|, le_max_of_le_left (abs_nonneg _)⟩ (S.phi i) :=
  LipschitzWith.of_dist_le_mul (S.dist_phi_le i)

/-- In the sup metric `φ_i` expands distances by at least `α_2(A_i) = min{|a_i|, |b_i|}`; the
same bound holds for the Euclidean metric. -/
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

/-- `φ_i` maps the `ε`-neighbourhood of a set into the `ε`-neighbourhood of its image. -/
theorem image_thickening_subset (i : ι) (ε : ℝ) (A : Set (ℝ × ℝ)) :
    S.phi i '' thickening ε A ⊆ thickening ε (S.phi i '' A) := by
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨w, hw, hzw⟩ := mem_thickening_iff.1 hz
  exact mem_thickening_iff.2 ⟨S.phi i w, ⟨w, hw, rfl⟩, (S.dist_phi_le_dist i z w).trans_lt hzw⟩

/-- `φ_i` is injective, since `a_i` and `b_i` are non-zero. -/
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

/-! ### Hutchinson's uniqueness -/

variable {S} in
/-- A compact set `K` with `K ⊆ ⋃_i φ_i(K)` lies in every non-empty compact set `L` with
`φ_i(L) ⊆ L` for all `i`: the largest distance from a point of `K` to `L` is attained at some
`φ_i(y)` with `y ∈ K`, and it is at most `r` times the distance from `y` to `L`. -/
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

/-- Hutchinson's uniqueness for `eq:self_affine_set_def`: the self-affine set `X = π(Σ)` is the
only non-empty compact set `K` with `K = ⋃_i φ_i(K)`. -/
theorem eq_attractor [Finite ι] {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hne : K.Nonempty)
    (h : K = ⋃ i, S.phi i '' K) : K = S.attractor := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  have : Nonempty ι := by
    obtain ⟨z, hz⟩ := hne
    rw [h] at hz
    obtain ⟨i, -⟩ := Set.mem_iUnion.1 hz
    exact ⟨i⟩
  have hKsub : ∀ i, S.phi i '' K ⊆ K := fun i =>
    (Set.subset_iUnion (fun i => S.phi i '' K) i).trans h.symm.subset
  exact Set.Subset.antisymm
    (hS.subset_of_invariant hK h.subset S.isCompact_attractor S.attractor_nonempty
      S.image_attractor_subset)
    (hS.subset_of_invariant S.isCompact_attractor S.attractor_eq_iUnion.subset hK hne hKsub)

/-! ### The second iterate -/

/-- The maps of `Φ^(2)` send a set `A` to `φ_i(φ_j(A))`. -/
theorem sq_phi_image (p : ι × ι) (A : Set (ℝ × ℝ)) :
    S.sq.phi p '' A = S.phi p.1 '' (S.phi p.2 '' A) := by
  rw [Set.image_image]
  exact Set.image_congr fun z _ => S.sq_phi p z

/-- `thm:two-block-normalisation`, attractor part: the identity `X = ⋃_{i,j} φ_i ∘ φ_j(X)` shows
that `Φ^(2)` has attractor `X`. -/
theorem attractor_sq [Finite ι] : S.sq.attractor = S.attractor := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [attractor, attractor, Set.range_eq_empty, Set.range_eq_empty]
  · refine (S.sq.eq_attractor S.isCompact_attractor S.attractor_nonempty ?_).symm
    simp only [sq_phi_image, Set.iUnion_prod', ← Set.image_iUnion, ← S.attractor_eq_iUnion]

end System

end BoxLike
