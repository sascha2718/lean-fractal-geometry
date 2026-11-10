module

/-
Falconer's upper bound for every planar self-affine set, `sec:affinity_dim`:
`eq:hausdorff_affinity_upper_bound` (tex lines 2062 to 2075) and the bound
`\overline{\dim}_M X ≤ dimaff(X)` of tex lines 510 to 510, after Falconer, Math. Proc. Cambridge
Philos. Soc. 103 (1988), Theorem 5.4, which the article cites. The systems are the planar
systems of `BoxLike/Planar/System.lean`: maps `φ_i(x) = A_i x + v_i` with `A_i ∈ GL_2(ℝ)` and
`‖A_i‖ < 1`, without any separation condition.

The covering argument runs in the Euclidean plane `EuclideanSpace ℝ (Fin 2)`, where the
self-affine set is `π^+(Σ^+)` of `BoxLike/Support/OneSidedProjection.lean`. Let `B` be a closed
ball of radius `R` containing `X`. For an invertible matrix `A` choose a unit vector `x₀` with
`|A x₀| = ‖A‖ = α_1(A)` and put `e = A x₀ / α_1(A)`. Then
`det(A x₀ | A y) = det A det(x₀ | y)`, so the component of `A y` orthogonal to `e` has modulus at
most `α_2(A) |y|` with `α_2(A) = |det A| / ‖A‖`, and its component along `e` has modulus at most
`α_1(A) |y|`: the ellipse `A(B(0, R))` lies in a rectangle with sides `2 α_1(A) R` and
`2 α_2(A) R`. Dividing the long side into `⌈α_1/α_2⌉` pieces covers it by `⌈α_1/α_2⌉` balls of
radius `α_2(A) diam(B)`, and it lies in one ball of radius `α_1(A) diam(B)`; these are the two
covers of tex lines 2065 to 2068. Fix `0 ≤ t ≤ 2` with `P(𝖠, t) < 0`, so that
`∑_n ∑_{|𝐢| = n} φ^t(A_𝐢) ≤ K`. At the scale `ρ diam(B)` every point of `X` lies in a copy
`φ_𝐢(X) ⊆ φ_𝐢(B)` whose singular value `α_k(A_𝐢)` lies between `δ₀ρ` and `ρ`, with `k = 1` for
`t ≤ 1` and `k = 2` for `1 < t ≤ 2`, and `δ₀ = min_i α_2(A_i)`. The cover of `φ_𝐢(B)` of the
matching kind has at most `2 (δ₀ρ)^{-t} φ^t(A_𝐢)` balls of radius `ρ diam(B)`, so
`N_{ρ diam(B)}(X) ≤ 2 K (δ₀ρ)^{-t}` and `\overline{\dim}_M X ≤ t`. The Hausdorff bound follows
from `\dim_H X ≤ \overline{\dim}_M X`.

The library measures planar sets in `ℝ × ℝ` with the sup metric; the coordinate map from the
Euclidean plane to `ℝ × ℝ` is `1`-Lipschitz and carries `π^+(Σ^+)` onto the attractor
`PlanarSystem.attractor`, and `System.toPlane` is `2`-Lipschitz, so the bounds hold for both
metrics.

* `Ellipse.planeLin_apply`, `Ellipse.norm_sq_eq`, `Ellipse.dot`, `Ellipse.cross`,
  `Ellipse.dot_sq_add_cross_sq`, `Ellipse.cross_planeLin`, `Ellipse.norm_sub_smul_sq`: the
  coordinate calculus of the Euclidean plane.
* `Ellipse.exists_norm_planeLin_eq`: the operator norm is attained on the unit circle.
* `Ellipse.exists_strip`: the ellipse `A(B(0, 1))` lies in a rectangle with sides `2 α_1(A)` and
  `2 α_2(A)`.
* `Ellipse.exists_centre`: `n` intervals of length `2L/n` cover `[-L, L]`.
* `Ellipse.exists_finset_cover`, `Ellipse.dist_le_norm_mul`: `c + A(B(0, R))` is covered by
  `⌈α_1/α_2⌉` balls of radius `2 α_2(A) R` and by one ball of radius `α_1(A) R`.
* `MatrixTuple.image_closedBall_subset_closedBall`,
  `MatrixTuple.exists_finset_image_closedBall_subset`: tex lines 2065 to 2068 for the ellipses
  `φ_𝐢(B)`.
* `MatrixTuple.ContractionBound.exists_canonicalProjPlus_eq_affineWord`:
  `π^+(𝐢) ∈ φ_{𝐢|_n}(X)`.
* `MatrixTuple.mul_abs_det_div_norm_le_norm_mul`, `MatrixTuple.norm_word_nil`,
  `MatrixTuple.abs_det_div_norm_word_nil`: `α_1(BC) ≥ α_1(B) α_2(C)` and `α_k(A_∅) = 1`.
* `MatrixTuple.exists_sum_svfSum_le_of_pressure_neg`: the sums
  `∑_n ∑_{|𝐢| = n} φ^t(A_𝐢)` are bounded when `P(𝖠, t) < 0`.
* `MatrixTuple.one_le_svf_of_norm`, `MatrixTuple.natCeil_le_svf_of_alpha₂`: the number of balls
  for a single word, against `φ^t(A_𝐢)`.
* `MatrixTuple.ContractionBound.externalCoveringNumber_le`: the covering count for a stopping
  rule and a per-word cover.
* `MatrixTuple.ContractionBound.upperBoxDim_le_of_pressure_neg`: `\overline{\dim}_M π^+(Σ^+) ≤ t`
  for `0 ≤ t ≤ 2` with `P(𝖠, t) < 0`.
* `ofPlane`, `lipschitzWith_ofPlane`, `lipschitzWith_toPlane`: the coordinate maps between the
  Euclidean plane and `ℝ × ℝ`.
* `PlanarSystem.attractor_eq_image`, `PlanarSystem.toPlane_image_attractor`,
  `PlanarSystem.isCompact_attractor`, `PlanarSystem.attractor_nonempty`,
  `PlanarSystem.eq_attractor`: `X = π(Σ)` is Hutchinson's self-affine set
  (`eq:self_affine_set_def`), the unique non-empty compact set with `X = ⋃_i φ_i(X)`.
* `PlanarSystem.upperBoxDim_attractor_le_of_pressure_neg_of_le_two`,
  `PlanarSystem.upperBoxDim_attractor_le_two`,
  `PlanarSystem.upperBoxDim_attractor_le_of_pressure_neg`,
  `PlanarSystem.upperBoxDim_attractor_le_dimaff`: Falconer's covering argument.
* `PlanarSystem.upperBoxDim_attractor_le`, `PlanarSystem.dimH_attractor_le`,
  `PlanarSystem.packingDim_attractor_le`: `\dim_H X ≤ \dim_P X ≤ \overline{\dim}_M X ≤
  min{2, dimaff(X)}` for every planar self-affine set (`eq:hausdorff_affinity_upper_bound`).
* `PlanarSystem.upperBoxDim_toPlane_attractor_le`, `PlanarSystem.dimH_toPlane_attractor_le`: the
  same bounds in the Euclidean plane.
* `System.upperBoxDim_attractor_le_planar`, `System.dimH_attractor_le_planar`: the box-like
  bounds of `BoxLike/FalconerBound.lean` as the specialisation to `S.toPlanar`.
-/
public import BoxLike.Planar.AffinityDim
public import BoxLike.Support.PlanarProjection
public import BoxLike.FalconerBound

@[expose] public section

namespace BoxLike

open Filter Topology Set Metric Matrix
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-! ### Ellipses in the Euclidean plane -/

namespace Ellipse

/-- The coordinates of `A x` in the Euclidean plane. -/
theorem planeLin_apply (A : Matrix (Fin 2) (Fin 2) ℝ) (x : EuclideanSpace ℝ (Fin 2))
    (i : Fin 2) : planeLin A x i = A i 0 * x 0 + A i 1 * x 1 := by
  rw [show x = WithLp.toLp 2 (WithLp.ofLp x) from rfl, planeLin_toLp]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `|x|² = x_0² + x_1²` in the Euclidean plane. -/
theorem norm_sq_eq (x : EuclideanSpace ℝ (Fin 2)) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

/-- The scalar product `⟨x, y⟩ = x_0 y_0 + x_1 y_1`. -/
def dot (x y : EuclideanSpace ℝ (Fin 2)) : ℝ := x 0 * y 0 + x 1 * y 1

/-- The determinant `det(x | y) = x_0 y_1 - x_1 y_0` of the matrix with columns `x` and `y`. -/
def cross (x y : EuclideanSpace ℝ (Fin 2)) : ℝ := x 0 * y 1 - x 1 * y 0

/-- Lagrange's identity `⟨x, y⟩² + det(x | y)² = |x|² |y|²`. -/
theorem dot_sq_add_cross_sq (x y : EuclideanSpace ℝ (Fin 2)) :
    dot x y ^ 2 + cross x y ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  rw [norm_sq_eq, norm_sq_eq, dot, cross]
  ring

/-- `|⟨x, y⟩| ≤ |x| |y|`. -/
theorem abs_dot_le (x y : EuclideanSpace ℝ (Fin 2)) : |dot x y| ≤ ‖x‖ * ‖y‖ := by
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  nlinarith [dot_sq_add_cross_sq x y, sq_nonneg (cross x y)]

/-- `|det(x | y)| ≤ |x| |y|`. -/
theorem abs_cross_le (x y : EuclideanSpace ℝ (Fin 2)) : |cross x y| ≤ ‖x‖ * ‖y‖ := by
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  nlinarith [dot_sq_add_cross_sq x y, sq_nonneg (dot x y)]

/-- `det(A x | A y) = det A det(x | y)`. -/
theorem cross_planeLin (A : Matrix (Fin 2) (Fin 2) ℝ) (x y : EuclideanSpace ℝ (Fin 2)) :
    cross (planeLin A x) (planeLin A y) = A.det * cross x y := by
  simp only [cross, planeLin_apply, det_fin_two]
  ring

/-- `det(c x | y) = c det(x | y)`. -/
theorem cross_smul_left (c : ℝ) (x y : EuclideanSpace ℝ (Fin 2)) :
    cross (c • x) y = c * cross x y := by
  simp only [cross, PiLp.smul_apply, smul_eq_mul]
  ring

/-- For a unit vector `e`, `|w - u e|² = (⟨e, w⟩ - u)² + det(e | w)²`: the coordinates of `w`
along `e` and along the orthogonal unit vector. -/
theorem norm_sub_smul_sq {e : EuclideanSpace ℝ (Fin 2)} (he : ‖e‖ = 1)
    (w : EuclideanSpace ℝ (Fin 2)) (u : ℝ) :
    ‖w - u • e‖ ^ 2 = (dot e w - u) ^ 2 + cross e w ^ 2 := by
  have h1 : e 0 ^ 2 + e 1 ^ 2 = 1 := by rw [← norm_sq_eq, he, one_pow]
  rw [norm_sq_eq]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, dot, cross]
  linear_combination (u ^ 2 - w 0 ^ 2 - w 1 ^ 2) * h1

/-- The operator norm `‖A‖ = α_1(A)` is attained on the unit circle. -/
theorem exists_norm_planeLin_eq (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ x : EuclideanSpace ℝ (Fin 2), ‖x‖ = 1 ∧ ‖planeLin A x‖ = ‖A‖ := by
  have hc : IsCompact (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := isCompact_sphere 0 1
  have hne : (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.2 zero_le_one
  obtain ⟨x₀, hx₀, hmax⟩ := hc.exists_isMaxOn hne
    (continuous_norm.comp (planeLin A).continuous).continuousOn
  have hx₀1 : ‖x₀‖ = 1 := by simpa using hx₀
  refine ⟨x₀, hx₀1, le_antisymm ?_ ?_⟩
  · have h := (planeLin A).le_opNorm x₀
    rwa [norm_planeLin, hx₀1, mul_one] at h
  · rw [← norm_planeLin]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
      have hmem : ‖y‖⁻¹ • y ∈ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hy'.ne']
      have h := hmax hmem
      simp only [Function.comp_apply, Set.mem_ofPred_eq, map_smul, norm_smul, norm_inv,
        norm_norm] at h
      rw [mul_comm]
      calc ‖planeLin A y‖ = ‖y‖ * (‖y‖⁻¹ * ‖planeLin A y‖) := by
            field_simp
        _ ≤ ‖y‖ * ‖planeLin A x₀‖ := mul_le_mul_of_nonneg_left h hy'.le

/-- The ellipse `A(B(0, 1))` of an invertible matrix lies in a rectangle with sides `2 α_1(A)`
and `2 α_2(A)`: for the unit vector `e = A x₀ / ‖A‖` along the major axis,
`|⟨e, A y⟩| ≤ α_1(A) |y|` and `|det(e | A y)| ≤ α_2(A) |y|`, with `α_1(A) = ‖A‖` and
`α_2(A) = |det A| / ‖A‖` (`sec:Singular_value_function`). -/
theorem exists_strip {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0) :
    ∃ e : EuclideanSpace ℝ (Fin 2), ‖e‖ = 1 ∧ ∀ y : EuclideanSpace ℝ (Fin 2),
      |dot e (planeLin A y)| ≤ ‖A‖ * ‖y‖ ∧ |cross e (planeLin A y)| ≤ |A.det| / ‖A‖ * ‖y‖ := by
  obtain ⟨x₀, hx₀, hAx₀⟩ := exists_norm_planeLin_eq A
  have hn : 0 < ‖A‖ := MatrixTuple.norm_pos_of_det_ne_zero hA
  have he : ‖‖A‖⁻¹ • planeLin A x₀‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, hAx₀, inv_mul_cancel₀ hn.ne']
  refine ⟨‖A‖⁻¹ • planeLin A x₀, he, fun y => ⟨?_, ?_⟩⟩
  · refine (abs_dot_le _ _).trans ?_
    rw [he, one_mul, ← norm_planeLin]
    exact (planeLin A).le_opNorm y
  · rw [cross_smul_left, cross_planeLin, abs_mul, abs_mul, abs_inv, abs_norm]
    have h := abs_cross_le x₀ y
    rw [hx₀, one_mul] at h
    calc ‖A‖⁻¹ * (|A.det| * |cross x₀ y|) ≤ ‖A‖⁻¹ * (|A.det| * ‖y‖) := by gcongr
      _ = |A.det| / ‖A‖ * ‖y‖ := by ring

/-- The `n` closed intervals of length `2L/n` with centres `-L + (2k + 1) L/n`, `k < n`, cover
`[-L, L]`. -/
theorem exists_centre {n : ℕ} (hn : 0 < n) {L u : ℝ} (hL : 0 ≤ L) (hu : |u| ≤ L) :
    ∃ k ∈ Finset.range n, |u - (-L + (2 * k + 1) * (L / n))| ≤ L / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rcases hL.lt_or_eq with hL | hL
  · set h : ℝ := 2 * L / n with hh
    have hh0 : 0 < h := by positivity
    set s : ℝ := (u + L) / h with hs
    have hs0 : 0 ≤ s := div_nonneg (by linarith [neg_abs_le u]) hh0.le
    have hsn : s ≤ n := by
      rw [hs, div_le_iff₀ hh0, hh]
      field_simp
      linarith [le_abs_self u]
    have hu' : u = -L + s * h := by
      rw [hs, div_mul_cancel₀ _ hh0.ne']
      ring
    obtain ⟨k, hk, hk0, hk1⟩ : ∃ k : ℕ, k < n ∧ (k : ℝ) ≤ s ∧ s ≤ k + 1 := by
      by_cases hfl : ⌊s⌋₊ < n
      · exact ⟨⌊s⌋₊, hfl, Nat.floor_le hs0, (Nat.lt_floor_add_one s).le⟩
      · refine ⟨n - 1, by omega, ?_, ?_⟩
        · have h1 : (n : ℝ) ≤ ⌊s⌋₊ := by exact_mod_cast not_lt.1 hfl
          have h2 := Nat.floor_le hs0
          rw [Nat.cast_sub (by omega), Nat.cast_one]
          linarith
        · rw [Nat.cast_sub (by omega), Nat.cast_one]
          linarith
    refine ⟨k, Finset.mem_range.2 hk, ?_⟩
    have hLn : L / n = h / 2 := by rw [hh]; ring
    rw [hLn, hu', abs_le]
    constructor <;> nlinarith
  · subst hL
    refine ⟨0, Finset.mem_range.2 hn, ?_⟩
    have : u = 0 := abs_nonpos_iff.1 hu
    simp [this]

/-- Tex lines 2162 to 2165: the ellipse `c + A(B(0, R))` of an invertible matrix is covered by
`⌈α_1(A)/α_2(A)⌉` balls of radius `α_2(A) · 2R`, where `α_1(A) = ‖A‖` and
`α_2(A) = |det A| / ‖A‖`. The rectangle of `exists_strip` with sides `2 α_1(A) R` and
`2 α_2(A) R` is cut into `n = ⌈α_1/α_2⌉` pieces with sides at most `2 α_2(A) R`, whose half
diagonals are at most `√2 α_2(A) R`. -/
theorem exists_finset_cover {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0)
    (c : EuclideanSpace ℝ (Fin 2)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ G : Finset (EuclideanSpace ℝ (Fin 2)), G.card ≤ ⌈‖A‖ / (|A.det| / ‖A‖)⌉₊ ∧
      ∀ y : EuclideanSpace ℝ (Fin 2), ‖y‖ ≤ R →
        ∃ g ∈ G, dist (c + planeLin A y) g ≤ |A.det| / ‖A‖ * (2 * R) := by
  classical
  obtain ⟨e, he, hstrip⟩ := exists_strip hA
  have ha1 : 0 < ‖A‖ := MatrixTuple.norm_pos_of_det_ne_zero hA
  have ha2 : 0 < |A.det| / ‖A‖ := MatrixTuple.abs_det_div_norm_pos hA
  set a₁ := ‖A‖ with ha₁
  set a₂ := |A.det| / ‖A‖ with ha₂
  set n := ⌈a₁ / a₂⌉₊ with hn
  have hn0 : 0 < n := Nat.ceil_pos.2 (div_pos ha1 ha2)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  set L := a₁ * R with hL
  have hL0 : 0 ≤ L := mul_nonneg ha1.le hR
  have hLn : L / n ≤ a₂ * R := by
    have h1 : a₁ / a₂ ≤ n := Nat.le_ceil _
    rw [div_le_iff₀ ha2] at h1
    rw [div_le_iff₀ hn', hL]
    nlinarith
  refine ⟨(Finset.range n).image fun k : ℕ => c + (-L + (2 * k + 1) * (L / n)) • e,
    Finset.card_image_le.trans (Finset.card_range n).le, fun y hy => ?_⟩
  obtain ⟨h1, h2⟩ := hstrip y
  have hu : |dot e (planeLin A y)| ≤ L :=
    h1.trans (mul_le_mul_of_nonneg_left hy ha1.le)
  have hv : |cross e (planeLin A y)| ≤ a₂ * R :=
    h2.trans (mul_le_mul_of_nonneg_left hy ha2.le)
  obtain ⟨k, hk, hku⟩ := exists_centre hn0 hL0 hu
  refine ⟨_, Finset.mem_image_of_mem _ hk, ?_⟩
  rw [dist_add_left, dist_eq_norm]
  have hsq := norm_sub_smul_sq he (planeLin A y) (-L + (2 * k + 1) * (L / n))
  have hb : 0 ≤ a₂ * (2 * R) := by positivity
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) hb two_ne_zero).1 ?_
  rw [hsq]
  have e1 : (dot e (planeLin A y) - (-L + (2 * k + 1) * (L / n))) ^ 2 ≤ (a₂ * R) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hku.trans hLn) 2
  have e2 : cross e (planeLin A y) ^ 2 ≤ (a₂ * R) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hv 2
  nlinarith [sq_nonneg (a₂ * R)]

/-- Tex lines 2162 and 2163: the ellipse `c + A(B(0, R))` lies in one ball of radius
`α_1(A) R`. -/
theorem dist_le_norm_mul (A : Matrix (Fin 2) (Fin 2) ℝ) (c y : EuclideanSpace ℝ (Fin 2))
    {R : ℝ} (hy : ‖y‖ ≤ R) : dist (c + planeLin A y) c ≤ ‖A‖ * R := by
  rw [dist_eq_norm, add_sub_cancel_left, ← norm_planeLin]
  exact ((planeLin A).le_opNorm y).trans (mul_le_mul_of_nonneg_left hy (norm_nonneg _))

end Ellipse

/-! ### The ellipses `φ_𝐢(B)` and the copies of `X` -/

namespace MatrixTuple

variable {ι : Type*} {A : ι → Matrix (Fin 2) (Fin 2) ℝ} (v : ι → EuclideanSpace ℝ (Fin 2))

/-- Tex lines 2162 and 2163: for a closed ball `B`, the ellipse `φ_𝐢(B)` is covered by one ball
of radius `α_1(A_𝐢) diam(B)`. -/
theorem image_closedBall_subset_closedBall (w : List ι) (b : EuclideanSpace ℝ (Fin 2)) {R : ℝ}
    (hR : 0 ≤ R) :
    affineWord A v w '' closedBall b R ⊆
      closedBall (affineWord A v w b) (‖word A w‖ * diam (closedBall b R)) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_closedBall, diam_closedBall_eq b hR]
  have h := Ellipse.dist_le_norm_mul (word A w) (affineWord A v w b) (x - b)
    (show ‖x - b‖ ≤ 2 * R by rw [← dist_eq_norm]; linarith [mem_closedBall.1 hx])
  rwa [← affineWord_sub, add_sub_cancel] at h

/-- Tex lines 2162 to 2165: for a closed ball `B` and an invertible tuple, the ellipse `φ_𝐢(B)`
is covered by `⌈α_1(A_𝐢)/α_2(A_𝐢)⌉` balls of radius `α_2(A_𝐢) diam(B)`, with
`α_1(A_𝐢) = ‖A_𝐢‖` and `α_2(A_𝐢) = |det A_𝐢| / ‖A_𝐢‖`. -/
theorem exists_finset_image_closedBall_subset (hA : ∀ i, (A i).det ≠ 0) (w : List ι)
    (b : EuclideanSpace ℝ (Fin 2)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ G : Finset (EuclideanSpace ℝ (Fin 2)),
      G.card ≤ ⌈‖word A w‖ / (|(word A w).det| / ‖word A w‖)⌉₊ ∧
      affineWord A v w '' closedBall b R ⊆
        ⋃ g ∈ G, closedBall g (|(word A w).det| / ‖word A w‖ * diam (closedBall b R)) := by
  obtain ⟨G, hG, hcov⟩ := Ellipse.exists_finset_cover (Convexity.det_word_ne_zero hA w)
    (affineWord A v w b) hR
  refine ⟨G, hG, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨g, hg, hgx⟩ := hcov (x - b) (by rw [← dist_eq_norm]; exact mem_closedBall.1 hx)
  rw [← affineWord_sub, add_sub_cancel] at hgx
  rw [diam_closedBall_eq b hR]
  exact mem_iUnion₂.2 ⟨g, hg, hgx⟩

variable {v} {r : ℝ}

/-- `π^+(𝐢) = φ_{𝐢|_n}(π^+(𝐣))` for some `𝐣`: the point `π^+(𝐢)` lies in the copy
`φ_{𝐢|_n}(X)` of the self-affine set (tex lines 2063 and 2064). -/
theorem ContractionBound.exists_canonicalProjPlus_eq_affineWord [Finite ι]
    (hA : ContractionBound A r)
    (n : ℕ) (y : ℕ → ι) :
    ∃ y', canonicalProjPlus A v y = affineWord A v (futureWordPlus y n) (canonicalProjPlus A v y')
    := by
  induction n generalizing y with
  | zero => exact ⟨y, rfl⟩
  | succ n ih =>
    obtain ⟨y', hy'⟩ := ih (shiftPlus y)
    refine ⟨y', ?_⟩
    rw [hA.canonicalProjPlus_eq_affineMap v y, futureWordPlus_succ', affineWord_cons,
      Function.comp_apply, hy']

/-! ### Singular values along words -/

/-- `α_1(BC) ≥ α_1(B) α_2(C)` for an invertible matrix `C`, since
`‖B‖ ≤ ‖BC‖ ‖C⁻¹‖ = ‖BC‖ / α_2(C)`. -/
theorem mul_abs_det_div_norm_le_norm_mul (B : Matrix (Fin 2) (Fin 2) ℝ)
    {C : Matrix (Fin 2) (Fin 2) ℝ} (hC : C.det ≠ 0) : ‖B‖ * (|C.det| / ‖C‖) ≤ ‖B * C‖ := by
  have hn := norm_pos_of_det_ne_zero hC
  have hd := abs_pos.2 hC
  have h : ‖B‖ ≤ ‖B * C‖ * ‖C⁻¹‖ := by
    calc ‖B‖ = ‖B * C * C⁻¹‖ := by
          rw [Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_iff_ne_zero.2 hC)]
      _ ≤ ‖B * C‖ * ‖C⁻¹‖ := l2_opNorm_mul _ _
  rw [norm_inv_eq_norm_div_abs_det] at h
  calc ‖B‖ * (|C.det| / ‖C‖) ≤ ‖B * C‖ * (‖C‖ / |C.det|) * (|C.det| / ‖C‖) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = ‖B * C‖ := by field_simp

variable (A) in
/-- `α_1(A_∅) = ‖1‖ = 1`. -/
theorem norm_word_nil : ‖word A []‖ = 1 := by
  rw [word_nil]
  refine le_antisymm norm_one_matrix_le ?_
  have h := abs_det_le_norm_sq (1 : Matrix (Fin 2) (Fin 2) ℝ)
  rw [det_one, abs_one] at h
  nlinarith [norm_nonneg (1 : Matrix (Fin 2) (Fin 2) ℝ)]

variable (A) in
/-- `α_2(A_∅) = |det 1| / ‖1‖ = 1`. -/
theorem abs_det_div_norm_word_nil : |(word A []).det| / ‖word A []‖ = 1 := by
  rw [norm_word_nil, word_nil, det_one, abs_one, div_one]

/-! ### The sums over words -/

variable [Fintype ι]

/-- For `s ≥ 0` with `P(𝖠, s) < 0` the partial sums of `∑_n ∑_{|𝐢| = n} φ^s(A_𝐢)` are bounded,
since `∑_{|𝐢| = n} φ^s(A_𝐢) ≤ e^{nP(𝖠, s)/2}` for large `n`. -/
theorem exists_sum_svfSum_le_of_pressure_neg [Nonempty ι] (hA : ∀ i, (A i).det ≠ 0) {s : ℝ}
    (hs : 0 ≤ s) (hP : pressure A s < 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℕ, ∑ n ∈ Finset.range L, svfSum A s n ≤ K := by
  have ht := Convexity.tendsto_pressure hA hs
  have hq0 : 0 < Real.exp (pressure A s / 2) := Real.exp_pos _
  have hq1 : Real.exp (pressure A s / 2) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hev : ∀ᶠ n : ℕ in atTop, ‖svfSum A s n‖ ≤ Real.exp (pressure A s / 2) ^ n := by
    filter_upwards [ht.eventually (gt_mem_nhds (show pressure A s < pressure A s / 2 by linarith)),
      eventually_gt_atTop 0] with n hn hn0
    have hpos := Convexity.svfSum_pos hA hs n
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [div_lt_iff₀ hn'] at hn
    rw [Real.norm_of_nonneg hpos.le, ← Real.exp_nat_mul]
    calc svfSum A s n = Real.exp (Real.log (svfSum A s n)) := (Real.exp_log hpos).symm
      _ ≤ Real.exp (n * (pressure A s / 2)) := Real.exp_le_exp.2 (by linarith)
  have hsum : Summable fun n => svfSum A s n :=
    Summable.of_norm_bounded_eventually_nat (summable_geometric_of_lt_one hq0.le hq1) hev
  have hle : ∀ L : ℕ, ∑ n ∈ Finset.range L, svfSum A s n ≤ ∑' n, svfSum A s n :=
    fun L => hsum.sum_le_tsum (Finset.range L) fun n _ => (Convexity.svfSum_pos hA hs n).le
  refine ⟨∑' n, svfSum A s n + 1, ?_, fun L => (hle L).trans (le_add_of_nonneg_right zero_le_one)⟩
  have h0 := hle 0
  rw [Finset.range_zero, Finset.sum_empty] at h0
  linarith

omit [Fintype ι] in
/-- For `0 ≤ t ≤ 1` and `δ₀ρ ≤ α_1(B)` the single ball covering the ellipse of `B` is at most
`2 (δ₀ρ)^{-t} φ^t(B)` balls, since `φ^t(B) = α_1(B)^t`. -/
theorem one_le_svf_of_norm {B : Matrix (Fin 2) (Fin 2) ℝ} {t δρ : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hδρ : 0 < δρ) (h : δρ ≤ ‖B‖) : (1 : ℝ) ≤ 2 * δρ ^ (-t) * svf t B := by
  have hsvf : svf t B = ‖B‖ ^ t := by rw [svf, ite_eq_left ht1]
  have hpow : δρ ^ (-t) * δρ ^ t = 1 := by
    rw [Real.rpow_neg hδρ.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hδρ t).ne']
  calc (1 : ℝ) ≤ 2 * (δρ ^ (-t) * δρ ^ t) := by rw [hpow]; norm_num
    _ ≤ 2 * (δρ ^ (-t) * ‖B‖ ^ t) := by gcongr
    _ = 2 * δρ ^ (-t) * svf t B := by rw [hsvf, mul_assoc]

omit [Fintype ι] in
/-- For `1 < t ≤ 2` and `δ₀ρ ≤ α_2(B)` the `⌈α_1(B)/α_2(B)⌉` balls covering the ellipse of `B`
are at most `2 α_1(B)/(δ₀ρ) ≤ 2 (δ₀ρ)^{-t} φ^t(B)`, since `φ^t(B) = α_1(B) α_2(B)^{t-1}`. -/
theorem natCeil_le_svf_of_alpha₂ {B : Matrix (Fin 2) (Fin 2) ℝ} (hB : B.det ≠ 0) {t δρ : ℝ}
    (ht1 : 1 < t) (ht2 : t ≤ 2) (hδρ : 0 < δρ) (h : δρ ≤ |B.det| / ‖B‖) :
    (⌈‖B‖ / (|B.det| / ‖B‖)⌉₊ : ℝ) ≤ 2 * δρ ^ (-t) * svf t B := by
  have hn := norm_pos_of_det_ne_zero hB
  have h2 := abs_det_div_norm_pos hB
  have h21 := abs_det_div_norm_le_norm hB
  have hq1 : 1 ≤ ‖B‖ / (|B.det| / ‖B‖) := (one_le_div h2).2 h21
  have hceil : (⌈‖B‖ / (|B.det| / ‖B‖)⌉₊ : ℝ) ≤ 2 * (‖B‖ / (|B.det| / ‖B‖)) := by
    have := Nat.ceil_lt_add_one (zero_le_one.trans hq1)
    linarith
  have hq : ‖B‖ / (|B.det| / ‖B‖) ≤ ‖B‖ / δρ := div_le_div_of_nonneg_left hn.le hδρ h
  have hsvf : ‖B‖ * δρ ^ (t - 1) ≤ svf t B := by
    rw [svf_eq_rpow_mul_rpow hB, svfExp_eq_one ht1.le ht2, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδρ.le h (by linarith)) hn.le
  have hpow : δρ ^ (-t) * δρ ^ (t - 1) = δρ⁻¹ := by
    rw [← Real.rpow_add hδρ, show -t + (t - 1) = -1 by ring, Real.rpow_neg_one]
  calc (⌈‖B‖ / (|B.det| / ‖B‖)⌉₊ : ℝ) ≤ 2 * (‖B‖ / δρ) := hceil.trans (by linarith)
    _ = 2 * δρ ^ (-t) * (‖B‖ * δρ ^ (t - 1)) := by
        rw [div_eq_mul_inv, ← hpow]
        ring
    _ ≤ 2 * δρ ^ (-t) * svf t B := mul_le_mul_of_nonneg_left hsvf (by positivity)

/-! ### The covering count -/

/-- The covering argument for a stopping rule. Let `f` be `α_1` or `α_2` along words, or any
function of words with `f(∅) = 1`, `f(𝐢j) ≥ δ₀ f(𝐢)` and `f(𝐢) ≤ r^{|𝐢|}`, and let the copy
`φ_𝐢(X)` of every word with `δ₀ρ ≤ f(𝐢) ≤ ρ` be covered by at most `B φ^t(A_𝐢)` balls of
radius `ε`. If `∑_{n < L} ∑_{|𝐢| = n} φ^t(A_𝐢) ≤ K` for all `L`, then `N_ε(X) ≤ BK`: every point
of `X` lies in a copy `φ_𝐢(X)` with `δ₀ρ ≤ f(𝐢) ≤ ρ`. -/
theorem ContractionBound.externalCoveringNumber_le (hA : ContractionBound A r)
    {f : List ι → ℝ} {t K B ρ δ₀ ε : ℝ} (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hε : 0 ≤ ε) (hf0 : f [] = 1) (hfδ : ∀ w j, δ₀ * f w ≤ f (w ++ [j]))
    (hfr : ∀ w, f w ≤ r ^ w.length)
    (hK : ∀ L, ∑ n ∈ Finset.range L, svfSum A t n ≤ K) (hB0 : 0 ≤ B)
    (hcov : ∀ w, δ₀ * ρ ≤ f w → f w ≤ ρ → ∃ G : Finset (EuclideanSpace ℝ (Fin 2)),
      (G.card : ℝ) ≤ B * svf t (word A w) ∧
        affineWord A v w '' range (canonicalProjPlus A v) ⊆ ⋃ g ∈ G, closedBall g ε) :
    (externalCoveringNumber ε.toNNReal (range (canonicalProjPlus A v)) : ℝ≥0∞) ≤
      ENNReal.ofReal (B * K) := by
  classical
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one (mul_pos hδ₀ hρ) hA.2.1
  have hG : ∀ (n : ℕ) (w : Fin n → ι), ∃ G : Finset (EuclideanSpace ℝ (Fin 2)),
      δ₀ * ρ ≤ f (List.ofFn w) → f (List.ofFn w) ≤ ρ →
        (G.card : ℝ) ≤ B * svf t (word A (List.ofFn w)) ∧
          affineWord A v (List.ofFn w) '' range (canonicalProjPlus A v) ⊆
            ⋃ g ∈ G, closedBall g ε := by
    intro n w
    by_cases h : δ₀ * ρ ≤ f (List.ofFn w) ∧ f (List.ofFn w) ≤ ρ
    · obtain ⟨G, hG⟩ := hcov _ h.1 h.2
      exact ⟨G, fun _ _ => hG⟩
    · exact ⟨∅, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose G hG using hG
  set W : (n : ℕ) → Finset (Fin n → ι) := fun n => Finset.univ.filter fun w =>
    δ₀ * ρ ≤ f (List.ofFn w) ∧ f (List.ofFn w) ≤ ρ with hW
  set C : Finset (EuclideanSpace ℝ (Fin 2)) :=
    (Finset.range L).biUnion fun n => (W n).biUnion fun w => G n w with hC
  have hcover : IsCover ε.toNNReal (range (canonicalProjPlus A v))
      (C : Set (EuclideanSpace ℝ (Fin 2))) := by
    rw [isCover_iff_subset_iUnion_closedBall, Real.coe_toNNReal _ hε]
    rintro _ ⟨y, rfl⟩
    have hex : ∃ n, f (futureWordPlus y n) ≤ ρ := by
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hρ hA.2.1
      refine ⟨k, (hfr _).trans ?_⟩
      rw [length_futureWordPlus]
      exact hk.le
    obtain ⟨n, hn1, hn2⟩ := exists_stop (F := fun n => f (futureWordPlus y n)) hδ₀.le hδ₀1
      hρ.le (by rw [futureWordPlus_zero, hf0]; exact hρ1)
      (fun n => by rw [futureWordPlus_succ]; exact hfδ _ _) hex
    have hlen : n < L := by
      by_contra h
      rw [not_lt] at h
      have h1 := hfr (futureWordPlus y n)
      rw [length_futureWordPlus] at h1
      have h2 : r ^ n ≤ r ^ L := pow_le_pow_of_le_one hA.1 hA.2.1.le h
      linarith
    obtain ⟨y', hy'⟩ := hA.exists_canonicalProjPlus_eq_affineWord (v := v) n y
    simp only [futureWordPlus_eq_ofFn] at hn1 hn2 hy'
    have hmem : canonicalProjPlus A v y ∈
        affineWord A v (List.ofFn fun j : Fin n => y j) '' range (canonicalProjPlus A v) :=
      ⟨_, ⟨y', rfl⟩, hy'.symm⟩
    obtain ⟨g, hg, hgy⟩ := mem_iUnion₂.1 ((hG n _ hn1 hn2).2 hmem)
    refine mem_iUnion₂.2 ⟨g, ?_, hgy⟩
    rw [Finset.mem_coe, hC, Finset.mem_biUnion]
    exact ⟨n, Finset.mem_range.2 hlen, Finset.mem_biUnion.2 ⟨fun j : Fin n => y j,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hn1, hn2⟩, hg⟩⟩
  have hsum : (C.card : ℝ) ≤ B * K := by
    calc (C.card : ℝ)
        ≤ ∑ n ∈ Finset.range L, ∑ w ∈ W n, ((G n w).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le.trans
            (Finset.sum_le_sum fun n _ => Finset.card_biUnion_le)
      _ ≤ ∑ n ∈ Finset.range L, ∑ w ∈ W n, B * svf t (word A (List.ofFn w)) := by
          refine Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun w hw => ?_
          rw [hW, Finset.mem_filter] at hw
          exact (hG n w hw.2.1 hw.2.2).1
      _ ≤ ∑ n ∈ Finset.range L, B * svfSum A t n := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [svfSum, ← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) fun w _ _ => svf_nonneg _ _) hB0
      _ = B * ∑ n ∈ Finset.range L, svfSum A t n := (Finset.mul_sum _ _ _).symm
      _ ≤ B * K := mul_le_mul_of_nonneg_left (hK L) hB0
  calc (externalCoveringNumber ε.toNNReal (range (canonicalProjPlus A v)) : ℝ≥0∞)
      ≤ (C.card : ℝ≥0∞) := by
        have h := hcover.externalCoveringNumber_le_encard
        rw [Set.encard_coe_eq_coe_finsetCard] at h
        exact_mod_cast ENat.toENNReal_le.2 h
    _ = ENNReal.ofReal (C.card : ℝ) := (ENNReal.ofReal_natCast _).symm
    _ ≤ ENNReal.ofReal (B * K) := ENNReal.ofReal_le_ofReal hsum

/-! ### Falconer's bound in the Euclidean plane -/

/-- Falconer's covering argument, Theorem 5.4 of his 1988 article, for `0 ≤ t ≤ 2` and every
affine iterated function system in the Euclidean plane with invertible contracting linear parts:
`\overline{\dim}_M X ≤ t` for `X = π^+(Σ^+)` when `P(𝖠, t) < 0`. The stopping rule is
`α_1(A_𝐢) ≤ ρ` with one ball per word for `t ≤ 1`, and `α_2(A_𝐢) ≤ ρ` with `⌈α_1/α_2⌉` balls
per word for `1 < t ≤ 2`; `N_{ρ diam(B)}(X) ≤ 2 K (δ₀ρ)^{-t}` by
`ContractionBound.externalCoveringNumber_le`. -/
theorem ContractionBound.upperBoxDim_le_of_pressure_neg [Nonempty ι]
    (hA : ContractionBound A r) (hdet : ∀ i, (A i).det ≠ 0) {t : ℝ≥0} (ht2 : (t : ℝ) ≤ 2)
    (hP : pressure A t < 0) : upperBoxDim (range (canonicalProjPlus A v)) ≤ t := by
  obtain ⟨K, hK0, hK⟩ := exists_sum_svfSum_le_of_pressure_neg hdet t.coe_nonneg hP
  obtain ⟨δ₀, R', hδ₀, -, hδ₀A, -⟩ := Convexity.exists_singular_bounds hdet
  obtain ⟨i⟩ : Nonempty ι := inferInstance
  have hδ₀1 : δ₀ ≤ 1 :=
    ((hδ₀A i).trans (abs_det_div_norm_le_norm (hdet i))).trans ((hA.2.2 i).trans hA.2.1.le)
  let : TopologicalSpace ι := ⊥
  have : DiscreteTopology ι := ⟨rfl⟩
  obtain ⟨R₀, hR₀⟩ := (hA.isCompact_range_canonicalProjPlus v).isBounded.subset_closedBall 0
  set R := max R₀ 1 with hR
  have hR1 : 1 ≤ R := le_max_right _ _
  have hR0 : 0 < R := one_pos.trans_le hR1
  have hXB : range (canonicalProjPlus A v) ⊆ closedBall 0 R :=
    hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  set D := diam (closedBall (0 : EuclideanSpace ℝ (Fin 2)) R) with hD
  have hD2 : D = 2 * R := diam_closedBall_eq 0 hR0.le
  have hD0 : 0 < D := by rw [hD2]; positivity
  have hstep : ∀ w j, δ₀ * ‖word A w‖ ≤ ‖word A (w ++ [j])‖ := fun w j => by
    rw [word_append, Convexity.word_cons, word_nil, mul_one, mul_comm]
    exact (mul_le_mul_of_nonneg_left (hδ₀A j) (norm_nonneg _)).trans
      (mul_abs_det_div_norm_le_norm_mul _ (hdet j))
  have hstep₂ : ∀ w j, δ₀ * (|(word A w).det| / ‖word A w‖) ≤
      |(word A (w ++ [j])).det| / ‖word A (w ++ [j])‖ := fun w j => by
    rw [word_append, mul_comm]
    have hj : |(word A [j]).det| / ‖word A [j]‖ = |(A j).det| / ‖A j‖ := by
      rw [Convexity.word_cons, word_nil, mul_one]
    refine le_trans ?_ (Convexity.mul_abs_det_div_norm_le (Convexity.det_word_ne_zero hdet w)
      (Convexity.det_word_ne_zero hdet [j]))
    rw [hj]
    exact mul_le_mul_of_nonneg_left (hδ₀A j) (abs_det_div_norm_pos
      (Convexity.det_word_ne_zero hdet w)).le
  have hcount : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      (externalCoveringNumber (ρ * D).toNNReal (range (canonicalProjPlus A v)) : ℝ≥0∞) ≤
        ENNReal.ofReal (2 * (δ₀ * ρ) ^ (-(t : ℝ)) * K) := by
    intro ρ hρ hρ1
    have hδρ : 0 < δ₀ * ρ := mul_pos hδ₀ hρ
    have hB0 : 0 ≤ 2 * (δ₀ * ρ) ^ (-(t : ℝ)) := by positivity
    have hε : 0 ≤ ρ * D := by positivity
    by_cases ht1 : (t : ℝ) ≤ 1
    · refine hA.externalCoveringNumber_le hδ₀ hδ₀1 hρ hρ1 hε (norm_word_nil A) hstep
        hA.norm_word_le hK hB0 fun w h1 h2 => ⟨{affineWord A v w 0}, ?_, ?_⟩
      · rw [Finset.card_singleton, Nat.cast_one]
        exact one_le_svf_of_norm t.coe_nonneg ht1 hδρ h1
      · refine (image_mono hXB).trans ((image_closedBall_subset_closedBall v w 0 hR0.le).trans ?_)
        rw [Finset.set_biUnion_singleton]
        exact closedBall_subset_closedBall (mul_le_mul_of_nonneg_right h2 diam_nonneg)
    · have hfr : ∀ w : List ι, |(word A w).det| / ‖word A w‖ ≤ r ^ w.length := fun w =>
        (abs_det_div_norm_le_norm (Convexity.det_word_ne_zero hdet w)).trans
          (hA.norm_word_le w)
      refine hA.externalCoveringNumber_le hδ₀ hδ₀1 hρ hρ1 hε (abs_det_div_norm_word_nil A)
        hstep₂ hfr hK hB0 fun w h1 h2 => ?_
      obtain ⟨G, hG, hcov⟩ := exists_finset_image_closedBall_subset v hdet w 0 hR0.le
      refine ⟨G, ?_, ?_⟩
      · exact (Nat.cast_le.2 hG).trans (natCeil_le_svf_of_alpha₂
          (Convexity.det_word_ne_zero hdet w) (not_le.1 ht1) ht2 hδρ h1)
      · refine (image_mono hXB).trans (hcov.trans ?_)
        exact iUnion₂_mono fun g _ =>
          closedBall_subset_closedBall (mul_le_mul_of_nonneg_right h2 diam_nonneg)
  refine upperBoxDim_le_of_forall (C := (2 * K * (δ₀ / D) ^ (-(t : ℝ))).toNNReal)
    (Real.toNNReal_pos.2 (by positivity)) ?_
  filter_upwards [eventually_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds hD0)] with ε hε0 hε1
  have hε : (0 : ℝ) < ε := hε0
  have hρ : 0 < ε / D := div_pos hε hD0
  have hρ1 : ε / D ≤ 1 := (div_le_one hD0).2 (le_of_lt hε1)
  have h := hcount _ hρ hρ1
  rw [div_mul_cancel₀ ε hD0.ne'] at h
  calc (externalCoveringNumber ε.toNNReal (range (canonicalProjPlus A v)) : ℝ≥0∞)
      ≤ ENNReal.ofReal (2 * (δ₀ * (ε / D)) ^ (-(t : ℝ)) * K) := h
    _ = ENNReal.ofReal (2 * K * (δ₀ / D) ^ (-(t : ℝ)) * ε ^ (-(t : ℝ))) := by
        rw [show δ₀ * (ε / D) = δ₀ / D * ε by ring,
          Real.mul_rpow (by positivity) hε.le]
        ring_nf
    _ = ((2 * K * (δ₀ / D) ^ (-(t : ℝ))).toNNReal : ℝ≥0∞) *
        ENNReal.ofReal (ε ^ (-(t : ℝ))) := ENNReal.ofReal_mul (by positivity)

end MatrixTuple

/-! ### The coordinate maps between the Euclidean plane and `ℝ × ℝ` -/

/-- The point of `ℝ × ℝ` with the coordinates of a point of the Euclidean plane; it inverts
`System.toPlane`. -/
noncomputable def ofPlane (z : EuclideanSpace ℝ (Fin 2)) : ℝ × ℝ := (z 0, z 1)

/-- `ofPlane` inverts `System.toPlane`. -/
@[simp] theorem ofPlane_toPlane (z : ℝ × ℝ) : ofPlane (System.toPlane z) = z := rfl

/-- The coordinate map from the Euclidean plane to `ℝ × ℝ` with the sup metric is
`1`-Lipschitz. -/
theorem lipschitzWith_ofPlane : LipschitzWith 1 ofPlane := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, Prod.dist_eq, dist_eq_norm x y]
  refine max_le ?_ ?_
  · rw [ofPlane, ofPlane, Real.dist_eq, ← Real.norm_eq_abs]
    exact PiLp.norm_apply_le (x - y) 0
  · rw [ofPlane, ofPlane, Real.dist_eq, ← Real.norm_eq_abs]
    exact PiLp.norm_apply_le (x - y) 1

/-- The coordinate map from the Euclidean plane to `ℝ × ℝ` is continuous. -/
theorem continuous_ofPlane : Continuous ofPlane := lipschitzWith_ofPlane.continuous

/-- `System.toPlane` commutes with subtraction. -/
theorem toPlane_sub (z z' : ℝ × ℝ) :
    System.toPlane (z - z') = System.toPlane z - System.toPlane z' := by
  ext j
  fin_cases j <;> rfl

/-- The identification `System.toPlane` of `ℝ × ℝ` with the sup metric with the Euclidean plane
is `2`-Lipschitz. -/
theorem lipschitzWith_toPlane : LipschitzWith 2 System.toPlane := by
  refine LipschitzWith.of_dist_le_mul fun z z' => ?_
  rw [dist_eq_norm, dist_eq_norm, ← toPlane_sub]
  set u := z - z'
  have h1 : |u.1| ≤ ‖u‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le u
  have h2 : |u.2| ≤ ‖u‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le u
  have hsq : ‖System.toPlane u‖ ^ 2 = u.1 ^ 2 + u.2 ^ 2 := by
    rw [Ellipse.norm_sq_eq]
    rfl
  have hu : 0 ≤ ‖u‖ := norm_nonneg u
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [hsq, NNReal.coe_ofNat]
  have h1' : u.1 ^ 2 ≤ ‖u‖ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h2' : u.2 ^ 2 ≤ ‖u‖ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  nlinarith

/-! ### The self-affine set of a planar system -/

namespace PlanarSystem

variable {ι : Type*} (P : PlanarSystem ι)

/-- The attractor `X = π(Σ)` of a planar system in `ℝ × ℝ` is the image of the self-affine set
`π^+(Σ^+)` of the affine system `(P.mat, P.planeTrans)` in the Euclidean plane. -/
theorem attractor_eq_image [Finite ι] :
    P.attractor = ofPlane '' range (MatrixTuple.canonicalProjPlus P.mat P.planeTrans) := by
  rw [← MatrixTuple.range_canonicalProj, ← range_comp, attractor]
  congr 1
  funext x
  rw [Function.comp_apply, ← P.toPlane_proj x, ofPlane_toPlane]

/-- The image of the attractor in the Euclidean plane is the self-affine set `π^+(Σ^+)` of the
affine system `(P.mat, P.planeTrans)`. -/
theorem toPlane_image_attractor [Finite ι] :
    System.toPlane '' P.attractor = range (MatrixTuple.canonicalProjPlus P.mat P.planeTrans) := by
  rw [← MatrixTuple.range_canonicalProj, attractor, ← range_comp]
  congr 1
  funext x
  exact P.toPlane_proj x

/-- The self-affine set of a planar system is compact. -/
theorem isCompact_attractor [Finite ι] : IsCompact P.attractor := by
  let : TopologicalSpace ι := ⊥
  have : DiscreteTopology ι := ⟨rfl⟩
  obtain ⟨r, hA⟩ := MatrixTuple.exists_contractionBound P.mat P.norm_lt_one
  rw [P.attractor_eq_image]
  exact (hA.isCompact_range_canonicalProjPlus P.planeTrans).image continuous_ofPlane

/-- The self-affine set of a planar system with at least one map is non-empty. -/
theorem attractor_nonempty [Nonempty ι] : P.attractor.Nonempty := range_nonempty _

/-- Hutchinson's theorem (`eq:self_affine_set_def`, tex lines 562 to 567): the attractor
`X = π(Σ)` of a planar system is the unique non-empty compact set `K ⊆ ℝ²` with
`K = ⋃_i φ_i(K)`, so it is the self-affine set of the article. -/
theorem eq_attractor [Finite ι] {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hne : K.Nonempty)
    (hinv : K = ⋃ i, P.phi i '' K) : K = P.attractor := by
  obtain ⟨r, hA⟩ := MatrixTuple.exists_contractionBound P.mat P.norm_lt_one
  have hinv' : System.toPlane '' K =
      ⋃ i, MatrixTuple.affineMap P.mat P.planeTrans i '' (System.toPlane '' K) := by
    conv_lhs => rw [hinv]
    rw [image_iUnion]
    refine iUnion_congr fun i => ?_
    rw [image_image, image_image]
    exact image_congr fun z _ => P.toPlane_phi i z
  have h := hA.eq_range_canonicalProjPlus P.planeTrans (hK.image System.continuous_toPlane)
    (hne.image _) hinv'
  rw [← P.toPlane_image_attractor] at h
  exact System.toPlane_injective.image_injective h

/-! ### Falconer's bound for planar self-affine sets -/

/-- Falconer's covering argument, Theorem 5.4 of his 1988 article, for every planar self-affine
set and `0 ≤ t ≤ 2`: `\overline{\dim}_M X ≤ t` when `P(𝖠, t) < 0`. The bound holds for
`π^+(Σ^+)` in the Euclidean plane (`MatrixTuple.ContractionBound.upperBoxDim_le_of_pressure_neg`)
and passes to `X ⊆ ℝ × ℝ` through the `1`-Lipschitz map `ofPlane`. -/
theorem upperBoxDim_attractor_le_of_pressure_neg_of_le_two [Fintype ι] [Nonempty ι] {t : ℝ≥0}
    (ht2 : (t : ℝ) ≤ 2) (hP : MatrixTuple.pressure P.mat t < 0) :
    upperBoxDim P.attractor ≤ t := by
  obtain ⟨r, hA⟩ := MatrixTuple.exists_contractionBound P.mat P.norm_lt_one
  rw [P.attractor_eq_image]
  exact (upperBoxDim_image_le lipschitzWith_ofPlane.lipschitzOnWith).trans
    (hA.upperBoxDim_le_of_pressure_neg (v := P.planeTrans) P.det_ne_zero ht2 hP)

/-- A planar self-affine set is a bounded subset of the plane, so `\overline{\dim}_M X ≤ 2`. -/
theorem upperBoxDim_attractor_le_two [Finite ι] : upperBoxDim P.attractor ≤ 2 :=
  upperBoxDim_le_two P.isCompact_attractor.isBounded

/-- Falconer's bound for every exponent: `\overline{\dim}_M X ≤ t` for every `t ≥ 0` with
`P(𝖠, t) < 0`. For `t > 2` it is `upperBoxDim_attractor_le_two`. -/
theorem upperBoxDim_attractor_le_of_pressure_neg [Fintype ι] [Nonempty ι] {t : ℝ} (ht : 0 ≤ t)
    (hP : MatrixTuple.pressure P.mat t < 0) : upperBoxDim P.attractor ≤ ENNReal.ofReal t := by
  rcases le_or_gt t 2 with ht2 | ht2
  · exact P.upperBoxDim_attractor_le_of_pressure_neg_of_le_two (t := t.toNNReal)
      (by rwa [Real.coe_toNNReal _ ht]) (by rwa [Real.coe_toNNReal _ ht])
  · calc upperBoxDim P.attractor ≤ 2 := P.upperBoxDim_attractor_le_two
      _ = ENNReal.ofReal 2 := ENNReal.ofReal_ofNat 2 |>.symm
      _ ≤ ENNReal.ofReal t := ENNReal.ofReal_le_ofReal ht2.le

/-- `\overline{\dim}_M X ≤ dimaff(X)` for every planar self-affine set, the bound of tex lines
542 to 543: the pressure is negative at every `t > dimaff(X)`. -/
theorem upperBoxDim_attractor_le_dimaff [Fintype ι] [Nonempty ι] :
    upperBoxDim P.attractor ≤ ENNReal.ofReal P.dimaff := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hsum : ENNReal.ofReal P.dimaff + ε = ENNReal.ofReal (P.dimaff + ε) := by
    rw [ENNReal.ofReal_add P.dimaff_nonneg ε.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  rw [hsum]
  refine P.upperBoxDim_attractor_le_of_pressure_neg (add_nonneg P.dimaff_nonneg ε.coe_nonneg) ?_
  exact P.pressure_neg_of_dimaff_lt (lt_add_of_pos_right _ (by exact_mod_cast hε))

/-- Falconer's bound, Theorem 5.4 of his 1988 article, for the upper Minkowski dimension:
`\overline{\dim}_M X ≤ min{2, dimaff(X)}` for every planar self-affine set, without a separation
condition (tex lines 510 to 510 and 2159 to 2172). -/
theorem upperBoxDim_attractor_le [Fintype ι] [Nonempty ι] :
    upperBoxDim P.attractor ≤ ENNReal.ofReal (min 2 P.dimaff) := by
  rcases le_total 2 P.dimaff with hd | hd
  · rw [min_eq_left hd, ENNReal.ofReal_ofNat]
    exact P.upperBoxDim_attractor_le_two
  · rw [min_eq_right hd]
    exact P.upperBoxDim_attractor_le_dimaff

/-- `eq:hausdorff_affinity_upper_bound`: `\dim_H X ≤ min{2, dimaff(X)}` for every planar
self-affine set, Falconer's Theorem 5.4, from `\dim_H X ≤ \overline{\dim}_M X`. -/
theorem dimH_attractor_le [Fintype ι] [Nonempty ι] :
    dimH P.attractor ≤ ENNReal.ofReal (min 2 P.dimaff) :=
  (dimH_le_upperBoxDim _).trans P.upperBoxDim_attractor_le

/-- The packing dimension of a planar self-affine set is at most `min{2, dimaff(X)}`, since
`\dim_P X ≤ \overline{\dim}_M X`. -/
theorem packingDim_attractor_le [Fintype ι] [Nonempty ι] :
    packingDim P.attractor ≤ ENNReal.ofReal (min 2 P.dimaff) :=
  (packingDim_le_upperBoxDim _).trans P.upperBoxDim_attractor_le

/-- Falconer's bound for the upper Minkowski dimension in the Euclidean plane: the image
`π^+(Σ^+)` of `X` under `System.toPlane` (`toPlane_image_attractor`) satisfies
`\overline{\dim}_M ≤ min{2, dimaff(X)}`. -/
theorem upperBoxDim_toPlane_attractor_le [Fintype ι] [Nonempty ι] :
    upperBoxDim (System.toPlane '' P.attractor) ≤ ENNReal.ofReal (min 2 P.dimaff) :=
  (upperBoxDim_image_le lipschitzWith_toPlane.lipschitzOnWith).trans P.upperBoxDim_attractor_le

/-- `eq:hausdorff_affinity_upper_bound` in the Euclidean plane: the image `π^+(Σ^+)` of `X`
under `System.toPlane` has Hausdorff dimension at most `min{2, dimaff(X)}`. -/
theorem dimH_toPlane_attractor_le [Fintype ι] [Nonempty ι] :
    dimH (System.toPlane '' P.attractor) ≤ ENNReal.ofReal (min 2 P.dimaff) :=
  (lipschitzWith_toPlane.dimH_image_le _).trans P.dimH_attractor_le

end PlanarSystem

/-! ### The box-like specialisation -/

namespace System

variable {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)

/-- The box-like bound `System.upperBoxDim_attractor_le` of `BoxLike/FalconerBound.lean` as the
specialisation of the planar bound to the planar system `S.toPlanar`:
`\overline{\dim}_M X ≤ min{2, dimaff(X)}`. -/
theorem upperBoxDim_attractor_le_planar :
    upperBoxDim S.attractor ≤ ENNReal.ofReal (min 2 S.dimaff) := by
  rw [← S.toPlanar_attractor, ← S.toPlanar_dimaff]
  exact S.toPlanar.upperBoxDim_attractor_le

/-- The box-like `eq:hausdorff_affinity_upper_bound`, `System.dimH_attractor_le` of
`BoxLike/FalconerBound.lean`, as the specialisation of the planar bound to `S.toPlanar`. -/
theorem dimH_attractor_le_planar : dimH S.attractor ≤ ENNReal.ofReal (min 2 S.dimaff) := by
  rw [← S.toPlanar_attractor, ← S.toPlanar_dimaff]
  exact S.toPlanar.dimH_attractor_le

end System

end BoxLike
