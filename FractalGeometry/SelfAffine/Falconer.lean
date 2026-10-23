import Mathlib
import GeometricMeasureTheory.Box.BoxDimension
import FractalGeometry.Dimension.PlaneCovering
import FractalGeometry.LinearCocycles.ExponentAtZero
import FractalGeometry.LinearCocycles.Pressure
import FractalGeometry.LinearCocycles.PressureBounds
import FractalGeometry.LinearCocycles.Products
import FractalGeometry.LinearCocycles.SingularValue
import FractalGeometry.LinearCocycles.SingularValueExponents
import FractalGeometry.SelfAffine.AffinityDimension
import FractalGeometry.SelfAffine.Coding
import FractalGeometry.SelfAffine.Coordinates
import FractalGeometry.SelfAffine.Planar
import FractalGeometry.Symbolic.OneSidedShift
import FractalGeometry.Symbolic.StoppingTime
import GeometricMeasureTheory

/-!
Falconer's affinity-dimension upper bound for finite contractive invertible
planar affine systems: Hausdorff dimension is at most upper box dimension,
which is at most min(2, affinity dimension). No separation condition is required.
The box dimension is the GeometricMeasureTheory covering-number definition.
Planar specialisation of the upper-bound argument in Kenneth J. Falconer,
The Hausdorff dimension of self-affine fractals, Mathematical Proceedings of
the Cambridge Philosophical Society 103(2) (1988), 339–350,
doi:10.1017/S0305004100064926. No almost-every-translation equality is claimed.
-/

open GeometricMeasureTheory

namespace FractalGeometry

open Filter Topology Set Metric Matrix

open scoped ENNReal NNReal Matrix.Norms.L2Operator

namespace Ellipse

theorem planeLin_apply (A : Matrix (Fin 2) (Fin 2) ℝ) (x : EuclideanSpace ℝ (Fin 2))
    (i : Fin 2) : planeLin A x i = A i 0 * x 0 + A i 1 * x 1 := by
  rw [show x = WithLp.toLp 2 (WithLp.ofLp x) from rfl, planeLin_toLp]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem norm_sq_eq (x : EuclideanSpace ℝ (Fin 2)) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

def dot (x y : EuclideanSpace ℝ (Fin 2)) : ℝ := x 0 * y 0 + x 1 * y 1

def cross (x y : EuclideanSpace ℝ (Fin 2)) : ℝ := x 0 * y 1 - x 1 * y 0

theorem dot_sq_add_cross_sq (x y : EuclideanSpace ℝ (Fin 2)) :
    dot x y ^ 2 + cross x y ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  rw [norm_sq_eq, norm_sq_eq, dot, cross]
  ring

theorem abs_dot_le (x y : EuclideanSpace ℝ (Fin 2)) : |dot x y| ≤ ‖x‖ * ‖y‖ := by
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  nlinarith [dot_sq_add_cross_sq x y, sq_nonneg (cross x y)]

theorem abs_cross_le (x y : EuclideanSpace ℝ (Fin 2)) : |cross x y| ≤ ‖x‖ * ‖y‖ := by
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  nlinarith [dot_sq_add_cross_sq x y, sq_nonneg (dot x y)]

theorem cross_planeLin (A : Matrix (Fin 2) (Fin 2) ℝ) (x y : EuclideanSpace ℝ (Fin 2)) :
    cross (planeLin A x) (planeLin A y) = A.det * cross x y := by
  simp only [cross, planeLin_apply, det_fin_two]
  ring

theorem cross_smul_left (c : ℝ) (x y : EuclideanSpace ℝ (Fin 2)) :
    cross (c • x) y = c * cross x y := by
  simp only [cross, PiLp.smul_apply, smul_eq_mul]
  ring

theorem norm_sub_smul_sq {e : EuclideanSpace ℝ (Fin 2)} (he : ‖e‖ = 1)
    (w : EuclideanSpace ℝ (Fin 2)) (u : ℝ) :
    ‖w - u • e‖ ^ 2 = (dot e w - u) ^ 2 + cross e w ^ 2 := by
  have h1 : e 0 ^ 2 + e 1 ^ 2 = 1 := by rw [← norm_sq_eq, he, one_pow]
  rw [norm_sq_eq]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, dot, cross]
  linear_combination (u ^ 2 - w 0 ^ 2 - w 1 ^ 2) * h1

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

theorem dist_le_norm_mul (A : Matrix (Fin 2) (Fin 2) ℝ) (c y : EuclideanSpace ℝ (Fin 2))
    {R : ℝ} (hy : ‖y‖ ≤ R) : dist (c + planeLin A y) c ≤ ‖A‖ * R := by
  rw [dist_eq_norm, add_sub_cancel_left, ← norm_planeLin]
  exact ((planeLin A).le_opNorm y).trans (mul_le_mul_of_nonneg_left hy (norm_nonneg _))

end Ellipse

namespace MatrixTuple

variable {ι : Type*} {A : ι → Matrix (Fin 2) (Fin 2) ℝ} (v : ι → EuclideanSpace ℝ (Fin 2))

theorem image_closedBall_subset_closedBall (w : List ι) (b : EuclideanSpace ℝ (Fin 2)) {R : ℝ}
    (hR : 0 ≤ R) :
    affineWord A v w '' closedBall b R ⊆
      closedBall (affineWord A v w b) (‖word A w‖ * diam (closedBall b R)) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_closedBall, diam_closedBall_eq b hR]
  have h := Ellipse.dist_le_norm_mul (word A w) (affineWord A v w b) (x - b)
    (show ‖x - b‖ ≤ 2 * R by rw [← dist_eq_norm]; linarith [mem_closedBall.1 hx])
  rwa [← affineWord_sub, add_sub_cancel] at h

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

theorem norm_word_nil : ‖word A []‖ = 1 := by
  rw [word_nil]
  refine le_antisymm norm_one_matrix_le ?_
  have h := abs_det_le_norm_sq (1 : Matrix (Fin 2) (Fin 2) ℝ)
  rw [det_one, abs_one] at h
  nlinarith [norm_nonneg (1 : Matrix (Fin 2) (Fin 2) ℝ)]

variable (A) in

theorem abs_det_div_norm_word_nil : |(word A []).det| / ‖word A []‖ = 1 := by
  rw [norm_word_nil, word_nil, det_one, abs_one, div_one]

variable [Fintype ι]

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

theorem one_le_svf_of_norm {B : Matrix (Fin 2) (Fin 2) ℝ} {t δρ : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hδρ : 0 < δρ) (h : δρ ≤ ‖B‖) : (1 : ℝ) ≤ 2 * δρ ^ (-t) * svf t B := by
  have hsvf : svf t B = ‖B‖ ^ t := by rw [svf, ite_eq_left ht1]
  have hpow : δρ ^ (-t) * δρ ^ t = 1 := by
    rw [Real.rpow_neg hδρ.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hδρ t).ne']
  calc (1 : ℝ) ≤ 2 * (δρ ^ (-t) * δρ ^ t) := by rw [hpow]; norm_num
    _ ≤ 2 * (δρ ^ (-t) * ‖B‖ ^ t) := by gcongr
    _ = 2 * δρ ^ (-t) * svf t B := by rw [hsvf, mul_assoc]

omit [Fintype ι] in

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

noncomputable def ofPlane (z : EuclideanSpace ℝ (Fin 2)) : ℝ × ℝ := (z 0, z 1)

@[simp] theorem ofPlane_toPlane (z : ℝ × ℝ) : ofPlane (PlaneCoordinates.toPlane z) = z := rfl

theorem lipschitzWith_ofPlane : LipschitzWith 1 ofPlane := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, Prod.dist_eq, dist_eq_norm x y]
  refine max_le ?_ ?_
  · rw [ofPlane, ofPlane, Real.dist_eq, ← Real.norm_eq_abs]
    exact PiLp.norm_apply_le (x - y) 0
  · rw [ofPlane, ofPlane, Real.dist_eq, ← Real.norm_eq_abs]
    exact PiLp.norm_apply_le (x - y) 1

theorem continuous_ofPlane : Continuous ofPlane := lipschitzWith_ofPlane.continuous

namespace AffineIFS

variable {ι : Type*} (P : AffineIFS ι)

theorem attractor_eq_image [Finite ι] :
    P.attractor = ofPlane '' range (MatrixTuple.canonicalProjPlus P.mat P.planeTrans) := by
  rw [← MatrixTuple.range_canonicalProj, ← range_comp, attractor]
  congr 1
  funext x
  rw [Function.comp_apply, ← P.toPlane_proj x, ofPlane_toPlane]

theorem isCompact_attractor [Finite ι] : IsCompact P.attractor := by
  let : TopologicalSpace ι := ⊥
  have : DiscreteTopology ι := ⟨rfl⟩
  obtain ⟨r, hA⟩ := MatrixTuple.exists_contractionBound P.mat P.norm_lt_one
  rw [P.attractor_eq_image]
  exact (hA.isCompact_range_canonicalProjPlus P.planeTrans).image continuous_ofPlane

theorem upperBoxDim_attractor_le_of_pressure_neg_of_le_two [Fintype ι] [Nonempty ι] {t : ℝ≥0}
    (ht2 : (t : ℝ) ≤ 2) (hP : MatrixTuple.pressure P.mat t < 0) :
    upperBoxDim P.attractor ≤ t := by
  obtain ⟨r, hA⟩ := MatrixTuple.exists_contractionBound P.mat P.norm_lt_one
  rw [P.attractor_eq_image]
  exact (upperBoxDim_image_le lipschitzWith_ofPlane.lipschitzOnWith).trans
    (hA.upperBoxDim_le_of_pressure_neg (v := P.planeTrans) P.det_ne_zero ht2 hP)

theorem upperBoxDim_attractor_le_two [Finite ι] : upperBoxDim P.attractor ≤ 2 :=
  upperBoxDim_le_two P.isCompact_attractor.isBounded

theorem upperBoxDim_attractor_le_of_pressure_neg [Fintype ι] [Nonempty ι] {t : ℝ} (ht : 0 ≤ t)
    (hP : MatrixTuple.pressure P.mat t < 0) : upperBoxDim P.attractor ≤ ENNReal.ofReal t := by
  rcases le_or_gt t 2 with ht2 | ht2
  · exact P.upperBoxDim_attractor_le_of_pressure_neg_of_le_two (t := t.toNNReal)
      (by rwa [Real.coe_toNNReal _ ht]) (by rwa [Real.coe_toNNReal _ ht])
  · calc upperBoxDim P.attractor ≤ 2 := P.upperBoxDim_attractor_le_two
      _ = ENNReal.ofReal 2 := ENNReal.ofReal_ofNat 2 |>.symm
      _ ≤ ENNReal.ofReal t := ENNReal.ofReal_le_ofReal ht2.le

theorem upperBoxDim_attractor_le_dimaff [Fintype ι] [Nonempty ι] :
    upperBoxDim P.attractor ≤ ENNReal.ofReal P.dimaff := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hsum : ENNReal.ofReal P.dimaff + ε = ENNReal.ofReal (P.dimaff + ε) := by
    rw [ENNReal.ofReal_add P.dimaff_nonneg ε.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  rw [hsum]
  refine P.upperBoxDim_attractor_le_of_pressure_neg (add_nonneg P.dimaff_nonneg ε.coe_nonneg) ?_
  exact P.pressure_neg_of_dimaff_lt (lt_add_of_pos_right _ (by exact_mod_cast hε))

theorem upperBoxDim_attractor_le [Fintype ι] [Nonempty ι] :
    upperBoxDim P.attractor ≤ ENNReal.ofReal (min 2 P.dimaff) := by
  rcases le_total 2 P.dimaff with hd | hd
  · rw [min_eq_left hd, ENNReal.ofReal_ofNat]
    exact P.upperBoxDim_attractor_le_two
  · rw [min_eq_right hd]
    exact P.upperBoxDim_attractor_le_dimaff

theorem dimH_attractor_le [Fintype ι] [Nonempty ι] :
    dimH P.attractor ≤ ENNReal.ofReal (min 2 P.dimaff) :=
  (dimH_le_upperBoxDim _).trans P.upperBoxDim_attractor_le

end AffineIFS

end FractalGeometry
