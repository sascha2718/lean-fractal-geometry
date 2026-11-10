module

/-
Exact dimension gives entropy dimension for bounded planar measures: the planar analogue of the
vendored `ExactOverlaps.Entropy.normalized_entropy_limit_of_exact_dimension`
(`vendor/ExactOverlaps/SelfSimilar/ExactDimensionEntropy.lean`), used by Rapaport
(arXiv:2309.03985, lines 1290 to 1294 and 1316 to 1320) in the form
`(1/n) H(μ, 𝒟_{χ n}) → χ dim μ`.

* `tendsto_ent_rect_div_of_isExactDim`: a probability measure `θ` on the plane with bounded
  support and exact dimension `d` has `ent θ (rect n n) / n → d log 2`.
* `tendsto_ent_rect_comp_div_of_isExactDim`: the same along natural levels `k n` with
  `k n / n → c > 0`, with limit `d c log 2`.
* `tendsto_ent_rect_lvl_div_of_isExactDim`: along the levels `lvl χ n`, `χ > 0`, limit `d χ`.
* `Exps.tendsto_ent_Dsq_div_of_isExactDim`: for the partitions `𝒟²_{χ₂ n}`, limit `d χ₂`.

The proof follows the vendored one. The information `-log θ(Q)` of the level-`n` dyadic square
`Q` containing `z` integrates to `ent θ (rect n n)`. In the supremum metric `Q` lies in the
closed ball `B(z, 2^{-n})`, which lies in the `3 × 3` block of squares around `Q`. By
Borel–Cantelli, almost surely the mass of `Q` is eventually at least `e^{-ε n}` times the mass of
the block, so the normalised information tends to `d log 2` almost surely. Dominated
convergence applies to the information truncated at `L n`, and the truncation error is at most
`2 e^{-L n / 2}` times the number `≤ (2R + 2)^2 4^n` of squares meeting the support.
-/

public import BoxLike.Rapaport.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Order.Filter.AtTopBot.Archimedean

@[expose] public section

namespace BoxLike.Rapaport

open MeasureTheory Filter Metric Set ExactOverlaps.Entropy
open scoped Topology ENNReal

section ExactDimEntropy

variable {θ : Measure (ℝ × ℝ)}

/-! ### Dyadic squares, cells and balls -/

/-- The level-`n` dyadic square partition `rect n n` is measurable. -/
private theorem measurable_rect_nat (n : ℕ) : Measurable (rect n n) :=
  ((measurable_dyadicQuantize _).comp measurable_fst).prodMk
    ((measurable_dyadicQuantize _).comp measurable_snd)

/-- Equal dyadic labels at level `n` put two reals within `2^{-n}` of each other. -/
private theorem abs_sub_le_of_dyadicQuantize_eq {n : ℕ} {x y : ℝ}
    (h : dyadicQuantize n x = dyadicQuantize n y) : |x - y| ≤ ((2 : ℝ) ^ n)⁻¹ := by
  have hs : (0 : ℝ) < 2 ^ n := by positivity
  simp only [dyadicQuantize, zpow_natCast] at h
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor h
  rw [← mul_sub, abs_mul, abs_of_pos hs] at h1
  calc |x - y| = ((2 : ℝ) ^ n)⁻¹ * (2 ^ n * |x - y|) := by field_simp
    _ ≤ ((2 : ℝ) ^ n)⁻¹ * 1 := by gcongr
    _ = _ := mul_one _

/-- Two reals within `2^{-n}` of each other have dyadic labels at level `n` differing by at
most one. -/
private theorem dyadicQuantize_sub_mem {n : ℕ} {x y : ℝ} (h : |x - y| ≤ ((2 : ℝ) ^ n)⁻¹) :
    dyadicQuantize n x - dyadicQuantize n y ∈ Finset.Icc (-1 : ℤ) 1 := by
  have hs : (0 : ℝ) < 2 ^ n := by positivity
  have h' : |2 ^ n * x - 2 ^ n * y| ≤ 1 := by
    rw [← mul_sub, abs_mul, abs_of_pos hs]
    calc 2 ^ n * |x - y| ≤ 2 ^ n * ((2 : ℝ) ^ n)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hs.ne'
  obtain ⟨hlo, hhi⟩ := abs_le.mp h'
  simp only [dyadicQuantize, zpow_natCast]
  have hx1 := Int.floor_le ((2 : ℝ) ^ n * x)
  have hx2 := Int.lt_floor_add_one ((2 : ℝ) ^ n * x)
  have hy1 := Int.floor_le ((2 : ℝ) ^ n * y)
  have hy2 := Int.lt_floor_add_one ((2 : ℝ) ^ n * y)
  have hl : (-2 : ℝ) < ((⌊(2 : ℝ) ^ n * x⌋ - ⌊(2 : ℝ) ^ n * y⌋ : ℤ) : ℝ) := by
    push_cast; linarith
  have hu : ((⌊(2 : ℝ) ^ n * x⌋ - ⌊(2 : ℝ) ^ n * y⌋ : ℤ) : ℝ) < 2 := by
    push_cast; linarith
  have hl' : (-2 : ℤ) < ⌊(2 : ℝ) ^ n * x⌋ - ⌊(2 : ℝ) ^ n * y⌋ := by exact_mod_cast hl
  have hu' : ⌊(2 : ℝ) ^ n * x⌋ - ⌊(2 : ℝ) ^ n * y⌋ < 2 := by exact_mod_cast hu
  rw [Finset.mem_Icc]
  omega

/-- The level-`n` dyadic square containing `z` lies in the closed ball `B(z, 2^{-n})` of the
supremum metric. -/
private theorem rect_fibre_subset_closedBall (n : ℕ) (z : ℝ × ℝ) :
    rect n n ⁻¹' {rect n n z} ⊆ closedBall z ((2 : ℝ) ^ n)⁻¹ := by
  intro w hw
  simp only [mem_preimage, mem_singleton_iff, rect, Prod.mk.injEq] at hw
  rw [mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_le (abs_sub_le_of_dyadicQuantize_eq hw.1) (abs_sub_le_of_dyadicQuantize_eq hw.2)

/-- The offsets `{-1, 0, 1}²` of the `3 × 3` block of neighbouring squares. -/
private def nbr : Finset (ℤ × ℤ) := Finset.Icc (-1) 1 ×ˢ Finset.Icc (-1) 1

/-- The closed ball `B(z, 2^{-n})` lies in the `3 × 3` block of level-`n` dyadic squares around
the square containing `z`. -/
private theorem closedBall_subset_nbr (n : ℕ) (z : ℝ × ℝ) :
    closedBall z ((2 : ℝ) ^ n)⁻¹ ⊆ ⋃ v ∈ nbr, rect n n ⁻¹' {rect n n z + v} := by
  intro w hw
  rw [mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hw
  simp only [mem_iUnion, mem_preimage, mem_singleton_iff, exists_prop]
  refine ⟨rect n n w - rect n n z, ?_, by abel⟩
  simp only [nbr, Finset.mem_product, rect, Prod.fst_sub, Prod.snd_sub]
  exact ⟨dyadicQuantize_sub_mem (le_of_max_le_left hw),
    dyadicQuantize_sub_mem (le_of_max_le_right hw)⟩

/-! ### Masses and information of dyadic squares -/

/-- The mass `θ(Q)` of the level-`n` dyadic square `Q` with label `b`. -/
private noncomputable def sqMass (θ : Measure (ℝ × ℝ)) (n : ℕ) (b : ℤ × ℤ) : ℝ :=
  θ.real (rect n n ⁻¹' {b})

/-- The mass of the `3 × 3` block of level-`n` dyadic squares centred at the label `b`. -/
private noncomputable def nbrMass (θ : Measure (ℝ × ℝ)) (n : ℕ) (b : ℤ × ℤ) : ℝ :=
  ∑ v ∈ nbr, sqMass θ n (b + v)

/-- The information `-log θ(Q)` of the level-`n` dyadic square `Q` containing `z`. -/
private noncomputable def sqInfo (θ : Measure (ℝ × ℝ)) (n : ℕ) (z : ℝ × ℝ) : ℝ :=
  -Real.log (sqMass θ n (rect n n z))

/-- The information of the level-`n` dyadic squares is measurable. -/
private theorem measurable_sqInfo (n : ℕ) : Measurable (sqInfo θ n) :=
  (measurable_of_countable fun b : ℤ × ℤ => -Real.log (sqMass θ n b)).comp
    (measurable_rect_nat n)

/-- The information of a dyadic square under a probability measure is nonnegative. -/
private theorem sqInfo_nonneg [IsProbabilityMeasure θ] (n : ℕ) (z : ℝ × ℝ) :
    0 ≤ sqInfo θ n z :=
  neg_nonneg.2 (Real.log_nonpos measureReal_nonneg measureReal_le_one)

/-- The ball `B(z, 2^{-n})` has mass at most that of the `3 × 3` block around the square of
`z`. -/
private theorem measureReal_closedBall_le_nbrMass [IsFiniteMeasure θ] (n : ℕ) (z : ℝ × ℝ) :
    θ.real (closedBall z ((2 : ℝ) ^ n)⁻¹) ≤ nbrMass θ n (rect n n z) :=
  (measureReal_mono (closedBall_subset_nbr n z) (measure_ne_top _ _)).trans
    (measureReal_biUnion_finset_le _ _)

/-- The masses of finitely many distinct level-`n` squares sum to at most one. -/
private theorem sum_sqMass_le_one [IsProbabilityMeasure θ] (n : ℕ) (G : Finset (ℤ × ℤ)) :
    ∑ b ∈ G, sqMass θ n b ≤ 1 := by
  unfold sqMass
  rw [← measureReal_biUnion_finset (Set.pairwiseDisjoint_fiber _ _)
    (fun b _ => measurable_rect_nat n (measurableSet_singleton b))]
  exact measureReal_le_one

/-- The block masses of finitely many level-`n` squares sum to at most `#nbr = 9`. -/
private theorem sum_nbrMass_le [IsProbabilityMeasure θ] (n : ℕ) (G : Finset (ℤ × ℤ)) :
    ∑ b ∈ G, nbrMass θ n b ≤ nbr.card := by
  unfold nbrMass
  rw [Finset.sum_comm]
  calc ∑ v ∈ nbr, ∑ b ∈ G, sqMass θ n (b + v) ≤ ∑ v ∈ nbr, (1 : ℝ) := by
        refine Finset.sum_le_sum fun v _ => ?_
        have h := Finset.sum_image (f := sqMass θ n) (s := G) (g := fun b => b + v)
          (fun a _ b _ hab => add_right_cancel hab)
        calc ∑ b ∈ G, sqMass θ n (b + v) = ∑ b ∈ G.image (· + v), sqMass θ n b := h.symm
          _ ≤ 1 := sum_sqMass_le_one n _
    _ = nbr.card := by simp

/-! ### Squares meeting the support -/

/-- The labels of the level-`n` dyadic squares meeting the closed ball `B(c, R)`. -/
private noncomputable def supp (c : ℝ × ℝ) (R : ℝ) (n : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc ⌊(2 : ℝ) ^ n * (c.1 - R)⌋ ⌊(2 : ℝ) ^ n * (c.1 + R)⌋ ×ˢ
    Finset.Icc ⌊(2 : ℝ) ^ n * (c.2 - R)⌋ ⌊(2 : ℝ) ^ n * (c.2 + R)⌋

/-- A point of `B(c, R)` lies in a level-`n` square with label in `supp c R n`. -/
private theorem rect_mem_supp {c z : ℝ × ℝ} {R : ℝ} (h : ‖z - c‖ ≤ R) (n : ℕ) :
    rect n n z ∈ supp c R n := by
  rw [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs, Real.norm_eq_abs] at h
  have h1 := abs_le.mp (le_of_max_le_left h)
  have h2 := abs_le.mp (le_of_max_le_right h)
  simp only [supp, rect, dyadicQuantize, zpow_natCast, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨Int.floor_mono ?_, Int.floor_mono ?_⟩, ⟨Int.floor_mono ?_, Int.floor_mono ?_⟩⟩ <;>
    gcongr <;> linarith

/-- At most `(2R + 2)^2 4^n` level-`n` squares meet `B(c, R)`. -/
private theorem card_supp_le {c : ℝ × ℝ} {R : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    ((supp c R n).card : ℝ) ≤ (2 * R + 2) ^ 2 * 4 ^ n := by
  have hp : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have key : ∀ a : ℝ, ((Finset.Icc ⌊(2 : ℝ) ^ n * (a - R)⌋
      ⌊(2 : ℝ) ^ n * (a + R)⌋).card : ℝ) ≤ (2 * R + 2) * 2 ^ n := by
    intro a
    rw [Int.card_Icc, ← Int.cast_natCast, Int.toNat_eq_max, Int.cast_max]
    have h1 := Int.floor_le ((2 : ℝ) ^ n * (a + R))
    have h2 := Int.lt_floor_add_one ((2 : ℝ) ^ n * (a - R))
    apply max_le
    · push_cast
      nlinarith
    · push_cast
      positivity
  rw [supp, Finset.card_product, Nat.cast_mul]
  calc _ ≤ ((2 * R + 2) * 2 ^ n) * ((2 * R + 2) * 2 ^ n) :=
        mul_le_mul (key _) (key _) (Nat.cast_nonneg _) (by positivity)
    _ = _ := by
      rw [show (4 : ℝ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
      ring

/-- Almost every point lies in a level-`n` square with label in `supp c R n`. -/
private theorem ae_rect_mem_supp {c : ℝ × ℝ} {R : ℝ} (hb : InBall θ c R) (n : ℕ) :
    ∀ᵐ z ∂θ, rect n n z ∈ supp c R n :=
  hb.mono fun _ hz => rect_mem_supp hz n

/-- Squares with label outside `supp c R n` carry no mass. -/
private theorem sqMass_eq_zero {c : ℝ × ℝ} {R : ℝ} (hb : InBall θ c R) {n : ℕ} {b : ℤ × ℤ}
    (hbn : b ∉ supp c R n) : sqMass θ n b = 0 := by
  have h0 : θ (rect n n ⁻¹' {b}) = 0 := by
    refine measure_mono_null (fun z hz => ?_) (ae_iff.mp (ae_rect_mem_supp hb n))
    simp only [mem_preimage, mem_singleton_iff] at hz
    simp only [mem_ofPred_eq, hz]
    exact hbn
  simp [sqMass, measureReal_def, h0]

/-! ### Integrals of functions of the square -/

/-- The integral of a function of the level-`n` square label is the finite sum of its values
weighted by the masses of the squares. -/
private theorem integral_comp_rect [IsFiniteMeasure θ] {c : ℝ × ℝ} {R : ℝ} (hb : InBall θ c R)
    (n : ℕ) (g : ℤ × ℤ → ℝ) :
    ∫ z, g (rect n n z) ∂θ = ∑ b ∈ supp c R n, sqMass θ n b * g b := by
  have hm := measurable_rect_nat n
  rw [← integral_map hm.aemeasurable (measurable_of_countable g).aestronglyMeasurable]
  have hae : ∀ᵐ b ∂(θ.map (rect n n)), b ∈ (supp c R n : Set (ℤ × ℤ)) :=
    (ae_map_iff hm.aemeasurable (Finset.measurableSet _)).2 (ae_rect_mem_supp hb n)
  rw [← Measure.restrict_eq_self_of_ae_mem hae,
    setIntegral_finset _ (IntegrableOn.of_finite (Finset.finite_toSet _))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_measureReal_apply hm (measurableSet_singleton b), smul_eq_mul]
  rfl

/-- The entropy of the level-`n` dyadic squares as a finite sum over the squares meeting the
support. -/
private theorem ent_rect_eq_sum {c : ℝ × ℝ} {R : ℝ} (hb : InBall θ c R) (n : ℕ) :
    ent θ (rect n n) = ∑ b ∈ supp c R n, sqMass θ n b * -Real.log (sqMass θ n b) := by
  rw [ent, tsum_eq_sum (s := supp c R n) fun b hb' => by
    change Real.negMulLog (sqMass θ n b) = 0
    rw [sqMass_eq_zero hb hb', Real.negMulLog_zero]]
  refine Finset.sum_congr rfl fun b _ => ?_
  change Real.negMulLog (sqMass θ n b) = _
  rw [Real.negMulLog]
  ring

/-! ### The truncation error -/

/-- One term of the truncation error: for `0 ≤ p`, `n ≥ 1`, `0 ≤ L` and `x = -log p / n`,
`0 ≤ p (x - min x L) ≤ 2 e^{-n L / 2}`. -/
private theorem trunc_term_le {p L : ℝ} {n : ℕ} (hp0 : 0 ≤ p) (hn : 1 ≤ n) (hL : 0 ≤ L) :
    0 ≤ p * (-Real.log p / n - min (-Real.log p / n) L) ∧
      p * (-Real.log p / n - min (-Real.log p / n) L) ≤ 2 * Real.exp (-(n * L) / 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨mul_nonneg hp0 (sub_nonneg.2 (min_le_left _ _)), ?_⟩
  rcases le_or_gt (-Real.log p / n) L with h | h
  · rw [min_eq_left h, sub_self, mul_zero]
    positivity
  rw [min_eq_right h.le]
  rcases hp0.eq_or_lt with rfl | hp
  · simp only [zero_mul]
    positivity
  have hpu : p = Real.exp (-(-Real.log p)) := by rw [neg_neg, Real.exp_log hp]
  generalize -Real.log p = u at h hpu ⊢
  rw [lt_div_iff₀ hn'] at h
  have hu0 : 0 ≤ u := by nlinarith
  have h1 : p * (u / n - L) ≤ p * u := by
    apply mul_le_mul_of_nonneg_left _ hp0
    have : u / n ≤ u := div_le_self hu0 (by exact_mod_cast hn)
    linarith
  have h2 : u ≤ 2 * Real.exp (u / 2) := by linarith [Real.add_one_le_exp (u / 2)]
  have h3 : p * u ≤ 2 * Real.exp (-u / 2) := by
    rw [hpu]
    calc Real.exp (-u) * u ≤ Real.exp (-u) * (2 * Real.exp (u / 2)) := by gcongr
      _ = 2 * Real.exp (-u / 2) := by
        rw [mul_left_comm, ← Real.exp_add]
        ring_nf
  have h4 : Real.exp (-u / 2) ≤ Real.exp (-(n * L) / 2) := Real.exp_le_exp.2 (by linarith)
  linarith

/-- The truncation error at level `n ≥ 1`: the normalised entropy exceeds the integral of the
normalised information truncated at `L` by at most `2 (2R + 2)^2 4^n e^{-n L / 2}`. -/
private theorem err_bounds [IsProbabilityMeasure θ] {c : ℝ × ℝ} {R L : ℝ} (hb : InBall θ c R)
    (hR : 0 ≤ R) (hL : 0 ≤ L) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ ent θ (rect n n) / n - ∫ z, min (sqInfo θ n z / n) L ∂θ ∧
      ent θ (rect n n) / n - ∫ z, min (sqInfo θ n z / n) L ∂θ ≤
        2 * (2 * R + 2) ^ 2 * (4 ^ n * Real.exp (-(n * L) / 2)) := by
  have hI : ∫ z, min (sqInfo θ n z / n) L ∂θ =
      ∑ b ∈ supp c R n, sqMass θ n b * min (-Real.log (sqMass θ n b) / n) L :=
    integral_comp_rect hb n fun b => min (-Real.log (sqMass θ n b) / n) L
  have hE : ent θ (rect n n) / n =
      ∑ b ∈ supp c R n, sqMass θ n b * (-Real.log (sqMass θ n b) / n) := by
    rw [ent_rect_eq_sum hb n, Finset.sum_div]
    exact Finset.sum_congr rfl fun b _ => mul_div_assoc _ _ _
  rw [hI, hE, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  have hterm := fun b => trunc_term_le (p := sqMass θ n b) measureReal_nonneg hn hL
  refine ⟨Finset.sum_nonneg fun b _ => (hterm b).1, ?_⟩
  calc _ ≤ ∑ b ∈ supp c R n, 2 * Real.exp (-(n * L) / 2) :=
        Finset.sum_le_sum fun b _ => (hterm b).2
    _ = (supp c R n).card * (2 * Real.exp (-(n * L) / 2)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 * R + 2) ^ 2 * 4 ^ n) * (2 * Real.exp (-(n * L) / 2)) := by
      gcongr
      exact card_supp_le hR n
    _ = _ := by ring

/-! ### Pointwise convergence of the information -/

/-- The squares whose mass is at most `t` times the mass of their `3 × 3` block carry `θ`-mass
at most `t · #nbr = 9 t`. -/
private theorem measure_bad_le [IsProbabilityMeasure θ] {c : ℝ × ℝ} {R : ℝ} (hb : InBall θ c R)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    θ {z | sqMass θ n (rect n n z) ≤ t * nbrMass θ n (rect n n z)} ≤
      ENNReal.ofReal (t * nbr.card) := by
  set G := (supp c R n).filter fun b => sqMass θ n b ≤ t * nbrMass θ n b
  have hsub : {z | sqMass θ n (rect n n z) ≤ t * nbrMass θ n (rect n n z)} ≤ᵐ[θ]
      ⋃ b ∈ G, rect n n ⁻¹' {b} := by
    filter_upwards [ae_rect_mem_supp hb n] with z hz hbad
    simp only [mem_iUnion, mem_preimage, mem_singleton_iff, exists_prop]
    exact ⟨rect n n z, Finset.mem_filter.2 ⟨hz, hbad⟩, rfl⟩
  calc θ {z | sqMass θ n (rect n n z) ≤ t * nbrMass θ n (rect n n z)}
      ≤ θ (⋃ b ∈ G, rect n n ⁻¹' {b}) := measure_mono_ae hsub
    _ ≤ ∑ b ∈ G, θ (rect n n ⁻¹' {b}) := measure_biUnion_finset_le _ _
    _ = ENNReal.ofReal (∑ b ∈ G, sqMass θ n b) := by
      rw [ENNReal.ofReal_sum_of_nonneg (f := sqMass θ n) fun b _ => measureReal_nonneg]
      exact Finset.sum_congr rfl fun b _ => (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (t * nbr.card) := by
      apply ENNReal.ofReal_le_ofReal
      calc ∑ b ∈ G, sqMass θ n b ≤ ∑ b ∈ G, t * nbrMass θ n b :=
            Finset.sum_le_sum fun b hb => (Finset.mem_filter.1 hb).2
        _ ≤ ∑ b ∈ supp c R n, t * nbrMass θ n b :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun b _ _ =>
              mul_nonneg ht (Finset.sum_nonneg fun _ _ => measureReal_nonneg)
        _ = t * ∑ b ∈ supp c R n, nbrMass θ n b := (Finset.mul_sum _ _ _).symm
        _ ≤ t * nbr.card := mul_le_mul_of_nonneg_left (sum_nbrMass_le n _) ht

/-- Almost surely, eventually in `n`, the information of the square containing `z` lies between
the ball information `-log θ(B(z, 2^{-n}))` and that plus `ε n`. -/
private theorem ae_eventually_info_ball [IsProbabilityMeasure θ] {c : ℝ × ℝ} {R : ℝ}
    (hb : InBall θ c R) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ z ∂θ, ∀ᶠ n : ℕ in atTop,
      -Real.log (θ.real (closedBall z ((2 : ℝ) ^ n)⁻¹)) ≤ sqInfo θ n z ∧
        sqInfo θ n z ≤ -Real.log (θ.real (closedBall z ((2 : ℝ) ^ n)⁻¹)) + n * ε := by
  have hsum : (∑' n : ℕ, θ {z | sqMass θ n (rect n n z) ≤
      Real.exp (n * -ε) * nbrMass θ n (rect n n z)}) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_
      (ENNReal.tsum_le_tsum fun n => measure_bad_le hb n (Real.exp_pos _).le)
    exact ((Real.summable_exp_nat_mul_iff.mpr (by linarith)).mul_right _).tsum_ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with z hz
  filter_upwards [hz] with n hn
  simp only [not_le] at hn
  set ball := θ.real (closedBall z ((2 : ℝ) ^ n)⁻¹)
  set q := sqMass θ n (rect n n z)
  have hqb : q ≤ ball := measureReal_mono (rect_fibre_subset_closedBall n z)
  have hbN : ball ≤ nbrMass θ n (rect n n z) := measureReal_closedBall_le_nbrMass n z
  have ht : 0 < Real.exp (n * -ε) := Real.exp_pos _
  have hball0 : 0 ≤ ball := measureReal_nonneg
  have hq : Real.exp (n * -ε) * ball < q :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hbN ht.le) hn
  have hq0 : 0 < q := lt_of_le_of_lt (mul_nonneg ht.le hball0) hq
  have hb0 : 0 < ball := hq0.trans_le hqb
  have h1 := Real.log_le_log hq0 hqb
  have h2 := Real.log_lt_log (mul_pos ht hb0) hq
  rw [Real.log_mul ht.ne' hb0.ne', Real.log_exp] at h2
  change -Real.log ball ≤ -Real.log q ∧ -Real.log q ≤ -Real.log ball + n * ε
  constructor <;> linarith

/-- The dyadic radii `2^{-n}` tend to `0` from above. -/
private theorem tendsto_dyadic_radius :
    Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2
    ⟨tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two),
      Eventually.of_forall fun n => by simp only [mem_Ioi]; positivity⟩

/-- For an exact-dimensional `θ`, almost surely the normalised information of the level-`n`
square containing `z` tends to `d log 2`. -/
private theorem ae_tendsto_sqInfo_div [IsProbabilityMeasure θ] {c : ℝ × ℝ} {R : ℝ}
    (hb : InBall θ c R) {d : ℝ} (hd : IsExactDim θ d) :
    ∀ᵐ z ∂θ, Tendsto (fun n : ℕ => sqInfo θ n z / n) atTop (𝓝 (d * Real.log 2)) := by
  have hall : ∀ᵐ z ∂θ, ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      -Real.log (θ.real (closedBall z ((2 : ℝ) ^ n)⁻¹)) ≤ sqInfo θ n z ∧
        sqInfo θ n z ≤ -Real.log (θ.real (closedBall z ((2 : ℝ) ^ n)⁻¹)) +
          n * (1 / ((k : ℝ) + 1)) :=
    ae_all_iff.2 fun k => ae_eventually_info_ball hb (by positivity)
  have hd' : ∀ᵐ z ∂θ, HasLocalDim θ z d := hd
  filter_upwards [hd', hall] with z hz hk
  have hz' : Tendsto (fun r : ℝ => Real.log (θ.real (closedBall z r)) / Real.log r)
      (𝓝[>] 0) (𝓝 d) := hz
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hB : Tendsto (fun n : ℕ => -Real.log (θ.real (closedBall z ((2 : ℝ) ^ n)⁻¹)) / n)
      atTop (𝓝 (d * Real.log 2)) := by
    refine ((hz'.comp tendsto_dyadic_radius).mul_const (Real.log 2)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    simp only [Function.comp_def, Real.log_inv, Real.log_pow]
    field_simp
  have herr : Tendsto (fun n : ℕ =>
      (sqInfo θ n z - -Real.log (θ.real (closedBall z ((2 : ℝ) ^ n)⁻¹))) / n) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    obtain ⟨k, hk'⟩ := exists_nat_one_div_lt hδ
    filter_upwards [hk k, eventually_gt_atTop 0] with n hn hnpos
    have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (by linarith [hn.1]) hnr.le),
      div_lt_iff₀ hnr]
    calc _ ≤ n * (1 / ((k : ℝ) + 1)) := by linarith [hn.2]
      _ < δ * n := by rw [mul_comm]; exact mul_lt_mul_of_pos_right hk' hnr
  have h := hB.add herr
  rw [add_zero] at h
  refine h.congr' (Eventually.of_forall fun n => ?_)
  ring

/-! ### The entropy dimension -/

/-- Exact dimension gives entropy dimension for bounded planar measures: if `θ` is a probability
measure on the plane with bounded support and exact dimension `d`, then
`ent θ (rect n n) / n → d log 2`. The planar analogue of the vendored
`ExactOverlaps.Entropy.normalized_entropy_limit_of_exact_dimension`, used by Rapaport
(arXiv:2309.03985, lines 1290 to 1294 and 1316 to 1320). -/
theorem tendsto_ent_rect_div_of_isExactDim [IsProbabilityMeasure θ] (hθ : BddSupp θ) {d : ℝ}
    (hd : IsExactDim θ d) :
    Tendsto (fun n : ℕ => ent θ (rect n n) / n) atTop (𝓝 (d * Real.log 2)) := by
  obtain ⟨c, R, hb⟩ := hθ
  have hb' : InBall θ c (max R 0) := hb.mono fun _ hz => hz.trans (le_max_left _ _)
  have hR : 0 ≤ max R 0 := le_max_right _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  set L := |d| * Real.log 2 + 4 * Real.log 4 with hLdef
  have hdl : 0 ≤ |d| * Real.log 2 := mul_nonneg (abs_nonneg d) hlog2.le
  have hL0 : 0 ≤ L := by positivity
  have hdL : d * Real.log 2 ≤ L := by
    have := mul_le_mul_of_nonneg_right (le_abs_self d) hlog2.le
    linarith
  have hlim : ∀ᵐ z ∂θ, Tendsto (fun n : ℕ => min (sqInfo θ n z / n) L) atTop
      (𝓝 (d * Real.log 2)) := by
    filter_upwards [ae_tendsto_sqInfo_div hb' hd] with z hz
    simpa only [min_eq_left hdL] using hz.min (tendsto_const_nhds (x := L))
  have hT : Tendsto (fun n : ℕ => ∫ z, min (sqInfo θ n z / n) L ∂θ) atTop
      (𝓝 (d * Real.log 2)) := by
    have h := tendsto_integral_of_dominated_convergence (fun _ => L) (fun n => ?_)
      (integrable_const L) (fun n => ae_of_all _ fun z => ?_) hlim
    · simpa using h
    · exact (((measurable_sqInfo n).div_const _).min measurable_const).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg
        (le_min (div_nonneg (sqInfo_nonneg n z) (Nat.cast_nonneg n)) hL0)]
      exact min_le_right _ _
  have herr : Tendsto (fun n : ℕ => ent θ (rect n n) / n - ∫ z, min (sqInfo θ n z / n) L ∂θ)
      atTop (𝓝 0) := by
    have ha : Real.log 4 - L / 2 < 0 := by linarith
    have hexp := ((Real.summable_exp_nat_mul_iff.mpr ha).tendsto_atTop_zero).const_mul
      (2 * (2 * max R 0 + 2) ^ 2)
    rw [mul_zero] at hexp
    refine squeeze_zero' ?_ ?_ hexp
    · filter_upwards [eventually_ge_atTop 1] with n hn using (err_bounds hb' hR hL0 hn).1
    · filter_upwards [eventually_ge_atTop 1] with n hn
      refine (err_bounds hb' hR hL0 hn).2.trans_eq ?_
      rw [show (n : ℝ) * (Real.log 4 - L / 2) = n * Real.log 4 + -(n * L) / 2 by ring,
        Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  simpa using herr.add hT

/-- Exact dimension gives the entropy dimension along natural levels `k n` with `k n / n → c > 0`:
`ent θ (rect (k n) (k n)) / n → d c log 2`. -/
theorem tendsto_ent_rect_comp_div_of_isExactDim [IsProbabilityMeasure θ] (hθ : BddSupp θ)
    {d : ℝ} (hd : IsExactDim θ d) {k : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hk : Tendsto (fun n : ℕ => (k n : ℝ) / n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => ent θ (rect (k n) (k n)) / n) atTop (𝓝 (d * Real.log 2 * c)) := by
  have hkR : Tendsto (fun n : ℕ => (k n : ℝ)) atTop atTop := by
    refine (Filter.Tendsto.pos_mul_atTop hc hk tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    exact div_mul_cancel₀ _ hn'
  have hk' : Tendsto k atTop atTop := tendsto_natCast_atTop_iff.1 hkR
  have h := ((tendsto_ent_rect_div_of_isExactDim hθ hd).comp hk').mul hk
  refine h.congr' ?_
  filter_upwards [hk'.eventually_gt_atTop 0, eventually_gt_atTop 0] with n hkn hn
  have hkn' : (k n : ℝ) ≠ 0 := by positivity
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp only [Function.comp_apply]
  field_simp

/-- Exact dimension gives the entropy dimension along the dyadic levels `lvl χ n` of an exponent
`χ > 0`: `ent θ (rect (lvl χ n) (lvl χ n)) / n → d χ`, Rapaport's
`(1/n) H(θ, 𝒟_{χ n}) → χ dim θ`. -/
theorem tendsto_ent_rect_lvl_div_of_isExactDim [IsProbabilityMeasure θ] (hθ : BddSupp θ)
    {d : ℝ} (hd : IsExactDim θ d) {χ : ℝ} (hχ : 0 < χ) :
    Tendsto (fun n : ℕ => ent θ (rect (lvl χ n) (lvl χ n)) / n) atTop (𝓝 (d * χ)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have ha : 0 ≤ χ / Real.log 2 := div_nonneg hχ.le hlog2.le
  have hlvl : ∀ n : ℕ, lvl χ n = ((⌊χ / Real.log 2 * n⌋₊ : ℕ) : ℤ) := by
    intro n
    rw [lvl, ← Int.floor_toNat,
      Int.toNat_of_nonneg (Int.floor_nonneg.2 (mul_nonneg ha (Nat.cast_nonneg n)))]
    congr 1
    push_cast
    ring
  have hk : Tendsto (fun n : ℕ => ((⌊χ / Real.log 2 * n⌋₊ : ℕ) : ℝ) / n) atTop
      (𝓝 (χ / Real.log 2)) :=
    (tendsto_nat_floor_mul_div_atTop ha).comp tendsto_natCast_atTop_atTop
  have h := tendsto_ent_rect_comp_div_of_isExactDim hθ hd (div_pos hχ hlog2) hk
  simp_rw [hlvl]
  convert h using 2
  field_simp

/-- Exact dimension gives the entropy dimension for the conformal partitions `𝒟²_{χ₂ n}`:
`ent θ (Dsq n) / n → d χ₂`, the form used by Rapaport (arXiv:2309.03985, lines 1290 to 1294 and
1316 to 1320). -/
theorem Exps.tendsto_ent_Dsq_div_of_isExactDim (χ : Exps) [IsProbabilityMeasure θ]
    (hθ : BddSupp θ) {d : ℝ} (hd : IsExactDim θ d) :
    Tendsto (fun n : ℕ => ent θ (χ.Dsq n) / n) atTop (𝓝 (d * χ.χ₂)) :=
  tendsto_ent_rect_lvl_div_of_isExactDim hθ hd χ.pos₂

end ExactDimEntropy

end BoxLike.Rapaport
