module

/-
Combinatorics of the dyadic rectangle partitions of the plane, for the proof of Rapaport's
theorem (arXiv:2309.03985, Section 2.5, lines 737 to 775 of the source, with the comparisons
(2.5) translation, (2.6) scaling and (2.7) perturbation). The fibre counts `FiberBound` and
their one-dimensional instances are in `Rapaport/Entropy/FiberBound.lean`, imported here.

* Measurability and algebra: `measurable_rect`, `measurable_hLabel`, `measurable_vLabel`,
  `Exps.measurable_E`, `Exps.measurable_E₁`, `Exps.measurable_E₂`, `Exps.measurable_Dsq`,
  `continuous_diagMap`, `measurable_diagMap`, `diagMap_comp_diagMap`, `diagMap_one_one`,
  `Exps.measurable_resc`, `Exps.resc_add`, `Exps.resc_neg_comp`, `rect_eq_pair`,
  `Exps.E_eq_pair`.
* Levels: `lvl_zero`, `lvl_mono`, `lvl_add_sub_le`, `le_lvl_add_sub`, `two_zpow_lvl_le`,
  `exp_lt_two_mul_two_zpow_lvl`, `two_zpow_neg_lvl_le`, `exp_neg_le_two_zpow_neg_lvl`,
  `lvl_tendsto_atTop`, `lvl_div_tendsto`, `two_zpow_lvl_ratio`.
* Nesting: `rect_eq_div_comp`, `rect_factor`, `fiberBound_rect_add_nat_rect`,
  `fiberBound_rect_rect_add_nat`, `fiberBound_rect_rect_of_le`, `fiberBound_rect_rect_of_ge`,
  `Exps.E_factor`, `Exps.fiberBound_E_of_le`, `Exps.E₁_eq_fst_comp_E`, `Exps.E₂_eq_snd_comp_E`,
  `Exps.E_factor_Dsq`, `Exps.fiberBound_E_E`, `Exps.fiberBound_E_Dsq`.
* Labels meeting a ball: `rect_image_closedBall_subset`, `card_Icc_quantize_le`,
  `card_rect_closedBall_le`, `exists_finset_rect_image_closedBall`,
  `Exps.exists_finset_E_image_closedBall`.
* Supports: `InRect`, `inBall_iff_inRect`, `InBall.mono`, `InBall.map_diagMap`,
  `InRect.map_diagMap`, `InBall.map_add_const`, `InBall.conv`, `InRect.conv`,
  `InBall.of_absolutelyContinuous`, `InBall.cond`, `InBall.sum`, `InBall.dirac`,
  `InBall.convk`, `InBall.convPow` and the `BddSupp` versions; `finiteLabels_of_ae_mem`,
  `finiteLabels_comp_of_ae_mem_closedBall`, `BddSupp.finiteLabels_rect` and its relatives.
* Planar commensurability: `fiberBound_rect_diagMap`, `fiberBound_rect_translate`,
  `fiberBound_rect_perturb`, each with its `_symm`, and the `hLabel`/`vLabel` versions.
* Cells: `rectCentre`, `inRect_of_ae_rect_eq`, `exp_mul_half_mesh_le`.
* Scaling (2.6): `Exps.fiberBound_E_diagMap`, `Exps.fiberBound_E_resc_neg`,
  `Exps.fiberBound_E_resc`, `HomSystem.fiberBound_E_Apow`, each with its `_symm`, and the
  `E₁`/`E₂` versions; `Exps.inBall_map_resc_of_ae`, `Exps.inBall_map_resc_cond`.
-/
public import BoxLike.Rapaport.Defs
public import BoxLike.Rapaport.Entropy.FiberBound
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

@[expose] public section

namespace BoxLike.Rapaport

open MeasureTheory ProbabilityTheory Filter Topology
open ExactOverlaps.Entropy
open scoped ENNReal

/-! ### Measurability and the diagonal maps -/

section Measurability

/-- The rectangle labels are measurable (Section 2.5 of the source). -/
@[fun_prop] theorem measurable_rect (i j : ℤ) : Measurable (rect i j) := by
  unfold rect
  fun_prop

/-- The horizontal labels are measurable. -/
@[fun_prop] theorem measurable_hLabel (i : ℤ) : Measurable (hLabel i) := by
  unfold hLabel
  fun_prop

/-- The vertical labels are measurable. -/
@[fun_prop] theorem measurable_vLabel (j : ℤ) : Measurable (vLabel j) := by
  unfold vLabel
  fun_prop

/-- The rectangle label is the pair of the horizontal and the vertical label. -/
theorem rect_eq_pair (i j : ℤ) (z : ℝ × ℝ) : rect i j z = (hLabel i z, vLabel j z) := rfl

/-- The diagonal map `(x, y) ↦ (s x, t y)` evaluated. -/
@[simp] theorem diagMap_apply (s t : ℝ) (z : ℝ × ℝ) : diagMap s t z = (s * z.1, t * z.2) := rfl

/-- The diagonal map is continuous. -/
@[fun_prop] theorem continuous_diagMap (s t : ℝ) : Continuous (diagMap s t) := by
  unfold diagMap
  fun_prop

/-- The diagonal map is measurable. -/
@[fun_prop] theorem measurable_diagMap (s t : ℝ) : Measurable (diagMap s t) :=
  (continuous_diagMap s t).measurable

/-- Diagonal maps compose by multiplying their entries. -/
theorem diagMap_comp_diagMap (s t s' t' : ℝ) :
    diagMap s t ∘ diagMap s' t' = diagMap (s * s') (t * t') := by
  funext z
  simp [mul_assoc]

/-- The identity is the diagonal map with entries `1`. -/
theorem diagMap_one_one : diagMap 1 1 = id := by
  funext z
  simp

/-- The diagonal map is additive. -/
theorem diagMap_add (s t : ℝ) (z w : ℝ × ℝ) :
    diagMap s t (z + w) = diagMap s t z + diagMap s t w := by
  ext <;> simp [mul_add]

/-- The diagonal map commutes with differences. -/
theorem diagMap_sub (s t : ℝ) (z w : ℝ × ℝ) :
    diagMap s t (z - w) = diagMap s t z - diagMap s t w := by
  ext <;> simp [mul_sub]

/-- The supremum norm grows by at most the larger entry under a diagonal map. -/
theorem norm_diagMap_le (s t : ℝ) (w : ℝ × ℝ) : ‖diagMap s t w‖ ≤ max |s| |t| * ‖w‖ := by
  simp only [Prod.norm_def, diagMap_apply, Real.norm_eq_abs, abs_mul]
  have h0 : 0 ≤ max |s| |t| := le_max_of_le_left (abs_nonneg s)
  apply max_le
  · exact mul_le_mul (le_max_left _ _) (le_max_left _ _) (abs_nonneg _) h0
  · exact mul_le_mul (le_max_right _ _) (le_max_right _ _) (abs_nonneg _) h0

namespace Exps

variable (χ : Exps)

/-- The partition `ℰ_n` is the rectangle partition at the levels `lvl χ₁ n` and `lvl χ₂ n`. -/
theorem E_eq_rect (n : ℤ) : χ.E n = rect (lvl χ.χ₁ n) (lvl χ.χ₂ n) := rfl

/-- The label of `ℰ_n` is the pair of the labels of `π₁⁻¹ ℰ_n` and `π₂⁻¹ ℰ_n`. -/
theorem E_eq_pair (n : ℤ) (z : ℝ × ℝ) : χ.E n z = (χ.E₁ n z, χ.E₂ n z) := rfl

/-- The partition `ℰ_n` is measurable. -/
@[fun_prop] theorem measurable_E (n : ℤ) : Measurable (χ.E n) := measurable_rect _ _

/-- The partition `π₁⁻¹ ℰ_n` is measurable. -/
@[fun_prop] theorem measurable_E₁ (n : ℤ) : Measurable (χ.E₁ n) := measurable_hLabel _

/-- The partition `π₂⁻¹ ℰ_n` is measurable. -/
@[fun_prop] theorem measurable_E₂ (n : ℤ) : Measurable (χ.E₂ n) := measurable_vLabel _

/-- The partition `𝒟²_{χ₂ n}` is measurable. -/
@[fun_prop] theorem measurable_Dsq (n : ℤ) : Measurable (χ.Dsq n) := measurable_rect _ _

/-- Rapaport's `A_χ^i` is measurable. -/
@[fun_prop] theorem measurable_resc (i : ℤ) : Measurable (χ.resc i) := measurable_diagMap _ _

/-- Rapaport's `A_χ^i` is continuous. -/
theorem continuous_resc (i : ℤ) : Continuous (χ.resc i) := continuous_diagMap _ _

/-- `A_χ^0` is the identity. -/
theorem resc_zero : χ.resc 0 = id := by
  rw [resc, Int.cast_zero, mul_zero, mul_zero, Real.exp_zero, diagMap_one_one]

/-- `A_χ^{i + j} = A_χ^i A_χ^j`. -/
theorem resc_add (i j : ℤ) : χ.resc (i + j) = χ.resc i ∘ χ.resc j := by
  rw [resc, resc, resc, diagMap_comp_diagMap, ← Real.exp_add, ← Real.exp_add]
  push_cast
  ring_nf

/-- `A_χ^{-i} A_χ^i` is the identity. -/
theorem resc_neg_comp (i : ℤ) : χ.resc (-i) ∘ χ.resc i = id := by
  rw [← resc_add, neg_add_cancel, resc_zero]

/-- `A_χ^i A_χ^{-i}` is the identity. -/
theorem resc_comp_neg (i : ℤ) : χ.resc i ∘ χ.resc (-i) = id := by
  rw [← resc_add, add_neg_cancel, resc_zero]

end Exps

end Measurability

/-! ### Dyadic levels -/

section Level

/-- `log 2 > 0`, the factor between natural and dyadic levels. -/
private theorem log_two_pos' : 0 < Real.log 2 := Real.log_pos one_lt_two

/-- A power of two as an exponential. -/
theorem two_zpow_eq_exp (k : ℤ) : (2 : ℝ) ^ k = Real.exp (k * Real.log 2) := by
  rw [← Real.rpow_intCast, Real.rpow_def_of_pos two_pos, mul_comm]

/-- The level of the planar level `0` is `0`. -/
@[simp] theorem lvl_zero (χ : ℝ) : lvl χ 0 = 0 := by simp [lvl]

/-- For `χ > 0` the dyadic level is monotone in the planar level. -/
theorem lvl_mono {χ : ℝ} (hχ : 0 < χ) : Monotone (lvl χ) := fun _ _ h =>
  Int.floor_mono ((div_le_div_iff_of_pos_right log_two_pos').2
    (mul_le_mul_of_nonneg_left (Int.cast_le.2 h) hχ.le))

/-- The level grows by at most `χ m / log 2 + 1` over `m` planar levels. -/
theorem lvl_add_sub_le (χ : ℝ) (n m : ℤ) :
    (lvl χ (n + m) - lvl χ n : ℝ) ≤ χ * m / Real.log 2 + 1 := by
  have ha := Int.floor_le (χ * ((n + m : ℤ) : ℝ) / Real.log 2)
  have hb := Int.lt_floor_add_one (χ * (n : ℝ) / Real.log 2)
  have he : χ * ((n + m : ℤ) : ℝ) / Real.log 2 = χ * n / Real.log 2 + χ * m / Real.log 2 := by
    push_cast
    ring
  unfold lvl
  linarith

/-- The level grows by at least `χ m / log 2 - 1` over `m` planar levels. -/
theorem le_lvl_add_sub (χ : ℝ) (n m : ℤ) :
    χ * m / Real.log 2 - 1 ≤ (lvl χ (n + m) - lvl χ n : ℝ) := by
  have ha := Int.lt_floor_add_one (χ * ((n + m : ℤ) : ℝ) / Real.log 2)
  have hb := Int.floor_le (χ * (n : ℝ) / Real.log 2)
  have he : χ * ((n + m : ℤ) : ℝ) / Real.log 2 = χ * n / Real.log 2 + χ * m / Real.log 2 := by
    push_cast
    ring
  unfold lvl
  linarith

/-- `2^{lvl χ n} ≤ e^{χ n}`: the mesh `2^{-lvl χ n}` is at least `e^{-χ n}`. -/
theorem two_zpow_lvl_le (χ : ℝ) (n : ℤ) : (2 : ℝ) ^ lvl χ n ≤ Real.exp (χ * n) := by
  rw [two_zpow_eq_exp]
  exact Real.exp_le_exp.2 ((le_div_iff₀ log_two_pos').1 (Int.floor_le _))

/-- `e^{χ n} < 2 · 2^{lvl χ n}`: the mesh `2^{-lvl χ n}` is below `2 e^{-χ n}`. -/
theorem exp_lt_two_mul_two_zpow_lvl (χ : ℝ) (n : ℤ) :
    Real.exp (χ * n) < 2 * (2 : ℝ) ^ lvl χ n := by
  have h := (div_lt_iff₀ log_two_pos').1 (Int.lt_floor_add_one (χ * (n : ℝ) / Real.log 2))
  have e : (2 : ℝ) * 2 ^ lvl χ n = (2 : ℝ) ^ (lvl χ n + 1) := by
    rw [zpow_add_one₀ two_ne_zero, mul_comm]
  rw [e, two_zpow_eq_exp]
  push_cast
  exact Real.exp_lt_exp.2 h

/-- The mesh `2^{-lvl χ n}` is at most `2 e^{-χ n}`. -/
theorem two_zpow_neg_lvl_le (χ : ℝ) (n : ℤ) :
    (2 : ℝ) ^ (-lvl χ n) ≤ 2 * Real.exp (-χ * n) := by
  have h := exp_lt_two_mul_two_zpow_lvl χ n
  have hp := zpow_pos (two_pos (α := ℝ)) (lvl χ n)
  rw [zpow_neg, neg_mul, Real.exp_neg]
  rw [inv_le_iff_one_le_mul₀ hp]
  have he := Real.exp_pos (χ * n)
  calc (1 : ℝ) = Real.exp (χ * n) * (Real.exp (χ * n))⁻¹ := (mul_inv_cancel₀ he.ne').symm
    _ ≤ 2 * 2 ^ lvl χ n * (Real.exp (χ * n))⁻¹ :=
        mul_le_mul_of_nonneg_right h.le (inv_nonneg.2 he.le)
    _ = 2 * (Real.exp (χ * n))⁻¹ * 2 ^ lvl χ n := by ring

/-- The mesh `2^{-lvl χ n}` is at least `e^{-χ n}`. -/
theorem exp_neg_le_two_zpow_neg_lvl (χ : ℝ) (n : ℤ) :
    Real.exp (-χ * n) ≤ (2 : ℝ) ^ (-lvl χ n) := by
  rw [zpow_neg, neg_mul, Real.exp_neg]
  exact inv_anti₀ (zpow_pos two_pos _) (two_zpow_lvl_le χ n)

/-- For `χ > 0` the dyadic level tends to infinity with the planar level. -/
theorem lvl_tendsto_atTop {χ : ℝ} (hχ : 0 < χ) :
    Tendsto (fun n : ℕ => lvl χ n) atTop atTop := by
  have h : Tendsto (fun n : ℕ => χ * (n : ℝ) / Real.log 2) atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hχ).atTop_div_const log_two_pos'
  refine (tendsto_floor_atTop.comp h).congr fun n => ?_
  simp [lvl]

/-- `lvl χ n / n → χ / log 2`. -/
theorem lvl_div_tendsto (χ : ℝ) :
    Tendsto (fun n : ℕ => (lvl χ n : ℝ) / n) atTop (𝓝 (χ / Real.log 2)) := by
  have hlow : Tendsto (fun n : ℕ => χ / Real.log 2 - 1 / (n : ℝ)) atTop
      (𝓝 (χ / Real.log 2)) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h := Int.lt_floor_add_one (χ * ((n : ℤ) : ℝ) / Real.log 2)
    rw [Int.cast_natCast] at h
    rw [le_div_iff₀ hn', sub_mul, one_div_mul_cancel hn'.ne']
    have e : χ / Real.log 2 * n = χ * n / Real.log 2 := by ring
    unfold lvl
    rw [Int.cast_natCast]
    linarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h := Int.floor_le (χ * ((n : ℤ) : ℝ) / Real.log 2)
    rw [Int.cast_natCast] at h
    rw [div_le_iff₀ hn']
    have e : χ / Real.log 2 * n = χ * n / Real.log 2 := by ring
    unfold lvl
    rw [Int.cast_natCast]
    linarith

/-- The ratio behind the scaling comparison (2.6) of the source: `2^{lvl χ (n+m)} e^{-χ n}` and
`2^{lvl χ m}` agree up to a factor `2`. -/
theorem two_zpow_lvl_ratio (χ : ℝ) (n m : ℤ) :
    1 / 2 ≤ (2 : ℝ) ^ lvl χ (n + m) * Real.exp (-χ * n) / (2 : ℝ) ^ lvl χ m ∧
      (2 : ℝ) ^ lvl χ (n + m) * Real.exp (-χ * n) / (2 : ℝ) ^ lvl χ m ≤ 2 := by
  have hA := two_zpow_lvl_le χ (n + m)
  have hA' := exp_lt_two_mul_two_zpow_lvl χ (n + m)
  have hB := two_zpow_lvl_le χ m
  have hB' := exp_lt_two_mul_two_zpow_lvl χ m
  have hBpos : 0 < (2 : ℝ) ^ lvl χ m := zpow_pos two_pos _
  have hE : Real.exp (χ * ((n + m : ℤ) : ℝ)) * Real.exp (-χ * n) = Real.exp (χ * m) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have he := Real.exp_pos (-χ * n)
  have ha1 : (2 : ℝ) ^ lvl χ (n + m) * Real.exp (-χ * n) ≤ Real.exp (χ * m) := by
    rw [← hE]
    exact mul_le_mul_of_nonneg_right hA he.le
  have ha2 : Real.exp (χ * m) < 2 * ((2 : ℝ) ^ lvl χ (n + m) * Real.exp (-χ * n)) := by
    rw [← hE, ← mul_assoc]
    exact mul_lt_mul_of_pos_right hA' he
  rw [le_div_iff₀ hBpos, div_le_iff₀ hBpos]
  constructor <;> linarith

/-- `⌊a⌋ - ⌊b⌋ ≤ a - b + 1`. -/
private theorem floor_sub_floor_le (a b : ℝ) : ((⌊a⌋ - ⌊b⌋ : ℤ) : ℝ) ≤ a - b + 1 := by
  have := Int.floor_le a
  have := Int.lt_floor_add_one b
  push_cast
  linarith

/-- A nonnegative integer `d ≤ x / log 2 + 1` has `2^d ≤ 2 e^x`. -/
private theorem two_pow_toNat_le {d : ℤ} {x : ℝ} (hd : 0 ≤ d)
    (h : (d : ℝ) ≤ x / Real.log 2 + 1) : (2 : ℝ) ^ d.toNat ≤ 2 * Real.exp x := by
  rw [← zpow_natCast, Int.toNat_of_nonneg hd, two_zpow_eq_exp]
  have h' : (d : ℝ) * Real.log 2 ≤ x + Real.log 2 := by
    have := mul_le_mul_of_nonneg_right h log_two_pos'.le
    rwa [add_mul, div_mul_cancel₀ _ log_two_pos'.ne', one_mul] at this
  calc Real.exp (d * Real.log 2) ≤ Real.exp (x + Real.log 2) := Real.exp_le_exp.2 h'
    _ = 2 * Real.exp x := by rw [Real.exp_add, Real.exp_log two_pos, mul_comm]

/-- The number `2^{lvl χ m - lvl χ n}` of horizontal children satisfies the bound
`2 e^{χ (m - n)}` for `n ≤ m`. -/
theorem two_pow_toNat_sub_lvl_le {χ : ℝ} (hχ : 0 < χ) {n m : ℤ} (hnm : n ≤ m) :
    (2 : ℝ) ^ (lvl χ m - lvl χ n).toNat ≤ 2 * Real.exp (χ * ((m : ℝ) - n)) := by
  refine two_pow_toNat_le (sub_nonneg.2 (lvl_mono hχ hnm)) ?_
  have h := lvl_add_sub_le χ n (m - n)
  rw [add_sub_cancel] at h
  push_cast at h ⊢
  exact h

end Level

/-! ### Nesting of the rectangle partitions -/

section Nesting

/-- Combining two coordinate fibre counts into a planar one. -/
private theorem fiberBound_prod_coord {f₁ g₁ f₂ g₂ : ℝ → ℤ} {N₁ N₂ : ℕ}
    (h₁ : FiberBound f₁ g₁ N₁) (h₂ : FiberBound f₂ g₂ N₂) :
    FiberBound (fun z : ℝ × ℝ => (f₁ z.1, f₂ z.2)) (fun z => (g₁ z.1, g₂ z.2)) (N₁ * N₂) :=
  (h₁.comp_left Prod.fst).prod (h₂.comp_left Prod.snd)

/-- Nesting of dyadic rectangles: the coarse label is the fine label divided by `2^a` and
`2^b`. -/
theorem rect_eq_div_comp (i j : ℤ) (a b : ℕ) :
    rect i j = (fun kl : ℤ × ℤ => (kl.1 / (2 ^ a : ℕ), kl.2 / (2 ^ b : ℕ))) ∘
      rect (i + a) (j + b) := by
  funext z
  exact Prod.ext (dyadicQuantize_add_nat i a z.1) (dyadicQuantize_add_nat j b z.2)

/-- A coarser rectangle partition is a function of a finer one. -/
theorem rect_factor {i j i' j' : ℤ} (hi : i ≤ i') (hj : j ≤ j') :
    ∃ φ : ℤ × ℤ → ℤ × ℤ, rect i j = φ ∘ rect i' j' := by
  have h := rect_eq_div_comp i j (i' - i).toNat (j' - j).toNat
  have e₁ : i + ((i' - i).toNat : ℤ) = i' := by omega
  have e₂ : j + ((j' - j).toNat : ℤ) = j' := by omega
  rw [e₁, e₂] at h
  exact ⟨_, h⟩

/-- A finer rectangle meets one coarser rectangle. -/
theorem fiberBound_rect_add_nat_rect (i j : ℤ) (a b : ℕ) :
    FiberBound (rect (i + a) (j + b)) (rect i j) 1 :=
  FiberBound.of_factor (rect_eq_div_comp i j a b)

/-- A rectangle at levels `(i, j)` has `2^a 2^b` children at levels `(i + a, j + b)`. -/
theorem fiberBound_rect_rect_add_nat (i j : ℤ) (a b : ℕ) :
    FiberBound (rect i j) (rect (i + a) (j + b)) (2 ^ a * 2 ^ b) :=
  fiberBound_prod_coord (fiberBound_dyadicQuantize_add_nat i a)
    (fiberBound_dyadicQuantize_add_nat j b)

/-- A rectangle at levels `(i, j)` has `2^{i'-i} 2^{j'-j}` children at levels `(i', j')`. -/
theorem fiberBound_rect_rect_of_le {i j i' j' : ℤ} (hi : i ≤ i') (hj : j ≤ j') :
    FiberBound (rect i j) (rect i' j') (2 ^ (i' - i).toNat * 2 ^ (j' - j).toNat) := by
  have h := fiberBound_rect_rect_add_nat i j (i' - i).toNat (j' - j).toNat
  have e₁ : i + ((i' - i).toNat : ℤ) = i' := by omega
  have e₂ : j + ((j' - j).toNat : ℤ) = j' := by omega
  rwa [e₁, e₂] at h

/-- A rectangle at finer levels meets one rectangle at coarser levels. -/
theorem fiberBound_rect_rect_of_ge {i j i' j' : ℤ} (hi : i ≤ i') (hj : j ≤ j') :
    FiberBound (rect i' j') (rect i j) 1 :=
  let ⟨_, h⟩ := rect_factor hi hj
  FiberBound.of_factor h

namespace Exps

variable (χ : Exps)

/-- `lvl χ₁ n ≤ lvl χ₂ n` for `n ≥ 0`. -/
theorem lvl_le_lvl {n : ℤ} (hn : 0 ≤ n) : lvl χ.χ₁ n ≤ lvl χ.χ₂ n :=
  Int.floor_mono ((div_le_div_iff_of_pos_right log_two_pos').2
    (mul_le_mul_of_nonneg_right χ.lt.le (Int.cast_nonneg hn)))

/-- `ℰ_n` is a function of `ℰ_m` for `n ≤ m`. -/
theorem E_factor {n m : ℤ} (hnm : n ≤ m) : ∃ φ : ℤ × ℤ → ℤ × ℤ, χ.E n = φ ∘ χ.E m :=
  rect_factor (lvl_mono χ.pos hnm) (lvl_mono χ.pos₂ hnm)

/-- A cell of `ℰ_m` meets one cell of `ℰ_n` for `n ≤ m`. -/
theorem fiberBound_E_of_le {n m : ℤ} (hnm : n ≤ m) : FiberBound (χ.E m) (χ.E n) 1 :=
  let ⟨_, h⟩ := χ.E_factor hnm
  FiberBound.of_factor h

/-- `π₁⁻¹ ℰ_n` is the first coordinate of `ℰ_n`. -/
theorem E₁_eq_fst_comp_E (n : ℤ) : χ.E₁ n = Prod.fst ∘ χ.E n := rfl

/-- `π₂⁻¹ ℰ_n` is the second coordinate of `ℰ_n`. -/
theorem E₂_eq_snd_comp_E (n : ℤ) : χ.E₂ n = Prod.snd ∘ χ.E n := rfl

/-- `ℰ_n` is a function of `𝒟²_{χ₂ n}` for `n ≥ 0`. -/
theorem E_factor_Dsq {n : ℤ} (hn : 0 ≤ n) : ∃ φ : ℤ × ℤ → ℤ × ℤ, χ.E n = φ ∘ χ.Dsq n :=
  rect_factor (χ.lvl_le_lvl hn) le_rfl

/-- Child count from `ℰ_n` to `ℰ_m`, `n ≤ m`: at most `4 e^{(χ₁ + χ₂)(m - n)}` (Section 2.5 of
the source). -/
theorem fiberBound_E_E {n m : ℤ} (hnm : n ≤ m) :
    FiberBound (χ.E n) (χ.E m) ⌊4 * Real.exp ((χ.χ₁ + χ.χ₂) * ((m : ℝ) - n))⌋₊ := by
  refine (fiberBound_rect_rect_of_le (lvl_mono χ.pos hnm) (lvl_mono χ.pos₂ hnm)).mono
    (Nat.le_floor ?_)
  have h₁ := two_pow_toNat_sub_lvl_le χ.pos hnm
  have h₂ := two_pow_toNat_sub_lvl_le χ.pos₂ hnm
  push_cast
  calc (2 : ℝ) ^ (lvl χ.χ₁ m - lvl χ.χ₁ n).toNat * 2 ^ (lvl χ.χ₂ m - lvl χ.χ₂ n).toNat
      ≤ (2 * Real.exp (χ.χ₁ * ((m : ℝ) - n))) * (2 * Real.exp (χ.χ₂ * ((m : ℝ) - n))) :=
        mul_le_mul h₁ h₂ (by positivity) (by positivity)
    _ = 4 * Real.exp ((χ.χ₁ + χ.χ₂) * ((m : ℝ) - n)) := by
        rw [add_mul, Real.exp_add]
        ring

/-- The bound of `fiberBound_E_E` as a real number: `⌊4 e^{(χ₁+χ₂)(m-n)}⌋₊ ≤ 4 e^{(χ₁+χ₂)(m-n)}`. -/
theorem floor_four_exp_le (n m : ℤ) :
    (⌊4 * Real.exp ((χ.χ₁ + χ.χ₂) * ((m : ℝ) - n))⌋₊ : ℝ) ≤
      4 * Real.exp ((χ.χ₁ + χ.χ₂) * ((m : ℝ) - n)) :=
  Nat.floor_le (by positivity)

/-- Child count from `ℰ_n` to `𝒟²_{χ₂ n}`, `n ≥ 0`: at most `2 e^{(χ₂ - χ₁) n}`. -/
theorem fiberBound_E_Dsq {n : ℤ} (hn : 0 ≤ n) :
    FiberBound (χ.E n) (χ.Dsq n) ⌊2 * Real.exp ((χ.χ₂ - χ.χ₁) * n)⌋₊ := by
  refine (fiberBound_rect_rect_of_le (χ.lvl_le_lvl hn) le_rfl).mono (Nat.le_floor ?_)
  rw [sub_self, Int.toNat_zero, pow_zero, mul_one]
  push_cast
  refine two_pow_toNat_le (sub_nonneg.2 (χ.lvl_le_lvl hn)) ?_
  have h := floor_sub_floor_le (χ.χ₂ * n / Real.log 2) (χ.χ₁ * n / Real.log 2)
  have e : χ.χ₂ * n / Real.log 2 - χ.χ₁ * n / Real.log 2 = (χ.χ₂ - χ.χ₁) * n / Real.log 2 := by
    ring
  rw [e] at h
  exact h

/-- The bound of `fiberBound_E_Dsq` as a real number. -/
theorem floor_two_exp_le (n : ℤ) :
    (⌊2 * Real.exp ((χ.χ₂ - χ.χ₁) * n)⌋₊ : ℝ) ≤ 2 * Real.exp ((χ.χ₂ - χ.χ₁) * n) :=
  Nat.floor_le (by positivity)

/-- `ℰ_0` is the partition into unit squares. -/
theorem E_zero : χ.E 0 = rect 0 0 := by
  rw [E_eq_rect, lvl_zero, lvl_zero]

end Exps

end Nesting

/-! ### Labels meeting a ball -/

section Counting

/-- The one-dimensional dyadic label is monotone. -/
theorem dyadicQuantize_mono (i : ℤ) : Monotone (dyadicQuantize i) := fun _ _ hxy =>
  Int.floor_mono (mul_le_mul_of_nonneg_left hxy (dyadic_scale_pos i).le)

/-- The supremum norm of a planar vector is at most `R` iff both coordinates are. -/
theorem norm_le_iff_abs_le (z : ℝ × ℝ) (R : ℝ) : ‖z‖ ≤ R ↔ |z.1| ≤ R ∧ |z.2| ≤ R := by
  rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]

/-- The dyadic labels at level `i` of `[a, b]` number at most `2^i (b - a) + 2`. -/
theorem card_Icc_quantize_le {i : ℤ} {a b : ℝ} (hab : a ≤ b) :
    ((Finset.Icc (dyadicQuantize i a) (dyadicQuantize i b)).card : ℝ) ≤ 2 ^ i * (b - a) + 2 := by
  have hle := dyadicQuantize_mono i hab
  rw [Int.card_Icc]
  have h0 : (0 : ℤ) ≤ dyadicQuantize i b + 1 - dyadicQuantize i a := by omega
  have e : (((dyadicQuantize i b + 1 - dyadicQuantize i a).toNat : ℕ) : ℝ) =
      ((dyadicQuantize i b + 1 - dyadicQuantize i a : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  rw [e]
  have h1 := Int.floor_le ((2 : ℝ) ^ i * b)
  have h2 := Int.lt_floor_add_one ((2 : ℝ) ^ i * a)
  unfold dyadicQuantize
  push_cast
  rw [mul_sub]
  linarith

/-- `rect i j` sends the closed sup-norm ball of radius `R` about `c` into a product of two
intervals of labels. -/
theorem rect_image_closedBall_subset (i j : ℤ) (c : ℝ × ℝ) (R : ℝ) :
    rect i j '' Metric.closedBall c R ⊆
      ↑(Finset.Icc (dyadicQuantize i (c.1 - R)) (dyadicQuantize i (c.1 + R)) ×ˢ
        Finset.Icc (dyadicQuantize j (c.2 - R)) (dyadicQuantize j (c.2 + R))) := by
  rintro _ ⟨z, hz, rfl⟩
  rw [mem_closedBall_iff_norm, norm_le_iff_abs_le, Prod.fst_sub, Prod.snd_sub, abs_le,
    abs_le] at hz
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  simp only [Finset.coe_product, Finset.coe_Icc, Set.mem_prod, Set.mem_Icc, rect]
  exact ⟨⟨dyadicQuantize_mono i (by linarith), dyadicQuantize_mono i (by linarith)⟩,
    ⟨dyadicQuantize_mono j (by linarith), dyadicQuantize_mono j (by linarith)⟩⟩

/-- The labels of `rect i j` meeting a closed ball of radius `R ≥ 0` number at most
`(2^i 2R + 2)(2^j 2R + 2)`. -/
theorem card_rect_closedBall_le (i j : ℤ) (c : ℝ × ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ((Finset.Icc (dyadicQuantize i (c.1 - R)) (dyadicQuantize i (c.1 + R)) ×ˢ
        Finset.Icc (dyadicQuantize j (c.2 - R)) (dyadicQuantize j (c.2 + R))).card : ℝ) ≤
      (2 ^ i * (2 * R) + 2) * (2 ^ j * (2 * R) + 2) := by
  have hi := card_Icc_quantize_le (i := i) (by linarith : c.1 - R ≤ c.1 + R)
  have hj := card_Icc_quantize_le (i := j) (by linarith : c.2 - R ≤ c.2 + R)
  rw [show c.1 + R - (c.1 - R) = 2 * R by ring] at hi
  rw [show c.2 + R - (c.2 - R) = 2 * R by ring] at hj
  rw [Finset.card_product, Nat.cast_mul]
  exact mul_le_mul hi hj (Nat.cast_nonneg _) (by positivity)

/-- A finite set of labels of `rect i j` covering the image of a closed ball, with its count. -/
theorem exists_finset_rect_image_closedBall (i j : ℤ) (c : ℝ × ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ s : Finset (ℤ × ℤ), rect i j '' Metric.closedBall c R ⊆ s ∧
      (s.card : ℝ) ≤ (2 ^ i * (2 * R) + 2) * (2 ^ j * (2 * R) + 2) :=
  ⟨_, rect_image_closedBall_subset i j c R, card_rect_closedBall_le i j c hR⟩

/-- A finite set of horizontal labels covering the image of a closed ball, with its count. -/
theorem exists_finset_hLabel_image_closedBall (i : ℤ) (c : ℝ × ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ s : Finset ℤ, hLabel i '' Metric.closedBall c R ⊆ s ∧
      (s.card : ℝ) ≤ 2 ^ i * (2 * R) + 2 := by
  refine ⟨Finset.Icc (dyadicQuantize i (c.1 - R)) (dyadicQuantize i (c.1 + R)), ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    have := rect_image_closedBall_subset i i c R ⟨z, hz, rfl⟩
    simp only [Finset.coe_product, Set.mem_prod] at this
    exact this.1
  · have h := card_Icc_quantize_le (i := i) (by linarith : c.1 - R ≤ c.1 + R)
    rwa [show c.1 + R - (c.1 - R) = 2 * R by ring] at h

/-- A finite set of vertical labels covering the image of a closed ball, with its count. -/
theorem exists_finset_vLabel_image_closedBall (j : ℤ) (c : ℝ × ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ s : Finset ℤ, vLabel j '' Metric.closedBall c R ⊆ s ∧
      (s.card : ℝ) ≤ 2 ^ j * (2 * R) + 2 := by
  refine ⟨Finset.Icc (dyadicQuantize j (c.2 - R)) (dyadicQuantize j (c.2 + R)), ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    have := rect_image_closedBall_subset j j c R ⟨z, hz, rfl⟩
    simp only [Finset.coe_product, Set.mem_prod] at this
    exact this.2
  · have h := card_Icc_quantize_le (i := j) (by linarith : c.2 - R ≤ c.2 + R)
    rwa [show c.2 + R - (c.2 - R) = 2 * R by ring] at h

/-- The cells of `ℰ_n` meeting a closed ball of radius `R ≥ 0` number at most
`(e^{χ₁ n} 2R + 2)(e^{χ₂ n} 2R + 2)`. -/
theorem Exps.exists_finset_E_image_closedBall (χ : Exps) (n : ℤ) (c : ℝ × ℝ) {R : ℝ}
    (hR : 0 ≤ R) :
    ∃ s : Finset (ℤ × ℤ), χ.E n '' Metric.closedBall c R ⊆ s ∧
      (s.card : ℝ) ≤ (Real.exp (χ.χ₁ * n) * (2 * R) + 2) * (Real.exp (χ.χ₂ * n) * (2 * R) + 2) := by
  obtain ⟨s, hs, hcard⟩ := exists_finset_rect_image_closedBall (lvl χ.χ₁ n) (lvl χ.χ₂ n) c hR
  refine ⟨s, hs, hcard.trans ?_⟩
  have h₁ := mul_le_mul_of_nonneg_right (two_zpow_lvl_le χ.χ₁ n) (by linarith : 0 ≤ 2 * R)
  have h₂ := mul_le_mul_of_nonneg_right (two_zpow_lvl_le χ.χ₂ n) (by linarith : 0 ≤ 2 * R)
  have p₁ : 0 ≤ (2 : ℝ) ^ lvl χ.χ₁ n * (2 * R) := by positivity
  have p₂ : 0 ≤ (2 : ℝ) ^ lvl χ.χ₂ n * (2 * R) := by positivity
  exact mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)

end Counting

/-! ### Supports: balls, rectangles and finite labels -/

section Support

variable {θ θ' : Measure (ℝ × ℝ)} {c c' : ℝ × ℝ} {R R' R₁ R₂ R₁' R₂' : ℝ}

/-- Closed sup-norm balls are measurable. -/
private theorem measurableSet_norm_sub_le (c : ℝ × ℝ) (R : ℝ) :
    MeasurableSet {z : ℝ × ℝ | ‖z - c‖ ≤ R} :=
  measurableSet_le (by fun_prop) measurable_const

/-- Closed rectangles are measurable. -/
private theorem measurableSet_inRect (c : ℝ × ℝ) (R₁ R₂ : ℝ) :
    MeasurableSet {z : ℝ × ℝ | |z.1 - c.1| ≤ R₁ ∧ |z.2 - c.2| ≤ R₂} := by
  rw [Set.ofPred_and]
  exact (measurableSet_le (f := fun z : ℝ × ℝ => |z.1 - c.1|) (by fun_prop)
    measurable_const).inter
    (measurableSet_le (f := fun z : ℝ × ℝ => |z.2 - c.2|) (by fun_prop) measurable_const)

/-- `θ` is carried by the rectangle `[c.1 - R₁, c.1 + R₁] × [c.2 - R₂, c.2 + R₂]`: the
coordinatewise form of `InBall`. -/
def InRect (θ : Measure (ℝ × ℝ)) (c : ℝ × ℝ) (R₁ R₂ : ℝ) : Prop :=
  ∀ᵐ z ∂θ, |z.1 - c.1| ≤ R₁ ∧ |z.2 - c.2| ≤ R₂

/-- A sup-norm ball is a square. -/
theorem inBall_iff_inRect : InBall θ c R ↔ InRect θ c R R := by
  unfold InBall InRect
  simp only [norm_le_iff_abs_le, Prod.fst_sub, Prod.snd_sub]

/-- A measure carried by a ball is carried by its square. -/
theorem InBall.inRect (h : InBall θ c R) : InRect θ c R R := inBall_iff_inRect.1 h

/-- A measure carried by a rectangle is carried by the ball of the larger half-side. -/
theorem InRect.inBall (h : InRect θ c R₁ R₂) : InBall θ c (max R₁ R₂) := by
  filter_upwards [h] with z hz
  rw [norm_le_iff_abs_le, Prod.fst_sub, Prod.snd_sub]
  exact ⟨hz.1.trans (le_max_left _ _), hz.2.trans (le_max_right _ _)⟩

/-- Enlarging the half-sides of a carrying rectangle. -/
theorem InRect.mono (h : InRect θ c R₁ R₂) (h₁ : R₁ ≤ R₁') (h₂ : R₂ ≤ R₂') :
    InRect θ c R₁' R₂' := by
  filter_upwards [h] with z hz using ⟨hz.1.trans h₁, hz.2.trans h₂⟩

/-- A diagonal map multiplies the half-sides of a carrying rectangle by `|s|` and `|t|`. -/
theorem InRect.map_diagMap (h : InRect θ c R₁ R₂) (s t : ℝ) :
    InRect (θ.map (diagMap s t)) (diagMap s t c) (|s| * R₁) (|t| * R₂) := by
  unfold InRect
  rw [ae_map_iff (measurable_diagMap s t).aemeasurable (measurableSet_inRect _ _ _)]
  filter_upwards [h] with z hz
  simp only [diagMap_apply, ← mul_sub, abs_mul]
  exact ⟨mul_le_mul_of_nonneg_left hz.1 (abs_nonneg s),
    mul_le_mul_of_nonneg_left hz.2 (abs_nonneg t)⟩

/-- A measure carried by a ball is carried by the larger concentric ball. -/
theorem InBall.mono (h : InBall θ c R) (hR : R ≤ R') : InBall θ c R' := by
  filter_upwards [h] with z hz using hz.trans hR

/-- Moving the centre of a carrying ball. -/
theorem InBall.recentre (h : InBall θ c R) (c' : ℝ × ℝ) : InBall θ c' (R + ‖c - c'‖) := by
  filter_upwards [h] with z hz
  calc ‖z - c'‖ ≤ ‖z - c‖ + ‖c - c'‖ := norm_sub_le_norm_sub_add_norm_sub z c c'
    _ ≤ R + ‖c - c'‖ := by linarith

/-- A measure carried by a ball is a.e. in the closed ball. -/
theorem InBall.ae_mem_closedBall (h : InBall θ c R) : ∀ᵐ z ∂θ, z ∈ Metric.closedBall c R :=
  Filter.Eventually.mono h fun _ hz => mem_closedBall_iff_norm.2 hz

/-- A diagonal map multiplies the radius of a carrying ball by at most `max |s| |t|`. -/
theorem InBall.map_diagMap (h : InBall θ c R) (s t : ℝ) :
    InBall (θ.map (diagMap s t)) (diagMap s t c) (max |s| |t| * R) := by
  unfold InBall at *
  rw [ae_map_iff (measurable_diagMap s t).aemeasurable (measurableSet_norm_sub_le _ _)]
  filter_upwards [h] with z hz
  rw [← diagMap_sub]
  exact (norm_diagMap_le s t (z - c)).trans
    (mul_le_mul_of_nonneg_left hz (le_max_of_le_left (abs_nonneg s)))

/-- A translation moves the centre of a carrying ball. -/
theorem InBall.map_add_const (h : InBall θ c R) (v : ℝ × ℝ) :
    InBall (θ.map (· + v)) (c + v) R := by
  unfold InBall at *
  rw [ae_map_iff (measurable_add_const v).aemeasurable (measurableSet_norm_sub_le _ _)]
  filter_upwards [h] with z hz
  rwa [add_sub_add_right_eq_sub]

/-- Convolution adds centres and radii of carrying balls. -/
theorem InBall.conv [SFinite θ'] (h : InBall θ c R) (h' : InBall θ' c' R') :
    InBall (θ ∗ θ') (c + c') (R + R') := by
  unfold InBall at *
  rw [Measure.conv, ae_map_iff measurable_add.aemeasurable (measurableSet_norm_sub_le _ _)]
  have h₁ : ∀ᵐ p ∂θ.prod θ', ‖p.1 - c‖ ≤ R := Measure.quasiMeasurePreserving_fst.ae h
  have h₂ : ∀ᵐ p ∂θ.prod θ', ‖p.2 - c'‖ ≤ R' := Measure.quasiMeasurePreserving_snd.ae h'
  filter_upwards [h₁, h₂] with p hp₁ hp₂
  calc ‖p.1 + p.2 - (c + c')‖ = ‖(p.1 - c) + (p.2 - c')‖ := by rw [add_sub_add_comm]
    _ ≤ ‖p.1 - c‖ + ‖p.2 - c'‖ := norm_add_le _ _
    _ ≤ R + R' := add_le_add hp₁ hp₂

/-- A translation moves the centre of a carrying rectangle. -/
theorem InRect.map_add_const (h : InRect θ c R₁ R₂) (v : ℝ × ℝ) :
    InRect (θ.map (· + v)) (c + v) R₁ R₂ := by
  unfold InRect at *
  rw [ae_map_iff (measurable_add_const v).aemeasurable (measurableSet_inRect _ _ _)]
  filter_upwards [h] with z hz
  simpa only [Prod.fst_add, Prod.snd_add, add_sub_add_right_eq_sub] using hz

/-- Convolution adds centres and half-sides of carrying rectangles. -/
theorem InRect.conv [SFinite θ'] (h : InRect θ c R₁ R₂) (h' : InRect θ' c' R₁' R₂') :
    InRect (θ ∗ θ') (c + c') (R₁ + R₁') (R₂ + R₂') := by
  unfold InRect at *
  rw [Measure.conv, ae_map_iff measurable_add.aemeasurable (measurableSet_inRect _ _ _)]
  have h₁ := Measure.quasiMeasurePreserving_fst (μ := θ) (ν := θ').ae h
  have h₂ := Measure.quasiMeasurePreserving_snd (μ := θ) (ν := θ').ae h'
  filter_upwards [h₁, h₂] with p hp₁ hp₂
  simp only [Prod.fst_add, Prod.snd_add, add_sub_add_comm]
  exact ⟨(abs_add_le _ _).trans (add_le_add hp₁.1 hp₂.1),
    (abs_add_le _ _).trans (add_le_add hp₁.2 hp₂.2)⟩

/-- An absolutely continuous measure is carried by the same ball. -/
theorem InBall.of_absolutelyContinuous (h : InBall θ c R) (hac : θ' ≪ θ) : InBall θ' c R :=
  hac.ae_le h

/-- A conditional measure `θ[|s]` is carried by the same ball. -/
theorem InBall.cond (h : InBall θ c R) (s : Set (ℝ × ℝ)) : InBall (θ[|s]) c R :=
  h.of_absolutelyContinuous cond_absolutelyContinuous

/-- A component `θ_{f = b}` is carried by the same ball. -/
theorem InBall.comp {L : Type*} (h : InBall θ c R) (f : ℝ × ℝ → L) (b : L) :
    InBall (comp θ f b) c R :=
  h.cond _

/-- A restriction is carried by the same ball. -/
theorem InBall.restrict (h : InBall θ c R) (s : Set (ℝ × ℝ)) : InBall (θ.restrict s) c R :=
  ae_restrict_of_ae h

/-- The zero measure is carried by every ball. -/
theorem InBall.zero : InBall 0 c R := by
  unfold InBall
  rw [ae_zero]
  exact Filter.eventually_bot

/-- A sum of measures carried by a ball is carried by it. -/
theorem InBall.add (h : InBall θ c R) (h' : InBall θ' c R) : InBall (θ + θ') c R :=
  ae_add_measure_iff.2 ⟨h, h'⟩

/-- A multiple of a measure carried by a ball is carried by it. -/
theorem InBall.smul (h : InBall θ c R) (a : ℝ≥0∞) : InBall (a • θ) c R :=
  Measure.ae_smul_measure h a

/-- A finite mixture of measures carried by a ball is carried by it. -/
theorem InBall.sum {ι : Type*} (s : Finset ι) (w : ι → ℝ≥0∞)
    {θ : ι → Measure (ℝ × ℝ)} (h : ∀ i ∈ s, InBall (θ i) c R) :
    InBall (∑ i ∈ s, w i • θ i) c R :=
  Finset.sum_induction _ (fun μ => InBall μ c R) (fun _ _ ha hb => ha.add hb) InBall.zero
    fun i hi => (h i hi).smul (w i)

/-- A Dirac mass at a point of the closed ball is carried by it. -/
theorem InBall.dirac {x : ℝ × ℝ} (h : ‖x - c‖ ≤ R) : InBall (Measure.dirac x) c R := by
  unfold InBall
  rw [ae_dirac_iff (measurableSet_norm_sub_le _ _)]
  exact h

/-- A Dirac mass is carried by every ball of nonnegative radius about its atom. -/
theorem InBall.dirac_self (hR : 0 ≤ R) : InBall (Measure.dirac c) c R :=
  InBall.dirac (by rwa [sub_self, norm_zero])

/-- The convolution of `k` s-finite planar measures is s-finite. -/
instance sFinite_convk : ∀ (k : ℕ) (θ : Fin k → Measure (ℝ × ℝ)) [∀ i, SFinite (θ i)],
    SFinite (convk k θ)
  | 0, _, _ => by
    show SFinite (Measure.dirac 0)
    infer_instance
  | k + 1, θ, _ => by
    have : ∀ i, SFinite (Fin.tail θ i) := fun i => inferInstanceAs (SFinite (θ i.succ))
    have := sFinite_convk k (Fin.tail θ)
    show SFinite (θ 0 ∗ convk k (Fin.tail θ))
    infer_instance

/-- The convolution of `k` measures carried by balls is carried by the ball whose centre and
radius are the sums of theirs. -/
theorem InBall.convk : ∀ {k : ℕ} {θ : Fin k → Measure (ℝ × ℝ)} [∀ i, SFinite (θ i)]
    {c : Fin k → ℝ × ℝ} {R : Fin k → ℝ}, (∀ i, InBall (θ i) (c i) (R i)) →
    InBall (Rapaport.convk k θ) (∑ i, c i) (∑ i, R i)
  | 0, θ, _, c, R, _ => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact InBall.dirac_self le_rfl
  | k + 1, θ, _, c, R, h => by
    have : ∀ i, SFinite (Fin.tail θ i) := fun i => inferInstanceAs (SFinite (θ i.succ))
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    show InBall (θ 0 ∗ Rapaport.convk k (Fin.tail θ)) _ _
    exact (h 0).conv (InBall.convk (θ := Fin.tail θ) (c := fun i => c i.succ)
      (R := fun i => R i.succ) fun i => h i.succ)

/-- The `k`-fold self-convolution of a measure carried by a ball of radius `R` about `c` is
carried by the ball of radius `k R` about `k c`. -/
theorem InBall.convPow [SFinite θ] (h : InBall θ c R) (k : ℕ) :
    InBall (convPow θ k) (k • c) (k * R) := by
  have hc : ∑ _i : Fin k, c = k • c := by simp
  have hR : ∑ _i : Fin k, R = k * R := by simp
  rw [← hc, ← hR]
  exact InBall.convk fun _ => h

/-- Bounded support passes to absolutely continuous measures. -/
theorem BddSupp.of_absolutelyContinuous (h : BddSupp θ) (hac : θ' ≪ θ) : BddSupp θ' :=
  let ⟨c, R, hθ⟩ := h
  ⟨c, R, hθ.of_absolutelyContinuous hac⟩

/-- Bounded support passes to conditional measures. -/
theorem BddSupp.cond (h : BddSupp θ) (s : Set (ℝ × ℝ)) : BddSupp (θ[|s]) :=
  h.of_absolutelyContinuous cond_absolutelyContinuous

/-- Bounded support passes to images under diagonal maps. -/
theorem BddSupp.map_diagMap (h : BddSupp θ) (s t : ℝ) : BddSupp (θ.map (diagMap s t)) :=
  let ⟨_, _, hθ⟩ := h
  ⟨_, _, hθ.map_diagMap s t⟩

/-- Bounded support passes to translates. -/
theorem BddSupp.map_add_const (h : BddSupp θ) (v : ℝ × ℝ) : BddSupp (θ.map (· + v)) :=
  let ⟨_, _, hθ⟩ := h
  ⟨_, _, hθ.map_add_const v⟩

/-- Bounded support passes to convolutions. -/
theorem BddSupp.conv [SFinite θ'] (h : BddSupp θ) (h' : BddSupp θ') : BddSupp (θ ∗ θ') :=
  let ⟨_, _, hθ⟩ := h
  let ⟨_, _, hθ'⟩ := h'
  ⟨_, _, hθ.conv hθ'⟩

/-- Dirac masses have bounded support. -/
theorem BddSupp.dirac (x : ℝ × ℝ) : BddSupp (Measure.dirac x) := ⟨x, 0, InBall.dirac_self le_rfl⟩

/-- The zero measure has bounded support. -/
theorem BddSupp.zero : BddSupp (0 : Measure (ℝ × ℝ)) := ⟨0, 0, InBall.zero⟩

/-- Bounded support passes to sums. -/
theorem BddSupp.add (h : BddSupp θ) (h' : BddSupp θ') : BddSupp (θ + θ') := by
  obtain ⟨c, R, hθ⟩ := h
  obtain ⟨c', R', hθ'⟩ := h'
  exact ⟨0, max (R + ‖c - 0‖) (R' + ‖c' - 0‖),
    ((hθ.recentre 0).mono (le_max_left _ _)).add ((hθ'.recentre 0).mono (le_max_right _ _))⟩

/-- Bounded support passes to multiples. -/
theorem BddSupp.smul (h : BddSupp θ) (a : ℝ≥0∞) : BddSupp (a • θ) :=
  let ⟨_, _, hθ⟩ := h
  ⟨_, _, hθ.smul a⟩

/-- Finite mixtures of measures of bounded support have bounded support. -/
theorem BddSupp.sum {ι : Type*} (s : Finset ι) (w : ι → ℝ≥0∞)
    {θ : ι → Measure (ℝ × ℝ)} (h : ∀ i ∈ s, BddSupp (θ i)) : BddSupp (∑ i ∈ s, w i • θ i) :=
  Finset.sum_induction _ BddSupp (fun _ _ ha hb => ha.add hb) BddSupp.zero
    fun i hi => (h i hi).smul (w i)

/-- Bounded support passes to convolutions of `k` measures. -/
theorem BddSupp.convk {k : ℕ} {θ : Fin k → Measure (ℝ × ℝ)} [∀ i, SFinite (θ i)]
    (h : ∀ i, BddSupp (θ i)) : BddSupp (Rapaport.convk k θ) := by
  choose c R hθ using h
  exact ⟨_, _, InBall.convk hθ⟩

/-- Bounded support passes to self-convolutions. -/
theorem BddSupp.convPow [SFinite θ] (h : BddSupp θ) (k : ℕ) : BddSupp (convPow θ k) :=
  let ⟨_, _, hθ⟩ := h
  ⟨_, _, hθ.convPow k⟩

/-- Labels a.e. in a finite set: only finitely many labels carry mass. -/
theorem finiteLabels_of_ae_mem {X L : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → L}
    {s : Set L} (hs : s.Finite) (h : ∀ᵐ x ∂μ, f x ∈ s) : FiniteLabels μ f := by
  refine hs.subset fun b hb => ?_
  by_contra hbs
  apply Function.mem_support.1 hb
  refine measure_mono_null (fun x hx => ?_) (ae_iff.1 h)
  have hx' : f x = b := hx
  show f x ∉ s
  rwa [hx']

/-- A labelling `f ∘ ψ` has finitely many labels of positive mass when `ψ` maps a set of full
measure into a closed ball whose image under `f` is finite. -/
theorem finiteLabels_comp_of_ae_mem_closedBall {X L : Type*} [MeasurableSpace X]
    {μ : Measure X} {ψ : X → ℝ × ℝ} {f : ℝ × ℝ → L}
    (hf : (f '' Metric.closedBall c R).Finite)
    (hψ : ∀ᵐ x ∂μ, ψ x ∈ Metric.closedBall c R) : FiniteLabels μ (f ∘ ψ) :=
  finiteLabels_of_ae_mem hf (hψ.mono fun x hx => ⟨ψ x, hx, rfl⟩)

/-- The image of a closed ball under `rect i j` is finite. -/
theorem rect_image_closedBall_finite (i j : ℤ) (c : ℝ × ℝ) (R : ℝ) :
    (rect i j '' Metric.closedBall c R).Finite :=
  (Finset.finite_toSet _).subset (rect_image_closedBall_subset i j c R)

/-- The image of a closed ball under a coarsening `φ ∘ rect i j` is finite. -/
theorem comp_rect_image_closedBall_finite {L : Type*} (φ : ℤ × ℤ → L) (i j : ℤ)
    (c : ℝ × ℝ) (R : ℝ) : ((φ ∘ rect i j) '' Metric.closedBall c R).Finite := by
  rw [Set.image_comp]
  exact (rect_image_closedBall_finite i j c R).image φ

/-- `rect i j ∘ ψ` has finitely many labels of positive mass when `ψ` maps a set of full measure
into a closed ball. -/
theorem finiteLabels_rect_comp_of_ae_mem_closedBall {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {ψ : X → ℝ × ℝ} (i j : ℤ)
    (hψ : ∀ᵐ x ∂μ, ψ x ∈ Metric.closedBall c R) : FiniteLabels μ (rect i j ∘ ψ) :=
  finiteLabels_comp_of_ae_mem_closedBall (rect_image_closedBall_finite i j c R) hψ

/-- A measure of bounded support has finitely many labels of positive mass for any coarsening
`φ ∘ rect i j`. -/
theorem BddSupp.finiteLabels_comp_rect {L : Type*} (h : BddSupp θ) (φ : ℤ × ℤ → L)
    (i j : ℤ) : FiniteLabels θ (φ ∘ rect i j) := by
  obtain ⟨c, R, hθ⟩ := h
  exact finiteLabels_comp_of_ae_mem_closedBall (ψ := id)
    (comp_rect_image_closedBall_finite φ i j c R) hθ.ae_mem_closedBall

/-- `FiniteLabels θ (rect i j)` for `θ` of bounded support. -/
theorem BddSupp.finiteLabels_rect (h : BddSupp θ) (i j : ℤ) : FiniteLabels θ (rect i j) :=
  h.finiteLabels_comp_rect id i j

/-- `FiniteLabels θ (hLabel i)` for `θ` of bounded support. -/
theorem BddSupp.finiteLabels_hLabel (h : BddSupp θ) (i : ℤ) : FiniteLabels θ (hLabel i) :=
  h.finiteLabels_comp_rect Prod.fst i i

/-- `FiniteLabels θ (vLabel j)` for `θ` of bounded support. -/
theorem BddSupp.finiteLabels_vLabel (h : BddSupp θ) (j : ℤ) : FiniteLabels θ (vLabel j) :=
  h.finiteLabels_comp_rect Prod.snd j j

/-- `FiniteLabels θ (χ.E n)` for `θ` of bounded support. -/
theorem BddSupp.finiteLabels_E (h : BddSupp θ) (χ : Exps) (n : ℤ) : FiniteLabels θ (χ.E n) :=
  h.finiteLabels_rect _ _

/-- `FiniteLabels θ (χ.E₁ n)` for `θ` of bounded support. -/
theorem BddSupp.finiteLabels_E₁ (h : BddSupp θ) (χ : Exps) (n : ℤ) :
    FiniteLabels θ (χ.E₁ n) :=
  h.finiteLabels_hLabel _

/-- `FiniteLabels θ (χ.E₂ n)` for `θ` of bounded support. -/
theorem BddSupp.finiteLabels_E₂ (h : BddSupp θ) (χ : Exps) (n : ℤ) :
    FiniteLabels θ (χ.E₂ n) :=
  h.finiteLabels_vLabel _

/-- `FiniteLabels θ (χ.Dsq n)` for `θ` of bounded support. -/
theorem BddSupp.finiteLabels_Dsq (h : BddSupp θ) (χ : Exps) (n : ℤ) :
    FiniteLabels θ (χ.Dsq n) :=
  h.finiteLabels_rect _ _

end Support

/-! ### Commensurability in the plane -/

section Planar

variable {X : Type*}

/-- Scaling count for one coordinate, in both directions. -/
private theorem fiberBound_quantize_mul {i i' : ℤ} {s : ℝ} (h₁ : 1 / 2 ≤ 2 ^ i * |s| / 2 ^ i')
    (h₂ : 2 ^ i * |s| / 2 ^ i' ≤ 2) :
    FiberBound (fun x => dyadicQuantize i (s * x)) (dyadicQuantize i') 3 ∧
      FiberBound (dyadicQuantize i') (fun x => dyadicQuantize i (s * x)) 3 := by
  have e : |(2 : ℝ) ^ i * s| / |(2 : ℝ) ^ i'| = 2 ^ i * |s| / 2 ^ i' := by
    rw [abs_mul, abs_of_pos (dyadic_scale_pos i), abs_of_pos (dyadic_scale_pos i')]
  have key₁ := fiberBound_floor_mul_of_ratio (s := (2 : ℝ) ^ i') (t := 2 ^ i * s)
    (by rw [e]; exact h₁) (by rw [e]; exact h₂)
  have key₂ := fiberBound_floor_mul_of_ratio_symm (s := (2 : ℝ) ^ i') (t := 2 ^ i * s)
    (by rw [e]; exact h₁) (by rw [e]; exact h₂)
  refine ⟨key₂.congr (fun x => ?_) (fun _ => rfl), key₁.congr (fun _ => rfl) (fun x => ?_)⟩ <;>
  · show ⌊(2 : ℝ) ^ i * (s * x)⌋ = ⌊2 ^ i * s * x⌋
    rw [mul_assoc]

/-- Translation count for one coordinate, in both directions. -/
private theorem fiberBound_quantize_add (i : ℤ) (c : ℝ) :
    FiberBound (fun x => dyadicQuantize i (x + c)) (dyadicQuantize i) 2 ∧
      FiberBound (dyadicQuantize i) (fun x => dyadicQuantize i (x + c)) 2 :=
  ⟨fiberBound_floor_mul_add_symm _ c, fiberBound_floor_mul_add _ c⟩

/-- Scaling count of Rapaport (2.6) in the plane: if both mesh ratios `2^i |s| / 2^{i'}` and
`2^j |t| / 2^{j'}` lie in `[1/2, 2]`, a cell of `rect i j ∘ diagMap s t` meets at most `9` cells
of `rect i' j'`. -/
theorem fiberBound_rect_diagMap {i j i' j' : ℤ} {s t : ℝ}
    (h₁ : 1 / 2 ≤ 2 ^ i * |s| / 2 ^ i') (h₂ : 2 ^ i * |s| / 2 ^ i' ≤ 2)
    (h₃ : 1 / 2 ≤ 2 ^ j * |t| / 2 ^ j') (h₄ : 2 ^ j * |t| / 2 ^ j' ≤ 2) :
    FiberBound (rect i j ∘ diagMap s t) (rect i' j') 9 :=
  fiberBound_prod_coord (fiberBound_quantize_mul h₁ h₂).1 (fiberBound_quantize_mul h₃ h₄).1

/-- The reverse scaling count: a cell of `rect i' j'` meets at most `9` cells of
`rect i j ∘ diagMap s t`. -/
theorem fiberBound_rect_diagMap_symm {i j i' j' : ℤ} {s t : ℝ}
    (h₁ : 1 / 2 ≤ 2 ^ i * |s| / 2 ^ i') (h₂ : 2 ^ i * |s| / 2 ^ i' ≤ 2)
    (h₃ : 1 / 2 ≤ 2 ^ j * |t| / 2 ^ j') (h₄ : 2 ^ j * |t| / 2 ^ j' ≤ 2) :
    FiberBound (rect i' j') (rect i j ∘ diagMap s t) 9 :=
  fiberBound_prod_coord (fiberBound_quantize_mul h₁ h₂).2 (fiberBound_quantize_mul h₃ h₄).2

/-- Scaling count for the horizontal labels. -/
theorem fiberBound_hLabel_diagMap {i i' : ℤ} {s : ℝ} (t : ℝ)
    (h₁ : 1 / 2 ≤ 2 ^ i * |s| / 2 ^ i') (h₂ : 2 ^ i * |s| / 2 ^ i' ≤ 2) :
    FiberBound (hLabel i ∘ diagMap s t) (hLabel i') 3 :=
  (fiberBound_quantize_mul h₁ h₂).1.comp_left Prod.fst

/-- The reverse scaling count for the horizontal labels. -/
theorem fiberBound_hLabel_diagMap_symm {i i' : ℤ} {s : ℝ} (t : ℝ)
    (h₁ : 1 / 2 ≤ 2 ^ i * |s| / 2 ^ i') (h₂ : 2 ^ i * |s| / 2 ^ i' ≤ 2) :
    FiberBound (hLabel i') (hLabel i ∘ diagMap s t) 3 :=
  (fiberBound_quantize_mul h₁ h₂).2.comp_left Prod.fst

/-- Scaling count for the vertical labels. -/
theorem fiberBound_vLabel_diagMap {j j' : ℤ} (s : ℝ) {t : ℝ}
    (h₁ : 1 / 2 ≤ 2 ^ j * |t| / 2 ^ j') (h₂ : 2 ^ j * |t| / 2 ^ j' ≤ 2) :
    FiberBound (vLabel j ∘ diagMap s t) (vLabel j') 3 :=
  (fiberBound_quantize_mul h₁ h₂).1.comp_left Prod.snd

/-- The reverse scaling count for the vertical labels. -/
theorem fiberBound_vLabel_diagMap_symm {j j' : ℤ} (s : ℝ) {t : ℝ}
    (h₁ : 1 / 2 ≤ 2 ^ j * |t| / 2 ^ j') (h₂ : 2 ^ j * |t| / 2 ^ j' ≤ 2) :
    FiberBound (vLabel j') (vLabel j ∘ diagMap s t) 3 :=
  (fiberBound_quantize_mul h₁ h₂).2.comp_left Prod.snd

/-- Translation count of Rapaport (2.5) in the plane: a cell of `rect i j ∘ (· + c)` meets at
most `4` cells of `rect i j`. -/
theorem fiberBound_rect_translate (i j : ℤ) (c : ℝ × ℝ) :
    FiberBound (rect i j ∘ (· + c)) (rect i j) 4 :=
  fiberBound_prod_coord (fiberBound_quantize_add i c.1).1 (fiberBound_quantize_add j c.2).1

/-- The reverse translation count: a cell of `rect i j` meets at most `4` cells of
`rect i j ∘ (· + c)`. -/
theorem fiberBound_rect_translate_symm (i j : ℤ) (c : ℝ × ℝ) :
    FiberBound (rect i j) (rect i j ∘ (· + c)) 4 :=
  fiberBound_prod_coord (fiberBound_quantize_add i c.1).2 (fiberBound_quantize_add j c.2).2

/-- Translation count for the horizontal labels. -/
theorem fiberBound_hLabel_translate (i : ℤ) (c : ℝ × ℝ) :
    FiberBound (hLabel i ∘ (· + c)) (hLabel i) 2 :=
  (fiberBound_quantize_add i c.1).1.comp_left Prod.fst

/-- The reverse translation count for the horizontal labels. -/
theorem fiberBound_hLabel_translate_symm (i : ℤ) (c : ℝ × ℝ) :
    FiberBound (hLabel i) (hLabel i ∘ (· + c)) 2 :=
  (fiberBound_quantize_add i c.1).2.comp_left Prod.fst

/-- Translation count for the vertical labels. -/
theorem fiberBound_vLabel_translate (j : ℤ) (c : ℝ × ℝ) :
    FiberBound (vLabel j ∘ (· + c)) (vLabel j) 2 :=
  (fiberBound_quantize_add j c.2).1.comp_left Prod.snd

/-- The reverse translation count for the vertical labels. -/
theorem fiberBound_vLabel_translate_symm (j : ℤ) (c : ℝ × ℝ) :
    FiberBound (vLabel j) (vLabel j ∘ (· + c)) 2 :=
  (fiberBound_quantize_add j c.2).2.comp_left Prod.snd

/-- Perturbation count of Rapaport (2.7) in the plane: coordinatewise errors of at most `C₁`
horizontal and `C₂` vertical meshes give the count `(2 ⌈C₁⌉₊ + 3)(2 ⌈C₂⌉₊ + 3)`. -/
theorem fiberBound_rect_perturb {F G : X → ℝ × ℝ} {i j : ℤ} {C₁ C₂ : ℝ}
    (h₁ : ∀ x, |(F x).1 - (G x).1| ≤ C₁ * 2 ^ (-i))
    (h₂ : ∀ x, |(F x).2 - (G x).2| ≤ C₂ * 2 ^ (-j)) :
    FiberBound (rect i j ∘ F) (rect i j ∘ G) ((2 * ⌈C₁⌉₊ + 3) * (2 * ⌈C₂⌉₊ + 3)) :=
  (fiberBound_dyadicQuantize_perturb (F := fun x => (F x).1) (G := fun x => (G x).1) h₁).prod
    (fiberBound_dyadicQuantize_perturb (F := fun x => (F x).2) (G := fun x => (G x).2) h₂)

/-- The reverse perturbation count in the plane. -/
theorem fiberBound_rect_perturb_symm {F G : X → ℝ × ℝ} {i j : ℤ} {C₁ C₂ : ℝ}
    (h₁ : ∀ x, |(F x).1 - (G x).1| ≤ C₁ * 2 ^ (-i))
    (h₂ : ∀ x, |(F x).2 - (G x).2| ≤ C₂ * 2 ^ (-j)) :
    FiberBound (rect i j ∘ G) (rect i j ∘ F) ((2 * ⌈C₁⌉₊ + 3) * (2 * ⌈C₂⌉₊ + 3)) :=
  fiberBound_rect_perturb (fun x => by rw [abs_sub_comm]; exact h₁ x)
    (fun x => by rw [abs_sub_comm]; exact h₂ x)

/-- Perturbation count for the horizontal labels. -/
theorem fiberBound_hLabel_perturb {F G : X → ℝ × ℝ} {i : ℤ} {C : ℝ}
    (h : ∀ x, |(F x).1 - (G x).1| ≤ C * 2 ^ (-i)) :
    FiberBound (hLabel i ∘ F) (hLabel i ∘ G) (2 * ⌈C⌉₊ + 3) :=
  fiberBound_dyadicQuantize_perturb (F := fun x => (F x).1) (G := fun x => (G x).1) h

/-- The reverse perturbation count for the horizontal labels. -/
theorem fiberBound_hLabel_perturb_symm {F G : X → ℝ × ℝ} {i : ℤ} {C : ℝ}
    (h : ∀ x, |(F x).1 - (G x).1| ≤ C * 2 ^ (-i)) :
    FiberBound (hLabel i ∘ G) (hLabel i ∘ F) (2 * ⌈C⌉₊ + 3) :=
  fiberBound_hLabel_perturb fun x => by rw [abs_sub_comm]; exact h x

/-- Perturbation count for the vertical labels. -/
theorem fiberBound_vLabel_perturb {F G : X → ℝ × ℝ} {j : ℤ} {C : ℝ}
    (h : ∀ x, |(F x).2 - (G x).2| ≤ C * 2 ^ (-j)) :
    FiberBound (vLabel j ∘ F) (vLabel j ∘ G) (2 * ⌈C⌉₊ + 3) :=
  fiberBound_dyadicQuantize_perturb (F := fun x => (F x).2) (G := fun x => (G x).2) h

/-- The reverse perturbation count for the vertical labels. -/
theorem fiberBound_vLabel_perturb_symm {F G : X → ℝ × ℝ} {j : ℤ} {C : ℝ}
    (h : ∀ x, |(F x).2 - (G x).2| ≤ C * 2 ^ (-j)) :
    FiberBound (vLabel j ∘ G) (vLabel j ∘ F) (2 * ⌈C⌉₊ + 3) :=
  fiberBound_vLabel_perturb fun x => by rw [abs_sub_comm]; exact h x

end Planar

/-! ### Cells and their sizes -/

section Cells

/-- The centre `((k + 1/2) 2^{-i}, (l + 1/2) 2^{-j})` of the dyadic rectangle labelled
`c = (k, l)` at the levels `(i, j)`. -/
noncomputable def rectCentre (i j : ℤ) (c : ℤ × ℤ) : ℝ × ℝ :=
  (((c.1 : ℝ) + 1 / 2) / 2 ^ i, ((c.2 : ℝ) + 1 / 2) / 2 ^ j)

/-- A point of the dyadic cell `k` at level `i` lies within half a mesh of its centre. -/
theorem abs_sub_cellCentre_le {i k : ℤ} {x : ℝ} (h : dyadicQuantize i x = k) :
    |x - ((k : ℝ) + 1 / 2) / 2 ^ i| ≤ 2 ^ (-i) / 2 := by
  have hpos := dyadic_scale_pos i
  have hx := Int.floor_eq_iff.1 h
  have h1 : |(2 : ℝ) ^ i * x - (k + 1 / 2)| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have h2 : x - ((k : ℝ) + 1 / 2) / 2 ^ i =
      ((2 : ℝ) ^ i)⁻¹ * ((2 : ℝ) ^ i * x - (k + 1 / 2)) := by
    field_simp
  rw [h2, abs_mul, abs_inv, abs_of_pos hpos, zpow_neg]
  calc ((2 : ℝ) ^ i)⁻¹ * |(2 : ℝ) ^ i * x - (k + 1 / 2)| ≤ ((2 : ℝ) ^ i)⁻¹ * (1 / 2) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hpos.le)
    _ = ((2 : ℝ) ^ i)⁻¹ / 2 := by ring

/-- A measure carried by the cell `c` of `rect i j` is carried by the rectangle of half-sides
`2^{-i}/2` and `2^{-j}/2` about the centre of the cell. -/
theorem inRect_of_ae_rect_eq {θ : Measure (ℝ × ℝ)} {i j : ℤ} {c : ℤ × ℤ}
    (h : ∀ᵐ z ∂θ, rect i j z = c) :
    InRect θ (rectCentre i j c) (2 ^ (-i) / 2) (2 ^ (-j) / 2) := by
  filter_upwards [h] with z hz
  rw [Prod.ext_iff] at hz
  exact ⟨abs_sub_cellCentre_le hz.1, abs_sub_cellCentre_le hz.2⟩

/-- `e^{χ n}` times half the mesh `2^{-lvl χ n}` is at most `1`. -/
theorem exp_mul_half_mesh_le (χ : ℝ) (n : ℤ) :
    Real.exp (χ * n) * ((2 : ℝ) ^ (-lvl χ n) / 2) ≤ 1 := by
  have h := exp_lt_two_mul_two_zpow_lvl χ n
  have hp := zpow_pos (two_pos (α := ℝ)) (lvl χ n)
  rw [zpow_neg]
  calc Real.exp (χ * n) * (((2 : ℝ) ^ lvl χ n)⁻¹ / 2) =
        Real.exp (χ * n) / (2 * 2 ^ lvl χ n) := by ring
    _ ≤ 1 := (div_le_one (by positivity)).2 h.le

end Cells

/-! ### Scaling of the non-conformal partitions -/

section Scaling

namespace Exps

variable (χ : Exps)

/-- Scaling (2.6) of the source: for `|s| = e^{-χ₁ n}` and `|t| = e^{-χ₂ n}`, a cell of
`ℰ_{n+m} ∘ diag(s, t)` meets at most `9` cells of `ℰ_m`. -/
theorem fiberBound_E_diagMap {n m : ℤ} {s t : ℝ} (hs : |s| = Real.exp (-χ.χ₁ * n))
    (ht : |t| = Real.exp (-χ.χ₂ * n)) : FiberBound (χ.E (n + m) ∘ diagMap s t) (χ.E m) 9 := by
  have h₁ := two_zpow_lvl_ratio χ.χ₁ n m
  have h₂ := two_zpow_lvl_ratio χ.χ₂ n m
  rw [← hs] at h₁
  rw [← ht] at h₂
  exact fiberBound_rect_diagMap h₁.1 h₁.2 h₂.1 h₂.2

/-- The reverse of `fiberBound_E_diagMap`: a cell of `ℰ_m` meets at most `9` cells of
`ℰ_{n+m} ∘ diag(s, t)`. -/
theorem fiberBound_E_diagMap_symm {n m : ℤ} {s t : ℝ} (hs : |s| = Real.exp (-χ.χ₁ * n))
    (ht : |t| = Real.exp (-χ.χ₂ * n)) : FiberBound (χ.E m) (χ.E (n + m) ∘ diagMap s t) 9 := by
  have h₁ := two_zpow_lvl_ratio χ.χ₁ n m
  have h₂ := two_zpow_lvl_ratio χ.χ₂ n m
  rw [← hs] at h₁
  rw [← ht] at h₂
  exact fiberBound_rect_diagMap_symm h₁.1 h₁.2 h₂.1 h₂.2

/-- Scaling (2.6) for `π₁⁻¹ ℰ`: for `|s| = e^{-χ₁ n}`, a cell of `π₁⁻¹ ℰ_{n+m} ∘ diag(s, t)`
meets at most `3` cells of `π₁⁻¹ ℰ_m`. -/
theorem fiberBound_E₁_diagMap {n m : ℤ} {s : ℝ} (t : ℝ) (hs : |s| = Real.exp (-χ.χ₁ * n)) :
    FiberBound (χ.E₁ (n + m) ∘ diagMap s t) (χ.E₁ m) 3 := by
  have h₁ := two_zpow_lvl_ratio χ.χ₁ n m
  rw [← hs] at h₁
  exact fiberBound_hLabel_diagMap t h₁.1 h₁.2

/-- The reverse of `fiberBound_E₁_diagMap`. -/
theorem fiberBound_E₁_diagMap_symm {n m : ℤ} {s : ℝ} (t : ℝ)
    (hs : |s| = Real.exp (-χ.χ₁ * n)) : FiberBound (χ.E₁ m) (χ.E₁ (n + m) ∘ diagMap s t) 3 := by
  have h₁ := two_zpow_lvl_ratio χ.χ₁ n m
  rw [← hs] at h₁
  exact fiberBound_hLabel_diagMap_symm t h₁.1 h₁.2

/-- Scaling (2.6) for `π₂⁻¹ ℰ`: for `|t| = e^{-χ₂ n}`, a cell of `π₂⁻¹ ℰ_{n+m} ∘ diag(s, t)`
meets at most `3` cells of `π₂⁻¹ ℰ_m`. -/
theorem fiberBound_E₂_diagMap {n m : ℤ} (s : ℝ) {t : ℝ} (ht : |t| = Real.exp (-χ.χ₂ * n)) :
    FiberBound (χ.E₂ (n + m) ∘ diagMap s t) (χ.E₂ m) 3 := by
  have h₂ := two_zpow_lvl_ratio χ.χ₂ n m
  rw [← ht] at h₂
  exact fiberBound_vLabel_diagMap s h₂.1 h₂.2

/-- The reverse of `fiberBound_E₂_diagMap`. -/
theorem fiberBound_E₂_diagMap_symm {n m : ℤ} (s : ℝ) {t : ℝ}
    (ht : |t| = Real.exp (-χ.χ₂ * n)) : FiberBound (χ.E₂ m) (χ.E₂ (n + m) ∘ diagMap s t) 3 := by
  have h₂ := two_zpow_lvl_ratio χ.χ₂ n m
  rw [← ht] at h₂
  exact fiberBound_vLabel_diagMap_symm s h₂.1 h₂.2

/-- The entries of `A_χ^{-n}` in the form `e^{-χ_j n}` of the scaling hypotheses. -/
private theorem abs_exp_mul_neg (a : ℝ) (n : ℤ) :
    |Real.exp (a * ((-n : ℤ) : ℝ))| = Real.exp (-a * n) := by
  rw [abs_of_pos (Real.exp_pos _)]
  push_cast
  ring_nf

/-- The entries of `A_χ^n` in the form `e^{-χ_j (-n)}` of the scaling hypotheses. -/
private theorem abs_exp_mul (a : ℝ) (n : ℤ) :
    |Real.exp (a * (n : ℝ))| = Real.exp (-a * ((-n : ℤ) : ℝ)) := by
  rw [abs_of_pos (Real.exp_pos _)]
  push_cast
  ring_nf

/-- Scaling by `A_χ^{-n}`: a cell of `ℰ_{n+m} ∘ A_χ^{-n}` meets at most `9` cells of `ℰ_m`. -/
theorem fiberBound_E_resc_neg (n m : ℤ) : FiberBound (χ.E (n + m) ∘ χ.resc (-n)) (χ.E m) 9 :=
  χ.fiberBound_E_diagMap (abs_exp_mul_neg _ n) (abs_exp_mul_neg _ n)

/-- The reverse of `fiberBound_E_resc_neg`. -/
theorem fiberBound_E_resc_neg_symm (n m : ℤ) :
    FiberBound (χ.E m) (χ.E (n + m) ∘ χ.resc (-n)) 9 :=
  χ.fiberBound_E_diagMap_symm (abs_exp_mul_neg _ n) (abs_exp_mul_neg _ n)

/-- Scaling by `A_χ^{-n}` for `π₁⁻¹ ℰ`. -/
theorem fiberBound_E₁_resc_neg (n m : ℤ) :
    FiberBound (χ.E₁ (n + m) ∘ χ.resc (-n)) (χ.E₁ m) 3 :=
  χ.fiberBound_E₁_diagMap _ (abs_exp_mul_neg _ n)

/-- The reverse of `fiberBound_E₁_resc_neg`. -/
theorem fiberBound_E₁_resc_neg_symm (n m : ℤ) :
    FiberBound (χ.E₁ m) (χ.E₁ (n + m) ∘ χ.resc (-n)) 3 :=
  χ.fiberBound_E₁_diagMap_symm _ (abs_exp_mul_neg _ n)

/-- Scaling by `A_χ^{-n}` for `π₂⁻¹ ℰ`. -/
theorem fiberBound_E₂_resc_neg (n m : ℤ) :
    FiberBound (χ.E₂ (n + m) ∘ χ.resc (-n)) (χ.E₂ m) 3 :=
  χ.fiberBound_E₂_diagMap _ (abs_exp_mul_neg _ n)

/-- The reverse of `fiberBound_E₂_resc_neg`. -/
theorem fiberBound_E₂_resc_neg_symm (n m : ℤ) :
    FiberBound (χ.E₂ m) (χ.E₂ (n + m) ∘ χ.resc (-n)) 3 :=
  χ.fiberBound_E₂_diagMap_symm _ (abs_exp_mul_neg _ n)

/-- Scaling by `A_χ^n`: a cell of `ℰ_m ∘ A_χ^n` meets at most `9` cells of `ℰ_{n+m}`. -/
theorem fiberBound_E_resc (n m : ℤ) : FiberBound (χ.E m ∘ χ.resc n) (χ.E (n + m)) 9 := by
  have h := χ.fiberBound_E_diagMap (n := -n) (m := n + m) (abs_exp_mul _ n) (abs_exp_mul _ n)
  rwa [neg_add_cancel_left] at h

/-- The reverse of `fiberBound_E_resc`. -/
theorem fiberBound_E_resc_symm (n m : ℤ) : FiberBound (χ.E (n + m)) (χ.E m ∘ χ.resc n) 9 := by
  have h := χ.fiberBound_E_diagMap_symm (n := -n) (m := n + m) (abs_exp_mul _ n)
    (abs_exp_mul _ n)
  rwa [neg_add_cancel_left] at h

/-- A measure carried by a cell of `ℰ_i` is sent by `A_χ^i` into the unit sup-norm ball about
the image of the centre of the cell: `A_χ^i` maps the cell into a square of side at most `2`. -/
theorem inBall_map_resc_of_ae {θ : Measure (ℝ × ℝ)} {i : ℤ} {c : ℤ × ℤ}
    (h : ∀ᵐ z ∂θ, χ.E i z = c) :
    InBall (θ.map (χ.resc i)) (χ.resc i (rectCentre (lvl χ.χ₁ i) (lvl χ.χ₂ i) c)) 1 := by
  have h₁ := (inRect_of_ae_rect_eq (i := lvl χ.χ₁ i) (j := lvl χ.χ₂ i) h).map_diagMap
    (Real.exp (χ.χ₁ * i)) (Real.exp (χ.χ₂ * i))
  rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)] at h₁
  rw [inBall_iff_inRect]
  exact h₁.mono (exp_mul_half_mesh_le _ _) (exp_mul_half_mesh_le _ _)

/-- The component `θ[|ℰ_i = c]`, rescaled by `A_χ^i`, is carried by the unit sup-norm ball
about the image of the centre of the cell. -/
theorem inBall_map_resc_cond (θ : Measure (ℝ × ℝ)) (i : ℤ) (c : ℤ × ℤ) :
    InBall ((θ[|χ.E i ⁻¹' {c}]).map (χ.resc i))
      (χ.resc i (rectCentre (lvl χ.χ₁ i) (lvl χ.χ₂ i) c)) 1 :=
  χ.inBall_map_resc_of_ae (ae_cond_mem (χ.measurable_E i (measurableSet_singleton c)))

/-- The component `comp θ (ℰ_i) c`, rescaled by `A_χ^i`, is carried by the unit sup-norm ball
about the image of the centre of the cell. -/
theorem inBall_map_resc_comp (θ : Measure (ℝ × ℝ)) (i : ℤ) (c : ℤ × ℤ) :
    InBall ((comp θ (χ.E i) c).map (χ.resc i))
      (χ.resc i (rectCentre (lvl χ.χ₁ i) (lvl χ.χ₂ i) c)) 1 :=
  χ.inBall_map_resc_cond θ i c

end Exps

namespace HomSystem

variable {ι : Type*} [Fintype ι] (S : HomSystem ι)

/-- `|r₁^k| = e^{-χ₁ k}`. -/
private theorem abs_r₁_pow_eq (k : ℕ) :
    |S.r₁ ^ k| = Real.exp (-S.exps.χ₁ * ((k : ℤ) : ℝ)) := by
  rw [Int.cast_natCast, abs_pow, show S.exps.χ₁ = S.χ₁ from rfl, HomSystem.χ₁, neg_neg,
    Real.exp_mul, Real.exp_log S.abs_r₁_pos, Real.rpow_natCast]

/-- `|r₂^k| = e^{-χ₂ k}`. -/
private theorem abs_r₂_pow_eq (k : ℕ) :
    |S.r₂ ^ k| = Real.exp (-S.exps.χ₂ * ((k : ℤ) : ℝ)) := by
  rw [Int.cast_natCast, abs_pow, show S.exps.χ₂ = S.χ₂ from rfl, HomSystem.χ₂, neg_neg,
    Real.exp_mul, Real.exp_log S.abs_r₂_pos, Real.rpow_natCast]

/-- Scaling (2.6) by `A^k = diag(r₁^k, r₂^k)`: a cell of `ℰ_{k+m} ∘ A^k` meets at most `9` cells
of `ℰ_m`. -/
theorem fiberBound_E_Apow (k : ℕ) (m : ℤ) :
    FiberBound (S.exps.E (k + m) ∘ S.Apow k) (S.exps.E m) 9 :=
  S.exps.fiberBound_E_diagMap (S.abs_r₁_pow_eq k) (S.abs_r₂_pow_eq k)

/-- The reverse of `fiberBound_E_Apow`: a cell of `ℰ_m` meets at most `9` cells of
`ℰ_{k+m} ∘ A^k`. -/
theorem fiberBound_E_Apow_symm (k : ℕ) (m : ℤ) :
    FiberBound (S.exps.E m) (S.exps.E (k + m) ∘ S.Apow k) 9 :=
  S.exps.fiberBound_E_diagMap_symm (S.abs_r₁_pow_eq k) (S.abs_r₂_pow_eq k)

/-- Scaling by `A^k` for `π₁⁻¹ ℰ`. -/
theorem fiberBound_E₁_Apow (k : ℕ) (m : ℤ) :
    FiberBound (S.exps.E₁ (k + m) ∘ S.Apow k) (S.exps.E₁ m) 3 :=
  S.exps.fiberBound_E₁_diagMap _ (S.abs_r₁_pow_eq k)

/-- The reverse of `fiberBound_E₁_Apow`. -/
theorem fiberBound_E₁_Apow_symm (k : ℕ) (m : ℤ) :
    FiberBound (S.exps.E₁ m) (S.exps.E₁ (k + m) ∘ S.Apow k) 3 :=
  S.exps.fiberBound_E₁_diagMap_symm _ (S.abs_r₁_pow_eq k)

/-- Scaling by `A^k` for `π₂⁻¹ ℰ`. -/
theorem fiberBound_E₂_Apow (k : ℕ) (m : ℤ) :
    FiberBound (S.exps.E₂ (k + m) ∘ S.Apow k) (S.exps.E₂ m) 3 :=
  S.exps.fiberBound_E₂_diagMap _ (S.abs_r₂_pow_eq k)

/-- The reverse of `fiberBound_E₂_Apow`. -/
theorem fiberBound_E₂_Apow_symm (k : ℕ) (m : ℤ) :
    FiberBound (S.exps.E₂ m) (S.exps.E₂ (k + m) ∘ S.Apow k) 3 :=
  S.exps.fiberBound_E₂_diagMap_symm _ (S.abs_r₂_pow_eq k)

end HomSystem

end Scaling

end BoxLike.Rapaport
