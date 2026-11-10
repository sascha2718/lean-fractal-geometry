module

/-
The affinity dimension `dimaff(𝖠)` of `sec:affinity_dim`.

The pressure `s ↦ P(𝖠, s)` is continuous and strictly decreasing on `[0, ∞)`, with
`P(𝖠, 0) = log N ≥ 0` and `P(𝖠, s) → -∞` as `s → ∞`; this is Käenmäki–Vilppolainen,
Lemma 2.1, for box-like systems. The affinity dimension is its unique zero on `[0, ∞)`.

* `svfExp`, `svf_boxMat_eq`: `φ^s(A) = α_1(A)^{p(s)} α_2(A)^{s - p(s)}` for a diagonal or
  anti-diagonal matrix `A`, where `p(s)` is `s`, `1` or `s / 2` on the three ranges of `s`.
* `svf_boxMat_add_le`, `le_svf_boxMat_add`: the key estimate
  `α_2(A)^δ φ^s(A) ≤ φ^{s+δ}(A) ≤ α_1(A)^δ φ^s(A)`.
* `System.Bounds.svfSum_exponent_add_le`, `System.RatioLowerBound.le_svfSum_exponent_add`:
  `δ₀^{nδ} ∑_{|𝐢| = n} φ^s(A_𝐢) ≤ ∑_{|𝐢| = n} φ^{s+δ}(A_𝐢) ≤ r^{nδ} ∑_{|𝐢| = n} φ^s(A_𝐢)`.
* `System.pressure_zero`: `P(𝖠, 0) = log N`.
* `System.exists_pressure_slope`: `δ log δ₀ ≤ P(𝖠, s + δ) - P(𝖠, s) ≤ δ log r` with
  `log δ₀ ≤ log r < 0`.
* `System.strictAntiOn_pressure`, `System.continuousOn_pressure`,
  `System.tendsto_pressure_atTop`: the pressure is strictly decreasing and continuous on
  `[0, ∞)` and tends to `-∞`.
* `System.existsUnique_pressure_eq_zero`: the pressure has a unique zero on `[0, ∞)`.
* `System.dimaff`, `System.dimaff_nonneg`, `System.pressure_dimaff`, `System.dimaff_eq`,
  `System.dimaff_pos`, `System.le_dimaff_of_pressure_nonneg`: the affinity dimension and its
  characterisation.
-/
public import BoxLike.Pressure
public import BoxLike.Projection
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

namespace BoxLike

open Filter Topology

/-! ### The singular value function in the exponent -/

/-- The exponent `p(s)` of `α_1` in `φ^s`: it is `s` for `s ≤ 1`, `1` for `1 < s ≤ 2` and
`s / 2` for `s > 2`. The exponent of `α_2` is `s - p(s)`. -/
noncomputable def svfExp (s : ℝ) : ℝ := if s ≤ 1 then s else if s ≤ 2 then 1 else s / 2

/-- The exponent `p(s)` of `α_1` in `φ^s` is non-decreasing in `s`. -/
theorem svfExp_le_svfExp_add (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) : svfExp s ≤ svfExp (s + δ) := by
  unfold svfExp
  split_ifs <;> linarith

/-- The exponent `s - p(s)` of `α_2` in `φ^s` is non-decreasing in `s`. -/
theorem svfExp_add_le (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) : svfExp (s + δ) ≤ svfExp s + δ := by
  unfold svfExp
  split_ifs <;> linarith

/-- `φ^s(A) = α_1(A)^{p(s)} α_2(A)^{s - p(s)}` for a diagonal or anti-diagonal matrix `A`
with `a ≠ 0`: the three formulas of `sec:Singular_value_function` in one. -/
theorem svf_boxMat_eq (s : ℝ) (c : ZMod 2) {a : ℝ} (b : ℝ) (ha : a ≠ 0) :
    svf s (boxMat c a b) = max |a| |b| ^ svfExp s * min |a| |b| ^ (s - svfExp s) := by
  have hmax : 0 ≤ max |a| |b| := le_max_of_le_left (abs_nonneg a)
  have hmin : 0 ≤ min |a| |b| := le_min (abs_nonneg a) (abs_nonneg b)
  unfold svfExp
  split_ifs with h1 h2
  · rw [svf_boxMat_of_le_one h1, sub_self, Real.rpow_zero, mul_one]
  · rw [svf_boxMat_of_le_two (not_le.1 h1) h2 c b ha, Real.rpow_one]
  · rw [svf_boxMat_of_two_lt (not_le.1 h2), Real.mul_rpow hmax hmin]
    congr 2
    ring

/-- `y^δ ≤ x^u y^{δ-u}` for `0 < y ≤ x` and `0 ≤ u`. -/
theorem rpow_le_rpow_mul_rpow_sub {x y u : ℝ} (δ : ℝ) (hy : 0 < y) (hyx : y ≤ x)
    (hu : 0 ≤ u) : y ^ δ ≤ x ^ u * y ^ (δ - u) :=
  calc y ^ δ = y ^ u * y ^ (δ - u) := by rw [← Real.rpow_add hy]; congr 1; ring
    _ ≤ x ^ u * y ^ (δ - u) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hy.le hyx hu) (Real.rpow_nonneg hy.le _)

/-- `x^u y^{δ-u} ≤ x^δ` for `0 < y ≤ x` and `u ≤ δ`. -/
theorem rpow_mul_rpow_sub_le {x y u δ : ℝ} (hy : 0 < y) (hyx : y ≤ x) (huδ : u ≤ δ) :
    x ^ u * y ^ (δ - u) ≤ x ^ δ :=
  have hx : 0 < x := hy.trans_le hyx
  calc x ^ u * y ^ (δ - u) ≤ x ^ u * x ^ (δ - u) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy.le hyx (sub_nonneg.2 huδ))
        (Real.rpow_nonneg hx.le _)
    _ = x ^ δ := by rw [← Real.rpow_add hx]; congr 1; ring

/-- Raising the exponent of `φ^s` from `s` to `s + δ` multiplies its value on a diagonal or
anti-diagonal matrix by `α_1^u α_2^{δ-u}` for some `0 ≤ u ≤ δ`. -/
theorem exists_svf_boxMat_add (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (c : ZMod 2) {a b : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ u, 0 ≤ u ∧ u ≤ δ ∧ svf (s + δ) (boxMat c a b) =
      svf s (boxMat c a b) * (max |a| |b| ^ u * min |a| |b| ^ (δ - u)) := by
  have hmax : 0 < max |a| |b| := lt_max_of_lt_left (abs_pos.2 ha)
  have hmin : 0 < min |a| |b| := lt_min (abs_pos.2 ha) (abs_pos.2 hb)
  have h1 := svfExp_le_svfExp_add s hδ
  have h2 := svfExp_add_le s hδ
  refine ⟨svfExp (s + δ) - svfExp s, by linarith, by linarith, ?_⟩
  rw [svf_boxMat_eq (s + δ) c b ha, svf_boxMat_eq s c b ha, mul_mul_mul_comm,
    ← Real.rpow_add hmax, ← Real.rpow_add hmin]
  congr 2 <;> ring

/-- The upper half of the key estimate of `sec:affinity_dim`:
`φ^{s+δ}(A) ≤ α_1(A)^δ φ^s(A)` for a diagonal or anti-diagonal matrix `A` with non-zero
entries. -/
theorem svf_boxMat_add_le (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (c : ZMod 2) {a b : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    svf (s + δ) (boxMat c a b) ≤ max |a| |b| ^ δ * svf s (boxMat c a b) := by
  have hmin : 0 < min |a| |b| := lt_min (abs_pos.2 ha) (abs_pos.2 hb)
  obtain ⟨u, -, huδ, h⟩ := exists_svf_boxMat_add s hδ c ha hb
  rw [h, mul_comm (max |a| |b| ^ δ)]
  exact mul_le_mul_of_nonneg_left (rpow_mul_rpow_sub_le hmin min_le_max huδ) (svf_nonneg _ _)

/-- The lower half of the key estimate of `sec:affinity_dim`:
`α_2(A)^δ φ^s(A) ≤ φ^{s+δ}(A)` for a diagonal or anti-diagonal matrix `A` with non-zero
entries. -/
theorem le_svf_boxMat_add (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (c : ZMod 2) {a b : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    min |a| |b| ^ δ * svf s (boxMat c a b) ≤ svf (s + δ) (boxMat c a b) := by
  have hmin : 0 < min |a| |b| := lt_min (abs_pos.2 ha) (abs_pos.2 hb)
  obtain ⟨u, hu, -, h⟩ := exists_svf_boxMat_add s hδ c ha hb
  rw [h, mul_comm (min |a| |b| ^ δ)]
  exact mul_le_mul_of_nonneg_left (rpow_le_rpow_mul_rpow_sub δ hmin min_le_max hu)
    (svf_nonneg _ _)

namespace System

/-! ### Words and the sums over words -/

section Words

variable {ι : Type*} {S : System ι} {r M δ₀ : ℝ}

/-- `φ^{s+δ}(A_𝐢) ≤ r^{δ|𝐢|} φ^s(A_𝐢)`, since `α_1(A_𝐢) ≤ r^{|𝐢|}`. -/
theorem Bounds.svf_matWord_add_le (hS : S.Bounds r M) (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (w : List ι) : svf (s + δ) (S.matWord w) ≤ (r ^ w.length) ^ δ * svf s (S.matWord w) := by
  rw [matWord_eq]
  refine (svf_boxMat_add_le s hδ _ (S.gDeriv_ne_zero _) (S.gDeriv_ne_zero _)).trans ?_
  refine mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (le_max_of_le_left (abs_nonneg _)) (max_le ?_ ?_) hδ) (svf_nonneg _ _)
  · simpa using hS.abs_gDeriv_le (S.codeWord 0 w)
  · simpa using hS.abs_gDeriv_le (S.codeWord 1 w)

/-- `δ₀^{δ|𝐢|} φ^s(A_𝐢) ≤ φ^{s+δ}(A_𝐢)`, since `α_2(A_𝐢) ≥ δ₀^{|𝐢|}`. -/
theorem RatioLowerBound.le_svf_matWord_add (hδ₀ : S.RatioLowerBound δ₀) (s : ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (w : List ι) :
    (δ₀ ^ w.length) ^ δ * svf s (S.matWord w) ≤ svf (s + δ) (S.matWord w) := by
  rw [matWord_eq]
  refine le_trans ?_ (le_svf_boxMat_add s hδ _ (S.gDeriv_ne_zero _) (S.gDeriv_ne_zero _))
  refine mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (pow_nonneg hδ₀.1.le _) (le_min ?_ ?_) hδ) (svf_nonneg _ _)
  · simpa using hδ₀.le_abs_gDeriv (S.codeWord 0 w)
  · simpa using hδ₀.le_abs_gDeriv (S.codeWord 1 w)

variable [Fintype ι]

/-- `∑_{|𝐢| = n} φ^{s+δ}(A_𝐢) ≤ r^{nδ} ∑_{|𝐢| = n} φ^s(A_𝐢)`. -/
theorem Bounds.svfSum_exponent_add_le (hS : S.Bounds r M) (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (n : ℕ) : S.svfSum (s + δ) n ≤ (r ^ n) ^ δ * S.svfSum s n := by
  rw [svfSum, svfSum, Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  have h := hS.svf_matWord_add_le s hδ (List.ofFn w)
  rwa [List.length_ofFn] at h

/-- `δ₀^{nδ} ∑_{|𝐢| = n} φ^s(A_𝐢) ≤ ∑_{|𝐢| = n} φ^{s+δ}(A_𝐢)`. -/
theorem RatioLowerBound.le_svfSum_exponent_add (hδ₀ : S.RatioLowerBound δ₀) (s : ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (n : ℕ) :
    (δ₀ ^ n) ^ δ * S.svfSum s n ≤ S.svfSum (s + δ) n := by
  rw [svfSum, svfSum, Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  have h := hδ₀.le_svf_matWord_add s hδ (List.ofFn w)
  rwa [List.length_ofFn] at h

end Words

/-! ### The pressure as a function of the exponent -/

variable {ι : Type*} [Fintype ι] [Nonempty ι] (S : System ι)

/-- `P(𝖠, 0) = log N`, so `P(𝖠, 0) ≥ 0`, as in `sec:affinity_dim`. -/
theorem pressure_zero : S.pressure 0 = Real.log (Fintype.card ι) := by
  obtain ⟨δ₀, hδ₀⟩ := S.exists_ratioLowerBound
  have hsum : ∀ n : ℕ, S.svfSum 0 n = (Fintype.card ι : ℝ) ^ n := fun n => by
    simp [svfSum, svf]
  have hev : (fun n : ℕ => Real.log (S.svfSum 0 n) / n) =ᶠ[atTop]
      fun _ => Real.log (Fintype.card ι) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [hsum n, Real.log_pow, mul_div_cancel_left₀ _ hn']
  exact tendsto_nhds_unique (hδ₀.tendsto_pressure le_rfl)
    (tendsto_const_nhds.congr' hev.symm)

/-- The slope of the pressure lies between `log δ₀` and `log r < 0`, where
`0 < δ₀ ≤ |a_i|, |b_i| ≤ r < 1` for all `i`:
`δ log δ₀ ≤ P(𝖠, s + δ) - P(𝖠, s) ≤ δ log r` for all `s, δ ≥ 0`. This is the estimate behind
Käenmäki–Vilppolainen, Lemma 2.1, cited in `sec:affinity_dim`. -/
theorem exists_pressure_slope : ∃ c₁ c₂ : ℝ, c₁ ≤ c₂ ∧ c₂ < 0 ∧ ∀ s δ : ℝ, 0 ≤ s → 0 ≤ δ →
    δ * c₁ ≤ S.pressure (s + δ) - S.pressure s ∧
      S.pressure (s + δ) - S.pressure s ≤ δ * c₂ := by
  obtain ⟨δ₀, hδ₀⟩ := S.exists_ratioLowerBound
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  obtain ⟨i⟩ : Nonempty ι := inferInstance
  have hδr : δ₀ ≤ r := (hδ₀.2 (i, 0)).trans (hS.abs_ratio_le (i, 0))
  have hr : 0 < r := hδ₀.1.trans_le hδr
  refine ⟨Real.log δ₀, Real.log r, Real.log_le_log hδ₀.1 hδr, Real.log_neg hr hS.r_lt_one,
    fun s δ hs hδ => ?_⟩
  have htend := fun t (ht : 0 ≤ t) => hδ₀.tendsto_pressure ht
  have hpos := fun t (ht : 0 ≤ t) (n : ℕ) => hδ₀.svfSum_pos ht n
  have hsδ : 0 ≤ s + δ := add_nonneg hs hδ
  constructor
  · have hle : (fun n : ℕ => δ * Real.log δ₀ + Real.log (S.svfSum s n) / n) ≤ᶠ[atTop]
        fun n : ℕ => Real.log (S.svfSum (s + δ) n) / n := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hp : 0 < (δ₀ ^ n) ^ δ := Real.rpow_pos_of_pos (pow_pos hδ₀.1 _) _
      have hlog := Real.log_le_log (mul_pos hp (hpos s hs n))
        (hδ₀.le_svfSum_exponent_add s hδ n)
      rw [Real.log_mul hp.ne' (hpos s hs n).ne', Real.log_rpow (pow_pos hδ₀.1 _),
        Real.log_pow] at hlog
      rw [le_div_iff₀ hn', add_mul, div_mul_cancel₀ _ hn'.ne']
      linarith [mul_assoc δ (n : ℝ) (Real.log δ₀), mul_right_comm δ (n : ℝ) (Real.log δ₀)]
    have := le_of_tendsto_of_tendsto (tendsto_const_nhds.add (htend s hs)) (htend _ hsδ) hle
    linarith
  · have hle : (fun n : ℕ => Real.log (S.svfSum (s + δ) n) / n) ≤ᶠ[atTop]
        fun n : ℕ => δ * Real.log r + Real.log (S.svfSum s n) / n := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hp : 0 < (r ^ n) ^ δ := Real.rpow_pos_of_pos (pow_pos hr _) _
      have hlog := Real.log_le_log (hpos _ hsδ n) (hS.svfSum_exponent_add_le s hδ n)
      rw [Real.log_mul hp.ne' (hpos s hs n).ne', Real.log_rpow (pow_pos hr _),
        Real.log_pow] at hlog
      rw [div_le_iff₀ hn', add_mul, div_mul_cancel₀ _ hn'.ne']
      linarith [mul_assoc δ (n : ℝ) (Real.log r), mul_right_comm δ (n : ℝ) (Real.log r)]
    have := le_of_tendsto_of_tendsto (htend _ hsδ) (tendsto_const_nhds.add (htend s hs)) hle
    linarith

/-- The increment bound of `exists_pressure_slope`, read for a pair of exponents
`0 ≤ s ≤ t`. -/
theorem exists_pressure_increment : ∃ c₁ c₂ : ℝ, c₁ ≤ c₂ ∧ c₂ < 0 ∧ ∀ s t : ℝ, 0 ≤ s → s ≤ t →
    (t - s) * c₁ ≤ S.pressure t - S.pressure s ∧
      S.pressure t - S.pressure s ≤ (t - s) * c₂ := by
  obtain ⟨c₁, c₂, hc, hc₂, h⟩ := S.exists_pressure_slope
  refine ⟨c₁, c₂, hc, hc₂, fun s t hs hst => ?_⟩
  have h' := h s (t - s) hs (sub_nonneg.2 hst)
  rwa [add_sub_cancel] at h'

/-- The pressure `s ↦ P(𝖠, s)` is strictly decreasing on `[0, ∞)`, as in
`sec:affinity_dim`. -/
theorem strictAntiOn_pressure : StrictAntiOn S.pressure (Set.Ici 0) := by
  obtain ⟨c₁, c₂, -, hc₂, h⟩ := S.exists_pressure_increment
  intro s hs t _ hst
  have h' := (h s t hs hst.le).2
  have hneg : (t - s) * c₂ < 0 := mul_neg_of_pos_of_neg (sub_pos.2 hst) hc₂
  linarith

/-- The pressure `s ↦ P(𝖠, s)` is continuous on `[0, ∞)`, as in `sec:affinity_dim`: it is
Lipschitz there. -/
theorem continuousOn_pressure : ContinuousOn S.pressure (Set.Ici 0) := by
  obtain ⟨c₁, c₂, hc, hc₂, h⟩ := S.exists_pressure_increment
  have hK : 0 ≤ -c₁ := by linarith
  have habs : ∀ x y : ℝ, 0 ≤ x → x ≤ y →
      |S.pressure x - S.pressure y| ≤ -c₁ * |x - y| := by
    intro x y hx hxy
    obtain ⟨h1, h2⟩ := h x y hx hxy
    have hxy' : 0 ≤ y - x := sub_nonneg.2 hxy
    have hle0 : S.pressure y - S.pressure x ≤ 0 :=
      h2.trans (mul_nonpos_of_nonneg_of_nonpos hxy' hc₂.le)
    rw [abs_sub_comm, abs_of_nonpos hle0, abs_of_nonpos (sub_nonpos.2 hxy)]
    linarith [neg_mul c₁ (-(x - y)), mul_neg c₁ (-(x - y)), mul_comm c₁ (y - x)]
  refine LipschitzOnWith.continuousOn (K := (-c₁).toNNReal)
    (LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_)
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK]
  rcases le_total x y with hxy | hxy
  · exact habs x y hx hxy
  · rw [abs_sub_comm, abs_sub_comm x y]
    exact habs y x hy hxy

/-- `lim_{s → ∞} P(𝖠, s) = -∞`, as in `sec:affinity_dim`. -/
theorem tendsto_pressure_atTop : Tendsto S.pressure atTop atBot := by
  obtain ⟨c₁, c₂, -, hc₂, h⟩ := S.exists_pressure_increment
  have hlin : Tendsto (fun t : ℝ => S.pressure 0 + t * c₂) atTop atBot :=
    tendsto_atBot_add_const_left _ _ ((tendsto_mul_const_atBot_of_neg hc₂).2 tendsto_id)
  refine tendsto_atBot_mono' atTop ?_ hlin
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have h' := (h 0 t le_rfl ht).2
  rw [sub_zero] at h'
  linarith

/-- The pressure has a unique zero on `[0, ∞)`, as in `sec:affinity_dim`. -/
theorem existsUnique_pressure_eq_zero : ∃! s : ℝ, 0 ≤ s ∧ S.pressure s = 0 := by
  have h0 : 0 ≤ S.pressure 0 := by
    rw [S.pressure_zero]
    exact Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  obtain ⟨x, hx, hx0⟩ : ∃ x : ℝ, S.pressure x < 0 ∧ 0 ≤ x :=
    ((S.tendsto_pressure_atTop.eventually (eventually_lt_atBot (0 : ℝ))).and
      (eventually_ge_atTop (0 : ℝ))).exists
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hx0
    (S.continuousOn_pressure.mono Set.Icc_subset_Ici_self)
    (⟨hx.le, h0⟩ : (0 : ℝ) ∈ Set.Icc (S.pressure x) (S.pressure 0))
  exact ⟨z, ⟨hz.1, hz0⟩, fun w hw =>
    S.strictAntiOn_pressure.injOn hw.1 hz.1 (hw.2.trans hz0.symm)⟩

/-! ### The affinity dimension -/

/-- The affinity dimension `dimaff(𝖠)` of `sec:affinity_dim`: the unique `s ≥ 0` for which
`P(𝖠, s) = 0`. -/
noncomputable def dimaff : ℝ := (S.existsUnique_pressure_eq_zero).exists.choose

/-- `dimaff(𝖠) ≥ 0`. -/
theorem dimaff_nonneg : 0 ≤ S.dimaff :=
  (S.existsUnique_pressure_eq_zero).exists.choose_spec.1

/-- `P(𝖠, dimaff(𝖠)) = 0`. -/
theorem pressure_dimaff : S.pressure S.dimaff = 0 :=
  (S.existsUnique_pressure_eq_zero).exists.choose_spec.2

/-- The affinity dimension is the only zero of the pressure on `[0, ∞)`. -/
theorem dimaff_eq {s : ℝ} (hs : 0 ≤ s) (h : S.pressure s = 0) : S.dimaff = s :=
  (S.existsUnique_pressure_eq_zero).unique ⟨S.dimaff_nonneg, S.pressure_dimaff⟩ ⟨hs, h⟩

/-- A system of at least two maps has positive affinity dimension, since
`P(𝖠, 0) = log N > 0`. -/
theorem dimaff_pos [Nontrivial ι] : 0 < S.dimaff := by
  refine lt_of_le_of_ne S.dimaff_nonneg fun h0 => ?_
  have h := S.pressure_dimaff
  rw [← h0, S.pressure_zero] at h
  have hcard : (1 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.one_lt_card
  exact (Real.log_pos hcard).ne' h

/-- An exponent `s ≥ 0` with `P(𝖠, s) ≥ 0` is at most the affinity dimension. -/
theorem le_dimaff_of_pressure_nonneg {s : ℝ} (hs : 0 ≤ s) (h : 0 ≤ S.pressure s) :
    s ≤ S.dimaff := by
  by_contra hlt
  have hlt' := S.strictAntiOn_pressure S.dimaff_nonneg hs (not_le.1 hlt)
  rw [S.pressure_dimaff] at hlt'
  linarith

end System

end BoxLike
