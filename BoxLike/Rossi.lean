module

/-
Rossi's bound `eq:hausdorff_ergodic_lyapunov` of `sec:ledrappier_young_formula` (tex lines 2598
to 2731), after Rossi, J. Math. Anal. Appl. 413 (2014), Theorem 2.2, which the article cites:
for every ergodic `μ ∈ M_σ(Σ)` the lower pointwise dimension of `π_*μ` is at most
`min{2, dimL(𝖠, μ)}` almost everywhere, so `\overline{dim}_H(π_*μ) ≤ min{2, dimL(𝖠, μ)}`.

The proof is a covering argument. Fix `t ≤ 2` with `h + Λ(t) < 0`, where `h = h_0(μ)`,
`Λ(t) = Λ(𝖠, μ, t)` is the energy of `eq:energy_def` and `λ_1`, `λ_2` are the Lyapunov
exponents, and fix a small `ε > 0`. By the Shannon–McMillan–Breiman theorem and the theorem of
Furstenberg and Kesten, for `μ`-almost every `𝐢` and all large `n` the word `𝐢|_n` is typical,
`μ([𝐢|_n]) ≥ e^{-n(h+ε)}`, and `α_k(A_{𝐢|_n}) ≤ e^{n(λ_k+ε)}` for `k = 1, 2`. There are at most
`e^{n(h+ε)}` such words of length `n`. The copy `φ_𝐢(X)` lies in a rectangle with sides
`2 α_1(A_𝐢) D` and `2 α_2(A_𝐢) D`, covered by squares of radius `α_1(A_𝐢) D` for `t ≤ 1` and
`α_2(A_𝐢) D` for `1 < t ≤ 2`; the cost `∑ diam^t` of one rectangle is at most
`4 (2D)^t e^{n(Λ(t) + 2ε)}`. The points whose words of length `n ≥ N` all have these properties
therefore form a set of finite `t`-dimensional Hausdorff measure, and the union over `N` has full
`π_*μ`-measure and Hausdorff dimension at most `t`. The mass distribution principle bounds the
lower pointwise dimension by `t` almost everywhere. For `t` above `dimL(𝖠, μ)` and at most `2`
the energy condition holds, and the bound `2` is that of every finite measure on the plane.

* `add_energy_neg_of_lyapDim_lt`: `h + Λ(t) < 0` for `dimL(𝖠, μ) < t ≤ 2`.
* `ae_lowerLocalDim_le_of_dimH_le`: a set of full measure with Hausdorff dimension at most `t`
  bounds the lower pointwise dimension by `t` almost everywhere.
* `ediam_closedBall_le`, `eventually_le_exp_of_tendsto_log`,
  `ae_eventually_block_mem_typicalWords`: three elementary lemmas.
* `System.ae_tendsto_log_norm_matWord`, `System.ae_tendsto_log_alpha₂_matWord`: the theorem of
  Furstenberg and Kesten for the forward products `A_{𝐢|_n}`.
* `System.wordRect`, `System.wordGrid`, `System.Bounds.proj_mem_wordRect`,
  `System.wordRect_subset_iUnion_closedBall`, `System.card_wordGrid_le`: the rectangle of a word
  containing `φ_𝐢(X)` and its cover by a grid of squares.
* `System.coverRadius`, `System.cover_cost_le`: the radius of the squares and the cost of one
  rectangle.
* `System.hausdorffMeasure_iInter_wordRect_le`: the covering bound for the `t`-dimensional
  Hausdorff measure.
* `System.exists_dimH_le_of_add_energy_neg`: a Borel set of full `π_*μ`-measure with Hausdorff
  dimension at most `t` when `h + Λ(t) < 0`.
* `System.ae_lowerLocalDim_map_proj_le`, `System.essSup_lowerLocalDim_map_proj_le`:
  `eq:hausdorff_ergodic_lyapunov`, almost everywhere and for the essential supremum.
-/
public import BoxLike.FalconerBound
public import BoxLike.Kingman
public import BoxLike.LocalDimBounds
public import BoxLike.Lyapunov
public import BoxLike.Measurable
public import BoxLike.ShannonMcMillanBreiman
public import BoxLike.Variational

@[expose] public section

namespace BoxLike

open MeasureTheory Measure Filter Topology Metric Set
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-! ### Real-variable lemmas -/

section Real

variable {h l1 l2 t : ℝ}

/-- For `dimL(𝖠, μ) < t ≤ 2` the energy condition `h_0(μ) + Λ(𝖠, μ, t) < 0` of the covering
argument for `eq:hausdorff_ergodic_lyapunov` holds: `dimL(𝖠, μ)` is the zero of the decreasing
function `t ↦ h_0(μ) + Λ(𝖠, μ, t)` (`eq:diml_min2`). -/
theorem add_energy_neg_of_lyapDim_lt (hl : l2 ≤ l1) (hl1 : l1 < 0) (ht : lyapDim h l1 l2 < t)
    (ht2 : t ≤ 2) : h + energy l1 l2 t < 0 := by
  have hl2 : l2 < 0 := hl.trans_lt hl1
  have hsum : l1 + l2 < 0 := by linarith
  unfold lyapDim at ht
  unfold energy
  by_cases h1 : h ≤ -l1
  · rw [ite_eq_left h1, div_lt_iff_of_neg hl1] at ht
    by_cases ht1 : t ≤ 1
    · rw [ite_eq_left ht1]
      linarith
    · rw [ite_eq_right ht1, ite_eq_left ht2]
      have := mul_neg_of_pos_of_neg (show 0 < t - 1 by linarith) hl2
      linarith
  · rw [ite_eq_right h1] at ht
    by_cases h2 : h ≤ -l1 - l2
    · rw [ite_eq_left h2] at ht
      have hq : (h + l1) / l2 < 0 := div_neg_of_pos_of_neg (by linarith) hl2
      have ht1 : ¬ t ≤ 1 := fun ht1 => by linarith
      rw [ite_eq_right ht1, ite_eq_left ht2]
      have h3 : 1 - t < (h + l1) / l2 := by linarith
      rw [lt_div_iff_of_neg hl2] at h3
      linarith
    · rw [ite_eq_right h2] at ht
      have h3 : 2 < -(2 * h) / (l1 + l2) := by
        rw [lt_div_iff_of_neg hsum]
        linarith
      linarith

end Real

/-! ### Elementary lemmas -/

/-- In a pseudometric space the closed ball of radius `R` has diameter at most `2R`; the
squares of the cover for `eq:hausdorff_ergodic_lyapunov` are such balls. -/
theorem ediam_closedBall_le {X : Type*} [PseudoMetricSpace X] (p : X) (R : ℝ) :
    ediam (closedBall p R) ≤ ENNReal.ofReal (2 * R) :=
  ediam_le_of_forall_dist_le fun x hx y hy => by
    have := dist_triangle_right x y p
    rw [mem_closedBall] at hx hy
    linarith

/-- If `n⁻¹ log F(n) → L` for a positive sequence `F`, then `F(n) ≤ e^{n(L+ε)}` for all large
`n`: the form in which the proof of `eq:hausdorff_ergodic_lyapunov` uses the Lyapunov
exponents. -/
theorem eventually_le_exp_of_tendsto_log {F : ℕ → ℝ} {L ε : ℝ} (hF : ∀ n, 0 < F n) (hε : 0 < ε)
    (h : Tendsto (fun n : ℕ => Real.log (F n) / n) atTop (𝓝 L)) :
    ∀ᶠ n : ℕ in atTop, F n ≤ Real.exp (n * (L + ε)) := by
  filter_upwards [h.eventually_lt_const (lt_add_of_pos_right L hε), eventually_gt_atTop 0]
    with n hn hn0
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  rw [div_lt_iff₀ hn'] at hn
  rw [← Real.log_le_iff_le_exp (hF n)]
  linarith

section Typical

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]

/-- The Shannon–McMillan–Breiman theorem of `sec:entropies` (tex lines 1885 to 1889) in
pointwise form, for the proof of `eq:hausdorff_ergodic_lyapunov`: for an ergodic `μ` and every
`ε > 0`, the block `x_0 ⋯ x_{n-1}` of `μ`-almost every `x` is a typical word,
`e^{-n(h+ε)} ≤ μ([x_0 ⋯ x_{n-1}]) ≤ e^{-n(h-ε)}`, for all large `n`. -/
theorem ae_eventually_block_mem_typicalWords (herg : Ergodic (shift 1) μ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᵐ x ∂μ, ∀ᶠ n : ℕ in atTop, block n x ∈ typicalWords μ (entropy μ) ε n := by
  filter_upwards [tendsto_neg_log_cylinder_entropy herg, ae_measureReal_cylinder_pos (μ := μ)]
    with x hx hpos
  filter_upwards [hx.eventually_lt_const (lt_add_of_pos_right _ hε),
    hx.eventually_const_lt (sub_lt_self _ hε), eventually_gt_atTop 0] with n h1 h2 hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hlog := Real.exp_log (hpos n)
  rw [div_lt_iff₀ hn'] at h1
  rw [lt_div_iff₀ hn'] at h2
  rw [mem_typicalWords]
  constructor
  · rw [← hlog, Real.exp_le_exp]
    nlinarith
  · rw [← hlog, Real.exp_le_exp]
    nlinarith

end Typical

/-! ### A set of full measure and small dimension -/

section MassDistribution

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {ν : Measure X}
  [IsFiniteMeasure ν]

/-- The mass distribution principle in the form used for `eq:hausdorff_ergodic_lyapunov`: if a
set `E` of full `ν`-measure has `dim_H E ≤ t`, then `\underline{dim}_loc(ν, x) ≤ t` for
`ν`-almost every `x`. Otherwise, for some `k` the points with
`\underline{dim}_loc(ν, x) > t + 1/(k+1)` form a set of positive outer measure, whose
intersection with `E` has Hausdorff dimension at least `t + 1/(k+1)`. -/
theorem ae_lowerLocalDim_le_of_dimH_le {E : Set X} (hE : ν Eᶜ = 0) {t : ℝ} (ht : 0 ≤ t)
    (hdim : dimH E ≤ ENNReal.ofReal t) : ∀ᵐ y ∂ν, lowerLocalDim ν y ≤ t := by
  have hk : ∀ k : ℕ, ν {y | t + 1 / ((k : ℝ) + 1) < lowerLocalDim ν y} = 0 := by
    intro k
    by_contra hne
    have hpos : 0 < ν ({y | t + 1 / ((k : ℝ) + 1) < lowerLocalDim ν y} ∩ E) := by
      rw [measure_inter_conull hE]
      exact pos_iff_ne_zero.2 hne
    have h1 := le_dimH_of_ae_le_lowerLocalDim hpos (Eventually.of_forall fun y hy => hy.1.le)
    have h2 := h1.trans ((dimH_mono inter_subset_right).trans hdim)
    rw [ENNReal.ofReal_le_ofReal_iff ht] at h2
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := Nat.one_div_pos_of_nat
    linarith
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_) (measure_iUnion_null hk)
  simp only [mem_ofPred_eq, not_le] at hy
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hy)
  exact mem_iUnion.2 ⟨k, by simp only [mem_ofPred_eq]; linarith⟩

end MassDistribution

namespace System

/-! ### The theorem of Furstenberg and Kesten for the forward products -/

section FurstenbergKesten

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]

/-- The theorem of Furstenberg and Kesten of `sec:lyapunov_exponents` (tex line 1508) for `α_1`
along the forward products, for the proof of `eq:hausdorff_ergodic_lyapunov`: for an ergodic
`μ`, `n⁻¹ log ‖A_{i_0} ⋯ A_{i_{n-1}}‖ → λ_1(𝖠, μ)` for `μ`-almost every `𝐢`. This is Kingman's
theorem for the sub-additive cocycle `log α_1(A_{𝐢|_n})` over `σ`. -/
theorem ae_tendsto_log_norm_matWord (herg : Ergodic (shift 1) μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => Real.log ‖S.matWord (futureWord x n)‖ / n) atTop
      (𝓝 (S.lyapunov₁ μ)) :=
  kingman_ergodic_of_tendsto herg (f := fun n x => Real.log ‖S.matWord (futureWord x n)‖)
    (fun m n x => by
      simp only [iterate_shift_one, futureWord_add]
      exact S.log_norm_matWord_append_le _ _)
    (fun n => measurable_comp_futureWord (fun w => Real.log ‖S.matWord w‖) n)
    (fun n => integrable_comp_futureWord (fun w => Real.log ‖S.matWord w‖) n)
    (S.tendsto_lyapunov₁ herg.toMeasurePreserving)

/-- The theorem of Furstenberg and Kesten of `sec:lyapunov_exponents` (tex line 1508) for
`α_2 = |det| / α_1` along the forward products, for the proof of
`eq:hausdorff_ergodic_lyapunov`: for an ergodic `μ`,
`n⁻¹ log α_2(A_{i_0} ⋯ A_{i_{n-1}}) → λ_2(𝖠, μ)` for `μ`-almost every `𝐢`. The function
`-log α_2(A_{𝐢|_n})` is a sub-additive cocycle over `σ`. -/
theorem ae_tendsto_log_alpha₂_matWord (herg : Ergodic (shift 1) μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ =>
      Real.log (|(S.matWord (futureWord x n)).det| / ‖S.matWord (futureWord x n)‖) / n) atTop
      (𝓝 (S.lyapunov₂ μ)) := by
  set G : List ι → ℝ := fun w => -Real.log (|(S.matWord w).det| / ‖S.matWord w‖) with hG
  have hL := (S.tendsto_lyapunov₂ herg.toMeasurePreserving).neg
  have h := kingman_ergodic_of_tendsto herg (f := fun n x => G (futureWord x n))
    (fun m n x => by
      simp only [hG, iterate_shift_one, futureWord_add]
      linarith [S.le_log_abs_det_div_norm_matWord_append (futureWord x m)
        (futureWord (shift m x) n)])
    (fun n => measurable_comp_futureWord G n) (fun n => integrable_comp_futureWord G n)
    (L := -S.lyapunov₂ μ) (hL.congr fun n => by rw [hG, integral_neg, neg_div])
  filter_upwards [h] with x hx
  have hx' := hx.neg
  rw [neg_neg] at hx'
  refine hx'.congr fun n => ?_
  simp only [hG, neg_div, neg_neg]

end FurstenbergKesten

/-! ### Rectangles and their grids -/

section Rectangles

variable {ι : Type*} (S : System ι)

/-- `α_2(A_𝐢) = |det A_𝐢| / ‖A_𝐢‖`, the form of `α_2` in `sec:lyapunov_exponents`. -/
theorem alpha₂_eq_abs_det_div_norm (w : List ι) :
    S.alpha₂ w = |(S.matWord w).det| / ‖S.matWord w‖ := by
  rw [abs_det_div_norm_matWord]
  rfl

/-- The interval `[c - b D, c + b D]` along the axis `c`, centred at the coordinate `c` of
`φ_𝐢(x₀)`, with `b` the side of `A_𝐢([0,1]²)` along the axis: a side of the rectangle of the
covering argument for `eq:hausdorff_ergodic_lyapunov`. -/
def wordInterval (x₀ : ℝ × ℝ) (D : ℝ) (c : ZMod 2) (w : List ι) : Set ℝ :=
  Icc (coord c (S.phiWord w x₀) - S.side c w * D) (coord c (S.phiWord w x₀) + S.side c w * D)

/-- The rectangle of the word `𝐢` in the covering argument for `eq:hausdorff_ergodic_lyapunov`,
with sides `2 b(𝐢) D` and `2 h(𝐢) D` and centre `φ_𝐢(x₀)`. For `x₀ ∈ X` and `D` a bound for
the diameter of `X` it contains `φ_𝐢(X)`. -/
def wordRect (x₀ : ℝ × ℝ) (D : ℝ) (w : List ι) : Set (ℝ × ℝ) :=
  S.wordInterval x₀ D 0 w ×ˢ S.wordInterval x₀ D 1 w

/-- The centres of the subdivision of `wordInterval x₀ D c w` into intervals of length `2ρD`,
for the cover of `eq:hausdorff_ergodic_lyapunov`. -/
noncomputable def axisGrid (x₀ : ℝ × ℝ) (D ρ : ℝ) (c : ZMod 2) (w : List ι) : Finset ℝ :=
  gridFinset (coord c (S.phiWord w x₀) - S.side c w * D)
    (coord c (S.phiWord w x₀) + S.side c w * D) (ρ * D)

/-- The centres of the squares of radius `ρD` covering the rectangle of the word `𝐢` in the
covering argument for `eq:hausdorff_ergodic_lyapunov`. -/
noncomputable def wordGrid (x₀ : ℝ × ℝ) (D ρ : ℝ) (w : List ι) : Finset (ℝ × ℝ) :=
  S.axisGrid x₀ D ρ 0 w ×ˢ S.axisGrid x₀ D ρ 1 w

/-- The rectangle of a word is Borel, so the set of full measure built from rectangles in the
proof of `eq:hausdorff_ergodic_lyapunov` is Borel. -/
theorem measurableSet_wordRect (x₀ : ℝ × ℝ) (D : ℝ) (w : List ι) :
    MeasurableSet (S.wordRect x₀ D w) :=
  measurableSet_Icc.prod measurableSet_Icc

variable {S} in
/-- For the proof of `eq:hausdorff_ergodic_lyapunov`, `π(𝐢)` lies in the rectangle of `𝐢|_n`
for every `n`: `π(𝐢) ∈ φ_{𝐢|_n}(X)`, and
`φ_{𝐢|_n}(X)` lies in the rectangle by `abs_coord_phiWord_sub_le`. -/
theorem Bounds.proj_mem_wordRect {r M D : ℝ} (hS : S.Bounds r M)
    (hdist : ∀ x ∈ S.attractor, ∀ x' ∈ S.attractor, dist x x' ≤ D) {x₀ : ℝ × ℝ}
    (hx₀ : x₀ ∈ S.attractor) (n : ℕ) (x : ℤ → ι) :
    S.proj x ∈ S.wordRect x₀ D (futureWord x n) := by
  obtain ⟨y, hy⟩ := hS.exists_proj_eq_phiWord n x
  have h := fun c => abs_le.1 (S.abs_coord_phiWord_sub_le hdist c (futureWord x n) ⟨y, rfl⟩ hx₀)
  rw [hy]
  refine ⟨?_, ?_⟩
  · show coord 0 (S.phiWord (futureWord x n) (S.proj y)) ∈ S.wordInterval x₀ D 0 (futureWord x n)
    exact ⟨by linarith [(h 0).1], by linarith [(h 0).2]⟩
  · show coord 1 (S.phiWord (futureWord x n) (S.proj y)) ∈ S.wordInterval x₀ D 1 (futureWord x n)
    exact ⟨by linarith [(h 1).1], by linarith [(h 1).2]⟩

/-- The squares of radius `ρD` about the points of `wordGrid x₀ D ρ w` cover the rectangle of
`w`, as in the covering argument for `eq:hausdorff_ergodic_lyapunov`. -/
theorem wordRect_subset_iUnion_closedBall {x₀ : ℝ × ℝ} {D ρ : ℝ} (hD : 0 < D) (hρ : 0 < ρ)
    (w : List ι) :
    S.wordRect x₀ D w ⊆ ⋃ p ∈ S.wordGrid x₀ D ρ w, closedBall p (ρ * D) := by
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  have hr : 0 < ρ * D := mul_pos hρ hD
  obtain ⟨u, hu, hau⟩ := isCover_gridCentres hr ha
  obtain ⟨v, hv, hbv⟩ := isCover_gridCentres hr hb
  have hau' : dist a u ≤ ρ * D := by
    have h : edist a u ≤ ENNReal.ofReal (ρ * D) := hau
    rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff hr.le] at h
  have hbv' : dist b v ≤ ρ * D := by
    have h : edist b v ≤ ENNReal.ofReal (ρ * D) := hbv
    rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff hr.le] at h
  refine mem_iUnion₂.2 ⟨(u, v), ?_, ?_⟩
  · rw [wordGrid, Finset.mem_product, axisGrid, axisGrid, ← Finset.mem_coe, ← Finset.mem_coe,
      coe_gridFinset, coe_gridFinset]
    exact ⟨hu, hv⟩
  · rw [mem_closedBall, Prod.dist_eq]
    exact max_le hau' hbv'

/-- The rectangle of `w` needs at most `(α_1(A_𝐢)/ρ + 1)(α_2(A_𝐢)/ρ + 1)` squares of radius
`ρD`, the count of the covering argument for `eq:hausdorff_ergodic_lyapunov`. -/
theorem card_wordGrid_le {x₀ : ℝ × ℝ} {D ρ : ℝ} (hD : 0 < D) (hρ : 0 < ρ) (w : List ι) :
    ((S.wordGrid x₀ D ρ w).card : ℝ) ≤ (S.alpha₁ w / ρ + 1) * (S.alpha₂ w / ρ + 1) := by
  have hgrid : ∀ c, ((S.axisGrid x₀ D ρ c w).card : ℝ) ≤ S.side c w / ρ + 1 := by
    intro c
    refine (card_gridFinset_le _ _ _).trans ?_
    have heq : (coord c (S.phiWord w x₀) + S.side c w * D -
        (coord c (S.phiWord w x₀) - S.side c w * D)) / (2 * (ρ * D)) = S.side c w / ρ := by
      field_simp
      ring
    rw [heq]
    have := Nat.floor_le (div_nonneg (S.side_pos c w).le hρ.le)
    linarith
  rw [wordGrid, Finset.card_product, Nat.cast_mul]
  refine (mul_le_mul (hgrid 0) (hgrid 1) (Nat.cast_nonneg _)
    (by have := S.side_pos 0 w; positivity)).trans (le_of_eq ?_)
  exact div_add_one_mul_div_add_one _ _ _

/-- The radius of the squares covering the rectangle of a word in the covering argument for
`eq:hausdorff_ergodic_lyapunov` with the exponent `t`: `α_1(A_𝐢)` for `t ≤ 1` and `α_2(A_𝐢)`
for `t > 1`. -/
noncomputable def coverRadius (t : ℝ) (w : List ι) : ℝ :=
  if t ≤ 1 then S.alpha₁ w else S.alpha₂ w

/-- The cover radius of `eq:hausdorff_ergodic_lyapunov` is positive. -/
theorem coverRadius_pos (t : ℝ) (w : List ι) : 0 < S.coverRadius t w := by
  unfold coverRadius
  split_ifs
  exacts [S.alpha₁_pos w, S.alpha₂_pos w]

/-- The cover radius of `eq:hausdorff_ergodic_lyapunov` is at most `α_1(A_𝐢)`. -/
theorem coverRadius_le_alpha₁ (t : ℝ) (w : List ι) : S.coverRadius t w ≤ S.alpha₁ w := by
  unfold coverRadius
  split_ifs
  exacts [le_rfl, S.alpha₂_le_alpha₁ w]

/-- The cost of the rectangle of a word `𝐢` of length `n` in the covering argument for
`eq:hausdorff_ergodic_lyapunov`: if `α_1(A_𝐢) ≤ e^{n(λ_1+ε)}` and `α_2(A_𝐢) ≤ e^{n(λ_2+ε)}`,
then its squares of radius `ρD` contribute at most `4 (2D)^t e^{n(Λ(t) + 2ε)}` to
`∑ diam^t`, for `0 ≤ t ≤ 2`. For `t ≤ 1` one square of radius `α_1 D` costs `(2 α_1 D)^t`; for
`1 < t ≤ 2` the `2 α_1/α_2` squares of radius `α_2 D` cost `(2 α_2 D)^t` each. -/
theorem cover_cost_le {t ε l1 l2 D : ℝ} {n : ℕ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) (hε : 0 ≤ ε)
    (hD : 0 < D) {w : List ι} (h1 : S.alpha₁ w ≤ Real.exp (n * (l1 + ε)))
    (h2 : S.alpha₂ w ≤ Real.exp (n * (l2 + ε))) :
    (S.alpha₁ w / S.coverRadius t w + 1) * (S.alpha₂ w / S.coverRadius t w + 1) *
        (2 * S.coverRadius t w * D) ^ t ≤
      4 * (2 * D) ^ t * Real.exp (n * (energy l1 l2 t + 2 * ε)) := by
  have ha1 := S.alpha₁_pos w
  have ha2 := S.alpha₂_pos w
  have h12 := S.alpha₂_le_alpha₁ w
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hD2 : 0 ≤ (2 * D) ^ t := Real.rpow_nonneg (by linarith) t
  have hslack : 0 ≤ n * ε * (2 - t) := mul_nonneg (mul_nonneg hn hε) (by linarith)
  unfold coverRadius energy
  by_cases ht1 : t ≤ 1
  · simp only [ht1, ↓reduceIte]
    have hq : S.alpha₂ w / S.alpha₁ w ≤ 1 := (div_le_one ha1).2 h12
    have hpow : (2 * S.alpha₁ w * D) ^ t = (2 * D) ^ t * S.alpha₁ w ^ t := by
      rw [show 2 * S.alpha₁ w * D = 2 * D * S.alpha₁ w by ring,
        Real.mul_rpow (by linarith) ha1.le]
    have hexp : S.alpha₁ w ^ t ≤ Real.exp (n * (t * l1 + 2 * ε)) := by
      calc S.alpha₁ w ^ t ≤ Real.exp (n * (l1 + ε)) ^ t := Real.rpow_le_rpow ha1.le h1 ht0
        _ = Real.exp (n * (l1 + ε) * t) := (Real.exp_mul _ _).symm
        _ ≤ Real.exp (n * (t * l1 + 2 * ε)) := Real.exp_le_exp.2 (by nlinarith)
    have hb0 : 0 ≤ (2 * D) ^ t * S.alpha₁ w ^ t := mul_nonneg hD2 (Real.rpow_nonneg ha1.le t)
    rw [div_self ha1.ne', hpow]
    calc (1 + 1) * (S.alpha₂ w / S.alpha₁ w + 1) * ((2 * D) ^ t * S.alpha₁ w ^ t)
        ≤ 4 * ((2 * D) ^ t * S.alpha₁ w ^ t) := by nlinarith
      _ ≤ 4 * ((2 * D) ^ t * Real.exp (n * (t * l1 + 2 * ε))) := by gcongr
      _ = 4 * (2 * D) ^ t * Real.exp (n * (t * l1 + 2 * ε)) := by ring
  · simp only [ht1, ht2, ↓reduceIte]
    have hpow : (2 * S.alpha₂ w * D) ^ t =
        (2 * D) ^ t * (S.alpha₂ w * S.alpha₂ w ^ (t - 1)) := by
      rw [show 2 * S.alpha₂ w * D = 2 * D * S.alpha₂ w by ring,
        Real.mul_rpow (by linarith) ha2.le, Real.rpow_sub_one ha2.ne',
        mul_div_cancel₀ _ ha2.ne']
    have hb0 : 0 ≤ S.alpha₂ w ^ (t - 1) := Real.rpow_nonneg ha2.le _
    have hb : S.alpha₂ w ^ (t - 1) ≤ Real.exp (n * (l2 + ε) * (t - 1)) := by
      rw [Real.exp_mul]
      exact Real.rpow_le_rpow ha2.le h2 (by linarith)
    have hprod : S.alpha₁ w * S.alpha₂ w ^ (t - 1) ≤
        Real.exp (n * (l1 + (t - 1) * l2 + 2 * ε)) := by
      calc S.alpha₁ w * S.alpha₂ w ^ (t - 1)
          ≤ Real.exp (n * (l1 + ε)) * Real.exp (n * (l2 + ε) * (t - 1)) :=
            mul_le_mul h1 hb hb0 (Real.exp_pos _).le
        _ = Real.exp (n * (l1 + ε) + n * (l2 + ε) * (t - 1)) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (n * (l1 + (t - 1) * l2 + 2 * ε)) := Real.exp_le_exp.2 (by nlinarith)
    have hsum : (S.alpha₁ w / S.alpha₂ w + 1) * S.alpha₂ w = S.alpha₁ w + S.alpha₂ w := by
      field_simp
    have key : (S.alpha₁ w / S.alpha₂ w + 1) * (1 + 1) * (S.alpha₂ w * S.alpha₂ w ^ (t - 1)) ≤
        4 * (S.alpha₁ w * S.alpha₂ w ^ (t - 1)) := by
      calc (S.alpha₁ w / S.alpha₂ w + 1) * (1 + 1) * (S.alpha₂ w * S.alpha₂ w ^ (t - 1))
          = 2 * ((S.alpha₁ w / S.alpha₂ w + 1) * S.alpha₂ w) * S.alpha₂ w ^ (t - 1) := by ring
        _ = 2 * (S.alpha₁ w + S.alpha₂ w) * S.alpha₂ w ^ (t - 1) := by rw [hsum]
        _ ≤ 4 * (S.alpha₁ w * S.alpha₂ w ^ (t - 1)) := by
          nlinarith [mul_nonneg (sub_nonneg.2 h12) hb0]
    rw [div_self ha2.ne', hpow]
    calc (S.alpha₁ w / S.alpha₂ w + 1) * (1 + 1) *
          ((2 * D) ^ t * (S.alpha₂ w * S.alpha₂ w ^ (t - 1)))
        = (2 * D) ^ t * ((S.alpha₁ w / S.alpha₂ w + 1) * (1 + 1) *
          (S.alpha₂ w * S.alpha₂ w ^ (t - 1))) := by ring
      _ ≤ (2 * D) ^ t * (4 * (S.alpha₁ w * S.alpha₂ w ^ (t - 1))) :=
          mul_le_mul_of_nonneg_left key hD2
      _ ≤ (2 * D) ^ t * (4 * Real.exp (n * (l1 + (t - 1) * l2 + 2 * ε))) := by gcongr
      _ = 4 * (2 * D) ^ t * Real.exp (n * (l1 + (t - 1) * l2 + 2 * ε)) := by ring

end Rectangles

/-! ### The covering bound -/

section Covering

variable {ι : Type*} (S : System ι)

/-- The covering bound behind `eq:hausdorff_ergodic_lyapunov`. Let `W_n` be a family of words of
length `n` and `ρ` a positive radius function with `ρ(𝐢) ≤ α_1(A_𝐢)`. If for all `n ≥ N` the
squares of radius `ρ(𝐢) D` covering the rectangles of the words of `W_n` have
`∑ diam^t ≤ K`, then the set of points lying, for every `n ≥ N`, in the rectangle of some word of
`W_n` has `t`-dimensional Hausdorff measure at most `K`. The diameters are at most
`2 r^n D → 0`. -/
theorem hausdorffMeasure_iInter_wordRect_le {x₀ : ℝ × ℝ} {D r M t K : ℝ} (hD : 0 < D)
    (hS : S.Bounds r M) (ht : 0 ≤ t) {ρ : List ι → ℝ} (hρ0 : ∀ w, 0 < ρ w)
    (hρ1 : ∀ w, ρ w ≤ S.alpha₁ w) (W : (n : ℕ) → Finset (Fin n → ι)) (N : ℕ)
    (hK : ∀ n, N ≤ n → ∑ w ∈ W n, (S.alpha₁ (List.ofFn w) / ρ (List.ofFn w) + 1) *
      (S.alpha₂ (List.ofFn w) / ρ (List.ofFn w) + 1) * (2 * ρ (List.ofFn w) * D) ^ t ≤ K) :
    μH[t] (⋂ n, ⋂ (_ : N ≤ n), ⋃ w ∈ W n, S.wordRect x₀ D (List.ofFn w)) ≤
      ENNReal.ofReal K := by
  classical
  obtain ⟨E, hE⟩ : ∃ E : Set (ℝ × ℝ),
      E = ⋂ n, ⋂ (_ : N ≤ n), ⋃ w ∈ W n, S.wordRect x₀ D (List.ofFn w) := ⟨_, rfl⟩
  rw [← hE]
  obtain ⟨I, hI⟩ : ∃ I : (n : ℕ) → Finset (Σ _ : Fin n → ι, ℝ × ℝ),
      I = fun n => (W n).sigma fun w => S.wordGrid x₀ D (ρ (List.ofFn w)) (List.ofFn w) :=
    ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : (n : ℕ) → I n → Set (ℝ × ℝ),
      T = fun n i => closedBall i.1.2 (ρ (List.ofFn i.1.1) * D) := ⟨_, rfl⟩
  have hIn : ∀ n, I n = (W n).sigma fun w =>
      S.wordGrid x₀ D (ρ (List.ofFn w)) (List.ofFn w) := fun n => by rw [hI]
  have hTn : ∀ n (i : I n), T n i = closedBall i.1.2 (ρ (List.ofFn i.1.1) * D) :=
    fun n i => by rw [hT]
  have hr : Tendsto (fun n : ℕ => ENNReal.ofReal (2 * D * r ^ n)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hS.r_nonneg hS.r_lt_one).const_mul
      (2 * D)
  have hdiam : ∀ n (i : I n), ediam (T n i) ≤ ENNReal.ofReal (2 * ρ (List.ofFn i.1.1) * D) := by
    intro n i
    rw [hTn, mul_assoc]
    exact ediam_closedBall_le _ _
  have hdiam' : ∀ n (i : I n), ediam (T n i) ≤ ENNReal.ofReal (2 * D * r ^ n) := fun n i => by
    refine (hdiam n i).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 := (hρ1 (List.ofFn i.1.1)).trans (hS.alpha₁_le _)
    rw [List.length_ofFn] at h1
    nlinarith
  have hcov : ∀ n, N ≤ n → E ⊆ ⋃ i, T n i := by
    intro n hn x hx
    rw [hE] at hx
    have hx' : x ∈ ⋃ w ∈ W n, S.wordRect x₀ D (List.ofFn w) := mem_iInter₂.1 hx n hn
    obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.1 hx'
    obtain ⟨p, hp, hxp⟩ :=
      mem_iUnion₂.1 (S.wordRect_subset_iUnion_closedBall hD (hρ0 (List.ofFn w)) _ hxw)
    have hmem : (⟨w, p⟩ : Σ _ : Fin n → ι, ℝ × ℝ) ∈ I n := by
      rw [hIn n]
      exact Finset.mem_sigma.2 ⟨hw, hp⟩
    refine mem_iUnion.2 ⟨⟨⟨w, p⟩, hmem⟩, ?_⟩
    rw [hTn]
    exact hxp
  have hsum : ∀ n, N ≤ n → ∑ i, ediam (T n i) ^ t ≤ ENNReal.ofReal K := by
    intro n hn
    have hf0 : ∀ i : Σ _ : Fin n → ι, ℝ × ℝ, 0 ≤ (2 * ρ (List.ofFn i.1) * D) ^ t := fun i =>
      Real.rpow_nonneg (by have := hρ0 (List.ofFn i.1); positivity) t
    have hreal : ∑ i ∈ I n, (2 * ρ (List.ofFn i.1) * D) ^ t ≤ K := by
      rw [hIn n, Finset.sum_sigma]
      refine le_trans (Finset.sum_le_sum fun w _ => ?_) (hK n hn)
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (S.card_wordGrid_le hD (hρ0 (List.ofFn w)) (List.ofFn w)) (hf0 ⟨w, (0, 0)⟩)
    calc ∑ i, ediam (T n i) ^ t
        ≤ ∑ i : I n, ENNReal.ofReal ((2 * ρ (List.ofFn i.1.1) * D) ^ t) :=
          Finset.sum_le_sum fun i _ => (ENNReal.rpow_le_rpow (hdiam n i) ht).trans_eq
            (ENNReal.ofReal_rpow_of_nonneg (by have := hρ0 (List.ofFn i.1.1); positivity) ht)
      _ = ∑ i ∈ I n, ENNReal.ofReal ((2 * ρ (List.ofFn i.1) * D) ^ t) :=
          Finset.sum_coe_sort (I n) fun i => ENNReal.ofReal ((2 * ρ (List.ofFn i.1) * D) ^ t)
      _ = ENNReal.ofReal (∑ i ∈ I n, (2 * ρ (List.ofFn i.1) * D) ^ t) :=
          (ENNReal.ofReal_sum_of_nonneg fun i _ => hf0 i).symm
      _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal hreal
  calc μH[t] E ≤ liminf (fun n => ∑ i, ediam (T n i) ^ t) atTop :=
        hausdorffMeasure_le_liminf_sum (ι := fun n => I n) t E _ hr T
          (Eventually.of_forall hdiam') (eventually_atTop.2 ⟨N, hcov⟩)
    _ ≤ ENNReal.ofReal K := liminf_le_of_frequently_le' (eventually_atTop.2 ⟨N, hsum⟩).frequently

end Covering

/-! ### Rossi's bound -/

section Rossi

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]

/-- The covering argument for `eq:hausdorff_ergodic_lyapunov`: for an ergodic `μ` and
`0 ≤ t ≤ 2` with `h_0(μ) + Λ(𝖠, μ, t) < 0` there is a Borel set `E ⊆ ℝ²` of full
`π_*μ`-measure with `dim_H E ≤ t`. With `ε = -(h_0(μ) + Λ(𝖠, μ, t))/4`, the set `E` is the union
over `N` of the points lying, for every `n ≥ N`, in the rectangle of some typical word `𝐢` of
length `n` with `α_k(A_𝐢) ≤ e^{n(λ_k+ε)}`; each part has finite `t`-dimensional Hausdorff
measure by `hausdorffMeasure_iInter_wordRect_le` and `cover_cost_le`, since there are at most
`e^{n(h+ε)}` such words. -/
theorem exists_dimH_le_of_add_energy_neg (herg : Ergodic (shift 1) μ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht2 : t ≤ 2) (hneg : entropy μ + energy (S.lyapunov₁ μ) (S.lyapunov₂ μ) t < 0) :
    ∃ E : Set (ℝ × ℝ), MeasurableSet E ∧ μ.map S.proj Eᶜ = 0 ∧ dimH E ≤ ENNReal.ofReal t := by
  classical
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
  set h := entropy μ with hh
  set l1 := S.lyapunov₁ μ with hl1
  set l2 := S.lyapunov₂ μ with hl2
  set ε := -(h + energy l1 l2 t) / 4 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  obtain ⟨x₀, hx₀⟩ := S.attractor_nonempty
  obtain ⟨D₀, hD₀⟩ := Metric.isBounded_iff.1 S.isCompact_attractor.isBounded
  set D := max D₀ 1 with hD_def
  have hD : 0 < D := one_pos.trans_le (le_max_right _ _)
  have hdist : ∀ x ∈ S.attractor, ∀ x' ∈ S.attractor, dist x x' ≤ D :=
    fun x hx x' hx' => (hD₀ hx hx').trans (le_max_left _ _)
  set W : (n : ℕ) → Finset (Fin n → ι) := fun n => (typicalWords μ h ε n).filter fun w =>
    S.alpha₁ (List.ofFn w) ≤ Real.exp (n * (l1 + ε)) ∧
      S.alpha₂ (List.ofFn w) ≤ Real.exp (n * (l2 + ε)) with hW
  set E : ℕ → Set (ℝ × ℝ) := fun N =>
    ⋂ n, ⋂ (_ : N ≤ n), ⋃ w ∈ W n, S.wordRect x₀ D (List.ofFn w) with hE
  have hK : ∀ n, ∑ w ∈ W n, (S.alpha₁ (List.ofFn w) / S.coverRadius t (List.ofFn w) + 1) *
      (S.alpha₂ (List.ofFn w) / S.coverRadius t (List.ofFn w) + 1) *
      (2 * S.coverRadius t (List.ofFn w) * D) ^ t ≤ 4 * (2 * D) ^ t := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hcard : ((W n).card : ℝ) ≤ Real.exp (n * (h + ε)) :=
      card_le_of_subset_typicalWords (Finset.filter_subset _ _)
    calc ∑ w ∈ W n, (S.alpha₁ (List.ofFn w) / S.coverRadius t (List.ofFn w) + 1) *
          (S.alpha₂ (List.ofFn w) / S.coverRadius t (List.ofFn w) + 1) *
          (2 * S.coverRadius t (List.ofFn w) * D) ^ t
        ≤ ∑ _w ∈ W n, 4 * (2 * D) ^ t * Real.exp (n * (energy l1 l2 t + 2 * ε)) := by
          refine Finset.sum_le_sum fun w hw => ?_
          obtain ⟨-, hw1, hw2⟩ := Finset.mem_filter.1 hw
          exact S.cover_cost_le ht0 ht2 hε.le hD hw1 hw2
      _ = (W n).card * (4 * (2 * D) ^ t * Real.exp (n * (energy l1 l2 t + 2 * ε))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Real.exp (n * (h + ε)) *
          (4 * (2 * D) ^ t * Real.exp (n * (energy l1 l2 t + 2 * ε))) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 4 * (2 * D) ^ t * Real.exp (n * (h + energy l1 l2 t + 3 * ε)) := by
          rw [mul_left_comm, ← Real.exp_add]
          ring_nf
      _ ≤ 4 * (2 * D) ^ t * 1 := by
          gcongr
          rw [Real.exp_le_one_iff]
          have : h + energy l1 l2 t + 3 * ε ≤ 0 := by rw [hε_def]; linarith
          exact mul_nonpos_of_nonneg_of_nonpos hn this
      _ = 4 * (2 * D) ^ t := mul_one _
  have hdimN : ∀ N, dimH (E N) ≤ ENNReal.ofReal t := fun N => by
    have hH := S.hausdorffMeasure_iInter_wordRect_le (x₀ := x₀) hD hS ht0
      (S.coverRadius_pos t) (S.coverRadius_le_alpha₁ t) W N (fun n _ => hK n)
    have hne : μH[((t.toNNReal : ℝ≥0) : ℝ)] (E N) ≠ ∞ := by
      rw [Real.coe_toNNReal t ht0]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH
    exact dimH_le_of_hausdorffMeasure_ne_top hne
  have hmeas : MeasurableSet (⋃ N, E N) :=
    MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
      Finset.measurableSet_biUnion (W n) fun w _ => S.measurableSet_wordRect _ _ _
  have hae : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, block n x ∈ W n := by
    filter_upwards [ae_eventually_block_mem_typicalWords herg hε,
      S.ae_tendsto_log_norm_matWord herg, S.ae_tendsto_log_alpha₂_matWord herg]
      with x hx h1 h2
    filter_upwards [hx, eventually_le_exp_of_tendsto_log (fun n => S.norm_matWord_pos _) hε h1,
      eventually_le_exp_of_tendsto_log (fun n => S.abs_det_div_norm_matWord_pos _) hε h2]
      with n hn hn1 hn2
    refine Finset.mem_filter.2 ⟨hn, ?_, ?_⟩
    · rw [← futureWord_eq_ofFn_block, alpha₁_eq_norm]
      exact hn1
    · rw [← futureWord_eq_ofFn_block, alpha₂_eq_abs_det_div_norm]
      exact hn2
  refine ⟨⋃ N, E N, hmeas, ?_, ?_⟩
  · rw [Measure.map_apply hS.measurable_proj hmeas.compl]
    have hnull := ae_iff.1 hae
    refine measure_mono_null ?_ hnull
    intro x hx hev
    apply hx
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine mem_iUnion.2 ⟨N, mem_iInter₂.2 fun n hn => mem_iUnion₂.2 ⟨block n x, hN n hn, ?_⟩⟩
    rw [← futureWord_eq_ofFn_block]
    exact hS.proj_mem_wordRect hdist hx₀ n x
  · rw [dimH_iUnion]
    exact iSup_le hdimN

/-- Rossi's bound `eq:hausdorff_ergodic_lyapunov` almost everywhere (Rossi, J. Math. Anal.
Appl. 413 (2014), Theorem 2.2; tex lines 2598 to 2601): for an ergodic `μ ∈ M_σ(Σ)`,
`\underline{dim}_loc(π_*μ, x) ≤ min{2, dimL(𝖠, μ)}` for `π_*μ`-almost every `x`. For every
`t ∈ (dimL(𝖠, μ), 2)` the energy condition `h_0(μ) + Λ(𝖠, μ, t) < 0` holds, and
`exists_dimH_le_of_add_energy_neg` with `ae_lowerLocalDim_le_of_dimH_le` gives the bound `t`;
the bound `2` holds for every finite measure on the plane. -/
theorem ae_lowerLocalDim_map_proj_le (herg : Ergodic (shift 1) μ) :
    ∀ᵐ y ∂(μ.map S.proj), lowerLocalDim (μ.map S.proj) y ≤
      min 2 (lyapDim (entropy μ) (S.lyapunov₁ μ) (S.lyapunov₂ μ)) := by
  set L := lyapDim (entropy μ) (S.lyapunov₁ μ) (S.lyapunov₂ μ) with hL
  have hinv := herg.toMeasurePreserving
  have hl1 := S.lyapunov₁_neg hinv
  have hl := S.lyapunov₂_le_lyapunov₁ hinv
  have hL0 : 0 ≤ L := lyapDim_nonneg hl hl1 (entropy_nonneg hinv)
  have hm0 : 0 ≤ min 2 L := le_min (by norm_num) hL0
  have h2 : ∀ᵐ y ∂(μ.map S.proj), lowerLocalDim (μ.map S.proj) y ≤ 2 := by
    simpa using ae_lowerLocalDim_le (μ := μ.map S.proj)
  have hk : ∀ k : ℕ, ∀ᵐ y ∂(μ.map S.proj),
      lowerLocalDim (μ.map S.proj) y ≤ min 2 L + 1 / ((k : ℝ) + 1) := by
    intro k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := Nat.one_div_pos_of_nat
    rcases le_or_gt 2 (min 2 L + 1 / ((k : ℝ) + 1)) with ht2 | ht2
    · exact h2.mono fun y hy => hy.trans ht2
    · have hL2 : L < 2 := by
        have : min 2 L < 2 := by linarith
        exact (min_lt_iff.1 this).resolve_left (lt_irrefl 2)
      have hmin : min 2 L = L := min_eq_right hL2.le
      rw [hmin] at ht2 ⊢
      obtain ⟨E, -, hE, hdim⟩ := S.exists_dimH_le_of_add_energy_neg herg
        (t := L + 1 / ((k : ℝ) + 1)) (by linarith) ht2.le
        (add_energy_neg_of_lyapDim_lt hl hl1 (by rw [← hL]; linarith) ht2.le)
      exact ae_lowerLocalDim_le_of_dimH_le hE (by linarith) hdim
  filter_upwards [ae_all_iff.2 hk] with y hy
  have hlim : Tendsto (fun k : ℕ => min 2 L + 1 / ((k : ℝ) + 1)) atTop (𝓝 (min 2 L)) := by
    have h := (tendsto_const_nhds (x := min 2 L) (f := (atTop : Filter ℕ))).add
      tendsto_one_div_add_atTop_nhds_zero_nat
    rwa [add_zero] at h
  exact ge_of_tendsto' hlim hy

/-- Rossi's bound `eq:hausdorff_ergodic_lyapunov` (Rossi, J. Math. Anal. Appl. 413 (2014),
Theorem 2.2; tex lines 2598 to 2601) for the essential supremum of the lower pointwise
dimension, which is `\overline{dim}_H(π_*μ)`: for every ergodic `μ ∈ M_σ(Σ)`,
`\overline{dim}_H(π_*μ) ≤ min{2, dimL(𝖠, μ)}`. -/
theorem essSup_lowerLocalDim_map_proj_le (herg : Ergodic (shift 1) μ) :
    essSup (lowerLocalDim (μ.map S.proj)) (μ.map S.proj) ≤
      min 2 (lyapDim (entropy μ) (S.lyapunov₁ μ) (S.lyapunov₂ μ)) := by
  have : (ae (μ.map S.proj)).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero _)
  exact essSup_le_of_ae_le _ (S.ae_lowerLocalDim_map_proj_le herg)
    (isCoboundedUnder_le_of_le _ fun y => lowerLocalDim_nonneg y)

end Rossi

end System

end BoxLike
