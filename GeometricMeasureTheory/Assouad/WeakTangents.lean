/-
# Section 5.3: Hausdorff convergence and weak tangents

Weak tangents are Hausdorff limits of magnified pieces of a closed set. They bound the Assouad
dimension from below, which gives the Assouad dimension of the reciprocal sequence and an example
of a Lipschitz map that increases Assouad dimension.

Similarities are Mathlib's bijective dilations `V ≃ᵈ V`, whose ratio scales all distances.

| Notes | Lean declaration | Location |
|---|---|---|
| Definition 5.5 (Hausdorff distance) | `Metric.hausdorffDist`, `EMetric.hausdorffEdist` | `Mathlib/Topology/MetricSpace/HausdorffDistance.lean` |
| The Hausdorff distance on compact sets | `TopologicalSpace.NonemptyCompacts.dist_eq` | `Mathlib/Topology/MetricSpace/Closeds.lean` |
| Lemma 5.6 (compactness of the space of compact sets) | the `CompactSpace (TopologicalSpace.NonemptyCompacts X)` instance | `Mathlib/Topology/Sets/VietorisTopology.lean` |
| Definition 5.7 (weak tangent) | `IsWeakTangent` | here |
| Proposition 5.8 (weak tangents bound the Assouad dimension) | `weak_tangent_bound` | here |
| Example 5.9 (the reciprocal sequence) | `reciprocal_assouad` | here |
| Example 5.10 (a Lipschitz map increasing Assouad dimension) | `lipschitz_assouad_increase` | here |
| Theorem 5.11 (Käenmäki–Ojala–Rossi) | not formalised | |
-/
import GeometricMeasureTheory.Assouad.Doubling

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

/-! ## Definition 5.5 and Lemma 5.6

The Hausdorff distance and the compactness of the space of non-empty compact subsets of a compact
space are in Mathlib. -/

example {X : Type*} [MetricSpace X] (A B : TopologicalSpace.NonemptyCompacts X) :
    dist A B = Metric.hausdorffDist (A : Set X) B :=
  Metric.NonemptyCompacts.dist_eq

example {X : Type*} [MetricSpace X] [CompactSpace X] :
    CompactSpace (TopologicalSpace.NonemptyCompacts X) :=
  inferInstance

/-! ## Definition 5.7 (`def:weak-tangent`) -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Definition 5.7 (`def:weak-tangent`): `E` is a weak tangent of the closed set `F` if the
magnifications `T n '' F ∩ W` of `F` by similarities, inside a fixed compact window `W`, converge
to `E` in Hausdorff distance. -/
def IsWeakTangent (E F : Set V) : Prop :=
  IsCompact E ∧ E.Nonempty ∧ ∃ (T : ℕ → V ≃ᵈ V) (W : Set V), IsCompact W ∧
    (∀ n, (T n '' F ∩ W).Nonempty) ∧
    Tendsto (fun n => Metric.hausdorffDist (T n '' F ∩ W) E) atTop (𝓝 0)

/-! ## Covering numbers and Assouad dimension

Two elementary comparisons of covering numbers, and the two ways of reading the infimum defining
the Assouad dimension. -/

variable {X : Type*} [MetricSpace X]

/-- An exponent satisfying the two-scale bound dominates the Assouad dimension. -/
theorem assouadDim_le_of_assouadDimLE {E : Set X} {s : ℝ≥0} (h : AssouadDimLE E s) :
    assouadDim E ≤ s := iInf₂_le s h

/-- A set satisfying the two-scale bound for every positive exponent has Assouad dimension zero. -/
theorem assouadDim_eq_zero_of_forall_pos {E : Set X} (h : ∀ s : ℝ≥0, 0 < s → AssouadDimLE E s) :
    assouadDim E = 0 := by
  refine le_antisymm (not_lt.1 fun hlt => ?_) zero_le
  obtain ⟨t, ht0, htx⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
  exact absurd (assouadDim_le_of_assouadDimLE (h t (by exact_mod_cast ht0))) (not_le.2 htx)

/-- A cover of a set gives a cover of a Lipschitz image, with the radius scaled by the constant.
Unlike `externalCoveringNumber_image_le`, the centres are not moved, so no factor of two is
lost. -/
theorem externalCoveringNumber_image_lipschitzWith_le {Y Z : Type*} [PseudoEMetricSpace Y]
    [PseudoEMetricSpace Z] {f : Y → Z} {K ε : ℝ≥0} (hf : LipschitzWith K f) (A : Set Y) :
    Metric.externalCoveringNumber (K * ε) (f '' A) ≤ Metric.externalCoveringNumber ε A :=
  le_iInf₂ fun _ hN => ((hN.image_lipschitz hf).externalCoveringNumber_le_encard).trans
    (encard_image_le _ _)

/-- If every point of `A` lies within `d` of `B`, a cover of `B` at radius `ε` becomes a cover of
`A` at radius `d + ε`. -/
theorem externalCoveringNumber_le_of_forall_dist_le {A B : Set X} {d ε δ : ℝ≥0}
    (h : ∀ z ∈ A, ∃ b ∈ B, dist z b ≤ (d : ℝ)) (hδ : d + ε ≤ δ) :
    Metric.externalCoveringNumber δ A ≤ Metric.externalCoveringNumber ε B := by
  refine le_iInf₂ fun N hN => Metric.IsCover.externalCoveringNumber_le_encard ?_
  rw [Metric.isCover_iff_subset_iUnion_closedBall] at hN ⊢
  intro z hz
  obtain ⟨b, hb, hzb⟩ := h z hz
  obtain ⟨c, hc, hbc⟩ := mem_iUnion₂.1 (hN hb)
  refine mem_iUnion₂.2 ⟨c, hc, ?_⟩
  simp only [mem_closedBall] at hbc ⊢
  calc dist z c ≤ dist z b + dist b c := dist_triangle _ _ _
    _ ≤ (d : ℝ) + (ε : ℝ) := add_le_add hzb hbc
    _ ≤ (δ : ℝ) := by exact_mod_cast hδ

/-! ## Proposition 5.8 (`thm:weak-tangent-bound`) -/

/-- A similarity image satisfies the two-scale covering bound of the set with the same constant,
because a similarity preserves the ratio of the two scales. -/
theorem assouadBound_image_dilationEquiv {F : Set X} {s : ℝ} {C : ℝ≥0} (T : X ≃ᵈ X)
    (hC : ∀ x ∈ F, ∀ r R : ℝ, 0 < r → r < R →
      (Metric.externalCoveringNumber r.toNNReal (F ∩ ball x R) : ℝ≥0∞) ≤
        C * ENNReal.ofReal ((R / r) ^ s))
    {x : X} (hx : x ∈ T '' F) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    (Metric.externalCoveringNumber r.toNNReal (T '' F ∩ ball x R) : ℝ≥0∞) ≤
      C * ENNReal.ofReal ((R / r) ^ s) := by
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  set lam : ℝ≥0 := Dilation.ratio T with hlamdef
  have hlam : (0 : ℝ) < lam := Dilation.ratio_pos T
  have hsub : T '' F ∩ ball (T x₀) R ⊆ T '' (F ∩ ball x₀ (R / lam)) := by
    rintro z ⟨⟨w, hw, rfl⟩, hz⟩
    refine ⟨w, ⟨hw, ?_⟩, rfl⟩
    rw [mem_ball] at hz ⊢
    rw [Dilation.dist_eq T w x₀] at hz
    exact (lt_div_iff₀' hlam).2 hz
  have hradius : lam * (r / lam).toNNReal = r.toNNReal := by
    calc lam * (r / lam).toNNReal = ((lam : ℝ)).toNNReal * (r / lam).toNNReal := by
          rw [Real.toNNReal_coe]
      _ = ((lam : ℝ) * (r / lam)).toNNReal := (Real.toNNReal_mul hlam.le).symm
      _ = r.toNNReal := by rw [mul_div_cancel₀ _ (ne_of_gt hlam)]
  have h1 : Metric.externalCoveringNumber r.toNNReal (T '' (F ∩ ball x₀ (R / lam)))
      ≤ Metric.externalCoveringNumber (r / lam).toNNReal (F ∩ ball x₀ (R / lam)) := by
    rw [← hradius]
    exact externalCoveringNumber_image_lipschitzWith_le (Dilation.lipschitz T) _
  have hquot : (R / lam) / (r / lam) = R / r := by
    field_simp
  calc (Metric.externalCoveringNumber r.toNNReal (T '' F ∩ ball (T x₀) R) : ℝ≥0∞)
      ≤ (Metric.externalCoveringNumber (r / lam).toNNReal (F ∩ ball x₀ (R / lam)) : ℝ≥0∞) :=
        ENat.toENNReal_le.2 ((Metric.externalCoveringNumber_mono_set hsub).trans h1)
    _ ≤ C * ENNReal.ofReal (((R / lam) / (r / lam)) ^ s) :=
        hC x₀ hx₀ (r / lam) (R / lam) (by positivity) (by gcongr)
    _ = C * ENNReal.ofReal ((R / r) ^ s) := by rw [hquot]

omit [NormedSpace ℝ V] in
/-- Proposition 5.8 (`thm:weak-tangent-bound`): a weak tangent has Assouad dimension at most that
of the set. Neither closedness nor non-emptiness of `F` is needed for the covering estimate. -/
theorem weak_tangent_bound {E F : Set V} (h : IsWeakTangent E F) :
    assouadDim E ≤ assouadDim F := by
  obtain ⟨hEc, hEne, T, W, hWc, hWne, htend⟩ := h
  refine le_iInf₂ fun s hs => ?_
  obtain ⟨C, hC1, hC⟩ := hs
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.coe_nonneg
  have h8 : (1 : ℝ) ≤ (8 : ℝ) ^ (s : ℝ) := Real.one_le_rpow (by norm_num) hs0
  refine assouadDim_le_of_assouadDimLE ⟨C * ((8 : ℝ) ^ (s : ℝ)).toNNReal, ?_, ?_⟩
  · calc (1 : ℝ≥0) = 1 * 1 := (one_mul 1).symm
      _ ≤ C * ((8 : ℝ) ^ (s : ℝ)).toNNReal :=
          mul_le_mul' hC1 (by simpa using Real.toNNReal_le_toNNReal h8)
  · intro y hy r R hr hrR
    have hr8 : (0 : ℝ) < r / 8 := by positivity
    obtain ⟨n, hn⟩ := (htend.eventually_lt_const hr8).exists
    have hAne : (T n '' F ∩ W).Nonempty := hWne n
    have hAbdd : Bornology.IsBounded (T n '' F ∩ W) := hWc.isBounded.subset inter_subset_right
    have hfin : Metric.hausdorffEDist E (T n '' F ∩ W) ≠ ⊤ :=
      Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded hEne hAne hEc.isBounded hAbdd
    have hEA : Metric.hausdorffDist E (T n '' F ∩ W) < r / 8 := by
      rwa [Metric.hausdorffDist_comm]
    obtain ⟨x, hxA, hyx⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hy hEA hfin
    have key : ∀ z ∈ E ∩ ball y R, ∃ b ∈ T n '' F ∩ ball x (2 * R),
        dist z b ≤ (((r / 8).toNNReal : ℝ≥0) : ℝ) := by
      rintro z ⟨hzE, hzy⟩
      obtain ⟨b, hbA, hzb⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hzE hEA hfin
      have hbz : dist b z < r / 8 := by rwa [dist_comm]
      rw [mem_ball] at hzy
      refine ⟨b, ⟨hbA.1, ?_⟩, ?_⟩
      · rw [mem_ball]
        have htri : dist b x ≤ dist b z + dist z y + dist y x := by
          calc dist b x ≤ dist b z + dist z x := dist_triangle _ _ _
            _ ≤ dist b z + (dist z y + dist y x) := by gcongr; exact dist_triangle _ _ _
            _ = dist b z + dist z y + dist y x := by ring
        linarith
      · rw [Real.coe_toNNReal _ hr8.le]
        exact hzb.le
    have hcov : Metric.externalCoveringNumber r.toNNReal (E ∩ ball y R)
        ≤ Metric.externalCoveringNumber (r / 4).toNNReal (T n '' F ∩ ball x (2 * R)) :=
      externalCoveringNumber_le_of_forall_dist_le key (by
        rw [← Real.toNNReal_add hr8.le (by positivity)]
        exact Real.toNNReal_le_toNNReal (by linarith))
    have hbound := assouadBound_image_dilationEquiv (T n) hC hxA.1
      (r := r / 4) (R := 2 * R) (by positivity) (by linarith)
    have hq : 2 * R / (r / 4) = 8 * (R / r) := by
      field_simp
      ring
    calc (Metric.externalCoveringNumber r.toNNReal (E ∩ ball y R) : ℝ≥0∞)
        ≤ (Metric.externalCoveringNumber (r / 4).toNNReal (T n '' F ∩ ball x (2 * R)) : ℝ≥0∞) :=
          ENat.toENNReal_le.2 hcov
      _ ≤ C * ENNReal.ofReal ((2 * R / (r / 4)) ^ (s : ℝ)) := hbound
      _ = (C * ((8 : ℝ) ^ (s : ℝ)).toNNReal : ℝ≥0) * ENNReal.ofReal ((R / r) ^ (s : ℝ)) := by
          rw [hq, Real.mul_rpow (by norm_num) (div_nonneg (by linarith) hr.le),
            ENNReal.ofReal_mul (by positivity),
            ENNReal.coe_mul, ← mul_assoc]
          rfl

/-! ## Examples 5.9 and 5.10 -/

/-- A non-degenerate interval has Assouad dimension one. -/
theorem assouadDim_Icc {a b : ℝ} (hab : a < b) : assouadDim (Icc a b) = 1 := by
  refine le_antisymm ?_ ?_
  · simpa using assouadDim_le_finrank (Icc a b)
  · have h := upperBoxDim_le_assouadDim (E := Icc a b) (isBounded_Icc a b)
      ⟨a, left_mem_Icc.2 hab.le⟩
    rwa [(box_interval hab).2] at h

/-- If `S` contains `0` and all the points `c / m` with `m ≥ c`, then its largest gap in `[0, 1]`
is at most `1 / c`. -/
theorem infDist_le_of_forall_div_mem {c : ℝ} (hc : 1 ≤ c) {S : Set ℝ} (h0 : (0 : ℝ) ∈ S)
    (hS : ∀ m : ℕ, 1 ≤ m → c ≤ (m : ℝ) → c / m ∈ S) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    Metric.infDist u S ≤ 1 / c := by
  obtain ⟨hu0, hu1⟩ := hu
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
  rcases eq_or_lt_of_le hu0 with h | hu0'
  · calc Metric.infDist u S ≤ dist u 0 := Metric.infDist_le_dist_of_mem h0
      _ = 0 := by rw [← h]; simp
      _ ≤ 1 / c := by positivity
  · have hcu0 : 0 < c / u := by positivity
    have hm1 : 1 ≤ ⌈c / u⌉₊ := Nat.one_le_ceil_iff.2 hcu0
    set M : ℝ := (⌈c / u⌉₊ : ℝ) with hMdef
    have hM : 0 < M := by
      rw [hMdef]
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm1
    have h1 : c / u ≤ M := Nat.le_ceil _
    have h2 : M ≤ c / u + 1 := (Nat.ceil_lt_add_one hcu0.le).le
    have hdiv : c / u * u = c := div_mul_cancel₀ c hu0'.ne'
    have hcu : c ≤ u * M := by
      linarith [mul_le_mul_of_nonneg_right h1 hu0'.le, hdiv]
    have hMc : u * M ≤ c + u := by
      linarith [mul_le_mul_of_nonneg_right h2 hu0'.le, hdiv]
    have hccu : c ≤ c / u := by rw [le_div_iff₀ hu0']; nlinarith
    have huc : u * c ≤ M := by nlinarith
    have hcm : c ≤ M := le_trans hccu h1
    have hple : c / M ≤ u := by rw [div_le_iff₀ hM]; linarith
    calc Metric.infDist u S ≤ dist u (c / M) :=
          Metric.infDist_le_dist_of_mem (hS _ hm1 hcm)
      _ = |u - c / M| := Real.dist_eq _ _
      _ ≤ 1 / c := by
          rw [abs_le]
          refine ⟨?_, ?_⟩
          · have hinv : (0 : ℝ) < 1 / c := by positivity
            linarith
          rw [sub_le_iff_le_add, div_add_div _ _ (ne_of_gt hc0) (ne_of_gt hM),
            le_div_iff₀ (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_right hMc hc0.le]

/-- Example 5.9 (`ex:reciprocal-assouad`): the unit interval is a weak tangent of the reciprocal
sequence, whose Assouad dimension is therefore one. -/
theorem reciprocal_assouad :
    IsWeakTangent (Icc (0 : ℝ) 1) (insert (0 : ℝ) (Set.range fun n : ℕ => ((n : ℝ) + 1)⁻¹)) ∧
      assouadDim (insert (0 : ℝ) (Set.range fun n : ℕ => ((n : ℝ) + 1)⁻¹)) = 1 := by
  have hTapp : ∀ (c : ℝ) (hc : c ≠ 0) (x : ℝ), DilationEquiv.mulLeft c hc x = c * x :=
    fun _ _ _ => rfl
  set F : Set ℝ := insert (0 : ℝ) (Set.range fun n : ℕ => ((n : ℝ) + 1)⁻¹) with hFdef
  have h0F : (0 : ℝ) ∈ F := mem_insert _ _
  have hmemF : ∀ m : ℕ, 1 ≤ m → ((m : ℝ))⁻¹ ∈ F := by
    intro m hm
    refine mem_insert_of_mem _ ⟨m - 1, ?_⟩
    show (((m - 1 : ℕ) : ℝ) + 1)⁻¹ = ((m : ℝ))⁻¹
    congr 1
    have h1 : (1 : ℕ) ≤ m := hm
    push_cast [Nat.cast_sub h1]
    ring
  have hFcompact : IsCompact F :=
    Filter.Tendsto.isCompact_insert_range (by
      simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have htangent : IsWeakTangent (Icc (0 : ℝ) 1) F := by
    refine ⟨isCompact_Icc, ⟨0, by norm_num⟩, fun k => DilationEquiv.mulLeft ((k : ℝ) + 1)
      (by positivity), Icc 0 1, isCompact_Icc, fun k => ?_, ?_⟩
    · exact ⟨0, ⟨⟨0, h0F, by rw [hTapp, mul_zero]⟩, by norm_num⟩⟩
    · refine squeeze_zero (fun k => Metric.hausdorffDist_nonneg) (fun k => ?_)
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
      refine Metric.hausdorffDist_le_of_infDist (by positivity) (fun z hz => ?_) (fun u hu => ?_)
      · calc Metric.infDist z (Icc (0 : ℝ) 1) ≤ dist z z := Metric.infDist_le_dist_of_mem hz.2
          _ = 0 := dist_self z
          _ ≤ 1 / ((k : ℝ) + 1) := by positivity
      · refine infDist_le_of_forall_div_mem hk1 ?_ ?_ hu
        · exact ⟨⟨0, h0F, by rw [hTapp, mul_zero]⟩, by norm_num⟩
        · intro m hm hcm
          have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
          refine ⟨⟨((m : ℝ))⁻¹, hmemF m hm, by rw [hTapp, div_eq_mul_inv]⟩, by positivity, ?_⟩
          rw [div_le_one hm0]
          exact hcm
  refine ⟨htangent, le_antisymm ?_ ?_⟩
  · simpa using assouadDim_le_finrank F
  · calc (1 : ℝ≥0∞) = assouadDim (Icc (0 : ℝ) 1) := (assouadDim_Icc (by norm_num)).symm
      _ ≤ assouadDim F := weak_tangent_bound htangent

/-! ### Example 5.10

The set is `{0} ∪ {2 ^ (-m)}`. The map sends the block of `n + 1` points with indices
`n ^ 2 ≤ m ≤ n ^ 2 + n` onto the arithmetic grid of spacing `2 ^ (-n(n+1)) / n`, and every other
point to `0`. -/

/-- The dyadic points `2 ^ (-m)` of Example 5.10. -/
def dyadicPoint (m : ℕ) : ℝ := (1 / 2 : ℝ) ^ m

/-- The compact set `{0} ∪ {2 ^ (-m)}` of Example 5.10. -/
def dyadicSet : Set ℝ := insert 0 (Set.range dyadicPoint)

/-- The values of the block map on the dyadic points: on the block `n ^ 2 ≤ m ≤ n ^ 2 + n` the
point `2 ^ (-m)` is sent to `(m - n ^ 2) / n * 2 ^ (-n(n+1))`, and the remaining points to `0`. -/
def blockValue (m : ℕ) : ℝ :=
  if m ≤ Nat.sqrt m * Nat.sqrt m + Nat.sqrt m then
    ((m - Nat.sqrt m * Nat.sqrt m : ℕ) : ℝ) / (Nat.sqrt m : ℝ) *
      (1 / 2 : ℝ) ^ (Nat.sqrt m * Nat.sqrt m + Nat.sqrt m)
  else 0

/-- The Lipschitz map of Example 5.10, extended by zero off the dyadic points. -/
def blockMap : ℝ → ℝ := Function.extend dyadicPoint blockValue 0

theorem dyadicPoint_pos (m : ℕ) : 0 < dyadicPoint m := by
  unfold dyadicPoint; positivity

theorem dyadicPoint_injective : Function.Injective dyadicPoint :=
  (pow_right_strictAnti₀ (by norm_num) (by norm_num)).injective

theorem dyadicPoint_lt_dyadicPoint {a b : ℕ} (h : a < b) : dyadicPoint b < dyadicPoint a :=
  pow_right_strictAnti₀ (by norm_num) (by norm_num) h

theorem zero_mem_dyadicSet : (0 : ℝ) ∈ dyadicSet := mem_insert _ _

theorem dyadicPoint_mem_dyadicSet (m : ℕ) : dyadicPoint m ∈ dyadicSet :=
  mem_insert_of_mem _ ⟨m, rfl⟩

theorem isCompact_dyadicSet : IsCompact dyadicSet :=
  Filter.Tendsto.isCompact_insert_range
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

theorem blockMap_zero : blockMap 0 = 0 := by
  have h : ¬∃ m, dyadicPoint m = 0 := fun ⟨m, hm⟩ => (dyadicPoint_pos m).ne' hm
  simpa [blockMap] using Function.extend_apply' blockValue (0 : ℝ → ℝ) 0 h

theorem blockMap_dyadicPoint (m : ℕ) : blockMap (dyadicPoint m) = blockValue m :=
  dyadicPoint_injective.extend_apply _ _ _

theorem blockValue_nonneg (m : ℕ) : 0 ≤ blockValue m := by
  unfold blockValue
  split_ifs with h
  · positivity
  · exact le_rfl

theorem blockValue_le (m : ℕ) : blockValue m ≤ dyadicPoint m := by
  unfold blockValue dyadicPoint
  split_ifs with h
  · rcases Nat.eq_zero_or_pos (Nat.sqrt m) with hn | hn
    · simp only [hn, Nat.cast_zero, div_zero, zero_mul]
      positivity
    · have hj : (m - Nat.sqrt m * Nat.sqrt m : ℕ) ≤ Nat.sqrt m := by omega
      have hfrac : ((m - Nat.sqrt m * Nat.sqrt m : ℕ) : ℝ) / (Nat.sqrt m : ℝ) ≤ 1 := by
        rw [div_le_one (by exact_mod_cast hn)]
        exact_mod_cast hj
      calc ((m - Nat.sqrt m * Nat.sqrt m : ℕ) : ℝ) / (Nat.sqrt m : ℝ) *
              (1 / 2 : ℝ) ^ (Nat.sqrt m * Nat.sqrt m + Nat.sqrt m)
          ≤ 1 * (1 / 2 : ℝ) ^ (Nat.sqrt m * Nat.sqrt m + Nat.sqrt m) := by gcongr
        _ = (1 / 2 : ℝ) ^ (Nat.sqrt m * Nat.sqrt m + Nat.sqrt m) := one_mul _
        _ ≤ (1 / 2 : ℝ) ^ m := pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  · positivity

/-- On the `n`-th block the map takes the values of an arithmetic grid of `n + 1` points. -/
theorem blockValue_grid {n j : ℕ} (hn : 1 ≤ n) (hj : j ≤ n) :
    blockValue (n * n + j) = (j : ℝ) / (n : ℝ) * (1 / 2 : ℝ) ^ (n * n + n) := by
  have hsqrt : Nat.sqrt (n * n + j) = n := by
    have h1 : n ≤ Nat.sqrt (n * n + j) := Nat.le_sqrt.2 (by omega)
    have h2 : Nat.sqrt (n * n + j) < n + 1 := Nat.sqrt_lt'.2 (by nlinarith)
    omega
  unfold blockValue
  rw [hsqrt, if_pos (Nat.add_le_add_left hj _), Nat.add_sub_cancel_left]

theorem blockMap_nonneg_le {x : ℝ} (hx : x ∈ dyadicSet) : 0 ≤ blockMap x ∧ blockMap x ≤ x := by
  rcases hx with rfl | ⟨m, rfl⟩
  · rw [blockMap_zero]
    exact ⟨le_rfl, le_rfl⟩
  · rw [blockMap_dyadicPoint]
    exact ⟨blockValue_nonneg m, blockValue_le m⟩

/-- Distinct points of the dyadic set are separated by a factor of two. -/
theorem dyadicSet_two_mul_le {x y : ℝ} (hx : x ∈ dyadicSet) (hy : y ∈ dyadicSet) (hlt : y < x) :
    2 * y ≤ x := by
  rcases hy with rfl | ⟨b, rfl⟩
  · rcases hx with rfl | ⟨a, rfl⟩
    · linarith
    · linarith [(dyadicPoint_pos a).le]
  · rcases hx with rfl | ⟨a, rfl⟩
    · exact absurd hlt (not_lt.2 (dyadicPoint_pos b).le)
    · have hab : a < b := by
        by_contra hle
        exact absurd hlt (not_lt.2 (by
          rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hle) with rfl | h
          · exact le_rfl
          · exact (dyadicPoint_lt_dyadicPoint h).le))
      have h1 : dyadicPoint b ≤ dyadicPoint (a + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hab
      have h2 : dyadicPoint (a + 1) = dyadicPoint a / 2 := by
        unfold dyadicPoint; rw [pow_succ]; ring
      linarith

theorem lipschitzOnWith_blockMap : LipschitzOnWith 2 blockMap dyadicSet := by
  have key : ∀ x ∈ dyadicSet, ∀ y ∈ dyadicSet, y ≤ x →
      dist (blockMap x) (blockMap y) ≤ 2 * dist x y := by
    intro x hx y hy hyx
    obtain ⟨hfx0, hfx⟩ := blockMap_nonneg_le hx
    obtain ⟨hfy0, hfy⟩ := blockMap_nonneg_le hy
    rcases eq_or_lt_of_le hyx with rfl | hlt
    · simp
    · have h2y : 2 * y ≤ x := dyadicSet_two_mul_le hx hy hlt
      have habs : |blockMap x - blockMap y| ≤ x := abs_le.2 ⟨by linarith, by linarith⟩
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (by linarith : (0:ℝ) ≤ x - y)]
      linarith
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rcases le_total y x with h | h
  · simpa using key x hx y hy h
  · rw [dist_comm, dist_comm x y]
    simpa using key y hy x hx h

/-- The two-scale covering estimate for the dyadic set: at most `log₂(2R/r) + 3` balls of radius
`r` cover the part of the set in a ball of radius `R`. -/
theorem externalCoveringNumber_dyadicSet_le {x : ℝ} {r R : ℝ} (hr : 0 < r) :
    Metric.externalCoveringNumber r.toNNReal (dyadicSet ∩ ball x R)
      ≤ ((⌊Real.log (2 * R / r) / Real.log 2⌋₊ + 3 : ℕ) : ℕ∞) := by
  classical
  set N : ℕ := ⌊Real.log (2 * R / r) / Real.log 2⌋₊ with hNdef
  set K : Set ℕ := {k | r < dyadicPoint k ∧ dyadicPoint k ∈ ball x R} with hKdef
  set K₁ : Set ℕ := {k ∈ K | dyadicPoint k ≤ 2 * R} with hK₁def
  set K₂ : Set ℕ := {k ∈ K | 2 * R < dyadicPoint k} with hK₂def
  have hcover : Metric.IsCover r.toNNReal (dyadicSet ∩ ball x R) (insert 0 (dyadicPoint '' K)) := by
    rw [Metric.isCover_iff_subset_iUnion_closedBall]
    rintro z ⟨hzE, hzB⟩
    rcases hzE with rfl | ⟨k, rfl⟩
    · exact mem_iUnion₂.2 ⟨0, mem_insert _ _, by simp⟩
    · by_cases hk : r < dyadicPoint k
      · exact mem_iUnion₂.2 ⟨dyadicPoint k, mem_insert_of_mem _ ⟨k, ⟨hk, hzB⟩, rfl⟩, by simp⟩
      · refine mem_iUnion₂.2 ⟨0, mem_insert _ _, ?_⟩
        simp only [mem_closedBall, Real.dist_eq, sub_zero,
          abs_of_pos (dyadicPoint_pos k), Real.coe_toNNReal _ hr.le]
        exact not_lt.1 hk
  have hK₂le : K₂.encard ≤ 1 := by
    have haux : ∀ a b : ℕ, a < b → b ∈ K₂ → a ∈ K₂ → False := by
      intro a b hab hb ha
      have hsep : 2 * dyadicPoint b ≤ dyadicPoint a :=
        dyadicSet_two_mul_le (dyadicPoint_mem_dyadicSet a) (dyadicPoint_mem_dyadicSet b)
          (dyadicPoint_lt_dyadicPoint hab)
      have hda : dist (dyadicPoint a) x < R := ha.1.2
      have hdb : dist (dyadicPoint b) x < R := hb.1.2
      have htri : dist (dyadicPoint a) (dyadicPoint b) < 2 * R := by
        calc dist (dyadicPoint a) (dyadicPoint b)
            ≤ dist (dyadicPoint a) x + dist x (dyadicPoint b) := dist_triangle _ _ _
          _ < R + R := by rw [dist_comm x]; linarith
          _ = 2 * R := by ring
      rw [Real.dist_eq, abs_lt] at htri
      linarith [hb.2, htri.2]
    rw [Set.encard_le_one_iff]
    intro a b ha hb
    by_contra hne
    rcases Nat.lt_or_ge a b with h | h
    · exact haux a b h hb ha
    · exact haux b a (lt_of_le_of_ne h (Ne.symm hne)) ha hb
  have hK₁le : K₁.encard ≤ ((N + 1 : ℕ) : ℕ∞) := by
    rcases eq_empty_or_nonempty K₁ with hempty | hne
    · simp [hempty]
    · set a : ℕ := sInf K₁ with hadef
      have haK : a ∈ K₁ := Nat.sInf_mem hne
      have hsub : K₁ ⊆ ↑(Finset.Icc a (a + N)) := by
        intro k hk
        have hak : a ≤ k := Nat.sInf_le hk
        obtain ⟨d, rfl⟩ : ∃ d, k = a + d := ⟨k - a, by omega⟩
        have hpow : dyadicPoint a = (2 : ℝ) ^ d * dyadicPoint (a + d) := by
          have h2 : (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ d = 1 := by rw [← mul_pow]; norm_num
          unfold dyadicPoint
          rw [pow_add]
          calc (1 / 2 : ℝ) ^ a = (1 / 2 : ℝ) ^ a * 1 := (mul_one _).symm
            _ = (1 / 2 : ℝ) ^ a * ((2 : ℝ) ^ d * (1 / 2 : ℝ) ^ d) := by rw [h2]
            _ = (2 : ℝ) ^ d * ((1 / 2 : ℝ) ^ a * (1 / 2 : ℝ) ^ d) := by ring
        have hd2 : (2 : ℝ) ^ d < 2 * R / r := by
          rw [lt_div_iff₀ hr]
          have h1 : (2 : ℝ) ^ d * r < (2 : ℝ) ^ d * dyadicPoint (a + d) := by
            have : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
            exact mul_lt_mul_of_pos_left hk.1.1 this
          calc (2 : ℝ) ^ d * r < (2 : ℝ) ^ d * dyadicPoint (a + d) := h1
            _ = dyadicPoint a := hpow.symm
            _ ≤ 2 * R := haK.2
        have hlog : (d : ℝ) * Real.log 2 < Real.log (2 * R / r) := by
          rw [← Real.log_pow]
          exact Real.log_lt_log (by positivity) hd2
        have hdN : d ≤ N := by
          refine Nat.le_floor ?_
          rw [le_div_iff₀ (Real.log_pos (by norm_num))]
          exact hlog.le
        rw [Finset.coe_Icc]
        exact ⟨hak, by omega⟩
      calc K₁.encard ≤ (↑(Finset.Icc a (a + N)) : Set ℕ).encard := encard_le_encard hsub
        _ = ((Finset.Icc a (a + N)).card : ℕ∞) := encard_coe_eq_coe_finsetCard _
        _ = ((N + 1 : ℕ) : ℕ∞) := by rw [Nat.card_Icc]; congr 1; omega
  have hKle : K.encard ≤ ((N + 2 : ℕ) : ℕ∞) := by
    have hKsplit : K ⊆ K₁ ∪ K₂ := by
      intro k hk
      rcases le_or_gt (dyadicPoint k) (2 * R) with h | h
      · exact Or.inl ⟨hk, h⟩
      · exact Or.inr ⟨hk, h⟩
    calc K.encard ≤ (K₁ ∪ K₂).encard := encard_le_encard hKsplit
      _ ≤ K₁.encard + K₂.encard := encard_union_le _ _
      _ ≤ ((N + 1 : ℕ) : ℕ∞) + 1 := add_le_add hK₁le hK₂le
      _ = ((N + 2 : ℕ) : ℕ∞) := by push_cast; ring
  calc Metric.externalCoveringNumber r.toNNReal (dyadicSet ∩ ball x R)
      ≤ (insert 0 (dyadicPoint '' K)).encard := hcover.externalCoveringNumber_le_encard
    _ ≤ (dyadicPoint '' K).encard + 1 := encard_insert_le _ _
    _ ≤ K.encard + 1 := add_le_add (encard_image_le _ _) le_rfl
    _ ≤ ((N + 2 : ℕ) : ℕ∞) + 1 := add_le_add hKle le_rfl
    _ = ((N + 3 : ℕ) : ℕ∞) := by push_cast; ring

theorem assouadDim_dyadicSet : assouadDim dyadicSet = 0 := by
  refine assouadDim_eq_zero_of_forall_pos fun s hs => ?_
  have hs0 : (0 : ℝ) < (s : ℝ) := hs
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc0 : (0 : ℝ) < 1 / ((s : ℝ) * Real.log 2) := div_pos one_pos (mul_pos hs0 hlog2)
  refine ⟨(4 + 1 / ((s : ℝ) * Real.log 2)).toNNReal, ?_, ?_⟩
  · rw [Real.one_le_toNNReal]
    linarith
  · intro x _ r R hr hrR
    have hR : 0 < R := lt_trans hr hrR
    set t : ℝ := R / r with htdef
    have ht1 : 1 ≤ t := (one_le_div hr).2 hrR.le
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht1
    have hts : 1 ≤ t ^ (s : ℝ) := Real.one_le_rpow ht1 hs0.le
    have h2t : 2 * R / r = 2 * t := by rw [htdef]; ring
    have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht1
    have hkey : Real.log t ≤ t ^ (s : ℝ) / (s : ℝ) := by
      rw [le_div_iff₀ hs0]
      have h := Real.log_le_sub_one_of_pos (x := t ^ (s : ℝ)) (by positivity)
      rw [Real.log_rpow ht0] at h
      linarith
    set N : ℕ := ⌊Real.log (2 * R / r) / Real.log 2⌋₊ with hNdef
    have hfloor : (N : ℝ) ≤ 1 + Real.log t / Real.log 2 := by
      have hle : (N : ℝ) ≤ Real.log (2 * R / r) / Real.log 2 := by
        refine Nat.floor_le ?_
        rw [h2t]
        exact div_nonneg (Real.log_nonneg (by linarith)) hlog2.le
      rw [h2t, Real.log_mul (by norm_num) (by positivity), add_div,
        div_self (ne_of_gt hlog2)] at hle
      exact hle
    have hfinal : ((N : ℝ) + 3) ≤ (4 + 1 / ((s : ℝ) * Real.log 2)) * t ^ (s : ℝ) := by
      have h3 : t ^ (s : ℝ) / (s : ℝ) / Real.log 2
          = 1 / ((s : ℝ) * Real.log 2) * t ^ (s : ℝ) := by
        field_simp
      calc ((N : ℝ) + 3) ≤ (1 + Real.log t / Real.log 2) + 3 := by linarith
        _ = 4 + Real.log t / Real.log 2 := by ring
        _ ≤ 4 + t ^ (s : ℝ) / (s : ℝ) / Real.log 2 := by gcongr
        _ = 4 + 1 / ((s : ℝ) * Real.log 2) * t ^ (s : ℝ) := by rw [h3]
        _ ≤ 4 * t ^ (s : ℝ) + 1 / ((s : ℝ) * Real.log 2) * t ^ (s : ℝ) := by nlinarith
        _ = (4 + 1 / ((s : ℝ) * Real.log 2)) * t ^ (s : ℝ) := by ring
    calc (Metric.externalCoveringNumber r.toNNReal (dyadicSet ∩ ball x R) : ℝ≥0∞)
        ≤ (((N + 3 : ℕ) : ℕ∞) : ℝ≥0∞) :=
          ENat.toENNReal_le.2 (externalCoveringNumber_dyadicSet_le hr)
      _ = ENNReal.ofReal ((N : ℝ) + 3) := by
          rw [show ((N : ℝ) + 3) = ((N + 3 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
          norm_cast
      _ ≤ ENNReal.ofReal ((4 + 1 / ((s : ℝ) * Real.log 2)) * t ^ (s : ℝ)) :=
          ENNReal.ofReal_le_ofReal hfinal
      _ = ((4 + 1 / ((s : ℝ) * Real.log 2)).toNNReal : ℝ≥0) * ENNReal.ofReal (t ^ (s : ℝ)) := by
          rw [ENNReal.ofReal_mul (by linarith)]
          rfl

/-- A set containing the grid `{j / n : j ≤ n}` comes within `1 / n` of every point of `[0,1]`. -/
theorem infDist_le_of_grid_subset {n : ℕ} (hn : 1 ≤ n) {S : Set ℝ}
    (hS : ∀ j : ℕ, j ≤ n → (j : ℝ) / n ∈ S) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    Metric.infDist u S ≤ 1 / n := by
  obtain ⟨hu0, hu1⟩ := hu
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hjn : ⌊u * n⌋₊ ≤ n := by
    have h1 : u * n ≤ (n : ℝ) := by nlinarith
    simpa using Nat.floor_le_floor h1
  have hj1 : ((⌊u * n⌋₊ : ℕ) : ℝ) ≤ u * n := Nat.floor_le (by positivity)
  have hj2 : u * n < (⌊u * n⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one _
  have hlow : ((⌊u * n⌋₊ : ℕ) : ℝ) / n ≤ u := by rw [div_le_iff₀ hn0]; linarith
  have hup : u - ((⌊u * n⌋₊ : ℕ) : ℝ) / n ≤ 1 / n := by
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hn0]
    linarith
  calc Metric.infDist u S ≤ dist u (((⌊u * n⌋₊ : ℕ) : ℝ) / n) :=
        Metric.infDist_le_dist_of_mem (hS _ hjn)
    _ = |u - ((⌊u * n⌋₊ : ℕ) : ℝ) / n| := Real.dist_eq _ _
    _ ≤ 1 / n := by
        rw [abs_le]
        have hpos : (0 : ℝ) < 1 / n := by positivity
        exact ⟨by linarith, hup⟩

theorem isWeakTangent_blockMap_image : IsWeakTangent (Icc (0 : ℝ) 1) (blockMap '' dyadicSet) := by
  have hTapp : ∀ (c : ℝ) (hc : c ≠ 0) (z : ℝ), DilationEquiv.mulLeft c hc z = c * z :=
    fun _ _ _ => rfl
  have h0img : (0 : ℝ) ∈ blockMap '' dyadicSet := ⟨0, zero_mem_dyadicSet, blockMap_zero⟩
  refine ⟨isCompact_Icc, ⟨0, by norm_num⟩,
    fun n => DilationEquiv.mulLeft ((2 : ℝ) ^ ((n + 1) * (n + 1) + (n + 1))) (by positivity),
    Icc 0 1, isCompact_Icc, fun n => ?_, ?_⟩
  · exact ⟨0, ⟨⟨0, h0img, by rw [hTapp, mul_zero]⟩, by norm_num⟩⟩
  · refine squeeze_zero (fun n => Metric.hausdorffDist_nonneg) (fun n => ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    set n₁ : ℕ := n + 1 with hn₁def
    have hn₁ : 1 ≤ n₁ := by omega
    have hn₁R : (0 : ℝ) < (n₁ : ℝ) := by exact_mod_cast hn₁
    have hpow : ((2 : ℝ) ^ (n₁ * n₁ + n₁)) * (1 / 2 : ℝ) ^ (n₁ * n₁ + n₁) = 1 := by
      rw [← mul_pow]; norm_num
    refine Metric.hausdorffDist_le_of_infDist (by positivity) (fun z hz => ?_) (fun u hu => ?_)
    · calc Metric.infDist z (Icc (0 : ℝ) 1) ≤ dist z z := Metric.infDist_le_dist_of_mem hz.2
        _ = 0 := dist_self z
        _ ≤ 1 / ((n : ℝ) + 1) := by positivity
    · have hcast : ((n : ℝ) + 1) = (n₁ : ℝ) := by rw [hn₁def]; push_cast; ring
      rw [hcast]
      refine infDist_le_of_grid_subset hn₁ (fun j hj => ?_) hu
      have hgrid : blockMap (dyadicPoint (n₁ * n₁ + j))
          = (j : ℝ) / (n₁ : ℝ) * (1 / 2 : ℝ) ^ (n₁ * n₁ + n₁) := by
        rw [blockMap_dyadicPoint, blockValue_grid hn₁ hj]
      refine ⟨⟨blockMap (dyadicPoint (n₁ * n₁ + j)),
        ⟨_, dyadicPoint_mem_dyadicSet _, rfl⟩, ?_⟩, ?_, ?_⟩
      · rw [hTapp, hgrid, ← mul_assoc, mul_comm ((2 : ℝ) ^ (n₁ * n₁ + n₁)), mul_assoc, hpow,
          mul_one]
      · positivity
      · rw [div_le_one hn₁R]
        exact_mod_cast hj

/-- Example 5.10 (`ex:lipschitz-assouad-increase`): a Lipschitz map on a compact subset of the line
that increases the Assouad dimension from zero to one. -/
theorem lipschitz_assouad_increase :
    ∃ (E : Set ℝ) (f : ℝ → ℝ) (L : ℝ≥0), IsCompact E ∧ LipschitzOnWith L f E ∧
      assouadDim E = 0 ∧ assouadDim (f '' E) = 1 := by
  refine ⟨dyadicSet, blockMap, 2, isCompact_dyadicSet, lipschitzOnWith_blockMap,
    assouadDim_dyadicSet, le_antisymm ?_ ?_⟩
  · simpa using assouadDim_le_finrank (blockMap '' dyadicSet)
  · have himg : IsCompact (blockMap '' dyadicSet) :=
      isCompact_dyadicSet.image_of_continuousOn lipschitzOnWith_blockMap.continuousOn
    calc (1 : ℝ≥0∞) = assouadDim (Icc (0 : ℝ) 1) := (assouadDim_Icc (by norm_num)).symm
      _ ≤ assouadDim (blockMap '' dyadicSet) :=
          weak_tangent_bound isWeakTangent_blockMap_image

end GeometricMeasureTheory
