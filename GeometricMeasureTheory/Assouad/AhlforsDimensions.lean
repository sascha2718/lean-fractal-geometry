/-
# Section 5.4: Dimensions of Ahlfors regular sets

On a compact Ahlfors regular set all the dimensions of Block I agree.

| Notes | Lean declaration | Location |
|---|---|---|
| Theorem 5.12 (dimensions of Ahlfors regular sets) | `ahlfors_dimensions` | here |
| The two-scale bound in the proof of Theorem 5.12 | `assouadDimLE_of_isAhlforsRegular` | here |
| The matching lower counting bound | `le_externalCoveringNumber_of_isAhlforsRegular` | here |
-/
import GeometricMeasureTheory.Assouad.WeakTangents
import GeometricMeasureTheory.Covering.AhlforsRegular

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-! ### Counting tools -/

/-- A bound below every member of a family of extended natural numbers descends to the infimum of
the family, after the coercion to `ℝ≥0∞`. -/
theorem le_toENNReal_iInf {ι : Sort*} {f : ι → ℕ∞} {b : ℝ≥0∞} (h : ∀ i, b ≤ (f i : ℝ≥0∞)) :
    b ≤ ((⨅ i, f i : ℕ∞) : ℝ≥0∞) := by
  rcases eq_or_ne (⨅ i, f i) ⊤ with htop | htop
  · simp [htop]
  · obtain ⟨i, hi⟩ := iInf_lt_iff.1 ((ENat.lt_add_one_iff htop).2 (le_refl (⨅ i, f i)))
    exact (h i).trans (ENat.toENNReal_mono ((ENat.lt_add_one_iff htop).1 hi))

/-- Powers of non-negative reals multiply under `ENNReal.ofReal`. -/
theorem ofReal_rpow_mul_ofReal_rpow {a b p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) :
    ENNReal.ofReal a ^ p * ENNReal.ofReal b ^ p = ENNReal.ofReal (a * b) ^ p := by
  rw [← ENNReal.mul_rpow_of_nonneg _ _ hp, ← ENNReal.ofReal_mul ha]

omit [MetricSpace X] [BorelSpace X] in
/-- Counting by mass: if the sets `B y` for `y ∈ S` are pairwise disjoint measurable subsets of a
set `A` of finite measure, each of mass at least `m / K`, then `S` has at most `K μ(A) / m`
elements. -/
theorem encard_mul_le_measure_of_pairwiseDisjoint {μ : Measure X} {S A : Set X} {B : X → Set X}
    {m K : ℝ≥0∞} (hm : m ≠ 0) (hK : K ≠ ∞) (hA : μ A ≠ ∞)
    (hmeas : ∀ y ∈ S, MeasurableSet (B y)) (hdisj : S.PairwiseDisjoint B)
    (hsub : ∀ y ∈ S, B y ⊆ A) (hle : ∀ y ∈ S, m ≤ K * μ (B y)) :
    (S.encard : ℝ≥0∞) * m ≤ K * μ A := by
  have hKA : K * μ A ≠ ∞ := ENNReal.mul_ne_top hK hA
  have key : ∀ T : Finset X, ↑T ⊆ S → (T.card : ℝ≥0∞) * m ≤ K * μ A := by
    intro T hT
    calc (T.card : ℝ≥0∞) * m
        = ∑ _y ∈ T, m := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ y ∈ T, K * μ (B y) := Finset.sum_le_sum fun y hy => hle y (hT hy)
      _ = K * μ (⋃ y ∈ T, B y) := by
          rw [measure_biUnion_finset (hdisj.subset hT) fun y hy => hmeas y (hT hy), Finset.mul_sum]
      _ ≤ K * μ A :=
          mul_le_mul_right (measure_mono (iUnion₂_subset fun y hy => hsub y (hT hy))) _
  rcases S.finite_or_infinite with hfin | hinf
  · rw [hfin.encard_eq_coe_toFinset_card, ENat.toENNReal_coe]
    exact key hfin.toFinset (by simp)
  · obtain ⟨n, hn⟩ :=
      ENNReal.exists_nat_gt (r := K * μ A / m) (by simp [ENNReal.div_eq_top, hm, hKA])
    obtain ⟨T, hTS, hTcard⟩ := hinf.exists_subset_card_eq n
    have h1 := key T hTS
    rw [hTcard] at h1
    exact absurd h1 (not_le.2 ((ENNReal.div_lt_iff (Or.inl hm) (Or.inr hKA)).1 hn))

/-! ### The two-scale bounds -/

/-- The two-scale counting bound in the proof of Theorem 5.12 (`thm:ahlfors-dimensions`): a compact
Ahlfors `s`-regular set satisfies `N_r(E ∩ B(x, R)) ≤ C' (R/r)^s` at every pair of scales, so its
Assouad dimension is at most `s`. -/
theorem assouadDimLE_of_isAhlforsRegular {μ : Measure X} {s : ℝ} {E : Set X} {C : ℝ≥0}
    (hμ : IsAhlforsRegular μ s E C) (hE : IsCompact E) : AssouadDimLE E s := by
  have hs : 0 < s := hμ.pos
  have hC1 : (1 : ℝ≥0∞) ≤ C := by exact_mod_cast hμ.one_le
  have hpow_pos : ∀ t : ℝ, 0 < t → ENNReal.ofReal t ^ s ≠ 0 := fun t ht =>
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 ht) ENNReal.ofReal_ne_top).ne'
  have hpow_top : ∀ t : ℝ, ENNReal.ofReal t ^ s ≠ ∞ := fun _ =>
    (ENNReal.rpow_lt_top_of_nonneg hs.le ENNReal.ofReal_ne_top).ne
  have hEb : Bornology.IsBounded E := hE.isBounded
  set d : ℝ := Metric.diam E with hddef
  have hd0 : 0 < d := Metric.diam_pos hμ.nontrivial hEb
  have hediam : ediam E = ENNReal.ofReal d := (ENNReal.ofReal_toReal hEb.ediam_ne_top).symm
  have hμE : μ E ≠ ∞ := (hμ.measure_lt_top_of_isCompact hE).ne
  have hμle : ∀ A : Set X, μ A ≤ μ E := fun A =>
    (measure_mono (subset_univ _)).trans_eq (by rw [← hμ.measure_inter univ, univ_inter])
  have hμfin : ∀ A : Set X, μ A ≠ ∞ := fun A => ne_top_of_le_ne_top hμE (hμle A)
  set K : ℝ≥0∞ := max 1 (max ((C : ℝ≥0∞) * C * 4 ^ s)
    ((C : ℝ≥0∞) * μ E * (ENNReal.ofReal (d / 4) ^ s)⁻¹)) with hKdef
  have h4top : (4 : ℝ≥0∞) ^ s ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg hs.le (by simp)).ne
  have hKtop : K ≠ ∞ := by
    refine (max_lt ENNReal.one_lt_top (max_lt ?_ ?_)).ne
    · exact ENNReal.mul_lt_top
        (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top) h4top.lt_top
    · exact (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hμE)
        (ENNReal.inv_ne_top.2 (hpow_pos _ (by linarith)))).lt_top
  refine ⟨K.toNNReal, ?_, ?_⟩
  · rw [← ENNReal.coe_le_coe, ENNReal.coe_one, ENNReal.coe_toNNReal hKtop]
    exact le_max_left _ _
  intro x hx r R hr hrR
  rw [ENNReal.coe_toNNReal hKtop]
  have hR : 0 < R := hr.trans hrR
  have hX1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((R / r) ^ s) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow ((one_le_div hr).2 hrR.le) hs.le)
  by_cases hdr : d ≤ r
  · -- The set is smaller than the resolving scale, so a single ball covers it.
    have h1 : Metric.externalCoveringNumber r.toNNReal (E ∩ ball x R) ≤ 1 := by
      refine Metric.externalCoveringNumber_le_one_of_ediam_le ?_
      calc ediam (E ∩ ball x R) ≤ ediam E := ediam_mono inter_subset_left
        _ = ENNReal.ofReal d := hediam
        _ ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal hdr
        _ = (r.toNNReal : ℝ≥0∞) := rfl
    calc ((Metric.externalCoveringNumber r.toNNReal (E ∩ ball x R) : ℕ∞) : ℝ≥0∞)
        ≤ ((1 : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_mono h1
      _ = 1 := ENat.toENNReal_one
      _ ≤ K * 1 := by rw [mul_one]; exact le_max_left _ _
      _ ≤ K * ENNReal.ofReal ((R / r) ^ s) := mul_le_mul_right hX1 _
  replace hdr : r < d := not_le.1 hdr
  have hrne : r ≠ 0 := hr.ne'
  have hr2 : 0 < r / 2 := by linarith
  -- A maximal `r`-separated family in `E ∩ B(x, R)` covers it, and its `r/2`-balls are disjoint.
  set A := E ∩ ball x R with hAdef
  set ε : ℝ≥0 := r.toNNReal with hεdef
  have hεc : (ε : ℝ≥0∞) = ENNReal.ofReal r := by rw [hεdef]; rfl
  have hε0 : ε ≠ 0 := by
    simp only [hεdef, ne_eq, Real.toNNReal_eq_zero, not_le]
    exact hr
  have hTB : TotallyBounded A := hE.totallyBounded.subset inter_subset_left
  have hpack : Metric.packingNumber ε A ≠ ⊤ := by
    obtain ⟨N, -, hNfin, hNcov⟩ :=
      Metric.exists_finite_isCover_of_totallyBounded (ε := ε / 2) (by simpa using hε0) hTB
    have h2 : (2 : ℝ≥0) * (ε / 2) = ε := by field_simp
    refine ne_top_of_le_ne_top ?_
      (h2 ▸ Metric.packingNumber_two_mul_le_externalCoveringNumber (ε / 2) A)
    exact ne_top_of_le_ne_top hNfin.encard_lt_top.ne hNcov.externalCoveringNumber_le_encard
  set S := Metric.maximalSeparatedSet ε A with hSdef
  have hScov : Metric.externalCoveringNumber ε A ≤ S.encard :=
    (Metric.isCover_maximalSeparatedSet hpack).externalCoveringNumber_le_encard
  have hSA : S ⊆ A := Metric.maximalSeparatedSet_subset
  have hSsep : Metric.IsSeparated (ε : ℝ≥0∞) S := Metric.isSeparated_maximalSeparatedSet
  have hdisj : S.PairwiseDisjoint fun y => ball y (r / 2) := by
    intro y hy z hz hyz
    have h := hSsep hy hz hyz
    rw [hεc, edist_dist, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr.le] at h
    exact Metric.ball_disjoint_ball (by linarith)
  have hballs : ∀ y ∈ S, ENNReal.ofReal (r / 2) ^ s ≤ C * μ (ball y (r / 2)) := fun y hy =>
    hμ.le_measure_ball y (hSA hy).1 (r / 2) hr2
      (by rw [hediam]; exact ENNReal.ofReal_le_ofReal (by linarith))
  have hsub : ∀ y ∈ S, ball y (r / 2) ⊆ ball x (2 * R) := by
    intro y hy z hz
    have h1 : dist y x < R := mem_ball.1 (hSA hy).2
    have h2 : dist z y < r / 2 := mem_ball.1 hz
    have h3 : dist z x ≤ dist z y + dist y x := dist_triangle z y x
    exact mem_ball.2 (by linarith)
  have hcount : (S.encard : ℝ≥0∞) * ENNReal.ofReal (r / 2) ^ s ≤ C * μ (ball x (2 * R)) :=
    encard_mul_le_measure_of_pairwiseDisjoint (hpow_pos _ hr2) ENNReal.coe_ne_top (hμfin _)
      (fun _ _ => measurableSet_ball) hdisj hsub hballs
  have hmX : ENNReal.ofReal ((R / r) ^ s) * ENNReal.ofReal (r / 2) ^ s
      = ENNReal.ofReal (R / 2) ^ s := by
    have hrr : R / r * (r / 2) = R / 2 := by field_simp
    rw [← ENNReal.ofReal_rpow_of_pos (show (0 : ℝ) < R / r by positivity),
      ofReal_rpow_mul_ofReal_rpow (by positivity) hs.le, hrr]
  rw [← ENNReal.mul_le_mul_iff_left (hpow_pos _ hr2) (hpow_top _), mul_assoc, hmX]
  calc ((Metric.externalCoveringNumber ε A : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (r / 2) ^ s
      ≤ (S.encard : ℝ≥0∞) * ENNReal.ofReal (r / 2) ^ s :=
        mul_le_mul_left (ENat.toENNReal_mono hScov) _
    _ ≤ C * μ (ball x (2 * R)) := hcount
    _ ≤ K * ENNReal.ofReal (R / 2) ^ s := by
        by_cases h2R : 2 * R ≤ d
        · -- Below the diameter, the upper mass bound applies to `B(x, 2R)`.
          have hup : μ (ball x (2 * R)) ≤ C * ENNReal.ofReal (2 * R) ^ s :=
            hμ.measure_ball_le x hx (2 * R) (by linarith)
              (by rw [hediam]; exact ENNReal.ofReal_le_ofReal h2R)
          have h4 : ENNReal.ofReal (2 * R) ^ s = 4 ^ s * ENNReal.ofReal (R / 2) ^ s := by
            rw [show (2 * R : ℝ) = 4 * (R / 2) by ring,
              ← ofReal_rpow_mul_ofReal_rpow (by norm_num) hs.le, ENNReal.ofReal_ofNat]
          calc (C : ℝ≥0∞) * μ (ball x (2 * R))
              ≤ C * (C * ENNReal.ofReal (2 * R) ^ s) := mul_le_mul_right hup _
            _ = (C : ℝ≥0∞) * C * 4 ^ s * ENNReal.ofReal (R / 2) ^ s := by rw [h4]; ring
            _ ≤ K * ENNReal.ofReal (R / 2) ^ s :=
                mul_le_mul_left (le_max_of_le_right (le_max_left _ _)) _
        · -- Above the diameter, the total mass of `E` bounds the count.
          replace h2R : d < 2 * R := not_le.1 h2R
          calc (C : ℝ≥0∞) * μ (ball x (2 * R)) ≤ C * μ E := mul_le_mul_right (hμle _) _
            _ = (C : ℝ≥0∞) * μ E * (ENNReal.ofReal (d / 4) ^ s)⁻¹
                  * ENNReal.ofReal (d / 4) ^ s := by
                rw [mul_assoc, ENNReal.inv_mul_cancel (hpow_pos _ (by linarith)) (hpow_top _),
                  mul_one]
            _ ≤ K * ENNReal.ofReal (R / 2) ^ s :=
                mul_le_mul' (le_max_of_le_right (le_max_right _ _))
                  (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (by linarith)) hs.le)

/-! ### Theorem 5.12 -/

/-- Theorem 5.12 (`thm:ahlfors-dimensions`): on a compact Ahlfors `s`-regular set the Hausdorff,
packing, box and Assouad dimensions all equal `s`. -/
theorem ahlfors_dimensions {μ : Measure X} {s : ℝ} {E : Set X} {C : ℝ≥0}
    (hμ : IsAhlforsRegular μ s E C) (hE : IsCompact E) :
    dimH E = ENNReal.ofReal s ∧ packingDim E = ENNReal.ofReal s ∧
      lowerBoxDim E = ENNReal.ofReal s ∧ upperBoxDim E = ENNReal.ofReal s ∧
      assouadDim E = ENNReal.ofReal s := by
  obtain ⟨-, -, -, hdimH, -⟩ := ahlfors_hausdorff hμ hE
  have hEb : Bornology.IsBounded E := hE.isBounded
  have hEne : E.Nonempty := hμ.nontrivial.nonempty
  -- The Assouad dimension is at most `s`, by the two-scale bound.
  have hassouad : assouadDim E ≤ ENNReal.ofReal s := by
    refine iInf_le_of_le s.toNNReal (iInf_le_of_le ?_ le_rfl)
    rw [Real.coe_toNNReal s hμ.pos.le]
    exact assouadDimLE_of_isAhlforsRegular hμ hE
  -- Every dimension in the chain is squeezed between the Hausdorff and the Assouad dimension.
  have hlow : ENNReal.ofReal s ≤ lowerBoxDim E := hdimH ▸ hausdorff_lower_box E
  have hupper : upperBoxDim E = ENNReal.ofReal s :=
    le_antisymm ((upperBoxDim_le_assouadDim hEb hEne).trans hassouad)
      (hlow.trans (lowerBoxDim_le_upperBoxDim E))
  refine ⟨hdimH, ?_, ?_, hupper, ?_⟩
  · exact le_antisymm (packingDim_le_upperBoxDim.trans_eq hupper)
      (hdimH ▸ dimH_le_packingDim E)
  · exact le_antisymm ((lowerBoxDim_le_upperBoxDim E).trans_eq hupper) hlow
  · exact le_antisymm hassouad (hupper ▸ upperBoxDim_le_assouadDim hEb hEne)

omit [BorelSpace X] in
/-- The counting bound from below on an Ahlfors regular set, stated after Theorem 5.12. The set
need not be compact: the argument only covers, moves centres into the set, and compares masses. -/
theorem le_externalCoveringNumber_of_isAhlforsRegular {μ : Measure X} {s : ℝ} {E : Set X}
    {C : ℝ≥0} (hμ : IsAhlforsRegular μ s E C) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ x ∈ E, ∀ r R : ℝ, 0 < r → r < R → ENNReal.ofReal R ≤ ediam E →
      c * ENNReal.ofReal ((R / r) ^ s) ≤
        (Metric.externalCoveringNumber r.toNNReal (E ∩ ball x R) : ℝ≥0∞) := by
  have hs : 0 < s := hμ.pos
  have hC1 : (1 : ℝ≥0∞) ≤ C := by exact_mod_cast hμ.one_le
  have hC0 : (C : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans_le hC1).ne'
  have hpow_pos : ∀ t : ℝ, 0 < t → ENNReal.ofReal t ^ s ≠ 0 := fun t ht =>
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 ht) ENNReal.ofReal_ne_top).ne'
  have hpow_top : ∀ t : ℝ, ENNReal.ofReal t ^ s ≠ ∞ := fun _ =>
    (ENNReal.rpow_lt_top_of_nonneg hs.le ENNReal.ofReal_ne_top).ne
  set Γ : ℝ≥0∞ := (C : ℝ≥0∞) * C * 3 ^ s with hΓdef
  have h3pos : (0 : ℝ≥0∞) < 3 ^ s := ENNReal.rpow_pos (by norm_num) (by simp)
  have h3top : (3 : ℝ≥0∞) ^ s ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg hs.le (by simp)).ne
  have hΓ0 : Γ ≠ 0 := mul_ne_zero (mul_ne_zero hC0 hC0) h3pos.ne'
  have hΓtop : Γ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) h3top
  have hCC : (1 : ℝ≥0∞) ≤ (C : ℝ≥0∞) * C := by
    calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
      _ ≤ (C : ℝ≥0∞) * C := mul_le_mul' hC1 hC1
  refine ⟨(Γ⁻¹).toNNReal, ENNReal.toNNReal_pos (by simp [hΓtop]) (by simp [hΓ0]), ?_⟩
  intro x hx r R hr hrR hRE
  rw [ENNReal.coe_toNNReal (by simp [hΓ0])]
  have hR : 0 < R := hr.trans hrR
  simp only [Metric.externalCoveringNumber]
  refine le_toENNReal_iInf fun Cov => le_toENNReal_iInf fun hCov => ?_
  rw [← ENNReal.mul_le_mul_iff_right hΓ0 hΓtop, ← mul_assoc, ENNReal.mul_inv_cancel hΓ0 hΓtop,
    one_mul]
  rcases Cov.finite_or_infinite with hfin | hinf
  swap
  · rw [hinf.encard_eq, ENat.toENNReal_top, ENNReal.mul_top hΓ0]
    exact le_top
  have hAne : (E ∩ ball x R).Nonempty := ⟨x, hx, mem_ball_self hR⟩
  have hone : (1 : ℝ≥0∞) ≤ (Cov.encard : ℝ≥0∞) := by
    rw [← ENat.toENNReal_one]
    exact ENat.toENNReal_mono (Set.one_le_encard_iff_nonempty.2 (hCov.nonempty hAne))
  by_cases h3r : ENNReal.ofReal (3 * r) ≤ ediam E
  · -- Move the centres of the cover into `E` and compare masses.
    have hpiece : ∀ z : X, μ (closedBall z r ∩ E) ≤ C * ENNReal.ofReal (3 * r) ^ s := by
      intro z
      rcases (closedBall z r ∩ E).eq_empty_or_nonempty with hz | ⟨w, hw1, hw2⟩
      · simp [hz]
      · refine (measure_mono ?_).trans (hμ.measure_ball_le w hw2 (3 * r) (by linarith) h3r)
        rintro v ⟨hv1, -⟩
        have h1 : dist v z ≤ r := mem_closedBall.1 hv1
        have h2 : dist w z ≤ r := mem_closedBall.1 hw1
        have h3 : dist v w ≤ dist v z + dist z w := dist_triangle v z w
        rw [dist_comm z w] at h3
        exact mem_ball.2 (by linarith)
    have hεr : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal r hr.le
    have hcover : E ∩ ball x R ⊆ ⋃ z ∈ hfin.toFinset, closedBall z r ∩ E := by
      intro v hv
      have h := hCov.subset_iUnion_closedBall hv
      rw [hεr] at h
      obtain ⟨z, hz, hvz⟩ := mem_iUnion₂.1 h
      exact mem_iUnion₂.2 ⟨z, by simpa using hz, hvz, hv.1⟩
    have hsum : μ (ball x R) ≤ (Cov.encard : ℝ≥0∞) * (C * ENNReal.ofReal (3 * r) ^ s) := by
      calc μ (ball x R) = μ (E ∩ ball x R) := by rw [inter_comm, hμ.measure_inter]
        _ ≤ ∑ z ∈ hfin.toFinset, μ (closedBall z r ∩ E) :=
            (measure_mono hcover).trans (measure_biUnion_finset_le _ _)
        _ ≤ ∑ _z ∈ hfin.toFinset, ((C : ℝ≥0∞) * ENNReal.ofReal (3 * r) ^ s) :=
            Finset.sum_le_sum fun z _ => hpiece z
        _ = (Cov.encard : ℝ≥0∞) * (C * ENNReal.ofReal (3 * r) ^ s) := by
            rw [Finset.sum_const, nsmul_eq_mul, hfin.encard_eq_coe_toFinset_card,
              ENat.toENNReal_coe]
    have h3pow : ENNReal.ofReal (3 * r) ^ s = 3 ^ s * ENNReal.ofReal r ^ s := by
      rw [← ofReal_rpow_mul_ofReal_rpow (by norm_num) hs.le, ENNReal.ofReal_ofNat]
    have hXr : ENNReal.ofReal ((R / r) ^ s) * ENNReal.ofReal r ^ s = ENNReal.ofReal R ^ s := by
      rw [← ENNReal.ofReal_rpow_of_pos (show (0 : ℝ) < R / r by positivity),
        ofReal_rpow_mul_ofReal_rpow (by positivity) hs.le, div_mul_cancel₀ _ hr.ne']
    rw [← ENNReal.mul_le_mul_iff_left (hpow_pos r hr) (hpow_top r), hXr]
    calc ENNReal.ofReal R ^ s ≤ C * μ (ball x R) := hμ.le_measure_ball x hx R hR hRE
      _ ≤ (C : ℝ≥0∞) * ((Cov.encard : ℝ≥0∞) * (C * ENNReal.ofReal (3 * r) ^ s)) :=
          mul_le_mul_right hsum _
      _ = Γ * (Cov.encard : ℝ≥0∞) * ENNReal.ofReal r ^ s := by rw [h3pow, hΓdef]; ring
  · -- At scales comparable with the diameter a single ball already gives the bound.
    replace h3r : ediam E < ENNReal.ofReal (3 * r) := not_le.1 h3r
    have hRr : R < 3 * r := by
      have h := hRE.trans_lt h3r
      rwa [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hR.le] at h
    have hle3 : (R / r) ^ s ≤ (3 : ℝ) ^ s :=
      Real.rpow_le_rpow (by positivity) (by rw [div_le_iff₀ hr]; linarith) hs.le
    calc ENNReal.ofReal ((R / r) ^ s) ≤ ENNReal.ofReal ((3 : ℝ) ^ s) :=
          ENNReal.ofReal_le_ofReal hle3
      _ = (3 : ℝ≥0∞) ^ s := by
          rw [← ENNReal.ofReal_rpow_of_pos (show (0 : ℝ) < 3 by norm_num), ENNReal.ofReal_ofNat]
      _ = 1 * 3 ^ s := (one_mul _).symm
      _ ≤ Γ * 1 := by rw [hΓdef, mul_one]; exact mul_le_mul_left hCC _
      _ ≤ Γ * (Cov.encard : ℝ≥0∞) := mul_le_mul_right hone _

end GeometricMeasureTheory

