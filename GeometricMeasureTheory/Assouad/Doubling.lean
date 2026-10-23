/-
# Section 5.2: Doubling spaces

A metric space is doubling if every ball can be covered by a bounded number of balls of half the
radius. This is exactly finiteness of the Assouad dimension. The balls of Definition 5.3 are balls
of the metric space `E`, so the covering balls are centred in `E` and the count is
`Metric.coveringNumber` rather than `Metric.externalCoveringNumber`, whose centres are ambient.

Mathlib's `IsUnifLocDoublingMeasure` is a doubling condition on measures at small scales, which is
a different notion; the measure version of the notes is `IsDoublingMeasure` in
`GeometricMeasureTheory.Assouad.MeasureDimensions`.

| Notes | Lean declaration | Location |
|---|---|---|
| Definition 5.3 (doubling space) | `IsDoublingSet` | here |
| Theorem 5.4 (doubling is finite Assouad dimension) | `doubling_assouad` | here |
| Finite Assouad dimension is doubling | `IsDoublingSet.of_assouadDim_ne_top` | here |
| Doubling gives a finite exponent | `assouadDim_ne_top_of_coveringNumber_le` | here |
| Subsets of Euclidean space are doubling | `isDoublingSet_of_finiteDimensional` | here |
-/
import GeometricMeasureTheory.Assouad.Basic

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

variable {X : Type*} [MetricSpace X]

/-- Definition 5.3 (`def:doubling-space`): `E` is doubling if there is an integer `D` such that
every ball of radius `R` centred in `E` can be covered by at most `D` balls of radius `R/2` with
centres in `E`. -/
def IsDoublingSet (E : Set X) : Prop :=
  ∃ D : ℕ, ∀ x ∈ E, ∀ R : ℝ, 0 < R →
    Metric.coveringNumber (R / 2).toNNReal (E ∩ ball x R) ≤ D

/-! ## Finite Assouad dimension is doubling

Halving the radius is the two-scale bound at `r = R / 4`, where the ratio `R / r` is the constant
`4`; the spare factor of two moves the centres of the cover into the set. -/

/-- A set of finite Assouad dimension is doubling. -/
theorem IsDoublingSet.of_assouadDim_ne_top {E : Set X} (h : assouadDim E ≠ ⊤) :
    IsDoublingSet E := by
  have hex : ∃ s : ℝ≥0, AssouadDimLE E (s : ℝ) := by
    by_contra hcon
    simp only [not_exists] at hcon
    exact h (by simp [assouadDim, hcon])
  obtain ⟨s, C, hC1, hC⟩ := hex
  refine ⟨⌈(C : ℝ) * 4 ^ (s : ℝ)⌉₊, fun x hx R hR => ?_⟩
  have hbound := hC x hx (R / 4) R (by linarith) (by linarith)
  have hratio : R / (R / 4) = 4 := by field_simp
  rw [hratio] at hbound
  have hrad : (2 : ℝ≥0) * (R / 4).toNNReal = (R / 2).toNNReal := by
    refine NNReal.coe_injective ?_
    push_cast [Real.coe_toNNReal _ (by linarith : (0 : ℝ) ≤ R / 4),
      Real.coe_toNNReal _ (by linarith : (0 : ℝ) ≤ R / 2)]
    ring
  have hcov : Metric.coveringNumber (R / 2).toNNReal (E ∩ ball x R)
      ≤ Metric.externalCoveringNumber (R / 4).toNNReal (E ∩ ball x R) := by
    rw [← hrad]
    exact Metric.coveringNumber_two_mul_le_externalCoveringNumber _ _
  refine hcov.trans ?_
  have hfinal : (Metric.externalCoveringNumber (R / 4).toNNReal (E ∩ ball x R) : ℝ≥0∞)
      ≤ ((⌈(C : ℝ) * 4 ^ (s : ℝ)⌉₊ : ℕ) : ℝ≥0∞) := by
    refine hbound.trans ?_
    calc (C : ℝ≥0∞) * ENNReal.ofReal (4 ^ (s : ℝ))
        = ENNReal.ofReal ((C : ℝ) * 4 ^ (s : ℝ)) := by
          rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal]
      _ ≤ ENNReal.ofReal ((⌈(C : ℝ) * 4 ^ (s : ℝ)⌉₊ : ℕ) : ℝ) :=
          ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
      _ = ((⌈(C : ℝ) * 4 ^ (s : ℝ)⌉₊ : ℕ) : ℝ≥0∞) := ENNReal.ofReal_natCast _
  exact_mod_cast hfinal

/-! ## Iterating the halving

Since the covering balls are centred in `E`, the doubling bound applies again at the smaller scale.
Covering `E ∩ B(z, 3ρ/2)` by `D` balls of radius `3ρ/4` centred in `E` shrinks the radius by the
factor `3/4` at each step, and `n` steps cost `D^n` balls. -/

/-- One halving step with centres in the set: `E ∩ closedBall z ρ` is covered by `D` balls of
radius `3ρ/4` centred in `E`. -/
private theorem exists_finsetCover_step {E : Set X} {D : ℕ}
    (h : ∀ x ∈ E, ∀ R : ℝ, 0 < R →
      Metric.coveringNumber (R / 2).toNNReal (E ∩ ball x R) ≤ D)
    {z : X} (hz : z ∈ E) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : Finset X, ↑C ⊆ E ∧ C.card ≤ D ∧
      Metric.IsCover (3 / 4 * ρ).toNNReal (E ∩ closedBall z ρ) ↑C := by
  have hcov := h z hz (3 / 2 * ρ) (by linarith)
  have hrad : (3 / 2 * ρ / 2 : ℝ) = 3 / 4 * ρ := by ring
  rw [hrad] at hcov
  have hne : Metric.coveringNumber (3 / 4 * ρ).toNNReal (E ∩ ball z (3 / 2 * ρ)) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hcov
  obtain ⟨C, hCsub, hCfin, hCcover, hCcard⟩ := Metric.exists_set_encard_eq_coveringNumber hne
  refine ⟨hCfin.toFinset, ?_, ?_, ?_⟩
  · rw [hCfin.coe_toFinset]
    exact hCsub.trans Set.inter_subset_left
  · have hcard : (hCfin.toFinset.card : ℕ∞) ≤ (D : ℕ∞) := by
      rw [← hCfin.encard_eq_coe_toFinset_card, hCcard]
      exact hcov
    exact_mod_cast hcard
  · rw [hCfin.coe_toFinset]
    exact hCcover.anti
      (Set.inter_subset_inter_right E (closedBall_subset_ball (by linarith)))

/-- Iterating the halving step `n` times covers `E ∩ closedBall z ρ` by `D^n` balls of radius
`(3/4)^n ρ` centred in `E`. -/
private theorem exists_finsetCover_iterate {E : Set X} {D : ℕ}
    (h : ∀ x ∈ E, ∀ R : ℝ, 0 < R →
      Metric.coveringNumber (R / 2).toNNReal (E ∩ ball x R) ≤ D)
    {z : X} (hz : z ∈ E) {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    ∃ C : Finset X, ↑C ⊆ E ∧ C.card ≤ D ^ n ∧
      Metric.IsCover ((3 / 4 : ℝ) ^ n * ρ).toNNReal (E ∩ closedBall z ρ) ↑C := by
  classical
  induction n with
  | zero =>
      refine ⟨{z}, by simpa using hz, by simp, fun w hw => ⟨z, by simp, ?_⟩⟩
      show edist w z ≤ ((((3 / 4 : ℝ) ^ 0 * ρ).toNNReal : ℝ≥0) : ℝ≥0∞)
      rw [edist_dist]
      refine ENNReal.ofReal_le_ofReal ?_
      simpa using hw.2
  | succ n ih =>
      obtain ⟨C, hCE, hCcard, hCcover⟩ := ih
      have hρn : (0 : ℝ) < (3 / 4 : ℝ) ^ n * ρ := by positivity
      have hchoice : ∀ c ∈ C, ∃ Cc : Finset X, ↑Cc ⊆ E ∧ Cc.card ≤ D ∧
          Metric.IsCover (3 / 4 * ((3 / 4 : ℝ) ^ n * ρ)).toNNReal
            (E ∩ closedBall c ((3 / 4 : ℝ) ^ n * ρ)) ↑Cc :=
        fun c hc => exists_finsetCover_step h (hCE (Finset.mem_coe.2 hc)) hρn
      choose! g hg1 hg2 hg3 using hchoice
      refine ⟨C.biUnion g, ?_, ?_, fun w hw => ?_⟩
      · intro u hu
        simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, exists_prop] at hu
        obtain ⟨c, hc, huc⟩ := hu
        exact hg1 c hc huc
      · calc (C.biUnion g).card ≤ ∑ c ∈ C, (g c).card := Finset.card_biUnion_le
          _ ≤ ∑ _c ∈ C, D := Finset.sum_le_sum fun c hc => hg2 c hc
          _ = C.card * D := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ D ^ n * D := Nat.mul_le_mul_right D hCcard
          _ = D ^ (n + 1) := by ring
      · obtain ⟨c, hc, hwc⟩ := hCcover hw
        have hwc' : dist w c ≤ (3 / 4 : ℝ) ^ n * ρ := by
          have hle : edist w c ≤ ENNReal.ofReal ((3 / 4 : ℝ) ^ n * ρ) := hwc
          rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff hρn.le] at hle
        obtain ⟨c', hc', hwc''⟩ :=
          hg3 c (Finset.mem_coe.1 hc) ⟨hw.1, mem_closedBall.2 hwc'⟩
        refine ⟨c', ?_, ?_⟩
        · simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, exists_prop]
          exact ⟨c, Finset.mem_coe.1 hc, hc'⟩
        · have heq : (3 / 4 : ℝ) ^ (n + 1) * ρ = 3 / 4 * ((3 / 4 : ℝ) ^ n * ρ) := by ring
          rw [heq]
          exact hwc''

/-- The substantive half of Theorem 5.4 (`thm:doubling-assouad`): if every ball of radius `R`
centred in `E` is covered by `D` balls of radius `R/2` with centres in `E`, then the Assouad
dimension of `E` is finite, with exponent `log D / log (4/3)`. -/
theorem assouadDim_ne_top_of_coveringNumber_le {E : Set X} {D : ℕ}
    (h : ∀ x ∈ E, ∀ R : ℝ, 0 < R →
      Metric.coveringNumber (R / 2).toNNReal (E ∩ ball x R) ≤ D) :
    assouadDim E ≠ ⊤ := by
  classical
  rcases E.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · rw [assouadDim_empty]
    simp
  have hD1 : 1 ≤ D := by
    have hpos : 0 < Metric.coveringNumber ((1 : ℝ) / 2).toNNReal (E ∩ ball x₀ 1) :=
      Metric.coveringNumber_pos_iff.2 ⟨x₀, hx₀, mem_ball_self one_pos⟩
    have hlt : (0 : ℕ∞) < (D : ℕ∞) := hpos.trans_le (h x₀ hx₀ 1 one_pos)
    have hD : 0 < D := by exact_mod_cast hlt
    omega
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD1
  have hD1R : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
  set s : ℝ := Real.logb (4 / 3) D with hsdef
  have hs0 : 0 ≤ s := Real.logb_nonneg (by norm_num) hD1R
  have hDs : ((4 : ℝ) / 3) ^ s = (D : ℝ) := Real.rpow_logb (by norm_num) (by norm_num) hDR
  have hAssouad : AssouadDimLE E ((s.toNNReal : ℝ≥0) : ℝ) := by
    rw [Real.coe_toNNReal s hs0]
    refine ⟨max 1 (D : ℝ≥0), le_max_left _ _, fun x hx r R hr hrR => ?_⟩
    have hR : 0 < R := hr.trans hrR
    have hex : ∃ n : ℕ, (3 / 4 : ℝ) ^ n * R ≤ r := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < r / R by positivity)
        (show (3 : ℝ) / 4 < 1 by norm_num)
      exact ⟨n, ((lt_div_iff₀ hR).1 hn).le⟩
    have hn : (3 / 4 : ℝ) ^ Nat.find hex * R ≤ r := Nat.find_spec hex
    have hρn : (0 : ℝ) < (3 / 4 : ℝ) ^ Nat.find hex * R := by positivity
    obtain ⟨C, hCE, hCcard, hCcover⟩ := exists_finsetCover_iterate h hx hR (Nat.find hex)
    have hcount : Metric.externalCoveringNumber r.toNNReal (E ∩ ball x R)
        ≤ ((D ^ Nat.find hex : ℕ) : ℕ∞) := by
      calc Metric.externalCoveringNumber r.toNNReal (E ∩ ball x R)
          ≤ Metric.externalCoveringNumber ((3 / 4 : ℝ) ^ Nat.find hex * R).toNNReal
              (E ∩ ball x R) :=
            Metric.externalCoveringNumber_anti ((Real.toNNReal_le_toNNReal_iff hr.le).2 hn)
        _ ≤ Metric.externalCoveringNumber ((3 / 4 : ℝ) ^ Nat.find hex * R).toNNReal
              (E ∩ closedBall x R) :=
            Metric.externalCoveringNumber_mono_set
              (Set.inter_subset_inter_right E ball_subset_closedBall)
        _ ≤ (C : Set X).encard := hCcover.externalCoveringNumber_le_encard
        _ = (C.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard C
        _ ≤ ((D ^ Nat.find hex : ℕ) : ℕ∞) := by exact_mod_cast hCcard
    have hRr : 1 ≤ R / r := (one_le_div hr).2 hrR.le
    have hreal : (D : ℝ) ^ Nat.find hex ≤ (D : ℝ) * (R / r) ^ s := by
      have hpow : (1 : ℝ) ≤ (R / r) ^ s := Real.one_le_rpow hRr hs0
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
      · rw [h0, pow_zero]
        nlinarith
      · obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
        have hmin : ¬((3 / 4 : ℝ) ^ m * R ≤ r) := Nat.find_min hex (by omega)
        rw [not_le] at hmin
        have hinv : ((4 : ℝ) / 3) ^ m * ((3 : ℝ) / 4) ^ m = 1 := by
          rw [← mul_pow]
          norm_num
        have hfrac : ((4 : ℝ) / 3) ^ m ≤ R / r := by
          rw [le_div_iff₀ hr]
          nlinarith [pow_pos (show (0 : ℝ) < 4 / 3 by norm_num) m, hmin.le]
        have hswap : (((4 : ℝ) / 3) ^ s) ^ m = (((4 : ℝ) / 3) ^ m) ^ s := by
          rw [← Real.rpow_natCast (((4 : ℝ) / 3) ^ s) m,
            ← Real.rpow_natCast ((4 : ℝ) / 3) m,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4 / 3),
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4 / 3), mul_comm s (m : ℝ)]
        calc (D : ℝ) ^ Nat.find hex = (D : ℝ) * (D : ℝ) ^ m := by rw [hm]; ring
          _ = (D : ℝ) * (((4 : ℝ) / 3) ^ s) ^ m := by rw [hDs]
          _ = (D : ℝ) * (((4 : ℝ) / 3) ^ m) ^ s := by rw [hswap]
          _ ≤ (D : ℝ) * (R / r) ^ s :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow (by positivity) hfrac hs0) hDR.le
    have hcast : ((D ^ Nat.find hex : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((D : ℝ) ^ Nat.find hex) := by
      rw [← ENNReal.ofReal_natCast]
      push_cast
      ring_nf
    calc (Metric.externalCoveringNumber r.toNNReal (E ∩ ball x R) : ℝ≥0∞)
        ≤ ((D ^ Nat.find hex : ℕ) : ℝ≥0∞) := by exact_mod_cast hcount
      _ = ENNReal.ofReal ((D : ℝ) ^ Nat.find hex) := hcast
      _ ≤ ENNReal.ofReal ((D : ℝ) * (R / r) ^ s) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (D : ℝ) * ENNReal.ofReal ((R / r) ^ s) :=
          ENNReal.ofReal_mul hDR.le
      _ ≤ ((max 1 (D : ℝ≥0) : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal ((R / r) ^ s) := by
          gcongr
          rw [show ENNReal.ofReal (D : ℝ) = (((D : ℝ≥0) : ℝ≥0) : ℝ≥0∞) by
            rw [← ENNReal.ofReal_coe_nnreal]; norm_num]
          exact_mod_cast le_max_right 1 (D : ℝ≥0)
  have hle : assouadDim E ≤ ((s.toNNReal : ℝ≥0) : ℝ≥0∞) := by
    rw [assouadDim]
    exact iInf₂_le (f := fun (t : ℝ≥0) (_ : AssouadDimLE E (t : ℝ)) => (t : ℝ≥0∞))
      s.toNNReal hAssouad
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top hle

/-- Theorem 5.4 (`thm:doubling-assouad`): a set is doubling if and only if its Assouad dimension is
finite. The covering balls are centred in the set, as are the balls of the metric space `E` in
Definition 5.3. -/
theorem doubling_assouad (E : Set X) : IsDoublingSet E ↔ assouadDim E ≠ ⊤ := by
  constructor
  · rintro ⟨D, hD⟩
    exact assouadDim_ne_top_of_coveringNumber_le hD
  · exact IsDoublingSet.of_assouadDim_ne_top

/-- Every subset of a finite-dimensional real normed space is doubling. -/
theorem isDoublingSet_of_finiteDimensional {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (E : Set V) : IsDoublingSet E :=
  IsDoublingSet.of_assouadDim_ne_top
    (ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (assouadDim_le_finrank E))

end GeometricMeasureTheory
