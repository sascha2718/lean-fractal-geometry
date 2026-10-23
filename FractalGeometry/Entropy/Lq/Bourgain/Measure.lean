import Mathlib
import ExactOverlaps.Entropy.RepeatedUniformity
import FractalGeometry.Entropy.Lq.Bourgain.Tree
import FractalGeometry.Entropy.Lq.Statements

open MeasureTheory ProbabilityTheory Finset

open ExactOverlaps.Entropy ExactOverlaps.FiniteProbability

open scoped Pointwise ENNReal

namespace FractalGeometry

namespace Lq

namespace Bourgain

noncomputable def scaled (M : ℕ) (A : Finset ℤ) : Finset ℝ :=
  A.image fun x : ℤ => (x : ℝ) / 2 ^ M

theorem scaled_injective (M : ℕ) : Function.Injective fun x : ℤ => (x : ℝ) / 2 ^ M := by
  intro x y h
  have h2 : (2 : ℝ) ^ M ≠ 0 := by positivity
  simpa [div_left_inj' h2] using h

theorem card_scaled (M : ℕ) (A : Finset ℤ) : (scaled M A).card = A.card :=
  card_image_of_injective _ (scaled_injective M)

theorem scaled_nonempty {M : ℕ} {A : Finset ℤ} (hA : A.Nonempty) : (scaled M A).Nonempty :=
  hA.image _

noncomputable def unifLaw (M : ℕ) (A : Finset ℤ) (hA : A.Nonempty) : ProbabilityMeasure ℝ :=
  ⟨(PMF.uniformOfFinset (scaled M A) (scaled_nonempty hA)).toMeasure, inferInstance⟩

open scoped Classical in

theorem unifLaw_apply (M : ℕ) {A : Finset ℤ} (hA : A.Nonempty) {s : Set ℝ}
    (hs : MeasurableSet s) :
    (unifLaw M A hA : Measure ℝ) s = ((scaled M A).filter (· ∈ s)).card / A.card := by
  classical
  change (PMF.uniformOfFinset (scaled M A) (scaled_nonempty hA)).toMeasure s = _
  rw [PMF.toMeasure_uniformOfFinset_apply _ _ hs, card_scaled]

theorem unifLaw_compl (M : ℕ) {A : Finset ℤ} (hA : A.Nonempty) :
    (unifLaw M A hA : Measure ℝ) ((scaled M A : Set ℝ)ᶜ) = 0 := by
  classical
  rw [unifLaw_apply M hA (Finset.measurableSet _).compl]
  convert ENNReal.zero_div
  simp only [Set.mem_compl_iff, mem_coe, Nat.cast_eq_zero, card_eq_zero]
  exact filter_false_of_mem fun x hx h => h hx

theorem hasBoundedSupport_unifLaw {M : ℕ} {A : Finset ℤ} (hA : A.Nonempty)
    (hAM : InUnit M A) : HasBoundedSupport (unifLaw M A hA) := by
  refine ⟨0, 1, ?_⟩
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_) (unifLaw_compl M hA)
  intro hy'
  apply hy
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hy'
  have h2 : (0 : ℝ) < 2 ^ M := by positivity
  have hx' := hAM x hx
  refine ⟨div_nonneg (by exact_mod_cast hx'.1) h2.le, ?_⟩
  rw [div_le_one h2]
  exact_mod_cast hx'.2.le

theorem dyadicQuantize_scaled {M l : ℕ} (hl : l ≤ M) (x : ℤ) :
    dyadicQuantize (l : ℤ) ((x : ℝ) / 2 ^ M) = pre M l x := by
  unfold dyadicQuantize pre
  have h : (2 : ℝ) ^ (l : ℤ) * ((x : ℝ) / 2 ^ M) = (x : ℝ) / ((2 ^ (M - l) : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ^ M = 2 ^ l * 2 ^ (M - l) := by rw [← pow_add, Nat.add_sub_cancel' hl]
    rw [zpow_natCast, Nat.cast_pow, Nat.cast_ofNat, h2]
    field_simp
  rw [h, Int.floor_div_natCast, Int.floor_intCast]
  push_cast
  rfl

open scoped Classical in

theorem card_scaled_filter {M l : ℕ} (hl : l ≤ M) (A : Finset ℤ) (c : ℤ) :
    ((scaled M A).filter (· ∈ dyadicCell (l : ℤ) c)).card = (cellOf M l A c).card := by
  unfold scaled cellOf
  rw [filter_image, card_image_of_injective _ (scaled_injective M)]
  congr 1
  ext x
  simp only [mem_filter, dyadicCell, Set.mem_ofPred_eq, dyadicQuantize_scaled hl]

theorem unifLaw_cell {M l : ℕ} (hl : l ≤ M) {A : Finset ℤ} (hA : A.Nonempty) (c : ℤ) :
    (unifLaw M A hA : Measure ℝ) (dyadicCell (l : ℤ) c) = (cellOf M l A c).card / A.card := by
  classical
  rw [unifLaw_apply M hA (measurableSet_dyadicCell _ _), card_scaled_filter hl]

theorem rescaledComponent_cell (μ : ProbabilityMeasure ℝ) (i : ℤ) (k : (dyadicLaw μ i).support)
    (L : ℕ) {j : ℤ} (hj : 0 ≤ j ∧ j < 2 ^ L) :
    (rescaledComponent μ i k : Measure ℝ) (dyadicCell L j) =
      ((μ : Measure ℝ) (dyadicCell i k))⁻¹ *
        (μ : Measure ℝ) (dyadicCell (i + L) (2 ^ L * k + j)) := by
  unfold rescaledComponent
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply (measurable_componentRescale i k)
    (measurableSet_dyadicCell _ _), rawComponent_apply]
  congr 2
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, dyadicCell, Set.mem_ofPred_eq,
    dyadicQuantize_componentRescale]
  constructor
  · rintro ⟨-, h⟩
    omega
  · intro h
    refine ⟨?_, by omega⟩
    rw [dyadicQuantize_add_nat i L x, h]
    have hpos : (0 : ℤ) < ((2 ^ L : ℕ) : ℤ) := by positivity
    push_cast at hpos ⊢
    rw [add_comm, Int.add_mul_ediv_left _ _ hpos.ne', Int.ediv_eq_zero_of_lt hj.1 hj.2, zero_add]

theorem variance_ge_of_sep (ν : Measure ℝ) [IsProbabilityMeasure ν] {a b : ℝ}
    (hab : ∀ᵐ x ∂ν, x ∈ Set.Icc a b) {E₁ E₂ : Set ℝ} (hE₁ : MeasurableSet E₁)
    (hE₂ : MeasurableSet E₂) {u v q : ℝ} (huv : u ≤ v) (h₁ : ∀ x ∈ E₁, x ≤ u)
    (h₂ : ∀ x ∈ E₂, v ≤ x) (hq₁ : q ≤ ν.real E₁) (hq₂ : q ≤ ν.real E₂) :
    q * ((v - u) / 2) ^ 2 ≤ variance id ν := by
  rw [variance_eq_integral measurable_id.aemeasurable]
  set c : ℝ := ∫ x, id x ∂ν
  set g : ℝ → ℝ := fun x => (id x - c) ^ 2 with hg
  have hgint : Integrable g ν := by
    refine Integrable.of_bound (by fun_prop) ((|a| + |b| + |c|) ^ 2) ?_
    filter_upwards [hab] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hg]
    simp only [id]
    have h1 : |x - c| ≤ |a| + |b| + |c| := by
      have hx1 : |x| ≤ |a| + |b| := by
        rw [abs_le]
        constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith [hx.1, hx.2]
      calc |x - c| ≤ |x| + |c| := abs_sub _ _
        _ ≤ _ := by linarith
    calc (x - c) ^ 2 = |x - c| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hg0 : 0 ≤ᵐ[ν] g := Filter.Eventually.of_forall fun x => sq_nonneg _
  have key : ∀ E : Set ℝ, MeasurableSet E → (∀ x ∈ E, (v - u) / 2 ≤ |x - c|) →
      q ≤ ν.real E → q * ((v - u) / 2) ^ 2 ≤ ∫ x, g x ∂ν := by
    intro E hE hd hq
    have hd' : ∀ x ∈ E, ((v - u) / 2) ^ 2 ≤ g x := by
      intro x hx
      have := hd x hx
      have h0 : 0 ≤ (v - u) / 2 := by linarith
      calc ((v - u) / 2) ^ 2 ≤ |x - c| ^ 2 := pow_le_pow_left₀ h0 this 2
        _ = g x := by simp [hg, sq_abs]
    have hset := setIntegral_ge_of_const_le hE (measure_ne_top ν E) hd' hgint.integrableOn
    have hle := setIntegral_le_integral (s := E) hgint hg0
    rw [smul_eq_mul] at hset
    have hsq : 0 ≤ ((v - u) / 2) ^ 2 := sq_nonneg _
    nlinarith
  by_cases hc : c ≤ (u + v) / 2
  · refine key E₂ hE₂ (fun x hx => ?_) hq₂
    have := h₂ x hx
    rw [abs_of_nonneg (by linarith)]
    linarith
  · refine key E₁ hE₁ (fun x hx => ?_) hq₁
    have := h₁ x hx
    rw [abs_of_nonpos (by linarith)]
    linarith

theorem min_add_two_le_max {K : Finset ℤ} (hK : 3 ≤ K.card) :
    ∃ c₁ ∈ K, ∃ c₃ ∈ K, c₁ + 2 ≤ c₃ := by
  have hne : K.Nonempty := card_pos.mp (by omega)
  refine ⟨K.min' hne, min'_mem _ _, K.max' hne, max'_mem _ _, ?_⟩
  by_contra hlt
  push Not at hlt
  have hsub : K ⊆ Icc (K.min' hne) (K.min' hne + 1) := fun c hc =>
    mem_Icc.mpr ⟨min'_le _ _ hc, by linarith [le_max' _ _ hc]⟩
  have := card_le_card hsub
  rw [Int.card_Icc] at this
  omega

theorem averageComponentVariance_unifLaw_ge {L S : ℕ} {A : Finset ℤ} {R : ℕ → ℕ}
    (hA : A.Nonempty) (hAM : InUnit (S * L) A) (h : IsUnif L S A R) {s : ℕ} (hs : s < S)
    (hR : 3 ≤ R s) :
    ((2 : ℝ) ^ L)⁻¹ * (((2 : ℝ) ^ L)⁻¹ / 2) ^ 2 ≤
      averageComponentVariance (unifLaw (S * L) A hA) (hasBoundedSupport_unifLaw hA hAM)
        ((s * L : ℕ) : ℤ) := by
  set μ := unifLaw (S * L) A hA with hμ
  set i : ℤ := ((s * L : ℕ) : ℤ) with hi
  unfold averageComponentVariance
  rw [← expectation_const (supportLaw (dyadicLaw μ i))
    (componentIndexLaw_support_finite μ (hasBoundedSupport_unifLaw hA hAM) i)
    (((2 : ℝ) ^ L)⁻¹ * (((2 : ℝ) ^ L)⁻¹ / 2) ^ 2)]
  apply expectation_mono
  intro k _

  have hsL : s * L ≤ S * L := Nat.mul_le_mul_right _ hs.le
  have hs1L : (s + 1) * L ≤ S * L := Nat.mul_le_mul_right _ hs
  have hle : s * L ≤ (s + 1) * L := Nat.mul_le_mul_right _ (Nat.le_succ s)
  have hkpos : (μ : Measure ℝ) (dyadicCell i k) ≠ 0 := dyadicCell_measure_ne_zero μ i k
  have hcell : (μ : Measure ℝ) (dyadicCell i k) =
      ((cellOf (S * L) (s * L) A k).card : ℝ≥0∞) / A.card := unifLaw_cell hsL hA (k : ℤ)
  obtain ⟨x, hx⟩ : (cellOf (S * L) (s * L) A k).Nonempty := by
    rw [← card_pos]
    by_contra h0
    apply hkpos
    rw [hcell]
    simp [Nat.eq_zero_of_not_pos h0]
  obtain ⟨hxA, hxk⟩ := mem_cellOf.mp hx

  set K := kids (S * L) (s * L) ((s + 1) * L) A k with hK
  have hKcard : K.card = R s := by
    have := h s hs x hxA
    rwa [branching_eq_card_kids, hxk] at this
  obtain ⟨c₁, hc₁, c₃, hc₃, h13⟩ := min_add_two_le_max (hKcard ▸ hR)
  have hLd : (s + 1) * L - s * L = L := by rw [Nat.succ_mul]; omega
  have hdiv : ∀ c ∈ K, c / 2 ^ L = k := by
    intro c hc
    have := pre_of_mem_kids hle hs1L hc
    rwa [hLd] at this
  set P : ℕ := ∏ s' ∈ Ico (s + 1) S, R s' with hP
  have hbounds := h.bounds hA
  have hPpos : 0 < P := prod_pos fun s' hs' => (hbounds s' (mem_Ico.mp hs').2).1
  have hRpos : 0 < R s := (hbounds s hs).1
  have hRle : R s ≤ 2 ^ L := (hbounds s hs).2
  have hcardA : 0 < A.card := card_pos.mpr hA

  have hkmass : (μ : Measure ℝ) (dyadicCell i k) = ((R s * P : ℕ) : ℝ≥0∞) / A.card := by
    rw [hcell, ← hxk, h.cell_card' hs.le hxA, prod_eq_prod_Ico_succ_bot hs]
  have hcmass : ∀ c ∈ K, (μ : Measure ℝ) (dyadicCell (i + L) c) = (P : ℝ≥0∞) / A.card := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hc
    have hyA := (mem_cellOf.mp hy).1
    have hcast : i + (L : ℤ) = (((s + 1) * L : ℕ) : ℤ) := by
      rw [hi]; push_cast; ring
    rw [hcast, hμ, unifLaw_cell hs1L hA, h.cell_card' (Nat.succ_le_of_lt hs) hyA]
  have hjmem : ∀ c ∈ K, 0 ≤ c - 2 ^ L * k ∧ c - 2 ^ L * k < 2 ^ L := by
    intro c hc
    have hd := hdiv c hc
    have hpos : (0 : ℤ) < 2 ^ L := by positivity
    have h1 := Int.emod_nonneg c hpos.ne'
    have h2 := Int.emod_lt_of_pos c hpos
    have h3 := Int.mul_ediv_add_emod c (2 ^ L)
    rw [hd] at h3
    constructor <;> linarith
  have hreal : ∀ c ∈ K, ((2 : ℝ) ^ L)⁻¹ ≤
      (rescaledComponent μ i k : Measure ℝ).real (dyadicCell L (c - 2 ^ L * k)) := by
    intro c hc
    rw [measureReal_def, rescaledComponent_cell μ i k L (hjmem c hc),
      show 2 ^ L * (k : ℤ) + (c - 2 ^ L * k) = c by ring, hkmass, hcmass c hc,
      ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_div,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
    have hP' : (0 : ℝ) < P := by exact_mod_cast hPpos
    have hR' : (0 : ℝ) < R s := by exact_mod_cast hRpos
    have hA' : (0 : ℝ) < A.card := by exact_mod_cast hcardA
    have hRle' : (R s : ℝ) ≤ 2 ^ L := by exact_mod_cast hRle
    push_cast
    rw [show ((R s : ℝ) * P / A.card)⁻¹ * (P / A.card) = (R s : ℝ)⁻¹ by field_simp]
    exact inv_anti₀ hR' hRle'

  set j₁ := c₁ - 2 ^ L * k
  set j₃ := c₃ - 2 ^ L * k
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  have hcomp : IsProbabilityMeasure (rescaledComponent μ i k : Measure ℝ) := inferInstance
  have hgap : ((j₃ : ℝ) - (j₁ + 1)) / 2 ^ L ≥ ((2 : ℝ) ^ L)⁻¹ := by
    rw [ge_iff_le, inv_eq_one_div, div_le_div_iff_of_pos_right h2L]
    have : j₁ + 2 ≤ j₃ := by simp only [j₁, j₃]; linarith
    have : (j₁ : ℝ) + 2 ≤ j₃ := by exact_mod_cast this
    linarith
  have hvar := variance_ge_of_sep (rescaledComponent μ i k : Measure ℝ) (a := 0) (b := 1)
    ((ae_rescaledComponent_mem_Ico μ i k).mono fun x hx => ⟨hx.1, hx.2.le⟩)
    (measurableSet_dyadicCell (L : ℤ) j₁) (measurableSet_dyadicCell (L : ℤ) j₃)
    (u := ((j₁ : ℝ) + 1) / 2 ^ L) (v := (j₃ : ℝ) / 2 ^ L)
    (by
      rw [div_le_div_iff_of_pos_right h2L]
      have h13' : j₁ + 2 ≤ j₃ := by simp only [j₁, j₃]; linarith
      have : (j₁ : ℝ) + 2 ≤ j₃ := by exact_mod_cast h13'
      linarith)
    (fun x hx => by
      rw [dyadicCell_eq_Ico, zpow_natCast] at hx
      exact hx.2.le)
    (fun x hx => by
      rw [dyadicCell_eq_Ico, zpow_natCast] at hx
      exact hx.1)
    (hreal c₁ hc₁) (hreal c₃ hc₃)
  unfold componentVariance
  refine le_trans ?_ hvar
  have hq : (0 : ℝ) ≤ ((2 : ℝ) ^ L)⁻¹ := by positivity
  apply mul_le_mul_of_nonneg_left _ hq
  apply pow_le_pow_left₀ (by positivity)
  rw [div_sub_div_same]
  linarith

theorem convPower_compl {M : ℕ} {A : Finset ℤ} (hA : A.Nonempty) (n : ℕ) :
    (realConvolutionPower (unifLaw M A hA) n : Measure ℝ) ((scaled M (n • A) : Set ℝ)ᶜ) = 0 := by
  induction n with
  | zero =>
    change (Measure.dirac (0 : ℝ)) _ = 0
    rw [Measure.dirac_apply' _ (Finset.measurableSet _).compl]
    simp only [Set.indicator_apply_eq_zero, Set.mem_compl_iff, mem_coe, Pi.one_apply,
      one_ne_zero, imp_false, not_not]
    refine mem_image.mpr ⟨0, ?_, by simp⟩
    rw [zero_nsmul]
    exact Finset.mem_zero.mpr rfl
  | succ n ih =>
    change (realConvolution (unifLaw M A hA) (realConvolutionPower (unifLaw M A hA) n) :
      Measure ℝ) _ = 0
    rw [realConvolution_toMeasure, Measure.conv, Measure.map_apply (by fun_prop)
      (Finset.measurableSet _).compl]
    refine measure_mono_null (t := ((scaled M A : Set ℝ)ᶜ ×ˢ Set.univ) ∪
      (Set.univ ×ˢ (scaled M (n • A) : Set ℝ)ᶜ)) ?_ ?_
    · intro p hp
      simp only [Set.mem_preimage, Set.mem_compl_iff, mem_coe] at hp
      by_contra hp'
      simp only [Set.mem_union, Set.mem_prod, Set.mem_compl_iff, mem_coe, Set.mem_univ,
        and_true, true_and, not_or, not_not] at hp'
      obtain ⟨a, ha, hpa⟩ := mem_image.mp hp'.1
      obtain ⟨b, hb, hpb⟩ := mem_image.mp hp'.2
      apply hp
      refine mem_image.mpr ⟨a + b, ?_, ?_⟩
      · rw [succ_nsmul']
        exact Finset.add_mem_add ha hb
      · rw [← hpa, ← hpb]
        push_cast
        ring
    · refine measure_union_null ?_ ?_
      · rw [Measure.prod_prod, unifLaw_compl, zero_mul]
      · rw [Measure.prod_prod, ih, mul_zero]

theorem dyadicEntropy_convPower_le {M : ℕ} {A : Finset ℤ} (hA : A.Nonempty) (n : ℕ)
    (hb : HasBoundedSupport (realConvolutionPower (unifLaw M A hA) n)) (l : ℤ) :
    dyadicEntropy (realConvolutionPower (unifLaw M A hA) n) hb l ≤ Real.log (n • A).card := by
  set τ := realConvolutionPower (unifLaw M A hA) n
  unfold dyadicEntropy
  refine le_trans (finiteEntropy_le_log_card _ _) ?_
  have hsub : (dyadicLaw_support_finite τ hb l).toFinset ⊆
      (scaled M (n • A)).image (dyadicQuantize l) := by
    intro k hk
    rw [Set.Finite.mem_toFinset, PMF.mem_support_iff, dyadicLaw_apply] at hk
    by_contra hnot
    apply hk
    refine measure_mono_null (fun y hy => ?_) (convPower_compl hA n)
    intro hy'
    exact hnot (mem_image.mpr ⟨y, hy', hy⟩)
  have hpos : 0 < (dyadicLaw_support_finite τ hb l).toFinset.card := by
    rw [card_pos, Set.Finite.toFinset_nonempty]
    exact PMF.support_nonempty _
  apply Real.log_le_log (by exact_mod_cast hpos)
  calc ((dyadicLaw_support_finite τ hb l).toFinset.card : ℝ)
      ≤ ((scaled M (n • A)).image (dyadicQuantize l)).card := by exact_mod_cast card_le_card hsub
    _ ≤ (scaled M (n • A)).card := by exact_mod_cast card_image_le
    _ = (n • A).card := by rw [card_scaled]

theorem averageComponentEntropy_ge (ν : ProbabilityMeasure ℝ) (hν : HasBoundedSupport ν) (j : ℤ)
    (m : ℕ) (a : ℝ) :
    (1 - a) * (1 - componentEntropyLowerTailMass ν hν j m a) ≤
      averageComponentEntropy ν hν j m := by
  classical
  let : Fintype (dyadicLaw ν j).support := (dyadicLaw_support_finite ν hν j).fintype
  have hsum := sum_dyadic_cell_mass ν hν j
  unfold componentEntropyLowerTailMass averageComponentEntropy
  rw [← hsum, ← sum_sub_distrib, mul_sum]
  apply sum_le_sum
  intro k _
  have hw : 0 ≤ ((dyadicLaw ν j) k).toReal := ENNReal.toReal_nonneg
  have he := normalizedDyadicEntropy_nonneg (rescaledComponent ν j k)
    (rescaledComponent_hasBoundedSupport ν j k) m
  split_ifs with h
  · simp only [sub_self, mul_zero]
    exact mul_nonneg hw he
  · push Not at h
    rw [sub_zero]
    nlinarith

theorem dichotomy_core {L : ℕ} (hL : 1 ≤ L) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ n : ℕ, 0 < n ∧ ∀ (S : ℕ) (A : Finset ℤ) (R : ℕ → ℕ), A.Nonempty → InUnit (S * L) A →
      IsUnif L S A R →
      (L : ℝ) * (1 - δ) ^ 2 * ((range S).filter (fun s => 3 ≤ R s)).card * Real.log 2 ≤
        Real.log (n • A).card := by
  set v : ℝ := ((2 : ℝ) ^ L)⁻¹ * (((2 : ℝ) ^ L)⁻¹ / 2) ^ 2 with hv
  have hvpos : 0 < v := by positivity
  obtain ⟨p, K, hK, hunif⟩ := exists_repeated_convolution_component_uniformity
    (σ := v / 2) (δ := δ) (by positivity) hδ (m := L) (by omega)
  refine ⟨K, hK, fun S A R hA hAM h => ?_⟩
  set μ := unifLaw (S * L) A hA
  have hμ : HasBoundedSupport μ := hasBoundedSupport_unifLaw hA hAM
  set τ := realConvolutionPower μ K
  have hτ : HasBoundedSupport τ := realConvolutionPower_hasBoundedSupport μ hμ K
  set d : ℤ := (dyadicSqrtScale K : ℤ)

  set j : ℕ → ℤ := fun s => ((s * L : ℕ) : ℤ) - d + p with hj
  have hjs : ∀ s, j s + L = j (s + 1) := by
    intro s
    simp only [hj]
    push_cast
    ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hincr : ∀ s, dyadicEntropy τ hτ (j (s + 1)) - dyadicEntropy τ hτ (j s) =
      (L : ℝ) * Real.log 2 * averageComponentEntropy τ hτ (j s) L := by
    intro s
    rw [averageComponentEntropy_eq_increment, hjs s]
    have : (L : ℝ) * Real.log 2 ≠ 0 := by
      have : (0 : ℝ) < L := by exact_mod_cast hL
      positivity
    field_simp
  have hgood : ∀ s ∈ (range S).filter (fun s => 3 ≤ R s),
      (L : ℝ) * (1 - δ) ^ 2 * Real.log 2 ≤
        dyadicEntropy τ hτ (j (s + 1)) - dyadicEntropy τ hτ (j s) := by
    intro s hs
    obtain ⟨hsS, hR⟩ := mem_filter.mp hs
    have hvar := averageComponentVariance_unifLaw_ge hA hAM h (mem_range.mp hsS) hR
    have htail := hunif K le_rfl μ hμ ((s * L : ℕ) : ℤ) (by linarith)
    have havg := averageComponentEntropy_ge τ hτ (j s) L δ
    rw [hincr s]
    have hL' : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    have h1 : (1 - δ) * (1 - δ) ≤ averageComponentEntropy τ hτ (j s) L := by
      refine le_trans ?_ havg
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact le_of_lt (by simpa [hj] using sub_lt_sub_left htail 1)
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hL' hlog2.le)
    nlinarith
  have hnonneg : ∀ s, 0 ≤ dyadicEntropy τ hτ (j (s + 1)) - dyadicEntropy τ hτ (j s) := by
    intro s
    rw [← hjs s]
    exact sub_nonneg.mpr (dyadicEntropy_le_add_nat τ hτ (j s) L)
  have htel : ∑ s ∈ range S, (dyadicEntropy τ hτ (j (s + 1)) - dyadicEntropy τ hτ (j s)) =
      dyadicEntropy τ hτ (j S) - dyadicEntropy τ hτ (j 0) :=
    sum_range_sub (fun s => dyadicEntropy τ hτ (j s)) S
  have hsplit := sum_filter_add_sum_filter_not (range S) (fun s => 3 ≤ R s)
    (fun s => dyadicEntropy τ hτ (j (s + 1)) - dyadicEntropy τ hτ (j s))
  have hA1 : ∑ s ∈ (range S).filter (fun s => 3 ≤ R s), (L : ℝ) * (1 - δ) ^ 2 * Real.log 2 ≤
      ∑ s ∈ (range S).filter (fun s => 3 ≤ R s),
        (dyadicEntropy τ hτ (j (s + 1)) - dyadicEntropy τ hτ (j s)) := sum_le_sum hgood
  have hA2 : 0 ≤ ∑ s ∈ (range S).filter (fun s => ¬ 3 ≤ R s),
      (dyadicEntropy τ hτ (j (s + 1)) - dyadicEntropy τ hτ (j s)) :=
    sum_nonneg fun s _ => hnonneg s
  rw [sum_const, nsmul_eq_mul] at hA1
  have hup := dyadicEntropy_convPower_le hA K hτ (j S)
  have hlow := dyadicEntropy_nonneg τ hτ (j 0)
  nlinarith

end Bourgain

end Lq

end FractalGeometry
