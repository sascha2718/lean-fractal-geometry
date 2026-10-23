import Mathlib
import GeometricMeasureTheory.Box.ModifiedBox
import FractalGeometry.Dimension.BoxTools
import FractalGeometry.LinearCocycles.Monomial
import FractalGeometry.SelfAffine.Rectangular.Attractor
import FractalGeometry.SelfAffine.Rectangular.Coding
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.SelfAffine.Rectangular.OpenSet
import FractalGeometry.SelfAffine.Rectangular.SingularValues
import FractalGeometry.Symbolic.Concatenation
import GeometricMeasureTheory.Box.BoxDimension

open GeometricMeasureTheory

namespace FractalGeometry

open Filter Topology Matrix

open scoped ENNReal NNReal Matrix.Norms.L2Operator

theorem rpow_mul_rpow_sub_mono {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) (s : ℝ) {d p : ℝ}
    (hdp : d ≤ p) : x ^ d * y ^ (s - d) ≤ x ^ p * y ^ (s - p) := by
  have hx : 0 < x := hy.trans_le hyx
  calc x ^ d * y ^ (s - d) = x ^ d * (y ^ (p - d) * y ^ (s - p)) := by
        rw [← Real.rpow_add hy]; congr 2; ring
    _ ≤ x ^ d * (x ^ (p - d) * y ^ (s - p)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hy.le hyx (sub_nonneg.2 hdp)) (Real.rpow_nonneg hy.le _))
          (Real.rpow_nonneg hx.le _)
    _ = x ^ p * y ^ (s - p) := by
        rw [← mul_assoc, ← Real.rpow_add hx]; congr 2; ring

theorem existsUnique_zero_of_increment {f : ℝ → ℝ} {c₁ c₂ : ℝ} (hc₂ : c₂ < 0) (h0 : 0 ≤ f 0)
    (h : ∀ s t : ℝ, 0 ≤ s → s ≤ t → (t - s) * c₁ ≤ f t - f s ∧ f t - f s ≤ (t - s) * c₂) :
    ∃! s : ℝ, 0 ≤ s ∧ f s = 0 := by
  have hanti : StrictAntiOn f (Set.Ici 0) := by
    intro s hs t _ hst
    have h' := (h s t hs hst.le).2
    have hneg : (t - s) * c₂ < 0 := mul_neg_of_pos_of_neg (sub_pos.2 hst) hc₂
    linarith
  have hc₁ : c₁ ≤ c₂ := by
    have h' := h 0 1 le_rfl zero_le_one
    linarith
  have hK : 0 ≤ -c₁ := by linarith
  have habs : ∀ x y : ℝ, 0 ≤ x → x ≤ y → |f x - f y| ≤ -c₁ * |x - y| := by
    intro x y hx hxy
    obtain ⟨h1, h2⟩ := h x y hx hxy
    have hxy' : 0 ≤ y - x := sub_nonneg.2 hxy
    have hle0 : f y - f x ≤ 0 := h2.trans (mul_nonpos_of_nonneg_of_nonpos hxy' hc₂.le)
    rw [abs_sub_comm, abs_of_nonpos hle0, abs_of_nonpos (sub_nonpos.2 hxy)]
    linarith [neg_mul c₁ (-(x - y)), mul_neg c₁ (-(x - y)), mul_comm c₁ (y - x)]
  have hcont : ContinuousOn f (Set.Ici 0) := by
    refine LipschitzOnWith.continuousOn (K := (-c₁).toNNReal)
      (LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_)
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK]
    rcases le_total x y with hxy | hxy
    · exact habs x y hx hxy
    · rw [abs_sub_comm, abs_sub_comm x y]
      exact habs y x hy hxy
  obtain ⟨x, hx0, hx⟩ : ∃ x : ℝ, 0 ≤ x ∧ f x ≤ 0 := by
    refine ⟨f 0 / -c₂, div_nonneg h0 (by linarith), ?_⟩
    have h' := (h 0 (f 0 / -c₂) le_rfl (div_nonneg h0 (by linarith))).2
    have : (f 0 / -c₂ - 0) * c₂ = -f 0 := by
      rw [sub_zero, div_neg, neg_mul, div_mul_cancel₀ _ hc₂.ne]
    linarith
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hx0 (hcont.mono Set.Icc_subset_Ici_self)
    (⟨hx, h0⟩ : (0 : ℝ) ∈ Set.Icc (f x) (f 0))
  exact ⟨z, ⟨hz.1, hz0⟩, fun w hw => hanti.injOn hw.1 hz.1 (hw.2.trans hz0.symm)⟩

theorem upperBoxDim_image_affine {a : ℝ} (ha : a ≠ 0) (b : ℝ) (F : Set ℝ) :
    upperBoxDim ((fun t : ℝ => a * t + b) '' F) = upperBoxDim F := by
  have hf : LipschitzWith ‖a‖₊ fun t : ℝ => a * t + b :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, Real.dist_eq, coe_nnnorm, Real.norm_eq_abs, ← abs_mul]
      exact le_of_eq (by ring_nf)
  have hg : LipschitzWith ‖a⁻¹‖₊ fun u : ℝ => a⁻¹ * (u - b) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, Real.dist_eq, coe_nnnorm, Real.norm_eq_abs, ← abs_mul]
      exact le_of_eq (by ring_nf)
  refine upperBoxDim_image_eq (hf.lipschitzOnWith) (hg.lipschitzOnWith) fun x _ => ?_
  field_simp
  ring

namespace RectangularIFS

variable {ι : Type*} (S : RectangularIFS ι)

noncomputable def projDim (c : ZMod 2) : ℝ := (upperBoxDim (coord c '' S.attractor)).toReal

theorem projDim_nonneg (c : ZMod 2) : 0 ≤ S.projDim c := ENNReal.toReal_nonneg

theorem continuous_coord (c : ZMod 2) : Continuous (coord c) := by
  unfold coord
  split_ifs <;> fun_prop

theorem upperBoxDim_coord_le_one [Finite ι] (c : ZMod 2) :
    upperBoxDim (coord c '' S.attractor) ≤ 1 :=
  upperBoxDim_le_one (S.isCompact_attractor.image (continuous_coord c)).isBounded

theorem projDim_le_one [Finite ι] (c : ZMod 2) : S.projDim c ≤ 1 := by
  have h := ENNReal.toReal_mono ENNReal.one_ne_top (S.upperBoxDim_coord_le_one c)
  rwa [ENNReal.toReal_one] at h

theorem upperBoxDim_coord_add_le [Finite ι] (i : ι) (c : ZMod 2) :
    upperBoxDim (coord (c + S.o i) '' S.attractor) ≤ upperBoxDim (coord c '' S.attractor) := by
  have hsub : (fun t : ℝ => S.ratio (i, c) * t + S.trans (i, c)) ''
      (coord (c + S.o i) '' S.attractor) ⊆ coord c '' S.attractor := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨S.phi i z, S.image_attractor_subset i ⟨z, hz, rfl⟩, S.coord_phi c i z⟩
  rw [← upperBoxDim_image_affine (S.ratio_ne_zero (i, c)) (S.trans (i, c))]
  exact upperBoxDim_mono hsub

theorem upperBoxDim_coord_eq [Finite ι] (h : ∃ i, S.o i = 1) (c c' : ZMod 2) :
    upperBoxDim (coord c '' S.attractor) = upperBoxDim (coord c' '' S.attractor) := by
  obtain ⟨i, hi⟩ := h
  have key : ∀ c : ZMod 2,
      upperBoxDim (coord (c + 1) '' S.attractor) ≤ upperBoxDim (coord c '' S.attractor) :=
    fun c => hi ▸ S.upperBoxDim_coord_add_le i c
  have h01 := key 0
  have h10 := key 1
  rw [show (1 : ZMod 2) + 1 = 0 from by decide] at h10
  rw [zero_add] at h01
  rcases zmod_two_cases c with rfl | rfl <;> rcases zmod_two_cases c' with rfl | rfl
  exacts [rfl, le_antisymm h10 h01, le_antisymm h01 h10, rfl]

theorem projDim_eq [Finite ι] (h : ∃ i, S.o i = 1) (c c' : ZMod 2) :
    S.projDim c = S.projDim c' := by
  rw [projDim, projDim, S.upperBoxDim_coord_eq h c c']

theorem phiWord_append (w w' : List ι) : S.phiWord (w ++ w') = S.phiWord w ∘ S.phiWord w' := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [List.cons_append, phiWord_cons, phiWord_cons, ih, Function.comp_assoc]

theorem phiWord_image_attractor_subset [Finite ι] (w : List ι) :
    S.phiWord w '' S.attractor ⊆ S.attractor := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [phiWord_cons, Set.image_comp]
    exact (Set.image_mono ih).trans (S.image_attractor_subset i)

theorem abs_gDeriv_codeWord_cons (c : ZMod 2) (i : ι) (w : List ι) :
    |S.gDeriv (S.codeWord c (i :: w))| =
      |S.ratio (i, c)| * |S.gDeriv (S.codeWord (c + S.o i) w)| := by
  rw [codeWord_cons, gDeriv_cons, abs_mul]

theorem exists_word_mem_side [Finite ι] {δ₀ r : ℝ} (hδ₀ : S.RatioLowerBound δ₀) (hδ₀1 : δ₀ ≤ 1)
    (hr0 : 0 < r) (hr : ∀ p, |S.ratio p| ≤ r) (k : ℕ) :
    ∀ (c : ZMod 2) (z : ℝ × ℝ), z ∈ S.attractor → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → r ^ k ≤ ρ →
      ∃ w : List ι, z ∈ S.phiWord w '' S.attractor ∧ |S.gDeriv (S.codeWord c w)| ≤ ρ ∧
        δ₀ * ρ ≤ |S.gDeriv (S.codeWord c w)| := by
  have hnil : ∀ (c : ZMod 2) (z : ℝ × ℝ), z ∈ S.attractor → ∀ ρ : ℝ, ρ = 1 →
      ∃ w : List ι, z ∈ S.phiWord w '' S.attractor ∧ |S.gDeriv (S.codeWord c w)| ≤ ρ ∧
        δ₀ * ρ ≤ |S.gDeriv (S.codeWord c w)| := fun c z hz ρ hρ =>
    ⟨[], ⟨z, hz, rfl⟩, by simp [hρ], by simp [hρ, hδ₀1]⟩
  induction k with
  | zero =>
    intro c z hz ρ _ hρ1 hk
    rw [pow_zero] at hk
    exact hnil c z hz ρ (le_antisymm hρ1 hk)
  | succ k ih =>
    intro c z hz ρ hρ hρ1 hk
    by_cases h1 : 1 ≤ ρ
    · exact hnil c z hz ρ (le_antisymm hρ1 h1)
    rw [not_le] at h1
    rw [S.attractor_eq_iUnion] at hz
    obtain ⟨i, z', hz', rfl⟩ : ∃ i, ∃ z' ∈ S.attractor, S.phi i z' = z := by simpa using hz
    have hq : 0 < |S.ratio (i, c)| := abs_pos.2 (S.ratio_ne_zero _)
    have hqδ : δ₀ ≤ |S.ratio (i, c)| := hδ₀.2 _
    by_cases h2 : |S.ratio (i, c)| ≤ ρ
    · refine ⟨[i], ⟨z', hz', rfl⟩, ?_, ?_⟩
      · rw [abs_gDeriv_codeWord_cons]
        simpa using h2
      · rw [abs_gDeriv_codeWord_cons]
        simp only [codeWord_nil, gDeriv_nil, abs_one, mul_one]
        calc δ₀ * ρ ≤ δ₀ * 1 := mul_le_mul_of_nonneg_left hρ1 hδ₀.1.le
          _ = δ₀ := mul_one _
          _ ≤ |S.ratio (i, c)| := hqδ
    · rw [not_le] at h2
      have hρ' : 0 < ρ / |S.ratio (i, c)| := div_pos hρ hq
      have hρ'1 : ρ / |S.ratio (i, c)| ≤ 1 := (div_le_one hq).2 h2.le
      have hk' : r ^ k ≤ ρ / |S.ratio (i, c)| := by
        rw [le_div_iff₀ hq]
        calc r ^ k * |S.ratio (i, c)| ≤ r ^ k * r :=
              mul_le_mul_of_nonneg_left (hr _) (pow_nonneg hr0.le _)
          _ = r ^ (k + 1) := (pow_succ _ _).symm
          _ ≤ ρ := hk
      obtain ⟨w, ⟨x, hx, hxw⟩, hw1, hw2⟩ := ih (c + S.o i) z' hz' _ hρ' hρ'1 hk'
      refine ⟨i :: w, ⟨x, hx, by rw [phiWord_cons, Function.comp_apply, hxw]⟩, ?_, ?_⟩
      · rw [abs_gDeriv_codeWord_cons]
        calc |S.ratio (i, c)| * |S.gDeriv (S.codeWord (c + S.o i) w)|
            ≤ |S.ratio (i, c)| * (ρ / |S.ratio (i, c)|) := mul_le_mul_of_nonneg_left hw1 hq.le
          _ = ρ := mul_div_cancel₀ _ hq.ne'
      · rw [abs_gDeriv_codeWord_cons]
        calc δ₀ * ρ = |S.ratio (i, c)| * (δ₀ * (ρ / |S.ratio (i, c)|)) := by
              field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hw2 hq.le

theorem exists_diagonal_extension [Finite ι] {δ₀ : ℝ} (hδ₀ : S.RatioLowerBound δ₀)
    (hδ₀1 : δ₀ ≤ 1) (c : ZMod 2) (w : List ι) : ∃ w' : List ι, S.oWord w' = 0 ∧
      S.phiWord w' '' S.attractor ⊆ S.phiWord w '' S.attractor ∧
      δ₀ * |S.gDeriv (S.codeWord c w)| ≤ |S.gDeriv (S.codeWord c w')| := by
  rcases zmod_two_cases (S.oWord w) with h0 | h1
  · exact ⟨w, h0, le_rfl, mul_le_of_le_one_left (abs_nonneg _) hδ₀1⟩
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ w.map S.o, x ≠ 0 :=
    List.exists_mem_ne_zero_of_sum_ne_zero (by
      change S.oWord w ≠ 0
      rw [h1]
      decide)
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  have hj : S.o j = 1 := (zmod_two_cases (S.o j)).resolve_left hx0
  refine ⟨w ++ [j], ?_, ?_, ?_⟩
  · rw [oWord_append, h1, oWord_cons, hj, oWord_nil]
    decide
  · rw [phiWord_append, Set.image_comp]
    refine Set.image_mono ?_
    simpa using S.image_attractor_subset j
  · rw [codeWord_append, gDeriv_append, abs_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    simpa using hδ₀.2 (j, c + S.oWord w)

theorem exists_affine_copy [Finite ι] [Nonempty ι] :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧ ∀ c : ZMod 2, ∀ y ∈ coord c '' S.attractor, ∀ ρ : ℝ, 0 < ρ →
      ρ ≤ 1 → ∃ a b : ℝ, κ * ρ ≤ |a| ∧ ∀ t ∈ coord c '' S.attractor,
        a * t + b ∈ coord c '' S.attractor ∧ |a * t + b - y| ≤ ρ := by
  obtain ⟨δ₀, hδ₀⟩ := S.exists_ratioLowerBound
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  obtain ⟨i⟩ : Nonempty ι := inferInstance
  have hδ₀1 : δ₀ ≤ 1 := (hδ₀.2 (i, 0)).trans (S.abs_ratio_lt_one _).le
  have hr : 0 < r := hδ₀.1.trans_le ((hδ₀.2 (i, 0)).trans (hS.abs_ratio_le (i, 0)))
  obtain ⟨D₀, hD₀⟩ := Metric.isBounded_iff.1 S.isCompact_attractor.isBounded
  have hD1 : 1 ≤ max D₀ 1 := le_max_right _ _
  have hD0 : 0 < max D₀ 1 := one_pos.trans_le hD1
  have hdist : ∀ x ∈ S.attractor, ∀ x' ∈ S.attractor, dist x x' ≤ max D₀ 1 :=
    fun x hx x' hx' => (hD₀ hx hx').trans (le_max_left _ _)
  have hδ₀0 := hδ₀.1
  refine ⟨δ₀ * δ₀ / max D₀ 1, by positivity, ?_, ?_⟩
  · rw [div_le_one hD0]
    calc δ₀ * δ₀ ≤ 1 * 1 := mul_le_mul hδ₀1 hδ₀1 hδ₀.1.le zero_le_one
      _ = 1 := one_mul 1
      _ ≤ max D₀ 1 := hD1
  rintro c _ ⟨z, hz, rfl⟩ ρ hρ hρ1
  have hρD : 0 < ρ / max D₀ 1 := div_pos hρ hD0
  have hρD1 : ρ / max D₀ 1 ≤ 1 := (div_le_one hD0).2 (hρ1.trans hD1)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hρD hS.r_lt_one
  obtain ⟨w, ⟨x₀, hx₀, rfl⟩, hw1, hw2⟩ :=
    S.exists_word_mem_side hδ₀ hδ₀1 hr hS.abs_ratio_le k c z hz _ hρD hρD1 hk.le
  obtain ⟨w', hw'o, hw'sub, hw'side⟩ := S.exists_diagonal_extension hδ₀ hδ₀1 c w
  refine ⟨S.gDeriv (S.codeWord c w'), S.gWord (S.codeWord c w') 0, ?_, ?_⟩
  · calc δ₀ * δ₀ / max D₀ 1 * ρ = δ₀ * (δ₀ * (ρ / max D₀ 1)) := by ring
      _ ≤ δ₀ * |S.gDeriv (S.codeWord c w)| := mul_le_mul_of_nonneg_left hw2 hδ₀.1.le
      _ ≤ _ := hw'side
  rintro _ ⟨x, hx, rfl⟩
  have hcopy : S.gDeriv (S.codeWord c w') * coord c x + S.gWord (S.codeWord c w') 0 =
      coord c (S.phiWord w' x) := by
    rw [coord_phiWord, hw'o, add_zero, ← gWord_apply]
  rw [hcopy]
  refine ⟨⟨_, S.phiWord_image_attractor_subset w' ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
  obtain ⟨x', hx', hx'eq⟩ := hw'sub ⟨x, hx, rfl⟩
  rw [← hx'eq, coord_phiWord, coord_phiWord,
    S.gWord_apply (S.codeWord c w) (coord (c + S.oWord w) x'),
    S.gWord_apply (S.codeWord c w) (coord (c + S.oWord w) x₀)]
  calc |S.gDeriv (S.codeWord c w) * coord (c + S.oWord w) x' + S.gWord (S.codeWord c w) 0 -
        (S.gDeriv (S.codeWord c w) * coord (c + S.oWord w) x₀ + S.gWord (S.codeWord c w) 0)|
      = |S.gDeriv (S.codeWord c w)| *
          |coord (c + S.oWord w) x' - coord (c + S.oWord w) x₀| := by
        rw [← abs_mul]; ring_nf
    _ ≤ ρ / max D₀ 1 * max D₀ 1 :=
        mul_le_mul hw1 ((abs_coord_sub_le _ x' x₀).trans (hdist x' hx' x₀ hx₀)) (abs_nonneg _)
          hρD.le
    _ = ρ := div_mul_cancel₀ _ hD0.ne'

theorem upperBoxDim_coord_le_lowerBoxDim [Finite ι] [Nonempty ι] (c : ZMod 2) :
    upperBoxDim (coord c '' S.attractor) ≤ lowerBoxDim (coord c '' S.attractor) := by
  obtain ⟨κ, hκ0, hκ1, hcopy⟩ := S.exists_affine_copy
  have hEc : IsCompact (coord c '' S.attractor) :=
    S.isCompact_attractor.image (continuous_coord c)
  refine upperBoxDim_le_lowerBoxDim_of_superMul (S.attractor_nonempty.image _) (β := κ / 4)
    (by positivity) (by linarith) fun τ σ hτ hτ1 hσ hσ1 => ?_
  set E := coord c '' S.attractor with hE
  have hρ : 0 < τ / 4 := by positivity
  have hcop' : ∀ y ∈ E, ∃ a b : ℝ, κ * (τ / 4) ≤ |a| ∧
      ∀ t ∈ E, a * t + b ∈ E ∧ |a * t + b - y| ≤ τ / 4 :=
    fun y hy => hcopy c y hy _ hρ (by linarith)
  choose! a b hab hcop using hcop'
  obtain ⟨C, hCE, hCsep, hCcard⟩ :=
    exists_separated_finset hEc.totallyBounded (Real.toNNReal_pos.2 hτ)
  set ε : ℝ≥0 := (κ / 4 * τ * σ).toNNReal with hε
  have h4 : 4 * ((τ / 4).toNNReal : ℝ≥0∞) = (τ.toNNReal : ℝ≥0∞) := by
    change 4 * ENNReal.ofReal (τ / 4) = ENNReal.ofReal τ
    rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  have hsum : ∑ y ∈ C, Metric.externalCoveringNumber ε ((fun t => a y * t + b y) '' E) ≤
      Metric.externalCoveringNumber ε E := by
    refine sum_externalCoveringNumber_le (ρ := (τ / 4).toNNReal) ?_ C ?_ _ ?_
    · refine Real.toNNReal_le_toNNReal ?_
      calc κ / 4 * τ * σ = τ / 4 * (κ * σ) := by ring
        _ ≤ τ / 4 * 1 := mul_le_mul_of_nonneg_left
            ((mul_le_of_le_one_left hσ.le hκ1).trans hσ1) hρ.le
        _ = τ / 4 := mul_one _
    · intro y hy y' hy' hne
      rw [h4]
      exact hCsep y hy y' hy' hne
    · rintro y hy _ ⟨t, ht, rfl⟩
      obtain ⟨h1, h2⟩ := hcop y (hCE hy) t ht
      refine ⟨h1, ?_⟩
      rw [edist_dist, Real.dist_eq]
      exact ENNReal.ofReal_le_ofReal h2
  have hpiece : ∀ y ∈ C, Metric.externalCoveringNumber σ.toNNReal E ≤
      Metric.externalCoveringNumber ε ((fun t => a y * t + b y) '' E) := by
    intro y hy
    have ha : 0 < |a y| := lt_of_lt_of_le (by positivity) (hab y (hCE hy))
    have ha0 : a y ≠ 0 := abs_pos.1 ha
    have hg : LipschitzWith ‖(a y)⁻¹‖₊ fun u : ℝ => (a y)⁻¹ * (u - b y) :=
      LipschitzWith.of_dist_le_mul fun x x' => by
        rw [Real.dist_eq, Real.dist_eq, coe_nnnorm, Real.norm_eq_abs, ← abs_mul]
        exact le_of_eq (by ring_nf)
    have himg : (fun u : ℝ => (a y)⁻¹ * (u - b y)) '' ((fun t => a y * t + b y) '' E) = E := by
      rw [Set.image_image]
      refine (Set.image_congr fun t _ => ?_).trans (Set.image_id E)
      simp only [id]
      field_simp
      ring
    have h1 := externalCoveringNumber_image_le_of_lipschitzWith hg ε
      ((fun t => a y * t + b y) '' E)
    rw [himg] at h1
    refine le_trans (Metric.externalCoveringNumber_anti ?_) h1
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, hε,
      Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ hσ.le, abs_inv,
      inv_mul_le_iff₀ ha]
    calc κ / 4 * τ * σ = κ * (τ / 4) * σ := by ring
      _ ≤ |a y| * σ := mul_le_mul_of_nonneg_right (hab y (hCE hy)) hσ.le
  have key : Metric.externalCoveringNumber τ.toNNReal E *
      Metric.externalCoveringNumber σ.toNNReal E ≤ Metric.externalCoveringNumber ε E :=
    calc Metric.externalCoveringNumber τ.toNNReal E * Metric.externalCoveringNumber σ.toNNReal E
        ≤ (C.card : ℕ∞) * Metric.externalCoveringNumber σ.toNNReal E := by gcongr
      _ = ∑ _y ∈ C, Metric.externalCoveringNumber σ.toNNReal E := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ y ∈ C, Metric.externalCoveringNumber ε ((fun t => a y * t + b y) '' E) :=
          Finset.sum_le_sum hpiece
      _ ≤ Metric.externalCoveringNumber ε E := hsum
  rw [← ENat.toENNReal_mul]
  exact ENat.toENNReal_le.2 key

theorem lowerBoxDim_coord_eq [Finite ι] [Nonempty ι] (c : ZMod 2) :
    lowerBoxDim (coord c '' S.attractor) = upperBoxDim (coord c '' S.attractor) :=
  le_antisymm (lowerBoxDim_le_upperBoxDim _) (S.upperBoxDim_coord_le_lowerBoxDim c)

theorem projDim_eq_lowerBoxDim [Finite ι] [Nonempty ι] (c : ZMod 2) :
    S.projDim c = (lowerBoxDim (coord c '' S.attractor)).toReal := by
  rw [projDim, S.lowerBoxDim_coord_eq]

noncomputable def wordBase (w : List ι) : ℝ := |S.gDeriv (S.codeWord 0 w)|

noncomputable def wordHeight (w : List ι) : ℝ := |S.gDeriv (S.codeWord 1 w)|

noncomputable def alpha₁ (w : List ι) : ℝ := max (S.wordBase w) (S.wordHeight w)

noncomputable def alpha₂ (w : List ι) : ℝ := min (S.wordBase w) (S.wordHeight w)

noncomputable def wordDim (w : List ι) : ℝ :=
  if S.wordHeight w ≤ S.wordBase w then S.projDim (S.oWord w) else S.projDim (S.oWord w + 1)

noncomputable def modSvf (s : ℝ) (w : List ι) : ℝ :=
  S.alpha₁ w ^ S.wordDim w * S.alpha₂ w ^ (s - S.wordDim w)

theorem wordBase_pos (w : List ι) : 0 < S.wordBase w := abs_pos.2 (S.gDeriv_ne_zero _)

theorem wordHeight_pos (w : List ι) : 0 < S.wordHeight w := abs_pos.2 (S.gDeriv_ne_zero _)

theorem alpha₂_pos (w : List ι) : 0 < S.alpha₂ w := lt_min (S.wordBase_pos w) (S.wordHeight_pos w)

theorem alpha₂_le_alpha₁ (w : List ι) : S.alpha₂ w ≤ S.alpha₁ w := min_le_max

theorem alpha₁_pos (w : List ι) : 0 < S.alpha₁ w := (S.alpha₂_pos w).trans_le (S.alpha₂_le_alpha₁ w)

theorem wordDim_le {D : ℝ} (h : ∀ c, S.projDim c ≤ D) (w : List ι) : S.wordDim w ≤ D := by
  unfold wordDim
  split_ifs <;> exact h _

theorem le_wordDim {D : ℝ} (h : ∀ c, D ≤ S.projDim c) (w : List ι) : D ≤ S.wordDim w := by
  unfold wordDim
  split_ifs <;> exact h _

theorem wordDim_nonneg (w : List ι) : 0 ≤ S.wordDim w := S.le_wordDim S.projDim_nonneg w

theorem modSvf_pos (s : ℝ) (w : List ι) : 0 < S.modSvf s w :=
  mul_pos (Real.rpow_pos_of_pos (S.alpha₁_pos w) _) (Real.rpow_pos_of_pos (S.alpha₂_pos w) _)

theorem modSvf_add (s δ : ℝ) (w : List ι) :
    S.modSvf (s + δ) w = S.alpha₂ w ^ δ * S.modSvf s w := by
  unfold modSvf
  rw [show s + δ - S.wordDim w = δ + (s - S.wordDim w) by ring, Real.rpow_add (S.alpha₂_pos w)]
  ring

theorem one_le_modSvf_zero (w : List ι) : 1 ≤ S.modSvf 0 w := by
  have h := rpow_mul_rpow_sub_mono (S.alpha₂_pos w) (S.alpha₂_le_alpha₁ w) 0 (S.wordDim_nonneg w)
  rw [Real.rpow_zero, sub_zero, Real.rpow_zero, one_mul] at h
  exact h

variable {S} {r M δ₀ : ℝ}

theorem Bounds.alpha₁_le (hS : S.Bounds r M) (w : List ι) : S.alpha₁ w ≤ r ^ w.length := by
  refine max_le ?_ ?_
  · simpa [wordBase] using hS.abs_gDeriv_le (S.codeWord 0 w)
  · simpa [wordHeight] using hS.abs_gDeriv_le (S.codeWord 1 w)

theorem RatioLowerBound.le_alpha₂ (hδ₀ : S.RatioLowerBound δ₀) (w : List ι) :
    δ₀ ^ w.length ≤ S.alpha₂ w := by
  refine le_min ?_ ?_
  · simpa [wordBase] using hδ₀.le_abs_gDeriv (S.codeWord 0 w)
  · simpa [wordHeight] using hδ₀.le_abs_gDeriv (S.codeWord 1 w)

theorem Bounds.modSvf_add_le (hS : S.Bounds r M) (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (w : List ι) :
    S.modSvf (s + δ) w ≤ (r ^ w.length) ^ δ * S.modSvf s w := by
  rw [modSvf_add]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (S.alpha₂_pos w).le
    ((S.alpha₂_le_alpha₁ w).trans (hS.alpha₁_le w)) hδ) (S.modSvf_pos s w).le

theorem RatioLowerBound.le_modSvf_add (hδ₀ : S.RatioLowerBound δ₀) (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (w : List ι) : (δ₀ ^ w.length) ^ δ * S.modSvf s w ≤ S.modSvf (s + δ) w := by
  rw [modSvf_add]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (pow_nonneg hδ₀.1.le _)
    (hδ₀.le_alpha₂ w) hδ) (S.modSvf_pos s w).le

theorem RatioLowerBound.modSvf_zero_le [Finite ι] (hδ₀ : S.RatioLowerBound δ₀)
    (hS : S.Bounds r M) (w : List ι) : S.modSvf 0 w ≤ (δ₀ ^ w.length) ^ (-1 : ℝ) := by
  have hd0 := S.wordDim_nonneg w
  have hd1 := S.wordDim_le S.projDim_le_one w
  have hp : 0 < δ₀ ^ w.length := pow_pos hδ₀.1 _
  have hα₁ : S.alpha₁ w ≤ 1 := (hS.alpha₁_le w).trans (pow_le_one₀ hS.r_nonneg hS.r_lt_one.le)
  have hp1 : δ₀ ^ w.length ≤ 1 := ((hδ₀.le_alpha₂ w).trans (S.alpha₂_le_alpha₁ w)).trans hα₁
  calc S.modSvf 0 w = S.alpha₁ w ^ S.wordDim w * S.alpha₂ w ^ (0 - S.wordDim w) := rfl
    _ ≤ 1 * (δ₀ ^ w.length) ^ (0 - S.wordDim w) :=
        mul_le_mul (Real.rpow_le_one (S.alpha₁_pos w).le hα₁ hd0)
          (Real.rpow_le_rpow_of_nonpos hp (hδ₀.le_alpha₂ w) (by linarith))
          (Real.rpow_nonneg (S.alpha₂_pos w).le _) zero_le_one
    _ ≤ (δ₀ ^ w.length) ^ (-1 : ℝ) := by
        rw [one_mul]
        exact Real.rpow_le_rpow_of_exponent_ge hp hp1 (by linarith)

theorem _root_.FractalGeometry.rpow_swap_le {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) {s p q : ℝ}
    (h : s ≤ p + q) : y ^ q * x ^ (s - q) ≤ x ^ p * y ^ (s - p) := by
  have h' := rpow_mul_rpow_sub_mono hy hyx s (show s - q ≤ p by linarith)
  rwa [sub_sub_cancel, mul_comm] at h'

theorem _root_.FractalGeometry.le_rpow_swap {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) {s p q : ℝ}
    (h : p + q ≤ s) : x ^ p * y ^ (s - p) ≤ y ^ q * x ^ (s - q) := by
  have h' := rpow_mul_rpow_sub_mono hy hyx s (show p ≤ s - q by linarith)
  rwa [sub_sub_cancel, mul_comm (x ^ (s - q))] at h'

variable (S)

noncomputable def side (c : ZMod 2) (w : List ι) : ℝ := |S.gDeriv (S.codeWord c w)|

noncomputable def sideSvf (s : ℝ) (c : ZMod 2) (w : List ι) : ℝ :=
  S.side c w ^ S.projDim (c + S.oWord w) * S.side (c + 1) w ^ (s - S.projDim (c + S.oWord w))

theorem side_pos (c : ZMod 2) (w : List ι) : 0 < S.side c w := abs_pos.2 (S.gDeriv_ne_zero _)

theorem side_append (c : ZMod 2) (w w' : List ι) :
    S.side c (w ++ w') = S.side c w * S.side (c + S.oWord w) w' := by
  rw [side, codeWord_append, gDeriv_append, abs_mul]
  rfl

theorem oWord_eq_zero (h : ∀ i, S.o i = 0) (w : List ι) : S.oWord w = 0 := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [oWord_cons, h, ih, add_zero]

theorem projDim_eq_or_diagonal [Finite ι] :
    (∀ c c', S.projDim c = S.projDim c') ∨ ∀ i, S.o i = 0 := by
  by_cases h : ∃ i, S.o i = 1
  · exact Or.inl (S.projDim_eq h)
  · refine Or.inr fun i => (zmod_two_cases (S.o i)).resolve_right fun hi => h ⟨i, hi⟩

theorem projDim_add_projDim (c : ZMod 2) :
    S.projDim c + S.projDim (c + 1) = S.projDim 0 + S.projDim 1 := by
  rcases zmod_two_cases c with rfl | rfl
  · rw [zero_add]
  · rw [show (1 : ZMod 2) + 1 = 0 from by decide, add_comm]

theorem modSvf_eq_ite (s : ℝ) (w : List ι) :
    S.modSvf s w = if S.wordHeight w ≤ S.wordBase w then S.sideSvf s 0 w else S.sideSvf s 1 w := by
  unfold modSvf wordDim alpha₁ alpha₂ sideSvf
  split_ifs with h
  · rw [max_eq_left h, min_eq_right h, zero_add, zero_add]
    rfl
  · rw [max_eq_right (not_le.1 h).le, min_eq_left (not_le.1 h).le,
      show (1 : ZMod 2) + 1 = 0 from by decide, add_comm 1 (S.oWord w)]
    rfl

theorem modSvf_eq_sideSvf (s : ℝ) (w : List ι) : ∃ c, S.modSvf s w = S.sideSvf s c w := by
  rw [modSvf_eq_ite]
  split_ifs
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩]

theorem sideSvf_le_modSvf {s : ℝ} (hs : s ≤ S.projDim 0 + S.projDim 1) (c : ZMod 2)
    (w : List ι) : S.sideSvf s c w ≤ S.modSvf s w := by
  have hsum := S.projDim_add_projDim (S.oWord w)
  rw [modSvf_eq_ite]
  split_ifs with h
  · rcases zmod_two_cases c with rfl | rfl
    · exact le_rfl
    · have h' := rpow_swap_le (S.wordHeight_pos w) h (s := s) (p := S.projDim (S.oWord w))
        (q := S.projDim (S.oWord w + 1)) (by linarith)
      unfold sideSvf
      rwa [show (1 : ZMod 2) + 1 = 0 from by decide, add_comm 1 (S.oWord w), zero_add]
  · rcases zmod_two_cases c with rfl | rfl
    · have h' := rpow_swap_le (S.wordBase_pos w) (not_le.1 h).le (s := s)
        (p := S.projDim (S.oWord w + 1)) (q := S.projDim (S.oWord w)) (by linarith)
      unfold sideSvf
      rwa [show (1 : ZMod 2) + 1 = 0 from by decide, add_comm 1 (S.oWord w), zero_add]
    · exact le_rfl

theorem modSvf_le_sideSvf {s : ℝ} (hs : S.projDim 0 + S.projDim 1 ≤ s) (c : ZMod 2)
    (w : List ι) : S.modSvf s w ≤ S.sideSvf s c w := by
  have hsum := S.projDim_add_projDim (S.oWord w)
  rw [modSvf_eq_ite]
  split_ifs with h
  · rcases zmod_two_cases c with rfl | rfl
    · exact le_rfl
    · have h' := le_rpow_swap (S.wordHeight_pos w) h (s := s) (p := S.projDim (S.oWord w))
        (q := S.projDim (S.oWord w + 1)) (by linarith)
      unfold sideSvf
      rwa [show (1 : ZMod 2) + 1 = 0 from by decide, add_comm 1 (S.oWord w), zero_add]
  · rcases zmod_two_cases c with rfl | rfl
    · have h' := le_rpow_swap (S.wordBase_pos w) (not_le.1 h).le (s := s)
        (p := S.projDim (S.oWord w + 1)) (q := S.projDim (S.oWord w)) (by linarith)
      unfold sideSvf
      rwa [show (1 : ZMod 2) + 1 = 0 from by decide, add_comm 1 (S.oWord w), zero_add]
    · exact le_rfl

theorem sideSvf_append [Finite ι] (s : ℝ) (c : ZMod 2) (w w' : List ι) :
    S.sideSvf s c (w ++ w') = S.sideSvf s c w * S.sideSvf s (c + S.oWord w) w' := by
  have hd : S.projDim (c + S.oWord w + S.oWord w') = S.projDim (c + S.oWord w) := by
    rcases S.projDim_eq_or_diagonal with h | h
    · exact h _ _
    · rw [S.oWord_eq_zero h w', add_zero]
  unfold sideSvf
  rw [side_append, side_append, oWord_append, ← add_assoc, hd, add_right_comm c 1,
    Real.mul_rpow (S.side_pos _ _).le (S.side_pos _ _).le,
    Real.mul_rpow (S.side_pos _ _).le (S.side_pos _ _).le]
  ring

theorem modSvf_append_le [Finite ι] {s : ℝ} (hs : s ≤ S.projDim 0 + S.projDim 1)
    (w w' : List ι) : S.modSvf s (w ++ w') ≤ S.modSvf s w * S.modSvf s w' := by
  obtain ⟨c, hc⟩ := S.modSvf_eq_sideSvf s (w ++ w')
  rw [hc, sideSvf_append]
  exact mul_le_mul (S.sideSvf_le_modSvf hs _ _) (S.sideSvf_le_modSvf hs _ _)
    (mul_pos (Real.rpow_pos_of_pos (S.side_pos _ _) _)
      (Real.rpow_pos_of_pos (S.side_pos _ _) _)).le (S.modSvf_pos s w).le

theorem le_modSvf_append [Finite ι] {s : ℝ} (hs : S.projDim 0 + S.projDim 1 ≤ s)
    (w w' : List ι) : S.modSvf s w * S.modSvf s w' ≤ S.modSvf s (w ++ w') := by
  obtain ⟨c, hc⟩ := S.modSvf_eq_sideSvf s (w ++ w')
  rw [hc, sideSvf_append]
  exact mul_le_mul (S.modSvf_le_sideSvf hs _ _) (S.modSvf_le_sideSvf hs _ _)
    (S.modSvf_pos s w').le (mul_pos (Real.rpow_pos_of_pos (S.side_pos _ _) _)
      (Real.rpow_pos_of_pos (S.side_pos _ _) _)).le

variable {S}

theorem _root_.FractalGeometry.log_div_le_of_le_rpow_mul {A B ρ δ : ℝ} {n : ℕ} (hn : 0 < n) (hA : 0 < A)
    (hB : 0 < B) (hρ : 0 < ρ) (h : A ≤ (ρ ^ n) ^ δ * B) :
    Real.log A / n ≤ δ * Real.log ρ + Real.log B / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < (ρ ^ n) ^ δ := Real.rpow_pos_of_pos (pow_pos hρ _) _
  have hlog := Real.log_le_log hA h
  rw [Real.log_mul hp.ne' hB.ne', Real.log_rpow (pow_pos hρ _), Real.log_pow] at hlog
  rw [div_le_iff₀ hn', add_mul, div_mul_cancel₀ _ hn'.ne']
  linarith [mul_assoc δ (n : ℝ) (Real.log ρ), mul_right_comm δ (n : ℝ) (Real.log ρ)]

theorem _root_.FractalGeometry.le_log_div_of_rpow_mul_le {A B ρ δ : ℝ} {n : ℕ} (hn : 0 < n)
    (hB : 0 < B) (hρ : 0 < ρ) (h : (ρ ^ n) ^ δ * B ≤ A) :
    δ * Real.log ρ + Real.log B / n ≤ Real.log A / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < (ρ ^ n) ^ δ := Real.rpow_pos_of_pos (pow_pos hρ _) _
  have hlog := Real.log_le_log (mul_pos hp hB) h
  rw [Real.log_mul hp.ne' hB.ne', Real.log_rpow (pow_pos hρ _), Real.log_pow] at hlog
  rw [le_div_iff₀ hn', add_mul, div_mul_cancel₀ _ hn'.ne']
  linarith [mul_assoc δ (n : ℝ) (Real.log ρ), mul_right_comm δ (n : ℝ) (Real.log ρ)]

section Pressure

variable (S) [Fintype ι]

noncomputable def modSvfSum (s : ℝ) (n : ℕ) : ℝ :=
  ∑ w : Fin n → ι, S.modSvf s (List.ofFn w)

noncomputable def modPressure (s : ℝ) : ℝ :=
  limsup (fun n : ℕ => Real.log (S.modSvfSum s n) / n) atTop

theorem modSvfSum_pos [Nonempty ι] (s : ℝ) (n : ℕ) : 0 < S.modSvfSum s n :=
  Finset.sum_pos (fun _ _ => S.modSvf_pos s _) Finset.univ_nonempty

theorem card_pow_le_modSvfSum_zero (n : ℕ) : (Fintype.card ι : ℝ) ^ n ≤ S.modSvfSum 0 n := by
  calc (Fintype.card ι : ℝ) ^ n = ∑ _w : Fin n → ι, (1 : ℝ) := by simp
    _ ≤ S.modSvfSum 0 n := Finset.sum_le_sum fun w _ => S.one_le_modSvf_zero _

variable {S}

theorem Bounds.modSvfSum_exponent_add_le (hS : S.Bounds r M) (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (n : ℕ) : S.modSvfSum (s + δ) n ≤ (r ^ n) ^ δ * S.modSvfSum s n := by
  rw [modSvfSum, modSvfSum, Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  have h := hS.modSvf_add_le s hδ (List.ofFn w)
  rwa [List.length_ofFn] at h

theorem RatioLowerBound.le_modSvfSum_exponent_add (hδ₀ : S.RatioLowerBound δ₀) (s : ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (n : ℕ) : (δ₀ ^ n) ^ δ * S.modSvfSum s n ≤ S.modSvfSum (s + δ) n := by
  rw [modSvfSum, modSvfSum, Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  have h := hδ₀.le_modSvf_add s hδ (List.ofFn w)
  rwa [List.length_ofFn] at h

theorem RatioLowerBound.modSvfSum_zero_le (hδ₀ : S.RatioLowerBound δ₀) (hS : S.Bounds r M)
    (n : ℕ) : S.modSvfSum 0 n ≤ (δ₀ ^ n) ^ (-1 : ℝ) * (Fintype.card ι : ℝ) ^ n := by
  calc S.modSvfSum 0 n ≤ ∑ _w : Fin n → ι, (δ₀ ^ n) ^ (-1 : ℝ) :=
        Finset.sum_le_sum fun w _ => by
          have h := hδ₀.modSvf_zero_le hS (List.ofFn w)
          rwa [List.length_ofFn] at h
    _ = (δ₀ ^ n) ^ (-1 : ℝ) * (Fintype.card ι : ℝ) ^ n := by
        simp [mul_comm]

theorem RatioLowerBound.modLog_bounds [Nonempty ι] (hδ₀ : S.RatioLowerBound δ₀)
    (hS : S.Bounds r M) (hr : 0 < r) {s δ : ℝ} (hs : 0 ≤ s) (hδ : 0 ≤ δ) {n : ℕ} (hn : 0 < n) :
    (δ * Real.log δ₀ + Real.log (S.modSvfSum s n) / n ≤ Real.log (S.modSvfSum (s + δ) n) / n ∧
      Real.log (S.modSvfSum (s + δ) n) / n ≤ δ * Real.log r + Real.log (S.modSvfSum s n) / n) ∧
    s * Real.log δ₀ ≤ Real.log (S.modSvfSum s n) / n ∧
      Real.log (S.modSvfSum s n) / n ≤ Real.log (Fintype.card ι) - Real.log δ₀ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hslope : ∀ s δ : ℝ, 0 ≤ δ →
      δ * Real.log δ₀ + Real.log (S.modSvfSum s n) / n ≤ Real.log (S.modSvfSum (s + δ) n) / n ∧
      Real.log (S.modSvfSum (s + δ) n) / n ≤
        δ * Real.log r + Real.log (S.modSvfSum s n) / n := fun s δ hδ =>
    ⟨le_log_div_of_rpow_mul_le hn (S.modSvfSum_pos s n) hδ₀.1
      (hδ₀.le_modSvfSum_exponent_add s hδ n),
    log_div_le_of_le_rpow_mul hn (S.modSvfSum_pos _ n) (S.modSvfSum_pos s n) hr
      (hS.modSvfSum_exponent_add_le s hδ n)⟩
  have hNn : Real.log ((Fintype.card ι : ℝ) ^ n) / n = Real.log (Fintype.card ι) := by
    rw [Real.log_pow, mul_div_cancel_left₀ _ hn'.ne']
  have h0 : 0 ≤ Real.log (S.modSvfSum 0 n) / n :=
    div_nonneg (Real.log_nonneg ((one_le_pow₀ (by exact_mod_cast Fintype.card_pos)).trans
      (S.card_pow_le_modSvfSum_zero n))) hn'.le
  have h0' : Real.log (S.modSvfSum 0 n) / n ≤ Real.log (Fintype.card ι) - Real.log δ₀ := by
    have h := log_div_le_of_le_rpow_mul hn (S.modSvfSum_pos 0 n) (pow_pos hN n) hδ₀.1
      (hδ₀.modSvfSum_zero_le hS n)
    rw [hNn] at h
    linarith
  have hs' := hslope 0 s hs
  rw [zero_add] at hs'
  have hlogr : Real.log r ≤ 0 := Real.log_nonpos hr.le hS.r_lt_one.le
  refine ⟨hslope s δ hδ, by linarith [hs'.1], ?_⟩
  have := mul_nonpos_of_nonneg_of_nonpos hs hlogr
  linarith [hs'.2]

variable (S)

theorem isBoundedUnder_le_modLog [Nonempty ι] {s : ℝ} (hs : 0 ≤ s) :
    IsBoundedUnder (· ≤ ·) atTop fun n : ℕ => Real.log (S.modSvfSum s n) / n := by
  obtain ⟨δ₀, hδ₀⟩ := S.exists_ratioLowerBound
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  obtain ⟨i⟩ : Nonempty ι := inferInstance
  have hr : 0 < r := hδ₀.1.trans_le ((hδ₀.2 (i, 0)).trans (hS.abs_ratio_le (i, 0)))
  exact isBoundedUnder_of_eventually_le ((eventually_gt_atTop 0).mono fun n hn =>
    (hδ₀.modLog_bounds hS hr hs le_rfl hn).2.2)

theorem isBoundedUnder_ge_modLog [Nonempty ι] {s : ℝ} (hs : 0 ≤ s) :
    IsBoundedUnder (· ≥ ·) atTop fun n : ℕ => Real.log (S.modSvfSum s n) / n := by
  obtain ⟨δ₀, hδ₀⟩ := S.exists_ratioLowerBound
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  obtain ⟨i⟩ : Nonempty ι := inferInstance
  have hr : 0 < r := hδ₀.1.trans_le ((hδ₀.2 (i, 0)).trans (hS.abs_ratio_le (i, 0)))
  exact isBoundedUnder_of_eventually_ge ((eventually_gt_atTop 0).mono fun n hn =>
    (hδ₀.modLog_bounds hS hr hs le_rfl hn).2.1)

theorem modPressure_zero_nonneg [Nonempty ι] : 0 ≤ S.modPressure 0 := by
  refine le_limsup_of_frequently_le (Eventually.frequently (Eventually.of_forall fun n => ?_))
    (S.isBoundedUnder_le_modLog le_rfl)
  exact div_nonneg (Real.log_nonneg ((one_le_pow₀ (by exact_mod_cast Fintype.card_pos)).trans
    (S.card_pow_le_modSvfSum_zero n))) (Nat.cast_nonneg n)

theorem exists_modPressure_slope [Nonempty ι] : ∃ c₁ c₂ : ℝ, c₂ < 0 ∧ ∀ s δ : ℝ, 0 ≤ s → 0 ≤ δ →
    δ * c₁ ≤ S.modPressure (s + δ) - S.modPressure s ∧
      S.modPressure (s + δ) - S.modPressure s ≤ δ * c₂ := by
  obtain ⟨δ₀, hδ₀⟩ := S.exists_ratioLowerBound
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  obtain ⟨i⟩ : Nonempty ι := inferInstance
  have hr : 0 < r := hδ₀.1.trans_le ((hδ₀.2 (i, 0)).trans (hS.abs_ratio_le (i, 0)))
  refine ⟨Real.log δ₀, Real.log r, Real.log_neg hr hS.r_lt_one, fun s δ hs hδ => ?_⟩
  have hsδ : 0 ≤ s + δ := add_nonneg hs hδ
  have hb := S.isBoundedUnder_le_modLog hs
  have hc := (S.isBoundedUnder_ge_modLog hs).isCoboundedUnder_le
  have hbδ := S.isBoundedUnder_le_modLog hsδ
  have hcδ := (S.isBoundedUnder_ge_modLog hsδ).isCoboundedUnder_le
  have hev : ∀ᶠ n : ℕ in atTop,
      δ * Real.log δ₀ + Real.log (S.modSvfSum s n) / n ≤ Real.log (S.modSvfSum (s + δ) n) / n ∧
      Real.log (S.modSvfSum (s + δ) n) / n ≤
        δ * Real.log r + Real.log (S.modSvfSum s n) / n :=
    (eventually_gt_atTop 0).mono fun n hn => (hδ₀.modLog_bounds hS hr hs hδ hn).1
  have hadd : ∀ c : ℝ, limsup (fun n : ℕ => c + Real.log (S.modSvfSum s n) / n) atTop =
      c + S.modPressure s := fun c => limsup_const_add atTop _ c hb hc
  have hbadd : ∀ c : ℝ, IsBoundedUnder (· ≤ ·) atTop
      fun n : ℕ => c + Real.log (S.modSvfSum s n) / n := fun c => by
    obtain ⟨b, hb'⟩ := hb
    exact ⟨c + b, by
      rw [eventually_map] at hb' ⊢
      exact hb'.mono fun n hn => by linarith⟩
  have hcadd : ∀ c : ℝ, IsCoboundedUnder (· ≤ ·) atTop
      fun n : ℕ => c + Real.log (S.modSvfSum s n) / n := fun c => by
    obtain ⟨b, hb'⟩ := S.isBoundedUnder_ge_modLog hs
    refine IsBoundedUnder.isCoboundedUnder_le ⟨c + b, ?_⟩
    rw [eventually_map] at hb' ⊢
    exact hb'.mono fun n hn => by
      have : b ≤ Real.log (S.modSvfSum s n) / n := hn
      show c + b ≤ c + Real.log (S.modSvfSum s n) / n
      linarith
  constructor
  · have h := limsup_le_limsup (hev.mono fun n hn => hn.1) (hcadd _) hbδ
    rw [hadd] at h
    unfold modPressure at h ⊢
    linarith
  · have h := limsup_le_limsup (hev.mono fun n hn => hn.2) hcδ (hbadd _)
    rw [hadd] at h
    unfold modPressure at h ⊢
    linarith

theorem exists_modPressure_increment [Nonempty ι] : ∃ c₁ c₂ : ℝ, c₂ < 0 ∧
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → (t - s) * c₁ ≤ S.modPressure t - S.modPressure s ∧
      S.modPressure t - S.modPressure s ≤ (t - s) * c₂ := by
  obtain ⟨c₁, c₂, hc₂, h⟩ := S.exists_modPressure_slope
  refine ⟨c₁, c₂, hc₂, fun s t hs hst => ?_⟩
  have h' := h s (t - s) hs (sub_nonneg.2 hst)
  rwa [add_sub_cancel] at h'

theorem strictAntiOn_modPressure [Nonempty ι] : StrictAntiOn S.modPressure (Set.Ici 0) := by
  obtain ⟨c₁, c₂, hc₂, h⟩ := S.exists_modPressure_increment
  intro s hs t _ hst
  have h' := (h s t hs hst.le).2
  have hneg : (t - s) * c₂ < 0 := mul_neg_of_pos_of_neg (sub_pos.2 hst) hc₂
  linarith

theorem existsUnique_modPressure_eq_zero [Nonempty ι] :
    ∃! s : ℝ, 0 ≤ s ∧ S.modPressure s = 0 := by
  obtain ⟨c₁, c₂, hc₂, h⟩ := S.exists_modPressure_increment
  exact existsUnique_zero_of_increment hc₂ S.modPressure_zero_nonneg h

noncomputable def dimmaff [Nonempty ι] : ℝ := (S.existsUnique_modPressure_eq_zero).exists.choose

theorem dimmaff_nonneg [Nonempty ι] : 0 ≤ S.dimmaff :=
  (S.existsUnique_modPressure_eq_zero).exists.choose_spec.1

theorem modPressure_dimmaff [Nonempty ι] : S.modPressure S.dimmaff = 0 :=
  (S.existsUnique_modPressure_eq_zero).exists.choose_spec.2

theorem dimmaff_le_of_modPressure_nonpos [Nonempty ι] {s : ℝ} (hs : 0 ≤ s)
    (h : S.modPressure s ≤ 0) : S.dimmaff ≤ s := by
  by_contra hlt
  have hlt' := S.strictAntiOn_modPressure hs S.dimmaff_nonneg (not_le.1 hlt)
  rw [S.modPressure_dimmaff] at hlt'
  linarith

theorem modSvfSum_add_le {s : ℝ} (hs : s ≤ S.projDim 0 + S.projDim 1) (m n : ℕ) :
    S.modSvfSum s (m + n) ≤ S.modSvfSum s m * S.modSvfSum s n := by
  rw [modSvfSum, sum_ofFn_add m n fun w => S.modSvf s w, modSvfSum, modSvfSum,
    Finset.sum_mul_sum]
  exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => S.modSvf_append_le hs _ _

theorem le_modSvfSum_add {s : ℝ} (hs : S.projDim 0 + S.projDim 1 ≤ s) (m n : ℕ) :
    S.modSvfSum s m * S.modSvfSum s n ≤ S.modSvfSum s (m + n) := by
  have hsplit : S.modSvfSum s (m + n) =
      ∑ g : Fin m → ι, ∑ h : Fin n → ι, S.modSvf s (List.ofFn g ++ List.ofFn h) :=
    sum_ofFn_add m n fun w => S.modSvf s w
  rw [hsplit, modSvfSum, modSvfSum, Finset.sum_mul_sum]
  exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => S.le_modSvf_append hs _ _

theorem tendsto_modPressure [Nonempty ι] {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun n : ℕ => Real.log (S.modSvfSum s n) / n) atTop (𝓝 (S.modPressure s)) := by
  suffices ∃ L, Tendsto (fun n : ℕ => Real.log (S.modSvfSum s n) / n) atTop (𝓝 L) by
    obtain ⟨L, hL⟩ := this
    rwa [modPressure, hL.limsup_eq]
  obtain ⟨δ₀, hδ₀⟩ := S.exists_ratioLowerBound
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  obtain ⟨i⟩ : Nonempty ι := inferInstance
  have hr : 0 < r := hδ₀.1.trans_le ((hδ₀.2 (i, 0)).trans (hS.abs_ratio_le (i, 0)))
  have hpos := fun n => S.modSvfSum_pos s n
  rcases le_total s (S.projDim 0 + S.projDim 1) with hst | hst
  · have hsub : Subadditive fun n => Real.log (S.modSvfSum s n) := fun m n => by
      rw [← Real.log_mul (hpos m).ne' (hpos n).ne']
      exact Real.log_le_log (hpos _) (S.modSvfSum_add_le hst m n)
    have hbdd : BddBelow (Set.range fun n : ℕ => Real.log (S.modSvfSum s n) / n) := by
      refine ⟨min 0 (s * Real.log δ₀), ?_⟩
      rintro _ ⟨n, rfl⟩
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · exact (min_le_right _ _).trans (hδ₀.modLog_bounds hS hr hs le_rfl hn).2.1
    exact ⟨_, hsub.tendsto_lim hbdd⟩
  · have hsub : Subadditive fun n => -Real.log (S.modSvfSum s n) := fun m n => by
      rw [← neg_add, neg_le_neg_iff, ← Real.log_mul (hpos m).ne' (hpos n).ne']
      exact Real.log_le_log (mul_pos (hpos m) (hpos n)) (S.le_modSvfSum_add hst m n)
    have hbdd : BddBelow (Set.range fun n : ℕ => -Real.log (S.modSvfSum s n) / n) := by
      refine ⟨min 0 (-(Real.log (Fintype.card ι) - Real.log δ₀)), ?_⟩
      rintro _ ⟨n, rfl⟩
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · refine (min_le_right _ _).trans ?_
        show -(Real.log (Fintype.card ι) - Real.log δ₀) ≤ -Real.log (S.modSvfSum s n) / n
        rw [neg_div, neg_le_neg_iff]
        exact (hδ₀.modLog_bounds hS hr hs le_rfl hn).2.2
    refine ⟨-hsub.lim, ((hsub.tendsto_lim hbdd).neg).congr fun n => ?_⟩
    rw [neg_div, neg_neg]

end Pressure

end RectangularIFS

end FractalGeometry
