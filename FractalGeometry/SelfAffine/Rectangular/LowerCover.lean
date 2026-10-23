import Mathlib
import GeometricMeasureTheory.Box.ModifiedBox
import FractalGeometry.Dimension.BoxTools
import FractalGeometry.LinearCocycles.Monomial
import FractalGeometry.SelfAffine.Rectangular.Attractor
import FractalGeometry.SelfAffine.Rectangular.Coding
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.SelfAffine.Rectangular.ModifiedPressure
import FractalGeometry.SelfAffine.Rectangular.OpenSet
import FractalGeometry.SelfAffine.Rectangular.RectangularOpenSet
import FractalGeometry.SelfAffine.Rectangular.SingularValues
import FractalGeometry.SelfAffine.Rectangular.Stopping
import FractalGeometry.SelfAffine.Rectangular.StoppingSum
import GeometricMeasureTheory.Box.BoxDimension
import GeometricMeasureTheory.Box.CoveringNumbers

open GeometricMeasureTheory

namespace FractalGeometry

open Filter Topology MeasureTheory Set

open scoped ENNReal NNReal

universe u

namespace FraserLower

theorem le_rpow_of_scale {δ₀ δ a e : ℝ} (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1) (ha : 0 < a)
    (hlt : a < δ) (hle : δ₀ * δ ≤ a) (he : -1 ≤ e) : δ₀ * a ^ e ≤ δ ^ e := by
  rcases le_total 0 e with he0 | he0
  · exact (mul_le_of_le_one_left (Real.rpow_nonneg ha.le _) hδ₀1).trans
      (Real.rpow_le_rpow ha.le hlt.le he0)
  · have hδ : 0 < δ := ha.trans hlt
    have hδa : δ ≤ a / δ₀ := by rw [le_div_iff₀ hδ₀, mul_comm]; exact hle
    have h1 : (a / δ₀) ^ e ≤ δ ^ e := Real.rpow_le_rpow_of_nonpos hδ hδa he0
    have h2 : δ₀ ≤ δ₀ ^ (-e) := by
      calc δ₀ = δ₀ ^ (1 : ℝ) := (Real.rpow_one δ₀).symm
        _ ≤ δ₀ ^ (-e) := Real.rpow_le_rpow_of_exponent_ge hδ₀ hδ₀1 (by linarith)
    calc δ₀ * a ^ e ≤ δ₀ ^ (-e) * a ^ e :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg ha.le _)
      _ = (a / δ₀) ^ e := by
          rw [Real.div_rpow ha.le hδ₀.le, Real.rpow_neg hδ₀.le, div_eq_mul_inv, mul_comm]
      _ ≤ δ ^ e := h1

theorem le_rpow_div {δ₀ δ α₁ α₂ s t η : ℝ} (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ 1) (hα₂ : 0 < α₂)
    (h21 : α₂ ≤ α₁) (hα₁ : α₁ ≤ 1) (hlt : α₂ < δ) (hle : δ₀ * δ ≤ α₂)
    (hs1 : s ≤ 1) (ht : 0 ≤ t) (hη : 0 ≤ η) :
    δ₀ * δ ^ (-(t - η)) * (α₁ ^ s * α₂ ^ (t - s)) ≤ (δ / α₁) ^ (-(s - η)) := by
  have hδ : 0 < δ := hα₂.trans hlt
  have hα₁0 : 0 < α₁ := hα₂.trans_le h21
  have hsplit : (δ / α₁) ^ (-(s - η)) = δ ^ (-(t - η)) * δ ^ (t - s) * α₁ ^ (s - η) := by
    rw [Real.div_rpow hδ.le hα₁0.le, ← Real.rpow_add hδ, Real.rpow_neg hα₁0.le, div_inv_eq_mul]
    congr 2
    ring
  have h1 : δ₀ * α₂ ^ (t - s) ≤ δ ^ (t - s) :=
    le_rpow_of_scale hδ₀ hδ₀1 hα₂ hlt hle (by linarith)
  have h2 : α₁ ^ s ≤ α₁ ^ (s - η) := Real.rpow_le_rpow_of_exponent_ge hα₁0 hα₁ (by linarith)
  rw [hsplit]
  have hδp : 0 ≤ δ ^ (-(t - η)) := Real.rpow_nonneg hδ.le _
  calc δ₀ * δ ^ (-(t - η)) * (α₁ ^ s * α₂ ^ (t - s))
      = δ ^ (-(t - η)) * (δ₀ * α₂ ^ (t - s)) * α₁ ^ s := by ring
    _ ≤ δ ^ (-(t - η)) * δ ^ (t - s) * α₁ ^ (s - η) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hδp) h2 (Real.rpow_nonneg hα₁0.le _)
          (mul_nonneg hδp (Real.rpow_nonneg hδ.le _))

theorem exists_Ioo_affine {A B lo hi x m : ℝ} (hA : A ≠ 0) (hlo : lo ≤ x) (hhi : x ≤ hi)
    (hm : 0 < m) (hml : m ≤ |A| * (hi - lo)) :
    ∃ α : ℝ, ∀ y ∈ Ioo α (α + m), |y - (A * x + B)| < m ∧ (y - B) / A ∈ Ioo lo hi := by
  have hA' : 0 < |A| := abs_pos.2 hA
  set μ := m / |A| with hμdef
  have hμ : 0 < μ := div_pos hm hA'
  have hμle : μ ≤ hi - lo := by rw [hμdef, div_le_iff₀ hA', mul_comm]; exact hml
  have hAμ : |A| * μ = m := by rw [hμdef]; field_simp
  set κ := max lo (x - μ) with hκ
  have hκ1 : lo ≤ κ := le_max_left _ _
  have hκ2 : x - μ ≤ κ := le_max_right _ _
  have hκ3 : κ + μ ≤ hi := by
    have : κ ≤ hi - μ := max_le (by linarith) (by linarith)
    linarith
  have hκ4 : κ ≤ x := max_le hlo (by linarith)
  have key : ∀ k : ℝ, κ < k → k < κ + μ → |A * k - A * x| < m ∧ k ∈ Ioo lo hi := by
    intro k hk1 hk2
    refine ⟨?_, ⟨by linarith, by linarith⟩⟩
    rw [← mul_sub, abs_mul, ← hAμ]
    refine mul_lt_mul_of_pos_left ?_ hA'
    rw [abs_lt]
    constructor <;> linarith
  rcases lt_or_gt_of_ne hA with hneg | hpos
  · have hAμ' : A * μ = -m := by rw [← hAμ, abs_of_neg hneg]; ring
    refine ⟨A * (κ + μ) + B, fun y hy => ?_⟩
    have hk1 : κ < (y - B) / A := by
      rw [lt_div_iff_of_neg hneg]
      nlinarith [hy.2]
    have hk2 : (y - B) / A < κ + μ := by
      rw [div_lt_iff_of_neg hneg]
      linarith [hy.1]
    obtain ⟨h1, h2⟩ := key _ hk1 hk2
    refine ⟨?_, h2⟩
    rwa [mul_div_cancel₀ _ hA, show y - B - A * x = y - (A * x + B) by ring] at h1
  · have hAμ' : A * μ = m := by rw [← hAμ, abs_of_pos hpos]
    refine ⟨A * κ + B, fun y hy => ?_⟩
    have hk1 : κ < (y - B) / A := by
      rw [lt_div_iff₀ hpos]
      linarith [hy.1]
    have hk2 : (y - B) / A < κ + μ := by
      rw [div_lt_iff₀ hpos]
      nlinarith [hy.2]
    obtain ⟨h1, h2⟩ := key _ hk1 hk2
    refine ⟨?_, h2⟩
    rwa [mul_div_cancel₀ _ hA, show y - B - A * x = y - (A * x + B) by ring] at h1

theorem exists_le_externalCoveringNumber {X : Type*} [PseudoMetricSpace X] {E : Set X}
    (hne : E.Nonempty) {d R : ℝ} (hR : 0 < R)
    (hd : ENNReal.ofReal d < lowerBoxDim E ∨ d ≤ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      ENNReal.ofReal (C * ρ ^ (-d)) ≤ Metric.externalCoveringNumber ρ.toNNReal E := by
  have h1 : ∀ ρ : ℝ, (1 : ℝ≥0∞) ≤ Metric.externalCoveringNumber ρ.toNNReal E := fun ρ => by
    have h : (1 : ℕ∞) ≤ Metric.externalCoveringNumber ρ.toNNReal E :=
      Order.one_le_iff_pos.2 (Metric.externalCoveringNumber_pos_iff.2 hne)
    exact_mod_cast ENat.toENNReal_le.2 h
  by_cases hd0 : d ≤ 0
  · refine ⟨R ^ d, Real.rpow_pos_of_pos hR d, fun ρ hρ hρR => le_trans ?_ (h1 ρ)⟩
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    calc R ^ d * ρ ^ (-d) ≤ R ^ d * R ^ (-d) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hρ.le hρR (by linarith)) (Real.rpow_nonneg hR.le _)
      _ = 1 := by rw [← Real.rpow_add hR]; simp
  have hd0' : 0 < d := not_le.1 hd0
  have hd' : ENNReal.ofReal d < lowerBoxDim E := hd.resolve_right hd0
  have hnot : ¬ LowerBoxDimLE E (d.toNNReal : ℝ) := fun h =>
    absurd (lowerBoxDim_le_of_lowerBoxDimLE h) (not_le.2 hd')
  have hev : ∀ᶠ ρ : ℝ in 𝓝[>] 0,
      ENNReal.ofReal (ρ ^ (-d)) < Metric.externalCoveringNumber ρ.toNNReal E := by
    unfold LowerBoxDimLE at hnot
    rw [Filter.not_frequently] at hnot
    filter_upwards [hnot] with ρ hρ
    rw [Real.coe_toNNReal _ hd0'.le] at hρ
    exact not_le.1 hρ
  obtain ⟨ε, hε, hεsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hε0 : 0 < ε := hε
  refine ⟨min 1 (ε ^ d), lt_min one_pos (Real.rpow_pos_of_pos hε0 d), fun ρ hρ _ => ?_⟩
  by_cases hρε : ρ < ε
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hεsub ⟨hρ, hρε⟩).le
    exact mul_le_of_le_one_left (Real.rpow_nonneg hρ.le _) (min_le_left _ _)
  · refine le_trans ?_ (h1 ρ)
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    calc min 1 (ε ^ d) * ρ ^ (-d) ≤ ε ^ d * ε ^ (-d) :=
          mul_le_mul (min_le_right _ _)
            (Real.rpow_le_rpow_of_nonpos hε0 (not_lt.1 hρε) (by linarith))
            (Real.rpow_nonneg hρ.le _) (Real.rpow_nonneg hε0.le _)
      _ = 1 := by rw [← Real.rpow_add hε0]; simp

end FraserLower

namespace RectangularIFS

variable {ι : Type*} (S : RectangularIFS ι)

theorem fraserContinuous_phiWord (w : List ι) : Continuous (S.phiWord w) := by
  induction w with
  | nil => exact continuous_id
  | cons i w ih => rw [phiWord_cons]; exact (S.continuous_phi i).comp ih

theorem fraserInjective_phiWord (w : List ι) : Function.Injective (S.phiWord w) := by
  induction w with
  | nil => exact Function.injective_id
  | cons i w ih => rw [phiWord_cons]; exact (S.injective_phi i).comp ih

theorem fraser_coord_mk (o : ZMod 2) (f : ZMod 2 → ℝ) (e : ZMod 2) :
    coord (e + o) (f (0 + o), f (1 + o)) = f e ∧ coord e (f (0 + o), f (1 + o)) = f (e + o) := by
  rcases zmod_two_cases o with rfl | rfl <;> rcases zmod_two_cases e with rfl | rfl <;>
    exact ⟨rfl, rfl⟩

theorem fraser_mem_rect_iff {a b c d : ℝ} (z : ℝ × ℝ) :
    z ∈ Ioo a b ×ˢ Ioo c d ↔
      ∀ e : ZMod 2, coord e z ∈ Ioo (if e = 0 then a else c) (if e = 0 then b else d) := by
  refine ⟨fun h e => ?_, fun h => ⟨h 0, h 1⟩⟩
  rcases zmod_two_cases e with rfl | rfl
  exacts [h.1, h.2]

theorem fraserAttractor_subset [Finite ι] {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hsub : ∀ i, S.phi i '' (Ioo a b ×ˢ Ioo c d) ⊆ Ioo a b ×ˢ Ioo c d) :
    S.attractor ⊆ Icc a b ×ˢ Icc c d := by
  have hcl : closure (Ioo a b ×ˢ Ioo c d) = Icc a b ×ˢ Icc c d := by
    rw [closure_prod_eq, closure_Ioo hab.ne, closure_Ioo hcd.ne]
  refine S.attractor_subset_of_invariant (isCompact_Icc.prod isCompact_Icc)
    ⟨(a, c), left_mem_Icc.2 hab.le, left_mem_Icc.2 hcd.le⟩ fun i => ?_
  rw [← hcl]
  exact (image_closure_subset_closure_image (S.continuous_phi i)).trans (closure_mono (hsub i))

theorem fraser_volume_le (lo hi : ZMod 2 → ℝ) (w : List ι) {x : ℝ × ℝ}
    (hx : ∀ e, coord e x ∈ Icc (lo e) (hi e)) {m : ℝ} (hm : 0 < m)
    (hml : ∀ e, m ≤ S.side e w * (hi (e + S.oWord w) - lo (e + S.oWord w))) :
    ENNReal.ofReal m * ENNReal.ofReal m ≤
      volume (S.phiWord w '' {z | ∀ e, coord e z ∈ Ioo (lo e) (hi e)} ∩
        Metric.ball (S.phiWord w x) m) := by
  have h1d : ∀ e : ZMod 2, ∃ α : ℝ, ∀ y ∈ Ioo α (α + m),
      |y - (S.gDeriv (S.codeWord e w) * coord (e + S.oWord w) x +
        S.gWord (S.codeWord e w) 0)| < m ∧
      (y - S.gWord (S.codeWord e w) 0) / S.gDeriv (S.codeWord e w) ∈
        Ioo (lo (e + S.oWord w)) (hi (e + S.oWord w)) :=
    fun e => FraserLower.exists_Ioo_affine (S.gDeriv_ne_zero _) (hx _).1 (hx _).2 hm (hml e)
  choose α hα using h1d
  have hpx : ∀ e, coord e (S.phiWord w x) = S.gDeriv (S.codeWord e w) *
      coord (e + S.oWord w) x + S.gWord (S.codeWord e w) 0 := fun e => by
    rw [coord_phiWord, gWord_apply]
  have hsub : Ioo (α 0) (α 0 + m) ×ˢ Ioo (α 1) (α 1 + m) ⊆
      S.phiWord w '' {z | ∀ e, coord e z ∈ Ioo (lo e) (hi e)} ∩
        Metric.ball (S.phiWord w x) m := by
    rintro y ⟨hy0, hy1⟩
    have hy : ∀ e, coord e y ∈ Ioo (α e) (α e + m) := fun e => by
      rcases zmod_two_cases e with rfl | rfl
      exacts [hy0, hy1]
    set P : ZMod 2 → ℝ := fun e =>
      (coord e y - S.gWord (S.codeWord e w) 0) / S.gDeriv (S.codeWord e w) with hP
    refine ⟨⟨(P (0 + S.oWord w), P (1 + S.oWord w)), fun σ => ?_, ?_⟩, ?_⟩
    · rw [(fraser_coord_mk (S.oWord w) P σ).2]
      have h := (hα (σ + S.oWord w) _ (hy _)).2
      have hσ : σ + S.oWord w + S.oWord w = σ := by
        rcases zmod_two_cases (S.oWord w) with h0 | h0 <;> rw [h0] <;>
          rcases zmod_two_cases σ with rfl | rfl <;> rfl
      rwa [hσ] at h
    · have hc : ∀ e, coord e (S.phiWord w (P (0 + S.oWord w), P (1 + S.oWord w))) =
          coord e y := by
        intro e
        rw [coord_phiWord, gWord_apply, (fraser_coord_mk (S.oWord w) P e).1, hP]
        field_simp [S.gDeriv_ne_zero (S.codeWord e w)]
        ring
      exact Prod.ext (hc 0) (hc 1)
    · rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      refine max_lt ?_ ?_
      · have h := (hα 0 _ (hy 0)).1
        rw [← hpx 0] at h
        exact h
      · have h := (hα 1 _ (hy 1)).1
        rw [← hpx 1] at h
        exact h
  calc ENNReal.ofReal m * ENNReal.ofReal m
      = volume (Ioo (α 0) (α 0 + m) ×ˢ Ioo (α 1) (α 1 + m)) := by
        rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo,
          add_sub_cancel_left, add_sub_cancel_left]
    _ ≤ _ := measure_mono hsub

theorem fraser_sum_volume_le [Fintype ι] {R : Set (ℝ × ℝ)} (hRo : IsOpen R)
    (hsub : ∀ i, S.phi i '' R ⊆ R)
    (hdisj : Pairwise fun i j => Disjoint (S.phi i '' R) (S.phi j '' R))
    {B : Set (ℝ × ℝ)} (hB : MeasurableSet B) (hBf : volume B ≠ ∞) (u : List ι) :
    ∑ j, (volume (S.phiWord (u ++ [j]) '' R ∩ B)).toReal ≤
      (volume (S.phiWord u '' R ∩ B)).toReal := by
  have hset : ∀ j, S.phiWord (u ++ [j]) '' R = S.phiWord u '' (S.phi j '' R) := fun j => by
    rw [phiWord_append, Set.image_comp]
    simp
  have hmeas : ∀ w : List ι, MeasurableSet (S.phiWord w '' R) := fun w =>
    hRo.measurableSet.image_of_continuousOn_injOn (S.fraserContinuous_phiWord w).continuousOn
      (S.fraserInjective_phiWord w).injOn
  have hfin : ∀ w, volume (S.phiWord w '' R ∩ B) ≠ ∞ := fun w =>
    ne_top_of_le_ne_top hBf (measure_mono inter_subset_right)
  rw [← ENNReal.toReal_sum fun j _ => hfin _]
  refine ENNReal.toReal_mono (hfin u) ?_
  rw [← measure_biUnion_finset (s := Finset.univ) ?_ fun j _ => (hmeas _).inter hB]
  · refine measure_mono (iUnion₂_subset fun j _ => ?_)
    rw [hset j]
    exact inter_subset_inter_left _ (image_mono (hsub j))
  · intro j _ j' _ hjj'
    rw [Function.onFun, hset j, hset j']
    exact ((Set.disjoint_image_iff (S.fraserInjective_phiWord u)).2 (hdisj hjj')).mono
      inter_subset_left inter_subset_left

open Classical in

theorem fraserStopSum_meets_le [Fintype ι] [Nonempty ι] {a b c d δ₀ δ : ℝ} (hab : a < b)
    (hcd : c < d) (hsub : ∀ i, S.phi i '' (Ioo a b ×ˢ Ioo c d) ⊆ Ioo a b ×ˢ Ioo c d)
    (hdisj : Pairwise fun i j =>
      Disjoint (S.phi i '' (Ioo a b ×ˢ Ioo c d)) (S.phi j '' (Ioo a b ×ˢ Ioo c d)))
    (hδ₀ : S.RatioLowerBound δ₀) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (k : ℕ) (z : ℝ × ℝ) :
    S.fraserStopSum δ
        (fun w => if (S.phiWord w '' S.attractor ∩ Metric.closedBall z δ).Nonempty then 1 else 0)
        k [] ≤
      (2 * (1 + δ₀ * min (b - a) (d - c)) / (δ₀ * min (b - a) (d - c))) ^ 2 := by
  set ρ₀ := min (b - a) (d - c) with hρdef
  have hρ : 0 < ρ₀ := lt_min (by linarith) (by linarith)
  set κ := δ₀ * ρ₀ with hκ
  have hκ0 : 0 < κ := mul_pos hδ₀.1 hρ
  set m := κ * δ with hmdef
  have hm : 0 < m := mul_pos hκ0 hδ
  set lo : ZMod 2 → ℝ := fun e => if e = 0 then a else c with hlo
  set hi : ZMod 2 → ℝ := fun e => if e = 0 then b else d with hhi
  have hbox : {z : ℝ × ℝ | ∀ e, coord e z ∈ Ioo (lo e) (hi e)} = Ioo a b ×ˢ Ioo c d := by
    ext z
    exact (fraser_mem_rect_iff z).symm
  have hX : ∀ x ∈ S.attractor, ∀ e, coord e x ∈ Icc (lo e) (hi e) := fun x hx e => by
    have h := S.fraserAttractor_subset hab hcd hsub hx
    rcases zmod_two_cases e with rfl | rfl
    exacts [h.1, h.2]
  have hlen : ∀ e, ρ₀ ≤ hi e - lo e := fun e => by
    rcases zmod_two_cases e with rfl | rfl
    · exact min_le_left _ _
    · exact min_le_right _ _
  set B := Metric.ball z (δ + m) with hBdef
  have hBvol : volume B = ENNReal.ofReal (2 * (δ + m)) * ENNReal.ofReal (2 * (δ + m)) := by
    have h := ball_prod_same z.1 z.2 (δ + m)
    rw [Prod.mk.eta] at h
    rw [hBdef, ← h, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_ball,
      Real.volume_ball]
  have hBf : volume B ≠ ∞ := measure_ball_lt_top.ne
  set g : List ι → ℝ := fun w => (volume (S.phiWord w '' (Ioo a b ×ˢ Ioo c d) ∩ B)).toReal
    with hg
  have hfin : ∀ w, volume (S.phiWord w '' (Ioo a b ×ˢ Ioo c d) ∩ B) ≠ ∞ := fun w =>
    ne_top_of_le_ne_top hBf (measure_mono inter_subset_right)
  have hroot : δ ≤ S.alpha₂ [] := by rw [alpha₂_nil]; exact hδ1
  have h1 : S.fraserStopSum δ (fun w => m * m *
      (if (S.phiWord w '' S.attractor ∩ Metric.closedBall z δ).Nonempty then 1 else 0)) k [] ≤
      S.fraserStopSum δ g k [] := by
    refine fraserStopSum_mono (fun u j hu _ => ?_) k [] hroot
    by_cases hmeet : (S.phiWord (u ++ [j]) '' S.attractor ∩ Metric.closedBall z δ).Nonempty
    · simp only [hmeet, ite_true, mul_one]
      obtain ⟨p, ⟨x, hxX, rfl⟩, hpz⟩ := hmeet
      have hα₂ : δ₀ * δ ≤ S.alpha₂ (u ++ [j]) :=
        (mul_le_mul_of_nonneg_left hu hδ₀.1.le).trans (hδ₀.alpha₂_append_ge u j)
      have hml : ∀ e, m ≤ S.side e (u ++ [j]) *
          (hi (e + S.oWord (u ++ [j])) - lo (e + S.oWord (u ++ [j]))) := fun e => by
        have hside : S.alpha₂ (u ++ [j]) ≤ S.side e (u ++ [j]) := by
          rcases zmod_two_cases e with rfl | rfl
          · exact min_le_left _ _
          · exact min_le_right _ _
        calc m = δ₀ * δ * ρ₀ := by rw [hmdef, hκ]; ring
          _ ≤ S.side e (u ++ [j]) *
              (hi (e + S.oWord (u ++ [j])) - lo (e + S.oWord (u ++ [j]))) :=
            mul_le_mul (hα₂.trans hside) (hlen _) hρ.le (S.side_pos _ _).le
      have hv := S.fraser_volume_le lo hi (u ++ [j]) (hX x hxX) hm hml
      rw [hbox] at hv
      have hball : Metric.ball (S.phiWord (u ++ [j]) x) m ⊆ B := fun y hy => by
        rw [Metric.mem_ball] at hy ⊢
        rw [Metric.mem_closedBall] at hpz
        calc dist y z ≤ dist y (S.phiWord (u ++ [j]) x) + dist (S.phiWord (u ++ [j]) x) z :=
              dist_triangle _ _ _
          _ < m + δ := add_lt_add_of_lt_of_le hy hpz
          _ = δ + m := add_comm _ _
      have hv' := hv.trans (measure_mono (inter_subset_inter_right _ hball))
      calc m * m = (ENNReal.ofReal m * ENNReal.ofReal m).toReal := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hm.le]
        _ ≤ g (u ++ [j]) := ENNReal.toReal_mono (hfin _) hv'
    · simp only [hmeet, ite_false, mul_zero]
      exact ENNReal.toReal_nonneg
  have h2 : S.fraserStopSum δ g k [] ≤ g [] :=
    fraserStopSum_le (fun w => ENNReal.toReal_nonneg)
      (fun u _ => S.fraser_sum_volume_le (isOpen_Ioo.prod isOpen_Ioo) hsub hdisj
        Metric.isOpen_ball.measurableSet hBf u) k [] hroot
  have h3 : g [] ≤ (2 * (δ + m)) * (2 * (δ + m)) := by
    have h := ENNReal.toReal_mono hBf (measure_mono (s := S.phiWord [] '' (Ioo a b ×ˢ Ioo c d) ∩ B)
      inter_subset_right)
    rw [hBvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h
    exact h
  rw [S.fraserStopSum_const_mul] at h1
  have hM : (2 * (1 + κ) / κ) ^ 2 = (2 * (δ + m)) * (2 * (δ + m)) / (m * m) := by
    rw [hmdef]
    field_simp
  rw [hM, le_div_iff₀ (mul_pos hm hm), mul_comm]
  linarith

theorem fraser_coveringNumber_le (w : List ι) (c : ZMod 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (E : Set (ℝ × ℝ)) :
    Metric.externalCoveringNumber (δ / S.side c w).toNNReal (coord (c + S.oWord w) '' E) ≤
      Metric.externalCoveringNumber δ.toNNReal (S.phiWord w '' E) := by
  set A := S.gDeriv (S.codeWord c w) with hAdef
  set B := S.gWord (S.codeWord c w) 0 with hBdef
  have hA : A ≠ 0 := S.gDeriv_ne_zero _
  have hlip : LipschitzWith ‖A⁻¹‖₊ fun y : ℝ × ℝ => A⁻¹ * (coord c y - B) :=
    LipschitzWith.of_dist_le_mul fun y y' => by
      have h : A⁻¹ * (coord c y - B) - A⁻¹ * (coord c y' - B) =
          A⁻¹ * (coord c y - coord c y') := by ring
      rw [Real.dist_eq, h, abs_mul, coe_nnnorm, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (abs_coord_sub_le c y y') (abs_nonneg _)
  have himg : (fun y : ℝ × ℝ => A⁻¹ * (coord c y - B)) '' (S.phiWord w '' E) =
      coord (c + S.oWord w) '' E := by
    rw [Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [coord_phiWord, gWord_apply]
    field_simp
    ring
  have h := externalCoveringNumber_image_le_of_lipschitzWith hlip δ.toNNReal (S.phiWord w '' E)
  rw [himg] at h
  have hK : ‖A⁻¹‖₊ * δ.toNNReal = (δ / S.side c w).toNNReal := by
    ext
    rw [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal _ hδ,
      Real.coe_toNNReal _ (div_nonneg hδ (S.side_pos c w).le), abs_inv, side, ← hAdef,
      div_eq_inv_mul]
  rwa [hK] at h

theorem fraser_exists_axis (w : List ι) :
    ∃ e : ZMod 2, S.side e w = S.alpha₁ w ∧ S.projDim (e + S.oWord w) = S.wordDim w := by
  by_cases h : S.wordHeight w ≤ S.wordBase w
  · refine ⟨0, (max_eq_left h).symm, ?_⟩
    simp only [wordDim, h, ite_true, zero_add]
  · refine ⟨1, (max_eq_right (not_le.1 h).le).symm, ?_⟩
    simp only [wordDim, h, ite_false, add_comm]

end RectangularIFS

namespace RectangularIFS

variable {ι : Type u} [Fintype ι] [Nonempty ι] (S : RectangularIFS ι)

theorem dimmaff_le_lowerBoxDim (h : S.RectangularOpenSet) :
    ENNReal.ofReal S.dimmaff ≤ lowerBoxDim S.attractor := by
  classical
  obtain ⟨a, b, c, d, hab, hcd, hsub, hdisj⟩ := h
  obtain ⟨δ₀, hδ₀⟩ := S.exists_ratioLowerBound
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  obtain ⟨i₀⟩ : Nonempty ι := inferInstance
  have hδ₀1 : δ₀ ≤ 1 := (hδ₀.2 (i₀, 0)).trans (S.abs_ratio_lt_one _).le
  refine ENNReal.le_of_forall_nnreal_lt fun q hq => ?_
  have hq' : (q : ℝ) < S.dimmaff := by
    rw [← ENNReal.ofReal_coe_nnreal] at hq
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg q.coe_nonneg).1 hq
  set t := ((q : ℝ) + S.dimmaff) / 2 with ht
  set η := t - q with hη
  have hη0 : 0 < η := by rw [hη, ht]; linarith
  have ht0 : 0 ≤ t := by rw [ht]; linarith [q.coe_nonneg]
  have htd : t < S.dimmaff := by rw [ht]; linarith
  obtain ⟨L, hL, hLδ⟩ := S.exists_le_fraserStopSum hS ht0 htd
  have hproj : ∀ e : ZMod 2, ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ₀⁻¹ →
      ENNReal.ofReal (C * ρ ^ (-(S.projDim e - η))) ≤
        Metric.externalCoveringNumber ρ.toNNReal (coord e '' S.attractor) := by
    intro e
    refine FraserLower.exists_le_externalCoveringNumber (S.attractor_nonempty.image _)
      (inv_pos.2 hδ₀.1) ?_
    by_cases h0 : S.projDim e - η ≤ 0
    · exact Or.inr h0
    · left
      have hLe : lowerBoxDim (coord e '' S.attractor) = ENNReal.ofReal (S.projDim e) := by
        rw [S.projDim_eq_lowerBoxDim e, ENNReal.ofReal_toReal]
        exact (((lowerBoxDim_le_upperBoxDim _).trans (S.upperBoxDim_coord_le_one e)).trans_lt
          ENNReal.one_lt_top).ne
      rw [hLe]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [S.projDim_nonneg e])).2 (by linarith)
  choose C hC0 hC using hproj
  set C₀ := min (C 0) (C 1) with hC₀def
  have hC₀ : 0 < C₀ := lt_min (hC0 0) (hC0 1)
  have hC₀le : ∀ e, C₀ ≤ C e := fun e => by
    rcases zmod_two_cases e with rfl | rfl
    exacts [min_le_left _ _, min_le_right _ _]
  set M₂ := (2 * (1 + δ₀ * min (b - a) (d - c)) / (δ₀ * min (b - a) (d - c))) ^ 2 with hM₂def
  have hρ : 0 < min (b - a) (d - c) := lt_min (by linarith) (by linarith)
  have hM₂ : 0 < M₂ := by
    have := hδ₀.1
    positivity
  refine le_lowerBoxDim_of_forall (C := (C₀ * δ₀ * L / M₂).toNNReal)
    (Real.toNNReal_pos.2 (by have := hδ₀.1; positivity)) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with δ hδ
  obtain ⟨hδ0, hδ1⟩ := hδ
  have hNfin : Metric.externalCoveringNumber δ.toNNReal S.attractor ≠ ⊤ :=
    externalCoveringNumber_ne_top S.isCompact_attractor.totallyBounded (Real.toNNReal_pos.2 hδ0)
  obtain ⟨D', hD'fin, hD'cov, hD'card⟩ := exists_isCover_encard_eq hNfin
  set D := hD'fin.toFinset with hDdef
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ0 hS.r_lt_one
  set ind : ℝ × ℝ → List ι → ℝ := fun z w =>
    if (S.phiWord w '' S.attractor ∩ Metric.closedBall z δ).Nonempty then 1 else 0 with hind
  have hword : ∀ u j, δ ≤ S.alpha₂ u → S.alpha₂ (u ++ [j]) < δ →
      C₀ * δ₀ * δ ^ (-(q : ℝ)) * S.modSvf t (u ++ [j]) ≤ ∑ z ∈ D, ind z (u ++ [j]) := by
    intro u j hu hw
    set w := u ++ [j] with hwdef
    have hα₂ : δ₀ * δ ≤ S.alpha₂ w :=
      (mul_le_mul_of_nonneg_left hu hδ₀.1.le).trans (hδ₀.alpha₂_append_ge u j)
    have hα₁ : S.alpha₁ w ≤ 1 :=
      (hS.alpha₁_le w).trans (pow_le_one₀ hS.r_nonneg hS.r_lt_one.le)
    obtain ⟨e, he1, he2⟩ := S.fraser_exists_axis w
    have hρ0 : 0 < δ / S.alpha₁ w := div_pos hδ0 (S.alpha₁_pos w)
    have hρR : δ / S.alpha₁ w ≤ δ₀⁻¹ := by
      rw [div_le_iff₀ (S.alpha₁_pos w), ← div_eq_inv_mul, le_div_iff₀ hδ₀.1]
      linarith [S.alpha₂_le_alpha₁ w]
    have hcount := hC (e + S.oWord w) _ hρ0 hρR
    rw [he2] at hcount
    have hcov := S.fraser_coveringNumber_le w e hδ0.le S.attractor
    rw [he1] at hcov
    have hfilter : Metric.externalCoveringNumber δ.toNNReal (S.phiWord w '' S.attractor) ≤
        ((D.filter fun z => (S.phiWord w '' S.attractor ∩ Metric.closedBall z δ).Nonempty).card :
          ℕ∞) := by
      refine le_trans (Metric.IsCover.externalCoveringNumber_le_encard ?_)
        (Set.encard_coe_eq_coe_finsetCard _).le
      intro y hy
      obtain ⟨z, hz, hyz⟩ := hD'cov (S.phiWord_image_attractor_subset w hy)
      refine ⟨z, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hD'fin.mem_toFinset.2 hz, y, hy, ?_⟩),
        hyz⟩
      have hyz' : edist y z ≤ (δ.toNNReal : ℝ≥0∞) := hyz
      rw [edist_dist] at hyz'
      exact Metric.mem_closedBall.2 ((ENNReal.ofReal_le_ofReal_iff hδ0.le).1 hyz')
    have hsum : ∑ z ∈ D, ind z w = ((D.filter fun z =>
        (S.phiWord w '' S.attractor ∩ Metric.closedBall z δ).Nonempty).card : ℝ) :=
      Finset.sum_boole _ _
    rw [hsum]
    have hchain := hcount.trans (ENat.toENNReal_le.2 (hcov.trans hfilter))
    rw [ENat.toENNReal_coe, ENNReal.ofReal_le_iff_le_toReal (ENNReal.natCast_ne_top _),
      ENNReal.toReal_natCast] at hchain
    refine le_trans ?_ hchain
    have halg := FraserLower.le_rpow_div hδ₀.1 hδ₀1 (S.alpha₂_pos w) (S.alpha₂_le_alpha₁ w) hα₁
      hw hα₂ (S.wordDim_le S.projDim_le_one w) ht0 hη0.le
    rw [show -(t - η) = -(q : ℝ) by rw [hη]; ring] at halg
    calc C₀ * δ₀ * δ ^ (-(q : ℝ)) * S.modSvf t w
        = C₀ * (δ₀ * δ ^ (-(q : ℝ)) *
            (S.alpha₁ w ^ S.wordDim w * S.alpha₂ w ^ (t - S.wordDim w))) := by
          rw [modSvf]; ring
      _ ≤ C (e + S.oWord w) * (δ / S.alpha₁ w) ^ (-(S.wordDim w - η)) :=
          mul_le_mul (hC₀le _) halg
            (mul_nonneg (mul_nonneg hδ₀.1.le (Real.rpow_nonneg hδ0.le _))
              (mul_nonneg (Real.rpow_nonneg (S.alpha₁_pos w).le _)
                (Real.rpow_nonneg (S.alpha₂_pos w).le _)))
            (hC0 _).le
  have hcountz : ∀ z, S.fraserStopSum δ (ind z) k [] ≤ M₂ := fun z =>
    S.fraserStopSum_meets_le hab hcd hsub hdisj hδ₀ hδ0 hδ1.le k z
  have hroot : δ ≤ S.alpha₂ [] := by rw [alpha₂_nil]; exact hδ1.le
  have hpos : 0 ≤ C₀ * δ₀ * δ ^ (-(q : ℝ)) :=
    mul_nonneg (mul_nonneg hC₀.le hδ₀.1.le) (Real.rpow_nonneg hδ0.le _)
  have hmain : C₀ * δ₀ * δ ^ (-(q : ℝ)) * L ≤ M₂ * D.card := by
    calc C₀ * δ₀ * δ ^ (-(q : ℝ)) * L
        ≤ C₀ * δ₀ * δ ^ (-(q : ℝ)) * S.fraserStopSum δ (S.modSvf t) k [] :=
          mul_le_mul_of_nonneg_left (hLδ δ hδ1.le k hk) hpos
      _ = S.fraserStopSum δ (fun w => C₀ * δ₀ * δ ^ (-(q : ℝ)) * S.modSvf t w) k [] :=
          (S.fraserStopSum_const_mul _ _ _ _ _).symm
      _ ≤ S.fraserStopSum δ (fun w => ∑ z ∈ D, ind z w) k [] :=
          fraserStopSum_mono hword k [] hroot
      _ = ∑ z ∈ D, S.fraserStopSum δ (ind z) k [] := S.fraserStopSum_sum δ D ind k []
      _ ≤ ∑ _z ∈ D, M₂ := Finset.sum_le_sum fun z _ => hcountz z
      _ = M₂ * D.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hNX : (Metric.externalCoveringNumber δ.toNNReal S.attractor : ℝ≥0∞) = (D.card : ℝ≥0∞) := by
    rw [← hD'card, hD'fin.encard_eq_coe_toFinset_card, ENat.toENNReal_coe]
  rw [hNX]
  change ENNReal.ofReal (C₀ * δ₀ * L / M₂) * ENNReal.ofReal (δ ^ (-(q : ℝ))) ≤ _
  rw [← ENNReal.ofReal_mul (by have := hδ₀.1; positivity), ← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ hM₂]
  calc C₀ * δ₀ * L * δ ^ (-(q : ℝ)) = C₀ * δ₀ * δ ^ (-(q : ℝ)) * L := by ring
    _ ≤ M₂ * D.card := hmain
    _ = D.card * M₂ := mul_comm _ _

end RectangularIFS

end FractalGeometry
