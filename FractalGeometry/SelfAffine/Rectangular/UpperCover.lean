import Mathlib
import GeometricMeasureTheory.Box.ModifiedBox
import FractalGeometry.Dimension.BoxTools
import FractalGeometry.Dimension.PlaneCovering
import FractalGeometry.LinearCocycles.Monomial
import FractalGeometry.SelfAffine.Rectangular.Attractor
import FractalGeometry.SelfAffine.Rectangular.Coding
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.SelfAffine.Rectangular.LowerCover
import FractalGeometry.SelfAffine.Rectangular.ModifiedPressure
import FractalGeometry.SelfAffine.Rectangular.OpenSet
import FractalGeometry.SelfAffine.Rectangular.SingularValues
import FractalGeometry.SelfAffine.Rectangular.Stopping
import FractalGeometry.Symbolic.BlockGrouping
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.StoppingTime
import GeometricMeasureTheory.Box.BoxDimension
import GeometricMeasureTheory.Box.CoveringNumbers

open GeometricMeasureTheory

namespace FractalGeometry

open Filter Topology

open scoped ENNReal NNReal

namespace FraserUpper

variable {X : Type*} [PseudoMetricSpace X]

theorem externalCoveringNumber_union_le (ε : ℝ≥0) (A B : Set X) :
    Metric.externalCoveringNumber ε (A ∪ B) ≤
      Metric.externalCoveringNumber ε A + Metric.externalCoveringNumber ε B := by
  rcases eq_or_ne (Metric.externalCoveringNumber ε A) ⊤ with hA | hA
  · rw [hA, top_add]
    exact le_top
  rcases eq_or_ne (Metric.externalCoveringNumber ε B) ⊤ with hB | hB
  · rw [hB, add_top]
    exact le_top
  obtain ⟨C, -, hC, hCe⟩ := exists_isCover_encard_eq hA
  obtain ⟨D, -, hD, hDe⟩ := exists_isCover_encard_eq hB
  have hcov : Metric.IsCover ε (A ∪ B) (C ∪ D) := by
    rintro x (hx | hx)
    · obtain ⟨y, hy, hxy⟩ := hC hx
      exact ⟨y, Or.inl hy, hxy⟩
    · obtain ⟨y, hy, hxy⟩ := hD hx
      exact ⟨y, Or.inr hy, hxy⟩
  rw [← hCe, ← hDe]
  exact hcov.externalCoveringNumber_le_encard.trans (Set.encard_union_le C D)

theorem externalCoveringNumber_biUnion_le {κ : Type*} (ε : ℝ≥0) (s : Finset κ)
    (A : κ → Set X) :
    (Metric.externalCoveringNumber ε (⋃ i ∈ s, A i) : ℝ≥0∞) ≤
      ∑ i ∈ s, (Metric.externalCoveringNumber ε (A i) : ℝ≥0∞) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hi]
    calc (Metric.externalCoveringNumber ε (A i ∪ ⋃ j ∈ s, A j) : ℝ≥0∞)
        ≤ ((Metric.externalCoveringNumber ε (A i) +
            Metric.externalCoveringNumber ε (⋃ j ∈ s, A j) : ℕ∞) : ℝ≥0∞) :=
          ENat.toENNReal_le.2 (externalCoveringNumber_union_le ε _ _)
      _ = (Metric.externalCoveringNumber ε (A i) : ℝ≥0∞) +
            (Metric.externalCoveringNumber ε (⋃ j ∈ s, A j) : ℝ≥0∞) := ENat.toENNReal_add _ _
      _ ≤ _ := by gcongr

theorem exists_externalCoveringNumber_le {E : Set X} {t : ℝ}
    (ht : upperBoxDim E < ENNReal.ofReal t) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r ≤ R →
      (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞) ≤ ENNReal.ofReal (C * r ^ (-t)) := by
  obtain ⟨s, hs⟩ := iInf_lt_iff.1 ht
  obtain ⟨hsE, hst⟩ := iInf_lt_iff.1 hs
  have hst' : (s : ℝ) < t := ENNReal.coe_lt_ofReal.1 hst
  have ht0 : 0 < t := lt_of_le_of_lt s.coe_nonneg hst'
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hsE
  have hu0 : (0 : ℝ) < u := hu
  set r₁ := min (u / 2) 1 with hr₁def
  have hr₁ : 0 < r₁ := lt_min (half_pos hu0) one_pos
  have hr₁u : r₁ < u := (min_le_left _ _).trans_lt (half_lt_self hu0)
  have hN₁ : (Metric.externalCoveringNumber r₁.toNNReal E : ℝ≥0∞) ≤
      ENNReal.ofReal (r₁ ^ (-(s : ℝ))) := hsub ⟨hr₁, hr₁u⟩
  refine ⟨max 1 (r₁ ^ (-(s : ℝ)) * R ^ t), lt_of_lt_of_le one_pos (le_max_left _ _),
    fun r hr hrR => ?_⟩
  rcases lt_or_ge r r₁ with hrr | hrr
  · have hN : (Metric.externalCoveringNumber r.toNNReal E : ℝ≥0∞) ≤
        ENNReal.ofReal (r ^ (-(s : ℝ))) := hsub ⟨hr, hrr.trans hr₁u⟩
    refine hN.trans (ENNReal.ofReal_le_ofReal ?_)
    calc r ^ (-(s : ℝ)) ≤ r ^ (-t) :=
          Real.rpow_le_rpow_of_exponent_ge hr (hrr.le.trans (min_le_right _ _)) (by linarith)
      _ ≤ max 1 (r₁ ^ (-(s : ℝ)) * R ^ t) * r ^ (-t) :=
          le_mul_of_one_le_left (Real.rpow_nonneg hr.le _) (le_max_left _ _)
  · have hanti := Metric.externalCoveringNumber_anti (A := E) (Real.toNNReal_le_toNNReal hrr)
    refine (ENat.toENNReal_le.2 hanti).trans (hN₁.trans (ENNReal.ofReal_le_ofReal ?_))
    calc r₁ ^ (-(s : ℝ)) = r₁ ^ (-(s : ℝ)) * R ^ t * R ^ (-t) := by
          rw [mul_assoc, ← Real.rpow_add hR, add_neg_cancel, Real.rpow_zero, mul_one]
      _ ≤ (r₁ ^ (-(s : ℝ)) * R ^ t) * r ^ (-t) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hr hrR (by linarith))
            (by positivity)
      _ ≤ max 1 (r₁ ^ (-(s : ℝ)) * R ^ t) * r ^ (-t) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hr.le _)

theorem externalCoveringNumber_le_mul_grid {A : Set (ℝ × ℝ)} (c : ZMod 2) {a b ρ : ℝ}
    (hρ : 0 < ρ) (hA : ∀ z ∈ A, RectangularIFS.coord (c + 1) z ∈ Set.Icc a b) :
    (Metric.externalCoveringNumber ρ.toNNReal A : ℝ≥0∞) ≤
      (Metric.externalCoveringNumber ρ.toNNReal (RectangularIFS.coord c '' A) : ℝ≥0∞) *
        ((⌊(b - a) / (2 * ρ)⌋₊ + 1 : ℕ) : ℝ≥0∞) := by
  rcases eq_or_ne (Metric.externalCoveringNumber ρ.toNNReal (RectangularIFS.coord c '' A)) ⊤ with hN | hN
  · rw [hN, ENat.toENNReal_top, ENNReal.top_mul (by positivity)]
    exact le_top
  obtain ⟨D, -, hD, hDe⟩ := exists_isCover_encard_eq hN
  set G := gridCentres a b ρ with hG
  set e : ℝ × ℝ → ℝ × ℝ := fun p => if c = 0 then p else p.swap with he
  have hcov : Metric.IsCover ρ.toNNReal A (e '' (D ×ˢ G)) := by
    intro z hz
    obtain ⟨u, hu, hzu⟩ := hD ⟨z, hz, rfl⟩
    obtain ⟨v, hv, hzv⟩ := isCover_gridCentres hρ (hA z hz)
    refine ⟨e (u, v), ⟨(u, v), ⟨hu, hv⟩, rfl⟩, ?_⟩
    replace hzu : edist (RectangularIFS.coord c z) u ≤ (ρ.toNNReal : ℝ≥0∞) := hzu
    replace hzv : edist (RectangularIFS.coord (c + 1) z) v ≤ (ρ.toNNReal : ℝ≥0∞) := hzv
    show edist z (e (u, v)) ≤ (ρ.toNNReal : ℝ≥0∞)
    rcases zmod_two_cases c with rfl | rfl
    · rw [zero_add] at hzv
      simp only [he, ↓reduceIte]
      exact (Prod.edist_eq _ _).trans_le (max_le hzu hzv)
    · rw [show (1 : ZMod 2) + 1 = 0 from by decide] at hzv
      simp only [he, one_ne_zero, ↓reduceIte, Prod.swap_prod_mk]
      exact (Prod.edist_eq _ _).trans_le (max_le hzv hzu)
  calc (Metric.externalCoveringNumber ρ.toNNReal A : ℝ≥0∞)
      ≤ ((e '' (D ×ˢ G)).encard : ℝ≥0∞) :=
        ENat.toENNReal_le.2 hcov.externalCoveringNumber_le_encard
    _ ≤ ((D ×ˢ G).encard : ℝ≥0∞) := ENat.toENNReal_le.2 (Set.encard_image_le _ _)
    _ = (D.encard : ℝ≥0∞) * (G.encard : ℝ≥0∞) := by
        rw [Set.encard_prod, ENat.toENNReal_mul]
    _ ≤ _ := by
        rw [hDe]
        gcongr
        rw [← ENat.toENNReal_coe]
        exact ENat.toENNReal_le.2 (encard_gridCentres_le a b ρ)

theorem div_rpow_neg_le {x y z δ₀ d s ε : ℝ} (hδ₀ : 0 < δ₀) (hy : 0 < y) (hz1 : δ₀ * y ≤ z)
    (hz2 : z ≤ y) (hzx : z ≤ x) (hx1 : x ≤ 1) (hd : 0 ≤ d) (hs : 0 ≤ s) (hε : 0 ≤ ε) :
    (y / x) ^ (-(d + ε)) ≤ δ₀ ^ (-s) * y ^ (-(s + ε)) * (x ^ d * z ^ (s - d)) := by
  have hz : 0 < z := (mul_pos hδ₀ hy).trans_le hz1
  have hx : 0 < x := hz.trans_le hzx
  have h1 : x ^ ε ≤ 1 := Real.rpow_le_one hx.le hx1 hε
  have h2 : δ₀ ^ s * y ^ s ≤ z ^ s := by
    rw [← Real.mul_rpow hδ₀.le hy.le]
    exact Real.rpow_le_rpow (by positivity) hz1 hs
  have h3 : z ^ d ≤ y ^ d := Real.rpow_le_rpow hz.le hz2 hd
  have hxd : 0 < x ^ d := Real.rpow_pos_of_pos hx d
  have hyd : 0 < y ^ d := Real.rpow_pos_of_pos hy d
  have hyε : 0 < y ^ ε := Real.rpow_pos_of_pos hy ε
  have hys : 0 < y ^ s := Real.rpow_pos_of_pos hy s
  have hδs : 0 < δ₀ ^ s := Real.rpow_pos_of_pos hδ₀ s
  have hzd : 0 < z ^ d := Real.rpow_pos_of_pos hz d
  rw [Real.rpow_neg (div_pos hy hx).le, Real.div_rpow hy.le hx.le, inv_div, Real.rpow_add hx,
    Real.rpow_add hy, Real.rpow_neg hδ₀.le, Real.rpow_neg hy.le, Real.rpow_add hy,
    Real.rpow_sub hz]
  calc x ^ d * x ^ ε / (y ^ d * y ^ ε) ≤ x ^ d / (y ^ d * y ^ ε) :=
        div_le_div_of_nonneg_right (mul_le_of_le_one_right hxd.le h1) (by positivity)
    _ = x ^ d * (δ₀ ^ s * y ^ s) / (δ₀ ^ s * y ^ s * y ^ ε * y ^ d) := by
        field_simp
    _ ≤ x ^ d * z ^ s / (δ₀ ^ s * y ^ s * y ^ ε * z ^ d) :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left h2 hxd.le) (by positivity)
          (mul_le_mul_of_nonneg_left h3 (by positivity))
    _ = (δ₀ ^ s)⁻¹ * (y ^ s * y ^ ε)⁻¹ * (x ^ d * (z ^ s / z ^ d)) := by
        field_simp

open _root_.FractalGeometry.RectangularIFS

variable {ι : Type*} (S : RectangularIFS ι)

theorem exists_long_axis (w : List ι) : ∃ c : ZMod 2, S.side c w = S.alpha₁ w ∧
    S.side (c + 1) w = S.alpha₂ w ∧ S.projDim (c + S.oWord w) = S.wordDim w := by
  by_cases h : S.wordHeight w ≤ S.wordBase w
  · refine ⟨0, (max_eq_left h).symm, ?_, ?_⟩
    · rw [zero_add]
      exact (min_eq_right h).symm
    · simp [wordDim, h]
  · have h' := (not_le.1 h).le
    refine ⟨1, (max_eq_right h').symm, ?_, ?_⟩
    · rw [show (1 : ZMod 2) + 1 = 0 from by decide]
      exact (min_eq_left h').symm
    · rw [wordDim, add_comm]
      simp [h]

theorem externalCoveringNumber_coord_phiWord_le (c : ZMod 2) (w : List ι) (E : Set (ℝ × ℝ))
    {ρ : ℝ} (hρ : 0 < ρ) :
    Metric.externalCoveringNumber ρ.toNNReal (coord c '' (S.phiWord w '' E)) ≤
      Metric.externalCoveringNumber (ρ / S.side c w).toNNReal (coord (c + S.oWord w) '' E) := by
  set u := S.codeWord c w with hu
  have himg : coord c '' (S.phiWord w '' E) =
      (fun t => S.gDeriv u * t + S.gWord u 0) '' (coord (c + S.oWord w) '' E) := by
    rw [Set.image_image, Set.image_image]
    refine Set.image_congr fun z _ => ?_
    rw [coord_phiWord, gWord_apply]
  have hf : LipschitzWith ‖S.gDeriv u‖₊ fun t : ℝ => S.gDeriv u * t + S.gWord u 0 :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, Real.dist_eq, coe_nnnorm, Real.norm_eq_abs, ← abs_mul]
      exact le_of_eq (by ring_nf)
  have hside : 0 < S.side c w := S.side_pos c w
  have hK : ‖S.gDeriv u‖₊ * (ρ / S.side c w).toNNReal = ρ.toNNReal := by
    ext
    rw [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs,
      Real.coe_toNNReal _ (div_nonneg hρ.le hside.le), Real.coe_toNNReal _ hρ.le]
    change S.side c w * (ρ / S.side c w) = ρ
    field_simp
  rw [himg, ← hK]
  exact externalCoveringNumber_image_le_of_lipschitzWith hf _ _

variable {S}

theorem attractor_subset_iUnion [Fintype ι] [Nonempty ι] {δ₀ r M ρ : ℝ}
    (hδ₀ : S.RatioLowerBound δ₀) (hδ₀1 : δ₀ ≤ 1) (hS : S.Bounds r M) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {L : ℕ} (hL : r ^ L < δ₀ * ρ) :
    S.attractor ⊆ ⋃ n ∈ Finset.range L, ⋃ w ∈ (Finset.univ.filter fun w : Fin n → ι =>
      δ₀ * ρ ≤ S.alpha₂ (List.ofFn w) ∧ S.alpha₂ (List.ofFn w) ≤ ρ),
        S.phiWord (List.ofFn w) '' S.attractor := by
  classical
  rintro _ ⟨x, rfl⟩
  have hex : ∃ n, S.alpha₂ (futureWord x n) ≤ ρ := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hρ hS.r_lt_one
    refine ⟨k, (hS.alpha₂_le _).trans ?_⟩
    rw [length_futureWord]
    exact hk.le
  obtain ⟨n, hn1, hn2⟩ := exists_stop (F := fun n => S.alpha₂ (futureWord x n)) hδ₀.1.le hδ₀1
    hρ.le (by rw [futureWord_zero, S.alpha₂_nil]; exact hρ1)
    (fun n => by rw [futureWord_succ]; exact hδ₀.alpha₂_append_ge _ _) hex
  obtain ⟨y, hy⟩ := hS.exists_proj_eq_phiWord n x
  have hlen : n < L := by
    by_contra h
    rw [not_lt] at h
    have h1 := hS.alpha₂_le (futureWord x n)
    rw [length_futureWord] at h1
    have h2 : r ^ n ≤ r ^ L := pow_le_pow_of_le_one hS.r_nonneg hS.r_lt_one.le h
    linarith
  rw [futureWord_eq_ofFn] at hn1 hn2 hy
  simp only [Set.mem_iUnion]
  exact ⟨n, Finset.mem_range.2 hlen, block n x,
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hn1, hn2⟩, S.proj y, ⟨y, rfl⟩, hy.symm⟩

theorem externalCoveringNumber_phiWord_le [Finite ι] [Nonempty ι] {δ₀ r M D ρ ε s : ℝ}
    (C : ZMod 2 → ℝ) (hδ₀ : S.RatioLowerBound δ₀) (hS : S.Bounds r M) (hD : 0 ≤ D)
    (hdist : ∀ x ∈ S.attractor, ∀ x' ∈ S.attractor, dist x x' ≤ D) (hC0 : ∀ c, 0 ≤ C c)
    (hC : ∀ c : ZMod 2, ∀ τ : ℝ, 0 < τ → τ ≤ δ₀⁻¹ →
      (Metric.externalCoveringNumber τ.toNNReal (coord c '' S.attractor) : ℝ≥0∞) ≤
        ENNReal.ofReal (C c * τ ^ (-(S.projDim c + ε))))
    (hρ : 0 < ρ) (hs : 0 ≤ s) (hε : 0 ≤ ε) {w : List ι} (h1 : δ₀ * ρ ≤ S.alpha₂ w)
    (h2 : S.alpha₂ w ≤ ρ) :
    (Metric.externalCoveringNumber ρ.toNNReal (S.phiWord w '' S.attractor) : ℝ≥0∞) ≤
      ENNReal.ofReal ((C 0 + C 1) * (D + 1) * δ₀ ^ (-s) * ρ ^ (-(s + ε)) * S.modSvf s w) := by
  obtain ⟨c, hc1, hc2, hcd⟩ := exists_long_axis S w
  obtain ⟨x₀, hx₀⟩ := S.attractor_nonempty
  set m := coord (c + 1) (S.phiWord w x₀) with hm
  have hA : ∀ z ∈ S.phiWord w '' S.attractor,
      coord (c + 1) z ∈ Set.Icc (m - S.alpha₂ w * D) (m + S.alpha₂ w * D) := by
    rintro _ ⟨p, hp, rfl⟩
    have h := S.abs_coord_phiWord_sub_le hdist (c + 1) w hp hx₀
    rw [hc2] at h
    exact ⟨by linarith [(abs_le.1 h).1], by linarith [(abs_le.1 h).2]⟩
  have hgrid := externalCoveringNumber_le_mul_grid c hρ hA
  have hproj := externalCoveringNumber_coord_phiWord_le S c w S.attractor hρ
  rw [hc1] at hproj
  have hα₁ : 0 < S.alpha₁ w := S.alpha₁_pos w
  have hα₂ : 0 < S.alpha₂ w := S.alpha₂_pos w
  have hτ : 0 < ρ / S.alpha₁ w := div_pos hρ hα₁
  have hτR : ρ / S.alpha₁ w ≤ δ₀⁻¹ := by
    rw [div_le_iff₀ hα₁]
    calc ρ = δ₀⁻¹ * (δ₀ * ρ) := by field_simp [hδ₀.1.ne']
      _ ≤ δ₀⁻¹ * S.alpha₁ w := mul_le_mul_of_nonneg_left
          (h1.trans (S.alpha₂_le_alpha₁ w)) (inv_nonneg.2 hδ₀.1.le)
  have hcount := hC (c + S.oWord w) _ hτ hτR
  rw [hcd] at hcount
  have hk : ((⌊(m + S.alpha₂ w * D - (m - S.alpha₂ w * D)) / (2 * ρ)⌋₊ + 1 : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (D + 1) := by
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    have heq : (m + S.alpha₂ w * D - (m - S.alpha₂ w * D)) / (2 * ρ) = S.alpha₂ w * D / ρ := by
      field_simp
      ring
    rw [heq]
    have hfl := Nat.floor_le (div_nonneg (mul_nonneg hα₂.le hD) hρ.le)
    have hle : S.alpha₂ w * D / ρ ≤ D := by
      rw [div_le_iff₀ hρ]
      nlinarith
    push_cast
    linarith
  have hα₁1 : S.alpha₁ w ≤ 1 :=
    (hS.alpha₁_le w).trans (pow_le_one₀ hS.r_nonneg hS.r_lt_one.le)
  have hreal := div_rpow_neg_le hδ₀.1 hρ h1 h2 (S.alpha₂_le_alpha₁ w) hα₁1
    (S.wordDim_nonneg w) hs hε
  have hCc : C (c + S.oWord w) ≤ C 0 + C 1 := by
    rcases zmod_two_cases (c + S.oWord w) with h | h <;> rw [h]
    · linarith [hC0 1]
    · linarith [hC0 0]
  calc (Metric.externalCoveringNumber ρ.toNNReal (S.phiWord w '' S.attractor) : ℝ≥0∞)
      ≤ (Metric.externalCoveringNumber ρ.toNNReal (coord c '' (S.phiWord w '' S.attractor)) :
          ℝ≥0∞) * ((⌊(m + S.alpha₂ w * D - (m - S.alpha₂ w * D)) / (2 * ρ)⌋₊ + 1 : ℕ) : ℝ≥0∞) :=
        hgrid
    _ ≤ ENNReal.ofReal (C (c + S.oWord w) * (ρ / S.alpha₁ w) ^ (-(S.wordDim w + ε))) *
          ENNReal.ofReal (D + 1) :=
        mul_le_mul' ((ENat.toENNReal_le.2 hproj).trans hcount) hk
    _ = ENNReal.ofReal (C (c + S.oWord w) * (ρ / S.alpha₁ w) ^ (-(S.wordDim w + ε)) *
          (D + 1)) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (hC0 _) (Real.rpow_nonneg hτ.le _))]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc C (c + S.oWord w) * (ρ / S.alpha₁ w) ^ (-(S.wordDim w + ε)) * (D + 1)
            ≤ (C 0 + C 1) * (δ₀ ^ (-s) * ρ ^ (-(s + ε)) *
                (S.alpha₁ w ^ S.wordDim w * S.alpha₂ w ^ (s - S.wordDim w))) * (D + 1) := by
              gcongr
              exact add_nonneg (hC0 0) (hC0 1)
          _ = (C 0 + C 1) * (D + 1) * δ₀ ^ (-s) * ρ ^ (-(s + ε)) * S.modSvf s w := by
              rw [modSvf]
              ring

variable (S)

theorem exists_sum_modSvfSum_le [Fintype ι] [Nonempty ι] {s : ℝ} (hs : 0 ≤ s)
    (hP : S.modPressure s < 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℕ, ∑ n ∈ Finset.range L, S.modSvfSum s n ≤ K := by
  have ht := S.tendsto_modPressure hs
  have hq0 : 0 < Real.exp (S.modPressure s / 2) := Real.exp_pos _
  have hq1 : Real.exp (S.modPressure s / 2) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hev : ∀ᶠ n : ℕ in atTop, ‖S.modSvfSum s n‖ ≤ Real.exp (S.modPressure s / 2) ^ n := by
    filter_upwards [ht.eventually
      (gt_mem_nhds (show S.modPressure s < S.modPressure s / 2 by linarith)),
      eventually_gt_atTop 0] with n hn hn0
    have hpos := S.modSvfSum_pos s n
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [div_lt_iff₀ hn'] at hn
    rw [Real.norm_of_nonneg hpos.le, ← Real.exp_nat_mul]
    calc S.modSvfSum s n = Real.exp (Real.log (S.modSvfSum s n)) := (Real.exp_log hpos).symm
      _ ≤ Real.exp (n * (S.modPressure s / 2)) := Real.exp_le_exp.2 (by linarith)
  have hsum : Summable fun n => S.modSvfSum s n :=
    Summable.of_norm_bounded_eventually_nat (summable_geometric_of_lt_one hq0.le hq1) hev
  have hle : ∀ L : ℕ, ∑ n ∈ Finset.range L, S.modSvfSum s n ≤ ∑' n, S.modSvfSum s n :=
    fun L => hsum.sum_le_tsum (Finset.range L) fun n _ => (S.modSvfSum_pos s n).le
  refine ⟨∑' n, S.modSvfSum s n + 1, ?_,
    fun L => (hle L).trans (le_add_of_nonneg_right zero_le_one)⟩
  have h0 := hle 0
  rw [Finset.range_zero, Finset.sum_empty] at h0
  linarith

end FraserUpper

namespace RectangularIFS

universe u

variable {ι : Type u} [Fintype ι] [Nonempty ι] (S : RectangularIFS ι)

theorem upperBoxDim_attractor_le_of_modPressure_neg {s : ℝ} (hs : 0 ≤ s)
    (hP : S.modPressure s < 0) {t : ℝ≥0} (hst : s < t) : upperBoxDim S.attractor ≤ t := by
  classical
  set ε := (t : ℝ) - s with hεdef
  have hε : 0 < ε := sub_pos.2 hst
  obtain ⟨K, hK0, hK⟩ := FraserUpper.exists_sum_modSvfSum_le S hs hP
  obtain ⟨δ₀, hδ₀⟩ := S.exists_ratioLowerBound
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  obtain ⟨i⟩ : Nonempty ι := inferInstance
  have hδ₀1 : δ₀ ≤ 1 := (hδ₀.2 (i, 0)).trans (S.abs_ratio_lt_one _).le
  have hδ₀0 := hδ₀.1
  obtain ⟨D₀, hD₀⟩ := Metric.isBounded_iff.1 S.isCompact_attractor.isBounded
  have hD1 : 1 ≤ max D₀ 1 := le_max_right _ _
  have hD0 : 0 < max D₀ 1 := one_pos.trans_le hD1
  have hdist : ∀ x ∈ S.attractor, ∀ x' ∈ S.attractor, dist x x' ≤ max D₀ 1 :=
    fun x hx x' hx' => (hD₀ hx hx').trans (le_max_left _ _)
  have hproj : ∀ c : ZMod 2, ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ δ₀⁻¹ →
      (Metric.externalCoveringNumber τ.toNNReal (coord c '' S.attractor) : ℝ≥0∞) ≤
        ENNReal.ofReal (C * τ ^ (-(S.projDim c + ε))) := by
    intro c
    refine FraserUpper.exists_externalCoveringNumber_le ?_ (inv_pos.2 hδ₀0)
    have hne : upperBoxDim (coord c '' S.attractor) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (S.upperBoxDim_coord_le_one c)
    rw [← ENNReal.ofReal_toReal hne]
    refine (ENNReal.ofReal_lt_ofReal_iff (by linarith [S.projDim_nonneg c])).2 ?_
    change S.projDim c < S.projDim c + ε
    linarith
  choose C hC0 hC using hproj
  set B := (C 0 + C 1) * (max D₀ 1 + 1) * δ₀ ^ (-s) with hB
  have hB0 : 0 < B := by
    have := hC0 0
    have := hC0 1
    positivity
  refine upperBoxDim_le_of_forall (C := (B * K).toNNReal) (Real.toNNReal_pos.2 (mul_pos hB0 hK0))
    ?_
  filter_upwards [eventually_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one' ℝ))] with ρ hρ0 hρ1
  have hρ : (0 : ℝ) < ρ := hρ0
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one (mul_pos hδ₀0 hρ) hS.r_lt_one
  set W : (n : ℕ) → Finset (Fin n → ι) := fun n => Finset.univ.filter fun w =>
    δ₀ * ρ ≤ S.alpha₂ (List.ofFn w) ∧ S.alpha₂ (List.ofFn w) ≤ ρ with hW
  have hsub : S.attractor ⊆ ⋃ n ∈ Finset.range L, ⋃ w ∈ W n,
      S.phiWord (List.ofFn w) '' S.attractor :=
    FraserUpper.attractor_subset_iUnion hδ₀ hδ₀1 hS hρ (le_of_lt hρ1) hL
  have hterm : ∀ n, ∀ w ∈ W n,
      (Metric.externalCoveringNumber ρ.toNNReal (S.phiWord (List.ofFn w) '' S.attractor) :
        ℝ≥0∞) ≤ ENNReal.ofReal (B * ρ ^ (-(s + ε)) * S.modSvf s (List.ofFn w)) := by
    intro n w hw
    rw [hW, Finset.mem_filter] at hw
    exact FraserUpper.externalCoveringNumber_phiWord_le C hδ₀ hS hD0.le hdist
      (fun c => (hC0 c).le) hC hρ hs hε.le hw.2.1 hw.2.2
  have hnonneg : ∀ n, ∀ w ∈ W n, 0 ≤ B * ρ ^ (-(s + ε)) * S.modSvf s (List.ofFn w) :=
    fun n w _ => by
      have := S.modSvf_pos s (List.ofFn w)
      positivity
  have hsumle : ∑ n ∈ Finset.range L, ∑ w ∈ W n,
      B * ρ ^ (-(s + ε)) * S.modSvf s (List.ofFn w) ≤ B * ρ ^ (-(s + ε)) * K := by
    calc ∑ n ∈ Finset.range L, ∑ w ∈ W n, B * ρ ^ (-(s + ε)) * S.modSvf s (List.ofFn w)
        ≤ ∑ n ∈ Finset.range L, B * ρ ^ (-(s + ε)) * S.modSvfSum s n := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [modSvfSum, Finset.mul_sum]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun w _ _ => by
              have := S.modSvf_pos s (List.ofFn w)
              positivity
      _ = B * ρ ^ (-(s + ε)) * ∑ n ∈ Finset.range L, S.modSvfSum s n :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ B * ρ ^ (-(s + ε)) * K :=
          mul_le_mul_of_nonneg_left (hK L) (by positivity)
  have hexp : s + ε = (t : ℝ) := by
    rw [hεdef]
    ring
  calc (Metric.externalCoveringNumber ρ.toNNReal S.attractor : ℝ≥0∞)
      ≤ (Metric.externalCoveringNumber ρ.toNNReal (⋃ n ∈ Finset.range L, ⋃ w ∈ W n,
          S.phiWord (List.ofFn w) '' S.attractor) : ℝ≥0∞) :=
        ENat.toENNReal_le.2 (Metric.externalCoveringNumber_mono_set hsub)
    _ ≤ ∑ n ∈ Finset.range L, (Metric.externalCoveringNumber ρ.toNNReal
          (⋃ w ∈ W n, S.phiWord (List.ofFn w) '' S.attractor) : ℝ≥0∞) :=
        FraserUpper.externalCoveringNumber_biUnion_le _ _ _
    _ ≤ ∑ n ∈ Finset.range L, ∑ w ∈ W n, (Metric.externalCoveringNumber ρ.toNNReal
          (S.phiWord (List.ofFn w) '' S.attractor) : ℝ≥0∞) :=
        Finset.sum_le_sum fun n _ => FraserUpper.externalCoveringNumber_biUnion_le _ _ _
    _ ≤ ∑ n ∈ Finset.range L, ∑ w ∈ W n,
          ENNReal.ofReal (B * ρ ^ (-(s + ε)) * S.modSvf s (List.ofFn w)) :=
        Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun w hw => hterm n w hw
    _ = ENNReal.ofReal (∑ n ∈ Finset.range L, ∑ w ∈ W n,
          B * ρ ^ (-(s + ε)) * S.modSvf s (List.ofFn w)) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun n _ => Finset.sum_nonneg (hnonneg n)]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg (hnonneg n)]
    _ ≤ ENNReal.ofReal (B * ρ ^ (-(s + ε)) * K) := ENNReal.ofReal_le_ofReal hsumle
    _ = ((B * K).toNNReal : ℝ≥0∞) * ENNReal.ofReal (ρ ^ (-(t : ℝ))) := by
        rw [hexp, mul_right_comm]
        exact ENNReal.ofReal_mul (by positivity)

theorem upperBoxDim_attractor_le_dimmaff :
    upperBoxDim S.attractor ≤ ENNReal.ofReal S.dimmaff := by
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  have hη' : (0 : ℝ) < η := hη
  have hpos : 0 ≤ S.dimmaff + η := add_nonneg S.dimmaff_nonneg hη'.le
  have hsum : ENNReal.ofReal S.dimmaff + η = ((S.dimmaff + η).toNNReal : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal (p := η), ← ENNReal.ofReal_add S.dimmaff_nonneg η.coe_nonneg]
    rfl
  rw [hsum]
  have hs : 0 ≤ S.dimmaff + η / 2 := by
    have := S.dimmaff_nonneg
    positivity
  have hP : S.modPressure (S.dimmaff + η / 2) < 0 := by
    have h' := S.strictAntiOn_modPressure (Set.mem_Ici.2 S.dimmaff_nonneg) (Set.mem_Ici.2 hs)
      (show S.dimmaff < S.dimmaff + η / 2 by linarith)
    rwa [S.modPressure_dimmaff] at h'
  refine S.upperBoxDim_attractor_le_of_modPressure_neg hs hP ?_
  rw [Real.coe_toNNReal _ hpos]
  linarith

end RectangularIFS

end FractalGeometry
