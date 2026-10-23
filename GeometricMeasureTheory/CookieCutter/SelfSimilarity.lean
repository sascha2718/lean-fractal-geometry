/-
# Section 6.2: "Almost" self-similar sets

Bounded distortion makes the repeller of a cookie cutter self-similar up to a bounded factor: every
small ball around a point of the repeller expands onto the whole repeller with bounded distortion,
and dually every small ball contains a bounded-distortion copy of the repeller. The second property
is the one promoted to a definition in Section 8.

| Notes | Lean declaration | Location |
|---|---|---|
| Corollary 6.5 (`thm:cookie-cutter-expansion`) | `CookieCutter.cookie_cutter_expansion` | here |
| Corollary 6.6 (`thm:cookie-cutter-contraction`) | `CookieCutter.cookie_cutter_contraction` | here |
-/
import GeometricMeasureTheory.CookieCutter.BoundedDistortion

open MeasureTheory Filter Topology Set Metric

open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

namespace CookieCutter

variable {ι : Type*} [Finite ι] [Nonempty ι] (C : CookieCutter ι)

omit [Finite ι] in
/-- A point of `X` whose image under a branch map lies in the repeller lies in the repeller. -/
private theorem mem_attractor_of_branchMap_mem (w : List ι) {u : ℝ} (hu : u ∈ C.X)
    (h : C.branchMap w u ∈ C.attractor) : u ∈ C.attractor := by
  simp only [attractor, mem_iInter]
  intro m
  obtain ⟨v, hvlen, hv⟩ := C.exists_cylinder_mem h (w.length + m)
  have hsplit : v = v.take w.length ++ v.drop w.length := (List.take_append_drop _ _).symm
  have hplen : (v.take w.length).length = w.length := by
    rw [List.length_take, hvlen]
    omega
  have hqlen : (v.drop w.length).length = m := by
    rw [List.length_drop, hvlen]
    omega
  have hvsub : C.cylinder v ⊆ C.cylinder (v.take w.length) := by
    conv_lhs => rw [hsplit]
    exact C.cylinder_append_subset _ _
  have hpw : v.take w.length = w := by
    by_contra hne
    exact Set.disjoint_left.1 (C.disjoint_cylinder hplen hne) (hvsub hv) ⟨u, hu, rfl⟩
  have hveq : v = w ++ v.drop w.length := by
    calc v = v.take w.length ++ v.drop w.length := hsplit
      _ = w ++ v.drop w.length := by rw [hpw]
  rw [hveq, C.cylinder_append_eq] at hv
  obtain ⟨t, ht, heq⟩ := hv
  have htu : t = u := C.injOn_branchMap w (C.cylinder_subset_X _ ht) hu heq
  simp only [level, mem_iUnion]
  exact ⟨v.drop w.length, hqlen, htu ▸ ht⟩

/-- A ball centred on the repeller is sandwiched between two cylinders of comparable diameter. -/
private theorem exists_cylinder_sandwich :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ C.attractor, ∀ r : ℝ, 0 < r → r ≤ diam C.X →
      ∃ w : List ι, x ∈ C.cylinder w ∧ ball x (c * r) ∩ C.attractor ⊆ C.cylinder w ∧
        c * r ≤ diam (C.cylinder w) ∧ diam (C.cylinder w) ≤ r := by
  obtain ⟨c₁, hc₁, hcyl⟩ := C.exists_cylinder_subset_closedBall
  obtain ⟨d, hd, hsep⟩ := C.separated_cylinder
  refine ⟨min (c₁ / 2) (d * c₁ / 2), lt_min (by positivity) (by positivity), ?_⟩
  intro x hx r hr hrX
  obtain ⟨w, hxw, hsub, hlow⟩ := hcyl x hx (r / 2) (by linarith) (by linarith)
  have hhigh : diam (C.cylinder w) ≤ r := by
    have hb := diam_mono hsub (isBounded_closedBall (x := x) (r := r / 2))
    have hcb := diam_closedBall (x := x) (show (0:ℝ) ≤ r / 2 by linarith)
    linarith
  refine ⟨w, hxw, ?_, ?_, hhigh⟩
  · rintro y ⟨hy1, hy2⟩
    obtain ⟨v, hvlen, hv⟩ := C.exists_cylinder_mem hy2 w.length
    by_cases hvw : v = w
    · rwa [hvw] at hv
    · exfalso
      have h := hsep w v hvlen.symm (Ne.symm hvw) x hxw y hv
      have hxy : |x - y| < min (c₁ / 2) (d * c₁ / 2) * r := by
        have hb := mem_ball.1 hy1
        rwa [Real.dist_eq, abs_sub_comm] at hb
      have hmin : min (c₁ / 2) (d * c₁ / 2) * r ≤ d * c₁ / 2 * r :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hr.le
      linarith [mul_le_mul_of_nonneg_left hlow hd.le]
  · calc min (c₁ / 2) (d * c₁ / 2) * r ≤ c₁ / 2 * r :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hr.le
      _ = c₁ * (r / 2) := by ring
      _ ≤ diam (C.cylinder w) := hlow

/-- Corollary 6.5 (`thm:cookie-cutter-expansion`): every small ball of the repeller is, after
rescaling by `r⁻¹`, a bounded-distortion subset of the repeller itself. -/
theorem cookie_cutter_expansion :
    ∃ c r₀ : ℝ, 0 < c ∧ 0 < r₀ ∧ ∀ x ∈ C.attractor, ∀ r : ℝ, 0 < r → r < r₀ →
      ∃ g : ℝ → ℝ, MapsTo g (C.attractor ∩ ball x r) C.attractor ∧
        ∀ y ∈ C.attractor ∩ ball x r, ∀ z ∈ C.attractor ∩ ball x r,
          c⁻¹ * r⁻¹ * |y - z| ≤ |g y - g z| ∧ |g y - g z| ≤ c * r⁻¹ * |y - z| := by
  obtain ⟨-, b₁, hb₁1, hb₁⟩ := C.bounded_distortion
  obtain ⟨c₀, hc₀, hsand⟩ := C.exists_cylinder_sandwich
  have hb₁0 : (0:ℝ) < b₁ := lt_of_lt_of_le one_pos hb₁1
  set c := max b₁ (b₁ / c₀) with hcdef
  have hcpos : 0 < c := lt_of_lt_of_le hb₁0 (le_max_left _ _)
  refine ⟨c, c₀ * diam C.X, hcpos, mul_pos hc₀ C.diam_X_pos, ?_⟩
  intro x hx r hr hr₀
  have hρ : 0 < r / c₀ := div_pos hr hc₀
  have hρX : r / c₀ ≤ diam C.X := (div_le_iff₀ hc₀).2 (by linarith [mul_comm c₀ (diam C.X)])
  obtain ⟨w, hxw, hball, hlow, hhigh⟩ := hsand x hx (r / c₀) hρ hρX
  have hcancel : c₀ * (r / c₀) = r := by field_simp
  rw [hcancel] at hball hlow
  have hmem : ∀ y ∈ C.attractor ∩ ball x r, y ∈ C.cylinder w := fun y hy =>
    hball ⟨hy.2, hy.1⟩
  have hinv : ∀ y ∈ C.attractor ∩ ball x r,
      Function.invFunOn (C.branchMap w) C.X y ∈ C.X ∧
        C.branchMap w (Function.invFunOn (C.branchMap w) C.X y) = y := by
    intro y hy
    obtain ⟨u, hu, hyu⟩ := hmem y hy
    have hex : ∃ a ∈ C.X, C.branchMap w a = y := ⟨u, hu, hyu⟩
    exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩
  refine ⟨Function.invFunOn (C.branchMap w) C.X, ?_, ?_⟩
  · intro y hy
    obtain ⟨hgX, hgeq⟩ := hinv y hy
    refine C.mem_attractor_of_branchMap_mem w hgX ?_
    rw [hgeq]
    exact hy.1
  · intro y hy z hz
    obtain ⟨hyX, hyeq⟩ := hinv y hy
    obtain ⟨hzX, hzeq⟩ := hinv z hz
    obtain ⟨hl, hu⟩ := hb₁ w _ hyX _ hzX
    rw [hyeq, hzeq] at hl hu
    set T := |Function.invFunOn (C.branchMap w) C.X y -
      Function.invFunOn (C.branchMap w) C.X z| with hTdef
    have hT : 0 ≤ T := abs_nonneg _
    have hD0 : 0 ≤ diam (C.cylinder w) := diam_nonneg
    have hrD : r ≤ diam (C.cylinder w) := hlow
    have hDr : c₀ * diam (C.cylinder w) ≤ r := by
      have h := mul_le_mul_of_nonneg_left hhigh hc₀.le
      rwa [hcancel] at h
    have hcc : b₁ ≤ c₀ * c := by
      have h : b₁ / c₀ ≤ c := le_max_right _ _
      rw [div_le_iff₀ hc₀] at h
      linarith [mul_comm c c₀]
    have hl' : diam (C.cylinder w) * T ≤ b₁ * |y - z| := by
      have h := mul_le_mul_of_nonneg_left hl hb₁0.le
      have he : b₁ * (b₁⁻¹ * diam (C.cylinder w) * T) = diam (C.cylinder w) * T := by
        field_simp
      rwa [he] at h
    constructor
    · have hmul : |y - z| ≤ c * r * T := by
        refine le_of_mul_le_mul_left ?_ hc₀
        calc c₀ * |y - z| ≤ c₀ * (b₁ * diam (C.cylinder w) * T) :=
              mul_le_mul_of_nonneg_left hu hc₀.le
          _ = b₁ * (c₀ * diam (C.cylinder w)) * T := by ring
          _ ≤ b₁ * r * T := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hDr hb₁0.le) hT
          _ ≤ c₀ * c * r * T := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcc hr.le) hT
          _ = c₀ * (c * r * T) := by ring
      have hfin : c⁻¹ * r⁻¹ * (c * r * T) = T := by
        field_simp
      calc c⁻¹ * r⁻¹ * |y - z| ≤ c⁻¹ * r⁻¹ * (c * r * T) :=
            mul_le_mul_of_nonneg_left hmul
              (mul_nonneg (inv_nonneg.2 hcpos.le) (inv_nonneg.2 hr.le))
        _ = T := hfin
    · have hmul2 : r * T ≤ c * |y - z| := by
        calc r * T ≤ diam (C.cylinder w) * T := mul_le_mul_of_nonneg_right hrD hT
          _ ≤ b₁ * |y - z| := hl'
          _ ≤ c * |y - z| := mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
      calc T = r⁻¹ * (r * T) := by field_simp
        _ ≤ r⁻¹ * (c * |y - z|) := mul_le_mul_of_nonneg_left hmul2 (inv_nonneg.2 hr.le)
        _ = c * r⁻¹ * |y - z| := by ring

/-- Corollary 6.6 (`thm:cookie-cutter-contraction`): every small ball of the repeller contains a
bounded-distortion copy of the whole repeller, scaled by `r`. -/
theorem cookie_cutter_contraction :
    ∃ c r₀ : ℝ, 0 < c ∧ 0 < r₀ ∧ ∀ x ∈ C.attractor, ∀ r : ℝ, 0 < r → r < r₀ →
      ∃ g : ℝ → ℝ, MapsTo g C.attractor (C.attractor ∩ ball x r) ∧
        ∀ y ∈ C.attractor, ∀ z ∈ C.attractor,
          c⁻¹ * r * |y - z| ≤ |g y - g z| ∧ |g y - g z| ≤ c * r * |y - z| := by
  obtain ⟨-, b₁, hb₁1, hb₁⟩ := C.bounded_distortion
  obtain ⟨c₁, hc₁, hcyl⟩ := C.exists_cylinder_subset_closedBall
  have hb₁0 : (0:ℝ) < b₁ := lt_of_lt_of_le one_pos hb₁1
  set c := max b₁ (2 * b₁ / c₁) with hcdef
  have hcpos : 0 < c := lt_of_lt_of_le hb₁0 (le_max_left _ _)
  refine ⟨c, diam C.X, hcpos, C.diam_X_pos, ?_⟩
  intro x hx r hr hr₀
  obtain ⟨w, hxw, hsub, hlow⟩ := hcyl x hx (r / 2) (by linarith) (by linarith)
  have hhigh : diam (C.cylinder w) ≤ r := by
    have hb := diam_mono hsub (isBounded_closedBall (x := x) (r := r / 2))
    have hcb := diam_closedBall (x := x) (show (0:ℝ) ≤ r / 2 by linarith)
    linarith
  refine ⟨C.branchMap w, ?_, ?_⟩
  · intro y hy
    refine ⟨C.mapsTo_branchMap_attractor w hy, ?_⟩
    have h2 := hsub ⟨y, C.attractor_subset_X hy, rfl⟩
    rw [mem_closedBall] at h2
    exact mem_ball.2 (lt_of_le_of_lt h2 (by linarith))
  · intro y hy z hz
    obtain ⟨hl, hu⟩ := hb₁ w y (C.attractor_subset_X hy) z (C.attractor_subset_X hz)
    set G := |C.branchMap w y - C.branchMap w z| with hGdef
    have hG : 0 ≤ G := abs_nonneg _
    have hT : 0 ≤ |y - z| := abs_nonneg _
    have hl' : diam (C.cylinder w) * |y - z| ≤ b₁ * G := by
      have h := mul_le_mul_of_nonneg_left hl hb₁0.le
      have he : b₁ * (b₁⁻¹ * diam (C.cylinder w) * |y - z|) =
          diam (C.cylinder w) * |y - z| := by field_simp
      rwa [he] at h
    have hc2 : 2 * b₁ ≤ c * c₁ := by
      have h : 2 * b₁ / c₁ ≤ c := le_max_right _ _
      rwa [div_le_iff₀ hc₁] at h
    constructor
    · have hkey : r * |y - z| ≤ c * G := by
        refine le_of_mul_le_mul_left ?_ hc₁
        have h1 := mul_le_mul_of_nonneg_right hlow hT
        have h2 := mul_le_mul_of_nonneg_right hc2 hG
        nlinarith [h1, h2, hl']
      have h := mul_le_mul_of_nonneg_left hkey (inv_nonneg.2 hcpos.le)
      have he : c⁻¹ * (c * G) = G := by field_simp
      rw [he] at h
      calc c⁻¹ * r * |y - z| = c⁻¹ * (r * |y - z|) := mul_assoc _ _ _
        _ ≤ G := h
    · calc G ≤ b₁ * diam (C.cylinder w) * |y - z| := hu
        _ ≤ c * r * |y - z| := by
            refine mul_le_mul_of_nonneg_right ?_ hT
            calc b₁ * diam (C.cylinder w) ≤ b₁ * r := mul_le_mul_of_nonneg_left hhigh hb₁0.le
              _ ≤ c * r := mul_le_mul_of_nonneg_right (le_max_left _ _) hr.le

end CookieCutter

end GeometricMeasureTheory
