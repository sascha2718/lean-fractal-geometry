/-
# Section 6.1: Bounded distortion

The principles of bounded variation and bounded distortion, and the separation they give between
the cylinders of a cookie cutter.

A potential of the notes is a function on `X₁ ∪ ⋯ ∪ X_N`; read through the branches it is a family
`φ : ι → ℝ → ℝ`, with `φ i u` the value at `F i u`. The Birkhoff sum of the notes is then
`S_k φ (F_𝐢 u) = birkhoffSum φ 𝐢 u`, and splitting a word as `𝐢 = v ++ z` expresses the partial sum
`S_{|v|} φ` on the cylinder `X_𝐢` as `birkhoffSum φ v ∘ F_z`. The geometric potential
`-s log|f'|` of Section 7.3 is `fun i u => s * Real.log |C.dF i u|`.

| Notes | Lean declaration | Location |
|---|---|---|
| Birkhoff sums `S_k φ` | `CookieCutter.birkhoffSum` | here |
| Proposition 6.1 (principle of bounded variation) | `CookieCutter.bounded_variation` | here |
| The exponential form `e^{-b} ≤ exp S_kφ(x) / exp S_kφ(y) ≤ e^b` | `CookieCutter.exp_birkhoffSum_le` | here |
| `-log|(f^k)'(x)| = S_k φ(x)` for `φ = -log|f'|` | `CookieCutter.log_abs_branchDeriv` | here |
| Proposition 6.2 (principle of bounded distortion) | `CookieCutter.bounded_distortion` | here |
| Corollary 6.3 (`thm:cookie-cutter-separation`) | `CookieCutter.cookie_cutter_separation` | here |
| A ball contains a cylinder of comparable size | `CookieCutter.exists_cylinder_subset_closedBall` | here |
| Mean value theorem | `exists_hasDerivAt_eq_slope` | `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean` |
-/
import GeometricMeasureTheory.CookieCutter.Basic

open MeasureTheory Filter Topology Set Metric

open scoped ENNReal NNReal

noncomputable section

namespace GeometricMeasureTheory

namespace CookieCutter

variable {ι : Type*} (C : CookieCutter ι)

/-- The Birkhoff sum `S_k φ` along a word, read through the branches: for `x = F_𝐢(u)` the notes'
`S_k φ(x) = ∑_{j < k} φ(f^j x)` is `birkhoffSum φ 𝐢 u`. -/
def birkhoffSum (C : CookieCutter ι) (φ : ι → ℝ → ℝ) : List ι → ℝ → ℝ
  | [], _ => 0
  | i :: w, x => φ i (C.branchMap w x) + C.birkhoffSum φ w x

/-- The empty word carries the empty Birkhoff sum. -/
@[simp]
theorem birkhoffSum_nil (φ : ι → ℝ → ℝ) (x : ℝ) : C.birkhoffSum φ ([] : List ι) x = 0 := by
  simp [birkhoffSum]

/-- Prepending a letter adds the value of the potential at that letter. -/
@[simp]
theorem birkhoffSum_cons (φ : ι → ℝ → ℝ) (i : ι) (w : List ι) (x : ℝ) :
    C.birkhoffSum φ (i :: w) x = φ i (C.branchMap w x) + C.birkhoffSum φ w x := by
  simp [birkhoffSum]

/-- Splitting a word splits its Birkhoff sum: the letters of `v` are read at the point already
moved by `F_w`. -/
theorem birkhoffSum_append (φ : ι → ℝ → ℝ) (v w : List ι) (x : ℝ) :
    C.birkhoffSum φ (v ++ w) x =
      C.birkhoffSum φ v (C.branchMap w x) + C.birkhoffSum φ w x := by
  induction v with
  | nil => simp
  | cons i v ih =>
      rw [List.cons_append, birkhoffSum_cons, birkhoffSum_cons, ih, C.branchMap_append]
      simp [add_assoc]

/-- The geometric potential of Section 7.3, `-s log|f'|` read through the branches. -/
def geometricPotential (C : CookieCutter ι) (s : ℝ) (i : ι) (u : ℝ) : ℝ :=
  s * Real.log |C.dF i u|

/-- `-s log|(f^k)'(x)| = S_k φ(x)` for the geometric potential: the chain rule in logarithmic
form. -/
theorem log_abs_branchDeriv (s : ℝ) (w : List ι) {x : ℝ} (hx : x ∈ C.X) :
    s * Real.log |C.branchDeriv w x| = C.birkhoffSum (C.geometricPotential s) w x := by
  induction w with
  | nil => simp
  | cons i w ih =>
      have hmem := C.mapsTo_branchMap w hx
      have h1 : C.dF i (C.branchMap w x) ≠ 0 := by
        have h := C.le_abs_dF i _ hmem
        intro hz
        rw [hz, abs_zero] at h
        exact absurd h (not_le.2 C.cmin_pos)
      have h2 : C.branchDeriv w x ≠ 0 := C.branchDeriv_ne_zero w hx
      rw [branchDeriv_cons, abs_mul, Real.log_mul (abs_ne_zero.2 h1) (abs_ne_zero.2 h2),
        birkhoffSum_cons, ← ih]
      simp only [geometricPotential]
      ring

/-! ## Proposition 6.1 (`thm:bounded-variation`) -/

/-- Proposition 6.1 (principle of bounded variation): the Birkhoff sums along a word vary by a
bounded amount over the cylinder, and by a fraction of that bound proportional to the diameter of
the cylinder of the remaining letters. -/
theorem bounded_variation {φ : ι → ℝ → ℝ} {c : ℝ≥0} (hφ : ∀ i, LipschitzOnWith c (φ i) C.X) :
    ∃ b : ℝ, 0 ≤ b ∧
      (∀ w : List ι, ∀ x ∈ C.X, ∀ y ∈ C.X,
          |C.birkhoffSum φ w x - C.birkhoffSum φ w y| ≤ b) ∧
        ∀ (v z : List ι), ∀ x ∈ C.X, ∀ y ∈ C.X,
          |C.birkhoffSum φ v (C.branchMap z x) - C.birkhoffSum φ v (C.branchMap z y)| ≤
            b * diam (C.cylinder z) / diam C.X := by
  have hc : (0 : ℝ) ≤ (c : ℝ) := c.coe_nonneg
  have hmax : 0 < 1 - C.cmax := by linarith [C.cmax_lt_one]
  have hX : 0 < diam C.X := C.diam_X_pos
  have key : ∀ (v : List ι) (u : ℝ), u ∈ C.X → ∀ u' ∈ C.X,
      (1 - C.cmax) * |C.birkhoffSum φ v u - C.birkhoffSum φ v u'| ≤
        (c : ℝ) * |u - u'| * (1 - C.cmax ^ v.length) := by
    intro v
    induction v with
    | nil => intro u _ u' _; simp
    | cons i v ih =>
        intro u hu u' hu'
        haveI : Nonempty ι := ⟨i⟩
        have h1 : |φ i (C.branchMap v u) - φ i (C.branchMap v u')| ≤
            (c : ℝ) * (C.cmax ^ v.length * |u - u'|) := by
          have hl := (hφ i).dist_le_mul _ (C.mapsTo_branchMap v hu) _ (C.mapsTo_branchMap v hu')
          rw [Real.dist_eq, Real.dist_eq] at hl
          refine hl.trans ?_
          gcongr
          exact C.abs_sub_branchMap_le v hu hu'
        have h2 := ih u hu u' hu'
        have habs : |C.birkhoffSum φ (i :: v) u - C.birkhoffSum φ (i :: v) u'| ≤
            |φ i (C.branchMap v u) - φ i (C.branchMap v u')| +
              |C.birkhoffSum φ v u - C.birkhoffSum φ v u'| := by
          rw [birkhoffSum_cons, birkhoffSum_cons]
          have hr : φ i (C.branchMap v u) + C.birkhoffSum φ v u -
              (φ i (C.branchMap v u') + C.birkhoffSum φ v u') =
              (φ i (C.branchMap v u) - φ i (C.branchMap v u')) +
                (C.birkhoffSum φ v u - C.birkhoffSum φ v u') := by ring
          rw [hr]
          exact abs_add_le _ _
        have h3 := mul_le_mul_of_nonneg_left habs hmax.le
        have h4 := mul_le_mul_of_nonneg_left h1 hmax.le
        rw [List.length_cons, pow_succ]
        linarith
  have key' : ∀ (v : List ι) (u : ℝ), u ∈ C.X → ∀ u' ∈ C.X,
      (1 - C.cmax) * |C.birkhoffSum φ v u - C.birkhoffSum φ v u'| ≤ (c : ℝ) * |u - u'| := by
    intro v u hu u' hu'
    cases v with
    | nil => simpa using mul_nonneg hc (abs_nonneg _)
    | cons i v =>
        haveI : Nonempty ι := ⟨i⟩
        have h := key (i :: v) u hu u' hu'
        have hp : 0 ≤ (c : ℝ) * |u - u'| * C.cmax ^ (i :: v).length :=
          mul_nonneg (mul_nonneg hc (abs_nonneg _)) (pow_nonneg C.cmax_pos.le _)
        nlinarith
  have hb0 : 0 ≤ (c : ℝ) * diam C.X / (1 - C.cmax) :=
    div_nonneg (mul_nonneg hc hX.le) hmax.le
  have hsecond : ∀ (v z : List ι), ∀ x ∈ C.X, ∀ y ∈ C.X,
      |C.birkhoffSum φ v (C.branchMap z x) - C.birkhoffSum φ v (C.branchMap z y)| ≤
        (c : ℝ) * diam C.X / (1 - C.cmax) * diam (C.cylinder z) / diam C.X := by
    intro v z x hx y hy
    have hd : |C.branchMap z x - C.branchMap z y| ≤ diam (C.cylinder z) := by
      rw [← Real.dist_eq]
      exact dist_le_diam_of_mem (C.isCompact_cylinder z).isBounded ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    have hk := key' v _ (C.mapsTo_branchMap z hx) _ (C.mapsTo_branchMap z hy)
    have heq : (c : ℝ) * diam C.X / (1 - C.cmax) * diam (C.cylinder z) / diam C.X =
        (c : ℝ) * diam (C.cylinder z) / (1 - C.cmax) := by
      field_simp
    rw [heq, le_div_iff₀ hmax]
    nlinarith
  exact ⟨(c : ℝ) * diam C.X / (1 - C.cmax), hb0, fun w x hx y hy => by
    have h := hsecond w [] x hx y hy
    have hq : (c : ℝ) * diam C.X / (1 - C.cmax) * diam C.X / diam C.X =
        (c : ℝ) * diam C.X / (1 - C.cmax) := by
      field_simp
    simpa [hq] using h, hsecond⟩

/-- The exponential form of Proposition 6.1. -/
theorem exp_birkhoffSum_le {φ : ι → ℝ → ℝ} {c : ℝ≥0} (hφ : ∀ i, LipschitzOnWith c (φ i) C.X) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ w : List ι, ∀ x ∈ C.X, ∀ y ∈ C.X,
      Real.exp (-b) ≤ Real.exp (C.birkhoffSum φ w x) / Real.exp (C.birkhoffSum φ w y) ∧
        Real.exp (C.birkhoffSum φ w x) / Real.exp (C.birkhoffSum φ w y) ≤ Real.exp b := by
  obtain ⟨b, hb0, hb, -⟩ := C.bounded_variation hφ
  refine ⟨b, hb0, fun w x hx y hy => ?_⟩
  have h := abs_sub_le_iff.1 (hb w x hx y hy)
  rw [← Real.exp_sub]
  exact ⟨Real.exp_le_exp.2 (by linarith [h.1, h.2]), Real.exp_le_exp.2 (by linarith [h.1, h.2])⟩

/-! ## Proposition 6.2 (`thm:bounded-distortion`) -/

/-- The mean value theorem for a branch map: the increment of `F_𝐢` between two points of `X` is
the derivative of `F_𝐢` at some point of `X` times the increment. -/
private theorem exists_abs_sub_branchMap_eq (w : List ι) {y z : ℝ} (hy : y ∈ C.X)
    (hz : z ∈ C.X) :
    ∃ ξ ∈ C.X, |C.branchMap w y - C.branchMap w z| = |C.branchDeriv w ξ| * |y - z| := by
  have hmvt : ∀ u ∈ C.X, ∀ v ∈ C.X, u < v → ∃ ξ ∈ C.X,
      C.branchMap w v - C.branchMap w u = C.branchDeriv w ξ * (v - u) := by
    intro u hu v hv huv
    have hsub : Icc u v ⊆ C.X := Icc_subset_Icc hu.1 hv.2
    have hcont : ContinuousOn (C.branchMap w) (Icc u v) := (C.continuousOn_branchMap w).mono hsub
    have hderiv : ∀ t ∈ Ioo u v, HasDerivAt (C.branchMap w) (C.branchDeriv w t) t := by
      intro t ht
      refine (C.hasDerivWithinAt_branchMap w (hsub (Ioo_subset_Icc_self ht))).hasDerivAt ?_
      rw [C.X_eq]
      exact Icc_mem_nhds (lt_of_le_of_lt hu.1 ht.1) (lt_of_lt_of_le ht.2 hv.2)
    obtain ⟨ξ, hξ, hslope⟩ :=
      exists_hasDerivAt_eq_slope (C.branchMap w) (C.branchDeriv w) huv hcont hderiv
    refine ⟨ξ, hsub (Ioo_subset_Icc_self hξ), ?_⟩
    have hne : v - u ≠ 0 := sub_ne_zero.2 huv.ne'
    rw [hslope]
    field_simp
  rcases lt_trichotomy y z with h | h | h
  · obtain ⟨ξ, hξ, he⟩ := hmvt y hy z hz h
    exact ⟨ξ, hξ, by rw [abs_sub_comm (C.branchMap w y), he, abs_mul, abs_sub_comm z y]⟩
  · exact ⟨y, hy, by simp [h]⟩
  · obtain ⟨ξ, hξ, he⟩ := hmvt z hz y hy h
    exact ⟨ξ, hξ, by rw [he, abs_mul]⟩

/-- Proposition 6.2 (principle of bounded distortion): the diameter of a cylinder is comparable to
the derivative of its branch map, and the branch map is bi-Lipschitz with constant comparable to
that diameter. -/
theorem bounded_distortion :
    (∃ b₀ : ℝ, 1 ≤ b₀ ∧ ∀ w : List ι, ∀ x ∈ C.X,
        b₀⁻¹ ≤ diam (C.cylinder w) / |C.branchDeriv w x| ∧
          diam (C.cylinder w) / |C.branchDeriv w x| ≤ b₀) ∧
      ∃ b₁ : ℝ, 1 ≤ b₁ ∧ ∀ w : List ι, ∀ y ∈ C.X, ∀ z ∈ C.X,
        b₁⁻¹ * diam (C.cylinder w) * |y - z| ≤ |C.branchMap w y - C.branchMap w z| ∧
          |C.branchMap w y - C.branchMap w z| ≤ b₁ * diam (C.cylinder w) * |y - z| := by
  have hX : 0 < diam C.X := C.diam_X_pos
  have hlip : ∀ i, LipschitzOnWith C.L (C.geometricPotential 1 i) C.X := by
    intro i
    have he : C.geometricPotential 1 i = fun u => Real.log |C.dF i u| := by
      funext u
      simp [geometricPotential]
    rw [he]
    exact C.lipschitzOnWith_log_abs_dF i
  obtain ⟨b, -, hb, -⟩ := C.bounded_variation hlip
  have hlogb : ∀ (w : List ι), ∀ x ∈ C.X, ∀ y ∈ C.X,
      abs (Real.log |C.branchDeriv w x| - Real.log |C.branchDeriv w y|) ≤ b := by
    intro w x hx y hy
    have h := hb w x hx y hy
    rw [← C.log_abs_branchDeriv 1 w hx, ← C.log_abs_branchDeriv 1 w hy] at h
    simpa using h
  have hratio : ∀ (w : List ι), ∀ x ∈ C.X, ∀ y ∈ C.X,
      |C.branchDeriv w x| ≤ Real.exp b * |C.branchDeriv w y| := by
    intro w x hx y hy
    have hdx : 0 < |C.branchDeriv w x| := abs_pos.2 (C.branchDeriv_ne_zero w hx)
    have hdy : 0 < |C.branchDeriv w y| := abs_pos.2 (C.branchDeriv_ne_zero w hy)
    have h := abs_sub_le_iff.1 (hlogb w x hx y hy)
    calc |C.branchDeriv w x| = Real.exp (Real.log |C.branchDeriv w x|) := (Real.exp_log hdx).symm
      _ ≤ Real.exp (b + Real.log |C.branchDeriv w y|) := Real.exp_le_exp.2 (by linarith [h.1])
      _ = Real.exp b * |C.branchDeriv w y| := by rw [Real.exp_add, Real.exp_log hdy]
  have hupper : ∀ (w : List ι), ∀ x ∈ C.X,
      diam (C.cylinder w) ≤ Real.exp b * |C.branchDeriv w x| * diam C.X := by
    intro w x hx
    have hnn : (0:ℝ) ≤ Real.exp b * |C.branchDeriv w x| :=
      mul_nonneg (Real.exp_pos b).le (abs_nonneg _)
    refine diam_le_of_forall_dist_le (mul_nonneg hnn diam_nonneg) ?_
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    obtain ⟨ξ, hξ, he⟩ := C.exists_abs_sub_branchMap_eq w hu hv
    rw [Real.dist_eq, he]
    have h2 : |u - v| ≤ diam C.X := by
      rw [← Real.dist_eq]
      exact dist_le_diam_of_mem C.isCompact_X.isBounded hu hv
    calc |C.branchDeriv w ξ| * |u - v| ≤ Real.exp b * |C.branchDeriv w x| * diam C.X :=
          mul_le_mul (hratio w ξ hξ x hx) h2 (abs_nonneg _) hnn
      _ = Real.exp b * |C.branchDeriv w x| * diam C.X := rfl
  have hlower : ∀ (w : List ι), ∀ x ∈ C.X,
      Real.exp (-b) * |C.branchDeriv w x| * diam C.X ≤ diam (C.cylinder w) := by
    intro w x hx
    have ha : C.a ∈ C.X := left_mem_Icc.2 C.lt_ab.le
    have hbb : C.b ∈ C.X := right_mem_Icc.2 C.lt_ab.le
    obtain ⟨ξ, hξ, he⟩ := C.exists_abs_sub_branchMap_eq w ha hbb
    have hd : |C.branchMap w C.a - C.branchMap w C.b| ≤ diam (C.cylinder w) := by
      rw [← Real.dist_eq]
      exact dist_le_diam_of_mem (C.isCompact_cylinder w).isBounded ⟨C.a, ha, rfl⟩ ⟨C.b, hbb, rfl⟩
    have hab : |C.a - C.b| = diam C.X := by
      rw [C.diam_X, abs_sub_comm, abs_of_nonneg (by linarith [C.lt_ab])]
    have h1 : Real.exp (-b) * |C.branchDeriv w x| ≤ |C.branchDeriv w ξ| := by
      calc Real.exp (-b) * |C.branchDeriv w x|
          ≤ Real.exp (-b) * (Real.exp b * |C.branchDeriv w ξ|) :=
            mul_le_mul_of_nonneg_left (hratio w x hx ξ hξ) (Real.exp_pos _).le
        _ = |C.branchDeriv w ξ| := by rw [← mul_assoc, ← Real.exp_add]; simp
    rw [← hab]
    refine le_trans (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) ?_
    rw [← he]
    exact hd
  have hfirst : ∃ b₀ : ℝ, 1 ≤ b₀ ∧ ∀ w : List ι, ∀ x ∈ C.X,
      b₀⁻¹ ≤ diam (C.cylinder w) / |C.branchDeriv w x| ∧
        diam (C.cylinder w) / |C.branchDeriv w x| ≤ b₀ := by
    refine ⟨max 1 (max (Real.exp b * diam C.X) (Real.exp b / diam C.X)), le_max_left _ _, ?_⟩
    set b₀ := max 1 (max (Real.exp b * diam C.X) (Real.exp b / diam C.X)) with hb₀def
    have hb₀pos : (0:ℝ) < b₀ := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hup : Real.exp b * diam C.X ≤ b₀ := le_max_of_le_right (le_max_left _ _)
    have hdown : Real.exp b / diam C.X ≤ b₀ := le_max_of_le_right (le_max_right _ _)
    have hinv : b₀⁻¹ ≤ Real.exp (-b) * diam C.X := by
      have hnn : (0:ℝ) ≤ Real.exp (-b) * diam C.X := mul_nonneg (Real.exp_pos _).le diam_nonneg
      have h3 := mul_le_mul_of_nonneg_left hdown hnn
      have h2 : Real.exp (-b) * diam C.X * (Real.exp b / diam C.X) = 1 := by
        field_simp [Real.exp_neg]
        rw [← Real.exp_add]
        simp
      rw [h2] at h3
      rw [inv_eq_one_div, div_le_iff₀ hb₀pos]
      exact h3
    intro w x hx
    have hdx : 0 < |C.branchDeriv w x| := abs_pos.2 (C.branchDeriv_ne_zero w hx)
    constructor
    · rw [le_div_iff₀ hdx]
      calc b₀⁻¹ * |C.branchDeriv w x| ≤ Real.exp (-b) * diam C.X * |C.branchDeriv w x| :=
            mul_le_mul_of_nonneg_right hinv hdx.le
        _ = Real.exp (-b) * |C.branchDeriv w x| * diam C.X := by ring
        _ ≤ diam (C.cylinder w) := hlower w x hx
    · rw [div_le_iff₀ hdx]
      calc diam (C.cylinder w) ≤ Real.exp b * |C.branchDeriv w x| * diam C.X := hupper w x hx
        _ = Real.exp b * diam C.X * |C.branchDeriv w x| := by ring
        _ ≤ b₀ * |C.branchDeriv w x| := mul_le_mul_of_nonneg_right hup hdx.le
  refine ⟨hfirst, ?_⟩
  obtain ⟨b₀, hb₀1, hb₀⟩ := hfirst
  refine ⟨b₀, hb₀1, fun w y hy z hz => ?_⟩
  have hb0pos : (0:ℝ) < b₀ := lt_of_lt_of_le one_pos hb₀1
  obtain ⟨ξ, hξ, he⟩ := C.exists_abs_sub_branchMap_eq w hy hz
  have hd : 0 < |C.branchDeriv w ξ| := abs_pos.2 (C.branchDeriv_ne_zero w hξ)
  obtain ⟨h1, h2⟩ := hb₀ w ξ hξ
  rw [le_div_iff₀ hd] at h1
  rw [div_le_iff₀ hd] at h2
  have hlow : b₀⁻¹ * diam (C.cylinder w) ≤ |C.branchDeriv w ξ| := by
    have h := mul_le_mul_of_nonneg_left h2 (inv_pos.2 hb0pos).le
    rwa [← mul_assoc, inv_mul_cancel₀ hb0pos.ne', one_mul] at h
  have hhigh : |C.branchDeriv w ξ| ≤ b₀ * diam (C.cylinder w) := by
    have h := mul_le_mul_of_nonneg_left h1 hb0pos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hb0pos.ne', one_mul] at h
  rw [he]
  exact ⟨mul_le_mul_of_nonneg_right hlow (abs_nonneg _),
    mul_le_mul_of_nonneg_right hhigh (abs_nonneg _)⟩

/-! ## Corollary 6.3 (`thm:cookie-cutter-separation`) -/

/-- Corollary 6.3 (`thm:cookie-cutter-separation`), first part: the children of a cylinder are
separated by a fixed fraction of its diameter. -/
theorem cookie_cutter_separation [Finite ι] [Nonempty ι] :
    ∃ d : ℝ, 0 < d ∧ ∀ (w : List ι) (i j : ι), i ≠ j →
      ∀ y ∈ C.cylinder (w ++ [i]), ∀ z ∈ C.cylinder (w ++ [j]),
        d * diam (C.cylinder w) ≤ |y - z| ∧ |y - z| ≤ diam (C.cylinder w) := by
  obtain ⟨-, b₁, hb₁1, hb₁⟩ := C.bounded_distortion
  have hb₁0 : (0:ℝ) < b₁ := lt_of_lt_of_le one_pos hb₁1
  haveI : Fintype ι := Fintype.ofFinite ι
  have hsep : ∀ p : ι × ι, ∃ e : ℝ, 0 < e ∧
      (p.1 ≠ p.2 → ∀ y ∈ C.cylinder [p.1], ∀ z ∈ C.cylinder [p.2], e ≤ |y - z|) := by
    intro p
    by_cases hij : p.1 = p.2
    · exact ⟨1, one_pos, fun h => absurd hij h⟩
    · obtain ⟨q, hq, hmin⟩ :=
        ((C.isCompact_cylinder [p.1]).prod (C.isCompact_cylinder [p.2])).exists_isMinOn
          ((C.cylinder_nonempty [p.1]).prod (C.cylinder_nonempty [p.2]))
          (continuous_abs.comp (continuous_fst.sub continuous_snd)).continuousOn
      refine ⟨|q.1 - q.2|, ?_, fun _ y hy z hz => isMinOn_iff.1 hmin (y, z) ⟨hy, hz⟩⟩
      rw [abs_pos, sub_ne_zero]
      intro hq12
      have hdisj : Disjoint (C.cylinder [p.1]) (C.cylinder [p.2]) :=
        C.disjoint_cylinder rfl (by simpa using hij)
      exact Set.disjoint_left.1 hdisj hq.1 (hq12 ▸ hq.2)
  choose e he0 he using hsep
  set d₀ := Finset.univ.inf' Finset.univ_nonempty e with hd₀def
  have hd₀pos : 0 < d₀ := by
    rw [hd₀def, Finset.lt_inf'_iff]
    exact fun p _ => he0 p
  have hd₀le : ∀ p : ι × ι, d₀ ≤ e p := fun p => Finset.inf'_le _ (Finset.mem_univ p)
  refine ⟨b₁⁻¹ * d₀, mul_pos (inv_pos.2 hb₁0) hd₀pos, ?_⟩
  intro w i j hij y hy z hz
  rw [C.cylinder_append_eq w [i]] at hy
  rw [C.cylinder_append_eq w [j]] at hz
  obtain ⟨y', hy', rfl⟩ := hy
  obtain ⟨z', hz', rfl⟩ := hz
  have hy'X : y' ∈ C.X := C.cylinder_subset_X [i] hy'
  have hz'X : z' ∈ C.X := C.cylinder_subset_X [j] hz'
  have hnn : (0:ℝ) ≤ b₁⁻¹ * diam (C.cylinder w) :=
    mul_nonneg (inv_nonneg.2 hb₁0.le) diam_nonneg
  refine ⟨?_, ?_⟩
  · have h2 : d₀ ≤ |y' - z'| := (hd₀le (i, j)).trans (he (i, j) hij y' hy' z' hz')
    calc b₁⁻¹ * d₀ * diam (C.cylinder w) = b₁⁻¹ * diam (C.cylinder w) * d₀ := by ring
      _ ≤ b₁⁻¹ * diam (C.cylinder w) * |y' - z'| := mul_le_mul_of_nonneg_left h2 hnn
      _ ≤ |C.branchMap w y' - C.branchMap w z'| := (hb₁ w y' hy'X z' hz'X).1
  · rw [← Real.dist_eq]
    exact dist_le_diam_of_mem (C.isCompact_cylinder w).isBounded ⟨y', hy'X, rfl⟩ ⟨z', hz'X, rfl⟩

/-- Distinct cylinders of the same length are separated by a fixed fraction of their diameter. -/
theorem separated_cylinder [Finite ι] [Nonempty ι] :
    ∃ d : ℝ, 0 < d ∧ ∀ (v w : List ι), v.length = w.length → v ≠ w →
      ∀ y ∈ C.cylinder v, ∀ z ∈ C.cylinder w, d * diam (C.cylinder v) ≤ |y - z| := by
  obtain ⟨d, hd, hsep⟩ := C.cookie_cutter_separation
  have key : ∀ v w : List ι, v.length = w.length → v ≠ w →
      ∃ (p v' w' : List ι) (i j : ι), i ≠ j ∧ v = p ++ i :: v' ∧ w = p ++ j :: w' := by
    intro v
    induction v with
    | nil =>
        intro w hlen hne
        cases w with
        | nil => exact absurd rfl hne
        | cons j w => simp at hlen
    | cons i v ih =>
        intro w hlen hne
        cases w with
        | nil => simp at hlen
        | cons j w =>
            by_cases hij : i = j
            · subst hij
              have hne' : v ≠ w := fun h => hne (by rw [h])
              obtain ⟨p, v', w', i', j', hij', hv, hw⟩ := ih w (by simpa using hlen) hne'
              exact ⟨i :: p, v', w', i', j', hij', by rw [hv]; rfl, by rw [hw]; rfl⟩
            · exact ⟨[], v, w, i, j, hij, rfl, rfl⟩
  refine ⟨d, hd, ?_⟩
  intro v w hlen hne y hy z hz
  obtain ⟨p, v', w', i, j, hij, rfl, rfl⟩ := key v w hlen hne
  have hvsub : C.cylinder (p ++ i :: v') ⊆ C.cylinder (p ++ [i]) := by
    have hp : p ++ i :: v' = (p ++ [i]) ++ v' := by simp
    rw [hp]
    exact C.cylinder_append_subset _ _
  have hwsub : C.cylinder (p ++ j :: w') ⊆ C.cylinder (p ++ [j]) := by
    have hp : p ++ j :: w' = (p ++ [j]) ++ w' := by simp
    rw [hp]
    exact C.cylinder_append_subset _ _
  have h := (hsep p i j hij y (hvsub hy) z (hwsub hz)).1
  have hd2 : diam (C.cylinder (p ++ i :: v')) ≤ diam (C.cylinder p) :=
    diam_mono (hvsub.trans (C.cylinder_append_subset p [i])) (C.isCompact_cylinder p).isBounded
  exact le_trans (mul_le_mul_of_nonneg_left hd2 hd.le) h

/-- Corollary 6.3 (`thm:cookie-cutter-separation`), second part: at the scale of its own diameter a
cylinder is squeezed between two balls around any of its points. -/
theorem cookie_cutter_separation_ball [Finite ι] [Nonempty ι] :
    ∃ lam : ℝ, 0 < lam ∧ ∀ w : List ι, ∀ x ∈ C.cylinder w ∩ C.attractor, ∀ r : ℝ,
      diam (C.cylinder w) ≤ r → C.cmin * r < diam (C.cylinder w) →
        ball x (lam * r) ∩ C.attractor ⊆ C.cylinder w ∩ C.attractor ∧
          C.cylinder w ∩ C.attractor ⊆ closedBall x r := by
  obtain ⟨d, hd, hsep⟩ := C.separated_cylinder
  refine ⟨d * C.cmin, mul_pos hd C.cmin_pos, ?_⟩
  intro w x hx r hr1 hr2
  refine ⟨?_, ?_⟩
  · rintro y ⟨hy1, hy2⟩
    refine ⟨?_, hy2⟩
    obtain ⟨v, hvlen, hv⟩ := C.exists_cylinder_mem hy2 w.length
    by_cases hvw : v = w
    · rwa [hvw] at hv
    · exfalso
      have h := hsep w v hvlen.symm (Ne.symm hvw) x hx.1 y hv
      have hxy : |x - y| < d * C.cmin * r := by
        have hb := mem_ball.1 hy1
        rwa [Real.dist_eq, abs_sub_comm] at hb
      nlinarith [mul_lt_mul_of_pos_left hr2 hd]
  · rintro y ⟨hy1, -⟩
    exact mem_closedBall.2
      ((dist_le_diam_of_mem (C.isCompact_cylinder w).isBounded hy1 hx.1).trans hr1)

/-- Appending a letter to a word shrinks the diameter of its cylinder by at most a fixed factor. -/
private theorem exists_le_diam_cylinder_append :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧ ∀ (u : List ι) (i : ι),
      κ * diam (C.cylinder u) ≤ diam (C.cylinder (u ++ [i])) := by
  obtain ⟨-, b₁, hb₁1, hb₁⟩ := C.bounded_distortion
  have hb₁0 : (0:ℝ) < b₁ := lt_of_lt_of_le one_pos hb₁1
  have hX := C.diam_X_pos
  refine ⟨min 1 (b₁⁻¹ * (C.cmin * diam C.X)),
    lt_min one_pos (mul_pos (inv_pos.2 hb₁0) (mul_pos C.cmin_pos hX)), min_le_left _ _, ?_⟩
  intro u i
  have ha : C.a ∈ C.X := left_mem_Icc.2 C.lt_ab.le
  have hbb : C.b ∈ C.X := right_mem_Icc.2 C.lt_ab.le
  have hya : C.branchMap [i] C.a ∈ C.X := C.mapsTo_branchMap [i] ha
  have hyb : C.branchMap [i] C.b ∈ C.X := C.mapsTo_branchMap [i] hbb
  have hab : |C.a - C.b| = diam C.X := by
    rw [C.diam_X, abs_sub_comm, abs_of_nonneg (by linarith [C.lt_ab])]
  have hsep : C.cmin * diam C.X ≤ |C.branchMap [i] C.a - C.branchMap [i] C.b| := by
    have h := C.le_abs_sub_branchMap [i] ha hbb
    rw [List.length_singleton, pow_one, hab] at h
    exact h
  have hmem : ∀ t ∈ C.X, C.branchMap u (C.branchMap [i] t) ∈ C.cylinder (u ++ [i]) := by
    intro t ht
    refine ⟨t, ht, ?_⟩
    rw [C.branchMap_append u [i]]
    rfl
  have hdiam : |C.branchMap u (C.branchMap [i] C.a) - C.branchMap u (C.branchMap [i] C.b)| ≤
      diam (C.cylinder (u ++ [i])) := by
    rw [← Real.dist_eq]
    exact dist_le_diam_of_mem (C.isCompact_cylinder _).isBounded (hmem C.a ha) (hmem C.b hbb)
  have hnn : (0:ℝ) ≤ b₁⁻¹ * diam (C.cylinder u) :=
    mul_nonneg (inv_nonneg.2 hb₁0.le) diam_nonneg
  calc min 1 (b₁⁻¹ * (C.cmin * diam C.X)) * diam (C.cylinder u)
      ≤ b₁⁻¹ * (C.cmin * diam C.X) * diam (C.cylinder u) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) diam_nonneg
    _ = b₁⁻¹ * diam (C.cylinder u) * (C.cmin * diam C.X) := by ring
    _ ≤ b₁⁻¹ * diam (C.cylinder u) * |C.branchMap [i] C.a - C.branchMap [i] C.b| :=
        mul_le_mul_of_nonneg_left hsep hnn
    _ ≤ |C.branchMap u (C.branchMap [i] C.a) - C.branchMap u (C.branchMap [i] C.b)| :=
        (hb₁ u _ hya _ hyb).1
    _ ≤ diam (C.cylinder (u ++ [i])) := hdiam

/-- Every ball centred on the repeller contains a cylinder of comparable diameter through its
centre. This is the geometric input to Theorem 7.11 and to Corollary 6.6. -/
theorem exists_cylinder_subset_closedBall [Finite ι] [Nonempty ι] :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ C.attractor, ∀ r : ℝ, 0 < r → r ≤ diam C.X →
      ∃ w : List ι, x ∈ C.cylinder w ∧ C.cylinder w ⊆ closedBall x r ∧
        c * r ≤ diam (C.cylinder w) := by
  obtain ⟨κ, hκ0, hκ1, hκ⟩ := C.exists_le_diam_cylinder_append
  refine ⟨κ, hκ0, ?_⟩
  intro x hx r hr hrX
  have aux : ∀ w : List ι, x ∈ C.cylinder w → diam (C.cylinder w) ≤ r →
      ∃ v : List ι, x ∈ C.cylinder v ∧ C.cylinder v ⊆ closedBall x r ∧
        κ * r ≤ diam (C.cylinder v) := by
    intro w
    induction w using List.reverseRecOn with
    | nil =>
        intro hx0 hdm
        refine ⟨[], hx0, fun y hy => mem_closedBall.2 ?_, ?_⟩
        · exact (dist_le_diam_of_mem (C.isCompact_cylinder []).isBounded hy hx0).trans hdm
        · rw [C.cylinder_nil]
          calc κ * r ≤ 1 * r := mul_le_mul_of_nonneg_right hκ1 hr.le
            _ = r := one_mul r
            _ ≤ diam C.X := hrX
    | append_singleton u i ih =>
        intro hx0 hdm
        rcases le_or_gt (diam (C.cylinder u)) r with hcase | hcase
        · exact ih (C.cylinder_append_subset u [i] hx0) hcase
        · refine ⟨u ++ [i], hx0, fun y hy => mem_closedBall.2 ?_, ?_⟩
          · exact (dist_le_diam_of_mem (C.isCompact_cylinder _).isBounded hy hx0).trans hdm
          · calc κ * r ≤ κ * diam (C.cylinder u) := mul_le_mul_of_nonneg_left hcase.le hκ0.le
              _ ≤ diam (C.cylinder (u ++ [i])) := hκ u i
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (div_pos hr C.diam_X_pos) C.cmax_lt_one
  obtain ⟨w, hwlen, hw⟩ := C.exists_cylinder_mem hx K
  refine aux w hw ?_
  have hle := C.diam_cylinder_le w
  rw [hwlen] at hle
  exact hle.trans ((lt_div_iff₀ C.diam_X_pos).1 hK).le

/-- Conversely, every ball centred on the repeller is contained in a cylinder of comparable
diameter, after shrinking the radius by a fixed factor. -/
theorem exists_closedBall_subset_cylinder [Finite ι] [Nonempty ι] :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ C.attractor, ∀ r : ℝ, 0 < r → r ≤ C.cmin * diam C.X →
      ∃ w : List ι, x ∈ C.cylinder w ∧ ball x (c * r) ∩ C.attractor ⊆ C.cylinder w ∧
        diam (C.cylinder w) ≤ r := by
  obtain ⟨c₁, hc₁, hcyl⟩ := C.exists_cylinder_subset_closedBall
  obtain ⟨d, hd, hsep⟩ := C.separated_cylinder
  refine ⟨d * c₁ / 2, by positivity, ?_⟩
  intro x hx r hr hrX
  have hr2 : (0:ℝ) < r / 2 := by linarith
  have hrX2 : r / 2 ≤ diam C.X := by
    nlinarith [mul_pos (sub_pos.2 C.cmin_lt_one) C.diam_X_pos, C.diam_X_pos]
  obtain ⟨w, hxw, hsub, hlow⟩ := hcyl x hx (r / 2) hr2 hrX2
  refine ⟨w, hxw, ?_, ?_⟩
  · rintro y ⟨hy1, hy2⟩
    obtain ⟨v, hvlen, hv⟩ := C.exists_cylinder_mem hy2 w.length
    by_cases hvw : v = w
    · rwa [hvw] at hv
    · exfalso
      have h := hsep w v hvlen.symm (Ne.symm hvw) x hxw y hv
      have hxy : |x - y| < d * c₁ / 2 * r := by
        have hb := mem_ball.1 hy1
        rwa [Real.dist_eq, abs_sub_comm] at hb
      linarith [mul_le_mul_of_nonneg_left hlow hd.le]
  · have hb := diam_mono hsub (isBounded_closedBall (x := x) (r := r / 2))
    have hcb := diam_closedBall (x := x) hr2.le
    linarith

end CookieCutter

end GeometricMeasureTheory
