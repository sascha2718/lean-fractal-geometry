module

/-
Fraser's modified singular value function and the modified affinity dimension `dimmaff(X)` of
`sec:affinity_dim` (tex lines 2077 to 2077), after Fraser, "On the packing dimension of box-like
self-affine sets in the plane", §2.1 (numbering of arXiv:1108.2639v1).

For a word `𝐢` the rectangle `A_𝐢([0,1]²)` has base `b(𝐢) = |a_𝐢|` and height `h(𝐢) = |b_𝐢|`,
the moduli of the entries of the first and second row of `A_𝐢`. Fraser sets
`s(𝐢) = \dim_B π_𝐢(X)`, where `π_𝐢 X` is the coordinate projection of `X` whose similar copy is
the projection of `φ_𝐢(X)` onto the longer side of the rectangle: `π_𝐢 = proj_x` when `A_𝐢` is
diagonal and `b(𝐢) ≥ h(𝐢)` or `A_𝐢` is anti-diagonal and `b(𝐢) < h(𝐢)`, and `π_𝐢 = proj_y`
otherwise. A square, `b(𝐢) = h(𝐢)`, counts as a rectangle whose longer side is its base; since
`α_1(𝐢) = α_2(𝐢)` for a square, the choice does not affect `ψ^s`. The modified singular value
function is `ψ^s(𝐢) = α_1(𝐢)^{s(𝐢)} α_2(𝐢)^{s - s(𝐢)}`. Fraser records after his Lemma 2.7 that
the Minkowski dimensions of the two projections exist. `System.projDim` is defined through
`upperBoxDim`, and `System.lowerBoxDim_coord_eq` proves that the lower Minkowski dimension is the
same, by super-multiplicativity of the covering counts, so `s_1` and `s_2` are Fraser's numbers.
The modified pressure is defined as the `lim sup` of `n⁻¹ log ∑_{|𝐢| = n} ψ^s(𝐢)`, and
`System.tendsto_modPressure` shows that it is a limit, as in Fraser's Lemma 2.1.

* `System.projDim`, `System.projDim_le_one`, `System.projDim_eq`: the numbers
  `s_1 = \overline{\dim}_M proj_x(X)` and `s_2 = \overline{\dim}_M proj_y(X)`, which are at
  most `1` and agree when some generator is anti-diagonal.
* `System.exists_affine_copy`, `System.lowerBoxDim_coord_eq`, `System.projDim_eq_lowerBoxDim`:
  every small ball about a point of `proj_c(X)` contains an affine copy of `proj_c(X)` of
  comparable size, so the Minkowski dimension of `proj_c(X)` exists.
* `System.wordBase`, `System.wordHeight`, `System.alpha₁`, `System.alpha₂`, `System.wordDim`,
  `System.modSvf`: the sides of `A_𝐢([0,1]²)`, the singular values, `s(𝐢)` and `ψ^s(𝐢)`.
* `System.wordDim_eq_axis`: `s(𝐢)` is also the dimension of the projection of `X` onto the axis
  parallel to the longer side, the description of tex lines 2077 to 2077.
* `System.modSvf_add`, `System.modSvf_of_wordBase_eq`: `ψ^{s+δ}(𝐢) = α_2(𝐢)^δ ψ^s(𝐢)`, and
  `ψ^s(𝐢) = α_1(𝐢)^s` for a square.
* `System.modSvf_le_svf`, `System.svf_le_modSvf`: `ψ^s(𝐢) ≤ φ^s(A_𝐢)` when `s(𝐢) ≤ p(s)` and
  the reverse inequality when `p(s) ≤ s(𝐢)`, with `p(s)` the exponent `svfExp s` of `α_1` in
  `φ^s`.
* `System.modSvf_append_le`, `System.le_modSvf_append`, `System.modSvfSum_add_le`,
  `System.le_modSvfSum_add`: Fraser's Lemma 2.1, `ψ^s` and the sums `Ψ_n^s` are
  sub-multiplicative for `s ≤ s_1 + s_2` and super-multiplicative for `s ≥ s_1 + s_2`.
* `System.modSvfSum`, `System.modPressure`, `System.exists_modPressure_increment`,
  `System.tendsto_modPressure`: the sums `Ψ_n^s = ∑_{|𝐢| = n} ψ^s(𝐢)`, the modified pressure,
  its slope bounds, and the existence of the limit defining it.
* `System.dimmaff`, `System.modPressure_dimmaff`, `System.dimmaff_eq`: the modified affinity
  dimension, the unique zero of the modified pressure on `[0, ∞)`.
* `System.upperBoxDim_coord_le_of_pressure_neg`, `System.upperBoxDim_coord_le_dimaff`,
  `System.projDim_le_dimaff`: Falconer's covering argument for the coordinate projections,
  `s_1, s_2 ≤ dimaff(X)`.
* `System.modPressure_le_pressure`, `System.dimmaff_le_dimaff_of_projDim_le`,
  `System.dimmaff_le_dimaff`: `dimmaff(X) ≤ dimaff(X)`.
* `System.modPressure_eq_pressure`, `System.dimmaff_eq_dimaff_of_projDim_eq_one`,
  `System.dimaff_eq_dimmaff_of_projDim_eq_one`, `System.dimmaff_eq_dimaff_of_full`: the pressure
  part of Fraser's Corollary 2.5, `dimmaff(X) = dimaff(X)` when `s_1 = s_2 = 1` and the dimension
  lies in `[1, 2]`, in particular when `s_1 = s_2 = 1` and `dimaff(X) ≤ 2`.
* `System.modSvf_eq_norm_det`: `ψ^s(𝐢) = ‖A_𝐢‖^{2t-s} |det A_𝐢|^{s-t}` when `s_1 = s_2 = t`.
-/
public import BoxLike.AffinityDim
public import BoxLike.Attractor
public import BoxLike.SetDimensions
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

@[expose] public section

namespace BoxLike

open Filter Topology Matrix
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-! ### Two real-variable lemmas -/

/-- `x^d y^{s-d}` is non-decreasing in `d` for `0 < y ≤ x`. -/
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

/-- A function on `[0, ∞)` with `f(0) ≥ 0` whose increments satisfy
`(t - s) c₁ ≤ f(t) - f(s) ≤ (t - s) c₂` for `0 ≤ s ≤ t`, with `c₂ < 0`, has a unique zero on
`[0, ∞)`. This is the argument of `sec:affinity_dim` for the pressure. -/
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

/-- An affine bijection of the line preserves the upper Minkowski dimension. -/
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

namespace System

variable {ι : Type*} (S : System ι)

/-! ### The Minkowski dimensions of the coordinate projections -/

/-- The number `s_1` for `c = 0` and `s_2` for `c = 1` of Fraser, §2.1: the Minkowski dimension
of the coordinate projection `proj_c(X)`. It is the upper Minkowski dimension, converted to a
real number; it is finite by `projDim_le_one`, and the lower Minkowski dimension has the same
value by `lowerBoxDim_coord_eq`. -/
noncomputable def projDim (c : ZMod 2) : ℝ := (upperBoxDim (coord c '' S.attractor)).toReal

/-- `s_1, s_2 ≥ 0`. -/
theorem projDim_nonneg (c : ZMod 2) : 0 ≤ S.projDim c := ENNReal.toReal_nonneg

/-- The coordinate projections are continuous. -/
theorem continuous_coord (c : ZMod 2) : Continuous (coord c) := by
  unfold coord
  split_ifs <;> fun_prop

/-- The coordinate projections are `1`-Lipschitz for the sup metric of the plane. -/
theorem lipschitzWith_coord (c : ZMod 2) : LipschitzWith 1 (coord c) :=
  LipschitzWith.of_dist_le_mul fun z w => by
    rw [Real.dist_eq, NNReal.coe_one, one_mul]
    exact abs_coord_sub_le c z w

/-- A bounded subset of the line has upper Minkowski dimension at most `1`, so the projections
of `X` do. -/
theorem upperBoxDim_coord_le_one [Finite ι] (c : ZMod 2) :
    upperBoxDim (coord c '' S.attractor) ≤ 1 :=
  upperBoxDim_le_one (S.isCompact_attractor.image (continuous_coord c)).isBounded

/-- `s_1, s_2 ≤ 1`. -/
theorem projDim_le_one [Finite ι] (c : ZMod 2) : S.projDim c ≤ 1 := by
  have h := ENNReal.toReal_mono ENNReal.one_ne_top (S.upperBoxDim_coord_le_one c)
  rwa [ENNReal.toReal_one] at h

/-- The projection `proj_c(X)` contains the similar copy `g_{(i,c)}(proj_{c + o(i)}(X))` of
`proj_{c + o(i)}(X)`, by `eq:phi_def_by_g`. -/
theorem upperBoxDim_coord_add_le [Finite ι] (i : ι) (c : ZMod 2) :
    upperBoxDim (coord (c + S.o i) '' S.attractor) ≤ upperBoxDim (coord c '' S.attractor) := by
  have hsub : (fun t : ℝ => S.ratio (i, c) * t + S.trans (i, c)) ''
      (coord (c + S.o i) '' S.attractor) ⊆ coord c '' S.attractor := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨S.phi i z, S.image_attractor_subset i ⟨z, hz, rfl⟩, S.coord_phi c i z⟩
  rw [← upperBoxDim_image_affine (S.ratio_ne_zero (i, c)) (S.trans (i, c))]
  exact upperBoxDim_mono hsub

/-- For a system with an anti-diagonal generator the two coordinate projections of `X` have the
same upper Minkowski dimension: each contains a similar copy of the other. This is the
identity `s_1 = s_2` of Fraser, Lemma 2.7, for sets of non-separated type. -/
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

/-- `s_1 = s_2` for a system with an anti-diagonal generator, in particular for a system with
rotations. -/
theorem projDim_eq [Finite ι] (h : ∃ i, S.o i = 1) (c c' : ZMod 2) :
    S.projDim c = S.projDim c' := by
  rw [projDim, projDim, S.upperBoxDim_coord_eq h c c']

/-! ### Existence of the Minkowski dimensions of the projections -/

/-- `φ_{𝐢𝐣} = φ_𝐢 ∘ φ_𝐣`. -/
theorem phiWord_append (w w' : List ι) : S.phiWord (w ++ w') = S.phiWord w ∘ S.phiWord w' := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [List.cons_append, phiWord_cons, phiWord_cons, ih, Function.comp_assoc]

/-- `φ_𝐢(X) ⊆ X`. -/
theorem phiWord_image_attractor_subset [Finite ι] (w : List ι) :
    S.phiWord w '' S.attractor ⊆ S.attractor := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [phiWord_cons, Set.image_comp]
    exact (Set.image_mono ih).trans (S.image_attractor_subset i)

/-- The derivative along the path of `Σ_Z` over `i𝐣` starting on the axis `c`. -/
theorem abs_gDeriv_codeWord_cons (c : ZMod 2) (i : ι) (w : List ι) :
    |S.gDeriv (S.codeWord c (i :: w))| =
      |S.ratio (i, c)| * |S.gDeriv (S.codeWord (c + S.o i) w)| := by
  rw [codeWord_cons, gDeriv_cons, abs_mul]

/-- The stopping argument: for `0 < ρ ≤ 1` every point `z ∈ X` lies in a copy `φ_𝐢(X)` whose side
`|g'|` along the axis `c` lies between `δ₀ρ` and `ρ`, where `δ₀ ≤ |a_i|, |b_i| ≤ r`. The induction
runs over a `k` with `r^k ≤ ρ`. -/
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

/-- A word `𝐢` extends by at most one letter to a word `𝐢'` with `A_{𝐢'}` diagonal: a word with an
anti-diagonal product contains an anti-diagonal letter `j`, and `𝐢' = 𝐢j`. The copy `φ_{𝐢'}(X)`
lies in `φ_𝐢(X)`, and its side along the axis `c` is at least `δ₀` times that of `φ_𝐢(X)`. -/
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

/-- Every closed ball of radius `ρ ≤ 1` about a point of `proj_c(X)` contains an affine copy
`t ↦ at + b` of `proj_c(X)` with `|a| ≥ κρ`, for a constant `κ > 0` of the system: the copy is
`proj_c(φ_{𝐢'}(X))` for a diagonal `A_{𝐢'}`. -/
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

/-- The covering counts of `proj_c(X)` are super-multiplicative, so its lower and upper Minkowski
dimensions agree. A `τ`-separated set of `N_τ` points of `proj_c(X)` gives disjoint balls of
radius `τ/4`, each containing an affine copy of `proj_c(X)` with ratio at least `κτ/4`, and each
copy needs `N_σ` balls of radius `κτσ/4`. -/
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

/-- The Minkowski dimension of each coordinate projection of `X` exists, as Fraser records after
his Lemma 2.7. -/
theorem lowerBoxDim_coord_eq [Finite ι] [Nonempty ι] (c : ZMod 2) :
    lowerBoxDim (coord c '' S.attractor) = upperBoxDim (coord c '' S.attractor) :=
  le_antisymm (lowerBoxDim_le_upperBoxDim _) (S.upperBoxDim_coord_le_lowerBoxDim c)

/-- `s_1` and `s_2` are the Minkowski dimensions `\dim_M proj_x(X)` and `\dim_M proj_y(X)` of
Fraser, §2.1: the lower Minkowski dimension gives the same number. -/
theorem projDim_eq_lowerBoxDim [Finite ι] [Nonempty ι] (c : ZMod 2) :
    S.projDim c = (lowerBoxDim (coord c '' S.attractor)).toReal := by
  rw [projDim, S.lowerBoxDim_coord_eq]

/-! ### The modified singular value function -/

/-- The base `b(𝐢)` of the rectangle `A_𝐢([0,1]²)`: the modulus of the non-zero entry of the
first row of `A_𝐢`. -/
noncomputable def wordBase (w : List ι) : ℝ := |S.gDeriv (S.codeWord 0 w)|

/-- The height `h(𝐢)` of the rectangle `A_𝐢([0,1]²)`: the modulus of the non-zero entry of the
second row of `A_𝐢`. -/
noncomputable def wordHeight (w : List ι) : ℝ := |S.gDeriv (S.codeWord 1 w)|

/-- The larger singular value `α_1(A_𝐢)`, the length of the longer side of `A_𝐢([0,1]²)`. -/
noncomputable def alpha₁ (w : List ι) : ℝ := max (S.wordBase w) (S.wordHeight w)

/-- The smaller singular value `α_2(A_𝐢)`, the length of the shorter side of `A_𝐢([0,1]²)`. -/
noncomputable def alpha₂ (w : List ι) : ℝ := min (S.wordBase w) (S.wordHeight w)

/-- Fraser's `s(𝐢) = \dim_B π_𝐢(X)`, §2.1. When `b(𝐢) ≥ h(𝐢)` the longer side of `A_𝐢([0,1]²)`
is horizontal and the projection of `φ_𝐢(X)` onto it is a similar copy of `proj_{o(𝐢)}(X)`;
when `b(𝐢) < h(𝐢)` the longer side is vertical and the projection of `φ_𝐢(X)` onto it is a
similar copy of `proj_{o(𝐢) + 1}(X)`. Here `o(𝐢) = 0` for a diagonal and `o(𝐢) = 1` for an
anti-diagonal `A_𝐢`. This is Fraser's table for `π_𝐢`; a square counts as `b(𝐢) ≥ h(𝐢)`. -/
noncomputable def wordDim (w : List ι) : ℝ :=
  if S.wordHeight w ≤ S.wordBase w then S.projDim (S.oWord w) else S.projDim (S.oWord w + 1)

/-- Fraser's modified singular value function
`ψ^s(𝐢) = α_1(𝐢)^{s(𝐢)} α_2(𝐢)^{s - s(𝐢)}`, equation (2.1) of his article. -/
noncomputable def modSvf (s : ℝ) (w : List ι) : ℝ :=
  S.alpha₁ w ^ S.wordDim w * S.alpha₂ w ^ (s - S.wordDim w)

/-- `b(𝐢) > 0`. -/
theorem wordBase_pos (w : List ι) : 0 < S.wordBase w := abs_pos.2 (S.gDeriv_ne_zero _)

/-- `h(𝐢) > 0`. -/
theorem wordHeight_pos (w : List ι) : 0 < S.wordHeight w := abs_pos.2 (S.gDeriv_ne_zero _)

/-- `α_2(𝐢) > 0`. -/
theorem alpha₂_pos (w : List ι) : 0 < S.alpha₂ w := lt_min (S.wordBase_pos w) (S.wordHeight_pos w)

/-- `α_2(𝐢) ≤ α_1(𝐢)`. -/
theorem alpha₂_le_alpha₁ (w : List ι) : S.alpha₂ w ≤ S.alpha₁ w := min_le_max

/-- `α_1(𝐢) > 0`. -/
theorem alpha₁_pos (w : List ι) : 0 < S.alpha₁ w := (S.alpha₂_pos w).trans_le (S.alpha₂_le_alpha₁ w)

/-- `α_1(𝐢) = ‖A_𝐢‖`. -/
theorem alpha₁_eq_norm (w : List ι) : S.alpha₁ w = ‖S.matWord w‖ := by
  rw [matWord_eq, norm_boxMat]
  rfl

/-- `α_1(𝐢) α_2(𝐢) = |det A_𝐢|`. -/
theorem alpha₁_mul_alpha₂ (w : List ι) : S.alpha₁ w * S.alpha₂ w = |(S.matWord w).det| := by
  rw [matWord_eq, abs_det_boxMat, abs_mul_abs_eq_max_mul_min]
  rfl

/-- `φ^s(A_𝐢) = α_1(𝐢)^{p(s)} α_2(𝐢)^{s - p(s)}` with `p(s) = svfExp s`. -/
theorem svf_matWord_eq (s : ℝ) (w : List ι) :
    svf s (S.matWord w) = S.alpha₁ w ^ svfExp s * S.alpha₂ w ^ (s - svfExp s) := by
  rw [matWord_eq, svf_boxMat_eq s _ _ (S.gDeriv_ne_zero _)]
  rfl

/-- The side of `A_𝐢([0,1]²)` along the axis `c` is at most `α_1(𝐢)`. -/
theorem abs_gDeriv_codeWord_le_alpha₁ (c : ZMod 2) (w : List ι) :
    |S.gDeriv (S.codeWord c w)| ≤ S.alpha₁ w := by
  rcases zmod_two_cases c with rfl | rfl
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- `s(𝐢)` is one of `s_1`, `s_2`, so a common upper bound of these bounds `s(𝐢)`. -/
theorem wordDim_le {D : ℝ} (h : ∀ c, S.projDim c ≤ D) (w : List ι) : S.wordDim w ≤ D := by
  unfold wordDim
  split_ifs <;> exact h _

/-- A common lower bound of `s_1`, `s_2` is a lower bound of `s(𝐢)`. -/
theorem le_wordDim {D : ℝ} (h : ∀ c, D ≤ S.projDim c) (w : List ι) : D ≤ S.wordDim w := by
  unfold wordDim
  split_ifs <;> exact h _

/-- `s(𝐢) ≥ 0`. -/
theorem wordDim_nonneg (w : List ι) : 0 ≤ S.wordDim w := S.le_wordDim S.projDim_nonneg w

/-- If `s_1 = s_2 = t`, then `s(𝐢) = t` for every word. -/
theorem wordDim_eq {t : ℝ} (h : ∀ c, S.projDim c = t) (w : List ι) : S.wordDim w = t :=
  le_antisymm (S.wordDim_le (fun c => (h c).le) w) (S.le_wordDim (fun c => (h c).ge) w)

/-- `ψ^s(𝐢) > 0`. -/
theorem modSvf_pos (s : ℝ) (w : List ι) : 0 < S.modSvf s w :=
  mul_pos (Real.rpow_pos_of_pos (S.alpha₁_pos w) _) (Real.rpow_pos_of_pos (S.alpha₂_pos w) _)

/-- `ψ^{s+δ}(𝐢) = α_2(𝐢)^δ ψ^s(𝐢)`: the exponent `s` enters `ψ^s` only through the smaller
singular value. -/
theorem modSvf_add (s δ : ℝ) (w : List ι) :
    S.modSvf (s + δ) w = S.alpha₂ w ^ δ * S.modSvf s w := by
  unfold modSvf
  rw [show s + δ - S.wordDim w = δ + (s - S.wordDim w) by ring, Real.rpow_add (S.alpha₂_pos w)]
  ring

/-- For a square, `b(𝐢) = h(𝐢)`, the modified singular value function is `ψ^s(𝐢) = α_1(𝐢)^s`,
whichever projection `s(𝐢)` refers to. -/
theorem modSvf_of_wordBase_eq (s : ℝ) {w : List ι} (h : S.wordBase w = S.wordHeight w) :
    S.modSvf s w = S.alpha₁ w ^ s := by
  have h' : S.alpha₂ w = S.alpha₁ w := by simp [alpha₁, alpha₂, h]
  rw [modSvf, h', ← Real.rpow_add (S.alpha₁_pos w)]
  congr 1
  ring

/-- `ψ^s(𝐢) ≤ φ^s(A_𝐢)` when `s(𝐢) ≤ p(s)`, the exponent of `α_1` in `φ^s`. For `s ≤ 2` the
condition reads `s(𝐢) ≤ min{1, s}`, and it holds for all `s > 2`. -/
theorem modSvf_le_svf {s : ℝ} {w : List ι} (h : S.wordDim w ≤ svfExp s) :
    S.modSvf s w ≤ svf s (S.matWord w) := by
  rw [svf_matWord_eq]
  exact rpow_mul_rpow_sub_mono (S.alpha₂_pos w) (S.alpha₂_le_alpha₁ w) s h

/-- `φ^s(A_𝐢) ≤ ψ^s(𝐢)` when `p(s) ≤ s(𝐢)`; for `s ≤ 1` the condition reads `s ≤ s(𝐢)`. -/
theorem svf_le_modSvf {s : ℝ} {w : List ι} (h : svfExp s ≤ S.wordDim w) :
    svf s (S.matWord w) ≤ S.modSvf s w := by
  rw [svf_matWord_eq]
  exact rpow_mul_rpow_sub_mono (S.alpha₂_pos w) (S.alpha₂_le_alpha₁ w) s h

/-- `ψ^0(𝐢) = (α_1(𝐢)/α_2(𝐢))^{s(𝐢)} ≥ 1`. -/
theorem one_le_modSvf_zero (w : List ι) : 1 ≤ S.modSvf 0 w := by
  have h := rpow_mul_rpow_sub_mono (S.alpha₂_pos w) (S.alpha₂_le_alpha₁ w) 0 (S.wordDim_nonneg w)
  rw [Real.rpow_zero, sub_zero, Real.rpow_zero, one_mul] at h
  exact h

variable {S} {r M δ₀ : ℝ}

/-- `α_1(𝐢) ≤ r^{|𝐢|}` when every `|a_i|` and `|b_i|` is at most `r`. -/
theorem Bounds.alpha₁_le (hS : S.Bounds r M) (w : List ι) : S.alpha₁ w ≤ r ^ w.length := by
  refine max_le ?_ ?_
  · simpa [wordBase] using hS.abs_gDeriv_le (S.codeWord 0 w)
  · simpa [wordHeight] using hS.abs_gDeriv_le (S.codeWord 1 w)

/-- `α_2(𝐢) ≥ δ₀^{|𝐢|}` when every `|a_i|` and `|b_i|` is at least `δ₀`. -/
theorem RatioLowerBound.le_alpha₂ (hδ₀ : S.RatioLowerBound δ₀) (w : List ι) :
    δ₀ ^ w.length ≤ S.alpha₂ w := by
  refine le_min ?_ ?_
  · simpa [wordBase] using hδ₀.le_abs_gDeriv (S.codeWord 0 w)
  · simpa [wordHeight] using hδ₀.le_abs_gDeriv (S.codeWord 1 w)

/-- `ψ^{s+δ}(𝐢) ≤ r^{δ|𝐢|} ψ^s(𝐢)`. -/
theorem Bounds.modSvf_add_le (hS : S.Bounds r M) (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (w : List ι) :
    S.modSvf (s + δ) w ≤ (r ^ w.length) ^ δ * S.modSvf s w := by
  rw [modSvf_add]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (S.alpha₂_pos w).le
    ((S.alpha₂_le_alpha₁ w).trans (hS.alpha₁_le w)) hδ) (S.modSvf_pos s w).le

/-- `δ₀^{δ|𝐢|} ψ^s(𝐢) ≤ ψ^{s+δ}(𝐢)`. -/
theorem RatioLowerBound.le_modSvf_add (hδ₀ : S.RatioLowerBound δ₀) (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (w : List ι) : (δ₀ ^ w.length) ^ δ * S.modSvf s w ≤ S.modSvf (s + δ) w := by
  rw [modSvf_add]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (pow_nonneg hδ₀.1.le _)
    (hδ₀.le_alpha₂ w) hδ) (S.modSvf_pos s w).le

/-- `ψ^0(𝐢) ≤ δ₀^{-|𝐢|}`, since `α_1(𝐢) ≤ 1`, `α_2(𝐢) ≥ δ₀^{|𝐢|}` and `0 ≤ s(𝐢) ≤ 1`. -/
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

/-! ### Fraser's Lemma 2.1: sub- and super-multiplicativity -/

/-- For `0 < y ≤ x` and `s ≤ p + q`: `y^q x^{s-q} ≤ x^p y^{s-p}`. -/
theorem _root_.BoxLike.rpow_swap_le {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) {s p q : ℝ}
    (h : s ≤ p + q) : y ^ q * x ^ (s - q) ≤ x ^ p * y ^ (s - p) := by
  have h' := rpow_mul_rpow_sub_mono hy hyx s (show s - q ≤ p by linarith)
  rwa [sub_sub_cancel, mul_comm] at h'

/-- For `0 < y ≤ x` and `p + q ≤ s`: `x^p y^{s-p} ≤ y^q x^{s-q}`. -/
theorem _root_.BoxLike.le_rpow_swap {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) {s p q : ℝ}
    (h : p + q ≤ s) : x ^ p * y ^ (s - p) ≤ y ^ q * x ^ (s - q) := by
  have h' := rpow_mul_rpow_sub_mono hy hyx s (show p ≤ s - q by linarith)
  rwa [sub_sub_cancel, mul_comm (x ^ (s - q))] at h'

variable (S)

/-- The side of the rectangle `A_𝐢([0,1]²)` along the axis `c`: `side 0 = b(𝐢)` and
`side 1 = h(𝐢)`. -/
noncomputable def side (c : ZMod 2) (w : List ι) : ℝ := |S.gDeriv (S.codeWord c w)|

/-- The value `ψ^s(𝐢)` would take if the side along the axis `c` were the longer one. By
`modSvf_eq_sideSvf` the function `ψ^s` is one of `sideSvf s 0` and `sideSvf s 1`, the larger
for `s ≤ s_1 + s_2` and the smaller for `s ≥ s_1 + s_2`. -/
noncomputable def sideSvf (s : ℝ) (c : ZMod 2) (w : List ι) : ℝ :=
  S.side c w ^ S.projDim (c + S.oWord w) * S.side (c + 1) w ^ (s - S.projDim (c + S.oWord w))

/-- The sides are positive. -/
theorem side_pos (c : ZMod 2) (w : List ι) : 0 < S.side c w := abs_pos.2 (S.gDeriv_ne_zero _)

/-- The sides of `A_{𝐢𝐣}([0,1]²)`: the side along `c` is the product of the side of `A_𝐢`
along `c` and the side of `A_𝐣` along `c + o(𝐢)`. -/
theorem side_append (c : ZMod 2) (w w' : List ι) :
    S.side c (w ++ w') = S.side c w * S.side (c + S.oWord w) w' := by
  rw [side, codeWord_append, gDeriv_append, abs_mul]
  rfl

/-- In a system without anti-diagonal generators every product `A_𝐢` is diagonal. -/
theorem oWord_eq_zero (h : ∀ i, S.o i = 0) (w : List ι) : S.oWord w = 0 := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [oWord_cons, h, ih, add_zero]

/-- Either `s_1 = s_2`, or every generator is diagonal: Fraser's non-separated and separated
types. -/
theorem projDim_eq_or_diagonal [Finite ι] :
    (∀ c c', S.projDim c = S.projDim c') ∨ ∀ i, S.o i = 0 := by
  by_cases h : ∃ i, S.o i = 1
  · exact Or.inl (S.projDim_eq h)
  · refine Or.inr fun i => (zmod_two_cases (S.o i)).resolve_right fun hi => h ⟨i, hi⟩

/-- `s_{1 + o} + s_{2 + o} = s_1 + s_2`. -/
theorem projDim_add_projDim (c : ZMod 2) :
    S.projDim c + S.projDim (c + 1) = S.projDim 0 + S.projDim 1 := by
  rcases zmod_two_cases c with rfl | rfl
  · rw [zero_add]
  · rw [show (1 : ZMod 2) + 1 = 0 from by decide, add_comm]

/-- The description of tex lines 2077 to 2077: `s(𝐢)` is the Minkowski dimension of the
projection of `X` onto the coordinate axis parallel to the longer side of `A_𝐢([0,1]²)`. It
agrees with Fraser's definition `wordDim`, which uses the other axis when `A_𝐢` is
anti-diagonal, because `s_1 = s_2` as soon as an anti-diagonal generator exists. -/
theorem wordDim_eq_axis [Finite ι] (w : List ι) :
    S.wordDim w = if S.wordHeight w ≤ S.wordBase w then S.projDim 0 else S.projDim 1 := by
  unfold wordDim
  rcases S.projDim_eq_or_diagonal with h | h
  · split_ifs <;> exact h _ _
  · rw [S.oWord_eq_zero h, zero_add]

/-- `ψ^s(𝐢)` is `sideSvf s 0 𝐢` when `b(𝐢) ≥ h(𝐢)` and `sideSvf s 1 𝐢` otherwise. -/
theorem modSvf_eq_ite (s : ℝ) (w : List ι) :
    S.modSvf s w = if S.wordHeight w ≤ S.wordBase w then S.sideSvf s 0 w else S.sideSvf s 1 w := by
  unfold modSvf wordDim alpha₁ alpha₂ sideSvf
  split_ifs with h
  · rw [max_eq_left h, min_eq_right h, zero_add, zero_add]
    rfl
  · rw [max_eq_right (not_le.1 h).le, min_eq_left (not_le.1 h).le,
      show (1 : ZMod 2) + 1 = 0 from by decide, add_comm 1 (S.oWord w)]
    rfl

/-- `ψ^s(𝐢)` is one of the two values `sideSvf s c 𝐢`. -/
theorem modSvf_eq_sideSvf (s : ℝ) (w : List ι) : ∃ c, S.modSvf s w = S.sideSvf s c w := by
  rw [modSvf_eq_ite]
  split_ifs
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩]

/-- For `s ≤ s_1 + s_2` the function `ψ^s` is the larger of the two values `sideSvf s c`. -/
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

/-- For `s ≥ s_1 + s_2` the function `ψ^s` is the smaller of the two values `sideSvf s c`. -/
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

/-- The values `sideSvf s c` are multiplicative along the path of `Σ_Z`:
`sideSvf s c (𝐢𝐣) = sideSvf s c 𝐢 · sideSvf s (c + o(𝐢)) 𝐣`. This uses that `s_1 = s_2` or
every generator is diagonal. -/
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

/-- Fraser's Lemma 2.1 (a1) and (a2): `ψ^s(𝐢𝐣) ≤ ψ^s(𝐢) ψ^s(𝐣)` for `s ≤ s_1 + s_2`. -/
theorem modSvf_append_le [Finite ι] {s : ℝ} (hs : s ≤ S.projDim 0 + S.projDim 1)
    (w w' : List ι) : S.modSvf s (w ++ w') ≤ S.modSvf s w * S.modSvf s w' := by
  obtain ⟨c, hc⟩ := S.modSvf_eq_sideSvf s (w ++ w')
  rw [hc, sideSvf_append]
  exact mul_le_mul (S.sideSvf_le_modSvf hs _ _) (S.sideSvf_le_modSvf hs _ _)
    (mul_pos (Real.rpow_pos_of_pos (S.side_pos _ _) _)
      (Real.rpow_pos_of_pos (S.side_pos _ _) _)).le (S.modSvf_pos s w).le

/-- Fraser's Lemma 2.1 (a2) and (a3): `ψ^s(𝐢) ψ^s(𝐣) ≤ ψ^s(𝐢𝐣)` for `s ≥ s_1 + s_2`. -/
theorem le_modSvf_append [Finite ι] {s : ℝ} (hs : S.projDim 0 + S.projDim 1 ≤ s)
    (w w' : List ι) : S.modSvf s w * S.modSvf s w' ≤ S.modSvf s (w ++ w') := by
  obtain ⟨c, hc⟩ := S.modSvf_eq_sideSvf s (w ++ w')
  rw [hc, sideSvf_append]
  exact mul_le_mul (S.modSvf_le_sideSvf hs _ _) (S.modSvf_le_sideSvf hs _ _)
    (S.modSvf_pos s w').le (mul_pos (Real.rpow_pos_of_pos (S.side_pos _ _) _)
      (Real.rpow_pos_of_pos (S.side_pos _ _) _)).le

variable {S}

/-! ### The sums over words and the modified pressure -/

/-- From `A ≤ (ρ^n)^δ B` to `n⁻¹ log A ≤ δ log ρ + n⁻¹ log B`. -/
theorem _root_.BoxLike.log_div_le_of_le_rpow_mul {A B ρ δ : ℝ} {n : ℕ} (hn : 0 < n) (hA : 0 < A)
    (hB : 0 < B) (hρ : 0 < ρ) (h : A ≤ (ρ ^ n) ^ δ * B) :
    Real.log A / n ≤ δ * Real.log ρ + Real.log B / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < (ρ ^ n) ^ δ := Real.rpow_pos_of_pos (pow_pos hρ _) _
  have hlog := Real.log_le_log hA h
  rw [Real.log_mul hp.ne' hB.ne', Real.log_rpow (pow_pos hρ _), Real.log_pow] at hlog
  rw [div_le_iff₀ hn', add_mul, div_mul_cancel₀ _ hn'.ne']
  linarith [mul_assoc δ (n : ℝ) (Real.log ρ), mul_right_comm δ (n : ℝ) (Real.log ρ)]

/-- From `(ρ^n)^δ B ≤ A` to `δ log ρ + n⁻¹ log B ≤ n⁻¹ log A`. -/
theorem _root_.BoxLike.le_log_div_of_rpow_mul_le {A B ρ δ : ℝ} {n : ℕ} (hn : 0 < n)
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

/-- The sum `Ψ_n^s = ∑_{|𝐢| = n} ψ^s(𝐢)` of Fraser, §2.1. -/
noncomputable def modSvfSum (s : ℝ) (n : ℕ) : ℝ :=
  ∑ w : Fin n → ι, S.modSvf s (List.ofFn w)

/-- The modified pressure `lim_n n⁻¹ log Ψ_n^s`, the logarithm of Fraser's `P(s)`, §2.1. It is
defined as the `lim sup`; `tendsto_modPressure` shows that the limit exists. -/
noncomputable def modPressure (s : ℝ) : ℝ :=
  limsup (fun n : ℕ => Real.log (S.modSvfSum s n) / n) atTop

/-- `Ψ_n^s > 0`. -/
theorem modSvfSum_pos [Nonempty ι] (s : ℝ) (n : ℕ) : 0 < S.modSvfSum s n :=
  Finset.sum_pos (fun _ _ => S.modSvf_pos s _) Finset.univ_nonempty

/-- `Ψ_n^0 ≥ N^n`, since `ψ^0 ≥ 1`. -/
theorem card_pow_le_modSvfSum_zero (n : ℕ) : (Fintype.card ι : ℝ) ^ n ≤ S.modSvfSum 0 n := by
  calc (Fintype.card ι : ℝ) ^ n = ∑ _w : Fin n → ι, (1 : ℝ) := by simp
    _ ≤ S.modSvfSum 0 n := Finset.sum_le_sum fun w _ => S.one_le_modSvf_zero _

variable {S}

/-- `Ψ_n^{s+δ} ≤ r^{nδ} Ψ_n^s`. -/
theorem Bounds.modSvfSum_exponent_add_le (hS : S.Bounds r M) (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (n : ℕ) : S.modSvfSum (s + δ) n ≤ (r ^ n) ^ δ * S.modSvfSum s n := by
  rw [modSvfSum, modSvfSum, Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  have h := hS.modSvf_add_le s hδ (List.ofFn w)
  rwa [List.length_ofFn] at h

/-- `δ₀^{nδ} Ψ_n^s ≤ Ψ_n^{s+δ}`. -/
theorem RatioLowerBound.le_modSvfSum_exponent_add (hδ₀ : S.RatioLowerBound δ₀) (s : ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (n : ℕ) : (δ₀ ^ n) ^ δ * S.modSvfSum s n ≤ S.modSvfSum (s + δ) n := by
  rw [modSvfSum, modSvfSum, Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  have h := hδ₀.le_modSvf_add s hδ (List.ofFn w)
  rwa [List.length_ofFn] at h

/-- `Ψ_n^0 ≤ δ₀^{-n} N^n`. -/
theorem RatioLowerBound.modSvfSum_zero_le (hδ₀ : S.RatioLowerBound δ₀) (hS : S.Bounds r M)
    (n : ℕ) : S.modSvfSum 0 n ≤ (δ₀ ^ n) ^ (-1 : ℝ) * (Fintype.card ι : ℝ) ^ n := by
  calc S.modSvfSum 0 n ≤ ∑ _w : Fin n → ι, (δ₀ ^ n) ^ (-1 : ℝ) :=
        Finset.sum_le_sum fun w _ => by
          have h := hδ₀.modSvf_zero_le hS (List.ofFn w)
          rwa [List.length_ofFn] at h
    _ = (δ₀ ^ n) ^ (-1 : ℝ) * (Fintype.card ι : ℝ) ^ n := by
        simp [mul_comm]

/-- The slope of `n⁻¹ log Ψ_n^s` in `s`, and the bounds
`s log δ₀ ≤ n⁻¹ log Ψ_n^s ≤ log N - log δ₀`, for `n ≥ 1`. -/
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

/-- The sequence `n⁻¹ log Ψ_n^s` is bounded above. -/
theorem isBoundedUnder_le_modLog [Nonempty ι] {s : ℝ} (hs : 0 ≤ s) :
    IsBoundedUnder (· ≤ ·) atTop fun n : ℕ => Real.log (S.modSvfSum s n) / n := by
  obtain ⟨δ₀, hδ₀⟩ := S.exists_ratioLowerBound
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  obtain ⟨i⟩ : Nonempty ι := inferInstance
  have hr : 0 < r := hδ₀.1.trans_le ((hδ₀.2 (i, 0)).trans (hS.abs_ratio_le (i, 0)))
  exact isBoundedUnder_of_eventually_le ((eventually_gt_atTop 0).mono fun n hn =>
    (hδ₀.modLog_bounds hS hr hs le_rfl hn).2.2)

/-- The sequence `n⁻¹ log Ψ_n^s` is bounded below. -/
theorem isBoundedUnder_ge_modLog [Nonempty ι] {s : ℝ} (hs : 0 ≤ s) :
    IsBoundedUnder (· ≥ ·) atTop fun n : ℕ => Real.log (S.modSvfSum s n) / n := by
  obtain ⟨δ₀, hδ₀⟩ := S.exists_ratioLowerBound
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  obtain ⟨i⟩ : Nonempty ι := inferInstance
  have hr : 0 < r := hδ₀.1.trans_le ((hδ₀.2 (i, 0)).trans (hS.abs_ratio_le (i, 0)))
  exact isBoundedUnder_of_eventually_ge ((eventually_gt_atTop 0).mono fun n hn =>
    (hδ₀.modLog_bounds hS hr hs le_rfl hn).2.1)

/-- The modified pressure at `0` is non-negative, since `Ψ_n^0 ≥ N^n`. -/
theorem modPressure_zero_nonneg [Nonempty ι] : 0 ≤ S.modPressure 0 := by
  refine le_limsup_of_frequently_le (Eventually.frequently (Eventually.of_forall fun n => ?_))
    (S.isBoundedUnder_le_modLog le_rfl)
  exact div_nonneg (Real.log_nonneg ((one_le_pow₀ (by exact_mod_cast Fintype.card_pos)).trans
    (S.card_pow_le_modSvfSum_zero n))) (Nat.cast_nonneg n)

/-- The slope of the modified pressure lies between `log δ₀` and `log r < 0`, where
`0 < δ₀ ≤ |a_i|, |b_i| ≤ r < 1` for all `i`. This is Fraser's Lemma 2.2 (1) in logarithmic
form. -/
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

/-- The increment bound of `exists_modPressure_slope`, read for a pair of exponents
`0 ≤ s ≤ t`. -/
theorem exists_modPressure_increment [Nonempty ι] : ∃ c₁ c₂ : ℝ, c₂ < 0 ∧
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → (t - s) * c₁ ≤ S.modPressure t - S.modPressure s ∧
      S.modPressure t - S.modPressure s ≤ (t - s) * c₂ := by
  obtain ⟨c₁, c₂, hc₂, h⟩ := S.exists_modPressure_slope
  refine ⟨c₁, c₂, hc₂, fun s t hs hst => ?_⟩
  have h' := h s (t - s) hs (sub_nonneg.2 hst)
  rwa [add_sub_cancel] at h'

/-- The modified pressure is strictly decreasing on `[0, ∞)`, Fraser's Lemma 2.2 (3). -/
theorem strictAntiOn_modPressure [Nonempty ι] : StrictAntiOn S.modPressure (Set.Ici 0) := by
  obtain ⟨c₁, c₂, hc₂, h⟩ := S.exists_modPressure_increment
  intro s hs t _ hst
  have h' := (h s t hs hst.le).2
  have hneg : (t - s) * c₂ < 0 := mul_neg_of_pos_of_neg (sub_pos.2 hst) hc₂
  linarith

/-- The modified pressure has a unique zero on `[0, ∞)`, Fraser's Lemma 2.2 (4). -/
theorem existsUnique_modPressure_eq_zero [Nonempty ι] :
    ∃! s : ℝ, 0 ≤ s ∧ S.modPressure s = 0 := by
  obtain ⟨c₁, c₂, hc₂, h⟩ := S.exists_modPressure_increment
  exact existsUnique_zero_of_increment hc₂ S.modPressure_zero_nonneg h

/-! ### The modified affinity dimension -/

/-- Fraser's modified affinity dimension `dimmaff(X)` of tex lines 2077 to 2077: the unique
`s ≥ 0` at which the modified pressure vanishes, that is, the unique solution of `P(s) = 1` in
Fraser's Theorem 2.3. It depends on the set `X` through `s_1` and `s_2`, not on the matrices
alone. -/
noncomputable def dimmaff [Nonempty ι] : ℝ := (S.existsUnique_modPressure_eq_zero).exists.choose

/-- `dimmaff(X) ≥ 0`. -/
theorem dimmaff_nonneg [Nonempty ι] : 0 ≤ S.dimmaff :=
  (S.existsUnique_modPressure_eq_zero).exists.choose_spec.1

/-- The modified pressure vanishes at `dimmaff(X)`. -/
theorem modPressure_dimmaff [Nonempty ι] : S.modPressure S.dimmaff = 0 :=
  (S.existsUnique_modPressure_eq_zero).exists.choose_spec.2

/-- The modified affinity dimension is the only zero of the modified pressure on `[0, ∞)`. -/
theorem dimmaff_eq [Nonempty ι] {s : ℝ} (hs : 0 ≤ s) (h : S.modPressure s = 0) : S.dimmaff = s :=
  (S.existsUnique_modPressure_eq_zero).unique ⟨S.dimmaff_nonneg, S.modPressure_dimmaff⟩ ⟨hs, h⟩

/-- An exponent `s ≥ 0` with non-positive modified pressure is at least `dimmaff(X)`. -/
theorem dimmaff_le_of_modPressure_nonpos [Nonempty ι] {s : ℝ} (hs : 0 ≤ s)
    (h : S.modPressure s ≤ 0) : S.dimmaff ≤ s := by
  by_contra hlt
  have hlt' := S.strictAntiOn_modPressure hs S.dimmaff_nonneg (not_le.1 hlt)
  rw [S.modPressure_dimmaff] at hlt'
  linarith

/-- An exponent `s ≥ 0` with non-negative modified pressure is at most `dimmaff(X)`. -/
theorem le_dimmaff_of_modPressure_nonneg [Nonempty ι] {s : ℝ} (hs : 0 ≤ s)
    (h : 0 ≤ S.modPressure s) : s ≤ S.dimmaff := by
  by_contra hlt
  have hlt' := S.strictAntiOn_modPressure S.dimmaff_nonneg hs (not_le.1 hlt)
  rw [S.modPressure_dimmaff] at hlt'
  linarith

/-! ### Comparison with the singular value pressure -/

/-- `p(s) = 1` for `1 ≤ s ≤ 2`. -/
theorem _root_.BoxLike.svfExp_eq_one {s : ℝ} (h1 : 1 ≤ s) (h2 : s ≤ 2) : svfExp s = 1 := by
  unfold svfExp
  split_ifs with h
  · exact le_antisymm h h1
  · rfl

/-- `Ψ_n^s ≤ ∑_{|𝐢| = n} φ^s(A_𝐢)` when `s_1, s_2 ≤ p(s)`. -/
theorem modSvfSum_le_svfSum {s : ℝ} (h : ∀ c, S.projDim c ≤ svfExp s) (n : ℕ) :
    S.modSvfSum s n ≤ S.svfSum s n :=
  Finset.sum_le_sum fun _ _ => S.modSvf_le_svf (S.wordDim_le h _)

/-- `∑_{|𝐢| = n} φ^s(A_𝐢) ≤ Ψ_n^s` when `p(s) ≤ s_1, s_2`. -/
theorem svfSum_le_modSvfSum {s : ℝ} (h : ∀ c, svfExp s ≤ S.projDim c) (n : ℕ) :
    S.svfSum s n ≤ S.modSvfSum s n :=
  Finset.sum_le_sum fun _ _ => S.svf_le_modSvf (S.le_wordDim h _)

/-- The modified pressure is at most the singular value pressure at every `s ≥ 0` with
`s_1, s_2 ≤ p(s)`: for `s ≤ 2` the condition reads `s_1, s_2 ≤ min{1, s}`, and it holds for all
`s > 2`. For `s < max{s_1, s_2}` the inequality between `ψ^s` and `φ^s` is reversed on some
words. -/
theorem modPressure_le_pressure [Nonempty ι] {s : ℝ} (hs : 0 ≤ s)
    (h : ∀ c, S.projDim c ≤ svfExp s) : S.modPressure s ≤ S.pressure s := by
  obtain ⟨δ₀, hδ₀⟩ := S.exists_ratioLowerBound
  have ht := hδ₀.tendsto_pressure hs
  rw [← ht.limsup_eq]
  refine limsup_le_limsup (Eventually.of_forall fun n => ?_)
    (S.isBoundedUnder_ge_modLog hs).isCoboundedUnder_le ht.isBoundedUnder_le
  exact div_le_div_of_nonneg_right (Real.log_le_log (S.modSvfSum_pos s n)
    (S.modSvfSum_le_svfSum h n)) (Nat.cast_nonneg n)

/-- The singular value pressure is at most the modified pressure at every `s ≥ 0` with
`p(s) ≤ s_1, s_2`. -/
theorem pressure_le_modPressure [Nonempty ι] {s : ℝ} (hs : 0 ≤ s)
    (h : ∀ c, svfExp s ≤ S.projDim c) : S.pressure s ≤ S.modPressure s := by
  obtain ⟨δ₀, hδ₀⟩ := S.exists_ratioLowerBound
  have ht := hδ₀.tendsto_pressure hs
  rw [← ht.limsup_eq]
  refine limsup_le_limsup (Eventually.of_forall fun n => ?_)
    ht.isBoundedUnder_ge.isCoboundedUnder_le (S.isBoundedUnder_le_modLog hs)
  exact div_le_div_of_nonneg_right (Real.log_le_log (hδ₀.svfSum_pos hs n)
    (S.svfSum_le_modSvfSum h n)) (Nat.cast_nonneg n)

/-- The two pressures agree at every `s ≥ 0` with `s_1 = s_2 = p(s)`. For `s_1 = s_2 = 1` this
is the range `1 ≤ s ≤ 2`, the observation behind Fraser's Corollary 2.5. -/
theorem modPressure_eq_pressure [Nonempty ι] {s : ℝ} (hs : 0 ≤ s)
    (h : ∀ c, S.projDim c = svfExp s) : S.modPressure s = S.pressure s :=
  le_antisymm (S.modPressure_le_pressure hs fun c => (h c).le)
    (S.pressure_le_modPressure hs fun c => (h c).ge)

/-! ### Falconer's bound for the coordinate projections and `dimmaff(X) ≤ dimaff(X)` -/

/-- For `s ≥ 0` with `P(𝖠, s) < 0` the partial sums of `∑_n ∑_{|𝐢| = n} φ^s(A_𝐢)` are bounded,
since `∑_{|𝐢| = n} φ^s(A_𝐢) ≤ e^{nP(𝖠, s)/2}` for large `n`. -/
theorem exists_sum_svfSum_le [Nonempty ι] {s : ℝ} (hs : 0 ≤ s) (hP : S.pressure s < 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℕ, ∑ n ∈ Finset.range L, S.svfSum s n ≤ K := by
  obtain ⟨δ₀, hδ₀⟩ := S.exists_ratioLowerBound
  have ht := hδ₀.tendsto_pressure hs
  have hq0 : 0 < Real.exp (S.pressure s / 2) := Real.exp_pos _
  have hq1 : Real.exp (S.pressure s / 2) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hev : ∀ᶠ n : ℕ in atTop, ‖S.svfSum s n‖ ≤ Real.exp (S.pressure s / 2) ^ n := by
    filter_upwards [ht.eventually (gt_mem_nhds (show S.pressure s < S.pressure s / 2 by linarith)),
      eventually_gt_atTop 0] with n hn hn0
    have hpos := hδ₀.svfSum_pos hs n
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [div_lt_iff₀ hn'] at hn
    rw [Real.norm_of_nonneg hpos.le, ← Real.exp_nat_mul]
    calc S.svfSum s n = Real.exp (Real.log (S.svfSum s n)) := (Real.exp_log hpos).symm
      _ ≤ Real.exp (n * (S.pressure s / 2)) := Real.exp_le_exp.2 (by linarith)
  have hsum : Summable fun n => S.svfSum s n :=
    Summable.of_norm_bounded_eventually_nat (summable_geometric_of_lt_one hq0.le hq1) hev
  have hle : ∀ L : ℕ, ∑ n ∈ Finset.range L, S.svfSum s n ≤ ∑' n, S.svfSum s n :=
    fun L => hsum.sum_le_tsum (Finset.range L) fun n _ => (hδ₀.svfSum_pos hs n).le
  refine ⟨∑' n, S.svfSum s n + 1, ?_, fun L => (hle L).trans (le_add_of_nonneg_right zero_le_one)⟩
  have h0 := hle 0
  rw [Finset.range_zero, Finset.sum_empty] at h0
  linarith

/-- Falconer's covering argument for a coordinate projection: `\overline{\dim}_M proj_c(X) ≤ s`
for `0 ≤ s ≤ 1` with `P(𝖠, s) < 0`. The intervals `proj_c(φ_𝐢(X))` of the words whose side
along the axis `c` lies between `δ₀ρ/D` and `ρ/D` cover `proj_c(X)` at scale `ρ`, and there are at
most `K (δ₀ρ/D)^{-s}` of them, since `φ^s(A_𝐢) = α_1(𝐢)^s` for `s ≤ 1`. -/
theorem upperBoxDim_coord_le_of_pressure_neg [Nonempty ι] (c : ZMod 2) {s : ℝ≥0} (hs1 : (s : ℝ) ≤ 1)
    (hP : S.pressure s < 0) : upperBoxDim (coord c '' S.attractor) ≤ s := by
  classical
  obtain ⟨K, hK0, hK⟩ := S.exists_sum_svfSum_le s.coe_nonneg hP
  obtain ⟨δ₀, hδ₀⟩ := S.exists_ratioLowerBound
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  obtain ⟨i⟩ : Nonempty ι := inferInstance
  have hδ₀1 : δ₀ ≤ 1 := (hδ₀.2 (i, 0)).trans (S.abs_ratio_lt_one _).le
  have hδ₀0 := hδ₀.1
  have hr : 0 < r := hδ₀.1.trans_le ((hδ₀.2 (i, 0)).trans (hS.abs_ratio_le (i, 0)))
  obtain ⟨D₀, hD₀⟩ := Metric.isBounded_iff.1 S.isCompact_attractor.isBounded
  have hD1 : 1 ≤ max D₀ 1 := le_max_right _ _
  have hD0 : 0 < max D₀ 1 := one_pos.trans_le hD1
  have hdist : ∀ x ∈ S.attractor, ∀ x' ∈ S.attractor, dist x x' ≤ max D₀ 1 :=
    fun x hx x' hx' => (hD₀ hx hx').trans (le_max_left _ _)
  obtain ⟨x₀, hx₀⟩ := S.attractor_nonempty
  have hexp : svfExp (s : ℝ) = s := ite_eq_left hs1
  refine upperBoxDim_le_of_forall
    (C := (K * (δ₀ / max D₀ 1) ^ (-(s : ℝ))).toNNReal) (Real.toNNReal_pos.2 (by positivity)) ?_
  filter_upwards [eventually_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one' ℝ))] with ρ hρ0 hρ1
  have hρ : (0 : ℝ) < ρ := hρ0
  have hρ₁ : 0 < ρ / max D₀ 1 := div_pos hρ hD0
  have hρ₁1 : ρ / max D₀ 1 ≤ 1 := (div_le_one hD0).2 ((le_of_lt hρ1).trans hD1)
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one (mul_pos hδ₀.1 hρ₁) hS.r_lt_one
  set W : (n : ℕ) → Finset (Fin n → ι) := fun n => Finset.univ.filter fun w =>
    δ₀ * (ρ / max D₀ 1) ≤ |S.gDeriv (S.codeWord c (List.ofFn w))| with hW
  set C : Finset ℝ := (Finset.range L).biUnion fun n =>
    (W n).image fun w => coord c (S.phiWord (List.ofFn w) x₀) with hC
  have hcov : Metric.IsCover ρ.toNNReal (coord c '' S.attractor) (C : Set ℝ) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hρ₁ hS.r_lt_one
    obtain ⟨w, ⟨x, hx, rfl⟩, hw1, hw2⟩ :=
      S.exists_word_mem_side hδ₀ hδ₀1 hr hS.abs_ratio_le k c z hz _ hρ₁ hρ₁1 hk.le
    have hlen : w.length < L := by
      by_contra h
      rw [not_lt] at h
      have h1 := hS.abs_gDeriv_le (S.codeWord c w)
      rw [length_codeWord] at h1
      have h2 : r ^ w.length ≤ r ^ L := pow_le_pow_of_le_one hS.r_nonneg hS.r_lt_one.le h
      linarith
    refine ⟨coord c (S.phiWord w x₀), ?_, ?_⟩
    · rw [Finset.mem_coe, hC, Finset.mem_biUnion]
      refine ⟨w.length, Finset.mem_range.2 hlen, Finset.mem_image.2 ⟨w.get, ?_, ?_⟩⟩
      · rw [hW, Finset.mem_filter, List.ofFn_get]
        exact ⟨Finset.mem_univ _, hw2⟩
      · rw [List.ofFn_get]
    · show edist _ _ ≤ ((ρ.toNNReal : ℝ≥0) : ℝ≥0∞)
      rw [edist_dist, Real.dist_eq, coord_phiWord, coord_phiWord,
        S.gWord_apply (S.codeWord c w) (coord (c + S.oWord w) x),
        S.gWord_apply (S.codeWord c w) (coord (c + S.oWord w) x₀)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc |S.gDeriv (S.codeWord c w) * coord (c + S.oWord w) x + S.gWord (S.codeWord c w) 0 -
            (S.gDeriv (S.codeWord c w) * coord (c + S.oWord w) x₀ +
              S.gWord (S.codeWord c w) 0)|
          = |S.gDeriv (S.codeWord c w)| *
              |coord (c + S.oWord w) x - coord (c + S.oWord w) x₀| := by
            rw [← abs_mul]; ring_nf
        _ ≤ ρ / max D₀ 1 * max D₀ 1 :=
            mul_le_mul hw1 ((abs_coord_sub_le _ x x₀).trans (hdist x hx x₀ hx₀))
              (abs_nonneg _) hρ₁.le
        _ = ρ := div_mul_cancel₀ _ hD0.ne'
  have hword : ∀ n, ((W n).card : ℝ) * (δ₀ * (ρ / max D₀ 1)) ^ (s : ℝ) ≤ S.svfSum s n := by
    intro n
    calc ((W n).card : ℝ) * (δ₀ * (ρ / max D₀ 1)) ^ (s : ℝ)
        = ∑ _w ∈ W n, (δ₀ * (ρ / max D₀ 1)) ^ (s : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ w ∈ W n, svf s (S.matWord (List.ofFn w)) := by
          refine Finset.sum_le_sum fun w hw => ?_
          rw [hW, Finset.mem_filter] at hw
          rw [svf_matWord_eq, hexp, sub_self, Real.rpow_zero, mul_one]
          exact Real.rpow_le_rpow (by positivity)
            (hw.2.trans (S.abs_gDeriv_codeWord_le_alpha₁ c _)) s.coe_nonneg
      _ ≤ S.svfSum s n := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun w _ _ => svf_nonneg _ _
  have hcard : (C.card : ℝ) * (δ₀ * (ρ / max D₀ 1)) ^ (s : ℝ) ≤ K := by
    have h1 : (C.card : ℝ) ≤ ∑ n ∈ Finset.range L, ((W n).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le.trans
        (Finset.sum_le_sum fun n _ => Finset.card_image_le)
    calc (C.card : ℝ) * (δ₀ * (ρ / max D₀ 1)) ^ (s : ℝ)
        ≤ (∑ n ∈ Finset.range L, ((W n).card : ℝ)) * (δ₀ * (ρ / max D₀ 1)) ^ (s : ℝ) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ∑ n ∈ Finset.range L, ((W n).card : ℝ) * (δ₀ * (ρ / max D₀ 1)) ^ (s : ℝ) :=
          Finset.sum_mul _ _ _
      _ ≤ ∑ n ∈ Finset.range L, S.svfSum s n := Finset.sum_le_sum fun n _ => hword n
      _ ≤ K := hK L
  have hsplit : (δ₀ * (ρ / max D₀ 1)) ^ (-(s : ℝ)) =
      (δ₀ / max D₀ 1) ^ (-(s : ℝ)) * ρ ^ (-(s : ℝ)) := by
    rw [← Real.mul_rpow (by positivity) hρ.le]
    congr 1
    ring
  have hreal : (C.card : ℝ) ≤ K * (δ₀ / max D₀ 1) ^ (-(s : ℝ)) * ρ ^ (-(s : ℝ)) := by
    have hpos : 0 < (δ₀ * (ρ / max D₀ 1)) ^ (s : ℝ) := by positivity
    rw [mul_assoc, ← hsplit, Real.rpow_neg (by positivity), ← div_eq_mul_inv,
      le_div_iff₀ hpos]
    exact hcard
  calc (Metric.externalCoveringNumber ρ.toNNReal (coord c '' S.attractor) : ℝ≥0∞)
      ≤ (C.card : ℝ≥0∞) := by
        have h := hcov.externalCoveringNumber_le_encard
        rw [Set.encard_coe_eq_coe_finsetCard] at h
        exact_mod_cast ENat.toENNReal_le.2 h
    _ = ENNReal.ofReal (C.card : ℝ) := (ENNReal.ofReal_natCast _).symm
    _ ≤ ENNReal.ofReal (K * (δ₀ / max D₀ 1) ^ (-(s : ℝ)) * ρ ^ (-(s : ℝ))) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ((K * (δ₀ / max D₀ 1) ^ (-(s : ℝ))).toNNReal : ℝ≥0∞) * ENNReal.ofReal (ρ ^ (-(s : ℝ))) :=
        ENNReal.ofReal_mul (by positivity)

/-- `\overline{\dim}_M proj_c(X) ≤ dimaff(X)`: Falconer's bound for the coordinate projections,
proved from `upperBoxDim_coord_le_of_pressure_neg` for `dimaff(X) < 1` and from
`upperBoxDim_coord_le_one` otherwise. -/
theorem upperBoxDim_coord_le_dimaff [Nonempty ι] (c : ZMod 2) :
    upperBoxDim (coord c '' S.attractor) ≤ ENNReal.ofReal S.dimaff := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hsum : ENNReal.ofReal S.dimaff + ε = ENNReal.ofReal (S.dimaff + ε) := by
    rw [ENNReal.ofReal_add S.dimaff_nonneg ε.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  rw [hsum]
  have hpos : 0 ≤ S.dimaff + ε := add_nonneg S.dimaff_nonneg ε.coe_nonneg
  by_cases h : S.dimaff + ε ≤ 1
  · have hP : S.pressure ((S.dimaff + ε).toNNReal : ℝ) < 0 := by
      rw [Real.coe_toNNReal _ hpos]
      have h' := S.strictAntiOn_pressure (Set.mem_Ici.2 S.dimaff_nonneg) (Set.mem_Ici.2 hpos)
        (show S.dimaff < S.dimaff + ε by
          have : (0 : ℝ) < ε := hε
          linarith)
      rwa [S.pressure_dimaff] at h'
    exact S.upperBoxDim_coord_le_of_pressure_neg c (by rwa [Real.coe_toNNReal _ hpos]) hP
  · calc upperBoxDim (coord c '' S.attractor) ≤ 1 := S.upperBoxDim_coord_le_one c
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal (S.dimaff + ε) := ENNReal.ofReal_le_ofReal (le_of_lt (not_le.1 h))

/-- `s_1, s_2 ≤ dimaff(X)`. -/
theorem projDim_le_dimaff [Nonempty ι] (c : ZMod 2) : S.projDim c ≤ S.dimaff := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (S.upperBoxDim_coord_le_dimaff c)
  rwa [ENNReal.toReal_ofReal S.dimaff_nonneg] at h

/-- `dimmaff(X) ≤ dimaff(X)` when `s_1, s_2 ≤ dimaff(X)`: then `ψ^s ≤ φ^s` at `s = dimaff(X)`.
The bounds `s_1, s_2 ≤ 1` give `ψ^s ≤ φ^s` only for `s ≥ max{s_1, s_2}`. -/
theorem dimmaff_le_dimaff_of_projDim_le [Nonempty ι] (h : ∀ c, S.projDim c ≤ S.dimaff) :
    S.dimmaff ≤ S.dimaff := by
  refine S.dimmaff_le_of_modPressure_nonpos S.dimaff_nonneg ?_
  refine (S.modPressure_le_pressure S.dimaff_nonneg fun c => ?_).trans_eq S.pressure_dimaff
  have h1 := S.projDim_le_one c
  have h2 := h c
  unfold svfExp
  split_ifs <;> linarith

/-- `dimmaff(X) ≤ dimaff(X)` when `dimaff(X) ≥ 1`, from `s_1, s_2 ≤ 1` alone. -/
theorem dimmaff_le_dimaff_of_one_le [Nonempty ι] (h : 1 ≤ S.dimaff) : S.dimmaff ≤ S.dimaff :=
  S.dimmaff_le_dimaff_of_projDim_le fun c => (S.projDim_le_one c).trans h

/-- `dimmaff(X) ≤ dimaff(X)`, tex lines 515 to 515 and 2184, where the article attributes it to
Fraser. It follows from `s_1, s_2 ≤ dimaff(X)` (`projDim_le_dimaff`), Falconer's covering
argument for the coordinate projections. -/
theorem dimmaff_le_dimaff [Nonempty ι] : S.dimmaff ≤ S.dimaff :=
  S.dimmaff_le_dimaff_of_projDim_le S.projDim_le_dimaff

/-- The pressure part of Fraser's Corollary 2.5: if `s_1 = s_2 = 1` and `1 ≤ dimaff(X) ≤ 2`,
then `dimmaff(X) = dimaff(X)`, since `ψ^s = φ^s` for `1 ≤ s ≤ 2`. -/
theorem dimmaff_eq_dimaff_of_projDim_eq_one [Nonempty ι] (h : ∀ c, S.projDim c = 1)
    (h1 : 1 ≤ S.dimaff) (h2 : S.dimaff ≤ 2) : S.dimmaff = S.dimaff := by
  refine S.dimmaff_eq S.dimaff_nonneg ?_
  rw [S.modPressure_eq_pressure S.dimaff_nonneg fun c => (h c).trans (svfExp_eq_one h1 h2).symm,
    S.pressure_dimaff]

/-- The pressure part of Fraser's Corollary 2.5, read from the modified side: if
`s_1 = s_2 = 1` and `1 ≤ dimmaff(X) ≤ 2`, then `dimaff(X) = dimmaff(X)`. -/
theorem dimaff_eq_dimmaff_of_projDim_eq_one [Nonempty ι] (h : ∀ c, S.projDim c = 1)
    (h1 : 1 ≤ S.dimmaff) (h2 : S.dimmaff ≤ 2) : S.dimaff = S.dimmaff := by
  refine S.dimaff_eq S.dimmaff_nonneg ?_
  rw [← S.modPressure_eq_pressure S.dimmaff_nonneg
    fun c => (h c).trans (svfExp_eq_one h1 h2).symm, S.modPressure_dimmaff]

/-- `thm:fraser`, third part, without a separation condition: if `s_1 = s_2 = 1` and
`dimaff(X) ≤ 2`, then `dimmaff(X) = dimaff(X)`. The lower bound `1 = s_1 ≤ dimaff(X)` is
`projDim_le_dimaff`. -/
theorem dimmaff_eq_dimaff_of_full [Nonempty ι] (h : ∀ c, S.projDim c = 1)
    (h2 : S.dimaff ≤ 2) : S.dimmaff = S.dimaff :=
  S.dimmaff_eq_dimaff_of_projDim_eq_one h ((h 0).symm.le.trans (S.projDim_le_dimaff 0)) h2

/-! ### Existence of the limit defining the modified pressure -/

omit [Fintype ι] in
/-- If `s_1 = s_2 = t`, then `ψ^s(𝐢) = ‖A_𝐢‖^{2t-s} |det A_𝐢|^{s-t}`. -/
theorem modSvf_eq_norm_det {t : ℝ} (h : ∀ c, S.projDim c = t) (s : ℝ) (w : List ι) :
    S.modSvf s w = ‖S.matWord w‖ ^ (2 * t - s) * |(S.matWord w).det| ^ (s - t) := by
  rw [modSvf, S.wordDim_eq h, ← alpha₁_eq_norm, ← alpha₁_mul_alpha₂,
    Real.mul_rpow (S.alpha₁_pos w).le (S.alpha₂_pos w).le, ← mul_assoc,
    ← Real.rpow_add (S.alpha₁_pos w)]
  congr 2
  ring

/-- Fraser's Lemma 2.1 (b1) and (b2): `Ψ_{m+n}^s ≤ Ψ_m^s Ψ_n^s` for `s ≤ s_1 + s_2`. -/
theorem modSvfSum_add_le {s : ℝ} (hs : s ≤ S.projDim 0 + S.projDim 1) (m n : ℕ) :
    S.modSvfSum s (m + n) ≤ S.modSvfSum s m * S.modSvfSum s n := by
  rw [modSvfSum, sum_ofFn_add m n fun w => S.modSvf s w, modSvfSum, modSvfSum,
    Finset.sum_mul_sum]
  exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => S.modSvf_append_le hs _ _

/-- Fraser's Lemma 2.1 (b2) and (b3): `Ψ_m^s Ψ_n^s ≤ Ψ_{m+n}^s` for `s ≥ s_1 + s_2`. -/
theorem le_modSvfSum_add {s : ℝ} (hs : S.projDim 0 + S.projDim 1 ≤ s) (m n : ℕ) :
    S.modSvfSum s m * S.modSvfSum s n ≤ S.modSvfSum s (m + n) := by
  have hsplit : S.modSvfSum s (m + n) =
      ∑ g : Fin m → ι, ∑ h : Fin n → ι, S.modSvf s (List.ofFn g ++ List.ofFn h) :=
    sum_ofFn_add m n fun w => S.modSvf s w
  rw [hsplit, modSvfSum, modSvfSum, Finset.sum_mul_sum]
  exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => S.le_modSvf_append hs _ _

/-- The limit defining the modified pressure exists, by Fekete's lemma: the sums `Ψ_n^s` are
sub-multiplicative for `s ≤ s_1 + s_2` and super-multiplicative for `s ≥ s_1 + s_2`. This is
Fraser's definition of `P(s)`, §2.1, in logarithmic form. -/
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

end System

end BoxLike
