module

/-
Projective exponential separation in `ex:projection_double_dimensional`, tex lines 2797 to
3012, by the volume argument on the translation cube `B ⊆ ℝ^8` with Lebesgue measure.

The maps of the projective system are `g_i^t(x) = a x + t_i` and `g_{i+4}^t(x) = b x + t_{i+4}`;
here the symbol `(i, 0)` of `Fin 4 × ZMod 2` is the map `g_i` and `(i, 1)` is `g_{i+4}`, with
translation coordinate `idx (i, c)`. For distinct words `𝐢`, `𝐣` of length `n` the difference
`L_{𝐢,𝐣}(t) = g_𝐢^t(0) - g_𝐣^t(0)` is linear in `t`; at the first differing symbol it has a
coefficient at least `κ b^{n-1}`, `κ = (1 - 2a)/(1 - a)`, so `|L_{𝐢,𝐣}| < ε` on a set of volume
at most `2ε/(κ b^{n-1})` in `B`. With `C = κ/8` and `c = b/128` the bad events `E_n` have volume
at most `(b/4) 2^{-n}`, their union has volume at most `b/4 < 1 = volume(B)`, and a translation
outside every `E_n` gives `Δ_n^Ψ ≥ C c^n` for all `n ≥ 1`.

* `PrescribedExample.volume_slab_le`: the one-dimensional interval estimate integrated over the
  other coordinates of a unit cube in `ℝ^{m+1}`.
* `PrescribedExample.idx`, `PrescribedExample.coef`, `PrescribedExample.gWord_zero_eq`:
  `g_𝐢^t(0) = ∑_q coef(𝐢)_q t_q`, with the coefficients independent of `t`.
* `PrescribedExample.L`, `PrescribedExample.L_append`: `L_{𝐢,𝐣}` and its factorisation at
  the first differing symbol.
* `PrescribedExample.one_le_coef_cons`, `PrescribedExample.coef_cons_le`,
  `PrescribedExample.kappa_le_coef_sub`, `PrescribedExample.kappa_mul_pow_le`: the coefficient
  bounds `≥ 1`, `≤ a/(1 - a)`, their difference `≥ κ`, and `κ b^{n-1}` for `L_{𝐢,𝐣}`.
* `PrescribedExample.volume_L_lt_le`: `volume{t ∈ B : |L_{𝐢,𝐣}(t)| < ε} ≤ 2ε/(κ b^{n-1})`.
* `PrescribedExample.constC`, `PrescribedExample.constc`, `PrescribedExample.badSet`,
  `PrescribedExample.volume_badSet_le`, `PrescribedExample.volume_iUnion_badSet_le`: the
  constants `C = κ/8`, `c = b/128`, the events `E_n` and the union bound.
* `PrescribedExample.exists_good_translation`: some `t ∈ B` lies outside every `E_n`.
* `PrescribedExample.le_abs_gWord_sub`, `PrescribedExample.le_gap`: `Δ_n^Ψ ≥ C c^n`.
* `System.noExactOverlaps_of_gWord_zero_ne`: distinct values `g_𝐢(0) ≠ g_𝐣(0)` for distinct words
  of equal length rule out exact overlaps.
* `PrescribedExample.exists_translation`: some `t ∈ B` gives the all-length gap, projective
  exponential separation with constant `C c` and no exact overlaps.
-/
public import BoxLike.PrescribedExample.Translations
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Fintype.Vector
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section

namespace BoxLike

open MeasureTheory Set
open scoped ENNReal

/-! ### No exact overlaps from distinct translations -/

namespace System

variable {ι : Type*} (S : System ι)

/-- A composition `g_𝐣` over a non-empty word has derivative of modulus less than one. -/
theorem abs_gDeriv_lt_one_of_ne_nil : ∀ {u : List (ι × ZMod 2)}, u ≠ [] → |S.gDeriv u| < 1
  | [], h => absurd rfl h
  | p :: u, _ => by
    have hu : |S.gDeriv u| ≤ 1 := by
      rcases u with _ | ⟨q, u⟩
      · simp
      · exact (abs_gDeriv_lt_one_of_ne_nil (List.cons_ne_nil q u)).le
    rw [gDeriv_cons, abs_mul]
    calc |S.ratio p| * |S.gDeriv u| ≤ |S.ratio p| * 1 :=
          mul_le_mul_of_nonneg_left hu (abs_nonneg _)
      _ < 1 := by rw [mul_one]; exact S.abs_ratio_lt_one p

/-- `ex:projection_double_dimensional`, "no exact overlaps" (tex line 2838): if
`g_𝐢(0) ≠ g_𝐣(0)` for any two distinct words `𝐢`, `𝐣` of the same length, then the projective
system has no exact overlaps. For words of different lengths, either one is a prefix of the
other, and the remaining word would give `g = id`, or `𝐢𝐣` and `𝐣𝐢` are distinct words of the
same length with `g_{𝐢𝐣} = g_{𝐣𝐢}`. -/
theorem noExactOverlaps_of_gWord_zero_ne
    (h : ∀ u u' : List (ι × ZMod 2), u.length = u'.length → u ≠ u' →
      S.gWord u 0 ≠ S.gWord u' 0) : S.NoExactOverlaps := by
  have hpre : ∀ u v : List (ι × ZMod 2), v ≠ [] → S.gWord u ≠ S.gWord (u ++ v) := by
    intro u v hv huv
    have hinj : Function.Injective (S.gWord u) := by
      intro x y hxy
      rw [S.gWord_apply u x, S.gWord_apply u y] at hxy
      exact mul_left_cancel₀ (S.gDeriv_ne_zero u) (add_right_cancel hxy)
    have hid : S.gWord v = id := by
      funext x
      have := congrFun huv x
      rw [gWord_append, Function.comp_apply] at this
      exact (hinj this).symm
    have h1 := S.gWord_apply v 1
    have h0 := S.gWord_apply v 0
    rw [hid] at h1 h0
    simp only [id, mul_zero, zero_add, mul_one] at h1 h0
    have hd : S.gDeriv v = 1 := by linarith
    have := S.abs_gDeriv_lt_one_of_ne_nil hv
    rw [hd, abs_one] at this
    exact lt_irrefl _ this
  intro u u' hne huu'
  by_cases h1 : u <+: u'
  · obtain ⟨v, rfl⟩ := h1
    exact hpre u v (fun hv => hne (by simp [hv])) huu'
  by_cases h2 : u' <+: u
  · obtain ⟨v, rfl⟩ := h2
    exact hpre u' v (fun hv => hne (by simp [hv])) huu'.symm
  have hne' : u ++ u' ≠ u' ++ u := by
    intro he
    rcases List.prefix_or_prefix_of_prefix (List.prefix_append u u')
      (he ▸ List.prefix_append u' u) with h | h
    · exact h1 h
    · exact h2 h
  refine h (u ++ u') (u' ++ u) (by simp [Nat.add_comm]) hne' ?_
  rw [gWord_append, gWord_append, huu']

end System

namespace PrescribedExample

/-! ### The one-dimensional interval estimate -/

/-- The interval estimate of `ex:projection_double_dimensional`, integrated over the other
coordinates: if the coefficient of `t_{q₀}` in the linear form `∑_q c_q t_q` has modulus at
least `θ > 0`, then on the unit cube `lo + [0, 1]^{m+1}` the form has modulus less than `ε`
only on a set of Lebesgue measure at most `2ε/θ`. For fixed other coordinates the condition
holds on an interval of length at most `2ε/θ`, and the other coordinates range over a unit
cube. -/
theorem volume_slab_le {m : ℕ} (c lo : Fin (m + 1) → ℝ) (q₀ : Fin (m + 1)) {θ ε : ℝ}
    (hθ : 0 < θ) (hc : θ ≤ |c q₀|) (hε : 0 ≤ ε) :
    volume {t : Fin (m + 1) → ℝ | (∀ q, t q ∈ Icc (lo q) (lo q + 1)) ∧
      |∑ q, c q * t q| < ε} ≤ ENNReal.ofReal (2 * ε / θ) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) q₀
  have he : MeasurePreserving e volume volume := volume_preserving_piFinSuccAbove _ q₀
  set K : Set (Fin m → ℝ) :=
    Set.pi univ fun j => Icc (lo (q₀.succAbove j)) (lo (q₀.succAbove j) + 1) with hK
  set d : (Fin m → ℝ) → ℝ := fun y => ∑ j, c (q₀.succAbove j) * y j with hd
  set T : Set (ℝ × (Fin m → ℝ)) := {z | z.2 ∈ K ∧ |c q₀ * z.1 + d z.2| < ε} with hT
  have hc0 : 0 < |c q₀| := hθ.trans_le hc
  have hKm : MeasurableSet K := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hTm : MeasurableSet T := by
    have hcont : Continuous fun z : ℝ × (Fin m → ℝ) => |c q₀ * z.1 + d z.2| := by
      simp only [hd]
      fun_prop
    exact (measurable_snd hKm).inter (isOpen_lt hcont continuous_const).measurableSet
  have hsub : {t : Fin (m + 1) → ℝ | (∀ q, t q ∈ Icc (lo q) (lo q + 1)) ∧
      |∑ q, c q * t q| < ε} ⊆ e ⁻¹' T := by
    intro t ⟨ht1, ht2⟩
    refine ⟨fun j _ => ht1 _, ?_⟩
    rw [Fin.sum_univ_succAbove _ q₀] at ht2
    simpa [e, d, MeasurableEquiv.piFinSuccAbove_apply, Fin.removeNth] using ht2
  have hsec : ∀ y : Fin m → ℝ, volume ((fun x => (x, y)) ⁻¹' T) ≤
      K.indicator (fun _ => ENNReal.ofReal (2 * ε / θ)) y := by
    intro y
    by_cases hy : y ∈ K
    · rw [indicator_of_mem hy]
      have hs : (fun x => (x, y)) ⁻¹' T ⊆ Metric.ball (-(d y) / c q₀) (ε / |c q₀|) := by
        intro x hx
        have hx2 : |c q₀ * x + d y| < ε := hx.2
        rw [Metric.mem_ball, Real.dist_eq, lt_div_iff₀ hc0, ← abs_mul]
        have hcne : c q₀ ≠ 0 := abs_pos.1 hc0
        have : (x - -d y / c q₀) * c q₀ = c q₀ * x + d y := by
          field_simp
          ring
        rwa [this]
      refine (measure_mono hs).trans ?_
      rw [Real.volume_ball]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hε hθ hc) zero_le_two
    · rw [indicator_of_notMem hy]
      have hs : (fun x => (x, y)) ⁻¹' T = ∅ := by
        ext x
        simp only [mem_preimage, mem_empty_iff_false, iff_false]
        exact fun h => hy h.1
      rw [hs, measure_empty]
  have hKvol : volume K = 1 := by
    rw [hK, volume_pi_pi]
    simp [Real.volume_Icc]
  calc volume {t : Fin (m + 1) → ℝ | (∀ q, t q ∈ Icc (lo q) (lo q + 1)) ∧
        |∑ q, c q * t q| < ε}
      ≤ volume (e ⁻¹' T) := measure_mono hsub
    _ = volume T := he.measure_preimage_equiv T
    _ = ∫⁻ y, volume ((fun x => (x, y)) ⁻¹' T) := Measure.prod_apply_symm hTm
    _ ≤ ∫⁻ y, K.indicator (fun _ => ENNReal.ofReal (2 * ε / θ)) y := lintegral_mono hsec
    _ = ENNReal.ofReal (2 * ε / θ) * volume K := lintegral_indicator_const hKm _
    _ = ENNReal.ofReal (2 * ε / θ) := by rw [hKvol, mul_one]

/-- The translation cube `B` has Lebesgue measure one. -/
theorem volume_cube (P : Params) : volume (cube P) = 1 := by
  rw [cube, volume_pi_pi]
  simp [Real.volume_Icc]

/-! ### The translation coefficients -/

/-- The translation coordinate of the symbol `(i, c)` of the projective system of
`ex:projection_double_dimensional`: `i` for `c = 0` (the map `g_i`) and `i + 4` for `c = 1`
(the map `g_{i+4}`). -/
def idx (p : Fin 4 × ZMod 2) : Fin 8 := if p.2 = 0 then Fin.castAdd 4 p.1 else Fin.natAdd 4 p.1

/-- Distinct symbols have distinct translation coordinates. -/
theorem idx_injective : Function.Injective idx := by decide

variable (P : Params)

/-- The translation of the symbol `p` of the projective system is the coordinate `idx p` of
`t`: `g_j^t(0) = t_j` (`ex:projection_double_dimensional`). -/
theorem sys_trans (t : Fin 8 → ℝ) (p : Fin 4 × ZMod 2) : (sys P t).trans p = t (idx p) := by
  rcases zmod_two_cases p.2 with h | h <;>
    simp [System.trans, System.coord, idx, sys, h]

/-- The contraction ratio of the symbol `p`, independent of the translations: `a` for the maps
`g_1, …, g_4` and `b` for `g_5, …, g_8`. -/
noncomputable def rat (p : Fin 4 × ZMod 2) : ℝ := if p.2 = 0 then P.a else P.b

/-- The contraction ratios of the projective system do not depend on the translations. -/
theorem sys_ratio_eq_rat (t : Fin 8 → ℝ) (p : Fin 4 × ZMod 2) : (sys P t).ratio p = rat P p :=
  rfl

/-- `b ≤ rat p`. -/
theorem b_le_rat (p : Fin 4 × ZMod 2) : P.b ≤ rat P p := by
  unfold rat; split_ifs
  · exact P.b_lt_a.le
  · exact le_rfl

/-- `rat p ≤ a`. -/
theorem rat_le_a (p : Fin 4 × ZMod 2) : rat P p ≤ P.a := by
  unfold rat; split_ifs
  · exact le_rfl
  · exact P.b_lt_a.le

/-- `rat p > 0`. -/
theorem rat_pos (p : Fin 4 × ZMod 2) : 0 < rat P p := P.b_pos.trans_le (b_le_rat P p)

/-- The coefficients of `g_𝐢^t(0)` as a linear form in `t ∈ ℝ^8`
(`ex:projection_double_dimensional`): `coef (p 𝐢) = e_{idx p} + rat(p) coef 𝐢`. -/
noncomputable def coef : List (Fin 4 × ZMod 2) → Fin 8 → ℝ
  | [] => fun _ => 0
  | p :: u => fun q => (if idx p = q then 1 else 0) + rat P p * coef u q

/-- The empty composition is the identity, with `g(0) = 0`. -/
@[simp] theorem coef_nil (q : Fin 8) : coef P [] q = 0 := rfl

/-- `g_{p 𝐢}^t(0) = t_{idx p} + rat(p) g_𝐢^t(0)` in coefficients. -/
theorem coef_cons (p : Fin 4 × ZMod 2) (u : List (Fin 4 × ZMod 2)) (q : Fin 8) :
    coef P (p :: u) q = (if idx p = q then 1 else 0) + rat P p * coef P u q := rfl

/-- `g_𝐢^t(0) = ∑_q coef(𝐢)_q t_q`: the value at zero of a composition of the projective system
of `ex:projection_double_dimensional` is linear in the translation vector `t`. -/
theorem gWord_zero_eq (t : Fin 8 → ℝ) (u : List (Fin 4 × ZMod 2)) :
    (sys P t).gWord u 0 = ∑ q, coef P u q * t q := by
  induction u with
  | nil => simp
  | cons p u ih =>
    rw [System.gWord_cons, Function.comp_apply, ih, System.g, sys_trans, sys_ratio_eq_rat]
    simp only [coef_cons, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_assoc, ← Finset.mul_sum]
    ring

/-- The coefficients are non-negative. -/
theorem coef_nonneg (u : List (Fin 4 × ZMod 2)) (q : Fin 8) : 0 ≤ coef P u q := by
  induction u with
  | nil => simp
  | cons p u ih =>
    rw [coef_cons]
    have := mul_nonneg (rat_pos P p).le ih
    split_ifs <;> linarith

/-- Every coefficient is at most `1 + a + a^2 + ⋯ = 1/(1 - a)`. -/
theorem coef_le (u : List (Fin 4 × ZMod 2)) (q : Fin 8) : coef P u q ≤ 1 / (1 - P.a) := by
  have ha : 0 < 1 - P.a := by linarith [P.a_lt_one]
  induction u with
  | nil => simp only [coef_nil]; positivity
  | cons p u ih =>
    rw [coef_cons]
    have h1 : rat P p * coef P u q ≤ P.a * (1 / (1 - P.a)) :=
      mul_le_mul (rat_le_a P p) ih (coef_nonneg P u q) P.a_pos.le
    have h2 : 1 + P.a * (1 / (1 - P.a)) = 1 / (1 - P.a) := by
      field_simp
      ring
    split_ifs <;> linarith

/-- The coefficient of `t_{i_k}` in `g_{i_k ⋯ i_n}^t(0)` is at least one
(`ex:projection_double_dimensional`). -/
theorem one_le_coef_cons (p : Fin 4 × ZMod 2) (u : List (Fin 4 × ZMod 2)) :
    1 ≤ coef P (p :: u) (idx p) := by
  rw [coef_cons, ite_eq_left rfl]
  linarith [mul_nonneg (rat_pos P p).le (coef_nonneg P u (idx p))]

/-- The coefficient of `t_{i_k}` in `g_{j_k ⋯ j_n}^t(0)` is at most `a + a^2 + ⋯ = a/(1 - a)`
when `j_k ≠ i_k` (`ex:projection_double_dimensional`). -/
theorem coef_cons_le {p p' : Fin 4 × ZMod 2} (hpp' : p ≠ p') (u : List (Fin 4 × ZMod 2)) :
    coef P (p' :: u) (idx p) ≤ P.a / (1 - P.a) := by
  rw [coef_cons, ite_eq_right fun h => hpp' (idx_injective h).symm, zero_add,
    div_eq_mul_one_div]
  exact mul_le_mul (rat_le_a P p') (coef_le P u _) (coef_nonneg P u _) P.a_pos.le

/-- The constant `κ = (1 - 2a)/(1 - a)` of `ex:projection_double_dimensional`. -/
noncomputable def kappa : ℝ := (1 - 2 * P.a) / (1 - P.a)

/-- `κ > 0`. -/
theorem kappa_pos : 0 < kappa P :=
  div_pos (one_sub_two_mul_a_pos P) (by linarith [P.a_lt_one])

/-- `κ ≤ 1`. -/
theorem kappa_le_one : kappa P ≤ 1 := by
  rw [kappa, div_le_one (by linarith [P.a_lt_one])]
  linarith [P.a_pos]

/-- The difference of the coefficients of `t_{i_k}` in `g_{i_k ⋯ i_n}^t(0)` and in
`g_{j_k ⋯ j_n}^t(0)` is at least `κ = 1 - a/(1 - a)` (`ex:projection_double_dimensional`). -/
theorem kappa_le_coef_sub {p p' : Fin 4 × ZMod 2} (hpp' : p ≠ p') (x x' : List (Fin 4 × ZMod 2)) :
    kappa P ≤ coef P (p :: x) (idx p) - coef P (p' :: x') (idx p) := by
  have h1 := one_le_coef_cons P p x
  have h2 := coef_cons_le P hpp' x'
  have e : kappa P = 1 - P.a / (1 - P.a) := by
    have : (1 : ℝ) - P.a ≠ 0 := by linarith [P.a_lt_one]
    rw [kappa]
    field_simp
    ring
  linarith

/-! ### The differences `L_{𝐢,𝐣}` -/

/-- The difference `L_{𝐢,𝐣}(t) = g_𝐢^t(0) - g_𝐣^t(0)` of `ex:projection_double_dimensional`. -/
noncomputable def L (u u' : List (Fin 4 × ZMod 2)) (t : Fin 8 → ℝ) : ℝ :=
  (sys P t).gWord u 0 - (sys P t).gWord u' 0

/-- `L_{𝐢,𝐣}(t) = (g_{i_1 ⋯ i_{k-1}}^t)'(0) (g_{i_k ⋯ i_n}^t(0) - g_{j_k ⋯ j_n}^t(0))` for words
with the common prefix `i_1 ⋯ i_{k-1}` (`ex:projection_double_dimensional`). -/
theorem L_append (w y y' : List (Fin 4 × ZMod 2)) (t : Fin 8 → ℝ) :
    L P (w ++ y) (w ++ y') t = (sys P t).gDeriv w * L P y y' t := by
  simp only [L, System.gWord_append, Function.comp_apply]
  rw [(sys P t).gWord_apply w ((sys P t).gWord y 0),
    (sys P t).gWord_apply w ((sys P t).gWord y' 0)]
  ring

/-- The derivative of a composition over `w` is `∏ rat`, independent of `t`, and at least
`b^{|w|}`. -/
theorem pow_le_gDeriv (t : Fin 8 → ℝ) (w : List (Fin 4 × ZMod 2)) :
    P.b ^ w.length ≤ (sys P t).gDeriv w := by
  induction w with
  | nil => simp
  | cons p w ih =>
    rw [System.gDeriv_cons, List.length_cons, pow_succ']
    exact mul_le_mul (b_le_rat P p) ih (pow_nonneg P.b_pos.le _) (rat_pos P p).le

/-- Two distinct words of the same length have a first differing symbol: they are `w p x` and
`w p' x'` with `p ≠ p'`. -/
theorem exists_first_diff {α : Type*} :
    ∀ {u u' : List α}, u.length = u'.length → u ≠ u' →
      ∃ w : List α, ∃ p : α, ∃ x : List α, ∃ p' : α, ∃ x' : List α,
        u = w ++ p :: x ∧ u' = w ++ p' :: x' ∧ p ≠ p'
  | [], [], _, hne => absurd rfl hne
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | p :: x, p' :: x', hlen, hne => by
    by_cases hp : p = p'
    · subst hp
      have hx : x ≠ x' := fun h => hne (by rw [h])
      obtain ⟨w, q, y, q', y', rfl, rfl, hq⟩ :=
        exists_first_diff (by simpa using hlen) hx
      exact ⟨p :: w, q, y, q', y', rfl, rfl, hq⟩
    · exact ⟨[], p, x, p', x', rfl, rfl, hp⟩

/-- For distinct words `𝐢`, `𝐣` of length `n`, `L_{𝐢,𝐣}(t) = ∑_q c_q t_q` with a coefficient
`c_{i_k} ≥ κ b^{n-1}` at the first differing symbol `i_k`, and with `c` independent of `t`
(`ex:projection_double_dimensional`). -/
theorem kappa_mul_pow_le {u u' : List (Fin 4 × ZMod 2)} (hlen : u.length = u'.length)
    (hne : u ≠ u') :
    ∃ c : Fin 8 → ℝ, ∃ q₀ : Fin 8, kappa P * P.b ^ (u.length - 1) ≤ c q₀ ∧
      ∀ t, L P u u' t = ∑ q, c q * t q := by
  obtain ⟨w, p, x, p', x', rfl, rfl, hpp'⟩ := exists_first_diff hlen hne
  set D : ℝ := (sys P 0).gDeriv w
  have hD : ∀ t, (sys P t).gDeriv w = D := fun _ => rfl
  refine ⟨fun q => D * (coef P (p :: x) q - coef P (p' :: x') q), idx p, ?_, fun t => ?_⟩
  · have hk := kappa_le_coef_sub P hpp' x x'
    have hb : P.b ^ ((w ++ p :: x).length - 1) ≤ P.b ^ w.length :=
      pow_le_pow_of_le_one P.b_pos.le P.b_lt_one.le (by simp)
    have hDb : P.b ^ w.length ≤ D := pow_le_gDeriv P 0 w
    have hκ := kappa_pos P
    calc kappa P * P.b ^ ((w ++ p :: x).length - 1) ≤ kappa P * D :=
          mul_le_mul_of_nonneg_left (hb.trans hDb) hκ.le
      _ ≤ (coef P (p :: x) (idx p) - coef P (p' :: x') (idx p)) * D :=
          mul_le_mul_of_nonneg_right hk ((pow_nonneg P.b_pos.le _).trans hDb)
      _ = D * (coef P (p :: x) (idx p) - coef P (p' :: x') (idx p)) := mul_comm _ _
  · rw [L_append, hD, L, gWord_zero_eq, gWord_zero_eq, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring

/-- `volume{t ∈ B : |L_{𝐢,𝐣}(t)| < ε} ≤ 2ε/(κ b^{n-1})` for distinct words of length `n`
(`ex:projection_double_dimensional`). -/
theorem volume_L_lt_le {u u' : List (Fin 4 × ZMod 2)} (hlen : u.length = u'.length)
    (hne : u ≠ u') {ε : ℝ} (hε : 0 ≤ ε) :
    volume {t | t ∈ cube P ∧ |L P u u' t| < ε} ≤
      ENNReal.ofReal (2 * ε / (kappa P * P.b ^ (u.length - 1))) := by
  obtain ⟨c, q₀, hc, hL⟩ := kappa_mul_pow_le P hlen hne
  have hθ : 0 < kappa P * P.b ^ (u.length - 1) := mul_pos (kappa_pos P) (pow_pos P.b_pos _)
  refine le_trans (measure_mono ?_)
    (volume_slab_le (m := 7) c (lo P) q₀ hθ (hc.trans (le_abs_self _)) hε)
  rintro t ⟨ht, hlt⟩
  exact ⟨fun q => ht q (mem_univ q), by rwa [← hL]⟩

/-! ### The bad events and their union -/

/-- The constant `C = κ/8` of `ex:projection_double_dimensional`. -/
noncomputable def constC : ℝ := kappa P / 8

/-- The constant `c = b/128` of `ex:projection_double_dimensional`. -/
noncomputable def constc : ℝ := P.b / 128

/-- `C > 0`. -/
theorem constC_pos : 0 < constC P := div_pos (kappa_pos P) (by norm_num)

/-- `C ≤ 1`. -/
theorem constC_le_one : constC P ≤ 1 := by
  rw [constC]
  linarith [kappa_le_one P]

/-- `c > 0`. -/
theorem constc_pos : 0 < constc P := div_pos P.b_pos (by norm_num)

/-- The bad event `E_n ⊆ B` of `ex:projection_double_dimensional`: the translations for which
`|L_{𝐢,𝐣}(t)| < C c^n` for at least one pair of distinct words of length `n`. -/
def badSet (n : ℕ) : Set (Fin 8 → ℝ) :=
  {t | t ∈ cube P ∧ ∃ u u' : List (Fin 4 × ZMod 2), u.length = n ∧ u'.length = n ∧ u ≠ u' ∧
    |L P u u' t| < constC P * constc P ^ n}

/-- The number of ordered pairs of words of length `n` over the eight symbols is `64^n`. -/
theorem card_pairs (n : ℕ) :
    Fintype.card (List.Vector (Fin 4 × ZMod 2) n × List.Vector (Fin 4 × ZMod 2) n) = 64 ^ n := by
  rw [Fintype.card_prod, card_vector, Fintype.card_prod, ZMod.card, Fintype.card_fin, ← mul_pow]
  norm_num

/-- The arithmetic of the union bound: `64^n · 2 C c^n / (κ b^{n-1}) = (b/4) 2^{-n}`. -/
theorem union_bound_arith (m : ℕ) :
    (64 : ℝ) ^ (m + 1) * (2 * (constC P * constc P ^ (m + 1)) / (kappa P * P.b ^ m)) =
      P.b / 4 * (1 / 2) ^ (m + 1) := by
  have hκ := (kappa_pos P).ne'
  have hb := P.b_pos.ne'
  have e : constc P ^ (m + 1) = P.b * P.b ^ m * ((1 / 2) ^ (m + 1) / 64 ^ (m + 1)) := by
    rw [constc, show (128 : ℝ) = 2 * 64 by norm_num, div_pow, mul_pow, pow_succ' P.b,
      div_pow, one_pow]
    field_simp
  rw [constC, e]
  field_simp
  ring

/-- `volume(E_n) ≤ (b/4) 2^{-n}` for `n ≥ 1` (`ex:projection_double_dimensional`): there are at
most `64^n` pairs of words of length `n`, each contributing at most `2 C c^n/(κ b^{n-1})`. -/
theorem volume_badSet_le (m : ℕ) :
    volume (badSet P (m + 1)) ≤ ENNReal.ofReal (P.b / 4 * (1 / 2) ^ (m + 1)) := by
  set ε := constC P * constc P ^ (m + 1)
  have hε : 0 ≤ ε := (mul_pos (constC_pos P) (pow_pos (constc_pos P) _)).le
  set β := ENNReal.ofReal (2 * ε / (kappa P * P.b ^ m))
  set piece : List.Vector (Fin 4 × ZMod 2) (m + 1) × List.Vector (Fin 4 × ZMod 2) (m + 1) →
      Set (Fin 8 → ℝ) := fun w => {t | t ∈ cube P ∧ w.1.1 ≠ w.2.1 ∧ |L P w.1.1 w.2.1 t| < ε}
  have hcover : badSet P (m + 1) ⊆ ⋃ w, piece w := by
    rintro t ⟨ht, u, u', hu, hu', hne, hlt⟩
    exact mem_iUnion.2 ⟨(⟨u, hu⟩, ⟨u', hu'⟩), ht, hne, hlt⟩
  have hpiece : ∀ w, volume (piece w) ≤ β := by
    intro w
    by_cases hw : w.1.1 = w.2.1
    · have : piece w = ∅ := eq_empty_of_forall_notMem fun t ht => ht.2.1 hw
      rw [this, measure_empty]
      exact bot_le
    · have h := volume_L_lt_le P (w.1.2.trans w.2.2.symm) hw hε
      rw [w.1.2, Nat.add_sub_cancel] at h
      refine le_trans (measure_mono ?_) h
      rintro t ⟨ht, -, hlt⟩
      exact ⟨ht, hlt⟩
  calc volume (badSet P (m + 1)) ≤ volume (⋃ w, piece w) := measure_mono hcover
    _ ≤ ∑ w, volume (piece w) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _w : List.Vector (Fin 4 × ZMod 2) (m + 1) × List.Vector (Fin 4 × ZMod 2) (m + 1),
          β := Finset.sum_le_sum fun w _ => hpiece w
    _ = ENNReal.ofReal ((64 : ℝ) ^ (m + 1) * (2 * ε / (kappa P * P.b ^ m))) := by
      rw [Finset.sum_const, Finset.card_univ, card_pairs, nsmul_eq_mul,
        ENNReal.ofReal_mul (by positivity)]
      norm_cast
    _ = ENNReal.ofReal (P.b / 4 * (1 / 2) ^ (m + 1)) := by rw [union_bound_arith]

/-- `volume(⋃_{n ≥ 1} E_n) ≤ b/4` (`ex:projection_double_dimensional`). -/
theorem volume_iUnion_badSet_le :
    volume (⋃ m : ℕ, badSet P (m + 1)) ≤ ENNReal.ofReal (P.b / 4) := by
  have hnn : ∀ m : ℕ, 0 ≤ P.b / 4 * (1 / 2 : ℝ) ^ (m + 1) := fun m => by
    have := P.b_pos
    positivity
  have hsum : Summable fun m : ℕ => P.b / 4 * (1 / 2 : ℝ) ^ (m + 1) := by
    simp_rw [pow_succ]
    exact (summable_geometric_two.mul_right _).mul_left _
  have htsum : ∑' m : ℕ, P.b / 4 * (1 / 2 : ℝ) ^ (m + 1) = P.b / 4 := by
    simp_rw [pow_succ]
    rw [tsum_mul_left, tsum_mul_right, tsum_geometric_two]
    ring
  calc volume (⋃ m : ℕ, badSet P (m + 1)) ≤ ∑' m, volume (badSet P (m + 1)) :=
        measure_iUnion_le _
    _ ≤ ∑' m : ℕ, ENNReal.ofReal (P.b / 4 * (1 / 2) ^ (m + 1)) :=
        ENNReal.tsum_le_tsum fun m => volume_badSet_le P m
    _ = ENNReal.ofReal (P.b / 4) := by rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum, htsum]

/-- Some translation `t ∈ B` lies outside every bad event `E_n`, `n ≥ 1`, since
`volume(⋃_{n ≥ 1} E_n) ≤ b/4 < 1 = volume(B)` (`ex:projection_double_dimensional`). -/
theorem exists_good_translation : ∃ t ∈ cube P, ∀ m : ℕ, t ∉ badSet P (m + 1) := by
  have hnot : ¬ cube P ⊆ ⋃ m : ℕ, badSet P (m + 1) := by
    intro hsub
    have h1 := (measure_mono hsub).trans (volume_iUnion_badSet_le P)
    rw [volume_cube] at h1
    have h2 : ENNReal.ofReal (P.b / 4) < 1 := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by linarith [P.b_lt_one])
    exact absurd h1 (not_le.2 h2)
  obtain ⟨t, ht, htn⟩ := not_subset.1 hnot
  exact ⟨t, ht, fun m hm => htn (mem_iUnion.2 ⟨m, hm⟩)⟩

/-! ### The gap and the separation conditions -/

variable {P}

/-- For `t ∈ B` outside every `E_n`, every pair of distinct words of length `n ≥ 1` satisfies
`|g_𝐢^t(0) - g_𝐣^t(0)| ≥ C c^n` (`ex:projection_double_dimensional`). -/
theorem le_abs_gWord_sub {t : Fin 8 → ℝ} (ht : t ∈ cube P) (hgood : ∀ m : ℕ, t ∉ badSet P (m + 1))
    {n : ℕ} (hn : 1 ≤ n) {u u' : List (Fin 4 × ZMod 2)} (hu : u.length = n) (hu' : u'.length = n)
    (hne : u ≠ u') :
    constC P * constc P ^ n ≤ |(sys P t).gWord u 0 - (sys P t).gWord u' 0| := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  by_contra hlt
  exact hgood m ⟨ht, u, u', hu, hu', hne, not_le.1 hlt⟩

/-- `Δ_n^Ψ ≥ C c^n` for every `n ≥ 1` (`ex:projection_double_dimensional`). -/
theorem le_gap {t : Fin 8 → ℝ} (ht : t ∈ cube P) (hgood : ∀ m : ℕ, t ∉ badSet P (m + 1))
    {n : ℕ} (hn : 1 ≤ n) : ENNReal.ofReal (constC P * constc P ^ n) ≤ (sys P t).gap n :=
  le_iInf fun _ => le_iInf fun _ => le_iInf fun hu => le_iInf fun hu' =>
    le_iInf fun hne => le_iInf fun _ =>
      ENNReal.ofReal_le_ofReal (le_abs_gWord_sub ht hgood hn hu hu' hne)

/-- Projective exponential separation for `t ∈ B` outside every `E_n`
(`ex:projection_double_dimensional`): `Δ_n^Ψ ≥ C c^n ≥ (C c)^n` for every `n ≥ 1`, since
`C ≤ 1`; the prefactor `C` is absorbed into the base `C c`. -/
theorem projExpSeparation {t : Fin 8 → ℝ} (ht : t ∈ cube P)
    (hgood : ∀ m : ℕ, t ∉ badSet P (m + 1)) : (sys P t).ProjExpSeparation := by
  have hC := constC_pos P
  have hc := constc_pos P
  refine ⟨constC P * constc P, mul_pos hC hc, fun k => k + 1,
    fun a b h => Nat.succ_lt_succ h, fun k => ?_⟩
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (le_gap ht hgood (Nat.le_add_left 1 k))
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_of_le_one hC.le (constC_le_one P) k.succ_ne_zero)
    (pow_nonneg hc.le _)

/-- No exact overlaps for `t ∈ B` outside every `E_n` (`ex:projection_double_dimensional`). -/
theorem noExactOverlaps {t : Fin 8 → ℝ} (ht : t ∈ cube P)
    (hgood : ∀ m : ℕ, t ∉ badSet P (m + 1)) : (sys P t).NoExactOverlaps := by
  refine (sys P t).noExactOverlaps_of_gWord_zero_ne fun u u' hlen hne heq => ?_
  rcases Nat.eq_zero_or_pos u.length with h0 | hpos
  · exact hne ((List.length_eq_zero_iff.1 h0).trans
      (List.length_eq_zero_iff.1 (hlen ▸ h0)).symm)
  · have h := le_abs_gWord_sub ht hgood hpos rfl hlen.symm hne
    rw [heq, sub_self, abs_zero] at h
    exact absurd h (not_le.2 (mul_pos (constC_pos P) (pow_pos (constc_pos P) _)))

variable (P)

/-- The translation selection of `ex:projection_double_dimensional`: some `t ∈ B` satisfies
`|g_𝐢^t(0) - g_𝐣^t(0)| ≥ C c^n` for all distinct words of every length `n ≥ 1`, with
`C = κ/8` and `c = b/128`; hence `Δ_n^Ψ ≥ C c^n`, the projective exponential separation
condition and the absence of exact overlaps. -/
theorem exists_translation :
    ∃ t ∈ cube P,
      (∀ n : ℕ, 1 ≤ n → ∀ u u' : List (Fin 4 × ZMod 2), u.length = n → u'.length = n →
        u ≠ u' → constC P * constc P ^ n ≤ |(sys P t).gWord u 0 - (sys P t).gWord u' 0|) ∧
      (∀ n : ℕ, 1 ≤ n → ENNReal.ofReal (constC P * constc P ^ n) ≤ (sys P t).gap n) ∧
      (sys P t).ProjExpSeparation ∧ (sys P t).NoExactOverlaps := by
  obtain ⟨t, ht, hgood⟩ := exists_good_translation P
  exact ⟨t, ht, fun n hn u u' hu hu' hne => le_abs_gWord_sub ht hgood hn hu hu' hne,
    fun n hn => le_gap ht hgood hn, projExpSeparation ht hgood, noExactOverlaps ht hgood⟩

end PrescribedExample

end BoxLike
