module

/-
The affinity dimension of a homogeneous diagonal system, for the projective exponential
separation case of the proof of `thm:main2` in `sec:dimension_result_proof`: "The pressure of
this subsystem at `u ≥ 0` is `log #W_n + log φ^u(diag(a_n, b_n))`. By `eq:diml_min2` and the
three limits above, `dimaff(X_n) → \dim_L(𝖠, μ_t)`." The energy `Λ(l_1, l_2, u)` of
`eq:energy_def` is linear in the exponents, and the Lyapunov dimension is the zero of the
strictly decreasing function `u ↦ h + Λ(l_1, l_2, u)`.

* `energy_mul`, `energy_div`, `tendsto_energy`: the energy is linear, hence continuous, in the
  pair of exponents.
* `energy_strictAnti`: `u ↦ Λ(l_1, l_2, u)` is strictly decreasing when `l_1, l_2 < 0`.
* `le_lyapDim_of_add_energy_nonneg`, `lt_lyapDim_of_add_energy_pos`,
  `lyapDim_lt_of_add_energy_neg`: the Lyapunov dimension is the zero of the strictly decreasing
  function `u ↦ h + Λ(l_1, l_2, u)`, so the sign of `h + Λ(l_1, l_2, u)` places `u` relative to
  `dim_L(h, l_1, l_2)`.
* `lyapDim_div`: `eq:diml_min2` is unchanged when `log #W_n`, `log |a_n|`, `log |b_n|` are
  divided by `n`.
* `tendsto_lyapDim`: `eq:diml_min2` is continuous where `l_2 < l_1 < 0` and `h > 0`: the limit
  `dimaff(X_n) → dim_L(𝖠, μ_t)` of the proof of `thm:main2`.
* `System.IsHomDiag.log_svf_matWord`: `log φ^u(A_𝐰) = |𝐰| Λ(log |a|, log |b|, u)`.
* `System.IsHomDiag.svfSum_eq`, `System.IsHomDiag.pressure_eq`:
  `P(u) = log #κ + Λ(log |a|, log |b|, u)` for `u ≥ 0`.
* `System.IsHomDiag.dimaff_eq`: `dimaff = dim_L(log #κ, log |a|, log |b|)`.
* `System.IsHomDiag.le_dimaff_of_nonneg`: `u ≤ dimaff` when `log #κ + Λ(log |a|, log |b|, u) ≥ 0`.
-/
public import BoxLike.AffinityDim
public import BoxLike.Lyapunov
public import BoxLike.MainTwoProse.DiagonalSubsystem
public import BoxLike.Variational

@[expose] public section

namespace BoxLike

open Filter Topology

/-! ### The energy as a function of the exponents -/

/-- The `s`-energy of `eq:energy_def` is linear in the pair of exponents. -/
theorem energy_mul (c l1 l2 s : ℝ) : energy (c * l1) (c * l2) s = c * energy l1 l2 s := by
  unfold energy
  split_ifs <;> ring

/-- The `s`-energy of `eq:energy_def` is linear in the pair of exponents: the form with
quotients, as for `log #W_n / n`, `log |a_n| / n`, `log |b_n| / n` in the proof of `thm:main2`. -/
theorem energy_div (l1 l2 s c : ℝ) : energy (l1 / c) (l2 / c) s = energy l1 l2 s / c := by
  rw [div_eq_inv_mul, div_eq_inv_mul, div_eq_inv_mul, energy_mul]

/-- The `s`-energy of `eq:energy_def` is continuous in the pair of exponents, for a fixed `s`:
the limits `log |a_n| / n → λ_1(𝖠, μ_t)` and `log |b_n| / n → λ_2(𝖠, μ_t)` of
`eq:diagonal-subsystem-limits` in the proof of `thm:main2`. -/
theorem tendsto_energy {x y : ℕ → ℝ} {l1 l2 : ℝ} (hx : Tendsto x atTop (𝓝 l1))
    (hy : Tendsto y atTop (𝓝 l2)) (s : ℝ) :
    Tendsto (fun m => energy (x m) (y m) s) atTop (𝓝 (energy l1 l2 s)) := by
  obtain ⟨c₁, c₂, hc⟩ := exists_energy_eq_linear s
  simp only [hc]
  exact (hx.const_mul c₁).add (hy.const_mul c₂)

/-- `eq:energy_def` through the exponent `p(s)` of `α_1` in `φ^s`:
`Λ(l_1, l_2, s) = p(s) l_1 + (s - p(s)) l_2`. -/
theorem energy_eq_svfExp (l1 l2 s : ℝ) :
    energy l1 l2 s = svfExp s * l1 + (s - svfExp s) * l2 := by
  unfold energy svfExp
  split_ifs <;> ring

/-- `u ↦ Λ(l_1, l_2, u)` is strictly decreasing when `l_1 < 0` and `l_2 < 0`: the sentence
"`Λ(𝖠, μ_t, ·)` is decreasing" of the proof of `thm:main2`. Both exponents `p(u)` and
`u - p(u)` of `eq:energy_def` are non-decreasing, and their sum is `u`. -/
theorem energy_strictAnti {l1 l2 : ℝ} (hl1 : l1 < 0) (hl2 : l2 < 0) :
    StrictAnti (energy l1 l2) := by
  intro s t hst
  have hp := svfExp_le_svfExp_add s (sub_nonneg.2 hst.le)
  have hq := svfExp_add_le s (sub_nonneg.2 hst.le)
  rw [add_sub_cancel] at hp hq
  rw [energy_eq_svfExp, energy_eq_svfExp]
  rcases lt_or_eq_of_le hp with hp' | hp'
  · have he : 0 ≤ (t - svfExp t) - (s - svfExp s) := by linarith
    nlinarith [mul_pos (sub_pos.2 hp') (neg_pos.2 hl1), mul_nonneg he (neg_nonneg.2 hl2.le)]
  · rw [← hp']
    nlinarith [mul_pos (sub_pos.2 hst) (neg_pos.2 hl2)]

/-- `u ≤ dim_L(h, l_1, l_2)` when `h + Λ(l_1, l_2, u) ≥ 0`, for `l_2 ≤ l_1 < 0` and `h ≥ 0`:
the Lyapunov dimension is the zero of the strictly decreasing function `u ↦ h + Λ(l_1, l_2, u)`,
"by the definition of the Lyapunov dimension, as `Λ(𝖠, μ_t, ·)` is decreasing" in the proof of
`thm:main2`. -/
theorem le_lyapDim_of_add_energy_nonneg {h l1 l2 u : ℝ} (hl : l2 ≤ l1) (hl1 : l1 < 0)
    (hh : 0 ≤ h) (hpos : 0 ≤ h + energy l1 l2 u) : u ≤ lyapDim h l1 l2 := by
  by_contra hlt
  rw [not_le] at hlt
  have := energy_strictAnti hl1 (hl.trans_lt hl1) hlt
  have h0 := add_energy_lyapDim hl hl1 hh
  linarith

/-- `u < dim_L(h, l_1, l_2)` when `h + Λ(l_1, l_2, u) > 0`, for `l_2 ≤ l_1 < 0` and `h ≥ 0`. -/
theorem lt_lyapDim_of_add_energy_pos {h l1 l2 u : ℝ} (hl : l2 ≤ l1) (hl1 : l1 < 0) (hh : 0 ≤ h)
    (hpos : 0 < h + energy l1 l2 u) : u < lyapDim h l1 l2 := by
  by_contra hle
  rw [not_lt] at hle
  have := (energy_strictAnti hl1 (hl.trans_lt hl1)).antitone hle
  have h0 := add_energy_lyapDim hl hl1 hh
  linarith

/-- `dim_L(h, l_1, l_2) < u` when `h + Λ(l_1, l_2, u) < 0`, for `l_2 ≤ l_1 < 0` and `h ≥ 0`. -/
theorem lyapDim_lt_of_add_energy_neg {h l1 l2 u : ℝ} (hl : l2 ≤ l1) (hl1 : l1 < 0) (hh : 0 ≤ h)
    (hneg : h + energy l1 l2 u < 0) : lyapDim h l1 l2 < u := by
  by_contra hle
  rw [not_lt] at hle
  have := (energy_strictAnti hl1 (hl.trans_lt hl1)).antitone hle
  have h0 := add_energy_lyapDim hl hl1 hh
  linarith

/-- The right-hand side of `eq:diml_min2` is unchanged when the entropy and both exponents are
divided by the same `c > 0`: `dimaff(X_n)` is the formula for `log #W_n`, `log |a_n|`,
`log |b_n|` as well as for `log #W_n / n`, `log |a_n| / n`, `log |b_n| / n` (proof of
`thm:main2`). -/
theorem lyapDim_div (h l1 l2 : ℝ) {c : ℝ} (hc : 0 < c) :
    lyapDim (h / c) (l1 / c) (l2 / c) = lyapDim h l1 l2 := by
  have hc' : c ≠ 0 := hc.ne'
  have e1 : h / c ≤ -(l1 / c) ↔ h ≤ -l1 := by
    rw [← neg_div, div_le_div_iff_of_pos_right hc]
  have e2 : h / c ≤ -(l1 / c) - l2 / c ↔ h ≤ -l1 - l2 := by
    rw [← neg_div, ← sub_div, div_le_div_iff_of_pos_right hc]
  unfold lyapDim
  simp only [e1, e2]
  split_ifs <;> field_simp

/-- The right-hand side of `eq:diml_min2` is continuous where `l_2 < l_1 < 0` and `h > 0`: if
`log #W_n → h`, `l_{1,n} → l_1` and `l_{2,n} → l_2`, then
`dim_L(log #W_n, l_{1,n}, l_{2,n}) → dim_L(h, l_1, l_2)`. This is the limit "by `eq:diml_min2`
and the three limits above, `dimaff(X_n) → \dim_L(𝖠, μ_t)`" of the proof of `thm:main2`, the
three limits being `eq:diagonal-subsystem-limits`. The Lyapunov dimension is the zero of
the strictly decreasing function `u ↦ h + Λ(l_1, l_2, u)`, and the energy is continuous in the
exponents, so for `u` on either side of the limit the sign of `log #W_n + Λ(l_{1,n}, l_{2,n}, u)`
is eventually that of `h + Λ(l_1, l_2, u)`. -/
theorem tendsto_lyapDim {H l1 l2 : ℕ → ℝ} {h a b : ℝ} (hH : Tendsto H atTop (𝓝 h))
    (h1 : Tendsto l1 atTop (𝓝 a)) (h2 : Tendsto l2 atTop (𝓝 b)) (hb : b < a) (ha : a < 0)
    (hh : 0 < h) :
    Tendsto (fun n => lyapDim (H n) (l1 n) (l2 n)) atTop (𝓝 (lyapDim h a b)) := by
  have hb0 : b < 0 := hb.trans ha
  -- eventually `l_{2,n} ≤ l_{1,n} < 0` and `log #W_n ≥ 0`
  have hev : ∀ᶠ n in atTop, l2 n ≤ l1 n ∧ l1 n < 0 ∧ 0 ≤ H n := by
    filter_upwards [h2.eventually_lt h1 hb, h1.eventually (gt_mem_nhds ha),
      hH.eventually (lt_mem_nhds hh)] with n hn1 hn2 hn3
    exact ⟨hn1.le, hn2, hn3.le⟩
  have hL := add_energy_lyapDim hb.le ha hh.le
  rw [tendsto_order]
  constructor
  · intro u hu
    have hpos : 0 < h + energy a b u := by
      have := energy_strictAnti ha hb0 hu
      linarith
    filter_upwards [hev, (hH.add (tendsto_energy h1 h2 u)).eventually (lt_mem_nhds hpos)]
      with n hn hn'
    exact lt_lyapDim_of_add_energy_pos hn.1 hn.2.1 hn.2.2 hn'
  · intro u hu
    have hneg : h + energy a b u < 0 := by
      have := energy_strictAnti ha hb0 hu
      linarith
    filter_upwards [hev, (hH.add (tendsto_energy h1 h2 u)).eventually (gt_mem_nhds hneg)]
      with n hn hn'
    exact lyapDim_lt_of_add_energy_neg hn.1 hn.2.1 hn.2.2 hn'

/-! ### The pressure and the affinity dimension of a homogeneous diagonal system -/

namespace System.IsHomDiag

variable {κ : Type*} [Fintype κ] [Nonempty κ] {T : System κ} {a b : ℝ} (hT : T.IsHomDiag a b)
include hT

omit [Fintype κ] in
/-- `log φ^u(A_𝐰) = |𝐰| Λ(log |a|, log |b|, u)` for a homogeneous diagonal system with
`|b| ≤ |a|`: `eq:energy_def` for one word, with `α_1(A_𝐰) = |a|^{|𝐰|}` and
`α_2(A_𝐰) = |b|^{|𝐰|}`. -/
theorem log_svf_matWord (hab : |b| ≤ |a|) (u : ℝ) (w : List κ) :
    Real.log (svf u (T.matWord w)) = w.length * energy (Real.log |a|) (Real.log |b|) u := by
  rw [T.log_svf_matWord, hT.log_norm_matWord hab, hT.log_abs_det_div_norm_matWord hab,
    energy_mul]

/-- `∑_{|𝐰| = n} φ^u(A_𝐰) = #κ^n exp(n Λ(log |a|, log |b|, u))` for a homogeneous diagonal
system with `|b| ≤ |a|`. -/
theorem svfSum_eq (hab : |b| ≤ |a|) (u : ℝ) (n : ℕ) :
    T.svfSum u n =
      (Fintype.card κ : ℝ) ^ n * Real.exp (n * energy (Real.log |a|) (Real.log |b|) u) := by
  have h : ∀ w : Fin n → κ, svf u (T.matWord (List.ofFn w)) =
      Real.exp (n * energy (Real.log |a|) (Real.log |b|) u) := fun w => by
    rw [← Real.exp_log (T.svf_matWord_pos u _), hT.log_svf_matWord hab, List.length_ofFn]
  rw [svfSum]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow]

/-- The pressure of a homogeneous diagonal system with `|b| ≤ |a|`:
`P(u) = log #κ + Λ(log |a|, log |b|, u)` for `u ≥ 0`, the sentence "the pressure of this
subsystem at `u ≥ 0` is `log #W_n + log φ^u(diag(a_n, b_n))`" of the proof of `thm:main2`. -/
theorem pressure_eq (hab : |b| ≤ |a|) {u : ℝ} (hu : 0 ≤ u) :
    T.pressure u = Real.log (Fintype.card κ) + energy (Real.log |a|) (Real.log |b|) u := by
  obtain ⟨δ, hδ⟩ := T.exists_ratioLowerBound
  refine tendsto_nhds_unique (hδ.tendsto_pressure hu) (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  rw [hT.svfSum_eq hab, Real.log_mul (pow_pos hc n).ne' (Real.exp_pos _).ne', Real.log_pow,
    Real.log_exp, ← mul_add, mul_div_cancel_left₀ _ hn']

/-- `dimaff = dim_L(log #κ, log |a|, log |b|)` for a homogeneous diagonal system with
`|b| ≤ |a|`: in the proof of `thm:main2`, `dimaff(X_n)` is the right-hand side of `eq:diml_min2`
with entropy `log #W_n` and Lyapunov exponents `log |a_n|` and `log |b_n|`, which "by
`eq:diml_min2` and the three limits above" tends to `\dim_L(𝖠, μ_t)`. -/
theorem dimaff_eq (hab : |b| ≤ |a|) :
    T.dimaff = lyapDim (Real.log (Fintype.card κ)) (Real.log |a|) (Real.log |b|) := by
  have hl : Real.log |b| ≤ Real.log |a| := Real.log_le_log (abs_pos.2 hT.b_ne_zero) hab
  have hl1 := hT.log_abs_a_neg
  have hh : 0 ≤ Real.log (Fintype.card κ) :=
    Real.log_nonneg (Nat.one_le_cast.2 Fintype.card_pos)
  refine System.dimaff_eq T (lyapDim_nonneg hl hl1 hh) ?_
  rw [hT.pressure_eq hab (lyapDim_nonneg hl hl1 hh), add_energy_lyapDim hl hl1 hh]

/-- `u ≤ dimaff` for `u ≥ 0` with `log #κ + Λ(log |a|, log |b|, u) ≥ 0`: the pressure of the
homogeneous diagonal system is non-negative at `u`. -/
theorem le_dimaff_of_nonneg (hab : |b| ≤ |a|) {u : ℝ} (hu : 0 ≤ u)
    (h : 0 ≤ Real.log (Fintype.card κ) + energy (Real.log |a|) (Real.log |b|) u) :
    u ≤ T.dimaff :=
  T.le_dimaff_of_pressure_nonneg hu (by rwa [hT.pressure_eq hab hu])

end System.IsHomDiag

end BoxLike
