module

/-
The glue between the library `BoxLike` and the core theorem `HomogeneousCore` of the proof of
Rapaport's theorem. Theorem B (iii) of the paper applies
`thm:rapaport` only to homogeneous diagonal subsystems `T` (`System.IsHomDiag`) with
`|b| < |a|`, through `System.dimH_subsystem_attractor_eq`. For such `T` with the uniform
Bernoulli measure `ν`, `μ = π_*ν`, `H = log #κ`, `χ₁ = -log |a|` and `χ₂ = -log |b|`. The
declarations about `T` live in `BoxLike.Rapaport.IsHomDiag`, outside the namespace of the library
predicate `System.IsHomDiag`, and take `hT : T.IsHomDiag a b` as their first explicit argument.

* `IsHomDiag.toHomSystem`: `T` as a `HomSystem` with the equal weights `1 / #κ`; its fields,
  `toHomSystem_H`, `toHomSystem_χ₁`, `toHomSystem_χ₂`, and `IsHomDiag.φ_eq`: its maps are the
  maps `φ_k` of `T`.
* `IsHomDiag.isInvariant_map_proj`, `IsHomDiag.bddSupp_map_proj`: `μ` is the self-affine measure
  of the homogeneous system and has bounded support.
* `IsHomDiag.gWord_axisWord_zero_eq_point`, `IsHomDiag.gWord_axisWord_one_eq_point`: the
  coordinates of `φ_u(0)` are the induced maps `g_u(0)` on the two axes.
* `IsHomDiag.xSep_of_axisExpSeparation`: exponential separation of the first axis is Rapaport's
  `XSep`.
* `IsHomDiag.simWord_eq_gWord`, `IsHomDiag.simWord_injective_of_axisExpSeparation`: exponential
  separation of an axis excludes exact overlaps of the coordinate maps, the hypotheses `hfreex`
  and `hfreey` of Kittle–Kogler.
* `IsHomDiag.isExactDim_map_fst`, `IsHomDiag.isExactDim_map_snd`: the coordinate projections of
  `μ` have dimension `1` when `χ_j ≤ H`.
* `IsHomDiag.isExactDim_map_proj_eq`, `IsHomDiag.condEntropyPoint_nonneg`,
  `IsHomDiag.condEntropyPoint_le`, `IsHomDiag.dim_le`: the Ledrappier–Young value
  `dim μ = 1 + (H - χ₁ - q) / χ₂` with `0 ≤ q ≤ H - χ₁`, so `dim μ ≤ 1 + (H - χ₁) / χ₂`.
* `min_two_lyapDim_eq`: `min{2, dim_L} = min{2, 1 + (H - χ₁) / χ₂}` when `H > χ₂`.
* `IsHomDiag.dimH_attractor_eq`: `dim_H X = min{2, dimaff(X)}` from `HomogeneousCore`,
  `FengLedrappierYoung` and `KittleKoglerDimension`; `IsHomDiag.dimH_attractor_eq_of_library`
  with the library proofs of the last two.
* `rapaportDiagonalDimension_homogeneous`: the same in the form that the proof of
  `System.dimH_subsystem_attractor_eq` uses, for alphabets without a measurable structure.
-/
public import BoxLike.Rapaport.Defs
public import BoxLike.AffinityMain
public import BoxLike.AxisSeparation
public import BoxLike.FalconerBound
public import BoxLike.FengLedrappierYoung
public import BoxLike.KittleKogler
public import BoxLike.LocalDimBounds
public import BoxLike.MainTwoProse.Endpoint
public import BoxLike.MainTwoProse.HomogeneousAffinity
public import BoxLike.ProjExpNoOverlaps

@[expose] public section

namespace BoxLike.Rapaport

open MeasureTheory Filter Set

universe u

/-! ### The Lyapunov dimension above the vertical exponent -/

/-- The case `H > χ₂` of `eq:diml_min2`: `min{2, dim_L(H, l₁, l₂)} = min{2, 1 + (H - χ₁) / χ₂}`
for `l₂ < l₁ < 0`, `χ_j = -l_j` and `H > χ₂`, the value of Rapaport's core theorem (lines 1900
to 1928 of the source). The first branch of `lyapDim` is excluded; in the third both sides are at
least `2`. -/
theorem min_two_lyapDim_eq {H l₁ l₂ : ℝ} (hl : l₂ < l₁) (hl₁ : l₁ < 0) (hH : -l₂ < H) :
    min 2 (lyapDim H l₁ l₂) = min 2 (1 + (H - -l₁) / -l₂) := by
  have hl₂ : l₂ < 0 := hl.trans hl₁
  unfold lyapDim
  rw [ite_eq_right (not_le.2 (show -l₁ < H by linarith))]
  split_ifs with h
  · congr 1
    rw [div_neg, sub_neg_eq_add]
    ring
  · replace h := not_le.1 h
    have h1 : 2 ≤ -(2 * H) / (l₁ + l₂) := by
      rw [le_div_iff_of_neg (by linarith)]
      linarith
    have h2 : 1 ≤ (H - -l₁) / -l₂ := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    rw [min_eq_left h1, min_eq_left (by linarith)]

namespace IsHomDiag

/-! ### The homogeneous system of a homogeneous diagonal system -/

section Hom

variable {κ : Type u} [Fintype κ] [Nonempty κ] {T : System κ} {a b : ℝ}
  (hT : T.IsHomDiag a b) (hab : |b| < |a|)
include hT

/-- The homogeneous diagonal system `T` with `|b| < |a|` as a `HomSystem`: the common linear
part `diag(a, b)`, the translations `v_k` of `T` and the equal weights `1 / #κ` of the Bernoulli
measure `ν_n` of the proof of `thm:main2`. -/
noncomputable def toHomSystem : HomSystem κ where
  r₁ := a
  r₂ := b
  v := T.v
  p := fun _ => 1 / Fintype.card κ
  r₂_ne_zero := hT.b_ne_zero
  abs_r₂_lt := hab
  abs_r₁_lt_one := hT.abs_a_lt_one
  p_pos := fun _ => by
    have : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.2 Fintype.card_pos
    positivity
  p_sum := sum_uniform_weight

/-- The horizontal contraction of `toHomSystem` is `a`. -/
@[simp] theorem toHomSystem_r₁ : (toHomSystem hT hab).r₁ = a := rfl

/-- The vertical contraction of `toHomSystem` is `b`. -/
@[simp] theorem toHomSystem_r₂ : (toHomSystem hT hab).r₂ = b := rfl

/-- The translations of `toHomSystem` are those of `T`. -/
@[simp] theorem toHomSystem_v : (toHomSystem hT hab).v = T.v := rfl

/-- The weights of `toHomSystem` are `1 / #κ`. -/
@[simp] theorem toHomSystem_p (k : κ) : (toHomSystem hT hab).p k = 1 / Fintype.card κ := rfl

/-- The entropy of the equal weights is `H = log #κ`, the entropy `log #W_n` of `ν_n` in the
proof of `thm:main2`. -/
theorem toHomSystem_H : (toHomSystem hT hab).H = Real.log (Fintype.card κ) := by
  simp only [HomSystem.H, toHomSystem_p]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.negMulLog, one_div, Real.log_inv]
  field_simp

/-- The first exponent of `toHomSystem` is `χ₁ = -log |a|`. -/
theorem toHomSystem_χ₁ : (toHomSystem hT hab).χ₁ = -Real.log |a| := rfl

/-- The second exponent of `toHomSystem` is `χ₂ = -log |b|`. -/
theorem toHomSystem_χ₂ : (toHomSystem hT hab).χ₂ = -Real.log |b| := rfl

/-- The maps of `toHomSystem` are the maps `φ_k` of `T`: `eq:phi_def_by_g` for a diagonal
generator, `φ_k(x, y) = (a x + v_k^{(1)}, b y + v_k^{(2)})`. -/
theorem φ_eq (k : κ) : (toHomSystem hT hab).φ k = T.phi k := by
  funext z
  rw [T.phi_of_o_eq_zero (hT.o_eq k)]
  ext <;> simp [HomSystem.φ, HomSystem.A, diagMap, System.g, hT.ratio_eq, System.trans]

/-! ### The points `φ_u(0)` and the induced maps on the axes -/

/-- The first coordinate of `φ_u(z)` is `g_u(z_1)` for the induced map `g_u` on the first axis
(`thm:rapaport`, the induced systems `Φ_1`), for every word `u` of length `n`. -/
theorem gWord_axisWord_zero_eq_φWord {n : ℕ} (u : Fin n → κ) (z : ℝ × ℝ) :
    T.gWord (axisWord 0 (List.ofFn u)) z.1 = ((toHomSystem hT hab).φWord n u z).1 := by
  induction n with
  | zero => simp [HomSystem.φWord]
  | succ n ih =>
    rw [List.ofFn_succ, axisWord_cons, System.gWord_cons, Function.comp_apply, ih]
    change _ = ((toHomSystem hT hab).φ (u 0) _).1
    rw [φ_eq, T.phi_of_o_eq_zero (hT.o_eq _)]

/-- The second coordinate of `φ_u(z)` is `g_u(z_2)` for the induced map `g_u` on the second
axis (`thm:rapaport`, the induced systems `Φ_2`). -/
theorem gWord_axisWord_one_eq_φWord {n : ℕ} (u : Fin n → κ) (z : ℝ × ℝ) :
    T.gWord (axisWord 1 (List.ofFn u)) z.2 = ((toHomSystem hT hab).φWord n u z).2 := by
  induction n with
  | zero => simp [HomSystem.φWord]
  | succ n ih =>
    rw [List.ofFn_succ, axisWord_cons, System.gWord_cons, Function.comp_apply, ih]
    change _ = ((toHomSystem hT hab).φ (u 0) _).2
    rw [φ_eq, T.phi_of_o_eq_zero (hT.o_eq _)]

/-- The first coordinate of Rapaport's point `φ_u(0)` is `g_u(0)` for the induced map on the
first axis (Section 6.3 of the source, lines 1902 to 1908). -/
theorem gWord_axisWord_zero_eq_point {n : ℕ} (u : Fin n → κ) :
    T.gWord (axisWord 0 (List.ofFn u)) 0 = ((toHomSystem hT hab).point u).1 :=
  gWord_axisWord_zero_eq_φWord hT hab u 0

/-- The second coordinate of Rapaport's point `φ_u(0)` is `g_u(0)` for the induced map on the
second axis. -/
theorem gWord_axisWord_one_eq_point {n : ℕ} (u : Fin n → κ) :
    T.gWord (axisWord 1 (List.ofFn u)) 0 = ((toHomSystem hT hab).point u).2 :=
  gWord_axisWord_one_eq_φWord hT hab u 0

omit [Fintype κ] [Nonempty κ] in
/-- The induced map of a planar word on the first axis has the derivative `a^n`: all words of
one length have equal derivatives, so the gap `axisGap 0 n` runs over all distinct pairs. -/
theorem gDeriv_axisWord_zero_eq (w : List κ) : T.gDeriv (axisWord 0 w) = a ^ w.length := by
  rw [T.gDeriv_axisWord_zero]
  induction w with
  | nil => simp
  | cons k w ih => rw [List.map_cons, List.prod_cons, ih, hT.a_eq, List.length_cons, pow_succ']

/-- Exponential separation of the system induced on the first axis (`thm:rapaport`) is
Rapaport's `XSep` for `toHomSystem` (Definition 1.1 of the source): the gap `axisGap 0 n` is the
infimum over distinct words of length `n`, all of which have the derivative `a^n`, and the words
`Fin n → κ` are the lists of length `n`. -/
theorem xSep_of_axisExpSeparation (h0 : T.AxisExpSeparation 0) : (toHomSystem hT hab).XSep := by
  obtain ⟨r, hr, hfr⟩ := (T.axisExpSeparation_iff_frequently 0).1 h0
  refine ⟨r, hr, hfr.mono fun n hn u u' huu' => ?_⟩
  have hne : List.ofFn u ≠ List.ofFn u' := fun h => huu' (List.ofFn_injective h)
  have hd : T.gDeriv (axisWord 0 (List.ofFn u)) = T.gDeriv (axisWord 0 (List.ofFn u')) := by
    rw [gDeriv_axisWord_zero_eq hT, gDeriv_axisWord_zero_eq hT, List.length_ofFn,
      List.length_ofFn]
  have hle := hn.trans (T.axisGap_le List.length_ofFn List.length_ofFn hne hd)
  rw [gWord_axisWord_zero_eq_point hT hab, gWord_axisWord_zero_eq_point hT hab] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)).1 hle

omit [Fintype κ] [Nonempty κ] in
/-- The coordinate maps `x ↦ a x + v_k^{(1)}` (for `c = 0`) and `y ↦ b y + v_k^{(2)}` (for
`c = 1`) of the homogeneous diagonal system compose to the induced maps `g_u` on the axis `c`
(`thm:rapaport`, the induced systems `Φ_c`). -/
theorem simWord_eq_gWord (c : ZMod 2) (u : List κ) :
    simWord (fun _ : κ => if c = 0 then a else b) (fun k => T.trans (k, c)) u =
      T.gWord (axisWord c u) := by
  induction u with
  | nil => rfl
  | cons j u ih =>
    rw [simWord_cons, ih, axisWord_cons, System.gWord_cons]
    funext x
    simp only [Function.comp_apply, System.g, hT.ratio_eq]

omit [Fintype κ] in
/-- Exponential separation of the system induced on the axis `c` excludes exact overlaps of its
maps, the hypotheses `hfreex` and `hfreey` of Kittle–Kogler in the library; the argument of
`ProjExpSeparation.noExactOverlaps` (tex lines 1298 to 1304): if `g_u = g_{u'}` for distinct
words, then `u u' ≠ u' u` are distinct words of length `|u| + |u'|` with equal maps, so the gap
vanishes from this length on, since it is non-increasing. -/
theorem simWord_injective_of_axisExpSeparation (c : ZMod 2) (h : T.AxisExpSeparation c) :
    Function.Injective
      (simWord (fun _ : κ => if c = 0 then a else b) (fun k => T.trans (k, c))) := by
  intro u u' huu'
  by_contra hne
  rw [simWord_eq_gWord hT, simWord_eq_gWord hT] at huu'
  have hne' : axisWord c u ≠ axisWord c u' := fun h => hne (axisWord_injective c h)
  have happ := T.append_ne_append_of_gWord_eq hne' huu'
  rw [← axisWord_append, ← axisWord_append] at happ
  have hm : T.axisGap c (u.length + u'.length) = 0 := by
    refine le_antisymm ?_ bot_le
    have hle := T.axisGap_le (c := c) (n := u.length + u'.length) (u := u ++ u') (u' := u' ++ u)
      (by simp) (by simp [add_comm]) (fun h => happ (by rw [h]))
      (by rw [axisWord_append, axisWord_append, System.gDeriv_append, System.gDeriv_append,
        mul_comm])
    rwa [axisWord_append, axisWord_append, System.gWord_append, System.gWord_append,
      Function.comp_apply, Function.comp_apply, huu', sub_self, abs_zero,
      ENNReal.ofReal_zero] at hle
  obtain ⟨r, hr, n, hn, hsep⟩ := h
  have h1 := hsep (u.length + u'.length)
  have h2 : T.axisGap c (n (u.length + u'.length)) ≤ T.axisGap c (u.length + u'.length) :=
    T.axisGap_anti c (hn.id_le _)
  rw [hm, nonpos_iff_eq_zero] at h2
  rw [h2] at h1
  exact (ENNReal.ofReal_pos.2 (pow_pos hr _)).not_ge h1

omit [Fintype κ] in
/-- `hfreex`: the maps `x ↦ a x + v_k^{(1)}` generate a free semigroup under exponential
separation of the first axis. -/
theorem simWord_injective_zero (h0 : T.AxisExpSeparation 0) :
    Function.Injective (simWord (fun _ : κ => a) (fun k => T.trans (k, 0))) := by
  simpa using simWord_injective_of_axisExpSeparation hT 0 h0

omit [Fintype κ] in
/-- `hfreey`: the maps `y ↦ b y + v_k^{(2)}` generate a free semigroup under exponential
separation of the second axis. -/
theorem simWord_injective_one (h1 : T.AxisExpSeparation 1) :
    Function.Injective (simWord (fun _ : κ => b) (fun k => T.trans (k, 1))) := by
  have h := simWord_injective_of_axisExpSeparation hT 1 h1
  simp only [one_ne_zero, ite_false] at h
  exact h

end Hom

/-! ### The projected Bernoulli measure -/

section Measure

variable {κ : Type u} [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ] [Nonempty κ]
  {T : System κ} {a b : ℝ}

omit [Nonempty κ] in
/-- `μ = π_*ν` has bounded support: it is carried by the compact attractor `X = π(Σ)`. -/
theorem bddSupp_map_proj : BddSupp ((uniformBernoulli κ).map T.proj) := by
  obtain ⟨r, M, hS⟩ := T.exists_bounds
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ × ℝ)).1 T.isCompact_attractor.isBounded
  refine ⟨0, R, ?_⟩
  refine (ae_map_mem_range T.isCompact_attractor.isClosed.measurableSet
    hS.measurable_proj.aemeasurable).mono fun z hz => ?_
  have := hR hz
  rwa [Metric.mem_closedBall, dist_eq_norm] at this

omit [MeasurableSingletonClass κ] [Nonempty κ] in
/-- The horizontal projection of `μ` is the marginal `ν_x` of `sec:dimension_of_projections`. -/
theorem map_fst_eq_marginal :
    ((uniformBernoulli κ).map T.proj).map Prod.fst = T.marginal 0 (uniformBernoulli κ) := rfl

omit [MeasurableSingletonClass κ] [Nonempty κ] in
/-- The vertical projection of `μ` is the marginal `ν_y` of `sec:dimension_of_projections`. -/
theorem map_snd_eq_marginal :
    ((uniformBernoulli κ).map T.proj).map Prod.snd = T.marginal 1 (uniformBernoulli κ) := rfl

/-- `q_n ≥ 0`: the conditional entropy of the first symbol given the planar point is
non-negative. -/
theorem condEntropyPoint_nonneg : 0 ≤ T.condEntropyPoint (uniformBernoulli κ) :=
  condEntropy_nonneg _ _

variable (hT : T.IsHomDiag a b)
include hT

/-- `μ = π_*ν` is the self-affine measure of `toHomSystem`: Hutchinson's equation
`μ = ∑_k (1 / #κ) (φ_k)_*μ`, from the invariance of the projection of a Bernoulli measure. -/
theorem isInvariant_map_proj (hab : |b| < |a|) :
    (toHomSystem hT hab).IsInvariant ((uniformBernoulli κ).map T.proj) := by
  have hinv := T.isInvariantMeasure_map_proj (measurePreserving_shift_uniformBernoulli 1)
    fun n w => measureReal_uniformBernoulli_cylinder_prod w
  unfold System.IsInvariantMeasure at hinv
  refine hinv.trans (Finset.sum_congr rfl fun k _ => ?_)
  dsimp only
  rw [uniformBernoulli_cylinder_single, φ_eq]
  rfl

/-- The horizontal projection of `μ` has dimension `min{1, H / χ₁} = 1` when `χ₁ ≤ H`
(Kittle–Kogler through `IsHomDiag.marginal_isExactDim`), a hypothesis of the core theorem.
Depends on: `KittleKoglerDimension`. -/
theorem isExactDim_map_fst (hkk : KittleKoglerDimension.{u}) (h0 : T.AxisExpSeparation 0)
    (hH : -Real.log |a| ≤ Real.log (Fintype.card κ)) :
    IsExactDim (((uniformBernoulli κ).map T.proj).map Prod.fst) 1 := by
  have hχ : 0 < -Real.log |a| := neg_pos.2 hT.log_abs_a_neg
  have h := hT.marginal_isExactDim hkk 0 (simWord_injective_of_axisExpSeparation hT 0 h0)
  simp only [ite_true] at h
  rwa [min_eq_left ((one_le_div hχ).2 hH)] at h

/-- The vertical projection of `μ` has dimension `min{1, H / χ₂} = 1` when `χ₂ ≤ H`
(Kittle–Kogler through `IsHomDiag.marginal_isExactDim`), a hypothesis of the core theorem.
Depends on: `KittleKoglerDimension`. -/
theorem isExactDim_map_snd (hkk : KittleKoglerDimension.{u}) (h1 : T.AxisExpSeparation 1)
    (hH : -Real.log |b| ≤ Real.log (Fintype.card κ)) :
    IsExactDim (((uniformBernoulli κ).map T.proj).map Prod.snd) 1 := by
  have hχ : 0 < -Real.log |b| := neg_pos.2 hT.log_abs_b_neg
  have h := hT.marginal_isExactDim hkk 1 (simWord_injective_of_axisExpSeparation hT 1 h1)
  simp only [one_ne_zero, ite_false] at h
  rwa [min_eq_left ((one_le_div hχ).2 hH)] at h

/-! ### The Ledrappier–Young value -/

/-- The planar Ledrappier–Young formula `thm:feng1` for `ν_n` when `χ₁ ≤ H`, along the proof of
`IsHomDiag.isExactDim_map_proj` without the vanishing of `q_n`: with `h_0 = H`,
`h_1 = q_{x,n} = H - χ₁` (the scalar formula with `d_{x,n} = 1`) and `h_2 = q_n`,
`dim μ = 1 + (H - χ₁ - q_n) / χ₂`.
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem isExactDim_map_proj_eq (hly : FengLedrappierYoung.{u}) (hkk : KittleKoglerDimension.{u})
    (hab : |b| < |a|)
    (hfreex : Function.Injective (simWord (fun _ : κ => a) (fun k => T.trans (k, 0))))
    (hH : -Real.log |a| ≤ Real.log (Fintype.card κ)) :
    IsExactDim ((uniformBernoulli κ).map T.proj)
      (1 + (Real.log (Fintype.card κ) - -Real.log |a| - T.condEntropyPoint (uniformBernoulli κ))
        / -Real.log |b|) := by
  have hinv := measurePreserving_shift_uniformBernoulli (κ := κ) 1
  have hχ : 0 < -Real.log |a| := neg_pos.2 hT.log_abs_a_neg
  have hla := hT.log_abs_a_neg.ne
  have hlb := hT.log_abs_b_neg.ne
  have hLY := hly T (uniformBernoulli κ) hinv ergodic_shift_uniformBernoulli
    (hT.lyapunov₂_lt_lyapunov₁ hab hinv)
  rw [hT.dimEntropy_zero hab.le, hT.dimEntropy_one_eq_condEntropyCoord hab.le,
    hT.dimEntropy_two_eq_condEntropyPoint hab.le,
    hT.condEntropyCoord_zero_eq_scalar hly hkk hab.le hfreex, hT.lyapunov₁_eq hab.le hinv,
    hT.lyapunov₂_eq hab.le hinv, min_eq_left ((one_le_div hχ).2 hH)] at hLY
  convert hLY using 1
  field_simp
  ring

/-- `q_n ≤ q_{x,n} = H - χ₁` when `χ₁ ≤ H`: conditioning on the
planar point gives at least as much information as conditioning on its first coordinate, and
the scalar Ledrappier–Young formula with `d_{x,n} = 1`.
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem condEntropyPoint_le (hly : FengLedrappierYoung.{u}) (hkk : KittleKoglerDimension.{u})
    (hab : |b| < |a|)
    (hfreex : Function.Injective (simWord (fun _ : κ => a) (fun k => T.trans (k, 0))))
    (hH : -Real.log |a| ≤ Real.log (Fintype.card κ)) :
    T.condEntropyPoint (uniformBernoulli κ) ≤ Real.log (Fintype.card κ) - -Real.log |a| := by
  have hχ : 0 < -Real.log |a| := neg_pos.2 hT.log_abs_a_neg
  have h := T.condEntropyPoint_le_condEntropyCoord (uniformBernoulli κ) 0
  rwa [hT.condEntropyCoord_zero_eq_scalar hly hkk hab.le hfreex,
    min_eq_left ((one_le_div hχ).2 hH), mul_one] at h

/-- The exact dimension `α` of `μ` satisfies `α ≤ 1 + (H - χ₁) / χ₂` when `χ₁ ≤ H`
since `q_n ≥ 0`.
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem dim_le (hly : FengLedrappierYoung.{u}) (hkk : KittleKoglerDimension.{u})
    (hab : |b| < |a|)
    (hfreex : Function.Injective (simWord (fun _ : κ => a) (fun k => T.trans (k, 0))))
    (hH : -Real.log |a| ≤ Real.log (Fintype.card κ)) {α : ℝ}
    (hα : IsExactDim ((uniformBernoulli κ).map T.proj) α) :
    α ≤ 1 + (Real.log (Fintype.card κ) - -Real.log |a|) / -Real.log |b| := by
  have hχ₂ : 0 < -Real.log |b| := neg_pos.2 hT.log_abs_b_neg
  rw [hα.unique (IsProbabilityMeasure.ne_zero _)
    (isExactDim_map_proj_eq hT hly hkk hab hfreex hH)]
  have hq : 0 ≤ T.condEntropyPoint (uniformBernoulli κ) := condEntropyPoint_nonneg
  have := div_le_div_of_nonneg_right
    (show Real.log (Fintype.card κ) - -Real.log |a| - T.condEntropyPoint (uniformBernoulli κ) ≤
      Real.log (Fintype.card κ) - -Real.log |a| by linarith) hχ₂.le
  linarith

end Measure

/-! ### The dimension of the attractor -/

section Attractor

variable {κ : Type u} [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ] [Nonempty κ]
  {T : System κ} {a b : ℝ}

/-- Rapaport's theorem `thm:rapaport` for a homogeneous diagonal system with `|b| < |a|` and
exponentially separated induced systems on both axes: `dim_H X = min{2, dimaff(X)}`, assuming
the core theorem. For `H ≤ χ₂` the library gives
`dim μ = dim_L(H, log |a|, log |b|)` (`IsHomDiag.isExactDim_map_proj`). For `H > χ₂` both
projections of `μ` have dimension `1`, `dim μ = α ≤ 1 + (H - χ₁) / χ₂`, and the core theorem
gives `α = 1 + (H - χ₁) / χ₂` unless `α = 2`; in both cases `α = min{2, dim_L}`. The lower bound
is `dim μ ≤ dim_H X`, the upper bound `eq:hausdorff_affinity_upper_bound`, and `dimaff(X)` is
`dim_L(H, log |a|, log |b|)` (`IsHomDiag.dimaff_eq`).
Depends on: `HomogeneousCore`, `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem dimH_attractor_eq (hcore : HomogeneousCore.{u}) (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (hT : T.IsHomDiag a b) (hab : |b| < |a|)
    (h0 : T.AxisExpSeparation 0) (h1 : T.AxisExpSeparation 1) :
    dimH T.attractor = ENNReal.ofReal (min 2 T.dimaff) := by
  have hne : (uniformBernoulli κ).map T.proj ≠ 0 := IsProbabilityMeasure.ne_zero _
  have hfreex := simWord_injective_zero hT h0
  have hfreey := simWord_injective_one hT h1
  have hla := hT.log_abs_a_neg
  have hlt : Real.log |b| < Real.log |a| := Real.log_lt_log (abs_pos.2 hT.b_ne_zero) hab
  obtain ⟨d, hd, hdeq⟩ : ∃ d, IsExactDim ((uniformBernoulli κ).map T.proj) d ∧
      d = min 2 T.dimaff := by
    rw [hT.dimaff_eq hab.le]
    rcases le_or_gt (Real.log (Fintype.card κ)) (-Real.log |b|) with hH | hH
    · -- `H ≤ χ₂`: the library
      have hH2 : Real.log (Fintype.card κ) ≤ -Real.log |a| - Real.log |b| := by linarith
      have hd := hT.isExactDim_map_proj hly hkk hab hfreex hfreey (Or.inl hH)
      rw [subsystemDim_eq_lyapDim hlt hla hH2] at hd
      exact ⟨_, hd, (min_eq_right (hd.dim_mem_Icc_two hne).2).symm⟩
    · -- `H > χ₂`: the core theorem
      have hH1 : -Real.log |a| ≤ Real.log (Fintype.card κ) := by linarith
      have hα := isExactDim_map_proj_eq hT hly hkk hab hfreex hH1
      refine ⟨_, hα, ?_⟩
      rw [min_two_lyapDim_eq hlt hla hH]
      have hα2 := (hα.dim_mem_Icc_two hne).2
      have hβ := dim_le hT hly hkk hab hfreex hH1 hα
      rcases hα2.lt_or_eq with hlt2 | heq2
      · have key := hcore (toHomSystem hT hab) _ (isInvariant_map_proj hT hab)
          (bddSupp_map_proj (T := T)) _ hα hlt2 (isExactDim_map_fst hT hkk h0 hH1)
          (isExactDim_map_snd hT hkk h1 hH.le) (xSep_of_axisExpSeparation hT hab h0)
        rw [toHomSystem_H, toHomSystem_χ₁, toHomSystem_χ₂] at key
        rw [← key, min_eq_right hlt2.le]
      · rw [heq2] at hβ ⊢
        rw [min_eq_left hβ]
  refine le_antisymm T.dimH_attractor_le ?_
  rw [← hdeq]
  exact T.le_dimH_attractor hd

/-- `dimH_attractor_eq` with the library proofs `fengLedrappierYoung_holds` and
`kittleKoglerDimension_holds` of `FengLedrappierYoung` and `KittleKoglerDimension`: only the
core theorem remains.
Depends on: `HomogeneousCore`. -/
theorem dimH_attractor_eq_of_library (hcore : HomogeneousCore.{u}) (hT : T.IsHomDiag a b)
    (hab : |b| < |a|) (h0 : T.AxisExpSeparation 0) (h1 : T.AxisExpSeparation 1) :
    dimH T.attractor = ENNReal.ofReal (min 2 T.dimaff) :=
  dimH_attractor_eq hcore fengLedrappierYoung_holds kittleKoglerDimension_holds hT hab h0 h1

end Attractor

end IsHomDiag

/-- Rapaport's theorem `thm:rapaport` for homogeneous diagonal systems with `|b| < |a|`, in the
form the proof of `System.dimH_subsystem_attractor_eq` uses it: the alphabet
carries no measurable structure, and the discrete one is chosen for the Bernoulli measure.
Depends on: `HomogeneousCore`. -/
theorem rapaportDiagonalDimension_homogeneous (hcore : HomogeneousCore.{u}) :
    ∀ {κ : Type u} [Fintype κ] [Nonempty κ] (T : System κ) {a b : ℝ}, T.IsHomDiag a b →
      |b| < |a| → T.AxisExpSeparation 0 → T.AxisExpSeparation 1 →
      dimH T.attractor = ENNReal.ofReal (min 2 T.dimaff) := by
  intro κ _ _ T a b hT hab h0 h1
  let _ : MeasurableSpace κ := ⊤
  have : MeasurableSingletonClass κ := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  exact IsHomDiag.dimH_attractor_eq_of_library hcore hT hab h0 h1

end BoxLike.Rapaport
