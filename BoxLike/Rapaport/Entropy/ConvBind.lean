module

/-
Convolution as a mixture of translates and the concavity of entropy under continuous mixtures,
for the proof of Rapaport's theorem (arXiv:2309.03985). The mixture `σ ∗ τ = ∫ σ.map (· + y) dτ`
is Mathlib's `Measure.bind`; concavity of `H(·, 𝒟)` and `H(·, 𝒟 ∣ ℰ)` under it is the continuous
form of the left inequality of Rapaport (2.4) (lines 719 to 723 of the source), used in
Section 3 for the lower bound `H(σ ∗ τ, 𝒟) ≥ H(σ, 𝒟) - O(1)` (proof of Proposition 1.7,
lines 1075 to 1188). The consequences for convolutions are in `Rapaport/Entropy/Conv.lean`.

* Mixtures of translates: `measurable_map_add_const`, `measurable_map_const_add`,
  `conv_eq_bind`, `conv_eq_bind_map_add_const`, `isProbabilityMeasure_bind`.
* Labellings with finitely many labels on every ball: `BallFinite`, `ballFinite_rect`,
  `BallFinite.comp_left`, `BallFinite.pair`, `BallFinite.comp_add_const`,
  `BallFinite.finiteLabels`, `ballFinite_hLabel`, `ballFinite_vLabel`, `Exps.ballFinite_E`,
  `Exps.ballFinite_E₁`, `Exps.ballFinite_E₂`, `Exps.ballFinite_Dsq`.
* Finite expressions: `cent_eq_sum_sum`, `ent_eq_cent_unit`, `measureReal_bind`.
* Jensen under `bind` (Rapaport (2.4), continuous form): `integrable_cent_bind_kernel`,
  `integral_cent_le_cent_bind`, `le_cent_bind_of_ae_le`, `integrable_ent_bind_kernel`,
  `integral_ent_le_ent_bind`, `le_ent_bind_of_ae_le`, and the forms
  `integral_cent_le_cent_bind_of_inBall`, `integral_ent_le_ent_bind_of_inBall`,
  `le_cent_bind_of_ae_le_of_inBall`, `le_ent_bind_of_ae_le_of_inBall` for kernels carried by a
  common ball.
-/
public import BoxLike.Rapaport.Entropy.Basic
public import BoxLike.Rapaport.Entropy.Rect
public import Mathlib.MeasureTheory.Measure.GiryMonad

@[expose] public section

namespace BoxLike.Rapaport

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ### Convolution as a mixture of translates -/

section Bind

/-- The translates `y ↦ σ.map (· + y)` of an s-finite planar measure form a measurable family,
the kernel of the mixture `σ ∗ τ = ∫ σ.map (· + y) dτ(y)`. -/
theorem measurable_map_add_const (σ : Measure (ℝ × ℝ)) [SFinite σ] :
    Measurable fun y : ℝ × ℝ => σ.map (· + y) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  convert measurable_measure_prodMk_right (μ := σ) (measurable_add hs) using 1
  funext y
  rw [Measure.map_apply (measurable_add_const y) hs]
  rfl

/-- The translates `x ↦ τ.map (x + ·)` of an s-finite planar measure form a measurable family. -/
theorem measurable_map_const_add (τ : Measure (ℝ × ℝ)) [SFinite τ] :
    Measurable fun x : ℝ × ℝ => τ.map (x + ·) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  convert measurable_measure_prodMk_left (ν := τ) (measurable_add hs) using 1
  funext x
  rw [Measure.map_apply (measurable_const_add x) hs]
  rfl

/-- Convolution is the mixture of the translates of `τ` by `σ`: `σ ∗ τ = ∫ τ.map (x + ·) dσ(x)`
(Mathlib's `Measure.prod` is a `bind`). -/
theorem conv_eq_bind (σ τ : Measure (ℝ × ℝ)) [SFinite σ] [SFinite τ] :
    σ ∗ τ = σ.bind fun x => τ.map (x + ·) := by
  ext s hs
  rw [Measure.conv, Measure.map_apply measurable_add hs, Measure.prod_apply (measurable_add hs),
    Measure.bind_apply hs (measurable_map_const_add τ).aemeasurable]
  refine lintegral_congr fun x => ?_
  rw [Measure.map_apply (measurable_const_add x) hs]
  rfl

/-- Convolution is the mixture of the translates of `σ` by `τ`: `σ ∗ τ = ∫ σ.map (· + y) dτ(y)`,
the form used for the lower bounds on `H(σ ∗ τ, 𝒟)`. -/
theorem conv_eq_bind_map_add_const (σ τ : Measure (ℝ × ℝ)) [SFinite σ] [SFinite τ] :
    σ ∗ τ = τ.bind fun y => σ.map (· + y) := by
  ext s hs
  rw [Measure.conv, Measure.map_apply measurable_add hs,
    Measure.prod_apply_symm (measurable_add hs),
    Measure.bind_apply hs (measurable_map_add_const σ).aemeasurable]
  refine lintegral_congr fun y => ?_
  rw [Measure.map_apply (measurable_add_const y) hs]
  rfl

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A mixture of probability measures by a probability measure is a probability measure. -/
theorem isProbabilityMeasure_bind {τ : Measure Y} [IsProbabilityMeasure τ] {κ : Y → Measure X}
    (hκ : Measurable κ) (hκ1 : ∀ y, IsProbabilityMeasure (κ y)) :
    IsProbabilityMeasure (τ.bind κ) := by
  constructor
  rw [Measure.bind_apply MeasurableSet.univ hκ.aemeasurable]
  simp only [measure_univ, lintegral_const, one_mul]

/-- The real mass of a measurable set under a mixture is the average of its masses. -/
theorem measureReal_bind {τ : Measure Y} {κ : Y → Measure X} (hκ : Measurable κ)
    (hκ1 : ∀ y, IsProbabilityMeasure (κ y)) {A : Set X} (hA : MeasurableSet A) :
    (τ.bind κ).real A = ∫ y, (κ y).real A ∂τ := by
  have h := integral_toReal (μ := τ) (f := fun y => κ y A)
    ((Measure.measurable_coe hA).comp hκ).aemeasurable (ae_of_all _ fun y => measure_lt_top _ _)
  rw [measureReal_def, Measure.bind_apply hA hκ.aemeasurable, ← h]
  rfl

end Bind

/-! ### Labellings with finitely many labels on every ball -/

section BallFinite

variable {L L' : Type*}

/-- Every closed ball meets only finitely many labels of `f`: the property shared by the
coarsenings `φ ∘ rect i j` of the dyadic rectangle partitions, which makes all entropies of
measures of bounded support finite sums. -/
def BallFinite (f : ℝ × ℝ → L) : Prop :=
  ∀ (c : ℝ × ℝ) (R : ℝ), (f '' Metric.closedBall c R).Finite

/-- The dyadic rectangle partitions meet finitely many cells on every ball. -/
theorem ballFinite_rect (i j : ℤ) : BallFinite (rect i j) :=
  rect_image_closedBall_finite i j

/-- A recoding of the labels keeps finiteness on balls. -/
theorem BallFinite.comp_left {f : ℝ × ℝ → L} (hf : BallFinite f) (φ : L → L') :
    BallFinite (φ ∘ f) := fun c R => by
  rw [Set.image_comp]
  exact (hf c R).image φ

/-- The join of two labellings finite on balls is finite on balls. -/
theorem BallFinite.pair {f : ℝ × ℝ → L} {g : ℝ × ℝ → L'} (hf : BallFinite f)
    (hg : BallFinite g) : BallFinite fun z => (f z, g z) := fun c R =>
  ((hf c R).prod (hg c R)).subset fun _ ⟨z, hz, he⟩ => he ▸ ⟨⟨z, hz, rfl⟩, ⟨z, hz, rfl⟩⟩

/-- A translate of a labelling finite on balls is finite on balls. -/
theorem BallFinite.comp_add_const {f : ℝ × ℝ → L} (hf : BallFinite f) (y : ℝ × ℝ) :
    BallFinite (f ∘ (· + y)) := fun c R => by
  refine (hf (c + y) R).subset ?_
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨z + y, ?_, rfl⟩
  rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
  rwa [add_sub_add_right_eq_sub]

/-- A labelling finite on balls has finitely many labels of positive mass under a measure of
bounded support. -/
theorem BallFinite.finiteLabels {f : ℝ × ℝ → L} (hf : BallFinite f) {θ : Measure (ℝ × ℝ)}
    (hθ : BddSupp θ) : FiniteLabels θ f := by
  obtain ⟨c, R, h⟩ := hθ
  exact finiteLabels_comp_of_ae_mem_closedBall (ψ := id) (hf c R) h.ae_mem_closedBall

/-- The horizontal labels are finite on balls. -/
theorem ballFinite_hLabel (i : ℤ) : BallFinite (hLabel i) :=
  (ballFinite_rect i i).comp_left Prod.fst

/-- The vertical labels are finite on balls. -/
theorem ballFinite_vLabel (j : ℤ) : BallFinite (vLabel j) :=
  (ballFinite_rect j j).comp_left Prod.snd

/-- The partitions `ℰ_n` are finite on balls. -/
theorem Exps.ballFinite_E (χ : Exps) (n : ℤ) : BallFinite (χ.E n) := ballFinite_rect _ _

/-- The partitions `π₁⁻¹ ℰ_n` are finite on balls. -/
theorem Exps.ballFinite_E₁ (χ : Exps) (n : ℤ) : BallFinite (χ.E₁ n) := ballFinite_hLabel _

/-- The partitions `π₂⁻¹ ℰ_n` are finite on balls. -/
theorem Exps.ballFinite_E₂ (χ : Exps) (n : ℤ) : BallFinite (χ.E₂ n) := ballFinite_vLabel _

/-- The partitions `𝒟²_{χ₂ n}` are finite on balls. -/
theorem Exps.ballFinite_Dsq (χ : Exps) (n : ℤ) : BallFinite (χ.Dsq n) := ballFinite_rect _ _

end BallFinite

/-! ### Entropies as finite sums -/

section FiniteSums

variable {X : Type*} [MeasurableSpace X]
variable {L L' : Type*} [MeasurableSpace L] [MeasurableSingletonClass L] [Countable L]
variable [MeasurableSpace L'] [MeasurableSingletonClass L'] [Countable L']

omit [Countable L'] in
/-- Conditional entropy as the finite double sum
`H(θ, f ∣ g) = ∑_c (∑_b η(θ(g = c, f = b)) - η(θ(g = c)))`, `η = negMulLog`, when the labels lie
almost surely in finsets (Rapaport, lines 663 to 668, with (2.3)). -/
theorem cent_eq_sum_sum {θ : Measure X} [IsFiniteMeasure θ] {f : X → L} {g : X → L'}
    (hf : Measurable f) (hg : Measurable g) (S : Finset L) (T : Finset L')
    (hS : ∀ᵐ x ∂θ, f x ∈ S) (hT : ∀ᵐ x ∂θ, g x ∈ T) :
    cent θ f g = ∑ c ∈ T, (∑ b ∈ S, Real.negMulLog (θ.real (g ⁻¹' {c} ∩ f ⁻¹' {b})) -
      Real.negMulLog (∑ b ∈ S, θ.real (g ⁻¹' {c} ∩ f ⁻¹' {b}))) := by
  have hST : ∀ᵐ x ∂θ, (f x, g x) ∈ S ×ˢ T := by
    filter_upwards [hS, hT] with x h1 h2
    exact Finset.mem_product.2 ⟨h1, h2⟩
  unfold cent
  rw [ent_eq_sum_of_subset (S ×ˢ T) (mem_of_ae_mem hST),
    ent_eq_sum_of_subset T (mem_of_ae_mem hT), Finset.sum_product_right,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [preimage_pair_singleton]
  rw [sum_measureReal_inter_fiber hf S (mem_of_ae_mem hS) (hg (measurableSet_singleton c))]

omit [MeasurableSpace L] [MeasurableSingletonClass L] [Countable L] [MeasurableSpace L']
  [MeasurableSingletonClass L'] [Countable L'] in
/-- Entropy is conditional entropy given the trivial partition. -/
theorem ent_eq_cent_unit {θ : Measure X} [IsProbabilityMeasure θ] (f : X → L) :
    ent θ f = cent θ f (fun _ => ()) := by
  have h1 : ent θ (fun x => (f x, ())) = ent θ f :=
    ent_eq_of_injective (φ := fun b => (b, ())) (fun _ _ h => (Prod.mk.inj h).1) rfl
  have h2 : ent θ (fun _ : X => ()) = 0 :=
    ent_eq_zero_of_ae_eq measurable_const () (ae_of_all _ fun _ => rfl)
  rw [cent, h1, h2, sub_zero]

end FiniteSums

/-! ### Jensen's inequality for entropy under mixtures -/

section Jensen

/-- Gibbs' inequality in the form behind the concavity of conditional entropy: for `p, P ≥ 0`
with `P b = 0 → p b = 0` and `∑ P ≤ Q`, the conditional term
`∑_b η(p_b) - η(∑_b p_b)` lies below the linear function `∑_b p_b (log Q - log P_b)`,
`η = negMulLog`. -/
private theorem sum_negMulLog_sub_le {ι : Type*} (s : Finset ι) {p P : ι → ℝ} {Q : ℝ}
    (hp : ∀ b ∈ s, 0 ≤ p b) (hP : ∀ b ∈ s, 0 ≤ P b) (hpP : ∀ b ∈ s, P b = 0 → p b = 0)
    (hQ : ∑ b ∈ s, P b ≤ Q) :
    ∑ b ∈ s, Real.negMulLog (p b) - Real.negMulLog (∑ b ∈ s, p b) ≤
      ∑ b ∈ s, p b * (Real.log Q - Real.log (P b)) := by
  set q := ∑ b ∈ s, p b with hq
  have hq0 : 0 ≤ q := Finset.sum_nonneg hp
  rcases hq0.eq_or_lt with hq0 | hqpos
  · have h0 : ∀ b ∈ s, p b = 0 := (Finset.sum_eq_zero_iff_of_nonneg hp).1 hq0.symm
    have e1 : ∑ b ∈ s, Real.negMulLog (p b) = 0 :=
      Finset.sum_eq_zero fun b hb => by rw [h0 b hb, Real.negMulLog_zero]
    have e2 : ∑ b ∈ s, p b * (Real.log Q - Real.log (P b)) = 0 :=
      Finset.sum_eq_zero fun b hb => by rw [h0 b hb, zero_mul]
    rw [e1, e2, ← hq0, Real.negMulLog_zero, sub_zero]
  obtain ⟨b₀, hb₀, hpb₀⟩ : ∃ b ∈ s, 0 < p b := by
    by_contra hcon
    push Not at hcon
    have : q ≤ 0 := Finset.sum_nonpos hcon
    linarith
  have hPb₀ : 0 < P b₀ :=
    lt_of_le_of_ne (hP b₀ hb₀) fun h => hpb₀.ne' (hpP b₀ hb₀ h.symm)
  have hQpos : 0 < Q := lt_of_lt_of_le hPb₀ ((Finset.single_le_sum hP hb₀).trans hQ)
  have key : ∀ b ∈ s, Real.negMulLog (p b) + p b * Real.log q -
      p b * (Real.log Q - Real.log (P b)) ≤ q * P b / Q - p b := by
    intro b hb
    rcases (hp b hb).eq_or_lt with h | h
    · rw [← h, Real.negMulLog_zero, zero_mul, zero_mul, sub_zero, add_zero, sub_zero]
      exact div_nonneg (mul_nonneg hq0 (hP b hb)) hQpos.le
    · have hPb : 0 < P b := lt_of_le_of_ne (hP b hb) fun h' => h.ne' (hpP b hb h'.symm)
      have hlog := Real.log_le_sub_one_of_pos (x := q * P b / (p b * Q)) (by positivity)
      rw [Real.log_div (by positivity) (by positivity), Real.log_mul hqpos.ne' hPb.ne',
        Real.log_mul h.ne' hQpos.ne'] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog h.le
      have he : p b * (q * P b / (p b * Q) - 1) = q * P b / Q - p b := by
        field_simp
      rw [he] at hmul
      unfold Real.negMulLog
      nlinarith
  have hsum := Finset.sum_le_sum key
  have hnq : Real.negMulLog q = -(∑ b ∈ s, p b * Real.log q) := by
    rw [← Finset.sum_mul, ← hq]
    unfold Real.negMulLog
    ring
  have hqP : ∑ b ∈ s, q * P b / Q ≤ q := by
    rw [← Finset.sum_div, ← Finset.mul_sum, div_le_iff₀ hQpos]
    exact mul_le_mul_of_nonneg_left hQ hq0
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  rw [hnq]
  linarith

variable {Y : Type*} [MeasurableSpace Y] {τ : Measure Y} [IsProbabilityMeasure τ]

/-- `negMulLog` of a measurable function with values in `[0, 1]` is integrable. -/
private theorem integrable_negMulLog_comp {u : Y → ℝ} (hu : Measurable u)
    (h0 : ∀ᵐ y ∂τ, 0 ≤ u y) (h1 : ∀ᵐ y ∂τ, u y ≤ 1) :
    Integrable (fun y => Real.negMulLog (u y)) τ := by
  refine Integrable.of_mem_Icc 0 1 (Real.continuous_negMulLog.measurable.comp hu).aemeasurable ?_
  filter_upwards [h0, h1] with y hy0 hy1
  exact ⟨Real.negMulLog_nonneg hy0 hy1,
    (Real.negMulLog_le_one_sub_self hy0).trans (by linarith)⟩

/-- A measurable function with values in `[0, 1]` is integrable. -/
private theorem integrable_of_unit {u : Y → ℝ} (hu : Measurable u) (h0 : ∀ y, 0 ≤ u y)
    (h1 : ∀ y, u y ≤ 1) : Integrable u τ :=
  Integrable.of_mem_Icc 0 1 hu.aemeasurable (ae_of_all _ fun y => ⟨h0 y, h1 y⟩)

/-- The conditional entropy functional `Φ(p) = ∑_c (∑_b η(p_{bc}) - η(∑_b p_{bc}))` of a family of
sub-probability vectors `p y` is integrable. -/
private theorem integrable_condFun {β γ : Type*} (S : Finset β) (T : Finset γ)
    (p : Y → β → γ → ℝ) (hpm : ∀ b c, Measurable fun y => p y b c) (hp0 : ∀ y b c, 0 ≤ p y b c)
    (hp1 : ∀ y b c, p y b c ≤ 1) (hq1 : ∀ᵐ y ∂τ, ∀ c ∈ T, ∑ b ∈ S, p y b c ≤ 1) :
    Integrable (fun y => ∑ c ∈ T, (∑ b ∈ S, Real.negMulLog (p y b c) -
      Real.negMulLog (∑ b ∈ S, p y b c))) τ := by
  refine integrable_finsetSum T fun c hc => ?_
  refine (integrable_finsetSum S fun b _ =>
    integrable_negMulLog_comp (hpm b c) (ae_of_all _ fun y => hp0 y b c)
      (ae_of_all _ fun y => hp1 y b c)).sub ?_
  refine integrable_negMulLog_comp (Finset.measurable_sum S fun b _ => hpm b c)
    (ae_of_all _ fun y => Finset.sum_nonneg fun b _ => hp0 y b c) ?_
  filter_upwards [hq1] with y hy using hy c hc

/-- Jensen's inequality for the conditional entropy functional
`Φ(p) = ∑_c (∑_b η(p_{bc}) - η(∑_b p_{bc}))`, which is concave on the nonnegative orthant:
`∫ Φ(p y) dτ ≤ Φ(∫ p y dτ)`. Proved through Gibbs' inequality, the supporting linear functions
of `Φ` at `∫ p y dτ`. -/
private theorem integral_condFun_le {β γ : Type*} (S : Finset β) (T : Finset γ)
    (p : Y → β → γ → ℝ) (hpm : ∀ b c, Measurable fun y => p y b c) (hp0 : ∀ y b c, 0 ≤ p y b c)
    (hp1 : ∀ y b c, p y b c ≤ 1) (hq1 : ∀ᵐ y ∂τ, ∀ c ∈ T, ∑ b ∈ S, p y b c ≤ 1) :
    ∫ y, ∑ c ∈ T, (∑ b ∈ S, Real.negMulLog (p y b c) - Real.negMulLog (∑ b ∈ S, p y b c)) ∂τ ≤
      ∑ c ∈ T, (∑ b ∈ S, Real.negMulLog (∫ y, p y b c ∂τ) -
        Real.negMulLog (∑ b ∈ S, ∫ y, p y b c ∂τ)) := by
  set P : β → γ → ℝ := fun b c => ∫ y, p y b c ∂τ with hPdef
  have hPi : ∀ b c, Integrable (fun y => p y b c) τ := fun b c =>
    integrable_of_unit (hpm b c) (fun y => hp0 y b c) fun y => hp1 y b c
  have hP0 : ∀ b c, 0 ≤ P b c := fun b c => integral_nonneg fun y => hp0 y b c
  have hzero : ∀ᵐ y ∂τ, ∀ b ∈ S, ∀ c ∈ T, P b c = 0 → p y b c = 0 := by
    rw [Filter.eventually_all_finset]
    intro b _
    rw [Filter.eventually_all_finset]
    intro c _
    by_cases h : P b c = 0
    · have h' := (integral_eq_zero_iff_of_nonneg (fun y => hp0 y b c) (hPi b c)).1 h
      filter_upwards [h'] with y hy using fun _ => hy
    · exact ae_of_all _ fun y h' => absurd h' h
  set R : Y → ℝ := fun y => ∑ c ∈ T, ∑ b ∈ S,
    p y b c * (Real.log (∑ b' ∈ S, P b' c) - Real.log (P b c)) with hRdef
  have hRi : Integrable R τ :=
    integrable_finsetSum T fun c _ => integrable_finsetSum S fun b _ => (hPi b c).mul_const _
  have hle : ∀ᵐ y ∂τ, (∑ c ∈ T, (∑ b ∈ S, Real.negMulLog (p y b c) -
      Real.negMulLog (∑ b ∈ S, p y b c))) ≤ R y := by
    filter_upwards [hzero] with y hy
    refine Finset.sum_le_sum fun c hc => ?_
    exact sum_negMulLog_sub_le S (fun b _ => hp0 y b c) (fun b _ => hP0 b c)
      (fun b hb => hy b hb c hc) le_rfl
  have hint := integral_mono_ae (integrable_condFun S T p hpm hp0 hp1 hq1) hRi hle
  have hR : ∫ y, R y ∂τ = ∑ c ∈ T, ∑ b ∈ S,
      P b c * (Real.log (∑ b' ∈ S, P b' c) - Real.log (P b c)) := by
    rw [hRdef, integral_finsetSum T fun c _ =>
      integrable_finsetSum S fun b _ => (hPi b c).mul_const _]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_finsetSum S fun b _ => (hPi b c).mul_const _]
    exact Finset.sum_congr rfl fun b _ => integral_mul_const _ _
  refine hint.trans (le_of_eq ?_)
  rw [hR]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e : ∀ b ∈ S, P b c * (Real.log (∑ b' ∈ S, P b' c) - Real.log (P b c)) =
      Real.negMulLog (P b c) + P b c * Real.log (∑ b' ∈ S, P b' c) := fun b _ => by
    unfold Real.negMulLog
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.sum_mul]
  unfold Real.negMulLog
  ring

variable {X : Type*} [MeasurableSpace X]
variable {L L' : Type*} [MeasurableSpace L] [MeasurableSingletonClass L] [Countable L]
variable [MeasurableSpace L'] [MeasurableSingletonClass L']
variable {κ : Y → Measure X}

omit [IsProbabilityMeasure τ] [Countable L] in
/-- The labels of a mixture lie almost surely in a finset that almost surely carries the labels of
the mixed measures. -/
private theorem ae_mem_bind (hκ : Measurable κ) {f : X → L} (hf : Measurable f) (S : Finset L)
    (hS : ∀ᵐ y ∂τ, ∀ᵐ x ∂κ y, f x ∈ S) : ∀ᵐ x ∂τ.bind κ, f x ∈ S := by
  have hm : MeasurableSet {x | f x ∈ S}ᶜ := (hf S.measurableSet).compl
  rw [ae_iff, ← Set.compl_ofPred, Measure.bind_apply hm hκ.aemeasurable]
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [hS] with y hy
  rw [ae_iff] at hy
  rwa [← Set.compl_ofPred] at hy

/-- The fibre masses `y ↦ κ_y(g = c, f = b)` of a measurable family. -/
private theorem measurable_measureReal_kernel (hκ : Measurable κ) {A : Set X}
    (hA : MeasurableSet A) : Measurable fun y => (κ y).real A :=
  ((Measure.measurable_coe hA).comp hκ).ennreal_toReal

/-- The conditional entropy of the measures of a probability kernel carried a.s. by finitely many
labels is integrable. -/
theorem integrable_cent_bind_kernel (hκ : Measurable κ) (hκ1 : ∀ y, IsProbabilityMeasure (κ y))
    {f : X → L} {g : X → L'} (hf : Measurable f) (hg : Measurable g) (S : Finset L)
    (T : Finset L') (hS : ∀ᵐ y ∂τ, ∀ᵐ x ∂κ y, f x ∈ S) (hT : ∀ᵐ y ∂τ, ∀ᵐ x ∂κ y, g x ∈ T) :
    Integrable (fun y => cent (κ y) f g) τ := by
  set p : Y → L → L' → ℝ := fun y b c => (κ y).real (g ⁻¹' {c} ∩ f ⁻¹' {b})
  have hpm : ∀ b c, Measurable fun y => p y b c := fun b c =>
    measurable_measureReal_kernel hκ
      ((hg (measurableSet_singleton c)).inter (hf (measurableSet_singleton b)))
  have hp1 : ∀ y b c, p y b c ≤ 1 := fun y b c => by
    have := hκ1 y
    exact measureReal_le_one
  have hq1 : ∀ᵐ y ∂τ, ∀ c ∈ T, ∑ b ∈ S, p y b c ≤ 1 := by
    filter_upwards [hS] with y hy c _
    have := hκ1 y
    rw [sum_measureReal_inter_fiber hf S (mem_of_ae_mem hy) (hg (measurableSet_singleton c))]
    exact measureReal_le_one
  refine (integrable_condFun S T p hpm (fun y b c => measureReal_nonneg) hp1 hq1).congr ?_
  filter_upwards [hS, hT] with y hSy hTy
  have := hκ1 y
  exact (cent_eq_sum_sum hf hg S T hSy hTy).symm

/-- Concavity of conditional entropy under mixtures, the continuous form of Rapaport (2.4) for
`H(·, 𝒟 ∣ ℰ)` (lines 719 to 723): for a measurable family of probability measures `κ y` whose
labels lie almost surely in finsets, `∫ H(κ_y, f ∣ g) dτ(y) ≤ H(∫ κ_y dτ(y), f ∣ g)`. -/
theorem integral_cent_le_cent_bind (hκ : Measurable κ) (hκ1 : ∀ y, IsProbabilityMeasure (κ y))
    {f : X → L} {g : X → L'} (hf : Measurable f) (hg : Measurable g) (S : Finset L)
    (T : Finset L') (hS : ∀ᵐ y ∂τ, ∀ᵐ x ∂κ y, f x ∈ S) (hT : ∀ᵐ y ∂τ, ∀ᵐ x ∂κ y, g x ∈ T) :
    ∫ y, cent (κ y) f g ∂τ ≤ cent (τ.bind κ) f g := by
  have := isProbabilityMeasure_bind (τ := τ) hκ hκ1
  set p : Y → L → L' → ℝ := fun y b c => (κ y).real (g ⁻¹' {c} ∩ f ⁻¹' {b}) with hpdef
  have hA : ∀ b c, MeasurableSet (g ⁻¹' {c} ∩ f ⁻¹' {b}) := fun b c =>
    (hg (measurableSet_singleton c)).inter (hf (measurableSet_singleton b))
  have hpm : ∀ b c, Measurable fun y => p y b c := fun b c =>
    measurable_measureReal_kernel hκ (hA b c)
  have hp1 : ∀ y b c, p y b c ≤ 1 := fun y b c => by
    have := hκ1 y
    exact measureReal_le_one
  have hq1 : ∀ᵐ y ∂τ, ∀ c ∈ T, ∑ b ∈ S, p y b c ≤ 1 := by
    filter_upwards [hS] with y hy c _
    have := hκ1 y
    rw [sum_measureReal_inter_fiber hf S (mem_of_ae_mem hy) (hg (measurableSet_singleton c))]
    exact measureReal_le_one
  have hcongr : ∫ y, cent (κ y) f g ∂τ = ∫ y, ∑ c ∈ T, (∑ b ∈ S, Real.negMulLog (p y b c) -
      Real.negMulLog (∑ b ∈ S, p y b c)) ∂τ := by
    refine integral_congr_ae ?_
    filter_upwards [hS, hT] with y hSy hTy
    have := hκ1 y
    exact cent_eq_sum_sum hf hg S T hSy hTy
  have hθ : cent (τ.bind κ) f g = ∑ c ∈ T, (∑ b ∈ S, Real.negMulLog (∫ y, p y b c ∂τ) -
      Real.negMulLog (∑ b ∈ S, ∫ y, p y b c ∂τ)) := by
    rw [cent_eq_sum_sum hf hg S T (ae_mem_bind hκ hf S hS) (ae_mem_bind hκ hg T hT)]
    simp only [hpdef, measureReal_bind hκ hκ1 (hA _ _)]
  rw [hcongr, hθ]
  exact integral_condFun_le S T p hpm (fun y b c => measureReal_nonneg) hp1 hq1

/-- A lower bound for the conditional entropies of almost every measure of the kernel is a lower
bound for the conditional entropy of the mixture (Rapaport (2.4), continuous form). -/
theorem le_cent_bind_of_ae_le (hκ : Measurable κ) (hκ1 : ∀ y, IsProbabilityMeasure (κ y))
    {f : X → L} {g : X → L'} (hf : Measurable f) (hg : Measurable g) (S : Finset L)
    (T : Finset L') (hS : ∀ᵐ y ∂τ, ∀ᵐ x ∂κ y, f x ∈ S) (hT : ∀ᵐ y ∂τ, ∀ᵐ x ∂κ y, g x ∈ T)
    {a : ℝ} (ha : ∀ᵐ y ∂τ, a ≤ cent (κ y) f g) : a ≤ cent (τ.bind κ) f g := by
  have h := integral_mono_ae (integrable_const a)
    (integrable_cent_bind_kernel hκ hκ1 hf hg S T hS hT) ha
  rw [integral_const, probReal_univ, one_smul] at h
  exact h.trans (integral_cent_le_cent_bind hκ hκ1 hf hg S T hS hT)

omit [MeasurableSpace L'] [MeasurableSingletonClass L'] in
/-- The entropies of the measures of a probability kernel carried a.s. by finitely many labels
form an integrable function. -/
theorem integrable_ent_bind_kernel (hκ : Measurable κ) (hκ1 : ∀ y, IsProbabilityMeasure (κ y))
    {f : X → L} (hf : Measurable f) (S : Finset L) (hS : ∀ᵐ y ∂τ, ∀ᵐ x ∂κ y, f x ∈ S) :
    Integrable (fun y => ent (κ y) f) τ := by
  have h := integrable_cent_bind_kernel hκ hκ1 hf measurable_const S {()} hS
    (ae_of_all _ fun y => ae_of_all _ fun x => Finset.mem_singleton_self ())
  refine h.congr (ae_of_all _ fun y => ?_)
  have := hκ1 y
  exact (ent_eq_cent_unit f).symm

omit [MeasurableSpace L'] [MeasurableSingletonClass L'] in
/-- Concavity of entropy under mixtures, the continuous form of the left inequality of
Rapaport (2.4) (line 719): `∫ H(κ_y, f) dτ(y) ≤ H(∫ κ_y dτ(y), f)` for a measurable family of
probability measures whose labels lie almost surely in a finset. -/
theorem integral_ent_le_ent_bind (hκ : Measurable κ) (hκ1 : ∀ y, IsProbabilityMeasure (κ y))
    {f : X → L} (hf : Measurable f) (S : Finset L) (hS : ∀ᵐ y ∂τ, ∀ᵐ x ∂κ y, f x ∈ S) :
    ∫ y, ent (κ y) f ∂τ ≤ ent (τ.bind κ) f := by
  have := isProbabilityMeasure_bind (τ := τ) hκ hκ1
  have h := integral_cent_le_cent_bind hκ hκ1 hf measurable_const S {()} hS
    (ae_of_all _ fun y => ae_of_all _ fun x => Finset.mem_singleton_self ())
  rw [ent_eq_cent_unit f]
  refine le_of_eq_of_le (integral_congr_ae (ae_of_all _ fun y => ?_)) h
  have := hκ1 y
  exact ent_eq_cent_unit f

omit [MeasurableSpace L'] [MeasurableSingletonClass L'] in
/-- A lower bound for the entropies of almost every measure of the kernel is a lower bound for
the entropy of the mixture (Rapaport (2.4), continuous form). -/
theorem le_ent_bind_of_ae_le (hκ : Measurable κ) (hκ1 : ∀ y, IsProbabilityMeasure (κ y))
    {f : X → L} (hf : Measurable f) (S : Finset L) (hS : ∀ᵐ y ∂τ, ∀ᵐ x ∂κ y, f x ∈ S) {a : ℝ}
    (ha : ∀ᵐ y ∂τ, a ≤ ent (κ y) f) : a ≤ ent (τ.bind κ) f := by
  have h := integral_mono_ae (integrable_const a) (integrable_ent_bind_kernel hκ hκ1 hf S hS) ha
  rw [integral_const, probReal_univ, one_smul] at h
  exact h.trans (integral_ent_le_ent_bind hκ hκ1 hf S hS)

end Jensen

/-! ### Kernels carried by a common ball -/

section Ball

variable {Y : Type*} [MeasurableSpace Y] {τ : Measure Y} [IsProbabilityMeasure τ]
variable {L L' : Type*} [MeasurableSpace L] [MeasurableSingletonClass L] [Countable L]
variable [MeasurableSpace L'] [MeasurableSingletonClass L']
variable {κ : Y → Measure (ℝ × ℝ)} {c : ℝ × ℝ} {R : ℝ}

omit [IsProbabilityMeasure τ] [MeasurableSpace L] [MeasurableSingletonClass L] [Countable L] in
/-- The labels finite on balls of measures carried by a common ball lie in a common finset. -/
private theorem ae_mem_toFinset_of_inBall {f : ℝ × ℝ → L} (hfb : BallFinite f)
    (hb : ∀ᵐ y ∂τ, InBall (κ y) c R) :
    ∀ᵐ y ∂τ, ∀ᵐ x ∂κ y, f x ∈ (hfb c R).toFinset := by
  filter_upwards [hb] with y hy
  filter_upwards [hy.ae_mem_closedBall] with x hx
  exact (Set.Finite.mem_toFinset _).2 ⟨x, hx, rfl⟩

/-- Concavity of conditional entropy under a mixture of measures carried by a common ball, for
labellings finite on balls (Rapaport (2.4), continuous form). -/
theorem integral_cent_le_cent_bind_of_inBall (hκ : Measurable κ)
    (hκ1 : ∀ y, IsProbabilityMeasure (κ y)) (hb : ∀ᵐ y ∂τ, InBall (κ y) c R)
    {f : ℝ × ℝ → L} {g : ℝ × ℝ → L'} (hf : Measurable f) (hg : Measurable g)
    (hfb : BallFinite f) (hgb : BallFinite g) :
    ∫ y, cent (κ y) f g ∂τ ≤ cent (τ.bind κ) f g :=
  integral_cent_le_cent_bind hκ hκ1 hf hg _ _ (ae_mem_toFinset_of_inBall hfb hb)
    (ae_mem_toFinset_of_inBall hgb hb)

/-- Lower bounds for conditional entropy pass to a mixture of measures carried by a common ball,
for labellings finite on balls (Rapaport (2.4), continuous form). -/
theorem le_cent_bind_of_ae_le_of_inBall (hκ : Measurable κ)
    (hκ1 : ∀ y, IsProbabilityMeasure (κ y)) (hb : ∀ᵐ y ∂τ, InBall (κ y) c R)
    {f : ℝ × ℝ → L} {g : ℝ × ℝ → L'} (hf : Measurable f) (hg : Measurable g)
    (hfb : BallFinite f) (hgb : BallFinite g) {a : ℝ} (ha : ∀ᵐ y ∂τ, a ≤ cent (κ y) f g) :
    a ≤ cent (τ.bind κ) f g :=
  le_cent_bind_of_ae_le hκ hκ1 hf hg _ _ (ae_mem_toFinset_of_inBall hfb hb)
    (ae_mem_toFinset_of_inBall hgb hb) ha

omit [MeasurableSpace L'] [MeasurableSingletonClass L'] in
/-- Concavity of entropy under a mixture of measures carried by a common ball, for labellings
finite on balls (Rapaport (2.4), continuous form). -/
theorem integral_ent_le_ent_bind_of_inBall (hκ : Measurable κ)
    (hκ1 : ∀ y, IsProbabilityMeasure (κ y)) (hb : ∀ᵐ y ∂τ, InBall (κ y) c R)
    {f : ℝ × ℝ → L} (hf : Measurable f) (hfb : BallFinite f) :
    ∫ y, ent (κ y) f ∂τ ≤ ent (τ.bind κ) f :=
  integral_ent_le_ent_bind hκ hκ1 hf _ (ae_mem_toFinset_of_inBall hfb hb)

omit [MeasurableSpace L'] [MeasurableSingletonClass L'] in
/-- Lower bounds for entropy pass to a mixture of measures carried by a common ball, for
labellings finite on balls (Rapaport (2.4), continuous form). -/
theorem le_ent_bind_of_ae_le_of_inBall (hκ : Measurable κ)
    (hκ1 : ∀ y, IsProbabilityMeasure (κ y)) (hb : ∀ᵐ y ∂τ, InBall (κ y) c R)
    {f : ℝ × ℝ → L} (hf : Measurable f) (hfb : BallFinite f) {a : ℝ}
    (ha : ∀ᵐ y ∂τ, a ≤ ent (κ y) f) : a ≤ ent (τ.bind κ) f :=
  le_ent_bind_of_ae_le hκ hκ1 hf _ (ae_mem_toFinset_of_inBall hfb hb) ha

end Ball

end BoxLike.Rapaport
