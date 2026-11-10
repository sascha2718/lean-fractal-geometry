module

/-
Lemma 3.2 of Rapaport (arXiv:2309.03985v1, lines 867 to 1017 of the source), "entropy of slices
of `O(1)` measures", for `d = 2`, through the vendored quantitative central limit theorem
`bounded_law_entropy_growth` of the Kittle–Kogler library.

* Conditional entropy: `sub_ent_le_cent_pair`, `sub_ent_le_cent_pair_swap`
  (`H(X ∣ Y, Z) ≥ H(X ∣ Y) - H(Z)`).
* Nesting of coordinate labels: `dyadicQuantize_factor`, `hLabel_factor`, `vLabel_factor`.
* The coordinate away from the slice: `ent_dyadicQuantize_le` (Chebyshev with half a mesh).
* The one-dimensional core: `dyadicEntropy_congr`, `exists_dyadicEntropy_growth`,
  `ent_hLabel_convk_eq`, `ent_vLabel_convk_eq`.
* The choice of the level: `sliceLevel`, `exists_sliceLevel_good`.
* Bookkeeping: `exists_slice_M`, `slice_step_spec`, `lvl_sub_le_of_le`,
  `InBall.ae_map_fst_mem_Icc`, `InBall.ae_map_snd_mem_Icc`, `inBall_convk_of_forall`,
  `sliceConst`.
* Lemma 3.2: `Exps.slices_one` (`j = 1`), `Exps.slices_two` (`j = 2`).
-/
public import BoxLike.Rapaport.Entropy.Conv
public import BoxLike.Rapaport.Entropy.Variance
public import ExactOverlaps.GaussianEntropyGrowth.LawEntropyGrowth
public import ExactOverlaps.SelfSimilar.ScaleEntropyComparison

@[expose] public section

namespace BoxLike.Rapaport

open MeasureTheory ProbabilityTheory Filter Topology
open ExactOverlaps.Entropy

/-! ### Conditioning on one more labelling -/

section Conditional

variable {X : Type*} [MeasurableSpace X] {θ : Measure X} [IsProbabilityMeasure θ]
variable {L L' L'' : Type*}
variable [MeasurableSpace L] [MeasurableSingletonClass L] [Countable L]
variable [MeasurableSpace L'] [MeasurableSingletonClass L'] [Countable L']
variable [MeasurableSpace L''] [MeasurableSingletonClass L''] [Countable L'']

/-- `H(θ, 𝒟 ∣ ℰ ∨ ℱ) ≥ H(θ, 𝒟 ∣ ℰ) - H(θ, ℱ)`: refining the conditioning partition by `ℱ`
costs at most the entropy of `ℱ` (the planar transfer in the proof of Lemma 3.2 of the source,
lines 867 to 1017). -/
theorem sub_ent_le_cent_pair {f : X → L} {g : X → L'} {h : X → L''} (hf : Measurable f)
    (hg : Measurable g) (hh : Measurable h) (hfinf : FiniteLabels θ f)
    (hfing : FiniteLabels θ g) (hfinh : FiniteLabels θ h) :
    cent θ f g - ent θ h ≤ cent θ f (fun x => (g x, h x)) := by
  have h1 : ent θ (fun x => (f x, g x)) ≤ ent θ (fun x => (f x, (g x, h x))) :=
    ent_le_of_factor (hf.prodMk (hg.prodMk hh)) (hfinf.pair (hfing.pair hfinh))
      (fun a : L × L' × L'' => (a.1, a.2.1)) rfl
  have h2 := ent_pair_le hg hh hfing hfinh
  unfold cent
  linarith

/-- The form of `sub_ent_le_cent_pair` with the additional labelling first. -/
theorem sub_ent_le_cent_pair_swap {f : X → L} {g : X → L'} {h : X → L''} (hf : Measurable f)
    (hg : Measurable g) (hh : Measurable h) (hfinf : FiniteLabels θ f)
    (hfing : FiniteLabels θ g) (hfinh : FiniteLabels θ h) :
    cent θ f g - ent θ h ≤ cent θ f (fun x => (h x, g x)) := by
  rw [← cent_comp_right_eq_of_injective Prod.swap_injective f (fun x => (h x, g x))]
  exact sub_ent_le_cent_pair hf hg hh hfinf hfing hfinh

end Conditional

/-! ### Nesting of the coordinate labels -/

section Nesting

/-- A coarser dyadic label is a function of a finer one. -/
theorem dyadicQuantize_factor {i i' : ℤ} (h : i ≤ i') :
    ∃ φ : ℤ → ℤ, ∀ x, dyadicQuantize i x = φ (dyadicQuantize i' x) := by
  refine ⟨fun l => l / (2 ^ (i' - i).toNat : ℕ), fun x => ?_⟩
  have e := dyadicQuantize_add_nat i (i' - i).toNat x
  rwa [show i + ((i' - i).toNat : ℤ) = i' by omega] at e

/-- A coarser horizontal labelling is a function of a finer one. -/
theorem hLabel_factor {i i' : ℤ} (h : i ≤ i') : ∃ φ : ℤ → ℤ, hLabel i = φ ∘ hLabel i' := by
  obtain ⟨φ, hφ⟩ := dyadicQuantize_factor h
  exact ⟨φ, funext fun z => hφ z.1⟩

/-- A coarser vertical labelling is a function of a finer one. -/
theorem vLabel_factor {j j' : ℤ} (h : j ≤ j') : ∃ φ : ℤ → ℤ, vLabel j = φ ∘ vLabel j' := by
  obtain ⟨φ, hφ⟩ := dyadicQuantize_factor h
  exact ⟨φ, funext fun z => hφ z.2⟩

end Nesting

/-! ### The coordinate away from the slice -/

section Chebyshev

/-- The dyadic labels at level `i` of a closed interval of length `2^{-i}` number at most `3`. -/
private theorem card_Icc_quantize_le_three (i : ℤ) (w : ℝ) :
    (Finset.Icc (dyadicQuantize i (w - ((2 : ℝ) ^ i)⁻¹ / 2))
      (dyadicQuantize i (w + ((2 : ℝ) ^ i)⁻¹ / 2))).card ≤ 3 := by
  have hp : 0 < ((2 : ℝ) ^ i)⁻¹ := inv_pos.2 (zpow_pos two_pos i)
  have h := card_Icc_quantize_le (i := i) (by linarith :
    w - ((2 : ℝ) ^ i)⁻¹ / 2 ≤ w + ((2 : ℝ) ^ i)⁻¹ / 2)
  have e : (2 : ℝ) ^ i * (w + ((2 : ℝ) ^ i)⁻¹ / 2 - (w - ((2 : ℝ) ^ i)⁻¹ / 2)) = 1 := by
    rw [show w + ((2 : ℝ) ^ i)⁻¹ / 2 - (w - ((2 : ℝ) ^ i)⁻¹ / 2) = ((2 : ℝ) ^ i)⁻¹ by ring]
    exact mul_inv_cancel₀ (zpow_pos two_pos i).ne'
  rw [e] at h
  have h3 : ((Finset.Icc (dyadicQuantize i (w - ((2 : ℝ) ^ i)⁻¹ / 2))
      (dyadicQuantize i (w + ((2 : ℝ) ^ i)⁻¹ / 2))).card : ℝ) ≤ 3 := by linarith
  exact_mod_cast h3

/-- The entropy of the dyadic labels at level `i` of a real coordinate `X` which is carried by
an interval of radius `R`: Chebyshev's inequality around the mean with half a mesh leaves at
most `3` labels inside and mass at most `Var X · 4 · 2^{2i}` outside, where at most
`2^i 2R + 2` labels occur. This bounds the entropy of the partition `π_{j'}⁻¹ ℰ_{q+m}` in the
proof of Lemma 3.2 of the source (lines 867 to 1017); it takes the place of Rapaport's rescaling
by `A_χ^{-a}` and his set `S`. -/
theorem ent_dyadicQuantize_le {σ : Measure (ℝ × ℝ)} [IsProbabilityMeasure σ]
    {X : ℝ × ℝ → ℝ} (hX : Measurable X) {a R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ᵐ z ∂σ, |X z - a| ≤ R) (i : ℤ) :
    ent σ (fun z => dyadicQuantize i (X z)) ≤
      Real.log 6 + 4 * variance X σ * ((2 : ℝ) ^ i) ^ 2 *
        Real.log ((2 : ℝ) ^ i * (2 * R) + 2) := by
  set f : ℝ × ℝ → ℤ := fun z => dyadicQuantize i (X z) with hfdef
  have hf : Measurable f := (measurable_dyadicQuantize i).comp hX
  have hmem : MemLp X 2 σ := MemLp.of_bound hX.aestronglyMeasurable (|a| + R)
    (hb.mono fun z hz => by
      rw [Real.norm_eq_abs]
      have := abs_sub_abs_le_abs_sub (X z) a
      linarith)
  -- the labels of the whole measure
  set s : Finset ℤ := Finset.Icc (dyadicQuantize i (a - R)) (dyadicQuantize i (a + R))
  have hs : ∀ z, |X z - a| ≤ R → f z ∈ s := by
    intro z hz
    rw [abs_le] at hz
    exact Finset.mem_Icc.2 ⟨dyadicQuantize_mono i (by linarith),
      dyadicQuantize_mono i (by linarith)⟩
  have hscard : (s.card : ℝ) ≤ (2 : ℝ) ^ i * (2 * R) + 2 := by
    have h := card_Icc_quantize_le (i := i) (by linarith : a - R ≤ a + R)
    rwa [show a + R - (a - R) = 2 * R by ring] at h
  have h2R : 0 ≤ (2 : ℝ) ^ i * (2 * R) :=
    mul_nonneg (zpow_pos two_pos i).le (by linarith)
  have hlog0 : 0 ≤ Real.log ((2 : ℝ) ^ i * (2 * R) + 2) := Real.log_nonneg (by linarith)
  have hlogs : Real.log s.card ≤ Real.log ((2 : ℝ) ^ i * (2 * R) + 2) := by
    rcases Nat.eq_zero_or_pos s.card with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact hlog0
    · exact Real.log_le_log (by exact_mod_cast h0) hscard
  have hfin : FiniteLabels σ f := finiteLabels_of_ae_mem_finset s (hb.mono fun z hz => hs z hz)
  -- the window of half a mesh about the mean
  set μX := ∫ w, X w ∂σ
  set ρ : ℝ := ((2 : ℝ) ^ i)⁻¹ / 2 with hρ
  have hρpos : 0 < ρ := by
    have := inv_pos.2 (zpow_pos (two_pos (α := ℝ)) i)
    positivity
  set B : Set (ℝ × ℝ) := {z | ρ ≤ |X z - μX|}ᶜ with hBdef
  have hB : MeasurableSet B :=
    (measurableSet_le measurable_const
      (continuous_abs.measurable.comp (hX.sub measurable_const))).compl
  have htwo := ent_le_two_pieces hf hfin hB
  -- inside the window: at most three labels
  have hin : σ.real B * ent (σ[|B]) f ≤ Real.log 3 := by
    by_cases h0 : σ B = 0
    · rw [measureReal_def, h0, ENNReal.toReal_zero, zero_mul]
      exact Real.log_nonneg (by norm_num)
    have := cond_isProbabilityMeasure h0
    set s' : Finset ℤ := Finset.Icc (dyadicQuantize i (μX - ρ)) (dyadicQuantize i (μX + ρ))
    have hs' : ∀ᵐ z ∂σ[|B], f z ∈ s' := by
      filter_upwards [ae_cond_mem hB] with z hz
      have hz' : |X z - μX| < ρ := not_le.1 hz
      rw [abs_lt] at hz'
      exact Finset.mem_Icc.2 ⟨dyadicQuantize_mono i (by linarith),
        dyadicQuantize_mono i (by linarith)⟩
    have h1 := ent_le_log_of_ae_mem hf s' hs'
    have h2 : Real.log s'.card ≤ Real.log 3 := by
      have := log_card_le_log (L := ℤ) (card_Icc_quantize_le_three i μX)
      exact_mod_cast this
    have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    calc σ.real B * ent (σ[|B]) f ≤ σ.real B * Real.log 3 :=
          mul_le_mul_of_nonneg_left (h1.trans h2) measureReal_nonneg
      _ ≤ 1 * Real.log 3 := mul_le_mul_of_nonneg_right measureReal_le_one h3
      _ = Real.log 3 := one_mul _
  -- outside the window: Chebyshev
  have hcheb : σ.real Bᶜ ≤ 4 * variance X σ * ((2 : ℝ) ^ i) ^ 2 := by
    rw [hBdef, compl_compl]
    refine (measureReal_abs_sub_integral_ge_le hmem hρpos).trans (le_of_eq ?_)
    rw [hρ]
    have := (zpow_pos (two_pos (α := ℝ)) i).ne'
    field_simp
    ring
  have hout : σ.real Bᶜ * ent (σ[|Bᶜ]) f ≤
      4 * variance X σ * ((2 : ℝ) ^ i) ^ 2 * Real.log ((2 : ℝ) ^ i * (2 * R) + 2) := by
    by_cases h0 : σ Bᶜ = 0
    · rw [measureReal_def, h0, ENNReal.toReal_zero, zero_mul]
      have := variance_nonneg X σ
      positivity
    have := cond_isProbabilityMeasure h0
    have hs'' : ∀ᵐ z ∂σ[|Bᶜ], f z ∈ s :=
      (hb.filter_mono cond_absolutelyContinuous.ae_le).mono fun z hz => hs z hz
    have h1 := (ent_le_log_of_ae_mem hf s hs'').trans hlogs
    calc σ.real Bᶜ * ent (σ[|Bᶜ]) f
        ≤ σ.real Bᶜ * Real.log ((2 : ℝ) ^ i * (2 * R) + 2) :=
          mul_le_mul_of_nonneg_left h1 measureReal_nonneg
      _ ≤ _ := mul_le_mul_of_nonneg_right hcheb hlog0
  have e6 : Real.log 6 = Real.log 3 + Real.log 2 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  linarith

end Chebyshev

/-! ### The one-dimensional core: the quantitative central limit theorem -/

section Core

/-- The dyadic entropy depends only on the law, not on the proof of bounded support. -/
theorem dyadicEntropy_congr {μ μ' : ProbabilityMeasure ℝ} (h : μ = μ') (hμ : HasBoundedSupport μ)
    (hμ' : HasBoundedSupport μ') (i : ℤ) : dyadicEntropy μ hμ i = dyadicEntropy μ' hμ' i := by
  subst h
  rfl

/-- The one-dimensional core of Lemma 3.2 of the source (lines 867 to 1017), through the
vendored quantitative central limit theorem `bounded_law_entropy_growth` with `C = 2^d`: for
every `d ≥ 1` there are `δ, A > 0` such that the law of a sum of `k` independent variables, each
carried by an interval of length `2R ≤ δ 2^{-i}`, whose variances add up to at least
`A 2^{-2i}`, gains at least `d log 2 - 1 - 2 log 7` nats of dyadic entropy from level `i - d` to
level `i`. The two scale entropies at `2^{-i}` and `2^{d-i}` are compared with the dyadic ones
by `abs_entropy_sub_dyadicEntropy_le`, at a cost of `log 7` each. -/
theorem exists_dyadicEntropy_growth (d : ℕ) (hd : d ≠ 0) :
    ∃ δ > 0, ∃ A > 0, ∀ (k : ℕ) (ν : Fin k → ProbabilityMeasure ℝ) (a : Fin k → ℝ) (R : ℝ)
      (i : ℤ) (hμ : HasBoundedSupport (continuousSumLaw ν)),
      (∀ l, ∀ᵐ x ∂(ν l : Measure ℝ), x ∈ Set.Icc (a l - R) (a l + R)) →
      2 * R ≤ δ * (2 : ℝ) ^ (-i) →
      A * ((2 : ℝ) ^ (-i)) ^ 2 ≤ ∑ l, variance id (ν l : Measure ℝ) →
      (d : ℝ) * Real.log 2 - 1 - 2 * Real.log 7 <
        dyadicEntropy (continuousSumLaw ν) hμ i -
          dyadicEntropy (continuousSumLaw ν) hμ (i - d) := by
  obtain ⟨δ, hδ, A, hA, h⟩ := ExactOverlaps.GaussianEntropyGrowth.bounded_law_entropy_growth.{0}
    (2 ^ d) (Nat.one_lt_two_pow hd) one_pos
  refine ⟨δ, hδ, A, hA, fun k ν a R i hμ hb hw hv => ?_⟩
  set r : ℝ := (2 : ℝ) ^ (-i) with hr
  have hr0 : 0 < r := zpow_pos two_pos _
  have hR0 : 0 < ((2 ^ d : ℕ) : ℝ) * r := by positivity
  have key := h r hr0 ν (fun l => ⟨a l - R, a l + R, by linarith, hb l⟩) hv
  rw [ExactOverlaps.GaussianScaleEntropy.entropyBetween_eq_bounded _ hμ hr0 hR0,
    ExactOverlaps.ScaleEntropy.entropyBetween] at key
  have e1 : (2 : ℝ) ^ i * r = 1 := by
    rw [hr, ← zpow_add₀ two_ne_zero, add_neg_cancel, zpow_zero]
  have e2 : (2 : ℝ) ^ (i - d) * (((2 ^ d : ℕ) : ℝ) * r) = 1 := by
    rw [hr, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, ← zpow_add₀ two_ne_zero,
      ← zpow_add₀ two_ne_zero, show i - (d : ℤ) + ((d : ℤ) + -i) = 0 by ring, zpow_zero]
  have h1 := ExactOverlaps.ScaleEntropy.abs_entropy_sub_dyadicEntropy_le _ hμ i r hr0
    (by rw [e1]; norm_num) e1.le
  have h2 := ExactOverlaps.ScaleEntropy.abs_entropy_sub_dyadicEntropy_le _ hμ (i - d) _ hR0
    (by rw [e2]; norm_num) e2.le
  have hlog : Real.log (((2 ^ d : ℕ) : ℝ)) = d * Real.log 2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  rw [hlog] at key
  rw [abs_le] at h1 h2
  linarith [h1.1, h1.2, h2.1, h2.2]

variable {k : ℕ} (θ : Fin k → Measure (ℝ × ℝ)) [∀ l, IsProbabilityMeasure (θ l)]

/-- The horizontal entropy of `θ_0 ∗ ⋯ ∗ θ_{k-1}` is the dyadic entropy of the vendored
`continuousSumLaw` of the first marginals. -/
theorem ent_hLabel_convk_eq (hb : ∀ l, BddSupp (θ l))
    (hμ : HasBoundedSupport (continuousSumLaw
      fun l => (⟨(θ l).map Prod.fst, inferInstance⟩ : ProbabilityMeasure ℝ))) (i : ℤ) :
    ent (convk k θ) (hLabel i) = dyadicEntropy (continuousSumLaw
      fun l => (⟨(θ l).map Prod.fst, inferInstance⟩ : ProbabilityMeasure ℝ)) hμ i := by
  rw [ent_hLabel_eq_dyadicEntropy (BddSupp.convk hb) i]
  refine dyadicEntropy_congr ?_ _ _ i
  exact ProbabilityMeasure.toMeasure_injective (map_fst_convk_eq_continuousSumLaw θ)

/-- The vertical entropy of `θ_0 ∗ ⋯ ∗ θ_{k-1}` is the dyadic entropy of the vendored
`continuousSumLaw` of the second marginals. -/
theorem ent_vLabel_convk_eq (hb : ∀ l, BddSupp (θ l))
    (hμ : HasBoundedSupport (continuousSumLaw
      fun l => (⟨(θ l).map Prod.snd, inferInstance⟩ : ProbabilityMeasure ℝ))) (j : ℤ) :
    ent (convk k θ) (vLabel j) = dyadicEntropy (continuousSumLaw
      fun l => (⟨(θ l).map Prod.snd, inferInstance⟩ : ProbabilityMeasure ℝ)) hμ j := by
  rw [ent_vLabel_eq_dyadicEntropy (BddSupp.convk hb) j]
  refine dyadicEntropy_congr ?_ _ _ j
  exact ProbabilityMeasure.toMeasure_injective (map_snd_convk_eq_continuousSumLaw θ)

end Core

/-! ### The choice of the level -/

section Level

/-- The planar level `q + m` of Lemma 3.2 for `k` summands: the integer
`t = ⌈-L / α⌉` with `L = log (ε k / (4A)) / 2`, so that `e^{-α t}` lies in `[e^{L-α}, e^L]` and
the mesh `2^{-lvl α t}` of the slice direction is of the order `√(ε k / A)`, the largest scale
at which the central limit theorem applies (Rapaport's `l - a`, lines 867 to 1017 of the
source). -/
noncomputable def sliceLevel (α ε A : ℝ) (k : ℕ) : ℤ :=
  ⌈-(Real.log (ε * k / (4 * A)) / 2) / α⌉

/-- `C e^{-γ x} (c + 2x) → 0` as `x → ∞`, for `γ > 0`. -/
private theorem tendsto_mul_exp_neg_mul_add (C c : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun x : ℝ => C * Real.exp (-γ * x) * (c + 2 * x)) atTop (𝓝 0) := by
  have hγx : Tendsto (fun x : ℝ => γ * x) atTop atTop := tendsto_id.const_mul_atTop hγ
  have h1 : Tendsto (fun x : ℝ => Real.exp (-γ * x)) atTop (𝓝 0) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp hγx).congr fun x => by
      simp only [Function.comp_apply, neg_mul]
  have h2 : Tendsto (fun x : ℝ => x * Real.exp (-γ * x)) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hγx).const_mul γ⁻¹
    rw [mul_zero] at h
    refine h.congr fun x => ?_
    simp only [Function.comp_apply, pow_one, neg_mul]
    field_simp
  have h3 := ((h1.const_mul c).add (h2.const_mul 2)).const_mul C
  simp only [mul_zero, add_zero] at h3
  refine h3.congr fun x => ?_
  ring

/-- The large-`k` conditions of Lemma 3.2 at the level `t = sliceLevel α ε A k` (proof of
Lemma 3.2 of the source, lines 867 to 1017): for `k` large, (i) intervals of length `2 ε⁻¹`
are at most `δ` meshes of the slice direction, (ii) `A` times the squared mesh is at most
`ε k`, (iii) the mesh `2^{-lvl β t}` of the other direction is at least `1`, and (iv) a variance
`V ≤ v₀ k^p` in the other direction with `p α < β` makes the Chebyshev error
`4 V 2^{2 lvl β t} log (2^{lvl β t} 2 k ε⁻¹ + 2)` at most `1`. -/
theorem exists_sliceLevel_good {α β ε δ A v₀ : ℝ} (p : ℕ) (hα : 0 < α) (hpβ : p * α < β)
    (hε : 0 < ε) (hδ : 0 < δ) (hA : 0 < A) (hv₀ : 0 ≤ v₀) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      2 * ε⁻¹ ≤ δ * (2 : ℝ) ^ (-lvl α (sliceLevel α ε A k)) ∧
      A * ((2 : ℝ) ^ (-lvl α (sliceLevel α ε A k))) ^ 2 ≤ ε * k ∧
      (2 : ℝ) ^ lvl β (sliceLevel α ε A k) ≤ 1 ∧
      ∀ V : ℝ, 0 ≤ V → V ≤ v₀ * (k : ℝ) ^ p →
        4 * V * ((2 : ℝ) ^ lvl β (sliceLevel α ε A k)) ^ 2 *
          Real.log ((2 : ℝ) ^ lvl β (sliceLevel α ε A k) * (2 * (k * ε⁻¹)) + 2) ≤ 1 := by
  have hβ : 0 < β := lt_of_le_of_lt (by positivity) hpβ
  set γ : ℝ := 2 * (β / α - p) with hγdef
  have hγ : 0 < γ := by
    have : (p : ℝ) < β / α := by rwa [lt_div_iff₀ hα]
    rw [hγdef]
    linarith
  set c₂ : ℝ := 2 * ε⁻¹ * (4 * A / ε) + 2 with hc₂
  have hc₂pos : 0 < c₂ := by positivity
  set C₁ : ℝ := 4 * v₀ * (4 * A / ε) ^ p * Real.exp (2 * β) with hC₁
  set g : ℝ → ℝ := fun x => C₁ * Real.exp (-γ * x) * (Real.log c₂ + 2 * x) with hg
  have hgt : Tendsto g atTop (𝓝 0) := tendsto_mul_exp_neg_mul_add C₁ (Real.log c₂) hγ
  set L : ℕ → ℝ := fun k => Real.log (ε * k / (4 * A)) / 2 with hLdef
  have hL : Tendsto L atTop atTop := by
    have : Tendsto (fun k : ℕ => ε * (k : ℝ) / (4 * A)) atTop atTop :=
      (tendsto_natCast_atTop_atTop.const_mul_atTop hε).atTop_div_const (by positivity)
    exact (Real.tendsto_log_atTop.comp this).atTop_div_const two_pos
  set L₀ : ℝ := max 0 (α + Real.log (2 * ε⁻¹ / δ)) with hL₀
  have hev : ∀ᶠ x in atTop, g x ≤ 1 ∧ L₀ ≤ x :=
    (hgt.eventually (eventually_le_nhds one_pos)).and (eventually_ge_atTop L₀)
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((hL.eventually hev).and (eventually_ge_atTop 1))
  refine ⟨K, fun k hk => ?_⟩
  obtain ⟨⟨hg1, hLL₀⟩, hk1⟩ := hK k hk
  set t : ℤ := sliceLevel α ε A k with htdef
  set Lk : ℝ := L k with hLk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hx : 0 < ε * k / (4 * A) := by positivity
  have hexpL : Real.exp (2 * Lk) = ε * k / (4 * A) := by
    rw [hLk, hLdef, show 2 * (Real.log (ε * k / (4 * A)) / 2) = Real.log (ε * k / (4 * A)) by
      ring]
    exact Real.exp_log hx
  have hLk0 : 0 ≤ Lk := le_trans (le_max_left _ _) hLL₀
  have hLk1 : α + Real.log (2 * ε⁻¹ / δ) ≤ Lk := le_trans (le_max_right _ _) hLL₀
  have ht1 : -Lk / α ≤ t := Int.le_ceil _
  have ht2 : (t : ℝ) < -Lk / α + 1 := Int.ceil_lt_add_one _
  have hat1 : -(α * t) ≤ Lk := by
    have := (div_le_iff₀ hα).1 ht1
    linarith
  have hat2 : α * t < -Lk + α := by
    have := mul_lt_mul_of_pos_left ht2 hα
    rw [mul_add, mul_div_cancel₀ _ hα.ne', mul_one] at this
    exact this
  have hw1 : (2 : ℝ) ^ lvl β t ≤ 1 := by
    have ht0 : t ≤ 0 := by
      have h0 : -Lk / α ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hα.le
      have h1 : (t : ℝ) < 1 := by linarith
      have h2 : t < 1 := by exact_mod_cast h1
      omega
    refine (two_zpow_lvl_le β t).trans ?_
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonneg_of_nonpos hβ.le (Int.cast_nonpos.2 ht0)
  refine ⟨?_, ?_, hw1, ?_⟩
  · -- (i) the width condition
    have h1 := exp_neg_le_two_zpow_neg_lvl α t
    have h2 : Real.exp (Real.log (2 * ε⁻¹ / δ)) ≤ Real.exp (-α * t) :=
      Real.exp_le_exp.2 (by linarith)
    rw [Real.exp_log (by positivity)] at h2
    have h3 := h2.trans h1
    rw [div_le_iff₀ hδ] at h3
    linarith
  · -- (ii) the variance condition
    have h1 := two_zpow_neg_lvl_le α t
    have h2 : Real.exp (-α * t) ≤ Real.exp Lk := Real.exp_le_exp.2 (by linarith)
    have h3 : (2 : ℝ) ^ (-lvl α t) ≤ 2 * Real.exp Lk := h1.trans (by linarith)
    have h4 : ((2 : ℝ) ^ (-lvl α t)) ^ 2 ≤ (2 * Real.exp Lk) ^ 2 :=
      pow_le_pow_left₀ (zpow_pos two_pos _).le h3 2
    have h5 : (2 * Real.exp Lk) ^ 2 = 4 * Real.exp (2 * Lk) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      norm_num
    rw [h5, hexpL] at h4
    calc A * ((2 : ℝ) ^ (-lvl α t)) ^ 2 ≤ A * (4 * (ε * k / (4 * A))) :=
          mul_le_mul_of_nonneg_left h4 hA.le
      _ = ε * k := by field_simp
  · -- (iv) the Chebyshev error
    intro V hV0 hV
    set w : ℝ := (2 : ℝ) ^ lvl β t with hwdef
    have hw0 : 0 < w := zpow_pos two_pos _
    have hβt : β * t < -(β / α) * Lk + β := by
      have h := mul_lt_mul_of_pos_left hat2 (div_pos hβ hα)
      have e : β / α * (α * t) = β * t := by field_simp
      have e' : β / α * (-Lk + α) = -(β / α) * Lk + β := by field_simp
      rw [e, e'] at h
      exact h
    have hw2 : w ^ 2 ≤ Real.exp (2 * β - 2 * (β / α) * Lk) := by
      have h1 : w ^ 2 ≤ Real.exp (β * t) ^ 2 :=
        pow_le_pow_left₀ hw0.le (two_zpow_lvl_le β t) 2
      have h2 : Real.exp (β * t) ^ 2 = Real.exp (2 * (β * t)) := by
        rw [← Real.exp_nat_mul]
        norm_num
      rw [h2] at h1
      exact h1.trans (Real.exp_le_exp.2 (by linarith))
    have hk : (k : ℝ) = 4 * A / ε * Real.exp (2 * Lk) := by
      rw [hexpL]
      field_simp
    have hkp : (k : ℝ) ^ p = (4 * A / ε) ^ p * Real.exp (2 * p * Lk) := by
      rw [hk, mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring
    have hVb : V ≤ v₀ * ((4 * A / ε) ^ p * Real.exp (2 * p * Lk)) := hV.trans (by rw [hkp])
    have he1 : 1 ≤ Real.exp (2 * Lk) := Real.one_le_exp (by linarith)
    have hlog0 : 0 ≤ Real.log (w * (2 * (k * ε⁻¹)) + 2) :=
      Real.log_nonneg (by have : 0 ≤ w * (2 * (k * ε⁻¹)) := by positivity
                          linarith)
    have hlog : Real.log (w * (2 * (k * ε⁻¹)) + 2) ≤ Real.log c₂ + 2 * Lk := by
      have h1 : w * (2 * (k * ε⁻¹)) + 2 ≤ c₂ * Real.exp (2 * Lk) := by
        have h2 : w * (2 * (k * ε⁻¹)) ≤ 2 * (k * ε⁻¹) := by
          have : 0 ≤ 2 * (k * ε⁻¹) := by positivity
          nlinarith
        have h3 : 2 * (k * ε⁻¹) = 2 * ε⁻¹ * (4 * A / ε) * Real.exp (2 * Lk) := by
          rw [hk]
          ring
        rw [hc₂]
        nlinarith
      calc Real.log (w * (2 * (k * ε⁻¹)) + 2) ≤ Real.log (c₂ * Real.exp (2 * Lk)) :=
            Real.log_le_log (by positivity) h1
        _ = Real.log c₂ + 2 * Lk := by
            rw [Real.log_mul hc₂pos.ne' (Real.exp_pos _).ne', Real.log_exp]
    have hE : Real.exp (2 * p * Lk) * Real.exp (2 * β - 2 * (β / α) * Lk) =
        Real.exp (2 * β) * Real.exp (-γ * Lk) := by
      rw [← Real.exp_add, ← Real.exp_add, hγdef]
      congr 1
      ring
    calc 4 * V * w ^ 2 * Real.log (w * (2 * (k * ε⁻¹)) + 2)
        ≤ 4 * (v₀ * ((4 * A / ε) ^ p * Real.exp (2 * p * Lk))) *
            Real.exp (2 * β - 2 * (β / α) * Lk) * (Real.log c₂ + 2 * Lk) := by
          refine mul_le_mul (mul_le_mul (by linarith) hw2 (by positivity) (by positivity))
            hlog hlog0 (by positivity)
      _ = 4 * v₀ * (4 * A / ε) ^ p * (Real.exp (2 * p * Lk) *
            Real.exp (2 * β - 2 * (β / α) * Lk)) * (Real.log c₂ + 2 * Lk) := by ring
      _ = g Lk := by
          rw [hE, hg, hC₁]
          ring
      _ ≤ 1 := hg1

end Level

/-! ### Lemma 3.2 -/

section Slices

/-- The number of planar levels `m` needed in Lemma 3.2: for `m ≥ M` the slice direction of
exponent `α` gains at least two dyadic levels and `ε m` absorbs the constant `C₀`. -/
theorem exists_slice_M {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) (C₀ : ℝ) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 2 ≤ α * m / Real.log 2 ∧ C₀ ≤ ε * m ∧ (0 : ℝ) < m := by
  refine ⟨⌈2 * Real.log 2 / α⌉₊ + ⌈C₀ / ε⌉₊ + 1, fun m hm => ?_⟩
  have hm' : ((⌈2 * Real.log 2 / α⌉₊ + ⌈C₀ / ε⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
  push_cast at hm'
  have h1 := Nat.le_ceil (2 * Real.log 2 / α)
  have h2 := Nat.le_ceil (C₀ / ε)
  have h3 : (0 : ℝ) ≤ ⌈2 * Real.log 2 / α⌉₊ := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ ⌈C₀ / ε⌉₊ := Nat.cast_nonneg _
  have hl2 := Real.log_pos one_lt_two
  refine ⟨?_, ?_, by linarith⟩
  · rw [le_div_iff₀ hl2]
    have : 2 * Real.log 2 / α ≤ m := by linarith
    rw [div_le_iff₀ hα] at this
    linarith
  · have : C₀ / ε ≤ m := by linarith
    rw [div_le_iff₀ hε] at this
    linarith

/-- The dyadic step `d = ⌊x⌋₊ - 1` of Lemma 3.2 for `x = α m / log 2 ≥ 2`: `d ≥ 1` and
`x - 2 ≤ d ≤ x - 1`. -/
theorem slice_step_spec {x : ℝ} (hx : 2 ≤ x) :
    ⌊x⌋₊ - 1 ≠ 0 ∧ ((⌊x⌋₊ - 1 : ℕ) : ℝ) ≤ x - 1 ∧ x - 2 ≤ ((⌊x⌋₊ - 1 : ℕ) : ℝ) := by
  have h2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hc : ((⌊x⌋₊ - 1 : ℕ) : ℝ) = (⌊x⌋₊ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hle := Nat.floor_le (by linarith : (0 : ℝ) ≤ x)
  have hlt := Nat.lt_floor_add_one x
  refine ⟨by omega, ?_, ?_⟩ <;> rw [hc] <;> linarith

/-- The coarse level `lvl α (t - m)` lies at least `d` dyadic levels below `lvl α t` when
`d ≤ α m / log 2 - 1`. -/
theorem lvl_sub_le_of_le {α : ℝ} (t : ℤ) {m d : ℕ} (h : (d : ℝ) ≤ α * m / Real.log 2 - 1) :
    lvl α (t - m) ≤ lvl α t - d := by
  have h1 := le_lvl_add_sub α (t - m) m
  rw [sub_add_cancel, Int.cast_natCast] at h1
  have h2 : ((d : ℤ) : ℝ) ≤ ((lvl α t - lvl α (t - m) : ℤ) : ℝ) := by
    push_cast
    linarith
  have h3 : (d : ℤ) ≤ lvl α t - lvl α (t - m) := by exact_mod_cast h2
  omega

/-- A planar measure carried by a ball of radius `R` about `c` has its first marginal carried by
`[c.1 - R, c.1 + R]`. -/
theorem InBall.ae_map_fst_mem_Icc {θ : Measure (ℝ × ℝ)} {c : ℝ × ℝ} {R : ℝ} (h : InBall θ c R) :
    ∀ᵐ x ∂(θ.map Prod.fst), x ∈ Set.Icc (c.1 - R) (c.1 + R) :=
  (ae_map_iff measurable_fst.aemeasurable measurableSet_Icc).2
    (Filter.Eventually.mono h fun z hz => by
      have h1 := ((norm_le_iff_abs_le _ _).1 hz).1
      rw [Prod.fst_sub, abs_le] at h1
      exact ⟨by linarith, by linarith⟩)

/-- A planar measure carried by a ball of radius `R` about `c` has its second marginal carried
by `[c.2 - R, c.2 + R]`. -/
theorem InBall.ae_map_snd_mem_Icc {θ : Measure (ℝ × ℝ)} {c : ℝ × ℝ} {R : ℝ} (h : InBall θ c R) :
    ∀ᵐ x ∂(θ.map Prod.snd), x ∈ Set.Icc (c.2 - R) (c.2 + R) :=
  (ae_map_iff measurable_snd.aemeasurable measurableSet_Icc).2
    (Filter.Eventually.mono h fun z hz => by
      have h1 := ((norm_le_iff_abs_le _ _).1 hz).2
      rw [Prod.snd_sub, abs_le] at h1
      exact ⟨by linarith, by linarith⟩)

/-- The convolution of `k` probability measures carried by balls of radius `R` is carried by the
ball of radius `k R` about the sum of the centres. -/
theorem inBall_convk_of_forall {k : ℕ} {θ : Fin k → Measure (ℝ × ℝ)}
    [∀ i, IsProbabilityMeasure (θ i)] {c : Fin k → ℝ × ℝ} {R : ℝ} (h : ∀ i, InBall (θ i) (c i) R) :
    InBall (convk k θ) (∑ i, c i) (k * R) := by
  have h' := InBall.convk (R := fun _ => R) h
  simpa [Finset.sum_const, nsmul_eq_mul] using h'

/-- The constant of Lemma 3.2: `2 log 2` from the dyadic step, `1 + 2 log 7` from the central
limit theorem and the comparison of scale and dyadic entropies, `2 (log 6 + 1)` from the two
partitions in the direction away from the slice. -/
noncomputable def sliceConst : ℝ := 2 * Real.log 2 + 2 * Real.log 7 + 2 * Real.log 6 + 3

namespace Exps

variable (χ : Exps)

/-- Lemma 3.2 of the source (lines 867 to 1017) for `d = 2` and the horizontal slice direction
`j = 1`: for `0 < ε < 1` and `m ≥ M(ε)`, `k ≥ K(ε, m)`, there is a level `q` such that for all
planar probability measures `θ_0, …, θ_{k-1}` carried by balls of radius `ε⁻¹` whose convolution
`σ` has `Var(π₁ σ) ≥ ε k`, `H(σ, ℰ_{q+m} ∣ ℰ_q ∨ π₂⁻¹ ℰ_{q+m}) / m > χ₁ - ε`. The level `q`
depends only on `ε`, `m` and `k`: it is `sliceLevel χ₁ ε A k - m` for the constant `A` of the
central limit theorem, the scale which Rapaport reaches by rescaling with `A_χ^{-a}`. -/
theorem slices_one : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∃ q : ℤ,
    ∀ (θ : Fin k → Measure (ℝ × ℝ)) [∀ i, IsProbabilityMeasure (θ i)] (c : Fin k → ℝ × ℝ),
      (∀ i, InBall (θ i) (c i) ε⁻¹) → ε * k ≤ var₁ (convk k θ) →
      χ.χ₁ - ε < cent (convk k θ) (χ.E (q + m))
        (fun z => (χ.E q z, χ.E₂ (q + m) z)) / m := by
  intro ε hε _hε1
  obtain ⟨M, hM⟩ := exists_slice_M χ.pos hε sliceConst
  refine ⟨M, fun m hm => ?_⟩
  obtain ⟨hm2, hmC, hmpos⟩ := hM m hm
  obtain ⟨hd0, hdle, hdge⟩ := slice_step_spec hm2
  set d : ℕ := ⌊χ.χ₁ * m / Real.log 2⌋₊ - 1 with hd
  obtain ⟨δ, hδ, A, hA, hclt⟩ := exists_dyadicEntropy_growth d hd0
  obtain ⟨K, hK⟩ := exists_sliceLevel_good (α := χ.χ₁) (β := χ.χ₂) (ε := ε) (δ := δ) (A := A)
    (v₀ := ε⁻¹ ^ 2) 1 χ.pos (by simpa using χ.lt) hε hδ hA (by positivity)
  refine ⟨K, fun k hk => ⟨sliceLevel χ.χ₁ ε A k - m, fun θ _ c hθ hvar => ?_⟩⟩
  obtain ⟨hwidth, hvarA, -, hcheb⟩ := hK k hk
  rw [sub_add_cancel]
  set t : ℤ := sliceLevel χ.χ₁ ε A k with ht
  set q : ℤ := t - (m : ℤ) with hq
  have hbdd : ∀ l, BddSupp (θ l) := fun l => ⟨c l, ε⁻¹, hθ l⟩
  have hσ : BddSupp (convk k θ) := BddSupp.convk hbdd
  -- the one-dimensional core on the first marginal
  have hμ : HasBoundedSupport (continuousSumLaw
      fun l => (⟨(θ l).map Prod.fst, inferInstance⟩ : ProbabilityMeasure ℝ)) :=
    continuousSumLaw_hasBoundedSupport _ fun l => hasBoundedSupport_fst (hbdd l)
  have hvsum : A * ((2 : ℝ) ^ (-lvl χ.χ₁ t)) ^ 2 ≤ ∑ l, variance id
      ((⟨(θ l).map Prod.fst, inferInstance⟩ : ProbabilityMeasure ℝ) : Measure ℝ) := by
    have e : ∑ l, variance id
        ((⟨(θ l).map Prod.fst, inferInstance⟩ : ProbabilityMeasure ℝ) : Measure ℝ) =
        var₁ (convk k θ) := by
      rw [var₁_convk hbdd]
      exact Finset.sum_congr rfl fun l _ => (var₁_eq_variance_map (θ l)).symm
    rw [e]
    linarith
  have hgrow := hclt k (fun l => ⟨(θ l).map Prod.fst, inferInstance⟩) (fun l => (c l).1) ε⁻¹
    (lvl χ.χ₁ t) hμ (fun l => (hθ l).ae_map_fst_mem_Icc) hwidth hvsum
  rw [← ent_hLabel_convk_eq θ hbdd hμ, ← ent_hLabel_convk_eq θ hbdd hμ] at hgrow
  have hgrow' : (d : ℝ) * Real.log 2 - 1 - 2 * Real.log 7 <
      ent (convk k θ) (χ.E₁ t) - ent (convk k θ) (hLabel (lvl χ.χ₁ t - d)) := hgrow
  -- the planar transfer
  have s1 : cent (convk k θ) (χ.E₁ t) (fun z => (χ.E q z, χ.E₂ t z)) ≤
      cent (convk k θ) (χ.E t) (fun z => (χ.E q z, χ.E₂ t z)) :=
    cent_le_of_factor (χ.measurable_E t) ((χ.measurable_E q).prodMk (χ.measurable_E₂ t))
      (hσ.finiteLabels_E χ t) ((hσ.finiteLabels_E χ q).pair (hσ.finiteLabels_E₂ χ t))
      Prod.fst rfl
  have s2 : cent (convk k θ) (χ.E₁ t) (χ.E q) - ent (convk k θ) (χ.E₂ t) ≤
      cent (convk k θ) (χ.E₁ t) (fun z => (χ.E q z, χ.E₂ t z)) :=
    sub_ent_le_cent_pair (χ.measurable_E₁ t) (χ.measurable_E q) (χ.measurable_E₂ t)
      (hσ.finiteLabels_E₁ χ t) (hσ.finiteLabels_E χ q) (hσ.finiteLabels_E₂ χ t)
  have s3 : cent (convk k θ) (χ.E₁ t) (χ.E₁ q) - ent (convk k θ) (χ.E₂ q) ≤
      cent (convk k θ) (χ.E₁ t) (χ.E q) :=
    sub_ent_le_cent_pair (χ.measurable_E₁ t) (χ.measurable_E₁ q) (χ.measurable_E₂ q)
      (hσ.finiteLabels_E₁ χ t) (hσ.finiteLabels_E₁ χ q) (hσ.finiteLabels_E₂ χ q)
  have s4 : cent (convk k θ) (χ.E₁ t) (hLabel (lvl χ.χ₁ t - d)) ≤
      cent (convk k θ) (χ.E₁ t) (χ.E₁ q) := by
    obtain ⟨ψ, hψ⟩ := hLabel_factor (lvl_sub_le_of_le (α := χ.χ₁) t hdle)
    exact cent_anti_of_factor (χ.measurable_E₁ t) (measurable_hLabel _)
      (hσ.finiteLabels_E₁ χ t) (hσ.finiteLabels_hLabel _) ψ hψ
  have s5 : ent (convk k θ) (χ.E₁ t) - ent (convk k θ) (hLabel (lvl χ.χ₁ t - d)) ≤
      cent (convk k θ) (χ.E₁ t) (hLabel (lvl χ.χ₁ t - d)) :=
    ent_sub_ent_le_cent (χ.measurable_E₁ t) (measurable_hLabel _) (hσ.finiteLabels_E₁ χ t)
      (hσ.finiteLabels_hLabel _)
  have s6 : ent (convk k θ) (χ.E₂ q) ≤ ent (convk k θ) (χ.E₂ t) := by
    obtain ⟨φ, hφ⟩ := vLabel_factor (lvl_mono χ.pos₂ (show q ≤ t by omega))
    exact ent_le_of_factor (χ.measurable_E₂ t) (hσ.finiteLabels_E₂ χ t) φ hφ
  -- the vertical partition has bounded entropy
  have s7 : ent (convk k θ) (χ.E₂ t) ≤ Real.log 6 + 1 := by
    have hball := inBall_convk_of_forall hθ
    have hb2 : ∀ᵐ z ∂(convk k θ), |z.2 - (∑ l, c l).2| ≤ k * ε⁻¹ :=
      Filter.Eventually.mono hball fun z hz => by
      have h1 := ((norm_le_iff_abs_le _ _).1 hz).2
      rwa [Prod.snd_sub] at h1
    have h := ent_dyadicQuantize_le (X := fun z : ℝ × ℝ => z.2) measurable_snd
      (by positivity) hb2 (lvl χ.χ₂ t)
    have hV0 : 0 ≤ var₂ (convk k θ) := variance_nonneg _ _
    have hVle : var₂ (convk k θ) ≤ ε⁻¹ ^ 2 * (k : ℝ) ^ 1 := by
      rw [var₂_convk hbdd]
      calc ∑ l, var₂ (θ l) ≤ ∑ _l : Fin k, ε⁻¹ ^ 2 :=
            Finset.sum_le_sum fun l _ => var₂_le_of_inBall (hθ l)
        _ = ε⁻¹ ^ 2 * (k : ℝ) ^ 1 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    have h' := hcheb (var₂ (convk k θ)) hV0 hVle
    have e : ent (convk k θ) (χ.E₂ t) =
        ent (convk k θ) (fun z => dyadicQuantize (lvl χ.χ₂ t) z.2) := rfl
    rw [e]
    exact h.trans (by unfold var₂ at h'; linarith)
  -- the dyadic step
  have hdl : χ.χ₁ * m - 2 * Real.log 2 ≤ d * Real.log 2 := by
    have hl2 := Real.log_pos one_lt_two
    have h := mul_le_mul_of_nonneg_right hdge hl2.le
    rw [sub_mul, div_mul_cancel₀ _ hl2.ne'] at h
    linarith
  rw [lt_div_iff₀ hmpos]
  unfold sliceConst at hmC
  linarith

/-- Lemma 3.2 of the source (lines 867 to 1017) for `d = 2` and the vertical slice direction
`j = 2`: for `0 < ε < 1` and `m ≥ M(ε)`, `k ≥ K(ε, m)`, there is a level `q` such that for all
planar probability measures `θ_0, …, θ_{k-1}` carried by balls of radius `ε⁻¹` whose convolution
`σ` has `Var(π₂ σ) ≥ ε k` and `Var(π₁ σ) ≤ ε⁻¹`,
`H(σ, ℰ_{q+m} ∣ ℰ_q ∨ π₁⁻¹ ℰ_{q+m}) / m > χ₂ - ε`. The level `q` depends only on `ε`, `m` and
`k`: it is `sliceLevel χ₂ ε A k - m` for the constant `A` of the central limit theorem. The
bound on `Var(π₁ σ)` is the source's hypothesis on the direction below `j`. -/
theorem slices_two : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∃ q : ℤ,
    ∀ (θ : Fin k → Measure (ℝ × ℝ)) [∀ i, IsProbabilityMeasure (θ i)] (c : Fin k → ℝ × ℝ),
      (∀ i, InBall (θ i) (c i) ε⁻¹) → ε * k ≤ var₂ (convk k θ) → var₁ (convk k θ) ≤ ε⁻¹ →
      χ.χ₂ - ε < cent (convk k θ) (χ.E (q + m))
        (fun z => (χ.E q z, χ.E₁ (q + m) z)) / m := by
  intro ε hε _hε1
  obtain ⟨M, hM⟩ := exists_slice_M χ.pos₂ hε sliceConst
  refine ⟨M, fun m hm => ?_⟩
  obtain ⟨hm2, hmC, hmpos⟩ := hM m hm
  obtain ⟨hd0, hdle, hdge⟩ := slice_step_spec hm2
  set d : ℕ := ⌊χ.χ₂ * m / Real.log 2⌋₊ - 1 with hd
  obtain ⟨δ, hδ, A, hA, hclt⟩ := exists_dyadicEntropy_growth d hd0
  obtain ⟨K, hK⟩ := exists_sliceLevel_good (α := χ.χ₂) (β := χ.χ₁) (ε := ε) (δ := δ) (A := A)
    (v₀ := ε⁻¹) 0 χ.pos₂ (by simpa using χ.pos) hε hδ hA (by positivity)
  refine ⟨K, fun k hk => ⟨sliceLevel χ.χ₂ ε A k - m, fun θ _ c hθ hvar hvar₁ => ?_⟩⟩
  obtain ⟨hwidth, hvarA, -, hcheb⟩ := hK k hk
  rw [sub_add_cancel]
  set t : ℤ := sliceLevel χ.χ₂ ε A k with ht
  set q : ℤ := t - (m : ℤ) with hq
  have hbdd : ∀ l, BddSupp (θ l) := fun l => ⟨c l, ε⁻¹, hθ l⟩
  have hσ : BddSupp (convk k θ) := BddSupp.convk hbdd
  -- the one-dimensional core on the second marginal
  have hμ : HasBoundedSupport (continuousSumLaw
      fun l => (⟨(θ l).map Prod.snd, inferInstance⟩ : ProbabilityMeasure ℝ)) :=
    continuousSumLaw_hasBoundedSupport _ fun l => hasBoundedSupport_snd (hbdd l)
  have hvsum : A * ((2 : ℝ) ^ (-lvl χ.χ₂ t)) ^ 2 ≤ ∑ l, variance id
      ((⟨(θ l).map Prod.snd, inferInstance⟩ : ProbabilityMeasure ℝ) : Measure ℝ) := by
    have e : ∑ l, variance id
        ((⟨(θ l).map Prod.snd, inferInstance⟩ : ProbabilityMeasure ℝ) : Measure ℝ) =
        var₂ (convk k θ) := by
      rw [var₂_convk hbdd]
      exact Finset.sum_congr rfl fun l _ => (var₂_eq_variance_map (θ l)).symm
    rw [e]
    linarith
  have hgrow := hclt k (fun l => ⟨(θ l).map Prod.snd, inferInstance⟩) (fun l => (c l).2) ε⁻¹
    (lvl χ.χ₂ t) hμ (fun l => (hθ l).ae_map_snd_mem_Icc) hwidth hvsum
  rw [← ent_vLabel_convk_eq θ hbdd hμ, ← ent_vLabel_convk_eq θ hbdd hμ] at hgrow
  have hgrow' : (d : ℝ) * Real.log 2 - 1 - 2 * Real.log 7 <
      ent (convk k θ) (χ.E₂ t) - ent (convk k θ) (vLabel (lvl χ.χ₂ t - d)) := hgrow
  -- the planar transfer
  have s1 : cent (convk k θ) (χ.E₂ t) (fun z => (χ.E q z, χ.E₁ t z)) ≤
      cent (convk k θ) (χ.E t) (fun z => (χ.E q z, χ.E₁ t z)) :=
    cent_le_of_factor (χ.measurable_E t) ((χ.measurable_E q).prodMk (χ.measurable_E₁ t))
      (hσ.finiteLabels_E χ t) ((hσ.finiteLabels_E χ q).pair (hσ.finiteLabels_E₁ χ t))
      Prod.snd rfl
  have s2 : cent (convk k θ) (χ.E₂ t) (χ.E q) - ent (convk k θ) (χ.E₁ t) ≤
      cent (convk k θ) (χ.E₂ t) (fun z => (χ.E q z, χ.E₁ t z)) :=
    sub_ent_le_cent_pair (χ.measurable_E₂ t) (χ.measurable_E q) (χ.measurable_E₁ t)
      (hσ.finiteLabels_E₂ χ t) (hσ.finiteLabels_E χ q) (hσ.finiteLabels_E₁ χ t)
  have s3 : cent (convk k θ) (χ.E₂ t) (χ.E₂ q) - ent (convk k θ) (χ.E₁ q) ≤
      cent (convk k θ) (χ.E₂ t) (χ.E q) :=
    sub_ent_le_cent_pair_swap (χ.measurable_E₂ t) (χ.measurable_E₂ q) (χ.measurable_E₁ q)
      (hσ.finiteLabels_E₂ χ t) (hσ.finiteLabels_E₂ χ q) (hσ.finiteLabels_E₁ χ q)
  have s4 : cent (convk k θ) (χ.E₂ t) (vLabel (lvl χ.χ₂ t - d)) ≤
      cent (convk k θ) (χ.E₂ t) (χ.E₂ q) := by
    obtain ⟨ψ, hψ⟩ := vLabel_factor (lvl_sub_le_of_le (α := χ.χ₂) t hdle)
    exact cent_anti_of_factor (χ.measurable_E₂ t) (measurable_vLabel _)
      (hσ.finiteLabels_E₂ χ t) (hσ.finiteLabels_vLabel _) ψ hψ
  have s5 : ent (convk k θ) (χ.E₂ t) - ent (convk k θ) (vLabel (lvl χ.χ₂ t - d)) ≤
      cent (convk k θ) (χ.E₂ t) (vLabel (lvl χ.χ₂ t - d)) :=
    ent_sub_ent_le_cent (χ.measurable_E₂ t) (measurable_vLabel _) (hσ.finiteLabels_E₂ χ t)
      (hσ.finiteLabels_vLabel _)
  have s6 : ent (convk k θ) (χ.E₁ q) ≤ ent (convk k θ) (χ.E₁ t) := by
    obtain ⟨φ, hφ⟩ := hLabel_factor (lvl_mono χ.pos (show q ≤ t by omega))
    exact ent_le_of_factor (χ.measurable_E₁ t) (hσ.finiteLabels_E₁ χ t) φ hφ
  -- the horizontal partition has bounded entropy
  have s7 : ent (convk k θ) (χ.E₁ t) ≤ Real.log 6 + 1 := by
    have hball := inBall_convk_of_forall hθ
    have hb1 : ∀ᵐ z ∂(convk k θ), |z.1 - (∑ l, c l).1| ≤ k * ε⁻¹ :=
      Filter.Eventually.mono hball fun z hz => by
        have h1 := ((norm_le_iff_abs_le _ _).1 hz).1
        rwa [Prod.fst_sub] at h1
    have h := ent_dyadicQuantize_le (X := fun z : ℝ × ℝ => z.1) measurable_fst
      (by positivity) hb1 (lvl χ.χ₁ t)
    have hV0 : 0 ≤ var₁ (convk k θ) := variance_nonneg _ _
    have hVle : var₁ (convk k θ) ≤ ε⁻¹ * (k : ℝ) ^ 0 := by
      rw [pow_zero, mul_one]
      exact hvar₁
    have h' := hcheb (var₁ (convk k θ)) hV0 hVle
    have e : ent (convk k θ) (χ.E₁ t) =
        ent (convk k θ) (fun z => dyadicQuantize (lvl χ.χ₁ t) z.1) := rfl
    rw [e]
    exact h.trans (by unfold var₁ at h'; linarith)
  -- the dyadic step
  have hdl : χ.χ₂ * m - 2 * Real.log 2 ≤ d * Real.log 2 := by
    have hl2 := Real.log_pos one_lt_two
    have h := mul_le_mul_of_nonneg_right hdge hl2.le
    rw [sub_mul, div_mul_cancel₀ _ hl2.ne'] at h
    linarith
  rw [lt_div_iff₀ hmpos]
  unfold sliceConst at hmC
  linarith

end Exps

end Slices

end BoxLike.Rapaport
