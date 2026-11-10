module

/-
The Shannon–McMillan–Breiman theorem for the two-sided shift over a finite alphabet, which
`sec:entropies` cites from Petersen before `thm:feng_entropy_kolmogorov_sinai` (tex lines 1885
to 1977) and the proof of `thm:main2` uses for its typical words (tex lines 3478 to 3485). The
proof is Breiman's (L. Breiman, Ann. Math. Statist. 28 (1957)) and uses no literature input.

For an invariant probability measure `μ` on `ℤ → α`, invariance and the multiplication rule give
`-log μ([x_0 ⋯ x_{n-1}]) = ∑_{k<n} I_k(σ^k x)` almost everywhere, where `I_k` is the information
of the coordinate zero given the last `k` symbols (`BoxLike/SMB/PastInformation.lean`). Chung's
maximal inequality makes `sup_k I_k` integrable, Lévy's upward theorem gives
`I_k → I_μ(𝒫 | 𝒫^-)`, and Maker's theorem (`BoxLike/SMB/Maker.lean`) gives the almost sure limit
`E_μ(I_μ(𝒫 | 𝒫^-) | ℐ)`, the pointwise entropy `h_0(μ, 𝐢)` of the partition by the past. For
ergodic `μ` it is the constant `H_μ(𝒫 | 𝒫^-) = h(μ)` of `BoxLike/PastEntropy.lean`.

* `measurable_condInfo`: the conditional information is Borel.
* `pastCondProb_shift`, `ae_measureReal_cylinder_pos`, `neg_log_cylinder_eq_sum_pastInfo`: the
  multiplication rule along the orbit.
* `tendsto_neg_log_cylinder_localEntropy`: the theorem for every invariant measure, with the
  limit `E_μ(I_μ(𝒫 | \widehat{ξ}) | ℐ)` for the partition `ξ` by the past of any Borel set of full
  measure, the form of Feng's (4.17) for the partition by the past.
* `tendsto_neg_log_cylinder_entropy`, `shannonMcMillanBreiman`: the ergodic theorem, with the
  limit `h(μ)`, and the statement `ShannonMcMillanBreimanStatement` of `BoxLike/SMBStatement.lean`.
* `typicalWords`, `tendsto_measure_block_not_mem_typicalWords`,
  `eventually_measureReal_not_typical_lt`, `eventually_sum_typicalWords`,
  `eventually_measureReal_inter_typical`, `measureReal_inter_typical_le_sum`,
  `card_le_of_subset_typicalWords`, `le_card_of_subset_typicalWords`, `card_typicalWords_le`,
  `le_card_typicalWords`: the interface for typical words, with the cylinders of measure between
  `e^{-n(h+ε)}` and `e^{-n(h-ε)}` carrying almost all the mass, and the cardinality bounds
  `#W ≤ e^{n(h+ε)}` and `#W ≥ μ(⋃_{w ∈ W} [w]) e^{n(h-ε)}` for families of typical words.
-/
public import BoxLike.SMB.Maker
public import BoxLike.SMB.PastInformation
public import BoxLike.SMBStatement
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

namespace BoxLike

open MeasureTheory ProbabilityTheory Filter Topology Set

universe u

section Info

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The conditional information `I_μ(𝒫 | \widehat{ξ})` of `sec:conditional` (tex lines 1652 to
1734) is Borel, for every partition `ξ`. -/
theorem measurable_condInfo (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (ξ : (ℤ → α) → Set (ℤ → α)) : Measurable (condInfo μ ξ) := by
  have h : Measurable fun p : α × (ℤ → α) => (condMeas μ ξ p.2).real {y | y 0 = p.1} :=
    measurable_from_prod_countable_right fun a =>
      ((measurable_condMeas μ ξ (measurableSet_coord_zero_eq a)).mono (saturated_le ξ)
        le_rfl).ennreal_toReal
  have hg : Measurable fun x : ℤ → α => (x 0, x) :=
    (measurable_pi_apply (0 : ℤ)).prodMk measurable_id
  have h2 : Measurable fun x : ℤ → α => (condMeas μ ξ x).real {y | y 0 = x 0} := h.comp hg
  show Measurable fun x => -Real.log ((condMeas μ ξ x).real {y | y 0 = x 0})
  exact (Real.measurable_log.comp h2).neg

end Info

/-! ### The multiplication rule along the orbit -/

section Telescoping

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] {μ : Measure (ℤ → α)}

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The block `x_0 ⋯ x_k` is the block `x_0 ⋯ x_{k-1}` followed by `x_k`. -/
theorem append_block_eq_block_succ (k : ℕ) (x : ℤ → α) :
    Fin.append (block k x) (fun _ : Fin 1 => x k) = block (k + 1) x := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
    simp [block]
  · rw [Fin.append_right]
    simp [block]

/-- For an invariant measure, the conditional probability of the symbol `x_k` given the `k`
symbols before it is `μ([x_0 ⋯ x_k]) / μ([x_0 ⋯ x_{k-1}])`: the conditional probability at
`σ^k x` of the definition `pastCondProb`. -/
theorem pastCondProb_shift (hinv : MeasurePreserving (shift 1) μ μ) (k : ℕ) (x : ℤ → α) :
    pastCondProb μ k (shift k x 0) (shift k x) =
      μ.real (cylinder (block (k + 1) x)) / μ.real (cylinder (block k x)) := by
  rw [pastCondProb, pastBlock_shift, measureReal_inter_pastBlock_preimage hinv,
    measureReal_pastBlock_preimage hinv, shift_apply, add_zero, append_block_eq_block_succ]

variable [Fintype α]

omit [MeasurableSingletonClass α] in
/-- Almost every point lies in no null cylinder: `μ([x_0 ⋯ x_{n-1}]) > 0` for every `n`. -/
theorem ae_measureReal_cylinder_pos [IsFiniteMeasure μ] :
    ∀ᵐ x ∂μ, ∀ n : ℕ, 0 < μ.real (cylinder (block n x)) := by
  have h : ∀ᵐ x ∂μ, ∀ n : ℕ, ∀ w : Fin n → α, μ (cylinder w) = 0 → x ∉ cylinder w :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun w => by
      by_cases hw : μ (cylinder w) = 0
      · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hw] with x hx using fun _ => hx
      · exact ae_of_all _ fun x h => absurd h hw
  filter_upwards [h] with x hx n
  refine ENNReal.toReal_pos (fun h0 => hx n (block n x) h0 fun _ => rfl) (measure_ne_top _ _)

/-- The multiplication rule along the orbit: for an invariant probability measure,
`-log μ([x_0 ⋯ x_{n-1}]) = ∑_{k<n} I_k(σ^k x)` for every `n` and `μ`-almost every `x`, where
`I_k` is the information of the coordinate zero given the last `k` symbols. -/
theorem neg_log_cylinder_eq_sum_pastInfo [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, -Real.log (μ.real (cylinder (block n x))) =
      ∑ k ∈ Finset.range n, pastInfo μ k (shift k x) := by
  filter_upwards [ae_measureReal_cylinder_pos] with x hx n
  have hterm : ∀ k ∈ Finset.range n, pastInfo μ k (shift k x) =
      Real.log (μ.real (cylinder (block k x))) -
        Real.log (μ.real (cylinder (block (k + 1) x))) := fun k _ => by
    rw [pastInfo, pastCondProb_shift hinv,
      Real.log_div (hx (k + 1)).ne' (hx k).ne']
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub' (fun k =>
    Real.log (μ.real (cylinder (block k x))))]
  have h0 : cylinder (block 0 x) = univ := by
    ext y
    simp [cylinder]
  rw [h0, probReal_univ, Real.log_one, zero_sub]

end Telescoping

/-! ### The theorem -/

section SMB

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]

/-- The Shannon–McMillan–Breiman theorem for an invariant, not necessarily ergodic, probability
measure on the two-sided shift over a finite alphabet (Breiman; `sec:entropies`, tex lines 1885
to 1977): for every Borel set `D` of full measure and the partition `ξ` of `D` by the past `𝐢^-`,
extended by the atom `Ω ∖ D`,
`-n⁻¹ log μ([x_0 ⋯ x_{n-1}]) → E_μ(I_μ(𝒫 | \widehat{ξ}) | ℐ)(x)` for `μ`-almost every `x`.
It is the form of Feng's (4.17) (Feng, Duke Math. J. 172 (2023), Lemma 4.6) for the partition by
the past. -/
theorem tendsto_neg_log_cylinder_localEntropy (hinv : MeasurePreserving (shift 1) μ μ)
    {D : Set (ℤ → α)} (hD : MeasurableSet D) (hfull : μ Dᶜ = 0) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => -Real.log (μ.real (cylinder (block n x))) / n) atTop
      (𝓝 (localEntropy μ (atomsOn D fun x => {y | SamePast y x}) x)) := by
  have hM := maker_ae hinv (f := pastInfo μ) (measurable_pastInfo μ) (measurable_condInfo μ _)
    integrable_pastInfoSup abs_pastInfo_le_pastInfoSup (tendsto_pastInfo hD hfull)
  filter_upwards [hM, neg_log_cylinder_eq_sum_pastInfo hinv] with x hx hsum
  refine hx.congr fun n => ?_
  simp only [iterate_shift_one, hsum n, div_eq_inv_mul]

/-- The Shannon–McMillan–Breiman theorem for an ergodic measure on the two-sided shift over a
finite alphabet, which `sec:entropies` cites from Petersen (tex lines 1885 to 1889):
`-n⁻¹ log μ([x_0 ⋯ x_{n-1}]) → h(μ)` for `μ`-almost every `x`, where `h(μ)` is the entropy rate
`entropy μ`. -/
theorem tendsto_neg_log_cylinder_entropy (herg : Ergodic (shift 1) μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => -Real.log (μ.real (cylinder (block n x))) / n) atTop
      (𝓝 (entropy μ)) := by
  have hinv := herg.toMeasurePreserving
  have hfull : μ (univ : Set (ℤ → α))ᶜ = 0 := by simp
  have hc := condEntropy_atomsOn_samePast hinv MeasurableSet.univ hfull
  filter_upwards [tendsto_neg_log_cylinder_localEntropy hinv MeasurableSet.univ hfull,
    localEntropy_ae_eq μ herg (atomsOn univ fun x => {y | SamePast y x})] with x hx hxe
  rwa [hxe, hc] at hx

/-- The Shannon–McMillan–Breiman theorem in the form fixed by `BoxLike/SMBStatement.lean`
(`sec:entropies`, tex lines 1885 to 1889), proved for every finite alphabet in the universe
`u`. -/
theorem shannonMcMillanBreiman : ShannonMcMillanBreimanStatement.{u} := by
  intro α _ _ _ μ _ herg
  exact tendsto_neg_log_cylinder_entropy herg

end SMB

/-! ### Typical words -/

section Typical

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]

open Classical in
/-- The typical words of length `n` for the entropy `h` and the tolerance `ε`: the words `w`
with `e^{-n(h+ε)} ≤ μ([w]) ≤ e^{-n(h-ε)}` (`sec:dimension_result_proof`, tex lines 3478 to
3666). -/
noncomputable def typicalWords (μ : Measure (ℤ → α)) (h ε : ℝ) (n : ℕ) : Finset (Fin n → α) :=
  Finset.univ.filter fun w => Real.exp (-(n * (h + ε))) ≤ μ.real (cylinder w) ∧
    μ.real (cylinder w) ≤ Real.exp (-(n * (h - ε)))

omit [MeasurableSingletonClass α] [IsProbabilityMeasure μ] in
/-- Membership in the typical words, unfolded. -/
theorem mem_typicalWords {h ε : ℝ} {n : ℕ} {w : Fin n → α} :
    w ∈ typicalWords μ h ε n ↔ Real.exp (-(n * (h + ε))) ≤ μ.real (cylinder w) ∧
      μ.real (cylinder w) ≤ Real.exp (-(n * (h - ε))) := by
  classical
  simp [typicalWords]

/-- The Shannon–McMillan–Breiman theorem as convergence in measure for typical words: for an
ergodic measure and every `ε > 0`, the measure of the set of points whose block of length `n` is
not typical tends to zero. -/
theorem tendsto_measure_block_not_mem_typicalWords (herg : Ergodic (shift 1) μ) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun n : ℕ => μ {x | block n x ∉ typicalWords μ (entropy μ) ε n}) atTop (𝓝 0) := by
  set f : ℕ → (ℤ → α) → ℝ := fun n x => -Real.log (μ.real (cylinder (block n x))) / n with hf
  have hfm : ∀ n, Measurable (f n) := fun n =>
    (measurable_of_countable (fun w : Fin n → α => -Real.log (μ.real (cylinder w)) / n)).comp
      (measurable_block n)
  have hconv := (tendstoInMeasure_iff_dist.1 (tendstoInMeasure_of_tendsto_ae (μ := μ)
    (g := fun _ => entropy μ) (fun n => (hfm n).aestronglyMeasurable)
    (tendsto_neg_log_cylinder_entropy herg))) ε hε
  set N : Set (ℤ → α) := {x | ∃ n : ℕ, μ.real (cylinder (block n x)) ≤ 0} with hN
  have hnull : μ N = 0 := by
    rw [← compl_compl N, ← mem_ae_iff]
    filter_upwards [ae_measureReal_cylinder_pos (μ := μ)] with x hx
    simpa [hN] using hx
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hconv
    (Eventually.of_forall fun _ => zero_le) ((eventually_gt_atTop 0).mono fun n hn => ?_)
  calc μ {x | block n x ∉ typicalWords μ (entropy μ) ε n}
      ≤ μ ({x | ε ≤ dist (f n x) (entropy μ)} ∪ N) := measure_mono fun x hx => ?_
    _ ≤ μ {x | ε ≤ dist (f n x) (entropy μ)} + μ N := measure_union_le _ _
    _ = μ {x | ε ≤ dist (f n x) (entropy μ)} := by rw [hnull, add_zero]
  by_contra hcon
  have hd : ¬ ε ≤ dist (f n x) (entropy μ) := fun h => hcon (Or.inl h)
  have hpos : ∀ m : ℕ, 0 < μ.real (cylinder (block m x)) := fun m =>
    lt_of_not_ge fun h => hcon (Or.inr ⟨m, h⟩)
  rw [not_le] at hd
  apply hx
  have hp := hpos n
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  rw [Real.dist_eq, abs_lt, hf] at hd
  obtain ⟨h1, h2⟩ := hd
  have hlog := Real.exp_log hp
  rw [mem_typicalWords]
  constructor
  · rw [← hlog, Real.exp_le_exp]
    have : -Real.log (μ.real (cylinder (block n x))) < n * (entropy μ + ε) := by
      rw [div_sub' hn'.ne', div_lt_iff₀ hn'] at h2
      linarith
    linarith
  · rw [← hlog, Real.exp_le_exp]
    have : n * (entropy μ - ε) < -Real.log (μ.real (cylinder (block n x))) := by
      rw [div_sub' hn'.ne', lt_div_iff₀ hn'] at h1
      linarith
    linarith

/-- The cylinders over typical words carry the measure of the set of points with a typical
block. -/
theorem sum_typicalWords_eq (h ε : ℝ) (n : ℕ) :
    ∑ w ∈ typicalWords μ h ε n, μ.real (cylinder w) =
      μ.real {x | block n x ∈ typicalWords μ h ε n} := by
  have h := sum_measureReal_preimage_singleton (μ := μ) (typicalWords μ h ε n) (f := block n)
    fun w _ => measurable_block n (measurableSet_singleton w)
  refine (Finset.sum_congr rfl fun w _ => by rw [cylinder_eq_preimage]).trans h

/-- For an ergodic measure and all `ε, δ > 0`, the set of points whose block of length `n` is not
typical eventually has measure less than `δ`. -/
theorem eventually_measureReal_not_typical_lt (herg : Ergodic (shift 1) μ) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, μ.real {x | block n x ∉ typicalWords μ (entropy μ) ε n} < δ := by
  have h := tendsto_measure_block_not_mem_typicalWords herg hε
  have hδ' : (0 : ENNReal) < ENNReal.ofReal δ := ENNReal.ofReal_pos.2 hδ
  filter_upwards [(tendsto_order.1 h).2 _ hδ'] with n hn
  rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg measureReal_nonneg, ofReal_measureReal
    (measure_ne_top _ _)]
  exact hn

omit [IsProbabilityMeasure μ] in
/-- The set of points with a typical block of length `n` is Borel. -/
theorem measurableSet_block_mem_typicalWords (h ε : ℝ) (n : ℕ) :
    MeasurableSet {x | block n x ∈ typicalWords μ h ε n} :=
  measurable_block n (Set.toFinite _).measurableSet

/-- The interface of the Shannon–McMillan–Breiman theorem for the typical words of the proof of
`thm:main2` (tex lines 3478 to 3485): for an ergodic measure and all `ε, δ > 0`, the cylinders
of length `n` with measure between `e^{-n(h+ε)}` and `e^{-n(h-ε)}` eventually carry measure at
least `1 - δ`. -/
theorem eventually_sum_typicalWords (herg : Ergodic (shift 1) μ) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, 1 - δ ≤ ∑ w ∈ typicalWords μ (entropy μ) ε n, μ.real (cylinder w) := by
  filter_upwards [eventually_measureReal_not_typical_lt herg hε hδ] with n hc
  rw [sum_typicalWords_eq]
  have hcompl : μ.real {x | block n x ∉ typicalWords μ (entropy μ) ε n} =
      1 - μ.real {x | block n x ∈ typicalWords μ (entropy μ) ε n} := by
    rw [← probReal_compl_eq_one_sub (measurableSet_block_mem_typicalWords _ _ n)]
    rfl
  linarith

/-- The form of the interface for a family of sets: for an ergodic measure and all `ε, δ > 0`,
eventually every Borel set `B` keeps all but `δ` of its measure on the points with a typical
block of length `n`. This is the form in which the typical words are combined with the Birkhoff
and mixing conditions in the proof of `thm:main2` (tex lines 3474 to 3485). -/
theorem eventually_measureReal_inter_typical (herg : Ergodic (shift 1) μ) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ B : Set (ℤ → α), MeasurableSet B →
      μ.real B - δ ≤ μ.real (B ∩ {x | block n x ∈ typicalWords μ (entropy μ) ε n}) := by
  filter_upwards [eventually_measureReal_not_typical_lt herg hε hδ] with n hc B hB
  have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := B)
    (measurableSet_block_mem_typicalWords (μ := μ) (entropy μ) ε n)
  have hdiff : μ.real (B \ {x | block n x ∈ typicalWords μ (entropy μ) ε n}) ≤
      μ.real {x | block n x ∉ typicalWords μ (entropy μ) ε n} :=
    measureReal_mono (fun x hx => hx.2) (measure_ne_top _ _)
  linarith

omit [MeasurableSingletonClass α] in
open Classical in
/-- The typical words whose cylinders meet a set `B` carry at least the measure of the points
of `B` with a typical block. -/
theorem measureReal_inter_typical_le_sum (B : Set (ℤ → α)) (h ε : ℝ) (n : ℕ) :
    μ.real (B ∩ {x | block n x ∈ typicalWords μ h ε n}) ≤
      ∑ w ∈ (typicalWords μ h ε n).filter (fun w => (cylinder w ∩ B).Nonempty),
        μ.real (cylinder w) := by
  refine (measureReal_mono (fun x hx => ?_) (measure_ne_top _ _)).trans
    (measureReal_biUnion_finset_le _ _)
  refine Set.mem_iUnion₂.2 ⟨block n x, Finset.mem_filter.2 ⟨hx.2, x, fun _ => rfl, hx.1⟩, ?_⟩
  exact fun _ => rfl

/-- A family `W` of typical words of length `n` has at most `e^{n(h+ε)}` members
(`sec:dimension_result_proof`, tex lines 3488 to 3489). -/
theorem card_le_of_subset_typicalWords {h ε : ℝ} {n : ℕ} {W : Finset (Fin n → α)}
    (hW : W ⊆ typicalWords μ h ε n) : (W.card : ℝ) ≤ Real.exp (n * (h + ε)) := by
  have hsum : W.card * Real.exp (-(n * (h + ε))) ≤ 1 := by
    calc W.card * Real.exp (-(n * (h + ε)))
        = ∑ _w ∈ W, Real.exp (-(n * (h + ε))) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ w ∈ W, μ.real (cylinder w) :=
          Finset.sum_le_sum fun w hw => (mem_typicalWords.1 (hW hw)).1
      _ ≤ ∑ w : Fin n → α, μ.real (cylinder w) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun _ _ _ => measureReal_nonneg
      _ = 1 := sum_measureReal_cylinder μ n
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)] at hsum
  exact hsum

/-- There are at most `e^{n(h+ε)}` typical words of length `n`. -/
theorem card_typicalWords_le (h ε : ℝ) (n : ℕ) :
    ((typicalWords μ h ε n).card : ℝ) ≤ Real.exp (n * (h + ε)) :=
  card_le_of_subset_typicalWords subset_rfl

omit [MeasurableSingletonClass α] [IsProbabilityMeasure μ] in
/-- A family `W` of typical words of length `n` has at least `e^{n(h-ε)}` times its total mass
members (`sec:dimension_result_proof`, tex lines 3488 to 3489). -/
theorem le_card_of_subset_typicalWords {h ε : ℝ} {n : ℕ} {W : Finset (Fin n → α)}
    (hW : W ⊆ typicalWords μ h ε n) :
    (∑ w ∈ W, μ.real (cylinder w)) * Real.exp (n * (h - ε)) ≤ W.card := by
  have hle : ∑ w ∈ W, μ.real (cylinder w) ≤ W.card * Real.exp (-(n * (h - ε))) := by
    calc ∑ w ∈ W, μ.real (cylinder w)
        ≤ ∑ _w ∈ W, Real.exp (-(n * (h - ε))) :=
          Finset.sum_le_sum fun w hw => (mem_typicalWords.1 (hW hw)).2
      _ = W.card * Real.exp (-(n * (h - ε))) := by rw [Finset.sum_const, nsmul_eq_mul]
  calc (∑ w ∈ W, μ.real (cylinder w)) * Real.exp (n * (h - ε))
      ≤ W.card * Real.exp (-(n * (h - ε))) * Real.exp (n * (h - ε)) :=
        mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
    _ = W.card := by rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

omit [MeasurableSingletonClass α] [IsProbabilityMeasure μ] in
/-- The typical words of length `n` number at least `e^{n(h-ε)}` times their total mass. -/
theorem le_card_typicalWords (h ε : ℝ) (n : ℕ) :
    (∑ w ∈ typicalWords μ h ε n, μ.real (cylinder w)) * Real.exp (n * (h - ε)) ≤
      (typicalWords μ h ε n).card :=
  le_card_of_subset_typicalWords subset_rfl

end Typical

end BoxLike
