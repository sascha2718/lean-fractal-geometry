module

/-
Auxiliary results for Proposition 1.7 of Rapaport (arXiv:2309.03985v1, lines 1075 to 1188 of the
source) for `d = 2`, which is proved in `Rapaport/Entropy/Proposition.lean`.

* The weak law of large numbers for the binomial count (lines 1120 to 1126):
  `sum_prod_weight_eq_one`, `sum_prod_mul_sum_sq`, `sum_prod_count_lt_le`.
* Concavity over the tuples of components (lines 1168 to 1178): `le_cent_convPow_of_tuples`.
* One tuple of components (lines 1128 to 1166): `propConst`, `propConst_nonneg`,
  `Exps.CoordLab`, `Exps.coordLab_E₁`, `Exps.coordLab_E₂`, `Exps.cent_map_resc_le`,
  `Exps.exists_convk_eq_conv_of_equiv`, `Exps.cent_convk_ge_of_sub`.
* One level `b` (lines 1116 to 1178): `Exps.exists_weight_le_cent_convPow`.
* The shift of the levels (lines 1180 to 1186): `card_sub_abs_le_card_of_shift`.
* One direction `j` (lines 1112 to 1186): `Exps.card_levels_gt`.
-/
public import BoxLike.Rapaport.Entropy.Slices

@[expose] public section

namespace BoxLike.Rapaport

open MeasureTheory ProbabilityTheory
open scoped ENNReal

section Binomial

variable {β : Type*} [Fintype β]

/-- A sum over `(K+1)`-tuples splits into the first entry and the remaining `K`-tuple (the
induction behind the weak law of large numbers of lines 1125 to 1126 of the source). -/
private theorem sum_pi_fin_succ {M : Type*} [AddCommMonoid M] (K : ℕ)
    (F : (Fin (K + 1) → β) → M) :
    ∑ t : Fin (K + 1) → β, F t = ∑ b : β, ∑ t : Fin K → β, F (Fin.cons b t) := by
  rw [← (Fin.consEquiv fun _ => β).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The product weights `∏ p (t i)` on `K`-tuples sum to `1`: `θ^{×k_j}` is a probability
measure (line 1126 of the source). -/
theorem sum_prod_weight_eq_one (p : β → ℝ) (hp1 : ∑ b, p b = 1) (K : ℕ) :
    ∑ t : Fin K → β, ∏ i, p (t i) = 1 := by
  rw [← Fintype.sum_pow, hp1, one_pow]

/-- The variance of a sum of `K` independent copies (the weak law of large numbers, lines 1125 to
1126 of the source): for `p` a probability vector and `d` of mean zero under `p`,
`∑_t (∏ p (t i)) (∑_i d (t i))² = K ∑_b p b d b²`. -/
theorem sum_prod_mul_sum_sq (p d : β → ℝ) (hp1 : ∑ b, p b = 1) (hd : ∑ b, p b * d b = 0) :
    ∀ K : ℕ, ∑ t : Fin K → β, (∏ i, p (t i)) * (∑ i, d (t i)) ^ 2 =
      K * ∑ b, p b * d b ^ 2
  | 0 => by simp
  | K + 1 => by
    rw [sum_pi_fin_succ]
    have ih := sum_prod_mul_sum_sq p d hp1 hd K
    have h1 := sum_prod_weight_eq_one p hp1 K
    have e : ∀ (b : β) (t : Fin K → β),
        (∏ i, p ((Fin.cons b t : Fin (K + 1) → β) i)) *
          (∑ i, d ((Fin.cons b t : Fin (K + 1) → β) i)) ^ 2 =
        p b * d b ^ 2 * ∏ i, p (t i) + 2 * (p b * d b) * ((∏ i, p (t i)) * ∑ i, d (t i)) +
          p b * ((∏ i, p (t i)) * (∑ i, d (t i)) ^ 2) := by
      intro b t
      rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      ring
    simp_rw [e]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, h1, ih, hd, hp1]
    push_cast
    ring

/-- Chebyshev's inequality for the binomial count (the weak law of large numbers in the proof of
Proposition 1.7 of the source, lines 1125 to 1126): under the product weights `∏ p (t i)` on
`K`-tuples, the tuples with fewer than `r ≤ K P / 2` entries in `g`, where `P` is the mass of `g`,
carry mass at most `4 / (K P)`. -/
theorem sum_prod_count_lt_le (p : β → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∑ b, p b = 1)
    (g : β → Prop) [DecidablePred g] {K : ℕ} (hK : 0 < K) {r : ℝ}
    (hP : 0 < ∑ b, if g b then p b else 0)
    (hr : r ≤ K * (∑ b, if g b then p b else 0) / 2) :
    ∑ t ∈ Finset.univ.filter (fun t : Fin K → β =>
        ((Finset.univ.filter fun i => g (t i)).card : ℝ) < r), ∏ i, p (t i) ≤
      4 / (K * ∑ b, if g b then p b else 0) := by
  set P := ∑ b, if g b then p b else 0 with hPdef
  set ind : β → ℝ := fun b => if g b then 1 else 0 with hind
  set d : β → ℝ := fun b => ind b - P with hd
  have hpind : ∑ b, p b * ind b = P := by
    rw [hPdef]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hind]
    split_ifs <;> simp
  have hd0 : ∑ b, p b * d b = 0 := by
    simp only [hd, mul_sub, Finset.sum_sub_distrib, hpind, ← Finset.sum_mul, hp1, one_mul,
      sub_self]
  have hd2 : ∑ b, p b * d b ^ 2 = P - P ^ 2 := by
    have e : ∀ b, p b * d b ^ 2 = (1 - 2 * P) * (p b * ind b) + P ^ 2 * p b := by
      intro b
      simp only [hd, hind]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hpind, hp1]
    ring
  have hvar := sum_prod_mul_sum_sq p d hp1 hd0 K
  rw [hd2] at hvar
  have hcount : ∀ t : Fin K → β,
      ((Finset.univ.filter fun i => g (t i)).card : ℝ) - K * P = ∑ i, d (t i) := by
    intro t
    rw [Finset.natCast_card_filter]
    simp only [hd, hind, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hKP : 0 < (K : ℝ) * P := mul_pos (by exact_mod_cast hK) hP
  set S := ∑ t ∈ Finset.univ.filter (fun t : Fin K → β =>
    ((Finset.univ.filter fun i => g (t i)).card : ℝ) < r), ∏ i, p (t i) with hS
  have hmain : ((K : ℝ) * P / 2) ^ 2 * S ≤ K * (P - P ^ 2) := by
    rw [hS, Finset.mul_sum, ← hvar]
    calc _ ≤ ∑ t ∈ Finset.univ.filter (fun t : Fin K → β =>
            ((Finset.univ.filter fun i => g (t i)).card : ℝ) < r),
            (∏ i, p (t i)) * (∑ i, d (t i)) ^ 2 := by
          refine Finset.sum_le_sum fun t ht => ?_
          rw [Finset.mem_filter] at ht
          rw [← hcount t, mul_comm]
          refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun i _ => hp0 _)
          have h1 : (K : ℝ) * P / 2 ≤
              K * P - (Finset.univ.filter fun i => g (t i)).card := by linarith [ht.2]
          have h2 : 0 ≤ (K : ℝ) * P / 2 := by positivity
          nlinarith
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun t _ _ => mul_nonneg (Finset.prod_nonneg fun i _ => hp0 _) (sq_nonneg _)
  have hle : (K : ℝ) * (P - P ^ 2) ≤ K * P := by
    have : (0 : ℝ) ≤ K * P ^ 2 := by positivity
    nlinarith
  rw [le_div_iff₀ hKP]
  have h3 : (K * P) * (S * (K * P)) ≤ (K * P) * 4 := by nlinarith
  exact le_of_mul_le_mul_left h3 hKP

end Binomial

/-! ### Averaging over tuples of components -/

section Tuples

variable {L L₁ L₂ : Type*} [MeasurableSpace L] [MeasurableSingletonClass L] [Countable L]
variable [MeasurableSpace L₁] [MeasurableSingletonClass L₁] [Countable L₁]
variable [MeasurableSpace L₂] [MeasurableSingletonClass L₂] [Countable L₂]

/-- The concavity step of the proof of Proposition 1.7 of the source (lines 1168 to 1178): in the
decomposition `θ^{∗K} = ∑_t (∏_i θ(f = t_i)) θ_{f = t_0} ∗ ⋯ ∗ θ_{f = t_{K-1}}`, a lower bound
`a` on `H(·, F ∣ G)` over a set `Z` of tuples gives `H(θ^{∗K}, F ∣ G) ≥ θ^{×K}(Z) a`; the other
tuples contribute nonnegatively. -/
theorem le_cent_convPow_of_tuples {θ : Measure (ℝ × ℝ)} [IsProbabilityMeasure θ]
    (hθ : BddSupp θ) {f : ℝ × ℝ → L} (hf : Measurable f) (hfin : FiniteLabels θ f) (K : ℕ)
    {F : ℝ × ℝ → L₁} {G : ℝ × ℝ → L₂} (hF : Measurable F) (hG : Measurable G)
    (hFb : BallFinite F) (hGb : BallFinite G) (Z : Finset (Fin K → hfin.toFinset)) {a : ℝ}
    (hZ : ∀ t ∈ Z, a ≤ cent (convk K fun i => comp θ f (t i : L)) F G) :
    (∑ t ∈ Z, ∏ i, θ.real (f ⁻¹' {(t i : L)})) * a ≤ cent (convPow θ K) F G := by
  have hc : ∀ (t : Fin K → hfin.toFinset) i, IsProbabilityMeasure (comp θ f (t i : L)) :=
    fun t i => comp_isProbabilityMeasure (hfin.mem_toFinset.1 (t i).2)
  have hθs : ∀ t : Fin K → hfin.toFinset,
      IsProbabilityMeasure (convk K fun i => comp θ f (t i : L)) :=
    fun t => isProbabilityMeasure_convk K _
  have hbs : ∀ t : Fin K → hfin.toFinset, BddSupp (convk K fun i => comp θ f (t i : L)) :=
    fun t => BddSupp.convk fun i => hθ.cond _
  have hw0 : ∀ t : Fin K → hfin.toFinset, 0 ≤ ∏ i, θ.real (f ⁻¹' {(t i : L)}) :=
    fun t => Finset.prod_nonneg fun i _ => measureReal_nonneg
  have hmix := sum_cent_le_cent
    (θs := fun t : Fin K → hfin.toFinset => convk K fun i => comp θ f (t i : L)) hw0
    (sum_prod_measureReal_fiber hf hfin K) (convPow_eq_sum_comp hf hfin K) hF hG
    (hFb.finiteLabels (hθ.convPow K)) (hGb.finiteLabels (hθ.convPow K))
  refine le_trans ?_ hmix
  rw [Finset.sum_mul]
  calc ∑ t ∈ Z, (∏ i, θ.real (f ⁻¹' {(t i : L)})) * a ≤
        ∑ t ∈ Z, (∏ i, θ.real (f ⁻¹' {(t i : L)})) *
          cent (convk K fun i => comp θ f (t i : L)) F G :=
        Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left (hZ t ht) (hw0 t)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun t _ _ =>
        mul_nonneg (hw0 t) (cent_nonneg hF hG (hFb.finiteLabels (hbs t))
          (hGb.finiteLabels (hbs t)))

end Tuples

/-! ### One tuple: the good components and the rest -/

/-- The constant lost by one tuple of components in the proof of Proposition 1.7 of the source:
`log 4 + 2 log 8` when the remaining components enter by convolution ((2.5), lines 1155 to 1162)
and `log 9 + 2 log 27` when the rescaling by `A_χ^b` is undone ((2.6), lines 1163 to 1166). -/
noncomputable def propConst : ℝ :=
  Real.log 4 + 2 * Real.log 8 + (Real.log 9 + 2 * Real.log 27)

/-- The constant `propConst` of the proof of Proposition 1.7 of the source is nonnegative. -/
theorem propConst_nonneg : 0 ≤ propConst := by
  have h4 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
  have h8 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)
  have h9 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 9)
  have h27 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 27)
  unfold propConst
  linarith

namespace Exps

variable (χ : Exps)

/-- The properties of a coordinate partition `H n` (`π₁⁻¹ ℰ_n` or `π₂⁻¹ ℰ_n`, the partition
`π_{[d] ∖ {j}}⁻¹ ℰ` of Proposition 1.7 of the source for `d = 2`) used in the proof of that
proposition: measurability, finiteness on balls, the translation count (2.5) and the scaling
count (2.6) by `A_χ^b`. -/
structure CoordLab (H : ℤ → ℝ × ℝ → ℤ) : Prop where
  /-- Every `H n` is measurable. -/
  meas : ∀ n, Measurable (H n)
  /-- Every ball meets finitely many cells of `H n`. -/
  ballFinite : ∀ n, BallFinite (H n)
  /-- A cell of a translate of `H n` meets at most `2` cells of `H n`. -/
  translate : ∀ n y, FiberBound (H n ∘ (· + y)) (H n) 2
  /-- A cell of `H n` meets at most `2` cells of a translate of `H n`. -/
  translate_symm : ∀ n y, FiberBound (H n) (H n ∘ (· + y)) 2
  /-- A cell of `H n ∘ A_χ^b` meets at most `3` cells of `H (b + n)`. -/
  resc : ∀ b n, FiberBound (H n ∘ χ.resc b) (H (b + n)) 3
  /-- A cell of `H (b + n)` meets at most `3` cells of `H n ∘ A_χ^b`. -/
  resc_symm : ∀ b n, FiberBound (H (b + n)) (H n ∘ χ.resc b) 3

/-- The partitions `π₁⁻¹ ℰ_n` satisfy `CoordLab`: (2.5) and (2.6) of the source (lines 756 to
763) in the first coordinate, used for the sets `Q₂` of Proposition 1.7. -/
theorem coordLab_E₁ : χ.CoordLab χ.E₁ where
  meas := χ.measurable_E₁
  ballFinite := χ.ballFinite_E₁
  translate n y := fiberBound_hLabel_translate _ y
  translate_symm n y := fiberBound_hLabel_translate_symm _ y
  resc b n := by
    have h := χ.fiberBound_E₁_resc_neg (-b) (b + n)
    rwa [neg_add_cancel_left, neg_neg] at h
  resc_symm b n := by
    have h := χ.fiberBound_E₁_resc_neg_symm (-b) (b + n)
    rwa [neg_add_cancel_left, neg_neg] at h

/-- The partitions `π₂⁻¹ ℰ_n` satisfy `CoordLab`: (2.5) and (2.6) of the source (lines 756 to
763) in the second coordinate, used for the sets `Q₁` of Proposition 1.7. -/
theorem coordLab_E₂ : χ.CoordLab χ.E₂ where
  meas := χ.measurable_E₂
  ballFinite := χ.ballFinite_E₂
  translate n y := fiberBound_vLabel_translate _ y
  translate_symm n y := fiberBound_vLabel_translate_symm _ y
  resc b n := by
    have h := χ.fiberBound_E₂_resc_neg (-b) (b + n)
    rwa [neg_add_cancel_left, neg_neg] at h
  resc_symm b n := by
    have h := χ.fiberBound_E₂_resc_neg_symm (-b) (b + n)
    rwa [neg_add_cancel_left, neg_neg] at h

variable {χ}

/-- Undoing the rescaling (2.6) of the source for `H(·, ℰ_{n+m} ∣ ℰ_n ∨ H_{n+m})`:
`H(A_χ^b σ, ℰ_{n+m} ∣ ℰ_n ∨ H_{n+m}) ≤ H(σ, ℰ_{b+n+m} ∣ ℰ_{b+n} ∨ H_{b+n+m}) + log 9 + 2 log 27`
for `σ` of bounded support (lines 1163 to 1166). -/
theorem cent_map_resc_le {H : ℤ → ℝ × ℝ → ℤ} (hH : χ.CoordLab H) {σ : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure σ] (hσ : BddSupp σ) (b n m : ℤ) :
    cent (σ.map (χ.resc b)) (χ.E (n + m)) (fun z => (χ.E n z, H (n + m) z)) ≤
      cent σ (χ.E (b + n + m)) (fun z => (χ.E (b + n) z, H (b + n + m) z)) +
        (Real.log 9 + 2 * Real.log 27) := by
  have hψ := χ.measurable_resc b
  have hg : Measurable fun z => (χ.E n z, H (n + m) z) :=
    (χ.measurable_E _).prodMk (hH.meas _)
  have hg' : Measurable fun z => (χ.E (b + n) z, H (b + n + m) z) :=
    (χ.measurable_E _).prodMk (hH.meas _)
  have hbm : BddSupp (σ.map (χ.resc b)) := hσ.map_diagMap _ _
  rw [cent_map hψ (χ.measurable_E _) hg]
  have hfinf : FiniteLabels σ (χ.E (n + m) ∘ χ.resc b) :=
    (finiteLabels_map_iff hψ (χ.measurable_E _)).1 (hbm.finiteLabels_E χ _)
  have hfing : FiniteLabels σ ((fun z => (χ.E n z, H (n + m) z)) ∘ χ.resc b) :=
    (finiteLabels_map_iff hψ hg).1 (((χ.ballFinite_E _).pair (hH.ballFinite _)).finiteLabels hbm)
  have hfing' : FiniteLabels σ fun z => (χ.E (b + n) z, H (b + n + m) z) :=
    ((χ.ballFinite_E _).pair (hH.ballFinite _)).finiteLabels hσ
  have hfinf' : FiniteLabels σ (χ.E (b + n + m)) := hσ.finiteLabels_E χ _
  have hs1 := hH.resc_symm b (n + m)
  have hs2 := hH.resc b (n + m)
  rw [← add_assoc] at hs1 hs2
  have h₂ : FiberBound (fun z => (χ.E (b + n) z, H (b + n + m) z))
      ((fun z => (χ.E n z, H (n + m) z)) ∘ χ.resc b) (9 * 3) :=
    (χ.fiberBound_E_resc_symm b n).prod hs1
  have h₃ : FiberBound ((fun z => (χ.E n z, H (n + m) z)) ∘ χ.resc b)
      (fun z => (χ.E (b + n) z, H (b + n + m) z)) (9 * 3) :=
    (χ.fiberBound_E_resc b n).prod hs2
  have hE := χ.fiberBound_E_resc_symm b (n + m)
  rw [← add_assoc] at hE
  have e₁ := cent_le_cent_add_two_log_of_commensurable_cond ((χ.measurable_E _).comp hψ)
    (hg.comp hψ) hg' hfinf hfing hfing' h₂ h₃
  have e₂ := cent_le_cent_add_log_of_fiber_card ((χ.measurable_E _).comp hψ)
    (χ.measurable_E (b + n + m)) hg' hfinf hfinf' hfing'
    (FiberBound.of_refine_left
      (f := fun x => (χ.E (b + n + m) x, (χ.E (b + n) x, H (b + n + m) x)))
      (f' := χ.E (b + n + m)) (φ := Prod.fst) rfl hE)
  norm_num at e₁ e₂ ⊢
  linarith

/-- Splitting `θ_0 ∗ ⋯ ∗ θ_{K-1}` into the convolution of the factors indexed by `G`, enumerated
by `e`, and a bounded probability measure `τ`, the convolution of the remaining factors (the
measures `σ` and `∗_{s=1}^{k_j} A_χ^b θ_{x_s,b}` of lines 1134 to 1162 of the source). -/
theorem exists_convk_eq_conv_of_equiv {K k : ℕ} (θ : Fin K → Measure (ℝ × ℝ))
    [∀ i, IsProbabilityMeasure (θ i)] (hθ : ∀ i, BddSupp (θ i)) (G : Finset (Fin K))
    (e : Fin k ≃ G) :
    ∃ τ : Measure (ℝ × ℝ), IsProbabilityMeasure τ ∧ BddSupp τ ∧
      convk K θ = (convk k fun l => θ (e l)) ∗ τ := by
  classical
  refine ⟨convFam fun i : {i // ¬ (· ∈ G) i} => θ i, inferInstance,
    BddSupp.convFam fun i => hθ _, ?_⟩
  rw [convk_split θ (· ∈ G)]
  congr 1
  rw [convk_eq_convFam]
  convert (convFam_comp_equiv (fun i : {i // (· ∈ G) i} => θ i) e).symm using 2

/-- One tuple of components in the proof of Proposition 1.7 of the source (lines 1128 to 1166):
for probability measures `ρ_0, …, ρ_{K-1}` of bounded support and a set `G` of indices, enumerated
by `e`, the convolution `σ` of the rescaled measures `A_χ^b ρ_i`, `i ∈ G`, bounds the convolution of
all of them: `H(ρ_0 ∗ ⋯ ∗ ρ_{K-1}, ℰ_{b+n+m} ∣ ℰ_{b+n} ∨ H_{b+n+m}) ≥
H(σ, ℰ_{n+m} ∣ ℰ_n ∨ H_{n+m}) - propConst`. -/
theorem cent_convk_ge_of_sub {H : ℤ → ℝ × ℝ → ℤ} (hH : χ.CoordLab H) {K k : ℕ}
    (ρ : Fin K → Measure (ℝ × ℝ)) [∀ i, IsProbabilityMeasure (ρ i)] (hρ : ∀ i, BddSupp (ρ i))
    (G : Finset (Fin K)) (e : Fin k ≃ G) (b n m : ℤ) :
    cent (convk k fun l => (ρ (e l)).map (χ.resc b)) (χ.E (n + m))
        (fun z => (χ.E n z, H (n + m) z)) - propConst ≤
      cent (convk K ρ) (χ.E (b + n + m)) (fun z => (χ.E (b + n) z, H (b + n + m) z)) := by
  have hb : ∀ i, BddSupp ((ρ i).map (χ.resc b)) := fun i => (hρ i).map_diagMap _ _
  have h1 : (convk K ρ).map (χ.resc b) = convk K fun i => (ρ i).map (χ.resc b) :=
    map_diagMap_convk _ _ K ρ
  obtain ⟨τ, hτp, hτ, h2⟩ := exists_convk_eq_conv_of_equiv (fun i => (ρ i).map (χ.resc b)) hb G e
  have hσ : BddSupp (convk k fun l => (ρ (e l)).map (χ.resc b)) :=
    BddSupp.convk fun l => hb _
  have hconv := cent_conv_ge_of_fiberBound hσ hτ (f := χ.E (n + m))
    (g := fun z => (χ.E n z, H (n + m) z)) (χ.measurable_E _)
    ((χ.measurable_E _).prodMk (hH.meas _)) (χ.ballFinite_E _)
    ((χ.ballFinite_E _).pair (hH.ballFinite _)) (N := 4) (N' := 4 * 2)
    (fun y => fiberBound_rect_translate _ _ y)
    (fun y => (fiberBound_rect_translate _ _ y).prod (hH.translate _ y))
    (fun y => (fiberBound_rect_translate_symm _ _ y).prod (hH.translate_symm _ y))
  rw [← h2, ← h1] at hconv
  have hres := cent_map_resc_le hH (BddSupp.convk hρ) b n m
  unfold propConst
  norm_num at hconv ⊢
  linarith

/-- One level `b` of the proof of Proposition 1.7 of the source (lines 1116 to 1178). Let `P` be
the mass of the components `θ_{x,b}` of `θ` at level `b` whose rescaling `A_χ^b θ_{x,b}` is
`good`, and let `k ≤ K P / 2`. If every convolution of `k` good measures carried by unit balls
has `H(·, ℰ_{q+m} ∣ ℰ_q ∨ H_{q+m}) ≥ a` (Lemma 3.2 at the level `q`), then for some weight
`W ≥ 1 - 4 / (K P)` (the mass of the tuples with at least `k` good entries, by Chebyshev),
`H(θ^{∗K}, ℰ_{b+q+m} ∣ ℰ_{b+q} ∨ H_{b+q+m}) ≥ W (a - propConst)`. -/
theorem exists_weight_le_cent_convPow {H : ℤ → ℝ × ℝ → ℤ} (hH : χ.CoordLab H)
    {θ : Measure (ℝ × ℝ)} [IsProbabilityMeasure θ] (hθ : BddSupp θ) (b q m : ℤ) {K k : ℕ}
    (hK : 0 < K) (good : Measure (ℝ × ℝ) → Prop) [DecidablePred good] {a : ℝ}
    (hP : 0 < cavg θ (χ.E b) fun ρ => if good (ρ.map (χ.resc b)) then 1 else 0)
    (hk : (k : ℝ) ≤
      K * (cavg θ (χ.E b) fun ρ => if good (ρ.map (χ.resc b)) then 1 else 0) / 2)
    (hslice : ∀ (θ' : Fin k → Measure (ℝ × ℝ)) [∀ i, IsProbabilityMeasure (θ' i)],
      (∀ i, ∃ z, InBall (θ' i) z 1) → (∀ i, good (θ' i)) →
        a ≤ cent (convk k θ') (χ.E (q + m)) (fun z => (χ.E q z, H (q + m) z))) :
    ∃ W : ℝ,
      1 - 4 / (K * cavg θ (χ.E b) fun ρ => if good (ρ.map (χ.resc b)) then 1 else 0) ≤ W ∧
      W ≤ 1 ∧ W * (a - propConst) ≤
        cent (convPow θ K) (χ.E (b + q + m)) (fun z => (χ.E (b + q) z, H (b + q + m) z)) := by
  classical
  have hf : Measurable (χ.E b) := χ.measurable_E b
  have hfin : FiniteLabels θ (χ.E b) := hθ.finiteLabels_E χ b
  set p : hfin.toFinset → ℝ := fun c => θ.real (χ.E b ⁻¹' {(c : ℤ × ℤ)}) with hp
  have hp0 : ∀ c, 0 ≤ p c := fun c => measureReal_nonneg
  have hp1 : ∑ c, p c = 1 := by
    rw [Finset.sum_coe_sort hfin.toFinset (fun c => θ.real (χ.E b ⁻¹' {c})),
      sum_measureReal_fiber hf _ fun _ hc => hfin.mem_toFinset.2 hc]
  set g : hfin.toFinset → Prop := fun c => good ((comp θ (χ.E b) (c : ℤ × ℤ)).map (χ.resc b))
    with hg
  have hPeq : (cavg θ (χ.E b) fun ρ => if good (ρ.map (χ.resc b)) then 1 else 0) =
      ∑ c, if g c then p c else 0 := by
    rw [cavg_eq_sum hfin, ← Finset.sum_coe_sort hfin.toFinset]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [hg, hp]
    split_ifs <;> simp
  rw [hPeq] at hP hk ⊢
  set Z := Finset.univ.filter fun t : Fin K → hfin.toFinset =>
    k ≤ (Finset.univ.filter fun i => g (t i)).card with hZ
  refine ⟨∑ t ∈ Z, ∏ i, p (t i), ?_, ?_, ?_⟩
  · have hsplit := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (Fin K → hfin.toFinset))
      (fun t => k ≤ (Finset.univ.filter fun i => g (t i)).card) (fun t => ∏ i, p (t i))
    rw [sum_prod_weight_eq_one p hp1] at hsplit
    have hbad := sum_prod_count_lt_le p hp0 hp1 g hK hP hk
    have hfeq : Finset.univ.filter (fun t : Fin K → hfin.toFinset =>
        ¬ k ≤ (Finset.univ.filter fun i => g (t i)).card) =
        Finset.univ.filter (fun t => ((Finset.univ.filter fun i => g (t i)).card : ℝ) < k) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le, Nat.cast_lt]
    rw [hfeq] at hsplit
    linarith
  · have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun t => ∏ i, p (t i))
      (Finset.subset_univ Z) (fun t _ _ => Finset.prod_nonneg fun i _ => hp0 (t i))
    rwa [sum_prod_weight_eq_one p hp1] at h
  · refine le_cent_convPow_of_tuples hθ hf hfin K (χ.measurable_E _)
      ((χ.measurable_E _).prodMk (hH.meas _)) (χ.ballFinite_E _)
      ((χ.ballFinite_E _).pair (hH.ballFinite _)) Z fun t ht => ?_
    rw [hZ, Finset.mem_filter] at ht
    obtain ⟨G, hGsub, hGcard⟩ := Finset.exists_subset_card_eq ht.2
    let e : Fin k ≃ G := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hGcard])).symm
    have hc : ∀ i, IsProbabilityMeasure (comp θ (χ.E b) (t i : ℤ × ℤ)) := fun i =>
      comp_isProbabilityMeasure (hfin.mem_toFinset.1 (t i).2)
    have h1 := cent_convk_ge_of_sub hH (fun i => comp θ (χ.E b) (t i : ℤ × ℤ))
      (fun i => hθ.cond _) G e b q m
    have h2 := hslice (fun l => (comp θ (χ.E b) (t (e l) : ℤ × ℤ)).map (χ.resc b))
      (fun l => exists_inBall_map_resc_comp χ θ b _) fun l => by
        have h := hGsub (e l).2
        rw [Finset.mem_filter] at h
        exact h.2
    linarith

end Exps

/-! ### Shifting the levels -/

/-- Shifting a set of levels by `q` (the last step of the proof of Proposition 1.7 of the source,
lines 1180 to 1186): if `B ⊆ [0, n)` and every `i ∈ B` with `i + q ∈ [0, n)` has `i + q ∈ Q`,
then `#Q ≥ #B - |q|`. -/
theorem card_sub_abs_le_card_of_shift {n : ℕ} {B Q : Finset ℕ} (hB : B ⊆ Finset.range n)
    (q : ℤ) (hQ : ∀ i ∈ B, ∀ i' : ℕ, i' < n → (i' : ℤ) = i + q → i' ∈ Q) :
    (B.card : ℝ) - |(q : ℝ)| ≤ Q.card := by
  classical
  have h1 : (B.filter fun i : ℕ => 0 ≤ (i : ℤ) + q ∧ (i : ℤ) + q < n).card ≤ Q.card := by
    refine Finset.card_le_card_of_injOn (fun i : ℕ => ((i : ℤ) + q).toNat) (fun i hi => ?_)
      (fun i hi j hj hij => ?_)
    · rw [Finset.mem_coe, Finset.mem_filter] at hi
      exact hQ i hi.1 _ (by simp only; omega) (by simp only; omega)
    · rw [Finset.mem_coe, Finset.mem_filter] at hi hj
      simp only at hij
      omega
  have h2 : (B.filter fun i : ℕ => ¬ (0 ≤ (i : ℤ) + q ∧ (i : ℤ) + q < n)).card ≤ q.natAbs := by
    have hsub : (B.filter fun i : ℕ => ¬ (0 ≤ (i : ℤ) + q ∧ (i : ℤ) + q < n)) ⊆
        Finset.Ico (n - q.toNat) n ∪ Finset.range (-q).toNat := by
      intro i hi
      rw [Finset.mem_filter] at hi
      have := Finset.mem_range.1 (hB hi.1)
      rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_range]
      omega
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    rw [Nat.card_Ico, Finset.card_range]
    omega
  have h3 := Finset.card_filter_add_card_filter_not (s := B)
    (fun i : ℕ => 0 ≤ (i : ℤ) + q ∧ (i : ℤ) + q < n)
  have h4 : (q.natAbs : ℝ) = |(q : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have h5 : (B.card : ℝ) ≤ Q.card + q.natAbs := by exact_mod_cast (by omega)
  linarith

/-! ### One direction -/

namespace Exps

variable {χ : Exps}

/-- One direction `j` of the proof of Proposition 1.7 of the source (lines 1112 to 1186), with
`x = χ_j` and `H = π_{j'}⁻¹ ℰ`: if more than `δ₀ n / 2` levels `b ∈ [1, n]` have components of
mass `> δ₀ / 2` whose rescaling `A_χ^b θ_{x,b}` is `good`, and convolutions of `k ≤ δ₀ K / 4`
good measures carried by unit balls satisfy Lemma 3.2 at the level `q`, then more than `δ₀ n / 4`
levels `q' ∈ [1, n]` have `H(θ^{∗K}, ℰ_{q'+m} ∣ ℰ_{q'} ∨ H_{q'+m}) / m > x - ε`. Here
`K > 32 χ₂ / (δ₀ ε)` makes the tuples with fewer than `k` good entries negligible, `m > 2
propConst / ε` absorbs the constant of one tuple, and `n ≥ 4 |q| / δ₀` absorbs the shift. -/
theorem card_levels_gt {H : ℤ → ℝ × ℝ → ℤ} (hH : χ.CoordLab H) {θ : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure θ] (hθ : BddSupp θ) (good : Measure (ℝ × ℝ) → Prop)
    [DecidablePred good] {x ε ε' δ₀ : ℝ} (hx : 0 ≤ x) (hxχ : x ≤ χ.χ₂) (hε : 0 < ε)
    (hε' : 0 ≤ ε') (hε'ε : ε' ≤ ε / 4) (hδ₀ : 0 < δ₀) {m K k : ℕ}
    (hm : 2 * propConst / ε < m) (hK : 32 * χ.χ₂ / (δ₀ * ε) < K) (hk : (k : ℝ) ≤ δ₀ * K / 4)
    {q : ℤ} (hslice : ∀ (θ' : Fin k → Measure (ℝ × ℝ)) [∀ i, IsProbabilityMeasure (θ' i)],
      (∀ i, ∃ z, InBall (θ' i) z 1) → (∀ i, good (θ' i)) →
        (x - ε') * m ≤ cent (convk k θ') (χ.E (q + m)) (fun z => (χ.E q z, H (q + m) z)))
    {n : ℕ} (hn : 4 * |(q : ℝ)| / δ₀ ≤ n)
    (hB : δ₀ / 2 * n < (((Finset.range n).filter fun i => δ₀ / 2 <
      cavg θ (χ.E ((i + 1 : ℕ) : ℤ)) fun ρ =>
        if good (ρ.map (χ.resc ((i + 1 : ℕ) : ℤ))) then 1 else 0).card : ℝ)) :
    δ₀ / 4 * n < (((Finset.range n).filter fun i =>
      x - ε < cent (convPow θ K) (χ.E ((i + 1 + m : ℕ) : ℤ))
        (fun z => (χ.E ((i + 1 : ℕ) : ℤ) z, H ((i + 1 + m : ℕ) : ℤ) z)) / m).card : ℝ) := by
  have hC := propConst_nonneg
  have hχ₂ := χ.pos₂
  have hm0 : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
  have hK0 : (0 : ℝ) < K := lt_of_le_of_lt (by positivity) hK
  have hK0' : 0 < K := by exact_mod_cast hK0
  have hCm : 2 * propConst < ε * m := by
    rw [div_lt_iff₀ hε] at hm
    linarith
  have hKδ : 32 * χ.χ₂ < K * (δ₀ * ε) := by
    rw [div_lt_iff₀ (by positivity)] at hK
    exact hK
  have hshift := card_sub_abs_le_card_of_shift (n := n)
    (B := (Finset.range n).filter fun i => δ₀ / 2 <
      cavg θ (χ.E ((i + 1 : ℕ) : ℤ)) fun ρ =>
        if good (ρ.map (χ.resc ((i + 1 : ℕ) : ℤ))) then 1 else 0)
    (Q := (Finset.range n).filter fun i =>
      x - ε < cent (convPow θ K) (χ.E ((i + 1 + m : ℕ) : ℤ))
        (fun z => (χ.E ((i + 1 : ℕ) : ℤ) z, H ((i + 1 + m : ℕ) : ℤ) z)) / m)
    (Finset.filter_subset _ _) q (fun i hi i' hi' hii' => ?_)
  · have hq : 4 * |(q : ℝ)| ≤ δ₀ * n := by
      rw [div_le_iff₀ hδ₀] at hn
      linarith
    linarith
  rw [Finset.mem_filter] at hi
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_range.2 hi', ?_⟩
  set b : ℤ := ((i + 1 : ℕ) : ℤ) with hb
  set P := cavg θ (χ.E b) fun ρ => if good (ρ.map (χ.resc b)) then 1 else 0 with hPdef
  have hP : δ₀ / 2 < P := hi.2
  have hP0 : 0 < P := lt_trans (by positivity) hP
  have hkP : (k : ℝ) ≤ K * P / 2 := by nlinarith
  obtain ⟨W, hW, hW1, hcent⟩ := exists_weight_le_cent_convPow hH hθ b q m hK0' good hP0 hkP
    hslice
  have e1 : ((i' + 1 + m : ℕ) : ℤ) = b + q + m := by
    rw [hb]
    push_cast
    omega
  have e2 : ((i' + 1 : ℕ) : ℤ) = b + q := by
    rw [hb]
    push_cast
    omega
  rw [e1, e2, lt_div_iff₀ hm0]
  -- the weight of the bad tuples is at most `ε / (4 χ₂)`
  have hKP : 0 < (K : ℝ) * P := mul_pos hK0 hP0
  have h4 : 4 / (K * P) ≤ ε / (4 * χ.χ₂) := by
    rw [div_le_div_iff₀ hKP (by positivity)]
    nlinarith [mul_pos (mul_pos hε hK0) (sub_pos.2 hP)]
  have h1W : 1 - W ≤ ε / (4 * χ.χ₂) := by linarith
  have hxη : ε / (4 * χ.χ₂) * x ≤ ε / 4 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hL : (x - ε') * m - propConst ≤ x * m := by nlinarith
  have hxm : 0 ≤ x * m := by positivity
  have p1 := mul_nonneg (sub_nonneg.2 hW1) (sub_nonneg.2 hL)
  have p2 := mul_le_mul_of_nonneg_right h1W hxm
  have p3 : ε / (4 * χ.χ₂) * (x * m) ≤ ε / 4 * m := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hxη hm0.le
  have p4 : ε' * m ≤ ε / 4 * m := mul_le_mul_of_nonneg_right hε'ε hm0.le
  nlinarith

end Exps

end BoxLike.Rapaport
