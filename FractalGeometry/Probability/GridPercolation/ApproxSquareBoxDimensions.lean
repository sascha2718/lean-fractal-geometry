import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Dimension.PhiAssouad.BoxRate
import FractalGeometry.Probability.GridPercolation.ApproxSquareCount
import FractalGeometry.Probability.GridPercolation.ApproxSquares
import FractalGeometry.Probability.GridPercolation.Floor
import FractalGeometry.Probability.GridPercolation.GridCoveringReduction
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.NonemptyCover
import FractalGeometry.Probability.GridPercolation.Process

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open Filter Topology

variable {A : GridLaw} {Ω : Type*}
  {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

noncomputable def lowerBoxDim (Y : Set (ℝ × ℝ)) : ℝ :=
  liminf (boxCoverRate Y) (nhdsWithin 0 (Set.Ioi 0))

noncomputable def gridBoxRate (A : GridLaw) (Y : Set (ℝ × ℝ)) (a : ℕ) : ℝ :=
  Real.log (coverNum (gridScale A.M a) Y).toNat / (a * Real.log A.M)

noncomputable def approximateSquareRate
    (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool) (ω : Ω) (a : ℕ) : ℝ :=
  Real.log (limitMeetingCodes X ω a).card / (a * Real.log A.M)

private lemma map_natFloor_atTop :
    Filter.map (fun t : ℝ => ⌊t⌋₊) atTop = (atTop : Filter ℕ) := by
  apply le_antisymm
  · exact tendsto_nat_floor_atTop
  · have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hmap :
        Filter.map (fun t : ℝ => ⌊t⌋₊)
            (Filter.map (fun n : ℕ => (n : ℝ)) atTop) ≤
          Filter.map (fun t : ℝ => ⌊t⌋₊) atTop :=
      Filter.map_mono hcast
    calc
      (atTop : Filter ℕ) = Filter.map (fun n : ℕ => n) atTop := by simp
      _ = Filter.map (fun t : ℝ => ⌊t⌋₊)
          (Filter.map (fun n : ℕ => (n : ℝ)) atTop) := by
            rw [Filter.map_map]
            congr 1
            funext n
            simp
      _ ≤ Filter.map (fun t : ℝ => ⌊t⌋₊) atTop := hmap

private lemma map_natCeil_atTop :
    Filter.map (fun t : ℝ => ⌈t⌉₊) atTop = (atTop : Filter ℕ) := by
  apply le_antisymm
  · exact tendsto_nat_ceil_atTop
  · have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hmap :
        Filter.map (fun t : ℝ => ⌈t⌉₊)
            (Filter.map (fun n : ℕ => (n : ℝ)) atTop) ≤
          Filter.map (fun t : ℝ => ⌈t⌉₊) atTop :=
      Filter.map_mono hcast
    calc
      (atTop : Filter ℕ) = Filter.map (fun n : ℕ => n) atTop := by simp
      _ = Filter.map (fun t : ℝ => ⌈t⌉₊)
          (Filter.map (fun n : ℕ => (n : ℝ)) atTop) := by
            rw [Filter.map_map]
            congr 1
            funext n
            simp
      _ ≤ Filter.map (fun t : ℝ => ⌈t⌉₊) atTop := hmap

private lemma map_gridRadius_atTop (A : GridLaw) :
    Filter.map (fun t : ℝ => (A.M : ℝ) ^ (-t)) atTop = nhdsWithin 0 (Set.Ioi 0) := by
  have hM0 : (0 : ℝ) < A.M := by exact_mod_cast A.hM_pos
  have hlogM : 0 < Real.log A.M := A.log_M_pos
  have hscale :
      Filter.map (fun t : ℝ => Real.log A.M * t) atTop = (atTop : Filter ℝ) := by
    change Filter.map (OrderIso.mulLeft₀ (Real.log A.M) hlogM) atTop = atTop
    exact (OrderIso.mulLeft₀ (Real.log A.M) hlogM).map_atTop
  have hnegscale :
      Filter.map (fun t : ℝ => -(Real.log A.M * t)) atTop = (atBot : Filter ℝ) := by
    calc
      Filter.map (fun t : ℝ => -(Real.log A.M * t)) atTop =
          Filter.map (fun s : ℝ => -s)
            (Filter.map (fun t : ℝ => Real.log A.M * t) atTop) := by
              rw [Filter.map_map]
              rfl
      _ = Filter.map (fun s : ℝ => -s) atTop := by rw [hscale]
      _ = atBot := Filter.map_neg_atTop
  calc
    Filter.map (fun t : ℝ => (A.M : ℝ) ^ (-t)) atTop =
        Filter.map Real.exp
          (Filter.map (fun t : ℝ => -(Real.log A.M * t)) atTop) := by
            rw [Filter.map_map]
            congr 1
            funext t
            simp only [Function.comp_apply]
            rw [Real.rpow_def_of_pos hM0]
            ring_nf
    _ = Filter.map Real.exp atBot := by rw [hnegscale]
    _ = nhdsWithin 0 (Set.Ioi 0) := Real.map_exp_atBot

private lemma limsup_liminf_eq_of_tendsto_sub_zero
    {ι : Type*} {f : Filter ι} [NeBot f] {u v : ι → ℝ}
    (huAbove : f.IsBoundedUnder (· ≤ ·) u)
    (huBelow : f.IsBoundedUnder (· ≥ ·) u)
    (hvAbove : f.IsBoundedUnder (· ≤ ·) v)
    (hvBelow : f.IsBoundedUnder (· ≥ ·) v)
    (hsub : Tendsto (fun i => u i - v i) f (𝓝 0)) :
    limsup u f = limsup v f ∧ liminf u f = liminf v f := by
  let e : ι → ℝ := fun i => u i - v i
  let e' : ι → ℝ := fun i => v i - u i
  have he : Tendsto e f (𝓝 0) := hsub
  have he' : Tendsto e' f (𝓝 0) := by
    simpa only [e, e', neg_sub, neg_zero] using hsub.neg
  have huv : v + e = u := by
    funext i
    change v i + (u i - v i) = u i
    ring
  have hvu : u + e' = v := by
    funext i
    change u i + (v i - u i) = v i
    ring
  constructor
  · apply le_antisymm
    · rw [← huv]
      calc
        limsup (v + e) f ≤ limsup v f + limsup e f :=
          limsup_add_le hvBelow hvAbove he.isCoboundedUnder_le he.isBoundedUnder_le
        _ = limsup v f := by rw [he.limsup_eq]; simp
    · rw [← hvu]
      calc
        limsup (u + e') f ≤ limsup u f + limsup e' f :=
          limsup_add_le huBelow huAbove he'.isCoboundedUnder_le he'.isBoundedUnder_le
        _ = limsup u f := by rw [he'.limsup_eq]; simp
  · apply le_antisymm
    · have h := le_liminf_add huBelow huAbove he'.isBoundedUnder_ge
          he'.isCoboundedUnder_ge
      rw [he'.liminf_eq, add_zero, hvu] at h
      exact h
    · have h := le_liminf_add hvBelow hvAbove he.isBoundedUnder_ge
          he.isCoboundedUnder_ge
      rw [he.liminf_eq, add_zero, huv] at h
      exact h

private lemma tendsto_mul_sub_self_zero_of_bounded
    {ι : Type*} {f : Filter ι} {u v : ι → ℝ} {C : ℝ}
    (hu0 : ∀ᶠ i in f, 0 ≤ u i)
    (huC : ∀ᶠ i in f, u i ≤ C) (hv : Tendsto v f (𝓝 1)) :
    Tendsto (fun i => u i * v i - u i) f (𝓝 0) := by
  have hdiff : Tendsto (fun i => v i - 1) f (𝓝 0) := by
    simpa using hv.sub (tendsto_const_nhds : Tendsto (fun _ : ι => (1 : ℝ)) f (𝓝 1))
  have hrhs : Tendsto (fun i => C * ‖v i - 1‖) f (𝓝 0) := by
    simpa using hdiff.norm.const_mul C
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall fun i => norm_nonneg _)
      ((hu0.and huC).mono fun i hi => ?_)
      hrhs
  rw [show u i * v i - u i = u i * (v i - 1) by ring, norm_mul,
    Real.norm_eq_abs, abs_of_nonneg hi.1]
  exact mul_le_mul_of_nonneg_right hi.2 (norm_nonneg _)

private lemma limsup_liminf_div_eq_nat
    (u : ℝ → ℝ) (hu0 : ∀ t, 0 ≤ u t) (hu : Monotone u)
    {C : ℝ} (hC : 0 ≤ C)
    (hqC : ∀ n : ℕ, 1 ≤ n → u n / n ≤ C) :
    limsup (fun t : ℝ => u t / t) atTop =
        limsup (fun n : ℕ => u n / n) atTop ∧
      liminf (fun t : ℝ => u t / t) atTop =
        liminf (fun n : ℕ => u n / n) atTop := by
  let q : ℕ → ℝ := fun n => u n / n
  let w : ℝ → ℝ := fun t => u t / t
  let qfloor : ℝ → ℝ := fun t => q ⌊t⌋₊
  let qceil : ℝ → ℝ := fun t => q ⌈t⌉₊
  let floorFactor : ℝ → ℝ := fun t => (⌊t⌋₊ : ℝ) / t
  let ceilFactor : ℝ → ℝ := fun t => (⌈t⌉₊ : ℝ) / t
  let lower : ℝ → ℝ := fun t => qfloor t * floorFactor t
  let upper : ℝ → ℝ := fun t => qceil t * ceilFactor t
  have hq0 : ∀ n, 0 ≤ q n := fun n => div_nonneg (hu0 n) (Nat.cast_nonneg n)
  have hqCev : ∀ᶠ n : ℕ in atTop, q n ≤ C := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hqC n hn
  have hqAbove : atTop.IsBoundedUnder (· ≤ ·) q :=
    isBoundedUnder_of_eventually_le hqCev
  have hqBelow : atTop.IsBoundedUnder (· ≥ ·) q :=
    isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall hq0)
  have hfloor0 : ∀ᶠ t : ℝ in atTop, 0 ≤ qfloor t :=
    Filter.Eventually.of_forall fun t => hq0 _
  have hceil0 : ∀ᶠ t : ℝ in atTop, 0 ≤ qceil t :=
    Filter.Eventually.of_forall fun t => hq0 _
  have hfloorC : ∀ᶠ t : ℝ in atTop, qfloor t ≤ C :=
    tendsto_nat_floor_atTop.eventually hqCev
  have hceilC : ∀ᶠ t : ℝ in atTop, qceil t ≤ C :=
    tendsto_nat_ceil_atTop.eventually hqCev
  have hfloorFactor : Tendsto floorFactor atTop (𝓝 1) :=
    tendsto_nat_floor_div_atTop
  have hceilFactor : Tendsto ceilFactor atTop (𝓝 1) :=
    tendsto_nat_ceil_div_atTop
  have hfloorFactor0 : ∀ᶠ t : ℝ in atTop, 0 ≤ floorFactor t := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact div_nonneg (Nat.cast_nonneg _) (zero_le_one.trans ht)
  have hceilFactor0 : ∀ᶠ t : ℝ in atTop, 0 ≤ ceilFactor t := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact div_nonneg (Nat.cast_nonneg _) (zero_le_one.trans ht)
  have hfactorTwo : ∀ᶠ t : ℝ in atTop, floorFactor t ≤ 2 ∧ ceilFactor t ≤ 2 := by
    filter_upwards [hfloorFactor.eventually (Iic_mem_nhds (by norm_num : (1 : ℝ) < 2)),
      hceilFactor.eventually (Iic_mem_nhds (by norm_num : (1 : ℝ) < 2))] with t hft hct
    exact ⟨hft, hct⟩
  have hlower0 : ∀ᶠ t : ℝ in atTop, 0 ≤ lower t :=
    (hfloor0.and hfloorFactor0).mono fun t ht => mul_nonneg ht.1 ht.2
  have hupper0 : ∀ᶠ t : ℝ in atTop, 0 ≤ upper t :=
    (hceil0.and hceilFactor0).mono fun t ht => mul_nonneg ht.1 ht.2
  have hlowerC : ∀ᶠ t : ℝ in atTop, lower t ≤ 2 * C := by
    filter_upwards [hfloor0, hfloorC, hfloorFactor0, hfactorTwo] with t hq0' hqC' hf0 hfac
    dsimp only [lower]
    calc
      qfloor t * floorFactor t ≤ C * 2 := mul_le_mul hqC' hfac.1 hf0 hC
      _ = 2 * C := by ring
  have hupperC : ∀ᶠ t : ℝ in atTop, upper t ≤ 2 * C := by
    filter_upwards [hceil0, hceilC, hceilFactor0, hfactorTwo] with t hq0' hqC' hf0 hfac
    dsimp only [upper]
    calc
      qceil t * ceilFactor t ≤ C * 2 := mul_le_mul hqC' hfac.2 hf0 hC
      _ = 2 * C := by ring
  have hqfloorAbove : atTop.IsBoundedUnder (· ≤ ·) qfloor :=
    isBoundedUnder_of_eventually_le hfloorC
  have hqfloorBelow : atTop.IsBoundedUnder (· ≥ ·) qfloor :=
    isBoundedUnder_of_eventually_ge hfloor0
  have hqceilAbove : atTop.IsBoundedUnder (· ≤ ·) qceil :=
    isBoundedUnder_of_eventually_le hceilC
  have hqceilBelow : atTop.IsBoundedUnder (· ≥ ·) qceil :=
    isBoundedUnder_of_eventually_ge hceil0
  have hlowerAbove : atTop.IsBoundedUnder (· ≤ ·) lower :=
    isBoundedUnder_of_eventually_le hlowerC
  have hlowerBelow : atTop.IsBoundedUnder (· ≥ ·) lower :=
    isBoundedUnder_of_eventually_ge hlower0
  have hupperAbove : atTop.IsBoundedUnder (· ≤ ·) upper :=
    isBoundedUnder_of_eventually_le hupperC
  have hupperBelow : atTop.IsBoundedUnder (· ≥ ·) upper :=
    isBoundedUnder_of_eventually_ge hupper0
  have hlowerPerturb :
      limsup lower atTop = limsup qfloor atTop ∧
        liminf lower atTop = liminf qfloor atTop := by
    apply limsup_liminf_eq_of_tendsto_sub_zero hlowerAbove hlowerBelow
      hqfloorAbove hqfloorBelow
    exact tendsto_mul_sub_self_zero_of_bounded hfloor0 hfloorC hfloorFactor
  have hupperPerturb :
      limsup upper atTop = limsup qceil atTop ∧
        liminf upper atTop = liminf qceil atTop := by
    apply limsup_liminf_eq_of_tendsto_sub_zero hupperAbove hupperBelow
      hqceilAbove hqceilBelow
    exact tendsto_mul_sub_self_zero_of_bounded hceil0 hceilC hceilFactor
  have hfloorLimsup : limsup qfloor atTop = limsup q atTop := by
    rw [show qfloor = q ∘ (fun t : ℝ => ⌊t⌋₊) by rfl, limsup_comp,
      map_natFloor_atTop]
  have hfloorLiminf : liminf qfloor atTop = liminf q atTop := by
    rw [show qfloor = q ∘ (fun t : ℝ => ⌊t⌋₊) by rfl, liminf_comp,
      map_natFloor_atTop]
  have hceilLimsup : limsup qceil atTop = limsup q atTop := by
    rw [show qceil = q ∘ (fun t : ℝ => ⌈t⌉₊) by rfl, limsup_comp,
      map_natCeil_atTop]
  have hceilLiminf : liminf qceil atTop = liminf q atTop := by
    rw [show qceil = q ∘ (fun t : ℝ => ⌈t⌉₊) by rfl, liminf_comp,
      map_natCeil_atTop]
  have hsqueeze : ∀ᶠ t : ℝ in atTop, lower t ≤ w t ∧ w t ≤ upper t := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    have hfloorLe : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (zero_le_one.trans ht)
    have hleCeil : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
    have huFloor : u ⌊t⌋₊ ≤ u t := hu hfloorLe
    have huCeil : u t ≤ u ⌈t⌉₊ := hu hleCeil
    have hfloorPos : (0 : ℝ) < ⌊t⌋₊ := by
      exact_mod_cast (Nat.floor_pos.mpr ht)
    have hceilPos : (0 : ℝ) < ⌈t⌉₊ := by
      exact zero_lt_one.trans_le (ht.trans hleCeil)
    constructor
    · dsimp only [lower, qfloor, floorFactor, q, w]
      rw [div_mul_div_cancel₀ hfloorPos.ne']
      exact div_le_div_of_nonneg_right huFloor ht0.le
    · dsimp only [upper, qceil, ceilFactor, q, w]
      rw [div_mul_div_cancel₀ hceilPos.ne']
      exact div_le_div_of_nonneg_right huCeil ht0.le
  have hwAbove : atTop.IsBoundedUnder (· ≤ ·) w :=
    hupperAbove.mono_le (hsqueeze.mono fun t ht => ht.2)
  have hwBelow : atTop.IsBoundedUnder (· ≥ ·) w :=
    hlowerBelow.mono_ge (hsqueeze.mono fun t ht => ht.1)
  have hlimsupUpper : limsup w atTop ≤ limsup upper atTop :=
    limsup_le_limsup (hsqueeze.mono fun t ht => ht.2) hwBelow.isCoboundedUnder_le
      hupperAbove
  have hliminfLower : liminf lower atTop ≤ liminf w atTop :=
    liminf_le_liminf (hsqueeze.mono fun t ht => ht.1) hlowerBelow
      hwAbove.isCoboundedUnder_ge
  have hnatCast : Tendsto (fun n : ℕ => (n : ℝ)) atTop (atTop : Filter ℝ) :=
    tendsto_natCast_atTop_atTop
  have hq_eq_comp : q = w ∘ (fun n : ℕ => (n : ℝ)) := by
    funext n
    rfl
  have hlimsupSubseq : limsup q atTop ≤ limsup w atTop := by
    rw [hq_eq_comp]
    exact hnatCast.limsup_comp_le_limsup hqBelow.isCoboundedUnder_le hwAbove
  have hliminfSubseq : liminf w atTop ≤ liminf q atTop := by
    rw [hq_eq_comp]
    exact hnatCast.liminf_le_liminf_comp hqAbove.isCoboundedUnder_ge hwBelow
  constructor
  · apply le_antisymm
    · calc
        limsup w atTop ≤ limsup upper atTop := hlimsupUpper
        _ = limsup qceil atTop := hupperPerturb.1
        _ = limsup q atTop := hceilLimsup
    · exact hlimsupSubseq
  · apply le_antisymm
    · exact hliminfSubseq
    · calc
        liminf q atTop = liminf qfloor atTop := hfloorLiminf.symm
        _ = liminf lower atTop := hlowerPerturb.2.symm
        _ ≤ liminf w atTop := hliminfLower

private lemma gridCover_toNat_le (ω : Ω) (a : ℕ) :
    (coverNum (gridScale A.M a) (limitSet X ω)).toNat ≤
      (A.M * A.N) ^ (a + 1) := by
  have hcard : (limitMeetingCodes X ω a).card ≤ Fintype.card (SquareCode A a) :=
    Finset.card_le_univ _
  have hcover : coverNum (gridScale A.M a) (limitSet X ω) ≤
      ((A.N * Fintype.card (SquareCode A a) : ℕ) : ℕ∞) := by
    calc
      coverNum (gridScale A.M a) (limitSet X ω) ≤
          (A.N : ℕ∞) * (limitMeetingCodes X ω a).card :=
        coverNum_le_mul_card_limitMeetingCodes ω a
      _ ≤ (A.N : ℕ∞) * Fintype.card (SquareCode A a) := by
        gcongr
      _ = ((A.N * Fintype.card (SquareCode A a) : ℕ) : ℕ∞) := by norm_cast
  have hnat := ENat.toNat_le_of_le_natCast hcover
  rw [card_squareCode] at hnat
  refine hnat.trans ?_
  have hb : A.N ^ (bfloor A.Gamma a) ≤ A.N ^ a :=
    pow_le_pow_right₀ (le_trans (by norm_num) (le_trans A.hM A.hMN.le)) (A.bfloor_le a)
  have hN : A.N ≤ A.M * A.N := by nlinarith [A.hM_pos, A.hN_pos]
  calc
    A.N * (A.M ^ a * A.N ^ (bfloor A.Gamma a)) ≤
        A.N * (A.M ^ a * A.N ^ a) := by gcongr
    _ = A.N * (A.M * A.N) ^ a := by rw [mul_pow]
    _ ≤ (A.M * A.N) * (A.M * A.N) ^ a := by gcongr
    _ = (A.M * A.N) ^ (a + 1) := by rw [pow_succ]; ring

private lemma gridCover_ne_top (ω : Ω) (a : ℕ) :
    coverNum (gridScale A.M a) (limitSet X ω) ≠ ⊤ := by
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top _)
    (coverNum_le_mul_card_limitMeetingCodes (X := X) ω a)

private lemma coverNum_gridRadius_ne_top (ω : Ω) (t : ℝ) :
    coverNum ((A.M : ℝ) ^ (-t)) (limitSet X ω) ≠ ⊤ := by
  let a : ℕ := ⌈max t 0⌉₊
  have hMone : (1 : ℝ) ≤ A.M := A.one_le_M_real
  have hta : t ≤ (a : ℝ) := by
    exact le_trans (le_max_left _ _) (Nat.le_ceil (max t 0))
  have hr : gridScale A.M a ≤ (A.M : ℝ) ^ (-t) := by
    unfold gridScale
    exact Real.rpow_le_rpow_of_exponent_le hMone (neg_le_neg hta)
  exact ne_top_of_le_ne_top (gridCover_ne_top (X := X) ω a) (coverNum_anti hr)

private lemma one_le_gridRadius_cover_toNat (ω : Ω)
    (hF : (limitSet X ω).Nonempty) (t : ℝ) :
    1 ≤ (coverNum ((A.M : ℝ) ^ (-t)) (limitSet X ω)).toNat := by
  have hne := coverNum_gridRadius_ne_top (X := X) ω t
  rw [← ENat.natCast_le_natCast, ENat.natCast_toNat hne]
  exact one_le_coverNum_of_nonempty hF

private lemma monotone_gridRadius_logCover (ω : Ω)
    (hF : (limitSet X ω).Nonempty) :
    Monotone (fun t : ℝ =>
      Real.log (coverNum ((A.M : ℝ) ^ (-t)) (limitSet X ω)).toNat /
        Real.log A.M) := by
  intro s t hst
  have hMone : (1 : ℝ) ≤ A.M := A.one_le_M_real
  have hr : (A.M : ℝ) ^ (-t) ≤ (A.M : ℝ) ^ (-s) :=
    Real.rpow_le_rpow_of_exponent_le hMone (neg_le_neg hst)
  have hcover := coverNum_anti (X := limitSet X ω) hr
  have hnat :
      (coverNum ((A.M : ℝ) ^ (-s)) (limitSet X ω)).toNat ≤
        (coverNum ((A.M : ℝ) ^ (-t)) (limitSet X ω)).toNat :=
    ENat.toNat_le_toNat hcover (coverNum_gridRadius_ne_top (X := X) ω t)
  have hpos : (0 : ℝ) <
      (coverNum ((A.M : ℝ) ^ (-s)) (limitSet X ω)).toNat := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one
      (one_le_gridRadius_cover_toNat (X := X) ω hF s)
  exact div_le_div_of_nonneg_right (Real.log_le_log hpos (by exact_mod_cast hnat))
    A.log_M_pos.le

private lemma gridRadius_logCover_div_bound (ω : Ω)
    (hF : (limitSet X ω).Nonempty) (n : ℕ) (hn : 1 ≤ n) :
    (Real.log (coverNum ((A.M : ℝ) ^ (-(n : ℝ))) (limitSet X ω)).toNat /
        Real.log A.M) / n ≤
      2 * Real.log (A.M * A.N) / Real.log A.M := by
  have hlogM : 0 < Real.log A.M := A.log_M_pos
  have hMN : (1 : ℝ) < A.M * A.N := by
    have hM1 : (1 : ℝ) < A.M := by
      exact_mod_cast lt_of_lt_of_le one_lt_two A.hM
    have hN1 : (1 : ℝ) ≤ A.N := by
      exact_mod_cast le_trans one_le_two (le_trans A.hM A.hMN.le)
    exact hM1.trans_le (le_mul_of_one_le_right (by positivity) hN1)
  have hlogMN : 0 < Real.log (A.M * A.N) := Real.log_pos hMN
  have hcount :
      (coverNum ((A.M : ℝ) ^ (-(n : ℝ))) (limitSet X ω)).toNat ≤
        (A.M * A.N) ^ (n + 1) := by
    simpa only [gridScale] using gridCover_toNat_le (A := A) (X := X) ω n
  have hcountPos : (0 : ℝ) <
      (coverNum ((A.M : ℝ) ^ (-(n : ℝ))) (limitSet X ω)).toNat := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one
      (one_le_gridRadius_cover_toNat (X := X) ω hF n)
  have hlogle :
      Real.log (coverNum ((A.M : ℝ) ^ (-(n : ℝ))) (limitSet X ω)).toNat ≤
        (n + 1 : ℝ) * Real.log (A.M * A.N) := by
    calc
      Real.log (coverNum ((A.M : ℝ) ^ (-(n : ℝ))) (limitSet X ω)).toNat ≤
          Real.log (((A.M * A.N) ^ (n + 1) : ℕ) : ℝ) :=
        Real.log_le_log hcountPos (by exact_mod_cast hcount)
      _ = (n + 1 : ℝ) * Real.log (A.M * A.N) := by
        rw [Nat.cast_pow, Nat.cast_mul, Real.log_pow]
        push_cast
        rfl
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hratio : ((n : ℝ) + 1) / n ≤ 2 := by
    rw [div_le_iff₀ hn0]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  calc
    (Real.log (coverNum ((A.M : ℝ) ^ (-(n : ℝ))) (limitSet X ω)).toNat /
          Real.log A.M) / n ≤
        (((n : ℝ) + 1) * Real.log (A.M * A.N) / Real.log A.M) / n :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right (by simpa using hlogle) hlogM.le) hn0.le
    _ = (((n : ℝ) + 1) / n) *
        (Real.log (A.M * A.N) / Real.log A.M) := by field_simp
    _ ≤ 2 * (Real.log (A.M * A.N) / Real.log A.M) :=
      mul_le_mul_of_nonneg_right hratio (div_nonneg hlogMN.le hlogM.le)
    _ = 2 * Real.log (A.M * A.N) / Real.log A.M := by ring

theorem upper_lowerBoxDim_eq_limsup_liminf_gridBoxRate {ω : Ω}
    (hF : (limitSet X ω).Nonempty) :
    upperBoxDim (limitSet X ω) =
        limsup (gridBoxRate A (limitSet X ω)) atTop ∧
      lowerBoxDim (limitSet X ω) =
        liminf (gridBoxRate A (limitSet X ω)) atTop := by
  let u : ℝ → ℝ := fun t =>
    Real.log (coverNum ((A.M : ℝ) ^ (-t)) (limitSet X ω)).toNat /
      Real.log A.M
  have hu0 : ∀ t, 0 ≤ u t := by
    intro t
    exact div_nonneg
      (Real.log_nonneg (by
        exact_mod_cast one_le_gridRadius_cover_toNat (X := X) ω hF t))
      A.log_M_pos.le
  have hu : Monotone u := monotone_gridRadius_logCover (X := X) ω hF
  have hC : 0 ≤ 2 * Real.log (A.M * A.N) / Real.log A.M := by
    have hMN : (1 : ℝ) < A.M * A.N := by
      have hM1 : (1 : ℝ) < A.M := by
        exact_mod_cast lt_of_lt_of_le one_lt_two A.hM
      have hN1 : (1 : ℝ) ≤ A.N := by
        exact_mod_cast le_trans one_le_two (le_trans A.hM A.hMN.le)
      exact hM1.trans_le (le_mul_of_one_le_right (by positivity) hN1)
    exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hMN.le)) A.log_M_pos.le
  have hdisc := limsup_liminf_div_eq_nat u hu0 hu hC
    (gridRadius_logCover_div_bound (X := X) ω hF)
  have hrate : ∀ t : ℝ,
      boxCoverRate (limitSet X ω) ((A.M : ℝ) ^ (-t)) = u t / t := by
    intro t
    have hM0 : (0 : ℝ) < A.M := by exact_mod_cast A.hM_pos
    unfold boxCoverRate
    dsimp only [u]
    rw [one_div, Real.log_inv, Real.rpow_neg hM0.le, Real.log_inv, neg_neg,
      Real.log_rpow hM0, div_div]
    congr 1
    ring
  have hgrid : (fun n : ℕ => u n / n) =
      gridBoxRate A (limitSet X ω) := by
    funext n
    simp only [u, gridBoxRate, gridScale, div_div]
    congr 1
    ring
  have hupper : upperBoxDim (limitSet X ω) =
      limsup (fun t : ℝ => u t / t) atTop := by
    rw [upperBoxDim, ← map_gridRadius_atTop A, ← limsup_comp]
    apply limsup_congr
    exact Filter.Eventually.of_forall hrate
  have hlower : lowerBoxDim (limitSet X ω) =
      liminf (fun t : ℝ => u t / t) atTop := by
    rw [lowerBoxDim, ← map_gridRadius_atTop A, ← liminf_comp]
    apply liminf_congr
    exact Filter.Eventually.of_forall hrate
  constructor
  · rw [hupper, hdisc.1, hgrid]
  · rw [hlower, hdisc.2, hgrid]

private lemma tendsto_approximateSquareRate_sub_gridBoxRate_zero {ω : Ω}
    (hF : (limitSet X ω).Nonempty) :
    Tendsto (fun a => approximateSquareRate X ω a -
      gridBoxRate A (limitSet X ω) a) atTop (𝓝 0) := by
  let D : ℝ := max (Real.log 25) (Real.log A.N)
  have hlogM : 0 < Real.log A.M := A.log_M_pos
  have hD0 : 0 ≤ D := by
    exact le_trans (Real.log_nonneg (by norm_num)) (le_max_left _ _)
  have hrhs : Tendsto (fun a : ℕ => D / (a * Real.log A.M)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_mul_const hlogM)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall fun a => norm_nonneg _)
      (eventually_atTop.2 ⟨1, fun a ha => ?_⟩) hrhs
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ha)
  have hden0 : 0 < (a : ℝ) * Real.log A.M := mul_pos ha0 hlogM
  have hcodePosNat : 0 < (limitMeetingCodes X ω a).card :=
    (limitMeetingCodes_nonempty_of_limitSet_nonempty hF a).card_pos
  have hcodePos : (0 : ℝ) < (limitMeetingCodes X ω a).card := by
    exact_mod_cast hcodePosNat
  have hcoverOne := one_le_gridRadius_cover_toNat (X := X) ω hF a
  have hcoverPosNat : 0 <
      (coverNum (gridScale A.M a) (limitSet X ω)).toNat := by
    simpa only [gridScale] using lt_of_lt_of_le Nat.zero_lt_one hcoverOne
  have hcoverPos : (0 : ℝ) <
      (coverNum (gridScale A.M a) (limitSet X ω)).toNat := by
    exact_mod_cast hcoverPosNat
  have hfin := gridCover_ne_top (X := X) ω a
  have hcodeCover : (limitMeetingCodes X ω a).card ≤
      25 * (coverNum (gridScale A.M a) (limitSet X ω)).toNat := by
    have h := card_limitMeetingCodes_le_coverNum (X := X) ω a
    rw [← ENat.natCast_toNat hfin] at h
    exact_mod_cast h
  have hcoverCode : (coverNum (gridScale A.M a) (limitSet X ω)).toNat ≤
      A.N * (limitMeetingCodes X ω a).card := by
    have h := coverNum_le_mul_card_limitMeetingCodes (X := X) ω a
    rw [← ENat.natCast_toNat hfin] at h
    exact_mod_cast h
  have hlogCodeCover :
      Real.log (limitMeetingCodes X ω a).card ≤
        Real.log 25 +
          Real.log (coverNum (gridScale A.M a) (limitSet X ω)).toNat := by
    calc
      Real.log (limitMeetingCodes X ω a).card ≤
          Real.log (25 *
            (coverNum (gridScale A.M a) (limitSet X ω)).toNat) :=
        Real.log_le_log hcodePos (by exact_mod_cast hcodeCover)
      _ = Real.log 25 +
          Real.log (coverNum (gridScale A.M a) (limitSet X ω)).toNat := by
        rw [Real.log_mul (by norm_num) hcoverPos.ne']
  have hlogCoverCode :
      Real.log (coverNum (gridScale A.M a) (limitSet X ω)).toNat ≤
        Real.log A.N + Real.log (limitMeetingCodes X ω a).card := by
    calc
      Real.log (coverNum (gridScale A.M a) (limitSet X ω)).toNat ≤
          Real.log (A.N * (limitMeetingCodes X ω a).card) :=
        Real.log_le_log hcoverPos (by exact_mod_cast hcoverCode)
      _ = Real.log A.N + Real.log (limitMeetingCodes X ω a).card := by
        rw [Real.log_mul (by exact_mod_cast A.hN_pos.ne') hcodePos.ne']
  have hupper : approximateSquareRate X ω a -
      gridBoxRate A (limitSet X ω) a ≤ D / (a * Real.log A.M) := by
    calc
      approximateSquareRate X ω a - gridBoxRate A (limitSet X ω) a =
          (Real.log (limitMeetingCodes X ω a).card -
            Real.log (coverNum (gridScale A.M a) (limitSet X ω)).toNat) /
              (a * Real.log A.M) := by
        simp only [approximateSquareRate, gridBoxRate]
        ring
      _ ≤ Real.log 25 / (a * Real.log A.M) :=
        div_le_div_of_nonneg_right (by linarith) hden0.le
      _ ≤ D / (a * Real.log A.M) :=
        div_le_div_of_nonneg_right (le_max_left _ _) hden0.le
  have hlower : -(D / (a * Real.log A.M)) ≤
      approximateSquareRate X ω a - gridBoxRate A (limitSet X ω) a := by
    have h : gridBoxRate A (limitSet X ω) a - approximateSquareRate X ω a ≤
        D / (a * Real.log A.M) := by
      calc
        gridBoxRate A (limitSet X ω) a - approximateSquareRate X ω a =
            (Real.log (coverNum (gridScale A.M a) (limitSet X ω)).toNat -
              Real.log (limitMeetingCodes X ω a).card) /
                (a * Real.log A.M) := by
          simp only [approximateSquareRate, gridBoxRate]
          ring
        _ ≤ Real.log A.N / (a * Real.log A.M) :=
          div_le_div_of_nonneg_right (by linarith) hden0.le
        _ ≤ D / (a * Real.log A.M) :=
          div_le_div_of_nonneg_right (le_max_right _ _) hden0.le
    linarith
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨hlower, hupper⟩

theorem limsup_liminf_approximateSquareRate_eq_gridBoxRate {ω : Ω}
    (hF : (limitSet X ω).Nonempty) :
    limsup (approximateSquareRate X ω) atTop =
        limsup (gridBoxRate A (limitSet X ω)) atTop ∧
      liminf (approximateSquareRate X ω) atTop =
        liminf (gridBoxRate A (limitSet X ω)) atTop := by
  let u : ℕ → ℝ := approximateSquareRate X ω
  let v : ℕ → ℝ := gridBoxRate A (limitSet X ω)
  have hu0 : ∀ a, 0 ≤ u a := fun a => div_nonneg
    (Real.log_nonneg (by
      have hcard : 1 ≤ (limitMeetingCodes X ω a).card :=
        (limitMeetingCodes_nonempty_of_limitSet_nonempty hF a).card_pos
      exact_mod_cast hcard))
    (mul_nonneg (Nat.cast_nonneg _) A.log_M_pos.le)
  have hv0 : ∀ a, 0 ≤ v a := fun a => div_nonneg
    (Real.log_nonneg (by
      have hcover : 1 ≤
          (coverNum ((A.M : ℝ) ^ (-(a : ℝ))) (limitSet X ω)).toNat :=
        one_le_gridRadius_cover_toNat (X := X) ω hF a
      have hcover' : (1 : ℝ) ≤
          (coverNum ((A.M : ℝ) ^ (-(a : ℝ))) (limitSet X ω)).toNat := by
        exact_mod_cast hcover
      simpa only [gridScale] using hcover'))
    (mul_nonneg (Nat.cast_nonneg _) A.log_M_pos.le)
  have hvC : ∀ᶠ a : ℕ in atTop,
      v a ≤ 2 * Real.log (A.M * A.N) / Real.log A.M := by
    filter_upwards [eventually_ge_atTop 1] with a ha
    simpa only [v, gridBoxRate, gridScale, div_div, mul_comm] using
      gridRadius_logCover_div_bound (X := X) ω hF a ha
  have hsub : Tendsto (fun a => u a - v a) atTop (𝓝 0) :=
    tendsto_approximateSquareRate_sub_gridBoxRate_zero (X := X) hF
  have hsmall : ∀ᶠ a : ℕ in atTop, u a - v a ≤ 1 :=
    hsub.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have huBound : ∀ᶠ a : ℕ in atTop,
      u a ≤ 2 * Real.log (A.M * A.N) / Real.log A.M + 1 :=
    (hvC.and hsmall).mono fun a h => by linarith
  have huAbove : atTop.IsBoundedUnder (· ≤ ·) u :=
    isBoundedUnder_of_eventually_le huBound
  have huBelow : atTop.IsBoundedUnder (· ≥ ·) u :=
    isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall hu0)
  have hvAbove : atTop.IsBoundedUnder (· ≤ ·) v :=
    isBoundedUnder_of_eventually_le hvC
  have hvBelow : atTop.IsBoundedUnder (· ≥ ·) v :=
    isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall hv0)
  exact limsup_liminf_eq_of_tendsto_sub_zero huAbove huBelow hvAbove hvBelow hsub

theorem upper_lowerBoxDim_eq_limsup_liminf_approximateSquareRate {ω : Ω}
    (hF : (limitSet X ω).Nonempty) :
    upperBoxDim (limitSet X ω) =
        limsup (approximateSquareRate X ω) atTop ∧
      lowerBoxDim (limitSet X ω) =
        liminf (approximateSquareRate X ω) atTop := by
  have hgrid := upper_lowerBoxDim_eq_limsup_liminf_gridBoxRate (X := X) hF
  have hcount := limsup_liminf_approximateSquareRate_eq_gridBoxRate (X := X) hF
  exact ⟨hgrid.1.trans hcount.1.symm, hgrid.2.trans hcount.2.symm⟩

theorem upperBoxDim_eq_limsup_approximateSquareRate {ω : Ω}
    (hF : (limitSet X ω).Nonempty) :
    upperBoxDim (limitSet X ω) =
      limsup (approximateSquareRate X ω) atTop :=
  (upper_lowerBoxDim_eq_limsup_liminf_approximateSquareRate (X := X) hF).1

theorem lowerBoxDim_eq_liminf_approximateSquareRate {ω : Ω}
    (hF : (limitSet X ω).Nonempty) :
    lowerBoxDim (limitSet X ω) =
      liminf (approximateSquareRate X ω) atTop :=
  (upper_lowerBoxDim_eq_limsup_liminf_approximateSquareRate (X := X) hF).2

end FractalGeometry.Probability.GridPercolation
