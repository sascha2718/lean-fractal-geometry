module

public import Mathlib
public import FractalGeometry.LinearCocycles.Invertibility
public import FractalGeometry.Symbolic.Entropy
public import FractalGeometry.Symbolic.WordAverages
public import FractalGeometry.LinearCocycles.Products
public import FractalGeometry.Symbolic.Shift
public import FractalGeometry.Symbolic.PastIdentities
public import FractalGeometry.Symbolic.FutureWords
public import FractalGeometry.Symbolic.Past
public import FractalGeometry.Symbolic.PastWords

@[expose] public section

namespace FractalGeometry


open MeasureTheory Filter Topology Set Matrix

open scoped Matrix.Norms.L2Operator Real

theorem tendsto_div_of_abs_sub_le {f g : ℕ → ℝ} {l : ℝ} (C : ℝ)
    (hb : ∀ᶠ n in atTop, |f n - g n| ≤ C)
    (hg : Tendsto (fun n : ℕ => g n / n) atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => f n / n) atTop (𝓝 l) := by
  have h0 : Tendsto (fun n : ℕ => (f n - g n) / n) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat C)
    filter_upwards [hb] with n hn
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right hn (Nat.cast_nonneg n)
  have := hg.add h0
  rw [add_zero] at this
  refine this.congr fun n => ?_
  rw [← add_div, add_sub_cancel]

namespace MatrixTuple

variable {ι : Type*} (A : ι → Matrix (Fin 2) (Fin 2) ℝ)

def pastProd (x : ℤ → ι) (n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ := word A (pastWord x n)

def HasPastRate (x : ℤ → ι) (v : Fin 2 → ℝ) (l : ℝ) : Prop :=
  Tendsto (fun n : ℕ => Real.log ‖pastProd A x n *ᵥ v‖ / n) atTop (𝓝 l)

variable {A}

theorem pastProd_congr {x y : ℤ → ι} (h : SamePast x y) (n : ℕ) :
    pastProd A x n = pastProd A y n := by
  rw [pastProd, pastProd, pastWord_congr h]

theorem hasPastRate_congr {x y : ℤ → ι} (h : SamePast x y) {v : Fin 2 → ℝ} {l : ℝ} :
    HasPastRate A x v l ↔ HasPastRate A y v l := by
  simp only [HasPastRate, pastProd_congr h]

theorem HasPastRate.unique {x : ℤ → ι} {v : Fin 2 → ℝ} {l l' : ℝ} (h : HasPastRate A x v l)
    (h' : HasPastRate A x v l') : l = l' :=
  tendsto_nhds_unique h h'

theorem pastProd_shift_one (x : ℤ → ι) (n : ℕ) :
    pastProd A (shift 1 x) (n + 1) = pastProd A x n * A (x 0) := by
  rw [pastProd, pastWord_shift_one, word_append, pastProd]
  simp [word]

theorem hasPastRate_shift_iff (x : ℤ → ι) (v : Fin 2 → ℝ) (l : ℝ) :
    HasPastRate A (shift 1 x) v l ↔ HasPastRate A x (A (x 0) *ᵥ v) l := by
  unfold HasPastRate
  rw [← tendsto_add_atTop_iff_nat 1]
  have h := tendsto_add_div_succ_iff (fun n => Real.log ‖pastProd A x n *ᵥ (A (x 0) *ᵥ v)‖) 0 l
  simp only [add_zero] at h
  rw [← h]
  refine Iff.of_eq (congrArg (fun F => Tendsto F atTop (𝓝 l)) (funext fun n => ?_))
  rw [pastProd_shift_one, ← mulVec_mulVec, Nat.cast_succ]

theorem HasPastRate.smul {x : ℤ → ι} {v : Fin 2 → ℝ} {l : ℝ} (h : HasPastRate A x v l)
    {c : ℝ} (hc : c ≠ 0) : HasPastRate A x (c • v) l := by
  refine tendsto_div_of_abs_sub_le (abs (Real.log |c|)) (Eventually.of_forall fun n => ?_) h
  rw [mulVec_smul, norm_smul, Real.norm_eq_abs]
  by_cases hv : ‖pastProd A x n *ᵥ v‖ = 0
  · rw [hv, mul_zero, sub_self]
    simpa only [abs_zero] using (abs_nonneg (Real.log |c|))
  rw [Real.log_mul (abs_ne_zero.2 hc) hv, add_sub_cancel_right]

theorem det_word_ne_zero (hA : ∀ i, (A i).det ≠ 0) (w : List ι) : (word A w).det ≠ 0 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [show word A (i :: w) = A i * word A w by simp [word], det_mul]
    exact mul_ne_zero (hA i) ih

theorem norm_pastProd_mulVec_pos (hA : ∀ i, (A i).det ≠ 0) (x : ℤ → ι) (n : ℕ)
    {v : Fin 2 → ℝ} (hv : v ≠ 0) : 0 < ‖pastProd A x n *ᵥ v‖ :=
  norm_pos_iff.2 (mulVec_ne_zero_of_det_ne_zero (det_word_ne_zero hA _) hv)

theorem HasPastRate.add_smul (hA : ∀ i, (A i).det ≠ 0) {x : ℤ → ι} {u w : Fin 2 → ℝ}
    {l₁ l₂ : ℝ} (hlt : l₂ < l₁) (hu : HasPastRate A x u l₂) (hw : HasPastRate A x w l₁)
    (hu0 : u ≠ 0) (hw0 : w ≠ 0) (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    HasPastRate A x (a • u + b • w) l₁ := by
  set p : ℕ → ℝ := fun n => ‖pastProd A x n *ᵥ u‖ with hp
  set q : ℕ → ℝ := fun n => ‖pastProd A x n *ᵥ w‖ with hq
  have hp0 : ∀ n, 0 < p n := fun n => norm_pastProd_mulVec_pos hA x n hu0
  have hq0 : ∀ n, 0 < q n := fun n => norm_pastProd_mulVec_pos hA x n hw0

  have hdiff : Tendsto (fun n : ℕ => (Real.log (p n) - Real.log (q n)) / n) atTop
      (𝓝 (l₂ - l₁)) := by
    have := hu.sub hw
    refine this.congr fun n => ?_
    rw [sub_div]
  have hbot : Tendsto (fun n : ℕ => Real.log (p n) - Real.log (q n)) atTop atBot := by
    have hc : (l₂ - l₁) / 2 < 0 := by linarith
    have hev : ∀ᶠ n : ℕ in atTop, (Real.log (p n) - Real.log (q n)) / n < (l₂ - l₁) / 2 :=
      hdiff.eventually (gt_mem_nhds (by linarith))
    refine tendsto_atBot_mono' atTop ?_
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop_of_neg hc)
    filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
    rw [div_lt_iff₀ hn'] at hn
    linarith
  have hratio : Tendsto (fun n => p n / q n) atTop (𝓝 0) := by
    have := Real.tendsto_exp_atBot.comp hbot
    refine this.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [Real.exp_sub, Real.exp_log (hp0 n), Real.exp_log (hq0 n)]

  have hb' : 0 < |b| := abs_pos.2 hb
  have hsmall : ∀ᶠ n in atTop, |a| * p n ≤ |b| / 2 * q n := by
    have hε : 0 < |b| / (2 * (|a| + 1)) := by positivity
    filter_upwards [hratio.eventually (gt_mem_nhds hε)] with n hn
    rw [div_lt_div_iff₀ (hq0 n) (by positivity)] at hn
    nlinarith [abs_nonneg a, hp0 n, hq0 n]
  refine tendsto_div_of_abs_sub_le (|Real.log (|b| / 2)| + |Real.log (3 * |b| / 2)|) ?_ hw
  filter_upwards [hsmall] with n hn
  set r := ‖pastProd A x n *ᵥ (a • u + b • w)‖ with hr
  have hsplit : pastProd A x n *ᵥ (a • u + b • w) =
      a • (pastProd A x n *ᵥ u) + b • (pastProd A x n *ᵥ w) := by
    rw [mulVec_add, mulVec_smul, mulVec_smul]
  have hup : r ≤ 3 * |b| / 2 * q n := by
    rw [hr, hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    change |a| * p n + |b| * q n ≤ _
    linarith
  have hlow : |b| / 2 * q n ≤ r := by
    rw [hr, hsplit]
    have h1 := norm_sub_norm_le (b • (pastProd A x n *ᵥ w)) (-(a • (pastProd A x n *ᵥ u)))
    rw [sub_neg_eq_add, add_comm, norm_neg, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs] at h1
    change |b| * q n - |a| * p n ≤ _ at h1
    linarith
  have hr0 : 0 < r := lt_of_lt_of_le (by have := hq0 n; positivity) hlow
  have hl1 : Real.log (|b| / 2) ≤ Real.log r - Real.log (q n) := by
    rw [← Real.log_div hr0.ne' (hq0 n).ne']
    exact Real.log_le_log (by positivity) ((le_div_iff₀ (hq0 n)).2 hlow)
  have hl2 : Real.log r - Real.log (q n) ≤ Real.log (3 * |b| / 2) := by
    rw [← Real.log_div hr0.ne' (hq0 n).ne']
    exact Real.log_le_log (div_pos hr0 (hq0 n)) ((div_le_iff₀ (hq0 n)).2 hup)
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log (|b| / 2)), abs_nonneg (Real.log (3 * |b| / 2))]
  · linarith [le_abs_self (Real.log (3 * |b| / 2)), abs_nonneg (Real.log (|b| / 2))]

def cross (u v : Fin 2 → ℝ) : ℝ := u 0 * v 1 - u 1 * v 0

theorem mem_span_iff_cross {u : Fin 2 → ℝ} (hu : u ≠ 0) (v : Fin 2 → ℝ) :
    v ∈ Submodule.span ℝ {u} ↔ cross u v = 0 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    simp only [cross, Pi.smul_apply, smul_eq_mul]
    ring
  · intro h
    simp only [cross] at h
    by_cases h0 : u 0 = 0
    · have h1 : u 1 ≠ 0 := fun h1 => hu (by ext j; fin_cases j <;> simp [h0, h1])
      have hv0 : v 0 = 0 := by
        rw [h0, zero_mul, zero_sub, neg_eq_zero] at h
        exact (mul_eq_zero.1 h).resolve_left h1
      refine ⟨v 1 / u 1, ?_⟩
      ext j; fin_cases j
      · simp [h0, hv0]
      · simp [div_mul_cancel₀ _ h1]
    · refine ⟨v 0 / u 0, ?_⟩
      ext j; fin_cases j
      · simp [div_mul_cancel₀ _ h0]
      · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
        rw [div_mul_eq_mul_div, div_eq_iff h0]
        linarith

theorem eq_cramer {u w : Fin 2 → ℝ} (h : cross u w ≠ 0) (v : Fin 2 → ℝ) :
    v = (cross v w / cross u w) • u + (cross u v / cross u w) • w := by
  ext j; fin_cases j <;>
  · simp only [Fin.zero_eta, Fin.mk_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff h]
    simp only [cross]
    ring

noncomputable def dirVec (θ : ℝ) : Fin 2 → ℝ := ![Real.cos θ, Real.sin θ]

theorem dirVec_ne_zero (θ : ℝ) : dirVec θ ≠ 0 := by
  intro h
  have h0 : Real.cos θ = 0 := congrFun h 0
  have h1 : Real.sin θ = 0 := congrFun h 1
  have := Real.sin_sq_add_cos_sq θ
  rw [h0, h1] at this
  norm_num at this

theorem cross_dirVec (θ θ' : ℝ) : cross (dirVec θ) (dirVec θ') = Real.sin (θ' - θ) := by
  simp only [cross, dirVec, Matrix.cons_val_zero, Matrix.cons_val_one, Real.sin_sub]
  ring

theorem eq_of_cross_dirVec_eq_zero {θ θ' : ℝ} (hθ : θ ∈ Ico 0 π) (hθ' : θ' ∈ Ico 0 π)
    (h : cross (dirVec θ) (dirVec θ') = 0) : θ = θ' := by
  rw [cross_dirVec] at h
  have := (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [hθ'.1, hθ.2])
    (by linarith [hθ'.2, hθ.1])).1 h
  linarith

theorem exists_dirVec {u : Fin 2 → ℝ} (hu : u ≠ 0) :
    ∃ θ ∈ Ico 0 π, ∃ c : ℝ, c ≠ 0 ∧ u = c • dirVec θ := by
  set z : ℂ := ⟨u 0, u 1⟩ with hz
  have hz0 : z ≠ 0 := by
    intro h
    apply hu
    ext j; fin_cases j
    · exact congrArg Complex.re h
    · exact congrArg Complex.im h
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hc : ‖z‖ * Real.cos (Complex.arg z) = u 0 := Complex.norm_mul_cos_arg z
  have hs : ‖z‖ * Real.sin (Complex.arg z) = u 1 := Complex.norm_mul_sin_arg z
  rcases lt_or_ge (Complex.arg z) 0 with hneg | hnn
  · refine ⟨Complex.arg z + π, ⟨by linarith [Complex.neg_pi_lt_arg z], by linarith⟩, -‖z‖,
      neg_ne_zero.2 hr.ne', ?_⟩
    ext j; fin_cases j
    · simp [dirVec, Real.cos_add_pi]
      linarith
    · simp [dirVec, Real.sin_add_pi]
      linarith
  · rcases lt_or_eq_of_le (Complex.arg_le_pi z) with hlt | heq
    · refine ⟨Complex.arg z, ⟨hnn, hlt⟩, ‖z‖, hr.ne', ?_⟩
      ext j; fin_cases j
      · simp [dirVec]
        linarith
      · simp [dirVec]
        linarith
    · refine ⟨0, ⟨le_rfl, Real.pi_pos⟩, -‖z‖, neg_ne_zero.2 hr.ne', ?_⟩
      rw [heq, Real.cos_pi] at hc
      rw [heq, Real.sin_pi] at hs
      ext j; fin_cases j
      · simp [dirVec]
        linarith
      · simp [dirVec]
        linarith

theorem mulVec_inv_mulVec {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.det ≠ 0) (v : Fin 2 → ℝ) :
    M *ᵥ (M⁻¹ *ᵥ v) = v := by
  rw [mulVec_mulVec, mul_nonsing_inv M (isUnit_iff_ne_zero.2 hM), one_mulVec]

theorem inv_mulVec_mulVec {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.det ≠ 0) (v : Fin 2 → ℝ) :
    M⁻¹ *ᵥ (M *ᵥ v) = v := by
  rw [mulVec_mulVec, nonsing_inv_mul M (isUnit_iff_ne_zero.2 hM), one_mulVec]

theorem mulVec_mem_span_iff {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.det ≠ 0) (u v : Fin 2 → ℝ) :
    M *ᵥ v ∈ Submodule.span ℝ {M *ᵥ u} ↔ v ∈ Submodule.span ℝ {u} := by
  simp only [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have := congrArg (fun w => M⁻¹ *ᵥ w) hc
    simpa only [mulVec_smul, inv_mulVec_mulVec hM] using this
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [mulVec_smul]⟩

def IsRegularWith (l₁ l₂ : ℝ) (x : ℤ → ι) (u : Fin 2 → ℝ) : Prop :=
  u ≠ 0 ∧ ∀ v : Fin 2 → ℝ,
    (v ∈ Submodule.span ℝ {u} → v ≠ 0 → HasPastRate A x v l₂) ∧
    (v ∉ Submodule.span ℝ {u} → HasPastRate A x v l₁)

def IsRegular (l₁ l₂ : ℝ) (x : ℤ → ι) : Prop := ∃ u, IsRegularWith (A := A) l₁ l₂ x u

variable (A) in

def regularSet (l₁ l₂ : ℝ) : Set (ℤ → ι) := {x | IsRegular (A := A) l₁ l₂ x}

variable (A) in

def slowLine (l₂ : ℝ) (x : ℤ → ι) : Set (Fin 2 → ℝ) :=
  {v | v = 0 ∨ ∃ r, HasPastRate A x v r ∧ r ≤ l₂}

theorem isRegularWith_congr {x y : ℤ → ι} (h : SamePast x y) {l₁ l₂ : ℝ} {u : Fin 2 → ℝ} :
    IsRegularWith (A := A) l₁ l₂ x u ↔ IsRegularWith (A := A) l₁ l₂ y u := by
  simp only [IsRegularWith, hasPastRate_congr h]

theorem isRegular_congr {x y : ℤ → ι} (h : SamePast x y) {l₁ l₂ : ℝ} :
    IsRegular (A := A) l₁ l₂ x ↔ IsRegular (A := A) l₁ l₂ y := by
  simp only [IsRegular, isRegularWith_congr h]

theorem mem_regularSet_of_samePast {x y : ℤ → ι} (h : SamePast x y) {l₁ l₂ : ℝ}
    (hx : x ∈ regularSet A l₁ l₂) : y ∈ regularSet A l₁ l₂ :=
  (isRegular_congr h).1 hx

theorem IsRegularWith.mem_span {l₁ l₂ : ℝ} (hlt : l₂ < l₁) {x : ℤ → ι} {u : Fin 2 → ℝ}
    (hx : IsRegularWith (A := A) l₁ l₂ x u) {v : Fin 2 → ℝ} {r : ℝ} (hv : HasPastRate A x v r)
    (hr : r ≤ l₂) : v ∈ Submodule.span ℝ {u} := by
  by_contra h
  have := hv.unique ((hx.2 v).2 h)
  linarith

theorem slowLine_eq_span {l₁ l₂ : ℝ} (hlt : l₂ < l₁) {x : ℤ → ι} {u : Fin 2 → ℝ}
    (hx : IsRegularWith (A := A) l₁ l₂ x u) :
    slowLine A l₂ x = (Submodule.span ℝ {u} : Set (Fin 2 → ℝ)) := by
  ext v
  simp only [slowLine, mem_ofPred_eq, SetLike.mem_coe]
  constructor
  · rintro (rfl | ⟨r, hv, hr⟩)
    · exact Submodule.zero_mem _
    · exact hx.mem_span hlt hv hr
  · intro hv
    by_cases hv0 : v = 0
    · exact Or.inl hv0
    · exact Or.inr ⟨l₂, (hx.2 v).1 hv hv0, le_rfl⟩

theorem IsRegularWith.of_mem_span {l₁ l₂ : ℝ} {x : ℤ → ι} {u v : Fin 2 → ℝ}
    (hx : IsRegularWith (A := A) l₁ l₂ x u) (hv : v ∈ Submodule.span ℝ {u}) (hv0 : v ≠ 0) :
    IsRegularWith (A := A) l₁ l₂ x v := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  have hc : c ≠ 0 := by rintro rfl; exact hv0 (zero_smul ℝ u)
  refine ⟨hv0, fun w => ?_⟩
  rw [Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 hc)]
  exact hx.2 w

theorem IsRegular.exists_dirVec {l₁ l₂ : ℝ} {x : ℤ → ι} (hx : IsRegular (A := A) l₁ l₂ x) :
    ∃ θ ∈ Ico 0 π, IsRegularWith (A := A) l₁ l₂ x (dirVec θ) := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨θ, hθ, c, hc, rfl⟩ := MatrixTuple.exists_dirVec hu.1
  refine ⟨θ, hθ, hu.of_mem_span ?_ (dirVec_ne_zero θ)⟩
  rw [Submodule.mem_span_singleton]
  exact ⟨c⁻¹, by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]⟩

theorem isRegularWith_of (hA : ∀ i, (A i).det ≠ 0) {l₁ l₂ : ℝ} (hlt : l₂ < l₁) {x : ℤ → ι}
    {u w : Fin 2 → ℝ} (hu0 : u ≠ 0) (hw0 : w ≠ 0) (hu : HasPastRate A x u l₂)
    (hw : HasPastRate A x w l₁) : IsRegularWith (A := A) l₁ l₂ x u := by
  have hsmul : ∀ v ∈ Submodule.span ℝ {u}, v ≠ 0 → HasPastRate A x v l₂ := by
    intro v hv hv0
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    have hc : c ≠ 0 := by rintro rfl; exact hv0 (zero_smul ℝ u)
    exact hu.smul hc
  have hwu : cross u w ≠ 0 := by
    intro h
    have := (hsmul w ((mem_span_iff_cross hu0 w).2 h) hw0).unique hw
    linarith
  refine ⟨hu0, fun v => ⟨hsmul v, fun hv => ?_⟩⟩
  have hb : cross u v / cross u w ≠ 0 :=
    div_ne_zero (fun h => hv ((mem_span_iff_cross hu0 v).2 h)) hwu
  rw [eq_cramer hwu v]
  exact hu.add_smul hA hlt hw hu0 hw0 _ hb

theorem isRegular_iff (hA : ∀ i, (A i).det ≠ 0) {l₁ l₂ : ℝ} (hlt : l₂ < l₁) (x : ℤ → ι) :
    IsRegular (A := A) l₁ l₂ x ↔ (∃ θ ∈ Ico 0 π, HasPastRate A x (dirVec θ) l₂) ∧
      (HasPastRate A x ![1, 0] l₁ ∨ HasPastRate A x ![0, 1] l₁) := by
  constructor
  · intro hx
    obtain ⟨θ, hθ, hu⟩ := hx.exists_dirVec
    refine ⟨⟨θ, hθ, (hu.2 _).1 (Submodule.mem_span_singleton_self _) hu.1⟩, ?_⟩
    by_cases h0 : (![1, 0] : Fin 2 → ℝ) ∈ Submodule.span ℝ {dirVec θ}
    · refine Or.inr ((hu.2 _).2 fun h1 => ?_)
      rw [mem_span_iff_cross hu.1] at h0 h1
      apply hu.1
      ext j; fin_cases j
      · simpa [cross] using h1
      · simpa [cross] using h0
    · exact Or.inl ((hu.2 _).2 h0)
  · rintro ⟨⟨θ, -, hθ⟩, h | h⟩
    · exact ⟨_, isRegularWith_of hA hlt (dirVec_ne_zero θ)
        (by intro h; simpa using congrFun h 0) hθ h⟩
    · exact ⟨_, isRegularWith_of hA hlt (dirVec_ne_zero θ)
        (by intro h; simpa using congrFun h 1) hθ h⟩

theorem mem_slowLine_shift_iff (hA : ∀ i, (A i).det ≠ 0) (l₂ : ℝ) (x : ℤ → ι)
    (v : Fin 2 → ℝ) : v ∈ slowLine A l₂ (shift 1 x) ↔ A (x 0) *ᵥ v ∈ slowLine A l₂ x := by
  have h0 : v = 0 ↔ A (x 0) *ᵥ v = 0 := by
    constructor
    · rintro rfl; exact mulVec_zero _
    · intro h
      by_contra hv
      exact mulVec_ne_zero_of_det_ne_zero (hA (x 0)) hv h
  simp only [slowLine, mem_ofPred_eq, hasPastRate_shift_iff, h0]

theorem image_slowLine (hA : ∀ i, (A i).det ≠ 0) (l₂ : ℝ) (x : ℤ → ι) :
    (A (x (-1)) *ᵥ ·) '' slowLine A l₂ x = slowLine A l₂ (shift (-1) x) := by
  have e1 : shift 1 (shift (-1) x) = x := by rw [shift_shift]; simp
  have e2 : shift (-1) x 0 = x (-1) := by simp
  have key : ∀ v, v ∈ slowLine A l₂ x ↔ A (x (-1)) *ᵥ v ∈ slowLine A l₂ (shift (-1) x) := by
    intro v
    have := mem_slowLine_shift_iff hA l₂ (shift (-1) x) v
    rwa [e1, e2] at this
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (key v).1 hv
  · intro hw
    refine ⟨(A (x (-1)))⁻¹ *ᵥ w, (key _).2 ?_, mulVec_inv_mulVec (hA _) w⟩
    rwa [mulVec_inv_mulVec (hA _)]

theorem shift_mem_regularSet_iff (hA : ∀ i, (A i).det ≠ 0) (l₁ l₂ : ℝ) (x : ℤ → ι) :
    shift 1 x ∈ regularSet A l₁ l₂ ↔ x ∈ regularSet A l₁ l₂ := by
  set B := A (x 0)
  have hB : B.det ≠ 0 := hA (x 0)
  have hsh : ∀ v l, HasPastRate A (shift 1 x) v l ↔ HasPastRate A x (B *ᵥ v) l :=
    fun v l => hasPastRate_shift_iff x v l
  have hne : ∀ v : Fin 2 → ℝ, B *ᵥ v ≠ 0 ↔ v ≠ 0 := fun v =>
    ⟨fun h hv => h (by rw [hv, mulVec_zero]), mulVec_ne_zero_of_det_ne_zero hB⟩
  constructor
  · rintro ⟨u', hu'0, hu'⟩
    refine ⟨B *ᵥ u', (hne u').2 hu'0, fun v => ?_⟩
    have ev : v = B *ᵥ (B⁻¹ *ᵥ v) := (mulVec_inv_mulVec hB v).symm
    have hspan : v ∈ Submodule.span ℝ {B *ᵥ u'} ↔ B⁻¹ *ᵥ v ∈ Submodule.span ℝ {u'} := by
      conv_lhs => rw [ev]
      exact mulVec_mem_span_iff hB u' _
    rw [hspan]
    obtain ⟨h1, h2⟩ := hu' (B⁻¹ *ᵥ v)
    rw [hsh, ← ev] at h1 h2
    refine ⟨fun hv hv0 => h1 hv ?_, h2⟩
    rw [← hne, ← ev]
    exact hv0
  · rintro ⟨u, hu0, hu⟩
    refine ⟨B⁻¹ *ᵥ u, ?_, fun v => ?_⟩
    · rw [← hne, mulVec_inv_mulVec hB]; exact hu0
    have hspan : v ∈ Submodule.span ℝ {B⁻¹ *ᵥ u} ↔ B *ᵥ v ∈ Submodule.span ℝ {u} := by
      conv_rhs => rw [← mulVec_inv_mulVec hB u]
      exact (mulVec_mem_span_iff hB _ v).symm
    rw [hspan, hsh, hsh]
    obtain ⟨h1, h2⟩ := hu (B *ᵥ v)
    exact ⟨fun hv hv0 => h1 hv ((hne v).2 hv0), h2⟩

variable (A) in

open Classical in

noncomputable def slowAngle (l₁ l₂ : ℝ) (x : ℤ → ι) : ℝ :=
  if h : ∃ θ, θ ∈ Ico 0 π ∧ HasPastRate A x (dirVec θ) l₂ ∧ x ∈ regularSet A l₁ l₂ then
    h.choose
  else 0

theorem slowAngle_spec {l₁ l₂ : ℝ} {x : ℤ → ι} (hx : x ∈ regularSet A l₁ l₂) :
    slowAngle A l₁ l₂ x ∈ Ico 0 π ∧ HasPastRate A x (dirVec (slowAngle A l₁ l₂ x)) l₂ := by
  have hex : ∃ θ, θ ∈ Ico 0 π ∧ HasPastRate A x (dirVec θ) l₂ ∧ x ∈ regularSet A l₁ l₂ := by
    obtain ⟨θ, hθ, hu⟩ := IsRegular.exists_dirVec hx
    exact ⟨θ, hθ, (hu.2 _).1 (Submodule.mem_span_singleton_self _) hu.1, hx⟩
  rw [slowAngle, dite_eq_left hex]
  exact ⟨hex.choose_spec.1, hex.choose_spec.2.1⟩

theorem slowAngle_of_notMem {l₁ l₂ : ℝ} {x : ℤ → ι} (hx : x ∉ regularSet A l₁ l₂) :
    slowAngle A l₁ l₂ x = 0 := by
  refine (dite_eq_right ?_).trans rfl
  rintro ⟨θ, -, -, h⟩
  exact hx h

theorem isRegularWith_slowAngle {l₁ l₂ : ℝ} (hlt : l₂ < l₁) {x : ℤ → ι}
    (hx : x ∈ regularSet A l₁ l₂) :
    IsRegularWith (A := A) l₁ l₂ x (dirVec (slowAngle A l₁ l₂ x)) := by
  obtain ⟨u, hu⟩ := hx
  exact hu.of_mem_span (hu.mem_span hlt (slowAngle_spec ⟨u, hu⟩).2 le_rfl)
    (dirVec_ne_zero _)

theorem slowAngle_eq {l₁ l₂ : ℝ} (hlt : l₂ < l₁) {x : ℤ → ι} (hx : x ∈ regularSet A l₁ l₂)
    {θ : ℝ} (hθ : θ ∈ Ico 0 π) (hr : HasPastRate A x (dirVec θ) l₂) :
    slowAngle A l₁ l₂ x = θ := by
  have hu := isRegularWith_slowAngle hlt hx
  refine eq_of_cross_dirVec_eq_zero (slowAngle_spec hx).1 hθ ?_
  exact (mem_span_iff_cross hu.1 _).1 (hu.mem_span hlt hr le_rfl)

section Measurability

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in

theorem pastProd_eq_ofFn (x : ℤ → ι) (n : ℕ) :
    pastProd A x n = word A (List.ofFn (block n (shift (-(n : ℤ)) x))) := by
  rw [pastProd, pastWord_eq_futureWord, futureWord_eq_ofFn_block]

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in

theorem continuous_dirVec : Continuous dirVec := by
  unfold dirVec
  refine continuous_pi fun j => ?_
  fin_cases j
  · exact Real.continuous_cos
  · exact Real.continuous_sin

theorem measurable_log_norm_pastProd_dirVec (n : ℕ) :
    Measurable fun p : (ℤ → ι) × ℝ => Real.log ‖pastProd A p.1 n *ᵥ dirVec p.2‖ / n := by
  have hF : Measurable fun q : ℝ × (Fin n → ι) =>
      Real.log ‖word A (List.ofFn q.2) *ᵥ dirVec q.1‖ / n := by
    refine measurable_from_prod_countable_left fun w => ?_
    have hc : Continuous fun θ : ℝ => ‖word A (List.ofFn w) *ᵥ dirVec θ‖ :=
      ((Matrix.mulVecLin (word A (List.ofFn w))).continuous_of_finiteDimensional.comp
        continuous_dirVec).norm
    exact (Real.measurable_log.comp hc.measurable).div_const _
  have hg : Measurable fun p : (ℤ → ι) × ℝ => (p.2, block n (shift (-(n : ℤ)) p.1)) :=
    measurable_snd.prodMk ((measurable_block n).comp ((measurable_shift _).comp measurable_fst))
  have e : (fun p : (ℤ → ι) × ℝ => Real.log ‖pastProd A p.1 n *ᵥ dirVec p.2‖ / n) =
      (fun q : ℝ × (Fin n → ι) => Real.log ‖word A (List.ofFn q.2) *ᵥ dirVec q.1‖ / n) ∘
        fun p : (ℤ → ι) × ℝ => (p.2, block n (shift (-(n : ℤ)) p.1)) := by
    funext p
    rw [Function.comp_apply, pastProd_eq_ofFn]
  rw [e]
  exact hF.comp hg

theorem measurableSet_hasPastRate_dirVec (l : ℝ) :
    MeasurableSet {p : (ℤ → ι) × ℝ | HasPastRate A p.1 (dirVec p.2) l} :=
  measurableSet_tendsto (𝓝 l) fun n => measurable_log_norm_pastProd_dirVec n

theorem measurableSet_hasPastRate (v : Fin 2 → ℝ) (l : ℝ) :
    MeasurableSet {x : ℤ → ι | HasPastRate A x v l} := by
  refine measurableSet_tendsto (𝓝 l) fun n => ?_
  simp only [pastProd_eq_ofFn]
  exact (measurable_comp_block (fun w : Fin n → ι =>
    Real.log ‖word A (List.ofFn w) *ᵥ v‖ / n)).comp (measurable_shift _)

variable (A) in

def angleGraph (l₁ l₂ : ℝ) : Set ((ℤ → ι) × ℝ) :=
  {p | p.2 ∈ Ico 0 π ∧ HasPastRate A p.1 (dirVec p.2) l₂ ∧
    (HasPastRate A p.1 ![1, 0] l₁ ∨ HasPastRate A p.1 ![0, 1] l₁)}

theorem measurableSet_angleGraph (l₁ l₂ : ℝ) : MeasurableSet (angleGraph A l₁ l₂) := by
  refine (measurableSet_Ico.preimage measurable_snd).inter
    ((measurableSet_hasPastRate_dirVec l₂).inter ?_)
  exact ((measurableSet_hasPastRate _ l₁).union (measurableSet_hasPastRate _ l₁)).preimage
    measurable_fst

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in

theorem mem_angleGraph_iff (hA : ∀ i, (A i).det ≠ 0) {l₁ l₂ : ℝ} (hlt : l₂ < l₁)
    (p : (ℤ → ι) × ℝ) :
    p ∈ angleGraph A l₁ l₂ ↔ p.1 ∈ regularSet A l₁ l₂ ∧ slowAngle A l₁ l₂ p.1 = p.2 := by
  constructor
  · rintro ⟨hθ, hr, he⟩
    have hreg : p.1 ∈ regularSet A l₁ l₂ := (isRegular_iff hA hlt p.1).2 ⟨⟨p.2, hθ, hr⟩, he⟩
    exact ⟨hreg, slowAngle_eq hlt hreg hθ hr⟩
  · rintro ⟨hreg, heq⟩
    obtain ⟨-, he⟩ := (isRegular_iff hA hlt p.1).1 hreg
    show p.2 ∈ Ico 0 π ∧ HasPastRate A p.1 (dirVec p.2) l₂ ∧ _
    rw [← heq]
    exact ⟨(slowAngle_spec hreg).1, (slowAngle_spec hreg).2, he⟩

theorem measurableSet_regularSet (hA : ∀ i, (A i).det ≠ 0) {l₁ l₂ : ℝ} (hlt : l₂ < l₁) :
    MeasurableSet (regularSet A l₁ l₂) := by
  have himage : regularSet A l₁ l₂ = Prod.fst '' angleGraph A l₁ l₂ := by
    ext x
    constructor
    · intro hx
      exact ⟨(x, slowAngle A l₁ l₂ x), (mem_angleGraph_iff hA hlt _).2 ⟨hx, rfl⟩, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ((mem_angleGraph_iff hA hlt p).1 hp).1
  rw [himage]
  refine (measurableSet_angleGraph l₁ l₂).image_of_measurable_injOn measurable_fst ?_
  intro p hp q hq hpq
  have h1 := ((mem_angleGraph_iff hA hlt p).1 hp).2
  have h2 := ((mem_angleGraph_iff hA hlt q).1 hq).2
  exact Prod.ext hpq (by rw [← h1, ← h2, hpq])

theorem measurable_slowAngle (hA : ∀ i, (A i).det ≠ 0) {l₁ l₂ : ℝ} (hlt : l₂ < l₁) :
    Measurable (slowAngle A l₁ l₂) := by
  intro s hs
  have hpre : slowAngle A l₁ l₂ ⁻¹' s =
      Prod.fst '' (angleGraph A l₁ l₂ ∩ (univ ×ˢ s)) ∪
        ((regularSet A l₁ l₂)ᶜ ∩ {_x | (0 : ℝ) ∈ s}) := by
    ext x
    simp only [mem_preimage, mem_union, mem_image, mem_inter_iff, mem_prod, mem_univ,
      true_and, mem_compl_iff, mem_ofPred_eq]
    by_cases hx : x ∈ regularSet A l₁ l₂
    · constructor
      · intro h
        exact Or.inl ⟨(x, slowAngle A l₁ l₂ x), ⟨(mem_angleGraph_iff hA hlt _).2 ⟨hx, rfl⟩, h⟩,
          rfl⟩
      · rintro (⟨p, ⟨hp, hps⟩, rfl⟩ | ⟨hx', -⟩)
        · rw [((mem_angleGraph_iff hA hlt p).1 hp).2]; exact hps
        · exact absurd hx hx'
    · rw [slowAngle_of_notMem hx]
      constructor
      · intro h; exact Or.inr ⟨hx, h⟩
      · rintro (⟨p, ⟨hp, -⟩, rfl⟩ | ⟨-, h⟩)
        · exact absurd ((mem_angleGraph_iff hA hlt p).1 hp).1 hx
        · exact h
  rw [hpre]
  refine MeasurableSet.union ?_ ((measurableSet_regularSet hA hlt).compl.inter ?_)
  · refine ((measurableSet_angleGraph l₁ l₂).inter (MeasurableSet.univ.prod hs)
      ).image_of_measurable_injOn measurable_fst ?_
    intro p hp q hq hpq
    have h1 := ((mem_angleGraph_iff hA hlt p).1 hp.1).2
    have h2 := ((mem_angleGraph_iff hA hlt q).1 hq.1).2
    exact Prod.ext hpq (by rw [← h1, ← h2, hpq])
  · by_cases h0 : (0 : ℝ) ∈ s
    · simp [h0]
    · simp [h0]

end Measurability

end MatrixTuple

end FractalGeometry
