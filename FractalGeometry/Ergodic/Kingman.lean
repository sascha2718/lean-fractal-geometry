module

/-
Kingman's subadditive ergodic theorem for integrable subadditive cocycles,
including the possible negative-infinity limit. The proof uses Birkhoff
and the stopping-time arguments of Katznelson-Weiss and Steele.

Reference: J. F. C. Kingman, The ergodic theory of subadditive stochastic
processes, JRSS B 30(3) (1968), 499-510, doi:10.1111/j.2517-6161.1968.tb00749.x.
-/

public import FractalGeometry.Ergodic.Birkhoff
public import Mathlib.Analysis.Subadditive
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

namespace FractalGeometry.Ergodic

open MeasureTheory Filter Topology Set

variable {X : Type*}

def IsSubadditiveCocycle (T : X → X) (f : ℕ → X → ℝ) : Prop :=
  ∀ m n x, f (m + n) x ≤ f m x + f n (T^[m] x)

noncomputable def normalisedCocycle (T : X → X) (f : ℕ → X → ℝ) : ℕ → X → ℝ :=
  fun n x => f n x - birkhoffSum T (f 1) n x

noncomputable def phaseSum (T : X → X) (g : ℕ → X → ℝ) (N n : ℕ) (x : X) : ℝ :=
  ∑ r ∈ Finset.range N, if r < n then g (n - r) (T^[r] x) else 0

def lowerSet (g : ℕ → X → ℝ) (q : ℝ) : Set X :=
  {x | ∃ m : ℕ, ∀ n, 1 ≤ n → n * q - m ≤ g n x}

namespace IsSubadditiveCocycle

variable {T : X → X} {f g : ℕ → X → ℝ}

theorem le_birkhoffSum (hf : IsSubadditiveCocycle T f) {n : ℕ} (hn : 1 ≤ n) (x : X) :
    f n x ≤ birkhoffSum T (f 1) n x := by
  induction n, hn using Nat.le_induction generalizing x with
  | base => simp
  | succ n _ ih =>
    have h := hf 1 n x
    rw [Nat.add_comm 1 n, Function.iterate_one] at h
    rw [birkhoffSum_succ_apply']
    linarith [ih (T x)]

theorem normalised (hf : IsSubadditiveCocycle T f) :
    IsSubadditiveCocycle T (normalisedCocycle T f) := by
  intro m n x
  simp only [normalisedCocycle]
  rw [birkhoffSum_add_right_apply]
  linarith [hf m n x]

theorem normalised_nonpos (hf : IsSubadditiveCocycle T f) {n : ℕ} (hn : 1 ≤ n) (x : X) :
    normalisedCocycle T f n x ≤ 0 := by
  simp only [normalisedCocycle]
  linarith [hf.le_birkhoffSum hn x]

section Nonpos

variable (hg : IsSubadditiveCocycle T g) (hneg : ∀ n, 1 ≤ n → ∀ x, g n x ≤ 0)
include hg hneg

theorem le_drop_left (a b : ℕ) (x : X) : g (a + b) x ≤ g b (T^[a] x) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · linarith [hg a b x, hneg a ha x]

theorem le_drop_right (a b : ℕ) (x : X) : g (a + b) x ≤ g a x := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  · linarith [hg a b x, hneg b hb (T^[a] x)]

theorem le_stopping {q : ℝ} {K : ℕ} {B : Set X}
    (hB : ∀ y, y ∉ B → ∃ n, 1 ≤ n ∧ n ≤ K ∧ g n y ≤ n * q) :
    ∀ N, 1 ≤ N → ∀ x,
      g N x ≤ q * N + |q| * (birkhoffSum T (B.indicator 1) N x + K) := by
  have hcnt : ∀ m y, 0 ≤ birkhoffSum T (B.indicator (1 : X → ℝ)) m y := fun m y =>
    Finset.sum_nonneg fun k _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hq : -|q| ≤ q := neg_abs_le q
  have hq0 : 0 ≤ |q| := abs_nonneg q
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro hN x
  by_cases hNK : N ≤ K
  · have h1 := hneg N hN x
    have h2 : |q| * N ≤ |q| * K := mul_le_mul_of_nonneg_left (by exact_mod_cast hNK) hq0
    have h3 : -(|q| * N) ≤ q * N :=
      by nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    have h4 := mul_nonneg hq0 (hcnt N x)
    nlinarith
  push Not at hNK
  by_cases hx : x ∈ B
  · have hone : birkhoffSum T (B.indicator (1 : X → ℝ)) 1 x = 1 := by
      rw [birkhoffSum_one_apply, Set.indicator_of_mem hx, Pi.one_apply]
    rcases Nat.lt_or_ge N 2 with hN2 | hN2
    · obtain rfl : N = 1 := by omega
      rw [hone]
      have h1 := hneg 1 le_rfl x
      have h2 : 0 ≤ |q| * K := mul_nonneg hq0 (Nat.cast_nonneg K)
      push_cast
      nlinarith
    · obtain ⟨M, rfl⟩ : ∃ M, N = 1 + M := ⟨N - 1, by omega⟩
      have h1 := hg 1 M x
      rw [Function.iterate_one] at h1
      have h2 := ih M (by omega) (by omega) (T x)
      have h3 := hneg 1 le_rfl x
      rw [birkhoffSum_add_right_apply, hone, Function.iterate_one]
      push_cast
      nlinarith
  · obtain ⟨n, hn1, hnK, hn⟩ := hB x hx
    obtain ⟨M, rfl⟩ : ∃ M, N = n + M := ⟨N - n, by omega⟩
    have h1 := hg n M x
    have h2 := ih M (by omega) (by omega) (T^[n] x)
    have h3 := mul_nonneg hq0 (hcnt n x)
    rw [birkhoffSum_add_right_apply]
    push_cast
    nlinarith

theorem mul_le_phaseSum (N : ℕ) {n : ℕ} (hn : 1 ≤ n) (x : X) :
    N * g n x ≤ phaseSum T g N n x := by
  have e : (N : ℝ) * g n x = ∑ _r ∈ Finset.range N, g n x := by simp
  rw [e, phaseSum]
  refine Finset.sum_le_sum fun r _ => ?_
  split_ifs with hr
  · have h := le_drop_left hg hneg r (n - r) x
    rwa [Nat.add_sub_cancel' hr.le] at h
  · exact hneg n hn x

theorem phaseSum_le {N : ℕ} (hN : 1 ≤ N) :
    ∀ n x, phaseSum T g N n x ≤ birkhoffSum T (g N) (n + 1 - N) x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x
  by_cases hsmall : n + 1 < 2 * N
  · have hmN : n + 1 - N ≤ N := by omega
    calc phaseSum T g N n x
        ≤ ∑ r ∈ Finset.range N, if r < n + 1 - N then g N (T^[r] x) else 0 := by
          refine Finset.sum_le_sum fun r _ => ?_
          by_cases hr : r < n + 1 - N
          · rw [ite_eq_left hr, ite_eq_left (by omega)]
            have h := le_drop_right hg hneg N (n - r - N) (T^[r] x)
            rwa [show N + (n - r - N) = n - r by omega] at h
          · rw [ite_eq_right hr]
            split_ifs with hrn
            · exact hneg (n - r) (by omega) _
            · exact le_rfl
      _ = birkhoffSum T (g N) (n + 1 - N) x := by
          rw [← Finset.sum_range_add_sum_Ico _ hmN, birkhoffSum]
          rw [Finset.sum_eq_zero (s := Finset.Ico (n + 1 - N) N) fun r hr => by
            rw [ite_eq_right (by simp only [Finset.mem_Ico] at hr; omega)], add_zero]
          refine Finset.sum_congr rfl fun r hr => ?_
          rw [ite_eq_left (Finset.mem_range.1 hr)]
  · push Not at hsmall
    have key : phaseSum T g N n x ≤
        birkhoffSum T (g N) N x + phaseSum T g N (n - N) (T^[N] x) := by
      rw [phaseSum, phaseSum, birkhoffSum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun r hr => ?_
      have hr' := Finset.mem_range.1 hr
      rw [ite_eq_left (by omega : r < n)]
      by_cases hrn : r < n - N
      · rw [ite_eq_left hrn]
        have h := hg N (n - N - r) (T^[r] x)
        rw [show N + (n - N - r) = n - r by omega, ← Function.iterate_add_apply,
          Nat.add_comm N r, Function.iterate_add_apply] at h
        exact h
      · rw [ite_eq_right hrn, add_zero, show n - r = N by omega]
    have hIH := ih (n - N) (by omega) (T^[N] x)
    rw [show n + 1 - N = N + (n - N + 1 - N) by omega, birkhoffSum_add_right_apply]
    linarith

theorem mul_le_birkhoffSum {N n : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n) (x : X) :
    N * g n x ≤ birkhoffSum T (g N) (n + 1 - N) x :=
  (mul_le_phaseSum hg hneg N hn x).trans (phaseSum_le hg hneg hN n x)

theorem lowerSet_subset_preimage (q : ℝ) : lowerSet g q ⊆ T ⁻¹' lowerSet g q := by
  rintro x ⟨m, hm⟩
  refine ⟨m + ⌈|q|⌉₊, fun n hn => ?_⟩
  have h1 := hg 1 n x
  rw [Nat.add_comm 1 n, Function.iterate_one] at h1
  have h2 := hm (n + 1) (by omega)
  have h3 := hneg 1 le_rfl x
  have h4 : |q| ≤ ⌈|q|⌉₊ := Nat.le_ceil _
  have h5 := neg_abs_le q
  push_cast at h2 ⊢
  linarith

theorem eventually_div_lt_of_tendsto {N : ℕ} (hN : 1 ≤ N) {x : X} {v b : ℝ}
    (hx : Tendsto (fun n : ℕ => birkhoffSum T (g N) (n + 1 - N) x / (N * n)) atTop (𝓝 v))
    (hvb : v < b) : ∀ᶠ n : ℕ in atTop, g n x / n < b := by
  filter_upwards [hx.eventually (gt_mem_nhds hvb), eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hdet := mul_le_birkhoffSum hg hneg (T := T) hN hn1 x
  rw [div_lt_iff₀ (by positivity)] at hn
  rw [div_lt_iff₀ hnpos]
  by_contra hcon
  push Not at hcon
  have := mul_le_mul_of_nonneg_left hcon hNpos.le
  nlinarith

end Nonpos

end IsSubadditiveCocycle

theorem eventually_lt_div_of_le {g : ℕ → X → ℝ} {x : X} {q a : ℝ} {m : ℕ}
    (hm : ∀ n, 1 ≤ n → n * q - m ≤ g n x) (haq : a < q) :
    ∀ᶠ n : ℕ in atTop, a < g n x / n := by
  have hq' : 0 < q - a := by linarith
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, (m : ℝ) / (q - a) < n₀ := exists_nat_gt _
  filter_upwards [eventually_ge_atTop (n₀ + 1)] with n hn
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn0 : (n₀ : ℝ) < n := by exact_mod_cast (show n₀ < n by omega)
  rw [lt_div_iff₀ hnpos]
  have h1 := hm n hn1
  rw [div_lt_iff₀ hq'] at hn₀
  nlinarith

theorem tendsto_birkhoffSum_phase {T : X → X} {φ : X → ℝ} {x : X} {v : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hx : Tendsto (fun m : ℕ => birkhoffAverage ℝ T φ m x) atTop (𝓝 v)) :
    Tendsto (fun n : ℕ => birkhoffSum T φ (n + 1 - N) x / (N * n)) atTop (𝓝 (v / N)) := by
  have hm : Tendsto (fun n : ℕ => n + 1 - N) atTop atTop :=
    (tendsto_sub_atTop_nat N).comp (tendsto_add_atTop_nat 1)
  have hratio : Tendsto (fun n : ℕ => ((n + 1 - N : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) + (1 - N) / n) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat _)
    rw [add_zero] at h1
    refine h1.congr' ((eventually_ge_atTop N).mono fun n hn => ?_)
    have hn0 : (n : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hN.trans hn
      positivity
    dsimp only
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  have hprod := ((hx.comp hm).mul hratio).div_const (N : ℝ)
  rw [mul_one] at hprod
  refine hprod.congr fun n => ?_
  simp only [Function.comp_apply, birkhoffAverage, smul_eq_mul]
  rcases Nat.eq_zero_or_pos (n + 1 - N) with h0 | hpos
  · rw [h0]
    simp
  · have hpos' : ((n + 1 - N : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      field_simp

section Measure

variable [MeasurableSpace X] {μ : Measure X} {T : X → X}

theorem integral_birkhoffSum (hT : MeasurePreserving T μ μ) {φ : X → ℝ} (hφ : Integrable φ μ)
    (n : ℕ) : ∫ x, birkhoffSum T φ n x ∂μ = n * ∫ x, φ x ∂μ := by
  have hk : ∀ k, ∫ x, φ (T^[k] x) ∂μ = ∫ x, φ x ∂μ := fun k => by
    have h := hT.iterate k
    rw [← integral_map h.aemeasurable (h.map_eq.symm ▸ hφ.aestronglyMeasurable), h.map_eq]
  simp only [birkhoffSum]
  rw [integral_finsetSum (Finset.range n) (f := fun k x => φ (T^[k] x))
    fun k _ => (hT.iterate k).integrable_comp_of_integrable hφ]
  simp [hk]

theorem IsSubadditiveCocycle.subadditive_integral {f : ℕ → X → ℝ}
    (hf : IsSubadditiveCocycle T f) (hT : MeasurePreserving T μ μ)
    (hint : ∀ n, Integrable (f n) μ) : Subadditive fun n : ℕ => ∫ x, f n x ∂μ := by
  intro m n
  have hint' : Integrable (fun x => f n (T^[m] x)) μ :=
    (hT.iterate m).integrable_comp_of_integrable (hint n)
  have hk : ∫ x, f n (T^[m] x) ∂μ = ∫ x, f n x ∂μ := by
    have h := hT.iterate m
    rw [← integral_map h.aemeasurable (h.map_eq.symm ▸ (hint n).aestronglyMeasurable),
      h.map_eq]
  calc ∫ x, f (m + n) x ∂μ ≤ ∫ x, (f m x + f n (T^[m] x)) ∂μ :=
        integral_mono (hint _) ((hint m).add hint') fun x => hf m n x
    _ = _ := by rw [integral_add (hint m) hint', hk]

theorem measurableSet_lowerSet {g : ℕ → X → ℝ} (hmeas : ∀ n, Measurable (g n)) (q : ℝ) :
    MeasurableSet (lowerSet g q) := by
  simp only [lowerSet, Set.ofPred_exists, Set.ofPred_forall]
  refine MeasurableSet.iUnion fun m => MeasurableSet.iInter fun n =>
    MeasurableSet.iInter fun _ => ?_
  exact measurableSet_le measurable_const (hmeas n)

namespace IsSubadditiveCocycle

variable {g : ℕ → X → ℝ} (hg : IsSubadditiveCocycle T g)
  (hneg : ∀ n, 1 ≤ n → ∀ x, g n x ≤ 0) (hmeas : ∀ n, Measurable (g n))
  (hint : ∀ n, Integrable (g n) μ)
include hg hneg hmeas hint

theorem measure_pos_of_lt [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ) {c q : ℝ}
    (hμ : 0 < μ.real univ) (hc : ∀ n, 1 ≤ n → c * μ.real univ ≤ (∫ x, g n x ∂μ) / n)
    (hq : q < c) : 0 < μ {y | ∀ n, 1 ≤ n → n * q < g n y} := by
  set B : ℕ → Set X := fun K => {y | ∀ n, 1 ≤ n → n ≤ K → n * q < g n y} with hBdef
  have hBm : ∀ K, MeasurableSet (B K) := fun K => by
    simp only [hBdef, Set.ofPred_forall]
    refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => ?_
    exact measurableSet_lt measurable_const (hmeas n)
  have hanti : Antitone B := fun K K' h y hy n h1 h2 => hy n h1 (h2.trans h)
  have hinter : (⋂ K, B K) = {y | ∀ n, 1 ≤ n → n * q < g n y} := by
    ext y
    simp only [hBdef, Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun h n hn => h n n hn le_rfl, fun h K n hn _ => h n hn⟩
  by_contra hD
  have hD0 : μ {y | ∀ n, 1 ≤ n → n * q < g n y} = 0 := not_lt.1 hD |>.antisymm zero_le
  have htend := tendsto_measure_iInter_atTop (fun K => (hBm K).nullMeasurableSet) hanti
    ⟨0, measure_ne_top μ _⟩
  rw [hinter, hD0] at htend
  have htend' : Tendsto (fun K => μ.real (B K)) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htend
    simpa [Function.comp_def, measureReal_def] using this
  set w := μ.real univ with hw
  have hcq : 0 < (c - q) * w / 2 := by
    have : 0 < c - q := by linarith
    positivity
  obtain ⟨K, hK⟩ := ((htend'.const_mul |q|).eventually
    (gt_mem_nhds (by rw [mul_zero]; exact hcq))).exists
  have hbound : ∀ N : ℕ, 1 ≤ N → c * w ≤ q * w + |q| * μ.real (B K) + |q| * K * w / N := by
    intro N hN
    have hdet := le_stopping hg hneg (q := q) (K := K) (B := B K) (fun y hy => by
      simp only [hBdef, Set.mem_ofPred_eq, not_forall, not_lt] at hy
      obtain ⟨n, hn1, hnK, hn⟩ := hy
      exact ⟨n, hn1, hnK, hn⟩) N hN
    have hind : Integrable ((B K).indicator (1 : X → ℝ)) μ :=
      (integrable_const (1 : ℝ)).indicator (hBm K)
    have hS : Integrable (birkhoffSum T ((B K).indicator (1 : X → ℝ)) N) μ :=
      integrable_birkhoffSum hT hind N
    have h1 : Integrable (fun x => birkhoffSum T ((B K).indicator (1 : X → ℝ)) N x + (K : ℝ))
        μ := hS.add (integrable_const _)
    have h2 : Integrable (fun x => q * N + |q| *
        (birkhoffSum T ((B K).indicator (1 : X → ℝ)) N x + (K : ℝ))) μ :=
      (integrable_const _).add (h1.const_mul _)
    have hR : ∫ x, (q * N + |q| * (birkhoffSum T ((B K).indicator (1 : X → ℝ)) N x + K)) ∂μ
        = w * (q * N) + |q| * (N * μ.real (B K) + w * K) := by
      rw [integral_add (integrable_const _) (h1.const_mul _), integral_const,
        integral_const_mul, integral_add hS (integrable_const _), integral_birkhoffSum hT hind,
        integral_indicator_one (hBm K), integral_const]
      simp only [smul_eq_mul, hw]
    have hle : ∫ x, g N x ∂μ ≤ w * (q * N) + |q| * (N * μ.real (B K) + w * K) :=
      hR ▸ integral_mono (hint N) h2 hdet
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have h3 := hc N hN
    rw [le_div_iff₀ hN'] at h3
    rw [show q * w + |q| * μ.real (B K) + |q| * K * w / N =
      (w * (q * N) + |q| * (N * μ.real (B K) + w * K)) / N by field_simp; ring,
      le_div_iff₀ hN']
    linarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ, |q| * K * w / ((c - q) * w / 2) < N := exists_nat_gt _
  have hN1 : 1 ≤ N := by
    have : (0 : ℝ) ≤ |q| * K * w / ((c - q) * w / 2) :=
      div_nonneg (mul_nonneg (mul_nonneg (abs_nonneg q) (Nat.cast_nonneg K)) hμ.le) hcq.le
    exact_mod_cast (show (0 : ℝ) < N by linarith)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN1
  have h2 : |q| * K * w / N < (c - q) * w / 2 := by
    rw [div_lt_iff₀ hN']
    rw [div_lt_iff₀ hcq] at hN
    linarith
  linarith [hbound N hN1]

theorem ae_lower [IsProbabilityMeasure μ] (hT : Ergodic T μ) {c q : ℝ}
    (hc : ∀ n, 1 ≤ n → c ≤ (∫ x, g n x ∂μ) / n) (hq : q < c) :
    ∀ᵐ x ∂μ, x ∈ lowerSet g q := by
  set G : Set X := lowerSet g q with hGdef
  have hGm : MeasurableSet G := measurableSet_lowerSet hmeas q
  have hsub : G ⊆ T ⁻¹' G := lowerSet_subset_preimage hg hneg q
  have hpos := measure_pos_of_lt hg hneg hmeas hint hT.toMeasurePreserving (c := c)
    (by simp) (fun n hn => by simpa using hc n hn) hq
  have hDG : {y | ∀ n, 1 ≤ n → n * q < g n y} ⊆ G := fun y hy =>
    ⟨0, fun n hn => by simpa using (hy n hn).le⟩
  rcases hT.ae_empty_or_univ_of_ae_le_preimage hGm.nullMeasurableSet hsub.eventuallyLE with
    h | h
  · have h0 : μ G = 0 := by rw [measure_congr h, measure_empty]
    exact absurd (h0 ▸ measure_mono hDG) (not_le.2 hpos)
  · rw [ae_eq_univ] at h
    exact (measure_eq_zero_iff_ae_notMem.1 h).mono fun x hx => not_not.1 hx

omit hg hneg hmeas in

theorem ae_upper [IsProbabilityMeasure μ] (hT : Ergodic T μ) {N : ℕ} (hN : 1 ≤ N) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => birkhoffSum T (g N) (n + 1 - N) x / (N * n)) atTop
      (𝓝 ((∫ x, g N x ∂μ) / N)) :=
  (birkhoff_ergodic hT (hint N)).mono fun _ hx => tendsto_birkhoffSum_phase hN hx

theorem tendsto_of_nonpos [IsProbabilityMeasure μ] (hT : Ergodic T μ) {c : ℝ}
    (hc : ∀ n, 1 ≤ n → c ≤ (∫ x, g n x ∂μ) / n)
    (hlim : Tendsto (fun n : ℕ => (∫ x, g n x ∂μ) / n) atTop (𝓝 c)) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => g n x / n) atTop (𝓝 c) := by
  have hlow : ∀ᵐ x ∂μ, ∀ q : ℚ, (q : ℝ) < c → x ∈ lowerSet g q :=
    ae_all_iff.2 fun q => by
      by_cases hq : (q : ℝ) < c
      · exact (ae_lower hg hneg hmeas hint hT hc hq).mono fun x hx _ => hx
      · exact Eventually.of_forall fun x h => absurd h hq
  have hup : ∀ᵐ x ∂μ, ∀ N : ℕ, Tendsto (fun n : ℕ => birkhoffSum T (g (N + 1)) (n + 1 - (N + 1))
      x / ((N + 1 : ℕ) * n)) atTop (𝓝 ((∫ x, g (N + 1) x ∂μ) / (N + 1 : ℕ))) :=
    ae_all_iff.2 fun N => ae_upper hint hT (Nat.le_add_left 1 N)
  filter_upwards [hlow, hup] with x hxl hxu
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨q, haq, hqc⟩ := exists_rat_btwn ha
    obtain ⟨m, hm⟩ := hxl q hqc
    exact eventually_lt_div_of_le hm haq
  · obtain ⟨N, hN⟩ := ((hlim.eventually (gt_mem_nhds hb)).and (eventually_ge_atTop 1)).exists
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    exact eventually_div_lt_of_tendsto hg hneg (Nat.le_add_left 1 N') (hxu N') hN.1

theorem ae_lower_of_invariant [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ) {E : Set X}
    (hE : MeasurableSet E) (hTE : T ⁻¹' E = E) {q q' : ℝ} (hqq : q' < q)
    (hF : ∀ F : Set X, MeasurableSet F → T ⁻¹' F = F → F ⊆ E → ∀ n, 1 ≤ n →
      q * μ.real F ≤ (∫ x in F, g n x ∂μ) / n) :
    ∀ᵐ x ∂μ, x ∈ E → x ∈ lowerSet g q' := by
  set G : Set X := lowerSet g q' with hGdef
  have hGm : MeasurableSet G := measurableSet_lowerSet hmeas q'
  have hsub : G ⊆ T ⁻¹' G := lowerSet_subset_preimage hg hneg q'
  set F : Set X := E \ G with hFdef
  have hFm : MeasurableSet F := hE.diff hGm
  have hTF : T ⁻¹' F ⊆ F := by
    intro x hx
    simp only [hFdef, Set.mem_preimage, Set.mem_sdiff] at hx ⊢
    refine ⟨?_, fun hxG => hx.2 (hsub hxG)⟩
    rw [← hTE]
    exact hx.1
  set F₀ : Set X := ⋂ k : ℕ, T^[k] ⁻¹' F with hF₀def
  have hFkm : ∀ k, MeasurableSet (T^[k] ⁻¹' F) := fun k => (hT.measurable.iterate k) hFm
  have hF₀m : MeasurableSet F₀ := MeasurableSet.iInter hFkm
  have hTF₀ : T ⁻¹' F₀ = F₀ := by
    ext x
    simp only [hF₀def, Set.mem_preimage, Set.mem_iInter]
    constructor
    · intro h k
      cases k with
      | zero => exact hTF (by simpa using h 0)
      | succ k => rw [Function.iterate_succ_apply]; exact h k
    · intro h k
      rw [← Function.iterate_succ_apply]
      exact h (k + 1)
  have hF₀F : F₀ ⊆ F := fun x hx => by simpa using Set.mem_iInter.1 hx 0
  have hF₀0 : μ F₀ = 0 := by
    by_contra hne
    have hν : MeasurePreserving T (μ.restrict F₀) (μ.restrict F₀) := by
      have := hT.restrict_preimage hF₀m
      rwa [hTF₀] at this
    have hw : 0 < (μ.restrict F₀).real univ := by
      rw [measureReal_restrict_apply_univ]
      exact ENNReal.toReal_pos hne (measure_ne_top μ _)
    have hpos := measure_pos_of_lt hg hneg hmeas (fun n => (hint n).restrict) hν (c := q)
      (q := q') hw (fun n hn => by
        rw [measureReal_restrict_apply_univ]
        exact hF F₀ hF₀m hTF₀ (hF₀F.trans Set.sdiff_subset) n hn) hqq
    rw [Measure.restrict_apply' hF₀m] at hpos
    have hempty : {y | ∀ n, 1 ≤ n → n * q' < g n y} ∩ F₀ = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hy hyF₀
      exact (hF₀F hyF₀).2 ⟨0, fun n hn => by simpa using (hy n hn).le⟩
    rw [hempty, measure_empty] at hpos
    exact lt_irrefl _ hpos
  have hanti : Antitone fun k : ℕ => T^[k] ⁻¹' F := antitone_nat_of_succ_le fun k x hx => by
    rw [Set.mem_preimage, Function.iterate_succ_apply'] at hx
    exact hTF hx
  have ht := tendsto_measure_iInter_atTop (fun k => (hFkm k).nullMeasurableSet) hanti
    ⟨0, measure_ne_top μ _⟩
  have hconst : ∀ k, μ (T^[k] ⁻¹' F) = μ F := fun k =>
    (hT.iterate k).measure_preimage hFm.nullMeasurableSet
  have hμF : μ F = 0 := by
    have h1 : Tendsto (fun _ : ℕ => μ F) atTop (𝓝 (μ F₀)) := ht.congr fun k => hconst k
    rw [← hF₀0]
    exact tendsto_nhds_unique tendsto_const_nhds h1
  refine (measure_eq_zero_iff_ae_notMem.1 hμF).mono fun x hx hxE => ?_
  by_contra hxG
  exact hx ⟨hxE, hxG⟩

theorem tendsto_or_tendsto_atBot_of_nonpos [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) :
    ∀ᵐ x ∂μ, (∃ L : ℝ, Tendsto (fun n : ℕ => g n x / n) atTop (𝓝 L)) ∨
      Tendsto (fun n : ℕ => g n x / n) atTop atBot := by
  set h : ℕ → X → ℝ := fun N x =>
    (μ[g (N + 1) | MeasurableSpace.invariants T]) x / ((N + 1 : ℕ) : ℝ) with hhdef
  have hhm : ∀ N, Measurable[MeasurableSpace.invariants T] (h N) := fun N =>
    (stronglyMeasurable_condExp.measurable).div_const _
  have hup : ∀ᵐ x ∂μ, ∀ N : ℕ, Tendsto (fun n : ℕ => birkhoffSum T (g (N + 1)) (n + 1 - (N + 1))
      x / ((N + 1 : ℕ) * n)) atTop (𝓝 (h N x)) :=
    ae_all_iff.2 fun N => (birkhoff_ae hT (hint (N + 1))).mono fun _ hx =>
      tendsto_birkhoffSum_phase (Nat.le_add_left 1 N) hx
  have hlow : ∀ᵐ x ∂μ, ∀ q q' : ℚ, (q' : ℝ) < q → (∀ N, (q : ℝ) < h N x) →
      x ∈ lowerSet g q' := by
    refine ae_all_iff.2 fun q => ae_all_iff.2 fun q' => ?_
    by_cases hqq : (q' : ℝ) < q
    · set E : Set X := {x | ∀ N, (q : ℝ) < h N x} with hEdef
      have hEI : MeasurableSet[MeasurableSpace.invariants T] E := by
        simp only [hEdef, Set.ofPred_forall]
        exact MeasurableSet.iInter fun N => measurableSet_lt measurable_const (hhm N)
      have hE : MeasurableSet E := MeasurableSpace.invariants_le T _ hEI
      have hTE : T ⁻¹' E = E := (MeasurableSpace.measurableSet_invariants.1 hEI).2
      have key := ae_lower_of_invariant hg hneg hmeas hint hT hE hTE hqq
        (fun F hF hTF hFE n hn => by
          obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
          have hFI : MeasurableSet[MeasurableSpace.invariants T] F :=
            MeasurableSpace.measurableSet_invariants.2 ⟨hF, hTF⟩
          have hNpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
          have hcond : Integrable (μ[g (N + 1) | MeasurableSpace.invariants T]) μ :=
            integrable_condExp
          rw [← setIntegral_condExp (MeasurableSpace.invariants_le T) (hint (N + 1)) hFI]
          have he : ∫ x in F, μ[g (N + 1) | MeasurableSpace.invariants T] x ∂μ =
              ((N + 1 : ℕ) : ℝ) * ∫ x in F, h N x ∂μ := by
            rw [← integral_const_mul]
            refine setIntegral_congr_fun hF fun x _ => ?_
            simp only [hhdef]
            field_simp
          rw [he, mul_div_cancel_left₀ _ hNpos.ne']
          calc q * μ.real F = ∫ _ in F, (q : ℝ) ∂μ := by
                rw [setIntegral_const, smul_eq_mul, mul_comm]
            _ ≤ ∫ x in F, h N x ∂μ :=
                setIntegral_mono_on (integrableOn_const (measure_ne_top μ _))
                  (hcond.div_const _).integrableOn hF fun x hx => (hFE hx N).le)
      exact key.mono fun x hx _ hxE => hx hxE
    · exact Eventually.of_forall fun x h => absurd h hqq
  filter_upwards [hup, hlow] with x hxu hxl
  by_cases hbdd : BddBelow (Set.range fun N => h N x)
  · left
    refine ⟨⨅ N, h N x, tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩⟩
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn ha
      obtain ⟨q', hq'1, hq'2⟩ := exists_rat_btwn hq1
      obtain ⟨m, hm⟩ := hxl q q' hq'2 fun N => hq2.trans_le (ciInf_le hbdd N)
      exact eventually_lt_div_of_le hm hq'1
    · obtain ⟨N, hN⟩ := exists_lt_of_ciInf_lt hb
      exact eventually_div_lt_of_tendsto hg hneg (Nat.le_add_left 1 N) (hxu N) hN
  · right
    rw [tendsto_atBot]
    intro b
    obtain ⟨N, hN⟩ : ∃ N, h N x < b := by
      by_contra hcon
      push Not at hcon
      exact hbdd ⟨b, by rintro _ ⟨N, rfl⟩; exact hcon N⟩
    exact (eventually_div_lt_of_tendsto hg hneg (Nat.le_add_left 1 N) (hxu N) hN).mono
      fun n hn => hn.le

end IsSubadditiveCocycle

theorem kingman_ergodic [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) {f : ℕ → X → ℝ} (hf : IsSubadditiveCocycle T f)
    (hmeas : ∀ n, Measurable (f n)) (hint : ∀ n, Integrable (f n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, f n x ∂μ) / n)) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => f n x / n) atTop
      (𝓝 (sInf ((fun n : ℕ => (∫ x, f n x ∂μ) / n) '' Set.Ici 1))) := by
  have hT' := hT.toMeasurePreserving
  have hsub := hf.subadditive_integral hT' hint
  set γ := sInf ((fun n : ℕ => (∫ x, f n x ∂μ) / n) '' Set.Ici 1) with hγ
  have hlimγ : Tendsto (fun n : ℕ => (∫ x, f n x ∂μ) / n) atTop (𝓝 γ) := by
    have := hsub.tendsto_lim hbdd
    rwa [Subadditive.lim] at this
  have hleγ : ∀ n : ℕ, 1 ≤ n → γ ≤ (∫ x, f n x ∂μ) / n := fun n hn => by
    have := hsub.lim_le_div hbdd (by omega : n ≠ 0)
    rwa [Subadditive.lim] at this
  set g := normalisedCocycle T f
  have hS : ∀ n, Integrable (birkhoffSum T (f 1) n) μ := integrable_birkhoffSum hT' (hint 1)
  have hgint : ∀ n, Integrable (g n) μ := fun n => (hint n).sub (hS n)
  have hgmeas : ∀ n, Measurable (g n) := fun n =>
    (hmeas n).sub (measurable_birkhoffSum hT'.measurable (hmeas 1) n)
  have hgI : ∀ n : ℕ, 1 ≤ n →
      (∫ x, g n x ∂μ) / n = (∫ x, f n x ∂μ) / n - ∫ x, f 1 x ∂μ := fun n hn => by
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    simp only [g, normalisedCocycle]
    rw [integral_sub (hint n) (hS n), integral_birkhoffSum hT' (hint 1)]
    field_simp
  have hgc : ∀ n, 1 ≤ n → γ - ∫ x, f 1 x ∂μ ≤ (∫ x, g n x ∂μ) / n := fun n hn => by
    rw [hgI n hn]
    linarith [hleγ n hn]
  have hglim : Tendsto (fun n : ℕ => (∫ x, g n x ∂μ) / n) atTop
      (𝓝 (γ - ∫ x, f 1 x ∂μ)) :=
    (hlimγ.sub_const _).congr' ((eventually_ge_atTop 1).mono fun n hn => (hgI n hn).symm)
  have hg := hf.normalised.tendsto_of_nonpos (fun n hn x => hf.normalised_nonpos hn x) hgmeas
    hgint hT hgc hglim
  filter_upwards [hg, birkhoff_ergodic hT (hint 1)] with x hx hb
  have := hx.add hb
  rw [sub_add_cancel] at this
  refine this.congr fun n => ?_
  simp only [normalisedCocycle, birkhoffAverage, smul_eq_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    ring

theorem kingman_ergodic_of_tendsto [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) {f : ℕ → X → ℝ} (hf : IsSubadditiveCocycle T f)
    (hmeas : ∀ n, Measurable (f n)) (hint : ∀ n, Integrable (f n) μ) {L : ℝ}
    (hL : Tendsto (fun n : ℕ => (∫ x, f n x ∂μ) / n) atTop (𝓝 L)) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => f n x / n) atTop (𝓝 L) := by
  have hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, f n x ∂μ) / n) := hL.bddBelow_range
  have hlim := (hf.subadditive_integral hT.toMeasurePreserving hint).tendsto_lim hbdd
  rw [Subadditive.lim] at hlim
  rw [tendsto_nhds_unique hL hlim]
  exact kingman_ergodic hT hf hmeas hint hbdd

theorem kingman_ae [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ) {f : ℕ → X → ℝ}
    (hf : IsSubadditiveCocycle T f) (hmeas : ∀ n, Measurable (f n))
    (hint : ∀ n, Integrable (f n) μ) :
    ∀ᵐ x ∂μ, (∃ L : ℝ, Tendsto (fun n : ℕ => f n x / n) atTop (𝓝 L)) ∨
      Tendsto (fun n : ℕ => f n x / n) atTop atBot := by
  set g := normalisedCocycle T f with hgdef
  have hS : ∀ n, Integrable (birkhoffSum T (f 1) n) μ := integrable_birkhoffSum hT (hint 1)
  have hgint : ∀ n, Integrable (g n) μ := fun n => (hint n).sub (hS n)
  have hgmeas : ∀ n, Measurable (g n) := fun n =>
    (hmeas n).sub (measurable_birkhoffSum hT.measurable (hmeas 1) n)
  have hg := hf.normalised.tendsto_or_tendsto_atBot_of_nonpos
    (fun n hn x => hf.normalised_nonpos hn x) hgmeas hgint hT
  filter_upwards [hg, birkhoff_ae hT (hint 1)] with x hx hb
  have he : ∀ n : ℕ, g n x / n + birkhoffAverage ℝ T (f 1) n x = f n x / n := fun n => by
    simp only [hgdef, normalisedCocycle, birkhoffAverage, smul_eq_mul]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
      ring
  rcases hx with ⟨L, hL⟩ | hbot
  · exact Or.inl ⟨_, (hL.add hb).congr he⟩
  · exact Or.inr ((hbot.atBot_add hb).congr he)

end Measure

end FractalGeometry.Ergodic
