module

public import Mathlib
public import FractalGeometry.Ergodic.Birkhoff

@[expose] public section

namespace FractalGeometry

open FractalGeometry.Ergodic

open MeasureTheory Filter Topology Set

section TailSup

variable {X : Type*}

noncomputable def tailSup (f : ℕ → X → ℝ) (g : X → ℝ) (N : ℕ) (x : X) : ℝ :=
  (⨆ k, ENNReal.ofReal |f (N + k) x - g x|).toReal

theorem tailSup_nonneg (f : ℕ → X → ℝ) (g : X → ℝ) (N : ℕ) (x : X) : 0 ≤ tailSup f g N x :=
  ENNReal.toReal_nonneg

theorem iSup_ofReal_abs_sub_le {f : ℕ → X → ℝ} {g F : X → ℝ} {x : X}
    (hf : ∀ k, |f k x| ≤ F x) (hg : |g x| ≤ F x) (N : ℕ) :
    ⨆ k, ENNReal.ofReal |f (N + k) x - g x| ≤ ENNReal.ofReal (2 * F x) :=
  iSup_le fun k => ENNReal.ofReal_le_ofReal <|
    (abs_sub (f (N + k) x) (g x)).trans (by linarith [hf (N + k)])

theorem tailSup_le {f : ℕ → X → ℝ} {g F : X → ℝ} {x : X} (hf : ∀ k, |f k x| ≤ F x)
    (hg : |g x| ≤ F x) (N : ℕ) : tailSup f g N x ≤ 2 * F x :=
  ENNReal.toReal_le_of_le_ofReal (by linarith [(abs_nonneg (g x)).trans hg])
    (iSup_ofReal_abs_sub_le hf hg N)

theorem abs_sub_le_tailSup {f : ℕ → X → ℝ} {g F : X → ℝ} {x : X} (hf : ∀ k, |f k x| ≤ F x)
    (hg : |g x| ≤ F x) (N k : ℕ) : |f (N + k) x - g x| ≤ tailSup f g N x := by
  have hne : ⨆ k, ENNReal.ofReal |f (N + k) x - g x| ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_ofReal_abs_sub_le hf hg N)
  exact (ENNReal.ofReal_le_iff_le_toReal hne).1
    (le_iSup (fun k => ENNReal.ofReal |f (N + k) x - g x|) k)

theorem tendsto_tailSup {f : ℕ → X → ℝ} {g : X → ℝ} {x : X}
    (hlim : Tendsto (fun k => f k x) atTop (𝓝 (g x))) :
    Tendsto (fun N => tailSup f g N x) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 hlim (ε / 2) (half_pos hε)
  refine ⟨N₀, fun N hN => ?_⟩
  have hle : tailSup f g N x ≤ ε / 2 := by
    refine ENNReal.toReal_le_of_le_ofReal (half_pos hε).le (iSup_le fun k => ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    have := hN₀ (N + k) (by omega)
    rw [Real.dist_eq] at this
    exact this.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tailSup_nonneg f g N x)]
  linarith

variable [MeasurableSpace X]

theorem measurable_tailSup {f : ℕ → X → ℝ} {g : X → ℝ} (hf : ∀ k, Measurable (f k))
    (hg : Measurable g) (N : ℕ) : Measurable (tailSup f g N) :=
  (Measurable.iSup fun k =>
    (continuous_abs.measurable.comp ((hf (N + k)).sub hg)).ennreal_ofReal).ennreal_toReal

end TailSup

section Maker

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {T : X → X}

theorem maker_ae (hT : MeasurePreserving T μ μ) {f : ℕ → X → ℝ} {g F : X → ℝ}
    (hf : ∀ k, Measurable (f k)) (hg : Measurable g) (hF : Integrable F μ)
    (hbound : ∀ᵐ x ∂μ, ∀ k, |f k x| ≤ F x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => f k x) atTop (𝓝 (g x))) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, f k (T^[k] x)) atTop
      (𝓝 ((μ[g | MeasurableSpace.invariants T]) x)) := by

  have hgF : ∀ᵐ x ∂μ, |g x| ≤ F x := by
    filter_upwards [hbound, hlim] with x hb hl
    exact le_of_tendsto ((continuous_abs.tendsto _).comp hl) (Eventually.of_forall hb)
  have hgi : Integrable g μ :=
    hF.mono' hg.aestronglyMeasurable (by simpa [Real.norm_eq_abs] using hgF)

  have hgood : ∀ᵐ x ∂μ, (∀ k, |f k x| ≤ F x) ∧ |g x| ≤ F x ∧
      Tendsto (fun k => f k x) atTop (𝓝 (g x)) := by
    filter_upwards [hbound, hgF, hlim] with x h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have horbit : ∀ᵐ x ∂μ, ∀ k, (∀ j, |f j (T^[k] x)| ≤ F (T^[k] x)) ∧
      |g (T^[k] x)| ≤ F (T^[k] x) :=
    ae_all_iff.2 fun k => (hT.iterate k).quasiMeasurePreserving.ae
      (p := fun y => (∀ j, |f j y| ≤ F y) ∧ |g y| ≤ F y) (hgood.mono fun _ hx => ⟨hx.1, hx.2.1⟩)

  set H : ℕ → X → ℝ := tailSup f g with hH
  have hHm : ∀ N, Measurable (H N) := measurable_tailSup hf hg
  have hHbd : ∀ N, ∀ᵐ x ∂μ, ‖H N x‖ ≤ 2 * F x := fun N => by
    filter_upwards [hgood] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (tailSup_nonneg f g N x)]
    exact tailSup_le hx.1 hx.2.1 N
  have hHi : ∀ N, Integrable (H N) μ := fun N =>
    (hF.const_mul 2).mono' (hHm N).aestronglyMeasurable (hHbd N)
  have hHint : Tendsto (fun N => ∫ x, H N x ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun x => 2 * F x)
      (fun N => (hHm N).aestronglyMeasurable) (hF.const_mul 2) hHbd
      (hgood.mono fun x hx => tendsto_tailSup hx.2.2)
    simpa using h

  have hB : ∀ᵐ x ∂μ, ∀ N, Tendsto (fun n => birkhoffAverage ℝ T (H N) n x) atTop
      (𝓝 ((μ[H N | MeasurableSpace.invariants T]) x)) :=
    ae_all_iff.2 fun N => birkhoff_ae hT (hHi N)

  set e : ℕ → X → ℝ := fun n x =>
    (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, |f k (T^[k] x) - g (T^[k] x)| with he
  have he0 : ∀ n x, 0 ≤ e n x := fun n x =>
    mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg n)) (Finset.sum_nonneg fun k _ => abs_nonneg _)
  have hem : ∀ n, Measurable (e n) := fun n =>
    measurable_const.mul (Finset.measurable_sum _ fun k _ =>
      continuous_abs.measurable.comp
        (((hf k).comp (hT.measurable.iterate k)).sub (hg.comp (hT.measurable.iterate k))))

  have hbd : ∀ᵐ x ∂μ, ∀ N, limsup (fun n => ENNReal.ofReal (e n x)) atTop ≤
      ENNReal.ofReal ((μ[H N | MeasurableSpace.invariants T]) x) := by
    filter_upwards [horbit, hB] with x hx hBx N
    set C := ∑ k ∈ Finset.range N, |f k (T^[k] x) - g (T^[k] x)| with hC
    have hle : ∀ n, e n x ≤ (n : ℝ)⁻¹ * C + birkhoffAverage ℝ T (H N) n x := fun n => by
      have hterm : ∀ k ∈ Finset.range n, |f k (T^[k] x) - g (T^[k] x)| ≤
          (if k < N then |f k (T^[k] x) - g (T^[k] x)| else 0) + H N (T^[k] x) := by
        intro k _
        split_ifs with hk
        · linarith [tailSup_nonneg f g N (T^[k] x)]
        · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hk)
          rw [zero_add]
          exact abs_sub_le_tailSup (hx (N + j)).1 (hx (N + j)).2 N j
      have hsplit : ∑ k ∈ Finset.range n,
          (if k < N then |f k (T^[k] x) - g (T^[k] x)| else 0) ≤ C := by
        rw [hC, ← Finset.sum_filter]
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_)
          (fun k _ _ => abs_nonneg _)
        rw [Finset.mem_filter] at hk
        exact Finset.mem_range.2 hk.2
      have hsum := (Finset.sum_le_sum hterm).trans_eq (Finset.sum_add_distrib)
      rw [he, birkhoffAverage, birkhoffSum, smul_eq_mul, ← mul_add]
      exact mul_le_mul_of_nonneg_left (hsum.trans (add_le_add_left hsplit _))
        (inv_nonneg.2 (Nat.cast_nonneg n))
    have htend : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * C + birkhoffAverage ℝ T (H N) n x) atTop
        (𝓝 (0 * C + (μ[H N | MeasurableSpace.invariants T]) x)) :=
      ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const C).add (hBx N)
    rw [zero_mul, zero_add] at htend
    calc limsup (fun n => ENNReal.ofReal (e n x)) atTop
        ≤ limsup (fun n : ℕ => ENNReal.ofReal ((n : ℝ)⁻¹ * C +
            birkhoffAverage ℝ T (H N) n x)) atTop :=
          limsup_le_limsup (Eventually.of_forall fun n => ENNReal.ofReal_le_ofReal (hle n))
      _ = ENNReal.ofReal ((μ[H N | MeasurableSpace.invariants T]) x) :=
          (ENNReal.tendsto_ofReal htend).limsup_eq

  set Φ : X → ENNReal := fun x => limsup (fun n => ENNReal.ofReal (e n x)) atTop with hΦ
  have hΦm : Measurable Φ := Measurable.limsup fun n => (hem n).ennreal_ofReal
  have hΦint : ∫⁻ x, Φ x ∂μ = 0 := by
    have hle : ∀ N, ∫⁻ x, Φ x ∂μ ≤ ENNReal.ofReal (∫ x, H N x ∂μ) := fun N => by
      calc ∫⁻ x, Φ x ∂μ ≤ ∫⁻ x, ENNReal.ofReal ((μ[H N | MeasurableSpace.invariants T]) x) ∂μ :=
            lintegral_mono_ae (hbd.mono fun x hx => hx N)
        _ = ENNReal.ofReal (∫ x, (μ[H N | MeasurableSpace.invariants T]) x ∂μ) :=
            (ofReal_integral_eq_lintegral_ofReal integrable_condExp
              (condExp_nonneg (ae_of_all _ fun x => tailSup_nonneg f g N x))).symm
        _ = ENNReal.ofReal (∫ x, H N x ∂μ) := by
            rw [integral_condExp (MeasurableSpace.invariants_le T)]
    have h0 := ENNReal.tendsto_ofReal hHint
    rw [ENNReal.ofReal_zero] at h0
    exact le_antisymm (ge_of_tendsto' h0 hle) zero_le
  have hΦ0 : ∀ᵐ x ∂μ, Φ x = 0 := (lintegral_eq_zero_iff hΦm).1 hΦint

  filter_upwards [hΦ0, birkhoff_ae hT hgi] with x hx hgx
  have hE : Tendsto (fun n => ENNReal.ofReal (e n x)) atTop (𝓝 0) :=
    tendsto_of_le_liminf_of_limsup_le zero_le hx.le
  have hE' : Tendsto (fun n => e n x) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hE
    simpa [Function.comp_def, ENNReal.toReal_ofReal (he0 _ x)] using h
  have hdiff : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, f k (T^[k] x) -
      birkhoffAverage ℝ T g n x) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hE'
    rw [birkhoffAverage, birkhoffSum, smul_eq_mul, ← mul_sub, ← Finset.sum_sub_distrib,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg n))]
    exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
      (inv_nonneg.2 (Nat.cast_nonneg n))
  have h := hdiff.add hgx
  simp only [sub_add_cancel, zero_add] at h
  exact h

end Maker

end FractalGeometry
