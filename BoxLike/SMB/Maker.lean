module

/-
Maker's generalised ergodic theorem, the step of Breiman's proof of the Shannon–McMillan–Breiman
theorem that `sec:entropies` cites before `thm:feng_entropy_kolmogorov_sinai` (tex lines 1885 to
1977). For a measure-preserving map `T` of a probability space and measurable functions
`f_k → g` almost everywhere with `sup_k |f_k|` integrable, the averages
`n⁻¹ ∑_{k<n} f_k(T^k x)` converge almost everywhere to `E(g | ℐ)(x)`, where `ℐ` is the
`σ`-algebra of `T`-invariant sets. It is derived from Birkhoff's theorem `birkhoff_ae`.

Proof. Write `H_N = sup_{k ≥ N} |f_k - g|`. For `n > N` the error
`n⁻¹ ∑_{k<n} |f_k - g|(T^k x)` is at most `n⁻¹ ∑_{k<N} |f_k - g|(T^k x)`, which tends to `0`,
plus the Birkhoff average of `H_N`, which tends to `E(H_N | ℐ)(x)`. So the upper limit `Φ(x)`
of the error is at most `E(H_N | ℐ)(x)` for every `N`, and `∫ Φ ≤ ∫ H_N → 0` by dominated
convergence. Hence `Φ = 0` almost everywhere, and Birkhoff's theorem for `g` gives the limit.

* `tailSup`, `measurable_tailSup`, `tailSup_nonneg`, `abs_sub_le_tailSup`, `tailSup_le`,
  `tendsto_tailSup`: the tail supremum `H_N = sup_{k ≥ N} |f_k - g|`.
* `maker_ae`: Maker's theorem, with the limit `E(g | ℐ)`.
* `maker_ergodic`: the ergodic form, with the limit `∫ g dμ`.
-/
public import BoxLike.Birkhoff
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Instances.ENNReal.Lemmas

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology Set

section TailSup

variable {X : Type*}

/-- The tail supremum `H_N(x) = sup_{k ≥ N} |f_k(x) - g(x)|` of the proof of Maker's theorem
(`sec:entropies`, tex lines 1885 to 1889), computed in `[0, ∞]` and read as a real number. -/
noncomputable def tailSup (f : ℕ → X → ℝ) (g : X → ℝ) (N : ℕ) (x : X) : ℝ :=
  (⨆ k, ENNReal.ofReal |f (N + k) x - g x|).toReal

/-- The tail supremum is non-negative. -/
theorem tailSup_nonneg (f : ℕ → X → ℝ) (g : X → ℝ) (N : ℕ) (x : X) : 0 ≤ tailSup f g N x :=
  ENNReal.toReal_nonneg

/-- If `|f_k(x)| ≤ F(x)` for every `k` and `|g(x)| ≤ F(x)`, the supremum defining `H_N(x)` is
at most `2 F(x)`. -/
theorem iSup_ofReal_abs_sub_le {f : ℕ → X → ℝ} {g F : X → ℝ} {x : X}
    (hf : ∀ k, |f k x| ≤ F x) (hg : |g x| ≤ F x) (N : ℕ) :
    ⨆ k, ENNReal.ofReal |f (N + k) x - g x| ≤ ENNReal.ofReal (2 * F x) :=
  iSup_le fun k => ENNReal.ofReal_le_ofReal <|
    (abs_sub (f (N + k) x) (g x)).trans (by linarith [hf (N + k)])

/-- Under the bounds `|f_k(x)| ≤ F(x)` and `|g(x)| ≤ F(x)`, `H_N(x) ≤ 2 F(x)`. -/
theorem tailSup_le {f : ℕ → X → ℝ} {g F : X → ℝ} {x : X} (hf : ∀ k, |f k x| ≤ F x)
    (hg : |g x| ≤ F x) (N : ℕ) : tailSup f g N x ≤ 2 * F x :=
  ENNReal.toReal_le_of_le_ofReal (by linarith [(abs_nonneg (g x)).trans hg])
    (iSup_ofReal_abs_sub_le hf hg N)

/-- Under the bounds `|f_k(x)| ≤ F(x)` and `|g(x)| ≤ F(x)`, `|f_k(x) - g(x)| ≤ H_N(x)` for
every `k ≥ N`. -/
theorem abs_sub_le_tailSup {f : ℕ → X → ℝ} {g F : X → ℝ} {x : X} (hf : ∀ k, |f k x| ≤ F x)
    (hg : |g x| ≤ F x) (N k : ℕ) : |f (N + k) x - g x| ≤ tailSup f g N x := by
  have hne : ⨆ k, ENNReal.ofReal |f (N + k) x - g x| ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_ofReal_abs_sub_le hf hg N)
  exact (ENNReal.ofReal_le_iff_le_toReal hne).1
    (le_iSup (fun k => ENNReal.ofReal |f (N + k) x - g x|) k)

/-- If `f_k(x) → g(x)`, then `H_N(x) → 0`. -/
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

/-- The tail supremum of measurable functions is measurable. -/
theorem measurable_tailSup {f : ℕ → X → ℝ} {g : X → ℝ} (hf : ∀ k, Measurable (f k))
    (hg : Measurable g) (N : ℕ) : Measurable (tailSup f g N) :=
  (Measurable.iSup fun k =>
    (continuous_abs.measurable.comp ((hf (N + k)).sub hg)).ennreal_ofReal).ennreal_toReal

end TailSup

section Maker

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {T : X → X}

/-- Maker's generalised ergodic theorem (P. T. Maker, Duke Math. J. 6 (1940)), as used in the
proof of the Shannon–McMillan–Breiman theorem cited in `sec:entropies`, tex lines 1885 to 1889:
for a measure-preserving map `T` of a probability space and measurable functions `f_k`
converging almost everywhere to a measurable `g`, with `|f_k| ≤ F` for an integrable `F`, the
averages `n⁻¹ ∑_{k<n} f_k(T^k x)` converge for almost every `x` to `E(g | ℐ)(x)`. -/
theorem maker_ae (hT : MeasurePreserving T μ μ) {f : ℕ → X → ℝ} {g F : X → ℝ}
    (hf : ∀ k, Measurable (f k)) (hg : Measurable g) (hF : Integrable F μ)
    (hbound : ∀ᵐ x ∂μ, ∀ k, |f k x| ≤ F x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => f k x) atTop (𝓝 (g x))) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, f k (T^[k] x)) atTop
      (𝓝 ((μ[g | MeasurableSpace.invariants T]) x)) := by
  -- the limit is dominated by `F`
  have hgF : ∀ᵐ x ∂μ, |g x| ≤ F x := by
    filter_upwards [hbound, hlim] with x hb hl
    exact le_of_tendsto ((continuous_abs.tendsto _).comp hl) (Eventually.of_forall hb)
  have hgi : Integrable g μ :=
    hF.mono' hg.aestronglyMeasurable (by simpa [Real.norm_eq_abs] using hgF)
  -- the good points and their orbits
  have hgood : ∀ᵐ x ∂μ, (∀ k, |f k x| ≤ F x) ∧ |g x| ≤ F x ∧
      Tendsto (fun k => f k x) atTop (𝓝 (g x)) := by
    filter_upwards [hbound, hgF, hlim] with x h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have horbit : ∀ᵐ x ∂μ, ∀ k, (∀ j, |f j (T^[k] x)| ≤ F (T^[k] x)) ∧
      |g (T^[k] x)| ≤ F (T^[k] x) :=
    ae_all_iff.2 fun k => (hT.iterate k).quasiMeasurePreserving.ae
      (p := fun y => (∀ j, |f j y| ≤ F y) ∧ |g y| ≤ F y) (hgood.mono fun _ hx => ⟨hx.1, hx.2.1⟩)
  -- the tail suprema
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
  -- Birkhoff's theorem for `H_N` and for `g`
  have hB : ∀ᵐ x ∂μ, ∀ N, Tendsto (fun n => birkhoffAverage ℝ T (H N) n x) atTop
      (𝓝 ((μ[H N | MeasurableSpace.invariants T]) x)) :=
    ae_all_iff.2 fun N => birkhoff_ae hT (hHi N)
  -- the errors
  set e : ℕ → X → ℝ := fun n x =>
    (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, |f k (T^[k] x) - g (T^[k] x)| with he
  have he0 : ∀ n x, 0 ≤ e n x := fun n x =>
    mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg n)) (Finset.sum_nonneg fun k _ => abs_nonneg _)
  have hem : ∀ n, Measurable (e n) := fun n =>
    measurable_const.mul (Finset.measurable_sum _ fun k _ =>
      continuous_abs.measurable.comp
        (((hf k).comp (hT.measurable.iterate k)).sub (hg.comp (hT.measurable.iterate k))))
  -- the upper limit of the error is at most `E(H_N | ℐ)`
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
  -- the upper limit of the error vanishes almost everywhere
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
  -- conclusion
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

/-- Maker's theorem for an ergodic map (`sec:entropies`, tex lines 1885 to 1889): the averages
`n⁻¹ ∑_{k<n} f_k(T^k x)` converge almost everywhere to `∫ g dμ`. -/
theorem maker_ergodic (hT : Ergodic T μ) {f : ℕ → X → ℝ} {g F : X → ℝ}
    (hf : ∀ k, Measurable (f k)) (hg : Measurable g) (hF : Integrable F μ)
    (hbound : ∀ᵐ x ∂μ, ∀ k, |f k x| ≤ F x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => f k x) atTop (𝓝 (g x))) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, f k (T^[k] x)) atTop
      (𝓝 (∫ x, g x ∂μ)) := by
  have hgm : Measurable[MeasurableSpace.invariants T] (μ[g | MeasurableSpace.invariants T]) :=
    stronglyMeasurable_condExp.measurable
  obtain ⟨c, hc⟩ := hT.toPreErgodic.ae_eq_const_of_ae_eq_comp
    (hgm.mono (MeasurableSpace.invariants_le T) le_rfl)
    (MeasurableSpace.comp_eq_of_measurable_invariants hgm)
  have hcg : c = ∫ x, g x ∂μ := by
    rw [← integral_condExp (MeasurableSpace.invariants_le T), integral_congr_ae hc]
    simp
  filter_upwards [maker_ae hT.toMeasurePreserving hf hg hF hbound hlim, hc] with x hx hxc
  rw [← hcg]
  rwa [hxc] at hx

end Maker

end BoxLike
