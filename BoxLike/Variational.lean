module

/-
The variational inequality `eq:variational` of `sec:affinity_dim`, its consequence for the
Lyapunov dimension of `eq:diml_min2`, and the formula for `φ^s(A_{𝐢|_n})` through the Birkhoff
sums of the potentials `f_{1,s}`, `f_{2,s}` of `sec:gibbs_measures`.

* `sum_mul_log_add_sum_negMulLog_le`: the inequality
  `∑_w p_w log a_w + ∑_w -p_w log p_w ≤ log Z + (∑_w a_w) / Z - 1` for a probability vector `p`,
  positive weights `a` and `Z > 0`; at `Z = ∑_w a_w` it is Jensen's inequality for `log`.
* `integral_comp_block_eq_sum`, `integral_comp_futureWord_eq_sum`: the integral of a function of
  the prefix `𝐢|_n` is the sum of its values weighted by the measures of the cylinders.
* `System.integral_log_svf_add_blockEntropy_le`: `eq:variational` at level `n`.
* `System.entropy_add_energyLim_le_pressure`: `eq:variational`,
  `h_0(μ) + Λ(𝖠, μ, s) ≤ P(𝖠, s)`.
* `lyapDim_nonneg`, `add_energy_lyapDim`: the piecewise formula `eq:diml_min2` is a non-negative
  solution of `h_0(μ) + Λ(𝖠, μ, s) = 0`.
* `System.pressure_lyapDim_nonneg`: `0 ≤ P(𝖠, \dim_L(𝖠, μ))`, the step behind
  `\dim_L(𝖠, μ) ≤ dimaff(𝖠)`.
* `svf_boxMat_eq_max_exp`: `φ^s` of a diagonal or anti-diagonal matrix for `0 < s < 2`, in
  logarithmic form.
* `System.abs_gDeriv_futureWord`: `eq:lyapunov_exp_for_psi`.
* `System.svf_matWord_futureWord`:
  `φ^s(A_{𝐢|_n}) = max{exp S_n f_{1,s}(τ(𝐢)), exp S_n f_{2,s}(τ(𝐢))}`.
-/
public import BoxLike.Lyapunov
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

@[expose] public section

namespace BoxLike

open MeasureTheory

/-! ### Jensen's inequality for the logarithm -/

/-- The finite inequality behind `eq:variational`: for a probability vector `p`, positive
weights `a` and `Z > 0`,
`∑_w p_w log a_w + ∑_w -p_w log p_w ≤ log Z + (∑_w a_w) / Z - 1`. It is the sum over `w` of
`log t ≤ t - 1` at `t = a_w / (p_w Z)`. -/
theorem sum_mul_log_add_sum_negMulLog_le {W : Type*} [Fintype W] {p a : W → ℝ} {Z : ℝ}
    (hp : ∀ w, 0 ≤ p w) (hsum : ∑ w, p w = 1) (ha : ∀ w, 0 < a w) (hZ : 0 < Z) :
    ∑ w, p w * Real.log (a w) + ∑ w, Real.negMulLog (p w)
      ≤ Real.log Z + ((∑ w, a w) / Z - 1) := by
  have key : ∀ w, p w * Real.log (a w) + Real.negMulLog (p w)
      ≤ p w * Real.log Z + (a w / Z - p w) := by
    intro w
    rcases (hp w).eq_or_lt with h | h
    · rw [← h]
      simpa using (div_pos (ha w) hZ).le
    · have hlog := Real.log_le_sub_one_of_pos (div_pos (ha w) (mul_pos h hZ))
      rw [Real.log_div (ha w).ne' (mul_pos h hZ).ne', Real.log_mul h.ne' hZ.ne'] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog h.le
      have e : p w * (a w / (p w * Z) - 1) = a w / Z - p w := by
        field_simp
      rw [e] at hmul
      rw [Real.negMulLog]
      linarith
  calc ∑ w, p w * Real.log (a w) + ∑ w, Real.negMulLog (p w)
      = ∑ w, (p w * Real.log (a w) + Real.negMulLog (p w)) := Finset.sum_add_distrib.symm
    _ ≤ ∑ w, (p w * Real.log Z + (a w / Z - p w)) := Finset.sum_le_sum fun w _ => key w
    _ = Real.log Z + ((∑ w, a w) / Z - 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div,
          hsum, one_mul]

/-! ### Integrals of functions of finitely many coordinates -/

section Integral

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The integral of a function of the block `x_0 ⋯ x_{n-1}` is the sum of its values weighted by
the measures of the cylinders of length `n`. -/
theorem integral_comp_block_eq_sum (μ : Measure (ℤ → α)) [IsFiniteMeasure μ] {n : ℕ}
    (F : (Fin n → α) → ℝ) :
    ∫ x, F (block n x) ∂μ = ∑ w : Fin n → α, μ.real (cylinder w) * F w := by
  have hF : Measurable F := Measurable.of_discrete
  rw [← integral_map (measurable_block n).aemeasurable hF.aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_measureReal_apply (measurable_block n) (measurableSet_singleton w),
    cylinder_eq_preimage, smul_eq_mul]

/-- The integral of a function of the prefix `𝐢|_n` is the sum of its values weighted by the
measures of the cylinders of length `n`. -/
theorem integral_comp_futureWord_eq_sum (μ : Measure (ℤ → α)) [IsFiniteMeasure μ]
    (G : List α → ℝ) (n : ℕ) :
    ∫ x, G (futureWord x n) ∂μ = ∑ w : Fin n → α, μ.real (cylinder w) * G (List.ofFn w) := by
  simp only [futureWord_eq_ofFn_block]
  exact integral_comp_block_eq_sum μ fun w => G (List.ofFn w)

end Integral

/-! ### The Lyapunov dimension solves the energy equation -/

/-- The piecewise formula `eq:diml_min2` is a non-negative solution `s` of
`h_0(μ) + Λ(𝖠, μ, s) = 0`, with the energy in the piecewise form of `eq:energy_def`. -/
theorem lyapDim_nonneg_and_add_energy {h l1 l2 : ℝ} (hl : l2 ≤ l1) (hl1 : l1 < 0)
    (hh : 0 ≤ h) : 0 ≤ lyapDim h l1 l2 ∧ h + energy l1 l2 (lyapDim h l1 l2) = 0 := by
  have hl2 : l2 < 0 := lt_of_le_of_lt hl hl1
  unfold lyapDim
  split_ifs with h1 h2
  · have hs1 : -h / l1 ≤ 1 := by
      rw [div_le_one_of_neg hl1]; linarith
    refine ⟨div_nonneg_of_nonpos (by linarith) hl1.le, ?_⟩
    rw [energy, ite_eq_left hs1, div_mul_cancel₀ _ hl1.ne]
    ring
  · rw [not_le] at h1
    have hneg : (h + l1) / l2 < 0 := div_neg_of_pos_of_neg (by linarith) hl2
    have hge : -1 ≤ (h + l1) / l2 := by
      rw [le_div_iff_of_neg hl2]; linarith
    refine ⟨by linarith, ?_⟩
    rw [energy, ite_eq_right (by linarith), ite_eq_left (by linarith)]
    have e : (h + l1) / l2 * l2 = h + l1 := div_mul_cancel₀ _ hl2.ne
    linarith
  · rw [not_le] at h1 h2
    have hsum : l1 + l2 < 0 := by linarith
    have hs2 : 2 < -(2 * h) / (l1 + l2) := by
      rw [lt_div_iff_of_neg hsum]; linarith
    refine ⟨by linarith, ?_⟩
    rw [energy, ite_eq_right (by linarith), ite_eq_right (by linarith)]
    have e : -(2 * h) / (l1 + l2) * (l1 + l2) = -(2 * h) := div_mul_cancel₀ _ hsum.ne
    linarith

/-- The Lyapunov dimension `dim_L(𝖠, μ)` of `eq:diml_min2` is non-negative. -/
theorem lyapDim_nonneg {h l1 l2 : ℝ} (hl : l2 ≤ l1) (hl1 : l1 < 0) (hh : 0 ≤ h) :
    0 ≤ lyapDim h l1 l2 :=
  (lyapDim_nonneg_and_add_energy hl hl1 hh).1

/-- The Lyapunov dimension `dim_L(𝖠, μ)` of `eq:diml_min2` solves
`h_0(μ) + Λ(𝖠, μ, s) = 0`. With `lyapDim_eq` it is the unique solution. -/
theorem add_energy_lyapDim {h l1 l2 : ℝ} (hl : l2 ≤ l1) (hl1 : l1 < 0) (hh : 0 ≤ h) :
    h + energy l1 l2 (lyapDim h l1 l2) = 0 :=
  (lyapDim_nonneg_and_add_energy hl hl1 hh).2

/-! ### The variational inequality -/

namespace System

section Variational

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]

/-- `eq:variational` at level `n`:
`∫ log φ^s(A_{𝐢|_n}) dμ(𝐢) + H_μ(𝒫_0^{n-1}) ≤ log ∑_{|𝐢| = n} φ^s(A_𝐢)`. The integrand is
constant on the cylinders of length `n`, and the inequality is Jensen's inequality for the
logarithm with the weights `μ([𝐢])`. -/
theorem integral_log_svf_add_blockEntropy_le (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    (∫ x, Real.log (svf s (S.matWord (futureWord x n))) ∂μ) + blockEntropy μ n
      ≤ Real.log (S.svfSum s n) := by
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
  obtain ⟨δ, hδ⟩ := S.exists_ratioLowerBound
  have hZ : 0 < S.svfSum s n := hδ.svfSum_pos hs n
  have h := sum_mul_log_add_sum_negMulLog_le (p := fun w : Fin n → ι => μ.real (cylinder w))
    (a := fun w => svf s (S.matWord (List.ofFn w))) (fun _ => measureReal_nonneg)
    (sum_measureReal_cylinder μ n) (fun _ => S.svf_matWord_pos s _) hZ
  rw [← svfSum, div_self hZ.ne', sub_self, add_zero] at h
  rw [integral_comp_futureWord_eq_sum μ fun w => Real.log (svf s (S.matWord w))]
  exact h

/-- `eq:variational`: `h_0(μ) + Λ(𝖠, μ, s) ≤ P(𝖠, s)` for every invariant probability measure
`μ` and every `s ≥ 0`. -/
theorem entropy_add_energyLim_le_pressure (hμ : MeasurePreserving (shift 1) μ μ) {s : ℝ}
    (hs : 0 ≤ s) : entropy μ + S.energyLim s μ ≤ S.pressure s := by
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
  obtain ⟨δ, hδ⟩ := S.exists_ratioLowerBound
  refine le_of_tendsto_of_tendsto' ((tendsto_entropy hμ).add (S.tendsto_energyLim hμ hs))
    (hδ.tendsto_pressure hs) fun n => ?_
  rw [← add_div, add_comm]
  exact div_le_div_of_nonneg_right (S.integral_log_svf_add_blockEntropy_le n hs)
    (Nat.cast_nonneg n)

/-- The pressure is non-negative at the Lyapunov dimension: `0 ≤ P(𝖠, \dim_L(𝖠, μ))`. Since
`s ↦ P(𝖠, s)` is strictly decreasing with its zero at `dimaff(𝖠)`, this is the step behind
`\dim_L(𝖠, μ) ≤ dimaff(𝖠)` in `sec:affinity_dim`. -/
theorem pressure_lyapDim_nonneg (hμ : MeasurePreserving (shift 1) μ μ) :
    0 ≤ S.pressure (lyapDim (entropy μ) (S.lyapunov₁ μ) (S.lyapunov₂ μ)) := by
  have hl := S.lyapunov₂_le_lyapunov₁ hμ
  have hl1 := S.lyapunov₁_neg hμ
  have hh := entropy_nonneg hμ
  have hs := lyapDim_nonneg hl hl1 hh
  have h := S.entropy_add_energyLim_le_pressure hμ hs
  rwa [S.energyLim_eq hμ hs, add_energy_lyapDim hl hl1 hh] at h

end Variational

end System

/-! ### The singular value function through the potentials -/

/-- `φ^s` of a diagonal or anti-diagonal matrix with non-zero entries `a`, `b`, for `0 < s < 2`,
in logarithmic form: `φ^s = max{|a|, |b|}^s` is the larger of `|a|^s` and `|b|^s` for `s < 1`,
and `φ^s = max{|a|, |b|} min{|a|, |b|}^{s-1}` is the larger of `|a| |b|^{s-1}` and
`|b| |a|^{s-1}` for `1 ≤ s < 2`. -/
theorem svf_boxMat_eq_max_exp {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) (c : ZMod 2) {a b : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    svf s (boxMat c a b) =
      max (Real.exp (if s < 1 then s * Real.log |a| else Real.log |a| + (s - 1) * Real.log |b|))
        (Real.exp (if s < 1 then s * Real.log |b| else Real.log |b| + (s - 1) * Real.log |a|)) := by
  have hu : |a| = Real.exp (Real.log |a|) := (Real.exp_log (abs_pos.2 ha)).symm
  have hv : |b| = Real.exp (Real.log |b|) := (Real.exp_log (abs_pos.2 hb)).symm
  generalize Real.log |a| = u at hu ⊢
  generalize Real.log |b| = v at hv ⊢
  rw [← Real.exp_monotone.map_max]
  rcases le_or_gt s 1 with h1 | h1
  · rw [svf_boxMat_of_le_one h1, hu, hv, ← Real.exp_monotone.map_max, ← Real.exp_mul]
    congr 1
    rcases h1.lt_or_eq with h1' | rfl
    · rw [ite_eq_left h1', ite_eq_left h1']
      rcases le_total u v with h | h
      · rw [max_eq_right h, max_eq_right (mul_le_mul_of_nonneg_left h hs0.le), mul_comm]
      · rw [max_eq_left h, max_eq_left (mul_le_mul_of_nonneg_left h hs0.le), mul_comm]
    · simp
  · rw [svf_boxMat_of_le_two h1 hs2.le c b ha, hu, hv, ← Real.exp_monotone.map_max,
      ← Real.exp_monotone.map_min, ← Real.exp_mul, ← Real.exp_add, ite_eq_right (not_lt.2 h1.le),
      ite_eq_right (not_lt.2 h1.le)]
    congr 1
    rcases le_total u v with h | h
    · rw [max_eq_right h, min_eq_left h, max_eq_right (by nlinarith)]
      ring
    · rw [max_eq_left h, min_eq_right h, max_eq_left (by nlinarith)]
      ring

namespace System

section Gibbs

variable {ι : Type*} (S : System ι)

/-- `f_{2,s}(τ(𝐢)) = f_{1,s}(ω(𝐢))`, as noted in `sec:gibbs_measures`. -/
theorem potential₂_tau (s : ℝ) (x : ℤ → ι) (k : ℤ) :
    S.potential₂ s (tau S.o x k) = S.potential₁ s (omega S.o x k) := rfl

/-- The Birkhoff sum `S_n f_{1,s}(τ(𝐢))` through the moduli `|g'_{τ(𝐢)|_n}|` and
`|g'_{ω(𝐢)|_n}|`. -/
theorem sum_potential₁_tau (s : ℝ) (x : ℤ → ι) (n : ℕ) :
    ∑ k ∈ Finset.range n, S.potential₁ s (tau S.o x k) =
      if s < 1 then s * Real.log |S.gDeriv (futureWord (tau S.o x) n)|
      else Real.log |S.gDeriv (futureWord (tau S.o x) n)| +
        (s - 1) * Real.log |S.gDeriv (futureWord (omega S.o x) n)| := by
  rw [log_abs_gDeriv_futureWord, log_abs_gDeriv_futureWord]
  unfold potential₁
  split_ifs
  · rw [Finset.mul_sum]
  · rw [Finset.sum_add_distrib, Finset.mul_sum]
    rfl

/-- The Birkhoff sum `S_n f_{2,s}(τ(𝐢))` through the moduli `|g'_{ω(𝐢)|_n}|` and
`|g'_{τ(𝐢)|_n}|`. -/
theorem sum_potential₂_tau (s : ℝ) (x : ℤ → ι) (n : ℕ) :
    ∑ k ∈ Finset.range n, S.potential₂ s (tau S.o x k) =
      if s < 1 then s * Real.log |S.gDeriv (futureWord (omega S.o x) n)|
      else Real.log |S.gDeriv (futureWord (omega S.o x) n)| +
        (s - 1) * Real.log |S.gDeriv (futureWord (tau S.o x) n)| := by
  have hk : ∀ k : ℤ, ((omega S.o x k).1, (omega S.o x k).2 + 1) = tau S.o x k := fun k => by
    rw [omega_apply, tau_apply, add_assoc, show (1 : ZMod 2) + 1 = 0 from by decide, add_zero]
  rw [log_abs_gDeriv_futureWord, log_abs_gDeriv_futureWord]
  simp only [potential₂_tau]
  unfold potential₁
  split_ifs
  · rw [Finset.mul_sum]
  · rw [Finset.sum_add_distrib, Finset.mul_sum]
    simp only [hk]

/-- `eq:lyapunov_exp_for_psi`: `|g'_{𝐣|_n}(0)| = exp S_n f_{1,1}(𝐣)`. -/
theorem abs_gDeriv_futureWord (y : ℤ → ι × ZMod 2) (n : ℕ) :
    |S.gDeriv (futureWord y n)| = Real.exp (∑ k ∈ Finset.range n, S.potential₁ 1 (y k)) := by
  rw [← Real.exp_log (abs_pos.2 (S.gDeriv_ne_zero _)), log_abs_gDeriv_futureWord]
  simp [potential₁]

/-- The identity of `sec:gibbs_measures`:
`φ^s(A_{𝐢|_n}) = max{exp S_n f_{1,s}(τ(𝐢)), exp S_n f_{2,s}(τ(𝐢))}` for `0 < s < 2`, where
`S_n f(τ(𝐢)) = ∑_{k<n} f(τ_k(𝐢))`. The product `A_{𝐢|_n}` is the diagonal or anti-diagonal
matrix with entries of moduli `|g'_{τ(𝐢)|_n}|` and `|g'_{ω(𝐢)|_n}|`. -/
theorem svf_matWord_futureWord (x : ℤ → ι) (n : ℕ) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    svf s (S.matWord (futureWord x n)) =
      max (Real.exp (∑ k ∈ Finset.range n, S.potential₁ s (tau S.o x k)))
        (Real.exp (∑ k ∈ Finset.range n, S.potential₂ s (tau S.o x k))) := by
  rw [matWord_eq, codeWord_futureWord_tau, codeWord_futureWord_omega,
    svf_boxMat_eq_max_exp hs0 hs2 _ (S.gDeriv_ne_zero _) (S.gDeriv_ne_zero _),
    sum_potential₁_tau, sum_potential₂_tau]

end Gibbs

end System

end BoxLike
