import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.LinearCocycles.Monomial
import FractalGeometry.LinearCocycles.MonomialSingularValues
import FractalGeometry.LinearCocycles.SingularValue
import FractalGeometry.Pressure.Rectangular.Defs
import FractalGeometry.Pressure.Rectangular.Matrices
import FractalGeometry.Pressure.Rectangular.Pressure
import FractalGeometry.Pressure.SingularValueEnergy
import FractalGeometry.SelfAffine.Rectangular.Coding
import FractalGeometry.SelfAffine.Rectangular.Defs
import FractalGeometry.SelfAffine.Rectangular.OpenSet
import FractalGeometry.SelfAffine.Rectangular.SingularValues
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.Shift
import FractalGeometry.Symbolic.WordAverages

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology

open scoped Matrix.Norms.L2Operator

section futureWord

variable {α : Type*}

variable [MeasurableSpace α]

variable [Finite α] [MeasurableSingletonClass α]

variable {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ] {G H : List α → ℝ} {c : ℝ}

theorem integral_futureWord_mono (h : ∀ w, G w ≤ H w) (n : ℕ) :
    ∫ x, G (futureWord x n) ∂μ ≤ ∫ x, H (futureWord x n) ∂μ :=
  integral_mono (integrable_comp_futureWord G n) (integrable_comp_futureWord H n) fun _ => h _

end futureWord

theorem exists_energy_eq_linear (s : ℝ) :
    ∃ c₁ c₂ : ℝ, ∀ l1 l2, energy l1 l2 s = c₁ * l1 + c₂ * l2 := by
  unfold energy
  split_ifs
  · exact ⟨s, 0, fun _ _ => by ring⟩
  · exact ⟨1, s - 1, fun _ _ => by ring⟩
  · exact ⟨s / 2, s / 2, fun _ _ => by ring⟩

namespace RectangularIFS

section Word

variable {ι : Type*} (S : RectangularIFS ι)

theorem norm_matWord (w : List ι) :
    ‖S.matWord w‖ = max |S.gDeriv (S.codeWord 0 w)| |S.gDeriv (S.codeWord 1 w)| := by
  rw [matWord_eq, norm_monomialMatrix]

theorem abs_det_matWord (w : List ι) :
    |(S.matWord w).det| = |S.gDeriv (S.codeWord 0 w)| * |S.gDeriv (S.codeWord 1 w)| := by
  rw [matWord_eq, abs_det_monomialMatrix]

theorem norm_matWord_pos (w : List ι) : 0 < ‖S.matWord w‖ := by
  rw [norm_matWord]
  exact lt_max_of_lt_left (abs_pos.2 (S.gDeriv_ne_zero _))

theorem abs_det_matWord_pos (w : List ι) : 0 < |(S.matWord w).det| := by
  rw [abs_det_matWord]
  exact mul_pos (abs_pos.2 (S.gDeriv_ne_zero _)) (abs_pos.2 (S.gDeriv_ne_zero _))

theorem abs_det_div_norm_matWord (w : List ι) :
    |(S.matWord w).det| / ‖S.matWord w‖ =
      min |S.gDeriv (S.codeWord 0 w)| |S.gDeriv (S.codeWord 1 w)| := by
  have h := S.norm_matWord_pos w
  rw [norm_matWord] at h
  rw [abs_det_matWord, norm_matWord, abs_mul_abs_eq_max_mul_min, mul_div_cancel_left₀ _ h.ne']

theorem abs_det_div_norm_matWord_pos (w : List ι) :
    0 < |(S.matWord w).det| / ‖S.matWord w‖ :=
  div_pos (S.abs_det_matWord_pos w) (S.norm_matWord_pos w)

theorem log_abs_det_div_norm_matWord (w : List ι) :
    Real.log (|(S.matWord w).det| / ‖S.matWord w‖) =
      Real.log |(S.matWord w).det| - Real.log ‖S.matWord w‖ :=
  Real.log_div (S.abs_det_matWord_pos w).ne' (S.norm_matWord_pos w).ne'

theorem log_abs_det_div_norm_matWord_le (w : List ι) :
    Real.log (|(S.matWord w).det| / ‖S.matWord w‖) ≤ Real.log ‖S.matWord w‖ := by
  refine Real.log_le_log (S.abs_det_div_norm_matWord_pos w) ?_
  rw [abs_det_div_norm_matWord, norm_matWord]
  exact min_le_max

theorem log_norm_matWord_append_le (w w' : List ι) :
    Real.log ‖S.matWord (w ++ w')‖ ≤ Real.log ‖S.matWord w‖ + Real.log ‖S.matWord w'‖ := by
  have h := S.norm_matWord_pos (w ++ w')
  rw [matWord_append] at h
  rw [← Real.log_mul (S.norm_matWord_pos w).ne' (S.norm_matWord_pos w').ne', matWord_append]
  exact Real.log_le_log h (norm_mul_le _ _)

theorem log_abs_det_matWord_append (w w' : List ι) :
    Real.log |(S.matWord (w ++ w')).det| =
      Real.log |(S.matWord w).det| + Real.log |(S.matWord w').det| := by
  rw [matWord_append, Matrix.det_mul, abs_mul,
    Real.log_mul (S.abs_det_matWord_pos w).ne' (S.abs_det_matWord_pos w').ne']

theorem le_log_abs_det_div_norm_matWord_append (w w' : List ι) :
    Real.log (|(S.matWord w).det| / ‖S.matWord w‖) +
        Real.log (|(S.matWord w').det| / ‖S.matWord w'‖) ≤
      Real.log (|(S.matWord (w ++ w')).det| / ‖S.matWord (w ++ w')‖) := by
  rw [log_abs_det_div_norm_matWord, log_abs_det_div_norm_matWord, log_abs_det_div_norm_matWord,
    log_abs_det_matWord_append]
  linarith [S.log_norm_matWord_append_le w w']

theorem svf_matWord_pos (s : ℝ) (w : List ι) : 0 < svf s (S.matWord w) := by
  have hn := S.norm_matWord_pos w
  have hd := S.abs_det_matWord_pos w
  unfold svf
  split_ifs
  · exact Real.rpow_pos_of_pos hn _
  · exact mul_pos (Real.rpow_pos_of_pos hn _) (Real.rpow_pos_of_pos hd _)
  · exact Real.rpow_pos_of_pos hd _

theorem log_svf_matWord (s : ℝ) (w : List ι) :
    Real.log (svf s (S.matWord w)) =
      energy (Real.log ‖S.matWord w‖) (Real.log (|(S.matWord w).det| / ‖S.matWord w‖)) s := by
  have hn := S.norm_matWord_pos w
  have hd := S.abs_det_matWord_pos w
  rw [log_abs_det_div_norm_matWord]
  unfold svf energy
  split_ifs
  · rw [Real.log_rpow hn]
  · rw [Real.log_mul (Real.rpow_pos_of_pos hn _).ne' (Real.rpow_pos_of_pos hd _).ne',
      Real.log_rpow hn, Real.log_rpow hd]
    ring
  · rw [Real.log_rpow hd]
    ring

theorem log_svf_matWord_append_le {s : ℝ} (hs : 0 ≤ s) (w w' : List ι) :
    Real.log (svf s (S.matWord (w ++ w'))) ≤
      Real.log (svf s (S.matWord w)) + Real.log (svf s (S.matWord w')) := by
  have h := S.svf_matWord_pos s (w ++ w')
  rw [matWord_append] at h
  rw [← Real.log_mul (S.svf_matWord_pos s w).ne' (S.svf_matWord_pos s w').ne', matWord_append]
  exact Real.log_le_log h (svf_mul_le hs _ _)

variable {S} {δ r M : ℝ}

theorem RatioLowerBound.le_log_norm_matWord (hδ : S.RatioLowerBound δ) (w : List ι) :
    Real.log δ * w.length ≤ Real.log ‖S.matWord w‖ := by
  have h : δ ^ w.length ≤ ‖S.matWord w‖ := by
    rw [norm_matWord]
    exact le_max_of_le_left (by simpa using hδ.le_abs_gDeriv (S.codeWord 0 w))
  have h' := Real.log_le_log (pow_pos hδ.1 _) h
  rwa [Real.log_pow, mul_comm] at h'

theorem RatioLowerBound.le_log_svf_matWord (hδ : S.RatioLowerBound δ) {s : ℝ} (hs : 0 ≤ s)
    (w : List ι) : s * Real.log δ * w.length ≤ Real.log (svf s (S.matWord w)) := by
  have h := Real.log_le_log (Real.rpow_pos_of_pos (pow_pos hδ.1 _) _) (hδ.le_svf_matWord hs w)
  rw [Real.log_rpow (pow_pos hδ.1 _), Real.log_pow] at h
  calc s * Real.log δ * w.length = s * (w.length * Real.log δ) := by ring
    _ ≤ Real.log (svf s (S.matWord w)) := h

theorem Bounds.log_norm_matWord_le (hS : S.Bounds r M) (w : List ι) :
    Real.log ‖S.matWord w‖ ≤ Real.log r * w.length := by
  have h : ‖S.matWord w‖ ≤ r ^ w.length := by
    rw [norm_matWord]
    exact max_le (by simpa using hS.abs_gDeriv_le (S.codeWord 0 w))
      (by simpa using hS.abs_gDeriv_le (S.codeWord 1 w))
  have h' := Real.log_le_log (S.norm_matWord_pos w) h
  rwa [Real.log_pow, mul_comm] at h'

variable (S)

theorem log_abs_gDeriv_futureWord (y : ℤ → ι × ZMod 2) (n : ℕ) :
    Real.log |S.gDeriv (futureWord y n)| =
      ∑ k ∈ Finset.range n, Real.log |S.ratio (y k)| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [futureWord_succ, gDeriv_append, abs_mul,
      Real.log_mul (abs_ne_zero.2 (S.gDeriv_ne_zero _)) (abs_ne_zero.2 (S.gDeriv_ne_zero _)),
      ih, Finset.sum_range_succ]
    simp

end Word

section Lyapunov

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : RectangularIFS ι) {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]

theorem tendsto_lyapunov₁ (hμ : MeasurePreserving (shift 1) μ μ) :
    Tendsto (fun n : ℕ => (∫ x, Real.log ‖S.matWord (futureWord x n)‖ ∂μ) / n) atTop
      (𝓝 (S.lyapunov₁ μ)) := by
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
  obtain ⟨δ, hδ⟩ := S.exists_ratioLowerBound
  obtain ⟨L, hL⟩ := exists_tendsto_integral_futureWord_div hμ
    (G := fun w => Real.log ‖S.matWord w‖) S.log_norm_matWord_append_le
    hδ.le_log_norm_matWord
  rw [lyapunov₁, hL.limUnder_eq]
  exact hL

theorem tendsto_lyapunov₂ (hμ : MeasurePreserving (shift 1) μ μ) :
    Tendsto (fun n : ℕ =>
      (∫ x, Real.log (|(S.matWord (futureWord x n)).det| / ‖S.matWord (futureWord x n)‖) ∂μ) / n)
      atTop (𝓝 (S.lyapunov₂ μ)) := by
  obtain ⟨r, M, hS⟩ := S.exists_bounds
  obtain ⟨L, hL⟩ := exists_tendsto_integral_futureWord_div_of_superadditive hμ
    (G := fun w => Real.log (|(S.matWord w).det| / ‖S.matWord w‖))
    S.le_log_abs_det_div_norm_matWord_append
    fun w => (S.log_abs_det_div_norm_matWord_le w).trans (hS.log_norm_matWord_le w)
  rw [lyapunov₂, hL.limUnder_eq]
  exact hL

theorem lyapunov₂_le_lyapunov₁ (hμ : MeasurePreserving (shift 1) μ μ) :
    S.lyapunov₂ μ ≤ S.lyapunov₁ μ :=
  le_of_tendsto_of_tendsto' (S.tendsto_lyapunov₂ hμ) (S.tendsto_lyapunov₁ hμ) fun n =>
    div_le_div_of_nonneg_right
      (integral_futureWord_mono S.log_abs_det_div_norm_matWord_le n) (Nat.cast_nonneg n)

end Lyapunov

section Energy

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : RectangularIFS ι) {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ]

theorem tendsto_energyLim (hμ : MeasurePreserving (shift 1) μ μ) {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun n : ℕ => (∫ x, Real.log (svf s (S.matWord (futureWord x n))) ∂μ) / n) atTop
      (𝓝 (S.energyLim s μ)) := by
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
  obtain ⟨δ, hδ⟩ := S.exists_ratioLowerBound
  obtain ⟨L, hL⟩ := exists_tendsto_integral_futureWord_div hμ
    (G := fun w => Real.log (svf s (S.matWord w))) (S.log_svf_matWord_append_le hs)
    (hδ.le_log_svf_matWord hs)
  rw [energyLim, hL.limUnder_eq]
  exact hL

theorem energyLim_eq (hμ : MeasurePreserving (shift 1) μ μ) {s : ℝ} (hs : 0 ≤ s) :
    S.energyLim s μ = energy (S.lyapunov₁ μ) (S.lyapunov₂ μ) s := by
  obtain ⟨c₁, c₂, hc⟩ := exists_energy_eq_linear s
  have h := ((S.tendsto_lyapunov₁ hμ).const_mul c₁).add ((S.tendsto_lyapunov₂ hμ).const_mul c₂)
  rw [← hc] at h
  refine tendsto_nhds_unique (S.tendsto_energyLim hμ hs) (h.congr fun n => ?_)
  have h₁ : Integrable (fun x => Real.log ‖S.matWord (futureWord x n)‖) μ :=
    integrable_comp_futureWord (fun w => Real.log ‖S.matWord w‖) n
  have h₂ : Integrable (fun x =>
      Real.log (|(S.matWord (futureWord x n)).det| / ‖S.matWord (futureWord x n)‖)) μ :=
    integrable_comp_futureWord (fun w => Real.log (|(S.matWord w).det| / ‖S.matWord w‖)) n
  simp only [log_svf_matWord, hc]
  rw [integral_add (h₁.const_mul c₁) (h₂.const_mul c₂), integral_const_mul, integral_const_mul]
  ring

variable {S} in

theorem IsEquilibriumState.pressure_eq {s : ℝ} (heq : S.IsEquilibriumState s μ)
    (hμ : MeasurePreserving (shift 1) μ μ) (hs : 0 ≤ s) :
    S.pressure s = entropy μ + energy (S.lyapunov₁ μ) (S.lyapunov₂ μ) s := by
  rw [← S.energyLim_eq hμ hs]
  exact heq

end Energy

end RectangularIFS

end FractalGeometry
