module

public import Mathlib
public import FractalGeometry.Symbolic.Conditional
public import FractalGeometry.Symbolic.ConditionalMeasures
public import FractalGeometry.Symbolic.Entropy
public import FractalGeometry.Symbolic.Shift
public import FractalGeometry.Symbolic.PastEntropy
public import FractalGeometry.Ergodic.Maker
public import FractalGeometry.Symbolic.PastInformation
public import FractalGeometry.Ergodic.ShannonMcMillanBreimanStatement
public import FractalGeometry.Symbolic.Past

/-!
Shannon–McMillan–Breiman for the two-sided shift over a finite alphabet.
The ergodic theorem gives the entropy rate; the invariant-measure version gives
conditional expectation of the past information on the invariant sigma algebra.
Reference: Leo Breiman, The individual ergodic theorem of information theory,
Annals of Mathematical Statistics 28(3) (1957), 809–811,
doi:10.1214/aoms/1177706899.
-/

@[expose] public section

namespace FractalGeometry

open MeasureTheory ProbabilityTheory Filter Topology Set

universe u

section Info

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

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

section Telescoping

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] {μ : Measure (ℤ → α)}

omit [MeasurableSpace α] [MeasurableSingletonClass α] in

theorem append_block_eq_block_succ (k : ℕ) (x : ℤ → α) :
    Fin.append (block k x) (fun _ : Fin 1 => x k) = block (k + 1) x := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
    simp [block]
  · rw [Fin.append_right]
    simp [block]

theorem pastCondProb_shift (hinv : MeasurePreserving (shift 1) μ μ) (k : ℕ) (x : ℤ → α) :
    pastCondProb μ k (shift k x 0) (shift k x) =
      μ.real (cylinder (block (k + 1) x)) / μ.real (cylinder (block k x)) := by
  rw [pastCondProb, pastBlock_shift, measureReal_inter_pastBlock_preimage hinv,
    measureReal_pastBlock_preimage hinv, shift_apply, add_zero, append_block_eq_block_succ]

variable [Fintype α]

omit [MeasurableSingletonClass α] in

theorem ae_measureReal_cylinder_pos [IsFiniteMeasure μ] :
    ∀ᵐ x ∂μ, ∀ n : ℕ, 0 < μ.real (cylinder (block n x)) := by
  have h : ∀ᵐ x ∂μ, ∀ n : ℕ, ∀ w : Fin n → α, μ (cylinder w) = 0 → x ∉ cylinder w :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun w => by
      by_cases hw : μ (cylinder w) = 0
      · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hw] with x hx using fun _ => hx
      · exact ae_of_all _ fun x h => absurd h hw
  filter_upwards [h] with x hx n
  refine ENNReal.toReal_pos (fun h0 => hx n (block n x) h0 fun _ => rfl) (measure_ne_top _ _)

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

section SMB

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ : Measure (ℤ → α)} [IsProbabilityMeasure μ]

theorem tendsto_neg_log_cylinder_localEntropy (hinv : MeasurePreserving (shift 1) μ μ)
    {D : Set (ℤ → α)} (hD : MeasurableSet D) (hfull : μ Dᶜ = 0) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => -Real.log (μ.real (cylinder (block n x))) / n) atTop
      (𝓝 (localEntropy μ (atomsOn D fun x => {y | SamePast y x}) x)) := by
  have hM := maker_ae hinv (f := pastInfo μ) (measurable_pastInfo μ) (measurable_condInfo μ _)
    integrable_pastInfoSup abs_pastInfo_le_pastInfoSup (tendsto_pastInfo hD hfull)
  filter_upwards [hM, neg_log_cylinder_eq_sum_pastInfo hinv] with x hx hsum
  refine hx.congr fun n => ?_
  simp only [iterate_shift_one, hsum n, div_eq_inv_mul]

theorem tendsto_neg_log_cylinder_entropy (herg : Ergodic (shift 1) μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => -Real.log (μ.real (cylinder (block n x))) / n) atTop
      (𝓝 (entropy μ)) := by
  have hinv := herg.toMeasurePreserving
  have hfull : μ (univ : Set (ℤ → α))ᶜ = 0 := by simp
  have hc := condEntropy_atomsOn_samePast hinv MeasurableSet.univ hfull
  filter_upwards [tendsto_neg_log_cylinder_localEntropy hinv MeasurableSet.univ hfull,
    localEntropy_ae_eq μ herg (atomsOn univ fun x => {y | SamePast y x})] with x hx hxe
  rwa [hxe, hc] at hx

theorem shannonMcMillanBreiman : ShannonMcMillanBreimanStatement.{u} := by
  intro α _ _ _ μ _ herg
  exact tendsto_neg_log_cylinder_entropy herg

end SMB

end FractalGeometry
