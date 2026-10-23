/-
The standard logarithmic covering-count limit. For a nonempty totally
bounded set, equality of its lower and upper box dimensions to a finite
value implies convergence of log N(r) / (-log r) to that value.
Uses the geometric measure theory library definitions, with no system
or iterated-function-system hypotheses.
-/
import GeometricMeasureTheory.Box.BoxDimension

open GeometricMeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

noncomputable section

namespace FractalGeometry.Dimension

variable {X : Type*} [PseudoMetricSpace X]

def coveringExponent (E : Set X) (r : ℝ) : ℝ :=
  Real.log (externalCoveringNumber r.toNNReal E : ℝ≥0∞).toReal / (-Real.log r)

theorem one_le_coveringNumber_toReal {E : Set X} (hE : TotallyBounded E)
    (hne : E.Nonempty) {r : ℝ} (hr : 0 < r) :
    1 ≤ (externalCoveringNumber r.toNNReal E : ℝ≥0∞).toReal := by
  have htop : (externalCoveringNumber r.toNNReal E : ℝ≥0∞) ≠ ⊤ :=
    ENat.toENNReal_ne_top.2 (externalCoveringNumber_ne_top hE (Real.toNNReal_pos.2 hr))
  have h1 : (1 : ℝ≥0∞) ≤ externalCoveringNumber r.toNNReal E := by
    have hnat : 1 ≤ externalCoveringNumber r.toNNReal E :=
      Order.one_le_iff_pos.2 (externalCoveringNumber_pos_iff.2 hne)
    simpa using ENat.toENNReal_le.2 hnat
  simpa using ENNReal.toReal_mono htop h1

theorem tendsto_coveringExponent_of_boxDim_eq {E : Set X} (hE : TotallyBounded E)
    (hne : E.Nonempty) {s : ℝ≥0} (hlower : lowerBoxDim E = (s : ℝ≥0∞))
    (hupper : upperBoxDim E = (s : ℝ≥0∞)) :
    Tendsto (coveringExponent E) (𝓝[>] (0 : ℝ)) (𝓝 (s : ℝ)) := by
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r ∧ r < 1 :=
    eventually_mem_nhdsWithin.and (nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one))
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    by_cases ha0 : a < 0
    · filter_upwards [hsmall] with r hr
      have hN := one_le_coveringNumber_toReal hE hne hr.1
      have hlog : 0 ≤ Real.log (externalCoveringNumber r.toNNReal E : ℝ≥0∞).toReal :=
        Real.log_nonneg hN
      exact ha0.trans_le (div_nonneg hlog (neg_nonneg.2 (Real.log_nonpos hr.1.le hr.2.le)))
    · have ha0' : 0 ≤ a := le_of_not_gt ha0
      have hnot : ¬ LowerBoxDimLE E a := by
        intro hle
        have hdim := lowerBoxDim_le_of_lowerBoxDimLE (s := ⟨a, ha0'⟩) hle
        rw [hlower] at hdim
        have : (s : ℝ) ≤ a := by exact_mod_cast ENNReal.coe_le_coe.1 hdim
        linarith
      have hcount : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
          ENNReal.ofReal (r ^ (-a)) < (externalCoveringNumber r.toNNReal E : ℝ≥0∞) := by
        simpa [LowerBoxDimLE, Filter.not_frequently, not_le] using hnot
      filter_upwards [hsmall, hcount] with r hr hNr
      have htop : (externalCoveringNumber r.toNNReal E : ℝ≥0∞) ≠ ⊤ :=
        ENat.toENNReal_ne_top.2 (externalCoveringNumber_ne_top hE (Real.toNNReal_pos.2 hr.1))
      have hreal : r ^ (-a) < (externalCoveringNumber r.toNNReal E : ℝ≥0∞).toReal := by
        have hh := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top htop).2 hNr
        simpa [ENNReal.toReal_ofReal (Real.rpow_nonneg hr.1.le _)] using hh
      have hlog := Real.log_lt_log (Real.rpow_pos_of_pos hr.1 _) hreal
      rw [Real.log_rpow hr.1] at hlog
      change a < _ / (-Real.log r)
      apply (lt_div_iff₀ (neg_pos.2 (Real.log_neg hr.1 hr.2))).2
      nlinarith
  · intro b hb
    have hb0 : 0 ≤ b := s.coe_nonneg.trans hb.le
    let bnn : ℝ≥0 := ⟨b, hb0⟩
    have hdim : upperBoxDim E < (bnn : ℝ≥0∞) := by
      rw [hupper]
      exact ENNReal.coe_lt_coe.2 (show s < bnn from hb)
    obtain ⟨t, ht⟩ := iInf_lt_iff.1 hdim
    obtain ⟨htLE, htb⟩ := iInf_lt_iff.1 ht
    have htb' : (t : ℝ) < b := by exact_mod_cast ENNReal.coe_lt_coe.1 htb
    filter_upwards [hsmall, htLE] with r hr hNr
    have hNpos : 0 < (externalCoveringNumber r.toNNReal E : ℝ≥0∞).toReal :=
      one_pos.trans_le (one_le_coveringNumber_toReal hE hne hr.1)
    have hreal : (externalCoveringNumber r.toNNReal E : ℝ≥0∞).toReal ≤ r ^ (-(t : ℝ)) :=
      ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hr.1.le _) hNr
    have hlog := Real.log_le_log hNpos hreal
    rw [Real.log_rpow hr.1] at hlog
    change _ / (-Real.log r) < b
    apply lt_of_le_of_lt ((div_le_iff₀ (neg_pos.2 (Real.log_neg hr.1 hr.2))).2 ?_) htb'
    nlinarith

end FractalGeometry.Dimension
