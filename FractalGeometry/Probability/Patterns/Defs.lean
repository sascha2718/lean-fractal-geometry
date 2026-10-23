import Mathlib

namespace FractalGeometry.Probability.Patterns

open MeasureTheory ProbabilityTheory Metric Filter Topology Asymptotics

open scoped ENNReal NNReal

abbrev Word (ι : Type*) (n : ℕ) := Fin n → ι

structure Weights (ι : Type*) [Fintype ι] where

  p : ι → ℝ

  pos : ∀ i, 0 < p i

  sum_eq_one : ∑ i, p i = 1

namespace Weights

variable {ι : Type*} [Fintype ι] (p : Weights ι)

noncomputable def wordProb {n : ℕ} (w : Word ι n) : ℝ := ∏ i, p.p (w i)

end Weights

variable {ι : Type*} [Fintype ι]

variable {Ω : Type*}

structure IsIIDProcess [MeasurableSpace ι] [MeasurableSpace Ω] (p : Weights ι)
    (P : Measure Ω) (I : ℕ → Ω → ι) : Prop where

  isProbability : IsProbabilityMeasure P

  measurable : ∀ k, Measurable (I k)

  indep : iIndepFun I P

  law : ∀ k i, P {ω | I k ω = i} = ENNReal.ofReal (p.p i)

def block (I : ℕ → Ω → ι) (n k : ℕ) (ω : Ω) : Word ι n := fun i => I (k - n + 1 + i) ω

noncomputable def Weights.prefixProb (p : Weights ι) {m : ℕ} (z : Word ι m) (k : ℕ) : ℝ := by
  classical exact ∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < k), p.p (z i)

def Overlap {m : ℕ} (u z : Word ι m) (h : ℕ) : Prop :=
  ∀ (j : Fin m) (hj : (j : ℕ) + h < m), u ⟨j + h, hj⟩ = z j

noncomputable def Weights.corr (p : Weights ι) {m : ℕ} (u z : Word ι m) : ℝ := by
  classical exact ∑ h ∈ Finset.range m, if Overlap u z h then (p.prefixProb z (m - h))⁻¹ else 0

noncomputable def Weights.patternMass (p : Weights ι) {m : ℕ} (U : Finset (Word ι m)) : ℝ :=
  ∑ z ∈ U, p.wordProb z

noncomputable def hittingTime (I : ℕ → Ω → ι) (m : ℕ) (U : Finset (Word ι m)) (ω : Ω) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : m ≤ k) (_ : block I m k ω ∈ U), (k : ℕ∞)

noncomputable def expectedHitting [MeasurableSpace Ω] (P : Measure Ω) (I : ℕ → Ω → ι) (m : ℕ)
    (U : Finset (Word ι m)) : ℝ≥0∞ :=
  ∫⁻ ω, (hittingTime I m U ω : ℝ≥0∞) ∂P

def NoOcc (I : ℕ → Ω → ι) (m : ℕ) (U : Finset (Word ι m)) (L : ℕ) (ω : Ω) : Prop :=
  ∀ k, m ≤ k → k ≤ L → block I m k ω ∉ U

end FractalGeometry.Probability.Patterns
