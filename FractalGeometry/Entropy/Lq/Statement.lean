import Mathlib
import FractalGeometry.Pressure.Rectangular.LyapunovStatement
import FractalGeometry.SelfSimilar.SimilarityWords

namespace FractalGeometry

open MeasureTheory

universe u

def ShmerkinStopping {κ : Type*} (r : κ → ℝ) (M : ℕ) (u : List κ) : Prop :=
  u ≠ [] ∧ |(u.map r).prod| ≤ (2 : ℝ) ^ (-(M : ℝ)) ∧
    (2 : ℝ) ^ (-(M : ℝ)) < |(u.dropLast.map r).prod|

def ShmerkinExpSeparation {κ : Type*} (r t : κ → ℝ) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∃ᶠ M : ℕ in Filter.atTop, ∀ u v : List κ, u ≠ v →
    ShmerkinStopping r M u → ShmerkinStopping r M v → (u.map r).prod = (v.map r).prod →
    (2 : ℝ) ^ (-(R * M)) ≤ |simWord r t u 0 - simWord r t v 0|

def ShmerkinLqDimension : Prop :=
  ∀ {κ : Type u} [Fintype κ] (r t p : κ → ℝ), (∀ j, r j ≠ 0) → (∀ j, |r j| < 1) →
    (∀ j, 0 < p j) → ∑ j, p j = 1 → ShmerkinExpSeparation r t →
    ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
    μ = ∑ j, ENNReal.ofReal (p j) • μ.map (fun x => r j * x + t j) →
    ∀ q : ℝ, 1 < q → ∀ α : ℝ, α < 1 → ∑ j, p j ^ q * |r j| ^ (-((q - 1) * α)) < 1 →
    ∀ᶠ M : ℕ in Filter.atTop, ∀ s : Finset ℤ,
      ∑ k ∈ s, (μ.real (Set.Ico ((k : ℝ) / 2 ^ M) ((k + 1) / 2 ^ M))) ^ q ≤
        (2 : ℝ) ^ (-((M : ℝ) * ((q - 1) * α)))

end FractalGeometry
