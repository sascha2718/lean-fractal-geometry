import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.LinearCocycles.Invertibility
import FractalGeometry.LinearCocycles.Regularity
import FractalGeometry.SelfAffine.BasicProperties
import FractalGeometry.SelfAffine.ConditionalEntropy
import FractalGeometry.SelfAffine.Partitions
import FractalGeometry.SelfAffine.Planar
import FractalGeometry.Symbolic.Conditional
import FractalGeometry.Symbolic.ConditionalEntropyRate
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.Past
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology Set Matrix

universe u

namespace AffineIFS

section Invariance

variable {ι : Type u} [MeasurableSpace ι] (P : AffineIFS ι)

theorem mulVec_mem_oseledets_iff (μ : Measure (ℤ → ι)) (x : ℤ → ι) (i : ℕ) (w : Fin 2 → ℝ) :
    w ∈ P.oseledets μ (shift 1 x) i ↔ P.mat (x 0) *ᵥ w ∈ P.oseledets μ x i := by
  rcases i with _ | _ | i
  · simp [oseledets, MatrixTuple.filtration]
  · simp only [oseledets]
    exact MatrixTuple.mem_slowLine_shift_iff P.det_ne_zero _ x w
  · simp only [oseledets, MatrixTuple.filtration_add_two, mem_singleton_iff]
    constructor
    · rintro rfl
      exact mulVec_zero _
    · intro h
      by_contra hw
      exact mulVec_ne_zero_of_det_ne_zero (P.det_ne_zero (x 0)) hw h

theorem pullShift_xi [Finite ι] (μ : Measure (ℤ → ι)) (i : ℕ) {x : ℤ → ι}
    (hx : x ∈ P.SigmaPrime μ) : pullShift (P.xi μ i) x = refineZero (P.xi μ i) x := by
  have hσx : shift 1 x ∈ P.SigmaPrime μ := (P.shift_mem_SigmaPrime_iff μ x).2 hx
  ext y
  simp only [pullShift, refineZero, xi, mem_preimage, atomsOn_of_mem hσx, atomsOn_of_mem hx,
    mem_inter_iff, mem_ofPred_eq, samePast_shift_one_iff, P.shift_mem_SigmaPrime_iff]
  constructor
  · rintro ⟨⟨⟨hp, h0⟩, hv⟩, hy⟩
    refine ⟨⟨⟨hp, ?_⟩, hy⟩, h0⟩
    rw [P.proj_sub_proj h0]
    exact (P.mulVec_mem_oseledets_iff μ x i _).1 hv
  · rintro ⟨⟨⟨hp, hv⟩, hy⟩, h0⟩
    refine ⟨⟨⟨hp, h0⟩, ?_⟩, hy⟩
    rw [P.proj_sub_proj h0] at hv
    exact (P.mulVec_mem_oseledets_iff μ x i _).2 hv

theorem xi_subset_SigmaPrime (μ : Measure (ℤ → ι)) (i : ℕ) {x : ℤ → ι}
    (hx : x ∈ P.SigmaPrime μ) : P.xi μ i x ⊆ P.SigmaPrime μ := by
  rw [xi, atomsOn_of_mem hx]
  exact inter_subset_right

theorem pullShift_xi_subset_of_notMem (μ : Measure (ℤ → ι)) (i : ℕ) {x : ℤ → ι}
    (hx : x ∉ P.SigmaPrime μ) : pullShift (P.xi μ i) x ⊆ (P.SigmaPrime μ)ᶜ := by
  have hσx : shift 1 x ∉ P.SigmaPrime μ := fun h => hx ((P.shift_mem_SigmaPrime_iff μ x).1 h)
  intro y hy
  simp only [pullShift, xi, mem_preimage, atomsOn_of_notMem hσx, mem_compl_iff] at hy ⊢
  exact fun h => hy ((P.shift_mem_SigmaPrime_iff μ y).2 h)

end Invariance

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (P : AffineIFS ι)

theorem infoSum_xi (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    (hfull : μ (P.SigmaPrime μ)ᶜ = 0) (i : ℕ) : P.InfoSum μ i :=
  infoSum_of_pullShift hinv (P.isMeasurablePartition_xi μ hlt i)
    (P.measurableSet_SigmaPrime μ hlt) hfull (fun _ hx => P.pullShift_xi μ i hx)
    (fun _ hx => P.xi_subset_SigmaPrime μ i hx) (fun _ hx => P.pullShift_xi_subset_of_notMem μ i hx)

theorem feng_entropy_as_limit_of_full (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (shift 1) μ μ) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    (hfull : μ (P.SigmaPrime μ)ᶜ = 0) (i : ℕ) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => -Real.log ((condMeas μ (P.xi μ i) x).real (cylinder (block n x))) / n)
      atTop (𝓝 (P.dimEntropyAt μ i x)) :=
  P.feng_entropy_as_limit_of_infoSum μ hinv (P.infoSum_xi μ hinv hlt hfull i)

end AffineIFS

end FractalGeometry
