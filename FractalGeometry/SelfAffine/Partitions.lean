import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.LinearCocycles.Products
import FractalGeometry.LinearCocycles.RegularFiltration
import FractalGeometry.LinearCocycles.Regularity
import FractalGeometry.SelfAffine.BasicProperties
import FractalGeometry.SelfAffine.Planar
import FractalGeometry.Symbolic.Conditional
import FractalGeometry.Symbolic.ConditionalRefinement
import FractalGeometry.Symbolic.Partitions
import FractalGeometry.Symbolic.Past
import FractalGeometry.Symbolic.Refinement
import FractalGeometry.Symbolic.Shift

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Set Matrix

open scoped Real

universe u

namespace AffineIFS

variable {ι : Type u} (P : AffineIFS ι)

section Oseledets

variable [MeasurableSpace ι]

noncomputable def lyapunov₁ (μ : Measure (ℤ → ι)) : ℝ := MatrixTuple.lyapunov₁ P.mat μ

noncomputable def lyapunov₂ (μ : Measure (ℤ → ι)) : ℝ := MatrixTuple.lyapunov₂ P.mat μ

noncomputable def SigmaPrime (μ : Measure (ℤ → ι)) : Set (ℤ → ι) :=
  MatrixTuple.regularSet P.mat (P.lyapunov₁ μ) (P.lyapunov₂ μ)

noncomputable def oseledets (μ : Measure (ℤ → ι)) (x : ℤ → ι) (i : ℕ) : Set (Fin 2 → ℝ) :=
  MatrixTuple.filtration P.mat (P.lyapunov₂ μ) x i

noncomputable def slowAngle (μ : Measure (ℤ → ι)) (x : ℤ → ι) : ℝ :=
  MatrixTuple.slowAngle P.mat (P.lyapunov₁ μ) (P.lyapunov₂ μ) x

theorem shift_mem_SigmaPrime_iff (μ : Measure (ℤ → ι)) (x : ℤ → ι) :
    shift 1 x ∈ P.SigmaPrime μ ↔ x ∈ P.SigmaPrime μ :=
  MatrixTuple.shift_mem_regularSet_iff P.det_ne_zero _ _ x

theorem oseledets_congr (μ : Measure (ℤ → ι)) {x y : ℤ → ι} (h : SamePast x y) (i : ℕ) :
    P.oseledets μ x i = P.oseledets μ y i :=
  MatrixTuple.filtration_congr h _ i

theorem oseledets_one_eq (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    {x : ℤ → ι} (hx : x ∈ P.SigmaPrime μ) :
    P.oseledets μ x 1 = {v | MatrixTuple.cross (MatrixTuple.dirVec (P.slowAngle μ x)) v = 0} :=
  MatrixTuple.slowLine_eq_cross hlt hx

theorem slowAngle_congr (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    {x y : ℤ → ι} (h : SamePast x y) : P.slowAngle μ x = P.slowAngle μ y :=
  MatrixTuple.slowAngle_congr hlt h

end Oseledets

section Measurability

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem measurableSet_SigmaPrime (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    MeasurableSet (P.SigmaPrime μ) :=
  MatrixTuple.measurableSet_regularSet P.det_ne_zero hlt

theorem measurable_slowAngle (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    Measurable (P.slowAngle μ) :=
  MatrixTuple.measurable_slowAngle P.det_ne_zero hlt

end Measurability

section Partitions

variable [MeasurableSpace ι]

noncomputable def xi (μ : Measure (ℤ → ι)) (i : ℕ) : (ℤ → ι) → Set (ℤ → ι) :=
  atomsOn (P.SigmaPrime μ) fun x =>
    {y | SamePast y x ∧ toVec (P.proj y - P.proj x) ∈ P.oseledets μ x i}

theorem xi_succ_subset (μ : Measure (ℤ → ι)) (i : ℕ) (x : ℤ → ι) :
    P.xi μ (i + 1) x ⊆ P.xi μ i x := by
  unfold xi
  by_cases hx : x ∈ P.SigmaPrime μ
  · rw [atomsOn_of_mem hx, atomsOn_of_mem hx]
    rintro y ⟨⟨hp, hv⟩, hy⟩
    exact ⟨⟨hp, MatrixTuple.filtration_succ_subset _ _ i hv⟩, hy⟩
  · rw [atomsOn_of_notMem hx, atomsOn_of_notMem hx]

end Partitions

section MeasurablePartitions

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem measurable_cross_slowAngle_proj (μ : Measure (ℤ → ι))
    (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ) :
    Measurable fun x =>
      MatrixTuple.cross (MatrixTuple.dirVec (P.slowAngle μ x)) (toVec (P.proj x)) := by
  have h := P.measurable_slowAngle μ hlt
  have hp := P.measurable_proj
  simp only [MatrixTuple.cross, MatrixTuple.dirVec, toVec, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  exact ((Real.measurable_cos.comp h).mul (measurable_snd.comp hp)).sub
    ((Real.measurable_sin.comp h).mul (measurable_fst.comp hp))

theorem isMeasurablePartition_xi (μ : Measure (ℤ → ι)) (hlt : P.lyapunov₂ μ < P.lyapunov₁ μ)
    (i : ℕ) : IsMeasurablePartition (P.xi μ i) := by
  have hD := P.measurableSet_SigmaPrime μ hlt
  unfold xi
  rcases i with _ | _ | i
  · refine isMeasurablePartition_atomsOn hD measurable_past fun x _ y _ => ?_
    simp [oseledets, MatrixTuple.filtration, past_eq_iff]
  · refine isMeasurablePartition_atomsOn hD
      (measurable_past.prodMk (P.measurable_cross_slowAngle_proj μ hlt)) fun x hx y _ => ?_
    simp only [mem_ofPred_eq, Prod.mk.injEq, past_eq_iff, P.oseledets_one_eq μ hlt hx]
    constructor
    · rintro ⟨hp, h⟩
      refine ⟨hp, ?_⟩
      rw [P.slowAngle_congr μ hlt hp]
      simp only [MatrixTuple.cross, toVec_sub, Pi.sub_apply] at h ⊢
      linarith
    · rintro ⟨hp, h⟩
      refine ⟨hp, ?_⟩
      rw [P.slowAngle_congr μ hlt hp] at h
      simp only [MatrixTuple.cross, toVec_sub, Pi.sub_apply] at h ⊢
      linarith
  · refine isMeasurablePartition_atomsOn hD (measurable_past.prodMk P.measurable_proj)
      fun x _ y _ => ?_
    simp only [mem_ofPred_eq, Prod.mk.injEq, past_eq_iff, oseledets,
      MatrixTuple.filtration_add_two, mem_singleton_iff, toVec_sub, sub_eq_zero]
    exact and_congr_right fun _ => toVec_injective.eq_iff

end MeasurablePartitions

section Entropies

variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def dimEntropy (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] (i : ℕ) : ℝ :=
  condEntropy μ (P.xi μ i)

noncomputable def dimEntropyAt (μ : Measure (ℤ → ι)) [IsFiniteMeasure μ] (i : ℕ) :
    (ℤ → ι) → ℝ :=
  localEntropy μ (P.xi μ i)

end Entropies

end AffineIFS

end FractalGeometry
