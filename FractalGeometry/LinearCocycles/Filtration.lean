module

public import Mathlib
public import FractalGeometry.LinearCocycles.Products
public import FractalGeometry.Symbolic.Shift
public import FractalGeometry.Symbolic.Past
public import FractalGeometry.Symbolic.PastWords

@[expose] public section

namespace FractalGeometry


open MeasureTheory Filter Topology Set Matrix Module

noncomputable def eucNorm (v : Fin 2 → ℝ) : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 2))‖

theorem eucNorm_eq (v : Fin 2 → ℝ) : eucNorm v = √(v 0 ^ 2 + v 1 ^ 2) := by
  rw [eucNorm, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two]

theorem eucNorm_sq (v : Fin 2 → ℝ) : eucNorm v ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  rw [eucNorm_eq, Real.sq_sqrt (by positivity)]

namespace MatrixTuple

variable {ι : Type*} (A : ι → Matrix (Fin 2) (Fin 2) ℝ)

def HasEucPastRate (x : ℤ → ι) (v : Fin 2 → ℝ) (l : ℝ) : Prop :=
  Tendsto (fun n : ℕ => Real.log (eucNorm (word A (pastWord x n) *ᵥ v)) / n) atTop (𝓝 l)

variable {A}

variable (A) [MeasurableSpace ι]

structure OseledetsSet (μ : Measure (ℤ → ι)) where

  carrier : Set (ℤ → ι)

  V : (ℤ → ι) → ℕ → Submodule ℝ (Fin 2 → ℝ)

  measurableSet_carrier : MeasurableSet carrier

  image_shift : shift 1 '' carrier = carrier

  measure_compl : μ carrierᶜ = 0

  mem_of_samePast : ∀ x ∈ carrier, ∀ y, SamePast y x → y ∈ carrier

  measurableSet_V : ∀ i ≤ 2, MeasurableSet {p : (ℤ → ι) × (Fin 2 → ℝ) | p.2 ∈ V p.1 i}

  map_V : ∀ x ∈ carrier, ∀ i ≤ 2, (V x i).map (A (x (-1))).mulVecLin = V (shift (-1) x) i

  finrank_V : ∀ x ∈ carrier, ∀ i ≤ 2, finrank ℝ (V x i) = 2 - i

  rate_zero : ∀ x ∈ carrier, ∀ v ∈ V x 0, v ∉ V x 1 → HasEucPastRate A x v (lyapunov₁ A μ)

  rate_one : ∀ x ∈ carrier, ∀ v ∈ V x 1, v ∉ V x 2 → HasEucPastRate A x v (lyapunov₂ A μ)

namespace OseledetsSet

variable {A} {μ : Measure (ℤ → ι)} (O : OseledetsSet A μ)

theorem V_zero_eq_top {x : ℤ → ι} (hx : x ∈ O.carrier) : O.V x 0 = ⊤ := by
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [O.finrank_V x hx 0 (by norm_num), finrank_fin_fun]

theorem V_two_eq_bot {x : ℤ → ι} (hx : x ∈ O.carrier) : O.V x 2 = ⊥ := by
  rw [← Submodule.finrank_eq_zero, O.finrank_V x hx 2 le_rfl]

theorem exists_mem_V_one_ne_zero {x : ℤ → ι} (hx : x ∈ O.carrier) :
    ∃ v ∈ O.V x 1, v ≠ 0 := by
  refine Submodule.exists_mem_ne_zero_of_ne_bot fun h => ?_
  have h1 := O.finrank_V x hx 1 (by norm_num)
  rw [h, finrank_bot] at h1
  norm_num at h1

theorem hasEucPastRate_of_notMem {x : ℤ → ι} (hx : x ∈ O.carrier) {v : Fin 2 → ℝ}
    (hv : v ∉ O.V x 1) : HasEucPastRate A x v (lyapunov₁ A μ) :=
  O.rate_zero x hx v (by rw [O.V_zero_eq_top hx]; trivial) hv

theorem hasEucPastRate_of_mem {x : ℤ → ι} (hx : x ∈ O.carrier) {v : Fin 2 → ℝ}
    (hv : v ∈ O.V x 1) (hv0 : v ≠ 0) : HasEucPastRate A x v (lyapunov₂ A μ) :=
  O.rate_one x hx v hv (by rw [O.V_two_eq_bot hx, Submodule.mem_bot]; exact hv0)

end OseledetsSet

end MatrixTuple

end FractalGeometry
