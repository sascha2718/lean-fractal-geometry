module

public import Mathlib
public import FractalGeometry.LinearCocycles.Products
public import FractalGeometry.Symbolic.Shift
public import FractalGeometry.LinearCocycles.Filtration
public import FractalGeometry.LinearCocycles.Regularity
public import FractalGeometry.LinearCocycles.PlaneNorm
public import FractalGeometry.Symbolic.Past
public import FractalGeometry.Symbolic.PastWords

@[expose] public section

namespace FractalGeometry


open MeasureTheory Filter Topology Set Matrix Module

open scoped Real

theorem abs_log_eucNorm_sub_log_norm_le (v : Fin 2 → ℝ) :
    |Real.log (eucNorm v) - Real.log ‖v‖| ≤ Real.log 2 := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  by_cases hv : v = 0
  · subst hv
    simpa [eucNorm] using hlog2
  have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hle : ‖v‖ ≤ eucNorm v := by
    rw [norm_fin_two, eucNorm_eq]
    refine max_le ?_ ?_
    · rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (v 1)])
    · rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (v 0)])
  have hge : eucNorm v ≤ 2 * ‖v‖ := by
    rw [norm_fin_two, eucNorm_eq]
    have h0 : |v 0| ≤ max |v 0| |v 1| := le_max_left _ _
    have h1 : |v 1| ≤ max |v 0| |v 1| := le_max_right _ _
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [abs_nonneg (v 0), abs_nonneg (v 1), sq_abs (v 0), sq_abs (v 1)]
  have hepos : 0 < eucNorm v := hpos.trans_le hle
  rw [abs_le]
  constructor
  · have := Real.log_le_log hpos hle
    linarith
  · have := Real.log_le_log hepos hge
    rw [Real.log_mul (by norm_num) hpos.ne'] at this
    linarith

namespace MatrixTuple

variable {ι : Type*} {A : ι → Matrix (Fin 2) (Fin 2) ℝ}

theorem hasPastRate_iff_hasEucPastRate (x : ℤ → ι) (v : Fin 2 → ℝ) (l : ℝ) :
    HasPastRate A x v l ↔ HasEucPastRate A x v l := by
  constructor
  · intro h
    exact tendsto_div_of_abs_sub_le (Real.log 2)
      (Eventually.of_forall fun n => abs_log_eucNorm_sub_log_norm_le _) h
  · intro h
    refine tendsto_div_of_abs_sub_le (Real.log 2) (Eventually.of_forall fun n => ?_) h
    rw [abs_sub_comm]
    exact abs_log_eucNorm_sub_log_norm_le _

variable [MeasurableSpace ι] {μ : Measure (ℤ → ι)}

theorem OseledetsSet.carrier_subset_regularSet (O : OseledetsSet A μ) (hA : ∀ i, (A i).det ≠ 0)
    (hlt : lyapunov₂ A μ < lyapunov₁ A μ) :
    O.carrier ⊆ regularSet A (lyapunov₁ A μ) (lyapunov₂ A μ) := by
  intro x hx
  obtain ⟨u, hu, hu0⟩ := O.exists_mem_V_one_ne_zero hx
  obtain ⟨w, hw⟩ : ∃ w, w ∉ O.V x 1 := by
    by_contra h
    push Not at h
    have htop : O.V x 1 = ⊤ := Submodule.eq_top_iff'.2 h
    have h1 := O.finrank_V x hx 1 (by norm_num)
    rw [htop, finrank_top, finrank_fin_fun] at h1
    norm_num at h1
  have hw0 : w ≠ 0 := fun h => hw (h ▸ (O.V x 1).zero_mem)
  exact ⟨u, isRegularWith_of hA hlt hu0 hw0
    ((hasPastRate_iff_hasEucPastRate x u _).2 (O.hasEucPastRate_of_mem hx hu hu0))
    ((hasPastRate_iff_hasEucPastRate x w _).2 (O.hasEucPastRate_of_notMem hx hw))⟩

theorem OseledetsSet.measure_regularSet_compl (O : OseledetsSet A μ) (hA : ∀ i, (A i).det ≠ 0)
    (hlt : lyapunov₂ A μ < lyapunov₁ A μ) :
    μ (regularSet A (lyapunov₁ A μ) (lyapunov₂ A μ))ᶜ = 0 :=
  measure_mono_null (compl_subset_compl.2 (O.carrier_subset_regularSet hA hlt)) O.measure_compl

variable (A μ) in

noncomputable def regularV (x : ℤ → ι) : ℕ → Submodule ℝ (Fin 2 → ℝ)
  | 0 => ⊤
  | 1 => ℝ ∙ dirVec (slowAngle A (lyapunov₁ A μ) (lyapunov₂ A μ) x)
  | _ => ⊥

theorem coe_regularV_one (hlt : lyapunov₂ A μ < lyapunov₁ A μ) {x : ℤ → ι}
    (hx : x ∈ regularSet A (lyapunov₁ A μ) (lyapunov₂ A μ)) :
    (regularV A μ x 1 : Set (Fin 2 → ℝ)) = slowLine A (lyapunov₂ A μ) x :=
  (slowLine_eq_span hlt (isRegularWith_slowAngle hlt hx)).symm

variable [Fintype ι] [MeasurableSingletonClass ι]

variable (A μ) in

noncomputable def regularOseledetsSet (hA : ∀ i, (A i).det ≠ 0)
    (hlt : lyapunov₂ A μ < lyapunov₁ A μ)
    (hfull : μ (regularSet A (lyapunov₁ A μ) (lyapunov₂ A μ))ᶜ = 0) : OseledetsSet A μ where
  carrier := regularSet A (lyapunov₁ A μ) (lyapunov₂ A μ)
  V := regularV A μ
  measurableSet_carrier := measurableSet_regularSet hA hlt
  image_shift := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (shift_mem_regularSet_iff hA _ _ x).2 hx
    · intro hy
      refine ⟨shift (-1) y, ?_, by rw [shift_shift]; simp⟩
      rw [← shift_mem_regularSet_iff hA, shift_shift]
      simpa using hy
  measure_compl := hfull
  mem_of_samePast := fun x hx y h => mem_regularSet_of_samePast h.symm hx
  measurableSet_V := by
    intro i hi
    rcases i with _ | _ | i
    · exact MeasurableSet.univ
    · have e : {p : (ℤ → ι) × (Fin 2 → ℝ) | p.2 ∈ regularV A μ p.1 1} =
          {p | cross (dirVec (slowAngle A (lyapunov₁ A μ) (lyapunov₂ A μ) p.1)) p.2 = 0} := by
        ext p
        exact mem_span_iff_cross (dirVec_ne_zero _) p.2
      rw [e]
      have hθ : Measurable fun p : (ℤ → ι) × (Fin 2 → ℝ) =>
          slowAngle A (lyapunov₁ A μ) (lyapunov₂ A μ) p.1 :=
        (measurable_slowAngle hA hlt).comp measurable_fst
      refine measurableSet_eq_fun ?_ measurable_const
      simp only [cross, dirVec, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact ((Real.measurable_cos.comp hθ).mul ((measurable_pi_apply 1).comp measurable_snd)).sub
        ((Real.measurable_sin.comp hθ).mul ((measurable_pi_apply 0).comp measurable_snd))
    · have e : {p : (ℤ → ι) × (Fin 2 → ℝ) | p.2 ∈ regularV A μ p.1 (i + 2)} =
          {p | p.2 = 0} := by
        ext p
        exact Submodule.mem_bot ℝ
      rw [e]
      exact measurableSet_eq_fun measurable_snd measurable_const
  map_V := by
    intro x hx i hi
    rcases i with _ | _ | i
    · change (⊤ : Submodule ℝ (Fin 2 → ℝ)).map (A (x (-1))).mulVecLin = ⊤
      rw [Submodule.map_top, LinearMap.range_eq_top]
      intro v
      exact ⟨(A (x (-1)))⁻¹ *ᵥ v, mulVec_inv_mulVec (hA _) v⟩
    · have hx' : shift (-1) x ∈ regularSet A (lyapunov₁ A μ) (lyapunov₂ A μ) := by
        rw [← shift_mem_regularSet_iff hA, shift_shift]
        simpa using hx
      refine SetLike.coe_injective ?_
      rw [Submodule.map_coe, coe_regularV_one hlt hx, coe_regularV_one hlt hx']
      exact image_slowLine hA _ x
    · exact Submodule.map_bot _
  finrank_V := by
    intro x _ i hi
    rcases i with _ | _ | i
    · change finrank ℝ (⊤ : Submodule ℝ (Fin 2 → ℝ)) = 2 - 0
      rw [finrank_top, finrank_fin_fun]
    · change finrank ℝ (ℝ ∙ dirVec (slowAngle A (lyapunov₁ A μ) (lyapunov₂ A μ) x)) = 2 - 1
      rw [finrank_span_singleton (dirVec_ne_zero _)]
    · change finrank ℝ (⊥ : Submodule ℝ (Fin 2 → ℝ)) = 2 - (i + 2)
      rw [finrank_bot]
      omega
  rate_zero := by
    intro x hx v _ hv
    exact (hasPastRate_iff_hasEucPastRate x v _).1
      (((isRegularWith_slowAngle hlt hx).2 v).2 hv)
  rate_one := by
    intro x hx v hv hv2
    have hv0 : v ≠ 0 := fun h => hv2 (h ▸ Submodule.zero_mem _)
    exact (hasPastRate_iff_hasEucPastRate x v _).1
      (((isRegularWith_slowAngle hlt hx).2 v).1 hv hv0)

theorem nonempty_oseledetsSet_iff (hA : ∀ i, (A i).det ≠ 0)
    (hlt : lyapunov₂ A μ < lyapunov₁ A μ) :
    Nonempty (OseledetsSet A μ) ↔ μ (regularSet A (lyapunov₁ A μ) (lyapunov₂ A μ))ᶜ = 0 :=
  ⟨fun ⟨O⟩ => O.measure_regularSet_compl hA hlt,
    fun h => ⟨regularOseledetsSet A μ hA hlt h⟩⟩

end MatrixTuple

end FractalGeometry
