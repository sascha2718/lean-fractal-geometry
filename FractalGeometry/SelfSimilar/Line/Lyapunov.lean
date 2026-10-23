import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.SelfSimilar.Line.Defs

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter

open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [MeasurableSpace ι]

namespace LineIFS

variable [MeasurableSingletonClass ι] (S : LineIFS ι)

noncomputable def lyapunov (ν : Measure (ℤ → ι)) : ℝ :=
  ∫ y, Real.log |S.ratio (y 0)| ∂ν

theorem lyapunov_neg [Finite ι] (ν : Measure (ℤ → ι)) [IsProbabilityMeasure ν] :
    S.lyapunov ν < 0 := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨y⟩ : Nonempty (ℤ → ι) := nonempty_of_isProbabilityMeasure ν
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
    (fun p : ι => Real.log |S.ratio p|) ⟨y 0, Finset.mem_univ _⟩
  obtain ⟨q, -, hq⟩ := Finset.exists_max_image Finset.univ
    (fun p : ι => abs (Real.log |S.ratio p|)) ⟨y 0, Finset.mem_univ _⟩
  have hneg : Real.log |S.ratio p| < 0 :=
    Real.log_neg (abs_pos.2 (S.ratio_ne_zero p)) (S.abs_ratio_lt_one p)
  have hmeas : Measurable fun y : ℤ → ι => Real.log |S.ratio (y 0)| :=
    (Measurable.of_discrete (f := fun p : ι => Real.log |S.ratio p|)).comp
      (measurable_pi_apply 0)
  have hint : Integrable (fun y : ℤ → ι => Real.log |S.ratio (y 0)|) ν :=
    Integrable.of_bound hmeas.aestronglyMeasurable (abs (Real.log |S.ratio q|))
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact hq (y 0) (Finset.mem_univ _))
  calc S.lyapunov ν ≤ ∫ _, Real.log |S.ratio p| ∂ν :=
        integral_mono hint (integrable_const _) fun y => hp (y 0) (Finset.mem_univ _)
    _ = Real.log |S.ratio p| := by simp
    _ < 0 := hneg

end LineIFS

end FractalGeometry
