import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.SelfAffine.Planar
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.Shift
import FractalGeometry.Symbolic.WordAverages

open FractalGeometry.Ergodic

namespace FractalGeometry

open MeasureTheory Filter Topology Matrix

open scoped Matrix.Norms.L2Operator

theorem toVec_injective : Function.Injective toVec := fun z w h => by
  rw [← ofVec_toVec z, h, ofVec_toVec]

theorem continuous_ofVec : Continuous ofVec := by
  unfold ofVec; fun_prop

theorem continuous_toVec : Continuous toVec := by
  unfold toVec
  refine continuous_pi fun j => ?_
  fin_cases j
  · exact continuous_fst
  · exact continuous_snd

namespace AffineIFS

variable {ι : Type*} (P : AffineIFS ι)

theorem continuous_phi (i : ι) : Continuous (P.phi i) := by
  unfold phi
  have : Continuous fun z => P.mat i *ᵥ toVec z :=
    (Matrix.mulVecLin (P.mat i)).continuous_of_finiteDimensional.comp continuous_toVec
  exact (continuous_ofVec.comp this).add continuous_const

theorem proj_eq [Finite ι] (x : ℤ → ι) : P.proj x = P.phi (x 0) (P.proj (shift 1 x)) := by
  have h1 : Tendsto (fun n => P.phiWord (futureWord x (n + 1)) 0) atTop (𝓝 (P.proj x)) :=
    (tendsto_add_atTop_iff_nat 1).2 (P.tendsto_phiWord x)
  have h2 : Tendsto (fun n => P.phi (x 0) (P.phiWord (futureWord (shift 1 x) n) 0)) atTop
      (𝓝 (P.phi (x 0) (P.proj (shift 1 x)))) :=
    ((P.continuous_phi (x 0)).tendsto _).comp (P.tendsto_phiWord (shift 1 x))
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  rw [futureWord_succ', phiWord_cons, Function.comp_apply]

theorem proj_sub_proj [Finite ι] {x y : ℤ → ι} (h : y 0 = x 0) :
    toVec (P.proj y - P.proj x) =
      P.mat (x 0) *ᵥ toVec (P.proj (shift 1 y) - P.proj (shift 1 x)) := by
  rw [P.proj_eq y, P.proj_eq x, h, P.phi_sub_phi, toVec_ofVec]

theorem measurable_proj [Finite ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] :
    Measurable P.proj := by
  refine measurable_of_tendsto_metrizable (f := fun n x => P.phiWord (futureWord x n) 0)
    (fun n => ?_) (tendsto_pi_nhds.2 P.tendsto_phiWord)
  simp only [futureWord_eq_ofFn_block]
  exact (Measurable.of_discrete (f := fun w : Fin n → ι => P.phiWord (List.ofFn w) 0)).comp
    (measurable_block n)

end AffineIFS

end FractalGeometry
