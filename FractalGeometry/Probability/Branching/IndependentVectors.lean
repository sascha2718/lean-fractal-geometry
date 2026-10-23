import Mathlib
import FractalGeometry.Probability.Branching.Law
import FractalGeometry.Probability.Branching.Process
import FractalGeometry.Probability.Branching.Words

namespace FractalGeometry.Probability.Branching

open Finset MeasureTheory Measure ProbabilityTheory Real

open scoped BigOperators

variable {A : Law} {Omega : Type*} [MeasurableSpace Omega]

noncomputable instance decidableRetainedBelow
    (X : Word A -> (Fin A.arity) -> Omega -> Bool)
    (omega : Omega) (root u : Word A) :
    Decidable (RetainedBelow X omega root u) := Classical.dec _

theorem iIndepFun_curry_of_uncurry
    {I : Type*} {J : I -> Type*} {Y : (i : I) -> J i -> Type*}
    [forall i j, MeasurableSpace (Y i j)]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {Z : (i : I) -> (j : J i) -> Omega -> Y i j}
    (hZ : forall i j, Measurable (Z i j))
    (h : iIndepFun (fun p : (i : I) × J i => Z p.1 p.2) P) :
    iIndepFun (fun i omega j => Z i j omega) P := by
  have hmap : forall i j, IsProbabilityMeasure (P.map (Z i j)) :=
    fun _ _ => inferInstance
  let _ (i : I) (j : J i) : IsProbabilityMeasure (P.map (Z i j)) := hmap i j
  have hinner (i : I) : iIndepFun (Z i) P := by
    apply h.precomp (g := fun j => Sigma.mk i j)
    intro j k hjk
    simpa using hjk
  have hcurry :
      (MeasurableEquiv.piCurry Y) ∘
          (fun omega (p : (i : I) × J i) => Z p.1 p.2 omega) =
        fun omega i j => Z i j omega := by
    ext omega i j
    simp [Sigma.curry]
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  rw [← hcurry, ← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [(iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)).mp h]
  calc
    Measure.map (MeasurableEquiv.piCurry Y)
        (Measure.infinitePi fun p => P.map (Z p.1 p.2)) =
        Measure.infinitePi
          (fun i => Measure.infinitePi fun j => P.map (Z i j)) :=
      Measure.infinitePi_map_piCurry (X := Y)
        (fun i j => P.map (Z i j))
    _ = Measure.infinitePi
          (fun i => P.map (fun omega j => Z i j omega)) := by
      congrm Measure.infinitePi fun i => ?_
      exact ((iIndepFun_iff_map_fun_eq_infinitePi_map (hZ i)).mp (hinner i)).symm

end FractalGeometry.Probability.Branching
