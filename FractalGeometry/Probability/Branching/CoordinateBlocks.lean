import Mathlib
import FractalGeometry.Probability.Branching.IndependentVectors
import FractalGeometry.Probability.Branching.Law

namespace FractalGeometry.Probability.Branching

universe u v

open Finset MeasureTheory Measure ProbabilityTheory Real

open scoped BigOperators

variable {A : Law} {Omega : Type*} [MeasurableSpace Omega]

inductive IndepBlock where
  | left
  | right
  deriving DecidableEq

def IndepBlock.Index (I J : Type u) : IndepBlock -> Type u
  | .left => I
  | .right => J

def IndepBlock.coordinate {Q : Type v} {I J : Type u} (f : I -> Q) (g : J -> Q) :
    (b : IndepBlock) -> IndepBlock.Index I J b -> Q
  | .left, i => f i
  | .right, j => g j

theorem IndepBlock.coordinate_injective {Q : Type v} {I J : Type u}
    {f : I -> Q} {g : J -> Q}
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : forall i j, f i ≠ g j) :
    Function.Injective
      (fun p : (b : IndepBlock) × IndepBlock.Index I J b =>
        IndepBlock.coordinate f g p.1 p.2) := by
  rintro ⟨b, x⟩ ⟨c, y⟩ h
  cases b <;> cases c
  · have hxy : x = y := hf h
    subst y
    rfl
  · exact False.elim (hfg x y h)
  · exact False.elim (hfg y x h.symm)
  · have hxy : x = y := hg h
    subst y
    rfl

theorem iIndepFun.indepFun_coordinateBlocks
    {Q : Type v} {I J : Type u} {Y : Q -> Type*} [forall q, MeasurableSpace (Y q)]
    {P : Measure Omega} {Z : (q : Q) -> Omega -> Y q}
    (hZ : forall q, Measurable (Z q)) (h : iIndepFun Z P)
    (f : I -> Q) (g : J -> Q)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : forall i j, f i ≠ g j) :
    IndepFun (fun omega i => Z (f i) omega) (fun omega j => Z (g j) omega) P := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  let W : (b : IndepBlock) ->
      (x : IndepBlock.Index I J b) -> Omega -> Y (IndepBlock.coordinate f g b x) :=
    fun b x => Z (IndepBlock.coordinate f g b x)
  have hraw : iIndepFun
      (fun p : (b : IndepBlock) × IndepBlock.Index I J b => W p.1 p.2) P := by
    exact h.precomp (IndepBlock.coordinate_injective hf hg hfg)
  have hblocks : iIndepFun (fun b omega x => W b x omega) P :=
    iIndepFun_curry_of_uncurry (fun b x => hZ _) hraw
  change IndepFun
    (fun omega (x : IndepBlock.Index I J IndepBlock.left) => W IndepBlock.left x omega)
    (fun omega (x : IndepBlock.Index I J IndepBlock.right) => W IndepBlock.right x omega) P
  exact hblocks.indepFun (i := IndepBlock.left) (j := IndepBlock.right) (by decide)

end FractalGeometry.Probability.Branching
