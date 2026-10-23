import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.SelfAffine.Rectangular.Orientation
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.ParityShift

open FractalGeometry.Ergodic

namespace FractalGeometry

open Filter Topology MeasureTheory

section Scalar

theorem sum_zmod_two {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) : ∑ c, f c = f 0 + f 1 :=
  Fin.sum_univ_two f

end Scalar

section Lift

variable {ι : Type*} (o : ι → ZMod 2) {n : ℕ}

def liftBlock (c : ZMod 2) (w : Fin n → ι) : Fin n → ι × ZMod 2 :=
  fun k => (w k, c + ∑ j ∈ Finset.Iio k, o (w j))

@[simp] theorem liftBlock_zero_snd (c : ZMod 2) (w : Fin (n + 1) → ι) :
    (liftBlock o c w 0).2 = c := by
  have h : Finset.Iio (0 : Fin (n + 1)) = ∅ := Finset.Iio_bot
  simp [liftBlock, h]

theorem liftBlock_injective :
    Function.Injective fun p : (Fin (n + 1) → ι) × ZMod 2 => liftBlock o p.2 p.1 := by
  rintro ⟨w, c⟩ ⟨w', c'⟩ h
  have hw : w = w' := funext fun k => congrArg Prod.fst (congrFun h k)
  have hc : c = c' := by simpa using congrArg Prod.snd (congrFun h 0)
  rw [hw, hc]

variable {o}

theorem mem_cylinder_liftBlock {y : ℤ → ι × ZMod 2} (hy : y ∈ subshift o) {w : Fin n → ι}
    (hw : unCode y ∈ cylinder w) : y ∈ cylinder (liftBlock o (y 0).2 w) := by
  intro k
  refine Prod.ext (hw k) ?_
  have hsum : ∑ j ∈ Finset.Iio k, o (w j) = ∑ j ∈ Finset.range k, o (unCode y j) := by
    rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, Finset.sum_map]
    exact Finset.sum_congr rfl fun j _ => congrArg o (hw j).symm
  change (y k).2 = (y 0).2 + ∑ j ∈ Finset.Iio k, o (w j)
  rw [hsum, ← eps_natCast, ← snd_eq_of_mem_subshift hy]

end Lift

section Measure

variable {ι : Type*} (o : ι → ZMod 2) {n : ℕ}

variable [MeasurableSpace ι]

theorem measurable_unCode : Measurable (unCode : (ℤ → ι × ZMod 2) → ℤ → ι) :=
  Measurable.of_eval fun n => measurable_fst.comp (measurable_pi_apply n)

variable {o} {ν : Measure (ℤ → ι × ZMod 2)}

theorem measureReal_preimage_unCode_cylinder [IsFiniteMeasure ν] (hν : ν (subshift o)ᶜ = 0)
    (w : Fin (n + 1) → ι) :
    ν.real (unCode ⁻¹' cylinder w) = ∑ c : ZMod 2, ν.real (cylinder (liftBlock o c w)) := by
  have h := sum_measureReal_inter_preimage_singleton ν (f := fun y => (y 0).2)
    (fun c => (measurable_snd.comp (measurable_pi_apply 0)) (measurableSet_singleton c))
    (unCode ⁻¹' cylinder w)
  rw [← h]
  refine Finset.sum_congr rfl fun c _ => measureReal_congr ?_
  have hae : ∀ᵐ y ∂ν, y ∈ subshift o := mem_ae_iff.2 hν
  refine Filter.eventuallyEqSet_iff.2 (hae.mono fun y hy => ⟨?_, fun h => ⟨?_, ?_⟩⟩)
  · rintro ⟨hw, rfl⟩
    exact mem_cylinder_liftBlock hy hw
  · exact fun k => congrArg Prod.fst (h k)
  · have h0 := congrArg Prod.snd (h 0)
    simpa using h0

end Measure

end FractalGeometry
