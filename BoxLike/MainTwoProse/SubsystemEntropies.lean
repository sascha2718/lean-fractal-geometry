module

/-
The conditional entropies `q_{x,n}`, `q_{y,n}` and `q_n` of the first subsystem symbol given the
horizontal coordinate, the vertical coordinate and the planar point of the coded point, in the
proof of `thm:main2` in `sec:dimension_result_proof`. The manuscript writes them as entropies
of `sec:entropies`: "Since `ν_n` is Bernoulli and the Oseledets subspace `V^1` is the `y`-axis,
`h_1(ν_n)` is the conditional entropy of the first symbol given the horizontal coordinate of
the coded point", `H_{ν_n}(𝒫 | \widehat{ξ_1^⊥})` is "the conditional entropy given the vertical
coordinate", and `h_2(ν_n)` is the one given the planar point. For the Bernoulli measure `ν_n`
of a homogeneous diagonal system with `|b| < |a|` they satisfy the steps of the prose:

* `System.condEntropyCoord`, `System.condEntropyPoint`: `q_{x,n}`, `q_{y,n}` (the coordinate
  `c = 0, 1`) and `q_n`.
* `System.IsHomDiag.condEntropyCoord_zero_eq_scalar`, `…condEntropyCoord_one_eq_scalar`: the
  scalar Ledrappier–Young formula `q_{x,n} = log #W_n + d_{x,n} log |a_n|`,
  `q_{y,n} = log #W_n + d_{y,n} log |b_n|`.
* `System.condEntropyPoint_le_condEntropyCoord`: conditioning on the planar point gives at least
  as much information as conditioning on one of its coordinates.
* `System.IsHomDiag.condEntropyCoord_one_eq_zero_of_le`, `…condEntropyPoint_eq_zero_of_le`: in
  the case `log #W_n ≤ -log |b_n|`, `q_{y,n} = 0` and `0 ≤ q_n ≤ q_{y,n} = 0`.
* `System.StrongSeparation.condEntropyPoint_eq_zero`: strong separation gives unique coding and
  `q_n = 0`.
* `System.IsHomDiag.dimEntropy_one_eq_condEntropyCoord`,
  `…condEntropy_xiPerp_eq_condEntropyCoord`, `…dimEntropy_two_eq_condEntropyPoint`: the past and
  future of a Bernoulli measure are independent and `V^1` is the vertical axis, so the entropies
  of the planar Ledrappier–Young formula are `h_1 = q_{x,n}` and `h_2 = q_n`.
-/
public import BoxLike.MainTwoProse.OpenSetBranch
public import BoxLike.MainTwoProse.PastIndependence

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

namespace System

variable {κ : Type*} [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- The conditional entropy `q_{c,n}` of the first symbol given the coordinate `c` of the coded
point (`q_{x,n}` for `c = 0`, `q_{y,n}` for `c = 1`, proof of `thm:main2`). -/
noncomputable def condEntropyCoord (T : System κ) (ν : Measure (ℤ → κ)) [IsFiniteMeasure ν]
    (c : ZMod 2) : ℝ :=
  condEntropy ν fun x => {y | coord c (T.proj y) = coord c (T.proj x)}

/-- The conditional entropy `q_n` of the first symbol given the planar coded point (proof of
`thm:main2`). -/
noncomputable def condEntropyPoint (T : System κ) (ν : Measure (ℤ → κ)) [IsFiniteMeasure ν] :
    ℝ :=
  condEntropy ν fun x => {y | T.proj y = T.proj x}

/-- Conditioning on the planar point gives at least as much information as conditioning on one
of its coordinates: `q_n ≤ q_{c,n}` (proof of `thm:main2`). -/
theorem condEntropyPoint_le_condEntropyCoord (T : System κ) (ν : Measure (ℤ → κ))
    [IsProbabilityMeasure ν] (c : ZMod 2) : T.condEntropyPoint ν ≤ T.condEntropyCoord ν c :=
  condEntropy_le_of_subset ν fun x y (hy : T.proj y = T.proj x) => by
    show coord c (T.proj y) = coord c (T.proj x)
    rw [hy]

/-- The coordinate `c` of the coded point is a Borel map of the future. -/
theorem measurable_coord_proj (T : System κ) (c : ZMod 2) :
    Measurable fun x : ℤ → κ => coord c (T.proj x) := by
  obtain ⟨r, M, hS⟩ := T.exists_bounds
  unfold coord
  split_ifs
  · exact measurable_fst.comp hS.measurable_proj
  · exact measurable_snd.comp hS.measurable_proj

/-- Strong separation gives unique coding, so `q_n = 0` (proof of `thm:main2`): the fibre of the
coded point of `𝐢` lies in the cylinder `[i_0]`. -/
theorem StrongSeparation.condEntropyPoint_eq_zero {T : System κ} (hsep : T.StrongSeparation)
    (ν : Measure (ℤ → κ)) [IsFiniteMeasure ν] : T.condEntropyPoint ν = 0 := by
  obtain ⟨r, M, hS⟩ := T.exists_bounds
  exact condEntropy_eq_zero_of_subset_cylinder ν (isMeasurablePartition_fibre hS.measurable_proj)
    fun x y (hy : T.proj y = T.proj x) => hsep.head_eq_of_proj_eq hy

namespace IsHomDiag

variable {T : System κ} {a b : ℝ} (hT : T.IsHomDiag a b)
include hT

/-- `h_1(ν_n) = q_{x,n}` (proof of `thm:main2`): the atom of `ξ_1` fixes the past and the
horizontal coordinate, since `V^1` is the vertical axis, and the past of the Bernoulli measure
is independent of its future. -/
theorem dimEntropy_one_eq_condEntropyCoord [Nonempty κ] (hab : |b| ≤ |a|) :
    T.dimEntropy (uniformBernoulli κ) 1 = T.condEntropyCoord (uniformBernoulli κ) 0 := by
  have hinv := measurePreserving_shift_uniformBernoulli (κ := κ) 1
  unfold dimEntropy condEntropyCoord
  rw [show T.xi (uniformBernoulli κ) 1 =
      fun x => {y | SamePast y x ∧ coord 0 (T.proj y) = coord 0 (T.proj x)} from
    funext (hT.xi_one_eq hab hinv)]
  exact condEntropy_samePast_eq_of_future (uniformMeasure κ) (T.measurable_coord_proj 0)
    fun x y h => by rw [T.proj_congr h]

/-- `H(𝒫 | \widehat{ξ_1^⊥}) = q_{y,n}` (proof of `thm:main2`): the atom of `ξ_1^⊥` fixes the
past and the vertical coordinate, and the past is independent of the future. -/
theorem condEntropy_xiPerp_eq_condEntropyCoord [Nonempty κ] (hab : |b| ≤ |a|) :
    condEntropy (uniformBernoulli κ) (T.xiPerp (uniformBernoulli κ)) =
      T.condEntropyCoord (uniformBernoulli κ) 1 := by
  have hinv := measurePreserving_shift_uniformBernoulli (κ := κ) 1
  unfold condEntropyCoord
  rw [show T.xiPerp (uniformBernoulli κ) =
      fun x => {y | SamePast y x ∧ coord 1 (T.proj y) = coord 1 (T.proj x)} from
    funext (hT.xiPerp_eq hab hinv)]
  exact condEntropy_samePast_eq_of_future (uniformMeasure κ) (T.measurable_coord_proj 1)
    fun x y h => by rw [T.proj_congr h]

/-- `h_2(ν_n) = q_n` (proof of `thm:main2`): the atom of `ξ_2` fixes the past and the planar
point, and the past is independent of the future. -/
theorem dimEntropy_two_eq_condEntropyPoint [Nonempty κ] (hab : |b| ≤ |a|) :
    T.dimEntropy (uniformBernoulli κ) 2 = T.condEntropyPoint (uniformBernoulli κ) := by
  have hinv := measurePreserving_shift_uniformBernoulli (κ := κ) 1
  obtain ⟨r, M, hS⟩ := T.exists_bounds
  unfold dimEntropy condEntropyPoint
  rw [show T.xi (uniformBernoulli κ) 2 = fun x => {y | SamePast y x ∧ T.proj y = T.proj x} from
    funext (hT.xi_two_eq hab hinv)]
  exact condEntropy_samePast_eq_of_future (uniformMeasure κ) hS.measurable_proj
    fun x y h => T.proj_congr h

end IsHomDiag

end System

namespace System.IsHomDiag

variable {κ : Type u} [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ] [Nonempty κ]
  {T : System κ} {a b : ℝ} (hT : T.IsHomDiag a b)
include hT

/-- The scalar Ledrappier–Young formula `q_{x,n} = log #W_n + d_{x,n} log |a_n|` with
`d_{x,n} = min{1, log #W_n / (-log |a_n|)}` (proof of `thm:main2`, citing Feng, Theorems 1.2
and 1.3).
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem condEntropyCoord_zero_eq_scalar (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (hab : |b| ≤ |a|)
    (hfreex : Function.Injective (simWord (fun _ : κ => a) (fun k => T.trans (k, 0)))) :
    T.condEntropyCoord (uniformBernoulli κ) 0 =
      Real.log (Fintype.card κ) - -Real.log |a| *
        min 1 (Real.log (Fintype.card κ) / -Real.log |a|) := by
  rw [← hT.dimEntropy_one_eq_condEntropyCoord hab]
  exact hT.dimEntropy_one_eq_scalar hly hkk hab hfreex

/-- The scalar Ledrappier–Young formula `q_{y,n} = log #W_n + d_{y,n} log |b_n|` with
`d_{y,n} = min{1, log #W_n / (-log |b_n|)}` (proof of `thm:main2`, citing Feng, Theorems 1.2
and 1.3).
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem condEntropyCoord_one_eq_scalar (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (hab : |b| ≤ |a|)
    (hfreey : Function.Injective (simWord (fun _ : κ => b) (fun k => T.trans (k, 1)))) :
    T.condEntropyCoord (uniformBernoulli κ) 1 =
      Real.log (Fintype.card κ) - -Real.log |b| *
        min 1 (Real.log (Fintype.card κ) / -Real.log |b|) := by
  rw [← hT.condEntropy_xiPerp_eq_condEntropyCoord hab]
  exact hT.condEntropy_xiPerp_eq_scalar hly hkk hab hfreey

/-- `q_{y,n} = 0` when `log #W_n ≤ -log |b_n|` (proof of `thm:main2`): then
`d_{y,n} = log #W_n / (-log |b_n|)`.
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem condEntropyCoord_one_eq_zero_of_le (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (hab : |b| ≤ |a|)
    (hfreey : Function.Injective (simWord (fun _ : κ => b) (fun k => T.trans (k, 1))))
    (hH : Real.log (Fintype.card κ) ≤ -Real.log |b|) :
    T.condEntropyCoord (uniformBernoulli κ) 1 = 0 := by
  have hlb : 0 < -Real.log |b| := neg_pos.2 hT.log_abs_b_neg
  rw [hT.condEntropyCoord_one_eq_scalar hly hkk hab hfreey, min_eq_right ((div_le_one hlb).2 hH),
    mul_div_cancel₀ _ hlb.ne', sub_self]

/-- The entropy threshold case of the proof of `thm:main2`: if `log #W_n ≤ -log |b_n|`, then
`0 ≤ q_n ≤ q_{y,n} = 0`, since conditioning on the planar point gives at least as much
information as conditioning on its vertical coordinate.
Depends on: `FengLedrappierYoung`, `KittleKoglerDimension`. -/
theorem condEntropyPoint_eq_zero_of_le (hly : FengLedrappierYoung.{u})
    (hkk : KittleKoglerDimension.{u}) (hab : |b| ≤ |a|)
    (hfreey : Function.Injective (simWord (fun _ : κ => b) (fun k => T.trans (k, 1))))
    (hH : Real.log (Fintype.card κ) ≤ -Real.log |b|) :
    T.condEntropyPoint (uniformBernoulli κ) = 0 := by
  refine le_antisymm ?_ (condEntropy_nonneg _ _)
  calc T.condEntropyPoint (uniformBernoulli κ)
      ≤ T.condEntropyCoord (uniformBernoulli κ) 1 := T.condEntropyPoint_le_condEntropyCoord _ 1
    _ = 0 := hT.condEntropyCoord_one_eq_zero_of_le hly hkk hab hfreey hH

end System.IsHomDiag

end BoxLike
