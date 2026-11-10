module

public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.MainTwoFree
public import BoxLike.DimensionFormula

@[expose] public section

/-!
The full parameter range of `thm:main2`. Below two this uses the manuscript's finite
diagonal subsystems. At and above two the threshold alternative is impossible and
the strong open set condition forces affinity dimension two by the determinant sum.
-/

namespace BoxLike.System

open MeasureTheory

universe u

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) [Nonempty ι]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The determinant argument in the proof of `thm:main_extended`, also used at the
endpoint of `thm:main2`: under SOSC, affinity dimension at least two equals two. -/
theorem StrongOpenSet.dimaff_eq_two (h : S.StrongOpenSet) (h2 : 2 ≤ S.dimaff) :
    S.dimaff = 2 := by
  have hsum := (h.sum_abs_det_eq_one S h2 S.pressure_dimaff).2
  apply S.dimaff_eq zero_le_two
  rw [S.pressure_of_two_le le_rfl]
  simpa using congrArg Real.log hsum

/-- `thm:main2` without an extra `dimaff < 2` assumption. The seven hypotheses on statements
are used only in the finite-subsystem branch below two; `FengLedrappierYoung` is a cited
theorem, and the library proves the other six, `KittleKoglerDimension` from the Lean
formalisation of Kittle–Kogler by its authors (`kittleKoglerDimension_holds`) and
`FengLedrappierYoungBar` from `FengLedrappierYoung`
(`fengLedrappierYoungBar_of_fengLedrappierYoung`). -/
theorem main2_noExactOverlaps_all (hms : BoxLike.MorrisShmerkinLyapunov.{u})
    (hfk : BoxLike.EquilibriumGibbsStatement.{u})
    (hfjj : BoxLike.FraserJordanJurgaDecomposition.{u})
    (hfib : BoxLike.FengInfoSumBar.{u}) (hly : BoxLike.FengLedrappierYoung.{u})
    (hlyb : BoxLike.FengLedrappierYoungBar.{u}) (hkk : BoxLike.KittleKoglerDimension.{u})
    (hrot : S.WithRotations) (hprox : S.Proximal) (hfree : S.NoExactOverlaps)
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ]
    (hinv : MeasurePreserving (BoxLike.shift 1) μ μ)
    (heq : S.IsEquilibriumState S.dimaff μ)
    (hor : S.dimaff ≤ 2 - S.lyapunov₁ μ / S.lyapunov₂ μ ∨ S.StrongOpenSet) :
    dimH S.attractor = ENNReal.ofReal S.dimaff := by
  rcases lt_or_ge S.dimaff 2 with h2 | h2
  · exact S.main2_noExactOverlaps hms hfk hfjj hfib hly hlyb hkk hrot hprox hfree h2 μ
      hinv heq hor
  · have h1neg := S.lyapunov₁_neg hinv
    have h2neg := (S.lyapunov₂_le_lyapunov₁ hinv).trans_lt h1neg
    have hratio : 0 < S.lyapunov₁ μ / S.lyapunov₂ μ := div_pos_of_neg_of_neg h1neg h2neg
    have hsosc : S.StrongOpenSet := hor.resolve_left (by linarith)
    rw [S.dimH_attractor_of_two_le hsosc h2, hsosc.dimaff_eq_two S h2]
    norm_num

end BoxLike.System
