module

/-
The paragraph after the proof of `prop:ssc_no_overlap_not_pesc` (tex lines 1447 to 1450): the
example satisfies the hypotheses of `thm:main2`, so `\dim_H X = dimaff(X)` although the projective
exponential separation condition fails. The example is that of `prop_ssc_no_overlap_not_pesc`,
along the proof of the article, with the theorem of Bárány and Käenmäki discharged
(`NoOverlap.prop_ssc_no_overlap_not_pesc_holds`).

* `NoOverlap.dimH_eq_dimaff_aligned`: the statement of `NoOverlap.dimH_eq_dimaff`, with no
  hypothesis besides those of `thm:main2`.
-/
public import BoxLike.BaranyKaenmaki
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.MainTwoFree

@[expose] public section

namespace BoxLike

/-- The example of `prop:ssc_no_overlap_not_pesc` satisfies the hypotheses of `thm:main2` and
`\dim_H X = dimaff(X)` (tex lines 1447 to 1450): it satisfies the strong separation condition,
hence the strong open set condition, its projective system has no exact overlaps, it fails the
projective exponential separation condition, and `dimaff(X) < 2` since `∑_i |det A_i| < 1`.
The theorem of Bárány and Käenmäki is discharged (`NoOverlap.prop_ssc_no_overlap_not_pesc_holds`);
the hypotheses are those of `thm:main2`. -/
theorem NoOverlap.dimH_eq_dimaff_aligned
    (hms : MorrisShmerkinLyapunov.{0}) (hfk : EquilibriumGibbsStatement.{0})
    (hfjj : FraserJordanJurgaDecomposition.{0}) (hfib : FengInfoSumBar.{0})
    (hly : FengLedrappierYoung.{0}) (hlyb : FengLedrappierYoungBar.{0})
    (hkk : KittleKoglerDimension.{0}) :
    ∃ S : System (Fin 4), S.StrongSeparation ∧ S.NoExactOverlaps ∧ ¬ S.ProjExpSeparation ∧
      S.dimaff < 2 ∧ dimH S.attractor = ENNReal.ofReal S.dimaff := by
  obtain ⟨S, ho, hprox, -, -, -, -, hsep, hfree, hpesc, hdet⟩ :=
    NoOverlap.prop_ssc_no_overlap_not_pesc_holds
  have hrot : S.WithRotations := ⟨⟨0, by rw [ho]; rfl⟩, ⟨3, by rw [ho]; rfl⟩⟩
  have hfree' : S.NoExactOverlaps := S.noExactOverlaps_iff.2 hfree
  have h2 := S.dimaff_lt_two_of_sum_abs_det_lt_one hdet
  obtain ⟨μ, hprob, hinv, heq⟩ := S.exists_isEquilibriumState S.dimaff_nonneg
  exact ⟨S, hsep, hfree', hpesc, h2, S.main2_noExactOverlaps hms hfk hfjj hfib hly hlyb hkk hrot
    hprox hfree' h2 μ hinv heq (Or.inr hsep.strongOpenSet)⟩

end BoxLike
