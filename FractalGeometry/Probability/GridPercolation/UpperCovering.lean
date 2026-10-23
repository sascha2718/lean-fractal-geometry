import FractalGeometry.Probability.GridPercolation.SquareFirstMoment

namespace FractalGeometry.Probability.GridPercolation

open FractalGeometry.Dimension.PhiAssouad
open scoped ENNReal

variable {A : GridLaw} {Ω : Type*}
  {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

theorem coverNum_le_squareCount (ω : Ω) (a : ℕ) :
    coverNum (gridScale A.M a) (limitSet X ω) ≤
      (A.N : ℕ∞) * squareCount X (bfloor A.Gamma a) (a - bfloor A.Gamma a) ω := by
  classical
  let b := bfloor A.Gamma a
  let L := a - b
  let T := (retainedDigitWords X b ω).sigma
    (fun u => activeColumns X (wordOfDigits u) L ω)
  let I := T ×ˢ Finset.range A.N
  let C : Set (Set (ℝ × ℝ)) :=
    (fun p : ((u : DigitWord A b) × ColumnWord A L) × ℕ =>
      (splitCode a p.1.1 p.1.2).slice p.2) '' (I : Set _)
  have hcov : limitSet X ω ⊆ ⋃₀ C := by
    intro z hzF
    have hzlevel : z ∈ levelSet X ω a := Set.mem_iInter.mp hzF a
    simp only [levelSet, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hzlevel
    obtain ⟨w, ⟨hwlen, hwret⟩, hzw⟩ := hzlevel
    have hb : b ≤ w.length := hwlen ▸ A.bfloor_le a
    obtain ⟨u, hu⟩ := exists_wordOfDigits_eq_of_length
      (show (w.take b).length = b by simp [List.length_take, Nat.min_eq_left hb])
    obtain ⟨v, r, hvr⟩ := exists_wordOfCoordinates_eq_of_length
      (show (w.drop b).length = L by simp [L, hwlen])
    have hw : wordOfDigits u ++ wordOfCoordinates v r = w := by
      rw [hu, hvr, List.take_append_drop]
    have hret : RetainedBelow X ω [] (wordOfDigits u) ∧
        RetainedBelow X ω (wordOfDigits u) (wordOfCoordinates v r) := by
      have h := (retained_iff_retainedBelow_nil X ω w).mp hwret
      rw [← hw, retainedBelow_append_iff] at h
      simpa using h
    have huT : u ∈ retainedDigitWords X b ω := mem_retainedDigitWords.mpr hret.1
    have hvT : v ∈ activeColumns X (wordOfDigits u) L ω := by
      simp only [activeColumns, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [tubePopulationBelow, Finset.card_pos]
      exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hret.2⟩⟩
    have hzc : z ∈ (splitCode a u v).region := by
      apply rect_subset_region_of_memCell (memCell_splitCode a u v r)
      rwa [hw]
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp (region_subset_iUnion_slice _ hzc)
    exact ⟨(splitCode a u v).slice i,
      ⟨(⟨u, v⟩, i), Finset.mem_coe.mpr
        (Finset.mem_product.mpr ⟨Finset.mem_sigma.mpr ⟨huT, hvT⟩, hi⟩), rfl⟩, hzi⟩
  have hdiam : ∀ S ∈ C, Metric.ediam S ≤ ENNReal.ofReal (gridScale A.M a) := by
    rintro S ⟨p, -, rfl⟩
    rw [gridScale_eq_inv_pow]
    exact ediam_slice_le _ _
  have hcard : T.card = squareCount X b L ω := by
    rw [Finset.card_sigma]
    rfl
  calc
    coverNum (gridScale A.M a) (limitSet X ω) ≤ C.encard :=
      coverNum_le_of_isCover hcov hdiam
    _ ≤ (I : Set (((u : DigitWord A b) × ColumnWord A L) × ℕ)).encard :=
      Set.encard_image_le _ _
    _ = (I.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard I
    _ = (A.N : ℕ∞) * squareCount X b L ω := by
      rw [Finset.card_product, Finset.card_range, hcard]
      norm_cast
      exact Nat.mul_comm _ _

theorem card_limitMeetingCodes_le_squareCount (ω : Ω) (a : ℕ) :
    (limitMeetingCodes X ω a).card ≤
      25 * A.N * squareCount X (bfloor A.Gamma a) (a - bfloor A.Gamma a) ω := by
  have h : ((limitMeetingCodes X ω a).card : ℕ∞) ≤
      ((25 * A.N * squareCount X (bfloor A.Gamma a) (a - bfloor A.Gamma a) ω : ℕ) : ℕ∞) := by
    calc
      _ ≤ (25 : ℕ∞) * coverNum (gridScale A.M a) (limitSet X ω) :=
        card_limitMeetingCodes_le_coverNum ω a
      _ ≤ 25 * ((A.N : ℕ∞) * squareCount X (bfloor A.Gamma a) (a - bfloor A.Gamma a) ω) := by
        gcongr
        exact coverNum_le_squareCount ω a
      _ = _ := by push_cast; rw [mul_assoc]
  exact_mod_cast h

end FractalGeometry.Probability.GridPercolation
