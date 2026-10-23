import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Probability.GridPercolation.ApproxSquares
import FractalGeometry.Probability.GridPercolation.Floor
import FractalGeometry.Probability.GridPercolation.GridCoveringReduction
import FractalGeometry.Probability.GridPercolation.Law
import FractalGeometry.Probability.GridPercolation.LowerCovering
import FractalGeometry.Probability.GridPercolation.Process

open FractalGeometry.Dimension.PhiAssouad

namespace FractalGeometry.Probability.GridPercolation

open Filter Topology

open scoped ENNReal

variable {A : GridLaw} {Ω : Type*}
  {X : Word A → (Fin A.M × Fin A.N) → Ω → Bool}

noncomputable def limitMeetingCodes (X : Word A → (Fin A.M × Fin A.N) → Ω → Bool)
    (ω : Ω) (a : ℕ) : Finset (SquareCode A a) := by
  classical
  exact Finset.univ.filter fun c => (c.region ∩ limitSet X ω).Nonempty

@[simp] lemma mem_limitMeetingCodes {ω : Ω} {a : ℕ} {c : SquareCode A a} :
    c ∈ limitMeetingCodes X ω a ↔ (c.region ∩ limitSet X ω).Nonempty := by
  simp [limitMeetingCodes]

theorem card_limitMeetingCodes_le_coverNum (ω : Ω) (a : ℕ) :
    ((limitMeetingCodes X ω a).card : ℕ∞) ≤
      (25 : ℕ∞) * coverNum (gridScale A.M a) (limitSet X ω) := by
  have h := card_le_mul_coverNum (A := A) 1 (limitMeetingCodes X ω a)
    (fun c hc => mem_limitMeetingCodes.mp hc) (r := gridScale A.M a) (by
      rw [gridScale_eq_inv_pow]
      norm_num)
  norm_num at h ⊢
  exact h

theorem coverNum_le_mul_card_limitMeetingCodes (ω : Ω) (a : ℕ) :
    coverNum (gridScale A.M a) (limitSet X ω) ≤
      (A.N : ℕ∞) * (limitMeetingCodes X ω a).card := by
  classical
  set T : Finset (SquareCode A a) := limitMeetingCodes X ω a with hT
  set I : Finset (SquareCode A a × ℕ) := T ×ˢ Finset.range A.N with hI
  set C : Set (Set (ℝ × ℝ)) :=
    (fun p : SquareCode A a × ℕ => p.1.slice p.2) '' (I : Set (SquareCode A a × ℕ)) with hC
  have hcov : limitSet X ω ⊆ ⋃₀ C := by
    intro z hzF
    have hzlevel : z ∈ levelSet X ω a := Set.mem_iInter.mp hzF a
    simp only [levelSet, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hzlevel
    obtain ⟨w, ⟨hwlen, hwret⟩, hzw⟩ := hzlevel
    set c : SquareCode A a := wordCode w hwlen with hc
    have hmem : c.MemCell w := memCell_wordCode w hwlen
    have hzc : z ∈ c.region := rect_subset_region_of_memCell hmem hzw
    have hcT : c ∈ T := by
      rw [hT, mem_limitMeetingCodes]
      exact ⟨z, hzc, hzF⟩
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp (region_subset_iUnion_slice c hzc)
    exact ⟨c.slice i,
      ⟨(c, i), Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hcT, hi⟩), rfl⟩, hzi⟩
  have hdiam : ∀ S ∈ C, Metric.ediam S ≤ ENNReal.ofReal (gridScale A.M a) := by
    rintro S ⟨p, -, rfl⟩
    rw [gridScale_eq_inv_pow]
    exact ediam_slice_le p.1 p.2
  calc
    coverNum (gridScale A.M a) (limitSet X ω) ≤ C.encard :=
      coverNum_le_of_isCover hcov hdiam
    _ ≤ (I : Set (SquareCode A a × ℕ)).encard := Set.encard_image_le _ _
    _ = (I.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard I
    _ = (A.N : ℕ∞) * T.card := by
      rw [hI, Finset.card_product, Finset.card_range]
      exact_mod_cast Nat.mul_comm T.card A.N
    _ = (A.N : ℕ∞) * (limitMeetingCodes X ω a).card := by rw [hT]

theorem limitMeetingCodes_nonempty_of_limitSet_nonempty {ω : Ω}
    (hF : (limitSet X ω).Nonempty) (a : ℕ) : (limitMeetingCodes X ω a).Nonempty := by
  classical
  obtain ⟨z, hzF⟩ := hF
  have hzlevel : z ∈ levelSet X ω a := Set.mem_iInter.mp hzF a
  simp only [levelSet, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hzlevel
  obtain ⟨w, ⟨hwlen, hwret⟩, hzw⟩ := hzlevel
  let c : SquareCode A a := wordCode w hwlen
  refine ⟨c, mem_limitMeetingCodes.mpr ?_⟩
  exact ⟨z, rect_subset_region_of_memCell (memCell_wordCode w hwlen) hzw, hzF⟩

end FractalGeometry.Probability.GridPercolation
