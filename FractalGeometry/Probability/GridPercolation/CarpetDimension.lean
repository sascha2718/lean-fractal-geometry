import FractalGeometry.Probability.GridPercolation.SmallCarpets

namespace FractalGeometry.Probability.GridPercolation

open FractalGeometry.Dimension.PhiAssouad

namespace GridLaw

noncomputable abbrev supportLaw (A : GridLaw) : GridLaw where
  M := A.M
  N := A.N
  hM := A.hM
  hMN := A.hMN
  p i j := if 0 < A.p i j then 1 else 0
  p_nonneg i j := by split_ifs <;> norm_num
  p_le_one i j := by split_ifs <;> norm_num

variable (A : GridLaw)

lemma allowed_supportLaw (a : Fin A.M × Fin A.N) :
    Allowed A.supportLaw a ↔ Allowed A a := by
  by_cases h : 0 < A.p a.1 a.2 <;> simp [Allowed, supportLaw, h]

lemma rect_supportLaw (w : Word A) : rect A.supportLaw w = rect A w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [rect, ih]; rfl

lemma carpet_supportLaw : carpet A.supportLaw = carpet A := by
  simp only [carpet, limitSet, levelSet, deterministic_retained, allowed_supportLaw, rect_supportLaw]

lemma supportLaw_sAdet : A.supportLaw.sAdet = A.sAdet := by
  have hcols : A.supportLaw.cols = A.cols := by
    ext i
    simp only [cols, Finset.mem_filter, Finset.mem_univ, true_and]
    exact exists_congr fun j => A.allowed_supportLaw (i, j)
  have hrows (i : Fin A.M) : A.supportLaw.rows i = A.rows i := by
    ext j
    simp only [rows, Finset.mem_filter, Finset.mem_univ, true_and]
    exact A.allowed_supportLaw (i, j)
  have hAx : A.supportLaw.Ax = A.Ax := congrArg Finset.card hcols
  have hB : A.supportLaw.Bmax = A.Bmax := by
    rw [Bmax_eq_sup, Bmax_eq_sup]
    exact Finset.sup_congr rfl fun i _ => congrArg Finset.card (hrows i)
  unfold sAdet
  rw [hAx, hB]

lemma supportLaw_mean_ge_two {a b : Fin A.M × Fin A.N} (hab : a ≠ b)
    (ha : Allowed A a) (hb : Allowed A b) : 2 ≤ A.supportLaw.m := by
  classical
  have hsum : A.supportLaw.m = ∑ c : Fin A.M × Fin A.N, A.supportLaw.p c.1 c.2 := by
    rw [Fintype.sum_prod_type']
    rfl
  rw [hsum]
  calc
    (2 : ℝ) = ∑ c ∈ ({a, b} : Finset (Fin A.M × Fin A.N)), A.supportLaw.p c.1 c.2 := by
      rw [Finset.sum_pair hab]
      norm_num [supportLaw, show 0 < A.p a.1 a.2 from ha, show 0 < A.p b.1 b.2 from hb]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun _ _ _ => A.supportLaw.p_nonneg _ _

end GridLaw

/-- Mackay's dimension formula for the deterministic support of any finite grid law. -/
theorem mackay_carpet_dimension (A : GridLaw) : dimA (carpet A) = A.sAdet := by
  by_cases h2 : ∃ a b, a ≠ b ∧ Allowed A a ∧ Allowed A b
  · obtain ⟨a, b, hab, ha, hb⟩ := h2
    have hm : 1 < A.supportLaw.m := one_lt_two.trans_le (A.supportLaw_mean_ge_two hab ha hb)
    rw [← A.carpet_supportLaw, ← A.supportLaw_sAdet]
    exact carpet_dimA hm
  · have h : ∀ a b, Allowed A a → Allowed A b → a = b :=
      fun a b ha hb => by_contra fun hab => h2 ⟨a, b, hab, ha, hb⟩
    rw [dimA_eq_zero_of_subsingleton (carpet_subsingleton h), A.sAdet_eq_zero h]

end FractalGeometry.Probability.GridPercolation
