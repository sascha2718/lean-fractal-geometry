import Mathlib
import FractalGeometry.Dimension.PhiAssouad.Covering
import FractalGeometry.Dimension.PhiAssouad.DimensionFunction
import FractalGeometry.Dimension.PhiAssouad.PlaneRectangles

namespace FractalGeometry.Dimension.PhiAssouad

open Filter Topology Set

open scoped ENNReal

def gridSquare (r : ℝ) (p : ℤ × ℤ) : Set (ℝ × ℝ) :=
  Set.Icc ((p.1 : ℝ) * r) (((p.1 : ℝ) + 1) * r) ×ˢ Set.Icc ((p.2 : ℝ) * r) (((p.2 : ℝ) + 1) * r)

lemma ediam_gridSquare_le (r : ℝ) (p : ℤ × ℤ) :
    Metric.ediam (gridSquare r p) ≤ ENNReal.ofReal r := by
  apply ediam_prod_Icc_le
  · have : ((p.1 : ℝ) + 1) * r - (p.1 : ℝ) * r = r := by ring
    rw [this]
  · have : ((p.2 : ℝ) + 1) * r - (p.2 : ℝ) * r = r := by ring
    rw [this]

theorem coverNum_eball_le (x : ℝ × ℝ) {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    (coverNum r (Metric.eball x (ENNReal.ofReal R)) : ℝ≥0∞) ≤
      ENNReal.ofReal (16 * (R / r) ^ 2) := by
  classical
  have hR0 : 0 < R := lt_of_lt_of_le hr hrR
  set I : Finset (ℤ × ℤ) :=
    Finset.Icc ⌊(x.1 - R) / r⌋ ⌊(x.1 + R) / r⌋ ×ˢ Finset.Icc ⌊(x.2 - R) / r⌋ ⌊(x.2 + R) / r⌋
    with hI
  set C : Set (Set (ℝ × ℝ)) := gridSquare r '' (I : Set (ℤ × ℤ)) with hC
  have hcov : Metric.eball x (ENNReal.ofReal R) ⊆ ⋃₀ C := by
    intro z hz
    rw [Metric.mem_eball, Prod.edist_eq, max_lt_iff, edist_dist, edist_dist,
      ENNReal.ofReal_lt_ofReal_iff hR0, ENNReal.ofReal_lt_ofReal_iff hR0, Real.dist_eq,
      Real.dist_eq] at hz
    obtain ⟨h1, h2⟩ := hz
    obtain ⟨h1a, h1b⟩ := abs_lt.mp h1
    obtain ⟨h2a, h2b⟩ := abs_lt.mp h2
    refine Set.mem_sUnion.mpr ⟨gridSquare r (⌊z.1 / r⌋, ⌊z.2 / r⌋),
      ⟨(⌊z.1 / r⌋, ⌊z.2 / r⌋), ?_, rfl⟩, ?_⟩
    · rw [hI]
      simp only [Finset.coe_product, Finset.coe_Icc, Set.mem_prod, Set.mem_Icc]
      refine ⟨⟨Int.floor_mono ?_, Int.floor_mono ?_⟩, ⟨Int.floor_mono ?_, Int.floor_mono ?_⟩⟩ <;>
        (apply div_le_div_of_nonneg_right _ hr.le; linarith)
    · simp only [gridSquare, Set.mem_prod, Set.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · exact (le_div_iff₀ hr).mp (Int.floor_le _)
      · exact ((div_lt_iff₀ hr).mp (Int.lt_floor_add_one _)).le
      · exact (le_div_iff₀ hr).mp (Int.floor_le _)
      · exact ((div_lt_iff₀ hr).mp (Int.lt_floor_add_one _)).le
  have hdiam : ∀ S ∈ C, Metric.ediam S ≤ ENNReal.ofReal r := by
    rintro S ⟨p, _, rfl⟩
    exact ediam_gridSquare_le r p

  have hline : ∀ u : ℝ, ((Finset.Icc ⌊(u - R) / r⌋ ⌊(u + R) / r⌋).card : ℝ) ≤ 4 * (R / r) := by
    intro u
    rw [Int.card_Icc]
    have h2r : 2 ≤ 2 * (R / r) := by
      have : 1 ≤ R / r := by rw [le_div_iff₀ hr]; linarith
      linarith
    have hdiff : ((u + R) / r) - ((u - R) / r) = 2 * (R / r) := by ring
    rcases le_or_gt 0 (⌊(u + R) / r⌋ + 1 - ⌊(u - R) / r⌋) with h | h
    · have hcast : (((⌊(u + R) / r⌋ + 1 - ⌊(u - R) / r⌋).toNat : ℕ) : ℝ) =
          ((⌊(u + R) / r⌋ : ℝ) + 1 - ⌊(u - R) / r⌋) := by
        have := Int.toNat_of_nonneg h
        have h' : (((⌊(u + R) / r⌋ + 1 - ⌊(u - R) / r⌋).toNat : ℕ) : ℤ) =
            ⌊(u + R) / r⌋ + 1 - ⌊(u - R) / r⌋ := this
        have h'' := congrArg (fun z : ℤ => (z : ℝ)) h'
        simp only [Int.cast_natCast, Int.cast_sub, Int.cast_add, Int.cast_one] at h''
        exact h''
      rw [hcast]
      have hfl1 : (⌊(u + R) / r⌋ : ℝ) ≤ (u + R) / r := Int.floor_le _
      have hfl2 : (u - R) / r < ⌊(u - R) / r⌋ + 1 := Int.lt_floor_add_one _
      linarith
    · rw [Int.toNat_eq_zero.mpr h.le]
      simp only [Nat.cast_zero]
      positivity
  have hcount : (I.card : ℝ) ≤ 16 * (R / r) ^ 2 := by
    rw [hI, Finset.card_product]
    push_cast
    calc ((Finset.Icc ⌊(x.1 - R) / r⌋ ⌊(x.1 + R) / r⌋).card : ℝ) *
          ((Finset.Icc ⌊(x.2 - R) / r⌋ ⌊(x.2 + R) / r⌋).card : ℝ)
        ≤ (4 * (R / r)) * (4 * (R / r)) :=
          mul_le_mul (hline x.1) (hline x.2) (Nat.cast_nonneg _) (by positivity)
      _ = 16 * (R / r) ^ 2 := by ring
  have h1 : coverNum r (Metric.eball x (ENNReal.ofReal R)) ≤ (I.card : ℕ∞) := by
    calc coverNum r (Metric.eball x (ENNReal.ofReal R)) ≤ C.encard :=
          coverNum_le_of_isCover hcov hdiam
      _ ≤ (↑I : Set (ℤ × ℤ)).encard := Set.encard_image_le _ _
      _ = (I.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard I
  calc (coverNum r (Metric.eball x (ENNReal.ofReal R)) : ℝ≥0∞)
      ≤ ((I.card : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_le.mpr h1
    _ = ENNReal.ofReal (I.card : ℝ) := by
        rw [ENat.toENNReal_coe, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (16 * (R / r) ^ 2) := ENNReal.ofReal_le_ofReal hcount

theorem two_mem_assouadExponents (X : Set (ℝ × ℝ)) : (2 : ℝ) ∈ AssouadExponents X := by
  refine ⟨by norm_num, 16, by norm_num, fun R r hr hrR _ x _ => ?_⟩
  calc (coverNum r (X ∩ Metric.eball x (ENNReal.ofReal R)) : ℝ≥0∞)
      ≤ (coverNum r (Metric.eball x (ENNReal.ofReal R)) : ℝ≥0∞) :=
        ENat.toENNReal_le.mpr (coverNum_mono Set.inter_subset_right)
    _ ≤ ENNReal.ofReal (16 * (R / r) ^ 2) := coverNum_eball_le x hr hrR
    _ = ENNReal.ofReal (16 * (R / r) ^ (2 : ℝ)) := by rw [Real.rpow_two]

theorem phiAssouadExponents_nonempty (φ : DimFun) (X : Set (ℝ × ℝ)) :
    (PhiAssouadExponents φ.toFun X).Nonempty :=
  ⟨2, assouadExponents_subset (fun R h0 h1 => φ.pos R ⟨h0, h1⟩) X (two_mem_assouadExponents X)⟩

end FractalGeometry.Dimension.PhiAssouad
