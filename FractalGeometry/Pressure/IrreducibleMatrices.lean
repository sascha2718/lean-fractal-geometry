import Mathlib
import FractalGeometry.LinearCocycles.Classification
import FractalGeometry.LinearCocycles.Products
import FractalGeometry.Pressure.QuasiMultiplicative

namespace FractalGeometry

open Filter Topology

open scoped Matrix Matrix.Norms.L2Operator

theorem eq_smul_of_mulVec_eq_zero {B : Matrix (Fin 2) (Fin 2) ℝ} (hB : B ≠ 0)
    {w y : Fin 2 → ℝ} (hw : w ≠ 0) (hBw : B *ᵥ w = 0) (hBy : B *ᵥ y = 0) :
    ∃ d : ℝ, y = d • w := by
  refine exists_eq_smul_of_det_colMat_eq_zero hw ?_
  by_contra hdet
  apply hB
  have h0 : B * colMat w y = 0 := by
    rw [mul_colMat, hBw, hBy]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [colMat]
  calc B = B * colMat w y * (colMat w y)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet),
          Matrix.mul_one]
    _ = 0 := by rw [h0, Matrix.zero_mul]

namespace MatrixTuple

variable {ι : Type*} {A : ι → Matrix (Fin 2) (Fin 2) ℝ}

theorem not_tupleIrreducible_of_mul_eq_zero {B C : Matrix (Fin 2) (Fin 2) ℝ} (hB : B ≠ 0)
    (hC : C ≠ 0) (hBC : B * C = 0) (hBAC : ∀ i, B * A i * C = 0) : ¬ TupleIrreducible A := by
  intro hirr
  obtain ⟨x, hx⟩ : ∃ x : Fin 2 → ℝ, C *ᵥ x ≠ 0 := by
    by_contra h
    push Not at h
    apply hC
    ext i j
    simpa [Matrix.mulVec_single] using congrFun (h (Pi.single j 1)) i
  refine hirr ⟨C *ᵥ x, hx, fun i => ?_⟩
  exact eq_smul_of_mulVec_eq_zero hB hx (by rw [Matrix.mulVec_mulVec, hBC, Matrix.zero_mulVec])
    (by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBAC i, Matrix.zero_mulVec])

theorem exists_pos_le_norm_mul_word_mul (hirr : TupleIrreducible A) :
    ∃ c : ℝ, 0 < c ∧ ∀ B C : Matrix (Fin 2) (Fin 2) ℝ, ‖B‖ = 1 → ‖C‖ = 1 →
      ∃ k : List ι, k.length ≤ 1 ∧ c ≤ ‖B * word A k * C‖ := by
  by_contra hne
  push Not at hne
  choose B C hB hC hk using fun n : ℕ => hne (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
  have hK : IsCompact (Metric.sphere (0 : Matrix (Fin 2) (Fin 2) ℝ) 1 ×ˢ
      Metric.sphere (0 : Matrix (Fin 2) (Fin 2) ℝ) 1) :=
    (isCompact_sphere 0 1).prod (isCompact_sphere 0 1)
  obtain ⟨⟨B₀, C₀⟩, ⟨hB₀, hC₀⟩, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := fun n => (B n, C n))
    fun n => ⟨by simp [hB n], by simp [hC n]⟩
  have hlimB : Tendsto (fun n => B (φ n)) atTop (𝓝 B₀) := (continuous_fst.tendsto _).comp hlim
  have hlimC : Tendsto (fun n => C (φ n)) atTop (𝓝 C₀) := (continuous_snd.tendsto _).comp hlim
  have hzero : ∀ k : List ι, k.length ≤ 1 → B₀ * word A k * C₀ = 0 := by
    intro k hk1
    have h1 : Tendsto (fun n => ‖B (φ n) * word A k * C (φ n)‖) atTop
        (𝓝 ‖B₀ * word A k * C₀‖) := ((hlimB.mul tendsto_const_nhds).mul hlimC).norm
    have h2 : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    exact norm_le_zero_iff.1 (le_of_tendsto_of_tendsto' h1 h2 fun n => (hk (φ n) k hk1).le)
  have hB0 : B₀ ≠ 0 := by
    rintro rfl
    simp at hB₀
  have hC0 : C₀ ≠ 0 := by
    rintro rfl
    simp at hC₀
  refine not_tupleIrreducible_of_mul_eq_zero hB0 hC0 ?_ (fun i => ?_) hirr
  · simpa using hzero [] (by simp)
  · simpa [word] using hzero [i] (by simp)

theorem normQuasiMultiplicative_of_tupleIrreducible (hirr : TupleIrreducible A) :
    ∃ c : ℝ, 0 < c ∧ ∀ u v : List ι, ∃ k : List ι, k.length ≤ 1 ∧
      c * (‖word A u‖ * ‖word A v‖) ≤ ‖word A (u ++ k ++ v)‖ := by
  obtain ⟨c, hc, h⟩ := exists_pos_le_norm_mul_word_mul hirr
  refine ⟨c, hc, fun u v => ?_⟩
  rcases (norm_nonneg (word A u)).eq_or_lt with hu | hu
  · exact ⟨[], by simp, by rw [← hu]; simp⟩
  rcases (norm_nonneg (word A v)).eq_or_lt with hv | hv
  · exact ⟨[], by simp, by rw [← hv]; simp⟩
  have hn : ∀ M : Matrix (Fin 2) (Fin 2) ℝ, 0 < ‖M‖ → ‖‖M‖⁻¹ • M‖ = 1 := fun M hM => by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hM.ne']
  obtain ⟨k, hk, hck⟩ := h _ _ (hn _ hu) (hn _ hv)
  refine ⟨k, hk, ?_⟩
  have e : ‖word A u‖⁻¹ • word A u * word A k * ‖word A v‖⁻¹ • word A v =
      (‖word A u‖⁻¹ * ‖word A v‖⁻¹) • word A (u ++ k ++ v) := by
    rw [word_append, word_append, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at hck
  calc c * (‖word A u‖ * ‖word A v‖)
      ≤ ‖word A u‖⁻¹ * ‖word A v‖⁻¹ * ‖word A (u ++ k ++ v)‖ * (‖word A u‖ * ‖word A v‖) :=
        mul_le_mul_of_nonneg_right hck (by positivity)
    _ = ‖word A (u ++ k ++ v)‖ := by field_simp

theorem normQuasiMultiplicative_of_irreducible (hirr : TupleIrreducible A) :
    NormQuasiMultiplicative A := by
  obtain ⟨c, hc, h⟩ := normQuasiMultiplicative_of_tupleIrreducible hirr
  exact ⟨1, c, hc, h⟩

end MatrixTuple

end FractalGeometry
