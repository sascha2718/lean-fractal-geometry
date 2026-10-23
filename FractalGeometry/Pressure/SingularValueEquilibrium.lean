import Mathlib
import FractalGeometry.Ergodic.Birkhoff
import FractalGeometry.Ergodic.Kingman
import FractalGeometry.LinearCocycles.Pressure
import FractalGeometry.LinearCocycles.Products
import FractalGeometry.LinearCocycles.SingularValue
import FractalGeometry.Pressure.SingularValueBlocks
import FractalGeometry.Pressure.SingularValueStatement
import FractalGeometry.Pressure.SingularValueVariational
import FractalGeometry.Symbolic.Entropy
import FractalGeometry.Symbolic.FutureWords
import FractalGeometry.Symbolic.GibbsEntropy
import FractalGeometry.Symbolic.InvariantProbability
import FractalGeometry.Symbolic.Shift
import FractalGeometry.Symbolic.WordAverages

open FractalGeometry.Ergodic

namespace FractalGeometry

open Filter MeasureTheory Topology ProbabilityTheory

open scoped ENNReal Matrix.Norms.L2Operator

namespace MatrixTuple

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {A : ι → Matrix (Fin 2) (Fin 2) ℝ} {s : ℝ}

theorem energyLim_le_blockEnergy_div (hA : ∀ i, (A i).det ≠ 0) (hs : 0 ≤ s)
    {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ)
    {m : ℕ} (hm : m ≠ 0) : energyLim A s μ ≤ blockEnergy A s μ m / m := by
  obtain ⟨c, hc⟩ := exists_le_log_svf_word hA hs
  have hsub := subadditive_integral_futureWord hμ (G := fun w => Real.log (svf s (word A w)))
    (log_svf_word_append_le hA hs)
  have hbdd : BddBelow (Set.range fun n : ℕ =>
      (∫ x, Real.log (svf s (word A (futureWord x n))) ∂μ) / n) := by
    refine ⟨min 0 c, ?_⟩
    rintro _ ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact (min_le_right _ _).trans (le_integral_futureWord_div hc hn)
  rw [tendsto_nhds_unique (tendsto_energyLim hA hμ hs) (hsub.tendsto_lim hbdd),
    blockEnergy_eq_integral]
  exact hsub.lim_le_div hbdd hm

theorem isEquilibriumState_iff_forall (hA : ∀ i, (A i).det ≠ 0) (hs : 0 ≤ s)
    {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ) :
    IsEquilibriumState A s μ ↔
      ∀ m : ℕ, 0 < m → m * pressure A s ≤ blockEntropy μ m + blockEnergy A s μ m := by
  constructor
  · intro heq m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have h1 := entropy_le_blockEntropy_div hμ hm.ne'
    have h2 := energyLim_le_blockEnergy_div hA hs hμ hm.ne'
    have hP : pressure A s = entropy μ + energyLim A s μ := heq
    calc (m : ℝ) * pressure A s = m * (entropy μ + energyLim A s μ) := by rw [hP]
      _ ≤ m * (blockEntropy μ m / m + blockEnergy A s μ m / m) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) hm'.le
      _ = blockEntropy μ m + blockEnergy A s μ m := by field_simp
  · intro h
    refine le_antisymm ?_ (entropy_add_energyLim_le_pressure hA hμ hs)
    have hlim := (tendsto_entropy hμ).add (tendsto_energyLim hA hμ hs)
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_gt_atTop 0] with m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    rw [← blockEnergy_eq_integral μ m, ← add_div, le_div_iff₀ hm', mul_comm]
    exact h m hm

end MatrixTuple

end FractalGeometry
