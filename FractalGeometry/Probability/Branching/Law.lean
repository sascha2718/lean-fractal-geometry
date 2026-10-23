import Mathlib

namespace FractalGeometry.Probability.Branching

/-- Independent retention probabilities for finitely many labelled child positions. -/
structure Law where
  arity : ℕ
  arity_pos : 0 < arity
  p : Fin arity → ℝ
  p_nonneg : ∀ i, 0 ≤ p i
  p_le_one : ∀ i, p i ≤ 1

def Law.m (A : Law) : ℝ := ∑ i, A.p i

theorem Law.m_nonneg (A : Law) : 0 ≤ A.m :=
  Finset.sum_nonneg fun i _ => A.p_nonneg i

end FractalGeometry.Probability.Branching
