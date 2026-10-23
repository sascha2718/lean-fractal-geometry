import FractalGeometry.Probability.Patterns.Defs

namespace FractalGeometry.Probability.Patterns

theorem Weights.sum_wordProb {ι : Type*} [Fintype ι] (p : Weights ι) (n : ℕ) :
    ∑ w : Word ι n, p.wordProb w = 1 := by
  unfold Weights.wordProb
  rw [← Fintype.prod_sum]
  simp [p.sum_eq_one]

end FractalGeometry.Probability.Patterns
