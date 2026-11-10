import FractalGeometry.Rapaport.Analytic.EntropyIncrease
import FractalGeometry.Hochman.Main

/-!
# Theorem 3.1 of Rapaport without hypotheses

Theorem 3.1 of A. Rapaport, *Dimension of self-conformal measures associated to an exponentially
separated analytic IFS on ℝ*, arXiv:2412.16753v2, for every system satisfying
`AnalyticESC.RapaportHyp`: `entropyIncreasePoly` with Hochman's entropy growth theorem
(M. Hochman, *On self-similar sets with overlaps and inverse theorems for entropy*, Ann. of Math.
180 (2014), Theorem 2.8) supplied by `FractalGeometry.Hochman.hochmanEntropyGrowth`.

## Main declarations

* `entropyIncreasePoly_of_rapaportHyp`: `EntropyIncreasePoly φ p hp`.
-/

namespace FractalGeometry.Rapaport.Analytic

/-- Theorem 3.1 of Rapaport (arXiv:2412.16753v2) for the self-conformal measure of a system
satisfying `AnalyticESC.RapaportHyp`. -/
theorem entropyIncreasePoly_of_rapaportHyp {N : ℕ} [NeZero N] {φ : Fin N → ℝ → ℝ}
    (hφ : AnalyticESC.RapaportHyp φ) {p : Fin N → ℝ} (hp : AnalyticESC.IsProbVec p) :
    EntropyIncreasePoly φ p hp :=
  entropyIncreasePoly FractalGeometry.Hochman.hochmanEntropyGrowth hφ hp

end FractalGeometry.Rapaport.Analytic
