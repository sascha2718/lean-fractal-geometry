import FractalGeometry.SelfConformal.Bernoulli
import FractalGeometry.SelfConformal.Coding
import FractalGeometry.SelfConformal.Complexification
import FractalGeometry.SelfConformal.CutSet
import FractalGeometry.SelfConformal.Distortion
import FractalGeometry.SelfConformal.Fibre
import FractalGeometry.SelfConformal.Lyapunov

/-!
# Toolkit for analytic iterated function systems on the line

Entry point importing the basic facts used in the formalisation of A. Rapaport, *Dimension of
self-conformal measures associated to an exponentially separated analytic IFS on ℝ*,
arXiv:2412.16753v2, Section 2: the one-sided Bernoulli shift (`Bernoulli`), the coding map, the
attractor and the self-conformal measure (`Coding`), bounded distortion, Lemma 2.1(1)
(`Distortion`), the cut-sets `Ψ_n` with (2.7) and (2.8) (`CutSet`), the complexification of the
system, Lemma 2.1(2) and Taylor's theorem (`Complexification`), the fibres of the coding map
(`Fibre`) and the Lyapunov exponent with the almost sure limit (2.6) (`Lyapunov`).
-/
