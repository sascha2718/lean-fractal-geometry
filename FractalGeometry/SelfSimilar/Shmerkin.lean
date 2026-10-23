import Mathlib
import FractalGeometry.Entropy.Lq.Basic
import FractalGeometry.Entropy.Lq.InverseTheorem
import FractalGeometry.Entropy.Lq.Main
import FractalGeometry.Entropy.Lq.Statement

/-!
Pablo Shmerkin, "On Furstenberg's intersection conjecture, self-similar measures,
and the L^q norms of convolutions", Annals of Mathematics 189(2) (2019), 319–391.
DOI: 10.4007/annals.2019.189.2.1; numbering follows arXiv:1609.07802v3.

Theorem 6.6, lower-bound consequence: for exponentially separated similarities
on the real line, positive probability weights, and `q > 1`, the q-mass sum of
any finite collection of level-M dyadic intervals is eventually bounded by
`2^(-M*(q-1)*α)` whenever `α < 1` and `∑ p_i^q |r_i|^(-(q-1)*α) < 1`.

The combinatorial proof uses an existential doubling exponent in the weak
Bourgain lemma. It does not prove Theorem 3.1 with its printed quantitative
exponent, the Furstenberg intersection theorem, or the full L^q-dimension equality.
-/

namespace FractalGeometry

universe u

theorem shmerkinLqDimension_holds : ShmerkinLqDimension.{u} :=
  shmerkinLqDimension_of_proposition68 fun _ _ _ _ h => Lq.proposition68 h

end FractalGeometry
