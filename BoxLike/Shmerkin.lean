module

/-
`ShmerkinLqDimension`, the lower bound of Theorem 6.6 of Shmerkin, Ann. of Math. (2) 189 (2019),
arXiv:1609.07802v3, proved along the source in `BoxLike/Shmerkin/`:

* `Basic`, `Section4`, `Prop413`, `Limit`, `TauTilde`, `Prop68`, `Main`: Sections 4 and 6.4.
* `Statements`: Theorems 2.1, 3.1, 3.2 and 5.1 as `Prop`s. `Theorem51`, `Flattening`: Theorem 5.1
  from Theorem 2.1 (Section 5), and its line form.
* `BSG/`, `BSG`: Theorem 3.2, the asymmetric Balog–Szemerédi–Gowers theorem (`theorem32`).
* `Bourgain/`: Theorem 3.1 in the weak form `Bourgain.theorem31Weak`, with some doubling exponent
  `ε(T) > 0` in place of `2^{-2T-1}`, from Hochman's saturation theorem of `ExactOverlaps` along
  Shmerkin, arXiv:2308.09846, Theorem 1.5. The source's form `Theorem31` is not proved.
* `Inverse/`: Theorem 2.1 from Theorems 3.1 and 3.2 along Section 3. The weak form suffices,
  since the exponent of Theorem 3.2 is chosen after `D`.
* `InverseTheorem`: `inverseTheorem`, `proposition68`.

Deviations, inside proofs: the closed middle half in Theorem 2.1; Lemma 3.6 loses `(2(D+1))^{-ℓ}`;
sumsets pass from `ZMod (2^m)` to `ℤ` at a factor `2`; Corollary 3.10 rescales to
`(⌊ℓ/D⌋ + 1) D²`; (vi) of Theorem 2.1 holds with the threshold `δ`; Theorem 5.1 on the circle is
for measures carried by `[3/8, 5/8]`.
-/
public import BoxLike.Shmerkin.Main

@[expose] public section

namespace BoxLike

universe u

/-- The lower bound of Shmerkin's Theorem 6.6. -/
theorem shmerkinLqDimension_holds : ShmerkinLqDimension.{u} :=
  shmerkinLqDimension_of_proposition68 fun _ _ _ _ h => Shmerkin.proposition68 h

end BoxLike
