module

/-
`KittleKoglerDimension` from the Lean formalisation of Kittle–Kogler, arXiv:2610.10511, by its
authors, the library `ExactOverlaps` in `vendor/`: its `theorem_1_1` (lower Hausdorff dimension
`min{1, h/|χ|}`), `hasExactDimension_lowerHausdorffDimension` (exact-dimensionality) and
`randomWalkEntropyRate_eq_of_noExactOverlaps` (`h = H(p)` without exact overlaps).

* `KittleKogler.system`: the weighted system of the source library with the data `r`, `t`, `p`.
* `KittleKogler.wordList`, `KittleKogler.system_wordMap_apply`, `KittleKogler.wordList_injective`,
  `KittleKogler.system_hasNoExactOverlaps`: words as lists; injectivity of `simWord r t` is the
  freeness condition of the source library.
* `KittleKogler.system_isStationary`, `KittleKogler.system_lyapunov`: stationarity and `χ`.
* `kittleKoglerDimension_holds`: the statement.
-/
public import BoxLike.Literature
public import ExactOverlaps.MainTheorem.Theorem11
public import ExactOverlaps.SelfSimilar.DimensionIdentification
public import ExactOverlaps.SelfSimilar.NoExactOverlaps

@[expose] public section

namespace BoxLike

open MeasureTheory
open scoped ENNReal NNReal

universe u

namespace KittleKogler

variable {κ : Type u}

/-- The letters of a word of the source library, first letter first. -/
def wordList : (n : ℕ) → ExactOverlaps.SelfSimilar.Word κ n → List κ
  | 0, _ => []
  | n + 1, w => w.1 :: wordList n w.2

/-- The word of the source library with the given letters. -/
def listWord : List κ → Σ n : ℕ, ExactOverlaps.SelfSimilar.Word κ n
  | [] => ⟨0, PUnit.unit⟩
  | a :: l => ⟨(listWord l).1 + 1, (a, (listWord l).2)⟩

/-- The letters of a word determine the word together with its length. -/
theorem listWord_wordList : ∀ (n : ℕ) (w : ExactOverlaps.SelfSimilar.Word κ n),
    listWord (wordList n w) = ⟨n, w⟩
  | 0, _ => rfl
  | n + 1, w => by
    rw [wordList, listWord, listWord_wordList n w.2]
    rfl

/-- Distinct words of the source library, of any lengths, have distinct lists of letters. -/
theorem wordList_injective :
    Function.Injective
      (fun w : Σ n : ℕ, ExactOverlaps.SelfSimilar.Word κ n => wordList w.1 w.2) :=
  Function.LeftInverse.injective (g := listWord) fun w => listWord_wordList w.1 w.2

variable [Fintype κ] (r t p : κ → ℝ) (hr : ∀ j, r j ≠ 0) (hr1 : ∀ j, |r j| < 1)
  (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1)

/-- The weighted system of the source library with the ratios `r`, the translations `t` and the
weights `p`. -/
def system : ExactOverlaps.SelfSimilar.System κ where
  map j := ⟨r j, hr j, t j⟩
  contracting := hr1
  weight j := Real.toNNReal (p j)
  weight_sum := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sum, NNReal.coe_one, ← hsum]
    exact Finset.sum_congr rfl fun i _ => Real.coe_toNNReal _ (hp i)

/-- The weights of the system are `p`. -/
theorem system_weight_coe (j : κ) : (((system r t p hr hr1 hp hsum).weight j : ℝ≥0) : ℝ) = p j :=
  Real.coe_toNNReal _ (hp j)

/-- The composed similarity of a word is `simWord r t` of its letters. -/
theorem system_wordMap_apply : ∀ (n : ℕ) (w : ExactOverlaps.SelfSimilar.Word κ n) (x : ℝ),
    (system r t p hr hr1 hp hsum).wordMap n w x = simWord r t (wordList n w) x
  | 0, _, x => by simp [wordList]
  | n + 1, w, x => by
    rw [wordList, ExactOverlaps.SelfSimilar.System.wordMap_succ,
      ExactOverlaps.RealSimilarity.comp_apply, system_wordMap_apply n w.2 x, simWord_cons,
      Function.comp_apply]
    rfl

/-- Injectivity of `simWord r t` on lists is the freeness condition of the source library. -/
theorem system_hasNoExactOverlaps (hfree : Function.Injective (simWord r t)) :
    (system r t p hr hr1 hp hsum).HasNoExactOverlaps := by
  intro v w h
  dsimp only at h
  apply wordList_injective
  dsimp only
  apply hfree
  funext x
  rw [← system_wordMap_apply r t p hr hr1 hp hsum v.1 v.2 x,
    ← system_wordMap_apply r t p hr hr1 hp hsum w.1 w.2 x, h]

/-- The stationarity equation of `KittleKoglerDimension` is that of the source library. -/
theorem system_isStationary (ν : Measure ℝ)
    (hν : ν = ∑ j, ENNReal.ofReal (p j) • ν.map (fun x => r j * x + t j)) :
    (system r t p hr hr1 hp hsum).IsStationary ν :=
  hν

/-- The Lyapunov exponent of the system is `χ = ∑_j p_j log |r_j|`. -/
theorem system_lyapunov :
    (system r t p hr hr1 hp hsum).lyapunov = ∑ j, p j * Real.log |r j| :=
  Finset.sum_congr rfl fun j _ => by rw [system_weight_coe]; rfl

end KittleKogler

/-- `KittleKoglerDimension`, the input of the proof of `thm:main2`, from Theorem 1.1 of the source
library: the lower Hausdorff dimension of the stationary measure is `min{1, h / |χ|}`, the measure
is exact-dimensional of this dimension, and without exact overlaps the entropy rate `h` is
`H(p)`. -/
theorem kittleKoglerDimension_holds : KittleKoglerDimension.{u} := by
  intro κ _ r t p hr hr1 hp hsum hfree ν _ hν
  have hp' : ∀ j, 0 ≤ p j := fun j => (hp j).le
  have hstat := KittleKogler.system_isStationary r t p hr hr1 hp' hsum ν hν
  have hdim :=
    (KittleKogler.system r t p hr hr1 hp' hsum).hasExactDimension_lowerHausdorffDimension ν hstat
  have hformula : (ExactOverlaps.lowerHausdorffDimension ν).toReal =
      min 1 ((KittleKogler.system r t p hr hr1 hp' hsum).randomWalkEntropyRate /
        |(KittleKogler.system r t p hr hr1 hp' hsum).lyapunov|) :=
    (KittleKogler.system r t p hr hr1 hp' hsum).theorem_1_1 ⟨ν, inferInstance⟩ hstat
  rw [ExactOverlaps.SelfSimilar.System.randomWalkEntropyRate_eq_of_noExactOverlaps _
      (KittleKogler.system_hasNoExactOverlaps r t p hr hr1 hp' hsum hfree),
    ExactOverlaps.SelfSimilar.System.alphabetEntropy_eq_sum,
    ExactOverlaps.SelfSimilar.System.abs_lyapunov_eq_neg, KittleKogler.system_lyapunov] at hformula
  simp only [KittleKogler.system_weight_coe] at hformula
  rw [hformula] at hdim
  exact hdim

end BoxLike
