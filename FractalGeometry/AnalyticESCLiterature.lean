import FractalGeometry.Bowen.Main
import FractalGeometry.Hochman.Main
import FractalGeometry.SelfConformal.FengHu.Main
import FractalGeometry.Rapaport.Analytic.EntropyIncrease
import FractalGeometry.Rapaport.Analytic.Main.RapaportMeasure
import FractalGeometry.Rapaport.Attractor.Corollary

/-!
# The literature hypotheses of `AnalyticESC`, proved

The library `AnalyticESC` (Bárány, Kolossváry and Troscheit, *On exponential separation of
analytic self-conformal sets on the real line*, arXiv:2509.07888) takes three cited results as
explicit hypotheses, the `Prop`-valued definitions `AnalyticESC.BowenGibbsStatement`,
`AnalyticESC.RapaportMeasureStatement` and `AnalyticESC.RapaportSetStatement` of
`AnalyticESC/Dimension/Defs.lean`. This module proves all three from Mathlib and the libraries
of this repository, with only the axioms `propext`, `Classical.choice` and `Quot.sound`.

* `bowenGibbsStatement`: R. Bowen, *Equilibrium states and the ergodic theory of Anosov
  diffeomorphisms*, LNM 470 (1975), Theorem 1.4, for the one-sided full shift
  (`FractalGeometry.Bowen`).
* `rapaportMeasureStatement`: A. Rapaport, *Dimension of self-conformal measures associated to an
  exponentially separated analytic IFS on ℝ*, arXiv:2412.16753v2, Theorem 1.2, with the exact
  dimensionality and fibre entropy formula of D.-J. Feng and H. Hu, *Dimension theory of iterated
  function systems*, CPAM 62 (2009), Theorem 2.8 and Proposition 4.10
  (`FractalGeometry.SelfConformal.FengHu`), and the entropy growth theorem of M. Hochman,
  *On self-similar sets with overlaps and inverse theorems for entropy*, Ann. of Math. 180 (2014),
  Theorem 2.8 (`FractalGeometry.Hochman`); Rapaport's Sections 3 and 4 are
  `FractalGeometry.Rapaport.Analytic`.
* `rapaportSetStatement`: Rapaport, Corollary 1.3 (`FractalGeometry.Rapaport.Attractor`).
-/

namespace FractalGeometry

/-- Bowen's theorem on the one-sided full shift: `AnalyticESC.BowenGibbsStatement`. -/
theorem bowenGibbsStatement : AnalyticESC.BowenGibbsStatement :=
  FractalGeometry.Bowen.bowenGibbsStatement_holds

/-- Rapaport's Theorem 1.2 with Feng–Hu exact dimensionality:
`AnalyticESC.RapaportMeasureStatement`. -/
theorem rapaportMeasureStatement : AnalyticESC.RapaportMeasureStatement :=
  FractalGeometry.Rapaport.Analytic.rapaportMeasure
    (fun _ hφ _ hp => FractalGeometry.Rapaport.Analytic.entropyIncreasePoly
      FractalGeometry.Hochman.hochmanEntropyGrowth hφ hp)
    (fun _ hφ _ hp => FractalGeometry.SelfConformal.FengHu.fengHuInterface_holds hφ hp)

/-- Rapaport's Corollary 1.3: `AnalyticESC.RapaportSetStatement`. -/
theorem rapaportSetStatement : AnalyticESC.RapaportSetStatement :=
  FractalGeometry.Rapaport.Attractor.rapaportSet_of_measure rapaportMeasureStatement
    bowenGibbsStatement

end FractalGeometry
