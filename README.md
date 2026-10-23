# FractalGeometry

A Lean 4 library of reusable results in fractal geometry, geometric measure theory,
dimension theory, iterated function systems, entropy, ergodic theory and probability.
Mathlib is its only external Lake dependency.

**Find a result:** [by subject](#result-index) ·
[by paper, author or theorem number](#paper-and-literature-index) ·
[module index](docs/modules.md) · [build and reuse](#build-checks-and-downstream-use).
Full paper titles, authors, publication details, DOI/arXiv identifiers, result numbers,
Lean names and scope qualifications are written directly in this README, so that a
search engine can index the correspondence without reading any other file.

```lean
import FractalGeometry.Ergodic

#check FractalGeometry.Ergodic.birkhoff_ergodic
#check FractalGeometry.Ergodic.kingman_ergodic
```

```lean
import FractalGeometry.ExactOverlaps

#check ExactOverlaps.SelfSimilar.System.theorem_1_1
```

`import FractalGeometry.All` imports the whole collection. `import FractalGeometry`
retains the smaller self-similar library. Individual modules provide smaller imports,
for example `GeometricMeasureTheory.Hausdorff.Frostman` or
`FractalGeometry.Entropy.Finite`. The [source manifest](provenance/sources.json)
records public source revisions and file hashes.

## Subject imports and structure

| Import | Contents |
|---|---|
| [`FractalGeometry.Dimension`](FractalGeometry/Dimension.lean) | Hausdorff, box, packing and Assouad dimensions; coverings and logarithmic covering limits |
| [`FractalGeometry.Measures`](FractalGeometry/Measures.lean) | Frostman and Ahlfors regularity, covering theorems, densities and rectifiability |
| [`FractalGeometry.SelfSimilar`](FractalGeometry/SelfSimilar.lean) | Hutchinson, homometry, Feng–Hu exact dimensionality, Shmerkin L^q bounds and Jordan–Rapaport dimension on the line |
| [`FractalGeometry.SelfAffine`](FractalGeometry/SelfAffine.lean) | Planar affine systems; Falconer's affinity bound, Fraser's box dimension, Mackay's carpet Assouad dimension and Feng's Ledrappier–Young formula |
| [`FractalGeometry.ExactOverlaps`](FractalGeometry/ExactOverlaps.lean) | Kittle–Kogler Theorem 1.1 and its 554-module proof dependency closure |
| [`FractalGeometry.SelfConformal`](FractalGeometry/SelfConformal.lean) | Analytic systems, separation, conjugacy, cookie cutters and quasi-self-similarity |
| [`FractalGeometry.Pressure`](FractalGeometry/Pressure.lean) | Pressure, Gibbs measures, planar matrix classification and quasi-subadditive limits |
| [`FractalGeometry.Ergodic`](FractalGeometry/Ergodic.lean) | Birkhoff, Kingman, Shannon–McMillan–Breiman, Kolmogorov–Sinai, planar Furstenberg–Kesten and Oseledets |
| [`FractalGeometry.Entropy`](FractalGeometry/Entropy.lean) | Finite Shannon entropy, conditional entropy, entropy rates and generator identity |
| [`FractalGeometry.Random`](FractalGeometry/Random.lean) | Branching processes, random self-affine box dimension, projection growth and finite-pattern waiting times |
| [`FractalGeometry.Renewal`](FractalGeometry/Renewal.lean) | Renewal tools and finite self-similar laws |
| [`FractalGeometry.Applications.BrownianImages`](FractalGeometry/Applications/BrownianImages.lean) | Correlation profiles, image-law separation and Minkowski reconstruction |

General tools sit below the systems and applications that use them. The source
collections keep their established namespaces. Distinct system definitions are not
implicitly identified: `FractalGeometry.System` uses positive ratios on `[0,1]`,
whereas `BrownianImages.System` also permits orientation reversal. Do not require
two separate packages exporting the same module names in one Lake workspace.

## Result index

The linked Lean declarations specify all hypotheses. A named literature statement
parameter is a hypothesis even when a proof uses only standard axioms.

### Dimensions, measures and covering

These results use the `GeometricMeasureTheory` namespace unless indicated otherwise.
Their numbered source is [Troscheit's geometric measure theory notes (GMT2026)](#ref-gmt2026).

| Result | Declaration(s) | Module |
|---|---|---|
| Hausdorff content, measure and their critical exponent | `hausdorffContentGauge`, `hausdorffMeasureGauge` and the comparison API | [Hausdorff.Basic](GeometricMeasureTheory/Hausdorff/Basic.lean) |
| Mass distribution principles, including general gauges | Gauge and power-law mass bounds | [GeneralGauges](GeometricMeasureTheory/Hausdorff/GeneralGauges.lean), [Computing](GeometricMeasureTheory/Hausdorff/Computing.lean) |
| Frostman's lemma for compact sets in finite-dimensional real normed spaces | `frostman_compact`, `frostman_compact_iff`, `frostman_dimension` | [Frostman](GeometricMeasureTheory/Hausdorff/Frostman.lean) |
| Symmetric Cantor sets and their Hausdorff dimensions | Cantor-set construction, measures and dimension formulae | [CantorSets](GeometricMeasureTheory/Hausdorff/CantorSets.lean) |
| Finite max-flow/min-cut on rooted trees | Flow and cut bounds used in Frostman's lemma | [FlowsAndCuts](GeometricMeasureTheory/Hausdorff/FlowsAndCuts.lean) |
| Finite Vitali and `5r` covering lemmas | Finite and countable selection results | [VitaliLemmas](GeometricMeasureTheory/Covering/VitaliLemmas.lean) |
| Vitali theorems for Hausdorff and Radon measures | Fine-cover selection and density comparison | [HausdorffVitali](GeometricMeasureTheory/Covering/HausdorffVitali.lean), [RadonVitali](GeometricMeasureTheory/Covering/RadonVitali.lean) |
| Ahlfors regular sets have the stated Hausdorff dimension | `ahlfors_hausdorff` | [AhlforsRegular](GeometricMeasureTheory/Covering/AhlforsRegular.lean) |
| Rectifiable/purely unrectifiable decomposition and density of Lipschitz curves | `rectifiable_decomposition`, `lipschitz_curve_density` | [Rectifiability](GeometricMeasureTheory/Covering/Rectifiability.lean) |
| Noninteger density theorem in the range `0 < s < 1` | `noninteger_density_of_lt_one` | [NonintegerDensity](GeometricMeasureTheory/Covering/NonintegerDensity.lean) |
| Box dimensions, Lipschitz invariance and scale comparisons | `upperBoxDim`, `lowerBoxDim` and their comparison API | [BoxDimension](GeometricMeasureTheory/Box/BoxDimension.lean) |
| Packing measure and packing dimension as modified upper box dimension | Packing and countable-cover characterisations | [PackingMeasure](GeometricMeasureTheory/Box/PackingMeasure.lean), [ModifiedBox](GeometricMeasureTheory/Box/ModifiedBox.lean) |
| Assouad dimension, doubling and weak tangents | Two-scale covering estimates and tangent bounds | [Basic](GeometricMeasureTheory/Assouad/Basic.lean), [Doubling](GeometricMeasureTheory/Assouad/Doubling.lean), [WeakTangents](GeometricMeasureTheory/Assouad/WeakTangents.lean) |
| Dimension comparisons and equality on Ahlfors regular sets | `dimension_comparison`, `ahlfors_dimensions` | [Comparison](GeometricMeasureTheory/Assouad/Comparison.lean), [AhlforsDimensions](GeometricMeasureTheory/Assouad/AhlforsDimensions.lean) |
| Local dimensions and upper regularity dimension of measures | Local mass and regularity comparisons | [MeasureDimensions](GeometricMeasureTheory/Assouad/MeasureDimensions.lean) |

`density_rectifiability` in [Rectifiability](GeometricMeasureTheory/Covering/Rectifiability.lean)
retains the explicit `BesicovitchLowerDensityBound` hypothesis. The general noninteger-density
theorem above dimension one, pure unrectifiability of the four-corner dust, a full-dimension
weak-tangent existence theorem, and the projection theorems are not claimed here.

The standard logarithmic quotient `log N(r) / (-log r)` converges to a finite
box dimension for a nonempty totally bounded set whose lower and upper dimensions
agree: `FractalGeometry.Dimension.tendsto_coveringExponent_of_boxDim_eq` in
[Dimension.LogLimit](FractalGeometry/Dimension/LogLimit.lean). This uses the
`GeometricMeasureTheory` box dimensions from [GMT2026, Definition 4.3](#ref-gmt2026).

For bounded planar sets, upper box dimension is at most φ-Assouad dimension:
`FractalGeometry.Dimension.PhiAssouad.upperBoxDim_le_dimAphi` in
[BoxComparison](FractalGeometry/Dimension/PhiAssouad/BoxComparison.lean), a specialisation
of [Banaji–Rutar–Troscheit 2025, Corollary 2.7](#ref-brt2025). This namespace uses
diameter covering counts and a real-valued logarithmic definition of box dimension.

### Self-similar sets, natural measures and homometry

| Result | Declaration(s) | Module |
|---|---|---|
| Unique attractor and natural measure on `[0,1]` | `FractalGeometry.System.exists_unique_isNatural` | [Hutchinson](FractalGeometry/Hutchinson.lean) |
| Uniqueness of a self-similar probability measure | `FractalGeometry.Hutchinson.eq_of_selfSimilar` | [Hutchinson](FractalGeometry/Hutchinson.lean) |
| Ahlfors regularity under strong separation | `FractalGeometry.exists_isAhlforsClosed` | [AhlforsRegular](FractalGeometry/AhlforsRegular.lean) |
| Frostman bound at every centre | `FractalGeometry.AhlforsRegular.exists_isFrostman_of_isNatural` | [AhlforsRegular](FractalGeometry/AhlforsRegular.lean) |
| Atomlessness and continuous pair-distance profiles | `FractalGeometry.IsFrostman.measure_singleton`, `FractalGeometry.continuous_phi` | [Regularity](FractalGeometry/Regularity.lean) |
| Cantor, homogeneous and paired systems; arithmetic classification | `cantorSystem_isDimension`, `pairSystem_nonArithmetic_iff` in `FractalGeometry` | [System](FractalGeometry/System.lean) |
| Distinct self-similar measures with identical pair-distance distributions | `FractalGeometry.homometric_example` | [HomometricMeasures](FractalGeometry/HomometricMeasures.lean) |
| Hutchinson's theorem allowing orientation reversal | `BrownianImages.System.exists_unique_isNatural` | [Hutchinson](BrownianImages/Hutchinson.lean) |
| Open set condition implies strong open set condition on the line (Schief) | `OpenSetCondition.strongOpenSetCondition` | [Schief](BrownianImages/Schief.lean) |
| Stopping-cylinder multiplicity and Ahlfors regularity under OSC | `IsFeasible.exists_multiplicity_bound`, `OpenSetCondition.exists_isAhlforsClosed` | [StoppingGeometry](BrownianImages/StoppingGeometry.lean) |

Literature: [Hutchinson1981](#ref-hutchinson1981), [Schief1994](#ref-schief1994);
the homometric construction is Proposition 8.2 of [Troscheit2026](#ref-troscheit2026).
The last three rows use the `BrownianImages` system. They can be imported directly without
importing its Brownian-process applications.

### Exact overlaps and self-similar measure dimension

[Kittle–Kogler, Theorem 1.1](#ref-kittlekogler2026) proves that the lower Hausdorff
dimension of a stationary measure for a finite real similarity system is
`min 1 (randomWalkEntropyRate / |lyapunov|)`. Signed contractions and zero listed
weights are permitted. The declarations are
`ExactOverlaps.SelfSimilar.System.theorem_1_1` and `theorem_1_1_ennreal` in
[MainTheorem.Theorem11](vendor/ExactOverlaps/MainTheorem/Theorem11.lean).

### Exact dimensionality without separation

**Proved self-similar-line specialisation of [Feng–Hu 2009, Theorem 2.8](#ref-fenghu2009):**
`FractalGeometry.SelfSimilar.FengHu.Coding.exists_isExactDim` in
[SelfSimilar.FengHu](FractalGeometry/SelfSimilar/FengHu.lean) states that the image of an
ergodic invariant probability measure under a bounded finite self-similar coding on
ℝ is exact-dimensional. The similarity ratios may have either sign and satisfy
`0 < |c_i| ≤ r < 1`. No separation condition is imposed. The theorem proves existence
of a constant almost-everywhere local dimension; the equality with projection
entropy divided by the Lyapunov exponent is not part of this endpoint.

### Self-similar L^q dimension under exponential separation

`FractalGeometry.shmerkinLqDimension_holds` proves the lower-bound consequence of
[Shmerkin 2019, Theorem 6.6](#ref-shmerkin2019), expressed as eventual dyadic
q-mass bounds for self-similar probability measures on ℝ. Both signs of the
nonzero contraction ratios are allowed. See
[SelfSimilar.Shmerkin](FractalGeometry/SelfSimilar/Shmerkin.lean).

### Ergodic self-similar measure dimension under exponential separation

`FractalGeometry.jordanRapaportDimension_holds` proves
[Jordan–Rapaport 2021, Theorem 1.1](#ref-jordanrapaport2021) for a finite similarity
IFS on ℝ: every ergodic invariant symbolic probability measure projects to an
exact-dimensional measure of dimension `min(1, entropy / |Lyapunov exponent|)`.
The ratios may have either sign. See
[Line.JordanRapaport](FractalGeometry/SelfSimilar/Line/JordanRapaport.lean).

### Planar affine dimension bound

**Proved planar specialisation of [Falconer 1988, Theorem 5.4, upper-bound part](#ref-falconer1988):**
for every finite nonempty family of invertible contracting affine maps on ℝ²,
`dim_H K ≤ upperBoxDim K ≤ min(2, affinityDim)` without a separation assumption.
`FractalGeometry.AffineIFS.upperBoxDim_attractor_le` and
`FractalGeometry.AffineIFS.dimH_attractor_le` are in
[SelfAffine.Falconer](FractalGeometry/SelfAffine/Falconer.lean).
The affinity dimension is the zero of singular-value pressure. The almost-everywhere
translation equality from the paper is not claimed.

### Rectangular self-affine box and packing dimensions

[Fraser 2012, Theorem 2.3](#ref-fraser2012) is proved for finite planar affine systems
with diagonal or anti-diagonal contracting linear parts. Packing dimension equals
upper box dimension, which is bounded above by the zero of modified singular-value
pressure. Under the rectangular open set condition, packing, lower box and upper
box dimensions all equal this zero. The endpoints are
`FractalGeometry.RectangularIFS.fraserBound_holds` and
`FractalGeometry.RectangularIFS.fraserROSC_holds` in
[Rectangular.Fraser](FractalGeometry/SelfAffine/Rectangular/Fraser.lean).

### Assouad dimension of Bedford–McMullen carpets

`FractalGeometry.BedfordMcMullen.System.mackay_dimension` proves
[Mackay 2011, Theorem 1.1](#ref-mackay2011) for a finite digit set in an
`M × N` grid with `2 ≤ M < N`: `dim_A K = log c / log M + log b / log N`,
where `c` counts nonempty columns and `b` is the largest number of digits in one
column. See [SelfAffine.BedfordMcMullen](FractalGeometry/SelfAffine/BedfordMcMullen.lean).

### Planar affine measure dimension

`FractalGeometry.planarFengLedrappierYoung_holds` proves exact dimensionality and
the formula `(h₁ − h₀)/λ₁ + (h₂ − h₁)/λ₂` for a projected ergodic invariant
probability measure of a finite invertible contracting planar affine system with
`λ₂ < λ₁`. Here `hᵢ` are conditional entropies along the Oseledets filtration.
See [SelfAffine.FengLedrappierYoung](FractalGeometry/SelfAffine/FengLedrappierYoung.lean)
and [Feng 2023, Theorems 1.2(ii) and 1.3](#ref-feng2023).

### Planar matrix classification

`FractalGeometry.tuple_classification` gives the strongly irreducible,
simultaneously monomial and simultaneously triangular alternatives for invertible
planar matrix families containing a proximal product. See
[LinearCocycles.Classification](FractalGeometry/LinearCocycles/Classification.lean)
and [Bárány–Käenmäki–Yu, Lemma 2.7](#ref-bky2026).

### Gibbs decomposition for positive rectangular systems

`FractalGeometry.fraserJordanJurgaDecomposition_holds` gives the two Gibbs components
and Lyapunov integral identities for positive diagonal/anti-diagonal systems at
`0 < s < 2`. See [Fraser–Jordan–Jurga 2020](#ref-fraserjordanjurga2020) for the exact
hypotheses and the parts of the published statements covered.

### Distinct Lyapunov exponents for rectangular equilibrium states

`FractalGeometry.morrisShmerkinLyapunov_holds` proves `λ₂ < λ₁` for a singular-value
equilibrium state at `0 < s < 2` of a finite contractive diagonal/anti-diagonal
matrix family with both orientations and a proximal diagonal generator.
This is a specialisation of [Morris–Shmerkin 2019, Theorem 3.1](#ref-morrisshmerkin2019);
see [Rectangular.MorrisShmerkin](FractalGeometry/Pressure/Rectangular/MorrisShmerkin.lean).

### Analytic and conformal systems

Paper: [Bárány–Kolossváry–Troscheit (BKT2025), arXiv:2509.07888v3](#ref-bkt2025).
Cookie cutters and quasi-self-similarity follow [GMT2026](#ref-gmt2026).

| Result | Declaration(s) | Module |
|---|---|---|
| Generic strong exponential separation in the relative `C²` topology | `AnalyticESC.theorem_1_4` | [Generic.OpenDense](AnalyticESC/Generic/OpenDense.lean) |
| Dual separation criterion and condensation dichotomy | `AnalyticESC.IFS.theorem_2_2`, `condensation_dichotomy`, `theorem_1_5` | [Main.Dichotomy](AnalyticESC/Main/Dichotomy.lean) |
| Explicit distortion criterion for strong exponential separation (`N ≥ 2`) | `AnalyticESC.IFS.proposition_1_8` | [Main.Criterion](AnalyticESC/Main/Criterion.lean) |
| Koenigs linearisation and conjugacy characterisations | `koenigs_comp`, `AnalyticESC.IFS.theorem_1_12_similarity` | [Koenigs](AnalyticESC/Conjugation/Koenigs.lean), [Characterisation](AnalyticESC/Conjugation/Characterisation.lean) |
| Polynomial and non-polynomial examples; local-dimension and `L^q` bounds | Example and local-mass estimates | [Example](AnalyticESC/Main/Example.lean), [NonPolynomialExample](AnalyticESC/Main/NonPolynomialExample.lean), [Lq](AnalyticESC/Dimension/Lq.lean) |
| Dimension consequences from Rapaport's theorem | `AnalyticESC.IFS.theorem_1_6` — **explicit literature hypotheses** | [Dimension.Rapaport](AnalyticESC/Dimension/Rapaport.lean) |
| Cookie-cutter bounded distortion and cylinder/ball comparisons | `CookieCutter.bounded_distortion` | [BoundedDistortion](GeometricMeasureTheory/CookieCutter/BoundedDistortion.lean) |
| Cookie-cutter dimension is the zero of pressure | `CookieCutter.cookie_cutter_dimension` | [Pressure.Dimension](GeometricMeasureTheory/Pressure/Dimension.lean) |
| Quasi-self-similar measure/content comparability and regularity | `qss_measure_content`, `qss_isAhlforsRegularSet_iff` | [Homogeneity](GeometricMeasureTheory/QuasiSelfSimilar/Homogeneity.lean) |

`AnalyticESC` retains `BowenGibbsStatement`, `RapaportMeasureStatement` and
`RapaportSetStatement` where required. They are explicit hypotheses, not axioms and not
silently discharged by similarly named theorems from another model. Its Corollary 1.7
covers `N ≥ 2`.
Full citations and the precise conditional inputs: [Bowen1975](#ref-bowen1975),
[Rapaport2024](#ref-rapaport2024), [FengHu2009](#ref-fenghu2009).


### Pressure, finite entropy and ergodic theory

| Result | Declaration | Module and source |
|---|---|---|
| Maximal and pointwise ergodic theorems | `FractalGeometry.Ergodic.maximal_ergodic`, `birkhoff_ae`, `birkhoff_ergodic` | [Birkhoff](FractalGeometry/Ergodic/Birkhoff.lean); [Birkhoff1931](#ref-birkhoff1931) |
| Subadditive ergodic theorem, including a possible negative-infinity limit | `FractalGeometry.Ergodic.kingman_ae`, `kingman_ergodic`, `kingman_ergodic_of_tendsto` | [Kingman](FractalGeometry/Ergodic/Kingman.lean); [Kingman1968](#ref-kingman1968) |
| Shannon–McMillan–Breiman for finite alphabets, including the invariant-measure local-entropy limit | `FractalGeometry.shannonMcMillanBreiman`, `tendsto_neg_log_cylinder_localEntropy` | [ShannonMcMillanBreiman](FractalGeometry/Ergodic/ShannonMcMillanBreiman.lean); [Breiman1957](#ref-breiman1957) |
| Kolmogorov–Sinai generator identity for the coordinate partition | `FractalGeometry.ksEntropy_shift_eq_entropy`, `tendsto_neg_log_cylinder_ksEntropy` | [KolmogorovSinai](FractalGeometry/Ergodic/KolmogorovSinai.lean); [Bowen1975, Chapter 2](#ref-bowen1975) |
| Conditional measures: disintegration, uniqueness and concentration on partition atoms | `FractalGeometry.condMeas`, `setLIntegral_lintegral_condMeas`, `condMeas_unique`, `condMeas_atom` | [Disintegration](FractalGeometry/Symbolic/Disintegration.lean); [Einsiedler–Ward 2011, Theorem 5.14](#ref-einsiedlerward2011) |
| Conditioning inside conditional measures along a finer measurable partition | `FractalGeometry.double_conditional` | [Conditioning](FractalGeometry/Symbolic/Conditioning.lean); [Einsiedler–Ward 2011, Proposition 5.20](#ref-einsiedlerward2011) |
| Almost-sure logarithmic growth of products of invertible planar matrices | `FractalGeometry.MatrixTuple.tendsto_log_norm_pastProd`, `tendsto_log_alpha₂_pastProd` | [FurstenbergKesten](FractalGeometry/Ergodic/FurstenbergKesten.lean); [FurstenbergKesten1960](#ref-furstenbergkesten1960) |
| Measurable invariant planar filtration when the Lyapunov exponents are distinct | `FractalGeometry.MatrixTuple.ae_mem_regularSet`, `nonempty_oseledetsSet_of_ergodic` | [Oseledets](FractalGeometry/Ergodic/Oseledets.lean); [Oseledec1968](#ref-oseledec1968) |
| Finite-map entropy loss is at most the log of the largest fibre | `FractalGeometry.Entropy.entropy_loss_le_log_fibre` | [Finite entropy](FractalGeometry/Entropy/Finite.lean); elementary Shannon-entropy inequality, proved directly |
| Entropy of a subprobability mass with finite support | `FractalGeometry.Entropy.entropy_sum_le_mass_log_card` | [Finite entropy](FractalGeometry/Entropy/Finite.lean) |
| Quasi-subadditive limits | `GeometricMeasureTheory.quasi_subadditive_limit` | [Subadditive](GeometricMeasureTheory/Pressure/Subadditive.lean); [GMT2026](#ref-gmt2026) |
| Pressure and Gibbs measure for cookie cutters | `GeometricMeasureTheory.CookieCutter.pressure_gibbs` | [Gibbs](GeometricMeasureTheory/Pressure/Gibbs.lean); [GMT2026](#ref-gmt2026) |
| Unique ergodic norm-equilibrium state with Gibbs bounds for irreducible invertible planar matrix families | `FractalGeometry.MatrixTuple.exists_unique_normEquilibrium`, `FractalGeometry.fengKaenmakiNormEquilibrium_holds` | [FengKaenmaki](FractalGeometry/Pressure/FengKaenmaki.lean); [FengKaenmaki2011, Proposition 1.2, existence/Gibbs/uniqueness parts](#ref-fengkaenmaki2011) |

### Random self-affine box dimension

`FractalGeometry.Probability.GridPercolation.gatzourasLalley_boxDimension`
proves the Gatzouras–Lalley box-dimension formula for independent Bernoulli
retention on a rectangular grid, almost surely on survival when mean offspring
exceeds one. `gatzourasLalley_boxCoverRate` proves convergence of the logarithmic
covering quotient at all small scales. See
[GridPercolation.GatzourasLalley](FractalGeometry/Probability/GridPercolation/GatzourasLalley.lean)
and [Gatzouras–Lalley 1994, Theorem 4.1](#ref-gatzouraslalley1994).

For the same model, `gatzourasLalley_projectionGrowth` proves that the logarithm
of the number of occupied columns at generation `n`, divided by `n`, converges
almost surely on survival to `log λ`. This is
[Proposition 3.5 of the author version](#ref-gatzouraslalley1994); see
[GridPercolation.ProjectionGrowth](FractalGeometry/Probability/GridPercolation/ProjectionGrowth.lean).

### Borel–Cantelli for branching trees

`FractalGeometry.Probability.Branching.treeSecondBorelCantelli_of_isPercolation`
proves the finite Bernoulli-child specialisation of
[Banaji–Rutar–Troscheit 2025, Lemma 1.6(ii)](#ref-brt2025): if nonnegative summable
weights `K_n` satisfy `∑ K_n P(E_n) m^n = ∞`, then almost surely on survival there
are infinitely many levels with a retained vertex whose subtree satisfies `E_n`.
See [Branching.BorelCantelli](FractalGeometry/Probability/Branching/BorelCantelli.lean).

### Finite-pattern waiting times

For an i.i.d. process on a finite alphabet with positive symbol probabilities,
`FractalGeometry.Probability.Patterns.IsIIDProcess.li_identity` proves the
correlation identity for the expected first occurrence of a finite family of
patterns of a common positive length. `sum_hitProb` proves that the winning-pattern
probabilities sum to one. See [Patterns.Li](FractalGeometry/Probability/Patterns/Li.lean)
and [Li1980](#ref-li1980).

### Branching processes and tree laws

Source: [Athreya–Troscheit](#ref-at2026); classical foundations:
[Athreya–Ney and Harris](#ref-branching-classics).

| Result | Declaration | Module |
|---|---|---|
| Extinction probability equals the probability of extinction | `BranchingProcess.sampleMeasure_not_survives` | [Law](BranchingProcess/Law.lean) |
| Reduced skeleton and conjugate dying-tree laws | `skeletonTreeLaw_eq_treeLaw`, `bushTreeLaw_eq_treeLaw` | [Skeleton](BranchingProcess/Skeleton.lean) |
| Joint Harris decomposition | `BranchingProcess.survivalMeasure_decorations_treeLaw` | [Harris](BranchingProcess/Harris.lean) |
| Subcritical total progeny has an exponential moment | `BranchingProcess.exists_exponential_moment` | [Progeny](BranchingProcess/Progeny.lean) |
| Regular subtrees and the law of the retained tree | `exists_regular_embedding_of_retainedInf` and pruned-tree laws | [Pruning](BranchingProcess/Pruning.lean), [PrunedTree](BranchingProcess/PrunedTree.lean) |

### Brownian-image applications and renewal tools

Paper: [Troscheit2026, arXiv:2610.16339v2](#ref-troscheit2026).
Renewal reference and scope: [Feller1971](#ref-feller1971).

| Result | Declaration(s) or entry point | Module |
|---|---|---|
| Correlation-profile separation of Brownian occupation laws | `BrownianImages.main` | [MainTheorem](BrownianImages/MainTheorem.lean) |
| Lattice and non-lattice profile asymptotics | Profile limits and lattice periodisation | [ProfileAsymptotics](BrownianImages/ProfileAsymptotics.lean), [LatticeProfile](BrownianImages/LatticeProfile.lean), [LatticePeriodisation](BrownianImages/LatticePeriodisation.lean) |
| Key renewal theorem for the finite self-similar laws used here | `key_renewal_theorem`, `nonlattice_renewal_limit`, `lattice_renewal_limit` | [RenewalTheorem](BrownianImages/RenewalTheorem.lean) |
| Analytic parameter dependence and small-dimension monotonicity | `analyticAt_fixedMean`, `exists_strictMonoOn_fixedMean` | [Analyticity](BrownianImages/FixedDimension/Analyticity.lean), [Monotone](BrownianImages/FixedDimension/Monotone.lean) |
| Discrete/countable exceptional level sets and separation for unequal profile means | Parameter separation and image-law singularity; the finite-exception assembly remains in the [source solution](#ref-troscheit2026) | [Separation](BrownianImages/FixedDimension/Separation.lean), [Laws](BrownianImages/FixedDimension/Laws.lean) |
| Minkowski reconstruction of the occupation measure from the compact image | `IsNatural.minkowskiReconstruction` | [FullEndpointAssembly](BrownianImages/Minkowski/FullEndpointAssembly.lean) |

The renewal statements retain the hypotheses specified in their Lean declarations.
Benny Avelin's renewal tools retain their attribution and licences, and the namespace
`AbsorptionCutoff.Renewal`. See [Feller1971](#ref-feller1971) for their scope.

## Paper and literature index

This is the reverse index: **paper → numbered result → Lean declaration or module**.
The subject tables link back to these entries.

**Proved** means the stated result is available in the linked library;
**specialisation** means the restricted form specified here;
**conditional** means an explicit literature hypothesis remains;
**source assembly** means the endpoint is assembled in the original source solution
and this collection contains the stated supporting results, rather than that wrapper.
Numbering refers to the identified edition or revision. The citation of a work does
not claim that all its results are formalised.

<a id="ref-bkt2025"></a>

#### BKT2025 — On exponential separation of analytic self-conformal sets on the real line

Balázs Bárány, István Kolossváry and Sascha Troscheit.
*On exponential separation of analytic self-conformal sets on the real line*. Preprint, 2025;
numbering follows **arXiv:2509.07888v3**.
[Paper, arXiv:2509.07888](https://arxiv.org/abs/2509.07888) ·
[version v3](https://arxiv.org/abs/2509.07888v3) ·
[formalisation revision](https://github.com/sascha2718/lean-dual-analytic-ifs/tree/0155d92226966a90fa219bbcb9d44d2ed89d84d2).

| Paper result | Coverage and Lean entry |
|---|---|
| Theorem 1.4, open and dense strong exponential separation in the relative C² topology | **Proved**; `AnalyticESC.theorem_1_4` in [Generic.OpenDense](AnalyticESC/Generic/OpenDense.lean) |
| Theorem 1.5, dual-projection separation criterion | **Proved**; `AnalyticESC.IFS.theorem_1_5` in [Main.Dichotomy](AnalyticESC/Main/Dichotomy.lean) |
| Theorem 1.6, Hausdorff dimension from exponential separation | **Conditional** on [Rapaport2024](#ref-rapaport2024), including the specified [FengHu2009](#ref-fenghu2009) exact-dimensionality input; `AnalyticESC.IFS.theorem_1_6` in [Dimension.Rapaport](AnalyticESC/Dimension/Rapaport.lean) |
| Corollary 1.7, generic dimension equality | **Conditional** on Rapaport's inputs, for `N ≥ 2`; `AnalyticESC.corollary_1_7` in [Dimension.OpenDense](AnalyticESC/Dimension/OpenDense.lean); the `N = 1` case is excluded |
| Proposition 1.8, explicit distortion criterion | **Proved** for `N ≥ 2`; `AnalyticESC.IFS.proposition_1_8` in [Main.Criterion](AnalyticESC/Main/Criterion.lean) |
| Section 1.2.2, polynomial and non-polynomial examples | Separation is **proved** in [Example](AnalyticESC/Main/Example.lean) and [NonPolynomialExample](AnalyticESC/Main/NonPolynomialExample.lean); polynomial dimension conclusions are **conditional** on Rapaport; its natural-measure local dimension and L^q bound take [Bowen1975](#ref-bowen1975) as a hypothesis in [Lq](AnalyticESC/Dimension/Lq.lean) |
| Theorem 1.12, conjugacy and subconjugacy to similarities | **Proved**; `AnalyticESC.IFS.theorem_1_12_similarity` in [Characterisation](AnalyticESC/Conjugation/Characterisation.lean) and `AnalyticESC.IFS.theorem_1_12` in [PeriodicPoints](AnalyticESC/Conjugation/PeriodicPoints.lean); the latter retains the non-singleton attractor assumption |
| Theorem 2.2, dual separation and super-exponential condensation dichotomy | **Proved**; `AnalyticESC.IFS.theorem_2_2` and `AnalyticESC.IFS.condensation_dichotomy` in [Main.Dichotomy](AnalyticESC/Main/Dichotomy.lean) |

Supporting Sections 2–5, Koenigs linearisation and independence of the admissible complex
radius are included. The representation uses holomorphic extensions of the real analytic maps.

<a id="ref-troscheit2026"></a>

#### Troscheit2026 — Distinguishing sets and measures from their planar Brownian images

Sascha Troscheit. *Distinguishing sets and measures from their planar Brownian images*.
Preprint, 2026. **arXiv:2610.16339v2**.
[Paper, arXiv:2610.16339](https://arxiv.org/abs/2610.16339) ·
[version v2](https://arxiv.org/abs/2610.16339v2) ·
[formalisation revision](https://github.com/sascha2718/lean-brownian-images/tree/daa44d7ea3c3ece10b5cdc7001eadddb0937a9c9).
The original `FractalGeometry` extraction used the earlier working title
*Pair-distance profiles and Minkowski reconstruction of planar Brownian images*.

| Paper result | Included library and endpoint coverage |
|---|---|
| Theorem 1.1, separation by expected correlation profiles | **Proved**; `BrownianImages.main` in [MainTheorem](BrownianImages/MainTheorem.lean) |
| Theorem 1.2, lattice/non-lattice profile asymptotics | **Source assembly** from [ProfileAsymptotics](BrownianImages/ProfileAsymptotics.lean), [LatticeProfile](BrownianImages/LatticeProfile.lean) and [LatticePeriodisation](BrownianImages/LatticePeriodisation.lean) |
| Corollary 1.3, lattice/non-lattice occupation-law separation | **Source assembly** from the profile limits and `BrownianImages.main`; [MainTheorem](BrownianImages/MainTheorem.lean) |
| Theorem 1.4, finite exceptions in the two-contraction family | **Source assembly**; [Separation](BrownianImages/FixedDimension/Separation.lean) proves discreteness/countability of level sets and [Laws](BrownianImages/FixedDimension/Laws.lean) proves separation for unequal profile means; the finite-level-set assembly remains in the source `Solution.lean` |
| Theorem 1.5, small-dimension monotonicity and separation | **Proved monotonicity**, `BrownianImages.exists_strictMonoOn_fixedMean` in [Monotone](BrownianImages/FixedDimension/Monotone.lean); combine with [Laws](BrownianImages/FixedDimension/Laws.lean) for the source assembly |
| Corollary 1.6, finite critical set | **Proved** for its `0 < s ≤ 1/2` range; `BrownianImages.criticalSet_finite` in [Separation](BrownianImages/FixedDimension/Separation.lean) |
| Theorem 1.7, Minkowski reconstruction of occupation measure | **Proved**; `BrownianImages.System.IsNatural.minkowskiReconstruction` in [FullEndpointAssembly](BrownianImages/Minkowski/FullEndpointAssembly.lean) |
| Corollary 1.8, lattice/non-lattice compact-image law separation | **Source assembly** from Theorem 1.7, profile separation and [Reconstruction](BrownianImages/Minkowski/Reconstruction.lean); the homogeneous case is also in [CantorSetApplication](BrownianImages/Minkowski/CantorSetApplication.lean) |
| Corollary 1.9, two-contraction compact-image separation | **Proved separation for unequal means**, `BrownianImages.MinkowskiReconstruction.fixedSystem_brownianImageLaw_mutuallySingular` in [Laws](BrownianImages/FixedDimension/Laws.lean); the finite-exception and small-dimension headline clauses are **source assemblies** |
| Proposition 8.2, distinct homometric natural measures | **Proved**; `FractalGeometry.homometric_example` in [HomometricMeasures](FractalGeometry/HomometricMeasures.lean), with the later system interface in [BrownianImages.HomometricMeasures](BrownianImages/HomometricMeasures.lean) |
| Lemma 9.3, analytic dependence of the fixed-dimension mean | **Proved**; `BrownianImages.analyticAt_fixedMean` in [Analyticity](BrownianImages/FixedDimension/Analyticity.lean) |

The original project verifies 32 numbered statements. This collection imports its library;
it does not import the original `Solution.lean` or claim its wrapper declarations as local
endpoints. In particular, the finite-exception wrapper is not a local theorem merely because
the discreteness/countability tools are present. Renewal scope is specified under
[Feller1971](#ref-feller1971).

<a id="ref-at2026"></a>

#### AT2026 — The quasi-isometry classes of Galton–Watson trees

Jayadev S. Athreya and Sascha Troscheit. *The quasi-isometry classes of Galton–Watson trees*.
Preprint, 2026. **arXiv:2609.23882**.
[Paper](https://arxiv.org/abs/2609.23882) ·
[source formalisation](https://github.com/sascha2718/qi-trees-and-matching-lean).

**Included:** the branching-process foundations, extinction identity
`BranchingProcess.sampleMeasure_not_survives` in [Law](BranchingProcess/Law.lean), reduced
and conjugate laws in [Skeleton](BranchingProcess/Skeleton.lean), the joint Harris decomposition
`BranchingProcess.survivalMeasure_decorations_treeLaw` in [Harris](BranchingProcess/Harris.lean),
subcritical progeny exponential moments in [Progeny](BranchingProcess/Progeny.lean), and
regular-subtree/pruned-tree tools in [Pruning](BranchingProcess/Pruning.lean) and
[PrunedTree](BranchingProcess/PrunedTree.lean). The decomposition is at bounded offspring
support and states laws of realised trees, not unused coordinates of an offspring field.
**Excluded from this collection:** the quasi-isometry classification, graph matching,
Markov matching and their application endpoints. The full paper title identifies the source;
it does not imply that its headline classification theorem is imported.

<a id="ref-gmt2026"></a>

#### GMT2026 — Geometric Measure Theory: Dynamics and Randomness

Sascha Troscheit. *Geometric Measure Theory: Dynamics and Randomness*. Lecture notes,
Uppsala University, HT2026.
[Author's lecture notes](https://www.troscheit.eu/GeometricMeasureTheory.pdf) ·
[Source library and numbered correspondence](https://github.com/sascha2718/lean-geometric-measure-theory/tree/78b2007b787735b6699a9c8d5f71223bd1fbf9e6).
The imported modules follow Sections 1–8; each module's opening table records the note's
result numbers and Lean names. This is a lecture-note source, with no journal DOI asserted.

Selected numbered entries in this README: **Theorem 2.26 (Frostman's lemma)** and
**Corollary 2.27 (dimension through Frostman measures)** are `GeometricMeasureTheory.frostman_compact`,
`frostman_compact_iff`, `frostman_dimension` in [Frostman](GeometricMeasureTheory/Hausdorff/Frostman.lean).
**Lemma 8.5 (quasi-self-similar packing bounds), Theorem 8.7 (measure/content comparability),
Corollary 8.9 (Ahlfors regularity criterion)** are `qss_packing_bounds`, `qss_measure_content`,
`qss_isAhlforsRegularSet_iff` in [Homogeneity](GeometricMeasureTheory/QuasiSelfSimilar/Homogeneity.lean).
The latter compares content and measure; it does not assert they are equal for every
quasi-self-similar set. The [subject index](#dimensions-measures-and-covering) lists the other
included families. Section 9 projection theorems, the general noninteger-density theorem for
`s > 1`, four-corner-dust pure unrectifiability and full-dimensional weak-tangent existence
are **excluded**. Density rectifiability retains a named hypothesis.

<a id="ref-kittlekogler2026"></a>

#### KittleKogler2026 — The exact overlaps conjecture for self-similar measures on the real line

Samuel Kittle and Constantin Kogler. *The exact overlaps conjecture for self-similar measures
on the real line*. Preprint, 2026. **arXiv:2610.10511v1**.
[Paper](https://arxiv.org/abs/2610.10511v1) ·
[authors' formalisation, pinned revision](https://github.com/ckkogler/exact-overlaps-one-dim-lean/tree/99c43adec5c5127ff9a65663641fe51f57c8f7d3).
**Theorem 1.1:** the dimension formula in terms of random-walk entropy and the Lyapunov
exponent is provided by `ExactOverlaps.SelfSimilar.System.theorem_1_1` in
[MainTheorem.Theorem11](vendor/ExactOverlaps/MainTheorem/Theorem11.lean).
The 554 source modules needed for this theorem are retained unchanged, with the
upstream licences. The upstream umbrella and 38 other modules are not included.

<a id="ref-hutchinson1981"></a>

#### Hutchinson1981 — Fractals and self-similarity

John E. Hutchinson. *Fractals and self-similarity*.
**Indiana University Mathematics Journal 30**(5) (1981), 713–747.
[DOI: 10.1512/iumj.1981.30.30055](https://doi.org/10.1512/iumj.1981.30.30055) ·
[author's full text](https://maths-people.anu.edu.au/~john/Assets/Research%20Papers/fractals_self-similarity.pdf).
**Sections 3.1 and 4.4, attractor and invariant-measure existence/uniqueness:** line-system
specialisations in [FractalGeometry.Hutchinson](FractalGeometry/Hutchinson.lean) and
[BrownianImages.Hutchinson](BrownianImages/Hutchinson.lean), notably the two namespaces'
`System.exists_unique_isNatural`. **Theorem 5.3(1), OSC geometry and measure bounds:**
the stopping-cylinder and Ahlfors-regularity specialisations are in
[StoppingGeometry](BrownianImages/StoppingGeometry.lean). The original small library's
[AhlforsRegular](FractalGeometry/AhlforsRegular.lean) instead assumes strong separation.

<a id="ref-schief1994"></a>

#### Schief1994 — Separation properties for self-similar sets

Andreas Schief. *Separation properties for self-similar sets*.
**Proceedings of the American Mathematical Society 122**(1) (1994), 111–115.
[DOI: 10.2307/2160849](https://doi.org/10.2307/2160849).
**Open set condition implies strong open set condition:** the line-system specialisation
is proved as `BrownianImages.System.OpenSetCondition.strongOpenSetCondition` in
[Schief](BrownianImages/Schief.lean). This entry does not claim the full collection of
equivalences for arbitrary Euclidean self-similar systems in the paper.

<a id="ref-birkhoff1931"></a>

#### Birkhoff1931 — Proof of the ergodic theorem

George D. Birkhoff. *Proof of the ergodic theorem*.
**Proceedings of the National Academy of Sciences of the United States of America 17**(12)
(1931), 656–660. [Original paper](https://users.math.uoc.gr/~nikosf/Ergodic2013/Birkhoff.pdf).
**Pointwise ergodic theorem:** the measurable probability-space formulation is proved as
`FractalGeometry.Ergodic.birkhoff_ae` and `FractalGeometry.Ergodic.birkhoff_ergodic` in [Birkhoff](FractalGeometry/Ergodic/Birkhoff.lean),
together with the maximal inequality `FractalGeometry.Ergodic.maximal_ergodic` used in the proof.
This identifies the classical theorem; no numbered correspondence with Birkhoff's flow
formulation is asserted.

<a id="ref-kingman1968"></a>

#### Kingman1968 — The ergodic theory of subadditive stochastic processes

J. F. C. Kingman. *The ergodic theory of subadditive stochastic processes*.
**Journal of the Royal Statistical Society, Series B (Methodological) 30**(3) (1968), 499–510.
[DOI: 10.1111/j.2517-6161.1968.tb00749.x](https://doi.org/10.1111/j.2517-6161.1968.tb00749.x).
**Subadditive ergodic theorem:** proved for integrable subadditive cocycles as
`FractalGeometry.Ergodic.kingman_ae`, `FractalGeometry.Ergodic.kingman_ergodic`, `FractalGeometry.Ergodic.kingman_ergodic_of_tendsto`
in [Kingman](FractalGeometry/Ergodic/Kingman.lean), including the possible negative-infinity limit.

The proof follows the stopping-time arguments of **Yitzhak Katznelson and Benjamin Weiss**,
*A simple proof of some ergodic theorems*, **Israel Journal of Mathematics 42**(4) (1982),
291–296 ([DOI: 10.1007/BF02761409](https://doi.org/10.1007/BF02761409)), and
**J. Michael Steele**, *Kingman's subadditive ergodic theorem*, **Annales de l'Institut
Henri Poincaré, Probabilités et Statistiques 25**(1) (1989), 93–98
([full text](https://www.numdam.org/item/AIHPB_1989__25_1_93_0.pdf)).
These are proof sources for the same Lean theorem, not extra independent endpoints.

<a id="ref-furstenbergkesten1960"></a>

#### FurstenbergKesten1960 — Products of random matrices

Harry Furstenberg and Harry Kesten. *Products of random matrices*.
**Annals of Mathematical Statistics 31**(2) (1960), 457–469.
[DOI: 10.1214/aoms/1177705909](https://doi.org/10.1214/aoms/1177705909).
**Specialisation:** almost-sure logarithmic growth of backward products of invertible
planar tuples, `FractalGeometry.MatrixTuple.tendsto_log_norm_pastProd` and
`FractalGeometry.MatrixTuple.tendsto_log_alpha₂_pastProd` in
[FurstenbergKesten](FractalGeometry/Ergodic/FurstenbergKesten.lean), derived from Kingman's theorem.
The original paper's full random-matrix generality is not asserted.

<a id="ref-oseledec1968"></a>

#### Oseledec1968 — A multiplicative ergodic theorem. Characteristic Ljapunov exponents of dynamical systems

V. I. Oseledec (also transliterated Oseledets). *A multiplicative ergodic theorem.
Characteristic Ljapunov exponents of dynamical systems*.
**Trudy Moskovskogo Matematicheskogo Obshchestva 19** (1968), 179–210.
[Original article and translation record](https://www.mathnet.ru/eng/mmo214);
English translation: **Transactions of the Moscow Mathematical Society 19** (1968), 197–231.
**Planar specialisation with distinct Lyapunov exponents:** finite invertible planar matrix families and an invariant
filtration in [Oseledets](FractalGeometry/Ergodic/Oseledets.lean) and
[OseledetsFiltration](FractalGeometry/LinearCocycles/Filtration.lean). This is not a formalisation of the
arbitrary-dimensional multiplicative ergodic theorem. The citation uses the original
Russian edition's pagination.

<a id="ref-breiman1957"></a>

#### Breiman1957 — The individual ergodic theorem of information theory

Leo Breiman. *The individual ergodic theorem of information theory*.
**Annals of Mathematical Statistics 28**(3) (1957), 809–811.
[DOI: 10.1214/aoms/1177706899](https://doi.org/10.1214/aoms/1177706899).
**Shannon–McMillan–Breiman theorem:** proved for the two-sided shift over a finite alphabet
as `FractalGeometry.shannonMcMillanBreiman`, with the non-ergodic conditional-entropy limit in
[ShannonMcMillanBreiman](FractalGeometry/Ergodic/ShannonMcMillanBreiman.lean).
The Kolmogorov–Sinai generator identity for the time-zero partition is separately proved as
`FractalGeometry.ksEntropy_shift_eq_entropy` in [KolmogorovSinai](FractalGeometry/Ergodic/KolmogorovSinai.lean),
following the entropy framework of [Bowen1975, Chapter 2](#ref-bowen1975).

<a id="ref-branching-classics"></a>

#### AthreyaNey1972 and Harris1963 — branching-process foundations

Krishna B. Athreya and Peter E. Ney. *Branching Processes*.
**Grundlehren der mathematischen Wissenschaften 196**, Springer, 1972.
Theodore E. Harris. *The Theory of Branching Processes*.
**Grundlehren der mathematischen Wissenschaften 119**, Springer, 1963.
[Harris book, DOI: 10.1007/978-3-642-51866-9](https://doi.org/10.1007/978-3-642-51866-9).

**Athreya–Ney Chapter I.12, Harris–Sevastyanov decomposition:** bounded-support versions
of the reduced skeleton, conjugate dying-tree law and joint decoration law are proved in
[Skeleton](BranchingProcess/Skeleton.lean) and [Harris](BranchingProcess/Harris.lean),
notably `BranchingProcess.survivalMeasure_decorations_treeLaw`.
The related extinction and exponential-progeny bounds are in
[Law](BranchingProcess/Law.lean) and [Progeny](BranchingProcess/Progeny.lean).
These book citations identify the foundations; the books as a whole are not formalised.

<a id="ref-feller1971"></a>

#### Feller1971 — An Introduction to Probability Theory and Its Applications, Volume II

William Feller. *An Introduction to Probability Theory and Its Applications*,
**Volume II, second edition**, John Wiley & Sons, New York, 1971. ISBN **0-471-25709-5**.
**Chapter XI, especially §XI.9 (9.2) and §XI.1 (1.10)–(1.17):** renewal and key renewal
theorems. The included Fourier proof is adapted from Benny Avelin's
[AbsorptionCutoff formalisation](https://github.com/BennyAvelin/AbsorptionCutoff/tree/41c45c6d72e979419e46224bb7b4be5cee31f2b5).
The general-purpose adaptation has additional moment/regularity assumptions specified in
[Renewal.Basic](BrownianImages/Renewal/Basic.lean) and
[Renewal.Approx](BrownianImages/Renewal/Approx.lean).

**Proved application specialisation:** finite self-similar laws, a bounded continuous
solution and an exponentially decaying continuous defect, with lattice periodisation
and the non-lattice limit; `BrownianImages.System.key_renewal_theorem`,
`BrownianImages.System.nonlattice_renewal_limit`, `BrownianImages.System.lattice_renewal_limit`
in [RenewalTheorem](BrownianImages/RenewalTheorem.lean).
The sharp, fully general renewal theorem under Feller's minimal hypotheses is **not claimed**.

<a id="ref-bowen1975"></a>

#### Bowen1975 — Equilibrium states and the ergodic theory of Anosov diffeomorphisms

Rufus Bowen. *Equilibrium states and the ergodic theory of Anosov diffeomorphisms*.
**Lecture Notes in Mathematics 470**, Springer, 1975.
[DOI: 10.1007/BFb0081279](https://doi.org/10.1007/BFb0081279).
**Theorem 1.4: proved mixing parity-shift specialisation.**
`FractalGeometry.existsUnique_ergodic_isGibbsPotential` in
[ParityShift.Bowen](FractalGeometry/Pressure/ParityShift/Bowen.lean) proves existence
and uniqueness of an ergodic Gibbs probability measure for Hölder potentials on
symbols `(i,c)`, with the transition `c′ = c + o(i)` modulo 2, when both orientation
values occur. It includes the cylinder Gibbs bounds and identifies their pressure
constant. This endpoint covers this finite mixing shift, rather than an arbitrary
subshift of finite type. [Book text, Theorem 1.4](https://www.cpht.polytechnique.fr/sites/default/files/Bowen_LN_Math_470_second_ed_v2013.pdf).

**Theorem 1.4, Gibbs measures for Hölder potentials: conditional input.**
`AnalyticESC.BowenGibbsStatement` is an explicit one-sided full-shift hypothesis
used in [Dimension.Lq](AnalyticESC/Dimension/Lq.lean). This entry does not claim
an independent proof of Bowen's theorem in that interface.

**Chapter 2, generator theorem: proved finite-alphabet two-sided-shift case.**
`FractalGeometry.ksEntropy_shift_eq_entropy` in
[KolmogorovSinai](FractalGeometry/Ergodic/KolmogorovSinai.lean) identifies the full
measure-theoretic entropy with the entropy rate of the coordinate partition.

<a id="ref-fraserjordanjurga2020"></a>

#### FraserJordanJurga2020 — Dimensions of equilibrium measures on a class of planar self-affine sets

Jonathan M. Fraser, Thomas Jordan and Natalia Jurga. *Dimensions of equilibrium
measures on a class of planar self-affine sets*. **Journal of Fractal Geometry 7**(1)
(2020), 87–111. [DOI: 10.4171/JFG/85](https://doi.org/10.4171/JFG/85) ·
[arXiv:1706.06833v2](https://arxiv.org/abs/1706.06833v2).
**Section 1.4, Lemma 1.3 and Corollaries 1.5–1.6: proved decomposition and Lyapunov-identity parts.**
`FractalGeometry.fraserJordanJurgaDecomposition_holds` in
[Rectangular.FraserJordanJurga](FractalGeometry/Pressure/Rectangular/FraserJordanJurga.lean)
decomposes an invariant probability measure satisfying the singular-value Gibbs
bounds into two ergodic Gibbs measures on the parity shift, and identifies its two
Lyapunov exponents with their coordinate integrals. The finite contractive family
has positive diagonal/anti-diagonal coefficients, both orientations and a proximal
diagonal generator; `0 < s < 2`. The formal hypothesis is `RectangularIFS.PositiveRatios`.
This endpoint does not include the pressure equalities, the strict inequality in
Corollary 1.6, or the paper's later measure-dimension formula.

<a id="ref-shmerkin2019"></a>

#### Shmerkin2019 — On Furstenberg's intersection conjecture, self-similar measures, and the L^q norms of convolutions

Pablo Shmerkin. *On Furstenberg's intersection conjecture, self-similar measures,
and the L^q norms of convolutions*. **Annals of Mathematics (2) 189**(2) (2019), 319–391.
[DOI: 10.4007/annals.2019.189.2.1](https://doi.org/10.4007/annals.2019.189.2.1) ·
[arXiv:1609.07802v3](https://arxiv.org/abs/1609.07802v3).
**Theorem 6.6, lower-bound consequence: proved.**
`FractalGeometry.shmerkinLqDimension_holds` in
[SelfSimilar.Shmerkin](FractalGeometry/SelfSimilar/Shmerkin.lean) gives, for `q > 1`,
an eventual bound `∑ μ(I)^q ≤ 2^(−M(q−1)α)` over every finite collection of level-M
dyadic intervals, assuming `α < 1` and `∑ p_i^q |r_i|^(−(q−1)α) < 1`.
The finite similarity family has nonzero ratios of modulus below one, positive
probability weights and **Definition 6.5** exponential separation.
The endpoint proves this lower-bound form, not the full L^q-dimension equality.

The supporting [Lq](FractalGeometry/Entropy/Lq/Statement.lean) modules include the
asymmetric Balog–Szemerédi–Gowers argument and convolution inverse estimates.
The Bourgain step proves a weaker form of **Theorem 3.1** with an existential
positive doubling exponent, not its printed exponent `2^(−2T−1)`.
Its proof uses Hochman's convolution-saturation result through the included
`ExactOverlaps` library, following the method in **Pablo Shmerkin**,
*Inverse theorems for discretized sums and L^q norms of convolutions in ℝ^d*,
[arXiv:2308.09846v3](https://arxiv.org/abs/2308.09846v3), Theorem 1.5.
The paper's Furstenberg-intersection and general dynamically driven results are
not claimed by this collection.

<a id="ref-jordanrapaport2021"></a>

#### JordanRapaport2021 — Dimension of ergodic measures projected onto self-similar sets with overlaps

Thomas Jordan and Ariel Rapaport. *Dimension of ergodic measures projected onto
self-similar sets with overlaps*. **Proceedings of the London Mathematical Society
(3) 122**(2) (2021), 191–206.
[DOI: 10.1112/plms.12337](https://doi.org/10.1112/plms.12337) ·
[arXiv:1908.00271v2](https://arxiv.org/abs/1908.00271v2).

**Theorem 1.1 — proved in a two-sided-shift formulation:**
`FractalGeometry.jordanRapaportDimension_holds` in
[Line.JordanRapaport](FractalGeometry/SelfSimilar/Line/JordanRapaport.lean) proves
`JordanRapaportDimension`: for a finite real-line similarity IFS with exponential
separation, the coding image of every ergodic shift-invariant probability measure
is exact-dimensional with dimension `min 1 (-entropy / lyapunov)`.
`LineIFS` allows nonzero ratios of either sign with absolute value below one;
its coding map uses the nonnegative coordinates. The proof uses the proved
[Shmerkin lower bound](#ref-shmerkin2019), with no remaining literature hypothesis.

<a id="ref-morrisshmerkin2019"></a>

#### MorrisShmerkin2019 — On equality of Hausdorff and affinity dimensions, via self-affine measures on positive subsystems

Ian D. Morris and Pablo Shmerkin. *On equality of Hausdorff and affinity dimensions,
via self-affine measures on positive subsystems*.
**Transactions of the American Mathematical Society 371**(3) (2019), 1547–1582.
[DOI: 10.1090/tran/7119](https://doi.org/10.1090/tran/7119) ·
[arXiv:1602.08789](https://arxiv.org/abs/1602.08789).
**Theorem 3.1, distinct-exponent conclusion: proved rectangular specialisation.**
`FractalGeometry.morrisShmerkinLyapunov_holds` in
[Rectangular.MorrisShmerkin](FractalGeometry/Pressure/Rectangular/MorrisShmerkin.lean)
proves that the Lyapunov exponents of a singular-value equilibrium state are
strictly different for `0 < s < 2`, provided the finite contractive family contains
both diagonal and anti-diagonal matrices and a proximal diagonal generator.
Its proof includes the equal-exponents/Bernoulli argument of **Lemma 3.4** and the
non-Bernoulli obstruction of **Lemma 3.5**. The full-support clause and general
irreducible-matrix form of Theorem 3.1 are not claimed by this endpoint.

<a id="ref-fraser2012"></a>

#### Fraser2012 — On the packing dimension of box-like self-affine sets in the plane

Jonathan M. Fraser. *On the packing dimension of box-like self-affine sets in the plane*.
**Nonlinearity 25**(7) (2012), 2075–2092.
[DOI: 10.1088/0951-7715/25/7/2075](https://doi.org/10.1088/0951-7715/25/7/2075) ·
[arXiv:1108.2639](https://arxiv.org/abs/1108.2639).
**Theorem 2.3: proved.** `FractalGeometry.RectangularIFS.fraserBound_holds`
proves packing dimension = upper box dimension ≤ the modified-pressure zero;
`FractalGeometry.RectangularIFS.fraserROSC_holds` proves packing dimension =
box dimension = that zero under the rectangular open set condition.
[Rectangular.Fraser](FractalGeometry/SelfAffine/Rectangular/Fraser.lean) uses finite
contractive diagonal/anti-diagonal planar affine maps, including reflections.
The dimensions are the `GeometricMeasureTheory` definitions.

**Corollary 2.5: proved.** Under the rectangular open set condition, if both
coordinate projections have box dimension one, packing and box dimensions equal
the affinity dimension: `FractalGeometry.RectangularIFS.fraser_full_projections`
in [FullProjections](FractalGeometry/SelfAffine/Rectangular/FullProjections.lean).
The affinity dimension is shared with the general planar `AffineIFS` interface.

<a id="ref-fenghu2009"></a>

#### FengHu2009 — Dimension theory of iterated function systems

De-Jun Feng and Huyi Hu. *Dimension theory of iterated function systems*.
**Communications on Pure and Applied Mathematics 62**(11) (2009), 1435–1500.
[DOI: 10.1002/cpa.20276](https://doi.org/10.1002/cpa.20276).
**Theorem 2.8: proved self-similar-line exact-dimensionality specialisation.**
`FractalGeometry.SelfSimilar.FengHu.Coding.exists_isExactDim` in
[SelfSimilar.FengHu](FractalGeometry/SelfSimilar/FengHu.lean) proves existence of a
constant local dimension for a projected ergodic invariant probability measure,
without separation. It does not yet express that constant using projection entropy.
[Authors' full paper](https://users.math.msu.edu/users/hhu/paper/09dimthy.pdf) ·
[arXiv:1002.2036](https://arxiv.org/abs/1002.2036).

**Separate conditional self-conformal input:** the broader exact-dimensionality conclusion is bundled into
`AnalyticESC.RapaportMeasureStatement` in
[Dimension.Rapaport](AnalyticESC/Dimension/Rapaport.lean). It remains a hypothesis
of the dimension consequences indexed here.

<a id="ref-rapaport2024"></a>

#### Rapaport2024 — Dimension of self-conformal measures associated to an exponentially separated analytic IFS on ℝ

Ariel Rapaport. *Dimension of self-conformal measures associated to an exponentially
separated analytic IFS on ℝ*. Preprint, 2024; cited version **arXiv:2412.16753v2**, 2025.
[Paper, version v2](https://arxiv.org/abs/2412.16753v2).
**Theorem 1.2 and Corollary 1.3: conditional inputs, not proved in this collection.**
They appear as `AnalyticESC.RapaportMeasureStatement` and `AnalyticESC.RapaportSetStatement`
in [Dimension.Rapaport](AnalyticESC/Dimension/Rapaport.lean); the former also bundles
the exact-dimensionality conclusion from [FengHu2009, Theorem 2.8](#ref-fenghu2009).
Theorems using these parameters remain conditional even though they have no nonstandard axioms.

<a id="ref-falconer1988"></a>

#### Falconer1988 — The Hausdorff dimension of self-affine fractals

Kenneth J. Falconer. *The Hausdorff dimension of self-affine fractals*.
**Mathematical Proceedings of the Cambridge Philosophical Society 103**(2) (1988), 339–350.
[DOI: 10.1017/S0305004100064926](https://doi.org/10.1017/S0305004100064926).
**Theorem 5.4, upper-bound part: proved planar specialisation.**
`FractalGeometry.AffineIFS.upperBoxDim_attractor_le` and `dimH_attractor_le` in
[SelfAffine.Falconer](FractalGeometry/SelfAffine/Falconer.lean) bound upper box and
Hausdorff dimension by `min(2, affinity dimension)` for finite nonempty invertible
contractive planar systems. No separation condition is assumed. The paper's
almost-every-translation equality is not proved here.

<a id="ref-li1980"></a>

#### Li1980 — A Martingale Approach to the Study of Occurrence of Sequence Patterns in Repeated Experiments

Shuo-Yen Robert Li. *A Martingale Approach to the Study of Occurrence of Sequence
Patterns in Repeated Experiments*. **Annals of Probability 8**(6) (1980), 1171–1176.
[DOI: 10.1214/aop/1176994578](https://doi.org/10.1214/aop/1176994578).

**Proved equal-length correlation identity:** in
[Patterns.Li](FractalGeometry/Probability/Patterns/Li.lean),
`FractalGeometry.Probability.Patterns.IsIIDProcess.li_identity` states
`E[T] · p(z) = ∑_u P(u wins) · wcorr(u,z)` for each target pattern `z`.
`Weights.wcorr_eq` identifies the weighted correlation with `p(z) · corr(u,z)`,
where `corr` sums reciprocal prefix probabilities over suffix-prefix matches.
`IsIIDProcess.sum_hitProb` gives `∑_u P(u wins) = 1`, and
`measure_hittingTime_top` gives almost-sure finite hitting time for a nonempty
pattern family. These results assume a finite alphabet, strictly positive symbol
probabilities and patterns of one common positive length. No correspondence with
a specific numbered statement or with the paper's unequal-length cases is asserted.

<a id="ref-einsiedlerward2011"></a>

#### EinsiedlerWard2011 — Ergodic Theory with a View Towards Number Theory

Manfred Einsiedler and Thomas Ward. *Ergodic Theory with a View Towards Number Theory*.
**Graduate Texts in Mathematics 259**, Springer, 2011.
[DOI: 10.1007/978-0-85729-021-2](https://doi.org/10.1007/978-0-85729-021-2).

**Theorem 5.14 — conditional-measure properties for standard Borel spaces:**
`FractalGeometry.condMeas` in [Conditional](FractalGeometry/Symbolic/Conditional.lean)
uses Mathlib's conditional-expectation kernel. The associated disintegration identity
for nonnegative measurable functions, almost-everywhere uniqueness and concentration
on measurable-partition atoms are proved as `setLIntegral_lintegral_condMeas`,
`condMeas_unique` and `condMeas_atom` in
[Disintegration](FractalGeometry/Symbolic/Disintegration.lean).
The atom statement uses partitions represented by fibres of a measurable real-valued map.

**Proposition 5.20 — proved measurable-partition formulation:**
`FractalGeometry.double_conditional` in
[Conditioning](FractalGeometry/Symbolic/Conditioning.lean) identifies conditioning
a conditional probability measure on a finer partition with conditioning the original
measure on that partition, almost everywhere. It also gives the iterated integral identity.

<a id="ref-feng2023"></a>

#### Feng2023 — Dimension of invariant measures for affine iterated function systems

De-Jun Feng. *Dimension of invariant measures for affine iterated function systems*.
**Duke Mathematical Journal 172**(4) (2023), 701–774.
[DOI: 10.1215/00127094-2022-0014](https://doi.org/10.1215/00127094-2022-0014) ·
[arXiv:1901.01691v2](https://arxiv.org/abs/1901.01691v2).

**Theorems 1.2(ii) and 1.3 — proved planar specialisation:**
`FractalGeometry.planarFengLedrappierYoung_holds` in
[FengLedrappierYoung](FractalGeometry/SelfAffine/FengLedrappierYoung.lean).
The statement requires invertible contracting maps and distinct Lyapunov exponents.
Arbitrary dimension, coincident exponents and general average contraction are not covered.

<a id="ref-fengkaenmaki2011"></a>

#### FengKaenmaki2011 — Equilibrium states of the pressure function for products of matrices

De-Jun Feng and Antti Käenmäki. *Equilibrium states of the pressure function for products
of matrices*. **Discrete and Continuous Dynamical Systems 30**(3) (2011), 699–708.
[DOI: 10.3934/dcds.2011.30.699](https://doi.org/10.3934/dcds.2011.30.699) ·
[arXiv:1009.3129v1](https://arxiv.org/abs/1009.3129v1).

**Proposition 1.2 — proved planar existence, Gibbs and uniqueness parts:**
`FractalGeometry.MatrixTuple.exists_unique_normEquilibrium` supplies the unique
ergodic equilibrium state on the two-sided shift, with Gibbs bounds, for `q > 0`.
`FractalGeometry.fengKaenmakiNormEquilibrium_holds` gives Gibbs bounds and uniqueness
on the one-sided shift. Both are in
[FengKaenmaki](FractalGeometry/Pressure/FengKaenmaki.lean).
Pressure differentiability is not asserted by these endpoints.

<a id="ref-bky2026"></a>

#### BKY2026 — Finer geometry of planar self-affine sets

Balázs Bárány, Antti Käenmäki and Han Yu. *Finer geometry of planar self-affine sets*.
**Advances in Mathematics 493** (2026), article 110914.
[DOI: 10.1016/j.aim.2026.110914](https://doi.org/10.1016/j.aim.2026.110914) ·
[arXiv:2107.00983v2](https://arxiv.org/abs/2107.00983v2).

**Lemma 2.7 — proved matrix classification:** `FractalGeometry.tuple_classification`
in [Classification](FractalGeometry/LinearCocycles/Classification.lean).
Numbering follows the linked revision. The paper's geometric dimension conclusions
are not asserted by this matrix-algebra endpoint.

<a id="ref-mackay2011"></a>

#### Mackay2011 — Assouad dimension of self-affine carpets

John M. Mackay. *Assouad dimension of self-affine carpets*.
**Conformal Geometry and Dynamics 15** (2011), 177–187.
[DOI: 10.1090/S1088-4173-2011-00232-3](https://doi.org/10.1090/S1088-4173-2011-00232-3) ·
[arXiv:1003.0930v2](https://arxiv.org/abs/1003.0930v2).

**Theorem 1.1 — proved Bedford–McMullen carpet formula:**
`FractalGeometry.BedfordMcMullen.System.mackay_dimension` in
[BedfordMcMullen](FractalGeometry/SelfAffine/BedfordMcMullen.lean).
For digits `D ⊆ {0,…,M−1} × {0,…,N−1}`, `2 ≤ M < N`, the attractor of
`(x,y) ↦ ((x+i)/M, (y+j)/N)`, `(i,j) ∈ D`, has Assouad dimension

`log c / log M + log b / log N`,

where `c = #{i : ∃ j, (i,j) ∈ D}` and `b = max_i #{j : (i,j) ∈ D}`.
The coordinate axes are exchanged relative to the paper. The definition
`FractalGeometry.Dimension.PhiAssouad.dimA` uses diameter covering counts inside
balls at two scales. Empty and single-digit sets are included as elementary
zero-dimensional cases. The paper's conformal Assouad dimension results and
its more general Lalley–Gatzouras formula are not asserted by this endpoint.

<a id="ref-gatzouraslalley1994"></a>

#### GatzourasLalley1994 — Statistically self-affine sets: Hausdorff and box dimensions

Dimitrios Gatzouras and Steven P. Lalley. *Statistically self-affine sets: Hausdorff
and box dimensions*. **Journal of Theoretical Probability 7**(2) (1994), 437–468.
[DOI: 10.1007/BF02214277](https://doi.org/10.1007/BF02214277) ·
[Authors' March 1993 version](https://www.aua.gr/gatzouras/JTP94.pdf).

**Theorem 4.1 — proved independent Bernoulli-retention specialisation:**
`FractalGeometry.Probability.GridPercolation.gatzourasLalley_boxDimension` and
`gatzourasLalley_boxCoverRate` in
[GatzourasLalley](FractalGeometry/Probability/GridPercolation/GatzourasLalley.lean).
For a grid with `2 ≤ M < N`, column means `E_i = ∑_j p_ij`, mean offspring
`m = ∑_i E_i > 1`, `Γ = log M / log N`, and
`λ = min_{0 ≤ t ≤ 1} ∑_{E_i > 0} E_i^t`, the almost-sure box dimension on survival is

`log m / log N + (1 − Γ) log λ / log M`.

**Proposition 3.5 — proved projection-population growth:**
`FractalGeometry.Probability.GridPercolation.gatzourasLalley_projectionGrowth` in
[ProjectionGrowth](FractalGeometry/Probability/GridPercolation/ProjectionGrowth.lean)
proves `log Z_n / n → log λ` almost surely on survival, where `Z_n` is the number
of occupied columns at generation `n`. It uses the same supercritical model
and the same `λ` as the box-dimension formula above.

Each child is retained independently with its fixed probability `p_ij ∈ [0,1]`.
The elementary one-column and fixed one-child-per-column cases are included.
Numbering follows the linked author version; the coordinate axes are exchanged.
The dimension definitions use diameter covering counts and real logarithmic
liminf/limsup in `FractalGeometry.Dimension.PhiAssouad`. No Hausdorff-dimension
formula or general dependent offspring law is claimed by these endpoints.

<a id="ref-brt2025"></a>

#### BRT2025 — Interpolating with generalized Assouad dimensions

Amlan Banaji, Alex Rutar and Sascha Troscheit. *Interpolating with generalized Assouad
dimensions*. **Journal of Geometric Analysis 35**(9) (2025), article 270.
[DOI: 10.1007/s12220-025-02099-w](https://doi.org/10.1007/s12220-025-02099-w) ·
[arXiv:2308.12975](https://arxiv.org/abs/2308.12975).

**Corollary 2.7 — proved bounded planar specialisation:**
`FractalGeometry.Dimension.PhiAssouad.upperBoxDim_le_dimAphi` in
[BoxComparison](FractalGeometry/Dimension/PhiAssouad/BoxComparison.lean).
Its `DimFun` records the dimension-function hypotheses of Definition 1.1.

**Lemma 1.6(ii) — proved finite Bernoulli-child specialisation:**
`FractalGeometry.Probability.Branching.treeSecondBorelCantelli_of_isPercolation` in
[Branching.BorelCantelli](FractalGeometry/Probability/Branching/BorelCantelli.lean)
proves recurrence of measurable retained-subtree events under the weighted-divergence
condition. Each labelled child position has a fixed retention probability, with all
retention variables independent and mean offspring count greater than one.
The endpoint does not cover every finitely supported offspring law or part (i).

## Source collections

The snapshot date is **22 October 2026**. The [manifest](provenance/sources.json)
records source revisions, retained files, hashes and integration changes.

| Collection | Included source modules | Public source |
|---|---:|---|
| `GeometricMeasureTheory` | 44 | [Lecture-note library](https://github.com/sascha2718/lean-geometric-measure-theory) |
| `AnalyticESC` | 45 | [Analytic exponential separation](https://github.com/sascha2718/lean-dual-analytic-ifs) |
| `BranchingProcess` | 15 | [Tree and branching-process formalisation](https://github.com/sascha2718/qi-trees-and-matching-lean) |
| `BrownianImages` | 143 | [Brownian-image formalisation](https://github.com/sascha2718/lean-brownian-images) |
| `ExactOverlaps` | 554 | [Kittle–Kogler formalisation](https://github.com/ckkogler/exact-overlaps-one-dim-lean) |

`FractalGeometry` supplies the self-similar core, the independent ergodic/entropy
and covering-limit modules, and the subject imports listed above.

## Build, checks and downstream use

Lean and Mathlib are pinned to **`v4.35.0-rc2`** in [lean-toolchain](lean-toolchain) and
[lakefile.toml](lakefile.toml). On a fresh independent checkout:

```sh
lake exe cache get
lake build
python3 scripts/check_library.py
```

On the author's workstation, `.lake/packages` is a shared symlink. Do not run `lake update`
or replace that directory as part of routine work. The collection needs no sibling checkout,
absolute source path or local path dependency to build elsewhere.

`lake build` builds the subject entry points, the combined import and
[`FractalGeometry.AxCheck`](FractalGeometry/AxCheck.lean). The audit checks every declaration
originating in every included component, including private helpers and vendored declarations,
and fails on any axiom other than `propext`, `Classical.choice` and `Quot.sound`. Neither
`FractalGeometry` nor `FractalGeometry.All` imports the audit. The structural Python check
verifies provenance hashes, complete import coverage, absence of statement-layer imports and
proof holes, and the module index; it does not replace Lean's proof check.

For a smaller build, use an entry point such as `lake build FractalGeometry.Dimension`.
To regenerate the complete module index after a deliberate inventory change:

```sh
python3 scripts/check_library.py --write-index
```

Downstream projects can require this repository and then use any of the listed imports:

```toml
[[require]]
name = "fractalgeometry"
git = "https://github.com/sascha2718/lean-fractal-geometry"
rev = "<commit-containing-the-required-results>"
```

Pin a concrete revision and use its matching toolchain. A local checkout can instead be
required with `path = "/path/to/FractalGeometry"`.

### Existing independent challenge audit

[Challenge.lean](Challenge.lean) and [Solution.lean](Solution.lean) retain exactly the original
six headline endpoints: `audit_hutchinson`, `audit_self_similar_unique`, `audit_ahlfors`,
`audit_frostman`, `audit_cantor_measure` and `audit_homometric`, in namespace `Challenge`.
The challenge remains independent of the library and keeps those theorems as holes.
The new modules do not expand this challenge's scope.

```sh
lake build Challenge Solution
./comparator-audit.sh
```

The comparator checks the six endpoints selected by [comparator-config.json](comparator-config.json).
Its external comparator/export tools must match the toolchain; `COMPARATOR_TOOLS` selects their
installation. This six-endpoint comparison is separate from the collection-wide Lean axiom audit.
It must not be described as an independent comparator audit of every imported paper.

### Documentation

This README indexes the literature and proved results. The
[module index](docs/modules.md) lists every library module and links to its Lean source.

## Licence and attribution

The collection is distributed under [Apache License 2.0](LICENSE), with the
separately licensed ExactOverlaps dependency. See [NOTICE](NOTICE) and the
licences in [provenance](provenance). ExactOverlaps retains its
[BSD Zero Clause licence](vendor/LICENSE) and
[LpSelfSimilar notice](vendor/LpSelfSimilar-LICENSE). The renewal adaptation
retains Benny Avelin's copyright and Apache licence.
