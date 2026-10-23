/-
Standard results of geometric measure theory, following Sections 1–8 of the lecture notes
*Geometric Measure Theory: Dynamics and Randomness* (HT2026, Uppsala University).

The library builds on Mathlib alone. Each module follows one section or subsection of the notes and
opens with a table listing every result of that part, the Lean declaration that states it, and
where it is found: in this library, in Mathlib, or in a Palomar entry.

Section 1, *Basic measure theory*
* `BasicMeasureTheory`: outer measures, Carathéodory measurability, regularity, the metric
  criterion, and weak convergence.

Section 2, *Hausdorff content, measure, and dimension*
* `Hausdorff.Basic`: δ-content, content and measure, their outer-measure and Borel properties,
  critical exponents, null sets, and Hausdorff dimension.
* `Hausdorff.NonadditiveContent`: content of intervals and the failure of additivity.
* `Hausdorff.CoveringConventions` (2.1): arbitrary covers, Borel regularity, Lipschitz images.
* `Hausdorff.DimensionProperties` (2.2): monotonicity and countable stability of dimension.
* `Hausdorff.GeneralGauges` (2.5): the mass distribution principle for a gauge.
* `Hausdorff.Computing` (2.3): the mass distribution principle, similarity scaling, and equality of
  content and measure.
* `Hausdorff.CantorSets` (2.3): symmetric Cantor sets, their measures, and their dimension.
* `Hausdorff.FlowsAndCuts` (2.4): max flow equals min cut on finite rooted trees.
* `Hausdorff.Frostman` (2.4): Frostman's lemma for compact sets.

Section 3, *Covering theorems, densities, and regular sets*
* `Covering.VitaliLemmas`: the finite Vitali lemma and the `5r`-covering lemma.
* `Covering.HausdorffVitali` (3.1): fine covers and Vitali's theorem for Hausdorff measure.
* `Covering.DensityComparison` (3.1): Hausdorff measure against local ball masses.
* `Covering.RadonVitali` (3.2): Vitali's theorem for Radon measures and relative densities.
* `Covering.AhlforsRegular` (3.3): Ahlfors regular measures and sets.
* `Covering.AhlforsRegularExamples` (3.3): intervals and Cantor sets.
* `Covering.Densities` (3.4): densities, `s`-sets, regular points, and the density bounds.
* `Covering.NonintegerDensity` (3.4): Marstrand's theorem for `0 < s < 1`.
* `Covering.DensityDecomposition` (3.5): regular and irregular parts of an `s`-set.
* `Covering.Arcs` (3.5): rectifiable arcs, their length, and their density.
* `Covering.Rectifiability` (3.5): rectifiable decomposition, curve-like and curve-free sets.
* `Covering.FourCornerDust` (3.5): the four-corner Cantor dust.

Section 4, *Box-counting and packing dimensions*
* `Box.CoveringNumbers` (4.1): covering and packing numbers at one scale.
* `Box.BoxDimension` (4.2): lower and upper box dimensions and their properties.
* `Box.PackingMeasure` (4.3): the packing premeasure, the packing measure, and packing dimension.
* `Box.ModifiedBox` (4.4): packing dimension as the modified upper box dimension.
* `Box.ScaleExamples` (4.5): digit-position sets separating the two box dimensions.

Section 5, *Assouad dimension and local scaling*
* `Assouad.Basic` (5.1): the two-scale definition and its properties.
* `Assouad.Doubling` (5.2): doubling sets and finiteness of the Assouad dimension.
* `Assouad.WeakTangents` (5.3): Hausdorff convergence, weak tangents, and their examples.
* `Assouad.AhlforsDimensions` (5.4): all dimensions agree on Ahlfors regular sets.
* `Assouad.MeasureDimensions` (5.5): local dimensions and the upper regularity dimension.
* `Assouad.Comparison` (5.6): the comparison of all the dimensions.

`AxCheck` is a separate target: it prints the axioms of the endpoints of the library, which must use
only `propext`, `Classical.choice`, `Quot.sound`, or a subset of these.
Section 6, *Cookie cutters*
* `CookieCutter.Basic`: the system, its inverse branches, cylinders, levels and repeller.
* `CookieCutter.BoundedDistortion` (6.1): Birkhoff sums, the principles of bounded variation and
  bounded distortion, and the separation of cylinders.
* `CookieCutter.SelfSimilarity` (6.2): the repeller is self-similar up to bounded distortion.

Section 7, *Thermodynamic formalism and pressure*
* `Pressure.Subadditive` (7.1): quasi-subadditive sequences and the growth rate of a
  quasi-multiplicative sequence.
* `Pressure.Gibbs` (7.2): the partition sums, the pressure, and the Gibbs measure of a Lipschitz
  potential.
* `Pressure.Dimension` (7.3): the pressure of the geometric potential, its unique zero, and the
  dimension and Hausdorff measure of the repeller.

Section 8, *Quasi-self-similar sets and their Hausdorff measure*
* `QuasiSelfSimilar.CompactVitali`: Vitali's covering theorem with compact sets in place of balls.
* `QuasiSelfSimilar.SelfSimilar` (8.2.1): self-similar sets, the similarity dimension, and the
  equality of Hausdorff measure and content.
* `QuasiSelfSimilar.Basic` (8.1): quasi-self-similar sets, bounded packings and finite measure.
* `QuasiSelfSimilar.Homogeneity` (8.2.2): the comparison of measure and content, and the
  characterisation of Ahlfors regularity.

-/
import GeometricMeasureTheory.BasicMeasureTheory
import GeometricMeasureTheory.Hausdorff.Basic
import GeometricMeasureTheory.Hausdorff.NonadditiveContent
import GeometricMeasureTheory.Hausdorff.CoveringConventions
import GeometricMeasureTheory.Hausdorff.DimensionProperties
import GeometricMeasureTheory.Hausdorff.GeneralGauges
import GeometricMeasureTheory.Hausdorff.Computing
import GeometricMeasureTheory.Hausdorff.CantorSets
import GeometricMeasureTheory.Hausdorff.FlowsAndCuts
import GeometricMeasureTheory.Hausdorff.Frostman
import GeometricMeasureTheory.Covering.VitaliLemmas
import GeometricMeasureTheory.Covering.HausdorffVitali
import GeometricMeasureTheory.Covering.DensityComparison
import GeometricMeasureTheory.Covering.RadonVitali
import GeometricMeasureTheory.Covering.AhlforsRegular
import GeometricMeasureTheory.Covering.AhlforsRegularExamples
import GeometricMeasureTheory.Covering.Densities
import GeometricMeasureTheory.Covering.NonintegerDensity
import GeometricMeasureTheory.Covering.DensityDecomposition
import GeometricMeasureTheory.Covering.Arcs
import GeometricMeasureTheory.Covering.Rectifiability
import GeometricMeasureTheory.Covering.FourCornerDust
import GeometricMeasureTheory.Box.CoveringNumbers
import GeometricMeasureTheory.Box.BoxDimension
import GeometricMeasureTheory.Box.PackingMeasure
import GeometricMeasureTheory.Box.ModifiedBox
import GeometricMeasureTheory.Box.ScaleExamples
import GeometricMeasureTheory.Assouad.Basic
import GeometricMeasureTheory.Assouad.Doubling
import GeometricMeasureTheory.Assouad.WeakTangents
import GeometricMeasureTheory.Assouad.AhlforsDimensions
import GeometricMeasureTheory.Assouad.MeasureDimensions
import GeometricMeasureTheory.Assouad.Comparison
import GeometricMeasureTheory.CookieCutter.Basic
import GeometricMeasureTheory.CookieCutter.BoundedDistortion
import GeometricMeasureTheory.CookieCutter.SelfSimilarity
import GeometricMeasureTheory.Pressure.Subadditive
import GeometricMeasureTheory.Pressure.Gibbs
import GeometricMeasureTheory.Pressure.Dimension
import GeometricMeasureTheory.QuasiSelfSimilar.CompactVitali
import GeometricMeasureTheory.QuasiSelfSimilar.SelfSimilar
import GeometricMeasureTheory.QuasiSelfSimilar.Basic
import GeometricMeasureTheory.QuasiSelfSimilar.Homogeneity
