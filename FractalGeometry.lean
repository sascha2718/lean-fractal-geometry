/-
Self-similar systems on the line and the geometry of their attractors. The
library develops contracting similarities, proves Hutchinson's theorem for the
attractor and natural measure, establishes Ahlfors regularity under strong
separation, and constructs two distinct homometric self-similar measures.

This compatibility entry point retains the original self-similar library.
`FractalGeometry.All` imports the consolidated collection; subject entry points
such as `FractalGeometry.Dimension` and `FractalGeometry.Ergodic` provide
smaller imports. The README indexes their results and source collections.

* `Regularity`: Frostman and Ahlfors regular measures on the line, their open-
  and closed-ball formulations, atomlessness, and the pair-distance
  distribution.
* `System`: self-similar systems `S_i(x) = r_i x + b_i` on `[0,1]`, attractors,
  strong separation, the similarity dimension, the natural measure, the
  log-ratios and their law, and three worked systems.
* `Hutchinson`: the coding map on `ℕ → ι`, the existence and uniqueness of the
  attractor and of the natural measure, and the uniqueness of a self-similar
  probability measure on `[0,1]`.
* `AhlforsRegular`: the natural measure of a strongly separated system is
  Ahlfors regular of its similarity dimension, with explicit constants, and the
  Frostman bound it yields at every centre.
* `Homometric`: two digit sets with the same signed difference multiset, their
  strong separation, and their common dimension `log 6 / log 30`.
* `HomometricMeasures`: the two natural measures associated with those digit
  sets are distinct and have equal signed convolutions and pair-distance
  distributions.

`AxCheck` is a separate target: it prints the original endpoints' axioms and
rejects nonstandard axioms throughout the consolidated collection.
-/
import FractalGeometry.Regularity
import FractalGeometry.System
import FractalGeometry.Hutchinson
import FractalGeometry.AhlforsRegular
import FractalGeometry.Homometric
import FractalGeometry.HomometricMeasures
