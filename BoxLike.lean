module

/-
`BoxLike`: a formalisation of `diagonal-antidiagonal.tex`, "Hausdorff dimension of planar
box-like self-affine sets with rotations" (Käenmäki, Prokaj, Simon, Troscheit),
arXiv:2611.09066v1, https://arxiv.org/abs/2611.09066v1.

Built on Mathlib and on the Kittle–Kogler library `ExactOverlaps` (`vendor/`). No `sorry`, no
axiom beyond `propext`, `Classical.choice` and `Quot.sound`. Theorems the article cites are
`Prop`-valued definitions in the `Literature*` modules, taken as hypotheses by the results that
use them and proved elsewhere in the library. `docs/correspondence.md` records the state of every
numbered result.

* `Orientation`: the two-sided shift `σ^n` and the orientation cocycle `ε_n` of
  `eq:def_of_eps_mod2`, with the cocycle identity `eq:tau_omega_sigma_commutative1`.
* `Coding`: the sub-shift `Σ_Z`, the codings `τ`, `ω` of `eq:def_of_tau_omega`, the partition
  `eq:tau_omega_partition` and `thm:tau_omega_sigma_commutative`.
* `System`: box-like systems, the matrices `A_i`, the maps `φ_i`, the projective system `Ψ` of
  `eq:def_of_g_system`, `eq:phi_def_by_g` and `thm:matrix_products_g_derivatives`.
* `Separation`: the projective gap `Δ_n^Ψ`, the projective exponential separation condition,
  the absence of exact overlaps, compositions of similarities and `lem:proj_gap_dominated`.
* `AxisSeparation`: the gap and the exponential separation of the systems a diagonal system
  induces on the coordinate axes, the definition before `thm:rapaport`.
* `ProjExpNoOverlaps`: projective exponential separation implies the absence of exact overlaps
  (`sec:exponential_separation`).
* `LiteratureRapaport`, `LiteratureHochmanRapaport`: the cited theorems `thm:rapaport` and
  `thm:hochman_rapaport` as `Prop`-valued statements, with their degenerate instances; the first is
  the hypothesis of case (iii) of `thm:main2`.
* `Projection`: the canonical projections `\overline{π}` and `π`, `eq:canonical_projection`,
  `eq:commutative_diagram` and `eq:self_affine_set_def` for `X = π(Σ)`.
* `SingularValue`: the singular value function `φ^s` of `sec:Singular_value_function`, its
  sub-multiplicativity, and `α_1 = max{|a|, |b|}`, `α_1 α_2 = |a| |b|` on diagonal and
  anti-diagonal matrices.
* `Pressure`: the sums `∑_{|𝐢| = n} φ^s(A_𝐢)` and the pressure `P(𝖠, s)` of `sec:affinity_dim`,
  with the existence of its limit by Fekete's lemma.
* `SecondIterate`: the second iterate `Φ^(2)` and the separation part of
  `thm:two-block-normalisation`.
* `LyapunovDim`: the real-variable part of `thm:main1`, `thm:main_extended` and `thm:main2`:
  `eq:energy_def`, `eq:diml_min2`, the threshold `2 - λ_1/λ_2`, `eq:main_extended1` and
  `eq:main_extended2`.
* `MeasureDim`: pointwise dimension, exact- and double-dimensional measures,
  `thm:exact-dimensional-mixture` and `eq:restricted-projection-dimensions`.
* `MeasureDimDouble`: double-dimensional measures in the sense of `sec:ledrappier_young_formula`
  (two distinct values, each on a set of positive measure), their characterisation by `udimp` and
  `ldimh`, and `thm:exact-dimensional-mixture` in full.
* `Measurable`: measurability of `τ`, `ω`, `\overline{π}` and `π`.
* `Entropy`: block entropies and the Kolmogorov–Sinai entropy `h_0`, with the existence of its
  limit.
* `EntropyFactor`: the two-lift comparison of block entropies behind `thm:entropy_eq_gibbs`.
* `Thermodynamic`: Lyapunov exponents, `eq:eq_state_def`, the potentials `f_{1,s}`, `f_{2,s}`,
  Gibbs measures on `Σ_Z`, the conclusion of `thm:eq_state_is_sum`, the coordinate marginals.
* `Literature`: the literature theorems of the main line as `Prop`s, all proved.
* `Main`: `thm:entropy_eq_gibbs` and the decomposition `eq:proj_eq_is_sum`, `eq:gibbs_proj_dim`
  of the coordinate marginals, for a tuple containing a proximal diagonal generator.
* `Proximal`: proximal matrices and tuples, `thm:box_like_proximal`.
* `Lyapunov`: existence of the limits defining `λ_1`, `λ_2` and `Λ`, `λ_2 ≤ λ_1 < 0`,
  `eq:energy_def`, and `\overline{λ}` as a limit.
* `Grouping`: the grouping map `β` and the measure part of `thm:two-block-normalisation`.
* `MeasureDimBounds`: upper packing and lower Hausdorff dimension of a measure,
  `eq:haus_dim_sum`.
* `General`: `eq:simple_lyapunov`, `thm:eq_state_proj_dim` and `thm:main1` for every proximal
  box-like tuple with rotations.
* `AffinityDim`: the pressure is continuous and strictly decreasing, `P(𝖠, 0) = log N`, the
  affinity dimension `dimaff` as its unique zero.
* `Variational`: `eq:variational`, `0 ≤ P(𝖠, \dim_L)`, the identity
  `φ^s(A_{𝐢|_n}) = max{exp S_n f_{1,s}, exp S_n f_{2,s}}`.
* `Attractor`: continuity of `π`, compactness and uniqueness of `X`, `Φ^(2)` has attractor `X`.
* `SeparationConditions`: the strong separation, strong open set and rectangular open set
  conditions, and their passage to `Φ^(2)`.
* `MassDistribution`: `dim μ ≤ \dim_H A` for an exact-dimensional measure charging `A`.
* `BoxLikeMatrix`: `thm:box_like_sa`.
* `AffinityMain`: `\dim_L ≤ dimaff`, `thm:main1` with `s = dimaff(X)`, `dim(π_*μ) ≤ \dim_H(X)`.
* `Birkhoff`: Birkhoff's pointwise ergodic theorem, through the maximal ergodic theorem.
* `Conditional`: partitions as atom maps, the `σ`-algebra `\widehat{ξ}`, conditional measures,
  conditional information and entropy (`sec:conditional`, `sec:entropies`).
* `ConditionalMeasures`: Rokhlin's disintegration for `condMeas`, integrability of the
  conditional information, `eq:ergodic_entropy_constant`.
* `ConditionalLemmas`: `thm:conditional_measures_of_a_conditional_measure`,
  `thm:double_conditional`, `thm:finer_partition_dirac_mass`.
* `SlowAxis`: the box-like set `Σ'`, `Σ^τ`, `Σ^ω`, the slow axis,
  `thm:lyapunov_exponents_via_g_system`.
* `DimPartitions`: the partitions `ξ_i`, `ξ_1^⊥`, `\overline{ξ}_i`, the entropies `h_i`,
  `\overline{h}_i`, the average measure, ergodicity of the equilibrium state.
* `MeasurablePartitions`: `ξ_i`, `ξ_1^⊥`, `\overline{ξ}_i` are measurable partitions.
* `PartitionIdentities`: `eq:sigma_tau_omega_positive_eq_measure1`, `thm:partitions_xi1`,
  `thm:partition_tau_conj`.
* `SigmaMeasure`: `μ(Σ') = 1`, `eq:lyapunov_exponent_gsystem`,
  `thm:sigma_tau_omega_positive_eq_measure`.
* `GibbsOrientation`: `thm:gibbs_tau_omega_positive`, `eq:orientation-restrictions`.
* `PastEntropy`: `h_0(μ) = h(μ)` and `\overline{h}_0(ν) = h(ν)`, by the chain rule and
  martingale convergence.
* `LiteratureFeng`: the results of Feng as `Prop`s; `FengInfoSum` and `FengInfoSumBar` are
  theorems of the library (`FengIdentity`, `FengIdentityBar`).
* `FengEntropy`: `thm:feng_entropy_as_limit`, `thm:feng_entropy_zero`.
* `ConditionalTwoWays`: transport of conditional measures, `thm:conditional_two_ways`.
* `StrongOpenSetEntropy`: `thm:SOSC_h2_zero`.
* `AverageEntropy`: `thm:overline_h1_zero`, `thm:overline_h1_zero_large`.
* `EquilibriumEntropySmall`: `thm:eq_state_h1_zero`, `thm:eq_state_h2_zero`,
  `thm:orto_partition_dirac`.
* `EquilibriumEntropyLarge`: `thm:overline_h1_large`, `thm:eq_state_h1_large`.
* `MainTwo`: `thm:main_extended` for `0 < s < 2` and the projectively exponentially separated
  case of `thm:main2`.
* `SelfAffineMeasure`: invariant measures `ν = ∑_i p_i (φ_i)_*ν` of the iterated function
  system, for the case `s ≥ 2` of `thm:main_extended`.
* `PressureLarge`: the range `s ≥ 2` of `sec:normalisation`: `φ^s = |det|^{s/2}`,
  `P(𝖠, s) = log ∑_i |det A_i|^{s/2}`, `λ_1 + λ_2 = ∑_i μ([i]) log |det A_i|` and the
  equilibrium equation.
* `BernoulliEntropy`: `h(μ) ≤ H_μ(𝒫)` with equality only for a Bernoulli measure, Gibbs'
  inequality and its equality case.
* `LebesgueOpenSet`: `∑_i |det A_i| ≤ 1` under the strong open set condition, and normalised
  Lebesgue measure on the open set as an invariant measure of exact dimension two.
* `InvariantMeasure`: Hutchinson's uniqueness of the invariant probability measure, and the
  invariance of the projection of a Bernoulli measure.
* `MainExtended`: `thm:main_extended` for `s ≥ 2` and in full.
* `BernoulliEquilibrium`: Bernoulli measures, their invariance, ergodicity and entropy; for
  `s ≥ 2` the equilibrium state exists, is unique and is Bernoulli (`sec:normalisation`).
* `DimensionFormula`: `\dim_H(X) = min{2, dimaff}` under the hypotheses of `thm:main_extended`,
  the statement of Rossi's bound `eq:hausdorff_ergodic_lyapunov`, which `RossiBound` proves, and
  equality in it for the equilibrium state.
* `LiteraturePlanarFeng`, `Planar.FengOne`: Feng's Ledrappier–Young formula for planar
  self-affine systems as a `Prop`, its box-like specialisation, and `thm:feng1`.
* `LiteratureFengKaenmaki`, `IrreducibleEquilibriumTuple`: Feng–Käenmäki, Proposition 1.2, as
  a `Prop`, its reductions, and `thm:irred_eq_state` at the article's scope.
* `Bowen`: Bowen's theorem, the unique ergodic Gibbs measure of a Hölder potential on `Σ_Z`
  (`bowenGibbsExistence`, `existsUnique_ergodic_isGibbsPotential`).
* `FraserJordanJurga`: `thm:eq_state_is_sum` (`fraserJordanJurgaDecomposition_holds`).
* `EquilibriumGibbsStatement`, `Support.RelativeEntropy`, `EquilibriumGibbs`:
  `thm:irred_eq_state` for box-like tuples with rotations and every `s > 0`
  (`equilibriumGibbs`, `System.irred_eq_state_of_withRotations`).
* `MorrisShmerkin`: `eq:simple_lyapunov` (`morrisShmerkinLyapunov_holds`).
* `KittleKogler`: `KittleKoglerDimension` from the vendored library
  (`kittleKoglerDimension_holds`).
* `FengHu`: `FengHuExactDim`, Feng–Hu's Theorem 2.8 for `Ψ` (`fengHuExactDim_holds`).
* `JordanRapaport`: `JordanRapaportDimension` from `ShmerkinLqDimension`
  (`jordanRapaportDimension_of_shmerkin`), along Section 2 of the source.
* `FengLedrappierYoung`: `PlanarFengLedrappierYoung`, `FengLedrappierYoung` and
  `FengLedrappierYoungBar` (`planarFengLedrappierYoung_holds`, `fengLedrappierYoung_holds`,
  `fengLedrappierYoungBar_holds`), along Feng's Sections 4 to 6 in the plane.
* `Shmerkin`: `ShmerkinLqDimension` (`shmerkinLqDimension_holds`), along the source
  (`BoxLike/Shmerkin/`), with Bourgain's structure theorem in a weak form.
* `Fraser`: `thm:fraser` along Fraser's Section 5 (`System.fraserBound_holds`,
  `System.fraserROSC_holds`).
* `Rossi`, `RossiBound`: Rossi's bound `eq:hausdorff_ergodic_lyapunov` (`System.rossiBound`).
* `QuasiMultiplicative`: Feng–Käenmäki, Proposition 1.2, for irreducible planar tuples
  (`fengKaenmakiNormEquilibrium_holds`, `fengKaenmakiGibbs_holds`, `fengKaenmakiUnique_holds`).
* `LiteratureRemarks`: Feng–Hu, Theorem 2.8, and the uniqueness part of `thm:irred_eq_state` as
  `Prop`s, both proved.
* `NoSeparation`: the remark before `thm:eq_state_proj_dim` that the coordinate marginals are
  double-dimensional without separation, and the uniqueness of `μ^(2)` in
  `thm:two-block-normalisation`.
* `UniqueEquilibrium`: uniqueness of the `s`-equilibrium state of a box-like tuple with
  rotations for every `s > 0` (`thm:irred_eq_state`), with no literature premise.
* `CodingTopology`: `τ`, `ω` as closed embeddings, `β` as a homeomorphism conjugating `σ²` to
  the shift, the natural projection `η` of `sec:two_sided_shift_space`; `η_*` is injective and
  preserves ergodicity in both directions.
* `NaturalExtension`: `η_* : ℳ_σ(Σ) → ℳ_σ(Σ^+)` is a bijection (`sec:two_sided_shift_space`),
  by the Carathéodory extension of a content on the clopen future sets.
* `LocalDimBounds`: pointwise dimensions on `ℝ^d` lie in `[0, d]` almost everywhere,
  exact-dimensional iff `\overline{\dim}_p = \underline{\dim}_H`, the first line of
  `eq:haus_dim_sum` for all finite Borel measures, the second line of
  `eq:dimension_measure_def`.
* `EquilibriumExistence`: an `s`-equilibrium state exists for every `s ≥ 0`, by the construction
  of Misiurewicz (tex lines 2105 to 2106, Käenmäki); irreducibility is not needed.
* `InvariantMeasures`: the invariant measures form a compact set in the weak-star topology and
  `h_0 + Λ(𝖠, ·, s)` is upper semicontinuous on it, so it attains its maximum (tex lines 2105
  to 2218, Käenmäki).
* `Example`: a separate rational two-map system accompanying `sec:dimension_of_projections`,
  whose coordinate marginals have two distinct pointwise dimensions, with `thm:main1` and
  `thm:main2` for `0 < s ≤ 1`; `ex:projection_double_dimensional` is `PrescribedExample`.
* `Classification`: `thm:A_classification`, proved for arbitrary planar tuples.
* `PressureZ`: the pressure `P_Z(f)` of `sec:gibbs_measures`,
  `P(𝖠, s) = P_Z(f_{1,s}) = P_Z(f_{2,s})`, `μ_2 = flip_*μ_1` and the integral formulas of
  `thm:eq_state_is_sum`.
* `GibbsProperties`: the equilibrium state is sub-multiplicative, not quasi-Bernoulli and not
  Bernoulli; the doubling inequality of Gibbs measures, `μ_1 ≠ μ_2`, `μ_1 ⟂ μ_2` and
  `eq:tau_cylinder`.
* `SetDimensions`: the upper and lower Minkowski dimensions and the packing dimension of sets,
  to which `sec:affinity_dim` refers, with `\dim_H E ≤ \underline{\dim}_M E`,
  `\dim_H E ≤ \dim_P E ≤ \overline{\dim}_M E`, bi-Lipschitz invariance, and the equality of the
  two Minkowski dimensions for a super-multiplicative covering count.
* `PackingDimMeasure`: the first line of `eq:dimension_measure_def`,
  `\overline{\dim}_p(μ) = inf {\dim_P A : μ(ℝ^d \ A) = 0}`, for every finite Borel measure on
  `ℝ^d`, through the packing dimension of `SetDimensions`.
* `ModifiedAffinity`: Fraser's modified singular value function, the modified pressure and the
  modified affinity dimension `dimmaff(X)` of `sec:affinity_dim`, with
  `dimmaff(X) ≤ dimaff(X)` for every box-like set.
* `FalconerBound`: Falconer's bound `\overline{\dim}_M X ≤ min{2, dimaff(X)}` for every box-like
  self-affine set, and with it `eq:hausdorff_affinity_upper_bound`.
* `FraserChain`: `thm:fraser` as the statements `System.FraserBound` and `System.FraserROSC`,
  which `Fraser` proves, with `\dim_P X = \overline{\dim}_M X`; the chain
  `\dim_H X = \dim_P X = \dim_M X = dimaff(X)` of the introduction, and the squeeze
  `dimmaff(X) = dimaff(X)` from the first part of `thm:fraser`.
* `NoOverlapExampleFree`: the algebraic part of `prop:ssc_no_overlap_not_pesc`: algebraically
  independent parameters and the freeness of the semigroup generated by the projective system.
* `NoOverlapExample`: `prop:ssc_no_overlap_not_pesc` and the paragraph after its proof, from
  the theorem of Bárány and Käenmäki in the form the article uses and in the form of the source.
* `BaranyKaenmaki`: `NoOverlap.BaranyKaenmakiPair` (`NoOverlap.baranyKaenmakiPair_holds`), a
  corrected Theorem 2.1 of the source, and `prop:ssc_no_overlap_not_pesc` with no hypothesis.
* `BaranyKaenmakiCounterexample`: Theorem 2.1 of the source as stated is false
  (`NoOverlap.not_baranyKaenmakiTheorem`).
* `Subsystem`: finite subsystems `(φ_{w_k})_k` of a box-like system, the absence of exact
  overlaps of their coordinate maps, and their unique coding inside a feasible open set.
* `TypicalWords`: the families `W_n` of diagonal words of the proof of `thm:main2`, with
  `log #W_n / n → h_0(μ)` and the coordinate contraction rates `λ_1`, `λ_2`.
* `HomogeneousSubsystem`: the Bernoulli measure `ν_n` of a subsystem with a common diagonal
  linear part, its Lyapunov exponents, entropy, coded measures and coordinate marginals.
* `SubsystemEntropy`: the entropies `h_i(ν_n)` through Kittle–Kogler and Feng's formulas, and
  the exact dimension of `ν_n`.
* `MainTwoFree`: `thm:main2` under no projective exact overlaps, the dimension chain under its
  hypotheses, and the application to the example of `prop:ssc_no_overlap_not_pesc`.
* `MainTwoEndpoint`: `thm:main2` for the full parameter range by the counting route, with the
  determinant argument at affinity dimension two.
* `EntropyEqualityEndpoint`: the literal conditional-entropy statement of
  `thm:entropy_eq_gibbs`.
* `MatrixTuple`: pressure, Lyapunov exponents, energy, equilibrium states and Gibbs bounds of
  an arbitrary tuple of real `2 × 2` matrices; the box-like objects are those of `S.mat`.
* `SMBStatement`: the statement of the Shannon–McMillan–Breiman theorem for the two-sided shift.
* `OpenQuestion`: `q:coincident-projection-dimensions` recorded as a proposition.
* `OrientationLift`: the lift `(τ_*μ + ω_*μ)/2` of a Bernoulli measure as a stationary Markov
  measure, its mixing and ergodicity, and mixing on cylinders implies ergodicity.
* `ProjectionLarge`: `thm:eq_state_proj_dim` for `s ≥ 2` through the lift, and for every `s > 0`.
* `MainOneFull`: `thm:main1` for every value of the affinity dimension.
* `OseledetsFiltration`, `OseledetsBridge`: the article's Oseledets set `Σ'` and filtration for a
  tuple, its existence for box-like tuples, `thm:lyapunov_exponents_via_g_system` for every
  choice, and the agreement of the partitions and entropies with the rate-defined ones.
* `PrescribedExample`: `ex:projection_double_dimensional`: the parameters, the pressure and the
  affinity dimension, the translation cube, strong separation, the volume argument for
  projective exponential separation, the Markov measure, the entropy and the exponents, and the
  assembled example (`PrescribedExample.projection_double_dimensional`).
* `Aligned`: `thm:box_like_sa` as one tuple-level statement; proofs along the prose route of
  `thm:box_like_proximal`,
  `prop:ssc_no_overlap_not_pesc`, `thm:sigma_tau_omega_positive_eq_measure`,
  `thm:conditional_two_ways` and `eq:haus_dim_sum`, and the all-anti-diagonal example of
  `sec:irreducibility`.
* `SMB`, `ShannonMcMillanBreiman`: the Shannon–McMillan–Breiman theorem by Breiman's argument.
* `KolmogorovSinai`: the entropy of finite partitions, the Kolmogorov–Sinai entropy as a supremum
  over finite Borel partitions, and the generator theorem for the two-sided shift.
* `CylinderEntropy`: `thm:feng_entropy_kolmogorov_sinai` for box-like systems.
* `TupleEquilibrium`, `TupleEquilibriumLarge`, `TupleEquilibriumNorm`,
  `TupleEquilibriumExistence`: equilibrium states of arbitrary tuples of invertible matrices: the
  variational inequality, existence, the case `s ≥ 2`, the norm and rescaled potentials, the
  reduction to the one-sided shift, and ergodicity of a unique equilibrium state.
* `TupleErgodicEquilibrium`: an ergodic equilibrium state exists for every tuple of invertible
  matrices and every `s ≥ 0`.
* `IrreducibleEquilibrium`: `thm:irred_eq_state` for irreducible box-like systems, from
  `FengKaenmakiGibbs` and `FengKaenmakiUnique`, which `QuasiMultiplicative` proves.
* `BernoulliGrouping`, `TwoBlockNormalisation`: grouping a Bernoulli measure into pairs, and
  `thm:two-block-normalisation` in one endpoint with its consequences.
* `FengIdentity`, `FengIdentityBar`: Feng's information-sum identity (Lemma 4.6, (4.16)) for
  the planar and the projective partitions, proved along Feng's Lemmas 4.4 and 4.5; the
  predicates `FengInfoSum` and `FengInfoSumBar` hold.
* `Kingman`, `FurstenbergKesten`: Kingman's subadditive ergodic theorem, proved from Birkhoff's
  theorem, and the Furstenberg–Kesten limits along the backward products of an invertible tuple.
* `Planar`: arbitrary planar self-affine systems: Oseledets' theorem, the partitions `ξ_i` and
  entropies `h_i`, `thm:feng_entropy_as_limit`, `thm:feng_entropy_kolmogorov_sinai` and
  `thm:feng_entropy_zero` for every planar self-affine set, Falconer's bound, and the invariance
  under linear changes of coordinates (`ChangeOfBasis`).
* `Support`: supporting claims of the prose: mixing of `Σ_Z`, the one-sided projection,
  convexity of the pressure, Gibbs doubling, conditional information, Hölder pressure and Gibbs
  uniqueness on `Σ_Z`, the introduction's threshold remarks and the potentials at `s = 2`.
* `MainTwoProse`: `thm:main2` along the prose proof.
* `MainTwoProse.ThresholdBound`: `rem:threshold_bound`, the lower bound
  `min{dimaff(X), 2 - λ₁/λ₂}` without separation beyond the absence of exact overlaps.
* `MainTwoProse.ProjectionDimension`: without projective exact overlaps and for `dimaff(X) < 2`,
  both coordinate projections of `X` have Hausdorff and Minkowski dimension `min{1, dimaff(X)}`
  (the paragraph of the proof of `thm:main2` after Kittle–Kogler).
* `ModifiedAffinityEquality`: `dimmaff(X) = dimaff(X)` for `dimaff(X) < 2` without the threshold or
  the strong open set condition (`sec:intro_fraser`).
* `MainTwoProse.HomogeneousAffinity`, `MainTwoProse.AxisSeparationSubsystem`,
  `MainTwoProse.ProjExpBranch`: case (iii) of `thm:main2`: the affinity dimension of a homogeneous
  diagonal subsystem, the exponential separation of its induced axis systems from the projective
  gap, and Rapaport's theorem applied to the subsystems (`System.main2_pesc`).
* `MainTwoProse.Full`: `thm:main2` as printed, with its three cases and the furthermore clause
  (`System.main2_full`, `System.main2_furthermore`).
* `ProjectiveLineSystem`: `FengLedrappierYoung` implies `FengLedrappierYoungBar`
  (`fengLedrappierYoungBar_of_fengLedrappierYoung`).
-/
public import BoxLike.Orientation
public import BoxLike.Coding
public import BoxLike.System
public import BoxLike.Separation
public import BoxLike.AxisSeparation
public import BoxLike.ProjExpNoOverlaps
public import BoxLike.Projection
public import BoxLike.SingularValue
public import BoxLike.Pressure
public import BoxLike.SecondIterate
public import BoxLike.LyapunovDim
public import BoxLike.MeasureDim
public import BoxLike.Measurable
public import BoxLike.Entropy
public import BoxLike.EntropyFactor
public import BoxLike.Thermodynamic
public import BoxLike.Literature
public import BoxLike.Main
public import BoxLike.Proximal
public import BoxLike.Lyapunov
public import BoxLike.Grouping
public import BoxLike.MeasureDimBounds
public import BoxLike.MeasureDimDouble
public import BoxLike.General
public import BoxLike.AffinityDim
public import BoxLike.Variational
public import BoxLike.Attractor
public import BoxLike.SeparationConditions
public import BoxLike.MassDistribution
public import BoxLike.BoxLikeMatrix
public import BoxLike.AffinityMain
public import BoxLike.Birkhoff
public import BoxLike.Conditional
public import BoxLike.ConditionalMeasures
public import BoxLike.ConditionalLemmas
public import BoxLike.SlowAxis
public import BoxLike.DimPartitions
public import BoxLike.MeasurablePartitions
public import BoxLike.PartitionIdentities
public import BoxLike.SigmaMeasure
public import BoxLike.GibbsOrientation
public import BoxLike.PastEntropy
public import BoxLike.LiteratureFeng
public import BoxLike.FengEntropy
public import BoxLike.ConditionalTwoWays
public import BoxLike.StrongOpenSetEntropy
public import BoxLike.AverageEntropy
public import BoxLike.EquilibriumEntropySmall
public import BoxLike.EquilibriumEntropyLarge
public import BoxLike.MainTwo
public import BoxLike.SelfAffineMeasure
public import BoxLike.PressureLarge
public import BoxLike.BernoulliEntropy
public import BoxLike.LebesgueOpenSet
public import BoxLike.InvariantMeasure
public import BoxLike.MainExtended
public import BoxLike.BernoulliEquilibrium
public import BoxLike.DimensionFormula
public import BoxLike.LiteratureRemarks
public import BoxLike.LiteratureRapaport
public import BoxLike.LiteratureHochmanRapaport
public import BoxLike.NoSeparation
public import BoxLike.UniqueEquilibrium
public import BoxLike.CodingTopology
public import BoxLike.NaturalExtension
public import BoxLike.LocalDimBounds
public import BoxLike.InvariantMeasures
public import BoxLike.EquilibriumExistence
public import BoxLike.Example
public import BoxLike.Classification
public import BoxLike.PressureZ
public import BoxLike.GibbsProperties
public import BoxLike.SetDimensions
public import BoxLike.PackingDimMeasure
public import BoxLike.ModifiedAffinity
public import BoxLike.FalconerBound
public import BoxLike.FraserChain
public import BoxLike.NoOverlapExampleFree
public import BoxLike.NoOverlapExample
public import BoxLike.Subsystem
public import BoxLike.TypicalWords
public import BoxLike.HomogeneousSubsystem
public import BoxLike.SubsystemEntropy
public import BoxLike.MainTwoFree

public import BoxLike.MainTwoEndpoint
public import BoxLike.EntropyEqualityEndpoint
public import BoxLike.MatrixTuple
public import BoxLike.SMBStatement
public import BoxLike.OpenQuestion
public import BoxLike.OrientationLift
public import BoxLike.ProjectionLarge
public import BoxLike.MainOneFull
public import BoxLike.OseledetsFiltration
public import BoxLike.OseledetsBridge
public import BoxLike.PrescribedExample.Defs
public import BoxLike.PrescribedExample.Parameters
public import BoxLike.PrescribedExample.Pressure
public import BoxLike.PrescribedExample.Translations
public import BoxLike.PrescribedExample.Separation
public import BoxLike.PrescribedExample.Geometry
public import BoxLike.PrescribedExample.Measure
public import BoxLike.PrescribedExample.Dimensions
public import BoxLike.PrescribedExample.Main
public import BoxLike.Aligned.SigmaTauOmega
public import BoxLike.Aligned.ConditionalTwoWays
public import BoxLike.Aligned.MeasureDimSets
public import BoxLike.Aligned.BoxLikeProximal
public import BoxLike.Aligned.NoOverlapPESCParams
public import BoxLike.Aligned.NoOverlapPESCFree
public import BoxLike.Aligned.NoOverlapPESC
public import BoxLike.BaranyKaenmaki
public import BoxLike.BaranyKaenmakiCounterexample
public import BoxLike.Aligned.NoOverlapPESCDim
public import BoxLike.SMB.Maker
public import BoxLike.SMB.PastInformation
public import BoxLike.ShannonMcMillanBreiman
public import BoxLike.KolmogorovSinai
public import BoxLike.CylinderEntropy
public import BoxLike.TupleEquilibrium
public import BoxLike.TupleEquilibriumLarge
public import BoxLike.TupleEquilibriumNorm
public import BoxLike.TupleEquilibriumExistence
public import BoxLike.TupleErgodicEquilibrium
public import BoxLike.FengIdentity
public import BoxLike.FengIdentityBar
public import BoxLike.Planar.FengIdentity
public import BoxLike.Planar.AffinityDim
public import BoxLike.Planar.FalconerBound
public import BoxLike.Kingman
public import BoxLike.FurstenbergKesten
public import BoxLike.Planar.OseledetsTheoremDirection
public import BoxLike.Planar.OseledetsTheorem
public import BoxLike.Planar.FengGeneral
public import BoxLike.Aligned.BoxLikeSA
public import BoxLike.Planar.ChangeOfBasis
public import BoxLike.Support.PotentialsAtTwo
public import BoxLike.Support.IntroductionClaims
public import BoxLike.LiteraturePlanarFeng
public import BoxLike.Planar.FengOne
public import BoxLike.LiteratureFengKaenmaki
public import BoxLike.IrreducibleEquilibriumTuple
public import BoxLike.Bowen.Defs
public import BoxLike.Bowen.PartitionBounds
public import BoxLike.Bowen.PeriodicMeasures
public import BoxLike.Bowen.Limit
public import BoxLike.Bowen.Ergodic
public import BoxLike.Bowen.Main
public import BoxLike.FraserJordanJurga.Gibbs
public import BoxLike.FraserJordanJurga.Decomposition
public import BoxLike.FraserJordanJurga.Lyapunov
public import BoxLike.FraserJordanJurga.Main
public import BoxLike.EquilibriumGibbsStatement
public import BoxLike.Support.RelativeEntropy
public import BoxLike.EquilibriumGibbs
public import BoxLike.MorrisShmerkin
public import BoxLike.KittleKogler
public import BoxLike.FengHu
public import BoxLike.JordanRapaport
public import BoxLike.FengLedrappierYoung
public import BoxLike.Shmerkin
public import BoxLike.Fraser.Upper
public import BoxLike.Fraser.UpperBound
public import BoxLike.Fraser.LowerStop
public import BoxLike.Fraser.LowerCover
public import BoxLike.Fraser.Lower
public import BoxLike.Fraser.Main
public import BoxLike.Rossi
public import BoxLike.RossiBound
public import BoxLike.QuasiMultiplicative.Defs
public import BoxLike.QuasiMultiplicative.Irreducible
public import BoxLike.QuasiMultiplicative.Uniqueness
public import BoxLike.QuasiMultiplicative.GibbsMeasurePressure
public import BoxLike.QuasiMultiplicative.GibbsMeasurePeriodic
public import BoxLike.QuasiMultiplicative.GibbsMeasureErgodic
public import BoxLike.QuasiMultiplicative.GibbsMeasure
public import BoxLike.QuasiMultiplicative.Main
public import BoxLike.IrreducibleEquilibrium
public import BoxLike.BernoulliGrouping
public import BoxLike.TwoBlockNormalisation
public import BoxLike.Planar.System
public import BoxLike.Planar.Oseledets
public import BoxLike.Planar.Partitions
public import BoxLike.Planar.Specialisation
public import BoxLike.Planar.Lyapunov
public import BoxLike.Planar.FengEntropy
public import BoxLike.Planar.OseledetsChoice
public import BoxLike.Planar.CylinderEntropy
public import BoxLike.Planar.FengPartitions
public import BoxLike.MainTwoProse.Pigeonhole
public import BoxLike.MainTwoProse.TypicalWordsSMB
public import BoxLike.MainTwoProse.DiagonalSubsystem
public import BoxLike.MainTwoProse.ScalarFeng
public import BoxLike.MainTwoProse.EntropyThreshold
public import BoxLike.MainTwoProse.OpenSetBranch
public import BoxLike.MainTwoProse.PastIndependence
public import BoxLike.MainTwoProse.SubsystemEntropies
public import BoxLike.MainTwoProse.Endpoint
public import BoxLike.MainTwoProse.ThresholdBound
public import BoxLike.MainTwoProse.HomogeneousAffinity
public import BoxLike.MainTwoProse.AxisSeparationSubsystem
public import BoxLike.MainTwoProse.ProjExpBranch
public import BoxLike.MainTwoProse.Full
public import BoxLike.MainTwoProse.ProjectionDimension
public import BoxLike.ModifiedAffinityEquality
public import BoxLike.Support.SubshiftMixing
public import BoxLike.Support.OneSidedProjection
public import BoxLike.Support.PressureConvexity
public import BoxLike.Support.GibbsDoubling
public import BoxLike.Support.ConditionalInformation
public import BoxLike.Support.HolderPressure
public import BoxLike.Support.GibbsUniqueness
public import BoxLike.Support.PlanarProjection
public import BoxLike.ProjectiveLineSystem
public import BoxLike.Rapaport
