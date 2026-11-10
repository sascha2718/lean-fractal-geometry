module

/-
Feng–Käenmäki, Proposition 1.2, in the form of the source (the potential `‖·‖^q` on the one-sided
shift), as a `Prop`-valued definition; proved in `BoxLike/QuasiMultiplicative/Main.lean`
(`fengKaenmakiNormEquilibrium_holds`). `FengKaenmakiGibbs` and `FengKaenmakiUnique` are its
box-like specialisations.

* `FengKaenmakiNormEquilibrium`: the statement, with its source record.
* `FengKaenmakiNormEquilibrium.degenerate_quarterTurn`: the degenerate instance of one letter.
* `FengKaenmakiNormEquilibrium.twoSided`: the reduction to the two-sided shift.
* `FengKaenmakiNormEquilibrium.svf`: the singular value potential for `0 < s < 2`.
* `FengKaenmakiNormEquilibrium.fengKaenmakiGibbs`, `FengKaenmakiNormEquilibrium.fengKaenmakiUnique`:
  the box-like specialisations.
-/
public import BoxLike.Literature
public import BoxLike.LiteratureRemarks
public import BoxLike.TupleEquilibriumExistence
public import BoxLike.TupleEquilibriumLarge
public import BoxLike.TupleEquilibriumNorm

@[expose] public section

namespace BoxLike

open MeasureTheory Filter Topology
open scoped Matrix Matrix.Norms.L2Operator

universe u

/-- Feng–Käenmäki, Proposition 1.2, for real planar
invertible tuples, in the form of the source.

Source. De-Jun Feng and Antti Käenmäki, *Equilibrium states of the pressure function for
products of matrices*, Discrete Contin. Dyn. Syst. 30 (2011), Proposition 1.2. The statement was
read in arXiv:1009.3129v1 (16 September 2010), p. 3, with its setting
on pp. 1–2; the journal version was not consulted.

Source hypotheses and conclusions. `F` is `ℝ` or `ℂ`; `{M_i}_{i=1}^ℓ` is a family of `d × d`
matrices over `F`, irreducible over `F^d` (their Definition 1.1: no non-zero proper linear
subspace `V` with `M_i V ⊆ V` for all `i`); `Σ` is the one-sided full shift over `{1, …, ℓ}`;
`M_σ(Σ)` the `σ`-invariant Borel probability measures; `P(q) = lim_n n⁻¹ log ∑_{|J| = n} ‖M_J‖^q`
(their (1.1)) with `M_J = M_{j_1} ⋯ M_{j_n}` and the standard matrix norm;
`M_*(μ) = lim_n n⁻¹ ∑_{|J| = n} μ([J]) log ‖M_J‖` (their (1.2)); `h(μ)` the measure-theoretic
entropy; a `q`-equilibrium state is `μ ∈ M_σ(Σ)` with `P(q) = q M_*(μ) + h(μ)` (their (1.4)).
Conclusion: for each `q > 0`, `P` has a unique `q`-equilibrium state `μ_q`, it satisfies
`C⁻¹ exp(-n P(q)) ‖M_J‖^q ≤ μ_q([J]) ≤ C exp(-n P(q)) ‖M_J‖^q` for all `n` and `J ∈ Σ_n`
(their (1.6)), and `P` is differentiable on `(0, ∞)` with `P'(q) = M_*(μ_q)`.

Specialisation. `F = ℝ`, `d = 2`, and the matrices are invertible, the article's `GL^N`; the
alphabet is a finite type `ι` with the discrete `σ`-algebra (`MeasurableSingletonClass`), and
`Σ = ℕ → ι` with `shiftPlus`; irreducibility is `TupleIrreducible`, no common invariant line.
The norm is the `ℓ²` operator norm: any two norms on `2 × 2` matrices are equivalent, so `P`,
`M_*` and the set of `q`-equilibrium states do not depend on the norm, and the Gibbs property
holds for one norm exactly when it holds for every norm, with another constant. The entropy is
`entropyPlus`, the entropy of the generating partition into the cylinders `[i]`, which is the
measure-theoretic entropy by the Kolmogorov–Sinai theorem. `P` and `M_*` are `limUnder` of the
source's sequences; the limits exist (`MatrixTuple.tendsto_normPressure`,
`MatrixTuple.tendsto_normLyapPlus`, `tendsto_entropyPlus`), so these are the source's values and
not junk values. The statement is weaker than the source in four respects: it does not assert
the existence of `μ_q`, which the library proves (`MatrixTuple.exists_isEquilibriumState`); it
asserts the Gibbs property for `n ≥ 1` only; it omits the differentiability of `P`; and it
excludes singular matrices, for which `P(q) = -∞` is possible and `Real.log 0 = 0` would make a
transcription false. For every invariant probability measure `ν` that is a `q`-equilibrium
state it concludes the Gibbs property of `ν` and that every invariant `q`-equilibrium state is
`ν`.

Degenerate instances. For the empty alphabet `TupleIrreducible` fails, every line being
invariant, so the statement is silent. For one letter the only invariant probability measure
on `Σ` is the Dirac mass; for the quarter turn, an irreducible orthogonal matrix, `P(q) = 0`,
the Dirac mass is the equilibrium state and has the Gibbs property with `C = 1`
(`FengKaenmakiNormEquilibrium.degenerate_quarterTurn` proves the conclusion there).

Relation to the library. The existing predicates `FengKaenmakiGibbs` and `FengKaenmakiUnique`
are the box-like specialisations of the singular value form for `0 < s < 2`; they follow from
this statement (`FengKaenmakiNormEquilibrium.fengKaenmakiGibbs`,
`FengKaenmakiNormEquilibrium.fengKaenmakiUnique`) through the two-sided-shift reduction and the
rescaling `A'_i = |det A_i|^{(s-1)/(2-s)} A_i` of tex lines 2123 to 2127, both proved in
`BoxLike/TupleEquilibriumNorm.lean`. The statement covers all irreducible invertible planar
tuples, the scope at which the article states `thm:irred_eq_state`. Downstream use:
`MatrixTuple.irred_eq_state_of_fengKaenmaki`.

Proof in the library. `fengKaenmakiNormEquilibrium_holds` (`BoxLike/QuasiMultiplicative/Main.lean`)
proves the statement: the norm of an irreducible tuple is quasi-multiplicative
(`MatrixTuple.normQuasiMultiplicative_of_irreducible`), the potential `‖·‖^q` has an ergodic
Gibbs measure on the two-sided shift (`normGibbsExistence`), and every invariant
`q`-equilibrium state equals it (`MatrixTuple.IsNormEquilibrium.eq_of_hasNormGibbs`). -/
def FengKaenmakiNormEquilibrium : Prop :=
  ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (A : ι → Matrix (Fin 2) (Fin 2) ℝ), (∀ i, (A i).det ≠ 0) → TupleIrreducible A →
    ∀ {q : ℝ}, 0 < q → ∀ (ν : Measure (ℕ → ι)) [IsProbabilityMeasure ν],
    MeasurePreserving shiftPlus ν ν → MatrixTuple.IsNormEquilibriumPlus A q ν →
    MatrixTuple.HasNormGibbsPlus A q ν ∧
      ∀ (ν' : Measure (ℕ → ι)) [IsProbabilityMeasure ν'], MeasurePreserving shiftPlus ν' ν' →
        MatrixTuple.IsNormEquilibriumPlus A q ν' → ν' = ν

namespace FengKaenmakiNormEquilibrium

/-! ### The degenerate instance of one letter -/

/-- The quarter turn `J = [[0, -1], [1, 0]]`. -/
def quarterTurn : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- The quarter turn is orthogonal: `Jᵀ J = I`. -/
theorem quarterTurn_conjTranspose_mul_self : quarterTurnᴴ * quarterTurn = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quarterTurn, Matrix.mul_apply, Fin.sum_univ_two]

/-- Multiplication by the orthogonal matrix `J` preserves the operator norm. -/
theorem norm_quarterTurn_mul (M : Matrix (Fin 2) (Fin 2) ℝ) : ‖quarterTurn * M‖ = ‖M‖ := by
  have h : ‖quarterTurn * M‖ * ‖quarterTurn * M‖ = ‖M‖ * ‖M‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, ← Matrix.l2_opNorm_conjTranspose_mul_self,
      Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc quarterTurnᴴ,
      quarterTurn_conjTranspose_mul_self, Matrix.one_mul]
  exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).1 h

/-- The quarter turn has no real eigenvector. -/
theorem tupleIrreducible_quarterTurn : TupleIrreducible fun _ : Unit => quarterTurn := by
  rintro ⟨v, hv, h⟩
  obtain ⟨c, hc⟩ := h ()
  have e0 := congrFun hc 0
  have e1 := congrFun hc 1
  simp [quarterTurn, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
  have hv1 : v 1 = -(c * v 0) := by linarith
  rw [hv1] at e1
  have h2 : v 0 * (1 + c * c) = 0 := by linear_combination e1
  have h0 : v 0 = 0 := (mul_eq_zero.1 h2).resolve_right (by nlinarith [mul_self_nonneg c])
  have h1 : v 1 = 0 := by rw [hv1, h0, mul_zero, neg_zero]
  exact hv (funext fun k => by fin_cases k <;> simp [h0, h1])

/-- The degenerate test of the premise: for the one-letter tuple of the quarter turn and every
`q > 0`, every invariant probability measure on `Σ^+` has the Gibbs property with `C = 1`,
since `‖J^n‖ = 1` and `P(q) = 0`, and any two probability measures on `Σ^+ = ℕ → Unit`
coincide. So the conclusion of `FengKaenmakiNormEquilibrium` holds at this instance. -/
theorem degenerate_quarterTurn {q : ℝ} (ν : Measure (ℕ → Unit)) [IsProbabilityMeasure ν] :
    MatrixTuple.HasNormGibbsPlus (fun _ : Unit => quarterTurn) q ν ∧
      ∀ (ν' : Measure (ℕ → Unit)) [IsProbabilityMeasure ν'], ν' = ν := by
  have hnorm : ∀ w : List Unit, ‖MatrixTuple.word (fun _ : Unit => quarterTurn) w‖ = 1 := by
    intro w
    induction w with
    | nil => simp
    | cons i w ih => rw [MatrixTuple.word_cons, norm_quarterTurn_mul, ih]
  have hP : MatrixTuple.normPressure (fun _ : Unit => quarterTurn) q = 0 := by
    have hs : ∀ n, MatrixTuple.normSum (fun _ : Unit => quarterTurn) q n = 1 := fun n => by
      simp [MatrixTuple.normSum, hnorm]
    simp only [MatrixTuple.normPressure, hs, Real.log_one, zero_div]
    exact tendsto_const_nhds.limUnder_eq
  have huniv : ∀ {n : ℕ} (w : Fin n → Unit), futureCylinder w = Set.univ := fun w =>
    Set.eq_univ_of_forall fun y k => Subsingleton.elim _ _
  refine ⟨⟨1, one_pos, fun n _ w => ?_⟩, fun ν' _ => ?_⟩
  · rw [huniv, probReal_univ, hP, hnorm]
    simp
  · ext B hB
    rcases Set.eq_empty_or_nonempty B with rfl | ⟨x, hx⟩
    · simp
    · have : B = Set.univ := Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
      rw [this, measure_univ, measure_univ]

/-! ### The reductions -/

variable {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {A : ι → Matrix (Fin 2) (Fin 2) ℝ}

/-- The two-sided-shift reduction: on `Σ = ℤ → ι`, an invariant `q`-equilibrium state of the
potential `‖·‖^q` has the Gibbs property and is the only invariant `q`-equilibrium state. The
image `η_*μ` is an invariant `q`-equilibrium state on `Σ^+` with the same cylinder masses, and
`η_*` is injective on the invariant measures. -/
theorem twoSided (h : FengKaenmakiNormEquilibrium.{u}) (hA : ∀ i, (A i).det ≠ 0)
    (hirr : TupleIrreducible A) {q : ℝ} (hq : 0 < q) {μ : Measure (ℤ → ι)}
    [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ)
    (heq : MatrixTuple.IsNormEquilibrium A q μ) :
    MatrixTuple.HasNormGibbs A q μ ∧
      ∀ μ' : Measure (ℤ → ι), IsProbabilityMeasure μ' → MeasurePreserving (shift 1) μ' μ' →
        MatrixTuple.IsNormEquilibrium A q μ' → μ' = μ := by
  obtain ⟨hG, hU⟩ := h A hA hirr hq (μ.map eta) (measurePreserving_shiftPlus_map_eta hμ)
    ((MatrixTuple.isNormEquilibriumPlus_map_eta_iff μ).2 heq)
  refine ⟨(MatrixTuple.hasNormGibbsPlus_map_eta_iff μ).1 hG, fun μ' hμ' hinv' heq' => ?_⟩
  exact map_eta_injective hinv' hμ (hU (μ'.map eta) (measurePreserving_shiftPlus_map_eta hinv')
    ((MatrixTuple.isNormEquilibriumPlus_map_eta_iff μ').2 heq'))

/-- The singular value potential for `0 < s < 2`, tex lines 2123 to 2127: an invariant
`s`-equilibrium state of an irreducible tuple of invertible planar matrices has the Gibbs bounds
of `thm:irred_eq_state` and is the only invariant `s`-equilibrium state. For `0 < s ≤ 1` the
premise applies with `q = s`, since `φ^s = ‖·‖^s`; for `1 < s < 2` it applies to the rescaled
tuple `A'_i = |det A_i|^{(s-1)/(2-s)} A_i` with `q = 2 - s`, since
`‖A'_𝐢‖^{2-s} = φ^s(A_𝐢)` and `A'` is invertible and irreducible. -/
theorem svf (h : FengKaenmakiNormEquilibrium.{u}) (hA : ∀ i, (A i).det ≠ 0)
    (hirr : TupleIrreducible A) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) {μ : Measure (ℤ → ι)}
    [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ)
    (heq : MatrixTuple.IsEquilibriumState A s μ) :
    MatrixTuple.HasGibbsBounds A s μ ∧
      ∀ μ' : Measure (ℤ → ι), IsProbabilityMeasure μ' → MeasurePreserving (shift 1) μ' μ' →
        MatrixTuple.IsEquilibriumState A s μ' → μ' = μ := by
  have : Nonempty ι := ⟨(nonempty_of_isProbabilityMeasure μ).some 0⟩
  rcases le_or_gt s 1 with hs1 | hs1
  · obtain ⟨hG, hU⟩ := h.twoSided hA hirr hs0 hμ
      ((MatrixTuple.isEquilibriumState_iff_isNormEquilibrium hA hμ hs0.le hs1).1 heq)
    refine ⟨(MatrixTuple.hasGibbsBounds_iff_hasNormGibbs hA hs0.le hs1).2 hG,
      fun μ' hμ' hinv' heq' => ?_⟩
    exact hU μ' hμ' hinv'
      ((MatrixTuple.isEquilibriumState_iff_isNormEquilibrium hA hinv' hs0.le hs1).1 heq')
  · obtain ⟨hG, hU⟩ := h.twoSided (MatrixTuple.det_rescale_ne_zero hA s)
      (MatrixTuple.tupleIrreducible_rescale hA s hirr) (by linarith : (0 : ℝ) < 2 - s) hμ
      ((MatrixTuple.isEquilibriumState_iff_rescale hA hμ hs1 hs2).1 heq)
    refine ⟨(MatrixTuple.hasGibbsBounds_iff_rescale hA hs1 hs2).2 hG,
      fun μ' hμ' hinv' heq' => ?_⟩
    exact hU μ' hμ' hinv' ((MatrixTuple.isEquilibriumState_iff_rescale hA hinv' hs1 hs2).1 heq')

end FengKaenmakiNormEquilibrium

/-! ### The existing predicates -/

/-- `FengKaenmakiNormEquilibrium` implies the library's `FengKaenmakiGibbs`, its specialisation to
box-like systems and `0 < s < 2`. -/
theorem FengKaenmakiNormEquilibrium.fengKaenmakiGibbs (h : FengKaenmakiNormEquilibrium.{u}) :
    FengKaenmakiGibbs.{u} := by
  intro ι _ _ _ S hirr s hs0 hs2 μ _ hμ heq
  exact (h.svf S.det_mat_ne_zero hirr hs0 hs2 hμ heq).1

/-- `FengKaenmakiNormEquilibrium` implies the library's `FengKaenmakiUnique`, its specialisation to
box-like systems and `0 < s < 2`. -/
theorem FengKaenmakiNormEquilibrium.fengKaenmakiUnique (h : FengKaenmakiNormEquilibrium.{u}) :
    FengKaenmakiUnique.{u} := by
  intro ι _ _ _ S hirr s hs0 hs2 μ μ' _ _ hμ hμ' heq heq'
  exact ((h.svf S.det_mat_ne_zero hirr hs0 hs2 hμ' heq').2 μ inferInstance hμ heq)

end BoxLike
