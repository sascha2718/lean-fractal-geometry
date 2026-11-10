module

/-
Hochman–Rapaport's theorem on planar self-affine sets with overlaps, `thm:hochman_rapaport` of
`sec:intro_setting`, as a `Prop`-valued definition. Nothing in the library uses it; it is
recorded because the article numbers it.

* `PlanarSystem.affDist`, `PlanarSystem.affDist_eq_zero_iff`: the distance of two compositions
  `φ_𝐢`, `φ_𝐣` in the affine coefficients, which vanishes exactly when `φ_𝐢 = φ_𝐣`.
* `PlanarSystem.affGap`, `PlanarSystem.affGap_le`: the least distance between distinct words of
  length `n`, `⊤` for the empty minimum.
* `PlanarSystem.ExpSeparation`, `PlanarSystem.expSeparation_iff_frequently`: the exponential
  separation condition of `sec:intro_setting`, and its form with infinitely many lengths.
* `HochmanRapaportDimension`: the statement, with its source record.
* `IsProximalMatrix.exists_ne_zero_mulVec_eq_smul`,
  `HochmanRapaportDimension.not_tupleStronglyIrreducible_of_subsingleton`,
  `HochmanRapaportDimension.degenerate_subsingleton`: a proximal matrix has a real eigenvector,
  so a one-letter proximal system is not strongly irreducible and the statement is vacuous at
  one letter.
-/
public import BoxLike.Classification
public import BoxLike.Planar.AffinityDim
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDimension

@[expose] public section

namespace BoxLike

open Matrix
open scoped ENNReal Matrix.Norms.L2Operator

universe u

namespace PlanarSystem

variable {ι : Type*} (P : PlanarSystem ι)

/-! ### The distance in the affine coefficients -/

/-- The distance of `φ_𝐢` and `φ_𝐣` in the affine coefficients: the `ℓ²` operator norm of the
difference `A_𝐢 - A_𝐣` of the linear parts plus the supremum norm of the difference
`φ_𝐢(0) - φ_𝐣(0)` of the translation parts (`sec:intro_setting`, tex lines 388 to 397, and the
norm on affine coefficients of tex line 1460). -/
noncomputable def affDist (w w' : List ι) : ℝ :=
  ‖MatrixTuple.word P.mat w - MatrixTuple.word P.mat w'‖ + ‖P.phiWord w 0 - P.phiWord w' 0‖

/-- The coefficient distance is non-negative. -/
theorem affDist_nonneg (w w' : List ι) : 0 ≤ P.affDist w w' :=
  add_nonneg (norm_nonneg _) (norm_nonneg _)

/-- The coefficient distance is symmetric. -/
theorem affDist_comm (w w' : List ι) : P.affDist w w' = P.affDist w' w := by
  rw [affDist, affDist, norm_sub_rev, norm_sub_rev (P.phiWord w 0)]

/-- The coefficient distance vanishes exactly when the two compositions are the same affine
map: `φ_𝐢(z) = φ_𝐢(0) + A_𝐢 z`. -/
theorem affDist_eq_zero_iff (w w' : List ι) : P.affDist w w' = 0 ↔ P.phiWord w = P.phiWord w' := by
  constructor
  · intro h
    rw [affDist] at h
    have h1 : ‖MatrixTuple.word P.mat w - MatrixTuple.word P.mat w'‖ = 0 :=
      le_antisymm (by linarith [norm_nonneg (P.phiWord w 0 - P.phiWord w' 0)]) (norm_nonneg _)
    have h2 : ‖P.phiWord w 0 - P.phiWord w' 0‖ = 0 :=
      le_antisymm (by linarith [norm_nonneg (MatrixTuple.word P.mat w - MatrixTuple.word P.mat w')])
        (norm_nonneg _)
    rw [norm_eq_zero, sub_eq_zero] at h1 h2
    funext z
    rw [P.phiWord_apply w, P.phiWord_apply w', h1, h2]
  · intro h
    have h0 : P.phiWord w 0 = P.phiWord w' 0 := by rw [h]
    have hmat : MatrixTuple.word P.mat w = MatrixTuple.word P.mat w' := by
      refine Matrix.toLin'.injective (LinearMap.ext fun u => ?_)
      simp only [Matrix.toLin'_apply]
      have hz := congrFun h (ofVec u)
      rw [P.phiWord_apply w, P.phiWord_apply w', h0, add_right_inj, toVec_ofVec] at hz
      simpa using congrArg toVec hz
    rw [affDist, hmat, h0, sub_self, sub_self, norm_zero, norm_zero, add_zero]

/-- The least coefficient distance between distinct words of length `n`; the minimum of the
empty set is `⊤`. -/
noncomputable def affGap (n : ℕ) : ℝ≥0∞ :=
  ⨅ (w : List ι) (w' : List ι) (_ : w.length = n) (_ : w'.length = n) (_ : w ≠ w'),
    ENNReal.ofReal (P.affDist w w')

/-- The least distance is at most the distance of any two distinct words of length `n`. -/
theorem affGap_le {n : ℕ} {w w' : List ι} (hw : w.length = n) (hw' : w'.length = n)
    (hne : w ≠ w') : P.affGap n ≤ ENNReal.ofReal (P.affDist w w') :=
  iInf_le_of_le w <| iInf_le_of_le w' <| iInf_le_of_le hw <| iInf_le_of_le hw' <| iInf_le _ hne

/-- The exponential separation condition of `sec:intro_setting` (tex lines 388 to 397), with
the distance in the affine coefficients: there are `c > 0` and a strictly increasing sequence
`(n_k)` with `min_{𝐢 ≠ 𝐣 ∈ Λ^{n_k}} ‖φ_𝐢 - φ_𝐣‖ ≥ c^{n_k}` for every `k`. -/
def ExpSeparation : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n : ℕ → ℕ, StrictMono n ∧ ∀ k, ENNReal.ofReal (c ^ n k) ≤ P.affGap (n k)

/-- The exponential separation condition in the form: the least coefficient distance between
distinct words of length `n` is at least `c^n` for infinitely many `n`. -/
theorem expSeparation_iff_frequently :
    P.ExpSeparation ↔
      ∃ c : ℝ, 0 < c ∧ ∃ᶠ n : ℕ in Filter.atTop, ENNReal.ofReal (c ^ n) ≤ P.affGap n := by
  constructor
  · rintro ⟨c, hc, n, hn, h⟩
    exact ⟨c, hc, Filter.frequently_atTop.2 fun N => ⟨n N, hn.id_le N, h N⟩⟩
  · rintro ⟨c, hc, h⟩
    obtain ⟨φ, hφ, hP⟩ := Filter.extraction_of_frequently_atTop h
    exact ⟨c, hc, φ, hφ, hP⟩

/-- For one map there is one word of each length, so the least distance is `⊤`. -/
theorem affGap_eq_top_of_subsingleton [Subsingleton ι] (n : ℕ) : P.affGap n = ⊤ := by
  refine le_antisymm le_top ?_
  refine le_iInf fun w => le_iInf fun w' => le_iInf fun hw => le_iInf fun hw' =>
    le_iInf fun hne => ?_
  exact absurd (List.ext_get (hw.trans hw'.symm) fun k _ _ => Subsingleton.elim _ _) hne

/-- A one-map system is exponentially separated. -/
theorem expSeparation_of_subsingleton [Subsingleton ι] : P.ExpSeparation :=
  ⟨1, one_pos, id, strictMono_id, fun n => by rw [P.affGap_eq_top_of_subsingleton]; exact le_top⟩

end PlanarSystem

/-- Hochman–Rapaport, *Hausdorff dimension of planar self-affine sets and measures with
overlaps*, J. Eur. Math. Soc. 24 (2022), Theorem 1.1: `thm:hochman_rapaport` of
`sec:intro_setting` (tex lines 388 to 404). The statement was read in arXiv:1904.09812v2
(3 May 2019), Section 1.1; the journal version was not consulted.

Source. `Φ = {φ_i}_{i ∈ Λ}` is a finite system of invertible affine contractions of `ℝ²`,
`φ_i(x) = A_i x + b_i`, with attractor `X`, and `φ_𝐢 = φ_{i_1} ∘ ⋯ ∘ φ_{i_n}` for
`𝐢 = i_1 ⋯ i_n ∈ Λ^n`. Non-conformality: there is no coordinate system in which all the maps
`φ_i` are similarities. Total irreducibility: there is no finite set of lines `{ℓ_1, …, ℓ_n}`
in `ℝ²` invariant under all the matrices `A_i`. Exponential separation: for a left-invariant
metric `d` on the group of invertible affine maps of `ℝ²` derived from a Riemannian metric,
there is `c > 0` such that for every `n` and every pair `𝐢 ≠ 𝐣 ∈ Λ^n`,
`d(φ_𝐢, φ_𝐣) > c^n`; the source remarks that the weaker property, with infinitely many `n`
in place of every `n`, suffices for its results, and that the existence of such a `c` does not
depend on the choice of `d`. Theorem 1.1: if `Φ` has no common fixed point, satisfies the
non-conformality and total irreducibility assumptions, and is exponentially separated, then
`dim X = min{2, dim_a X}`, with `dim_a X` the affinity dimension and `dim` the Hausdorff
dimension.

The statement. The alphabet is a finite non-empty type `ι` and the system a
`PlanarSystem ι`: invertible linear parts `A_i` with `‖A_i‖ < 1`, the contractions of
`sec:box_like_self_affine`; its attractor is `PlanarSystem.attractor` and its affinity dimension
`PlanarSystem.dimaff`, the zero of the singular value pressure of `(A_i)`. Total irreducibility
is `TupleStronglyIrreducible P.mat`. The article states the theorem for proximal strongly
irreducible systems, and the statement takes `TupleProximal P.mat`, some product `A_𝐢` having
two real eigenvalues of distinct moduli, in place of non-conformality: a proximal tuple is
non-conformal, since in a coordinate system in which every `φ_i` is a similarity every product
`A_𝐢` is conjugate to a scalar multiple of an orthogonal matrix, whose eigenvalues have equal
modulus. The absence of a common fixed point is `¬ ∃ z, ∀ i, φ_i(z) = z`. Exponential
separation is `PlanarSystem.ExpSeparation`: the distance in the affine coefficients,
`‖A_𝐢 - A_𝐣‖ + ‖φ_𝐢(0) - φ_𝐣(0)‖` (`PlanarSystem.affDist`), in place of the metric `d`,
the bound `≥ c^n` in place of `> c^n`, and a strictly increasing sequence of lengths in place
of every `n`, the weaker form the source allows. The conclusion is
`dim_H X = min{2, dimaff(X)}` in `ℝ≥0∞`, with the supremum metric on the plane, which has
the same Hausdorff dimension as the Euclidean metric.

Deviations. The coefficient distance in place of the left-invariant Riemannian metric: with
`g = φ_𝐢⁻¹ ∘ φ_𝐣`, left invariance gives `d(φ_𝐢, φ_𝐣) = d(id, g)`, and on a neighbourhood of
the identity `d(id, ·)` is comparable to the coefficient distance to the identity, while the
coefficient norms of `φ_𝐢` and of `φ_𝐢⁻¹` along words of length `n` are at most exponential in
`n`; so along words of length `n` the two distances are comparable up to factors exponential
in `n`, and the condition in one is the condition in the other with a different `c`. The
article passes from the coefficient norm to the condition at tex line 1460. The hypothesis
`TupleProximal` is stronger than non-conformality, as explained, so the statement is a
consequence of the source's theorem. The source's definition with every `n` is replaced by the
form with infinitely many `n` that the source says suffices, which is the article's definition.

Degenerate instance. A one-letter system is never both proximal and strongly irreducible: a
proximal power of its matrix has a real eigenvector, whose orbit under the matrix is a finite
invariant set of lines (`HochmanRapaportDimension.not_tupleStronglyIrreducible_of_subsingleton`),
so the statement is vacuous at one letter (`HochmanRapaportDimension.degenerate_subsingleton`).
A single contraction also has a fixed point, so the third hypothesis fails there as well. -/
def HochmanRapaportDimension : Prop :=
  ∀ {ι : Type u} [Fintype ι] [Nonempty ι] (P : PlanarSystem ι), TupleProximal P.mat →
    TupleStronglyIrreducible P.mat → (¬ ∃ z : ℝ × ℝ, ∀ i, P.phi i z = z) → P.ExpSeparation →
    dimH P.attractor = ENNReal.ofReal (min 2 P.dimaff)

/-! ### The degenerate instance of one letter -/

/-- A proximal matrix has a real eigenvector: its eigenvalue `l₁` is a root of the
characteristic polynomial, so `l₁ I - B` is singular. -/
theorem IsProximalMatrix.exists_ne_zero_mulVec_eq_smul {B : Matrix (Fin 2) (Fin 2) ℝ}
    (hB : IsProximalMatrix B) : ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ ∃ l : ℝ, B *ᵥ v = l • v := by
  obtain ⟨l₁, l₂, -, htr, hdet⟩ := isProximalMatrix_iff_trace_det.1 hB
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  have h0 : (l₁ • (1 : Matrix (Fin 2) (Fin 2) ℝ) - B).det = 0 := by
    rw [Matrix.det_fin_two]
    simp
    linear_combination (-l₁) * htr + hdet
  obtain ⟨v, hv, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  refine ⟨v, hv, l₁, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hBv
  exact hBv.symm

namespace HochmanRapaportDimension

variable {ι : Type*}

/-- A tuple indexed by at most one letter whose matrix is invertible and has a power with a
real eigenvector `v` is not strongly irreducible: the lines of `v, B v, …, B^{k-1} v` form a
finite invariant set. -/
theorem not_tupleStronglyIrreducible_of_pow [Subsingleton ι] {A : ι → Matrix (Fin 2) (Fin 2) ℝ}
    (i : ι) (hdet : (A i).det ≠ 0) {k : ℕ} (hk : 0 < k) {v : Fin 2 → ℝ} (hv : v ≠ 0) {l : ℝ}
    (h : (A i ^ k) *ᵥ v = l • v) : ¬ TupleStronglyIrreducible A := by
  classical
  have hdetpow : ∀ j : ℕ, (A i ^ j).det ≠ 0 := fun j => by
    rw [Matrix.det_pow]; exact pow_ne_zero j hdet
  refine not_not.2 ⟨(Finset.range k).image fun j => (A i ^ j) *ᵥ v, ?_, ?_, ?_⟩
  · exact ⟨(A i ^ 0) *ᵥ v, Finset.mem_image_of_mem _ (Finset.mem_range.2 hk)⟩
  · intro u hu
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hu
    exact mulVec_ne_zero_of_det_ne_zero (hdetpow j) hv
  · intro i' u hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hu
    rw [Finset.mem_range] at hj
    rw [Subsingleton.elim i' i, Matrix.mulVec_mulVec, ← pow_succ']
    rcases Nat.lt_or_ge (j + 1) k with hlt | hge
    · exact ⟨(A i ^ (j + 1)) *ᵥ v, Finset.mem_image_of_mem _ (Finset.mem_range.2 hlt), 1,
        (one_smul _ _).symm⟩
    · have heq : j + 1 = k := by omega
      refine ⟨(A i ^ 0) *ᵥ v, Finset.mem_image_of_mem _ (Finset.mem_range.2 hk), l, ?_⟩
      rw [heq, h, pow_zero, Matrix.one_mulVec]

/-- The degenerate test of the premise: a one-letter planar system that is proximal is not
strongly irreducible, since its proximal power has a real eigenvector. -/
theorem not_tupleStronglyIrreducible_of_subsingleton [Subsingleton ι] (P : PlanarSystem ι)
    (h : TupleProximal P.mat) : ¬ TupleStronglyIrreducible P.mat := by
  obtain ⟨w, hw, hB⟩ := h
  obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil w hw
  have hrep : w.map P.mat = List.replicate w.length (P.mat i) :=
    List.eq_replicate_iff.2 ⟨List.length_map .., fun B hB => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hB
      rw [Subsingleton.elim j i]⟩
  rw [hrep, List.prod_replicate] at hB
  obtain ⟨v, hv, l, hl⟩ := hB.exists_ne_zero_mulVec_eq_smul
  exact not_tupleStronglyIrreducible_of_pow i (P.det_ne_zero i) (List.length_pos_of_ne_nil hw)
    hv hl

/-- The hypotheses of `HochmanRapaportDimension` are contradictory at one letter: no one-letter
system is proximal and strongly irreducible. -/
theorem degenerate_subsingleton [Subsingleton ι] (P : PlanarSystem ι) :
    ¬ (TupleProximal P.mat ∧ TupleStronglyIrreducible P.mat) := fun h =>
  not_tupleStronglyIrreducible_of_subsingleton P h.1 h.2

end HochmanRapaportDimension

end BoxLike
