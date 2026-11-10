module

/-
The affinity dimension of a planar self-affine set, `sec:affinity_dim` (tex lines 2042 to 2060
and 2171 to 2172). For a planar system `φ_i(x) = A_i x + v_i` of `BoxLike/Planar/System.lean`,
with `A_i ∈ GL_2(ℝ)` and `‖A_i‖ < 1`, the singular value pressure `P(𝖠, s)` is the pressure
`MatrixTuple.pressure` of the tuple `𝖠 = P.mat`. Under `max_i ‖A_i‖ < 1` it is continuous and
strictly decreasing on `[0, ∞)`, with `P(𝖠, 0) = log N ≥ 0` and `P(𝖠, s) → -∞`
(`BoxLike/Support/PressureConvexity.lean`), and `dimaff(𝖠)` is its unique zero on `[0, ∞)`. The
convention `dimaff(X) = dimaff(𝖠)` of tex lines 2074 to 2075 is built into the definition: the
affinity dimension of a planar system depends on its linear parts alone.

* `PlanarSystem.tendsto_pressure`: the pressure is the limit of tex lines 2050 to 2052.
* `PlanarSystem.existsUnique_pressure_eq_zero`: the pressure of `P.mat` has a unique zero on
  `[0, ∞)`.
* `PlanarSystem.dimaff`, `PlanarSystem.dimaff_nonneg`, `PlanarSystem.pressure_dimaff`,
  `PlanarSystem.dimaff_eq`: the affinity dimension and its characterisation.
* `PlanarSystem.pressure_neg_of_dimaff_lt`, `PlanarSystem.pressure_pos_of_lt_dimaff`,
  `PlanarSystem.le_dimaff_of_pressure_nonneg`, `PlanarSystem.dimaff_le_of_pressure_nonpos`: the
  sign of the pressure on either side of `dimaff(𝖠)`.
* `PlanarSystem.dimaff_pos`: a system of at least two maps has positive affinity dimension.
* `PlanarSystem.dimaff_congr`: `dimaff(X) = dimaff(𝖠)`, a function of the linear parts.
* `System.toPlanar_pressure`, `System.toPlanar_dimaff`: the pressure and the affinity dimension
  of a box-like system are those of its planar system.
-/
public import BoxLike.Planar.System
public import BoxLike.Support.PressureConvexity

@[expose] public section

namespace BoxLike

open Filter Topology

namespace PlanarSystem

variable {ι : Type*} [Fintype ι] [Nonempty ι] (P : PlanarSystem ι)

/-- Tex lines 2145 to 2152: the singular value pressure of the linear parts of a planar system is
the limit `P(𝖠, s) = lim_n n⁻¹ log ∑_{|𝐢| = n} φ^s(A_𝐢)` for `s ≥ 0`, which exists by Fekete's
lemma. -/
theorem tendsto_pressure {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun n : ℕ => Real.log (MatrixTuple.svfSum P.mat s n) / n) atTop
      (𝓝 (MatrixTuple.pressure P.mat s)) :=
  MatrixTuple.Convexity.tendsto_pressure P.det_ne_zero hs

/-- Tex lines 2154 to 2157: the singular value pressure `s ↦ P(𝖠, s)` of the linear parts of a
planar system has a unique zero on `[0, ∞)`, since the matrices are invertible and
`max_i ‖A_i‖ < 1`. -/
theorem existsUnique_pressure_eq_zero :
    ∃! s : ℝ, 0 ≤ s ∧ MatrixTuple.pressure P.mat s = 0 :=
  MatrixTuple.pressure_existsUnique_eq_zero P.det_ne_zero P.norm_lt_one

/-- The affinity dimension `dimaff(X) = dimaff(𝖠)` of a planar self-affine set
(`sec:affinity_dim`, tex lines 2057 to 2060 and 2171 to 2172): the unique `s ≥ 0` with
`P(𝖠, s) = 0`, for the tuple `𝖠 = P.mat` of linear parts. -/
noncomputable def dimaff : ℝ := P.existsUnique_pressure_eq_zero.exists.choose

/-- `dimaff(𝖠) ≥ 0` (`sec:affinity_dim`). -/
theorem dimaff_nonneg : 0 ≤ P.dimaff :=
  P.existsUnique_pressure_eq_zero.exists.choose_spec.1

/-- `P(𝖠, dimaff(𝖠)) = 0` (`sec:affinity_dim`). -/
theorem pressure_dimaff : MatrixTuple.pressure P.mat P.dimaff = 0 :=
  P.existsUnique_pressure_eq_zero.exists.choose_spec.2

/-- The affinity dimension is the only zero of the pressure on `[0, ∞)` (`sec:affinity_dim`). -/
theorem dimaff_eq {s : ℝ} (hs : 0 ≤ s) (h : MatrixTuple.pressure P.mat s = 0) :
    P.dimaff = s :=
  P.existsUnique_pressure_eq_zero.unique ⟨P.dimaff_nonneg, P.pressure_dimaff⟩ ⟨hs, h⟩

/-- The pressure is negative above the affinity dimension, since it is strictly decreasing on
`[0, ∞)` (tex lines 2057 and 2058). -/
theorem pressure_neg_of_dimaff_lt {t : ℝ} (ht : P.dimaff < t) :
    MatrixTuple.pressure P.mat t < 0 := by
  have h := MatrixTuple.pressure_strictAntiOn_Ici P.det_ne_zero P.norm_lt_one
    (Set.mem_Ici.2 P.dimaff_nonneg) (Set.mem_Ici.2 (P.dimaff_nonneg.trans ht.le)) ht
  rwa [P.pressure_dimaff] at h

/-- The pressure is positive on `[0, dimaff(𝖠))` (tex lines 2057 and 2058). -/
theorem pressure_pos_of_lt_dimaff {t : ℝ} (ht0 : 0 ≤ t) (ht : t < P.dimaff) :
    0 < MatrixTuple.pressure P.mat t := by
  have h := MatrixTuple.pressure_strictAntiOn_Ici P.det_ne_zero P.norm_lt_one
    (Set.mem_Ici.2 ht0) (Set.mem_Ici.2 P.dimaff_nonneg) ht
  rwa [P.pressure_dimaff] at h

/-- An exponent `s` with `P(𝖠, s) ≥ 0` is at most the affinity dimension. -/
theorem le_dimaff_of_pressure_nonneg {s : ℝ} (h : 0 ≤ MatrixTuple.pressure P.mat s) :
    s ≤ P.dimaff := by
  by_contra hlt
  exact (not_le.2 (P.pressure_neg_of_dimaff_lt (not_le.1 hlt))) h

/-- An exponent `s ≥ 0` with `P(𝖠, s) ≤ 0` is at least the affinity dimension. -/
theorem dimaff_le_of_pressure_nonpos {s : ℝ} (hs : 0 ≤ s)
    (h : MatrixTuple.pressure P.mat s ≤ 0) : P.dimaff ≤ s := by
  by_contra hlt
  exact (not_le.2 (P.pressure_pos_of_lt_dimaff hs (not_le.1 hlt))) h

/-- A planar system of at least two maps has positive affinity dimension, since
`P(𝖠, 0) = log N > 0` (tex line 2058). -/
theorem dimaff_pos [Nontrivial ι] : 0 < P.dimaff := by
  refine lt_of_le_of_ne P.dimaff_nonneg fun h0 => ?_
  have h := P.pressure_dimaff
  rw [← h0, MatrixTuple.pressure_at_zero] at h
  have hcard : (1 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.one_lt_card
  exact (Real.log_pos hcard).ne' h

/-- The convention `dimaff(X) = dimaff(𝖠)` of tex lines 2074 to 2075: two planar systems with
the same linear parts have the same affinity dimension. -/
theorem dimaff_congr {Q : PlanarSystem ι} (h : P.mat = Q.mat) : P.dimaff = Q.dimaff := by
  refine P.dimaff_eq Q.dimaff_nonneg ?_
  rw [h]
  exact Q.pressure_dimaff

end PlanarSystem

namespace System

variable {ι : Type*} (S : System ι)

/-- The singular value pressure of a box-like system is the pressure of the linear parts of its
planar system. -/
theorem toPlanar_pressure [Fintype ι] (s : ℝ) :
    MatrixTuple.pressure S.toPlanar.mat s = S.pressure s := rfl

/-- The affinity dimension of a box-like system, `System.dimaff` of `BoxLike/AffinityDim.lean`,
is the affinity dimension of its planar system (`sec:affinity_dim`). -/
theorem toPlanar_dimaff [Fintype ι] [Nonempty ι] : S.toPlanar.dimaff = S.dimaff :=
  S.toPlanar.dimaff_eq S.dimaff_nonneg S.pressure_dimaff

end System

end BoxLike
