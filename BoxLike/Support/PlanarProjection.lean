module

/-
The canonical projection of a general planar system of `BoxLike/Planar/System.lean` as the
canonical projection `π = π^+ ∘ η` of its affine system in the Euclidean plane, as
`sec:box_like_self_affine` defines it for every planar self-affine set (tex lines 733 to 741).

* `PlanarSystem.planeTrans`: the translations in `EuclideanSpace ℝ (Fin 2)`.
* `PlanarSystem.toPlane_phi`, `PlanarSystem.toPlane_phiWord`: the maps and their compositions.
* `PlanarSystem.toPlane_proj`: `π` of the planar system is `MatrixTuple.canonicalProj`.
-/
public import BoxLike.Planar.System
public import BoxLike.Support.OneSidedProjection

@[expose] public section

open Filter Topology Matrix
open scoped Matrix.Norms.L2Operator


namespace BoxLike.PlanarSystem

variable {ι : Type*} (P : PlanarSystem ι)

/-- The translations of a planar system in the Euclidean plane. -/
noncomputable def planeTrans (i : ι) : EuclideanSpace ℝ (Fin 2) := System.toPlane (P.v i)

/-- The maps of a planar system are the affine maps of `(P.mat, P.planeTrans)`. -/
theorem toPlane_phi (i : ι) (z : ℝ × ℝ) :
    System.toPlane (P.phi i z) =
      MatrixTuple.affineMap P.mat P.planeTrans i (System.toPlane z) := by
  simp only [phi, MatrixTuple.affineMap, planeTrans, System.toPlane]
  rw [planeLin_toLp, ← WithLp.toLp_add]
  congr 1
  ext j; fin_cases j <;> simp [ofVec, toVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The compositions of a planar system are those of `(P.mat, P.planeTrans)`. -/
theorem toPlane_phiWord (w : List ι) (z : ℝ × ℝ) :
    System.toPlane (P.phiWord w z) =
      MatrixTuple.affineWord P.mat P.planeTrans w (System.toPlane z) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [toPlane_phi, ih]

/-- The canonical projection of a planar system is `π = π^+ ∘ η` of the affine system
`(P.mat, P.planeTrans)`. -/
theorem toPlane_proj [Finite ι] (x : ℤ → ι) :
    System.toPlane (P.proj x) = MatrixTuple.canonicalProj P.mat P.planeTrans x := by
  obtain ⟨r, hA⟩ := MatrixTuple.exists_contractionBound P.mat P.norm_lt_one
  have h1 := (System.continuous_toPlane.tendsto _).comp (P.tendsto_phiWord x)
  have h2 := hA.tendsto_affineWord P.planeTrans (eta x)
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  rw [Function.comp_apply, toPlane_phiWord, futureWord_eq_futureWordPlus, System.toPlane_zero]

end BoxLike.PlanarSystem
