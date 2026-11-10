module

/-
The shared vocabulary of the proof of Bowen's theorem in `BoxLike/Bowen/`: the existence of an
ergodic Gibbs measure for a Hölder potential on the mixing sub-shift `Σ_Z`, which
`sec:gibbs_measures` asserts (tex lines 2382 to 2384) with a citation of Sarig's notes.

* `GibbsUpTo`: the Gibbs bounds of `IsGibbsPotential` for the cylinders of length at most `N`.
* `isGibbsPotential_iff_forall_gibbsUpTo`: the Gibbs property is the conjunction of the bounds
  up to every length.
-/
public import BoxLike.Support.GibbsDoubling

@[expose] public section

namespace BoxLike

open MeasureTheory

variable {ι : Type*} [MeasurableSpace ι] {o : ι → ZMod 2}
  {f : (ℤ → ι × ZMod 2) → ℝ} {ν : Measure (ℤ → ι × ZMod 2)} {P C : ℝ}

/-- The Gibbs bounds of `sec:gibbs_measures` with constants `P` and `C` for the cylinders of
length at most `N`: `C⁻¹ exp(-nP + S_n f(𝐢)) ≤ ν([𝐢|_n]) ≤ C exp(-nP + S_n f(𝐢))` for all
`𝐢 ∈ Σ_Z` and `1 ≤ n ≤ N`. -/
def GibbsUpTo (o : ι → ZMod 2) (f : (ℤ → ι × ZMod 2) → ℝ) (ν : Measure (ℤ → ι × ZMod 2))
    (P C : ℝ) (N : ℕ) : Prop :=
  0 < C ∧ ∀ y ∈ subshift o, ∀ n : ℕ, 0 < n → n ≤ N →
    C⁻¹ * Real.exp (-(n * P) + birkhoffSum (shift 1) f n y) ≤
        ν.real (cylinder fun k : Fin n => y k) ∧
      ν.real (cylinder fun k : Fin n => y k) ≤
        C * Real.exp (-(n * P) + birkhoffSum (shift 1) f n y)

/-- The Gibbs property of `sec:gibbs_measures` holds exactly when the Gibbs bounds hold up to
every length `N`, with the same constants. -/
theorem isGibbsPotential_iff_forall_gibbsUpTo :
    IsGibbsPotential o f ν P C ↔ ∀ N : ℕ, GibbsUpTo o f ν P C N := by
  constructor
  · rintro ⟨hC, h⟩ N
    exact ⟨hC, fun y hy n hn _ => h y hy n hn⟩
  · intro h
    exact ⟨(h 0).1, fun y hy n hn => (h n).2 y hy n hn le_rfl⟩

end BoxLike
