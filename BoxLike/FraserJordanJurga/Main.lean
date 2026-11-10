module

/-
`thm:eq_state_is_sum` (Fraser–Jordan–Jurga, J. Fractal Geom. 7 (2020), Lemma 1.3 and
Corollaries 1.5 and 1.6), the predicate `FraserJordanJurgaDecomposition` of
`BoxLike/Literature.lean`, assembled from the five steps of its proof. No literature premise is
used.

1. Bowen's theorem gives the ergodic `s`-Gibbs measure `μ_1` carried by `Σ_Z` for `f_{1,s}`, and
   `μ_2 = flip_*μ_1` is the ergodic `s`-Gibbs measure for `f_{2,s}`
   (`System.exists_isGibbs_potential₁`, `System.isGibbs_potential₂_map_flipAxis`,
   `BoxLike/FraserJordanJurga/Gibbs.lean`).
2. The image `q_*μ_1` on `Σ` is an ergodic probability measure with the Gibbs bounds of
   `thm:irred_eq_state` (`ergodic_map_unCode`, `System.hasGibbsBounds_map_unCode`).
3. Every invariant probability measure `μ` with these bounds is `q_*μ_1`
   (`System.eq_of_hasGibbsBounds`, `BoxLike/FraserJordanJurga/Decomposition.lean`).
4. The four decompositions of `q_*μ_1` (`map_unCode_eq_tau`, `map_unCode_eq_omega`,
   `map_unCode_eq₁`, `map_unCode_eq₂`).
5. The two Lyapunov identities `λ_1(𝖠, q_*μ_1) = \overline{λ}(𝖠, μ_1)` and
   `λ_2(𝖠, q_*μ_1) = \overline{λ}(𝖠, flip_*μ_1)` (`System.lyapunov_map_unCode_of_isGibbs`,
   `BoxLike/FraserJordanJurga/Lyapunov.lean`).

The assembly first takes the statement of step 5 as the hypothesis `hlyap`
(`fraserJordanJurgaDecomposition_of_lyapunov`) and then discharges it.

* `System.gibbsDecomposition_map_unCode`: `q_*μ_1` has the decomposition with `μ_1` and
  `flip_*μ_1`, given the two Lyapunov identities.
* `System.eq_map_unCode_of_hasGibbsBounds`: step 3 for the measure `μ_1` of step 1.
* `System.exists_gibbsDecomposition_of_lyapunov`: the conclusion of `thm:eq_state_is_sum` for one
  system and one measure, given the Lyapunov identities.
* `fraserJordanJurgaDecomposition_of_lyapunov`: `FraserJordanJurgaDecomposition` from the
  statement of `System.lyapunov_map_unCode_of_isGibbs`.
* `fraserJordanJurgaDecomposition_holds`: `FraserJordanJurgaDecomposition` is a theorem.
-/
public import BoxLike.FraserJordanJurga.Decomposition
public import BoxLike.FraserJordanJurga.Gibbs
public import BoxLike.FraserJordanJurga.Lyapunov

@[expose] public section

namespace BoxLike

open MeasureTheory

universe u

namespace System

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (S : System ι) {s : ℝ}

/-- `thm:eq_state_is_sum` for the measure `q_*μ_1`: if `μ_1` is an ergodic Gibbs probability
measure carried by `Σ_Z` for `f_{1,s}` and the Lyapunov exponents of `q_*μ_1` are
`\overline{λ}(𝖠, μ_1)` and `\overline{λ}(𝖠, flip_*μ_1)`, then `q_*μ_1` has the four
decompositions with the `s`-Gibbs measures `μ_1` and `μ_2 = flip_*μ_1`. -/
theorem gibbsDecomposition_map_unCode (μ₁ : Measure (ℤ → ι × ZMod 2))
    [IsProbabilityMeasure μ₁] (herg : Ergodic (shift 1) μ₁) (hsupp : μ₁ (subshift S.o)ᶜ = 0)
    (hg : IsGibbs S.o (S.potential₁ s) μ₁)
    (hl₁ : S.lyapunov₁ (μ₁.map unCode) = S.lyapBar μ₁)
    (hl₂ : S.lyapunov₂ (μ₁.map unCode) = S.lyapBar (μ₁.map flipAxis)) :
    S.GibbsDecomposition s (μ₁.map unCode) μ₁ (μ₁.map flipAxis) where
  prob₁ := inferInstance
  prob₂ := inferInstance
  ergodic₁ := herg
  ergodic₂ := ergodic_map_flipAxis herg
  supp₁ := hsupp
  supp₂ := map_flipAxis_subshift_compl hsupp
  gibbs₁ := hg
  gibbs₂ := S.isGibbs_potential₂_map_flipAxis hg
  eq_tau := map_unCode_eq_tau hsupp
  eq_omega := map_unCode_eq_omega hsupp
  eq₁ := map_unCode_eq₁ hsupp
  eq₂ := map_unCode_eq₂ hsupp
  lyapunov₁_eq := hl₁
  lyapunov₂_eq := hl₂

/-- `thm:eq_state_is_sum`, uniqueness: for `0 < s < 2`, every invariant probability measure on `Σ`
with the Gibbs bounds of `thm:irred_eq_state` is the image `q_*μ_1` of the ergodic `s`-Gibbs
measure `μ_1`, since `q_*μ_1` is ergodic and has the same bounds. -/
theorem eq_map_unCode_of_hasGibbsBounds (hs0 : 0 < s) (hs2 : s < 2)
    (μ₁ : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure μ₁] (herg : Ergodic (shift 1) μ₁)
    (hsupp : μ₁ (subshift S.o)ᶜ = 0) (hg : IsGibbs S.o (S.potential₁ s) μ₁)
    {μ : Measure (ℤ → ι)} [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ)
    (hgμ : S.HasGibbsBounds s μ) : μ = μ₁.map unCode :=
  S.eq_of_hasGibbsBounds hμ (ergodic_map_unCode herg) hgμ
    (S.hasGibbsBounds_map_unCode hs0 hs2 hsupp hg)

/-- `thm:eq_state_is_sum` for one system: for a box-like tuple with rotations and `0 < s < 2`,
every invariant probability measure `μ` with the Gibbs bounds of `thm:irred_eq_state` has the
decomposition with the `s`-Gibbs measures `μ_1` (Bowen's theorem) and `μ_2 = flip_*μ_1`, given
the Lyapunov identities `hlyap` of `System.lyapunov_map_unCode_of_isGibbs` for the ergodic Gibbs
measures for `f_{1,s}`. -/
theorem exists_gibbsDecomposition_of_lyapunov (hrot : S.WithRotations) (hs0 : 0 < s)
    (hs2 : s < 2)
    (hlyap : ∀ (μ₁ : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure μ₁],
      Ergodic (shift 1) μ₁ → μ₁ (subshift S.o)ᶜ = 0 → IsGibbs S.o (S.potential₁ s) μ₁ →
      S.lyapunov₁ (μ₁.map unCode) = S.lyapBar μ₁ ∧
        S.lyapunov₂ (μ₁.map unCode) = S.lyapBar (μ₁.map flipAxis))
    (μ : Measure (ℤ → ι)) [IsProbabilityMeasure μ] (hμ : MeasurePreserving (shift 1) μ μ)
    (hgμ : S.HasGibbsBounds s μ) :
    ∃ μ₁ μ₂ : Measure (ℤ → ι × ZMod 2), S.GibbsDecomposition s μ μ₁ μ₂ := by
  obtain ⟨μ₁, hp, hsupp, herg, hg⟩ := S.exists_isGibbs_potential₁ hrot s
  have heq := S.eq_map_unCode_of_hasGibbsBounds hs0 hs2 μ₁ herg hsupp hg hμ hgμ
  obtain ⟨hl₁, hl₂⟩ := hlyap μ₁ herg hsupp hg
  subst heq
  exact ⟨μ₁, μ₁.map flipAxis, S.gibbsDecomposition_map_unCode μ₁ herg hsupp hg hl₁ hl₂⟩

end System

/-- `thm:eq_state_is_sum`, the predicate `FraserJordanJurgaDecomposition`, from the statement of
`System.lyapunov_map_unCode_of_isGibbs`: for every ergodic Gibbs probability measure `μ_1` carried
by `Σ_Z` for `f_{1,s}`, `λ_1(𝖠, q_*μ_1) = \overline{λ}(𝖠, μ_1)` and
`λ_2(𝖠, q_*μ_1) = \overline{λ}(𝖠, flip_*μ_1)`. The hypothesis `S.HasProximalDiagonal` of the
predicate is not used. -/
theorem fraserJordanJurgaDecomposition_of_lyapunov
    (hlyap : ∀ {ι : Type u} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (S : System ι), S.WithRotations → ∀ {s : ℝ}, 0 < s → s < 2 →
      ∀ (μ₁ : Measure (ℤ → ι × ZMod 2)) [IsProbabilityMeasure μ₁], Ergodic (shift 1) μ₁ →
      μ₁ (subshift S.o)ᶜ = 0 → IsGibbs S.o (S.potential₁ s) μ₁ →
      S.lyapunov₁ (μ₁.map unCode) = S.lyapBar μ₁ ∧
        S.lyapunov₂ (μ₁.map unCode) = S.lyapBar (μ₁.map flipAxis)) :
    FraserJordanJurgaDecomposition.{u} := by
  intro ι _ _ _ S hrot _ s hs0 hs2 μ _ hμ hgμ
  exact S.exists_gibbsDecomposition_of_lyapunov hrot hs0 hs2
    (fun μ₁ _ => hlyap S hrot hs0 hs2 μ₁) μ hμ hgμ

/-- `thm:eq_state_is_sum` (Fraser–Jordan–Jurga, Lemma 1.3 and Corollaries 1.5 and 1.6), the
predicate `FraserJordanJurgaDecomposition` of `BoxLike/Literature.lean`, as a theorem of the
library: for a box-like tuple with rotations and `0 < s < 2`, every invariant probability measure
`μ` on `Σ` with the Gibbs bounds of `thm:irred_eq_state` is `μ = q_*μ_1` for the ergodic
`s`-Gibbs measure `μ_1` of Bowen's theorem, has the four decompositions with `μ_1` and
`μ_2 = flip_*μ_1`, and satisfies `λ_1(𝖠, μ) = \overline{λ}(𝖠, μ_1)` and
`λ_2(𝖠, μ) = \overline{λ}(𝖠, μ_2)`. No literature premise is used. -/
theorem fraserJordanJurgaDecomposition_holds : FraserJordanJurgaDecomposition.{u} := by
  refine fraserJordanJurgaDecomposition_of_lyapunov ?_
  intro ι _ _ _ S hrot s hs0 hs2 μ₁ _ herg hsupp hg
  exact S.lyapunov_map_unCode_of_isGibbs hrot hs0 hs2 μ₁ herg hsupp hg

end BoxLike
