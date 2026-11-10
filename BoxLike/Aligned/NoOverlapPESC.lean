module

/-
`prop:ssc_no_overlap_not_pesc` of `sec:exponential_separation`, assembled along its proof from the
theorem of Bárány and Käenmäki in the form the article uses, `BaranyKaenmakiPair`.

The steps of the proof and the declarations that carry them:

* the pair `(λ, t)` of Bárány–Käenmäki with `Δ_n ≤ C_0 exp(-n²)` for all `n ≥ 1`:
  `BaranyKaenmakiPair` (`BoxLike.NoOverlapExample`), proved in `BoxLike.BaranyKaenmaki`
  (`baranyKaenmakiPair_holds`);
* the parameters, outside the countable union of proper algebraic hypersurfaces over
  `ℚ(λ, t)`: `exists_params_not_mem_exceptionalSet`,
  `algebraicIndependent_iff_not_mem_exceptionalSet` (`BoxLike.Aligned.NoOverlapPESCParams`);
* the standing hypotheses: `Params.lam_ne_r₁`, `Params.proximal`, `Params.irreducible`,
  `System.not_tupleStronglyIrreducible`, `Params.hasProximalDiagonal`;
* the conjugacy of `g_1, g_2, g_3` with the homogeneous system and `Δ_n^{diag} = Δ_n`:
  `Params.gWord_firstAxis_conj`, `Params.diagGap_eq_homGap`;
* the strong separation condition through the four `y`-bands: `Params.strongSeparation`;
* the freeness of `Ψ`: `Params.mulIndependent`, `Params.count_eq_of_gDeriv_eq`,
  `Params.length_eq_of_gDeriv_eq`, `Params.lamWord_eq`, `eq_of_valPoly_eq`,
  `Params.freeProjective_of_mulIndependent` (`BoxLike.Aligned.NoOverlapPESCFree`);
* the failure of projective exponential separation by `lem:proj_gap_dominated` with `m = 3`:
  `homGap_lt_of_le_mul_exp`, `Params.not_projExpSeparation`.

Declarations:

* `exists_system_of_homFree_of_exceptionalSet`: the proposition from the properties of the
  pair `(λ, t)` that the proof uses.
* `prop_ssc_no_overlap_not_pesc`: `prop:ssc_no_overlap_not_pesc` from `BaranyKaenmakiPair`,
  along the proof of the article; `BoxLike.BaranyKaenmaki` discharges the hypothesis
  (`prop_ssc_no_overlap_not_pesc_holds`).
-/
public import BoxLike.Aligned.NoOverlapPESCFree
public import BoxLike.Aligned.NoOverlapPESCParams

@[expose] public section

namespace BoxLike

namespace NoOverlap

open Matrix

/-- `prop:ssc_no_overlap_not_pesc` from the properties of the pair `(λ, t)` that the proof uses:
`0 < λ < 1/3`, `0 < t < λ/(1-λ)`, the homogeneous system `(λx, λx + t, λx + 1)` generates a free
semigroup, and its gap `Δ_n^{λ,t}` lies eventually below every exponential `c^n`.

The proof follows the article. The parameters are chosen in the box of the proof outside the
countable union of proper algebraic hypersurfaces over `ℚ(λ, t)`, so that they are algebraically
independent over `ℚ(λ, t)`. The freeness of `Ψ` is proved through the multiplicative
independence of `λ, r_1, …, r_5`, the symbol counts and the coefficient of the first non-`λ`
symbol. The conclusions are those of `exists_system_of_homFree`. -/
theorem exists_system_of_homFree_of_exceptionalSet {lam t : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam < 1 / 3) (ht0 : 0 < t) (ht1 : t < lam / (1 - lam)) (hfree : HomFree lam t)
    (hgap : ∀ c : ℝ, 0 < c → ∃ n₀ : ℕ, ∀ n ≥ n₀, homGap lam t n < ENNReal.ofReal (c ^ n)) :
    ∃ S : System (Fin 4), S.o = ![0, 0, 0, 1] ∧ S.Proximal ∧ S.Irreducible ∧
      ¬ TupleStronglyIrreducible S.mat ∧
      (∀ i (v : Fin 2 → ℝ), v 0 = 0 ∨ v 1 = 0 → (S.mat i *ᵥ v) 0 = 0 ∨ (S.mat i *ᵥ v) 1 = 0) ∧
      (∃ i₀, S.o i₀ = 0 ∧ |S.a i₀| ≠ |S.b i₀|) ∧
      S.StrongSeparation ∧ S.FreeProjective ∧ ¬ S.ProjExpSeparation ∧
      ∑ i, |(S.mat i).det| < 1 := by
  obtain ⟨P, rfl, rfl, hθ⟩ := exists_params_not_mem_exceptionalSet hlam0 hlam1 ht0 ht1
  have hx := (algebraicIndependent_iff_not_mem_exceptionalSet P.θ).2 hθ
  have hlamK : P.lam ∈ Subfield.closure ({P.lam, P.t} : Set ℝ) :=
    Subfield.subset_closure (by simp)
  have htK : P.t ∈ Subfield.closure ({P.lam, P.t} : Set ℝ) := Subfield.subset_closure (by simp)
  have hne : P.lam ≠ P.r₁ := P.lam_ne_r₁ hlamK hx
  exact ⟨P.sys, rfl, P.proximal hne, P.irreducible hne, P.sys.not_tupleStronglyIrreducible,
    fun i _ hv => P.sys.mulVec_mem_axes i hv, P.hasProximalDiagonal hne, P.strongSeparation,
    P.freeProjective_of_mulIndependent hlamK htK hfree hx, P.not_projExpSeparation hgap,
    P.sum_abs_det_lt_one⟩

/-- `prop:ssc_no_overlap_not_pesc`: there is a system `Φ = (φ_1, φ_2, φ_3, φ_4)` with `N = 4` and
`ℓ = 3` for which `(A_1, A_2, A_3, A_4)` is proximal and irreducible but not strongly irreducible
and `|a_{i_0}| ≠ |b_{i_0}|` for some `i_0 ≤ ℓ`, such that `X` satisfies the strong separation
condition and the maps of `Ψ` generate a free semigroup, yet `X` does not satisfy the projective
exponential separation condition. The union of the coordinate axes is invariant under every
`A_i`, and `∑_i |det A_i| < 1`.

The only hypothesis is the theorem of Bárány and Käenmäki in the form the article uses,
`BaranyKaenmakiPair`: a free pair with `Δ_n ≤ C_0 exp(-n²)` for all `n ≥ 1`, which the library
proves (`baranyKaenmakiPair_holds`). The proof follows the article: the parameters avoid the
countable union of proper algebraic hypersurfaces over `ℚ(λ, t)`, and the freeness of `Ψ` goes
through multiplicative independence, symbol counts and coefficient comparison
(`exists_system_of_homFree_of_exceptionalSet`). The statement is that of
`ssc_no_overlap_not_pesc`. -/
theorem prop_ssc_no_overlap_not_pesc (h : BaranyKaenmakiPair) :
    ∃ S : System (Fin 4), S.o = ![0, 0, 0, 1] ∧ S.Proximal ∧ S.Irreducible ∧
      ¬ TupleStronglyIrreducible S.mat ∧
      (∀ i (v : Fin 2 → ℝ), v 0 = 0 ∨ v 1 = 0 → (S.mat i *ᵥ v) 0 = 0 ∨ (S.mat i *ᵥ v) 1 = 0) ∧
      (∃ i₀, S.o i₀ = 0 ∧ |S.a i₀| ≠ |S.b i₀|) ∧
      S.StrongSeparation ∧ S.FreeProjective ∧ ¬ S.ProjExpSeparation ∧
      ∑ i, |(S.mat i).det| < 1 := by
  obtain ⟨lam, t, C₀, hlam0, hlam1, ht0, ht1, -, hC, hfree, hgap⟩ := h
  exact exists_system_of_homFree_of_exceptionalSet hlam0 hlam1 ht0 ht1 hfree fun c hc =>
    homGap_lt_of_le_mul_exp hC hgap hc

end NoOverlap

end BoxLike
